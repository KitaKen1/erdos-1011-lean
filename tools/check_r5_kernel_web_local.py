#!/usr/bin/env python3
"""Recheck the entire standalone source locally, with bounded memory/time.

No project olean is imported by this source. Mathlib/Lean dependencies are
cached. This does not contact public Lean4Web and does not publish anything.
Logs and reports are never overwritten. A success requires all module-end
markers, the original final type, the exact three axioms, and the EOF audit.
"""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import PurePosixPath
import re
import signal
import subprocess
import time

from prepare_r5_kernel_web import ROOT, PROJECT, OUTPUT, MANIFEST, render, sha256

TARGET = "Erdos1011KernelLean4Web.formal_target_r5_ge80"
AXIOM_LINE = f"'{TARGET}' depends on axioms: [propext, Classical.choice, Quot.sound]"
AUDIT = f"R5_KERNEL_PASS {TARGET}: standard=3, extra=0, sorryAx=0"
FINISHED = "R5_KERNEL_WEB_FINISHED standard=3, extra=0, sorryAx=0"
EXPECTED_TYPE = (f"{TARGET} (n : ℕ) : 80 ≤ n → "
                 "Erdos1011.M 5 n = n ^ 2 / 4 - 3 * n + 14 ∧ "
                 "Erdos1011.f 5 n = n ^ 2 / 4 - 3 * n + 14 + 1 ∧ "
                 "Erdos1011.ThresholdExtremalOffset 5 n")


def assess(text, exit_code, modules):
    names = [m["module"] for m in modules]
    began = re.findall(r"^R5_WEB_BEGIN (\S+)$", text, re.M)
    ended = re.findall(r"^R5_WEB_END (\S+)$", text, re.M)
    events = re.findall(r"^R5_WEB_(BEGIN|END) (\S+)$", text, re.M)
    expected_events = [(event, name) for name in names for event in ("BEGIN", "END")]
    checks = dict(exit_zero=exit_code == 0,
                  module_starts_match=began == names,
                  module_completions_match=ended == names,
                  sequential_module_events=events == expected_events,
                  final_type=EXPECTED_TYPE in " ".join(text.split()),
                  exactly_standard_three=AXIOM_LINE in text,
                  final_strict_audit=AUDIT in text,
                  eof_sentinel=FINISHED in text,
                  no_error_diagnostics=not re.search(
                      r"(?m)^.*\berror:|memory_exception|excessive memory consumption", text))
    return checks, len(ended)


def stop(process):
    os.killpg(process.pid, signal.SIGTERM)
    try:
        return process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        return process.wait()


def verify_record(record, text, manifest, manifest_hash):
    checks, completed = assess(text, record["exit_code"], manifest["modules"])
    if record["status"] != "PASS" or not all(checks.values()):
        raise ValueError("record does not contain a complete successful standalone check")
    if record["log_sha256"] != sha256(text.encode()):
        raise ValueError("standalone log hash mismatch")
    if record["source_sha256"] != manifest["source_sha256"]:
        raise ValueError("standalone source hash mismatch")
    if record["bundle_manifest_sha256"] != manifest_hash:
        raise ValueError("bundle manifest hash mismatch")
    for field in ("lean_toolchain", "lake_manifest_sha256", "bytes", "source"):
        if record[field] != manifest[field]:
            raise ValueError("record field mismatch: " + field)
    if record["completed_modules"] != completed or record["module_count"] != completed:
        raise ValueError("completed module count mismatch")
    if not record["checks"].get("inputs_unchanged"):
        raise ValueError("inputs changed during recorded check")
    command = record.get("command", [])
    if len(command) != 6 or command[:5] != ["lake", "env", "lean", "-j1", "-M6144"]:
        raise ValueError("recorded command mismatch")
    # The historical checkout prefix is provenance, not the verifier location.
    # Bind the command to the same repository-relative source and its hashes,
    # so the unchanged record remains verifiable from another local clone.
    target = PurePosixPath(command[-1])
    source = PurePosixPath(manifest["source"])
    if (not target.is_absolute() or source.is_absolute() or ".." in target.parts or
            target.parts[-len(source.parts):] != source.parts):
        raise ValueError("recorded command source mismatch")
    return dict(offline_evidence_check="PASS", completed_modules=completed,
                source_sha256=manifest["source_sha256"],
                note="Recorded local evidence consistency only; Lean was not rerun; no public verification claim.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("label")
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--verify-only", action="store_true",
                        help="check recorded evidence without running Lean or writing files")
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z0-9_]+", args.label) or args.timeout <= 0:
        parser.error("use an alphanumeric label and a positive timeout")
    expected, manifest = render()
    if OUTPUT.read_text() != expected or json.loads(MANIFEST.read_text()) != manifest:
        raise ValueError("bundle/manifest must reproduce from current source before checking")
    evidence = ROOT / "verification/r5-kernel"
    logfile = evidence / (args.label + ".log")
    report = evidence / (args.label + ".json")
    if args.verify_only:
        print(json.dumps(verify_record(json.loads(report.read_text()), logfile.read_text(),
                                      manifest, sha256(MANIFEST.read_bytes())), indent=2))
        return 0
    if logfile.exists() or report.exists():
        parser.error("choose a new label to preserve previous evidence")
    source_hash = sha256(OUTPUT.read_bytes())
    manifest_hash = sha256(MANIFEST.read_bytes())
    start = time.monotonic()
    command = ["lake", "env", "lean", "-j1", "-M6144", str(OUTPUT)]
    timed_out, interrupted = False, False
    print("CHECK local standalone", OUTPUT.name, "sha256", source_hash, flush=True)
    print("LOG", logfile, flush=True)
    with logfile.open("x") as log:
        process = subprocess.Popen(command, cwd=PROJECT, stdout=log,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            code = process.wait(timeout=args.timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            code = stop(process)
        except KeyboardInterrupt:
            interrupted = True
            code = stop(process)
    text = logfile.read_text()
    checks, completed = assess(text, code, manifest["modules"])
    checks["inputs_unchanged"] = (
        sha256(OUTPUT.read_bytes()) == source_hash and
        sha256(MANIFEST.read_bytes()) == manifest_hash and
        (PROJECT / "lean-toolchain").read_text().strip() == manifest["lean_toolchain"] and
        sha256((PROJECT / "lake-manifest.json").read_bytes()) == manifest["lake_manifest_sha256"])
    passed = all(checks.values()) and not timed_out and not interrupted
    result = dict(status="PASS" if passed else "TIMEOUT" if timed_out else
                  "INTERRUPTED" if interrupted else "FAIL",
                  finished_utc=datetime.now(timezone.utc).isoformat(),
                  command=command, exit_code=code, seconds=round(time.monotonic() - start, 3),
                  timeout_seconds=args.timeout, source=manifest["source"],
                  source_sha256=source_hash, bytes=manifest["bytes"],
                  bundle_manifest_sha256=manifest_hash,
                  lean_toolchain=manifest["lean_toolchain"],
                  lake_manifest_sha256=manifest["lake_manifest_sha256"],
                  module_count=len(manifest["modules"]), completed_modules=completed,
                  checks=checks, log_sha256=sha256(logfile.read_bytes()),
                  environment="LOCAL ONLY; not public Lean4Web; no upload or push",
                  scope="Whole standalone source re-elaborated; only Lean/Mathlib dependencies imported; no local project olean imports.")
    with report.open("x") as handle:
        handle.write(json.dumps(result, indent=2) + "\n")
    print(text[-5000:])
    print(json.dumps(result, indent=2), flush=True)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
