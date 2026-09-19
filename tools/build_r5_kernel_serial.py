#!/usr/bin/env python3
"""Build one ready local Lean module at a time, recording every Lake result.

Lake --no-build reports stale leaves without starting their compilers. Build
only the first such leaf and repeat. Unlike invoking one root target, this
does not start several heavy transitive dependencies simultaneously.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "lean-r5"


def ready_modules(output):
    return re.findall(
        r"Building (R5Kernel(?:\.[A-Za-z0-9_]+)+)\r?\n"
        r"error: target is out-of-date and needs to be rebuilt", output)


def run(command, log, timeout):
    with subprocess.Popen(command, cwd=PROJECT, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, text=True,
                          start_new_session=True) as process:
        try:
            output, _ = process.communicate(timeout=timeout)
        except (subprocess.TimeoutExpired, KeyboardInterrupt):
            os.killpg(process.pid, signal.SIGTERM)
            try:
                output, _ = process.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                output, _ = process.communicate()
            log.write(output)
            log.flush()
            raise
    log.write("COMMAND " + json.dumps(command) + "\n" + output + "\n")
    log.flush()
    return process.returncode, output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("label")
    parser.add_argument("target")
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()
    if not re.fullmatch(r"R5Kernel(?:\.[A-Za-z0-9_]+)+", args.target):
        parser.error("target must be a local R5Kernel module")
    if not re.fullmatch(r"[A-Za-z0-9_]+", args.label):
        parser.error("label must contain only letters, digits, underscores")
    directory = ROOT / "verification/r5-kernel"
    logfile = directory / (args.label + ".log")
    report = directory / (args.label + ".json")
    if logfile.exists() or report.exists():
        parser.error("choose a new label to preserve previous evidence")
    files = sorted((PROJECT / "R5Kernel").rglob("*.lean"))
    files += [PROJECT / "lakefile.toml", PROJECT / "lake-manifest.json",
              PROJECT / "lean-toolchain"]
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in files}
    start = time.monotonic()
    built = []
    status = "FAIL"
    failure = None
    try:
        with logfile.open("x") as log:
            for _ in range(len(files) + 1):
                code, output = run(
                    ["lake", "--no-cache", "--no-ansi", "--no-build", "build", args.target],
                    log, args.timeout)
                if code == 0:
                    status = "PASS"
                    break
                ready = ready_modules(output)
                if not ready:
                    failure = "No ready local module; inspect the Lake error."
                    print(output[-5000:], flush=True)
                    break
                module = ready[0]
                if module in built:
                    failure = "A rebuilt module is stale again; inputs may have changed."
                    break
                print("Building sequentially: " + module, flush=True)
                code, output = run(["lake", "--no-cache", "--no-ansi", "build", module],
                                   log, args.timeout)
                print(output[-1800:], flush=True)
                if code:
                    failure = "Build failed: " + module
                    break
                built.append(module)
    except subprocess.TimeoutExpired:
        status = "TIMEOUT"
    except KeyboardInterrupt:
        status = "INTERRUPTED"
    changed = [str(p.relative_to(ROOT)) for p in files
               if hashlib.sha256(p.read_bytes()).hexdigest() != hashes[str(p.relative_to(ROOT))]]
    if changed:
        status, failure = "FAIL", "Inputs changed during build: " + ", ".join(changed)
    result = dict(status=status, target=args.target, built_modules=built,
                  seconds=round(time.monotonic() - start, 3),
                  per_command_timeout=args.timeout, failure=failure,
                  input_sha256=hashes,
                  log_sha256=hashlib.sha256(logfile.read_bytes()).hexdigest(),
                  scope="The selected target and its audited declarations. This is an incremental build, not a clean rebuild.")
    report.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "input_sha256"}, indent=2))
    return 0 if status == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
