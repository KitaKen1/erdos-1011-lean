#!/usr/bin/env python3
"""Bound a local Lean check; preserve exact command, inputs, output, and outcome."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("label")
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--expect-rejection", action="store_true")
    parser.add_argument("--require", action="append", default=[])
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command
    if command and command[0] == "--":
        command = command[1:]
    if not command or command[0] != "lake":
        parser.error("supply a local lake command after --")
    directory = ROOT / "verification/r5-kernel"
    directory.mkdir(parents=True, exist_ok=True)
    output = directory / (args.label + ".log")
    report = directory / (args.label + ".json")
    if output.exists() or report.exists():
        parser.error("use a new label to preserve prior evidence")
    inputs = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in sorted((ROOT / "lean-r5/R5Kernel").rglob("*.lean"))}
    start = time.monotonic()
    with output.open("w") as log:
        process = subprocess.Popen(command, cwd=ROOT / "lean-r5", stdout=log,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        timeout = False
        try:
            code = process.wait(timeout=args.timeout)
        except subprocess.TimeoutExpired:
            timeout = True
            os.killpg(process.pid, signal.SIGTERM)
            try:
                code = process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                code = process.wait()
    text = output.read_text()
    matched = all(message in text for message in args.require)
    passed = not timeout and matched and ((code != 0 and "R5_KERNEL_REJECTED" in text)
                                          if args.expect_rejection else code == 0)
    result = {"status": "EXPECTED_REJECTION" if passed and args.expect_rejection else
              "PASS" if passed else "TIMEOUT" if timeout else "FAIL",
              "command": command, "exit_code": code, "seconds": round(time.monotonic() - start, 3),
              "timeout_seconds": args.timeout, "required_messages": args.require,
              "lean_toolchain": (ROOT / "lean-r5/lean-toolchain").read_text().strip(),
              "lake_manifest_sha256": hashlib.sha256((ROOT / "lean-r5/lake-manifest.json").read_bytes()).hexdigest(),
              "input_sha256": inputs, "log_sha256": hashlib.sha256(output.read_bytes()).hexdigest(),
              "scope": "This command and its audited declarations; the required messages identify the checked targets. Imported dependencies may be cached."}
    report.write_text(json.dumps(result, indent=2) + "\n")
    print(text[-7000:])
    print(json.dumps({k: v for k, v in result.items() if k != "input_sha256"}, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
