#!/usr/bin/env python3
"""Print a proof-preserving decision-instance priority edit for 96 S9 blocks."""
import argparse
from prepare_r5_kernel_web import PROJECT

ANCHOR = "namespace Erdos1011\n"
INSERT = """
-- Enumerate the bounded finset, not the whole finite ambient type.
attribute [local instance 2000] Finset.decidableDforallFinset
"""


def paths():
    return [PROJECT / f"R5Kernel/S9C{ell}TypeMaskChunk{k}.lean"
            for ell in (5, 7, 9) for k in range(32)]


def transform(source):
    if ANCHOR + INSERT in source:
        return source
    if source.count(ANCHOR) != 1 or "attribute [local instance 2000]" in source:
        raise ValueError("unexpected source layout or existing instance override")
    return source.replace(ANCHOR, ANCHOR + INSERT)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.check:
        for path in paths():
            assert transform(path.read_text()) == path.read_text(), str(path)
        print("All 96 S9 blocks use bounded-finset decision priority (not a Lean check).")
    else:
        print("*** Begin Patch")
        for path in paths():
            source = path.read_text()
            if source == transform(source):
                continue
            print(f"*** Update File: {path}\n@@\n {ANCHOR.rstrip()}")
            print("\n".join("+" + line for line in INSERT.splitlines()))
        print("*** End Patch")
