#!/usr/bin/env python3
"""Print untrusted complement witnesses; the generated Lean checks all 126."""
from prepare_c11_low_witness import DEST, module
import re


def witnesses():
    source = (DEST / "S11C11CanonicalDefinitions.lean").read_text()
    masks = list(map(int, re.findall(r"\d+", source.split(": List ℕ :=", 1)[1].split("]", 1)[0])))
    assert len(masks) == 126
    moved = {}
    for c, mask in enumerate(masks):
        for d in range(22):
            image = sum(1 << ((x + d if d < 11 else d - x) % 11)
                        for x in range(11) if mask >> x & 1)
            moved.setdefault(image, (c, d))
    return [moved[2047 ^ mask] for mask in masks]


def generate():
    body = """/- These explicit candidates avoid existential search; the kernel
checks the equality for every canonical representative below. -/
def kernelC11ComplementWitness (i : Fin 126) : Fin 126 × Fin 22 :=
  match i.val with
"""
    body += "\n".join(f"  | {i} => ({c}, {d})" for i, (c, d) in enumerate(witnesses()))
    body += """
  | _ => (0, 0)

theorem kernel_c11_complement_witness_valid : ∀ i : Fin 126,
    (kernelC11SmallMask
      (kernelC11CanonicalRep126 (kernelC11ComplementWitness i).1).val).map
        (kernelC11ActionEquiv (kernelC11ComplementWitness i).2).toEmbedding =
      (Finset.univ : Finset (Fin 11)) \\
        kernelC11SmallMask (kernelC11CanonicalRep126 i).val := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_complement_witness_valid
"""
    return module(["R5Kernel.Probes.S11C11OrbitAction",
                   "R5Kernel.Probes.S11C11Canonical126", "R5Kernel.Audit"], body)


if __name__ == "__main__":
    path = DEST / "S11C11ComplementWitness.lean"
    if path.exists():
        raise ValueError("refusing to overwrite " + str(path))
    print("*** Begin Patch")
    print(f"*** Add File: {path}")
    print("\n".join("+" + line for line in generate().splitlines()))
    print("*** End Patch")
