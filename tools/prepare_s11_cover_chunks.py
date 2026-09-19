#!/usr/bin/env python3
"""Split C5/C7 representative arithmetic into kernel-checked blocks of eight.

No arithmetic answer is supplied by this generator. It prints Lean source
for the existing exact inequalities, plus a checked partition and assembly.
"""
import difflib
import re
from prepare_c11_low_witness import DEST, module


def representative_masks(ell):
    prefix = "kernelS11" if ell == 5 else "kernelS11C7"
    source = (DEST / f"S11C{ell}CanonicalDefinitions.lean").read_text()
    declaration = source.split(f"def {prefix}RepresentativeMasks", 1)[1]
    return list(map(int, re.findall(r"\d+", declaration.split("[", 1)[1].split("]", 1)[0])))


def generate(ell):
    assert ell in (5, 7)
    prefix = "kernelS11" if ell == 5 else "kernelS11C7"
    theorem_prefix = "kernel_s11" if ell == 5 else "kernel_s11c7"
    bound = 284 if ell == 5 else 516
    masks = representative_masks(ell)
    blocks = [masks[i:i + 8] for i in range(0, len(masks), 8)]
    for k, rows in enumerate(blocks):
        body = f"""def {prefix}CoverMasksChunk{k} : List ℕ :=
  [{', '.join(map(str, rows))}]

theorem {theorem_prefix}_cover_bound_block{k} :
    ∀ m ∈ {prefix}CoverMasksChunk{k},
      {prefix}CoverValue ({prefix}Row m) ≤ {bound} := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``{theorem_prefix}_cover_bound_block{k}
"""
        yield f"S11C{ell}CoverBoundChunk{k}", module([f"R5Kernel.Probes.S11C{ell}Cover"], body)
    parts = [f"{prefix}CoverMasksChunk{k}" for k in range(len(blocks))]
    partition = parts[-1]
    for part in reversed(parts[:-1]):
        partition = f"{part} ++ ({partition})"
    body = f"""theorem {theorem_prefix}_cover_masks_partition :
    {prefix}RepresentativeMasks =
      {partition} := by
  decide +kernel

theorem {theorem_prefix}_all_canonical_cover_bounds :
    ∀ m ∈ {prefix}RepresentativeMasks,
      {prefix}CoverValue ({prefix}Row m) ≤ {bound} := by
  intro m hm
  rw [{theorem_prefix}_cover_masks_partition] at hm
"""
    for k in range(len(blocks) - 1):
        body += f"""  rcases List.mem_append.mp hm with hm | hm
  · exact {theorem_prefix}_cover_bound_block{k} m hm
"""
    body += f"""  exact {theorem_prefix}_cover_bound_block{len(blocks) - 1} m hm

run_cmd R5Kernel.checkStandardAxioms ``{theorem_prefix}_cover_masks_partition
run_cmd R5Kernel.checkStandardAxioms ``{theorem_prefix}_all_canonical_cover_bounds
"""
    yield f"S11C{ell}CoverChecks", module(
        [f"R5Kernel.Probes.S11C{ell}CoverBoundChunk{k}" for k in range(len(blocks))], body)


if __name__ == "__main__":
    print("*** Begin Patch")
    for ell in (5, 7):
        for name, source in generate(ell):
            path = DEST / (name + ".lean")
            if path.exists():
                current = path.read_text()
                if current == source:
                    continue
                if name != f"S11C{ell}CoverChecks":
                    raise ValueError("refusing to overwrite existing block " + str(path))
                print(f"*** Update File: {path}")
                diff = list(difflib.unified_diff(current.splitlines(), source.splitlines(), n=3))
                for line in diff[2:]:
                    print("@@" if line.startswith("@@") else line)
            else:
                print(f"*** Add File: {path}")
                print("\n".join("+" + line for line in source.splitlines()))
    print("*** End Patch")
