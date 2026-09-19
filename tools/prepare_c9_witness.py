#!/usr/bin/env python3
"""Print C9 orbit witnesses; generated Lean checks all 512 masks."""
from prepare_c11_low_witness import DEST, module
import re


def canonical_masks():
    source = (DEST / "S11C9OrbitDefinitions.lean").read_text()
    return list(map(int, re.findall(r"\d+", source.split("kernelC9CanonicalMasks : List ℕ :=", 1)[1].split("]", 1)[0])))


def witnesses():
    rows = {}
    for c in canonical_masks():
        for d in range(18):
            moved = sum(1 << ((x + d if d < 9 else d - x) % 9)
                        for x in range(9) if c >> x & 1)
            rows.setdefault(moved, (c, d))
    assert set(rows) == set(range(512))
    return dict(sorted(rows.items()))


def generate():
    body = """/- Explicit candidates are untrusted; the kernel checks every mask. -/
def kernelC9OrbitWitness (m : ℕ) : Fin 512 × Fin 18 :=
  match m with
"""
    body += "\n".join(f"  | {m} => ({c}, {d})" for m, (c, d) in witnesses().items())
    body += """
  | _ => (0, 0)

def KernelC9OrbitWitnessValid (m : ℕ) : Prop :=
  (kernelC9OrbitWitness m).1.val ∈ kernelC9CanonicalMasks ∧
    (kernelC9SmallMask (kernelC9OrbitWitness m).1.val).map
      (kernelC9ActionEquiv (kernelC9OrbitWitness m).2).toEmbedding = kernelC9SmallMask m

noncomputable instance (m : ℕ) : Decidable (KernelC9OrbitWitnessValid m) := by
  unfold KernelC9OrbitWitnessValid
  infer_instance

def kernelC9OrbitEncode (J : Finset (Fin 9)) : Fin 512 :=
  ⟨(∑ x ∈ J, 2 ^ x.val) % 512, Nat.mod_lt _ (by decide)⟩

theorem kernel_c9_orbit_decode_encode : ∀ J : Finset (Fin 9),
    kernelC9SmallMask (kernelC9OrbitEncode J).val = J := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_c9_orbit_decode_encode
"""
    yield "S11C9OrbitWitness", module(["R5Kernel.Probes.S11C9OrbitAction"], body)
    for k in range(4):
        body = f"""theorem kernel_c9_orbit_witness_block{k} : ∀ i : Fin 128,
    KernelC9OrbitWitnessValid (i.val + {128 * k}) := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_c9_orbit_witness_block{k}
"""
        yield f"S11C9OrbitWitnessChunk{k}", module(["R5Kernel.Probes.S11C9OrbitWitness"], body)
    body = """theorem kernel_c9_orbit_witness_all (m : Fin 512) :
    KernelC9OrbitWitnessValid m.val := by
"""
    for k in range(4):
        body += f"  by_cases h{k} : m.val < {128 * (k + 1)}\n"
        body += f"""  · have hb := kernel_c9_orbit_witness_block{k} ⟨m.val - {128 * k}, by omega⟩
    have he : m.val - {128 * k} + {128 * k} = m.val := by omega
    simpa only [he] using hb
"""
    body += """  omega

theorem kernel_c9_orbit_witness_coverage (J : Finset (Fin 9)) :
    ∃ c : Fin 512, ∃ d : Fin 18, c.val ∈ kernelC9CanonicalMasks ∧
      (kernelC9SmallMask c.val).map (kernelC9ActionEquiv d).toEmbedding = J := by
  let m := kernelC9OrbitEncode J
  have he : kernelC9SmallMask m.val = J := kernel_c9_orbit_decode_encode J
  have hw := kernel_c9_orbit_witness_all m
  unfold KernelC9OrbitWitnessValid at hw
  rw [he] at hw
  exact ⟨(kernelC9OrbitWitness m.val).1, (kernelC9OrbitWitness m.val).2, hw⟩

run_cmd R5Kernel.checkStandardAxioms ``kernel_c9_orbit_witness_all
run_cmd R5Kernel.checkStandardAxioms ``kernel_c9_orbit_witness_coverage
"""
    yield "S11C9OrbitWitnessCoverage", module(
        [f"R5Kernel.Probes.S11C9OrbitWitnessChunk{k}" for k in range(4)], body)


if __name__ == "__main__":
    print("*** Begin Patch")
    for name, source in generate():
        path = DEST / (name + ".lean")
        if path.exists():
            raise ValueError("refusing to overwrite " + str(path))
        print(f"*** Add File: {path}")
        print("\n".join("+" + line for line in source.splitlines()))
    print("*** End Patch")
