#!/usr/bin/env python3
"""Print Lean candidate witnesses for small C11 masks; Lean checks every row."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "lean-r5/R5Kernel/Probes"


def witnesses():
    source = (DEST / "S11C11CanonicalDefinitions.lean").read_text()
    masks = list(map(int, re.findall(r"\d+", source.split(": List ℕ :=", 1)[1].split("]", 1)[0])))
    result = {}
    for c, mask in enumerate(masks[:125]):
        if bin(mask).count("1") > 5:
            continue
        for d in range(22):
            moved = sum(1 << ((x + d if d < 11 else d - x) % 11)
                        for x in range(11) if mask >> x & 1)
            result.setdefault(moved, (c, d))
    assert set(result) == {m for m in range(2048) if bin(m).count("1") <= 5}
    return dict(sorted(result.items()))


def module(imports, body):
    return "\n".join("import " + x for x in imports) + """

set_option Elab.async false
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000

namespace Erdos1011

""" + body + "\nend Erdos1011\n"


def generate():
    rows = witnesses()
    body = """/- Explicit witnesses replace existential orbit searches. The candidates
are untrusted: all 2048 mask codes are checked in sixteen small blocks. -/
def kernelC11LowCardWitness (m : ℕ) : Fin 125 × Fin 22 :=
  match m with
"""
    body += "\n".join(f"  | {m} => ({c}, {d})" for m, (c, d) in rows.items())
    body += """
  | _ => (0, 0)

def KernelC11LowCardWitnessValid (m : ℕ) : Prop :=
  (kernelC11SmallMask m).card ≤ 5 →
    (kernelC11SmallMask (kernelC11CanonicalRep (kernelC11LowCardWitness m).1).val).map
      (kernelC11ActionEquiv (kernelC11LowCardWitness m).2).toEmbedding = kernelC11SmallMask m

noncomputable instance (m : ℕ) : Decidable (KernelC11LowCardWitnessValid m) := by
  unfold KernelC11LowCardWitnessValid
  infer_instance

def kernelC11LowEncode (J : Finset (Fin 11)) : Fin 2048 :=
  ⟨(∑ x ∈ J, 2 ^ x.val) % 2048, Nat.mod_lt _ (by decide)⟩

theorem kernel_c11_low_decode_encode : ∀ J : Finset (Fin 11),
    kernelC11SmallMask (kernelC11LowEncode J).val = J := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_low_decode_encode
"""
    yield "S11C11LowCardWitness", module(["R5Kernel.Probes.S11C11OrbitAction"], body)
    for k in range(16):
        body = f"""theorem kernel_c11_low_witness_block{k} : ∀ i : Fin 128,
    KernelC11LowCardWitnessValid (i.val + {128 * k}) := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_low_witness_block{k}
"""
        yield f"S11C11LowCardChunk{k}", module(["R5Kernel.Probes.S11C11LowCardWitness"], body)
    body = """theorem kernel_c11_low_witness_all (m : Fin 2048) :
    KernelC11LowCardWitnessValid m.val := by
"""
    for k in range(16):
        body += f"  by_cases h{k} : m.val < {128 * (k + 1)}\n"
        body += f"""  · have hb := kernel_c11_low_witness_block{k} ⟨m.val - {128 * k}, by omega⟩
    have he : m.val - {128 * k} + {128 * k} = m.val := by omega
    simpa only [he] using hb
"""
    body += """  omega

theorem kernel_c11_low_card_coverage (J : Finset (Fin 11)) (hJ : J.card ≤ 5) :
    ∃ c : Fin 125, ∃ d : Fin 22,
      (kernelC11SmallMask (kernelC11CanonicalRep c).val).map
        (kernelC11ActionEquiv d).toEmbedding = J := by
  let m := kernelC11LowEncode J
  have he : kernelC11SmallMask m.val = J := kernel_c11_low_decode_encode J
  have hw := kernel_c11_low_witness_all m
  unfold KernelC11LowCardWitnessValid at hw
  rw [he] at hw
  exact ⟨(kernelC11LowCardWitness m.val).1, (kernelC11LowCardWitness m.val).2, hw hJ⟩

run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_low_witness_all
run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_low_card_coverage
"""
    yield "S11C11LowCardCoverage", module(
        [f"R5Kernel.Probes.S11C11LowCardChunk{k}" for k in range(16)], body)


if __name__ == "__main__":
    print("*** Begin Patch")
    for name, source in generate():
        path = DEST / (name + ".lean")
        if path.exists():
            raise ValueError("refusing to overwrite " + str(path))
        print(f"*** Add File: {path}")
        print("\n".join("+" + line for line in source.splitlines()))
    print("*** End Patch")
