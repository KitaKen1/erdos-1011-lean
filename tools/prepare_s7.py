#!/usr/bin/env python3
"""Print an apply_patch for S7 certificates, never trusted as a proof.

C5 reuses the 23 explicit witnesses in the checked S7C5Data source;
these are candidate data, not an independent witness search.
C7 uses exact-integer uniform-weight search. Every resulting inequality and
orbit-coverage theorem must be independently checked by the Lean kernel.
No filesystem writes or network access.
"""
from pathlib import Path
import ast
import re

from prepare_s10c5 import body, cycle_names
from analyze_small_uniform import uniform_rows
from analyze_r5_symmetry import canonicalize

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "lean-r5/R5Kernel"


def resize(source, ell):
    values = {"11": "7", "5": str(ell), "6": str(7 - ell),
              "7": str(8 - ell), "32": str(2 ** ell), "2048": "128"}
    source = re.sub(r"\b(?:11|5|6|7|32|2048)\b", lambda m: values[m[0]], source)
    source = source.replace("s11", "s7").replace("S11", "S7")
    return cycle_names(source, ell).replace("seven isolated-vertex counts", "isolate counts")


def module(imports, source, ell):
    return "\n".join("import " + x for x in imports) + f"""

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S7C{ell}
open scoped BigOperators

""" + source.strip() + f"\n\nend Erdos1011.S7C{ell}\n"


def witness_rows(ell):
    reps = sorted({canonicalize(m, 7, ell)[0] for m in range(1, 128)})
    if ell == 7:
        rows = uniform_rows(7, 7)
        return {m: (rows[m][1], [rows[m][2]] * 7) for m in reps}
    source = (DEST / "S7C5Data.lean").read_text()
    pattern = r"^  \| (\d+) => \((\d+), (\[[0-9, ]+\])\)$"
    result = {}
    for mask, beta, values in re.findall(pattern, source, re.M):
        weights = ast.literal_eval(values)
        assert len(weights) == 7 and all(w >= 0 for w in weights)
        result[int(mask)] = (int(beta), weights)
    assert sorted(result) == reps
    return dict(sorted(result.items()))


def generate(ell):
    prefix = f"S7C{ell}"
    bound = {5: 65, 7: 54}[ell]
    local = body("S11C5Local")
    local = local[local.index("def kernelC5Embedding"):local.index("theorem kernel_c5_isolates_card")]
    cover = body("S11C5Cover")
    cover = cover[cover.index("def kernelIsoEmbedding"):cover.index("def kernelS11CoverValue")]
    beta = body("S11C5Beta")
    beta = beta[:beta.index("theorem kernel_s11_all_canonical_beta")]
    structural = resize(local + cover + beta, ell)
    structural += "\nrun_cmd R5Kernel.checkStandardAxioms ``kernel_s7_types_covered\n"
    structural += "run_cmd R5Kernel.checkStandardAxioms ``kernel_s7_sum_le_cover\n"
    structural += "run_cmd R5Kernel.checkStandardAxioms ``kernel_s7_beta_of_cycle_bound\n"
    orbit_import = "R5Kernel.Probes.S11C5OrbitData" if ell == 5 else "R5Kernel.Probes.S11C7BetaData"
    yield prefix + "Structure", module([orbit_import, "R5Kernel.SmallUniform"], structural, ell)

    rows = witness_rows(ell)
    reps = list(rows)
    data = f"def kernelS7RepresentativeMasks : List ℕ := {reps}\n\n"
    data += "def kernelS7Row (mask : ℕ) : ℕ × List ℕ :=\n  match mask with\n"
    data += "\n".join(f"  | {m} => ({beta}, {weights})" for m, (beta, weights) in rows.items())
    data += "\n  | _ => (0, [])\n\n"
    data_tail = """def weight (m : ℕ) (i : Fin 7) : ℕ := (kernelS7Row m).2.getD i.val 0

def maskSet (m : Fin 128) : Finset (Fin 7) := kernelSmallMask 7 m.val

theorem canonical_beta_fields : ∀ m ∈ kernelS7RepresentativeMasks,
    m % 32 ∈ kernelC5CanonicalMasks ∧
    kernelC5Slice (kernelSmallMask 7 m) = kernelC5SmallMask (m % 32) ∧
    kernelC5CanonicalAlpha (m % 32) +
      ((kernelSmallMask 7 m).filter (fun x => ¬ x.val < 5)).card ≤
        (kernelS7Row m).1 := by
  decide +kernel

theorem canonical_beta (m : ℕ) (hm : m ∈ kernelS7RepresentativeMasks)
    (I : Finset (Fin 7)) (hI : I ∈ cycleTypes 7 5)
    (hIR : I ⊆ kernelSmallMask 7 m) : I.card ≤ (kernelS7Row m).1 := by
  obtain ⟨hsmall, hslice, hsize⟩ := canonical_beta_fields m hm
  apply kernel_s7_beta_of_cycle_bound _ (kernelC5CanonicalAlpha (m % 32)) _ ?_
    hsize I (Finset.mem_filter.mp hI).2.2 hIR
  rw [hslice]
  exact kernel_c5_canonical_beta_data (m % 32) hsmall

def coverValue (m : ℕ) : ℕ :=
  let R := kernelSmallMask 7 m
  (kernelS7Row m).1 * (∑ x ∈ R, weight m x) +
    ∑ p ∈ kernelC5Product, let I := kernelJoinParts p
      if (I ∩ R).Nonempty then
        2 * I.card - ∑ x ∈ I, if x ∈ R then weight m x else 0
      else 0

theorem value_le_cover (m : ℕ) :
    R5Kernel.dualValue (cycleTypes 7 5) (kernelSmallMask 7 m)
        (kernelS7Row m).1 2 (weight m) ≤ coverValue m := by
  unfold R5Kernel.dualValue coverValue
  exact Nat.add_le_add_left (kernel_s7_sum_le_cover _) _

run_cmd R5Kernel.checkStandardAxioms ``canonical_beta
run_cmd R5Kernel.checkStandardAxioms ``value_le_cover
"""
    # Resize only the proof template, never masks or numeric witnesses.
    data += re.sub(r"\b(?:5|32)\b", lambda m: str(ell if m[0] == "5" else 2 ** ell), data_tail)
    yield prefix + "Data", module([f"R5Kernel.{prefix}Structure"], cycle_names(data, ell), ell)

    symmetry = resize(body("S11C5BlockSymmetry"), ell)
    orbit = body("S11C5OrbitData")
    orbit = orbit[orbit.index("def kernelIsoPrefix"):orbit.index("run_cmd")]
    symmetry += resize(orbit, ell).replace("r5RepMaskSet11", "maskSet")
    masks = body("S11C5AllMasks")
    masks = masks[masks.index("theorem kernel_s11_all_subsets_canonical"):masks.index("-- A complete dual certificate")]
    symmetry += resize(masks, ell).replace("r5RepMaskSet11", "maskSet")
    symmetry += "\nrun_cmd R5Kernel.checkStandardAxioms ``kernel_s7_all_subsets_canonical\n"
    yield prefix + "Symmetry", module([f"R5Kernel.{prefix}Data", "Mathlib.Logic.Equiv.Fintype"], symmetry, ell)

    checks = f"""theorem all_cover_bounds : ∀ m ∈ kernelS7RepresentativeMasks,
    coverValue m ≤ {bound} := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``all_cover_bounds
"""
    yield prefix + "Checks", module([f"R5Kernel.{prefix}Data"], checks, ell)

    certificates = f"""theorem all_nonempty_certificates (R : Finset (Fin 7)) (hR : R.Nonempty) :
    ∃ b : ℕ, ∃ w : Fin 7 → ℕ,
      (∀ I ∈ cycleTypes 7 {ell}, I ⊆ R → I.card ≤ b) ∧
      R5Kernel.dualValue (cycleTypes 7 {ell}) R b 2 w ≤ {bound} := by
  obtain ⟨m, hm, e, hadj, hmap⟩ := kernel_s7_all_subsets_canonical R hR
  have hv := (value_le_cover m.val).trans (all_cover_bounds m.val hm)
  have ht := R5Kernel.graph_dualCertificate_transport
    (cycleGraph 7 {ell}) (cycleGraph 7 {ell}) e hadj (maskSet m)
    (kernelS7Row m.val).1 2 {bound} (weight m.val)
    (canonical_beta m.val hm) hv
  refine ⟨(kernelS7Row m.val).1, (fun y => weight m.val (e.symm y)), ?_⟩
  simpa only [hmap, R5Kernel.independentFamily, cycleTypes] using ht

theorem supportSurplus_le_{bound // 2} {{A B : Finset (Finset (Fin 7))}}
    (hAU : A ⊆ cycleTypes 7 {ell}) (hBU : B ⊆ cycleTypes 7 {ell})
    (hcompat : DegreeCompatible A B) : supportSurplus A B ≤ {bound // 2} := by
  have h : 2 * supportSurplus A B ≤ {bound} :=
    kernel_supportSurplus_scaled_of_certificates hAU hBU hcompat
      all_nonempty_certificates
  omega

run_cmd R5Kernel.checkStandardAxioms ``all_nonempty_certificates
run_cmd R5Kernel.checkStandardAxioms ``supportSurplus_le_{bound // 2}
"""
    yield prefix + "Certificates", module([f"R5Kernel.{prefix}Checks", f"R5Kernel.{prefix}Symmetry", "R5Kernel.GraphSymmetry"], certificates, ell)


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cycle", type=int, choices=(5, 7), required=True)
    args = parser.parse_args()
    print("*** Begin Patch")
    for name, source in generate(args.cycle):
        destination = DEST / (name + ".lean")
        if destination.exists():
            raise SystemExit(f"Refusing to overwrite: {destination}")
        print(f"*** Add File: {destination}")
        print("\n".join("+" + line for line in source.splitlines()))
    print("*** End Patch")
