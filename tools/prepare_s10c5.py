#!/usr/bin/env python3
"""Print an apply_patch for the S10 cycle migration; witnesses are untrusted.

Uses the already kernel-checked S11-C5 structural proofs as source templates.
The output changes the cycle length and number of isolated vertices. Lean
must recheck every generated theorem; Python is not part of the trust base.
No filesystem writes or network access.
"""
from pathlib import Path
import re
from analyze_small_uniform import uniform_rows
from analyze_r5_symmetry import canonicalize

ROOT = Path(__file__).resolve().parents[1]
PROBES = ROOT / "lean-r5/R5Kernel/Probes"
DEST = ROOT / "lean-r5/R5Kernel"


def body(name):
    source = (PROBES / (name + ".lean")).read_text()
    return source.split("namespace Erdos1011\n", 1)[1].rsplit("end Erdos1011", 1)[0]


def cycle_names(source, ell):
    source = source.replace("C5", f"C{ell}").replace("c5", f"c{ell}")
    if ell == 9:
        source = source.replace("kernel_c9_all_subsets_covered", "kernelC9_all_subsets_covered")
    return source


def resize(source, ell):
    # Simultaneous substitution distinguishes cycle size 5, isolate size 6,
    # and the 7 possible isolate cardinalities in the source templates.
    values = {"11": "10", "5": str(ell), "6": str(10 - ell),
              "7": str(11 - ell), "32": str(2 ** ell), "2048": "1024"}
    source = re.sub(r"\b(?:11|5|6|7|32|2048)\b", lambda m: values[m[0]], source)
    source = source.replace("s11", "s10").replace("S11", "S10")
    source = cycle_names(source, ell).replace("seven isolated-vertex counts", "isolate counts")
    if ell != 5:
        source = source.replace("Eight cycle shapes", "Cycle shapes")
    return source


def module(imports, source, ell):
    header = "\n".join("import " + x for x in imports) + """

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S10C5
open scoped BigOperators

"""
    return header.replace("S10C5", f"S10C{ell}") + source.strip() + f"\n\nend Erdos1011.S10C{ell}\n"


def generate(ell=5):
    prefix = f"S10C{ell}"
    bound = {5: 226, 7: 214, 9: 184}[ell]
    local = body("S11C5Local")
    local = local[local.index("def kernelC5Embedding"):local.index("theorem kernel_c5_isolates_card")]
    cover = body("S11C5Cover")
    cover = cover[cover.index("def kernelIsoEmbedding"):cover.index("def kernelS11CoverValue")]
    beta = body("S11C5Beta")
    beta = beta[:beta.index("theorem kernel_s11_all_canonical_beta")]
    structural = resize(local + cover + beta, ell)
    structural += "\nrun_cmd R5Kernel.checkStandardAxioms ``kernel_s10_types_covered\n"
    structural += "run_cmd R5Kernel.checkStandardAxioms ``kernel_s10_sum_le_cover\n"
    structural += "run_cmd R5Kernel.checkStandardAxioms ``kernel_s10_beta_of_cycle_bound\n"
    orbit_import = "R5Kernel.Probes.S11C5OrbitData" if ell == 5 else f"R5Kernel.Probes.S11C{ell}BetaData"
    structural_imports = [orbit_import]
    if ell == 9:
        structural_imports.append("R5Kernel.Probes.S11C9Cover")
    structural_imports.append("R5Kernel.SmallUniform")
    yield prefix + "Structure", module(structural_imports, structural, ell)

    reps = sorted({canonicalize(m, 10, ell)[0] for m in range(1, 1024)})
    rows = uniform_rows(10, ell)
    data = "def kernelS10RepresentativeMasks : List ℕ := " + str(reps) + "\n\n"
    data += "def kernelS10Row (mask : ℕ) : ℕ × ℕ :=\n  match mask with\n"
    data += "\n".join(f"  | {m} => ({rows[m][1]}, {rows[m][2]})" for m in reps)
    data += "\n  | _ => (0, 0)\n\n"
    data_tail = """def maskSet (m : Fin 1024) : Finset (Fin 10) := kernelSmallMask 10 m.val

theorem canonical_beta_fields : ∀ m ∈ kernelS10RepresentativeMasks,
    m % 32 ∈ kernelC5CanonicalMasks ∧
    kernelC5Slice (kernelSmallMask 10 m) = kernelC5SmallMask (m % 32) ∧
    kernelC5CanonicalAlpha (m % 32) +
      ((kernelSmallMask 10 m).filter (fun x => ¬ x.val < 5)).card ≤
        (kernelS10Row m).1 := by
  decide +kernel

theorem canonical_beta (m : ℕ) (hm : m ∈ kernelS10RepresentativeMasks)
    (I : Finset (Fin 10)) (hI : I ∈ cycleTypes 10 5)
    (hIR : I ⊆ kernelSmallMask 10 m) : I.card ≤ (kernelS10Row m).1 := by
  obtain ⟨hsmall, hslice, hsize⟩ := canonical_beta_fields m hm
  apply kernel_s10_beta_of_cycle_bound _ (kernelC5CanonicalAlpha (m % 32)) _ ?_
    hsize I (Finset.mem_filter.mp hI).2.2 hIR
  rw [hslice]
  exact kernel_c5_canonical_beta_data (m % 32) hsmall

def coverValue (m : ℕ) : ℕ :=
  let R := kernelSmallMask 10 m
  let row := kernelS10Row m
  row.1 * (R.card * row.2) +
    ∑ p ∈ kernelC5Product, let I := kernelJoinParts p
      if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * row.2 else 0

theorem value_le_cover (m : ℕ) :
    R5Kernel.dualValue (cycleTypes 10 5) (kernelSmallMask 10 m)
        (kernelS10Row m).1 2 (fun _ => (kernelS10Row m).2) ≤ coverValue m := by
  rw [kernel_dualValue_uniform]
  exact Nat.add_le_add_left (kernel_s10_sum_le_cover _) _

run_cmd R5Kernel.checkStandardAxioms ``canonical_beta
run_cmd R5Kernel.checkStandardAxioms ``value_le_cover
"""
    data_tail = re.sub(r"\b(?:5|32)\b", lambda m: str(ell if m[0] == "5" else 2 ** ell), data_tail)
    data += cycle_names(data_tail, ell)
    yield prefix + "Data", module([f"R5Kernel.{prefix}Structure"], data, ell)

    symmetry = resize(body("S11C5BlockSymmetry"), ell)
    orbit = body("S11C5OrbitData")
    orbit = orbit[orbit.index("def kernelIsoPrefix"):orbit.index("run_cmd")]
    orbit = resize(orbit, ell).replace("r5RepMaskSet11", "maskSet")
    all_masks = body("S11C5AllMasks")
    all_masks = all_masks[all_masks.index("theorem kernel_s11_all_subsets_canonical"):all_masks.index("-- A complete dual certificate")]
    all_masks = resize(all_masks, ell).replace("r5RepMaskSet11", "maskSet")
    symmetry += orbit + all_masks
    symmetry += "\nrun_cmd R5Kernel.checkStandardAxioms ``kernel_s10_all_subsets_canonical\n"
    yield prefix + "Symmetry", module([f"R5Kernel.{prefix}Data", "Mathlib.Logic.Equiv.Fintype"], symmetry, ell)

    chunks = (len(reps) + 7) // 8
    for chunk in range(chunks):
        selected = reps[8 * chunk:8 * chunk + 8]
        checks = f"def block{chunk} : List ℕ := {selected}\n\n"
        checks += f"""theorem cover_bound_block{chunk} : ∀ m ∈ block{chunk},
    coverValue m ≤ {bound} := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``cover_bound_block{chunk}
"""
        yield f"{prefix}Checks{chunk}", module([f"R5Kernel.{prefix}Data"], checks, ell)

    cases = " ∨ ".join(f"m ∈ block{i}" for i in range(chunks))
    aggregate = f"""theorem all_cover_bounds (m : ℕ) (hm : m ∈ kernelS10RepresentativeMasks) :
    coverValue m ≤ {bound} := by
  have hblocks : ∀ m ∈ kernelS10RepresentativeMasks,
      {cases} := by decide +kernel
  rcases hblocks m hm with {" | ".join("h" for _ in range(chunks))}
"""
    aggregate += "\n".join(f"  · exact cover_bound_block{i} m h" for i in range(chunks)) + "\n\n"
    template = (DEST / "S10C5Certificates.lean").read_text()
    template = template[template.index("theorem all_nonempty_certificates"):template.rindex("end Erdos1011.S10C5")]
    template = re.sub(r"\b(?:5|226|113)\b", lambda m: {"5": str(ell), "226": str(bound), "113": str(bound // 2)}[m[0]], template)
    aggregate += template.replace("supportSurplus_le_113", f"supportSurplus_le_{bound // 2}")
    imports = [f"R5Kernel.{prefix}Checks{i}" for i in range(chunks)]
    imports += [f"R5Kernel.{prefix}Symmetry", "R5Kernel.GraphSymmetry"]
    yield prefix + "Certificates", module(imports, aggregate, ell)


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cycle", type=int, choices=(5, 7, 9), default=5)
    parser.add_argument("names", nargs="*")
    args = parser.parse_args()
    print("*** Begin Patch")
    for name, source in generate(args.cycle):
        if args.names and name not in args.names:
            continue
        destination = DEST / (name + ".lean")
        if destination.exists():
            raise SystemExit(f"Refusing to overwrite: {destination}")
        print(f"*** Add File: {destination}")
        print("\n".join("+" + line for line in source.splitlines()))
    print("*** End Patch")
