import R5Kernel.Probes.S11C7OrbitData

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelC7CanonicalAlpha (m : ℕ) : ℕ :=
  match m with
  | 0 => 0
  | 1 | 3 => 1
  | 5 | 7 | 9 | 11 | 15 | 19 | 27 => 2
  | 21 | 23 | 31 | 43 | 47 | 55 | 63 | 127 => 3
  | _ => 0

theorem kernel_c7_canonical_beta_data : ∀ m ∈ kernelC7CanonicalMasks,
    ∀ J : Finset (Fin 7),
      (cycleGraph 7 7).IsIndepSet (J : Set (Fin 7)) →
      J ⊆ kernelC7SmallMask m → J.card ≤ kernelC7CanonicalAlpha m := by
  decide +kernel

theorem kernel_s11c7_canonical_beta_fields : ∀ m ∈ kernelS11C7RepresentativeMasks,
    m % 128 ∈ kernelC7CanonicalMasks ∧
    (kernelS11C7Row m).mask.val = m ∧
    kernelC7Slice (r5RepMaskSet11C7 (kernelS11C7Row m).mask) = kernelC7SmallMask (m % 128) ∧
    kernelC7CanonicalAlpha (m % 128) +
      ((r5RepMaskSet11C7 (kernelS11C7Row m).mask).filter (fun x => ¬ x.val < 7)).card ≤
        (kernelS11C7Row m).beta := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_c7_canonical_beta_data
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c7_canonical_beta_fields

end Erdos1011
