import R5Kernel.Probes.S11C9OrbitData

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelC9CanonicalAlpha (m : ℕ) : ℕ :=
  match m with
  | 0 => 0
  | 1 | 3 => 1
  | 5 | 7 | 9 | 11 | 15 | 17 | 19 | 27 | 35 => 2
  | 21 | 23 | 31 | 37 | 39 | 43 | 45 | 47 | 55 | 63 | 73 | 75 | 79 | 83 | 91 | 103 | 107 | 111 => 3
  | 51 => 2
  | 85 | 87 | 93 | 95 | 119 | 127 | 171 | 175 | 183 | 191 | 223 | 239 | 255 | 511 => 4
  | 219 => 3
  | _ => 0

theorem kernel_c9_canonical_beta_data : ∀ m ∈ kernelC9CanonicalMasks,
    ∀ J : Finset (Fin 9),
      (cycleGraph 9 9).IsIndepSet (J : Set (Fin 9)) →
      J ⊆ kernelC9SmallMask m → J.card ≤ kernelC9CanonicalAlpha m := by
  decide +kernel

theorem kernel_s11c9_canonical_beta_fields : ∀ m ∈ kernelS11C9RepresentativeMasks,
    m % 512 ∈ kernelC9CanonicalMasks ∧
    (kernelS11C9Row m).mask.val = m ∧
    kernelC9Slice (r5RepMaskSet11C9 (kernelS11C9Row m).mask) = kernelC9SmallMask (m % 512) ∧
    kernelC9CanonicalAlpha (m % 512) +
      ((r5RepMaskSet11C9 (kernelS11C9Row m).mask).filter (fun x => ¬ x.val < 9)).card ≤
        (kernelS11C9Row m).beta := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_c9_canonical_beta_data
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c9_canonical_beta_fields

end Erdos1011
