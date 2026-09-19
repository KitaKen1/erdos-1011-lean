import R5Kernel.Probes.S11C5Local

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelC5CanonicalMasks : List ℕ := [0, 1, 3, 5, 7, 11, 15, 31]

def kernelC5SmallMask (m : ℕ) : Finset (Fin 5) :=
  Finset.univ.filter (fun x => (m / 2 ^ x.val) % 2 = 1)

def kernelC5CanonicalAlpha (m : ℕ) : ℕ :=
  if m = 0 then 0 else if m = 1 ∨ m = 3 then 1 else 2

-- At most 8 × 32 small cases, never the 2048 subsets of Fin 11.
theorem kernel_c5_canonical_beta_data : ∀ m ∈ kernelC5CanonicalMasks,
    ∀ J : Finset (Fin 5),
      (cycleGraph 5 5).IsIndepSet (J : Set (Fin 5)) →
      J ⊆ kernelC5SmallMask m → J.card ≤ kernelC5CanonicalAlpha m := by
  decide +kernel

-- Field identities and isolated-vertex counts for all 55 original rows.
theorem kernel_s11_canonical_beta_fields : ∀ m ∈ kernelS11RepresentativeMasks,
    m % 32 ∈ kernelC5CanonicalMasks ∧
    (kernelS11Row m).mask.val = m ∧
    kernelC5Slice (r5RepMaskSet11 (kernelS11Row m).mask) = kernelC5SmallMask (m % 32) ∧
    kernelC5CanonicalAlpha (m % 32) +
      ((r5RepMaskSet11 (kernelS11Row m).mask).filter (fun x => ¬ x.val < 5)).card ≤
        (kernelS11Row m).beta := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_c5_canonical_beta_data
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_canonical_beta_fields

end Erdos1011
