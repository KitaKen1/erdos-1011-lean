import R5Kernel.SmallUniform

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000

namespace Erdos1011

/-!
  The first S10 migration slice is deliberately kept independent of the
  large legacy replay tables in `Parts/M071`--`M073`.  It establishes the
  finite-mask interface used by any future C5/C7/C9 certificate: every
  subset of `Fin 10` has a canonical ten-bit code, zero is exactly the
  empty mask, and decoded masks never contain more than ten vertices.

  These are kernel-checked facts (`decide +kernel`), so this module carries
  no native-decision or project-specific axioms.
-/

theorem kernel_s10_decode_encode (R : Finset (Fin 10)) :
    kernelSmallMask 10 (kernelSmallEncode R).val = R := by
  revert R
  decide +kernel

theorem kernel_s10_mask_card_le (m : Fin 1024) :
    (kernelSmallMask 10 m.val).card ≤ 10 := by
  revert m
  decide +kernel

theorem kernel_s10_mask_nonempty_iff (m : Fin 1024) :
    (kernelSmallMask 10 m.val).Nonempty ↔ m.val ≠ 0 := by
  revert m
  decide +kernel

theorem kernel_s10_encode_nonempty_iff (R : Finset (Fin 10)) :
    (kernelSmallEncode R).val ≠ 0 ↔ R.Nonempty := by
  revert R
  decide +kernel

/- The arithmetic headroom available to any eventual S10 certificate. -/
theorem kernel_small_gap_s10_80 {n : ℕ} (hn : 80 ≤ n) :
    (n - 10)^2 / 4 + 149 ≤ fiveCandidate n := by
  rw [fiveCandidate_recenter hn]
  have hshift : n - 6 = (n - 10) + 4 := by omega
  have hsq : (n - 6)^2 = (n - 10)^2 + (8 * (n - 10) + 16) := by
    rw [hshift]
    ring
  have hdiv :
      (n - 10)^2 / 4 + (8 * (n - 10) + 16) / 4 ≤
        ((n - 10)^2 + (8 * (n - 10) + 16)) / 4 :=
    Nat.div_add_div_le_add_div
  rw [← hsq] at hdiv
  have hD : 144 ≤ (8 * (n - 10) + 16) / 4 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2
    omega
  omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s10_decode_encode
run_cmd R5Kernel.checkStandardAxioms ``kernel_s10_mask_card_le
run_cmd R5Kernel.checkStandardAxioms ``kernel_s10_mask_nonempty_iff
run_cmd R5Kernel.checkStandardAxioms ``kernel_s10_encode_nonempty_iff
run_cmd R5Kernel.checkStandardAxioms ``kernel_small_gap_s10_80

end Erdos1011
