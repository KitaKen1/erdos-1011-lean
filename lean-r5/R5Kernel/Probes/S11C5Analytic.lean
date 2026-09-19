import R5Kernel.Probes.S11C5Atomic
import R5Kernel.Audit

set_option Elab.async false
set_option maxHeartbeats 1000000

namespace Erdos1011
open scoped BigOperators

-- The singleton beta bound does not require enumerating independent sets.
theorem kernel_s11_singleton_beta : ∀ I ∈ cycleTypes 11 5,
    I ⊆ r5RepMaskSet11 (kernelS11Row 1).mask → I.card ≤ (kernelS11Row 1).beta := by
  have hcard := kernel_s11_atomic_card_one
  have hbeta : (kernelS11Row 1).beta = 1 := rfl
  intro I _hI hsub
  have h := Finset.card_le_card hsub
  simpa only [hcard, hbeta] using h

-- At the full-mask row all scaled vertex weights equal 2, so every residual
-- summand cancels symbolically. No enumeration of the 703 types is needed.
theorem kernel_s11_full_scaled_value : r5RepNatScaledValue11 (kernelS11Row 2047) = 176 := by
  have hmask := kernel_s11_atomic_full_mask
  have hbeta : (kernelS11Row 2047).beta = 8 := rfl
  have hweights := kernel_s11_atomic_full_weights
  unfold r5RepNatScaledValue11
  simp only [hmask, hbeta, hweights, Finset.mem_univ, ite_true]
  norm_num [Finset.sum_const, Nat.mul_comm]

theorem kernel_s11_full_scaled_bound : r5RepNatScaledValue11 (kernelS11Row 2047) ≤ 284 := by
  rw [kernel_s11_full_scaled_value]
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_singleton_beta
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_full_scaled_value
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_full_scaled_bound

end Erdos1011
