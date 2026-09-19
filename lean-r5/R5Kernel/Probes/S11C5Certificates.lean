import R5Kernel.Probes.S11C5Local
import R5Kernel.Probes.S11C5SingletonData
import R5Kernel.Probes.S11C5Analytic

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Erdos1011
open scoped BigOperators

-- These are exactly the mask, beta, and scaled-bound obligations consumed by
-- the original C5 support-surplus argument, restricted to a canonical row.
def KernelS11C5Certificate (m : Fin 2048) : Prop :=
  (kernelS11Row m.val).mask = m ∧
  (∀ I ∈ cycleTypes 11 5,
    I ⊆ r5RepMaskSet11 (kernelS11Row m.val).mask →
      I.card ≤ (kernelS11Row m.val).beta) ∧
  r5RepNatScaledValue11 (kernelS11Row m.val) ≤ 284

theorem kernel_s11_full_beta : ∀ I ∈ cycleTypes 11 5,
    I ⊆ r5RepMaskSet11 (kernelS11Row 2047).mask →
      I.card ≤ (kernelS11Row 2047).beta := by
  intro I hI _
  exact kernel_s11_independent_card I (Finset.mem_filter.mp hI).2.2

theorem kernel_s11_singleton_scaled_value :
    r5RepNatScaledValue11 (kernelS11Row 1) = 16 := by
  unfold r5RepNatScaledValue11
  rw [kernel_s11_singleton_mask]
  simp only [kernel_s11_singleton_weights]
  have hres : (∑ I ∈ cycleTypes 11 5, if (I ∩ {0}).Nonempty then
      2 * I.card - ∑ e ∈ I,
        if e ∈ ({0} : Finset (Fin 11)) then (if e = 0 then 16 else 0) else 0
      else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro I hI
    have hcard := kernel_s11_independent_card I (Finset.mem_filter.mp hI).2.2
    by_cases hzero : (0 : Fin 11) ∈ I
    · have hle : 2 * I.card ≤ 16 := by omega
      simp [Finset.inter_singleton_of_mem hzero, hzero, Nat.sub_eq_zero_of_le hle]
    · simp [Finset.inter_singleton_of_notMem hzero]
  rw [hres]
  norm_num [kernelS11Row, mkR5RepDual11]

theorem kernel_s11_certificate_singleton : KernelS11C5Certificate 1 := by
  refine ⟨kernel_s11_mask_fields.1, kernel_s11_singleton_beta, ?_⟩
  change r5RepNatScaledValue11 (kernelS11Row 1) ≤ 284
  rw [kernel_s11_singleton_scaled_value]
  decide +kernel

theorem kernel_s11_certificate_full : KernelS11C5Certificate 2047 :=
  ⟨kernel_s11_mask_fields.2, kernel_s11_full_beta, kernel_s11_full_scaled_bound⟩

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_singleton_scaled_value
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_certificate_singleton
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_certificate_full

end Erdos1011
