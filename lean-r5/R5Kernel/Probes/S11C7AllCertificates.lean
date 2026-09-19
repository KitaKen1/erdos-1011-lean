import R5Kernel.Probes.S11C7CoverChecks
import R5Kernel.Probes.S11C7Beta

set_option Elab.async false

namespace Erdos1011

def KernelS11C7Certificate (m : Fin 2048) : Prop :=
  (kernelS11C7Row m.val).mask = m ∧
  (∀ I ∈ cycleTypes 11 7,
    I ⊆ r5RepMaskSet11C7 (kernelS11C7Row m.val).mask →
      I.card ≤ (kernelS11C7Row m.val).beta) ∧
  r5RepNatScaledValue11C7 (kernelS11C7Row m.val) ≤ 516

theorem kernel_s11c7_all_canonical_scaled_bounds :
    ∀ m ∈ kernelS11C7RepresentativeMasks,
      r5RepNatScaledValue11C7 (kernelS11C7Row m) ≤ 516 := by
  intro m hm
  exact (kernel_s11c7_value_le_cover _).trans
    (kernel_s11c7_all_canonical_cover_bounds m hm)

theorem kernel_s11c7_all_canonical_certificates (m : Fin 2048)
    (hm : m.val ∈ kernelS11C7RepresentativeMasks) : KernelS11C7Certificate m :=
  ⟨kernel_s11c7_all_canonical_mask m hm,
    kernel_s11c7_all_canonical_beta m.val hm,
    kernel_s11c7_all_canonical_scaled_bounds m.val hm⟩

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c7_all_canonical_scaled_bounds
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c7_all_canonical_certificates

end Erdos1011
