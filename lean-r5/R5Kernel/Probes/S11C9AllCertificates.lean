import R5Kernel.Probes.S11C9CoverChecks
import R5Kernel.Probes.S11C9Beta

set_option Elab.async false

namespace Erdos1011

def KernelS11C9Certificate (m : Fin 2048) : Prop :=
  (kernelS11C9Row m.val).mask = m ∧
  (∀ I ∈ cycleTypes 11 9,
    I ⊆ r5RepMaskSet11C9 (kernelS11C9Row m.val).mask →
      I.card ≤ (kernelS11C9Row m.val).beta) ∧
  r5RepNatScaledValue11C9 (kernelS11C9Row m.val) ≤ 232

theorem kernel_s11c9_all_canonical_scaled_bounds :
    ∀ m ∈ kernelS11C9RepresentativeMasks,
      r5RepNatScaledValue11C9 (kernelS11C9Row m) ≤ 232 := by
  intro m hm
  exact (kernel_s11c9_value_le_cover _).trans
    (kernel_s11c9_all_canonical_cover_bounds m hm)

theorem kernel_s11c9_all_canonical_certificates (m : Fin 2048)
    (hm : m.val ∈ kernelS11C9RepresentativeMasks) : KernelS11C9Certificate m :=
  ⟨kernel_s11c9_all_canonical_mask m hm,
    kernel_s11c9_all_canonical_beta m.val hm,
    kernel_s11c9_all_canonical_scaled_bounds m.val hm⟩

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c9_all_canonical_scaled_bounds
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c9_all_canonical_certificates

end Erdos1011
