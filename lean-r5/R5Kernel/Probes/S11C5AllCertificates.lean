import R5Kernel.Probes.S11C5CoverChecks
import R5Kernel.Probes.S11C5Beta
import R5Kernel.Probes.S11C5Certificates

set_option Elab.async false

namespace Erdos1011

theorem kernel_s11_all_canonical_scaled_bounds : ∀ m ∈ kernelS11RepresentativeMasks,
    r5RepNatScaledValue11 (kernelS11Row m) ≤ 284 := by
  intro m hm
  exact (kernel_s11_value_le_cover _).trans (kernel_s11_all_canonical_cover_bounds m hm)

theorem kernel_s11_all_canonical_certificates (m : Fin 2048)
    (hm : m.val ∈ kernelS11RepresentativeMasks) : KernelS11C5Certificate m :=
  ⟨kernel_s11_all_canonical_mask m hm, kernel_s11_all_canonical_beta m.val hm,
    kernel_s11_all_canonical_scaled_bounds m.val hm⟩

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_all_canonical_scaled_bounds
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_all_canonical_certificates

end Erdos1011
