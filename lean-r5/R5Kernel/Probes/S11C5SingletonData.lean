import R5Kernel.Probes.S11C5CanonicalDefinitions
import R5Kernel.Audit

set_option Elab.async false

namespace Erdos1011

theorem kernel_s11_singleton_mask :
    r5RepMaskSet11 (kernelS11Row 1).mask = {0} := by decide +kernel

theorem kernel_s11_singleton_weights : ∀ i : Fin 11,
    r5RepScaledNum11 (kernelS11Row 1) i = if i = 0 then 16 else 0 := by decide +kernel

theorem kernel_s11_mask_fields :
    (kernelS11Row 1).mask = 1 ∧ (kernelS11Row 2047).mask = 2047 := by decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_singleton_mask
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_singleton_weights
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_mask_fields

end Erdos1011
