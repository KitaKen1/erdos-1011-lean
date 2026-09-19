import R5Kernel.Probes.S11C5CanonicalDefinitions
import R5Kernel.Audit

set_option Elab.async false
set_option maxHeartbeats 1000000

namespace Erdos1011

theorem kernel_s11_atomic_card_one :
    (r5RepMaskSet11 (kernelS11Row 1).mask).card = 1 := by decide +kernel

theorem kernel_s11_atomic_full_mask :
    r5RepMaskSet11 (kernelS11Row 2047).mask = Finset.univ := by decide +kernel

theorem kernel_s11_atomic_full_weights :
    ∀ i : Fin 11, r5RepScaledNum11 (kernelS11Row 2047) i = 2 := by decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_atomic_card_one
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_atomic_full_mask
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_atomic_full_weights

end Erdos1011
