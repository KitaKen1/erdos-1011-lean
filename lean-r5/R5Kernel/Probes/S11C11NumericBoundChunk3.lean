import R5Kernel.Probes.S11C11NumericDefinitions
import R5Kernel.Probes.S11C11Canonical126
import R5Kernel.Audit

set_option Elab.async false
set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

namespace Erdos1011

theorem kernel_c11_canonical_scaled_bound_chunk3 : ∀ i : Fin 30,
    r5RepNatScaledValue11C11
        (kernelC11Row (kernelC11CanonicalRep126
          ⟨i.val + 96, by omega⟩).val) ≤ 206 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_canonical_scaled_bound_chunk3

end Erdos1011
