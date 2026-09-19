import R5Kernel.Probes.S11C11NumericDefinitions
import R5Kernel.Probes.S11C11Canonical126
import R5Kernel.Audit

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace Erdos1011

theorem kernel_c11_canonical_row_mask : ∀ i : Fin 126,
    (kernelC11Row (kernelC11CanonicalRep126 i).val).mask =
      kernelC11CanonicalRep126 i := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_canonical_row_mask

end Erdos1011
