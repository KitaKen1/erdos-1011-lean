import R5Kernel.Probes.S11C11CanonicalDefinitions
import R5Kernel.Audit

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace Erdos1011

theorem kernel_c11_local_alpha : ∀ J : Finset (Fin 11),
    (cycleGraph 11 11).IsIndepSet (J : Set (Fin 11)) → J.card ≤ 5 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_local_alpha

end Erdos1011
