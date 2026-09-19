import R5Kernel.S10C7Data

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S10C7
open scoped BigOperators

def block4 : List ℕ := [183, 191, 255, 384, 385, 387, 389, 391]

theorem cover_bound_block4 : ∀ m ∈ block4,
    coverValue m ≤ 214 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``cover_bound_block4

end Erdos1011.S10C7
