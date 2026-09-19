import R5Kernel.S10C9Data

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S10C9
open scoped BigOperators

def block10 : List ℕ := [631, 639, 683, 687, 695, 703, 731, 735]

theorem cover_bound_block10 : ∀ m ∈ block10,
    coverValue m ≤ 184 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``cover_bound_block10

end Erdos1011.S10C9
