import R5Kernel.S10C9Data

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S10C9
open scoped BigOperators

def block4 : List ℕ := [107, 111, 119, 127, 171, 175, 183, 191]

theorem cover_bound_block4 : ∀ m ∈ block4,
    coverValue m ≤ 184 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``cover_bound_block4

end Erdos1011.S10C9
