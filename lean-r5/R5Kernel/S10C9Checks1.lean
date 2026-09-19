import R5Kernel.S10C9Data

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S10C9
open scoped BigOperators

def block1 : List ℕ := [19, 21, 23, 27, 31, 35, 37, 39]

theorem cover_bound_block1 : ∀ m ∈ block1,
    coverValue m ≤ 184 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``cover_bound_block1

end Erdos1011.S10C9
