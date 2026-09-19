import R5Kernel.S10C7Data

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S10C7
open scoped BigOperators

def block3 : List ℕ := [143, 147, 149, 151, 155, 159, 171, 175]

theorem cover_bound_block3 : ∀ m ∈ block3,
    coverValue m ≤ 214 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``cover_bound_block3

end Erdos1011.S10C7
