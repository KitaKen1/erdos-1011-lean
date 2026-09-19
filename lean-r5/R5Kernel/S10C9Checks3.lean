import R5Kernel.S10C9Data

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S10C9
open scoped BigOperators

def block3 : List ℕ := [79, 83, 85, 87, 91, 93, 95, 103]

theorem cover_bound_block3 : ∀ m ∈ block3,
    coverValue m ≤ 184 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``cover_bound_block3

end Erdos1011.S10C9
