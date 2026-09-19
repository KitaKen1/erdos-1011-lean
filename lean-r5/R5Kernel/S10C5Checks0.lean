import R5Kernel.S10C5Data

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S10C5
open scoped BigOperators

def block0 : List ℕ := [1, 3, 5, 7, 11, 15, 31, 32]

theorem cover_bound_block0 : ∀ m ∈ block0,
    coverValue m ≤ 226 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``cover_bound_block0

end Erdos1011.S10C5
