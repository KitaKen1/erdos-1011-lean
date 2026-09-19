import R5Kernel.S10C5Data

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S10C5
open scoped BigOperators

def block2 : List ℕ := [97, 99, 101, 103, 107, 111, 127, 224]

theorem cover_bound_block2 : ∀ m ∈ block2,
    coverValue m ≤ 226 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``cover_bound_block2

end Erdos1011.S10C5
