import R5Kernel.S10C5Data

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S10C5
open scoped BigOperators

def block5 : List ℕ := [993, 995, 997, 999, 1003, 1007, 1023]

theorem cover_bound_block5 : ∀ m ∈ block5,
    coverValue m ≤ 226 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``cover_bound_block5

end Erdos1011.S10C5
