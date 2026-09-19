import R5Kernel.S10C9Data

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S10C9
open scoped BigOperators

def block8 : List ℕ := [559, 563, 567, 575, 585, 587, 591, 595]

theorem cover_bound_block8 : ∀ m ∈ block8,
    coverValue m ≤ 184 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``cover_bound_block8

end Erdos1011.S10C9
