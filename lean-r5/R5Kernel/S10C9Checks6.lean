import R5Kernel.S10C9Data

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S10C9
open scoped BigOperators

def block6 : List ℕ := [517, 519, 521, 523, 527, 529, 531, 533]

theorem cover_bound_block6 : ∀ m ∈ block6,
    coverValue m ≤ 184 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``cover_bound_block6

end Erdos1011.S10C9
