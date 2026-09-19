import R5Kernel.S7C7Data

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S7C7
open scoped BigOperators

theorem all_cover_bounds : ∀ m ∈ kernelS7RepresentativeMasks,
    coverValue m ≤ 54 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``all_cover_bounds

end Erdos1011.S7C7
