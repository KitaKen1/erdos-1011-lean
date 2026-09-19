import R5Kernel.Probes.S11C7Cover

set_option Elab.async false
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelS11C7CoverMasksChunk7 : List ℕ :=
  [901, 903, 905, 907, 911, 915, 917, 919]

theorem kernel_s11c7_cover_bound_block7 :
    ∀ m ∈ kernelS11C7CoverMasksChunk7,
      kernelS11C7CoverValue (kernelS11C7Row m) ≤ 516 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c7_cover_bound_block7

end Erdos1011
