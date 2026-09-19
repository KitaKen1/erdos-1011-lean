import R5Kernel.Probes.S11C7Cover

set_option Elab.async false
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelS11C7CoverMasksChunk0 : List ℕ :=
  [1, 3, 5, 7, 9, 11, 15, 19]

theorem kernel_s11c7_cover_bound_block0 :
    ∀ m ∈ kernelS11C7CoverMasksChunk0,
      kernelS11C7CoverValue (kernelS11C7Row m) ≤ 516 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c7_cover_bound_block0

end Erdos1011
