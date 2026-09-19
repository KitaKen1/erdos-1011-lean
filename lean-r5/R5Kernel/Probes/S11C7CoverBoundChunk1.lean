import R5Kernel.Probes.S11C7Cover

set_option Elab.async false
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelS11C7CoverMasksChunk1 : List ℕ :=
  [21, 23, 27, 31, 43, 47, 55, 63]

theorem kernel_s11c7_cover_bound_block1 :
    ∀ m ∈ kernelS11C7CoverMasksChunk1,
      kernelS11C7CoverValue (kernelS11C7Row m) ≤ 516 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c7_cover_bound_block1

end Erdos1011
