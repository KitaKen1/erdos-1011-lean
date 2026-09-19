import R5Kernel.Probes.S11C7Cover

set_option Elab.async false
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelS11C7CoverMasksChunk6 : List ℕ :=
  [427, 431, 439, 447, 511, 896, 897, 899]

theorem kernel_s11c7_cover_bound_block6 :
    ∀ m ∈ kernelS11C7CoverMasksChunk6,
      kernelS11C7CoverValue (kernelS11C7Row m) ≤ 516 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c7_cover_bound_block6

end Erdos1011
