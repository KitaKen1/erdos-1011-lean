import R5Kernel.Probes.S11C7Cover

set_option Elab.async false
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelS11C7CoverMasksChunk3 : List ℕ :=
  [143, 147, 149, 151, 155, 159, 171, 175]

theorem kernel_s11c7_cover_bound_block3 :
    ∀ m ∈ kernelS11C7CoverMasksChunk3,
      kernelS11C7CoverValue (kernelS11C7Row m) ≤ 516 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c7_cover_bound_block3

end Erdos1011
