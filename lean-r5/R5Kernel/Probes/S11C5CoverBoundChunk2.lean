import R5Kernel.Probes.S11C5Cover

set_option Elab.async false
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelS11CoverMasksChunk2 : List ℕ :=
  [97, 99, 101, 103, 107, 111, 127, 224]

theorem kernel_s11_cover_bound_block2 :
    ∀ m ∈ kernelS11CoverMasksChunk2,
      kernelS11CoverValue (kernelS11Row m) ≤ 284 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_cover_bound_block2

end Erdos1011
