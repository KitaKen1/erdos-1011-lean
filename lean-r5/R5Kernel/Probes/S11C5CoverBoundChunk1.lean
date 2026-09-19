import R5Kernel.Probes.S11C5Cover

set_option Elab.async false
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelS11CoverMasksChunk1 : List ℕ :=
  [33, 35, 37, 39, 43, 47, 63, 96]

theorem kernel_s11_cover_bound_block1 :
    ∀ m ∈ kernelS11CoverMasksChunk1,
      kernelS11CoverValue (kernelS11Row m) ≤ 284 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_cover_bound_block1

end Erdos1011
