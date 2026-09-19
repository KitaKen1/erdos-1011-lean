import R5Kernel.Probes.S11C5Cover

set_option Elab.async false
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelS11CoverMasksChunk4 : List ℕ :=
  [481, 483, 485, 487, 491, 495, 511, 992]

theorem kernel_s11_cover_bound_block4 :
    ∀ m ∈ kernelS11CoverMasksChunk4,
      kernelS11CoverValue (kernelS11Row m) ≤ 284 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_cover_bound_block4

end Erdos1011
