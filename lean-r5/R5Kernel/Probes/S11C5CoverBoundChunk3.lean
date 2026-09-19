import R5Kernel.Probes.S11C5Cover

set_option Elab.async false
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelS11CoverMasksChunk3 : List ℕ :=
  [225, 227, 229, 231, 235, 239, 255, 480]

theorem kernel_s11_cover_bound_block3 :
    ∀ m ∈ kernelS11CoverMasksChunk3,
      kernelS11CoverValue (kernelS11Row m) ≤ 284 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_cover_bound_block3

end Erdos1011
