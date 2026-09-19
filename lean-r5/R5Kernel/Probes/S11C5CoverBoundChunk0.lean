import R5Kernel.Probes.S11C5Cover

set_option Elab.async false
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelS11CoverMasksChunk0 : List ℕ :=
  [1, 3, 5, 7, 11, 15, 31, 32]

theorem kernel_s11_cover_bound_block0 :
    ∀ m ∈ kernelS11CoverMasksChunk0,
      kernelS11CoverValue (kernelS11Row m) ≤ 284 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_cover_bound_block0

end Erdos1011
