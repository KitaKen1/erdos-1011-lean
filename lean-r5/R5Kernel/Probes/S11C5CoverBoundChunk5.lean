import R5Kernel.Probes.S11C5Cover

set_option Elab.async false
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelS11CoverMasksChunk5 : List ℕ :=
  [993, 995, 997, 999, 1003, 1007, 1023, 2016]

theorem kernel_s11_cover_bound_block5 :
    ∀ m ∈ kernelS11CoverMasksChunk5,
      kernelS11CoverValue (kernelS11Row m) ≤ 284 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_cover_bound_block5

end Erdos1011
