import R5Kernel.Probes.S11C9Cover

set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelS11C9RepresentativeMasksChunk2 : List Nat :=
  [517, 519, 521, 523, 527, 529, 531, 533, 535, 539, 543, 547, 549, 551, 555,
   557, 559, 563, 567, 575, 585, 587, 591, 595]

theorem kernel_s11c9_cover_bounds_chunk2 :
    ∀ m ∈ kernelS11C9RepresentativeMasksChunk2,
      kernelS11C9CoverValue (kernelS11C9Row m) ≤ 232 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c9_cover_bounds_chunk2

end Erdos1011
