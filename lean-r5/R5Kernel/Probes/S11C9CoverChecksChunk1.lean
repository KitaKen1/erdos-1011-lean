import R5Kernel.Probes.S11C9Cover

set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelS11C9RepresentativeMasksChunk1 : List Nat :=
  [79, 83, 85, 87, 91, 93, 95, 103, 107, 111, 119, 127, 171, 175, 183, 191,
   219, 223, 239, 255, 511, 512, 513, 515]

theorem kernel_s11c9_cover_bounds_chunk1 :
    ∀ m ∈ kernelS11C9RepresentativeMasksChunk1,
      kernelS11C9CoverValue (kernelS11C9Row m) ≤ 232 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c9_cover_bounds_chunk1

end Erdos1011
