import R5Kernel.Probes.S11C9Cover

set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelS11C9RepresentativeMasksChunk0 : List Nat :=
  [1, 3, 5, 7, 9, 11, 15, 17, 19, 21, 23, 27, 31, 35, 37, 39, 43, 45,
   47, 51, 55, 63, 73, 75]

theorem kernel_s11c9_cover_bounds_chunk0 :
    ∀ m ∈ kernelS11C9RepresentativeMasksChunk0,
      kernelS11C9CoverValue (kernelS11C9Row m) ≤ 232 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c9_cover_bounds_chunk0

end Erdos1011
