import R5Kernel.Probes.S11C9Cover

set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelS11C9RepresentativeMasksChunk3 : List Nat :=
  [597, 599, 603, 605, 607, 615, 619, 623, 631, 639, 683, 687, 695, 703, 731,
   735, 751, 767, 1023, 1536, 1537, 1539, 1541, 1543]

theorem kernel_s11c9_cover_bounds_chunk3 :
    ∀ m ∈ kernelS11C9RepresentativeMasksChunk3,
      kernelS11C9CoverValue (kernelS11C9Row m) ≤ 232 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c9_cover_bounds_chunk3

end Erdos1011
