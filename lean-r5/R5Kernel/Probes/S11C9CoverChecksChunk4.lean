import R5Kernel.Probes.S11C9Cover

set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelS11C9RepresentativeMasksChunk4 : List Nat :=
  [1545, 1547, 1551, 1553, 1555, 1557, 1559, 1563, 1567, 1571, 1573, 1575,
   1579, 1581, 1583, 1587, 1591, 1599, 1609, 1611, 1615, 1619, 1621, 1623]

theorem kernel_s11c9_cover_bounds_chunk4 :
    ∀ m ∈ kernelS11C9RepresentativeMasksChunk4,
      kernelS11C9CoverValue (kernelS11C9Row m) ≤ 232 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c9_cover_bounds_chunk4

end Erdos1011
