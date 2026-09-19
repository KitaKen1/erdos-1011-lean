import R5Kernel.Probes.S11C9Cover

set_option Elab.async false
set_option maxHeartbeats 5000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelS11C9RepresentativeMasksChunk5 : List Nat :=
  [1627, 1629, 1631, 1639, 1643, 1647, 1655, 1663, 1707, 1711, 1719, 1727,
   1755, 1759, 1775, 1791, 2047]

theorem kernel_s11c9_cover_bounds_chunk5 :
    ∀ m ∈ kernelS11C9RepresentativeMasksChunk5,
      kernelS11C9CoverValue (kernelS11C9Row m) ≤ 232 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c9_cover_bounds_chunk5

end Erdos1011
