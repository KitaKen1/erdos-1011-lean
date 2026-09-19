import R5Kernel.Probes.S11C5CoverBoundChunk0
import R5Kernel.Probes.S11C5CoverBoundChunk1
import R5Kernel.Probes.S11C5CoverBoundChunk2
import R5Kernel.Probes.S11C5CoverBoundChunk3
import R5Kernel.Probes.S11C5CoverBoundChunk4
import R5Kernel.Probes.S11C5CoverBoundChunk5
import R5Kernel.Probes.S11C5CoverBoundChunk6

set_option Elab.async false
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000

namespace Erdos1011

theorem kernel_s11_cover_masks_partition :
    kernelS11RepresentativeMasks =
      kernelS11CoverMasksChunk0 ++ (kernelS11CoverMasksChunk1 ++ (kernelS11CoverMasksChunk2 ++ (kernelS11CoverMasksChunk3 ++ (kernelS11CoverMasksChunk4 ++ (kernelS11CoverMasksChunk5 ++ (kernelS11CoverMasksChunk6)))))) := by
  decide +kernel

theorem kernel_s11_all_canonical_cover_bounds :
    ∀ m ∈ kernelS11RepresentativeMasks,
      kernelS11CoverValue (kernelS11Row m) ≤ 284 := by
  intro m hm
  rw [kernel_s11_cover_masks_partition] at hm
  rcases List.mem_append.mp hm with hm | hm
  · exact kernel_s11_cover_bound_block0 m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact kernel_s11_cover_bound_block1 m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact kernel_s11_cover_bound_block2 m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact kernel_s11_cover_bound_block3 m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact kernel_s11_cover_bound_block4 m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact kernel_s11_cover_bound_block5 m hm
  exact kernel_s11_cover_bound_block6 m hm

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_cover_masks_partition
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_all_canonical_cover_bounds

end Erdos1011
