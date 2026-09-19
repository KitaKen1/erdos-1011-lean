import R5Kernel.Probes.S11C7CoverBoundChunk0
import R5Kernel.Probes.S11C7CoverBoundChunk1
import R5Kernel.Probes.S11C7CoverBoundChunk2
import R5Kernel.Probes.S11C7CoverBoundChunk3
import R5Kernel.Probes.S11C7CoverBoundChunk4
import R5Kernel.Probes.S11C7CoverBoundChunk5
import R5Kernel.Probes.S11C7CoverBoundChunk6
import R5Kernel.Probes.S11C7CoverBoundChunk7
import R5Kernel.Probes.S11C7CoverBoundChunk8
import R5Kernel.Probes.S11C7CoverBoundChunk9
import R5Kernel.Probes.S11C7CoverBoundChunk10
import R5Kernel.Probes.S11C7CoverBoundChunk11

set_option Elab.async false
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000

namespace Erdos1011

theorem kernel_s11c7_cover_masks_partition :
    kernelS11C7RepresentativeMasks =
      kernelS11C7CoverMasksChunk0 ++ (kernelS11C7CoverMasksChunk1 ++ (kernelS11C7CoverMasksChunk2 ++ (kernelS11C7CoverMasksChunk3 ++ (kernelS11C7CoverMasksChunk4 ++ (kernelS11C7CoverMasksChunk5 ++ (kernelS11C7CoverMasksChunk6 ++ (kernelS11C7CoverMasksChunk7 ++ (kernelS11C7CoverMasksChunk8 ++ (kernelS11C7CoverMasksChunk9 ++ (kernelS11C7CoverMasksChunk10 ++ (kernelS11C7CoverMasksChunk11))))))))))) := by
  decide +kernel

theorem kernel_s11c7_all_canonical_cover_bounds :
    ∀ m ∈ kernelS11C7RepresentativeMasks,
      kernelS11C7CoverValue (kernelS11C7Row m) ≤ 516 := by
  intro m hm
  rw [kernel_s11c7_cover_masks_partition] at hm
  rcases List.mem_append.mp hm with hm | hm
  · exact kernel_s11c7_cover_bound_block0 m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact kernel_s11c7_cover_bound_block1 m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact kernel_s11c7_cover_bound_block2 m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact kernel_s11c7_cover_bound_block3 m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact kernel_s11c7_cover_bound_block4 m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact kernel_s11c7_cover_bound_block5 m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact kernel_s11c7_cover_bound_block6 m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact kernel_s11c7_cover_bound_block7 m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact kernel_s11c7_cover_bound_block8 m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact kernel_s11c7_cover_bound_block9 m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact kernel_s11c7_cover_bound_block10 m hm
  exact kernel_s11c7_cover_bound_block11 m hm

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c7_cover_masks_partition
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c7_all_canonical_cover_bounds

end Erdos1011
