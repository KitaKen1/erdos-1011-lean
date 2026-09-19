import R5Kernel.Probes.S11C9CoverChecksChunk0
import R5Kernel.Probes.S11C9CoverChecksChunk1
import R5Kernel.Probes.S11C9CoverChecksChunk2
import R5Kernel.Probes.S11C9CoverChecksChunk3
import R5Kernel.Probes.S11C9CoverChecksChunk4
import R5Kernel.Probes.S11C9CoverChecksChunk5

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

namespace Erdos1011

theorem kernel_s11c9_representative_masks_partition :
    kernelS11C9RepresentativeMasks =
      kernelS11C9RepresentativeMasksChunk0 ++
      (kernelS11C9RepresentativeMasksChunk1 ++
        (kernelS11C9RepresentativeMasksChunk2 ++
          (kernelS11C9RepresentativeMasksChunk3 ++
            (kernelS11C9RepresentativeMasksChunk4 ++
              kernelS11C9RepresentativeMasksChunk5)))) := by
  decide +kernel

theorem kernel_s11c9_all_canonical_cover_bounds :
    ∀ m ∈ kernelS11C9RepresentativeMasks,
      kernelS11C9CoverValue (kernelS11C9Row m) ≤ 232 := by
  intro m hm
  rw [kernel_s11c9_representative_masks_partition] at hm
  rcases List.mem_append.mp hm with hm | hm
  · exact kernel_s11c9_cover_bounds_chunk0 m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact kernel_s11c9_cover_bounds_chunk1 m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact kernel_s11c9_cover_bounds_chunk2 m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact kernel_s11c9_cover_bounds_chunk3 m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact kernel_s11c9_cover_bounds_chunk4 m hm
  · exact kernel_s11c9_cover_bounds_chunk5 m hm

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c9_representative_masks_partition
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c9_all_canonical_cover_bounds

end Erdos1011
