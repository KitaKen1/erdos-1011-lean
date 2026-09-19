import R5Kernel.Probes.S11C9OrbitDefinitions

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace Erdos1011

theorem kernel_c9_iso_prefix_card : ∀ k : Fin 3,
    (kernelC9IsoPrefix k).card = k.val := by
  decide +kernel

theorem kernel_s11c9_packed_shapes : ∀ c : Fin 512,
    c.val ∈ kernelC9CanonicalMasks → ∀ k : Fin 3,
      r5RepMaskSet11C9 (kernelS11C9Pack c k) =
        kernelC9JoinParts (kernelC9SmallMask c.val, kernelC9IsoPrefix k) ∧
      ((kernelS11C9Pack c k).val ∈ kernelS11C9RepresentativeMasks ∨
        kernelS11C9Pack c k = 0) := by
  decide +kernel

theorem kernel_s11c9_zero_mask : r5RepMaskSet11C9 0 = ∅ := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_c9_iso_prefix_card
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c9_packed_shapes

end Erdos1011
