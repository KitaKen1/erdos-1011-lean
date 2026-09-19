import R5Kernel.Probes.S11C9OrbitWitnessChunk0
import R5Kernel.Probes.S11C9OrbitWitnessChunk1
import R5Kernel.Probes.S11C9OrbitWitnessChunk2
import R5Kernel.Probes.S11C9OrbitWitnessChunk3

set_option Elab.async false
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000

namespace Erdos1011

theorem kernel_c9_orbit_witness_all (m : Fin 512) :
    KernelC9OrbitWitnessValid m.val := by
  by_cases h0 : m.val < 128
  · have hb := kernel_c9_orbit_witness_block0 ⟨m.val - 0, by omega⟩
    have he : m.val - 0 + 0 = m.val := by omega
    simpa only [he] using hb
  by_cases h1 : m.val < 256
  · have hb := kernel_c9_orbit_witness_block1 ⟨m.val - 128, by omega⟩
    have he : m.val - 128 + 128 = m.val := by omega
    simpa only [he] using hb
  by_cases h2 : m.val < 384
  · have hb := kernel_c9_orbit_witness_block2 ⟨m.val - 256, by omega⟩
    have he : m.val - 256 + 256 = m.val := by omega
    simpa only [he] using hb
  by_cases h3 : m.val < 512
  · have hb := kernel_c9_orbit_witness_block3 ⟨m.val - 384, by omega⟩
    have he : m.val - 384 + 384 = m.val := by omega
    simpa only [he] using hb
  omega

theorem kernel_c9_orbit_witness_coverage (J : Finset (Fin 9)) :
    ∃ c : Fin 512, ∃ d : Fin 18, c.val ∈ kernelC9CanonicalMasks ∧
      (kernelC9SmallMask c.val).map (kernelC9ActionEquiv d).toEmbedding = J := by
  let m := kernelC9OrbitEncode J
  have he : kernelC9SmallMask m.val = J := kernel_c9_orbit_decode_encode J
  have hw := kernel_c9_orbit_witness_all m
  unfold KernelC9OrbitWitnessValid at hw
  rw [he] at hw
  exact ⟨(kernelC9OrbitWitness m.val).1, (kernelC9OrbitWitness m.val).2, hw⟩

run_cmd R5Kernel.checkStandardAxioms ``kernel_c9_orbit_witness_all
run_cmd R5Kernel.checkStandardAxioms ``kernel_c9_orbit_witness_coverage

end Erdos1011
