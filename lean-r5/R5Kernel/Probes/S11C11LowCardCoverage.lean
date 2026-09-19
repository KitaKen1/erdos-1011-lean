import R5Kernel.Probes.S11C11LowCardChunk0
import R5Kernel.Probes.S11C11LowCardChunk1
import R5Kernel.Probes.S11C11LowCardChunk2
import R5Kernel.Probes.S11C11LowCardChunk3
import R5Kernel.Probes.S11C11LowCardChunk4
import R5Kernel.Probes.S11C11LowCardChunk5
import R5Kernel.Probes.S11C11LowCardChunk6
import R5Kernel.Probes.S11C11LowCardChunk7
import R5Kernel.Probes.S11C11LowCardChunk8
import R5Kernel.Probes.S11C11LowCardChunk9
import R5Kernel.Probes.S11C11LowCardChunk10
import R5Kernel.Probes.S11C11LowCardChunk11
import R5Kernel.Probes.S11C11LowCardChunk12
import R5Kernel.Probes.S11C11LowCardChunk13
import R5Kernel.Probes.S11C11LowCardChunk14
import R5Kernel.Probes.S11C11LowCardChunk15

set_option Elab.async false
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000

namespace Erdos1011

theorem kernel_c11_low_witness_all (m : Fin 2048) :
    KernelC11LowCardWitnessValid m.val := by
  by_cases h0 : m.val < 128
  · have hb := kernel_c11_low_witness_block0 ⟨m.val - 0, by omega⟩
    have he : m.val - 0 + 0 = m.val := by omega
    simpa only [he] using hb
  by_cases h1 : m.val < 256
  · have hb := kernel_c11_low_witness_block1 ⟨m.val - 128, by omega⟩
    have he : m.val - 128 + 128 = m.val := by omega
    simpa only [he] using hb
  by_cases h2 : m.val < 384
  · have hb := kernel_c11_low_witness_block2 ⟨m.val - 256, by omega⟩
    have he : m.val - 256 + 256 = m.val := by omega
    simpa only [he] using hb
  by_cases h3 : m.val < 512
  · have hb := kernel_c11_low_witness_block3 ⟨m.val - 384, by omega⟩
    have he : m.val - 384 + 384 = m.val := by omega
    simpa only [he] using hb
  by_cases h4 : m.val < 640
  · have hb := kernel_c11_low_witness_block4 ⟨m.val - 512, by omega⟩
    have he : m.val - 512 + 512 = m.val := by omega
    simpa only [he] using hb
  by_cases h5 : m.val < 768
  · have hb := kernel_c11_low_witness_block5 ⟨m.val - 640, by omega⟩
    have he : m.val - 640 + 640 = m.val := by omega
    simpa only [he] using hb
  by_cases h6 : m.val < 896
  · have hb := kernel_c11_low_witness_block6 ⟨m.val - 768, by omega⟩
    have he : m.val - 768 + 768 = m.val := by omega
    simpa only [he] using hb
  by_cases h7 : m.val < 1024
  · have hb := kernel_c11_low_witness_block7 ⟨m.val - 896, by omega⟩
    have he : m.val - 896 + 896 = m.val := by omega
    simpa only [he] using hb
  by_cases h8 : m.val < 1152
  · have hb := kernel_c11_low_witness_block8 ⟨m.val - 1024, by omega⟩
    have he : m.val - 1024 + 1024 = m.val := by omega
    simpa only [he] using hb
  by_cases h9 : m.val < 1280
  · have hb := kernel_c11_low_witness_block9 ⟨m.val - 1152, by omega⟩
    have he : m.val - 1152 + 1152 = m.val := by omega
    simpa only [he] using hb
  by_cases h10 : m.val < 1408
  · have hb := kernel_c11_low_witness_block10 ⟨m.val - 1280, by omega⟩
    have he : m.val - 1280 + 1280 = m.val := by omega
    simpa only [he] using hb
  by_cases h11 : m.val < 1536
  · have hb := kernel_c11_low_witness_block11 ⟨m.val - 1408, by omega⟩
    have he : m.val - 1408 + 1408 = m.val := by omega
    simpa only [he] using hb
  by_cases h12 : m.val < 1664
  · have hb := kernel_c11_low_witness_block12 ⟨m.val - 1536, by omega⟩
    have he : m.val - 1536 + 1536 = m.val := by omega
    simpa only [he] using hb
  by_cases h13 : m.val < 1792
  · have hb := kernel_c11_low_witness_block13 ⟨m.val - 1664, by omega⟩
    have he : m.val - 1664 + 1664 = m.val := by omega
    simpa only [he] using hb
  by_cases h14 : m.val < 1920
  · have hb := kernel_c11_low_witness_block14 ⟨m.val - 1792, by omega⟩
    have he : m.val - 1792 + 1792 = m.val := by omega
    simpa only [he] using hb
  by_cases h15 : m.val < 2048
  · have hb := kernel_c11_low_witness_block15 ⟨m.val - 1920, by omega⟩
    have he : m.val - 1920 + 1920 = m.val := by omega
    simpa only [he] using hb
  omega

theorem kernel_c11_low_card_coverage (J : Finset (Fin 11)) (hJ : J.card ≤ 5) :
    ∃ c : Fin 125, ∃ d : Fin 22,
      (kernelC11SmallMask (kernelC11CanonicalRep c).val).map
        (kernelC11ActionEquiv d).toEmbedding = J := by
  let m := kernelC11LowEncode J
  have he : kernelC11SmallMask m.val = J := kernel_c11_low_decode_encode J
  have hw := kernel_c11_low_witness_all m
  unfold KernelC11LowCardWitnessValid at hw
  rw [he] at hw
  exact ⟨(kernelC11LowCardWitness m.val).1, (kernelC11LowCardWitness m.val).2, hw hJ⟩

run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_low_witness_all
run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_low_card_coverage

end Erdos1011
