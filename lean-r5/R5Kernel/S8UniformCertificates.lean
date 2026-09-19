import R5Kernel.S8C5UniformChunk0
import R5Kernel.S8C5UniformChunk1
import R5Kernel.S8C5UniformChunk2
import R5Kernel.S8C5UniformChunk3
import R5Kernel.S8C5UniformChunk4
import R5Kernel.S8C5UniformChunk5
import R5Kernel.S8C5UniformChunk6
import R5Kernel.S8C5UniformChunk7
import R5Kernel.S8C5UniformChunk8
import R5Kernel.S8C5UniformChunk9
import R5Kernel.S8C5UniformChunk10
import R5Kernel.S8C5UniformChunk11
import R5Kernel.S8C5UniformChunk12
import R5Kernel.S8C5UniformChunk13
import R5Kernel.S8C5UniformChunk14
import R5Kernel.S8C5UniformChunk15
import R5Kernel.S8C7UniformChunk0
import R5Kernel.S8C7UniformChunk1
import R5Kernel.S8C7UniformChunk2
import R5Kernel.S8C7UniformChunk3
import R5Kernel.S8C7UniformChunk4
import R5Kernel.S8C7UniformChunk5
import R5Kernel.S8C7UniformChunk6
import R5Kernel.S8C7UniformChunk7
import R5Kernel.S8C7UniformChunk8
import R5Kernel.S8C7UniformChunk9
import R5Kernel.S8C7UniformChunk10
import R5Kernel.S8C7UniformChunk11
import R5Kernel.S8C7UniformChunk12
import R5Kernel.S8C7UniformChunk13
import R5Kernel.S8C7UniformChunk14
import R5Kernel.S8C7UniformChunk15

set_option Elab.async false

namespace Erdos1011

theorem kernel_s8c5_uniform_masks (m : Fin 256) :
    KernelS8C5UniformCertificate m.val := by
  have hm := m.isLt
  by_cases h0 : m.val < 16
  · have hi : m.val - 0 < 16 := by omega
    have heq : m.val - 0 + 0 = m.val := by omega
    simpa only [heq] using
      kernel_s8c5_uniform_chunk0 ⟨m.val - 0, hi⟩
  by_cases h1 : m.val < 32
  · have hi : m.val - 16 < 16 := by omega
    have heq : m.val - 16 + 16 = m.val := by omega
    simpa only [heq] using
      kernel_s8c5_uniform_chunk1 ⟨m.val - 16, hi⟩
  by_cases h2 : m.val < 48
  · have hi : m.val - 32 < 16 := by omega
    have heq : m.val - 32 + 32 = m.val := by omega
    simpa only [heq] using
      kernel_s8c5_uniform_chunk2 ⟨m.val - 32, hi⟩
  by_cases h3 : m.val < 64
  · have hi : m.val - 48 < 16 := by omega
    have heq : m.val - 48 + 48 = m.val := by omega
    simpa only [heq] using
      kernel_s8c5_uniform_chunk3 ⟨m.val - 48, hi⟩
  by_cases h4 : m.val < 80
  · have hi : m.val - 64 < 16 := by omega
    have heq : m.val - 64 + 64 = m.val := by omega
    simpa only [heq] using
      kernel_s8c5_uniform_chunk4 ⟨m.val - 64, hi⟩
  by_cases h5 : m.val < 96
  · have hi : m.val - 80 < 16 := by omega
    have heq : m.val - 80 + 80 = m.val := by omega
    simpa only [heq] using
      kernel_s8c5_uniform_chunk5 ⟨m.val - 80, hi⟩
  by_cases h6 : m.val < 112
  · have hi : m.val - 96 < 16 := by omega
    have heq : m.val - 96 + 96 = m.val := by omega
    simpa only [heq] using
      kernel_s8c5_uniform_chunk6 ⟨m.val - 96, hi⟩
  by_cases h7 : m.val < 128
  · have hi : m.val - 112 < 16 := by omega
    have heq : m.val - 112 + 112 = m.val := by omega
    simpa only [heq] using
      kernel_s8c5_uniform_chunk7 ⟨m.val - 112, hi⟩
  by_cases h8 : m.val < 144
  · have hi : m.val - 128 < 16 := by omega
    have heq : m.val - 128 + 128 = m.val := by omega
    simpa only [heq] using
      kernel_s8c5_uniform_chunk8 ⟨m.val - 128, hi⟩
  by_cases h9 : m.val < 160
  · have hi : m.val - 144 < 16 := by omega
    have heq : m.val - 144 + 144 = m.val := by omega
    simpa only [heq] using
      kernel_s8c5_uniform_chunk9 ⟨m.val - 144, hi⟩
  by_cases h10 : m.val < 176
  · have hi : m.val - 160 < 16 := by omega
    have heq : m.val - 160 + 160 = m.val := by omega
    simpa only [heq] using
      kernel_s8c5_uniform_chunk10 ⟨m.val - 160, hi⟩
  by_cases h11 : m.val < 192
  · have hi : m.val - 176 < 16 := by omega
    have heq : m.val - 176 + 176 = m.val := by omega
    simpa only [heq] using
      kernel_s8c5_uniform_chunk11 ⟨m.val - 176, hi⟩
  by_cases h12 : m.val < 208
  · have hi : m.val - 192 < 16 := by omega
    have heq : m.val - 192 + 192 = m.val := by omega
    simpa only [heq] using
      kernel_s8c5_uniform_chunk12 ⟨m.val - 192, hi⟩
  by_cases h13 : m.val < 224
  · have hi : m.val - 208 < 16 := by omega
    have heq : m.val - 208 + 208 = m.val := by omega
    simpa only [heq] using
      kernel_s8c5_uniform_chunk13 ⟨m.val - 208, hi⟩
  by_cases h14 : m.val < 240
  · have hi : m.val - 224 < 16 := by omega
    have heq : m.val - 224 + 224 = m.val := by omega
    simpa only [heq] using
      kernel_s8c5_uniform_chunk14 ⟨m.val - 224, hi⟩
  have hi : m.val - 240 < 16 := by omega
  have heq : m.val - 240 + 240 = m.val := by omega
  simpa only [heq] using
    kernel_s8c5_uniform_chunk15 ⟨m.val - 240, hi⟩

theorem kernel_s8c5_all_nonempty_uniform_certificates
    (R : Finset (Fin 8)) (_hR : R.Nonempty) :
    ∃ b : ℕ, ∃ w : Fin 8 → ℕ,
      (∀ I ∈ cycleTypes 8 5, I ⊆ R → I.card ≤ b) ∧
      R5Kernel.dualValue (cycleTypes 8 5) R b 2 w ≤ 114 := by
  let m := kernelSmallEncode R
  have hc := kernel_s8c5_uniform_masks m
  dsimp only [KernelS8C5UniformCertificate] at hc
  rw [← kernel_s8c5_uniform_types_eq, kernel_s8_decode_encode R] at hc
  refine ⟨(kernelS8C5UniformRow m.val).1,
    (fun _ => (kernelS8C5UniformRow m.val).2), hc.1, ?_⟩
  rw [kernel_dualValue_uniform]
  exact hc.2

theorem kernel_s8c5_supportSurplus_le_57
    {A B : Finset (Finset (Fin 8))}
    (hAU : A ⊆ cycleTypes 8 5) (hBU : B ⊆ cycleTypes 8 5)
    (hcompat : DegreeCompatible A B) : supportSurplus A B ≤ 57 := by
  have h : 2 * supportSurplus A B ≤ 114 :=
    kernel_supportSurplus_scaled_of_certificates hAU hBU hcompat
      kernel_s8c5_all_nonempty_uniform_certificates
  omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s8c5_uniform_masks
run_cmd R5Kernel.checkStandardAxioms ``kernel_s8c5_all_nonempty_uniform_certificates
run_cmd R5Kernel.checkStandardAxioms ``kernel_s8c5_supportSurplus_le_57

theorem kernel_s8c7_uniform_masks (m : Fin 256) :
    KernelS8C7UniformCertificate m.val := by
  have hm := m.isLt
  by_cases h0 : m.val < 16
  · have hi : m.val - 0 < 16 := by omega
    have heq : m.val - 0 + 0 = m.val := by omega
    simpa only [heq] using
      kernel_s8c7_uniform_chunk0 ⟨m.val - 0, hi⟩
  by_cases h1 : m.val < 32
  · have hi : m.val - 16 < 16 := by omega
    have heq : m.val - 16 + 16 = m.val := by omega
    simpa only [heq] using
      kernel_s8c7_uniform_chunk1 ⟨m.val - 16, hi⟩
  by_cases h2 : m.val < 48
  · have hi : m.val - 32 < 16 := by omega
    have heq : m.val - 32 + 32 = m.val := by omega
    simpa only [heq] using
      kernel_s8c7_uniform_chunk2 ⟨m.val - 32, hi⟩
  by_cases h3 : m.val < 64
  · have hi : m.val - 48 < 16 := by omega
    have heq : m.val - 48 + 48 = m.val := by omega
    simpa only [heq] using
      kernel_s8c7_uniform_chunk3 ⟨m.val - 48, hi⟩
  by_cases h4 : m.val < 80
  · have hi : m.val - 64 < 16 := by omega
    have heq : m.val - 64 + 64 = m.val := by omega
    simpa only [heq] using
      kernel_s8c7_uniform_chunk4 ⟨m.val - 64, hi⟩
  by_cases h5 : m.val < 96
  · have hi : m.val - 80 < 16 := by omega
    have heq : m.val - 80 + 80 = m.val := by omega
    simpa only [heq] using
      kernel_s8c7_uniform_chunk5 ⟨m.val - 80, hi⟩
  by_cases h6 : m.val < 112
  · have hi : m.val - 96 < 16 := by omega
    have heq : m.val - 96 + 96 = m.val := by omega
    simpa only [heq] using
      kernel_s8c7_uniform_chunk6 ⟨m.val - 96, hi⟩
  by_cases h7 : m.val < 128
  · have hi : m.val - 112 < 16 := by omega
    have heq : m.val - 112 + 112 = m.val := by omega
    simpa only [heq] using
      kernel_s8c7_uniform_chunk7 ⟨m.val - 112, hi⟩
  by_cases h8 : m.val < 144
  · have hi : m.val - 128 < 16 := by omega
    have heq : m.val - 128 + 128 = m.val := by omega
    simpa only [heq] using
      kernel_s8c7_uniform_chunk8 ⟨m.val - 128, hi⟩
  by_cases h9 : m.val < 160
  · have hi : m.val - 144 < 16 := by omega
    have heq : m.val - 144 + 144 = m.val := by omega
    simpa only [heq] using
      kernel_s8c7_uniform_chunk9 ⟨m.val - 144, hi⟩
  by_cases h10 : m.val < 176
  · have hi : m.val - 160 < 16 := by omega
    have heq : m.val - 160 + 160 = m.val := by omega
    simpa only [heq] using
      kernel_s8c7_uniform_chunk10 ⟨m.val - 160, hi⟩
  by_cases h11 : m.val < 192
  · have hi : m.val - 176 < 16 := by omega
    have heq : m.val - 176 + 176 = m.val := by omega
    simpa only [heq] using
      kernel_s8c7_uniform_chunk11 ⟨m.val - 176, hi⟩
  by_cases h12 : m.val < 208
  · have hi : m.val - 192 < 16 := by omega
    have heq : m.val - 192 + 192 = m.val := by omega
    simpa only [heq] using
      kernel_s8c7_uniform_chunk12 ⟨m.val - 192, hi⟩
  by_cases h13 : m.val < 224
  · have hi : m.val - 208 < 16 := by omega
    have heq : m.val - 208 + 208 = m.val := by omega
    simpa only [heq] using
      kernel_s8c7_uniform_chunk13 ⟨m.val - 208, hi⟩
  by_cases h14 : m.val < 240
  · have hi : m.val - 224 < 16 := by omega
    have heq : m.val - 224 + 224 = m.val := by omega
    simpa only [heq] using
      kernel_s8c7_uniform_chunk14 ⟨m.val - 224, hi⟩
  have hi : m.val - 240 < 16 := by omega
  have heq : m.val - 240 + 240 = m.val := by omega
  simpa only [heq] using
    kernel_s8c7_uniform_chunk15 ⟨m.val - 240, hi⟩

theorem kernel_s8c7_all_nonempty_uniform_certificates
    (R : Finset (Fin 8)) (_hR : R.Nonempty) :
    ∃ b : ℕ, ∃ w : Fin 8 → ℕ,
      (∀ I ∈ cycleTypes 8 7, I ⊆ R → I.card ≤ b) ∧
      R5Kernel.dualValue (cycleTypes 8 7) R b 2 w ≤ 93 := by
  let m := kernelSmallEncode R
  have hc := kernel_s8c7_uniform_masks m
  dsimp only [KernelS8C7UniformCertificate] at hc
  rw [← kernel_s8c7_uniform_types_eq, kernel_s8_decode_encode R] at hc
  refine ⟨(kernelS8C7UniformRow m.val).1,
    (fun _ => (kernelS8C7UniformRow m.val).2), hc.1, ?_⟩
  rw [kernel_dualValue_uniform]
  exact hc.2

theorem kernel_s8c7_supportSurplus_le_46
    {A B : Finset (Finset (Fin 8))}
    (hAU : A ⊆ cycleTypes 8 7) (hBU : B ⊆ cycleTypes 8 7)
    (hcompat : DegreeCompatible A B) : supportSurplus A B ≤ 46 := by
  have h : 2 * supportSurplus A B ≤ 93 :=
    kernel_supportSurplus_scaled_of_certificates hAU hBU hcompat
      kernel_s8c7_all_nonempty_uniform_certificates
  omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s8c7_uniform_masks
run_cmd R5Kernel.checkStandardAxioms ``kernel_s8c7_all_nonempty_uniform_certificates
run_cmd R5Kernel.checkStandardAxioms ``kernel_s8c7_supportSurplus_le_46

end Erdos1011

