import R5Kernel.R5TypeChunks
import R5Kernel.SmallUniform
import R5Kernel.Probes.CycleSurplusBridge
import R5Kernel.S9C5TypeMaskChunk0
import R5Kernel.S9C5TypeMaskChunk1
import R5Kernel.S9C5TypeMaskChunk2
import R5Kernel.S9C5TypeMaskChunk3
import R5Kernel.S9C5TypeMaskChunk4
import R5Kernel.S9C5TypeMaskChunk5
import R5Kernel.S9C5TypeMaskChunk6
import R5Kernel.S9C5TypeMaskChunk7
import R5Kernel.S9C5TypeMaskChunk8
import R5Kernel.S9C5TypeMaskChunk9
import R5Kernel.S9C5TypeMaskChunk10
import R5Kernel.S9C5TypeMaskChunk11
import R5Kernel.S9C5TypeMaskChunk12
import R5Kernel.S9C5TypeMaskChunk13
import R5Kernel.S9C5TypeMaskChunk14
import R5Kernel.S9C5TypeMaskChunk15
import R5Kernel.S9C5TypeMaskChunk16
import R5Kernel.S9C5TypeMaskChunk17
import R5Kernel.S9C5TypeMaskChunk18
import R5Kernel.S9C5TypeMaskChunk19
import R5Kernel.S9C5TypeMaskChunk20
import R5Kernel.S9C5TypeMaskChunk21
import R5Kernel.S9C5TypeMaskChunk22
import R5Kernel.S9C5TypeMaskChunk23
import R5Kernel.S9C5TypeMaskChunk24
import R5Kernel.S9C5TypeMaskChunk25
import R5Kernel.S9C5TypeMaskChunk26
import R5Kernel.S9C5TypeMaskChunk27
import R5Kernel.S9C5TypeMaskChunk28
import R5Kernel.S9C5TypeMaskChunk29
import R5Kernel.S9C5TypeMaskChunk30
import R5Kernel.S9C5TypeMaskChunk31
import R5Kernel.S9C7TypeMaskChunk0
import R5Kernel.S9C7TypeMaskChunk1
import R5Kernel.S9C7TypeMaskChunk2
import R5Kernel.S9C7TypeMaskChunk3
import R5Kernel.S9C7TypeMaskChunk4
import R5Kernel.S9C7TypeMaskChunk5
import R5Kernel.S9C7TypeMaskChunk6
import R5Kernel.S9C7TypeMaskChunk7
import R5Kernel.S9C7TypeMaskChunk8
import R5Kernel.S9C7TypeMaskChunk9
import R5Kernel.S9C7TypeMaskChunk10
import R5Kernel.S9C7TypeMaskChunk11
import R5Kernel.S9C7TypeMaskChunk12
import R5Kernel.S9C7TypeMaskChunk13
import R5Kernel.S9C7TypeMaskChunk14
import R5Kernel.S9C7TypeMaskChunk15
import R5Kernel.S9C7TypeMaskChunk16
import R5Kernel.S9C7TypeMaskChunk17
import R5Kernel.S9C7TypeMaskChunk18
import R5Kernel.S9C7TypeMaskChunk19
import R5Kernel.S9C7TypeMaskChunk20
import R5Kernel.S9C7TypeMaskChunk21
import R5Kernel.S9C7TypeMaskChunk22
import R5Kernel.S9C7TypeMaskChunk23
import R5Kernel.S9C7TypeMaskChunk24
import R5Kernel.S9C7TypeMaskChunk25
import R5Kernel.S9C7TypeMaskChunk26
import R5Kernel.S9C7TypeMaskChunk27
import R5Kernel.S9C7TypeMaskChunk28
import R5Kernel.S9C7TypeMaskChunk29
import R5Kernel.S9C7TypeMaskChunk30
import R5Kernel.S9C7TypeMaskChunk31
import R5Kernel.S9C9TypeMaskChunk0
import R5Kernel.S9C9TypeMaskChunk1
import R5Kernel.S9C9TypeMaskChunk2
import R5Kernel.S9C9TypeMaskChunk3
import R5Kernel.S9C9TypeMaskChunk4
import R5Kernel.S9C9TypeMaskChunk5
import R5Kernel.S9C9TypeMaskChunk6
import R5Kernel.S9C9TypeMaskChunk7
import R5Kernel.S9C9TypeMaskChunk8
import R5Kernel.S9C9TypeMaskChunk9
import R5Kernel.S9C9TypeMaskChunk10
import R5Kernel.S9C9TypeMaskChunk11
import R5Kernel.S9C9TypeMaskChunk12
import R5Kernel.S9C9TypeMaskChunk13
import R5Kernel.S9C9TypeMaskChunk14
import R5Kernel.S9C9TypeMaskChunk15
import R5Kernel.S9C9TypeMaskChunk16
import R5Kernel.S9C9TypeMaskChunk17
import R5Kernel.S9C9TypeMaskChunk18
import R5Kernel.S9C9TypeMaskChunk19
import R5Kernel.S9C9TypeMaskChunk20
import R5Kernel.S9C9TypeMaskChunk21
import R5Kernel.S9C9TypeMaskChunk22
import R5Kernel.S9C9TypeMaskChunk23
import R5Kernel.S9C9TypeMaskChunk24
import R5Kernel.S9C9TypeMaskChunk25
import R5Kernel.S9C9TypeMaskChunk26
import R5Kernel.S9C9TypeMaskChunk27
import R5Kernel.S9C9TypeMaskChunk28
import R5Kernel.S9C9TypeMaskChunk29
import R5Kernel.S9C9TypeMaskChunk30
import R5Kernel.S9C9TypeMaskChunk31

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 30000000
set_option maxRecDepth 200000

namespace Erdos1011
open scoped BigOperators

theorem kernel_s9c5_type_chunks_union :
    kernelS9C5UniformTypes = kernelS9C5TypeChunk0 ∪ kernelS9C5TypeChunk1 ∪ kernelS9C5TypeChunk2 ∪ kernelS9C5TypeChunk3 ∪ kernelS9C5TypeChunk4 ∪ kernelS9C5TypeChunk5 := by
  decide +kernel

theorem kernel_s9c5_sum_decomp (R : Finset (Fin 9)) (w : ℕ) :
    (∑ I ∈ kernelS9C5UniformTypes, if (I ∩ R).Nonempty then
      2 * I.card - (I ∩ R).card * w else 0) =
      (∑ I ∈ kernelS9C5TypeChunk0, if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * w else 0) +
      (∑ I ∈ kernelS9C5TypeChunk1, if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * w else 0) +
      (∑ I ∈ kernelS9C5TypeChunk2, if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * w else 0) +
      (∑ I ∈ kernelS9C5TypeChunk3, if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * w else 0) +
      (∑ I ∈ kernelS9C5TypeChunk4, if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * w else 0) +
      (∑ I ∈ kernelS9C5TypeChunk5, if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * w else 0) := by
  rw [kernel_s9c5_type_chunks_union]
  repeat rw [Finset.sum_union]
  all_goals decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_type_chunks_union
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_sum_decomp

theorem kernel_s9c5_block0_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 0)).1 *
        ((kernelSmallMask 9 (i.val + 0)).card *
          (kernelS9C5UniformRow (i.val + 0)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 0, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block0 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 0) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk0_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk0_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk0_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk0_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk0_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk0_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk0_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk0_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk0_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk0_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk0_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk0_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block0_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 0, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 0, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 0, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 0, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 0, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 0, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 0, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    have hsum' :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val, by omega⟩))))) := by
      simpa only [Nat.add_zero] using hsum
    rw [hsum'] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block0_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block0

theorem kernel_s9c5_block1_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 16)).1 *
        ((kernelSmallMask 9 (i.val + 16)).card *
          (kernelS9C5UniformRow (i.val + 16)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 16, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block1 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 16) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk1_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk1_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk1_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk1_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk1_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk1_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk1_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk1_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk1_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk1_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk1_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk1_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block1_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 16, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 16, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 16, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 16, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 16, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 16, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 16, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block1_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block1

theorem kernel_s9c5_block2_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 32)).1 *
        ((kernelSmallMask 9 (i.val + 32)).card *
          (kernelS9C5UniformRow (i.val + 32)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 32, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block2 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 32) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk2_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk2_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk2_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk2_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk2_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk2_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk2_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk2_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk2_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk2_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk2_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk2_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block2_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 32, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 32, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 32, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 32, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 32, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 32, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 32, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block2_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block2

theorem kernel_s9c5_block3_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 48)).1 *
        ((kernelSmallMask 9 (i.val + 48)).card *
          (kernelS9C5UniformRow (i.val + 48)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 48, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block3 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 48) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk3_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk3_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk3_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk3_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk3_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk3_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk3_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk3_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk3_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk3_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk3_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk3_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block3_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 48, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 48, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 48, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 48, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 48, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 48, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 48, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block3_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block3

theorem kernel_s9c5_block4_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 64)).1 *
        ((kernelSmallMask 9 (i.val + 64)).card *
          (kernelS9C5UniformRow (i.val + 64)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 64, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block4 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 64) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk4_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk4_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk4_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk4_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk4_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk4_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk4_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk4_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk4_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk4_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk4_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk4_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block4_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 64, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 64, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 64, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 64, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 64, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 64, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 64, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block4_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block4

theorem kernel_s9c5_block5_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 80)).1 *
        ((kernelSmallMask 9 (i.val + 80)).card *
          (kernelS9C5UniformRow (i.val + 80)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 80, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block5 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 80) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk5_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk5_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk5_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk5_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk5_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk5_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk5_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk5_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk5_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk5_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk5_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk5_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block5_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 80, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 80, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 80, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 80, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 80, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 80, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 80, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block5_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block5

theorem kernel_s9c5_block6_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 96)).1 *
        ((kernelSmallMask 9 (i.val + 96)).card *
          (kernelS9C5UniformRow (i.val + 96)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 96, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block6 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 96) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk6_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk6_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk6_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk6_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk6_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk6_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk6_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk6_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk6_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk6_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk6_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk6_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block6_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 96, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 96, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 96, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 96, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 96, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 96, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 96, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block6_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block6

theorem kernel_s9c5_block7_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 112)).1 *
        ((kernelSmallMask 9 (i.val + 112)).card *
          (kernelS9C5UniformRow (i.val + 112)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 112, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block7 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 112) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk7_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk7_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk7_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk7_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk7_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk7_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk7_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk7_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk7_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk7_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk7_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk7_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block7_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 112, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 112, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 112, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 112, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 112, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 112, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 112, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block7_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block7

theorem kernel_s9c5_block8_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 128)).1 *
        ((kernelSmallMask 9 (i.val + 128)).card *
          (kernelS9C5UniformRow (i.val + 128)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 128, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block8 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 128) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk8_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk8_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk8_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk8_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk8_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk8_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk8_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk8_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk8_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk8_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk8_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk8_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block8_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 128, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 128, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 128, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 128, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 128, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 128, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 128, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block8_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block8

theorem kernel_s9c5_block9_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 144)).1 *
        ((kernelSmallMask 9 (i.val + 144)).card *
          (kernelS9C5UniformRow (i.val + 144)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 144, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block9 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 144) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk9_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk9_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk9_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk9_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk9_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk9_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk9_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk9_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk9_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk9_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk9_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk9_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block9_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 144, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 144, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 144, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 144, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 144, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 144, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 144, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block9_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block9

theorem kernel_s9c5_block10_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 160)).1 *
        ((kernelSmallMask 9 (i.val + 160)).card *
          (kernelS9C5UniformRow (i.val + 160)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 160, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block10 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 160) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk10_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk10_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk10_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk10_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk10_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk10_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk10_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk10_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk10_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk10_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk10_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk10_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block10_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 160, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 160, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 160, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 160, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 160, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 160, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 160, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block10_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block10

theorem kernel_s9c5_block11_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 176)).1 *
        ((kernelSmallMask 9 (i.val + 176)).card *
          (kernelS9C5UniformRow (i.val + 176)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 176, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block11 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 176) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk11_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk11_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk11_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk11_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk11_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk11_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk11_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk11_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk11_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk11_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk11_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk11_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block11_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 176, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 176, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 176, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 176, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 176, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 176, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 176, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block11_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block11

theorem kernel_s9c5_block12_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 192)).1 *
        ((kernelSmallMask 9 (i.val + 192)).card *
          (kernelS9C5UniformRow (i.val + 192)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 192, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block12 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 192) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk12_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk12_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk12_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk12_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk12_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk12_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk12_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk12_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk12_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk12_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk12_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk12_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block12_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 192, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 192, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 192, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 192, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 192, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 192, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 192, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block12_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block12

theorem kernel_s9c5_block13_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 208)).1 *
        ((kernelSmallMask 9 (i.val + 208)).card *
          (kernelS9C5UniformRow (i.val + 208)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 208, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block13 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 208) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk13_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk13_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk13_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk13_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk13_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk13_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk13_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk13_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk13_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk13_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk13_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk13_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block13_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 208, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 208, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 208, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 208, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 208, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 208, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 208, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block13_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block13

theorem kernel_s9c5_block14_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 224)).1 *
        ((kernelSmallMask 9 (i.val + 224)).card *
          (kernelS9C5UniformRow (i.val + 224)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 224, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block14 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 224) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk14_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk14_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk14_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk14_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk14_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk14_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk14_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk14_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk14_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk14_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk14_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk14_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block14_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 224, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 224, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 224, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 224, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 224, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 224, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 224, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block14_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block14

theorem kernel_s9c5_block15_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 240)).1 *
        ((kernelSmallMask 9 (i.val + 240)).card *
          (kernelS9C5UniformRow (i.val + 240)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 240, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block15 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 240) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk15_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk15_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk15_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk15_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk15_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk15_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk15_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk15_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk15_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk15_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk15_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk15_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block15_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 240, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 240, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 240, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 240, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 240, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 240, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 240, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block15_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block15

theorem kernel_s9c5_block16_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 256)).1 *
        ((kernelSmallMask 9 (i.val + 256)).card *
          (kernelS9C5UniformRow (i.val + 256)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 256, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block16 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 256) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk16_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk16_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk16_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk16_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk16_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk16_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk16_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk16_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk16_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk16_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk16_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk16_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block16_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 256, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 256, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 256, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 256, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 256, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 256, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 256, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block16_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block16

theorem kernel_s9c5_block17_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 272)).1 *
        ((kernelSmallMask 9 (i.val + 272)).card *
          (kernelS9C5UniformRow (i.val + 272)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 272, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block17 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 272) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk17_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk17_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk17_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk17_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk17_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk17_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk17_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk17_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk17_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk17_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk17_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk17_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block17_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 272, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 272, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 272, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 272, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 272, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 272, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 272, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block17_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block17

theorem kernel_s9c5_block18_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 288)).1 *
        ((kernelSmallMask 9 (i.val + 288)).card *
          (kernelS9C5UniformRow (i.val + 288)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 288, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block18 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 288) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk18_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk18_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk18_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk18_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk18_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk18_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk18_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk18_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk18_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk18_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk18_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk18_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block18_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 288, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 288, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 288, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 288, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 288, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 288, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 288, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block18_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block18

theorem kernel_s9c5_block19_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 304)).1 *
        ((kernelSmallMask 9 (i.val + 304)).card *
          (kernelS9C5UniformRow (i.val + 304)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 304, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block19 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 304) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk19_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk19_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk19_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk19_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk19_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk19_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk19_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk19_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk19_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk19_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk19_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk19_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block19_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 304, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 304, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 304, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 304, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 304, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 304, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 304, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block19_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block19

theorem kernel_s9c5_block20_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 320)).1 *
        ((kernelSmallMask 9 (i.val + 320)).card *
          (kernelS9C5UniformRow (i.val + 320)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 320, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block20 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 320) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk20_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk20_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk20_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk20_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk20_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk20_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk20_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk20_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk20_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk20_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk20_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk20_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block20_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 320, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 320, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 320, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 320, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 320, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 320, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 320, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block20_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block20

theorem kernel_s9c5_block21_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 336)).1 *
        ((kernelSmallMask 9 (i.val + 336)).card *
          (kernelS9C5UniformRow (i.val + 336)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 336, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block21 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 336) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk21_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk21_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk21_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk21_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk21_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk21_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk21_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk21_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk21_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk21_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk21_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk21_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block21_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 336, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 336, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 336, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 336, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 336, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 336, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 336, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block21_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block21

theorem kernel_s9c5_block22_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 352)).1 *
        ((kernelSmallMask 9 (i.val + 352)).card *
          (kernelS9C5UniformRow (i.val + 352)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 352, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block22 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 352) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk22_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk22_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk22_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk22_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk22_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk22_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk22_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk22_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk22_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk22_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk22_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk22_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block22_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 352, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 352, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 352, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 352, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 352, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 352, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 352, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block22_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block22

theorem kernel_s9c5_block23_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 368)).1 *
        ((kernelSmallMask 9 (i.val + 368)).card *
          (kernelS9C5UniformRow (i.val + 368)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 368, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block23 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 368) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk23_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk23_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk23_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk23_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk23_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk23_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk23_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk23_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk23_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk23_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk23_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk23_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block23_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 368, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 368, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 368, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 368, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 368, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 368, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 368, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block23_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block23

theorem kernel_s9c5_block24_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 384)).1 *
        ((kernelSmallMask 9 (i.val + 384)).card *
          (kernelS9C5UniformRow (i.val + 384)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 384, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block24 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 384) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk24_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk24_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk24_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk24_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk24_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk24_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk24_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk24_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk24_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk24_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk24_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk24_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block24_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 384, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 384, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 384, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 384, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 384, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 384, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 384, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block24_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block24

theorem kernel_s9c5_block25_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 400)).1 *
        ((kernelSmallMask 9 (i.val + 400)).card *
          (kernelS9C5UniformRow (i.val + 400)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 400, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block25 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 400) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk25_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk25_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk25_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk25_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk25_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk25_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk25_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk25_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk25_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk25_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk25_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk25_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block25_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 400, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 400, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 400, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 400, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 400, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 400, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 400, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block25_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block25

theorem kernel_s9c5_block26_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 416)).1 *
        ((kernelSmallMask 9 (i.val + 416)).card *
          (kernelS9C5UniformRow (i.val + 416)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 416, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block26 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 416) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk26_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk26_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk26_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk26_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk26_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk26_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk26_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk26_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk26_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk26_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk26_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk26_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block26_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 416, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 416, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 416, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 416, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 416, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 416, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 416, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block26_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block26

theorem kernel_s9c5_block27_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 432)).1 *
        ((kernelSmallMask 9 (i.val + 432)).card *
          (kernelS9C5UniformRow (i.val + 432)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 432, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block27 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 432) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk27_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk27_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk27_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk27_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk27_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk27_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk27_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk27_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk27_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk27_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk27_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk27_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block27_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 432, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 432, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 432, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 432, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 432, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 432, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 432, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block27_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block27

theorem kernel_s9c5_block28_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 448)).1 *
        ((kernelSmallMask 9 (i.val + 448)).card *
          (kernelS9C5UniformRow (i.val + 448)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 448, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block28 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 448) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk28_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk28_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk28_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk28_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk28_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk28_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk28_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk28_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk28_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk28_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk28_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk28_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block28_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 448, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 448, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 448, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 448, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 448, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 448, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 448, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block28_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block28

theorem kernel_s9c5_block29_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 464)).1 *
        ((kernelSmallMask 9 (i.val + 464)).card *
          (kernelS9C5UniformRow (i.val + 464)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 464, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block29 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 464) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk29_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk29_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk29_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk29_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk29_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk29_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk29_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk29_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk29_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk29_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk29_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk29_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block29_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 464, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 464, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 464, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 464, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 464, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 464, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 464, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block29_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block29

theorem kernel_s9c5_block30_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 480)).1 *
        ((kernelSmallMask 9 (i.val + 480)).card *
          (kernelS9C5UniformRow (i.val + 480)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 480, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block30 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 480) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk30_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk30_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk30_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk30_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk30_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk30_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk30_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk30_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk30_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk30_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk30_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk30_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block30_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 480, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 480, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 480, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 480, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 480, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 480, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 480, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block30_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block30

theorem kernel_s9c5_block31_arithmetic : ∀ i : Fin 16,
    (kernelS9C5UniformRow (i.val + 496)).1 *
        ((kernelSmallMask 9 (i.val + 496)).card *
          (kernelS9C5UniformRow (i.val + 496)).2) +
      ∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 496, by omega⟩ ≤ 164 := by
  decide +kernel

theorem kernel_s9c5_uniform_block31 (i : Fin 16) :
    KernelS9C5UniformCertificate (i.val + 496) := by
  dsimp [KernelS9C5UniformCertificate]
  have hb0 := kernel_s9c5_type_mask_chunk31_direct_beta0 i
  have hs0 := kernel_s9c5_type_mask_chunk31_sum0 i
  have hb1 := kernel_s9c5_type_mask_chunk31_direct_beta1 i
  have hs1 := kernel_s9c5_type_mask_chunk31_sum1 i
  have hb2 := kernel_s9c5_type_mask_chunk31_direct_beta2 i
  have hs2 := kernel_s9c5_type_mask_chunk31_sum2 i
  have hb3 := kernel_s9c5_type_mask_chunk31_direct_beta3 i
  have hs3 := kernel_s9c5_type_mask_chunk31_sum3 i
  have hb4 := kernel_s9c5_type_mask_chunk31_direct_beta4 i
  have hs4 := kernel_s9c5_type_mask_chunk31_sum4 i
  have hb5 := kernel_s9c5_type_mask_chunk31_direct_beta5 i
  have hs5 := kernel_s9c5_type_mask_chunk31_sum5 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c5_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C5TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C5TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C5TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C5TypeChunk3
          · exact hb3 I h3 hsub
          · by_cases h4 : I ∈ kernelS9C5TypeChunk4
            · exact hb4 I h4 hsub
            · by_cases h5 : I ∈ kernelS9C5TypeChunk5
              · exact hb5 I h5 hsub
              · simp [Finset.mem_union, h0, h1, h2, h3, h4, h5] at hI
  · rw [kernel_s9c5_sum_decomp]
    have ha := kernel_s9c5_block31_arithmetic i
    have hsum :
        (∑ j : Fin 6, kernelS9C5PartialBound j ⟨i.val + 496, by omega⟩) =
          kernelS9C5PartialBound 0 ⟨i.val + 496, by omega⟩ +
          (kernelS9C5PartialBound 1 ⟨i.val + 496, by omega⟩ +
          (kernelS9C5PartialBound 2 ⟨i.val + 496, by omega⟩ +
          (kernelS9C5PartialBound 3 ⟨i.val + 496, by omega⟩ +
          (kernelS9C5PartialBound 4 ⟨i.val + 496, by omega⟩ +
          (kernelS9C5PartialBound 5 ⟨i.val + 496, by omega⟩))))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 hs4 hs5 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_block31_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_block31

theorem kernel_s9c5_uniform_masks (m : Fin 512) :
    KernelS9C5UniformCertificate m.val := by
  have hm := m.isLt
  by_cases h0 : m.val < 16
  · have hi : m.val - 0 < 16 := by omega
    have heq : m.val - 0 + 0 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block0 ⟨m.val - 0, hi⟩
  by_cases h1 : m.val < 32
  · have hi : m.val - 16 < 16 := by omega
    have heq : m.val - 16 + 16 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block1 ⟨m.val - 16, hi⟩
  by_cases h2 : m.val < 48
  · have hi : m.val - 32 < 16 := by omega
    have heq : m.val - 32 + 32 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block2 ⟨m.val - 32, hi⟩
  by_cases h3 : m.val < 64
  · have hi : m.val - 48 < 16 := by omega
    have heq : m.val - 48 + 48 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block3 ⟨m.val - 48, hi⟩
  by_cases h4 : m.val < 80
  · have hi : m.val - 64 < 16 := by omega
    have heq : m.val - 64 + 64 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block4 ⟨m.val - 64, hi⟩
  by_cases h5 : m.val < 96
  · have hi : m.val - 80 < 16 := by omega
    have heq : m.val - 80 + 80 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block5 ⟨m.val - 80, hi⟩
  by_cases h6 : m.val < 112
  · have hi : m.val - 96 < 16 := by omega
    have heq : m.val - 96 + 96 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block6 ⟨m.val - 96, hi⟩
  by_cases h7 : m.val < 128
  · have hi : m.val - 112 < 16 := by omega
    have heq : m.val - 112 + 112 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block7 ⟨m.val - 112, hi⟩
  by_cases h8 : m.val < 144
  · have hi : m.val - 128 < 16 := by omega
    have heq : m.val - 128 + 128 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block8 ⟨m.val - 128, hi⟩
  by_cases h9 : m.val < 160
  · have hi : m.val - 144 < 16 := by omega
    have heq : m.val - 144 + 144 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block9 ⟨m.val - 144, hi⟩
  by_cases h10 : m.val < 176
  · have hi : m.val - 160 < 16 := by omega
    have heq : m.val - 160 + 160 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block10 ⟨m.val - 160, hi⟩
  by_cases h11 : m.val < 192
  · have hi : m.val - 176 < 16 := by omega
    have heq : m.val - 176 + 176 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block11 ⟨m.val - 176, hi⟩
  by_cases h12 : m.val < 208
  · have hi : m.val - 192 < 16 := by omega
    have heq : m.val - 192 + 192 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block12 ⟨m.val - 192, hi⟩
  by_cases h13 : m.val < 224
  · have hi : m.val - 208 < 16 := by omega
    have heq : m.val - 208 + 208 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block13 ⟨m.val - 208, hi⟩
  by_cases h14 : m.val < 240
  · have hi : m.val - 224 < 16 := by omega
    have heq : m.val - 224 + 224 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block14 ⟨m.val - 224, hi⟩
  by_cases h15 : m.val < 256
  · have hi : m.val - 240 < 16 := by omega
    have heq : m.val - 240 + 240 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block15 ⟨m.val - 240, hi⟩
  by_cases h16 : m.val < 272
  · have hi : m.val - 256 < 16 := by omega
    have heq : m.val - 256 + 256 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block16 ⟨m.val - 256, hi⟩
  by_cases h17 : m.val < 288
  · have hi : m.val - 272 < 16 := by omega
    have heq : m.val - 272 + 272 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block17 ⟨m.val - 272, hi⟩
  by_cases h18 : m.val < 304
  · have hi : m.val - 288 < 16 := by omega
    have heq : m.val - 288 + 288 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block18 ⟨m.val - 288, hi⟩
  by_cases h19 : m.val < 320
  · have hi : m.val - 304 < 16 := by omega
    have heq : m.val - 304 + 304 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block19 ⟨m.val - 304, hi⟩
  by_cases h20 : m.val < 336
  · have hi : m.val - 320 < 16 := by omega
    have heq : m.val - 320 + 320 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block20 ⟨m.val - 320, hi⟩
  by_cases h21 : m.val < 352
  · have hi : m.val - 336 < 16 := by omega
    have heq : m.val - 336 + 336 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block21 ⟨m.val - 336, hi⟩
  by_cases h22 : m.val < 368
  · have hi : m.val - 352 < 16 := by omega
    have heq : m.val - 352 + 352 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block22 ⟨m.val - 352, hi⟩
  by_cases h23 : m.val < 384
  · have hi : m.val - 368 < 16 := by omega
    have heq : m.val - 368 + 368 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block23 ⟨m.val - 368, hi⟩
  by_cases h24 : m.val < 400
  · have hi : m.val - 384 < 16 := by omega
    have heq : m.val - 384 + 384 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block24 ⟨m.val - 384, hi⟩
  by_cases h25 : m.val < 416
  · have hi : m.val - 400 < 16 := by omega
    have heq : m.val - 400 + 400 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block25 ⟨m.val - 400, hi⟩
  by_cases h26 : m.val < 432
  · have hi : m.val - 416 < 16 := by omega
    have heq : m.val - 416 + 416 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block26 ⟨m.val - 416, hi⟩
  by_cases h27 : m.val < 448
  · have hi : m.val - 432 < 16 := by omega
    have heq : m.val - 432 + 432 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block27 ⟨m.val - 432, hi⟩
  by_cases h28 : m.val < 464
  · have hi : m.val - 448 < 16 := by omega
    have heq : m.val - 448 + 448 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block28 ⟨m.val - 448, hi⟩
  by_cases h29 : m.val < 480
  · have hi : m.val - 464 < 16 := by omega
    have heq : m.val - 464 + 464 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block29 ⟨m.val - 464, hi⟩
  by_cases h30 : m.val < 496
  · have hi : m.val - 480 < 16 := by omega
    have heq : m.val - 480 + 480 = m.val := by omega
    simpa only [heq] using
      kernel_s9c5_uniform_block30 ⟨m.val - 480, hi⟩
  have hi : m.val - 496 < 16 := by omega
  have heq : m.val - 496 + 496 = m.val := by omega
  simpa only [heq] using
    kernel_s9c5_uniform_block31 ⟨m.val - 496, hi⟩

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_uniform_masks

theorem kernel_s9c5_all_nonempty_uniform_certificates
    (R : Finset (Fin 9)) (_hR : R.Nonempty) :
    ∃ b : ℕ, ∃ w : Fin 9 → ℕ,
      (∀ I ∈ cycleTypes 9 5, I ⊆ R → I.card ≤ b) ∧
      R5Kernel.dualValue (cycleTypes 9 5) R b 2 w ≤ 164 := by
  let m := kernelSmallEncode R
  have hc := kernel_s9c5_uniform_masks m
  dsimp only [KernelS9C5UniformCertificate] at hc
  rw [← kernel_s9c5_uniform_types_eq, kernel_s9_decode_encode R] at hc
  refine ⟨(kernelS9C5UniformRow m.val).1,
    (fun _ => (kernelS9C5UniformRow m.val).2), hc.1, ?_⟩
  rw [kernel_dualValue_uniform]
  exact hc.2

theorem kernel_s9c5_supportSurplus_le_82
    {A B : Finset (Finset (Fin 9))}
    (hAU : A ⊆ cycleTypes 9 5) (hBU : B ⊆ cycleTypes 9 5)
    (hcompat : DegreeCompatible A B) : supportSurplus A B ≤ 82 := by
  have h : 2 * supportSurplus A B ≤ 164 :=
    kernel_supportSurplus_scaled_of_certificates hAU hBU hcompat
      kernel_s9c5_all_nonempty_uniform_certificates
  omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_all_nonempty_uniform_certificates
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_supportSurplus_le_82

theorem kernel_s9c7_type_chunks_union :
    kernelS9C7UniformTypes = kernelS9C7TypeChunk0 ∪ kernelS9C7TypeChunk1 ∪ kernelS9C7TypeChunk2 ∪ kernelS9C7TypeChunk3 := by
  decide +kernel

theorem kernel_s9c7_sum_decomp (R : Finset (Fin 9)) (w : ℕ) :
    (∑ I ∈ kernelS9C7UniformTypes, if (I ∩ R).Nonempty then
      2 * I.card - (I ∩ R).card * w else 0) =
      (∑ I ∈ kernelS9C7TypeChunk0, if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * w else 0) +
      (∑ I ∈ kernelS9C7TypeChunk1, if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * w else 0) +
      (∑ I ∈ kernelS9C7TypeChunk2, if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * w else 0) +
      (∑ I ∈ kernelS9C7TypeChunk3, if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * w else 0) := by
  rw [kernel_s9c7_type_chunks_union]
  repeat rw [Finset.sum_union]
  all_goals decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_type_chunks_union
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_sum_decomp

theorem kernel_s9c7_block0_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 0)).1 *
        ((kernelSmallMask 9 (i.val + 0)).card *
          (kernelS9C7UniformRow (i.val + 0)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 0, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block0 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 0) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk0_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk0_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk0_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk0_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk0_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk0_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk0_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk0_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block0_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 0, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 0, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 0, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 0, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 0, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    have hsum' :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val, by omega⟩))) := by
      simpa only [Nat.add_zero] using hsum
    rw [hsum'] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block0_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block0

theorem kernel_s9c7_block1_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 16)).1 *
        ((kernelSmallMask 9 (i.val + 16)).card *
          (kernelS9C7UniformRow (i.val + 16)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 16, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block1 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 16) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk1_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk1_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk1_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk1_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk1_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk1_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk1_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk1_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block1_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 16, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 16, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 16, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 16, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 16, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block1_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block1

theorem kernel_s9c7_block2_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 32)).1 *
        ((kernelSmallMask 9 (i.val + 32)).card *
          (kernelS9C7UniformRow (i.val + 32)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 32, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block2 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 32) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk2_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk2_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk2_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk2_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk2_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk2_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk2_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk2_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block2_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 32, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 32, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 32, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 32, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 32, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block2_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block2

theorem kernel_s9c7_block3_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 48)).1 *
        ((kernelSmallMask 9 (i.val + 48)).card *
          (kernelS9C7UniformRow (i.val + 48)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 48, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block3 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 48) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk3_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk3_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk3_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk3_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk3_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk3_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk3_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk3_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block3_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 48, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 48, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 48, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 48, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 48, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block3_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block3

theorem kernel_s9c7_block4_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 64)).1 *
        ((kernelSmallMask 9 (i.val + 64)).card *
          (kernelS9C7UniformRow (i.val + 64)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 64, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block4 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 64) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk4_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk4_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk4_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk4_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk4_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk4_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk4_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk4_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block4_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 64, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 64, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 64, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 64, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 64, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block4_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block4

theorem kernel_s9c7_block5_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 80)).1 *
        ((kernelSmallMask 9 (i.val + 80)).card *
          (kernelS9C7UniformRow (i.val + 80)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 80, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block5 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 80) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk5_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk5_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk5_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk5_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk5_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk5_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk5_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk5_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block5_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 80, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 80, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 80, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 80, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 80, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block5_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block5

theorem kernel_s9c7_block6_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 96)).1 *
        ((kernelSmallMask 9 (i.val + 96)).card *
          (kernelS9C7UniformRow (i.val + 96)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 96, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block6 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 96) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk6_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk6_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk6_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk6_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk6_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk6_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk6_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk6_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block6_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 96, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 96, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 96, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 96, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 96, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block6_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block6

theorem kernel_s9c7_block7_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 112)).1 *
        ((kernelSmallMask 9 (i.val + 112)).card *
          (kernelS9C7UniformRow (i.val + 112)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 112, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block7 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 112) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk7_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk7_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk7_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk7_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk7_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk7_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk7_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk7_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block7_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 112, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 112, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 112, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 112, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 112, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block7_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block7

theorem kernel_s9c7_block8_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 128)).1 *
        ((kernelSmallMask 9 (i.val + 128)).card *
          (kernelS9C7UniformRow (i.val + 128)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 128, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block8 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 128) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk8_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk8_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk8_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk8_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk8_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk8_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk8_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk8_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block8_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 128, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 128, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 128, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 128, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 128, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block8_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block8

theorem kernel_s9c7_block9_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 144)).1 *
        ((kernelSmallMask 9 (i.val + 144)).card *
          (kernelS9C7UniformRow (i.val + 144)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 144, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block9 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 144) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk9_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk9_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk9_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk9_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk9_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk9_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk9_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk9_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block9_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 144, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 144, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 144, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 144, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 144, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block9_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block9

theorem kernel_s9c7_block10_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 160)).1 *
        ((kernelSmallMask 9 (i.val + 160)).card *
          (kernelS9C7UniformRow (i.val + 160)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 160, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block10 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 160) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk10_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk10_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk10_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk10_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk10_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk10_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk10_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk10_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block10_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 160, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 160, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 160, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 160, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 160, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block10_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block10

theorem kernel_s9c7_block11_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 176)).1 *
        ((kernelSmallMask 9 (i.val + 176)).card *
          (kernelS9C7UniformRow (i.val + 176)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 176, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block11 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 176) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk11_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk11_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk11_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk11_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk11_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk11_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk11_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk11_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block11_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 176, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 176, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 176, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 176, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 176, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block11_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block11

theorem kernel_s9c7_block12_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 192)).1 *
        ((kernelSmallMask 9 (i.val + 192)).card *
          (kernelS9C7UniformRow (i.val + 192)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 192, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block12 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 192) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk12_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk12_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk12_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk12_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk12_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk12_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk12_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk12_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block12_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 192, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 192, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 192, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 192, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 192, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block12_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block12

theorem kernel_s9c7_block13_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 208)).1 *
        ((kernelSmallMask 9 (i.val + 208)).card *
          (kernelS9C7UniformRow (i.val + 208)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 208, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block13 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 208) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk13_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk13_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk13_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk13_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk13_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk13_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk13_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk13_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block13_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 208, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 208, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 208, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 208, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 208, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block13_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block13

theorem kernel_s9c7_block14_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 224)).1 *
        ((kernelSmallMask 9 (i.val + 224)).card *
          (kernelS9C7UniformRow (i.val + 224)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 224, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block14 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 224) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk14_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk14_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk14_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk14_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk14_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk14_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk14_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk14_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block14_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 224, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 224, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 224, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 224, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 224, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block14_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block14

theorem kernel_s9c7_block15_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 240)).1 *
        ((kernelSmallMask 9 (i.val + 240)).card *
          (kernelS9C7UniformRow (i.val + 240)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 240, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block15 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 240) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk15_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk15_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk15_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk15_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk15_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk15_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk15_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk15_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block15_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 240, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 240, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 240, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 240, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 240, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block15_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block15

theorem kernel_s9c7_block16_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 256)).1 *
        ((kernelSmallMask 9 (i.val + 256)).card *
          (kernelS9C7UniformRow (i.val + 256)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 256, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block16 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 256) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk16_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk16_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk16_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk16_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk16_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk16_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk16_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk16_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block16_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 256, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 256, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 256, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 256, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 256, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block16_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block16

theorem kernel_s9c7_block17_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 272)).1 *
        ((kernelSmallMask 9 (i.val + 272)).card *
          (kernelS9C7UniformRow (i.val + 272)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 272, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block17 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 272) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk17_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk17_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk17_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk17_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk17_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk17_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk17_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk17_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block17_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 272, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 272, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 272, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 272, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 272, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block17_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block17

theorem kernel_s9c7_block18_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 288)).1 *
        ((kernelSmallMask 9 (i.val + 288)).card *
          (kernelS9C7UniformRow (i.val + 288)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 288, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block18 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 288) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk18_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk18_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk18_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk18_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk18_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk18_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk18_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk18_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block18_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 288, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 288, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 288, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 288, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 288, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block18_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block18

theorem kernel_s9c7_block19_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 304)).1 *
        ((kernelSmallMask 9 (i.val + 304)).card *
          (kernelS9C7UniformRow (i.val + 304)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 304, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block19 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 304) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk19_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk19_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk19_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk19_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk19_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk19_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk19_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk19_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block19_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 304, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 304, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 304, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 304, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 304, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block19_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block19

theorem kernel_s9c7_block20_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 320)).1 *
        ((kernelSmallMask 9 (i.val + 320)).card *
          (kernelS9C7UniformRow (i.val + 320)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 320, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block20 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 320) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk20_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk20_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk20_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk20_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk20_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk20_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk20_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk20_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block20_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 320, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 320, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 320, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 320, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 320, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block20_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block20

theorem kernel_s9c7_block21_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 336)).1 *
        ((kernelSmallMask 9 (i.val + 336)).card *
          (kernelS9C7UniformRow (i.val + 336)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 336, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block21 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 336) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk21_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk21_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk21_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk21_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk21_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk21_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk21_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk21_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block21_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 336, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 336, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 336, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 336, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 336, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block21_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block21

theorem kernel_s9c7_block22_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 352)).1 *
        ((kernelSmallMask 9 (i.val + 352)).card *
          (kernelS9C7UniformRow (i.val + 352)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 352, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block22 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 352) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk22_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk22_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk22_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk22_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk22_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk22_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk22_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk22_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block22_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 352, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 352, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 352, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 352, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 352, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block22_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block22

theorem kernel_s9c7_block23_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 368)).1 *
        ((kernelSmallMask 9 (i.val + 368)).card *
          (kernelS9C7UniformRow (i.val + 368)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 368, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block23 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 368) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk23_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk23_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk23_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk23_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk23_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk23_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk23_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk23_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block23_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 368, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 368, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 368, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 368, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 368, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block23_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block23

theorem kernel_s9c7_block24_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 384)).1 *
        ((kernelSmallMask 9 (i.val + 384)).card *
          (kernelS9C7UniformRow (i.val + 384)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 384, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block24 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 384) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk24_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk24_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk24_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk24_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk24_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk24_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk24_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk24_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block24_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 384, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 384, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 384, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 384, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 384, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block24_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block24

theorem kernel_s9c7_block25_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 400)).1 *
        ((kernelSmallMask 9 (i.val + 400)).card *
          (kernelS9C7UniformRow (i.val + 400)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 400, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block25 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 400) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk25_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk25_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk25_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk25_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk25_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk25_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk25_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk25_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block25_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 400, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 400, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 400, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 400, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 400, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block25_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block25

theorem kernel_s9c7_block26_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 416)).1 *
        ((kernelSmallMask 9 (i.val + 416)).card *
          (kernelS9C7UniformRow (i.val + 416)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 416, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block26 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 416) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk26_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk26_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk26_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk26_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk26_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk26_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk26_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk26_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block26_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 416, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 416, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 416, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 416, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 416, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block26_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block26

theorem kernel_s9c7_block27_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 432)).1 *
        ((kernelSmallMask 9 (i.val + 432)).card *
          (kernelS9C7UniformRow (i.val + 432)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 432, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block27 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 432) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk27_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk27_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk27_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk27_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk27_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk27_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk27_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk27_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block27_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 432, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 432, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 432, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 432, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 432, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block27_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block27

theorem kernel_s9c7_block28_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 448)).1 *
        ((kernelSmallMask 9 (i.val + 448)).card *
          (kernelS9C7UniformRow (i.val + 448)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 448, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block28 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 448) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk28_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk28_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk28_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk28_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk28_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk28_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk28_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk28_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block28_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 448, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 448, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 448, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 448, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 448, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block28_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block28

theorem kernel_s9c7_block29_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 464)).1 *
        ((kernelSmallMask 9 (i.val + 464)).card *
          (kernelS9C7UniformRow (i.val + 464)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 464, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block29 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 464) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk29_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk29_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk29_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk29_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk29_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk29_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk29_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk29_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block29_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 464, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 464, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 464, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 464, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 464, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block29_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block29

theorem kernel_s9c7_block30_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 480)).1 *
        ((kernelSmallMask 9 (i.val + 480)).card *
          (kernelS9C7UniformRow (i.val + 480)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 480, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block30 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 480) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk30_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk30_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk30_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk30_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk30_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk30_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk30_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk30_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block30_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 480, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 480, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 480, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 480, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 480, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block30_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block30

theorem kernel_s9c7_block31_arithmetic : ∀ i : Fin 16,
    (kernelS9C7UniformRow (i.val + 496)).1 *
        ((kernelSmallMask 9 (i.val + 496)).card *
          (kernelS9C7UniformRow (i.val + 496)).2) +
      ∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 496, by omega⟩ ≤ 146 := by
  decide +kernel

theorem kernel_s9c7_uniform_block31 (i : Fin 16) :
    KernelS9C7UniformCertificate (i.val + 496) := by
  dsimp [KernelS9C7UniformCertificate]
  have hb0 := kernel_s9c7_type_mask_chunk31_direct_beta0 i
  have hs0 := kernel_s9c7_type_mask_chunk31_sum0 i
  have hb1 := kernel_s9c7_type_mask_chunk31_direct_beta1 i
  have hs1 := kernel_s9c7_type_mask_chunk31_sum1 i
  have hb2 := kernel_s9c7_type_mask_chunk31_direct_beta2 i
  have hs2 := kernel_s9c7_type_mask_chunk31_sum2 i
  have hb3 := kernel_s9c7_type_mask_chunk31_direct_beta3 i
  have hs3 := kernel_s9c7_type_mask_chunk31_sum3 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c7_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C7TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C7TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C7TypeChunk2
        · exact hb2 I h2 hsub
        · by_cases h3 : I ∈ kernelS9C7TypeChunk3
          · exact hb3 I h3 hsub
          · simp [Finset.mem_union, h0, h1, h2, h3] at hI
  · rw [kernel_s9c7_sum_decomp]
    have ha := kernel_s9c7_block31_arithmetic i
    have hsum :
        (∑ j : Fin 4, kernelS9C7PartialBound j ⟨i.val + 496, by omega⟩) =
          kernelS9C7PartialBound 0 ⟨i.val + 496, by omega⟩ +
          (kernelS9C7PartialBound 1 ⟨i.val + 496, by omega⟩ +
          (kernelS9C7PartialBound 2 ⟨i.val + 496, by omega⟩ +
          (kernelS9C7PartialBound 3 ⟨i.val + 496, by omega⟩))) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 hs3 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_block31_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_block31

theorem kernel_s9c7_uniform_masks (m : Fin 512) :
    KernelS9C7UniformCertificate m.val := by
  have hm := m.isLt
  by_cases h0 : m.val < 16
  · have hi : m.val - 0 < 16 := by omega
    have heq : m.val - 0 + 0 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block0 ⟨m.val - 0, hi⟩
  by_cases h1 : m.val < 32
  · have hi : m.val - 16 < 16 := by omega
    have heq : m.val - 16 + 16 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block1 ⟨m.val - 16, hi⟩
  by_cases h2 : m.val < 48
  · have hi : m.val - 32 < 16 := by omega
    have heq : m.val - 32 + 32 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block2 ⟨m.val - 32, hi⟩
  by_cases h3 : m.val < 64
  · have hi : m.val - 48 < 16 := by omega
    have heq : m.val - 48 + 48 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block3 ⟨m.val - 48, hi⟩
  by_cases h4 : m.val < 80
  · have hi : m.val - 64 < 16 := by omega
    have heq : m.val - 64 + 64 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block4 ⟨m.val - 64, hi⟩
  by_cases h5 : m.val < 96
  · have hi : m.val - 80 < 16 := by omega
    have heq : m.val - 80 + 80 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block5 ⟨m.val - 80, hi⟩
  by_cases h6 : m.val < 112
  · have hi : m.val - 96 < 16 := by omega
    have heq : m.val - 96 + 96 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block6 ⟨m.val - 96, hi⟩
  by_cases h7 : m.val < 128
  · have hi : m.val - 112 < 16 := by omega
    have heq : m.val - 112 + 112 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block7 ⟨m.val - 112, hi⟩
  by_cases h8 : m.val < 144
  · have hi : m.val - 128 < 16 := by omega
    have heq : m.val - 128 + 128 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block8 ⟨m.val - 128, hi⟩
  by_cases h9 : m.val < 160
  · have hi : m.val - 144 < 16 := by omega
    have heq : m.val - 144 + 144 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block9 ⟨m.val - 144, hi⟩
  by_cases h10 : m.val < 176
  · have hi : m.val - 160 < 16 := by omega
    have heq : m.val - 160 + 160 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block10 ⟨m.val - 160, hi⟩
  by_cases h11 : m.val < 192
  · have hi : m.val - 176 < 16 := by omega
    have heq : m.val - 176 + 176 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block11 ⟨m.val - 176, hi⟩
  by_cases h12 : m.val < 208
  · have hi : m.val - 192 < 16 := by omega
    have heq : m.val - 192 + 192 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block12 ⟨m.val - 192, hi⟩
  by_cases h13 : m.val < 224
  · have hi : m.val - 208 < 16 := by omega
    have heq : m.val - 208 + 208 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block13 ⟨m.val - 208, hi⟩
  by_cases h14 : m.val < 240
  · have hi : m.val - 224 < 16 := by omega
    have heq : m.val - 224 + 224 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block14 ⟨m.val - 224, hi⟩
  by_cases h15 : m.val < 256
  · have hi : m.val - 240 < 16 := by omega
    have heq : m.val - 240 + 240 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block15 ⟨m.val - 240, hi⟩
  by_cases h16 : m.val < 272
  · have hi : m.val - 256 < 16 := by omega
    have heq : m.val - 256 + 256 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block16 ⟨m.val - 256, hi⟩
  by_cases h17 : m.val < 288
  · have hi : m.val - 272 < 16 := by omega
    have heq : m.val - 272 + 272 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block17 ⟨m.val - 272, hi⟩
  by_cases h18 : m.val < 304
  · have hi : m.val - 288 < 16 := by omega
    have heq : m.val - 288 + 288 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block18 ⟨m.val - 288, hi⟩
  by_cases h19 : m.val < 320
  · have hi : m.val - 304 < 16 := by omega
    have heq : m.val - 304 + 304 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block19 ⟨m.val - 304, hi⟩
  by_cases h20 : m.val < 336
  · have hi : m.val - 320 < 16 := by omega
    have heq : m.val - 320 + 320 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block20 ⟨m.val - 320, hi⟩
  by_cases h21 : m.val < 352
  · have hi : m.val - 336 < 16 := by omega
    have heq : m.val - 336 + 336 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block21 ⟨m.val - 336, hi⟩
  by_cases h22 : m.val < 368
  · have hi : m.val - 352 < 16 := by omega
    have heq : m.val - 352 + 352 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block22 ⟨m.val - 352, hi⟩
  by_cases h23 : m.val < 384
  · have hi : m.val - 368 < 16 := by omega
    have heq : m.val - 368 + 368 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block23 ⟨m.val - 368, hi⟩
  by_cases h24 : m.val < 400
  · have hi : m.val - 384 < 16 := by omega
    have heq : m.val - 384 + 384 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block24 ⟨m.val - 384, hi⟩
  by_cases h25 : m.val < 416
  · have hi : m.val - 400 < 16 := by omega
    have heq : m.val - 400 + 400 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block25 ⟨m.val - 400, hi⟩
  by_cases h26 : m.val < 432
  · have hi : m.val - 416 < 16 := by omega
    have heq : m.val - 416 + 416 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block26 ⟨m.val - 416, hi⟩
  by_cases h27 : m.val < 448
  · have hi : m.val - 432 < 16 := by omega
    have heq : m.val - 432 + 432 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block27 ⟨m.val - 432, hi⟩
  by_cases h28 : m.val < 464
  · have hi : m.val - 448 < 16 := by omega
    have heq : m.val - 448 + 448 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block28 ⟨m.val - 448, hi⟩
  by_cases h29 : m.val < 480
  · have hi : m.val - 464 < 16 := by omega
    have heq : m.val - 464 + 464 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block29 ⟨m.val - 464, hi⟩
  by_cases h30 : m.val < 496
  · have hi : m.val - 480 < 16 := by omega
    have heq : m.val - 480 + 480 = m.val := by omega
    simpa only [heq] using
      kernel_s9c7_uniform_block30 ⟨m.val - 480, hi⟩
  have hi : m.val - 496 < 16 := by omega
  have heq : m.val - 496 + 496 = m.val := by omega
  simpa only [heq] using
    kernel_s9c7_uniform_block31 ⟨m.val - 496, hi⟩

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_uniform_masks

theorem kernel_s9c7_all_nonempty_uniform_certificates
    (R : Finset (Fin 9)) (_hR : R.Nonempty) :
    ∃ b : ℕ, ∃ w : Fin 9 → ℕ,
      (∀ I ∈ cycleTypes 9 7, I ⊆ R → I.card ≤ b) ∧
      R5Kernel.dualValue (cycleTypes 9 7) R b 2 w ≤ 146 := by
  let m := kernelSmallEncode R
  have hc := kernel_s9c7_uniform_masks m
  dsimp only [KernelS9C7UniformCertificate] at hc
  rw [← kernel_s9c7_uniform_types_eq, kernel_s9_decode_encode R] at hc
  refine ⟨(kernelS9C7UniformRow m.val).1,
    (fun _ => (kernelS9C7UniformRow m.val).2), hc.1, ?_⟩
  rw [kernel_dualValue_uniform]
  exact hc.2

theorem kernel_s9c7_supportSurplus_le_73
    {A B : Finset (Finset (Fin 9))}
    (hAU : A ⊆ cycleTypes 9 7) (hBU : B ⊆ cycleTypes 9 7)
    (hcompat : DegreeCompatible A B) : supportSurplus A B ≤ 73 := by
  have h : 2 * supportSurplus A B ≤ 146 :=
    kernel_supportSurplus_scaled_of_certificates hAU hBU hcompat
      kernel_s9c7_all_nonempty_uniform_certificates
  omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_all_nonempty_uniform_certificates
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_supportSurplus_le_73

theorem kernel_s9c9_type_chunks_union :
    kernelS9C9UniformTypes = kernelS9C9TypeChunk0 ∪ kernelS9C9TypeChunk1 ∪ kernelS9C9TypeChunk2 := by
  decide +kernel

theorem kernel_s9c9_sum_decomp (R : Finset (Fin 9)) (w : ℕ) :
    (∑ I ∈ kernelS9C9UniformTypes, if (I ∩ R).Nonempty then
      2 * I.card - (I ∩ R).card * w else 0) =
      (∑ I ∈ kernelS9C9TypeChunk0, if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * w else 0) +
      (∑ I ∈ kernelS9C9TypeChunk1, if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * w else 0) +
      (∑ I ∈ kernelS9C9TypeChunk2, if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * w else 0) := by
  rw [kernel_s9c9_type_chunks_union]
  repeat rw [Finset.sum_union]
  all_goals decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_type_chunks_union
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_sum_decomp

theorem kernel_s9c9_block0_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 0)).1 *
        ((kernelSmallMask 9 (i.val + 0)).card *
          (kernelS9C9UniformRow (i.val + 0)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 0, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block0 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 0) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk0_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk0_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk0_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk0_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk0_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk0_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block0_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 0, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 0, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 0, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 0, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    have hsum' :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val, by omega⟩)) := by
      simpa only [Nat.add_zero] using hsum
    rw [hsum'] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block0_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block0

theorem kernel_s9c9_block1_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 16)).1 *
        ((kernelSmallMask 9 (i.val + 16)).card *
          (kernelS9C9UniformRow (i.val + 16)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 16, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block1 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 16) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk1_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk1_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk1_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk1_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk1_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk1_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block1_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 16, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 16, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 16, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 16, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block1_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block1

theorem kernel_s9c9_block2_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 32)).1 *
        ((kernelSmallMask 9 (i.val + 32)).card *
          (kernelS9C9UniformRow (i.val + 32)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 32, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block2 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 32) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk2_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk2_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk2_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk2_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk2_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk2_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block2_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 32, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 32, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 32, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 32, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block2_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block2

theorem kernel_s9c9_block3_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 48)).1 *
        ((kernelSmallMask 9 (i.val + 48)).card *
          (kernelS9C9UniformRow (i.val + 48)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 48, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block3 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 48) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk3_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk3_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk3_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk3_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk3_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk3_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block3_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 48, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 48, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 48, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 48, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block3_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block3

theorem kernel_s9c9_block4_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 64)).1 *
        ((kernelSmallMask 9 (i.val + 64)).card *
          (kernelS9C9UniformRow (i.val + 64)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 64, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block4 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 64) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk4_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk4_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk4_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk4_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk4_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk4_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block4_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 64, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 64, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 64, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 64, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block4_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block4

theorem kernel_s9c9_block5_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 80)).1 *
        ((kernelSmallMask 9 (i.val + 80)).card *
          (kernelS9C9UniformRow (i.val + 80)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 80, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block5 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 80) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk5_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk5_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk5_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk5_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk5_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk5_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block5_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 80, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 80, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 80, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 80, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block5_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block5

theorem kernel_s9c9_block6_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 96)).1 *
        ((kernelSmallMask 9 (i.val + 96)).card *
          (kernelS9C9UniformRow (i.val + 96)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 96, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block6 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 96) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk6_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk6_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk6_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk6_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk6_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk6_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block6_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 96, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 96, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 96, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 96, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block6_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block6

theorem kernel_s9c9_block7_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 112)).1 *
        ((kernelSmallMask 9 (i.val + 112)).card *
          (kernelS9C9UniformRow (i.val + 112)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 112, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block7 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 112) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk7_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk7_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk7_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk7_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk7_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk7_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block7_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 112, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 112, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 112, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 112, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block7_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block7

theorem kernel_s9c9_block8_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 128)).1 *
        ((kernelSmallMask 9 (i.val + 128)).card *
          (kernelS9C9UniformRow (i.val + 128)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 128, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block8 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 128) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk8_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk8_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk8_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk8_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk8_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk8_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block8_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 128, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 128, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 128, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 128, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block8_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block8

theorem kernel_s9c9_block9_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 144)).1 *
        ((kernelSmallMask 9 (i.val + 144)).card *
          (kernelS9C9UniformRow (i.val + 144)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 144, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block9 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 144) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk9_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk9_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk9_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk9_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk9_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk9_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block9_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 144, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 144, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 144, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 144, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block9_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block9

theorem kernel_s9c9_block10_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 160)).1 *
        ((kernelSmallMask 9 (i.val + 160)).card *
          (kernelS9C9UniformRow (i.val + 160)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 160, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block10 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 160) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk10_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk10_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk10_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk10_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk10_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk10_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block10_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 160, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 160, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 160, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 160, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block10_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block10

theorem kernel_s9c9_block11_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 176)).1 *
        ((kernelSmallMask 9 (i.val + 176)).card *
          (kernelS9C9UniformRow (i.val + 176)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 176, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block11 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 176) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk11_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk11_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk11_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk11_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk11_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk11_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block11_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 176, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 176, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 176, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 176, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block11_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block11

theorem kernel_s9c9_block12_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 192)).1 *
        ((kernelSmallMask 9 (i.val + 192)).card *
          (kernelS9C9UniformRow (i.val + 192)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 192, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block12 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 192) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk12_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk12_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk12_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk12_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk12_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk12_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block12_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 192, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 192, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 192, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 192, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block12_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block12

theorem kernel_s9c9_block13_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 208)).1 *
        ((kernelSmallMask 9 (i.val + 208)).card *
          (kernelS9C9UniformRow (i.val + 208)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 208, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block13 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 208) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk13_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk13_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk13_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk13_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk13_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk13_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block13_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 208, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 208, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 208, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 208, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block13_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block13

theorem kernel_s9c9_block14_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 224)).1 *
        ((kernelSmallMask 9 (i.val + 224)).card *
          (kernelS9C9UniformRow (i.val + 224)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 224, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block14 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 224) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk14_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk14_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk14_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk14_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk14_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk14_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block14_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 224, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 224, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 224, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 224, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block14_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block14

theorem kernel_s9c9_block15_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 240)).1 *
        ((kernelSmallMask 9 (i.val + 240)).card *
          (kernelS9C9UniformRow (i.val + 240)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 240, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block15 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 240) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk15_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk15_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk15_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk15_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk15_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk15_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block15_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 240, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 240, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 240, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 240, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block15_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block15

theorem kernel_s9c9_block16_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 256)).1 *
        ((kernelSmallMask 9 (i.val + 256)).card *
          (kernelS9C9UniformRow (i.val + 256)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 256, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block16 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 256) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk16_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk16_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk16_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk16_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk16_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk16_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block16_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 256, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 256, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 256, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 256, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block16_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block16

theorem kernel_s9c9_block17_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 272)).1 *
        ((kernelSmallMask 9 (i.val + 272)).card *
          (kernelS9C9UniformRow (i.val + 272)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 272, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block17 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 272) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk17_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk17_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk17_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk17_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk17_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk17_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block17_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 272, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 272, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 272, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 272, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block17_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block17

theorem kernel_s9c9_block18_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 288)).1 *
        ((kernelSmallMask 9 (i.val + 288)).card *
          (kernelS9C9UniformRow (i.val + 288)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 288, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block18 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 288) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk18_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk18_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk18_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk18_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk18_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk18_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block18_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 288, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 288, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 288, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 288, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block18_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block18

theorem kernel_s9c9_block19_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 304)).1 *
        ((kernelSmallMask 9 (i.val + 304)).card *
          (kernelS9C9UniformRow (i.val + 304)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 304, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block19 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 304) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk19_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk19_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk19_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk19_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk19_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk19_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block19_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 304, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 304, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 304, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 304, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block19_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block19

theorem kernel_s9c9_block20_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 320)).1 *
        ((kernelSmallMask 9 (i.val + 320)).card *
          (kernelS9C9UniformRow (i.val + 320)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 320, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block20 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 320) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk20_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk20_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk20_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk20_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk20_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk20_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block20_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 320, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 320, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 320, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 320, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block20_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block20

theorem kernel_s9c9_block21_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 336)).1 *
        ((kernelSmallMask 9 (i.val + 336)).card *
          (kernelS9C9UniformRow (i.val + 336)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 336, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block21 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 336) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk21_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk21_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk21_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk21_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk21_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk21_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block21_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 336, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 336, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 336, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 336, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block21_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block21

theorem kernel_s9c9_block22_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 352)).1 *
        ((kernelSmallMask 9 (i.val + 352)).card *
          (kernelS9C9UniformRow (i.val + 352)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 352, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block22 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 352) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk22_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk22_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk22_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk22_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk22_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk22_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block22_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 352, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 352, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 352, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 352, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block22_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block22

theorem kernel_s9c9_block23_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 368)).1 *
        ((kernelSmallMask 9 (i.val + 368)).card *
          (kernelS9C9UniformRow (i.val + 368)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 368, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block23 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 368) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk23_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk23_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk23_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk23_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk23_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk23_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block23_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 368, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 368, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 368, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 368, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block23_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block23

theorem kernel_s9c9_block24_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 384)).1 *
        ((kernelSmallMask 9 (i.val + 384)).card *
          (kernelS9C9UniformRow (i.val + 384)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 384, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block24 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 384) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk24_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk24_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk24_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk24_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk24_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk24_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block24_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 384, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 384, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 384, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 384, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block24_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block24

theorem kernel_s9c9_block25_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 400)).1 *
        ((kernelSmallMask 9 (i.val + 400)).card *
          (kernelS9C9UniformRow (i.val + 400)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 400, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block25 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 400) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk25_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk25_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk25_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk25_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk25_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk25_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block25_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 400, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 400, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 400, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 400, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block25_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block25

theorem kernel_s9c9_block26_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 416)).1 *
        ((kernelSmallMask 9 (i.val + 416)).card *
          (kernelS9C9UniformRow (i.val + 416)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 416, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block26 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 416) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk26_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk26_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk26_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk26_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk26_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk26_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block26_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 416, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 416, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 416, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 416, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block26_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block26

theorem kernel_s9c9_block27_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 432)).1 *
        ((kernelSmallMask 9 (i.val + 432)).card *
          (kernelS9C9UniformRow (i.val + 432)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 432, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block27 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 432) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk27_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk27_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk27_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk27_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk27_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk27_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block27_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 432, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 432, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 432, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 432, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block27_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block27

theorem kernel_s9c9_block28_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 448)).1 *
        ((kernelSmallMask 9 (i.val + 448)).card *
          (kernelS9C9UniformRow (i.val + 448)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 448, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block28 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 448) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk28_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk28_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk28_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk28_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk28_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk28_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block28_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 448, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 448, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 448, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 448, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block28_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block28

theorem kernel_s9c9_block29_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 464)).1 *
        ((kernelSmallMask 9 (i.val + 464)).card *
          (kernelS9C9UniformRow (i.val + 464)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 464, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block29 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 464) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk29_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk29_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk29_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk29_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk29_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk29_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block29_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 464, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 464, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 464, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 464, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block29_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block29

theorem kernel_s9c9_block30_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 480)).1 *
        ((kernelSmallMask 9 (i.val + 480)).card *
          (kernelS9C9UniformRow (i.val + 480)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 480, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block30 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 480) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk30_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk30_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk30_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk30_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk30_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk30_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block30_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 480, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 480, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 480, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 480, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block30_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block30

theorem kernel_s9c9_block31_arithmetic : ∀ i : Fin 16,
    (kernelS9C9UniformRow (i.val + 496)).1 *
        ((kernelSmallMask 9 (i.val + 496)).card *
          (kernelS9C9UniformRow (i.val + 496)).2) +
      ∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 496, by omega⟩ ≤ 120 := by
  decide +kernel

theorem kernel_s9c9_uniform_block31 (i : Fin 16) :
    KernelS9C9UniformCertificate (i.val + 496) := by
  dsimp [KernelS9C9UniformCertificate]
  have hb0 := kernel_s9c9_type_mask_chunk31_direct_beta0 i
  have hs0 := kernel_s9c9_type_mask_chunk31_sum0 i
  have hb1 := kernel_s9c9_type_mask_chunk31_direct_beta1 i
  have hs1 := kernel_s9c9_type_mask_chunk31_sum1 i
  have hb2 := kernel_s9c9_type_mask_chunk31_direct_beta2 i
  have hs2 := kernel_s9c9_type_mask_chunk31_sum2 i
  constructor
  · intro I hI hsub
    rw [kernel_s9c9_type_chunks_union] at hI
    by_cases h0 : I ∈ kernelS9C9TypeChunk0
    · exact hb0 I h0 hsub
    · by_cases h1 : I ∈ kernelS9C9TypeChunk1
      · exact hb1 I h1 hsub
      · by_cases h2 : I ∈ kernelS9C9TypeChunk2
        · exact hb2 I h2 hsub
        · simp [Finset.mem_union, h0, h1, h2] at hI
  · rw [kernel_s9c9_sum_decomp]
    have ha := kernel_s9c9_block31_arithmetic i
    have hsum :
        (∑ j : Fin 3, kernelS9C9PartialBound j ⟨i.val + 496, by omega⟩) =
          kernelS9C9PartialBound 0 ⟨i.val + 496, by omega⟩ +
          (kernelS9C9PartialBound 1 ⟨i.val + 496, by omega⟩ +
          (kernelS9C9PartialBound 2 ⟨i.val + 496, by omega⟩)) := by
      simp [Fin.sum_univ_succ]
    simp only [Nat.add_zero] at hs0 hs1 hs2 ha ⊢
    rw [hsum] at ha
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_block31_arithmetic
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_block31

theorem kernel_s9c9_uniform_masks (m : Fin 512) :
    KernelS9C9UniformCertificate m.val := by
  have hm := m.isLt
  by_cases h0 : m.val < 16
  · have hi : m.val - 0 < 16 := by omega
    have heq : m.val - 0 + 0 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block0 ⟨m.val - 0, hi⟩
  by_cases h1 : m.val < 32
  · have hi : m.val - 16 < 16 := by omega
    have heq : m.val - 16 + 16 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block1 ⟨m.val - 16, hi⟩
  by_cases h2 : m.val < 48
  · have hi : m.val - 32 < 16 := by omega
    have heq : m.val - 32 + 32 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block2 ⟨m.val - 32, hi⟩
  by_cases h3 : m.val < 64
  · have hi : m.val - 48 < 16 := by omega
    have heq : m.val - 48 + 48 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block3 ⟨m.val - 48, hi⟩
  by_cases h4 : m.val < 80
  · have hi : m.val - 64 < 16 := by omega
    have heq : m.val - 64 + 64 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block4 ⟨m.val - 64, hi⟩
  by_cases h5 : m.val < 96
  · have hi : m.val - 80 < 16 := by omega
    have heq : m.val - 80 + 80 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block5 ⟨m.val - 80, hi⟩
  by_cases h6 : m.val < 112
  · have hi : m.val - 96 < 16 := by omega
    have heq : m.val - 96 + 96 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block6 ⟨m.val - 96, hi⟩
  by_cases h7 : m.val < 128
  · have hi : m.val - 112 < 16 := by omega
    have heq : m.val - 112 + 112 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block7 ⟨m.val - 112, hi⟩
  by_cases h8 : m.val < 144
  · have hi : m.val - 128 < 16 := by omega
    have heq : m.val - 128 + 128 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block8 ⟨m.val - 128, hi⟩
  by_cases h9 : m.val < 160
  · have hi : m.val - 144 < 16 := by omega
    have heq : m.val - 144 + 144 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block9 ⟨m.val - 144, hi⟩
  by_cases h10 : m.val < 176
  · have hi : m.val - 160 < 16 := by omega
    have heq : m.val - 160 + 160 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block10 ⟨m.val - 160, hi⟩
  by_cases h11 : m.val < 192
  · have hi : m.val - 176 < 16 := by omega
    have heq : m.val - 176 + 176 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block11 ⟨m.val - 176, hi⟩
  by_cases h12 : m.val < 208
  · have hi : m.val - 192 < 16 := by omega
    have heq : m.val - 192 + 192 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block12 ⟨m.val - 192, hi⟩
  by_cases h13 : m.val < 224
  · have hi : m.val - 208 < 16 := by omega
    have heq : m.val - 208 + 208 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block13 ⟨m.val - 208, hi⟩
  by_cases h14 : m.val < 240
  · have hi : m.val - 224 < 16 := by omega
    have heq : m.val - 224 + 224 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block14 ⟨m.val - 224, hi⟩
  by_cases h15 : m.val < 256
  · have hi : m.val - 240 < 16 := by omega
    have heq : m.val - 240 + 240 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block15 ⟨m.val - 240, hi⟩
  by_cases h16 : m.val < 272
  · have hi : m.val - 256 < 16 := by omega
    have heq : m.val - 256 + 256 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block16 ⟨m.val - 256, hi⟩
  by_cases h17 : m.val < 288
  · have hi : m.val - 272 < 16 := by omega
    have heq : m.val - 272 + 272 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block17 ⟨m.val - 272, hi⟩
  by_cases h18 : m.val < 304
  · have hi : m.val - 288 < 16 := by omega
    have heq : m.val - 288 + 288 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block18 ⟨m.val - 288, hi⟩
  by_cases h19 : m.val < 320
  · have hi : m.val - 304 < 16 := by omega
    have heq : m.val - 304 + 304 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block19 ⟨m.val - 304, hi⟩
  by_cases h20 : m.val < 336
  · have hi : m.val - 320 < 16 := by omega
    have heq : m.val - 320 + 320 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block20 ⟨m.val - 320, hi⟩
  by_cases h21 : m.val < 352
  · have hi : m.val - 336 < 16 := by omega
    have heq : m.val - 336 + 336 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block21 ⟨m.val - 336, hi⟩
  by_cases h22 : m.val < 368
  · have hi : m.val - 352 < 16 := by omega
    have heq : m.val - 352 + 352 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block22 ⟨m.val - 352, hi⟩
  by_cases h23 : m.val < 384
  · have hi : m.val - 368 < 16 := by omega
    have heq : m.val - 368 + 368 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block23 ⟨m.val - 368, hi⟩
  by_cases h24 : m.val < 400
  · have hi : m.val - 384 < 16 := by omega
    have heq : m.val - 384 + 384 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block24 ⟨m.val - 384, hi⟩
  by_cases h25 : m.val < 416
  · have hi : m.val - 400 < 16 := by omega
    have heq : m.val - 400 + 400 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block25 ⟨m.val - 400, hi⟩
  by_cases h26 : m.val < 432
  · have hi : m.val - 416 < 16 := by omega
    have heq : m.val - 416 + 416 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block26 ⟨m.val - 416, hi⟩
  by_cases h27 : m.val < 448
  · have hi : m.val - 432 < 16 := by omega
    have heq : m.val - 432 + 432 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block27 ⟨m.val - 432, hi⟩
  by_cases h28 : m.val < 464
  · have hi : m.val - 448 < 16 := by omega
    have heq : m.val - 448 + 448 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block28 ⟨m.val - 448, hi⟩
  by_cases h29 : m.val < 480
  · have hi : m.val - 464 < 16 := by omega
    have heq : m.val - 464 + 464 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block29 ⟨m.val - 464, hi⟩
  by_cases h30 : m.val < 496
  · have hi : m.val - 480 < 16 := by omega
    have heq : m.val - 480 + 480 = m.val := by omega
    simpa only [heq] using
      kernel_s9c9_uniform_block30 ⟨m.val - 480, hi⟩
  have hi : m.val - 496 < 16 := by omega
  have heq : m.val - 496 + 496 = m.val := by omega
  simpa only [heq] using
    kernel_s9c9_uniform_block31 ⟨m.val - 496, hi⟩

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_uniform_masks

theorem kernel_s9c9_all_nonempty_uniform_certificates
    (R : Finset (Fin 9)) (_hR : R.Nonempty) :
    ∃ b : ℕ, ∃ w : Fin 9 → ℕ,
      (∀ I ∈ cycleTypes 9 9, I ⊆ R → I.card ≤ b) ∧
      R5Kernel.dualValue (cycleTypes 9 9) R b 2 w ≤ 120 := by
  let m := kernelSmallEncode R
  have hc := kernel_s9c9_uniform_masks m
  dsimp only [KernelS9C9UniformCertificate] at hc
  rw [← kernel_s9c9_uniform_types_eq, kernel_s9_decode_encode R] at hc
  refine ⟨(kernelS9C9UniformRow m.val).1,
    (fun _ => (kernelS9C9UniformRow m.val).2), hc.1, ?_⟩
  rw [kernel_dualValue_uniform]
  exact hc.2

theorem kernel_s9c9_supportSurplus_le_60
    {A B : Finset (Finset (Fin 9))}
    (hAU : A ⊆ cycleTypes 9 9) (hBU : B ⊆ cycleTypes 9 9)
    (hcompat : DegreeCompatible A B) : supportSurplus A B ≤ 60 := by
  have h : 2 * supportSurplus A B ≤ 120 :=
    kernel_supportSurplus_scaled_of_certificates hAU hBU hcompat
      kernel_s9c9_all_nonempty_uniform_certificates
  omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_all_nonempty_uniform_certificates
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_supportSurplus_le_60

end Erdos1011
