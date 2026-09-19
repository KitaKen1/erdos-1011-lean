import R5Kernel.R5TypeChunks

set_option Elab.async false
set_option maxHeartbeats 30000000
set_option maxRecDepth 200000

namespace Erdos1011

-- Enumerate the bounded finset, not the whole finite ambient type.
attribute [local instance 2000] Finset.decidableDforallFinset
open scoped BigOperators

theorem kernel_s9c5_type_mask_chunk20_direct_beta0 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 320)
    let row := kernelS9C5UniformRow (i.val + 320)
    ∀ I ∈ kernelS9C5TypeChunk0,
      I ⊆ R → I.card ≤ row.1 := by
  decide +kernel

theorem kernel_s9c5_type_mask_chunk20_direct_beta1 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 320)
    let row := kernelS9C5UniformRow (i.val + 320)
    ∀ I ∈ kernelS9C5TypeChunk1,
      I ⊆ R → I.card ≤ row.1 := by
  decide +kernel

theorem kernel_s9c5_type_mask_chunk20_direct_beta2 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 320)
    let row := kernelS9C5UniformRow (i.val + 320)
    ∀ I ∈ kernelS9C5TypeChunk2,
      I ⊆ R → I.card ≤ row.1 := by
  decide +kernel

theorem kernel_s9c5_type_mask_chunk20_direct_beta3 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 320)
    let row := kernelS9C5UniformRow (i.val + 320)
    ∀ I ∈ kernelS9C5TypeChunk3,
      I ⊆ R → I.card ≤ row.1 := by
  decide +kernel

theorem kernel_s9c5_type_mask_chunk20_direct_beta4 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 320)
    let row := kernelS9C5UniformRow (i.val + 320)
    ∀ I ∈ kernelS9C5TypeChunk4,
      I ⊆ R → I.card ≤ row.1 := by
  decide +kernel

theorem kernel_s9c5_type_mask_chunk20_direct_beta5 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 320)
    let row := kernelS9C5UniformRow (i.val + 320)
    ∀ I ∈ kernelS9C5TypeChunk5,
      I ⊆ R → I.card ≤ row.1 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_type_mask_chunk20_direct_beta0
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_type_mask_chunk20_direct_beta1
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_type_mask_chunk20_direct_beta2
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_type_mask_chunk20_direct_beta3
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_type_mask_chunk20_direct_beta4
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_type_mask_chunk20_direct_beta5


theorem kernel_s9c5_type_mask_chunk20_beta0 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 320)
    let row := kernelS9C5UniformRow (i.val + 320)
    ∀ I ∈ kernelS9C5TypeChunk0,
      (I ∩ R).Nonempty → 2 * I.card ≤ (I ∩ R).card * row.2 + kernelS9C5PartialBound 0 ⟨i.val + 320, by omega⟩ := by
  decide +kernel

theorem kernel_s9c5_type_mask_chunk20_sum0 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 320)
    let row := kernelS9C5UniformRow (i.val + 320)
    (∑ I ∈ kernelS9C5TypeChunk0,
      if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * row.2 else 0) ≤
      kernelS9C5PartialBound 0 ⟨i.val + 320, by omega⟩ := by
  decide +kernel

theorem kernel_s9c5_type_mask_chunk20_beta1 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 320)
    let row := kernelS9C5UniformRow (i.val + 320)
    ∀ I ∈ kernelS9C5TypeChunk1,
      (I ∩ R).Nonempty → 2 * I.card ≤ (I ∩ R).card * row.2 + kernelS9C5PartialBound 1 ⟨i.val + 320, by omega⟩ := by
  decide +kernel

theorem kernel_s9c5_type_mask_chunk20_sum1 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 320)
    let row := kernelS9C5UniformRow (i.val + 320)
    (∑ I ∈ kernelS9C5TypeChunk1,
      if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * row.2 else 0) ≤
      kernelS9C5PartialBound 1 ⟨i.val + 320, by omega⟩ := by
  decide +kernel

theorem kernel_s9c5_type_mask_chunk20_beta2 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 320)
    let row := kernelS9C5UniformRow (i.val + 320)
    ∀ I ∈ kernelS9C5TypeChunk2,
      (I ∩ R).Nonempty → 2 * I.card ≤ (I ∩ R).card * row.2 + kernelS9C5PartialBound 2 ⟨i.val + 320, by omega⟩ := by
  decide +kernel

theorem kernel_s9c5_type_mask_chunk20_sum2 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 320)
    let row := kernelS9C5UniformRow (i.val + 320)
    (∑ I ∈ kernelS9C5TypeChunk2,
      if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * row.2 else 0) ≤
      kernelS9C5PartialBound 2 ⟨i.val + 320, by omega⟩ := by
  decide +kernel

theorem kernel_s9c5_type_mask_chunk20_beta3 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 320)
    let row := kernelS9C5UniformRow (i.val + 320)
    ∀ I ∈ kernelS9C5TypeChunk3,
      (I ∩ R).Nonempty → 2 * I.card ≤ (I ∩ R).card * row.2 + kernelS9C5PartialBound 3 ⟨i.val + 320, by omega⟩ := by
  decide +kernel

theorem kernel_s9c5_type_mask_chunk20_sum3 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 320)
    let row := kernelS9C5UniformRow (i.val + 320)
    (∑ I ∈ kernelS9C5TypeChunk3,
      if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * row.2 else 0) ≤
      kernelS9C5PartialBound 3 ⟨i.val + 320, by omega⟩ := by
  decide +kernel

theorem kernel_s9c5_type_mask_chunk20_beta4 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 320)
    let row := kernelS9C5UniformRow (i.val + 320)
    ∀ I ∈ kernelS9C5TypeChunk4,
      (I ∩ R).Nonempty → 2 * I.card ≤ (I ∩ R).card * row.2 + kernelS9C5PartialBound 4 ⟨i.val + 320, by omega⟩ := by
  decide +kernel

theorem kernel_s9c5_type_mask_chunk20_sum4 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 320)
    let row := kernelS9C5UniformRow (i.val + 320)
    (∑ I ∈ kernelS9C5TypeChunk4,
      if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * row.2 else 0) ≤
      kernelS9C5PartialBound 4 ⟨i.val + 320, by omega⟩ := by
  decide +kernel

theorem kernel_s9c5_type_mask_chunk20_beta5 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 320)
    let row := kernelS9C5UniformRow (i.val + 320)
    ∀ I ∈ kernelS9C5TypeChunk5,
      (I ∩ R).Nonempty → 2 * I.card ≤ (I ∩ R).card * row.2 + kernelS9C5PartialBound 5 ⟨i.val + 320, by omega⟩ := by
  decide +kernel

theorem kernel_s9c5_type_mask_chunk20_sum5 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 320)
    let row := kernelS9C5UniformRow (i.val + 320)
    (∑ I ∈ kernelS9C5TypeChunk5,
      if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * row.2 else 0) ≤
      kernelS9C5PartialBound 5 ⟨i.val + 320, by omega⟩ := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_type_mask_chunk20_beta0
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_type_mask_chunk20_sum0
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_type_mask_chunk20_beta1
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_type_mask_chunk20_sum1
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_type_mask_chunk20_beta2
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_type_mask_chunk20_sum2
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_type_mask_chunk20_beta3
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_type_mask_chunk20_sum3
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_type_mask_chunk20_beta4
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_type_mask_chunk20_sum4
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_type_mask_chunk20_beta5
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c5_type_mask_chunk20_sum5

end Erdos1011
