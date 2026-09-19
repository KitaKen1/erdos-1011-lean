import R5Kernel.R5TypeChunks

set_option Elab.async false
set_option maxHeartbeats 30000000
set_option maxRecDepth 200000

namespace Erdos1011

-- Enumerate the bounded finset, not the whole finite ambient type.
attribute [local instance 2000] Finset.decidableDforallFinset
open scoped BigOperators

theorem kernel_s9c7_type_mask_chunk6_direct_beta0 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 96)
    let row := kernelS9C7UniformRow (i.val + 96)
    ∀ I ∈ kernelS9C7TypeChunk0,
      I ⊆ R → I.card ≤ row.1 := by
  decide +kernel

theorem kernel_s9c7_type_mask_chunk6_direct_beta1 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 96)
    let row := kernelS9C7UniformRow (i.val + 96)
    ∀ I ∈ kernelS9C7TypeChunk1,
      I ⊆ R → I.card ≤ row.1 := by
  decide +kernel

theorem kernel_s9c7_type_mask_chunk6_direct_beta2 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 96)
    let row := kernelS9C7UniformRow (i.val + 96)
    ∀ I ∈ kernelS9C7TypeChunk2,
      I ⊆ R → I.card ≤ row.1 := by
  decide +kernel

theorem kernel_s9c7_type_mask_chunk6_direct_beta3 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 96)
    let row := kernelS9C7UniformRow (i.val + 96)
    ∀ I ∈ kernelS9C7TypeChunk3,
      I ⊆ R → I.card ≤ row.1 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_type_mask_chunk6_direct_beta0
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_type_mask_chunk6_direct_beta1
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_type_mask_chunk6_direct_beta2
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_type_mask_chunk6_direct_beta3


theorem kernel_s9c7_type_mask_chunk6_beta0 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 96)
    let row := kernelS9C7UniformRow (i.val + 96)
    ∀ I ∈ kernelS9C7TypeChunk0,
      (I ∩ R).Nonempty → 2 * I.card ≤ (I ∩ R).card * row.2 + kernelS9C7PartialBound 0 ⟨i.val + 96, by omega⟩ := by
  decide +kernel

theorem kernel_s9c7_type_mask_chunk6_sum0 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 96)
    let row := kernelS9C7UniformRow (i.val + 96)
    (∑ I ∈ kernelS9C7TypeChunk0,
      if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * row.2 else 0) ≤
      kernelS9C7PartialBound 0 ⟨i.val + 96, by omega⟩ := by
  decide +kernel

theorem kernel_s9c7_type_mask_chunk6_beta1 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 96)
    let row := kernelS9C7UniformRow (i.val + 96)
    ∀ I ∈ kernelS9C7TypeChunk1,
      (I ∩ R).Nonempty → 2 * I.card ≤ (I ∩ R).card * row.2 + kernelS9C7PartialBound 1 ⟨i.val + 96, by omega⟩ := by
  decide +kernel

theorem kernel_s9c7_type_mask_chunk6_sum1 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 96)
    let row := kernelS9C7UniformRow (i.val + 96)
    (∑ I ∈ kernelS9C7TypeChunk1,
      if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * row.2 else 0) ≤
      kernelS9C7PartialBound 1 ⟨i.val + 96, by omega⟩ := by
  decide +kernel

theorem kernel_s9c7_type_mask_chunk6_beta2 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 96)
    let row := kernelS9C7UniformRow (i.val + 96)
    ∀ I ∈ kernelS9C7TypeChunk2,
      (I ∩ R).Nonempty → 2 * I.card ≤ (I ∩ R).card * row.2 + kernelS9C7PartialBound 2 ⟨i.val + 96, by omega⟩ := by
  decide +kernel

theorem kernel_s9c7_type_mask_chunk6_sum2 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 96)
    let row := kernelS9C7UniformRow (i.val + 96)
    (∑ I ∈ kernelS9C7TypeChunk2,
      if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * row.2 else 0) ≤
      kernelS9C7PartialBound 2 ⟨i.val + 96, by omega⟩ := by
  decide +kernel

theorem kernel_s9c7_type_mask_chunk6_beta3 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 96)
    let row := kernelS9C7UniformRow (i.val + 96)
    ∀ I ∈ kernelS9C7TypeChunk3,
      (I ∩ R).Nonempty → 2 * I.card ≤ (I ∩ R).card * row.2 + kernelS9C7PartialBound 3 ⟨i.val + 96, by omega⟩ := by
  decide +kernel

theorem kernel_s9c7_type_mask_chunk6_sum3 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 96)
    let row := kernelS9C7UniformRow (i.val + 96)
    (∑ I ∈ kernelS9C7TypeChunk3,
      if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * row.2 else 0) ≤
      kernelS9C7PartialBound 3 ⟨i.val + 96, by omega⟩ := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_type_mask_chunk6_beta0
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_type_mask_chunk6_sum0
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_type_mask_chunk6_beta1
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_type_mask_chunk6_sum1
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_type_mask_chunk6_beta2
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_type_mask_chunk6_sum2
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_type_mask_chunk6_beta3
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c7_type_mask_chunk6_sum3

end Erdos1011
