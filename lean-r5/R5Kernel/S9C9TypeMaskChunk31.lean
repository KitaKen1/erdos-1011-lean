import R5Kernel.R5TypeChunks

set_option Elab.async false
set_option maxHeartbeats 30000000
set_option maxRecDepth 200000

namespace Erdos1011

-- Enumerate the bounded finset, not the whole finite ambient type.
attribute [local instance 2000] Finset.decidableDforallFinset
open scoped BigOperators

theorem kernel_s9c9_type_mask_chunk31_direct_beta0 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 496)
    let row := kernelS9C9UniformRow (i.val + 496)
    ∀ I ∈ kernelS9C9TypeChunk0,
      I ⊆ R → I.card ≤ row.1 := by
  decide +kernel

theorem kernel_s9c9_type_mask_chunk31_direct_beta1 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 496)
    let row := kernelS9C9UniformRow (i.val + 496)
    ∀ I ∈ kernelS9C9TypeChunk1,
      I ⊆ R → I.card ≤ row.1 := by
  decide +kernel

theorem kernel_s9c9_type_mask_chunk31_direct_beta2 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 496)
    let row := kernelS9C9UniformRow (i.val + 496)
    ∀ I ∈ kernelS9C9TypeChunk2,
      I ⊆ R → I.card ≤ row.1 := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_type_mask_chunk31_direct_beta0
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_type_mask_chunk31_direct_beta1
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_type_mask_chunk31_direct_beta2


theorem kernel_s9c9_type_mask_chunk31_beta0 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 496)
    let row := kernelS9C9UniformRow (i.val + 496)
    ∀ I ∈ kernelS9C9TypeChunk0,
      (I ∩ R).Nonempty → 2 * I.card ≤ (I ∩ R).card * row.2 + kernelS9C9PartialBound 0 ⟨i.val + 496, by omega⟩ := by
  decide +kernel

theorem kernel_s9c9_type_mask_chunk31_sum0 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 496)
    let row := kernelS9C9UniformRow (i.val + 496)
    (∑ I ∈ kernelS9C9TypeChunk0,
      if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * row.2 else 0) ≤
      kernelS9C9PartialBound 0 ⟨i.val + 496, by omega⟩ := by
  decide +kernel

theorem kernel_s9c9_type_mask_chunk31_beta1 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 496)
    let row := kernelS9C9UniformRow (i.val + 496)
    ∀ I ∈ kernelS9C9TypeChunk1,
      (I ∩ R).Nonempty → 2 * I.card ≤ (I ∩ R).card * row.2 + kernelS9C9PartialBound 1 ⟨i.val + 496, by omega⟩ := by
  decide +kernel

theorem kernel_s9c9_type_mask_chunk31_sum1 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 496)
    let row := kernelS9C9UniformRow (i.val + 496)
    (∑ I ∈ kernelS9C9TypeChunk1,
      if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * row.2 else 0) ≤
      kernelS9C9PartialBound 1 ⟨i.val + 496, by omega⟩ := by
  decide +kernel

theorem kernel_s9c9_type_mask_chunk31_beta2 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 496)
    let row := kernelS9C9UniformRow (i.val + 496)
    ∀ I ∈ kernelS9C9TypeChunk2,
      (I ∩ R).Nonempty → 2 * I.card ≤ (I ∩ R).card * row.2 + kernelS9C9PartialBound 2 ⟨i.val + 496, by omega⟩ := by
  decide +kernel

theorem kernel_s9c9_type_mask_chunk31_sum2 : ∀ i : Fin 16,
    let R := kernelSmallMask 9 (i.val + 496)
    let row := kernelS9C9UniformRow (i.val + 496)
    (∑ I ∈ kernelS9C9TypeChunk2,
      if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * row.2 else 0) ≤
      kernelS9C9PartialBound 2 ⟨i.val + 496, by omega⟩ := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_type_mask_chunk31_beta0
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_type_mask_chunk31_sum0
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_type_mask_chunk31_beta1
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_type_mask_chunk31_sum1
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_type_mask_chunk31_beta2
run_cmd R5Kernel.checkStandardAxioms ``kernel_s9c9_type_mask_chunk31_sum2

end Erdos1011
