import R5Kernel.Probes.S11C11NumericBetaChunk0
import R5Kernel.Probes.S11C11NumericBetaChunk1
import R5Kernel.Probes.S11C11NumericBetaChunk2
import R5Kernel.Probes.S11C11NumericBetaChunk3
import R5Kernel.Probes.S11C11CycleTypesExplicit
import R5Kernel.Probes.S11C11Canonical126
import R5Kernel.Audit

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace Erdos1011

theorem kernel_c11_canonical_beta_indexed : ∀ i : Fin 126, ∀ j : Fin 198,
    kernelC11CycleTypeAt j ⊆ r5RepMaskSet11C11
        (kernelC11Row (kernelC11CanonicalRep126 i).val).mask →
      (kernelC11CycleTypeAt j).card ≤
        (kernelC11Row (kernelC11CanonicalRep126 i).val).beta := by
  intro i
  by_cases h0 : i.val < 32
  · let k : Fin 32 := ⟨i.val, h0⟩
    have h := kernel_c11_canonical_beta_chunk0 k
    have hk : (⟨k.val, by omega⟩ : Fin 126) = i := by
      apply Fin.ext
      rfl
    simpa [hk] using h
  · by_cases h1 : i.val < 64
    · let k : Fin 32 := ⟨i.val - 32, by omega⟩
      have h := kernel_c11_canonical_beta_chunk1 k
      have hk : (⟨k.val + 32, by omega⟩ : Fin 126) = i := by
        apply Fin.ext
        dsimp [k]
        omega
      simpa [hk] using h
    · by_cases h2 : i.val < 96
      · let k : Fin 32 := ⟨i.val - 64, by omega⟩
        have h := kernel_c11_canonical_beta_chunk2 k
        have hk : (⟨k.val + 64, by omega⟩ : Fin 126) = i := by
          apply Fin.ext
          dsimp [k]
          omega
        simpa [hk] using h
      · let k : Fin 30 := ⟨i.val - 96, by omega⟩
        have h := kernel_c11_canonical_beta_chunk3 k
        have hk : (⟨k.val + 96, by omega⟩ : Fin 126) = i := by
          apply Fin.ext
          dsimp [k]
          omega
        simpa [hk] using h

theorem kernel_c11_canonical_beta : ∀ i : Fin 126, ∀ I ∈ cycleTypes 11 11,
    I ⊆ r5RepMaskSet11C11
        (kernelC11Row (kernelC11CanonicalRep126 i).val).mask →
      I.card ≤ (kernelC11Row (kernelC11CanonicalRep126 i).val).beta := by
  intro i I hI hsub
  have hI' : I ∈ (Finset.univ : Finset (Fin 198)).image kernelC11CycleTypeAt := by
    rw [← kernel_c11_cycle_types_eq_image]
    exact hI
  rcases Finset.mem_image.mp hI' with ⟨j, _hj, rfl⟩
  exact kernel_c11_canonical_beta_indexed i j hsub

run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_canonical_beta_indexed
run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_canonical_beta

end Erdos1011
