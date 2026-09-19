import R5Kernel.Probes.S11C11NumericBoundChunk0
import R5Kernel.Probes.S11C11NumericBoundChunk1
import R5Kernel.Probes.S11C11NumericBoundChunk2
import R5Kernel.Probes.S11C11NumericBoundChunk3
import R5Kernel.Audit

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace Erdos1011

theorem kernel_c11_canonical_scaled_bound : ∀ i : Fin 126,
    r5RepNatScaledValue11C11
        (kernelC11Row (kernelC11CanonicalRep126 i).val) ≤ 206 := by
  intro i
  by_cases h0 : i.val < 32
  · let k : Fin 32 := ⟨i.val, h0⟩
    have h := kernel_c11_canonical_scaled_bound_chunk0 k
    have hk : (⟨k.val, by omega⟩ : Fin 126) = i := by
      apply Fin.ext
      rfl
    simpa [hk] using h
  · by_cases h1 : i.val < 64
    · let k : Fin 32 := ⟨i.val - 32, by omega⟩
      have h := kernel_c11_canonical_scaled_bound_chunk1 k
      have hk : (⟨k.val + 32, by omega⟩ : Fin 126) = i := by
        apply Fin.ext
        dsimp [k]
        omega
      simpa [hk] using h
    · by_cases h2 : i.val < 96
      · let k : Fin 32 := ⟨i.val - 64, by omega⟩
        have h := kernel_c11_canonical_scaled_bound_chunk2 k
        have hk : (⟨k.val + 64, by omega⟩ : Fin 126) = i := by
          apply Fin.ext
          dsimp [k]
          omega
        simpa [hk] using h
      · let k : Fin 30 := ⟨i.val - 96, by omega⟩
        have h := kernel_c11_canonical_scaled_bound_chunk3 k
        have hk : (⟨k.val + 96, by omega⟩ : Fin 126) = i := by
          apply Fin.ext
          dsimp [k]
          omega
        simpa [hk] using h

run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_canonical_scaled_bound

end Erdos1011
