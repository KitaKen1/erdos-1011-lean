import R5Kernel.Probes.S11C11OrbitCoverageCardLE5
import R5Kernel.Probes.S11C11Canonical126
import R5Kernel.Probes.S11C11OrbitCoverageComplementChunks

set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1011

def kernelC11ComplementMask (m : Fin 2048) : Fin 2048 :=
  ⟨2047 - m.val, by omega⟩

theorem kernel_c11_smallMask_complement : ∀ m : Fin 2048,
    kernelC11SmallMask (kernelC11ComplementMask m).val =
      (Finset.univ : Finset (Fin 11)) \ kernelC11SmallMask m.val := by
  decide +kernel

theorem kernel_c11_complement_canonical_orbit : ∀ i : Fin 126,
    ∃ c : Fin 126, ∃ d : Fin 22,
      (kernelC11SmallMask (kernelC11CanonicalRep126 c).val).map
          (kernelC11ActionEquiv d).toEmbedding =
        (Finset.univ : Finset (Fin 11)) \
          kernelC11SmallMask (kernelC11CanonicalRep126 i).val := by
  exact kernel_c11_complement_canonical_orbit_split

theorem kernel_c11_map_complement (e : Fin 11 ≃ Fin 11) (S : Finset (Fin 11)) :
    ((Finset.univ : Finset (Fin 11)) \ S).map e.toEmbedding =
      Finset.univ \ S.map e.toEmbedding := by
  rw [Finset.map_sdiff, Finset.map_univ_equiv]

theorem kernel_c11_action_comp : ∀ q d : Fin 22, ∃ t : Fin 22,
    ∀ x : Fin 11, kernelC11Action t x =
      kernelC11Action d (kernelC11Action q x) := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_smallMask_complement
run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_complement_canonical_orbit
run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_map_complement
run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_action_comp

end Erdos1011
