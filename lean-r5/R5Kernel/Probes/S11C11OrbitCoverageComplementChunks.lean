import R5Kernel.Probes.S11C11ComplementWitness
import R5Kernel.Audit

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace Erdos1011

theorem kernel_c11_complement_canonical_orbit_split : ∀ i : Fin 126,
    ∃ c : Fin 126, ∃ d : Fin 22,
      (kernelC11SmallMask (kernelC11CanonicalRep126 c).val).map
          (kernelC11ActionEquiv d).toEmbedding =
        (Finset.univ : Finset (Fin 11)) \
          kernelC11SmallMask (kernelC11CanonicalRep126 i).val := by
  intro i
  exact ⟨(kernelC11ComplementWitness i).1, (kernelC11ComplementWitness i).2,
    kernel_c11_complement_witness_valid i⟩

run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_complement_canonical_orbit_split

end Erdos1011
