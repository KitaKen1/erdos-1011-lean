import R5Kernel.Probes.S11C11OrbitTransport
import R5Kernel.Probes.S11C11OrbitCoverage
import R5Kernel.Audit

set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

namespace Erdos1011
open scoped BigOperators

theorem kernel_c11_all_mask_certificate (m : Fin 2048) :
    ∃ b : ℕ, ∃ w : Fin 11 → ℕ,
      (∀ I ∈ cycleTypes 11 11,
        I ⊆ r5RepMaskSet11C11 m → I.card ≤ b) ∧
      R5Kernel.dualValue (cycleTypes 11 11)
        (r5RepMaskSet11C11 m) b 2 w ≤ 206 := by
  let R := r5RepMaskSet11C11 m
  obtain ⟨c, d, hcover⟩ := kernelC11_all_subsets_covered R
  obtain ⟨b, w, hbeta, hvalue⟩ :=
    kernel_c11_canonical_orbit_certificate c d
  have hR :
      (r5RepMaskSet11C11 (kernelC11CanonicalRep126 c)).map
          (kernelC11ActionEquiv d).toEmbedding = R := by
    simpa [r5RepMaskSet11C11, kernelC11SmallMask] using hcover
  refine ⟨b, w, ?_, ?_⟩
  · intro I hI hsub
    apply hbeta I hI
    rw [hR]
    exact hsub
  · simpa [R, hR] using hvalue

run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_all_mask_certificate

end Erdos1011
