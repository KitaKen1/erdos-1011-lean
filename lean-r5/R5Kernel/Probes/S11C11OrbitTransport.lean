import R5Kernel.Probes.S11C11Certificates
import R5Kernel.Probes.S11C11OrbitAction
import R5Kernel.GraphSymmetry
import R5Kernel.Audit

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace Erdos1011
open scoped BigOperators

theorem kernel_c11_canonical_orbit_certificate (i : Fin 126) (d : Fin 22) :
    ∃ b : ℕ, ∃ w : Fin 11 → ℕ,
      (∀ I ∈ cycleTypes 11 11,
        I ⊆ (r5RepMaskSet11C11 (kernelC11CanonicalRep126 i)).map
          (kernelC11ActionEquiv d).toEmbedding → I.card ≤ b) ∧
      R5Kernel.dualValue (cycleTypes 11 11)
        ((r5RepMaskSet11C11 (kernelC11CanonicalRep126 i)).map
          (kernelC11ActionEquiv d).toEmbedding) b 2 w ≤ 206 := by
  let r := kernelC11Row (kernelC11CanonicalRep126 i).val
  have hc := kernel_c11_all_canonical_certificates i
  have htrans := R5Kernel.graph_dualCertificate_transport
    (cycleGraph 11 11) (cycleGraph 11 11) (kernelC11ActionEquiv d)
    (kernel_c11_action_adj d) (r5RepMaskSet11C11 r.mask) r.beta 2 206
    (r5RepScaledNum11C11 r) hc.2.1 (by
      simpa [cycleTypes, R5Kernel.independentFamily, r, r5RepNatScaledValue11C11, R5Kernel.dualValue,
        r5RepMaskSet11C11, r5RepMaskSet11] using hc.2.2)
  refine ⟨r.beta, (fun y => r5RepScaledNum11C11 r ((kernelC11ActionEquiv d).symm y)), ?_⟩
  simpa [cycleTypes, R5Kernel.independentFamily, r, hc.1] using htrans

run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_canonical_orbit_certificate

end Erdos1011
