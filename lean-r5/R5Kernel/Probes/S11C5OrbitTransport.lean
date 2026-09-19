import R5Kernel.Probes.S11C5AllCertificates
import R5Kernel.GraphSymmetry

set_option Elab.async false

namespace Erdos1011

-- Any proved graph automorphism transports a fully checked canonical row.
-- Constructing an automorphism for every mask remains a separate obligation.
theorem kernel_s11_canonical_orbit_certificate (m : Fin 2048)
    (hm : m.val ∈ kernelS11RepresentativeMasks) (e : Fin 11 ≃ Fin 11)
    (hadj : ∀ x y, (cycleGraph 11 5).Adj (e x) (e y) ↔ (cycleGraph 11 5).Adj x y) :
    ∃ b : ℕ, ∃ w : Fin 11 → ℕ,
      (∀ I ∈ cycleTypes 11 5, I ⊆ (r5RepMaskSet11 m).map e.toEmbedding → I.card ≤ b) ∧
      R5Kernel.dualValue (cycleTypes 11 5) ((r5RepMaskSet11 m).map e.toEmbedding)
        b 2 w ≤ 284 := by
  have hc := kernel_s11_all_canonical_certificates m hm
  let r := kernelS11Row m.val
  have htrans :
      (∀ I ∈ cycleTypes 11 5,
        I ⊆ (r5RepMaskSet11 r.mask).map e.toEmbedding → I.card ≤ r.beta) ∧
      R5Kernel.dualValue (cycleTypes 11 5) ((r5RepMaskSet11 r.mask).map e.toEmbedding)
        r.beta 2 (fun y => r5RepScaledNum11 r (e.symm y)) ≤ 284 :=
    R5Kernel.graph_dualCertificate_transport (cycleGraph 11 5) (cycleGraph 11 5)
      e hadj (r5RepMaskSet11 r.mask) r.beta 2 284 (r5RepScaledNum11 r) hc.2.1 hc.2.2
  refine ⟨r.beta, (fun y => r5RepScaledNum11 r (e.symm y)), ?_⟩
  have hr : r.mask = m := hc.1
  simpa only [hr] using htrans

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_canonical_orbit_certificate

end Erdos1011
