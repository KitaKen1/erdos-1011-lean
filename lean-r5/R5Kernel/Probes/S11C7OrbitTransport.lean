import R5Kernel.Probes.S11C7AllCertificates
import R5Kernel.GraphSymmetry
import R5Kernel.Probes.S11C7BlockSymmetry

set_option Elab.async false

namespace Erdos1011

theorem kernel_s11c7_canonical_orbit_certificate (m : Fin 2048)
    (hm : m.val ∈ kernelS11C7RepresentativeMasks) (e : Fin 11 ≃ Fin 11)
    (hadj : ∀ x y, (cycleGraph 11 7).Adj (e x) (e y) ↔ (cycleGraph 11 7).Adj x y) :
    ∃ b : ℕ, ∃ w : Fin 11 → ℕ,
      (∀ I ∈ cycleTypes 11 7,
        I ⊆ (r5RepMaskSet11C7 m).map e.toEmbedding → I.card ≤ b) ∧
      R5Kernel.dualValue (cycleTypes 11 7)
        ((r5RepMaskSet11C7 m).map e.toEmbedding) b 4 w ≤ 516 := by
  have hc := kernel_s11c7_all_canonical_certificates m hm
  let r := kernelS11C7Row m.val
  have htrans :
      (∀ I ∈ cycleTypes 11 7,
        I ⊆ (r5RepMaskSet11C7 r.mask).map e.toEmbedding → I.card ≤ r.beta) ∧
      R5Kernel.dualValue (cycleTypes 11 7)
        ((r5RepMaskSet11C7 r.mask).map e.toEmbedding) r.beta 4
        (fun y => r5RepScaledNum11C7 r (e.symm y)) ≤ 516 :=
    R5Kernel.graph_dualCertificate_transport (cycleGraph 11 7) (cycleGraph 11 7)
      e hadj (r5RepMaskSet11C7 r.mask) r.beta 4 516
      (r5RepScaledNum11C7 r) hc.2.1 hc.2.2
  refine ⟨r.beta, (fun y => r5RepScaledNum11C7 r (e.symm y)), ?_⟩
  have hr : r.mask = m := hc.1
  simpa only [hr] using htrans

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c7_canonical_orbit_certificate

end Erdos1011
