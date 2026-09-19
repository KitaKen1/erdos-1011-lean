import R5Kernel.Probes.S11C9AllCertificates
import R5Kernel.GraphSymmetry
import R5Kernel.Probes.S11C9BlockSymmetry

set_option Elab.async false

namespace Erdos1011

theorem kernel_s11c9_canonical_orbit_certificate (m : Fin 2048)
    (hm : m.val ∈ kernelS11C9RepresentativeMasks) (e : Fin 11 ≃ Fin 11)
    (hadj : ∀ x y, (cycleGraph 11 9).Adj (e x) (e y) ↔ (cycleGraph 11 9).Adj x y) :
    ∃ b : ℕ, ∃ w : Fin 11 → ℕ,
      (∀ I ∈ cycleTypes 11 9,
        I ⊆ (r5RepMaskSet11C9 m).map e.toEmbedding → I.card ≤ b) ∧
      R5Kernel.dualValue (cycleTypes 11 9)
        ((r5RepMaskSet11C9 m).map e.toEmbedding) b 2 w ≤ 232 := by
  have hc := kernel_s11c9_all_canonical_certificates m hm
  let r := kernelS11C9Row m.val
  have htrans :
      (∀ I ∈ cycleTypes 11 9,
        I ⊆ (r5RepMaskSet11C9 r.mask).map e.toEmbedding → I.card ≤ r.beta) ∧
      R5Kernel.dualValue (cycleTypes 11 9)
        ((r5RepMaskSet11C9 r.mask).map e.toEmbedding) r.beta 2
        (fun y => r5RepScaledNum11C9 r (e.symm y)) ≤ 232 :=
    R5Kernel.graph_dualCertificate_transport (cycleGraph 11 9) (cycleGraph 11 9)
      e hadj (r5RepMaskSet11C9 r.mask) r.beta 2 232
      (r5RepScaledNum11C9 r) hc.2.1 hc.2.2
  refine ⟨r.beta, (fun y => r5RepScaledNum11C9 r (e.symm y)), ?_⟩
  have hr : r.mask = m := hc.1
  simpa only [hr] using htrans

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c9_canonical_orbit_certificate

end Erdos1011
