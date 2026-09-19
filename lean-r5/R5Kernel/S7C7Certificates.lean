import R5Kernel.S7C7Checks
import R5Kernel.S7C7Symmetry
import R5Kernel.GraphSymmetry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S7C7
open scoped BigOperators

theorem all_nonempty_certificates (R : Finset (Fin 7)) (hR : R.Nonempty) :
    ∃ b : ℕ, ∃ w : Fin 7 → ℕ,
      (∀ I ∈ cycleTypes 7 7, I ⊆ R → I.card ≤ b) ∧
      R5Kernel.dualValue (cycleTypes 7 7) R b 2 w ≤ 54 := by
  obtain ⟨m, hm, e, hadj, hmap⟩ := kernel_s7_all_subsets_canonical R hR
  have hv := (value_le_cover m.val).trans (all_cover_bounds m.val hm)
  have ht := R5Kernel.graph_dualCertificate_transport
    (cycleGraph 7 7) (cycleGraph 7 7) e hadj (maskSet m)
    (kernelS7Row m.val).1 2 54 (weight m.val)
    (canonical_beta m.val hm) hv
  refine ⟨(kernelS7Row m.val).1, (fun y => weight m.val (e.symm y)), ?_⟩
  simpa only [hmap, R5Kernel.independentFamily, cycleTypes] using ht

theorem supportSurplus_le_27 {A B : Finset (Finset (Fin 7))}
    (hAU : A ⊆ cycleTypes 7 7) (hBU : B ⊆ cycleTypes 7 7)
    (hcompat : DegreeCompatible A B) : supportSurplus A B ≤ 27 := by
  have h : 2 * supportSurplus A B ≤ 54 :=
    kernel_supportSurplus_scaled_of_certificates hAU hBU hcompat
      all_nonempty_certificates
  omega

run_cmd R5Kernel.checkStandardAxioms ``all_nonempty_certificates
run_cmd R5Kernel.checkStandardAxioms ``supportSurplus_le_27

end Erdos1011.S7C7
