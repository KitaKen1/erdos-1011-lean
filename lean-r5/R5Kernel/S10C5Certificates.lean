import R5Kernel.S10C5Checks0
import R5Kernel.S10C5Checks1
import R5Kernel.S10C5Checks2
import R5Kernel.S10C5Checks3
import R5Kernel.S10C5Checks4
import R5Kernel.S10C5Checks5
import R5Kernel.S10C5Symmetry
import R5Kernel.GraphSymmetry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace Erdos1011.S10C5

theorem all_cover_bounds (m : ℕ) (hm : m ∈ kernelS10RepresentativeMasks) :
    coverValue m ≤ 226 := by
  have hblocks : ∀ m ∈ kernelS10RepresentativeMasks,
      m ∈ block0 ∨ m ∈ block1 ∨ m ∈ block2 ∨
      m ∈ block3 ∨ m ∈ block4 ∨ m ∈ block5 := by decide +kernel
  rcases hblocks m hm with h | h | h | h | h | h
  · exact cover_bound_block0 m h
  · exact cover_bound_block1 m h
  · exact cover_bound_block2 m h
  · exact cover_bound_block3 m h
  · exact cover_bound_block4 m h
  · exact cover_bound_block5 m h

theorem all_nonempty_certificates (R : Finset (Fin 10)) (hR : R.Nonempty) :
    ∃ b : ℕ, ∃ w : Fin 10 → ℕ,
      (∀ I ∈ cycleTypes 10 5, I ⊆ R → I.card ≤ b) ∧
      R5Kernel.dualValue (cycleTypes 10 5) R b 2 w ≤ 226 := by
  obtain ⟨m, hm, e, hadj, hmap⟩ := kernel_s10_all_subsets_canonical R hR
  have hv := (value_le_cover m.val).trans (all_cover_bounds m.val hm)
  have ht := R5Kernel.graph_dualCertificate_transport
    (cycleGraph 10 5) (cycleGraph 10 5) e hadj (maskSet m)
    (kernelS10Row m.val).1 2 226 (fun _ => (kernelS10Row m.val).2)
    (canonical_beta m.val hm) hv
  refine ⟨(kernelS10Row m.val).1, (fun _ => (kernelS10Row m.val).2), ?_⟩
  simpa only [hmap, R5Kernel.independentFamily, cycleTypes] using ht

theorem supportSurplus_le_113 {A B : Finset (Finset (Fin 10))}
    (hAU : A ⊆ cycleTypes 10 5) (hBU : B ⊆ cycleTypes 10 5)
    (hcompat : DegreeCompatible A B) : supportSurplus A B ≤ 113 := by
  have h : 2 * supportSurplus A B ≤ 226 :=
    kernel_supportSurplus_scaled_of_certificates hAU hBU hcompat
      all_nonempty_certificates
  omega

run_cmd R5Kernel.checkStandardAxioms ``all_cover_bounds
run_cmd R5Kernel.checkStandardAxioms ``all_nonempty_certificates
run_cmd R5Kernel.checkStandardAxioms ``supportSurplus_le_113

end Erdos1011.S10C5
