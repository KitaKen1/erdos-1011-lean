import R5Kernel.S10C7Checks0
import R5Kernel.S10C7Checks1
import R5Kernel.S10C7Checks2
import R5Kernel.S10C7Checks3
import R5Kernel.S10C7Checks4
import R5Kernel.S10C7Checks5
import R5Kernel.S10C7Checks6
import R5Kernel.S10C7Checks7
import R5Kernel.S10C7Checks8
import R5Kernel.S10C7Symmetry
import R5Kernel.GraphSymmetry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S10C7
open scoped BigOperators

theorem all_cover_bounds (m : ℕ) (hm : m ∈ kernelS10RepresentativeMasks) :
    coverValue m ≤ 214 := by
  have hblocks : ∀ m ∈ kernelS10RepresentativeMasks,
      m ∈ block0 ∨ m ∈ block1 ∨ m ∈ block2 ∨ m ∈ block3 ∨ m ∈ block4 ∨ m ∈ block5 ∨ m ∈ block6 ∨ m ∈ block7 ∨ m ∈ block8 := by decide +kernel
  rcases hblocks m hm with h | h | h | h | h | h | h | h | h
  · exact cover_bound_block0 m h
  · exact cover_bound_block1 m h
  · exact cover_bound_block2 m h
  · exact cover_bound_block3 m h
  · exact cover_bound_block4 m h
  · exact cover_bound_block5 m h
  · exact cover_bound_block6 m h
  · exact cover_bound_block7 m h
  · exact cover_bound_block8 m h

theorem all_nonempty_certificates (R : Finset (Fin 10)) (hR : R.Nonempty) :
    ∃ b : ℕ, ∃ w : Fin 10 → ℕ,
      (∀ I ∈ cycleTypes 10 7, I ⊆ R → I.card ≤ b) ∧
      R5Kernel.dualValue (cycleTypes 10 7) R b 2 w ≤ 214 := by
  obtain ⟨m, hm, e, hadj, hmap⟩ := kernel_s10_all_subsets_canonical R hR
  have hv := (value_le_cover m.val).trans (all_cover_bounds m.val hm)
  have ht := R5Kernel.graph_dualCertificate_transport
    (cycleGraph 10 7) (cycleGraph 10 7) e hadj (maskSet m)
    (kernelS10Row m.val).1 2 214 (fun _ => (kernelS10Row m.val).2)
    (canonical_beta m.val hm) hv
  refine ⟨(kernelS10Row m.val).1, (fun _ => (kernelS10Row m.val).2), ?_⟩
  simpa only [hmap, R5Kernel.independentFamily, cycleTypes] using ht

theorem supportSurplus_le_107 {A B : Finset (Finset (Fin 10))}
    (hAU : A ⊆ cycleTypes 10 7) (hBU : B ⊆ cycleTypes 10 7)
    (hcompat : DegreeCompatible A B) : supportSurplus A B ≤ 107 := by
  have h : 2 * supportSurplus A B ≤ 214 :=
    kernel_supportSurplus_scaled_of_certificates hAU hBU hcompat
      all_nonempty_certificates
  omega

run_cmd R5Kernel.checkStandardAxioms ``all_cover_bounds
run_cmd R5Kernel.checkStandardAxioms ``all_nonempty_certificates
run_cmd R5Kernel.checkStandardAxioms ``supportSurplus_le_107

end Erdos1011.S10C7
