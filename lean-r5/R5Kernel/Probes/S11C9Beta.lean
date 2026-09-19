import R5Kernel.Probes.S11C9BetaData

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Erdos1011

theorem kernel_s11c9_beta_of_cycle_bound (R : Finset (Fin 11)) (a b : ℕ)
    (hcycle : ∀ J : Finset (Fin 9),
      (cycleGraph 9 9).IsIndepSet (J : Set (Fin 9)) →
      J ⊆ kernelC9Slice R → J.card ≤ a)
    (hab : a + (R.filter (fun x => ¬ x.val < 9)).card ≤ b)
    (I : Finset (Fin 11)) (hI : (cycleGraph 11 9).IsIndepSet (I : Set (Fin 11)))
    (hIR : I ⊆ R) : I.card ≤ b := by
  have hsub : kernelC9Slice I ⊆ kernelC9Slice R := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hIR (Finset.mem_filter.mp hx).2⟩
  have hc := hcycle (kernelC9Slice I) (kernel_c9_slice_independent I hI) hsub
  have hcard : (I.filter (fun x => x.val < 9)).card ≤ a := by
    rw [← kernel_c9_slice_map, Finset.card_map]
    exact hc
  have hiso := Finset.card_le_card (Finset.filter_subset_filter (fun x => ¬ x.val < 9) hIR)
  have hsplit := Finset.card_filter_add_card_filter_not (s := I) (fun x => x.val < 9)
  omega

theorem kernel_s11c9_all_canonical_beta : ∀ m ∈ kernelS11C9RepresentativeMasks,
    ∀ I ∈ cycleTypes 11 9,
      I ⊆ r5RepMaskSet11C9 (kernelS11C9Row m).mask →
        I.card ≤ (kernelS11C9Row m).beta := by
  intro m hm I hI hIR
  obtain ⟨hsmall, _hmask, hslice, hsize⟩ := kernel_s11c9_canonical_beta_fields m hm
  apply kernel_s11c9_beta_of_cycle_bound _ (kernelC9CanonicalAlpha (m % 512)) _ ?_
    hsize I (Finset.mem_filter.mp hI).2.2 hIR
  rw [hslice]
  exact kernel_c9_canonical_beta_data (m % 512) hsmall

theorem kernel_s11c9_all_canonical_mask (m : Fin 2048)
    (hm : m.val ∈ kernelS11C9RepresentativeMasks) :
    (kernelS11C9Row m.val).mask = m := by
  exact Fin.ext (kernel_s11c9_canonical_beta_fields m.val hm).2.1

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c9_beta_of_cycle_bound
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c9_all_canonical_beta
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c9_all_canonical_mask

end Erdos1011
