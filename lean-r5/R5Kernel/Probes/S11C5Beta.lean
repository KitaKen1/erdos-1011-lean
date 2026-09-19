import R5Kernel.Probes.S11C5BetaData

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Erdos1011

theorem kernel_s11_beta_of_cycle_bound (R : Finset (Fin 11)) (a b : ℕ)
    (hcycle : ∀ J : Finset (Fin 5),
      (cycleGraph 5 5).IsIndepSet (J : Set (Fin 5)) →
      J ⊆ kernelC5Slice R → J.card ≤ a)
    (hab : a + (R.filter (fun x => ¬ x.val < 5)).card ≤ b)
    (I : Finset (Fin 11)) (hI : (cycleGraph 11 5).IsIndepSet (I : Set (Fin 11)))
    (hIR : I ⊆ R) : I.card ≤ b := by
  have hsub : kernelC5Slice I ⊆ kernelC5Slice R := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hIR (Finset.mem_filter.mp hx).2⟩
  have hc := hcycle (kernelC5Slice I) (kernel_c5_slice_independent I hI) hsub
  have hcard : (I.filter (fun x => x.val < 5)).card ≤ a := by
    rw [← kernel_c5_slice_map, Finset.card_map]
    exact hc
  have hiso := Finset.card_le_card (Finset.filter_subset_filter (fun x => ¬ x.val < 5) hIR)
  have hsplit := Finset.card_filter_add_card_filter_not (s := I) (fun x => x.val < 5)
  omega

theorem kernel_s11_all_canonical_beta : ∀ m ∈ kernelS11RepresentativeMasks,
    ∀ I ∈ cycleTypes 11 5,
      I ⊆ r5RepMaskSet11 (kernelS11Row m).mask → I.card ≤ (kernelS11Row m).beta := by
  intro m hm I hI hIR
  obtain ⟨hsmall, _hmask, hslice, hsize⟩ := kernel_s11_canonical_beta_fields m hm
  apply kernel_s11_beta_of_cycle_bound _ (kernelC5CanonicalAlpha (m % 32)) _ ?_
    hsize I (Finset.mem_filter.mp hI).2.2 hIR
  rw [hslice]
  exact kernel_c5_canonical_beta_data (m % 32) hsmall

theorem kernel_s11_all_canonical_mask (m : Fin 2048)
    (hm : m.val ∈ kernelS11RepresentativeMasks) : (kernelS11Row m.val).mask = m := by
  exact Fin.ext (kernel_s11_canonical_beta_fields m.val hm).2.1

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_beta_of_cycle_bound
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_all_canonical_beta
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_all_canonical_mask

end Erdos1011
