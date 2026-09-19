import R5Kernel.Probes.S11C7BetaData

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Erdos1011

theorem kernel_s11c7_beta_of_cycle_bound (R : Finset (Fin 11)) (a b : ℕ)
    (hcycle : ∀ J : Finset (Fin 7),
      (cycleGraph 7 7).IsIndepSet (J : Set (Fin 7)) →
      J ⊆ kernelC7Slice R → J.card ≤ a)
    (hab : a + (R.filter (fun x => ¬ x.val < 7)).card ≤ b)
    (I : Finset (Fin 11)) (hI : (cycleGraph 11 7).IsIndepSet (I : Set (Fin 11)))
    (hIR : I ⊆ R) : I.card ≤ b := by
  have hsub : kernelC7Slice I ⊆ kernelC7Slice R := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hIR (Finset.mem_filter.mp hx).2⟩
  have hc := hcycle (kernelC7Slice I) (kernel_c7_slice_independent I hI) hsub
  have hcard : (I.filter (fun x => x.val < 7)).card ≤ a := by
    rw [← kernel_c7_slice_map, Finset.card_map]
    exact hc
  have hiso := Finset.card_le_card (Finset.filter_subset_filter (fun x => ¬ x.val < 7) hIR)
  have hsplit := Finset.card_filter_add_card_filter_not (s := I) (fun x => x.val < 7)
  omega

theorem kernel_s11c7_all_canonical_beta : ∀ m ∈ kernelS11C7RepresentativeMasks,
    ∀ I ∈ cycleTypes 11 7,
      I ⊆ r5RepMaskSet11C7 (kernelS11C7Row m).mask →
        I.card ≤ (kernelS11C7Row m).beta := by
  intro m hm I hI hIR
  obtain ⟨hsmall, _hmask, hslice, hsize⟩ := kernel_s11c7_canonical_beta_fields m hm
  apply kernel_s11c7_beta_of_cycle_bound _ (kernelC7CanonicalAlpha (m % 128)) _ ?_
    hsize I (Finset.mem_filter.mp hI).2.2 hIR
  rw [hslice]
  exact kernel_c7_canonical_beta_data (m % 128) hsmall

theorem kernel_s11c7_all_canonical_mask (m : Fin 2048)
    (hm : m.val ∈ kernelS11C7RepresentativeMasks) :
    (kernelS11C7Row m.val).mask = m := by
  exact Fin.ext (kernel_s11c7_canonical_beta_fields m.val hm).2.1

run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c7_beta_of_cycle_bound
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c7_all_canonical_beta
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c7_all_canonical_mask

end Erdos1011
