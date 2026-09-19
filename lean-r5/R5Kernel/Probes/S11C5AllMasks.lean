import R5Kernel.Probes.S11C5OrbitData
import R5Kernel.Probes.S11C5BlockSymmetry
import R5Kernel.Probes.S11C5OrbitTransport
import Mathlib.Logic.Equiv.Fintype

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Erdos1011

-- This is a theorem for an arbitrary nonempty vertex subset, not a
-- hypothesis that the externally computed orbit enumeration is complete.
theorem kernel_s11_all_subsets_canonical (R : Finset (Fin 11)) (hR : R.Nonempty) :
    ∃ m : Fin 2048, m.val ∈ kernelS11RepresentativeMasks ∧
      ∃ e : Fin 11 ≃ Fin 11,
        (∀ x y, (cycleGraph 11 5).Adj (e x) (e y) ↔ (cycleGraph 11 5).Adj x y) ∧
        (r5RepMaskSet11 m).map e.toEmbedding = R := by
  obtain ⟨c, d, hc, hd⟩ := kernel_c5_all_subsets_covered (kernelC5Slice R)
  have hcard : (kernelIsoSlice R).card < 7 := by
    have h := Finset.card_le_univ (kernelIsoSlice R)
    simp only [Fintype.card_fin] at h
    omega
  let k : Fin 7 := ⟨(kernelIsoSlice R).card, hcard⟩
  obtain ⟨b, hb⟩ := Equiv.Perm.exists_map_finset_eq (kernelIsoPrefix k) (kernelIsoSlice R)
    (kernel_iso_prefix_card k)
  let a := kernelC5ActionEquiv d
  let e := kernelBlockEquiv a b
  let m := kernelS11Pack c k
  obtain ⟨hparts, hm⟩ := kernel_s11_packed_shapes c hc k
  have hmap : (r5RepMaskSet11 m).map e.toEmbedding = R := by
    change (r5RepMaskSet11 (kernelS11Pack c k)).map
      (kernelBlockEquiv (kernelC5ActionEquiv d) b).toEmbedding = R
    rw [hparts, kernel_block_map_join, hd, hb, kernel_join_slices]
  have hmem : m.val ∈ kernelS11RepresentativeMasks := by
    rcases hm with hm | hm
    · exact hm
    · have hempty : R = ∅ := by
        rw [← hmap]
        change (r5RepMaskSet11 (kernelS11Pack c k)).map e.toEmbedding = ∅
        rw [hm, kernel_s11_zero_mask, Finset.map_empty]
      exact (hR.ne_empty hempty).elim
  refine ⟨m, hmem, e, ?_, hmap⟩
  exact kernel_block_adj a b (kernel_c5_action_adj d)

-- A complete dual certificate exists for every nonempty subset of C5 + 6K1.
-- Its numerical bound is the original bound 284 at common denominator 2.
theorem kernel_s11_all_nonempty_certificates (R : Finset (Fin 11)) (hR : R.Nonempty) :
    ∃ b : ℕ, ∃ w : Fin 11 → ℕ,
      (∀ I ∈ cycleTypes 11 5, I ⊆ R → I.card ≤ b) ∧
      R5Kernel.dualValue (cycleTypes 11 5) R b 2 w ≤ 284 := by
  obtain ⟨m, hm, e, hadj, hmap⟩ := kernel_s11_all_subsets_canonical R hR
  obtain ⟨b, w, hw⟩ := kernel_s11_canonical_orbit_certificate m hm e hadj
  exact ⟨b, w, by simpa only [hmap] using hw⟩

#print axioms kernel_s11_all_nonempty_certificates
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_all_subsets_canonical
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11_all_nonempty_certificates

end Erdos1011
