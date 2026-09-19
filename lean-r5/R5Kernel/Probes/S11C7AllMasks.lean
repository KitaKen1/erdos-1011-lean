import R5Kernel.Probes.S11C7OrbitData
import R5Kernel.Probes.S11C7BlockSymmetry
import R5Kernel.Probes.S11C7OrbitTransport
import Mathlib.Logic.Equiv.Fintype

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Erdos1011

theorem kernel_s11c7_all_subsets_canonical (R : Finset (Fin 11)) (hR : R.Nonempty) :
    ∃ m : Fin 2048, m.val ∈ kernelS11C7RepresentativeMasks ∧
      ∃ e : Fin 11 ≃ Fin 11,
        (∀ x y, (cycleGraph 11 7).Adj (e x) (e y) ↔ (cycleGraph 11 7).Adj x y) ∧
        (r5RepMaskSet11C7 m).map e.toEmbedding = R := by
  obtain ⟨c, d, hc, hd⟩ := kernel_c7_all_subsets_covered (kernelC7Slice R)
  have hcard : (kernelC7IsoSlice R).card < 5 := by
    have h := Finset.card_le_univ (kernelC7IsoSlice R)
    simp only [Fintype.card_fin] at h
    omega
  let k : Fin 5 := ⟨(kernelC7IsoSlice R).card, hcard⟩
  obtain ⟨b, hb⟩ := Equiv.Perm.exists_map_finset_eq (kernelC7IsoPrefix k)
    (kernelC7IsoSlice R) (kernel_c7_iso_prefix_card k)
  let a := kernelC7ActionEquiv d
  let e := kernelC7BlockEquiv a b
  let m := kernelS11C7Pack c k
  obtain ⟨hparts, hm⟩ := kernel_s11c7_packed_shapes c hc k
  have hmap : (r5RepMaskSet11C7 m).map e.toEmbedding = R := by
    change (r5RepMaskSet11C7 (kernelS11C7Pack c k)).map
      (kernelC7BlockEquiv (kernelC7ActionEquiv d) b).toEmbedding = R
    rw [hparts, kernel_c7_block_map_join, hd, hb, kernel_c7_join_slices]
  have hmem : m.val ∈ kernelS11C7RepresentativeMasks := by
    rcases hm with hm | hm
    · exact hm
    · have hempty : R = ∅ := by
        rw [← hmap]
        change (r5RepMaskSet11C7 (kernelS11C7Pack c k)).map e.toEmbedding = ∅
        rw [hm, kernel_s11c7_zero_mask, Finset.map_empty]
      exact (hR.ne_empty hempty).elim
  refine ⟨m, hmem, e, ?_, hmap⟩
  exact kernel_c7_block_adj a b (kernel_c7_action_adj d)

theorem kernel_s11c7_all_nonempty_certificates (R : Finset (Fin 11)) (hR : R.Nonempty) :
    ∃ b : ℕ, ∃ w : Fin 11 → ℕ,
      (∀ I ∈ cycleTypes 11 7, I ⊆ R → I.card ≤ b) ∧
      R5Kernel.dualValue (cycleTypes 11 7) R b 4 w ≤ 516 := by
  obtain ⟨m, hm, e, hadj, hmap⟩ := kernel_s11c7_all_subsets_canonical R hR
  obtain ⟨b, w, hw⟩ := kernel_s11c7_canonical_orbit_certificate m hm e hadj
  exact ⟨b, w, by simpa only [hmap] using hw⟩

#print axioms kernel_s11c7_all_nonempty_certificates
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c7_all_subsets_canonical
run_cmd R5Kernel.checkStandardAxioms ``kernel_s11c7_all_nonempty_certificates

end Erdos1011
