import R5Kernel.S7C5Structure
import R5Kernel.SmallGraphColoring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000

namespace Erdos1011
open SimpleGraph

/- A triangle-free graph containing a pentagon has at most two neighbors
on that pentagon from any vertex. Only the fixed pentagon is enumerated. -/
theorem kernel_s7_c5_neighbor_count
    {H : SimpleGraph (Fin 7)} [DecidableRel H.Adj]
    (htri : H.CliqueFree 3) (hcycle : cycleGraph 7 5 ≤ H) (v : Fin 7) :
    ((H.neighborFinset v).filter (fun x => x.val < 5)).card ≤ 2 := by
  let I := S7C5.kernelC5Slice (H.neighborFinset v)
  have hI : (cycleGraph 5 5).IsIndepSet (I : Set (Fin 5)) := by
    intro x hx y hy hxy hadj
    have hxv : H.Adj v (S7C5.kernelC5Embedding x) :=
      (H.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hx).2
    have hyv : H.Adj v (S7C5.kernelC5Embedding y) :=
      (H.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hy).2
    have hc : (cycleGraph 7 5).Adj
        (S7C5.kernelC5Embedding x) (S7C5.kernelC5Embedding y) := by
      change x ≠ y ∧ (cycleRel 5 5 x y ∨ cycleRel 5 5 y x) at hadj
      exact ⟨fun h => hadj.1 (S7C5.kernelC5Embedding.injective h), hadj.2⟩
    exact htri _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxv, hyv, hcycle hc⟩)
  have hcard := kernel_c5_local_alpha I hI
  rw [← S7C5.kernel_c5_slice_map, Finset.card_map]
  exact hcard

/- Delete the two extra vertices' incident edges. The remaining graph has
only the pentagon's five edges; the deletions cost at most 3 and 2 edges. -/
theorem kernel_s7_c5_edge_bound
    {H : SimpleGraph (Fin 7)} [DecidableRel H.Adj]
    (htri : H.CliqueFree 3) (hcycle : cycleGraph 7 5 ≤ H) :
    H.edgeFinset.card ≤ 10 := by
  have h6cycle := kernel_s7_c5_neighbor_count htri hcycle 6
  have h6rest : ((H.neighborFinset 6).filter (fun x => ¬ x.val < 5)).card ≤ 1 := by
    have hsub : (H.neighborFinset 6).filter (fun x => ¬ x.val < 5) ⊆ {5} := by
      intro x hx
      obtain ⟨hx, hge⟩ := Finset.mem_filter.mp hx
      have hne := ((H.mem_neighborFinset _ _).mp hx).ne'
      have hneval : x.val ≠ 6 := fun h => hne (Fin.ext h)
      have heq : x = 5 := Fin.ext (by omega)
      simp only [Finset.mem_singleton, heq]
    simpa using Finset.card_le_card hsub
  have h6 : H.degree 6 ≤ 3 := by
    have hs := Finset.card_filter_add_card_filter_not
      (s := H.neighborFinset 6) (fun x => x.val < 5)
    rw [H.card_neighborFinset_eq_degree] at hs
    omega
  let H6 := H.deleteIncidenceSet 6
  have h5 : H6.degree 5 ≤ 2 := by
    have hsub : H6.neighborFinset 5 ⊆
        (H.neighborFinset 5).filter (fun x => x.val < 5) := by
      intro x hx
      have ha := (H6.mem_neighborFinset _ _).mp hx
      obtain ⟨haH, _, hx6⟩ := deleteIncidenceSet_adj.mp ha
      have hx5 := ha.ne'
      have h5val : x.val ≠ 5 := fun h => hx5 (Fin.ext h)
      have h6val : x.val ≠ 6 := fun h => hx6 (Fin.ext h)
      exact Finset.mem_filter.mpr ⟨(H.mem_neighborFinset _ _).mpr haH, by omega⟩
    exact (Finset.card_le_card hsub).trans (kernel_s7_c5_neighbor_count htri hcycle 5)
  have hsub : H6.deleteIncidenceSet 5 ≤ cycleGraph 7 5 := by
    intro x y hadj
    obtain ⟨ha6, hx5, hy5⟩ := deleteIncidenceSet_adj.mp hadj
    obtain ⟨ha, hx6, hy6⟩ := deleteIncidenceSet_adj.mp ha6
    have hx : x.val < 5 := by
      have h5 : x.val ≠ 5 := fun h => hx5 (Fin.ext h)
      have h6 : x.val ≠ 6 := fun h => hx6 (Fin.ext h)
      omega
    have hy : y.val < 5 := by
      have h5 : y.val ≠ 5 := fun h => hy5 (Fin.ext h)
      have h6 : y.val ≠ 6 := fun h => hy6 (Fin.ext h)
      omega
    let a : Fin 5 := ⟨x.val, hx⟩
    let b : Fin 5 := ⟨y.val, hy⟩
    have hne : a ≠ b := fun h => ha.ne (Fin.ext (congrArg (fun z : Fin 5 => z.val) h))
    have hab : (cycleGraph 5 5).Adj a b := by
      by_contra hnot
      obtain ⟨z, haz, hbz⟩ := kernel_c5_nonadjacent_common_neighbor a b hne hnot
      have haz' : (cycleGraph 7 5).Adj x (S7C5.kernelC5Embedding z) := by
        change a ≠ z ∧ (cycleRel 5 5 a z ∨ cycleRel 5 5 z a) at haz
        exact ⟨fun h => haz.1 (Fin.ext (congrArg (fun z : Fin 7 => z.val) h)), haz.2⟩
      have hbz' : (cycleGraph 7 5).Adj y (S7C5.kernelC5Embedding z) := by
        change b ≠ z ∧ (cycleRel 5 5 b z ∨ cycleRel 5 5 z b) at hbz
        exact ⟨fun h => hbz.1 (Fin.ext (congrArg (fun z : Fin 7 => z.val) h)), hbz.2⟩
      exact htri _ (SimpleGraph.is3Clique_triple_iff.mpr
        ⟨ha, hcycle haz', hcycle hbz'⟩)
    change a ≠ b ∧ (cycleRel 5 5 a b ∨ cycleRel 5 5 b a) at hab
    exact ⟨ha.ne, hab.2⟩
  have hc : (cycleGraph 7 5).edgeFinset.card = 5 := by decide +kernel
  have hleft := Finset.card_le_card (SimpleGraph.edgeFinset_mono hsub)
  rw [hc, card_edgeFinset_deleteIncidenceSet,
    show H6.edgeFinset.card = H.edgeFinset.card - H.degree 6 from
      card_edgeFinset_deleteIncidenceSet H 6] at hleft
  omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s7_c5_neighbor_count
run_cmd R5Kernel.checkStandardAxioms ``kernel_s7_c5_edge_bound

end Erdos1011
