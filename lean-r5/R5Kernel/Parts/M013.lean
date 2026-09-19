import R5Kernel.Parts.M012

/- Source module: Erdos1011.EdgeDecomposition. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_EdgeDecomposition


namespace Erdos1011

open SimpleGraph
open scoped BigOperators

/-! 
The upper-bound argument counts edges by splitting the vertex set into the two
endpoints of a distinguished edge, its two sides, and the residual set.  This
file starts that graph-to-arithmetic interface with an oriented adjacency
count.  Using oriented pairs avoids any dependence on a choice of ordering for
`Sym2`; the handshake identity is supplied by `DegreeAverage`.
-/

/-- Number of oriented edges from `P` to `Q`. -/
def adjPairCount {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) : ℕ :=
  ∑ x ∈ P, ∑ y ∈ Q, if G.Adj x y then 1 else 0

theorem vertexDegree_eq_univ_adj_sum
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n) :
    vertexDegree G x =
      ∑ y ∈ (Finset.univ : Finset (Fin n)), if G.Adj x y then 1 else 0 := by
  classical
  unfold vertexDegree
  let hs : (G.neighborSet x).Finite := Set.toFinite _
  rw [Set.ncard_eq_toFinset_card (G.neighborSet x) hs]
  have hfilter : hs.toFinset =
      (Finset.univ : Finset (Fin n)).filter (G.Adj x) := by
    ext y
    simp only [hs.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborSet]
  rw [hfilter]
  rw [Finset.card_filter]

theorem sum_vertexDegree_eq_adjPairCount_univ
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Finset (Fin n)) :
    (∑ x ∈ P, vertexDegree G x) =
      adjPairCount G P (Finset.univ : Finset (Fin n)) := by
  classical
  unfold adjPairCount
  simp_rw [vertexDegree_eq_univ_adj_sum]

theorem adjPairCount_symm
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) :
    adjPairCount G P Q = adjPairCount G Q P := by
  classical
  unfold adjPairCount
  rw [Finset.sum_comm]
  simp [adj_comm]

theorem adjPairCount_right_union
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q R : Finset (Fin n)) (hQR : Disjoint Q R) :
    adjPairCount G P (Q ∪ R) =
      adjPairCount G P Q + adjPairCount G P R := by
  classical
  unfold adjPairCount
  simp_rw [Finset.sum_union hQR, Finset.sum_add_distrib]

/- Finite-set representatives of the residual partition.  These are kept
   separate from the support families: they include vertices with empty
   residual type as well. -/
noncomputable def sideAFinset
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) : Finset (Fin n) := by
  classical
  exact (Set.toFinite (edgeSideASet G u v)).toFinset

noncomputable def sideBFinset
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) : Finset (Fin n) := by
  classical
  exact (Set.toFinite (edgeSideBSet G u v)).toFinset

noncomputable def residualFinset
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) : Finset (Fin n) := by
  classical
  exact (Set.toFinite (residualSet G u v)).toFinset

theorem mem_sideAFinset_iff
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v x : Fin n} :
    x ∈ sideAFinset G u v ↔ x ∈ edgeSideASet G u v := by
  simp [sideAFinset]

theorem mem_sideBFinset_iff
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v x : Fin n} :
    x ∈ sideBFinset G u v ↔ x ∈ edgeSideBSet G u v := by
  simp [sideBFinset]

theorem mem_residualFinset_iff
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v x : Fin n} :
    x ∈ residualFinset G u v ↔ x ∈ residualSet G u v := by
  simp [residualFinset]

theorem sideAFinset_swap_eq_sideBFinset
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    sideAFinset G v u = sideBFinset G u v := by
  ext x
  rw [mem_sideAFinset_iff, mem_sideBFinset_iff]
  rfl

theorem sideBFinset_swap_eq_sideAFinset
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    sideBFinset G v u = sideAFinset G u v := by
  exact (sideAFinset_swap_eq_sideBFinset G v u).symm

theorem endpoint_side_residual_partition
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    (Finset.univ : Finset (Fin n)) =
      ({u} : Finset (Fin n)) ∪ {v} ∪ sideAFinset G u v ∪
        sideBFinset G u v ∪ residualFinset G u v := by
  classical
  ext x
  have hparts := residualSet_eq_compl_endpoints_union_sides G u v
  by_cases hxu : x = u
  · subst x
    simp
  by_cases hxv : x = v
  · subst x
    simp
  by_cases hxA : x ∈ edgeSideASet G u v
  · simp [hxA, mem_sideAFinset_iff]
  by_cases hxB : x ∈ edgeSideBSet G u v
  · simp [hxB, mem_sideBFinset_iff]
  have hxS : x ∈ residualSet G u v := by
    rw [hparts]
    simp [hxu, hxv, hxA, hxB]
  simp [mem_residualFinset_iff, hxS]

theorem sideAFinset_card_eq_ncard
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    (sideAFinset G u v).card = (edgeSideASet G u v).ncard := by
  rw [Set.ncard_eq_toFinset_card]
  rfl

theorem sideBFinset_card_eq_ncard
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    (sideBFinset G u v).card = (edgeSideBSet G u v).ncard := by
  rw [Set.ncard_eq_toFinset_card]
  rfl

theorem residualFinset_card_eq_ncard
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    (residualFinset G u v).card = (residualSet G u v).ncard := by
  rw [Set.ncard_eq_toFinset_card]
  rfl

theorem adjPairCount_right_singleton_of_adj
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Finset (Fin n)) (v : Fin n)
    (h : ∀ x ∈ P, G.Adj x v) :
    adjPairCount G P {v} = P.card := by
  classical
  unfold adjPairCount
  simp only [Finset.sum_singleton]
  rw [show P.card = ∑ x ∈ P, (1 : ℕ) by simp]
  apply Finset.sum_congr rfl
  intro x hx
  simp [h x hx]

theorem adjPairCount_right_singleton_of_not_adj
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Finset (Fin n)) (v : Fin n)
    (h : ∀ x ∈ P, ¬ G.Adj x v) :
    adjPairCount G P {v} = 0 := by
  classical
  unfold adjPairCount
  simp only [Finset.sum_singleton]
  apply Finset.sum_eq_zero
  intro x hx
  simp [h x hx]

theorem adjPairCount_eq_zero_of_forall_not_adj
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n))
    (h : ∀ x ∈ P, ∀ y ∈ Q, ¬ G.Adj x y) :
    adjPairCount G P Q = 0 := by
  classical
  unfold adjPairCount
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  simp [h x hx y hy]

theorem endpoint_side_residual_pairwise_disjoint
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (htri : G.CliqueFree 3) {u v : Fin n} (huv : G.Adj u v) :
    Disjoint ({u} : Finset (Fin n)) {v} ∧
      Disjoint (({u} : Finset (Fin n)) ∪ {v}) (sideAFinset G u v) ∧
      Disjoint (({u} : Finset (Fin n)) ∪ {v} ∪ sideAFinset G u v)
        (sideBFinset G u v) ∧
      Disjoint (({u} : Finset (Fin n)) ∪ {v} ∪ sideAFinset G u v ∪
        sideBFinset G u v) (residualFinset G u v) := by
  classical
  have huvne : u ≠ v := huv.ne
  have hUA : Disjoint ({u} : Finset (Fin n)) (sideAFinset G u v) := by
    rw [Finset.disjoint_singleton_left]
    exact fun h => (endpoint_not_mem_edgeSideASet (G := G) (u := u) (v := v))
      ((mem_sideAFinset_iff.mp h))
  have hUB : Disjoint ({u} : Finset (Fin n)) (sideBFinset G u v) := by
    rw [Finset.disjoint_singleton_left]
    exact fun h => (opposite_endpoint_not_mem_edgeSideBSet (G := G) (u := u) (v := v))
      (mem_sideBFinset_iff.mp h)
  have hUS : Disjoint ({u} : Finset (Fin n)) (residualFinset G u v) := by
    rw [Finset.disjoint_singleton_left]
    intro h
    exact (mem_residualFinset_iff.mp h).1 rfl
  have hVA : Disjoint ({v} : Finset (Fin n)) (sideAFinset G u v) := by
    rw [Finset.disjoint_singleton_left]
    exact fun h => (opposite_endpoint_not_mem_edgeSideASet (G := G) (u := u) (v := v))
      (mem_sideAFinset_iff.mp h)
  have hVB : Disjoint ({v} : Finset (Fin n)) (sideBFinset G u v) := by
    rw [Finset.disjoint_singleton_left]
    exact fun h => (endpoint_not_mem_edgeSideBSet (G := G) (u := u) (v := v))
      (mem_sideBFinset_iff.mp h)
  have hVS : Disjoint ({v} : Finset (Fin n)) (residualFinset G u v) := by
    rw [Finset.disjoint_singleton_left]
    intro h
    exact (mem_residualFinset_iff.mp h).2.1 rfl
  have hAB : Disjoint (sideAFinset G u v) (sideBFinset G u v) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact Set.disjoint_left.mp (edgeSide_sets_disjoint htri huv)
      (mem_sideAFinset_iff.mp hxA) (mem_sideBFinset_iff.mp hxB)
  have hAS : Disjoint (sideAFinset G u v) (residualFinset G u v) := by
    rw [Finset.disjoint_left]
    intro x hxA hxS
    exact (mem_residualFinset_iff.mp hxS).2.2.2
      (mem_sideAFinset_iff.mp hxA).1
  have hBS : Disjoint (sideBFinset G u v) (residualFinset G u v) := by
    rw [Finset.disjoint_left]
    intro x hxB hxS
    exact (mem_residualFinset_iff.mp hxS).2.2.1
      (mem_sideBFinset_iff.mp hxB).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Finset.disjoint_left] using huvne
  · exact Finset.disjoint_union_left.mpr ⟨hUA, hVA⟩
  · have hUVB : Disjoint (({u} : Finset (Fin n)) ∪ {v})
        (sideBFinset G u v) :=
      Finset.disjoint_union_left.mpr ⟨hUB, hVB⟩
    exact Finset.disjoint_union_left.mpr ⟨hUVB, hAB⟩
  · have hUVS : Disjoint (({u} : Finset (Fin n)) ∪ {v})
        (residualFinset G u v) :=
      Finset.disjoint_union_left.mpr ⟨hUS, hVS⟩
    have hUVAS : Disjoint ((({u} : Finset (Fin n)) ∪ {v}) ∪
        sideAFinset G u v) (residualFinset G u v) :=
      Finset.disjoint_union_left.mpr ⟨hUVS, hAS⟩
    exact Finset.disjoint_union_left.mpr ⟨hUVAS, hBS⟩

/- The degree sum on the A-side separates into the forced edge to `v`, the
   cross edges to B, and the residual incidences.  The vanishing terms are
   exactly the triangle-free and side-independence conditions. -/
theorem sideA_degree_sum_decomposition
    {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj]
    (htri : G.CliqueFree 3) {u v : Fin n} (huv : G.Adj u v) :
    (∑ x ∈ sideAFinset G u v, vertexDegree G x) =
      (sideAFinset G u v).card +
        adjPairCount G (sideAFinset G u v) (sideBFinset G u v) +
        adjPairCount G (sideAFinset G u v) (residualFinset G u v) := by
  classical
  let A := sideAFinset G u v
  let B := sideBFinset G u v
  let S := residualFinset G u v
  have hparts := endpoint_side_residual_pairwise_disjoint htri huv
  have hcover : (Finset.univ : Finset (Fin n)) =
      (({u} : Finset (Fin n)) ∪ {v} ∪ A ∪ B) ∪ S := by
    simpa [A, B, S, Finset.union_assoc] using
      endpoint_side_residual_partition G u v
  have hsum : (∑ x ∈ A, vertexDegree G x) =
      adjPairCount G A ({u} : Finset (Fin n)) +
      adjPairCount G A ({v} : Finset (Fin n)) +
      adjPairCount G A A + adjPairCount G A B + adjPairCount G A S := by
    rw [sum_vertexDegree_eq_adjPairCount_univ G A, hcover]
    rw [adjPairCount_right_union G A
      ((({u} : Finset (Fin n)) ∪ {v}) ∪ A ∪ B) S hparts.2.2.2]
    rw [adjPairCount_right_union G A
      ((({u} : Finset (Fin n)) ∪ {v}) ∪ A) B hparts.2.2.1]
    rw [adjPairCount_right_union G A
      (({u} : Finset (Fin n)) ∪ {v}) A hparts.2.1]
    rw [adjPairCount_right_union G A ({u} : Finset (Fin n)) {v} hparts.1]
  have hAu : ∀ x ∈ A, ¬ G.Adj x u := by
    intro x hx hxu
    have hxA : x ∈ edgeSideASet G u v :=
      mem_sideAFinset_iff.mp hx
    exact htri _ (SimpleGraph.is3Clique_triple_iff.mpr
      ⟨huv, hxu.symm, hxA.1⟩)
  have hAv : ∀ x ∈ A, G.Adj x v := by
    intro x hx
    exact (mem_sideAFinset_iff.mp hx).1.symm
  have hAA : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ¬ G.Adj x y := by
    intro x hx y hy hxy
    exact edgeSideASet_independent htri u v
      (mem_sideAFinset_iff.mp hx) (mem_sideAFinset_iff.mp hy) hxy
  have hAA0 : ∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y := by
    intro x hx y hy
    by_cases hxy : x = y
    · subst y
      exact G.loopless.irrefl x
    · exact hAA x hx y hy hxy
  have hzU := adjPairCount_right_singleton_of_not_adj G A u hAu
  have hzV := adjPairCount_right_singleton_of_adj G A v hAv
  have hzA := adjPairCount_eq_zero_of_forall_not_adj G A A hAA0
  rw [hzU, hzV, hzA] at hsum
  simpa [A, B, S, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum

theorem sideB_degree_sum_decomposition
    {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj]
    (htri : G.CliqueFree 3) {u v : Fin n} (huv : G.Adj u v) :
    (∑ x ∈ sideBFinset G u v, vertexDegree G x) =
      (sideBFinset G u v).card +
        adjPairCount G (sideBFinset G u v) (sideAFinset G u v) +
        adjPairCount G (sideBFinset G u v) (residualFinset G u v) := by
  classical
  let A := sideAFinset G u v
  let B := sideBFinset G u v
  let S := residualFinset G u v
  have hparts := endpoint_side_residual_pairwise_disjoint htri huv
  have hcover : (Finset.univ : Finset (Fin n)) =
      (({u} : Finset (Fin n)) ∪ {v} ∪ A ∪ B) ∪ S := by
    simpa [A, B, S, Finset.union_assoc] using
      endpoint_side_residual_partition G u v
  have hsum : (∑ x ∈ B, vertexDegree G x) =
      adjPairCount G B ({u} : Finset (Fin n)) +
      adjPairCount G B ({v} : Finset (Fin n)) +
      adjPairCount G B A + adjPairCount G B B + adjPairCount G B S := by
    rw [sum_vertexDegree_eq_adjPairCount_univ G B, hcover]
    rw [adjPairCount_right_union G B
      ((({u} : Finset (Fin n)) ∪ {v}) ∪ A ∪ B) S hparts.2.2.2]
    rw [adjPairCount_right_union G B
      ((({u} : Finset (Fin n)) ∪ {v}) ∪ A) B hparts.2.2.1]
    rw [adjPairCount_right_union G B
      (({u} : Finset (Fin n)) ∪ {v}) A hparts.2.1]
    rw [adjPairCount_right_union G B ({u} : Finset (Fin n)) {v} hparts.1]
  have hBu : ∀ x ∈ B, G.Adj x u := by
    intro x hx
    exact (mem_sideBFinset_iff.mp hx).1.symm
  have hBv : ∀ x ∈ B, ¬ G.Adj x v := by
    intro x hx hxv
    have hxB : x ∈ edgeSideBSet G u v := mem_sideBFinset_iff.mp hx
    exact htri _ (SimpleGraph.is3Clique_triple_iff.mpr
      ⟨huv, hxB.1, hxv.symm⟩)
  have hBB : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → ¬ G.Adj x y := by
    intro x hx y hy hxy
    exact edgeSideBSet_independent htri u v
      (mem_sideBFinset_iff.mp hx) (mem_sideBFinset_iff.mp hy) hxy
  have hBB0 : ∀ x ∈ B, ∀ y ∈ B, ¬ G.Adj x y := by
    intro x hx y hy
    by_cases hxy : x = y
    · subst y
      exact G.loopless.irrefl x
    · exact hBB x hx y hy hxy
  have hzU := adjPairCount_right_singleton_of_adj G B u hBu
  have hzV := adjPairCount_right_singleton_of_not_adj G B v hBv
  have hzB := adjPairCount_eq_zero_of_forall_not_adj G B B hBB0
  rw [hzU, hzV, hzB] at hsum
  simpa [A, B, S, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum

theorem residual_degree_sum_decomposition
    {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj]
    (htri : G.CliqueFree 3) {u v : Fin n} (huv : G.Adj u v) :
    (∑ x ∈ residualFinset G u v, vertexDegree G x) =
      adjPairCount G (residualFinset G u v) (sideAFinset G u v) +
        adjPairCount G (residualFinset G u v) (sideBFinset G u v) +
        adjPairCount G (residualFinset G u v) (residualFinset G u v) := by
  classical
  let A := sideAFinset G u v
  let B := sideBFinset G u v
  let S := residualFinset G u v
  have hparts := endpoint_side_residual_pairwise_disjoint
    (G := G) htri huv
  have hcover : (Finset.univ : Finset (Fin n)) =
      (({u} : Finset (Fin n)) ∪ {v} ∪ A ∪ B) ∪ S := by
    simpa [A, B, S, Finset.union_assoc] using
      endpoint_side_residual_partition G u v
  have hsum : (∑ x ∈ S, vertexDegree G x) =
      adjPairCount G S ({u} : Finset (Fin n)) +
      adjPairCount G S ({v} : Finset (Fin n)) +
      adjPairCount G S A + adjPairCount G S B + adjPairCount G S S := by
    rw [sum_vertexDegree_eq_adjPairCount_univ G S, hcover]
    rw [adjPairCount_right_union G S
      ((({u} : Finset (Fin n)) ∪ {v}) ∪ A ∪ B) S hparts.2.2.2]
    rw [adjPairCount_right_union G S
      ((({u} : Finset (Fin n)) ∪ {v}) ∪ A) B hparts.2.2.1]
    rw [adjPairCount_right_union G S
      (({u} : Finset (Fin n)) ∪ {v}) A hparts.2.1]
    rw [adjPairCount_right_union G S ({u} : Finset (Fin n)) {v} hparts.1]
  have hSu : ∀ x ∈ S, ¬ G.Adj x u := by
    intro x hx hxu
    exact (mem_residualFinset_iff.mp hx).2.2.1 hxu.symm
  have hSv : ∀ x ∈ S, ¬ G.Adj x v := by
    intro x hx hxv
    exact (mem_residualFinset_iff.mp hx).2.2.2 hxv.symm
  have hzU := adjPairCount_right_singleton_of_not_adj G S u hSu
  have hzV := adjPairCount_right_singleton_of_not_adj G S v hSv
  rw [hzU, hzV] at hsum
  simpa [A, B, S, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum

/- Combining the five degree contributions gives an exact oriented edge
   identity.  The final conversion from this identity to the paper's
   `ab + e(H) + W - C` formula only needs the cross-type and residual-edge
   bookkeeping; no further graph partition argument is required. -/
theorem edgeCount_oriented_decomposition
    {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj]
    (htri : G.CliqueFree 3) {u v : Fin n} (huv : G.Adj u v) :
    let A := sideAFinset G u v
    let B := sideBFinset G u v
    let S := residualFinset G u v
    2 * edgeCount G =
      2 * (A.card + B.card + 1) +
        2 * adjPairCount G A B +
        2 * adjPairCount G A S +
        2 * adjPairCount G B S +
        adjPairCount G S S := by
  classical
  let A := sideAFinset G u v
  let B := sideBFinset G u v
  let S := residualFinset G u v
  have hparts := endpoint_side_residual_pairwise_disjoint htri huv
  have hcover : (Finset.univ : Finset (Fin n)) =
      (({u} : Finset (Fin n)) ∪ {v} ∪ A ∪ B) ∪ S := by
    simpa [A, B, S, Finset.union_assoc] using
      endpoint_side_residual_partition G u v
  have hsum := vertexDegree_sum_eq_twice_edgeCount G
  rw [hcover] at hsum
  rw [Finset.sum_union hparts.2.2.2,
    Finset.sum_union hparts.2.2.1,
    Finset.sum_union hparts.2.1,
    Finset.sum_union hparts.1] at hsum
  simp only [Finset.sum_singleton] at hsum
  have hdu : vertexDegree G u = B.card + 1 := by
    rw [vertexDegree_eq_edgeSideB_ncard_add_one huv]
    rw [← sideBFinset_card_eq_ncard G u v]
  have hdv : vertexDegree G v = A.card + 1 := by
    rw [vertexDegree_eq_edgeSideA_ncard_add_one huv]
    rw [← sideAFinset_card_eq_ncard G u v]
  have hA := sideA_degree_sum_decomposition (G := G) htri huv
  have hB := sideB_degree_sum_decomposition (G := G) htri huv
  have hS := residual_degree_sum_decomposition (G := G) htri huv
  rw [hdu, hdv, hA, hB, hS] at hsum
  have hBA : adjPairCount G (sideBFinset G u v) (sideAFinset G u v) =
      adjPairCount G (sideAFinset G u v) (sideBFinset G u v) :=
    adjPairCount_symm G _ _
  have hSA : adjPairCount G (residualFinset G u v) (sideAFinset G u v) =
      adjPairCount G (sideAFinset G u v) (residualFinset G u v) :=
    adjPairCount_symm G _ _
  have hSB : adjPairCount G (residualFinset G u v) (sideBFinset G u v) =
      adjPairCount G (sideBFinset G u v) (residualFinset G u v) :=
    adjPairCount_symm G _ _
  rw [hBA, hSA, hSB] at hsum
  change 2 * edgeCount G = _
  have hEq := hsum.symm
  dsimp [A, B, S] at hEq ⊢
  ring_nf at hEq ⊢
  exact hEq

/- The residual vertices seen from one side are exactly the corresponding
   residual types.  This is the first direct bridge from `adjPairCount` to the
   finite support-family weights. -/
theorem sideA_adjPairCount_eq_type_card_sum
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} :
    adjPairCount G (sideAFinset G u v) (residualFinset G u v) =
      ∑ x ∈ sideAFinset G u v, (residualType G u v x).ncard := by
  classical
  let A := sideAFinset G u v
  let S := residualFinset G u v
  have hfilter (x : Fin n) :
      residualTypeFinset G u v x = S.filter (G.Adj x) := by
    ext z
    simp [S, residualTypeFinset, residualType, mem_residualTypeFinset_iff,
      mem_residualFinset_iff, and_comm, adj_comm]
  unfold adjPairCount
  apply Finset.sum_congr rfl
  intro x hx
  have hcard :
      (residualTypeFinset G u v x).card =
        ∑ y ∈ S, if G.Adj x y then 1 else 0 := by
    rw [hfilter x, Finset.card_filter]
  rw [residualTypeFinset_card_eq_ncard] at hcard
  exact hcard.symm

theorem sideB_adjPairCount_eq_type_card_sum
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} :
    adjPairCount G (sideBFinset G u v) (residualFinset G u v) =
      ∑ x ∈ sideBFinset G u v, (residualType G u v x).ncard := by
  classical
  let B := sideBFinset G u v
  let S := residualFinset G u v
  have hfilter (x : Fin n) :
      residualTypeFinset G u v x = S.filter (G.Adj x) := by
    ext z
    simp [S, residualTypeFinset, residualType, mem_residualTypeFinset_iff,
      mem_residualFinset_iff, and_comm, adj_comm]
  unfold adjPairCount
  apply Finset.sum_congr rfl
  intro x hx
  have hcard :
      (residualTypeFinset G u v x).card =
        ∑ y ∈ S, if G.Adj x y then 1 else 0 := by
    rw [hfilter x, Finset.card_filter]
  rw [residualTypeFinset_card_eq_ncard] at hcard
  exact hcard.symm

theorem supportWeightA_eq_nonemptyType_card_sum
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (hno : ∀ x x', x ∈ edgeSideASet G u v →
      x' ∈ edgeSideASet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x') :
    supportWeight (supportFamilyA G u v) =
      ∑ x ∈ nonemptyATypeVertices G u v,
        (residualTypeFinset G u v x).card := by
  classical
  have hinj : Set.InjOn (fun x : Fin n => residualTypeFinset G u v x)
      (nonemptyATypeVertices G u v) := by
    intro x hx y hy hxy
    by_contra hxy'
    have hx' := mem_nonemptyATypeVertices_iff.mp hx
    have hy' := mem_nonemptyATypeVertices_iff.mp hy
    have htype : residualType G u v x = residualType G u v y := by
      ext z
      have hz := congrArg (fun I : Finset (Fin n) => z ∈ I) hxy
      exact iff_of_eq (by simpa only [mem_residualTypeFinset_iff] using hz)
    exact (hno x y hx'.1 hy'.1 hxy' hx'.2 htype).elim
  unfold supportWeight supportFamilyA
  rw [Finset.sum_image hinj]

theorem supportWeightB_eq_nonemptyType_card_sum
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (hno : ∀ x x', x ∈ edgeSideBSet G u v →
      x' ∈ edgeSideBSet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x') :
    supportWeight (supportFamilyB G u v) =
      ∑ x ∈ nonemptyBTypeVertices G u v,
        (residualTypeFinset G u v x).card := by
  classical
  have hinj : Set.InjOn (fun x : Fin n => residualTypeFinset G u v x)
      (nonemptyBTypeVertices G u v) := by
    intro x hx y hy hxy
    by_contra hxy'
    have hx' := mem_nonemptyBTypeVertices_iff.mp hx
    have hy' := mem_nonemptyBTypeVertices_iff.mp hy
    have htype : residualType G u v x = residualType G u v y := by
      ext z
      have hz := congrArg (fun I : Finset (Fin n) => z ∈ I) hxy
      exact iff_of_eq (by simpa only [mem_residualTypeFinset_iff] using hz)
    exact (hno x y hx'.1 hy'.1 hxy' hx'.2 htype).elim
  unfold supportWeight supportFamilyB
  rw [Finset.sum_image hinj]

theorem supportWeightA_eq_type_card_sum
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (hno : ∀ x x', x ∈ edgeSideASet G u v →
      x' ∈ edgeSideASet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x') :
    supportWeight (supportFamilyA G u v) =
      ∑ x ∈ sideAFinset G u v, (residualType G u v x).ncard := by
  classical
  let A := sideAFinset G u v
  let N := nonemptyATypeVertices G u v
  have hN : N = A.filter (fun x => (residualType G u v x).Nonempty) := by
    ext x
    simp [N, A, nonemptyATypeVertices, sideAFinset]
  have hsub : N ⊆ A := by
    calc
      N = A.filter (fun x => (residualType G u v x).Nonempty) := hN
      _ ⊆ A := by apply Finset.filter_subset
  have hzero : ∀ x ∈ A, x ∉ N →
      (residualType G u v x).ncard = 0 := by
    intro x hx hxn
    have hne : ¬ (residualType G u v x).Nonempty := by
      intro hne
      apply hxn
      rw [hN]
      exact Finset.mem_filter.mpr ⟨hx, hne⟩
    rw [Set.ncard_eq_zero]
    exact Set.not_nonempty_iff_eq_empty.mp hne
  calc
    supportWeight (supportFamilyA G u v) =
        ∑ x ∈ N, (residualTypeFinset G u v x).card := by
      simpa [N] using supportWeightA_eq_nonemptyType_card_sum hno
    _ = ∑ x ∈ N, (residualType G u v x).ncard := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [residualTypeFinset_card_eq_ncard]
    _ = ∑ x ∈ A, (residualType G u v x).ncard := by
      apply Finset.sum_subset hsub
      intro x hx hxn
      exact hzero x hx hxn
    _ = ∑ x ∈ sideAFinset G u v, (residualType G u v x).ncard := by
      rfl

theorem supportWeightB_eq_type_card_sum
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (hno : ∀ x x', x ∈ edgeSideBSet G u v →
      x' ∈ edgeSideBSet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x') :
    supportWeight (supportFamilyB G u v) =
      ∑ x ∈ sideBFinset G u v, (residualType G u v x).ncard := by
  classical
  let B := sideBFinset G u v
  let N := nonemptyBTypeVertices G u v
  have hN : N = B.filter (fun x => (residualType G u v x).Nonempty) := by
    ext x
    simp [N, B, nonemptyBTypeVertices, sideBFinset]
  have hsub : N ⊆ B := by
    calc
      N = B.filter (fun x => (residualType G u v x).Nonempty) := hN
      _ ⊆ B := by apply Finset.filter_subset
  have hzero : ∀ x ∈ B, x ∉ N →
      (residualType G u v x).ncard = 0 := by
    intro x hx hxn
    have hne : ¬ (residualType G u v x).Nonempty := by
      intro hne
      apply hxn
      rw [hN]
      exact Finset.mem_filter.mpr ⟨hx, hne⟩
    rw [Set.ncard_eq_zero]
    exact Set.not_nonempty_iff_eq_empty.mp hne
  calc
    supportWeight (supportFamilyB G u v) =
        ∑ x ∈ N, (residualTypeFinset G u v x).card := by
      simpa [N] using supportWeightB_eq_nonemptyType_card_sum hno
    _ = ∑ x ∈ N, (residualType G u v x).ncard := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [residualTypeFinset_card_eq_ncard]
    _ = ∑ x ∈ B, (residualType G u v x).ncard := by
      apply Finset.sum_subset hsub
      intro x hx hxn
      exact hzero x hx hxn
    _ = ∑ x ∈ sideBFinset G u v, (residualType G u v x).ncard := by
      rfl

theorem supportCross_eq_nonemptyType_vertex_pair_sum
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (hnoA : ∀ x x', x ∈ edgeSideASet G u v →
      x' ∈ edgeSideASet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    (hnoB : ∀ x x', x ∈ edgeSideBSet G u v →
      x' ∈ edgeSideBSet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x') :
    supportCross (supportFamilyA G u v) (supportFamilyB G u v) =
      ∑ y ∈ nonemptyBTypeVertices G u v,
        ∑ x ∈ nonemptyATypeVertices G u v,
          if Disjoint (residualTypeFinset G u v x)
              (residualTypeFinset G u v y) then 0 else 1 := by
  classical
  have hinjA : Set.InjOn (fun x : Fin n => residualTypeFinset G u v x)
      (nonemptyATypeVertices G u v) := by
    intro x hx y hy hxy
    by_contra hxy'
    have hx' := mem_nonemptyATypeVertices_iff.mp hx
    have hy' := mem_nonemptyATypeVertices_iff.mp hy
    have htype : residualType G u v x = residualType G u v y := by
      ext z
      have hz := congrArg (fun I : Finset (Fin n) => z ∈ I) hxy
      exact iff_of_eq (by simpa only [mem_residualTypeFinset_iff] using hz)
    exact (hnoA x y hx'.1 hy'.1 hxy' hx'.2 htype).elim
  have hinjB : Set.InjOn (fun x : Fin n => residualTypeFinset G u v x)
      (nonemptyBTypeVertices G u v) := by
    intro x hx y hy hxy
    by_contra hxy'
    have hx' := mem_nonemptyBTypeVertices_iff.mp hx
    have hy' := mem_nonemptyBTypeVertices_iff.mp hy
    have htype : residualType G u v x = residualType G u v y := by
      ext z
      have hz := congrArg (fun I : Finset (Fin n) => z ∈ I) hxy
      exact iff_of_eq (by simpa only [mem_residualTypeFinset_iff] using hz)
    exact (hnoB x y hx'.1 hy'.1 hxy' hx'.2 htype).elim
  unfold supportCross supportHits supportFamilyA supportFamilyB
  rw [Finset.sum_image hinjB]
  simp_rw [Finset.sum_image hinjA]

/- Extending the preceding identity across the vertices with empty residual
   type is useful because the graph-side edge count uses the full side sets,
   whereas `supportCross` only sees nonempty supports. -/
noncomputable def supportPairIndicator
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v x y : Fin n) : ℕ := by
  classical
  exact if (residualType G u v x).Nonempty ∧
      (residualType G u v y).Nonempty then
    if Disjoint (residualTypeFinset G u v x)
        (residualTypeFinset G u v y) then 0 else 1
  else 0

theorem supportCross_eq_all_side_pair_sum
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (hnoA : ∀ x x', x ∈ edgeSideASet G u v →
      x' ∈ edgeSideASet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    (hnoB : ∀ x x', x ∈ edgeSideBSet G u v →
      x' ∈ edgeSideBSet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x') :
    supportCross (supportFamilyA G u v) (supportFamilyB G u v) =
      ∑ y ∈ sideBFinset G u v,
        ∑ x ∈ sideAFinset G u v,
          supportPairIndicator G u v x y := by
  classical
  let A := sideAFinset G u v
  let B := sideBFinset G u v
  let NA := nonemptyATypeVertices G u v
  let NB := nonemptyBTypeVertices G u v
  have hNA : NA ⊆ A := by
    intro x hx
    exact mem_sideAFinset_iff.mpr (mem_nonemptyATypeVertices_iff.mp hx).1
  have hNB : NB ⊆ B := by
    intro y hy
    exact mem_sideBFinset_iff.mpr (mem_nonemptyBTypeVertices_iff.mp hy).1
  have hcross := supportCross_eq_nonemptyType_vertex_pair_sum hnoA hnoB
  let f (x : Fin n) (y : Fin n) : ℕ := supportPairIndicator G u v x y
  have hinner0 (y : Fin n) (hy : y ∈ NB) :
      (∑ x ∈ NA, if Disjoint (residualTypeFinset G u v x)
          (residualTypeFinset G u v y) then 0 else 1) =
        ∑ x ∈ NA, f x y := by
    apply Finset.sum_congr rfl
    intro x hx
    have hnx : (residualType G u v x).Nonempty :=
      (mem_nonemptyATypeVertices_iff.mp hx).2
    have hny : (residualType G u v y).Nonempty :=
      (mem_nonemptyBTypeVertices_iff.mp hy).2
    simp [f, supportPairIndicator, hnx, hny]
  have hinner (y : Fin n) (hy : y ∈ NB) :
      (∑ x ∈ NA, if Disjoint (residualTypeFinset G u v x)
          (residualTypeFinset G u v y) then 0 else 1) =
        ∑ x ∈ A, f x y := by
    calc
      (∑ x ∈ NA, if Disjoint (residualTypeFinset G u v x)
          (residualTypeFinset G u v y) then 0 else 1) =
          ∑ x ∈ NA, f x y := hinner0 y hy
      _ = ∑ x ∈ A, f x y := by
        apply Finset.sum_subset hNA
        intro x hx hxn
        have hnx : ¬ (residualType G u v x).Nonempty := by
          intro hnx
          apply hxn
          exact Finset.mem_filter.mpr ⟨hx, hnx⟩
        have hny : (residualType G u v y).Nonempty :=
          (mem_nonemptyBTypeVertices_iff.mp hy).2
        simp [f, supportPairIndicator, hnx, hny]
  have houter :
      (∑ y ∈ NB, ∑ x ∈ NA, if Disjoint (residualTypeFinset G u v x)
          (residualTypeFinset G u v y) then 0 else 1) =
        ∑ y ∈ B, ∑ x ∈ A, f x y := by
    calc
      (∑ y ∈ NB, ∑ x ∈ NA, if Disjoint (residualTypeFinset G u v x)
          (residualTypeFinset G u v y) then 0 else 1) =
          ∑ y ∈ NB, ∑ x ∈ A, f x y := by
            apply Finset.sum_congr rfl
            intro y hy
            exact hinner y hy
      _ = ∑ y ∈ B, ∑ x ∈ A, f x y := by
        apply Finset.sum_subset hNB
        intro y hy hyn
        apply Finset.sum_eq_zero
        intro x hx
        have hny : ¬ (residualType G u v y).Nonempty := by
          intro hny
          apply hyn
          exact Finset.mem_filter.mpr ⟨hy, hny⟩
        simp [f, supportPairIndicator, hny]
  calc
    supportCross (supportFamilyA G u v) (supportFamilyB G u v) =
        ∑ y ∈ NB, ∑ x ∈ NA,
          if Disjoint (residualTypeFinset G u v x)
              (residualTypeFinset G u v y) then 0 else 1 := by
      simpa [NA, NB] using hcross
    _ = ∑ y ∈ B, ∑ x ∈ A, f x y := houter
    _ = ∑ y ∈ sideBFinset G u v,
        ∑ x ∈ sideAFinset G u v, supportPairIndicator G u v x y := by
      rfl

/- The preceding support sum is exactly the complement of the graph-side
   cross-edge indicator.  This is the finite form of the paper's
   ``ab-C`` term; vertices whose residual type is empty contribute zero to
   the support indicator, while maximality forces the corresponding cross
   edge. -/
theorem all_cross_pair_partition
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (hmax : IsEdgeMaximalTriangleFree G)
    (huv : G.Adj u v)
    (hnoA : ∀ x x', x ∈ edgeSideASet G u v →
      x' ∈ edgeSideASet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    (hnoB : ∀ x x', x ∈ edgeSideBSet G u v →
      x' ∈ edgeSideBSet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x') :
    adjPairCount G (sideAFinset G u v) (sideBFinset G u v) +
        supportCross (supportFamilyA G u v) (supportFamilyB G u v) =
      (sideAFinset G u v).card * (sideBFinset G u v).card := by
  classical
  have hcross := supportCross_eq_all_side_pair_sum hnoA hnoB
  have hsum :
      adjPairCount G (sideAFinset G u v) (sideBFinset G u v) +
          supportCross (supportFamilyA G u v) (supportFamilyB G u v) =
        ∑ y ∈ sideBFinset G u v,
          ∑ x ∈ sideAFinset G u v,
            ((if G.Adj x y then 1 else 0) +
              supportPairIndicator G u v x y) := by
    unfold adjPairCount
    rw [Finset.sum_comm, hcross]
    rw [← Finset.sum_add_distrib]
    simp only [Finset.sum_add_distrib]
  have hpoint {x y : Fin n}
      (hx : x ∈ sideAFinset G u v)
      (hy : y ∈ sideBFinset G u v) :
      (if G.Adj x y then 1 else 0) +
          supportPairIndicator G u v x y = 1 := by
    have hxA : x ∈ edgeSideASet G u v :=
      (mem_sideAFinset_iff.mp hx)
    have hyB : y ∈ edgeSideBSet G u v :=
      (mem_sideBFinset_iff.mp hy)
    have hiff := cross_adj_iff_residual_disjoint hmax huv hxA hyB
    have hdis : Disjoint (residualTypeFinset G u v x)
          (residualTypeFinset G u v y) ↔
        Disjoint (residualType G u v x) (residualType G u v y) := by
      rw [Finset.disjoint_left, Set.disjoint_left]
      simp only [mem_residualTypeFinset_iff]
    have hiff' : G.Adj x y ↔
        Disjoint (residualTypeFinset G u v x)
          (residualTypeFinset G u v y) := hiff.trans hdis.symm
    by_cases hboth : (residualType G u v x).Nonempty ∧
        (residualType G u v y).Nonempty
    · by_cases hd : Disjoint (residualTypeFinset G u v x)
          (residualTypeFinset G u v y)
      · have ha : G.Adj x y := hiff'.mpr hd
        simp [supportPairIndicator, hboth, ha, hd]
      · have hna : ¬ G.Adj x y := by
          intro ha
          exact hd (hiff'.mp ha)
        simp [supportPairIndicator, hboth, hna, hd]
    · have hdisSet : Disjoint (residualType G u v x)
          (residualType G u v y) := by
        rw [Set.disjoint_left]
        intro z hzx hzy
        by_cases hnx : (residualType G u v x).Nonempty
        · have hny : ¬ (residualType G u v y).Nonempty := by
            intro hny
            exact hboth ⟨hnx, hny⟩
          exact (hny ⟨z, hzy⟩).elim
        · exact (hnx ⟨z, hzx⟩).elim
      have ha : G.Adj x y := hiff.mpr hdisSet
      simp [supportPairIndicator, hboth, ha]
  rw [hsum]
  rw [show (sideAFinset G u v).card * (sideBFinset G u v).card =
      ∑ y ∈ sideBFinset G u v,
        ∑ x ∈ sideAFinset G u v, (1 : ℕ) by simp [Nat.mul_comm]]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  rw [hpoint hx hy]

/- The residual self-pair count is the oriented edge count of the induced
   residual graph.  Keeping this equality explicit prevents a hidden factor
   of two when importing Mantel/Turán bounds. -/
theorem adjPairCount_self_eq_twice_induce_edgeFinset_card
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (S : Finset (Fin n)) :
    adjPairCount G S S =
      2 * (G.induce (S : Set (Fin n))).edgeFinset.card := by
  classical
  let H : SimpleGraph S := G.induce (S : Set (Fin n))
  have hdeg (x : S) :
      H.degree x = ∑ y : S, if H.Adj x y then 1 else 0 := by
    unfold SimpleGraph.degree
    rw [SimpleGraph.neighborFinset_eq_filter]
    rw [← Finset.card_filter]
  have hsum := H.sum_degrees_eq_twice_card_edges
  have hsum' :
      (∑ x : S, ∑ y : S, if H.Adj x y then 1 else 0) =
        2 * H.edgeFinset.card := by
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro x hx
    exact (hdeg x).symm
  have hpair :
      adjPairCount G S S =
        ∑ x : S, ∑ y : S, if G.Adj x y then 1 else 0 := by
    change (∑ x ∈ S, ∑ y ∈ S, if G.Adj x y then 1 else 0) = _
    calc
      (∑ x ∈ S, ∑ y ∈ S, if G.Adj x y then 1 else 0) =
          ∑ x ∈ S, ∑ y : S, if G.Adj x (y : Fin n) then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        exact (Finset.sum_coe_sort S
          (fun y : Fin n => if G.Adj x y then 1 else 0)).symm
      _ = ∑ x : S, ∑ y : S, if G.Adj x y then 1 else 0 := by
        exact (Finset.sum_coe_sort S
          (fun x : Fin n => ∑ y : S, if G.Adj x (y : Fin n) then 1 else 0)).symm
  calc
    adjPairCount G S S =
        ∑ x : S, ∑ y : S, if G.Adj x y then 1 else 0 := hpair
    _ = 2 * H.edgeFinset.card := by
      simpa [H, SimpleGraph.induce_adj] using hsum'
    _ = 2 * (G.induce (S : Set (Fin n))).edgeFinset.card := by
      change 2 * H.edgeFinset.card = 2 * H.edgeFinset.card
      rfl

/- Mantel's bound, expressed in the oriented-pair convention used above. -/

/- Putting the graph-side decomposition and the support-side partition
   together gives the exact additive form of the paper's capacity identity.
   The product uses the full endpoint degrees (`|A|+1`, `|B|+1`), which is
   why the endpoint terms from the handshake expansion disappear here. -/
theorem edgeCount_add_supportCross_eq_full_product_plus_residual
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (hmax : IsEdgeMaximalTriangleFree G)
    (huv : G.Adj u v)
    (hnoA : ∀ x x', x ∈ edgeSideASet G u v →
      x' ∈ edgeSideASet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    (hnoB : ∀ x x', x ∈ edgeSideBSet G u v →
      x' ∈ edgeSideBSet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x') :
    edgeCount G + supportCross (supportFamilyA G u v)
        (supportFamilyB G u v) =
      (sideAFinset G u v).card.succ *
          (sideBFinset G u v).card.succ +
        (G.induce (residualFinset G u v : Set (Fin n))).edgeFinset.card +
        supportWeight (supportFamilyA G u v) +
        supportWeight (supportFamilyB G u v) := by
  classical
  let A := sideAFinset G u v
  let B := sideBFinset G u v
  let S := residualFinset G u v
  have hdecomp := edgeCount_oriented_decomposition (G := G) hmax.1 huv
  dsimp [A, B, S] at hdecomp
  have hcross := all_cross_pair_partition (G := G) hmax huv hnoA hnoB
  have hself := adjPairCount_self_eq_twice_induce_edgeFinset_card
    (G := G) (residualFinset G u v)
  have hWA : supportWeight (supportFamilyA G u v) =
      adjPairCount G (sideAFinset G u v) (residualFinset G u v) := by
    calc
      supportWeight (supportFamilyA G u v) =
          ∑ x ∈ sideAFinset G u v, (residualType G u v x).ncard :=
        supportWeightA_eq_type_card_sum hnoA
      _ = adjPairCount G (sideAFinset G u v) (residualFinset G u v) :=
        (sideA_adjPairCount_eq_type_card_sum (G := G) (u := u) (v := v)).symm
  have hWB : supportWeight (supportFamilyB G u v) =
      adjPairCount G (sideBFinset G u v) (residualFinset G u v) := by
    calc
      supportWeight (supportFamilyB G u v) =
          ∑ x ∈ sideBFinset G u v, (residualType G u v x).ncard :=
        supportWeightB_eq_type_card_sum hnoB
      _ = adjPairCount G (sideBFinset G u v) (residualFinset G u v) :=
        (sideB_adjPairCount_eq_type_card_sum (G := G) (u := u) (v := v)).symm
  have hprod :
      (sideAFinset G u v).card.succ * (sideBFinset G u v).card.succ =
        (sideAFinset G u v).card * (sideBFinset G u v).card +
          (sideAFinset G u v).card + (sideBFinset G u v).card + 1 := by
    simp only [Nat.succ_eq_add_one]
    ring
  rw [hprod]
  rw [hWA, hWB]
  have hself' : adjPairCount G (residualFinset G u v)
      (residualFinset G u v) =
      2 * (G.induce (residualFinset G u v : Set (Fin n))).edgeFinset.card := by
    exact hself
  rw [hself'] at hdecomp
  omega

/- Rewriting the previous additive equality with `supportSurplus = W-C`
   gives the paper's usual (truncated-natural subtraction) presentation. -/

/- A certificate-friendly inequality extracted from the exact identity.  The
   two numerical premises are precisely the residual-edge and support-surplus
   bounds supplied by a finite capacity certificate. -/

/- The additive identity is enough for an upper bound; no separate
   hypothesis `supportCross ≤ W_A + W_B` is needed.  If the cross term is at
   most the total support weight, the truncated subtraction in
   `supportSurplus` is the ordinary difference.  If it is larger, the same
   identity directly gives the stronger bound obtained by dropping the
   nonnegative excess cross term. -/
theorem edgeCount_le_full_product_plus_residual_bound_of_additive
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (hmax : IsEdgeMaximalTriangleFree G)
    (huv : G.Adj u v)
    (hnoA : ∀ x x', x ∈ edgeSideASet G u v →
      x' ∈ edgeSideASet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    (hnoB : ∀ x x', x ∈ edgeSideBSet G u v →
      x' ∈ edgeSideBSet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    {e q : ℕ}
    (he : (G.induce (residualFinset G u v : Set (Fin n))).edgeFinset.card ≤ e)
    (hq : supportSurplus (supportFamilyA G u v)
        (supportFamilyB G u v) ≤ q) :
    edgeCount G ≤
      (sideAFinset G u v).card.succ *
          (sideBFinset G u v).card.succ + e + q := by
  have hadd := edgeCount_add_supportCross_eq_full_product_plus_residual
    (G := G) hmax huv hnoA hnoB
  unfold supportSurplus at hq
  by_cases hCW : supportCross (supportFamilyA G u v)
      (supportFamilyB G u v) ≤
      supportWeight (supportFamilyA G u v) +
        supportWeight (supportFamilyB G u v)
  · have hsub : supportWeight (supportFamilyA G u v) +
        supportWeight (supportFamilyB G u v) -
          supportCross (supportFamilyA G u v)
            (supportFamilyB G u v) ≤ q := hq
    omega
  · have hWC : supportWeight (supportFamilyA G u v) +
        supportWeight (supportFamilyB G u v) ≤
      supportCross (supportFamilyA G u v)
        (supportFamilyB G u v) := by omega
    omega

/- The full endpoint-degree product and the residual cardinality partition the
   vertex set.  This is the `a+b+s=n` side-condition expected by the coarse
   arithmetic dispatcher. -/
theorem full_side_degree_residual_card_sum
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (htri : G.CliqueFree 3) {u v : Fin n} (huv : G.Adj u v) :
    (sideAFinset G u v).card.succ +
        (sideBFinset G u v).card.succ +
        (residualSet G u v).ncard = n := by
  have hsum := degreeSumPair_add_residual_ncard_eq_n htri huv
  unfold degreeSumPair at hsum
  rw [vertexDegree_eq_edgeSideB_ncard_add_one huv,
    vertexDegree_eq_edgeSideA_ncard_add_one huv] at hsum
  rw [← sideBFinset_card_eq_ncard G u v,
    ← sideAFinset_card_eq_ncard G u v] at hsum
  omega

/- The pointwise analogue of `sideA_degree_sum_decomposition`.  For a vertex
   on the A-side, its neighbours split into the distinguished endpoint `v`,
   the opposite side, and its residual type.  This is the local identity used
   to turn the maximum degree-sum choice into the support compatibility rule. -/
theorem vertexDegree_sideA_decomposition
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (htri : G.CliqueFree 3) {u v x : Fin n} (huv : G.Adj u v)
    (hxA : x ∈ edgeSideASet G u v) :
    vertexDegree G x =
      1 + adjPairCount G ({x} : Finset (Fin n)) (sideBFinset G u v) +
        (residualType G u v x).ncard := by
  classical
  let A := sideAFinset G u v
  let B := sideBFinset G u v
  let S := residualFinset G u v
  have hparts := endpoint_side_residual_pairwise_disjoint htri huv
  have hcover : (Finset.univ : Finset (Fin n)) =
      (({u} : Finset (Fin n)) ∪ {v} ∪ A ∪ B) ∪ S := by
    simpa [A, B, S, Finset.union_assoc] using
      endpoint_side_residual_partition G u v
  have hsum := vertexDegree_eq_univ_adj_sum G x
  rw [hcover] at hsum
  rw [Finset.sum_union hparts.2.2.2,
    Finset.sum_union hparts.2.2.1,
    Finset.sum_union hparts.2.1,
    Finset.sum_union hparts.1] at hsum
  simp only [Finset.sum_singleton] at hsum
  have hxu : ¬ G.Adj x u := by
    intro hux
    exact htri _ (SimpleGraph.is3Clique_triple_iff.mpr
      ⟨huv, hux.symm, hxA.1⟩)
  have hxv : G.Adj x v := hxA.1.symm
  have hxx : ∀ y ∈ A, ¬ G.Adj x y := by
    intro y hy
    by_cases hxy : x = y
    · subst y
      exact G.loopless.irrefl x
    exact edgeSideASet_independent htri u v hxA
      (mem_sideAFinset_iff.mp hy) hxy
  have hAraw : (∑ y ∈ A, if G.Adj x y then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    simp [hxx y hy]
  have hxs : adjPairCount G ({x} : Finset (Fin n)) S =
      (residualType G u v x).ncard := by
    unfold adjPairCount
    simp only [Finset.sum_singleton]
    have hfilter : residualTypeFinset G u v x = S.filter (G.Adj x) := by
      ext z
      simp [S, residualTypeFinset, residualType,
        mem_residualTypeFinset_iff, mem_residualFinset_iff,
        and_comm, adj_comm]
    have hcard : (residualTypeFinset G u v x).card =
        ∑ y ∈ S, if G.Adj x y then 1 else 0 := by
      rw [hfilter, Finset.card_filter]
    rw [residualTypeFinset_card_eq_ncard] at hcard
    exact hcard.symm
  have hsum' : vertexDegree G x =
      1 + (∑ y ∈ B, if G.Adj x y then 1 else 0) +
        ∑ y ∈ S, if G.Adj x y then 1 else 0 := by
    simpa [hxu, hxv, hAraw, A, B, S] using hsum
  have hB : (∑ y ∈ B, if G.Adj x y then 1 else 0) =
      adjPairCount G ({x} : Finset (Fin n)) B := by
    simp [adjPairCount]
  have hSraw : (∑ y ∈ S, if G.Adj x y then 1 else 0) =
      adjPairCount G ({x} : Finset (Fin n)) S := by
    simp [adjPairCount]
  rw [hB, hSraw, hxs] at hsum'
  simpa [A, B, S, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum'

/- The degree-sum maximality of the selected edge gives the numerical local
   capacity inequality.  The left side is the residual type size plus the
   number of cross-neighbours of `x`; the right side is the full opposite
   side size. -/
theorem residualType_ncard_add_cross_le_sideB_card_of_degree_sum_max
    {r n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : HighExtremal r n G)
    {u v x : Fin n} (huv : G.Adj u v)
    (hD : ∀ H a b, HighExtremalEdgePairs r n (H, (a, b)) →
      degreeSumPair (H, (a, b)) ≤ degreeSumPair (G, (u, v)))
    (hxA : x ∈ edgeSideASet G u v) :
    (residualType G u v x).ncard +
        adjPairCount G ({x} : Finset (Fin n)) (sideBFinset G u v) ≤
      (sideBFinset G u v).card := by
  have hdeg := high_extremal_adj_degree_sum_le hG hD hxA.1.symm
  change vertexDegree G x + vertexDegree G v ≤
    vertexDegree G u + vertexDegree G v at hdeg
  have hdx := vertexDegree_sideA_decomposition hG.1.1 huv hxA
  have hdu : vertexDegree G u = (sideBFinset G u v).card + 1 := by
    rw [vertexDegree_eq_edgeSideB_ncard_add_one huv,
      ← sideBFinset_card_eq_ncard G u v]
  have hdeg' : vertexDegree G x ≤ vertexDegree G u := by omega
  rw [hdx, hdu] at hdeg'
  omega

/- For a fixed A-side vertex, the support hits on the B-side are exactly the
   B-side vertices which are not adjacent to it.  Maximality supplies the
   cross-edge/disjointness equivalence; the no-repeated-type hypothesis lets
   us pass from vertices to the support-family image without changing the
   count. -/
theorem supportHits_eq_sideB_nonadj_count
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v x : Fin n} (hmax : IsEdgeMaximalTriangleFree G)
    (huv : G.Adj u v)
    (hnoB : ∀ y y', y ∈ edgeSideBSet G u v →
      y' ∈ edgeSideBSet G u v → y ≠ y' →
      (residualType G u v y).Nonempty →
      residualType G u v y ≠ residualType G u v y')
    (hxA : x ∈ edgeSideASet G u v) :
    supportHits (supportFamilyB G u v) (residualTypeFinset G u v x) =
      ∑ y ∈ sideBFinset G u v, if G.Adj x y then 0 else 1 := by
  classical
  let B := sideBFinset G u v
  let N := nonemptyBTypeVertices G u v
  have hNsub : N ⊆ B := by
    intro y hy
    exact mem_sideBFinset_iff.mpr (mem_nonemptyBTypeVertices_iff.mp hy).1
  have hinjB : Set.InjOn (fun y : Fin n => residualTypeFinset G u v y)
      (nonemptyBTypeVertices G u v) := by
    intro y hy y' hy' heq
    by_contra hyy'
    have hy0 := mem_nonemptyBTypeVertices_iff.mp hy
    have hy'0 := mem_nonemptyBTypeVertices_iff.mp hy'
    have htype : residualType G u v y = residualType G u v y' := by
      ext z
      have hz := congrArg (fun I : Finset (Fin n) => z ∈ I) heq
      exact iff_of_eq (by simpa only [mem_residualTypeFinset_iff] using hz)
    exact (hnoB y y' hy0.1 hy'0.1 hyy' hy0.2 htype).elim
  have hdis_finset_iff {y : Fin n}
      (hyB : y ∈ edgeSideBSet G u v) :
      G.Adj x y ↔ Disjoint (residualTypeFinset G u v x)
        (residualTypeFinset G u v y) := by
    have hiff := cross_adj_iff_residual_disjoint hmax huv hxA hyB
    have hdis : Disjoint (residualTypeFinset G u v x)
        (residualTypeFinset G u v y) ↔
        Disjoint (residualType G u v x) (residualType G u v y) := by
      rw [Finset.disjoint_left, Set.disjoint_left]
      simp only [mem_residualTypeFinset_iff]
    exact hiff.trans hdis.symm
  have hterm {y : Fin n} (hyN : y ∈ N) :
      (if Disjoint (residualTypeFinset G u v y)
          (residualTypeFinset G u v x) then 0 else 1) =
        (if G.Adj x y then 0 else 1) := by
    have hyB : y ∈ edgeSideBSet G u v :=
      (mem_nonemptyBTypeVertices_iff.mp hyN).1
    have hiff := hdis_finset_iff hyB
    have hiff' : G.Adj x y ↔ Disjoint (residualTypeFinset G u v y)
        (residualTypeFinset G u v x) := by
      simpa [disjoint_comm] using hiff
    by_cases hd : Disjoint (residualTypeFinset G u v y)
        (residualTypeFinset G u v x)
    · have ha : G.Adj x y := hiff'.mpr hd
      simp [hd, ha]
    · have hna : ¬ G.Adj x y := by
        intro ha
        exact hd (hiff'.mp ha)
      simp [hd, hna]
  have hterm_empty {y : Fin n} (hyB : y ∈ B) (hyn : y ∉ N) :
      (if G.Adj x y then 0 else 1) = 0 := by
    have hySet : y ∈ edgeSideBSet G u v := mem_sideBFinset_iff.mp hyB
    have hne : ¬ (residualType G u v y).Nonempty := by
      intro hne
      apply hyn
      exact Finset.mem_filter.mpr ⟨hyB, hne⟩
    have hdisSet : Disjoint (residualType G u v x)
        (residualType G u v y) := by
      rw [Set.disjoint_left]
      intro z hzx hzy
      exact (hne ⟨z, hzy⟩).elim
    have hadj := (cross_adj_iff_residual_disjoint hmax huv hxA hySet).mpr hdisSet
    simp [hadj]
  calc
    supportHits (supportFamilyB G u v) (residualTypeFinset G u v x) =
        ∑ y ∈ N, if Disjoint (residualTypeFinset G u v y)
          (residualTypeFinset G u v x) then 0 else 1 := by
      unfold supportHits supportFamilyB
      rw [Finset.sum_image hinjB]
    _ = ∑ y ∈ N, if G.Adj x y then 0 else 1 := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hterm hy
    _ = ∑ y ∈ B, if G.Adj x y then 0 else 1 := by
      apply Finset.sum_subset hNsub
      intro y hyB hyn
      exact hterm_empty hyB hyn
    _ = ∑ y ∈ sideBFinset G u v, if G.Adj x y then 0 else 1 := by
      rfl

/- Combining the previous two local identities yields the first half of the
   abstract `DegreeCompatible` predicate for the actual graph support
   families. -/
theorem supportFamilyA_degree_compatible_of_degree_sum_max
    {r n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : HighExtremal r n G)
    {u v : Fin n} (huv : G.Adj u v)
    (hD : ∀ H a b, HighExtremalEdgePairs r n (H, (a, b)) →
      degreeSumPair (H, (a, b)) ≤ degreeSumPair (G, (u, v)))
    (hnoB : ∀ y y', y ∈ edgeSideBSet G u v →
      y' ∈ edgeSideBSet G u v → y ≠ y' →
      (residualType G u v y).Nonempty →
      residualType G u v y ≠ residualType G u v y') :
    ∀ I ∈ supportFamilyA G u v,
      I.card ≤ supportHits (supportFamilyB G u v) I := by
  intro I hI
  rcases mem_supportFamilyA_iff.mp hI with ⟨x, hx, hIx⟩
  have hxA : x ∈ edgeSideASet G u v :=
    (mem_nonemptyATypeVertices_iff.mp hx).1
  have hIcard : I.card = (residualType G u v x).ncard := by
    rw [← hIx, residualTypeFinset_card_eq_ncard]
  have hlocal := residualType_ncard_add_cross_le_sideB_card_of_degree_sum_max
    hG huv hD hxA
  have hmax : IsEdgeMaximalTriangleFree G :=
    edge_maximal_of_edgeCount_max hG.1 hG.2
  have hpart :
      adjPairCount G ({x} : Finset (Fin n)) (sideBFinset G u v) +
        supportHits (supportFamilyB G u v)
          (residualTypeFinset G u v x) =
      (sideBFinset G u v).card := by
    rw [supportHits_eq_sideB_nonadj_count (G := G) hmax huv hnoB hxA]
    unfold adjPairCount
    simp only [Finset.sum_singleton]
    rw [show (sideBFinset G u v).card =
      ∑ y ∈ sideBFinset G u v, (1 : ℕ) by simp]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hadj : G.Adj x y <;> simp [hadj]
  rw [hIx] at hpart
  omega

theorem residualType_ncard_add_cross_le_sideA_card_of_degree_sum_max
    {r n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : HighExtremal r n G)
    {u v y : Fin n} (huv : G.Adj u v)
    (hD : ∀ H a b, HighExtremalEdgePairs r n (H, (a, b)) →
      degreeSumPair (H, (a, b)) ≤ degreeSumPair (G, (u, v)))
    (hyB : y ∈ edgeSideBSet G u v) :
    (residualType G u v y).ncard +
        adjPairCount G ({y} : Finset (Fin n)) (sideAFinset G u v) ≤
      (sideAFinset G u v).card := by
  have hD' : ∀ H a b, HighExtremalEdgePairs r n (H, (a, b)) →
      degreeSumPair (H, (a, b)) ≤ degreeSumPair (G, (v, u)) := by
    intro H a b hp
    have hh := hD H a b hp
    simpa [degreeSumPair, Nat.add_comm] using hh
  have hyA' : y ∈ edgeSideASet G v u := by
    simpa [edgeSideASet, edgeSideBSet] using hyB
  have hlocal := residualType_ncard_add_cross_le_sideB_card_of_degree_sum_max
    hG huv.symm hD' hyA'
  simpa [residualType_swap, sideAFinset_swap_eq_sideBFinset,
    adj_comm] using hlocal

theorem supportFamilyB_degree_compatible_of_degree_sum_max
    {r n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : HighExtremal r n G)
    {u v : Fin n} (huv : G.Adj u v)
    (hD : ∀ H a b, HighExtremalEdgePairs r n (H, (a, b)) →
      degreeSumPair (H, (a, b)) ≤ degreeSumPair (G, (u, v)))
    (hnoA : ∀ x x', x ∈ edgeSideASet G u v →
      x' ∈ edgeSideASet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x') :
    ∀ I ∈ supportFamilyB G u v,
      I.card ≤ supportHits (supportFamilyA G u v) I := by
  intro I hI
  rcases mem_supportFamilyB_iff.mp hI with ⟨y, hy, hIy⟩
  have hyB : y ∈ edgeSideBSet G u v :=
    (mem_nonemptyBTypeVertices_iff.mp hy).1
  have hIcard : I.card = (residualType G u v y).ncard := by
    rw [← hIy, residualTypeFinset_card_eq_ncard]
  have hlocal := residualType_ncard_add_cross_le_sideA_card_of_degree_sum_max
    hG huv hD hyB
  have hmax : IsEdgeMaximalTriangleFree G :=
    edge_maximal_of_edgeCount_max hG.1 hG.2
  have hpart :
      adjPairCount G ({y} : Finset (Fin n)) (sideAFinset G u v) +
        supportHits (supportFamilyA G u v)
          (residualTypeFinset G u v y) =
      (sideAFinset G u v).card := by
    have hD' : ∀ H a b, HighExtremalEdgePairs r n (H, (a, b)) →
        degreeSumPair (H, (a, b)) ≤ degreeSumPair (G, (v, u)) := by
      intro H a b hp
      have hh := hD H a b hp
      simpa [degreeSumPair, Nat.add_comm] using hh
    have hyA' : y ∈ edgeSideASet G v u := by
      simpa [edgeSideASet, edgeSideBSet] using hyB
    have hnoA' : ∀ y y', y ∈ edgeSideBSet G v u →
        y' ∈ edgeSideBSet G v u → y ≠ y' →
        (residualType G v u y).Nonempty →
        residualType G v u y ≠ residualType G v u y' := by
      intro y y' hy hy' hyy' hTy hEq
      apply hnoA y y'
      · simpa [edgeSideASet, edgeSideBSet] using hy
      · simpa [edgeSideASet, edgeSideBSet] using hy'
      · exact hyy'
      · simpa [residualType_swap] using hTy
      · simpa [residualType_swap] using hEq
    have hhit' := supportHits_eq_sideB_nonadj_count
      (G := G) hmax huv.symm hnoA' hyA'
    rw [supportFamilyB_swap_eq_supportFamilyA G u v,
      residualTypeFinset_swap G u v y,
      sideBFinset_swap_eq_sideAFinset G u v] at hhit'
    have hhit : supportHits (supportFamilyA G u v)
        (residualTypeFinset G u v y) =
        ∑ z ∈ sideAFinset G u v, if G.Adj y z then 0 else 1 := by
      simpa [adj_comm] using hhit'
    rw [hhit]
    unfold adjPairCount
    simp only [Finset.sum_singleton]
    rw [show (sideAFinset G u v).card =
      ∑ z ∈ sideAFinset G u v, (1 : ℕ) by simp]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hadj : G.Adj y z <;> simp [hadj]
  rw [hIy] at hpart
  omega

theorem degreeCompatible_of_degree_sum_max
    {r n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : HighExtremal r n G)
    {u v : Fin n} (huv : G.Adj u v)
    (hD : ∀ H a b, HighExtremalEdgePairs r n (H, (a, b)) →
      degreeSumPair (H, (a, b)) ≤ degreeSumPair (G, (u, v)))
    (hnoA : ∀ x x', x ∈ edgeSideASet G u v →
      x' ∈ edgeSideASet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    (hnoB : ∀ y y', y ∈ edgeSideBSet G u v →
      y' ∈ edgeSideBSet G u v → y ≠ y' →
      (residualType G u v y).Nonempty →
      residualType G u v y ≠ residualType G u v y') :
    DegreeCompatible (supportFamilyA G u v) (supportFamilyB G u v) := by
  refine ⟨supportFamilyA_degree_compatible_of_degree_sum_max hG huv hD hnoB,
    supportFamilyB_degree_compatible_of_degree_sum_max hG huv hD hnoA⟩

/- A partition identity for degree sums.  The hypotheses are deliberately
   only finset disjointness and a cover, so this lemma can be reused for both
   the residual decomposition and finite certificate checks. -/

end Erdos1011

end Web_Erdos1011_EdgeDecomposition
