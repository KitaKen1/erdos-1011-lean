import R5Kernel.Parts.M008

/- Source module: Erdos1011.Twinization. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_Twinization


namespace Erdos1011

open SimpleGraph

/-! Structural facts used by the residual-type reduction.  The key point is
    that, in an edge-maximal triangle-free graph, cross edges between the two
    sides of an edge are exactly disjointness of their residual neighbourhoods.
    This is the formal version of equation (2) in the paper notes. -/

theorem cross_adj_iff_residual_disjoint
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : IsEdgeMaximalTriangleFree G)
    {u v x y : Fin n} (huv : G.Adj u v)
    (hxA : x ∈ edgeSideASet G u v)
    (hyB : y ∈ edgeSideBSet G u v) :
    G.Adj x y ↔ Disjoint (residualType G u v x) (residualType G u v y) := by
  constructor
  · intro hxy
    refine Set.disjoint_left.mpr ?_
    intro z hzx hzy
    exact hG.1 _ (SimpleGraph.is3Clique_triple_iff.mpr
      ⟨hxy, hzx.1, hzy.1⟩)
  · intro hdisj
    by_contra hxy
    obtain ⟨z, hxz, hyz⟩ := common_neighbor_of_edge_maximal hG
      (x := x) (y := y) (by
        intro h
        subst y
        exact Set.disjoint_left.mp (edgeSide_sets_disjoint hG.1 huv) hxA hyB) hxy
    have hxu : ¬ G.Adj u x := by
      intro hux
      exact hG.1 _ (SimpleGraph.is3Clique_triple_iff.mpr
        ⟨huv, hux, hxA.1⟩)
    have hyv : ¬ G.Adj v y := by
      intro hvy
      exact hG.1 _ (SimpleGraph.is3Clique_triple_iff.mpr
        ⟨huv, hyB.1, hvy⟩)
    have hzu : z ≠ u := by
      intro h
      subst z
      exact hxu hxz.symm
    have hzv : z ≠ v := by
      intro h
      subst z
      exact hyv hyz.symm
    have hznotu : ¬ G.Adj u z := by
      intro huz
      exact hG.1 _ (SimpleGraph.is3Clique_triple_iff.mpr
        ⟨huz, hyB.1, hyz.symm⟩)
    have hznotv : ¬ G.Adj v z := by
      intro hvz
      exact hG.1 _ (SimpleGraph.is3Clique_triple_iff.mpr
        ⟨hvz, hxA.1, hxz.symm⟩)
    have hzX : z ∈ residualType G u v x := by
      exact ⟨hxz, ⟨hzu, hzv, hznotu, hznotv⟩⟩
    have hzY : z ∈ residualType G u v y := by
      exact ⟨hyz, ⟨hzu, hzv, hznotu, hznotv⟩⟩
    exact (Set.disjoint_left.mp hdisj) hzX hzY

theorem same_residual_type_twin
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : IsEdgeMaximalTriangleFree G)
    {u v x x' : Fin n} (huv : G.Adj u v)
    (hxA : x ∈ edgeSideASet G u v)
    (hx'A : x' ∈ edgeSideASet G u v)
    (hxx' : x ≠ x')
    (htype : residualType G u v x = residualType G u v x') :
    ∀ y, y ≠ x → y ≠ x' → (G.Adj x y ↔ G.Adj x' y) := by
  have hxu : ¬ G.Adj u x := by
    intro hux
    exact hG.1 _ (SimpleGraph.is3Clique_triple_iff.mpr
      ⟨huv, hux, hxA.1⟩)
  have hx'u : ¬ G.Adj u x' := by
    intro hux
    exact hG.1 _ (SimpleGraph.is3Clique_triple_iff.mpr
      ⟨huv, hux, hx'A.1⟩)
  intro y hyx hyx'
  by_cases hyu : y = u
  · subst y
    simp [hxu, hx'u, adj_comm]
  by_cases hyv : y = v
  · subst y
    exact ⟨fun _ => hx'A.1.symm, fun _ => hxA.1.symm⟩
  by_cases hyvA : G.Adj v y
  · have hyA : y ∈ edgeSideASet G u v :=
      mem_edgeSideASet_iff.mpr ⟨hyvA, hyu⟩
    have hnotxy : ¬ G.Adj x y := by
      exact edgeSideASet_independent hG.1 u v hxA hyA (by
        intro h
        exact hyx h.symm)
    have hnotx'y : ¬ G.Adj x' y := by
      exact edgeSideASet_independent hG.1 u v hx'A hyA (by
        intro h
        exact hyx' h.symm)
    simp [hnotxy, hnotx'y]
  by_cases hyuB : G.Adj u y
  · have hyB : y ∈ edgeSideBSet G u v :=
      mem_edgeSideBSet_iff.mpr ⟨hyuB, hyv⟩
    have hcross := cross_adj_iff_residual_disjoint hG huv hxA hyB
    have hcross' := cross_adj_iff_residual_disjoint hG huv hx'A hyB
    rw [hcross, hcross', htype]
  · have hyS : y ∈ residualSet G u v := ⟨hyu, hyv, hyuB, hyvA⟩
    have hmem : y ∈ residualType G u v x ↔ y ∈ residualType G u v x' := by
      rw [htype]
    simpa [residualType, hyS] using hmem

/- Replacing one member of a repeated A-type by a copy of `u` does not lower
   the chromatic number.  The homomorphism sends the replaced vertex to the
   other member of the repeated type and fixes all other vertices. -/
theorem high_replaceVertex_of_same_residual_type
    {r n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : HighChromaticTriangleFree r n G)
    (hmax : IsEdgeMaximalTriangleFree G)
    {u v x x' : Fin n} (huv : G.Adj u v)
    (hxA : x ∈ edgeSideASet G u v)
    (hx'A : x' ∈ edgeSideASet G u v)
    (hxx' : x ≠ x')
    (htype : residualType G u v x = residualType G u v x') :
    HighChromaticTriangleFree r n (G.replaceVertex u x) := by
  classical
  let H := G.replaceVertex u x
  let f : Fin n → Fin n := fun z => if z = x then x' else z
  have hhom : G →g H := by
    refine { toFun := f, map_rel' := ?_ }
    intro a b hab
    by_cases hax : a = x
    · subst a
      by_cases hbx : b = x
      · subst b
        exact (G.loopless.irrefl x hab).elim
      by_cases hbx' : b = x'
      · subst b
        have hnot : ¬ G.Adj x x' := by
          exact edgeSideASet_independent hG.1 u v hxA hx'A hxx'
        exact (hnot hab).elim
      have htw := same_residual_type_twin hmax huv hxA hx'A hxx' htype b hbx hbx'
      have hrep : H.Adj x' b ↔ G.Adj x' b :=
        SimpleGraph.adj_replaceVertex_iff_of_ne (G := G) (s := u) (t := x)
          hxx'.symm hbx
      simpa [f, hbx, hbx'] using hrep.mpr (htw.mp hab)
    · by_cases hbx : b = x
      · subst b
        by_cases hax' : a = x'
        · subst a
          have hnot : ¬ G.Adj x' x := by
            exact edgeSideASet_independent hG.1 u v hx'A hxA hxx'.symm
          exact (hnot hab).elim
        have htw := same_residual_type_twin hmax huv hxA hx'A hxx' htype a hax hax'
        have hrep : H.Adj a x' ↔ G.Adj a x' :=
          SimpleGraph.adj_replaceVertex_iff_of_ne (G := G) (s := u) (t := x)
            hax hxx'.symm
        simpa [f, hax] using hrep.mpr ((htw.mp hab.symm).symm)
      have hrep : H.Adj a b ↔ G.Adj a b :=
        SimpleGraph.adj_replaceVertex_iff_of_ne (G := G) (s := u) (t := x)
          hax hbx
      simpa [f, hax, hbx] using hrep.mpr hab
  refine ⟨by simpa [H] using hG.1.replaceVertex u x, ?_⟩
  exact hG.2.trans (SimpleGraph.chromaticNumber_mono_of_hom hhom)

theorem vertexDegree_eq_degree
    {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    [Fintype (G.neighborSet v)] :
    vertexDegree G v = G.degree v := by
  unfold vertexDegree
  rw [Set.ncard_eq_toFinset_card']
  rw [Set.toFinset_card (G.neighborSet v)]
  exact SimpleGraph.card_neighborSet_eq_degree G v

theorem edgeCount_replaceVertex_of_not_adj
    {n : ℕ} (G : SimpleGraph (Fin n)) {s t : Fin n}
    (hst : ¬ G.Adj s t) :
    edgeCount (G.replaceVertex s t) =
      edgeCount G + vertexDegree G s - vertexDegree G t := by
  classical
  unfold edgeCount
  rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
  change (G.replaceVertex s t).edgeFinset.card = G.edgeFinset.card +
    vertexDegree G s - vertexDegree G t
  have hcard := G.card_edgeFinset_replaceVertex_of_not_adj hst
  rw [vertexDegree_eq_degree G s, vertexDegree_eq_degree G t]
  simpa using hcard

/- In an edge-extremal graph, the repeated-type replacement has zero edge
   increment.  This is the quantitative part of the twinization argument;
   the minimal-type choice is used only in the subsequent combinatorial step. -/
theorem replacement_equal_edgeCount_of_extremal
    {r n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : HighExtremal r n G)
    {u v x x' : Fin n} (huv : G.Adj u v)
    (hD : ∀ H a b, HighExtremalEdgePairs r n (H, (a, b)) →
      degreeSumPair (H, (a, b)) ≤ degreeSumPair (G, (u, v)))
    (hxA : x ∈ edgeSideASet G u v)
    (hx'A : x' ∈ edgeSideASet G u v)
    (hxx' : x ≠ x')
    (htype : residualType G u v x = residualType G u v x') :
    edgeCount (G.replaceVertex u x) = edgeCount G ∧
      vertexDegree G x = vertexDegree G u := by
  have hsat : IsEdgeMaximalTriangleFree G :=
    edge_maximal_of_edgeCount_max hG.1 hG.2
  have hhigh : HighChromaticTriangleFree r n (G.replaceVertex u x) :=
    high_replaceVertex_of_same_residual_type hG.1 hsat huv hxA hx'A hxx' htype
  have hle : edgeCount (G.replaceVertex u x) ≤ edgeCount G := hG.2 _ hhigh
  have hxu : ¬ G.Adj u x := by
    intro hux
    exact hG.1.1 _ (SimpleGraph.is3Clique_triple_iff.mpr
      ⟨huv, hux, hxA.1⟩)
  have hformula := edgeCount_replaceVertex_of_not_adj G hxu
  have hpair := hD G x v ⟨hG, hxA.1.symm⟩
  change vertexDegree G x + vertexDegree G v ≤
    vertexDegree G u + vertexDegree G v at hpair
  have hdeg : vertexDegree G x ≤ vertexDegree G u := by omega
  rw [hformula] at hle
  have hxeq : vertexDegree G x = vertexDegree G u := by omega
  constructor
  · rw [hformula, hxeq]
    omega
  · exact hxeq

theorem replaceVertex_neighborSet_left_eq
    {n : ℕ} (G : SimpleGraph (Fin n)) {s t : Fin n}
    (hst : ¬ G.Adj s t) :
    (G.replaceVertex s t).neighborSet s = G.neighborSet s := by
  ext z
  simp only [SimpleGraph.mem_neighborSet]
  by_cases hzt : z = t
  · subst z
    simp [SimpleGraph.not_adj_replaceVertex_same, hst]
  · rw [G.adj_replaceVertex_iff_of_ne_left s hzt]

theorem replaceVertex_neighborSet_eq_of_adj_iff
    {n : ℕ} (G : SimpleGraph (Fin n)) {s t w : Fin n}
    (hwt : w ≠ t)
    (hadj : G.Adj w t ↔ G.Adj w s) :
    (G.replaceVertex s t).neighborSet w = G.neighborSet w := by
  ext z
  simp only [SimpleGraph.mem_neighborSet]
  by_cases hzt : z = t
  · subst z
    constructor
    · intro h
      exact hadj.mpr ((G.adj_replaceVertex_iff_of_ne_right s hwt).mp h.symm).symm
    · intro h
      exact ((G.adj_replaceVertex_iff_of_ne_right s hwt).mpr
        (hadj.mp h).symm).symm
  · rw [G.adj_replaceVertex_iff_of_ne s hwt hzt]

theorem replaceVertex_residualType_empty
    {n : ℕ} (G : SimpleGraph (Fin n)) {u v x : Fin n}
    (huv : G.Adj u v) (hxA : x ∈ edgeSideASet G u v) :
    residualType (G.replaceVertex u x) u v x = ∅ := by
  have hxu_ne : u ≠ x := by
    intro h
    apply hxA.2
    simpa [h]
  have hxu_ne' : x ≠ u := hxu_ne.symm
  have hxv_ne : v ≠ x := by
    intro h
    subst x
    exact G.loopless.irrefl v hxA.1
  have hvx : G.Adj v x := hxA.1
  ext z
  by_cases hzx : z = x
  · subst z
    simp [residualType, residualSet, SimpleGraph.replaceVertex, hxu_ne, hxu_ne', hxv_ne,
      hvx, huv, adj_comm]
  · simp [residualType, residualSet, SimpleGraph.replaceVertex, hxu_ne, hxv_ne, hzx]
    aesop

theorem replaceVertex_residualType_eq_of_ne
    {n : ℕ} (G : SimpleGraph (Fin n)) {u v x y : Fin n}
    (huv : G.Adj u v) (hxA : x ∈ edgeSideASet G u v)
    (hy : y ≠ x) :
    residualType (G.replaceVertex u x) u v y = residualType G u v y := by
  have hxu_ne : u ≠ x := by
    intro h
    apply hxA.2
    simpa [h]
  have hxu_ne' : x ≠ u := hxu_ne.symm
  have hxv_ne : v ≠ x := by
    intro h
    subst x
    exact G.loopless.irrefl v hxA.1
  have hvx : G.Adj v x := hxA.1
  ext z
  by_cases hzx : z = x
  · subst z
    simp [residualType, residualSet, SimpleGraph.replaceVertex, hxu_ne, hxu_ne', hxv_ne,
      hy, hvx, huv, adj_comm]
  · simp [residualType, residualSet, SimpleGraph.replaceVertex, hxu_ne, hxv_ne, hy, hzx]

theorem nonemptyTypeCount_replaceVertex_lt
    {n : ℕ} (G : SimpleGraph (Fin n)) {u v x : Fin n}
    (htri : G.CliqueFree 3)
    (huv : G.Adj u v) (hxA : x ∈ edgeSideASet G u v)
    (hTx : (residualType G u v x).Nonempty) :
    nonemptyTypeCount (G.replaceVertex u x) u v < nonemptyTypeCount G u v := by
  let H := G.replaceVertex u x
  have hux : ¬ G.Adj u x := by
    intro h
    exact htri _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨huv, h, hxA.1⟩)
  have hxu_ne : u ≠ x := by
    intro h
    apply hxA.2
    simpa [h]
  have hxv_ne : v ≠ x := by
    intro h
    subst x
    exact G.loopless.irrefl v hxA.1
  have hsideA : edgeSideASet H u v = edgeSideASet G u v := by
    have hNv := replaceVertex_neighborSet_eq_of_adj_iff G hxv_ne
      (iff_of_true hxA.1 huv.symm)
    simp [edgeSideASet, H, hNv]
  have hsideB : edgeSideBSet H u v = edgeSideBSet G u v := by
    have hNu := replaceVertex_neighborSet_left_eq G hux
    simp [edgeSideBSet, H, hNu]
  have htx0 : residualType H u v x = ∅ := by
    exact replaceVertex_residualType_empty G huv hxA
  have hty : ∀ {y : Fin n}, y ≠ x →
      residualType H u v y = residualType G u v y := by
    intro y hy
    exact replaceVertex_residualType_eq_of_ne G huv hxA hy
  let A0 : Set (Fin n) := {y | y ∈ edgeSideASet G u v ∧
    (residualType G u v y).Nonempty}
  let A1 : Set (Fin n) := {y | y ∈ edgeSideASet H u v ∧
    (residualType H u v y).Nonempty}
  let B0 : Set (Fin n) := {y | y ∈ edgeSideBSet G u v ∧
    (residualType G u v y).Nonempty}
  let B1 : Set (Fin n) := {y | y ∈ edgeSideBSet H u v ∧
    (residualType H u v y).Nonempty}
  have hAset : A1 = A0 \ {x} := by
    ext y
    by_cases hy : y = x
    · subst y
      simp [A1, A0, hsideA, htx0, hxA, hTx]
    · have hty' := hty hy
      simp [A1, A0, hsideA, hty', hy]
  have hBset : B1 = B0 := by
    ext y
    by_cases hy : y = x
    · subst y
      simp [B1, B0, hsideB, hux]
    · have hty' := hty hy
      simp [B1, B0, hsideB, hty']
  have hxA0 : x ∈ A0 := by
    exact ⟨hxA, hTx⟩
  have hAlt : A1.ncard < A0.ncard := by
    rw [hAset]
    exact Set.ncard_sdiff_singleton_lt_of_mem hxA0
  have hBeq : B1.ncard = B0.ncard := by rw [hBset]
  unfold nonemptyTypeCount
  change A1.ncard + B1.ncard < A0.ncard + B0.ncard
  omega

theorem no_repeated_nonempty_A_type_of_minimal_choice
    {r n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (hG : HighExtremal r n G)
    (hD : ∀ H a b, HighExtremalEdgePairs r n (H, (a, b)) →
      degreeSumPair (H, (a, b)) ≤ degreeSumPair (G, (u, v)))
    (hmin : ∀ H a b, HighExtremalEdgePairs r n (H, (a, b)) →
      degreeSumPair (H, (a, b)) = degreeSumPair (G, (u, v)) →
      nonemptyTypeCount G u v ≤ nonemptyTypeCount H a b)
    {x x' : Fin n} (huv : G.Adj u v)
    (hxA : x ∈ edgeSideASet G u v)
    (hx'A : x' ∈ edgeSideASet G u v)
    (hxx' : x ≠ x')
    (htype : residualType G u v x = residualType G u v x')
    (hTx : (residualType G u v x).Nonempty) :
    False := by
  let H := G.replaceVertex u x
  have hsat : IsEdgeMaximalTriangleFree G :=
    edge_maximal_of_edgeCount_max hG.1 hG.2
  have hhigh : HighChromaticTriangleFree r n H := by
    exact high_replaceVertex_of_same_residual_type hG.1 hsat huv hxA hx'A hxx' htype
  have heq : edgeCount H = edgeCount G ∧ vertexDegree G x = vertexDegree G u := by
    exact replacement_equal_edgeCount_of_extremal hG huv hD hxA hx'A hxx' htype
  have hHext : HighExtremal r n H := by
    refine ⟨by simpa [H] using hhigh, ?_⟩
    intro K hK
    calc
      edgeCount K ≤ edgeCount G := hG.2 K hK
      _ = edgeCount H := by simpa [H] using heq.1.symm
  have hux : ¬ G.Adj u x := by
    intro h
    exact hG.1.1 _ (SimpleGraph.is3Clique_triple_iff.mpr
      ⟨huv, h, hxA.1⟩)
  have hxu_ne : u ≠ x := by
    intro h
    apply hxA.2
    simpa [h]
  have hxv_ne : v ≠ x := by
    intro h
    subst x
    exact G.loopless.irrefl v hxA.1
  have hHuv : H.Adj u v := by
    have hh := G.adj_replaceVertex_iff_of_ne u hxu_ne hxv_ne
    exact hh.mpr huv
  have hNu := replaceVertex_neighborSet_left_eq G hux
  have hNv := replaceVertex_neighborSet_eq_of_adj_iff G hxv_ne
    (iff_of_true hxA.1 huv.symm)
  have hdegree : degreeSumPair (H, (u, v)) = degreeSumPair (G, (u, v)) := by
    simp [degreeSumPair, H, vertexDegree, hNu, hNv]
  have hmin' := hmin H u v ⟨hHext, hHuv⟩ hdegree
  have hlt : nonemptyTypeCount H u v < nonemptyTypeCount G u v := by
    simpa [H] using nonemptyTypeCount_replaceVertex_lt G hG.1.1 huv hxA hTx
  exact (Nat.not_lt_of_ge hmin') hlt

/- The residual decomposition is equivariant under exchanging the endpoints of
   the distinguished edge.  These equalities let the A-side twinization lemma
   be reused verbatim for the B side. -/

theorem residualSet_swap
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    residualSet G v u = residualSet G u v := by
  ext x
  simp [residualSet, and_comm, and_left_comm, and_assoc]

theorem residualType_swap
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v x : Fin n) :
    residualType G v u x = residualType G u v x := by
  simp [residualType, residualSet_swap]

theorem nonemptyTypeCount_swap
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    nonemptyTypeCount G v u = nonemptyTypeCount G u v := by
  simp [nonemptyTypeCount, edgeSideASet, edgeSideBSet, residualType,
    residualSet, and_comm, and_left_comm, and_assoc, Nat.add_comm]

theorem no_repeated_nonempty_B_type_of_minimal_choice
    {r n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (hG : HighExtremal r n G)
    (hD : ∀ H a b, HighExtremalEdgePairs r n (H, (a, b)) →
      degreeSumPair (H, (a, b)) ≤ degreeSumPair (G, (u, v)))
    (hmin : ∀ H a b, HighExtremalEdgePairs r n (H, (a, b)) →
      degreeSumPair (H, (a, b)) = degreeSumPair (G, (u, v)) →
      nonemptyTypeCount G u v ≤ nonemptyTypeCount H a b)
    {y y' : Fin n} (huv : G.Adj u v)
    (hyB : y ∈ edgeSideBSet G u v)
    (hy'B : y' ∈ edgeSideBSet G u v)
    (hyy' : y ≠ y')
    (htype : residualType G u v y = residualType G u v y')
    (hTy : (residualType G u v y).Nonempty) :
    False := by
  have huv' : G.Adj v u := huv.symm
  have hyA' : y ∈ edgeSideASet G v u := by
    simpa [edgeSideASet, edgeSideBSet] using hyB
  have hy'A' : y' ∈ edgeSideASet G v u := by
    simpa [edgeSideASet, edgeSideBSet] using hy'B
  have htype' : residualType G v u y = residualType G v u y' := by
    simpa [residualType_swap] using htype
  have hTy' : (residualType G v u y).Nonempty := by
    simpa [residualType_swap] using hTy
  have hD' : ∀ H a b, HighExtremalEdgePairs r n (H, (a, b)) →
      degreeSumPair (H, (a, b)) ≤ degreeSumPair (G, (v, u)) := by
    intro H a b hp
    have hh := hD H a b hp
    simpa [degreeSumPair, Nat.add_comm] using hh
  have hmin' : ∀ H a b, HighExtremalEdgePairs r n (H, (a, b)) →
      degreeSumPair (H, (a, b)) = degreeSumPair (G, (v, u)) →
      nonemptyTypeCount G v u ≤ nonemptyTypeCount H a b := by
    intro H a b hp heq
    have heq' : degreeSumPair (H, (a, b)) = degreeSumPair (G, (u, v)) := by
      simpa [degreeSumPair, Nat.add_comm] using heq
    have hle := hmin H a b hp heq'
    simpa [nonemptyTypeCount_swap] using hle
  exact no_repeated_nonempty_A_type_of_minimal_choice hG hD' hmin'
    huv' hyA' hy'A' hyy' htype' hTy'

/- Package the preceding choice and twinization steps.  The result is the
   exact structural output needed before the finite support-capacity audit:
   one extremal edge is simultaneously degree-sum maximal, type-count
   minimal, and has no repeated nonempty residual type on either side. -/
theorem exists_twinized_extremal_edge
    {r n : ℕ}
    (h : ∃ G : SimpleGraph (Fin n),
      HighChromaticTriangleFree r n G)
    (hedge : ∀ G : SimpleGraph (Fin n), HighExtremal r n G →
      ∃ u v : Fin n, G.Adj u v) :
    ∃ G u v, HighExtremal r n G ∧ G.Adj u v ∧
      (∀ H a b, HighExtremalEdgePairs r n (H, (a, b)) →
        degreeSumPair (H, (a, b)) ≤ degreeSumPair (G, (u, v))) ∧
      (∀ H a b, HighExtremalEdgePairs r n (H, (a, b)) →
        degreeSumPair (H, (a, b)) = degreeSumPair (G, (u, v)) →
        nonemptyTypeCount G u v ≤ nonemptyTypeCount H a b) ∧
      (∀ x x', x ∈ edgeSideASet G u v →
        x' ∈ edgeSideASet G u v → x ≠ x' →
        (residualType G u v x).Nonempty →
        residualType G u v x ≠ residualType G u v x') ∧
      (∀ y y', y ∈ edgeSideBSet G u v →
        y' ∈ edgeSideBSet G u v → y ≠ y' →
        (residualType G u v y).Nonempty →
        residualType G u v y ≠ residualType G u v y') := by
  obtain ⟨G, u, v, hG, huv, hD, hmin0⟩ :=
    exists_min_type_extremal_edge h hedge
  have hmin : ∀ H a b, HighExtremalEdgePairs r n (H, (a, b)) →
      degreeSumPair (H, (a, b)) = degreeSumPair (G, (u, v)) →
      nonemptyTypeCount G u v ≤ nonemptyTypeCount H a b := by
    intro H a b hp heq
    exact hmin0 H a b ⟨hp, heq⟩
  refine ⟨G, u, v, hG, huv, hD, hmin, ?_, ?_⟩
  · intro x x' hxA hx'A hxx' hTx htype
    exact no_repeated_nonempty_A_type_of_minimal_choice hG hD hmin huv
      hxA hx'A hxx' htype hTx
  · intro y y' hyB hy'B hyy' hTy htype
    exact no_repeated_nonempty_B_type_of_minimal_choice hG hD hmin huv
      hyB hy'B hyy' htype hTy

end Erdos1011

end Web_Erdos1011_Twinization
