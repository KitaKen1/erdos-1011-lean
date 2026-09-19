import R5Kernel.Parts.M007

/- Source module: Erdos1011.ExtremalChoice. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_ExtremalChoice


namespace Erdos1011

open SimpleGraph

def HighGraphSet (r n : ℕ) : Set (SimpleGraph (Fin n)) :=
  {G | HighChromaticTriangleFree r n G}

theorem exists_high_extremal
    {r n : ℕ} (h : ∃ G : SimpleGraph (Fin n),
      HighChromaticTriangleFree r n G) :
    ∃ G : SimpleGraph (Fin n), HighChromaticTriangleFree r n G ∧
      ∀ H : SimpleGraph (Fin n), HighChromaticTriangleFree r n H →
        edgeCount H ≤ edgeCount G := by
  obtain ⟨G, hG⟩ := h
  obtain ⟨G₀, hG₀, hmax⟩ := Set.exists_max_image (HighGraphSet r n)
    edgeCount (Set.toFinite _) ⟨G, hG⟩
  refine ⟨G₀, hG₀, ?_⟩
  intro H hH
  exact hmax H hH

theorem edge_maximal_of_edgeCount_max
    {r n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : HighChromaticTriangleFree r n G)
    (hmax : ∀ H : SimpleGraph (Fin n),
      HighChromaticTriangleFree r n H → edgeCount H ≤ edgeCount G) :
    IsEdgeMaximalTriangleFree G := by
  classical
  refine ⟨hG.1, ?_⟩
  intro x y hxy hxyG hfree
  let H := G ⊔ SimpleGraph.edge x y
  have hchi : (r : ℕ∞) ≤ H.chromaticNumber :=
    le_trans hG.2 (SimpleGraph.chromaticNumber_mono H le_sup_left)
  have hhigh : HighChromaticTriangleFree r n H := ⟨hfree, hchi⟩
  have hset : H.edgeSet = insert s(x, y) G.edgeSet := by
    dsimp [H]
    rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_edge_of_ne hxy]
    ext e
    simp [or_comm]
  have hnotmem : s(x, y) ∉ G.edgeSet := by
    simpa [SimpleGraph.mem_edgeSet] using hxyG
  have hcount : edgeCount H = edgeCount G + 1 := by
    rw [edgeCount, edgeCount, hset, Set.ncard_insert_of_notMem hnotmem]
  have hle := hmax H hhigh
  rw [hcount] at hle
  omega

def HighExtremal (r n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  HighChromaticTriangleFree r n G ∧
    ∀ H : SimpleGraph (Fin n), HighChromaticTriangleFree r n H →
      edgeCount H ≤ edgeCount G

def HighExtremalEdgePairs (r n : ℕ) :
    Set (SimpleGraph (Fin n) × (Fin n × Fin n)) :=
  {p | HighExtremal r n p.1 ∧ p.1.Adj p.2.1 p.2.2}

noncomputable def vertexDegree {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  (G.neighborSet v).ncard

noncomputable def degreeSumPair {n : ℕ}
    (p : SimpleGraph (Fin n) × (Fin n × Fin n)) : ℕ :=
  vertexDegree p.1 p.2.1 + vertexDegree p.1 p.2.2

def residualSet {n : ℕ} (G : SimpleGraph (Fin n))
    (u v : Fin n) : Set (Fin n) :=
  {x | x ≠ u ∧ x ≠ v ∧ ¬ G.Adj u x ∧ ¬ G.Adj v x}

theorem residualSet_eq_compl_endpoints_union_sides
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    residualSet G u v =
      (({u, v} : Set (Fin n)) ∪ edgeSideASet G u v ∪ edgeSideBSet G u v)ᶜ := by
  ext x
  by_cases hxu : x = u <;> by_cases hxv : x = v <;>
    simp [residualSet, edgeSideASet, edgeSideBSet, and_comm, and_left_comm, and_assoc,
      hxu, hxv]

theorem vertexDegree_eq_edgeSideA_ncard_add_one
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (huv : G.Adj u v) :
    vertexDegree G v = (edgeSideASet G u v).ncard + 1 := by
  unfold vertexDegree
  have huv' : u ∈ G.neighborSet v := by
    simpa only [SimpleGraph.mem_neighborSet] using huv.symm
  have h := Set.ncard_sdiff_singleton_add_one huv'
  simpa [edgeSideASet] using h.symm

theorem vertexDegree_eq_edgeSideB_ncard_add_one
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (huv : G.Adj u v) :
    vertexDegree G u = (edgeSideBSet G u v).ncard + 1 := by
  unfold vertexDegree
  have huv' : v ∈ G.neighborSet u := by
    simpa only [SimpleGraph.mem_neighborSet] using huv
  have h := Set.ncard_sdiff_singleton_add_one huv'
  simpa [edgeSideBSet] using h.symm

theorem residualSet_ncard_add_side_ncard_eq
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (htri : G.CliqueFree 3) {u v : Fin n} (huv : G.Adj u v) :
    (residualSet G u v).ncard + (edgeSideASet G u v).ncard +
      (edgeSideBSet G u v).ncard + 2 = n := by
  let U : Set (Fin n) := ({u, v} : Set (Fin n)) ∪
    edgeSideASet G u v ∪ edgeSideBSet G u v
  have hUA : Disjoint ({u, v} : Set (Fin n)) (edgeSideASet G u v) := by
    refine Set.disjoint_left.mpr ?_
    intro x hxUV hxA
    have hxUV' : x = u ∨ x = v := by simpa using hxUV
    rcases hxUV' with rfl | rfl
    · exact endpoint_not_mem_edgeSideASet hxA
    · exact opposite_endpoint_not_mem_edgeSideASet hxA
  have hUB : Disjoint ({u, v} : Set (Fin n)) (edgeSideBSet G u v) := by
    refine Set.disjoint_left.mpr ?_
    intro x hxUV hxB
    have hxUV' : x = u ∨ x = v := by simpa using hxUV
    rcases hxUV' with rfl | rfl
    · exact opposite_endpoint_not_mem_edgeSideBSet hxB
    · exact endpoint_not_mem_edgeSideBSet hxB
  have hUAB : Disjoint ({u, v} : Set (Fin n))
      (edgeSideASet G u v ∪ edgeSideBSet G u v) := by
    refine Set.disjoint_left.mpr ?_
    intro x hxUV hxAB
    rcases hxAB with hxA | hxB
    · exact hUA.le_bot ⟨hxUV, hxA⟩
    · exact hUB.le_bot ⟨hxUV, hxB⟩
  have hAB : Disjoint (edgeSideASet G u v) (edgeSideBSet G u v) :=
    edgeSide_sets_disjoint htri huv
  have hcardAB : (edgeSideASet G u v ∪ edgeSideBSet G u v).ncard =
      (edgeSideASet G u v).ncard + (edgeSideBSet G u v).ncard :=
    Set.ncard_union_eq hAB
  have hcardU : U.ncard = 2 +
      (edgeSideASet G u v).ncard + (edgeSideBSet G u v).ncard := by
    dsimp [U]
    rw [Set.union_assoc]
    change (({u, v} : Set (Fin n)) ∪
      (edgeSideASet G u v ∪ edgeSideBSet G u v)).ncard = _
    rw [Set.ncard_union_eq hUAB, Set.ncard_pair huv.ne, hcardAB]
    simp [Nat.add_assoc]
  have hsum := Set.ncard_add_ncard_compl U
  have hres : residualSet G u v = Uᶜ := by simpa [U] using
    residualSet_eq_compl_endpoints_union_sides G u v
  rw [← hres] at hsum
  rw [hcardU] at hsum
  simpa [Nat.card_fin, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsum

theorem degreeSumPair_add_residual_ncard_eq_n
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (htri : G.CliqueFree 3) {u v : Fin n} (huv : G.Adj u v) :
    degreeSumPair (G, (u, v)) + (residualSet G u v).ncard = n := by
  unfold degreeSumPair
  rw [vertexDegree_eq_edgeSideB_ncard_add_one huv,
    vertexDegree_eq_edgeSideA_ncard_add_one huv]
  have h := residualSet_ncard_add_side_ncard_eq htri huv
  omega

def residualType {n : ℕ} (G : SimpleGraph (Fin n))
    (u v x : Fin n) : Set (Fin n) :=
  G.neighborSet x ∩ residualSet G u v

noncomputable def nonemptyTypeCount {n : ℕ}
    (G : SimpleGraph (Fin n)) (u v : Fin n) : ℕ :=
  (Set.ncard {x | x ∈ edgeSideASet G u v ∧
    (residualType G u v x).Nonempty}) +
  (Set.ncard {x | x ∈ edgeSideBSet G u v ∧
    (residualType G u v x).Nonempty})

def fixedDegreePairs {r n D : ℕ} :
    Set (SimpleGraph (Fin n) × (Fin n × Fin n)) :=
  {p | HighExtremalEdgePairs r n p ∧ degreeSumPair p = D}

theorem exists_high_extremal_edge_pair
    {r n : ℕ}
    (h : ∃ G : SimpleGraph (Fin n), HighChromaticTriangleFree r n G)
    (hedge : ∀ G : SimpleGraph (Fin n), HighExtremal r n G →
      ∃ u v : Fin n, G.Adj u v) :
    (HighExtremalEdgePairs r n).Nonempty := by
  obtain ⟨G, hG, hmax⟩ := exists_high_extremal h
  obtain ⟨u, v, huv⟩ := hedge G ⟨hG, hmax⟩
  exact ⟨(G, (u, v)), ⟨⟨hG, hmax⟩, huv⟩⟩

theorem exists_max_degree_sum_extremal_edge
    {r n : ℕ}
    (h : ∃ G : SimpleGraph (Fin n), HighChromaticTriangleFree r n G)
    (hedge : ∀ G : SimpleGraph (Fin n), HighExtremal r n G →
      ∃ u v : Fin n, G.Adj u v) :
    ∃ G u v, HighExtremal r n G ∧ G.Adj u v ∧
      ∀ H x y, HighExtremalEdgePairs r n (H, (x, y)) →
        vertexDegree H x + vertexDegree H y ≤ vertexDegree G u + vertexDegree G v := by
  have hp : (HighExtremalEdgePairs r n).Nonempty :=
    exists_high_extremal_edge_pair h hedge
  obtain ⟨p, hp, hmax⟩ := Set.exists_max_image
    (HighExtremalEdgePairs r n)
    degreeSumPair
    (Set.toFinite _)
    hp
  rcases p with ⟨G, uv⟩
  rcases uv with ⟨u, v⟩
  refine ⟨G, u, v, hp.1, hp.2, ?_⟩
  intro H x y hp'
  exact hmax (H, (x, y)) hp'

theorem exists_min_type_extremal_edge
    {r n : ℕ}
    (h : ∃ G : SimpleGraph (Fin n), HighChromaticTriangleFree r n G)
    (hedge : ∀ G : SimpleGraph (Fin n), HighExtremal r n G →
      ∃ u v : Fin n, G.Adj u v) :
    ∃ G u v, HighExtremal r n G ∧ G.Adj u v ∧
      (∀ H x y, HighExtremalEdgePairs r n (H, (x, y)) →
        degreeSumPair (H, (x, y)) ≤ degreeSumPair (G, (u, v))) ∧
      (∀ H x y, HighExtremalEdgePairs r n (H, (x, y)) ∧
        degreeSumPair (H, (x, y)) = degreeSumPair (G, (u, v)) →
        nonemptyTypeCount G u v ≤ nonemptyTypeCount H x y) := by
  obtain ⟨G₀, u₀, v₀, hG₀, hu₀v₀, hD⟩ :=
    exists_max_degree_sum_extremal_edge h hedge
  let D := degreeSumPair (G₀, (u₀, v₀))
  have hp : (fixedDegreePairs (r := r) (n := n) (D := D)).Nonempty := by
    exact ⟨(G₀, (u₀, v₀)), ⟨⟨hG₀, hu₀v₀⟩, rfl⟩⟩
  obtain ⟨p, hp, hmin⟩ := Set.exists_min_image
    (fixedDegreePairs (r := r) (n := n) (D := D))
    (fun p => nonemptyTypeCount p.1 p.2.1 p.2.2)
    (Set.toFinite _)
    hp
  rcases p with ⟨G, uv⟩
  rcases uv with ⟨u, v⟩
  have hGD : degreeSumPair (G, (u, v)) = D := hp.2
  refine ⟨G, u, v, hp.1.1, hp.1.2, ?_, ?_⟩
  · intro H x y hp'
    calc
      degreeSumPair (H, (x, y)) ≤ D := by
        simpa [degreeSumPair, D] using hD H x y hp'
      _ = degreeSumPair (G, (u, v)) := hGD.symm
  · intro H x y hp'
    apply hmin (H, (x, y))
    change HighExtremalEdgePairs r n (H, (x, y)) ∧
      degreeSumPair (H, (x, y)) = D
    exact ⟨hp'.1, hp'.2.trans hGD⟩

end Erdos1011

end Web_Erdos1011_ExtremalChoice
