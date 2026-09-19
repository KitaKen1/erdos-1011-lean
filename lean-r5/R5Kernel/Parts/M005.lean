import R5Kernel.Parts.M004

/- Source module: Erdos1011.Upper. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_Upper


namespace Erdos1011

open SimpleGraph

/- The elementary five-cycle product estimate used in the stability proof.
   We state it over `ℝ` so that the paper's expression
   `(2 z - 5 z₀) z₀` has its usual meaning; graph cardinalities can be cast to
   reals when this lemma is instantiated. -/

/-- A graph is edge-maximal triangle-free when adding every missing edge creates
a triangle.  This is the saturation interface needed by the upper-bound
argument; it is independent of any enumeration certificate. -/
def IsEdgeMaximalTriangleFree {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  G.CliqueFree 3 ∧ ∀ ⦃x y : Fin n⦄, x ≠ y → ¬ G.Adj x y →
    ¬ (G ⊔ SimpleGraph.edge x y).CliqueFree 3

/-!  Set versions are used for structural lemmas, so their statements do not
depend on the proof-irrelevant `Fintype` choices hidden in `neighborFinset`. -/

def edgeSideASet {n : ℕ} (G : SimpleGraph (Fin n))
    (u v : Fin n) : Set (Fin n) := G.neighborSet v \ {u}

def edgeSideBSet {n : ℕ} (G : SimpleGraph (Fin n))
    (u v : Fin n) : Set (Fin n) := G.neighborSet u \ {v}

@[simp] theorem mem_edgeSideASet_iff {n : ℕ} {G : SimpleGraph (Fin n)}
    {u v w : Fin n} :
    w ∈ edgeSideASet G u v ↔ G.Adj v w ∧ w ≠ u := by
  simp [edgeSideASet]

@[simp] theorem mem_edgeSideBSet_iff {n : ℕ} {G : SimpleGraph (Fin n)}
    {u v w : Fin n} :
    w ∈ edgeSideBSet G u v ↔ G.Adj u w ∧ w ≠ v := by
  simp [edgeSideBSet]

theorem edgeSideASet_subset_neighborSet {n : ℕ} {G : SimpleGraph (Fin n)}
    {u v : Fin n} : edgeSideASet G u v ⊆ G.neighborSet v := by
  intro w hw
  exact hw.1

theorem edgeSideBSet_subset_neighborSet {n : ℕ} {G : SimpleGraph (Fin n)}
    {u v : Fin n} : edgeSideBSet G u v ⊆ G.neighborSet u := by
  intro w hw
  exact hw.1

theorem edgeSideASet_independent {n : ℕ} {G : SimpleGraph (Fin n)}
    (htri : G.CliqueFree 3) (u v : Fin n) :
    G.IsIndepSet (edgeSideASet G u v) := by
  intro a ha b hb hab
  exact (SimpleGraph.isIndepSet_neighborSet_of_triangleFree G htri v)
    (edgeSideASet_subset_neighborSet ha)
    (edgeSideASet_subset_neighborSet hb) hab

theorem edgeSideBSet_independent {n : ℕ} {G : SimpleGraph (Fin n)}
    (htri : G.CliqueFree 3) (u v : Fin n) :
    G.IsIndepSet (edgeSideBSet G u v) := by
  intro a ha b hb hab
  exact (SimpleGraph.isIndepSet_neighborSet_of_triangleFree G htri u)
    (edgeSideBSet_subset_neighborSet ha)
    (edgeSideBSet_subset_neighborSet hb) hab

theorem edgeSide_sets_disjoint {n : ℕ} {G : SimpleGraph (Fin n)}
    (htri : G.CliqueFree 3) {u v : Fin n} (huv : G.Adj u v) :
    Disjoint (edgeSideASet G u v) (edgeSideBSet G u v) := by
  refine Set.disjoint_left.mpr ?_
  intro w hwA hwB
  have hvw : G.Adj v w := edgeSideASet_subset_neighborSet hwA
  have huw : G.Adj u w := edgeSideBSet_subset_neighborSet hwB
  exact htri _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨huv, huw, hvw⟩)

theorem endpoint_not_mem_edgeSideASet {n : ℕ} {G : SimpleGraph (Fin n)}
    {u v : Fin n} : u ∉ edgeSideASet G u v := by
  intro hu
  exact hu.2 rfl

theorem endpoint_not_mem_edgeSideBSet {n : ℕ} {G : SimpleGraph (Fin n)}
    {u v : Fin n} : v ∉ edgeSideBSet G u v := by
  intro hv
  exact hv.2 rfl

theorem opposite_endpoint_not_mem_edgeSideASet {n : ℕ} {G : SimpleGraph (Fin n)}
    {u v : Fin n} : v ∉ edgeSideASet G u v := by
  intro hv
  exact G.loopless.irrefl v hv.1

theorem opposite_endpoint_not_mem_edgeSideBSet {n : ℕ} {G : SimpleGraph (Fin n)}
    {u v : Fin n} : u ∉ edgeSideBSet G u v := by
  intro hu
  exact G.loopless.irrefl u hu.1

/-- Saturation gives a common neighbor for every missing pair. -/
theorem common_neighbor_of_edge_maximal
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : IsEdgeMaximalTriangleFree G)
    {x y : Fin n} (hxy : x ≠ y) (hxyG : ¬ G.Adj x y) :
    ∃ z : Fin n, G.Adj x z ∧ G.Adj y z := by
  by_contra hnone
  apply hG.2 hxy hxyG
  intro t ht
  rcases (SimpleGraph.is3Clique_iff.mp ht) with
    ⟨a, b, c, hab, hac, hbc, _⟩
  let new : Fin n → Fin n → Prop := fun p q =>
    (p = x ∧ q = y) ∨ (p = y ∧ q = x)
  have base_of_not_new : ∀ {p q : Fin n},
      (h : (G ⊔ SimpleGraph.edge x y).Adj p q) →
        ¬ new p q → G.Adj p q := by
    intro p q h hpq
    rw [SimpleGraph.sup_adj] at h
    apply h.resolve_right
    intro he
    rw [SimpleGraph.edge_adj] at he
    exact hpq he.1
  have hab' : G.Adj a b ∨ new a b := by
    rw [SimpleGraph.sup_adj] at hab
    rcases hab with habG | habE
    · exact Or.inl habG
    · rw [SimpleGraph.edge_adj] at habE
      exact Or.inr habE.1
  have hac' : G.Adj a c ∨ new a c := by
    rw [SimpleGraph.sup_adj] at hac
    rcases hac with hacG | hacE
    · exact Or.inl hacG
    · rw [SimpleGraph.edge_adj] at hacE
      exact Or.inr hacE.1
  have hbc' : G.Adj b c ∨ new b c := by
    rw [SimpleGraph.sup_adj] at hbc
    rcases hbc with hbcG | hbcE
    · exact Or.inl hbcG
    · rw [SimpleGraph.edge_adj] at hbcE
      exact Or.inr hbcE.1
  rcases hab' with habG | habN
  · rcases hac' with hacG | hacN
    · rcases hbc' with hbcG | hbcN
      · exact hG.1 _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨habG, hacG, hbcG⟩)
      · rcases hbcN with ⟨hbx, hcy⟩ | ⟨hby, hcx⟩
        · subst b; subst c
          exact hnone ⟨a, habG.symm, hacG.symm⟩
        · subst b; subst c
          exact hnone ⟨a, hacG.symm, habG.symm⟩
    · rcases hacN with ⟨hax, hcy⟩ | ⟨hay, hcx⟩
      · rcases hbc' with hbcG | hbcN
        · subst a; subst c
          exact hnone ⟨b, habG, hbcG.symm⟩
        · aesop
      · rcases hbc' with hbcG | hbcN
        · subst a; subst c
          exact hnone ⟨b, hbcG.symm, habG⟩
        · aesop
  · rcases habN with ⟨hax, hby⟩ | ⟨hay, hbx⟩
    · rcases hac' with hacG | hacN
      · rcases hbc' with hbcG | hbcN
        · subst a; subst b
          exact hnone ⟨c, hacG, hbcG⟩
        · aesop
      · aesop
    · rcases hac' with hacG | hacN
      · rcases hbc' with hbcG | hbcN
        · subst a; subst b
          exact hnone ⟨c, hbcG, hacG⟩
        · aesop
      · aesop

/- A useful analytic consequence of the Andrásfai--Erdős--Sós theorem:
   a triangle-free graph that is at least 4-chromatic must have a vertex of
   degree at most `2n/5`.  This is only a coarse bound, but it is an
   independently checked upper-bound ingredient. -/

/- The single-edge saturation condition is equivalent, for this purpose, to
   maximality in the graph lattice.  This bridge lets us apply Mathlib's
   maximal-clique-free structure lemmas without introducing a certificate. -/

/- A triangle-free graph admits at most two neighbors on a 5-cycle.  The
   proof uses only the five cycle edges: each adjacent pair of cycle vertices
   cannot both be adjacent to the same outside vertex, and summing those five
   integer inequalities gives twice the desired bound. -/

/- A triangle-free graph cannot contain the next wheel level `W₁,₁`: in
   Mathlib's indexing this follows directly from the generic clique-free
   intersection lemma.  This small fact is useful when applying the
   wheel-based minimum-degree estimate to an extracted `W₁,₀`. -/

end Erdos1011

end Web_Erdos1011_Upper
