import R5Kernel.Parts.M009

/- Source module: Erdos1011.SupportReduction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_SupportReduction


namespace Erdos1011

open SimpleGraph

/-! Finite support families extracted from the residual neighbourhoods of an
    extremal edge.  These definitions are intentionally independent of the
    finite certificate tables: they are the graph-to-capacity interface. -/

noncomputable def residualTypeFinset
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v x : Fin n) : Finset (Fin n) := by
  classical
  exact (Set.toFinite (residualType G u v x)).toFinset

theorem mem_residualTypeFinset_iff
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v x z : Fin n} :
    z ∈ residualTypeFinset G u v x ↔ z ∈ residualType G u v x := by
  simp [residualTypeFinset]

noncomputable def nonemptyATypeVertices
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) : Finset (Fin n) := by
  classical
  exact (Set.toFinite (edgeSideASet G u v)).toFinset.filter
    (fun x => (residualType G u v x).Nonempty)

noncomputable def nonemptyBTypeVertices
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) : Finset (Fin n) := by
  classical
  exact (Set.toFinite (edgeSideBSet G u v)).toFinset.filter
    (fun x => (residualType G u v x).Nonempty)

theorem mem_nonemptyATypeVertices_iff
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v x : Fin n} :
    x ∈ nonemptyATypeVertices G u v ↔
      x ∈ edgeSideASet G u v ∧ (residualType G u v x).Nonempty := by
  simp [nonemptyATypeVertices]

theorem mem_nonemptyBTypeVertices_iff
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v x : Fin n} :
    x ∈ nonemptyBTypeVertices G u v ↔
      x ∈ edgeSideBSet G u v ∧ (residualType G u v x).Nonempty := by
  simp [nonemptyBTypeVertices]

noncomputable def supportFamilyA
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    Finset (Finset (Fin n)) := by
  classical
  exact (nonemptyATypeVertices G u v).image
    (fun x => residualTypeFinset G u v x)

noncomputable def supportFamilyB
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    Finset (Finset (Fin n)) := by
  classical
  exact (nonemptyBTypeVertices G u v).image
    (fun x => residualTypeFinset G u v x)

theorem mem_supportFamilyA_iff
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n} {I : Finset (Fin n)} :
    I ∈ supportFamilyA G u v ↔
      ∃ x, x ∈ nonemptyATypeVertices G u v ∧ residualTypeFinset G u v x = I := by
  classical
  simp [supportFamilyA]

theorem mem_supportFamilyB_iff
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n} {I : Finset (Fin n)} :
    I ∈ supportFamilyB G u v ↔
      ∃ x, x ∈ nonemptyBTypeVertices G u v ∧ residualTypeFinset G u v x = I := by
  classical
  simp [supportFamilyB]

theorem residualType_independent
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (htri : G.CliqueFree 3) (u v x : Fin n) :
    G.IsIndepSet (residualType G u v x) := by
  intro a ha b hb hab
  exact (SimpleGraph.isIndepSet_neighborSet_of_triangleFree G htri x)
    ha.1 hb.1 hab

theorem supportFamilyA_nonempty
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    {I : Finset (Fin n)} (hI : I ∈ supportFamilyA G u v) :
    I.Nonempty := by
  rcases (mem_supportFamilyA_iff.mp hI) with ⟨x, hx, rfl⟩
  exact (Set.toFinite (residualType G u v x)).toFinset_nonempty.mpr
    (mem_nonemptyATypeVertices_iff.mp hx).2

theorem supportFamilyB_nonempty
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    {I : Finset (Fin n)} (hI : I ∈ supportFamilyB G u v) :
    I.Nonempty := by
  rcases (mem_supportFamilyB_iff.mp hI) with ⟨x, hx, rfl⟩
  exact (Set.toFinite (residualType G u v x)).toFinset_nonempty.mpr
    (mem_nonemptyBTypeVertices_iff.mp hx).2

theorem supportFamilyA_independent
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (htri : G.CliqueFree 3) {u v : Fin n}
    {I : Finset (Fin n)} (hI : I ∈ supportFamilyA G u v) :
    G.IsIndepSet (I : Set (Fin n)) := by
  rcases (mem_supportFamilyA_iff.mp hI) with ⟨x, hx, rfl⟩
  intro a ha b hb hab
  apply residualType_independent htri u v x
  · exact (mem_residualTypeFinset_iff.mp ha)
  · exact (mem_residualTypeFinset_iff.mp hb)
  · exact hab

theorem supportFamilyB_independent
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (htri : G.CliqueFree 3) {u v : Fin n}
    {I : Finset (Fin n)} (hI : I ∈ supportFamilyB G u v) :
    G.IsIndepSet (I : Set (Fin n)) := by
  rcases (mem_supportFamilyB_iff.mp hI) with ⟨x, hx, rfl⟩
  intro a ha b hb hab
  apply residualType_independent htri u v x
  · exact (mem_residualTypeFinset_iff.mp ha)
  · exact (mem_residualTypeFinset_iff.mp hb)
  · exact hab

theorem residualTypeFinset_card_eq_ncard
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v x : Fin n} :
    (residualTypeFinset G u v x).card = (residualType G u v x).ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card]
  rfl

/- Endpoint exchange acts on the finite support data as expected.  These
   equalities are useful for reusing the A-side degree argument on the
   B-side without duplicating the residual-type bookkeeping. -/
theorem residualTypeFinset_swap
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v x : Fin n) :
    residualTypeFinset G v u x = residualTypeFinset G u v x := by
  ext z
  simp only [mem_residualTypeFinset_iff]
  rw [residualType_swap]

theorem nonemptyATypeVertices_swap_eq_nonemptyBTypeVertices
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    nonemptyATypeVertices G v u = nonemptyBTypeVertices G u v := by
  ext x
  rw [mem_nonemptyATypeVertices_iff, mem_nonemptyBTypeVertices_iff]
  simp [edgeSideASet, edgeSideBSet, residualType_swap]

theorem supportFamilyA_swap_eq_supportFamilyB
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    supportFamilyA G v u = supportFamilyB G u v := by
  ext I
  simp only [mem_supportFamilyA_iff, mem_supportFamilyB_iff]
  constructor
  · rintro ⟨x, hx, hIx⟩
    refine ⟨x, ?_, ?_⟩
    · rw [nonemptyATypeVertices_swap_eq_nonemptyBTypeVertices G u v] at hx
      exact hx
    · simpa [residualTypeFinset_swap] using hIx
  · rintro ⟨x, hx, hIx⟩
    refine ⟨x, ?_, ?_⟩
    · rw [← nonemptyATypeVertices_swap_eq_nonemptyBTypeVertices G u v] at hx
      exact hx
    · simpa [residualTypeFinset_swap] using hIx

theorem supportFamilyB_swap_eq_supportFamilyA
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    supportFamilyB G v u = supportFamilyA G u v := by
  exact (supportFamilyA_swap_eq_supportFamilyB G v u).symm

end Erdos1011

end Web_Erdos1011_SupportReduction
