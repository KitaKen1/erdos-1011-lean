import R5Kernel.Parts.M029

/- Source module: Erdos1011.R5S6Classification. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_R5S6Classification


namespace Erdos1011

open SimpleGraph

/- A decidable graph-isomorphism predicate for the isolated-C₅ model.  The
   explicit equivalence is convenient for the finite checker; a genuine
   `SimpleGraph` isomorphism is exported below. -/
def graphIsoS6C5 (H : SimpleGraph (Fin 6)) : Prop :=
  ∃ e : Fin 6 ≃ Fin 6, ∀ x y : Fin 6,
    H.Adj (e x) (e y) ↔ s6c5Graph.Adj x y

instance graphIsoS6C5_decidable (H : SimpleGraph (Fin 6))
    [DecidableRel H.Adj] : Decidable (graphIsoS6C5 H) := by
  unfold graphIsoS6C5
  apply Fintype.decidableExistsFintype

theorem kernel_s6_model_is_cycle : s6c5Graph = cycleGraph 6 5 := rfl

/- Fixed-model data, not an enumeration of graphs on six vertices. -/
theorem kernel_s6_nonadjacent_cases : ∀ x y : Fin 6,
    x ≠ y → ¬ s6c5Graph.Adj x y →
      x = 5 ∨ y = 5 ∨ ∃ z : Fin 6, s6c5Graph.Adj x z ∧ s6c5Graph.Adj y z := by
  decide +kernel

/- An odd cycle on six triangle-free vertices must have length five.
   Relabel its vertices and distinguish whether the remaining vertex is attached. -/
theorem kernel_s6_shape_classification
    (H : SimpleGraph (Fin 6)) (htri : triangleFree6 H)
    (hnot2 : ¬ H.Colorable 2) : attachedC5In6 H ∨ graphIsoS6C5 H := by
  classical
  have htri' : H.CliqueFree 3 := by
    intro t ht
    obtain ⟨x, y, z, hxy, hxz, hyz, _⟩ := SimpleGraph.is3Clique_iff.mp ht
    exact htri x y z hxy hxz hyz
  obtain ⟨u, p, hcyc, hodd⟩ :=
    kernel_exists_odd_cycle_of_exists_odd_closed_walk
      (kernel_exists_odd_closed_walk_of_not_colorable_two hnot2)
  have hlo := kernel_triangle_free_odd_cycle_length_ge_five htri' p hcyc hodd
  have hhi := kernel_r5_odd_cycle_length_le_card p hcyc
  have hlen : p.length = 5 := by obtain ⟨k, hk⟩ := hodd; omega
  let cyc : Fin 5 ↪ Fin 6 :=
    { toFun := fun i => p.getVert i.val
      inj' := by
        intro i j hij
        apply Fin.ext
        apply hcyc.getVert_injOn'
        · rw [hlen]; change i.val ≤ 5 - 1; omega
        · rw [hlen]; change j.val ≤ 5 - 1; omega
        · exact hij }
  let e := kernel_r5ExtendEmbeddingToPerm (by decide : 5 ≤ 6) cyc
  let f : Fin 5 → Fin 6 := fun i => e ⟨i.val, by omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    have heq := e.injective hij
    exact Fin.ext (congrArg (fun z : Fin 6 => z.val) heq)
  have hcycle : ∀ i : Fin 5,
      H.Adj (f i) (f ⟨(i.val + 1) % 5, Nat.mod_lt _ (by omega)⟩) := by
    intro i
    simp only [f, e, kernel_r5ExtendEmbeddingToPerm_apply]
    change H.Adj (p.getVert i.val) (p.getVert ((i.val + 1) % 5))
    exact kernel_r5WalkCycleAdj_mod p hcyc hlen (by omega) i
  have hforward : ∀ {x y : Fin 6}, s6c5Graph.Adj x y → H.Adj (e x) (e y) := by
    rw [kernel_s6_model_is_cycle]
    exact kernel_r5CycleGraphAdj_of_succ (by omega) (by omega) e hcycle
  by_cases hatt : ∃ i : Fin 5, H.Adj (e 5) (f i)
  · left
    refine ⟨f, e 5, hf, hcycle, ?_, hatt⟩
    intro i hi
    have heq := e.injective hi
    have hv := congrArg Fin.val heq
    change 5 = i.val at hv
    omega
  · have hzero : ∀ x : Fin 6, ¬ H.Adj (e 5) (e x) := by
      intro x hx
      by_cases hx5 : x = 5
      · subst x; exact hx.ne rfl
      · apply hatt
        refine ⟨⟨x.val, by omega⟩, ?_⟩
        exact hx
    right
    refine ⟨e, ?_⟩
    intro x y
    constructor
    · intro hadj
      by_contra hnot
      have hne : x ≠ y := fun heq => hadj.ne (congrArg e heq)
      rcases kernel_s6_nonadjacent_cases x y hne hnot with hx | hy | ⟨z, hxz, hyz⟩
      · subst x; exact hzero y hadj
      · subst y; exact hzero x hadj.symm
      · exact htri (e x) (e y) (e z) hadj (hforward hxz) (hforward hyz)
    · exact hforward

/- Preserve the original encoded API as a consequence of the structural proof. -/
theorem finite_code_six_shape_classification :
    ∀ E : Finset EdgeCode6,
      triangleFree6 (finiteCodeGraph6 E) →
      ¬ proper2_6 (finiteCodeGraph6 E) →
      attachedC5In6 (finiteCodeGraph6 E) ∨
        graphIsoS6C5 (finiteCodeGraph6 E) := by
  intro E htri hnot2
  exact kernel_s6_shape_classification _ htri
    (fun h => hnot2 (proper2_6_iff_colorable_two.mpr h))

theorem graphIsoS6C5_nonempty_iso {H : SimpleGraph (Fin 6)}
    (h : graphIsoS6C5 H) : Nonempty (s6c5Graph ≃g H) := by
  rcases h with ⟨e, he⟩
  refine ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩
  intro x y
  exact he x y

noncomputable def graphIsoS6C5Iso {H : SimpleGraph (Fin 6)}
    (h : graphIsoS6C5 H) : s6c5Graph ≃g H :=
  Classical.choice (graphIsoS6C5_nonempty_iso h)

theorem s6_shape_classification
    (H : SimpleGraph (Fin 6)) [DecidableRel H.Adj]
    (htri : triangleFree6 H) (hnot2 : ¬ H.Colorable 2) :
    attachedC5In6 H ∨ graphIsoS6C5 H := by
  let E := edgeCodeOfGraph6 H
  have hEq : finiteCodeGraph6 E = H := finiteCodeGraph6_edgeCodeOfGraph6 H
  have htriE : triangleFree6 (finiteCodeGraph6 E) := hEq.symm ▸ htri
  have hnot2E : ¬ proper2_6 (finiteCodeGraph6 E) := by
    intro hp
    apply hnot2
    exact proper2_6_iff_colorable_two.mp (hEq ▸ hp)
  have hshape := finite_code_six_shape_classification E htriE hnot2E
  exact hEq ▸ hshape

theorem induced_six_shape_classification
    {n : ℕ} {G : SimpleGraph (Fin n)} {S : Set (Fin n)}
    (htri : G.CliqueFree 3) {H : SimpleGraph (Fin 6)}
    [DecidableRel H.Adj]
    (e : (G.induce S) ≃g H)
    (hnot2 : ¬ (G.induce S).Colorable 2) :
    attachedC5In6 H ∨ graphIsoS6C5 H := by
  have hInd : (G.induce S).CliqueFree 3 := by
    intro t ht
    exact htri (t.map (.subtype S))
      ((SimpleGraph.isNClique_induce_iff (G := G) S t 3).mp ht)
  have hHtri : H.CliqueFree 3 :=
    cliqueFree_three_of_hom e.symm.toHom hInd
  have hHtri6 : triangleFree6 H := by
    intro x y z hxy hxz hyz
    exact hHtri _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy, hxz, hyz⟩)
  have hHnot2 : ¬ H.Colorable 2 := by
    intro hc
    apply hnot2
    exact SimpleGraph.Colorable.of_hom e.toHom hc
  exact s6_shape_classification H hHtri6 hHnot2

run_cmd R5Kernel.checkStandardAxioms ``kernel_s6_shape_classification
run_cmd R5Kernel.checkStandardAxioms ``finite_code_six_shape_classification
run_cmd R5Kernel.checkStandardAxioms ``induced_six_shape_classification

end Erdos1011

end Web_Erdos1011_R5S6Classification
