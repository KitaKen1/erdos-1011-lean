import R5Kernel.Parts.M010

/- Source module: Erdos1011.CoreReduction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_CoreReduction


namespace Erdos1011

open SimpleGraph

theorem four_mul_fiveCandidate_ge
    {n : ℕ} (hn : 27 ≤ n) :
    n ^ 2 - 12 * n + 55 ≤ 4 * fiveCandidate n := by
  unfold fiveCandidate
  have hr : n % 4 < 4 := Nat.mod_lt _ (by omega)
  have hmod := Nat.pow_mod n 2 4
  interval_cases h : n % 4 <;> norm_num [h] at hmod
  all_goals have hdiv := Nat.mod_add_div (n ^ 2) 4
  all_goals omega

theorem residual_ncard_le_eleven_of_degree_sum_bound
    {n m D s : ℕ} (hn : 27 ≤ n)
    (hm : fiveCandidate n ≤ m)
    (havg : 4 * m ≤ n * D)
    (hsum : D + s = n) :
    s ≤ 11 := by
  have hbase := four_mul_fiveCandidate_ge hn
  have hmul : 4 * fiveCandidate n ≤ 4 * m :=
    Nat.mul_le_mul_left 4 hm
  have hineq : n ^ 2 - 12 * n + 55 ≤ n * D :=
    hbase.trans (hmul.trans havg)
  by_contra hs
  have hs12 : 12 ≤ s := by omega
  have hn12 : 12 ≤ n := by omega
  have hprod : 12 * n ≤ s * n := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right n hs12
  have hprod' : 12 * n ≤ n * s := by
    simpa [Nat.mul_comm] using hprod
  have hsq : 12 * n ≤ n ^ 2 := by
    have := Nat.mul_le_mul_left n hn12
    simpa [pow_two, Nat.mul_comm] using this
  have hsq' : 12 * n ≤ n * n := by
    simpa [pow_two] using hsq
  have hmulSum := congrArg (fun x => n * x) hsum
  simp only [Nat.mul_add] at hmulSum
  have hineq' : n * n - 12 * n + 55 ≤ n * D := by
    simpa [pow_two] using hineq
  omega

theorem high_extremal_edgeCount_ge_fiveCandidate
    {n : ℕ} (hn : 80 ≤ n) {G : SimpleGraph (Fin n)}
    (hG : HighExtremal 5 n G) :
    fiveCandidate n ≤ edgeCount G := by
  obtain ⟨a, b, ha, hb, hcard, hE⟩ := five_blowup_parameters hn
  obtain ⟨W, hW, hEW⟩ := qBlowup_fin_witness ha hb hcard
  have hle := hG.2 W hW
  simpa [hEW, hE] using hle

theorem high_extremal_residual_ncard_le_eleven
    {n : ℕ} (hn : 80 ≤ n) {G : SimpleGraph (Fin n)}
    (hG : HighExtremal 5 n G) {u v : Fin n} (huv : G.Adj u v)
    (havg : 4 * edgeCount G ≤ n * degreeSumPair (G, (u, v))) :
    (residualSet G u v).ncard ≤ 11 := by
  have hsum := degreeSumPair_add_residual_ncard_eq_n hG.1.1 huv
  exact residual_ncard_le_eleven_of_degree_sum_bound (by omega)
    (high_extremal_edgeCount_ge_fiveCandidate hn hG) havg hsum

/-! A first formal version of the key residual reduction used in the paper:
    if the residual graph of an edge is bipartite, the whole triangle-free
    graph is four-colourable.  The proof is deliberately written with the
    endpoint/sides/residual partition exposed, so later capacity lemmas can
    use it without unpacking an informal picture. -/

theorem colorable_four_of_residual_colorable_two
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (htri : G.CliqueFree 3) (huv : G.Adj u v)
    (hS : (G.induce (residualSet G u v)).Colorable 2) :
    G.Colorable 4 := by
  classical
  obtain ⟨C⟩ := hS
  have huv_ne : u ≠ v := huv.ne
  let c : Fin n → Fin 4 := fun z =>
    if z = u then 0
    else if z = v then 1
    else if z ∈ edgeSideASet G u v then 0
    else if z ∈ edgeSideBSet G u v then 1
    else if hz : z ∈ residualSet G u v then
      Fin.natAdd 2 (C ⟨z, hz⟩)
    else 0
  have hcu : c u = 0 := by simp only [c, if_pos rfl]
  have hcv : c v = 1 := by simp [c, huv_ne, huv_ne.symm]
  have hca {x : Fin n} (hx : x ∈ edgeSideASet G u v) : c x = 0 := by
    have hxu : x ≠ u := hx.2
    have hxv : x ≠ v := by
      intro h
      subst x
      exact G.loopless.irrefl v hx.1
    simp only [c, if_neg hxu, if_neg hxv, if_pos hx]
  have hcb {x : Fin n} (hx : x ∈ edgeSideBSet G u v) : c x = 1 := by
    have hxv : x ≠ v := hx.2
    have hxu : x ≠ u := by
      intro h
      subst x
      exact G.loopless.irrefl u hx.1
    have hxa : x ∉ edgeSideASet G u v := by
      intro h
      exact Set.disjoint_left.mp (edgeSide_sets_disjoint htri huv) h hx
    simp only [c, if_neg hxu, if_neg hxv, if_neg hxa, if_pos hx]
  have hcs {x : Fin n} (hx : x ∈ residualSet G u v) :
      c x = Fin.natAdd 2 (C ⟨x, hx⟩) := by
    have hxa : x ∉ edgeSideASet G u v := by
      intro h
      exact hx.2.2.2 h.1
    have hxb : x ∉ edgeSideBSet G u v := by
      intro h
      exact hx.2.2.1 h.1
    simp only [c, if_neg hx.1, if_neg hx.2.1, if_neg hxa, if_neg hxb, dif_pos hx]
  have h0shift (a : Fin 2) : (0 : Fin 4) ≠ Fin.natAdd 2 a := by
    intro h
    have hv := congrArg Fin.val h
    simp [Fin.natAdd] at hv
    omega
  have h1shift (a : Fin 2) : (1 : Fin 4) ≠ Fin.natAdd 2 a := by
    intro h
    have hv := congrArg Fin.val h
    simp [Fin.natAdd] at hv
    omega
  have hshift0 (a : Fin 2) : Fin.natAdd 2 a ≠ (0 : Fin 4) :=
    (h0shift a).symm
  have hshift1 (a : Fin 2) : Fin.natAdd 2 a ≠ (1 : Fin 4) :=
    (h1shift a).symm
  have hshift_ne {a b : Fin 2} (hab : a ≠ b) :
      Fin.natAdd 2 a ≠ Fin.natAdd 2 b := by
    intro h
    apply hab
    exact (Fin.natAdd_inj 2).mp h
  have hvalid : ∀ {x y : Fin n}, G.Adj x y → c x ≠ c y := by
    intro x y hxy
    have hxy_ne : x ≠ y := hxy.ne
    have hpart (z : Fin n) :
        z = u ∨ z = v ∨ z ∈ edgeSideASet G u v ∨
          z ∈ edgeSideBSet G u v ∨ z ∈ residualSet G u v := by
      have heq := residualSet_eq_compl_endpoints_union_sides G u v
      by_cases hzu : z = u
      · exact Or.inl hzu
      by_cases hzv : z = v
      · exact Or.inr (Or.inl hzv)
      by_cases hzA : z ∈ edgeSideASet G u v
      · exact Or.inr (Or.inr (Or.inl hzA))
      by_cases hzB : z ∈ edgeSideBSet G u v
      · exact Or.inr (Or.inr (Or.inr (Or.inl hzB)))
      right; right; right; right
      rw [heq]
      simp [hzu, hzv, hzA, hzB]
    have hnot_u_A {z : Fin n} (hzA : z ∈ edgeSideASet G u v)
        (huz : G.Adj u z) : False := by
      exact htri _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨huv, huz, hzA.1⟩)
    have hnot_v_B {z : Fin n} (hzB : z ∈ edgeSideBSet G u v)
        (hvz : G.Adj v z) : False := by
      exact htri _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨huv.symm, hvz, hzB.1⟩)
    rcases hpart x with hxu | hxv | hxA | hxB | hxS
    · subst x
      rcases hpart y with hyu | hyv | hyA | hyB | hyS
      · exact (hxy_ne hyu.symm).elim
      · subst y; rw [hcu, hcv]; decide
      · exact (hnot_u_A hyA hxy).elim
      · rw [hcu, hcb hyB]; decide
      · exact (hyS.2.2.1 hxy).elim
    · subst x
      rcases hpart y with hyu | hyv | hyA | hyB | hyS
      · subst y; rw [hcv, hcu]; decide
      · exact (hxy_ne hyv.symm).elim
      · rw [hcv, hca hyA]; decide
      · exact (hnot_v_B hyB hxy).elim
      · exact (hyS.2.2.2 hxy).elim
    · rcases hpart y with hyu | hyv | hyA | hyB | hyS
      · subst y; exact (hnot_u_A hxA hxy.symm).elim
      · subst y; rw [hca hxA, hcv]; decide
      · exact ((edgeSideASet_independent htri u v hxA hyA hxy_ne) hxy).elim
      · rw [hca hxA, hcb hyB]; decide
      · rw [hca hxA, hcs hyS]; exact h0shift _
    · rcases hpart y with hyu | hyv | hyA | hyB | hyS
      · subst y; rw [hcb hxB, hcu]; decide
      · subst y; exact (hnot_v_B hxB hxy.symm).elim
      · rw [hcb hxB, hca hyA]; decide
      · exact ((edgeSideBSet_independent htri u v hxB hyB hxy_ne) hxy).elim
      · rw [hcb hxB, hcs hyS]; exact h1shift _
    · rcases hpart y with hyu | hyv | hyA | hyB | hyS
      · subst y; exact (hxS.2.2.1 hxy.symm).elim
      · subst y; exact (hxS.2.2.2 hxy.symm).elim
      · rw [hcs hxS, hca hyA]; exact hshift0 _
      · rw [hcs hxS, hcb hyB]; exact hshift1 _
      · have hC : C ⟨x, hxS⟩ ≠ C ⟨y, hyS⟩ := by
          apply C.valid
          simpa only [SimpleGraph.induce_adj] using hxy
        rw [hcs hxS, hcs hyS]
        exact hshift_ne hC
  exact ⟨Coloring.mk c hvalid⟩

/- A sharpened three-colour version for a bipartite residual graph.  The
   residual 2-colouring is required to make every B-type monochromatic; a B
   vertex can then use whichever of the two residual colours it does not see.
   This is the structural lemma used to exclude the residual P₃ shape. -/

/- If the residual induced graph has no edges, the two sides and the residual
   set can be coloured with three colours directly.  This is the small-
   residual branch needed before applying the finite s=3 capacity table. -/

theorem residual_not_colorable_two_of_high_five
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (hG : HighChromaticTriangleFree 5 n G) (huv : G.Adj u v) :
    ¬ (G.induce (residualSet G u v)).Colorable 2 := by
  intro hS
  have h4 : G.Colorable 4 := colorable_four_of_residual_colorable_two hG.1 huv hS
  have hle : G.chromaticNumber ≤ 4 := h4.chromaticNumber_le
  have hbad : (5 : ℕ∞) ≤ 4 := hG.2.trans hle
  norm_num at hbad

/- The choice machinery can now be instantiated at r=5 without any extra
   hypothesis about where an edge comes from: chromatic number at least five
   implies that the graph is not the bottom graph, hence has an edge. -/
theorem exists_twinized_extremal_edge_five
    {n : ℕ}
    (h : ∃ G : SimpleGraph (Fin n),
      HighChromaticTriangleFree 5 n G) :
    ∃ G u v, HighExtremal 5 n G ∧ G.Adj u v ∧
      (∀ H a b, HighExtremalEdgePairs 5 n (H, (a, b)) →
        degreeSumPair (H, (a, b)) ≤ degreeSumPair (G, (u, v))) ∧
      (∀ H a b, HighExtremalEdgePairs 5 n (H, (a, b)) →
        degreeSumPair (H, (a, b)) = degreeSumPair (G, (u, v)) →
        nonemptyTypeCount G u v ≤ nonemptyTypeCount H a b) ∧
      (∀ x x', x ∈ edgeSideASet G u v →
        x' ∈ edgeSideASet G u v → x ≠ x' →
        (residualType G u v x).Nonempty →
        residualType G u v x ≠ residualType G u v x') ∧
      (∀ y y', y ∈ edgeSideBSet G u v →
        y' ∈ edgeSideBSet G u v → y ≠ y' →
        (residualType G u v y).Nonempty →
        residualType G u v y ≠ residualType G u v y') ∧
      ¬ (G.induce (residualSet G u v)).Colorable 2 := by
  have hedge : ∀ G : SimpleGraph (Fin n), HighExtremal 5 n G →
      ∃ u v : Fin n, G.Adj u v := by
    intro G hG
    have htwo : (2 : ℕ∞) ≤ G.chromaticNumber := by
      exact le_trans (by norm_num) hG.1.2
    have hne : G ≠ (⊥ : SimpleGraph (Fin n)) :=
      (two_le_chromaticNumber_iff_ne_bot).mp htwo
    exact (ne_bot_iff_exists_adj).mp hne
  obtain ⟨G, u, v, hG, huv, hD, hmin, hnoA, hnoB⟩ :=
    exists_twinized_extremal_edge h hedge
  refine ⟨G, u, v, hG, huv, hD, hmin, hnoA, hnoB, ?_⟩
  exact residual_not_colorable_two_of_high_five hG.1 huv

end Erdos1011

end Web_Erdos1011_CoreReduction
