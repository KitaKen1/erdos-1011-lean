import R5Kernel.Probes.S11C11EmbeddingBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1
set_option maxRecDepth 200000

open Lean Elab Command

namespace Erdos1011

theorem kernel_small_gap_s11_80 {n : ℕ} (hn : 80 ≤ n) :
    (n - 11)^2 / 4 + 184 ≤ fiveCandidate n := by
  by_cases h80 : n = 80
  · subst n
    norm_num [fiveCandidate]
  by_cases h81 : n = 81
  · subst n
    norm_num [fiveCandidate]
  by_cases h82 : n = 82
  · subst n
    norm_num [fiveCandidate]
  have hn83 : 83 ≤ n := by omega
  have hn80 : 80 ≤ n := by omega
  rw [fiveCandidate_recenter hn80]
  have hshift : n - 6 = (n - 11) + 5 := by omega
  have hsq : (n - 6)^2 = (n - 11)^2 + (10 * (n - 11) + 25) := by
    rw [hshift]
    ring
  have hdiv :
      (n - 11)^2 / 4 + (10 * (n - 11) + 25) / 4 ≤
        ((n - 11)^2 + (10 * (n - 11) + 25)) / 4 :=
    Nat.div_add_div_le_add_div
  rw [← hsq] at hdiv
  have hD : 179 ≤ (10 * (n - 11) + 25) / 4 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2
    omega
  omega

theorem kernel_residual_decomposition_bound_s11_small
    {n a b e q m : ℕ} (hn : 80 ≤ n)
    (hsum : a + b + 11 = n) (heq : e + q ≤ 184)
    (hdecomp : m ≤ a * b + e + q) : m ≤ fiveCandidate n := by
  have hab : a * b ≤ (a + b)^2 / 4 := nat_mul_le_add_sq_div_four a b
  have hshift : a + b = n - 11 := by omega
  have hab' : a * b ≤ (n - 11)^2 / 4 := by
    calc a * b ≤ (a + b)^2 / 4 := hab
      _ = (n - 11)^2 / 4 := by rw [hshift]
  have hbound : m ≤ (n - 11)^2 / 4 + 184 := by omega
  exact hbound.trans (kernel_small_gap_s11_80 hn)

theorem kernel_residual_edge_bound_s11_of_triangle_free
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (htri : G.CliqueFree 3)
    (hS11 : (residualSet G u v).ncard = 11) :
    ∀ [DecidableRel G.Adj],
      (G.induce (residualFinset G u v : Set (Fin n))).edgeFinset.card ≤ 30 := by
  intro inst
  letI : DecidableRel G.Adj := inst
  let S := residualFinset G u v
  have hScard : S.card = 11 := by
    dsimp [S]
    rw [residualFinset_card_eq_ncard]
    exact hS11
  let H := G.induce (S : Set (Fin n))
  have hHtri : H.CliqueFree 3 := by
    intro t ht
    apply htri (t.map (.subtype (S : Set (Fin n))))
    exact (SimpleGraph.isNClique_induce_iff
      (S : Set (Fin n)) t 3).mp ht
  have hbound := SimpleGraph.CliqueFree.card_edgeFinset_le
    (G := H) (r := 2) hHtri
  have hbound' : H.edgeFinset.card ≤ 30 := by
    simpa [H, Fintype.card_coe, hScard,
      SimpleGraph.card_edgeFinset_turanGraph] using hbound
  simpa [H, S] using hbound'

set_option maxHeartbeats 3000000 in
theorem kernel_verified_r5_upper_from_s11_c11_embedding_exact
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n}
    (hn : 80 ≤ n)
    (hH : HighExtremal 5 n G)
    (huv : G.Adj u v)
    (hD : ∀ H _a _b, HighExtremalEdgePairs 5 n (H, (_a, _b)) →
      degreeSumPair (H, (_a, _b)) ≤ degreeSumPair (G, (u, v)))
    (hnoA : ∀ x x', x ∈ edgeSideASet G u v →
      x' ∈ edgeSideASet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    (hnoB : ∀ x x', x ∈ edgeSideBSet G u v →
      x' ∈ edgeSideBSet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    (hS11 : (residualSet G u v).ncard = 11)
    (f : Fin 11 ↪ Fin n)
    (hrange : Set.range f = residualSet G u v)
    (hAdj : ∀ {x y : Fin 11}, (cycleGraph 11 11).Adj x y →
      G.Adj (f x) (f y)) :
    edgeCount G ≤ fiveCandidate n := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  have hmax : IsEdgeMaximalTriangleFree G :=
    edge_maximal_of_edgeCount_max hH.1 hH.2
  have hcompat : DegreeCompatible (supportFamilyA G u v)
      (supportFamilyB G u v) :=
    degreeCompatible_of_degree_sum_max hH huv hD hnoA hnoB
  have hq : supportSurplus (supportFamilyA G u v)
      (supportFamilyB G u v) ≤ 103 :=
    kernel_c11_supportSurplus_le_103_of_cycle_embedding hH.1.1
      f hrange hAdj hcompat
  have he :
      (G.induce (residualFinset G u v : Set (Fin n))).edgeFinset.card ≤ 30 :=
    kernel_residual_edge_bound_s11_of_triangle_free hH.1.1 hS11
  have hsum := full_side_degree_residual_card_sum hmax.1 huv
  have hsum11 : (sideAFinset G u v).card.succ +
      (sideBFinset G u v).card.succ + 11 = n := by
    simpa [hS11] using hsum
  have hdecomp := edgeCount_le_full_product_plus_residual_bound_of_additive
    (G := G) hmax huv hnoA hnoB he hq
  exact kernel_residual_decomposition_bound_s11_small hn hsum11
    (by omega) hdecomp

run_cmd R5Kernel.checkStandardAxioms ``kernel_small_gap_s11_80
run_cmd R5Kernel.checkStandardAxioms ``kernel_residual_decomposition_bound_s11_small
run_cmd R5Kernel.checkStandardAxioms ``kernel_residual_edge_bound_s11_of_triangle_free
run_cmd R5Kernel.checkStandardAxioms ``kernel_verified_r5_upper_from_s11_c11_embedding_exact

end Erdos1011
