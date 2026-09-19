import R5Kernel.S7C5Certificates
import R5Kernel.S7C7Certificates
import R5Kernel.S7C5EdgeBound
import R5Kernel.SmallCycleEndpoint
import R5Kernel.Parts.M024

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000

namespace Erdos1011
open SimpleGraph

theorem kernel_s7_residual_edge_bound_of_c5_embedding
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (htri : G.CliqueFree 3)
    (f : Fin 7 ↪ Fin n) (hrange : Set.range f = residualSet G u v)
    (hAdj : ∀ {x y : Fin 7}, (cycleGraph 7 5).Adj x y → G.Adj (f x) (f y)) :
    (G.induce (residualFinset G u v : Set (Fin n))).edgeFinset.card ≤ 10 := by
  classical
  have htri7 : (G.comap f).CliqueFree 3 :=
    SimpleGraph.CliqueFree.comap (SimpleGraph.Embedding.comap f G).isContained htri
  have he := kernel_s7_c5_edge_bound htri7 (by intro x y h; exact hAdj h)
  have e : G.comap f ≃g G.induce (Set.range f) :=
    (SimpleGraph.Embedding.comap f G).isoInduceRange
  have hset : Set.range f = (residualFinset G u v : Set (Fin n)) := by
    rw [hrange]
    ext x
    exact mem_residualFinset_iff.symm
  rw [hset] at e
  rw [← e.card_edgeFinset_eq]
  exact he

/- The C5 and C7 cases have separate edge/surplus budgets: 10+32 and 12+27.
No classification into the old twenty seven-vertex graph profiles is used. -/
theorem kernel_verified_r5_upper_from_s7_odd_cycle_embedding_exact
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (hn : 80 ≤ n)
    (hH : HighExtremal 5 n G) (huv : G.Adj u v)
    (hD : ∀ H a b, HighExtremalEdgePairs 5 n (H, (a, b)) →
      degreeSumPair (H, (a, b)) ≤ degreeSumPair (G, (u, v)))
    (hnoA : ∀ x x', x ∈ edgeSideASet G u v →
      x' ∈ edgeSideASet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    (hnoB : ∀ x x', x ∈ edgeSideBSet G u v →
      x' ∈ edgeSideBSet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    (hS7 : (residualSet G u v).ncard = 7) :
    edgeCount G ≤ fiveCandidate n := by
  classical
  obtain ⟨ell, hlow, hhigh, hodd, f, hrange, hAdj⟩ :=
    kernel_high_five_spanning_odd_cycle hH.1 huv hS7
  have hell : ell = 5 ∨ ell = 7 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hgap := small_gap_s7_80 hn
  rcases hell with h5 | h7
  · subst ell
    have hmax : IsEdgeMaximalTriangleFree G := edge_maximal_of_edgeCount_max hH.1 hH.2
    have hcompat := degreeCompatible_of_degree_sum_max hH huv hD hnoA hnoB
    have hq := kernel_supportSurplus_le_of_cycle_embedding hH.1.1
      f hrange hAdj hcompat S7C5.supportSurplus_le_32
    have he := kernel_s7_residual_edge_bound_of_c5_embedding hH.1.1 f hrange hAdj
    have hsum := full_side_degree_residual_card_sum hmax.1 huv
    have hsum' : (sideAFinset G u v).card.succ +
        (sideBFinset G u v).card.succ = n - 7 := by
      rw [hS7] at hsum
      omega
    have hdecomp := edgeCount_le_full_product_plus_residual_bound_of_additive
      (G := G) hmax huv hnoA hnoB he hq
    have hab := nat_mul_le_add_sq_div_four
      (sideAFinset G u v).card.succ (sideBFinset G u v).card.succ
    rw [hsum'] at hab
    omega
  · subst ell
    apply kernel_verified_r5_upper_from_cycle_embedding
      hH huv hD hnoA hnoB hS7 f hrange hAdj S7C7.supportSurplus_le_27
    norm_num [kernelMantelBudget]
    omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_s7_residual_edge_bound_of_c5_embedding
run_cmd R5Kernel.checkStandardAxioms ``kernel_verified_r5_upper_from_s7_odd_cycle_embedding_exact

end Erdos1011
