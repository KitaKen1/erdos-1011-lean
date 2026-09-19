import R5Kernel.SmallUniform
import R5Kernel.OddCycleEmbedding

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace Erdos1011
open SimpleGraph

/-- No external shape selector: an odd cycle is extracted from high chromaticity. -/
theorem kernel_high_five_spanning_odd_cycle
    {n s : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (hG : HighChromaticTriangleFree 5 n G) (huv : G.Adj u v)
    (hS : (residualSet G u v).ncard = s) :
    ∃ ell, 5 ≤ ell ∧ ell ≤ s ∧ Odd ell ∧
      ∃ f : Fin s ↪ Fin n, Set.range f = residualSet G u v ∧
        ∀ {x y : Fin s}, (cycleGraph s ell).Adj x y → G.Adj (f x) (f y) := by
  classical
  obtain ⟨hT, z, q, hcyc, hodd⟩ :=
    kernel_r5_odd_cycle_of_high_extremal_residual_card_generic hG huv hS
  let g := kernel_residualEmbeddingOfCardEq (residualFinset G u v) hT
  letI : DecidableRel (G.comap g).Adj := Classical.decRel _
  have htri : (G.comap g).CliqueFree 3 :=
    SimpleGraph.CliqueFree.comap
      (SimpleGraph.Embedding.comap g G).isContained hG.1
  have hnot3 : q.length ≠ 3 := by
    intro h3
    rcases (is3Clique_iff_exists_cycle_length_three (G := G.comap g)).mpr
      ⟨z, q, hcyc, h3⟩ with ⟨t, ht⟩
    exact htri t ht
  have hlow : 5 ≤ q.length := by
    have h3 := hcyc.three_le_length
    obtain ⟨k, hk⟩ := hodd
    omega
  have hhigh := kernel_r5_odd_cycle_length_le_card q hcyc
  obtain ⟨f, hrange, hAdj⟩ := kernel_r5SpanningEmbeddingOfCycle
    (residualFinset G u v) hT q hcyc rfl hhigh (by omega)
  refine ⟨q.length, hlow, hhigh, hodd, f, ?_, hAdj⟩
  rw [hrange]
  ext x
  exact mem_residualFinset_iff

def kernelMantelBudget (s : ℕ) : ℕ :=
  (s ^ 2 - (s % 2) ^ 2) / 4 + (s % 2).choose 2

theorem kernel_residual_edge_bound_of_triangle_free_card
    {n s : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (htri : G.CliqueFree 3) (hS : (residualSet G u v).ncard = s) :
    ∀ [DecidableRel G.Adj],
      (G.induce (residualFinset G u v : Set (Fin n))).edgeFinset.card ≤
        kernelMantelBudget s := by
  intro inst
  let S := residualFinset G u v
  have hScard : S.card = s := by
    dsimp [S]
    rw [residualFinset_card_eq_ncard]
    exact hS
  let H := G.induce (S : Set (Fin n))
  have hHtri : H.CliqueFree 3 := by
    intro t ht
    apply htri (t.map (.subtype (S : Set (Fin n))))
    exact (SimpleGraph.isNClique_induce_iff (S : Set (Fin n)) t 3).mp ht
  have hbound := SimpleGraph.CliqueFree.card_edgeFinset_le (G := H) (r := 2) hHtri
  simpa [H, S, Fintype.card_coe, hScard, kernelMantelBudget,
    SimpleGraph.card_edgeFinset_turanGraph] using hbound

theorem kernel_verified_r5_upper_from_cycle_embedding
    {n s ell q : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n}
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
    (hS : (residualSet G u v).ncard = s)
    (f : Fin s ↪ Fin n) (hrange : Set.range f = residualSet G u v)
    (hAdj : ∀ {x y : Fin s}, (cycleGraph s ell).Adj x y → G.Adj (f x) (f y))
    (hbound : ∀ {A B : Finset (Finset (Fin s))},
      A ⊆ cycleTypes s ell → B ⊆ cycleTypes s ell →
      DegreeCompatible A B → supportSurplus A B ≤ q)
    (hbudget : (n - s)^2 / 4 + kernelMantelBudget s + q ≤ fiveCandidate n) :
    edgeCount G ≤ fiveCandidate n := by
  classical
  have hmax : IsEdgeMaximalTriangleFree G := edge_maximal_of_edgeCount_max hH.1 hH.2
  have hcompat := degreeCompatible_of_degree_sum_max hH huv hD hnoA hnoB
  have hq := kernel_supportSurplus_le_of_cycle_embedding hH.1.1
    f hrange hAdj hcompat hbound
  have he := kernel_residual_edge_bound_of_triangle_free_card hH.1.1 hS
  have hsum := full_side_degree_residual_card_sum hmax.1 huv
  have hsum' : (sideAFinset G u v).card.succ +
      (sideBFinset G u v).card.succ = n - s := by
    rw [hS] at hsum
    omega
  have hdecomp := edgeCount_le_full_product_plus_residual_bound_of_additive
    (G := G) hmax huv hnoA hnoB he hq
  have hab := nat_mul_le_add_sq_div_four
    (sideAFinset G u v).card.succ (sideBFinset G u v).card.succ
  rw [hsum'] at hab
  omega

run_cmd R5Kernel.checkStandardAxioms ``kernel_high_five_spanning_odd_cycle
run_cmd R5Kernel.checkStandardAxioms ``kernel_residual_edge_bound_of_triangle_free_card
run_cmd R5Kernel.checkStandardAxioms ``kernel_verified_r5_upper_from_cycle_embedding

end Erdos1011
