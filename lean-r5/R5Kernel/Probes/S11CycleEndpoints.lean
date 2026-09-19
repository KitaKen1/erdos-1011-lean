import R5Kernel.Probes.S11CycleBounds
import R5Kernel.Probes.S11C11EndpointBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000

namespace Erdos1011

theorem kernel_verified_r5_upper_from_s11_cycle_embedding
    {n ell q : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
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
    (hAdj : ∀ {x y : Fin 11}, (cycleGraph 11 ell).Adj x y →
      G.Adj (f x) (f y))
    (hbound : ∀ {A B : Finset (Finset (Fin 11))},
      A ⊆ cycleTypes 11 ell → B ⊆ cycleTypes 11 ell →
      DegreeCompatible A B → supportSurplus A B ≤ q)
    (hqsmall : q ≤ 154) :
    edgeCount G ≤ fiveCandidate n := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  have hmax : IsEdgeMaximalTriangleFree G :=
    edge_maximal_of_edgeCount_max hH.1 hH.2
  have hcompat : DegreeCompatible (supportFamilyA G u v)
      (supportFamilyB G u v) :=
    degreeCompatible_of_degree_sum_max hH huv hD hnoA hnoB
  have hq : supportSurplus (supportFamilyA G u v)
      (supportFamilyB G u v) ≤ q :=
    kernel_supportSurplus_le_of_cycle_embedding hH.1.1
      f hrange hAdj hcompat hbound
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

run_cmd R5Kernel.checkStandardAxioms ``kernel_verified_r5_upper_from_s11_cycle_embedding

theorem kernel_verified_r5_upper_from_s11_c5_embedding_exact
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
    (hAdj : ∀ {x y : Fin 11}, (cycleGraph 11 5).Adj x y →
      G.Adj (f x) (f y)) :
    edgeCount G ≤ fiveCandidate n := by
  exact kernel_verified_r5_upper_from_s11_cycle_embedding
    hn hH huv hD hnoA hnoB hS11 f hrange hAdj
    kernel_s11c5_supportSurplus_le_142 (by omega)

run_cmd R5Kernel.checkStandardAxioms ``kernel_verified_r5_upper_from_s11_c5_embedding_exact

theorem kernel_verified_r5_upper_from_s11_c7_embedding_exact
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
    (hAdj : ∀ {x y : Fin 11}, (cycleGraph 11 7).Adj x y →
      G.Adj (f x) (f y)) :
    edgeCount G ≤ fiveCandidate n := by
  exact kernel_verified_r5_upper_from_s11_cycle_embedding
    hn hH huv hD hnoA hnoB hS11 f hrange hAdj
    kernel_s11c7_supportSurplus_le_129 (by omega)

run_cmd R5Kernel.checkStandardAxioms ``kernel_verified_r5_upper_from_s11_c7_embedding_exact

theorem kernel_verified_r5_upper_from_s11_c9_embedding_exact
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
    (hAdj : ∀ {x y : Fin 11}, (cycleGraph 11 9).Adj x y →
      G.Adj (f x) (f y)) :
    edgeCount G ≤ fiveCandidate n := by
  exact kernel_verified_r5_upper_from_s11_cycle_embedding
    hn hH huv hD hnoA hnoB hS11 f hrange hAdj
    kernel_s11c9_supportSurplus_le_116 (by omega)

run_cmd R5Kernel.checkStandardAxioms ``kernel_verified_r5_upper_from_s11_c9_embedding_exact

end Erdos1011

