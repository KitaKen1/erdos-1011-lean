import R5Kernel.S8Dispatcher

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.unusedVariables false

namespace Erdos1011

/- Preserve the original endpoint types, including the now-unneeded order premise. -/
theorem verified_r5_upper_from_s8_c5_embedding_exact
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
    (hS8 : (residualSet G u v).ncard = 8)
    (horder : supportWeight (supportFamilyA G u v) ≤
      supportWeight (supportFamilyB G u v))
    (f : Fin 8 ↪ Fin n)
    (hrange : Set.range f = residualSet G u v)
    (hAdj : ∀ {x y : Fin 8}, (cycleGraph 8 5).Adj x y →
      G.Adj (f x) (f y)) :
    edgeCount G ≤ fiveCandidate n := by
  exact kernel_verified_r5_upper_from_s8_cycle_embedding
    hn hH huv hD hnoA hnoB hS8 (Or.inl rfl) f hrange hAdj

theorem verified_r5_upper_from_s8_odd_cycle_embedding_exact
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
    (hS8 : (residualSet G u v).ncard = 8)
    (horder : supportWeight (supportFamilyA G u v) ≤
      supportWeight (supportFamilyB G u v)) :
    edgeCount G ≤ fiveCandidate n := by
  exact kernel_verified_r5_upper_from_s8_odd_cycle_embedding_exact
    hn hH huv hD hnoA hnoB hS8

run_cmd R5Kernel.checkStandardAxioms ``verified_r5_upper_from_s8_c5_embedding_exact
run_cmd R5Kernel.checkStandardAxioms ``verified_r5_upper_from_s8_odd_cycle_embedding_exact

end Erdos1011

