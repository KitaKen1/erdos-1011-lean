import R5Kernel.S10Dispatcher

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace Erdos1011
open SimpleGraph

/- Preserve the original S10 endpoint signature while using only kernel proofs. -/
theorem verified_r5_upper_from_s10_odd_cycle_embedding_exact
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
    (hS10 : (residualSet G u v).ncard = 10) :
    edgeCount G ≤ fiveCandidate n := by
  exact kernel_verified_r5_upper_from_s10_odd_cycle_embedding_exact
    hn hH huv hD hnoA hnoB hS10

run_cmd R5Kernel.checkStandardAxioms ``verified_r5_upper_from_s10_odd_cycle_embedding_exact

end Erdos1011
