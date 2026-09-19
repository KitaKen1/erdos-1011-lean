import R5Kernel.S9Dispatcher

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000

namespace Erdos1011

/- A small, independently auditable adapter with the exact type consumed by
   the direct upper-bound layer.  Keeping this bridge separate avoids pulling
   the historical M068--M079 replay chain into the S9 audit. -/
theorem kernel_verified_r5_upper_from_s9_odd_cycle_embedding_exact_direct
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n}
    (hn : 80 ≤ n) (hH : HighExtremal 5 n G) (huv : G.Adj u v)
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
    (hS9 : (residualSet G u v).ncard = 9) :
    edgeCount G ≤ fiveCandidate n := by
  exact kernel_verified_r5_upper_from_s9_odd_cycle_embedding_exact
    hn hH huv hD hnoA hnoB hS9

run_cmd R5Kernel.checkStandardAxioms ``kernel_verified_r5_upper_from_s9_odd_cycle_embedding_exact_direct

end Erdos1011
