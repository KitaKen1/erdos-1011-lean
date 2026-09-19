import R5Kernel.S10LegacyAPI
import R5Kernel.S11Dispatcher

/- Source module: R5S10S11OddCycleExactBridge. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_R5S10S11OddCycleExactBridge


namespace Erdos1011

open SimpleGraph

/- S10 is re-exported by S10LegacyAPI with its original statement.
   Both endpoints use kernel-checked certificates and structural extraction.
   The obsolete finite-profile replay chain is not imported here. -/

set_option maxHeartbeats 5000000 in
theorem verified_r5_upper_from_s11_odd_cycle_embedding_exact
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
    (hS11 : (residualSet G u v).ncard = 11) :
    edgeCount G ≤ fiveCandidate n := by
  exact kernel_verified_r5_upper_from_s11_odd_cycle_embedding_exact
    hn hH huv hD hnoA hnoB hS11

run_cmd R5Kernel.checkStandardAxioms ``verified_r5_upper_from_s11_odd_cycle_embedding_exact

end Erdos1011

end Web_R5S10S11OddCycleExactBridge
