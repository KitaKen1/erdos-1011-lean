import R5Kernel.S7Dispatcher

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace Erdos1011
open SimpleGraph

/- Preserve the old endpoint type; the new proof needs no support orientation. -/
theorem verified_r5_upper_from_s7_shape_auto_direct
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
    (horder : supportWeight (supportFamilyA G u v) ≤
      supportWeight (supportFamilyB G u v))
    (hS7 : (residualSet G u v).ncard = 7) :
    edgeCount G ≤ fiveCandidate n := by
  exact kernel_verified_r5_upper_from_s7_odd_cycle_embedding_exact
    hn hH huv hD hnoA hnoB hS7

run_cmd R5Kernel.checkStandardAxioms ``verified_r5_upper_from_s7_shape_auto_direct

end Erdos1011
