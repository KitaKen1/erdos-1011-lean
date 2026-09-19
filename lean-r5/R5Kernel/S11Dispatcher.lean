import R5Kernel.OddCycleEmbedding
import R5Kernel.Probes.S11CycleEndpoints

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace Erdos1011

/- All four cycle cases close from high extremality and residual size alone;
no cycle embedding or certificate hypothesis remains in the endpoint. -/
theorem kernel_verified_r5_upper_from_s11_odd_cycle_embedding_exact
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
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  obtain ⟨_hT, _z, _q, _hcyc, _hodd, hcases⟩ :=
    kernel_r5_high_extremal_spanning_embedding_fin11 hH.1 huv hS11
  rcases hcases with h5 | h7 | h9 | h11
  · rcases h5 with ⟨f, hrange, hAdj⟩
    exact kernel_verified_r5_upper_from_s11_c5_embedding_exact
      hn hH huv hD hnoA hnoB hS11 f hrange hAdj
  · rcases h7 with ⟨f, hrange, hAdj⟩
    exact kernel_verified_r5_upper_from_s11_c7_embedding_exact
      hn hH huv hD hnoA hnoB hS11 f hrange hAdj
  · rcases h9 with ⟨f, hrange, hAdj⟩
    exact kernel_verified_r5_upper_from_s11_c9_embedding_exact
      hn hH huv hD hnoA hnoB hS11 f hrange hAdj
  · rcases h11 with ⟨f, hrange, hAdj⟩
    exact kernel_verified_r5_upper_from_s11_c11_embedding_exact
      hn hH huv hD hnoA hnoB hS11 f hrange hAdj


run_cmd R5Kernel.checkStandardAxioms ``kernel_verified_r5_upper_from_s11_odd_cycle_embedding_exact

end Erdos1011

