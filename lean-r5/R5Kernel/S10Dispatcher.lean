import R5Kernel.S10C5Certificates
import R5Kernel.S10C7Certificates
import R5Kernel.S10C9Certificates
import R5Kernel.S10UniformData
import R5Kernel.SmallCycleEndpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000

namespace Erdos1011

theorem kernel_verified_r5_upper_from_s10_cycle_embedding
    {n ell : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
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
    (hS10 : (residualSet G u v).ncard = 10)
    (hell : ell = 5 ∨ ell = 7 ∨ ell = 9)
    (f : Fin 10 ↪ Fin n) (hrange : Set.range f = residualSet G u v)
    (hAdj : ∀ {x y : Fin 10}, (cycleGraph 10 ell).Adj x y → G.Adj (f x) (f y)) :
    edgeCount G ≤ fiveCandidate n := by
  have hbound : ∀ {A B : Finset (Finset (Fin 10))},
      A ⊆ cycleTypes 10 ell → B ⊆ cycleTypes 10 ell →
      DegreeCompatible A B → supportSurplus A B ≤ 113 := by
    intro A B hA hB hcompat
    rcases hell with h5 | h7 | h9
    · subst ell
      exact S10C5.supportSurplus_le_113 hA hB hcompat
    · subst ell
      exact (S10C7.supportSurplus_le_107 hA hB hcompat).trans (by omega)
    · subst ell
      exact (S10C9.supportSurplus_le_92 hA hB hcompat).trans (by omega)
  apply kernel_verified_r5_upper_from_cycle_embedding
    hH huv hD hnoA hnoB hS10 f hrange hAdj hbound
  have hgap := kernel_small_gap_s10_80 hn
  norm_num [kernelMantelBudget]
  omega

theorem kernel_verified_r5_upper_from_s10_odd_cycle_embedding_exact
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
    (hS10 : (residualSet G u v).ncard = 10) :
    edgeCount G ≤ fiveCandidate n := by
  obtain ⟨ell, hlow, hhigh, hodd, f, hrange, hAdj⟩ :=
    kernel_high_five_spanning_odd_cycle hH.1 huv hS10
  have hell : ell = 5 ∨ ell = 7 ∨ ell = 9 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  exact kernel_verified_r5_upper_from_s10_cycle_embedding
    hn hH huv hD hnoA hnoB hS10 hell f hrange hAdj

run_cmd R5Kernel.checkStandardAxioms ``kernel_verified_r5_upper_from_s10_cycle_embedding
run_cmd R5Kernel.checkStandardAxioms ``kernel_verified_r5_upper_from_s10_odd_cycle_embedding_exact

end Erdos1011
