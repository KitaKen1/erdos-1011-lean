import R5Kernel.S8UniformCertificates
import R5Kernel.SmallCycleEndpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000

namespace Erdos1011

theorem kernel_small_gap_s8_80 {n : ℕ} (hn : 80 ≤ n) :
    (n - 8)^2 / 4 + 77 ≤ fiveCandidate n := by
  rw [fiveCandidate_recenter hn]
  have hshift : n - 6 = (n - 8) + 2 := by omega
  have hsq : (n - 6)^2 = (n - 8)^2 + (4 * (n - 8) + 4) := by
    rw [hshift]
    ring
  have hdiv :
      (n - 8)^2 / 4 + (4 * (n - 8) + 4) / 4 ≤
        ((n - 8)^2 + (4 * (n - 8) + 4)) / 4 :=
    Nat.div_add_div_le_add_div
  rw [← hsq] at hdiv
  have hD : 72 ≤ (4 * (n - 8) + 4) / 4 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2
    omega
  omega

theorem kernel_verified_r5_upper_from_s8_cycle_embedding
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
    (hS8 : (residualSet G u v).ncard = 8)
    (hell : ell = 5 ∨ ell = 7)
    (f : Fin 8 ↪ Fin n) (hrange : Set.range f = residualSet G u v)
    (hAdj : ∀ {x y : Fin 8}, (cycleGraph 8 ell).Adj x y → G.Adj (f x) (f y)) :
    edgeCount G ≤ fiveCandidate n := by
  have hbound : ∀ {A B : Finset (Finset (Fin 8))},
      A ⊆ cycleTypes 8 ell → B ⊆ cycleTypes 8 ell →
      DegreeCompatible A B → supportSurplus A B ≤ 57 := by
    intro A B hA hB hcompat
    rcases hell with h5 | h7
    · subst ell
      exact kernel_s8c5_supportSurplus_le_57 hA hB hcompat
    · subst ell
      exact (kernel_s8c7_supportSurplus_le_46 hA hB hcompat).trans (by omega)
  apply kernel_verified_r5_upper_from_cycle_embedding
    hH huv hD hnoA hnoB hS8 f hrange hAdj hbound
  have hgap := kernel_small_gap_s8_80 hn
  norm_num [kernelMantelBudget]
  omega

/-- Complete S8 branch, with no numerical certificate or supplied embedding. -/
theorem kernel_verified_r5_upper_from_s8_odd_cycle_embedding_exact
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
    (hS8 : (residualSet G u v).ncard = 8) :
    edgeCount G ≤ fiveCandidate n := by
  obtain ⟨ell, hlow, hhigh, hodd, f, hrange, hAdj⟩ :=
    kernel_high_five_spanning_odd_cycle hH.1 huv hS8
  have hell : ell = 5 ∨ ell = 7 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  exact kernel_verified_r5_upper_from_s8_cycle_embedding
    hn hH huv hD hnoA hnoB hS8 hell f hrange hAdj

run_cmd R5Kernel.checkStandardAxioms ``kernel_small_gap_s8_80
run_cmd R5Kernel.checkStandardAxioms ``kernel_verified_r5_upper_from_s8_cycle_embedding
run_cmd R5Kernel.checkStandardAxioms ``kernel_verified_r5_upper_from_s8_odd_cycle_embedding_exact

end Erdos1011

