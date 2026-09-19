import R5Kernel.S9PartialCertificates
import R5Kernel.SmallCycleEndpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000

namespace Erdos1011

theorem kernel_small_gap_s9_80 {n : ℕ} (hn : 80 ≤ n) :
    (n - 9)^2 / 4 + 114 ≤ fiveCandidate n := by
  by_cases h80 : n = 80
  · subst n
    norm_num [fiveCandidate]
  have hn81 : 81 ≤ n := by omega
  rw [fiveCandidate_recenter hn]
  have hshift : n - 6 = (n - 9) + 3 := by omega
  have hsq : (n - 6)^2 = (n - 9)^2 + (6 * (n - 9) + 9) := by
    rw [hshift]
    ring
  have hdiv :
      (n - 9)^2 / 4 + (6 * (n - 9) + 9) / 4 ≤
        ((n - 9)^2 + (6 * (n - 9) + 9)) / 4 :=
    Nat.div_add_div_le_add_div
  rw [← hsq] at hdiv
  have hD : 109 ≤ (6 * (n - 9) + 9) / 4 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2
    omega
  omega

theorem kernel_verified_r5_upper_from_s9_cycle_embedding
    {n ell q : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
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
    (hS9 : (residualSet G u v).ncard = 9)
    (hell : ell = 5 ∨ ell = 7 ∨ ell = 9)
    (f : Fin 9 ↪ Fin n) (hrange : Set.range f = residualSet G u v)
    (hAdj : ∀ {x y : Fin 9}, (cycleGraph 9 ell).Adj x y → G.Adj (f x) (f y)) :
    edgeCount G ≤ fiveCandidate n := by
  have hbound : ∀ {A B : Finset (Finset (Fin 9))},
      A ⊆ cycleTypes 9 ell → B ⊆ cycleTypes 9 ell →
      DegreeCompatible A B → supportSurplus A B ≤ 82 := by
    intro A B hA hB hcompat
    rcases hell with h5 | h7 | h9
    · subst ell
      exact kernel_s9c5_supportSurplus_le_82 hA hB hcompat
    · subst ell
      exact (kernel_s9c7_supportSurplus_le_73 hA hB hcompat).trans (by omega)
    · subst ell
      exact (kernel_s9c9_supportSurplus_le_60 hA hB hcompat).trans (by omega)
  apply kernel_verified_r5_upper_from_cycle_embedding
    hH huv hD hnoA hnoB hS9 f hrange hAdj hbound
  have hgap := kernel_small_gap_s9_80 hn
  norm_num [kernelMantelBudget]
  omega

theorem kernel_verified_r5_upper_from_s9_odd_cycle_embedding_exact
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
  obtain ⟨ell, hlow, hhigh, hodd, f, hrange, hAdj⟩ :=
    kernel_high_five_spanning_odd_cycle hH.1 huv hS9
  have hell : ell = 5 ∨ ell = 7 ∨ ell = 9 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  exact kernel_verified_r5_upper_from_s9_cycle_embedding (q := 82)
    hn hH huv hD hnoA hnoB hS9 hell f hrange hAdj

run_cmd R5Kernel.checkStandardAxioms ``kernel_small_gap_s9_80
run_cmd R5Kernel.checkStandardAxioms ``kernel_verified_r5_upper_from_s9_cycle_embedding
run_cmd R5Kernel.checkStandardAxioms ``kernel_verified_r5_upper_from_s9_odd_cycle_embedding_exact

end Erdos1011
