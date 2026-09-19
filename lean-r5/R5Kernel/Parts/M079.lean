import R5Kernel.Parts.M078
import R5Kernel.Parts.M033
import R5Kernel.S7LegacyAPI
import R5Kernel.S8LegacyAPI
import R5Kernel.S9DirectAdapter

/- Source module: R5DirectAllUpper. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_R5DirectAllUpper


namespace Erdos1011

open SimpleGraph

/- The insertion layer contains an orientation adapter for the extremal edge,
   but importing that layer here would create a cycle through the target file.
   Keep the three elementary swap steps local to this target-safe dispatcher. -/
theorem direct_degreeSum_bound_swap
    {r n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (hD : ∀ H a b, HighExtremalEdgePairs r n (H, (a, b)) →
      degreeSumPair (H, (a, b)) ≤ degreeSumPair (G, (u, v))) :
    ∀ H a b, HighExtremalEdgePairs r n (H, (a, b)) →
      degreeSumPair (H, (a, b)) ≤ degreeSumPair (G, (v, u)) := by
  intro H a b hp
  have hh := hD H a b hp
  simpa [degreeSumPair, Nat.add_comm] using hh

theorem direct_noRepeated_sideA_swap
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (hnoB : ∀ x x', x ∈ edgeSideBSet G u v →
      x' ∈ edgeSideBSet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x') :
    ∀ y y', y ∈ edgeSideASet G v u →
      y' ∈ edgeSideASet G v u → y ≠ y' →
      (residualType G v u y).Nonempty →
      residualType G v u y ≠ residualType G v u y' := by
  intro y y' hy hy' hyy' hTy hEq
  apply hnoB y y'
  · simpa [edgeSideASet, edgeSideBSet] using hy
  · simpa [edgeSideASet, edgeSideBSet] using hy'
  · exact hyy'
  · simpa [residualType_swap] using hTy
  · simpa [residualType_swap] using hEq

theorem direct_noRepeated_sideB_swap
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (hnoA : ∀ x x', x ∈ edgeSideASet G u v →
      x' ∈ edgeSideASet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x') :
    ∀ y y', y ∈ edgeSideBSet G v u →
      y' ∈ edgeSideBSet G v u → y ≠ y' →
      (residualType G v u y).Nonempty →
      residualType G v u y ≠ residualType G v u y' := by
  intro y y' hy hy' hyy' hTy hEq
  apply hnoA y y'
  · simpa [edgeSideASet, edgeSideBSet] using hy
  · simpa [edgeSideASet, edgeSideBSet] using hy'
  · exact hyy'
  · simpa [residualType_swap] using hTy
  · simpa [residualType_swap] using hEq

theorem exists_twinized_extremal_edge_five_oriented_direct
    {n : ℕ}
    (h : ∃ G : SimpleGraph (Fin n),
      HighChromaticTriangleFree 5 n G) :
    ∃ G u v, HighExtremal 5 n G ∧ G.Adj u v ∧
      (∀ H a b, HighExtremalEdgePairs 5 n (H, (a, b)) →
        degreeSumPair (H, (a, b)) ≤ degreeSumPair (G, (u, v))) ∧
      (∀ x x', x ∈ edgeSideASet G u v →
        x' ∈ edgeSideASet G u v → x ≠ x' →
        (residualType G u v x).Nonempty →
        residualType G u v x ≠ residualType G u v x') ∧
      (∀ y y', y ∈ edgeSideBSet G u v →
        y' ∈ edgeSideBSet G u v → y ≠ y' →
        (residualType G u v y).Nonempty →
        residualType G u v y ≠ residualType G u v y') ∧
      supportWeight (supportFamilyA G u v) ≤
        supportWeight (supportFamilyB G u v) := by
  obtain ⟨G, u, v, hG, huv, hD, _hmin, hnoA, hnoB, _hnot2⟩ :=
    exists_twinized_extremal_edge_five h
  by_cases horder : supportWeight (supportFamilyA G u v) ≤
      supportWeight (supportFamilyB G u v)
  · exact ⟨G, u, v, hG, huv, hD, hnoA, hnoB, horder⟩
  · have hD' := direct_degreeSum_bound_swap hD
    have hnoA' := direct_noRepeated_sideA_swap hnoB
    have hnoB' := direct_noRepeated_sideB_swap hnoA
    have horder' : supportWeight (supportFamilyA G v u) ≤
        supportWeight (supportFamilyB G v u) := by
      have hle : supportWeight (supportFamilyB G u v) ≤
          supportWeight (supportFamilyA G u v) :=
        Nat.le_of_lt (Nat.lt_of_not_ge horder)
      simpa only [supportFamilyA_swap_eq_supportFamilyB G u v,
        supportFamilyB_swap_eq_supportFamilyA G u v] using hle
    exact ⟨G, v, u, hG, huv.symm, hD', hnoA', hnoB', horder'⟩

set_option maxHeartbeats 5000000 in
theorem verified_r5_upper_from_s9_odd_cycle_embedding_exact_direct
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
    (hS9 : (residualSet G u v).ncard = 9) :
    edgeCount G ≤ fiveCandidate n := by
  exact kernel_verified_r5_upper_from_s9_odd_cycle_embedding_exact_direct
    hn hH huv hD hnoA hnoB hS9

/- Every residual size 6,...,11 now has a kernel-checked endpoint. The S7
   endpoint retains its original name but no longer uses the twenty-profile
   classification; its proof also extracts an odd cycle directly. -/
set_option maxHeartbeats 8000000 in
theorem verified_r5_upper_ge80_of_s7_shape_auto_and_direct_odd_cycles :
    ∀ n : ℕ, 80 ≤ n → ∀ G : SimpleGraph (Fin n),
      HighChromaticTriangleFree 5 n G → edgeCount G ≤ fiveCandidate n := by
  intro n hn G hG
  classical
  obtain ⟨G₀, u, v, hG₀, huv, hD, hnoA, hnoB, horder⟩ :=
    exists_twinized_extremal_edge_five_oriented_direct (n := n) ⟨G, hG⟩
  have hmax : IsEdgeMaximalTriangleFree G₀ :=
    edge_maximal_of_edgeCount_max hG₀.1 hG₀.2
  have hsizes := verified_r5_residual_size_between_six_eleven hG₀ huv hD hn
  by_cases hS7 : (residualSet G₀ u v).ncard = 7
  · have hupper := verified_r5_upper_from_s7_shape_auto_direct hn hG₀ huv hD
      hnoA hnoB horder hS7
    exact (hG₀.2 G hG).trans hupper
  have hcases :
      (residualSet G₀ u v).ncard = 6 ∨
      (residualSet G₀ u v).ncard = 8 ∨
      (residualSet G₀ u v).ncard = 9 ∨
      (residualSet G₀ u v).ncard = 10 ∨
      (residualSet G₀ u v).ncard = 11 := by omega
  rcases hcases with h6 | h8 | h9 | h10 | h11
  · have hupper := verified_r5_upper_from_residual_s6_cardinality_of_extremal_choice
      hG₀ huv hnoA hnoB hn h6
    exact (hG₀.2 G hG).trans hupper
  · have hupper := verified_r5_upper_from_s8_odd_cycle_embedding_exact
      hn hG₀ huv hD hnoA hnoB h8 horder
    exact (hG₀.2 G hG).trans hupper
  · have hupper := verified_r5_upper_from_s9_odd_cycle_embedding_exact_direct
      hn hG₀ huv hD hnoA hnoB h9
    exact (hG₀.2 G hG).trans hupper
  · have hupper := verified_r5_upper_from_s10_odd_cycle_embedding_exact
      hn hG₀ huv hD hnoA hnoB h10
    exact (hG₀.2 G hG).trans hupper
  · have hupper := verified_r5_upper_from_s11_odd_cycle_embedding_exact
      hn hG₀ huv hD hnoA hnoB h11
    exact (hG₀.2 G hG).trans hupper

run_cmd R5Kernel.checkStandardAxioms ``verified_r5_upper_ge80_of_s7_shape_auto_and_direct_odd_cycles

end Erdos1011

end Web_R5DirectAllUpper
