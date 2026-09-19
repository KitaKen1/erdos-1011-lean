import R5Kernel.Parts.M011

/- Source module: Erdos1011.DegreeAverage. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_DegreeAverage


namespace Erdos1011

open SimpleGraph
open scoped BigOperators

theorem vertexDegree_sum_eq_twice_edgeCount
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    (∑ v, vertexDegree G v) = 2 * edgeCount G := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  have h := G.sum_degrees_eq_twice_card_edges
  have hv : (∑ v, vertexDegree G v) = ∑ v, G.degree v := by
    apply Finset.sum_congr rfl
    intro v hv
    exact vertexDegree_eq_degree G v
  rw [hv]
  rw [edgeCount_eq_edgeFinset_card_r4 G]
  exact h

theorem sum_neighbor_values_eq_sum_sq
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (d : Fin n → ℕ)
    (hd : ∀ v, d v = vertexDegree G v) :
    (∑ x, ∑ y ∈ (Finset.univ : Finset (Fin n)).filter (G.Adj x), d y) =
      ∑ v, d v ^ 2 := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  have hcount : ((Finset.univ.filter (G.Adj · y)).card : ℕ) = d y := by
    rw [hd y]
    unfold vertexDegree
    let hs : (G.neighborSet y).Finite := Set.toFinite _
    rw [Set.ncard_eq_toFinset_card (G.neighborSet y) hs]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hs.mem_toFinset]
    constructor <;> intro h
    · exact h.symm
    · exact h.symm
  have hinner : (∑ x, if G.Adj x y then d y else 0) = d y ^ 2 := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, hcount]
    simp [pow_two, Nat.mul_comm]
  exact hinner

theorem sum_sq_le_mul_of_adj_degree_sum_le
    {n m D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (d : Fin n → ℕ) (hd : ∀ v, d v = vertexDegree G v)
    (hm : ∑ v, d v = 2 * m)
    (hbound : ∀ ⦃x y : Fin n⦄, G.Adj x y → d x + d y ≤ D) :
    (∑ v, d v ^ 2) ≤ m * D := by
  classical
  have hcard (x : Fin n) :
      (Finset.univ.filter (G.Adj x)).card = d x := by
    rw [hd x]
    unfold vertexDegree
    let hs : (G.neighborSet x).Finite := Set.toFinite _
    rw [Set.ncard_eq_toFinset_card (G.neighborSet x) hs]
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hs.mem_toFinset]
    exact Iff.rfl
  have hlocal (x : Fin n) :
      (∑ y ∈ (Finset.univ.filter (G.Adj x)), (d x + d y)) ≤ d x * D := by
    have hi :
        (∑ y ∈ (Finset.univ.filter (G.Adj x)), (d x + d y)) ≤
          ∑ y ∈ (Finset.univ.filter (G.Adj x)), D := by
      apply Finset.sum_le_sum
      intro y hy
      exact hbound (Finset.mem_filter.mp hy).2
    rw [Finset.sum_const, hcard x] at hi
    simpa [Nat.mul_comm] using hi
  have hsumI := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (fun x hx => hlocal x)
  have hfirst :
      (∑ x, ∑ y ∈ (Finset.univ.filter (G.Adj x)), d x) = ∑ x, d x ^ 2 := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_const, hcard x]
    simp [pow_two, Nat.mul_comm]
  simp_rw [Finset.sum_add_distrib] at hsumI
  rw [hfirst, sum_neighbor_values_eq_sum_sq G d hd] at hsumI
  rw [← Finset.sum_mul, hm] at hsumI
  have hsumI' : 2 * (∑ v, d v ^ 2) ≤ 2 * (m * D) := by
    simpa [two_mul, Nat.mul_assoc, add_mul] using hsumI
  exact Nat.le_of_mul_le_mul_left hsumI' (by omega)

/-! A purely arithmetic Cauchy--Schwarz bridge.  The graph-theoretic part of
    the degree-sum argument only has to provide the two displayed hypotheses:
    the handshake identity and an upper bound on the sum of squared degrees.
    Keeping this lemma graph-free makes the later incidence bookkeeping much
    easier to audit. -/
theorem four_mul_m_le_n_mul_D_of_sum_sq_le
    {n m D : ℕ} (d : Fin n → ℕ)
    (hsum : ∑ v, d v = 2 * m)
    (hsq : ∑ v, d v ^ 2 ≤ m * D) :
    4 * m ≤ n * D := by
  classical
  let qd : Fin n → ℚ := fun v => d v
  have hc := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (Fin n))) (f := qd)
  have hcast_sum : (∑ v, qd v) = (2 * m : ℚ) := by
    dsimp [qd]
    rw [← Nat.cast_sum, hsum]
    norm_num
  have hcast_sq : (∑ v, (qd v) ^ 2) ≤ (m * D : ℚ) := by
    have hsq' : ((∑ v, d v ^ 2 : ℕ) : ℚ) ≤ (m * D : ℚ) := by
      exact_mod_cast hsq
    simpa [qd, Nat.cast_sum, Nat.cast_pow] using hsq'
  have hc' : (2 * m : ℚ) ^ 2 ≤ (n : ℚ) * (m * D : ℚ) := by
    rw [hcast_sum] at hc
    have hcard : ((Finset.univ : Finset (Fin n)).card : ℚ) = n := by
      simp
    rw [hcard] at hc
    exact hc.trans (mul_le_mul_of_nonneg_left hcast_sq (by positivity))
  by_cases hm : m = 0
  · simp [hm]
  · have hmpos : (0 : ℚ) < m := by exact_mod_cast (Nat.zero_lt_of_ne_zero hm)
    have hnat : (4 * m : ℚ) ≤ (n * D : ℚ) := by
      nlinarith [hc']
    exact_mod_cast hnat

theorem high_extremal_adj_degree_sum_le
    {r n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : HighExtremal r n G)
    {u v : Fin n}
    (hD : ∀ H a b, HighExtremalEdgePairs r n (H, (a, b)) →
      degreeSumPair (H, (a, b)) ≤ degreeSumPair (G, (u, v))) :
    ∀ ⦃x y : Fin n⦄, G.Adj x y →
      vertexDegree G x + vertexDegree G y ≤ degreeSumPair (G, (u, v)) := by
  intro x y hxy
  have hp : HighExtremalEdgePairs r n (G, (x, y)) := ⟨hG, hxy⟩
  have hle := hD G x y hp
  simpa [degreeSumPair] using hle

theorem four_mul_edgeCount_le_of_high_extremal_edge
    {r n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : HighExtremal r n G) {u v : Fin n}
    (hD : ∀ H a b, HighExtremalEdgePairs r n (H, (a, b)) →
      degreeSumPair (H, (a, b)) ≤ degreeSumPair (G, (u, v))) :
    4 * edgeCount G ≤ n * degreeSumPair (G, (u, v)) := by
  let d : Fin n → ℕ := fun x => vertexDegree G x
  have hd : ∀ x, d x = vertexDegree G x := by intro x; rfl
  have hsum : ∑ x, d x = 2 * edgeCount G := by
    simpa [d] using vertexDegree_sum_eq_twice_edgeCount G
  have hbound : ∀ ⦃x y : Fin n⦄, G.Adj x y →
      d x + d y ≤ degreeSumPair (G, (u, v)) := by
    intro x y hxy
    exact high_extremal_adj_degree_sum_le hG hD hxy
  have hsq : (∑ x, d x ^ 2) ≤
      edgeCount G * degreeSumPair (G, (u, v)) :=
    sum_sq_le_mul_of_adj_degree_sum_le G d hd hsum hbound
  exact four_mul_m_le_n_mul_D_of_sum_sq_le d hsum hsq

theorem high_extremal_residual_ncard_le_eleven_of_degree_sum_max
    {n : ℕ} (hn : 80 ≤ n) {G : SimpleGraph (Fin n)}
    (hG : HighExtremal 5 n G) {u v : Fin n} (huv : G.Adj u v)
    (hD : ∀ H a b, HighExtremalEdgePairs 5 n (H, (a, b)) →
      degreeSumPair (H, (a, b)) ≤ degreeSumPair (G, (u, v))) :
    (residualSet G u v).ncard ≤ 11 := by
  classical
  apply high_extremal_residual_ncard_le_eleven hn hG huv
  exact four_mul_edgeCount_le_of_high_extremal_edge hG hD

end Erdos1011

end Web_Erdos1011_DegreeAverage
