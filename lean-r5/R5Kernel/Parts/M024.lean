import R5Kernel.Parts.M023

/- Source module: Erdos1011.R5Coarse201. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_R5Coarse201


namespace Erdos1011

/-! Sharp small-residual arithmetic constants from the paper's simplified
tables.  These are valid from `n = 80` onward (the endpoint equalities at
`n = 80` are intentional). -/

theorem small_gap_s7_80 {n : ℕ} (hn : 80 ≤ n) :
    (n - 7)^2 / 4 + 42 ≤ fiveCandidate n := by
  by_cases h80 : n = 80
  · subst n
    norm_num [fiveCandidate]
  by_cases h81 : n = 81
  · subst n
    norm_num [fiveCandidate]
  have hn82 : 82 ≤ n := by omega
  have hn80 : 80 ≤ n := by omega
  rw [fiveCandidate_recenter hn80]
  have hshift : n - 6 = (n - 7) + 1 := by omega
  have hsq : (n - 6)^2 = (n - 7)^2 + (2 * (n - 7) + 1) := by
    rw [hshift]
    ring
  have hdiv :
      (n - 7)^2 / 4 + (2 * (n - 7) + 1) / 4 ≤
        ((n - 7)^2 + (2 * (n - 7) + 1)) / 4 :=
    Nat.div_add_div_le_add_div
  rw [← hsq] at hdiv
  have hD : 37 ≤ (2 * (n - 7) + 1) / 4 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2
    omega
  omega

theorem small_gap_s8_80 {n : ℕ} (hn : 80 ≤ n) :
    (n - 8)^2 / 4 + 77 ≤ fiveCandidate n := by
  have hn80 : 80 ≤ n := by omega
  rw [fiveCandidate_recenter hn80]
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

theorem small_gap_s9_80 {n : ℕ} (hn : 80 ≤ n) :
    (n - 9)^2 / 4 + 114 ≤ fiveCandidate n := by
  by_cases h80 : n = 80
  · subst n
    norm_num [fiveCandidate]
  have hn81 : 81 ≤ n := by omega
  have hn80 : 80 ≤ n := by omega
  rw [fiveCandidate_recenter hn80]
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

theorem small_gap_s10_80 {n : ℕ} (hn : 80 ≤ n) :
    (n - 10)^2 / 4 + 149 ≤ fiveCandidate n := by
  have hn80 : 80 ≤ n := by omega
  rw [fiveCandidate_recenter hn80]
  have hshift : n - 6 = (n - 10) + 4 := by omega
  have hsq : (n - 6)^2 = (n - 10)^2 + (8 * (n - 10) + 16) := by
    rw [hshift]
    ring
  have hdiv :
      (n - 10)^2 / 4 + (8 * (n - 10) + 16) / 4 ≤
        ((n - 10)^2 + (8 * (n - 10) + 16)) / 4 :=
    Nat.div_add_div_le_add_div
  rw [← hsq] at hdiv
  have hD : 144 ≤ (8 * (n - 10) + 16) / 4 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2
    omega
  omega

theorem small_gap_s11_80 {n : ℕ} (hn : 80 ≤ n) :
    (n - 11)^2 / 4 + 184 ≤ fiveCandidate n := by
  by_cases h80 : n = 80
  · subst n
    norm_num [fiveCandidate]
  by_cases h81 : n = 81
  · subst n
    norm_num [fiveCandidate]
  by_cases h82 : n = 82
  · subst n
    norm_num [fiveCandidate]
  have hn83 : 83 ≤ n := by omega
  have hn80 : 80 ≤ n := by omega
  rw [fiveCandidate_recenter hn80]
  have hshift : n - 6 = (n - 11) + 5 := by omega
  have hsq : (n - 6)^2 = (n - 11)^2 + (10 * (n - 11) + 25) := by
    rw [hshift]
    ring
  have hdiv :
      (n - 11)^2 / 4 + (10 * (n - 11) + 25) / 4 ≤
        ((n - 11)^2 + (10 * (n - 11) + 25)) / 4 :=
    Nat.div_add_div_le_add_div
  rw [← hsq] at hdiv
  have hD : 179 ≤ (10 * (n - 11) + 25) / 4 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2
    omega
  omega

theorem residual_decomposition_bound_s7_small
    {n a b e q m : ℕ} (hn : 80 ≤ n)
    (hsum : a + b + 7 = n) (heq : e + q ≤ 42)
    (hdecomp : m ≤ a * b + e + q) : m ≤ fiveCandidate n := by
  have hab : a * b ≤ (a + b)^2 / 4 := nat_mul_le_add_sq_div_four a b
  have hshift : a + b = n - 7 := by omega
  have hab' : a * b ≤ (n - 7)^2 / 4 := by
    calc a * b ≤ (a + b)^2 / 4 := hab
      _ = (n - 7)^2 / 4 := by rw [hshift]
  have hbound : m ≤ (n - 7)^2 / 4 + 42 := by omega
  exact hbound.trans (small_gap_s7_80 hn)

/- The coarse S₇ shape bound `q≤40`, together with Mantel's `e≤12`,
   already closes the candidate once `n≥100`.  Keeping this arithmetic
   endpoint separate lets the structural shape theorem discharge the whole
   long part without selecting one of the finite profile rows. -/

theorem residual_decomposition_bound_s8_small
    {n a b e q m : ℕ} (hn : 80 ≤ n)
    (hsum : a + b + 8 = n) (heq : e + q ≤ 77)
    (hdecomp : m ≤ a * b + e + q) : m ≤ fiveCandidate n := by
  have hab : a * b ≤ (a + b)^2 / 4 := nat_mul_le_add_sq_div_four a b
  have hshift : a + b = n - 8 := by omega
  have hab' : a * b ≤ (n - 8)^2 / 4 := by
    calc a * b ≤ (a + b)^2 / 4 := hab
      _ = (n - 8)^2 / 4 := by rw [hshift]
  have hbound : m ≤ (n - 8)^2 / 4 + 77 := by omega
  exact hbound.trans (small_gap_s8_80 hn)

theorem residual_decomposition_bound_s9_small
    {n a b e q m : ℕ} (hn : 80 ≤ n)
    (hsum : a + b + 9 = n) (heq : e + q ≤ 114)
    (hdecomp : m ≤ a * b + e + q) : m ≤ fiveCandidate n := by
  have hab : a * b ≤ (a + b)^2 / 4 := nat_mul_le_add_sq_div_four a b
  have hshift : a + b = n - 9 := by omega
  have hab' : a * b ≤ (n - 9)^2 / 4 := by
    calc a * b ≤ (a + b)^2 / 4 := hab
      _ = (n - 9)^2 / 4 := by rw [hshift]
  have hbound : m ≤ (n - 9)^2 / 4 + 114 := by omega
  exact hbound.trans (small_gap_s9_80 hn)

theorem residual_decomposition_bound_s10_small
    {n a b e q m : ℕ} (hn : 80 ≤ n)
    (hsum : a + b + 10 = n) (heq : e + q ≤ 149)
    (hdecomp : m ≤ a * b + e + q) : m ≤ fiveCandidate n := by
  have hab : a * b ≤ (a + b)^2 / 4 := nat_mul_le_add_sq_div_four a b
  have hshift : a + b = n - 10 := by omega
  have hab' : a * b ≤ (n - 10)^2 / 4 := by
    calc a * b ≤ (a + b)^2 / 4 := hab
      _ = (n - 10)^2 / 4 := by rw [hshift]
  have hbound : m ≤ (n - 10)^2 / 4 + 149 := by omega
  exact hbound.trans (small_gap_s10_80 hn)

theorem residual_decomposition_bound_s11_small
    {n a b e q m : ℕ} (hn : 80 ≤ n)
    (hsum : a + b + 11 = n) (heq : e + q ≤ 184)
    (hdecomp : m ≤ a * b + e + q) : m ≤ fiveCandidate n := by
  have hab : a * b ≤ (a + b)^2 / 4 := nat_mul_le_add_sq_div_four a b
  have hshift : a + b = n - 11 := by omega
  have hab' : a * b ≤ (n - 11)^2 / 4 := by
    calc a * b ≤ (a + b)^2 / 4 := hab
      _ = (n - 11)^2 / 4 := by rw [hshift]
  have hbound : m ≤ (n - 11)^2 / 4 + 184 := by omega
  exact hbound.trans (small_gap_s11_80 hn)

theorem edgeCount_le_fiveCandidate_of_simplified_s7_s9
    {n m : ℕ} (hn : 80 ≤ n)
    (hcert : ∃ s a b e q : ℕ,
      a + b + s = n ∧
      m ≤ a * b + e + q ∧
      ((s = 7 ∧ e + q ≤ 42) ∨
       (s = 8 ∧ e + q ≤ 77) ∨
       (s = 9 ∧ e + q ≤ 114))) :
    m ≤ fiveCandidate n := by
  rcases hcert with ⟨s, a, b, e, q, hsum, hdecomp, hcase⟩
  rcases hcase with ⟨rfl, heq⟩ | ⟨rfl, heq⟩ | ⟨rfl, heq⟩
  · exact residual_decomposition_bound_s7_small hn hsum heq hdecomp
  · exact residual_decomposition_bound_s8_small hn hsum heq hdecomp
  · exact residual_decomposition_bound_s9_small hn hsum heq hdecomp

/-! Arithmetic endgame for the simplified paper tables.  The constants here
    are the coarse residual bounds from `paper-r5-small-core-simplification-20260909.md`:
    for `s=7,…,11`, the weighted surplus bounds are
    `40,77,152,290,456`, while Mantel gives residual edge bounds
    `12,16,20,25,30`.  This file does not assert the graph-to-table reduction. -/

end Erdos1011

end Web_Erdos1011_R5Coarse201
