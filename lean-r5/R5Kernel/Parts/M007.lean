import R5Kernel.Parts.M006

/- Source module: Erdos1011.CoarseArithmetic. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_CoarseArithmetic


namespace Erdos1011

/-! Arithmetic endgame for the coarse `s = 7,\ldots,11` residual bounds.
    The graph-theoretic input is intentionally separated: once a residual
    edge-plus-surplus bound is available, these lemmas compare it with the
    five-colour candidate for every `n ≥ 1248`.  No finite search or opaque
    certificate is used. -/

/- The elementary product estimate behind the `ab` term in the residual
   decomposition.  It is stated over naturals, with the division by four
   kept explicit so that the floor in the candidate is visible. -/
theorem nat_mul_le_add_sq_div_four (a b : ℕ) :
    a * b ≤ (a + b) ^ 2 / 4 := by
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2
  have hsq : 0 ≤ ((a : ℤ) - (b : ℤ)) ^ 2 := sq_nonneg _
  have hfour : (4 : ℤ) * (a : ℤ) * (b : ℤ) ≤ ((a : ℤ) + (b : ℤ)) ^ 2 := by
    nlinarith [hsq]
  have hfourNat : 4 * a * b ≤ (a + b) ^ 2 := by
    exact_mod_cast hfour
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hfourNat

theorem residual_decomposition_bound_s6
    {n a b e q m : ℕ}
    (hn : 80 ≤ n)
    (hsum : a + b + 6 = n)
    (he : e ≤ 5)
    (hq : q ≤ 0)
    (hdecomp : m ≤ a * b + e + q) :
    m ≤ fiveCandidate n := by
  have hq0 : q = 0 := by omega
  subst q
  have hab : a * b ≤ (a + b) ^ 2 / 4 := nat_mul_le_add_sq_div_four a b
  have hshift : a + b = n - 6 := by omega
  have hprod : a * b + e ≤ (n - 6) ^ 2 / 4 + 5 := by
    have hab' : a * b ≤ (n - 6) ^ 2 / 4 := by
      calc
        a * b ≤ (a + b) ^ 2 / 4 := hab
        _ = (n - 6) ^ 2 / 4 := by rw [hshift]
    omega
  rw [fiveCandidate_recenter hn]
  omega

/- A single dispatcher for the five residual sizes occurring after the
   degree-sum reduction.  The first component is the non-strict upper bound
   needed in the `s=6` case; the second records that every larger residual
   size is in fact strictly below the candidate. -/

/- Arithmetic endgame for the two nontrivial residual sizes in the r = 4
   argument.  The graph classification supplies `e(H)+F ≤ 11` for `s=4`
   and `≤ 30` for `s=5`; these lemmas compare those constants with the
   four-colour candidate. -/

/- Degree-average arithmetic for the r=4 candidate.  The floor loss is at
   most three after multiplying by four, which is enough to force the
   residual set down to at most five vertices once n is at least 32. -/

/- The three-point arithmetic bridge in its sharp form.  The graph-specific
   finite certificate supplies the combined estimate `e(H)+F ≤ 5`; keeping
   this as one hypothesis avoids losing the unit needed by the candidate. -/

/- Final arithmetic interface for a graph-level certificate: once the edge
   decomposition has been proved and its residual case has been supplied, the
   edge count follows immediately.  The certificate deliberately contains no
   hidden graph assumptions; those belong to the yet-to-be-formalized
   graph-to-support extraction. -/

end Erdos1011

end Web_Erdos1011_CoarseArithmetic
