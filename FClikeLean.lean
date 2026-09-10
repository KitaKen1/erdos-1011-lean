/-
Unofficial Formal Conjectures-style draft for Erdős Problem #1011.
This file is a prospective example, not an upstream Formal Conjectures file.
-/

import FormalConjecturesUtil

/-!
# Erdős Problem 1011: determine the threshold function

The answer to this problem is a function, not a truth value. The general
answer has type `ℕ → ℕ → ℕ`, and a fixed-`r` answer has type `ℕ → ℕ`.
No proposed formula is included in the problem's definitions or hypotheses.

To give a solution, replace the function-valued `answer(sorry)` with an
explicit function and prove that its values are the least forcing thresholds.
The separate `by sorry` is the proof placeholder. The answer may itself be
written as `answer(by exact fun n => ...)`.

As with other FC "determine" problems, returning the semantic `sInf`
definition itself does not count as determining an explicit answer.

References:
- https://www.erdosproblems.com/1011
- https://github.com/google-deepmind/formal-conjectures
- https://arxiv.org/abs/2404.07486
-/

open scoped ENat

namespace Erdos1011

/-- A triangle-free `n`-vertex graph with chromatic number at least `r`. -/
def HighChromaticTriangleFree (r n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  G.CliqueFree 3 ∧ (r : ℕ∞) ≤ G.chromaticNumber

/-- The finite edge count of a graph. -/
noncomputable def edgeCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  exact G.edgeFinset.card

/- Maximum edge count in the high-chromatic triangle-free class. -/
noncomputable def M (r n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n),
    HighChromaticTriangleFree r n G ∧ edgeCount G = m}

/-- `m` is a triangle-forcing threshold for `(r,n)`. -/
def IsThreshold (r n m : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), m ≤ edgeCount G →
    (r : ℕ∞) ≤ G.chromaticNumber → ¬ G.CliqueFree 3

/-- Semantic notation for the unknown threshold, not an explicit answer. -/
noncomputable def f (r n : ℕ) : ℕ :=
  sInf {m : ℕ | IsThreshold r n m}

/-- The proposed value forces a triangle, and every smaller value fails. -/
def IsExactThresholdValue (r n m : ℕ) : Prop :=
  IsThreshold r n m ∧ ∀ m' < m, ¬ IsThreshold r n m'

/- The offset is stated explicitly because the extremal edge count `M` and
   the forcing threshold `f` are different quantities.  It is asserted only
   on ranges where the high-chromatic class is nonempty. -/
def ThresholdExtremalOffset (r n : ℕ) : Prop :=
  f r n = M r n + 1

/-- Specification of an answer function for one fixed chromatic parameter.
This includes every natural-number order, including the empty graph. -/
def DeterminesThresholdsFor (r : ℕ) (F : ℕ → ℕ) : Prop :=
  ∀ n, IsExactThresholdValue r n (F n)

/-- Specification of the answer function `F r n` to the original problem. -/
def DeterminesThresholds (F : ℕ → ℕ → ℕ) : Prop :=
  ∀ r, DeterminesThresholdsFor r (F r)

/-- Determine the entire triangle-forcing threshold function `F r n`. -/
@[category research open, AMS 5]
theorem erdos_1011.formal_target :
    DeterminesThresholds (answer(sorry) : ℕ → ℕ → ℕ) := by
  sorry

/- The five variants ask the same question, with only `r` specialized.
All five quantify over every `n`; no eventual cutoff is imposed on `r5`.
The `solved` category records the mathematical status, not completion of the
proof placeholders in this file or an audit of the sibling implementation. -/

/-- Determine the threshold function at `r = 1`, for every `n`. -/
@[category research solved, AMS 5]
theorem erdos_1011.variants.r1 :
    DeterminesThresholdsFor 1 (answer(sorry) : ℕ → ℕ) := by
  sorry

/-- Determine the threshold function at `r = 2`, for every `n`. -/
@[category research solved, AMS 5]
theorem erdos_1011.variants.r2 :
    DeterminesThresholdsFor 2 (answer(sorry) : ℕ → ℕ) := by
  sorry

/-- Determine the threshold function at `r = 3`, for every `n`. -/
@[category research solved, AMS 5]
theorem erdos_1011.variants.r3 :
    DeterminesThresholdsFor 3 (answer(sorry) : ℕ → ℕ) := by
  sorry

/-- Determine the threshold function at `r = 4`, for every `n`.
The explicit answer belongs in `answer(...)`, not in the specification. -/
@[category research solved, AMS 5]
theorem erdos_1011.variants.r4 :
    DeterminesThresholdsFor 4 (answer(sorry) : ℕ → ℕ) := by
  sorry

/-- Determine the threshold function at `r = 5`, for every `n`.
An eventual formula alone does not solve this all-order variant. -/
@[category research open, AMS 5]
theorem erdos_1011.variants.r5 :
    DeterminesThresholdsFor 5 (answer(sorry) : ℕ → ℕ) := by
  sorry

end Erdos1011
