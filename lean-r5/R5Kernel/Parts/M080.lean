import R5Kernel.Parts.M079

/- Source module: Erdos1011Target. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011Target


/-!
# Standalone target statements

These propositions mirror the shape expected by the Formal Conjectures
repository.  The `answer(...)` wrapper is intentionally not used here: this
file is a Mathlib-only target that can be checked on Lean4Web as well.
The finite external replay assets have now been recovered and rechecked; the
remaining `sorry` proofs mark the still-missing Lean-level ambient classifiers
and their connection to the target, not missing finite certificate files.
-/

namespace Erdos1011

/-!
The fixed-4 lower-bound construction is now explicit in `Erdos1011.R4`.
The remaining exact upper-bound theorem is kept as a target proposition until
the finite classification/stability proof is formalized; importing this file
does not turn that target into an axiom.
-/

/-! Revised staged target: the graph-specific work is a pointwise edge
inequality.  The existing wrapper below turns this into the exact M/f pair. -/

/- The explicit Grötzsch blow-up now supplies the lower-bound half of the
fixed-4 value formula without any certificate hypothesis.  The upper-bound
half remains the missing theorem below. -/

/-! Revised staged r=5 target.  Prove this upper inequality and a matching
witness separately; only then invoke the exact M/f wrapper. -/
def fixedFiveUpperBoundTarget : Prop :=
  ∀ n : ℕ, 80 ≤ n → ∀ G : SimpleGraph (Fin n),
    HighChromaticTriangleFree 5 n G → edgeCount G ≤ fiveCandidate n

theorem fixed_five_candidate_of_greatest
    (h : ∀ n : ℕ, 80 ≤ n → IsGreatest
      {k : ℕ | ∃ G : SimpleGraph (Fin n),
        HighChromaticTriangleFree 5 n G ∧ edgeCount G = k}
      (fiveCandidate n)) : fixedFiveCandidate := by
  unfold fixedFiveCandidate FixedFivePairCandidate
  intro n hn
  have hn' := f_eq_succ_and_M_eq_of_isGreatest (h n hn)
  have hmn : M 5 n = fiveCandidate n := hn'.2
  have hfn : f 5 n = fiveCandidate n + 1 := hn'.1
  refine ⟨hmn, ?_, ?_⟩
  · simpa [fiveThresholdCandidate] using hfn
  · simpa [ThresholdExtremalOffset, hmn, hfn]

/- This is the preferred final r=5 interface: it exposes the two actual proof
obligations instead of hiding them in an `IsGreatest` premise. -/
theorem fixed_five_candidate_of_upper_and_lower
    (hupper : fixedFiveUpperBoundTarget)
    (hlower : fixedFiveLowerWitnessTarget) :
    fixedFiveCandidate := by
  apply fixed_five_candidate_of_greatest
  intro n hn
  rcases hlower n hn with ⟨G₀, hG₀, hE₀⟩
  refine ⟨⟨G₀, hG₀, hE₀⟩, ?_⟩
  intro k hk
  rcases hk with ⟨G, hG, hE⟩
  rw [← hE]
  exact hupper n hn G hG

/-! The coarse-tail endpoint is already constructive.  Exposing it here keeps
the standalone target honest: the remaining `fixed_five_candidate` theorem
starts at 80, while this independently checked corollary covers the entire
tail `n ≥ 1248` without importing the certificate insertion layer. -/

/- The full upper target can therefore be reduced to a bounded structural
   search.  This helper records precisely the only interval still needed once
   the constructive tail is available. -/

theorem fixed_five_candidate : fixedFiveCandidate := by
  apply fixed_five_candidate_of_upper_and_lower
  · intro n hn G hG
    exact verified_r5_upper_ge80_of_s7_shape_auto_and_direct_odd_cycles
      n hn G hG
  · exact fixed_five_lower_witness

/- The row-1115 blow-up already supplies the lower half of the Q-free target.
   Keep the universal upper half as a separate target proposition: this makes
   the remaining certificate obligation explicit without importing the
   insertion-layer bridge (which depends on this target file). -/

/-!
The report also gives a defect-stability statement involving the minimum
vertex deletion number `d₂(G)` and two twin classes.  We leave that as a
separate follow-up target until those two notions have fixed Lean definitions;
the file does not replace it with a vacuous proposition.
-/

run_cmd R5Kernel.checkStandardAxioms ``fixed_five_candidate

end Erdos1011

end Web_Erdos1011Target
