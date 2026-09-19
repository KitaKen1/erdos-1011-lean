import Lean.Elab.Frontend
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.FiveWheelLike
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

def erdos1011_r5_cachedLookup {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) : α :=
  (Array.ofFn f)[i.1]'(by simpa only [Array.size_ofFn] using i.2)

theorem erdos1011_r5_cachedLookup_eq {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) :
    erdos1011_r5_cachedLookup f i = f i := by
  simp [erdos1011_r5_cachedLookup]

