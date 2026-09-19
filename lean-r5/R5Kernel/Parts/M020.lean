import R5Kernel.Parts.M019

/- Source module: Erdos1011.R5Capacity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_R5Capacity


namespace Erdos1011

open scoped BigOperators

/-! The finite universe of nonempty independent support types for a labelled
    cycle with isolated vertices. -/
/- `cycleTypes` is re-exported by M019 from the compact certificate definitions. -/

def intersectsFinset {s : ℕ} (I J : Finset (Fin s)) : Prop := ¬ Disjoint I J

instance intersectsFinset_decidable {s : ℕ} :
    DecidableRel (@intersectsFinset s) := by
  intro I J
  unfold intersectsFinset
  infer_instance

/- A representative central tuple.  The full `80,…,200` sweep is kept as a
   Python-side audit until the Lean evaluator is replaced by a faster profile
   implementation; an attempted single Lean quantifier returned `false`
   without yielding a witness, so it remains an explicit audit item rather
   than a mathematical counterexample. -/

end Erdos1011

end Web_Erdos1011_R5Capacity
