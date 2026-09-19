import R5Kernel.Parts.M018
import R5Kernel.Probes.S11C5CanonicalDefinitions

/- Source module: Erdos1011.CycleCapacity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_CycleCapacity


namespace Erdos1011

open scoped BigOperators

/-! Kernel-checked independent-set weight data for a cycle with isolated
    vertices.  These are the small residual universes used in the coarse
    `s = 7,\ldots,11` argument. -/

/- The cycle definitions are shared with the compact certificate modules.
   Importing their single owner avoids duplicate declarations at integration. -/

end Erdos1011

end Web_Erdos1011_CycleCapacity
