import R5Kernel.Parts.M003

/- Source module: Erdos1011.TargetCore. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_TargetCore


/-!
# Shared target interfaces

This module contains only the target predicates and the lower-bound-to-
`IsGreatest` wrappers that are shared by the Formal-Conjectures-shaped target
and the independently checked completion modules.  Keeping these definitions
below `R5` and above the final wrappers avoids an import cycle: the target can
propositions.
-/

namespace Erdos1011

def fixedFiveCandidate : Prop := FixedFivePairCandidate

def fixedFiveLowerWitnessTarget : Prop :=
  ∀ n : ℕ, 80 ≤ n → ∃ G : SimpleGraph (Fin n),
    HighChromaticTriangleFree 5 n G ∧ edgeCount G = fiveCandidate n

theorem fixed_five_lower_witness : fixedFiveLowerWitnessTarget := by
  intro n hn
  obtain ⟨a, b, ha, hb, hcard, hE⟩ := five_blowup_parameters hn
  obtain ⟨G, hG, hGE⟩ := qBlowup_fin_witness ha hb hcard
  exact ⟨G, hG, by simpa [hE] using hGE⟩

end Erdos1011

end Web_Erdos1011_TargetCore
