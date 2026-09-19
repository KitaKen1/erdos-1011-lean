import R5Kernel.Parts.M016

/- Source module: Erdos1011.R5S6. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_R5S6


namespace Erdos1011

/-!
  The `s = 6` branch of the r=5 argument has a concrete `C₅ ⊔ K₁`
  certificate in `S6Capacity`.  This file exposes the exact interface needed
  by the graph-level proof: a labelled embedding of the six residual vertices,
  equality of the transported support families, and the finite V/D-count
  hypothesis.  No structural hypothesis is hidden in this wrapper.
-/

theorem r5_s6_support_surplus_nonpositive_of_embedded_certificate
    {n : ℕ} (f : Fin 6 ↪ Fin n)
    {𝒜 ℬ : Finset (Finset (Fin 6))}
    {𝒜' ℬ' : Finset (Finset (Fin n))}
    (h𝒜eq : 𝒜' = mapSupportFamilyEmbedding f 𝒜)
    (hℬeq : ℬ' = mapSupportFamilyEmbedding f ℬ)
    (h𝒜sub : 𝒜 ⊆ s6Supports) (hℬsub : ℬ ⊆ s6Supports)
    (h𝒜T : s6TFamily ⊆ 𝒜) (hℬT : s6TFamily ⊆ ℬ)
    (hcount : 5 ≤
      (∑ I ∈ 𝒜 \ s6TFamily, if I ∈ s6VDFamily then 1 else 0) +
      (∑ J ∈ ℬ \ s6TFamily, if J ∈ s6VDFamily then 1 else 0)) :
    supportSurplus 𝒜' ℬ' ≤ 0 := by
  exact s6_support_surplus_nonpositive_of_embedded_certificate
    h𝒜eq hℬeq h𝒜sub hℬsub h𝒜T hℬT hcount

end Erdos1011

end Web_Erdos1011_R5S6
