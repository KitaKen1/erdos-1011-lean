import R5Kernel.Parts.M015

/- Source module: Erdos1011.S6Transport. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_S6Transport


namespace Erdos1011

/- Transport the concrete `C₅ ⊔ K₁` capacity certificate through an arbitrary
   relabelling of the six residual vertices.  The only graph-specific input
   still needed by a later theorem is an equality identifying its support
   families with these mapped finite families. -/

theorem embedded_s6_support_surplus_nonpositive_of_vd_count
    {t : ℕ} (f : Fin 6 ↪ Fin t)
    {𝒜 ℬ : Finset (Finset (Fin 6))}
    (h𝒜sub : 𝒜 ⊆ s6Supports) (hℬsub : ℬ ⊆ s6Supports)
    (h𝒜T : s6TFamily ⊆ 𝒜) (hℬT : s6TFamily ⊆ ℬ)
    (hcount : 5 ≤
      (∑ I ∈ 𝒜 \ s6TFamily, if I ∈ s6VDFamily then 1 else 0) +
      (∑ J ∈ ℬ \ s6TFamily, if J ∈ s6VDFamily then 1 else 0)) :
    supportSurplus (mapSupportFamilyEmbedding f 𝒜)
        (mapSupportFamilyEmbedding f ℬ) ≤ 0 := by
  rw [supportSurplus_mapSupportFamilyEmbedding]
  exact s6_support_surplus_nonpositive_of_vd_count
    h𝒜sub hℬsub h𝒜T hℬT hcount

theorem s6_support_surplus_nonpositive_of_embedded_certificate
    {t : ℕ} {f : Fin 6 ↪ Fin t}
    {𝒜 ℬ : Finset (Finset (Fin 6))}
    {𝒜' ℬ' : Finset (Finset (Fin t))}
    (h𝒜eq : 𝒜' = mapSupportFamilyEmbedding f 𝒜)
    (hℬeq : ℬ' = mapSupportFamilyEmbedding f ℬ)
    (h𝒜sub : 𝒜 ⊆ s6Supports) (hℬsub : ℬ ⊆ s6Supports)
    (h𝒜T : s6TFamily ⊆ 𝒜) (hℬT : s6TFamily ⊆ ℬ)
    (hcount : 5 ≤
      (∑ I ∈ 𝒜 \ s6TFamily, if I ∈ s6VDFamily then 1 else 0) +
      (∑ J ∈ ℬ \ s6TFamily, if J ∈ s6VDFamily then 1 else 0)) :
    supportSurplus 𝒜' ℬ' ≤ 0 := by
  rw [h𝒜eq, hℬeq]
  exact embedded_s6_support_surplus_nonpositive_of_vd_count
    f h𝒜sub hℬsub h𝒜T hℬT hcount

end Erdos1011

end Web_Erdos1011_S6Transport
