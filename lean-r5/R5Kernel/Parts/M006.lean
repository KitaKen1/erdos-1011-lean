import R5Kernel.Parts.M005

/- Source module: Erdos1011.Capacity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_Capacity


/-!
# Finite support-family bookkeeping

This file is the first Lean target for the new paper proof.  It deliberately
separates the finite arithmetic certificate from the graph-theoretic reduction:
the latter still has to be formalized.  A support family is a finset of
nonempty independent subsets of a residual graph.  The definitions below make
the quantity `F = W_A + W_B - C` and the maximum-degree compatibility condition
explicit.
-/

namespace Erdos1011

open scoped BigOperators

variable {s : ℕ}

/-- The total support weight of a finite family. -/
def supportWeight (𝒜 : Finset (Finset (Fin s))) : ℕ :=
  ∑ I ∈ 𝒜, I.card

/-- Number of supports in `𝒜` intersecting a fixed support `J`. -/
def supportHits (𝒜 : Finset (Finset (Fin s))) (J : Finset (Fin s)) : ℕ :=
  ∑ I ∈ 𝒜, if Disjoint I J then 0 else 1

/-- Number of intersecting pairs between two support families. -/
def supportCross (𝒜 ℬ : Finset (Finset (Fin s))) : ℕ :=
  ∑ J ∈ ℬ, supportHits 𝒜 J

/-- The support contribution in the edge-count identity. -/
def supportSurplus (𝒜 ℬ : Finset (Finset (Fin s))) : ℕ :=
  supportWeight 𝒜 + supportWeight ℬ - supportCross 𝒜 ℬ

/-- The local degree-sum constraint on both sides of an extremal edge. -/
def DegreeCompatible (𝒜 ℬ : Finset (Finset (Fin s))) : Prop :=
  (∀ I ∈ 𝒜, I.card ≤ supportHits ℬ I) ∧
  (∀ J ∈ ℬ, J.card ≤ supportHits 𝒜 J)

theorem supportWeight_eq_sdiff_add
    {𝒜 𝒯 : Finset (Finset (Fin s))} (h𝒯 : 𝒯 ⊆ 𝒜) :
    supportWeight 𝒜 = supportWeight (𝒜 \ 𝒯) + supportWeight 𝒯 := by
  calc
    supportWeight 𝒜 = supportWeight (𝒜 \ 𝒯 ∪ 𝒯) := by
      rw [Finset.sdiff_union_of_subset h𝒯]
    _ = supportWeight (𝒜 \ 𝒯) + supportWeight 𝒯 := by
      unfold supportWeight
      rw [Finset.sum_union Finset.sdiff_disjoint]

theorem supportCross_ge_leftWeight
    {𝒜 ℬ : Finset (Finset (Fin s))}
    (h : ∀ J ∈ ℬ, J.card ≤ supportHits 𝒜 J) :
    supportWeight ℬ ≤ supportCross 𝒜 ℬ := by
  simp only [supportWeight, supportCross]
  exact Finset.sum_le_sum (fun J hJ => h J hJ)

theorem supportCross_symm
    {𝒜 ℬ : Finset (Finset (Fin s))} :
    supportCross 𝒜 ℬ = supportCross ℬ 𝒜 := by
  classical
  simp only [supportCross, supportHits, disjoint_comm]
  rw [Finset.sum_comm]
  simp [disjoint_comm]

theorem supportCross_ge_rightWeight
    {𝒜 ℬ : Finset (Finset (Fin s))}
    (h : ∀ I ∈ 𝒜, I.card ≤ supportHits ℬ I) :
    supportWeight 𝒜 ≤ supportCross 𝒜 ℬ := by
  rw [supportCross_symm]
  exact supportCross_ge_leftWeight h

theorem supportSurplus_le_leftWeight
    {𝒜 ℬ : Finset (Finset (Fin s))}
    (h : ∀ J ∈ ℬ, J.card ≤ supportHits 𝒜 J) :
    supportSurplus 𝒜 ℬ ≤ supportWeight 𝒜 := by
  have hcross := supportCross_ge_leftWeight h
  unfold supportSurplus
  omega

theorem supportSurplus_le_rightWeight
    {𝒜 ℬ : Finset (Finset (Fin s))}
    (h : ∀ I ∈ 𝒜, I.card ≤ supportHits ℬ I) :
    supportSurplus 𝒜 ℬ ≤ supportWeight ℬ := by
  have hcross := supportCross_ge_rightWeight h
  unfold supportSurplus
  omega

theorem supportSurplus_le_minWeight
    {𝒜 ℬ : Finset (Finset (Fin s))}
    (h : DegreeCompatible 𝒜 ℬ) :
    supportSurplus 𝒜 ℬ ≤ min (supportWeight 𝒜) (supportWeight ℬ) := by
  exact Nat.le_min.mpr ⟨supportSurplus_le_leftWeight h.2,
    supportSurplus_le_rightWeight h.1⟩

/-! The finite tables are recorded as ordinary natural-number data first.  A
later graph-reduction file will connect each `d` entry to the corresponding
capacity minimum.  This arithmetic layer is already kernel-checkable and
avoids making the final theorem depend on an opaque external certificate. -/

end Erdos1011

end Web_Erdos1011_Capacity
