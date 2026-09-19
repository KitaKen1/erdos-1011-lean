import R5Kernel.Parts.M014
import R5Kernel.Audit

/- Source module: Erdos1011.S6Capacity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_S6Capacity


namespace Erdos1011

/-! Finite support data for the `C₅` plus one isolated vertex residual.  The
    twenty-one nonempty independent sets are written explicitly.  Keeping
    this table separate from the graph reduction makes the subsequent
    capacity inequality a small, replayable finite lemma. -/

abbrev V6 := Fin 6

def s6c5Adj (x y : V6) : Prop :=
  x.val < 5 ∧ y.val < 5 ∧
    (((x.val + 1) % 5 = y.val) ∨ ((y.val + 1) % 5 = x.val))

instance s6c5Adj_decidable : DecidableRel s6c5Adj := by
  intro x y
  unfold s6c5Adj
  infer_instance

def s6c5Independent (I : Finset V6) : Prop :=
  ∀ ⦃x⦄, x ∈ I → ∀ ⦃y⦄, y ∈ I → x ≠ y → ¬ s6c5Adj x y

instance s6c5Independent_decidable (I : Finset V6) :
    Decidable (s6c5Independent I) := by
  unfold s6c5Independent
  infer_instance

private def v0 : Finset V6 := {0}
private def v1 : Finset V6 := {1}
private def v2 : Finset V6 := {2}
private def v3 : Finset V6 := {3}
private def v4 : Finset V6 := {4}
private def d0 : Finset V6 := {4, 1}
private def d1 : Finset V6 := {0, 2}
private def d2 : Finset V6 := {1, 3}
private def d3 : Finset V6 := {2, 4}
private def d4 : Finset V6 := {3, 0}
private def z6 : Finset V6 := {5}
private def u0 : Finset V6 := {5, 0}
private def u1 : Finset V6 := {5, 1}
private def u2 : Finset V6 := {5, 2}
private def u3 : Finset V6 := {5, 3}
private def u4 : Finset V6 := {5, 4}
private def t0 : Finset V6 := {5, 4, 1}
private def t1 : Finset V6 := {5, 0, 2}
private def t2 : Finset V6 := {5, 1, 3}
private def t3 : Finset V6 := {5, 2, 4}
private def t4 : Finset V6 := {5, 3, 0}

def s6VDFamily : Finset (Finset V6) :=
  {v0, v1, v2, v3, v4, d0, d1, d2, d3, d4}

def s6UFamily : Finset (Finset V6) := {u0, u1, u2, u3, u4}

def s6ZFamily : Finset (Finset V6) := {z6}

def s6TFamily : Finset (Finset V6) := {t0, t1, t2, t3, t4}

def s6Supports : Finset (Finset V6) :=
  {v0, v1, v2, v3, v4, d0, d1, d2, d3, d4, z6,
   u0, u1, u2, u3, u4, t0, t1, t2, t3, t4}

def s6TIntersectCount (I : Finset V6) : ℕ :=
  ∑ T ∈ s6TFamily, if Disjoint I T then 0 else 1

theorem s6_nonempty_independent_classification
    {I : Finset V6} (hI : I.Nonempty) (hInd : s6c5Independent I) :
    I ∈ s6Supports := by
  decide +kernel +revert

theorem s6_support_partition
    {I : Finset V6} (hI : I ∈ s6Supports) :
    I ∈ s6VDFamily ∨ I ∈ s6UFamily ∨ I ∈ s6ZFamily ∨ I ∈ s6TFamily := by
  decide +kernel +revert

theorem s6_support_intersection_penalty
    {I : Finset V6} (hI : I ∈ s6Supports) :
    (I ∈ s6VDFamily → I.card + 1 ≤ s6TIntersectCount I) ∧
    (I ∈ s6UFamily → I.card + 3 ≤ s6TIntersectCount I) ∧
    (I ∈ s6ZFamily → I.card + 4 ≤ s6TIntersectCount I) := by
  decide +kernel +revert

theorem s6_mandatory_cross_count :
    (∑ T ∈ (s6TFamily : Finset (Finset V6)),
      ∑ U ∈ (s6TFamily : Finset (Finset V6)),
        if Disjoint T U then (0 : ℕ) else 1) = 25 := by
  decide +kernel

theorem s6_cross_lower_bound
    {𝒜 ℬ : Finset (Finset V6)}
    (h𝒜 : s6TFamily ⊆ 𝒜) (hℬ : s6TFamily ⊆ ℬ) :
    25 +
        (∑ I ∈ 𝒜 \ s6TFamily, s6TIntersectCount I) +
        (∑ J ∈ ℬ \ s6TFamily, s6TIntersectCount J) ≤
      supportCross 𝒜 ℬ := by
  let 𝒜₀ := 𝒜 \ s6TFamily
  let ℬ₀ := ℬ \ s6TFamily
  have h𝒜_union : 𝒜₀ ∪ s6TFamily = 𝒜 := by
    exact Finset.sdiff_union_of_subset h𝒜
  have hℬ_union : ℬ₀ ∪ s6TFamily = ℬ := by
    exact Finset.sdiff_union_of_subset hℬ
  have hinner (J : Finset V6) :
      supportHits 𝒜 J =
        (∑ I ∈ 𝒜₀, if Disjoint I J then 0 else 1) +
          (∑ I ∈ s6TFamily, if Disjoint I J then 0 else 1) := by
    calc
      supportHits 𝒜 J =
          ∑ I ∈ 𝒜₀ ∪ s6TFamily, if Disjoint I J then 0 else 1 := by
            unfold supportHits
            rw [h𝒜_union]
      _ = (∑ I ∈ 𝒜₀, if Disjoint I J then 0 else 1) +
          (∑ I ∈ s6TFamily, if Disjoint I J then 0 else 1) := by
            rw [Finset.sum_union Finset.sdiff_disjoint]
  have hfirst :
      (∑ J ∈ s6TFamily, supportHits 𝒜 J) =
        (∑ J ∈ s6TFamily, ∑ I ∈ 𝒜₀,
          if Disjoint I J then 0 else 1) +
        (∑ J ∈ s6TFamily, ∑ I ∈ s6TFamily,
          if Disjoint I J then 0 else 1) := by
    simp_rw [hinner]
    rw [Finset.sum_add_distrib]
  have hsecond :
      (∑ J ∈ ℬ₀, ∑ I ∈ s6TFamily, if Disjoint I J then 0 else 1) ≤
        (∑ J ∈ ℬ₀, supportHits 𝒜 J) := by
    apply Finset.sum_le_sum
    intro J hJ
    apply Finset.sum_le_sum_of_subset_of_nonneg h𝒜
    intro I hI hI₀
    split <;> omega
  have hsplit :
      supportCross 𝒜 ℬ =
        (∑ J ∈ s6TFamily, supportHits 𝒜 J) +
          (∑ J ∈ ℬ₀, supportHits 𝒜 J) := by
    unfold supportCross
    rw [← hℬ_union, Finset.sum_union Finset.sdiff_disjoint]
    dsimp [ℬ₀]
    ac_rfl
  have hmandatory :
      (∑ J ∈ s6TFamily, ∑ I ∈ s6TFamily,
        if Disjoint I J then 0 else 1) = 25 := by
    exact s6_mandatory_cross_count
  have hAinter :
      (∑ J ∈ s6TFamily, ∑ I ∈ 𝒜₀,
        if Disjoint I J then 0 else 1) =
      (∑ I ∈ 𝒜₀, s6TIntersectCount I) := by
    unfold s6TIntersectCount
    rw [Finset.sum_comm]
  have hBinter :
      (∑ J ∈ ℬ₀, ∑ I ∈ s6TFamily,
        if Disjoint I J then 0 else 1) =
      (∑ J ∈ ℬ₀, s6TIntersectCount J) := by
    simp [s6TIntersectCount, disjoint_comm]
  have hcross' := hsplit
  rw [hfirst, hmandatory, hAinter] at hcross'
  have hsecond' := hsecond
  rw [hBinter] at hsecond'
  change supportCross 𝒜 ℬ =
    (∑ I ∈ 𝒜 \ s6TFamily, s6TIntersectCount I) + 25 +
      (∑ J ∈ ℬ \ s6TFamily, supportHits 𝒜 J) at hcross'
  change (∑ J ∈ ℬ \ s6TFamily, s6TIntersectCount J) ≤
      (∑ J ∈ ℬ \ s6TFamily, supportHits 𝒜 J) at hsecond'
  omega

theorem s6_mandatory_weight :
    supportWeight s6TFamily = 15 := by
  decide +kernel

/-! The five rotations in the paper's explicit four-colour table.  The
    ten indices record the five vertex types followed by the five diagonal
    types; separating these indices from the actual support finsets lets the
    covering statement be checked over only `2^10` subsets. -/
abbrev S6VDIndex := Fin 10

def s6Next (j : Fin 5) : Fin 5 :=
  ⟨(j.val + 1) % 5, Nat.mod_lt _ (by decide)⟩

def s6VIndex (j : Fin 5) : S6VDIndex :=
  ⟨j.val, by omega⟩

def s6DIndex (j : Fin 5) : S6VDIndex :=
  ⟨5 + j.val, by omega⟩

def s6VDCode (I : Finset V6) : S6VDIndex :=
  if I = v0 then 0 else if I = v1 then 1 else if I = v2 then 2
  else if I = v3 then 3 else if I = v4 then 4
  else if I = d0 then 5 else if I = d1 then 6 else if I = d2 then 7
  else if I = d3 then 8 else 9

theorem s6VDCode_inj
    {I J : Finset V6} (hI : I ∈ s6VDFamily) (hJ : J ∈ s6VDFamily)
    (hcode : s6VDCode I = s6VDCode J) : I = J := by
  decide +kernel +revert

def s6VDIndexFamily (𝒜 : Finset (Finset V6)) : Finset S6VDIndex :=
  (𝒜.filter (fun I => I ∈ s6VDFamily)).image s6VDCode

theorem s6VDIndexFamily_card (𝒜 : Finset (Finset V6)) :
    (s6VDIndexFamily 𝒜).card =
      (𝒜.filter (fun I => I ∈ s6VDFamily)).card := by
  unfold s6VDIndexFamily
  apply Finset.card_image_of_injOn
  intro I hI J hJ hIJ
  exact s6VDCode_inj (Finset.mem_filter.mp hI).2
    (Finset.mem_filter.mp hJ).2 hIJ

def s6ForbiddenA (j : Fin 5) : Finset S6VDIndex :=
  {s6VIndex j, s6DIndex (s6Next j)}

def s6ForbiddenB (j : Fin 5) : Finset S6VDIndex :=
  {s6VIndex (s6Next j), s6DIndex j}

/- Each support index forbids exactly one of the five rotations. -/
def kernelS6BlockedA (i : S6VDIndex) : Fin 5 :=
  if hi : i.val < 5 then ⟨i.val, hi⟩
  else ⟨(i.val + 4) % 5, Nat.mod_lt _ (by decide)⟩

def kernelS6BlockedB (i : S6VDIndex) : Fin 5 :=
  if i.val < 5 then ⟨(i.val + 4) % 5, Nat.mod_lt _ (by decide)⟩
  else ⟨i.val - 5, by omega⟩

theorem kernel_s6_forbidden_blocked : ∀ j : Fin 5, ∀ i : S6VDIndex,
    (i ∈ s6ForbiddenA j ↔ kernelS6BlockedA i = j) ∧
    (i ∈ s6ForbiddenB j ↔ kernelS6BlockedB i = j) := by
  decide +kernel

theorem s6_vd_rotation_cover :
    ∀ X Y : Finset S6VDIndex, X.card + Y.card ≤ 4 →
      ∃ j : Fin 5, Disjoint X (s6ForbiddenA j) ∧
        Disjoint Y (s6ForbiddenB j) := by
  intro X Y hsize
  let bad := X.image kernelS6BlockedA ∪ Y.image kernelS6BlockedB
  have hbad : bad.card ≤ 4 :=
    (Finset.card_union_le _ _).trans
      ((Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)).trans hsize)
  have hex : ∃ j : Fin 5, j ∉ bad := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset (Fin 5)) ⊆ bad := fun j _ => h j
    have hc := Finset.card_le_card hsub
    have : 5 ≤ bad.card := by simpa using hc
    omega
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, Finset.disjoint_left.mpr ?_, Finset.disjoint_left.mpr ?_⟩
  · intro i hi hforbid
    apply hj
    exact Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨i, hi, ((kernel_s6_forbidden_blocked j i).1).mp hforbid⟩)
  · intro i hi hforbid
    apply hj
    exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨i, hi, ((kernel_s6_forbidden_blocked j i).2).mp hforbid⟩)

/-! One of the five explicit four-colour tables (the unrotated table).  The
    remaining four are obtained by cyclically relabelling the five cycle
    vertices; the finite rotation cover above identifies which table applies.
    We record the table as executable finite data and check its three edge
    conditions directly. -/

def s6AColor0Family : Finset (Finset V6) :=
  {∅, v1, v2, v3, v4, d0, d2, d3, t0, t2, t3}

def s6AColor2Family : Finset (Finset V6) := {d4, t4}

def s6BColor1Family : Finset (Finset V6) :=
  {∅, v0, v2, v4, d1, d3}

def s6BColor2Family : Finset (Finset V6) := {v3, d2, d4, t2, t4}

def s6AColor0 (I : Finset V6) : Fin 4 :=
  if I ∈ s6AColor0Family then 0
  else if I ∈ s6AColor2Family then 2
  else 3

def s6BColor0 (I : Finset V6) : Fin 4 :=
  if I ∈ s6BColor1Family then 1
  else if I ∈ s6BColor2Family then 2
  else 3

def s6CoreColor0 (x : V6) : Fin 4 :=
  -- The sixth (isolated) residual vertex uses the spare colour 1; this is
  -- the colour-0-shift of the paper's `(1,2,3,2,3;2)` core table.
  if x.val = 0 then 0 else if x.val = 1 then 1
  else if x.val = 2 then 2 else if x.val = 3 then 1
  else if x.val = 4 then 2 else 1

/-! Every non-mandatory support pays at least one unit of intersection
    penalty when it is a vertex/diagonal type.  This is the finite
    bookkeeping step that turns a lower bound on the number of such types
    into the `5 + W ≤ T` hypothesis used by the surplus lemma below. -/
theorem s6_support_penalty_of_vd_count
    {𝒜 ℬ : Finset (Finset V6)}
    (h𝒜sub : 𝒜 ⊆ s6Supports) (hℬsub : ℬ ⊆ s6Supports)
    (_h𝒜T : s6TFamily ⊆ 𝒜) (_hℬT : s6TFamily ⊆ ℬ)
    (hcount : 5 ≤
      (∑ I ∈ 𝒜 \ s6TFamily, if I ∈ s6VDFamily then 1 else 0) +
      (∑ J ∈ ℬ \ s6TFamily, if J ∈ s6VDFamily then 1 else 0)) :
    5 +
        (∑ I ∈ 𝒜 \ s6TFamily, I.card) +
        (∑ J ∈ ℬ \ s6TFamily, J.card) ≤
      (∑ I ∈ 𝒜 \ s6TFamily, s6TIntersectCount I) +
        (∑ J ∈ ℬ \ s6TFamily, s6TIntersectCount J) := by
  have hpointA (I : Finset V6) (hI : I ∈ 𝒜 \ s6TFamily) :
      I.card + (if I ∈ s6VDFamily then 1 else 0) ≤ s6TIntersectCount I := by
    have hIsup : I ∈ s6Supports := h𝒜sub (Finset.mem_sdiff.mp hI).1
    have hpart := s6_support_partition hIsup
    have hnotT : I ∉ s6TFamily := (Finset.mem_sdiff.mp hI).2
    rcases hpart with hV | hU | hZ | hT
    · have hp := (s6_support_intersection_penalty hIsup).1 hV
      simpa [hV] using hp
    · have hp := (s6_support_intersection_penalty hIsup).2.1 hU
      by_cases hv : I ∈ s6VDFamily
      · simp [hv]
        omega
      · simp [hv]
        exact (Nat.le_trans (Nat.le_add_right I.card 3) hp)
    · have hp := (s6_support_intersection_penalty hIsup).2.2 hZ
      by_cases hv : I ∈ s6VDFamily
      · simp [hv]
        omega
      · simp [hv]
        exact (Nat.le_trans (Nat.le_add_right I.card 4) hp)
    · exact (hnotT hT).elim
  have hpointB (J : Finset V6) (hJ : J ∈ ℬ \ s6TFamily) :
      J.card + (if J ∈ s6VDFamily then 1 else 0) ≤ s6TIntersectCount J := by
    have hJsup : J ∈ s6Supports := hℬsub (Finset.mem_sdiff.mp hJ).1
    have hpart := s6_support_partition hJsup
    have hnotT : J ∉ s6TFamily := (Finset.mem_sdiff.mp hJ).2
    rcases hpart with hV | hU | hZ | hT
    · have hp := (s6_support_intersection_penalty hJsup).1 hV
      simpa [hV] using hp
    · have hp := (s6_support_intersection_penalty hJsup).2.1 hU
      by_cases hv : J ∈ s6VDFamily
      · simp [hv]
        omega
      · simp [hv]
        exact (Nat.le_trans (Nat.le_add_right J.card 3) hp)
    · have hp := (s6_support_intersection_penalty hJsup).2.2 hZ
      by_cases hv : J ∈ s6VDFamily
      · simp [hv]
        omega
      · simp [hv]
        exact (Nat.le_trans (Nat.le_add_right J.card 4) hp)
    · exact (hnotT hT).elim
  have hsumA :
      (∑ I ∈ 𝒜 \ s6TFamily, I.card) +
          (∑ I ∈ 𝒜 \ s6TFamily, if I ∈ s6VDFamily then 1 else 0) ≤
        ∑ I ∈ 𝒜 \ s6TFamily, s6TIntersectCount I := by
    simpa [Finset.sum_add_distrib, add_assoc, add_comm, add_left_comm] using
      (Finset.sum_le_sum (fun I hI => hpointA I hI))
  have hsumB :
      (∑ J ∈ ℬ \ s6TFamily, J.card) +
          (∑ J ∈ ℬ \ s6TFamily, if J ∈ s6VDFamily then 1 else 0) ≤
        ∑ J ∈ ℬ \ s6TFamily, s6TIntersectCount J := by
    simpa [Finset.sum_add_distrib, add_assoc, add_comm, add_left_comm] using
      (Finset.sum_le_sum (fun J hJ => hpointB J hJ))
  omega

theorem s6_support_surplus_nonpositive_of_penalty
    {𝒜 ℬ : Finset (Finset V6)}
    (h𝒜 : s6TFamily ⊆ 𝒜) (hℬ : s6TFamily ⊆ ℬ)
    (hpen : 5 +
        (∑ I ∈ 𝒜 \ s6TFamily, I.card) +
        (∑ J ∈ ℬ \ s6TFamily, J.card) ≤
      (∑ I ∈ 𝒜 \ s6TFamily, s6TIntersectCount I) +
        (∑ J ∈ ℬ \ s6TFamily, s6TIntersectCount J)) :
    supportSurplus 𝒜 ℬ ≤ 0 := by
  have hWA := supportWeight_eq_sdiff_add h𝒜
  have hWB := supportWeight_eq_sdiff_add hℬ
  have hTweight := s6_mandatory_weight
  have hcross := s6_cross_lower_bound h𝒜 hℬ
  have hpen' :
      5 + supportWeight (𝒜 \ s6TFamily) + supportWeight (ℬ \ s6TFamily) ≤
        (∑ I ∈ 𝒜 \ s6TFamily, s6TIntersectCount I) +
          (∑ J ∈ ℬ \ s6TFamily, s6TIntersectCount J) := by
    simpa [supportWeight, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hpen
  unfold supportSurplus
  rw [hWA, hWB, hTweight] at *
  have hle :
      supportWeight (𝒜 \ s6TFamily) + 15 +
          (supportWeight (ℬ \ s6TFamily) + 15) ≤ supportCross 𝒜 ℬ := by
    omega
  have hz := Nat.sub_eq_zero_of_le hle
  omega

theorem s6_support_surplus_nonpositive_of_vd_count
    {𝒜 ℬ : Finset (Finset V6)}
    (h𝒜sub : 𝒜 ⊆ s6Supports) (hℬsub : ℬ ⊆ s6Supports)
    (h𝒜T : s6TFamily ⊆ 𝒜) (hℬT : s6TFamily ⊆ ℬ)
    (hcount : 5 ≤
      (∑ I ∈ 𝒜 \ s6TFamily, if I ∈ s6VDFamily then 1 else 0) +
      (∑ J ∈ ℬ \ s6TFamily, if J ∈ s6VDFamily then 1 else 0)) :
    supportSurplus 𝒜 ℬ ≤ 0 := by
  apply s6_support_surplus_nonpositive_of_penalty h𝒜T hℬT
  exact s6_support_penalty_of_vd_count h𝒜sub hℬsub h𝒜T hℬT hcount

run_cmd R5Kernel.checkStandardAxioms ``s6_vd_rotation_cover
run_cmd R5Kernel.checkStandardAxioms ``s6_support_surplus_nonpositive_of_vd_count

end Erdos1011

end Web_Erdos1011_S6Capacity
