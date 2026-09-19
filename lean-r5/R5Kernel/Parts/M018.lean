import R5Kernel.Parts.M017

/- Source module: Erdos1011.CapacityGreedy. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_CapacityGreedy


namespace Erdos1011

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

def wtSum (w : α → ℕ) (S : Finset α) : ℕ := ∑ x ∈ S, w x

def wtLayer (w : α → ℕ) (S : Finset α) (k : ℕ) : Finset α :=
  S.filter (fun x => w x = k)

def topWtSumAux (w : α → ℕ) (U : Finset α) (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      let Uh := wtLayer w U (k + 1)
      let Ul := U \ Uh
      (Finset.range (min p Uh.card + 1)).sup
        (fun c => c * (k + 1) + topWtSumAux w Ul (p - c) k)

def topWtSum (w : α → ℕ) (U : Finset α) (p s : ℕ) : ℕ :=
  topWtSumAux w U p s

theorem wtLayer_subset {w : α → ℕ} {S U : Finset α} (hSU : S ⊆ U) (k : ℕ) :
    wtLayer w S k ⊆ wtLayer w U k := by
  exact Finset.filter_subset_filter _ hSU

theorem wtSum_zero_of_le_zero {w : α → ℕ} {S : Finset α}
    (hw : ∀ x ∈ S, w x ≤ 0) : wtSum w S = 0 := by
  unfold wtSum
  apply Finset.sum_eq_zero
  intro x hx
  have hx0 : w x = 0 := Nat.eq_zero_of_le_zero (hw x hx)
  simp [hx0]

theorem topWtSumAux_bound
    {w : α → ℕ} {S U : Finset α} {p k : ℕ}
    (hSU : S ⊆ U) (hScard : S.card ≤ p)
    (hw : ∀ x ∈ U, w x ≤ k) :
    wtSum w S ≤ topWtSumAux w U p k := by
  induction k generalizing S U p with
  | zero =>
      exact (wtSum_zero_of_le_zero (fun x hx => hw x (hSU hx))).le
  | succ k ih =>
      let Sh := wtLayer w S (k + 1)
      let Sl := S.filter (fun x => w x ≤ k)
      let Uh := wtLayer w U (k + 1)
      let Ul := U \ Uh
      have hShU : Sh ⊆ Uh := wtLayer_subset hSU (k + 1)
      have hShcard : Sh.card ≤ min p Uh.card := by
        apply Nat.le_min.mpr
        constructor
        · exact (Finset.card_filter_le S _).trans hScard
        · exact Finset.card_le_card hShU
      have hSlU : Sl ⊆ U := by
        intro x hx
        exact hSU (Finset.mem_filter.mp hx).1
      have hpart : Sh ∪ Sl = S := by
        ext x
        by_cases hxS : x ∈ S
        · by_cases hEq : w x = k + 1
          · simp [Sh, Sl, wtLayer, hEq, hxS]
          · have hle : w x ≤ k := by
              have := hw x (hSU hxS)
              omega
            simp [Sh, Sl, wtLayer, hEq, hxS, hle]
        · simp [Sh, Sl, wtLayer, hxS]
      have hdisj : Disjoint Sh Sl := by
        rw [Finset.disjoint_left]
        intro x hxH hxL
        have hHval := (Finset.mem_filter.mp hxH).2
        have hLval := (Finset.mem_filter.mp hxL).2
        omega
      have hcard : Sh.card + Sl.card = S.card := by
        rw [← Finset.card_union_of_disjoint hdisj, hpart]
      have hSh_le_p : Sh.card ≤ p := hShcard.trans (min_le_left _ _)
      have hSlcard : Sl.card ≤ p - Sh.card := by omega
      have hSlUl : Sl ⊆ Ul := by
        intro x hx
        apply Finset.mem_sdiff.mpr
        constructor
        · exact hSlU hx
        · intro hxH
          have hlow := (Finset.mem_filter.mp hx).2
          have hhigh := (Finset.mem_filter.mp hxH).2
          omega
      have hSl_bound : wtSum w Sl ≤ topWtSumAux w Ul (p - Sh.card) k := by
        apply ih hSlUl hSlcard
        intro x hx
        have hxU := (Finset.mem_sdiff.mp hx).1
        have hxnot := (Finset.mem_sdiff.mp hx).2
        have hxle := hw x hxU
        by_contra hnotle
        have hEq : w x = k + 1 := by omega
        exact hxnot (Finset.mem_filter.mpr ⟨hxU, hEq⟩)
      have hSh_sum : wtSum w Sh = Sh.card * (k + 1) := by
        unfold wtSum Sh wtLayer
        apply Finset.sum_eq_card_nsmul
        intro x hx
        exact (Finset.mem_filter.mp hx).2
      have hsum : wtSum w S = wtSum w Sh + wtSum w Sl := by
        unfold wtSum
        rw [← hpart, Finset.sum_union hdisj]
      unfold topWtSumAux
      dsimp [Uh, Ul]
      rw [hsum, hSh_sum]
      have harg : Sh.card ∈ Finset.range (min p Uh.card + 1) :=
        Finset.mem_range.mpr (by omega)
      have hsup := Finset.le_sup
        (s := Finset.range (min p Uh.card + 1))
        (f := fun c => c * (k + 1) + topWtSumAux w Ul (p - c) k) harg
      exact le_trans
        (Nat.add_le_add (le_rfl) hSl_bound) hsup

theorem topWtSumAux_eq_wtSum_of_card_le
    {w : α → ℕ} {U : Finset α} {p s : ℕ}
    (hUcard : U.card ≤ p) (hw : ∀ x ∈ U, w x ≤ s) :
    topWtSumAux w U p s = wtSum w U := by
  induction s generalizing U p with
  | zero =>
      unfold topWtSumAux
      symm
      exact wtSum_zero_of_le_zero (fun x hx => hw x hx)
  | succ k ih =>
      let Uh := wtLayer w U (k + 1)
      let Ul := U \ Uh
      have hUhU : Uh ⊆ U := by
        intro x hx
        exact (Finset.mem_filter.mp hx).1
      have hpart : Uh ∪ Ul = U := by
        exact Finset.union_sdiff_of_subset hUhU
      have hdisj : Disjoint Uh Ul := by
        rw [Finset.disjoint_left]
        intro x hxH hxL
        exact (Finset.mem_sdiff.mp hxL).2 hxH
      have hcardEq : Uh.card + Ul.card = U.card := by
        rw [← Finset.card_union_of_disjoint hdisj, hpart]
      have hUhSum : wtSum w Uh = Uh.card * (k + 1) := by
        unfold wtSum Uh wtLayer
        apply Finset.sum_eq_card_nsmul
        intro x hx
        exact (Finset.mem_filter.mp hx).2
      have hUlw : ∀ x ∈ Ul, w x ≤ k := by
        intro x hx
        have hxU := (Finset.mem_sdiff.mp hx).1
        have hxnot := (Finset.mem_sdiff.mp hx).2
        have hxle := hw x hxU
        by_contra hnotle
        have hEq : w x = k + 1 := by omega
        exact hxnot (Finset.mem_filter.mpr ⟨hxU, hEq⟩)
      have hterm : ∀ c ∈ Finset.range (min p Uh.card + 1),
          c * (k + 1) + topWtSumAux w Ul (p - c) k ≤ wtSum w U := by
        intro c hc
        have hc' : c ≤ min p Uh.card := by
          exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
        have hcU : c ≤ Uh.card := (Nat.le_min.mp hc').2
        have hcp : Ul.card ≤ p - c := by
          have hpc : c ≤ p := (Nat.le_min.mp hc').1
          omega
        have hrec := ih hcp hUlw
        have hcw : c * (k + 1) ≤ wtSum w Uh := by
          rw [hUhSum]
          exact Nat.mul_le_mul_right (k + 1) hcU
        have hsum : wtSum w U = wtSum w Uh + wtSum w Ul := by
          unfold wtSum
          rw [← hpart, Finset.sum_union hdisj]
        rw [hrec]
        rw [hsum]
        exact Nat.add_le_add hcw le_rfl
      have hupper : topWtSumAux w U p (k + 1) ≤ wtSum w U := by
        unfold topWtSumAux
        dsimp [Uh, Ul]
        exact Finset.sup_le hterm
      have hlower : wtSum w U ≤ topWtSumAux w U p (k + 1) :=
        topWtSumAux_bound (S := U) (U := U) (by exact Finset.Subset.rfl) hUcard hw
      exact le_antisymm hupper hlower

theorem topWtSum_eq_wtSum_of_card_le
    {w : α → ℕ} {U : Finset α} {p s : ℕ}
    (hUcard : U.card ≤ p) (hw : ∀ x ∈ U, w x ≤ s) :
    topWtSum w U p s = wtSum w U := by
  exact topWtSumAux_eq_wtSum_of_card_le hUcard hw

theorem wtSum_le_topWtSum {w : α → ℕ} {S U : Finset α} {p s : ℕ}
    (hSU : S ⊆ U) (hScard : S.card ≤ p) (hw : ∀ x ∈ U, w x ≤ s) :
    wtSum w S ≤ topWtSum w U p s :=
  topWtSumAux_bound hSU hScard hw

def hitFamily (R : α → α → Prop) [DecidableRel R]
    (U : Finset α) (J : α) : Finset α := U.filter (fun I => R I J)

def freeFamily (R : α → α → Prop) [DecidableRel R]
    (U : Finset α) (J : α) : Finset α := U.filter (fun I => ¬ R I J)

def capacityRow (w : α → ℕ) (R : α → α → Prop) [DecidableRel R]
    (U : Finset α) (J : α) (p t c : ℕ) (s : ℕ) : ℕ :=
  topWtSum w (hitFamily R U J) c s +
    topWtSum w (freeFamily R U J) (p - c) s

def capacityGoodSet (w : α → ℕ) (R : α → α → Prop) [DecidableRel R]
    (U : Finset α) (J : α) (p t s : ℕ) : Finset ℕ :=
  (Finset.range (min p (hitFamily R U J).card + 1)).filter
    (fun c => capacityRow w R U J p t c s ≥ t)

def capacityD (w : α → ℕ) (R : α → α → Prop) [DecidableRel R]
    (U : Finset α) (J : α) (p t s : ℕ) : ℕ :=
  let C := capacityGoodSet w R U J p t s
  if h : C.Nonempty then C.min' h else p + 1

theorem capacityD_le_of_good
    {w : α → ℕ} {R : α → α → Prop} [DecidableRel R]
    {U : Finset α} {J : α} {p t s c : ℕ}
    (hc : c ≤ min p (hitFamily R U J).card)
    (hgood : capacityRow w R U J p t c s ≥ t) :
    capacityD w R U J p t s ≤ c := by
  unfold capacityD
  dsimp
  unfold capacityGoodSet
  split
  · next hC =>
      apply Finset.min'_le
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by omega), hgood⟩
  · next hC =>
      exfalso
      apply hC
      refine ⟨c, ?_⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hgood⟩

theorem capacityD_le_of_family
    {w : α → ℕ} {R : α → α → Prop} [DecidableRel R]
    {U A : Finset α} {J : α} {p t s : ℕ}
    (hAU : A ⊆ U) (hAcard : A.card ≤ p)
    (hw : ∀ x ∈ U, w x ≤ s)
    (hrow : wtSum w A ≥ t) :
    capacityD w R U J p t s ≤ (A.filter (fun I => R I J)).card := by
  let Ah := A.filter (fun I => R I J)
  let Af := A.filter (fun I => ¬ R I J)
  have hAhU : Ah ⊆ hitFamily R U J := by
    intro I hI
    exact Finset.mem_filter.mpr ⟨hAU (Finset.mem_filter.mp hI).1,
      (Finset.mem_filter.mp hI).2⟩
  have hAfU : Af ⊆ freeFamily R U J := by
    intro I hI
    exact Finset.mem_filter.mpr ⟨hAU (Finset.mem_filter.mp hI).1,
      (Finset.mem_filter.mp hI).2⟩
  have hpart : Ah ∪ Af = A := by
    ext I
    by_cases hI : R I J <;> simp [Ah, Af, hI]
  have hdisj : Disjoint Ah Af := by
    rw [Finset.disjoint_left]
    intro I hIh hIf
    exact (Finset.mem_filter.mp hIf).2 (Finset.mem_filter.mp hIh).2
  have hcard : Ah.card + Af.card = A.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hpart]
  have hAfcard : Af.card ≤ p - Ah.card := by omega
  have hrow' : capacityRow w R U J p t Ah.card s ≥ t := by
    have hAhw := wtSum_le_topWtSum hAhU (le_refl _)
      (fun x hx => hw x (Finset.mem_filter.mp hx).1)
    have hAfw := wtSum_le_topWtSum hAfU hAfcard
      (fun x hx => hw x (Finset.mem_filter.mp hx).1)
    have hsum : wtSum w A = wtSum w Ah + wtSum w Af := by
      unfold wtSum
      rw [← hpart, Finset.sum_union hdisj]
    unfold capacityRow
    have hsum' : t ≤ wtSum w Ah + wtSum w Af := by omega
    exact hsum'.trans (Nat.add_le_add hAhw hAfw)
  exact capacityD_le_of_good
    (by
      apply Nat.le_min.mpr
      constructor
      · exact (Finset.card_filter_le A (fun I => R I J)).trans hAcard
      · exact Finset.card_le_card hAhU) hrow'

def capacityDelta (w : α → ℕ) (R : α → α → Prop) [DecidableRel R]
    (U : Finset α) (J : α) (p t s : ℕ) : ℕ :=
  max (w J) (capacityD w R U J p t s)

theorem hitCount_eq_card_filter
    {R : α → α → Prop} [DecidableRel R]
    (A : Finset α) (J : α) :
    (∑ I ∈ A, if R I J then 1 else 0) = (A.filter (fun I => R I J)).card := by
  rw [← Finset.sum_filter]
  simp

/-!
The same bookkeeping works with an arbitrary multiplier `k`.  The `k = 1`
instance above is the form used by the first capacity certificate.  Keeping
the multiplier explicit is useful for the paper's stronger estimate

  `k * F ≤ (k - 1) * W_A + Σ max (0, (k+1)w(J) - kδ_t(J))`.

All quantities here are natural numbers, so the displayed positive part is
represented by truncated subtraction.  The theorem is deliberately stated
for the finite capacity object rather than for a particular graph encoding.
-/

def capacityTermK (k : ℕ) (w : α → ℕ) (R : α → α → Prop)
    [DecidableRel R] (U : Finset α) (J : α) (p t maxW : ℕ) : ℕ :=
  (k + 1) * w J - k * capacityDelta w R U J p t maxW

def capacityQK (k : ℕ) (w : α → ℕ) (R : α → α → Prop)
    [DecidableRel R] (U : Finset α) (q p t maxW : ℕ) : ℕ :=
  topWtSum (capacityTermK k w R U · p t maxW) U q ((k + 1) * maxW)

theorem capacityTermK_le_weight
    {k : ℕ} {w : α → ℕ} {R : α → α → Prop} [DecidableRel R]
    {U : Finset α} {J : α} {p t maxW : ℕ}
    (hw : w J ≤ maxW) :
    capacityTermK k w R U J p t maxW ≤ (k + 1) * maxW := by
  unfold capacityTermK
  have hmul : (k + 1) * w J ≤ (k + 1) * maxW :=
    Nat.mul_le_mul_left (k + 1) hw
  omega

theorem capacityQK_upper_of_subset
    {k : ℕ} {w : α → ℕ} {R : α → α → Prop} [DecidableRel R]
    {U B : Finset α} {q p t maxW : ℕ}
    (hBU : B ⊆ U) (hBcard : B.card ≤ q)
    (hw : ∀ J ∈ U, w J ≤ maxW) :
    wtSum (fun J => capacityTermK k w R U J p t maxW) B ≤
      capacityQK k w R U q p t maxW := by
  unfold capacityQK
  apply wtSum_le_topWtSum hBU hBcard
  intro J hJ
  exact capacityTermK_le_weight (hw J hJ)

theorem capacityQK_surplus_bound
    {k : ℕ} {w : α → ℕ} {R : α → α → Prop} [DecidableRel R]
    {U A B : Finset α} {p q t maxW : ℕ}
    (hAU : A ⊆ U) (hBU : B ⊆ U)
    (hAcard : A.card ≤ p) (hBcard : B.card ≤ q)
    (hw : ∀ J ∈ U, w J ≤ maxW)
    (hWA : wtSum w A ≥ t)
    (horder : wtSum w A ≤ wtSum w B)
    (hcompat : ∀ J ∈ B, w J ≤
      ∑ I ∈ A, if R I J then 1 else 0) :
    k * (wtSum w A + wtSum w B -
        (∑ J ∈ B, ∑ I ∈ A, if R I J then 1 else 0)) ≤
      (k - 1) * wtSum w A + capacityQK k w R U q p t maxW := by
  have hcross_eq :
      (∑ J ∈ B, ∑ I ∈ A, if R I J then 1 else 0) =
        ∑ J ∈ B, (A.filter (fun I => R I J)).card := by
    apply Finset.sum_congr rfl
    intro J hJ
    exact hitCount_eq_card_filter A J
  have hDelta : ∀ J ∈ B,
      capacityDelta w R U J p t maxW ≤
        (A.filter (fun I => R I J)).card := by
    intro J hJ
    have hd := capacityD_le_of_family (w := w) (R := R) (U := U)
      (A := A) (J := J) hAU hAcard hw hWA
    have hdeg : w J ≤ (A.filter (fun I => R I J)).card := by
      rw [← hitCount_eq_card_filter A J]
      exact hcompat J hJ
    unfold capacityDelta
    exact max_le hdeg hd
  have hpoint : ∀ J ∈ B,
      (k + 1) * w J - k * (A.filter (fun I => R I J)).card ≤
        capacityTermK k w R U J p t maxW := by
    intro J hJ
    unfold capacityTermK
    have hd := hDelta J hJ
    exact Nat.sub_le_sub_left (Nat.mul_le_mul_left k hd) _
  have hpoint' : ∀ J ∈ B,
      (k + 1) * w J ≤
        k * (A.filter (fun I => R I J)).card +
          capacityTermK k w R U J p t maxW := by
    intro J hJ
    unfold capacityTermK
    have hd := hDelta J hJ
    have hmul : k * (A.filter (fun I => R I J)).card ≥
        k * capacityDelta w R U J p t maxW :=
      Nat.mul_le_mul_left k hd
    omega
  have hsumPoint :
      (∑ J ∈ B, (k + 1) * w J) ≤
        k * (∑ J ∈ B, (A.filter (fun I => R I J)).card) +
          wtSum (fun J => capacityTermK k w R U J p t maxW) B := by
    have hsum := Finset.sum_le_sum (fun J hJ => hpoint' J hJ)
    simpa [wtSum, Finset.sum_add_distrib, Finset.mul_sum] using hsum
  have hq := capacityQK_upper_of_subset (k := k) (w := w) (R := R)
    (U := U) (B := B) (q := q) (p := p) (t := t) (maxW := maxW)
    hBU hBcard hw
  have hcompatSum :
      wtSum w B ≤ ∑ J ∈ B, (A.filter (fun I => R I J)).card := by
    simp only [wtSum]
    exact Finset.sum_le_sum (fun J hJ => by
      rw [← hitCount_eq_card_filter A J]
      exact hcompat J hJ)
  have hmain :
      k * (wtSum w A + wtSum w B -
        (∑ J ∈ B, (A.filter (fun I => R I J)).card)) ≤
      (k - 1) * wtSum w A +
        wtSum (fun J => capacityTermK k w R U J p t maxW) B := by
    let C : ℕ := ∑ J ∈ B, (A.filter (fun I => R I J)).card
    let WA : ℕ := wtSum w A
    let WB : ℕ := wtSum w B
    let T : ℕ := wtSum (fun J => capacityTermK k w R U J p t maxW) B
    have hsumWB : (k + 1) * WB ≤ k * C + T := by
      simpa [WB, C, T, wtSum, Finset.mul_sum, Nat.add_mul] using hsumPoint
    have hkwA : k * WA ≤ (k - 1) * WA + WA := by
      cases k with
      | zero => simp
      | succ k => simp [Nat.succ_mul]
    have hWApart : k * WA ≤ (k - 1) * WA + WB :=
      hkwA.trans (Nat.add_le_add_left horder ((k - 1) * WA))
    have hfirst : k * WA + k * WB - k * C ≤
        ((k - 1) * WA + WB) + k * WB - k * C := by
      exact Nat.sub_le_sub_right
        (Nat.add_le_add_right hWApart (k * WB)) (k * C)
    have hraw : WB + k * WB - k * C ≤ T := by
      apply Nat.sub_le_iff_le_add'.mpr
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        Nat.succ_mul] using hsumWB
    have hsecond : ((k - 1) * WA + WB) + k * WB - k * C ≤
        (k - 1) * WA + T := by
      have hsplit : ((k - 1) * WA + WB) + k * WB - k * C ≤
          (k - 1) * WA + (WB + k * WB - k * C) := by
        omega
      have := Nat.add_le_add_left hraw ((k - 1) * WA)
      exact hsplit.trans (by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this)
    dsimp [WA, WB, C, T] at hfirst hsecond ⊢
    rw [Nat.mul_sub_left_distrib, Nat.mul_add]
    exact hfirst.trans hsecond
  rw [hcross_eq]
  exact le_trans hmain (Nat.add_le_add_left hq _)

def capacitySumK (k : ℕ) (w : α → ℕ) (R : α → α → Prop)
    [DecidableRel R] (U : Finset α) (p t maxW : ℕ) : ℕ :=
  wtSum (capacityTermK k w R U · p t maxW) U

theorem capacityQK_eq_capacitySumK
    {k : ℕ} {w : α → ℕ} {R : α → α → Prop} [DecidableRel R]
    {U : Finset α} {p t maxW : ℕ}
    (hw : ∀ J ∈ U, w J ≤ maxW) :
    capacityQK k w R U U.card p t maxW = capacitySumK k w R U p t maxW := by
  unfold capacityQK capacitySumK
  apply topWtSum_eq_wtSum_of_card_le
  · exact le_rfl
  · intro J hJ
    exact capacityTermK_le_weight (hw J hJ)

theorem capacitySumK_surplus_bound
    {k : ℕ} {w : α → ℕ} {R : α → α → Prop} [DecidableRel R]
    {U A B : Finset α} {p t maxW : ℕ}
    (hAU : A ⊆ U) (hBU : B ⊆ U)
    (hAcard : A.card ≤ p)
    (hw : ∀ J ∈ U, w J ≤ maxW)
    (hWA : wtSum w A ≥ t)
    (horder : wtSum w A ≤ wtSum w B)
    (hcompat : ∀ J ∈ B, w J ≤
      ∑ I ∈ A, if R I J then 1 else 0) :
    k * (wtSum w A + wtSum w B -
        (∑ J ∈ B, ∑ I ∈ A, if R I J then 1 else 0)) ≤
      (k - 1) * wtSum w A + capacitySumK k w R U p t maxW := by
  have hq := capacityQK_surplus_bound (k := k) (w := w) (R := R)
    (U := U) (A := A) (B := B) (p := p) (q := U.card) (t := t)
    (maxW := maxW) hAU hBU hAcard (Finset.card_le_card hBU) hw hWA horder hcompat
  rw [capacityQK_eq_capacitySumK hw] at hq
  exact hq

end Erdos1011

end Web_Erdos1011_CapacityGreedy
