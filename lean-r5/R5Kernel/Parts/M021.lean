import R5Kernel.Parts.M020

/- Source module: Erdos1011.R5MinimalRepresentative. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_R5MinimalRepresentative


namespace Erdos1011

open scoped BigOperators

/-!
  The finite capacity tables bound a support family once a finite universe is
  known.  This file records the elementary ``minimal representative'' step
  used before that table lookup.  It is stated with natural weights, which is
  the representation used by the existing dual replay layer.

  The finite descent theorem below constructs an inclusion-minimal `P` from
  the right-side compatibility hypothesis.  The remaining graph-specific
  input is the finite-table bound on the resulting tight union and residual
  term; that input is kept as a hypothesis so the arithmetic layer remains
  reusable by every structural producer.
-/

def supportIncidenceWeight
    {s : ℕ} (P : Finset (Finset (Fin s))) (R : Finset (Fin s))
    (weights : Fin s → ℕ) : ℕ :=
  ∑ I ∈ P, ∑ e ∈ R, if e ∈ I then weights e else 0

def supportResidualWeight
    {s : ℕ} (P : Finset (Finset (Fin s))) (R : Finset (Fin s))
    (weights : Fin s → ℕ) : ℕ :=
  ∑ I ∈ P, (I.card - ∑ e ∈ R, if e ∈ I then weights e else 0)

def supportTightMembers
    {s : ℕ} (P B : Finset (Finset (Fin s))) : Finset (Finset (Fin s)) :=
  B.filter (fun J => supportHits P J = J.card)

def supportTightUnion
    {s : ℕ} (P B : Finset (Finset (Fin s))) : Finset (Fin s) :=
  (supportTightMembers P B).biUnion id

theorem mem_supportTightUnion_iff
    {s : ℕ} {P B : Finset (Finset (Fin s))} {e : Fin s} :
    e ∈ supportTightUnion P B ↔
      ∃ J ∈ B, supportHits P J = J.card ∧ e ∈ J := by
  classical
  unfold supportTightUnion supportTightMembers
  simp [and_assoc, and_left_comm, and_comm]

theorem supportSurplus_le_supportSurplus_subset
    {s : ℕ} {A P B : Finset (Finset (Fin s))}
    (hP : P ⊆ A)
    (hremove : ∀ I ∈ A \ P, I.card ≤ supportHits B I) :
    supportSurplus A B ≤ supportSurplus P B := by
  classical
  have hUnion : A \ P ∪ P = A := Finset.sdiff_union_of_subset hP
  have hWeight : supportWeight A =
      supportWeight (A \ P) + supportWeight P :=
    supportWeight_eq_sdiff_add hP
  have hHits (J : Finset (Fin s)) :
      supportHits A J = supportHits (A \ P) J + supportHits P J := by
    calc
      supportHits A J = supportHits ((A \ P) ∪ P) J := by rw [hUnion]
      _ = supportHits (A \ P) J + supportHits P J := by
        unfold supportHits
        rw [Finset.sum_union Finset.sdiff_disjoint]
  have hCross : supportCross A B =
      supportCross (A \ P) B + supportCross P B := by
    unfold supportCross
    calc
      (∑ J ∈ B, supportHits A J) =
          ∑ J ∈ B, (supportHits (A \ P) J + supportHits P J) := by
        apply Finset.sum_congr rfl
        intro J hJ
        exact hHits J
      _ = (∑ J ∈ B, supportHits (A \ P) J) +
          (∑ J ∈ B, supportHits P J) := by
        rw [Finset.sum_add_distrib]
  have hdrop : supportWeight (A \ P) ≤ supportCross (A \ P) B := by
    exact supportCross_ge_rightWeight hremove
  unfold supportSurplus
  rw [hWeight, hCross]
  omega

theorem supportHits_erase_add
    {s : ℕ} {P : Finset (Finset (Fin s))}
    {I J : Finset (Fin s)} (hI : I ∈ P) :
    supportHits P J = supportHits (P.erase I) J +
      (if Disjoint I J then 0 else 1) := by
  unfold supportHits
  rw [Finset.sum_erase_add P (fun I => if Disjoint I J then 0 else 1) hI]

theorem exists_support_minimal_representative
    {s : ℕ} {A B : Finset (Finset (Fin s))}
    (hcompat : ∀ J ∈ B, J.card ≤ supportHits A J) :
    ∃ P : Finset (Finset (Fin s)),
      P ⊆ A ∧
      (∀ J ∈ B, J.card ≤ supportHits P J) ∧
      (∀ I ∈ P, ∃ J ∈ B,
        supportHits P J = J.card ∧ ¬ Disjoint I J) := by
  classical
  let Good : Finset (Finset (Fin s)) → Prop := fun P =>
    P ⊆ A ∧ ∀ J ∈ B, J.card ≤ supportHits P J
  obtain ⟨P, hPmin⟩ := exists_minimal_of_wellFoundedLT Good
    ⟨A, (by intro x hx; exact hx), hcompat⟩
  have hPgood : Good P := hPmin.1
  have hPsub : P ⊆ A := hPgood.1
  have hPcompat : ∀ J ∈ B, J.card ≤ supportHits P J := hPgood.2
  refine ⟨P, hPsub, hPcompat, ?_⟩
  intro I hIP
  by_contra hnone
  have hGoodErase : Good (P.erase I) := by
    refine ⟨(Finset.erase_subset I P).trans hPsub, ?_⟩
    intro J hJB
    have hbase := hPcompat J hJB
    have hdecomp := supportHits_erase_add (J := J) hIP
    by_cases hdis : Disjoint I J
    · rw [hdecomp, if_pos hdis] at hbase
      exact hbase
    · have hneq : supportHits P J ≠ J.card := by
        intro heq
        exact hnone ⟨J, hJB, heq, hdis⟩
      have hlt : J.card < supportHits P J :=
        Nat.lt_of_le_of_ne hbase (fun heq => hneq heq.symm)
      rw [hdecomp, if_neg hdis] at hlt
      omega
  have hEq : P = P.erase I :=
    (minimal_iff.mp hPmin).2 hGoodErase (Finset.erase_subset I P)
  have hImem : I ∈ P.erase I := by
    rw [← hEq]
    exact hIP
  have hnot : I ∉ P.erase I := by simp
  exact hnot hImem

theorem supportWeight_le_incidence_add_residual
    {s : ℕ} {P : Finset (Finset (Fin s))} {R : Finset (Fin s)}
    {weights : Fin s → ℕ} :
    supportWeight P ≤
      supportIncidenceWeight P R weights + supportResidualWeight P R weights := by
  unfold supportWeight supportIncidenceWeight supportResidualWeight
  calc
    (∑ I ∈ P, I.card) ≤
        ∑ I ∈ P, ((∑ e ∈ R, if e ∈ I then weights e else 0) +
          (I.card - ∑ e ∈ R, if e ∈ I then weights e else 0)) := by
      apply Finset.sum_le_sum
      intro I hI
      omega
    _ = (∑ I ∈ P, ∑ e ∈ R, if e ∈ I then weights e else 0) +
          ∑ I ∈ P, (I.card - ∑ e ∈ R, if e ∈ I then weights e else 0) := by
      rw [Finset.sum_add_distrib]

theorem supportIncidenceWeight_eq_reordered
    {s : ℕ} {P : Finset (Finset (Fin s))} {R : Finset (Fin s)}
    {weights : Fin s → ℕ} :
    supportIncidenceWeight P R weights =
      ∑ e ∈ R, ∑ I ∈ P, if e ∈ I then weights e else 0 := by
  unfold supportIncidenceWeight
  rw [Finset.sum_comm]

theorem supportIncidenceWeight_le_beta
    {s : ℕ} {P : Finset (Finset (Fin s))} {R : Finset (Fin s)}
    {weights : Fin s → ℕ} {β : ℕ}
    (hβ : ∀ e ∈ R, (∑ I ∈ P, if e ∈ I then 1 else 0) ≤ β) :
    supportIncidenceWeight P R weights ≤
      β * (∑ e ∈ R, weights e) := by
  rw [supportIncidenceWeight_eq_reordered]
  calc
    (∑ e ∈ R, ∑ I ∈ P, if e ∈ I then weights e else 0) ≤
        ∑ e ∈ R, weights e * β := by
      apply Finset.sum_le_sum
      intro e he
      have h := hβ e he
      have hmul :
          (∑ I ∈ P, if e ∈ I then weights e else 0) =
            weights e * (∑ I ∈ P, if e ∈ I then 1 else 0) := by
        calc
          (∑ I ∈ P, if e ∈ I then weights e else 0) =
              ∑ I ∈ P, weights e * (if e ∈ I then 1 else 0) := by
                apply Finset.sum_congr rfl
                intro I hI
                by_cases hmem : e ∈ I <;> simp [hmem]
          _ = weights e * (∑ I ∈ P, if e ∈ I then 1 else 0) := by
                rw [Finset.mul_sum]
      rw [hmul]
      exact Nat.mul_le_mul_left _ h
    _ = β * (∑ e ∈ R, weights e) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [Nat.mul_comm]

theorem supportHits_ge_incidence_of_mem
    {s : ℕ} {P : Finset (Finset (Fin s))}
    {e : Fin s} {J : Finset (Fin s)} (heJ : e ∈ J) :
    (∑ I ∈ P, if e ∈ I then 1 else 0) ≤ supportHits P J := by
  unfold supportHits
  apply Finset.sum_le_sum
  intro I hI
  by_cases heI : e ∈ I
  · have hnot : ¬ Disjoint I J := by
      intro hdis
      exact (Finset.disjoint_left.1 hdis) heI heJ
    simp [heI, hnot]
  · simp [heI]

/- The preceding lemma only needs the cardinal bound on tight members.  This
   exact hypothesis is useful for representative-dual certificates, whose
   `β` is the independence number of the tight union rather than the maximum
   size of every support on the opposite side. -/
theorem supportIncidence_le_beta_on_tightUnion_of_tight
    {s : ℕ} {P B : Finset (Finset (Fin s))} {β : ℕ}
    (hβ : ∀ J ∈ supportTightMembers P B, J.card ≤ β) :
    ∀ e ∈ supportTightUnion P B,
      (∑ I ∈ P, if e ∈ I then 1 else 0) ≤ β := by
  intro e he
  rcases (mem_supportTightUnion_iff.mp he) with ⟨J, hJB, htight, heJ⟩
  have hmem : J ∈ supportTightMembers P B := by
    exact Finset.mem_filter.mpr ⟨hJB, htight⟩
  exact (supportHits_ge_incidence_of_mem heJ).trans_eq htight |>.trans
    (hβ J hmem)

theorem supportWeight_le_beta_mul_sum_add_residual
    {s : ℕ} {P : Finset (Finset (Fin s))} {R : Finset (Fin s)}
    {weights : Fin s → ℕ} {β : ℕ}
    (hβ : ∀ e ∈ R, (∑ I ∈ P, if e ∈ I then 1 else 0) ≤ β) :
    supportWeight P ≤
      β * (∑ e ∈ R, weights e) + supportResidualWeight P R weights := by
  exact (supportWeight_le_incidence_add_residual).trans
    (Nat.add_le_add_right (supportIncidenceWeight_le_beta hβ) _)

theorem supportSurplus_le_beta_mul_sum_add_residual
    {s : ℕ} {P B : Finset (Finset (Fin s))} {R : Finset (Fin s)}
    {weights : Fin s → ℕ} {β K : ℕ}
    (hcompat : ∀ J ∈ B, J.card ≤ supportHits P J)
    (hβ : ∀ e ∈ R, (∑ I ∈ P, if e ∈ I then 1 else 0) ≤ β)
    (hres : β * (∑ e ∈ R, weights e) + supportResidualWeight P R weights ≤ K) :
    supportSurplus P B ≤ K := by
  have hsurplus : supportSurplus P B ≤ supportWeight P :=
    supportSurplus_le_leftWeight hcompat
  exact hsurplus.trans ((supportWeight_le_beta_mul_sum_add_residual hβ).trans hres)

theorem supportSurplus_le_beta_mul_sum_add_residual_of_subset
    {s : ℕ} {A P B : Finset (Finset (Fin s))}
    {R : Finset (Fin s)} {weights : Fin s → ℕ} {β K : ℕ}
    (hP : P ⊆ A)
    (hremove : ∀ I ∈ A \ P, I.card ≤ supportHits B I)
    (hcompat : ∀ J ∈ B, J.card ≤ supportHits P J)
    (hβ : ∀ e ∈ R, (∑ I ∈ P, if e ∈ I then 1 else 0) ≤ β)
    (hres : β * (∑ e ∈ R, weights e) + supportResidualWeight P R weights ≤ K) :
    supportSurplus A B ≤ K := by
  exact (supportSurplus_le_supportSurplus_subset hP hremove).trans
    (supportSurplus_le_beta_mul_sum_add_residual hcompat hβ hres)

theorem supportSurplus_le_beta_mul_sum_add_residual_of_tight_union_of_tight
    {s : ℕ} {A P B : Finset (Finset (Fin s))}
    {weights : Fin s → ℕ} {β K : ℕ}
    (hP : P ⊆ A)
    (hremove : ∀ I ∈ A \ P, I.card ≤ supportHits B I)
    (hcompat : ∀ J ∈ B, J.card ≤ supportHits P J)
    (hβ : ∀ J ∈ supportTightMembers P B, J.card ≤ β)
    (hres : β * (∑ e ∈ supportTightUnion P B, weights e) +
      supportResidualWeight P (supportTightUnion P B) weights ≤ K) :
    supportSurplus A B ≤ K := by
  apply supportSurplus_le_beta_mul_sum_add_residual_of_subset hP hremove hcompat
  · exact supportIncidence_le_beta_on_tightUnion_of_tight hβ
  · exact hres

end Erdos1011

end Web_Erdos1011_R5MinimalRepresentative
