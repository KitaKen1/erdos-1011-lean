import R5Kernel.Parts.M014
import R5Kernel.Probes.S11C11AllMasks
import R5Kernel.Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1
set_option maxRecDepth 200000

open Lean Elab Command

namespace Erdos1011

open scoped BigOperators

def kernelSupportIncidenceWeight
    {s : ℕ} (P : Finset (Finset (Fin s))) (R : Finset (Fin s))
    (weights : Fin s → ℕ) : ℕ :=
  ∑ I ∈ P, ∑ e ∈ R, if e ∈ I then weights e else 0

def kernelSupportResidualWeightScaled
    {s : ℕ} (P : Finset (Finset (Fin s))) (R : Finset (Fin s))
    (weights : Fin s → ℕ) (d : ℕ) : ℕ :=
  ∑ I ∈ P, (d * I.card - ∑ e ∈ R, if e ∈ I then weights e else 0)

def kernelSupportTightMembers
    {s : ℕ} (P B : Finset (Finset (Fin s))) : Finset (Finset (Fin s)) :=
  B.filter (fun J => supportHits P J = J.card)

def kernelSupportTightUnion
    {s : ℕ} (P B : Finset (Finset (Fin s))) : Finset (Fin s) :=
  (kernelSupportTightMembers P B).biUnion id

theorem kernel_mem_supportTightUnion_iff
    {s : ℕ} {P B : Finset (Finset (Fin s))} {e : Fin s} :
    e ∈ kernelSupportTightUnion P B ↔
      ∃ J ∈ B, supportHits P J = J.card ∧ e ∈ J := by
  classical
  unfold kernelSupportTightUnion kernelSupportTightMembers
  simp [and_assoc, and_left_comm, and_comm]

theorem kernel_supportSurplus_le_supportSurplus_subset
    {s : ℕ} {A P B : Finset (Finset (Fin s))}
    (hP : P ⊆ A)
    (hremove : ∀ I ∈ A \ P, I.card ≤ supportHits B I) :
    supportSurplus A B ≤ supportSurplus P B := by
  classical
  have hUnion : A \ P ∪ P = A := Finset.sdiff_union_of_subset hP
  have hWeight : supportWeight A =
      supportWeight (A \ P) + supportWeight P := by
    exact supportWeight_eq_sdiff_add hP
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

theorem kernel_supportHits_erase_add
    {s : ℕ} {P : Finset (Finset (Fin s))}
    {I J : Finset (Fin s)} (hI : I ∈ P) :
    supportHits P J = supportHits (P.erase I) J +
      (if Disjoint I J then 0 else 1) := by
  unfold supportHits
  rw [Finset.sum_erase_add P (fun I => if Disjoint I J then 0 else 1) hI]

theorem kernel_supportHits_ge_incidence_of_mem
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

theorem kernel_exists_support_minimal_representative
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
    have hdecomp := kernel_supportHits_erase_add (J := J) hIP
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

theorem kernel_supportResidualWeightScaled_le_if_of_subset
    {s : ℕ} {P U : Finset (Finset (Fin s))} {R : Finset (Fin s)}
    {weights : Fin s → ℕ} {d : ℕ}
    (hPU : P ⊆ U)
    (hnon : ∀ I ∈ P, (I ∩ R).Nonempty) :
    kernelSupportResidualWeightScaled P R weights d ≤
      ∑ I ∈ U, if (I ∩ R).Nonempty then
        d * I.card - ∑ e ∈ I,
          if e ∈ R then weights e else 0 else 0 := by
  have hrewrite :
      kernelSupportResidualWeightScaled P R weights d =
        ∑ I ∈ P, if (I ∩ R).Nonempty then
          d * I.card - ∑ e ∈ I,
            if e ∈ R then weights e else 0 else 0 := by
    unfold kernelSupportResidualWeightScaled
    apply Finset.sum_congr rfl
    intro I hI
    rw [if_pos (hnon I hI)]
    congr 1
    calc
      (∑ e ∈ R, if e ∈ I then weights e else 0) =
          ∑ e ∈ R.filter (fun e => e ∈ I), weights e := by
        rw [Finset.sum_filter]
      _ = ∑ e ∈ I.filter (fun e => e ∈ R), weights e := by
        have hfilter : R.filter (fun e => e ∈ I) =
            I.filter (fun e => e ∈ R) := by
          ext e
          simp [and_comm]
        rw [hfilter]
      _ = ∑ e ∈ I, if e ∈ R then weights e else 0 := by
        rw [Finset.sum_filter]
  rw [hrewrite]
  apply Finset.sum_le_sum_of_subset_of_nonneg hPU
  intro I hIU hIP
  exact Nat.zero_le _

theorem kernel_supportSurplus_le_scaled_beta_mul_sum_add_residual
    {s : ℕ} {A P B : Finset (Finset (Fin s))} {R : Finset (Fin s)}
    {weights : Fin s → ℕ} {d β K : ℕ}
    (hP : P ⊆ A)
    (hremove : ∀ I ∈ A \ P, I.card ≤ supportHits B I)
    (hcompat : ∀ J ∈ B, J.card ≤ supportHits P J)
    (hβ : ∀ e ∈ R, (∑ I ∈ P, if e ∈ I then 1 else 0) ≤ β)
    (hres : β * (∑ e ∈ R, weights e) +
      kernelSupportResidualWeightScaled P R weights d ≤ K) :
    d * supportSurplus A B ≤ K := by
  have hsubset : supportSurplus A B ≤ supportSurplus P B :=
    kernel_supportSurplus_le_supportSurplus_subset hP hremove
  have hsurplus : supportSurplus P B ≤ supportWeight P :=
    supportSurplus_le_leftWeight hcompat
  have hmul : d * supportWeight P ≤
      kernelSupportIncidenceWeight P R weights +
        kernelSupportResidualWeightScaled P R weights d := by
    unfold supportWeight kernelSupportIncidenceWeight
      kernelSupportResidualWeightScaled
    calc
      d * (∑ I ∈ P, I.card) =
          ∑ I ∈ P, d * I.card := by rw [Finset.mul_sum]
      _ ≤ ∑ I ∈ P, ((∑ e ∈ R, if e ∈ I then weights e else 0) +
          (d * I.card - ∑ e ∈ R, if e ∈ I then weights e else 0)) := by
        apply Finset.sum_le_sum
        intro I hI
        omega
      _ = kernelSupportIncidenceWeight P R weights +
          kernelSupportResidualWeightScaled P R weights d := by
        simp [kernelSupportIncidenceWeight,
          kernelSupportResidualWeightScaled, Finset.sum_add_distrib]
  have hinc : kernelSupportIncidenceWeight P R weights ≤
      β * (∑ e ∈ R, weights e) := by
    unfold kernelSupportIncidenceWeight
    rw [Finset.sum_comm]
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
  have hsurplus' : d * supportSurplus P B ≤
      β * (∑ e ∈ R, weights e) +
        kernelSupportResidualWeightScaled P R weights d := by
    exact (Nat.mul_le_mul_left d hsurplus).trans
      (hmul.trans (Nat.add_le_add_right hinc _))
  exact (Nat.mul_le_mul_left d hsubset).trans (hsurplus'.trans hres)

theorem kernel_c11_all_subset_certificate (R : Finset (Fin 11)) :
    ∃ b : ℕ, ∃ w : Fin 11 → ℕ,
      (∀ I ∈ cycleTypes 11 11, I ⊆ R → I.card ≤ b) ∧
      R5Kernel.dualValue (cycleTypes 11 11) R b 2 w ≤ 206 := by
  obtain ⟨c, d, hR⟩ := kernelC11_all_subsets_covered R
  obtain ⟨b, w, hβ, hvalue⟩ :=
    kernel_c11_canonical_orbit_certificate c d
  have hR' :
      (r5RepMaskSet11C11 (kernelC11CanonicalRep126 c)).map
          (kernelC11ActionEquiv d).toEmbedding = R := by
    simpa [r5RepMaskSet11C11, kernelC11SmallMask] using hR
  refine ⟨b, w, ?_, ?_⟩
  · intro I hI hsub
    apply hβ I hI
    rw [hR']
    exact hsub
  · simpa only [hR'] using hvalue

run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_all_subset_certificate

set_option maxHeartbeats 20000000 in
theorem kernel_c11_supportSurplus_le_103_of_minimal
    {A B P : Finset (Finset (Fin 11))}
    (hAU : A ⊆ cycleTypes 11 11)
    (hBU : B ⊆ cycleTypes 11 11)
    (hcompat : DegreeCompatible A B)
    (hP : P ⊆ A)
    (hPcompat : ∀ J ∈ B, J.card ≤ supportHits P J)
    (hminimal : ∀ I ∈ P, ∃ J ∈ B,
      supportHits P J = J.card ∧ ¬ Disjoint I J)
    (hcert : ∃ b : ℕ, ∃ w : Fin 11 → ℕ,
      (∀ I ∈ cycleTypes 11 11,
        I ⊆ kernelSupportTightUnion P B → I.card ≤ b) ∧
      R5Kernel.dualValue (cycleTypes 11 11)
        (kernelSupportTightUnion P B) b 2 w ≤ 206) :
    supportSurplus A B ≤ 103 := by
  classical
  let T := kernelSupportTightUnion P B
  obtain ⟨b, w, hβrow, hvalue⟩ := hcert
  by_cases hPne : P.Nonempty
  · have hRne : T.Nonempty := by
      rcases hPne with ⟨I, hIP⟩
      rcases hminimal I hIP with ⟨J, hJB, htight, hnotdisj⟩
      have hIJ : (I ∩ J).Nonempty := by
        by_contra h
        apply hnotdisj
        rw [Finset.disjoint_left]
        intro e heI heJ
        exact h ⟨e, Finset.mem_inter.mpr ⟨heI, heJ⟩⟩
      rcases hIJ with ⟨e, he⟩
      exact ⟨e, kernel_mem_supportTightUnion_iff.mpr
        ⟨J, hJB, htight, (Finset.mem_inter.mp he).2⟩⟩
    have hβ : ∀ e ∈ T,
        (∑ I ∈ P, if e ∈ I then 1 else 0) ≤ b := by
      intro e he
      rcases kernel_mem_supportTightUnion_iff.mp he with
        ⟨J, hJB, htight, heJ⟩
      have hJR : J ⊆ T := by
        intro x hx
        exact kernel_mem_supportTightUnion_iff.mpr ⟨J, hJB, htight, hx⟩
      exact (kernel_supportHits_ge_incidence_of_mem heJ).trans_eq htight |>.trans
        (hβrow J (hBU hJB) hJR)
    have hresSub :
        kernelSupportResidualWeightScaled P T w 2 ≤
          ∑ I ∈ cycleTypes 11 11, if (I ∩ T).Nonempty then
            2 * I.card - ∑ e ∈ I,
              if e ∈ T then w e else 0 else 0 := by
      apply kernel_supportResidualWeightScaled_le_if_of_subset (hP.trans hAU)
      intro I hIP
      rcases hminimal I hIP with ⟨J, hJB, htight, hnotdisj⟩
      have hIJ : (I ∩ J).Nonempty := by
        by_contra h
        apply hnotdisj
        rw [Finset.disjoint_left]
        intro e heI heJ
        exact h ⟨e, Finset.mem_inter.mpr ⟨heI, heJ⟩⟩
      rcases hIJ with ⟨e, he⟩
      exact ⟨e, Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp he).1, by
          exact kernel_mem_supportTightUnion_iff.mpr
            ⟨J, hJB, htight, (Finset.mem_inter.mp he).2⟩⟩⟩
    have hfull :
        b * (∑ e ∈ T, w e) +
          (∑ I ∈ cycleTypes 11 11, if (I ∩ T).Nonempty then
            2 * I.card - ∑ e ∈ I,
              if e ∈ T then w e else 0 else 0) ≤ 206 := by
      simpa only [T, R5Kernel.dualValue] using hvalue
    have hres : b * (∑ e ∈ T, w e) +
        kernelSupportResidualWeightScaled P T w 2 ≤ 206 := by
      exact (Nat.add_le_add_left hresSub _).trans hfull
    have htwice := kernel_supportSurplus_le_scaled_beta_mul_sum_add_residual
      (A := A) (P := P) (B := B) (R := T) (d := 2)
      (weights := w) (β := b) (K := 206)
      hP (fun I hI => hcompat.1 I (Finset.mem_sdiff.mp hI).1)
      hPcompat hβ hres
    omega
  · have hPempty : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hPne
    subst P
    have hBempty : B = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hBn
      rcases hBn with ⟨J, hJB⟩
      have h := hPcompat J hJB
      have hpos : 0 < J.card := by
        have hJind := Finset.mem_filter.mp (hBU hJB)
        exact Finset.card_pos.mpr hJind.2.1
      have hzero : supportHits (∅ : Finset (Finset (Fin 11))) J = 0 := by
        simp [supportHits]
      rw [hzero] at h
      omega
    have hAempty : A = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hAn
      rcases hAn with ⟨I, hIA⟩
      have h := hcompat.1 I hIA
      have hpos : 0 < I.card := by
        have hIind := Finset.mem_filter.mp (hAU hIA)
        exact Finset.card_pos.mpr hIind.2.1
      have hzero : supportHits (∅ : Finset (Finset (Fin 11))) I = 0 := by
        simp [supportHits]
      rw [hBempty, hzero] at h
      omega
    simp [supportSurplus, supportWeight, supportCross, supportHits, hAempty,
      hBempty]

theorem kernel_c11_supportSurplus_le_103
    {A B : Finset (Finset (Fin 11))}
    (hAU : A ⊆ cycleTypes 11 11)
    (hBU : B ⊆ cycleTypes 11 11)
    (hcompat : DegreeCompatible A B) :
    supportSurplus A B ≤ 103 := by
  rcases kernel_exists_support_minimal_representative hcompat.2 with
    ⟨P, hP, hPcompat, hminimal⟩
  exact kernel_c11_supportSurplus_le_103_of_minimal
    hAU hBU hcompat hP hPcompat hminimal
      (kernel_c11_all_subset_certificate (kernelSupportTightUnion P B))

run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_supportSurplus_le_103_of_minimal
run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_supportSurplus_le_103

end Erdos1011
