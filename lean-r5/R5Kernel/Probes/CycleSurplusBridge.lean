import R5Kernel.Probes.S11C11EmbeddingBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000

namespace Erdos1011
open scoped BigOperators

/- The minimal-support argument needs certificates only for nonempty tight
unions. Keep the cycle size, scale, and bound symbolic for every profile. -/
theorem kernel_supportSurplus_scaled_of_minimal
    {s ell d K : ℕ}
    {A B P : Finset (Finset (Fin s))}
    (hAU : A ⊆ cycleTypes s ell)
    (hBU : B ⊆ cycleTypes s ell)
    (hcompat : DegreeCompatible A B)
    (hP : P ⊆ A)
    (hPcompat : ∀ J ∈ B, J.card ≤ supportHits P J)
    (hminimal : ∀ I ∈ P, ∃ J ∈ B,
      supportHits P J = J.card ∧ ¬ Disjoint I J)
    (hcert : ∀ R : Finset (Fin s), R.Nonempty →
      ∃ b : ℕ, ∃ w : Fin s → ℕ,
      (∀ I ∈ cycleTypes s ell,
        I ⊆ R → I.card ≤ b) ∧
      R5Kernel.dualValue (cycleTypes s ell)
        R b d w ≤ K) :
    d * supportSurplus A B ≤ K := by
  classical
  let T := kernelSupportTightUnion P B
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
    obtain ⟨b, w, hβrow, hvalue⟩ := hcert T hRne
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
        kernelSupportResidualWeightScaled P T w d ≤
          ∑ I ∈ cycleTypes s ell, if (I ∩ T).Nonempty then
            d * I.card - ∑ e ∈ I,
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
          (∑ I ∈ cycleTypes s ell, if (I ∩ T).Nonempty then
            d * I.card - ∑ e ∈ I,
              if e ∈ T then w e else 0 else 0) ≤ K := by
      simpa only [T, R5Kernel.dualValue] using hvalue
    have hres : b * (∑ e ∈ T, w e) +
        kernelSupportResidualWeightScaled P T w d ≤ K := by
      exact (Nat.add_le_add_left hresSub _).trans hfull
    have htwice := kernel_supportSurplus_le_scaled_beta_mul_sum_add_residual
      (A := A) (P := P) (B := B) (R := T) (d := d)
      (weights := w) (β := b) (K := K)
      hP (fun I hI => hcompat.1 I (Finset.mem_sdiff.mp hI).1)
      hPcompat hβ hres
    exact htwice
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
      have hzero : supportHits (∅ : Finset (Finset (Fin s))) J = 0 := by
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
      have hzero : supportHits (∅ : Finset (Finset (Fin s))) I = 0 := by
        simp [supportHits]
      rw [hBempty, hzero] at h
      omega
    simp [supportSurplus, supportWeight, supportCross, supportHits, hAempty,
      hBempty]


theorem kernel_supportSurplus_scaled_of_certificates
    {s ell d K : ℕ} {A B : Finset (Finset (Fin s))}
    (hAU : A ⊆ cycleTypes s ell) (hBU : B ⊆ cycleTypes s ell)
    (hcompat : DegreeCompatible A B)
    (hcert : ∀ R : Finset (Fin s), R.Nonempty →
      ∃ b : ℕ, ∃ w : Fin s → ℕ,
        (∀ I ∈ cycleTypes s ell, I ⊆ R → I.card ≤ b) ∧
        R5Kernel.dualValue (cycleTypes s ell) R b d w ≤ K) :
    d * supportSurplus A B ≤ K := by
  obtain ⟨P, hP, hPcompat, hminimal⟩ :=
    kernel_exists_support_minimal_representative hcompat.2
  exact kernel_supportSurplus_scaled_of_minimal
    hAU hBU hcompat hP hPcompat hminimal hcert

theorem kernel_supportSurplus_le_of_cycle_embedding
    {n s ell q : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (htri : G.CliqueFree 3)
    (f : Fin s ↪ Fin n)
    (hrange : Set.range f = residualSet G u v)
    (hAdj : ∀ {x y : Fin s}, (cycleGraph s ell).Adj x y →
      G.Adj (f x) (f y))
    (hcompat : DegreeCompatible (supportFamilyA G u v)
      (supportFamilyB G u v))
    (hbound : ∀ {A B : Finset (Finset (Fin s))},
      A ⊆ cycleTypes s ell → B ⊆ cycleTypes s ell →
      DegreeCompatible A B → supportSurplus A B ≤ q) :
    supportSurplus (supportFamilyA G u v)
      (supportFamilyB G u v) ≤ q := by
  classical
  have hmapsA : kernelFamilyMapsToEmbedding f (supportFamilyA G u v) := by
    intro I hI z hz
    rcases mem_supportFamilyA_iff.mp hI with ⟨x, hx, hIx⟩
    subst I
    rw [hrange]
    exact (mem_residualTypeFinset_iff.mp hz).2
  have hmapsB : kernelFamilyMapsToEmbedding f (supportFamilyB G u v) := by
    intro I hI z hz
    rcases mem_supportFamilyB_iff.mp hI with ⟨x, hx, hIx⟩
    subst I
    rw [hrange]
    exact (mem_residualTypeFinset_iff.mp hz).2
  have hAind : ∀ I ∈ supportFamilyA G u v,
      I.Nonempty ∧ G.IsIndepSet (I : Set (Fin n)) := by
    intro I hI
    exact ⟨supportFamilyA_nonempty hI,
      supportFamilyA_independent htri hI⟩
  have hBind : ∀ I ∈ supportFamilyB G u v,
      I.Nonempty ∧ G.IsIndepSet (I : Set (Fin n)) := by
    intro I hI
    exact ⟨supportFamilyB_nonempty hI,
      supportFamilyB_independent htri hI⟩
  let 𝒜 := kernelPullSupportFamilyEmbedding f (supportFamilyA G u v)
  let ℬ := kernelPullSupportFamilyEmbedding f (supportFamilyB G u v)
  have hAmap : mapSupportFamilyEmbedding f 𝒜 =
      supportFamilyA G u v := by
    simpa [𝒜] using kernel_map_pullSupportFamilyEmbedding_eq f hmapsA
  have hBmap : mapSupportFamilyEmbedding f ℬ =
      supportFamilyB G u v := by
    simpa [ℬ] using kernel_map_pullSupportFamilyEmbedding_eq f hmapsB
  have hAU : 𝒜 ⊆ cycleTypes s ell := by
    intro I hI
    have hI' := kernel_pullSupportFamilyEmbedding_independent_of_graphHom
      (f := f) (K := cycleGraph s ell) (H := G)
      hAdj hAind hmapsA I hI
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI'.1, hI'.2⟩
  have hBU : ℬ ⊆ cycleTypes s ell := by
    intro I hI
    have hI' := kernel_pullSupportFamilyEmbedding_independent_of_graphHom
      (f := f) (K := cycleGraph s ell) (H := G)
      hAdj hBind hmapsB I hI
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI'.1, hI'.2⟩
  have hcomp : DegreeCompatible 𝒜 ℬ := by
    apply kernel_degreeCompatible_of_mapped_certificate f
      (𝒜' := supportFamilyA G u v) (ℬ' := supportFamilyB G u v)
    · exact hAmap.symm
    · exact hBmap.symm
    · exact hcompat
  have hlocal : supportSurplus 𝒜 ℬ ≤ q :=
    hbound hAU hBU hcomp
  calc
    supportSurplus (supportFamilyA G u v) (supportFamilyB G u v) =
        supportSurplus (mapSupportFamilyEmbedding f 𝒜)
          (mapSupportFamilyEmbedding f ℬ) := by rw [hAmap, hBmap]
    _ = supportSurplus 𝒜 ℬ :=
      supportSurplus_mapSupportFamilyEmbedding f 𝒜 ℬ
    _ ≤ q := hlocal

run_cmd R5Kernel.checkStandardAxioms ``kernel_supportSurplus_scaled_of_minimal
run_cmd R5Kernel.checkStandardAxioms ``kernel_supportSurplus_scaled_of_certificates
run_cmd R5Kernel.checkStandardAxioms ``kernel_supportSurplus_le_of_cycle_embedding

end Erdos1011

