import R5Kernel.Parts.M022

/- Source module: Erdos1011.R5CapacityBridge. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_R5CapacityBridge


namespace Erdos1011

open scoped BigOperators

/-! Transport the cycle-capacity estimate across a labelled finite residual.

    The ambient support families live on `Fin t`, while the finite capacity
    table is enumerated on `Fin s`.  The hypotheses deliberately separate
    the two pieces of data supplied by a structural certificate:

    * `hAdj` says that the labelled cycle-model edges occur in the ambient
      graph;
    * `h𝒜'`, `hℬ'`, and the two `familyMapsToEmbedding` hypotheses say that
      every ambient support member is nonempty, independent, and contained in
      the labelled residual.

    The proof then performs all bookkeeping in the kernel: pull back both
    families, use the preceding finite-universe lemma, and transport the
    resulting surplus inequality back to the ambient graph. -/

/-!
The multiplier form of the capacity estimate, specialized to the support
families used for the `r = 5` reduction.  This is the Lean counterpart of
the paper's `k F` inequality; no structural classification is hidden in the
statement.
-/

def cycleCapacitySumK (k s ell p t : ℕ) : ℕ :=
  capacitySumK k (fun I : Finset (Fin s) => I.card)
    (@intersectsFinset s) (cycleTypes s ell) p t s

set_option maxHeartbeats 1000000 in

theorem supportSurplus_le_cycleCapacitySumK
    {k s ell p t : ℕ} {A B : Finset (Finset (Fin s))}
    (hAU : A ⊆ cycleTypes s ell) (hBU : B ⊆ cycleTypes s ell)
    (hAcard : A.card ≤ p)
    (hWA : supportWeight A ≥ t)
    (horder : supportWeight A ≤ supportWeight B)
    (hcompat : DegreeCompatible A B) :
    k * supportSurplus A B ≤
      (k - 1) * supportWeight A + cycleCapacitySumK k s ell p t := by
  letI : DecidableRel (@intersectsFinset s) := intersectsFinset_decidable
  have hcap := capacitySumK_surplus_bound
    (k := k)
    (w := fun I : Finset (Fin s) => I.card)
    (R := @intersectsFinset s) (U := cycleTypes s ell)
    (A := A) (B := B) (p := p) (t := t) (maxW := s)
    hAU hBU hAcard
    (fun J hJ => by simpa using (Finset.card_le_univ J))
    (by simpa [supportWeight, wtSum] using hWA)
    (by simpa [supportWeight, wtSum] using horder)
    (by
      intro J hJ
      have h := hcompat.2 J hJ
      simpa [supportHits, intersectsFinset] using h)
  have hcross :
      (∑ J ∈ B, ∑ I ∈ A, if Disjoint I J then 0 else 1) =
        (∑ J ∈ B, ∑ I ∈ A, if @intersectsFinset s I J then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro J hJ
    apply Finset.sum_congr rfl
    intro I hI
    by_cases hd : Disjoint I J <;> simp [intersectsFinset, hd]
  unfold cycleCapacitySumK supportSurplus supportCross supportHits
  rw [hcross]
  simpa [supportWeight, wtSum] using hcap

/-! Generic form of the multiplier certificate.  Keeping the finite universe
    `U` as an explicit parameter lets the S7 attachment and external-edge
    tables use exactly the same kernel-checked argument as the cycle tables. -/

/-! Pullback transport for an arbitrary finite support universe.  Unlike the
    cycle specialization below, this theorem does not mention a graph: the
    caller supplies the two subset facts for the chosen universe `U`.  This
    is exactly the interface needed by the labelled attachment and
    external-edge tables. -/

/- Direct transport for an externally supplied D1--D4 certificate.  This is
   the data path used when a finite row is too expensive to replay through the
   generic `capacityQ` evaluator: the producer supplies a certificate on the
   pulled-back families, and this theorem handles all ambient relabelling. -/

/- The cycle-universe specialization of the multiplier bridge.  This is the
   form used when a residual row has no useful bound on `B.card` and the
   finite table is replayed with the full cycle universe. -/
set_option maxHeartbeats 1000000 in
theorem supportSurplus_le_cycleCapacitySumK_of_embedding
    {k s t ell p τ : ℕ} (f : Fin s ↪ Fin t)
    {H : SimpleGraph (Fin t)}
    {𝒜' ℬ' : Finset (Finset (Fin t))}
    (hAdj : ∀ {x y : Fin s}, (cycleGraph s ell).Adj x y →
      H.Adj (f x) (f y))
    (h𝒜' : ∀ I ∈ 𝒜', I.Nonempty ∧ H.IsIndepSet (I : Set (Fin t)))
    (hℬ' : ∀ J ∈ ℬ', J.Nonempty ∧ H.IsIndepSet (J : Set (Fin t)))
    (hMapsA : familyMapsToEmbedding f 𝒜')
    (hMapsB : familyMapsToEmbedding f ℬ')
    (hAcard : 𝒜'.card ≤ p)
    (hWA : supportWeight 𝒜' ≥ τ)
    (horder : supportWeight 𝒜' ≤ supportWeight ℬ')
    (hcompat : DegreeCompatible 𝒜' ℬ') :
    k * supportSurplus 𝒜' ℬ' ≤
      (k - 1) * supportWeight 𝒜' + cycleCapacitySumK k s ell p τ := by
  classical
  let 𝒜 := pullSupportFamilyEmbedding f 𝒜'
  let ℬ := pullSupportFamilyEmbedding f ℬ'
  have hAmap : mapSupportFamilyEmbedding f 𝒜 = 𝒜' := by
    simpa [𝒜] using map_pullSupportFamilyEmbedding_eq f hMapsA
  have hBmap : mapSupportFamilyEmbedding f ℬ = ℬ' := by
    simpa [ℬ] using map_pullSupportFamilyEmbedding_eq f hMapsB
  have hAU : 𝒜 ⊆ cycleTypes s ell := by
    intro I hI
    have hI' := pullSupportFamilyEmbedding_independent_of_graphHom
      (f := f) (K := cycleGraph s ell) (H := H) hAdj h𝒜' hMapsA I hI
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI'.1, hI'.2⟩
  have hBU : ℬ ⊆ cycleTypes s ell := by
    intro I hI
    have hI' := pullSupportFamilyEmbedding_independent_of_graphHom
      (f := f) (K := cycleGraph s ell) (H := H) hAdj hℬ' hMapsB I hI
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI'.1, hI'.2⟩
  have hAcard' : 𝒜.card ≤ p := by
    rw [← mapSupportFamilyEmbedding_card f 𝒜, hAmap]
    exact hAcard
  have hWA' : supportWeight 𝒜 ≥ τ := by
    rw [← supportWeight_mapSupportFamilyEmbedding f 𝒜, hAmap]
    exact hWA
  have horder' : supportWeight 𝒜 ≤ supportWeight ℬ := by
    rw [← supportWeight_mapSupportFamilyEmbedding f 𝒜,
      ← supportWeight_mapSupportFamilyEmbedding f ℬ, hAmap, hBmap]
    exact horder
  have hcompat' : DegreeCompatible 𝒜 ℬ := by
    apply degreeCompatible_of_mapped_certificate f
      (𝒜' := 𝒜') (ℬ' := ℬ')
    · exact hAmap.symm
    · exact hBmap.symm
    · exact hcompat
  have hfinite := supportSurplus_le_cycleCapacitySumK
    (k := k) (s := s) (ell := ell) (p := p) (t := τ)
    hAU hBU hAcard' hWA' horder' hcompat'
  calc
    k * supportSurplus 𝒜' ℬ' =
        k * supportSurplus (mapSupportFamilyEmbedding f 𝒜)
          (mapSupportFamilyEmbedding f ℬ) := by rw [hAmap, hBmap]
    _ = k * supportSurplus 𝒜 ℬ := by
      rw [supportSurplus_mapSupportFamilyEmbedding]
    _ ≤ (k - 1) * supportWeight 𝒜 +
        cycleCapacitySumK k s ell p τ := hfinite
    _ = (k - 1) * supportWeight 𝒜' +
        cycleCapacitySumK k s ell p τ := by
      rw [← supportWeight_mapSupportFamilyEmbedding f 𝒜, hAmap]

/- A coarse but completely generic fallback: once the left support family is
   known to lie in a finite universe, its surplus is bounded by the total
   universe weight.  This is the kernel form of the q-values used for the
   s=7,...,11 coarse branches. -/
end Erdos1011

end Web_Erdos1011_R5CapacityBridge
