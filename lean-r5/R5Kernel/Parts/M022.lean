import R5Kernel.Parts.M021

/- Source module: Erdos1011.SupportPull. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_SupportPull


namespace Erdos1011

/-! Pull a support family back along an embedding, assuming that every member
    of the family is contained in the image of that embedding.  This is the
    bookkeeping needed to turn a residual set with a chosen finite labelling
    into a family on `Fin s`. -/

def familyMapsToEmbedding {s t : ℕ} (f : Fin s ↪ Fin t)
    (𝒜' : Finset (Finset (Fin t))) : Prop :=
  ∀ I ∈ 𝒜', ∀ x ∈ I, x ∈ Set.range f

noncomputable def pullSupportFamilyEmbedding {s t : ℕ} (f : Fin s ↪ Fin t)
    (𝒜' : Finset (Finset (Fin t))) : Finset (Finset (Fin s)) := by
  classical
  exact 𝒜'.image (fun I => I.preimage f f.injective.injOn)

theorem map_preimage_support_eq
    {s t : ℕ} (f : Fin s ↪ Fin t)
    {I : Finset (Fin t)}
    (hI : ∀ x ∈ I, x ∈ Set.range f) :
    (I.preimage f f.injective.injOn).map f = I := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_map.1 hx with ⟨y, hy, rfl⟩
    exact Finset.mem_preimage.1 hy
  · intro hx
    obtain ⟨y, rfl⟩ := hI x hx
    apply Finset.mem_map.2
    refine ⟨y, Finset.mem_preimage.2 ?_, rfl⟩
    exact hx

theorem map_pullSupportFamilyEmbedding_eq
    {s t : ℕ} (f : Fin s ↪ Fin t)
    {𝒜' : Finset (Finset (Fin t))}
    (h𝒜' : familyMapsToEmbedding f 𝒜') :
    mapSupportFamilyEmbedding f (pullSupportFamilyEmbedding f 𝒜') = 𝒜' := by
  classical
  ext I
  constructor
  · intro hI
    rcases Finset.mem_image.1 hI with ⟨J, hJ, hJI⟩
    rcases Finset.mem_image.1 hJ with ⟨K, hK, hKJ⟩
    have hKmap : J.map f = K := by
      rw [← hKJ]
      exact map_preimage_support_eq f (h𝒜' K hK)
    have : K = I := by
      exact hKmap.symm.trans hJI
    simpa [this] using hK
  · intro hI
    apply Finset.mem_image.2
    refine ⟨I.preimage f f.injective.injOn, ?_, ?_⟩
    · apply Finset.mem_image.2
      exact ⟨I, hI, rfl⟩
    · exact map_preimage_support_eq f (h𝒜' I hI)

theorem degreeCompatible_of_mapped_certificate
    {s t : ℕ} (f : Fin s ↪ Fin t)
    {𝒜 ℬ : Finset (Finset (Fin s))}
    {𝒜' ℬ' : Finset (Finset (Fin t))}
    (h𝒜eq : 𝒜' = mapSupportFamilyEmbedding f 𝒜)
    (hℬeq : ℬ' = mapSupportFamilyEmbedding f ℬ)
    (hcompat : DegreeCompatible 𝒜' ℬ') :
    DegreeCompatible 𝒜 ℬ := by
  constructor
  · intro I hI
    have hImap : I.map f ∈ 𝒜' := by
      rw [h𝒜eq]
      exact Finset.mem_image.2 ⟨I, hI, rfl⟩
    have hle := hcompat.1 (I.map f) hImap
    have hhit : supportHits ℬ' (I.map f) = supportHits ℬ I := by
      rw [hℬeq]
      exact supportHits_mapSupportFamilyEmbedding f ℬ I
    simpa [Finset.card_map, hhit] using hle
  · intro J hJ
    have hJmap : J.map f ∈ ℬ' := by
      rw [hℬeq]
      exact Finset.mem_image.2 ⟨J, hJ, rfl⟩
    have hle := hcompat.2 (J.map f) hJmap
    have hhit : supportHits 𝒜' (J.map f) = supportHits 𝒜 J := by
      rw [h𝒜eq]
      exact supportHits_mapSupportFamilyEmbedding f 𝒜 J
    simpa [Finset.card_map, hhit] using hle

/-! If a labelled finite model has all of its edges present in the ambient
    graph, then pulling a family back along the labelling preserves the
    nonempty-independent support certificate.  This is the graph-theoretic
    half of the finite-model transport; numerical quantities are handled by
    `SupportEquiv` above. -/
theorem pullSupportFamilyEmbedding_independent_of_graphHom
    {s t : ℕ} (f : Fin s ↪ Fin t) {K : SimpleGraph (Fin s)}
    {H : SimpleGraph (Fin t)}
    (hAdj : ∀ {x y : Fin s}, K.Adj x y → H.Adj (f x) (f y))
    {𝒜' : Finset (Finset (Fin t))}
    (h𝒜' : ∀ I ∈ 𝒜', I.Nonempty ∧ H.IsIndepSet (I : Set (Fin t)))
    (hMaps : familyMapsToEmbedding f 𝒜') :
    ∀ I ∈ pullSupportFamilyEmbedding f 𝒜',
      I.Nonempty ∧ K.IsIndepSet (I : Set (Fin s)) := by
  classical
  intro I hI
  rcases Finset.mem_image.mp hI with ⟨J, hJ, rfl⟩
  have hJ' := h𝒜' J hJ
  have hnon : (J.preimage f f.injective.injOn).Nonempty := by
    rcases hJ'.1 with ⟨w, hw⟩
    rcases hMaps J hJ w hw with ⟨z, rfl⟩
    exact ⟨z, Finset.mem_preimage.mpr hw⟩
  refine ⟨hnon, ?_⟩
  intro a ha b hb hab hKadj
  have hJa : f a ∈ J := Finset.mem_preimage.mp ha
  have hJb : f b ∈ J := Finset.mem_preimage.mp hb
  have hne : f a ≠ f b := by
    intro heq
    exact hab (f.injective heq)
  exact hJ'.2 hJa hJb hne (hAdj hKadj)

end Erdos1011

end Web_Erdos1011_SupportPull
