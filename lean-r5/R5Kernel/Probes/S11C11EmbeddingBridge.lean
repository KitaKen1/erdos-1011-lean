import R5Kernel.Probes.S11C11SurplusBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1
set_option maxRecDepth 200000

open Lean Elab Command

namespace Erdos1011

def kernelFamilyMapsToEmbedding {s t : ℕ} (f : Fin s ↪ Fin t)
    (𝒜' : Finset (Finset (Fin t))) : Prop :=
  ∀ I ∈ 𝒜', ∀ x ∈ I, x ∈ Set.range f

noncomputable def kernelPullSupportFamilyEmbedding {s t : ℕ} (f : Fin s ↪ Fin t)
    (𝒜' : Finset (Finset (Fin t))) : Finset (Finset (Fin s)) := by
  classical
  exact 𝒜'.image (fun I => I.preimage f f.injective.injOn)

theorem kernel_map_preimage_support_eq
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

theorem kernel_map_pullSupportFamilyEmbedding_eq
    {s t : ℕ} (f : Fin s ↪ Fin t)
    {𝒜' : Finset (Finset (Fin t))}
    (h𝒜' : kernelFamilyMapsToEmbedding f 𝒜') :
    mapSupportFamilyEmbedding f (kernelPullSupportFamilyEmbedding f 𝒜') = 𝒜' := by
  classical
  ext I
  constructor
  · intro hI
    rcases Finset.mem_image.1 hI with ⟨J, hJ, hJI⟩
    rcases Finset.mem_image.1 hJ with ⟨K, hK, hKJ⟩
    have hKmap : J.map f = K := by
      rw [← hKJ]
      exact kernel_map_preimage_support_eq f (h𝒜' K hK)
    have : K = I := hKmap.symm.trans hJI
    simpa [this] using hK
  · intro hI
    apply Finset.mem_image.2
    refine ⟨I.preimage f f.injective.injOn, ?_, ?_⟩
    · apply Finset.mem_image.2
      exact ⟨I, hI, rfl⟩
    · exact kernel_map_preimage_support_eq f (h𝒜' I hI)

theorem kernel_degreeCompatible_of_mapped_certificate
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

theorem kernel_pullSupportFamilyEmbedding_independent_of_graphHom
    {s t : ℕ} (f : Fin s ↪ Fin t) {K : SimpleGraph (Fin s)}
    {H : SimpleGraph (Fin t)}
    (hAdj : ∀ {x y : Fin s}, K.Adj x y → H.Adj (f x) (f y))
    {𝒜' : Finset (Finset (Fin t))}
    (h𝒜' : ∀ I ∈ 𝒜', I.Nonempty ∧ H.IsIndepSet (I : Set (Fin t)))
    (hMaps : kernelFamilyMapsToEmbedding f 𝒜') :
    ∀ I ∈ kernelPullSupportFamilyEmbedding f 𝒜',
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

set_option maxHeartbeats 20000000 in
theorem kernel_c11_supportSurplus_le_103_of_cycle_embedding
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n} (htri : G.CliqueFree 3)
    (f : Fin 11 ↪ Fin n)
    (hrange : Set.range f = residualSet G u v)
    (hAdj : ∀ {x y : Fin 11}, (cycleGraph 11 11).Adj x y →
      G.Adj (f x) (f y))
    (hcompat : DegreeCompatible (supportFamilyA G u v)
      (supportFamilyB G u v)) :
    supportSurplus (supportFamilyA G u v)
      (supportFamilyB G u v) ≤ 103 := by
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
  have hAU : 𝒜 ⊆ cycleTypes 11 11 := by
    intro I hI
    have hI' := kernel_pullSupportFamilyEmbedding_independent_of_graphHom
      (f := f) (K := cycleGraph 11 11) (H := G)
      hAdj hAind hmapsA I hI
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI'.1, hI'.2⟩
  have hBU : ℬ ⊆ cycleTypes 11 11 := by
    intro I hI
    have hI' := kernel_pullSupportFamilyEmbedding_independent_of_graphHom
      (f := f) (K := cycleGraph 11 11) (H := G)
      hAdj hBind hmapsB I hI
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI'.1, hI'.2⟩
  have hcomp : DegreeCompatible 𝒜 ℬ := by
    apply kernel_degreeCompatible_of_mapped_certificate f
      (𝒜' := supportFamilyA G u v) (ℬ' := supportFamilyB G u v)
    · exact hAmap.symm
    · exact hBmap.symm
    · exact hcompat
  have hlocal : supportSurplus 𝒜 ℬ ≤ 103 :=
    kernel_c11_supportSurplus_le_103 hAU hBU hcomp
  calc
    supportSurplus (supportFamilyA G u v) (supportFamilyB G u v) =
        supportSurplus (mapSupportFamilyEmbedding f 𝒜)
          (mapSupportFamilyEmbedding f ℬ) := by rw [hAmap, hBmap]
    _ = supportSurplus 𝒜 ℬ :=
      supportSurplus_mapSupportFamilyEmbedding f 𝒜 ℬ
    _ ≤ 103 := hlocal

run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_supportSurplus_le_103_of_cycle_embedding

end Erdos1011
