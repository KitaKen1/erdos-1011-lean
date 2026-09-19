import R5Kernel.Parts.M013

/- Source module: Erdos1011.SupportEquiv. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_SupportEquiv


namespace Erdos1011

open scoped BigOperators

/- Reindexing a support family along an equivalence preserves all numerical
   quantities used in the capacity argument.  These lemmas isolate the
   bookkeeping needed to transport the finite `Fin 6` tables to an arbitrary
   six-vertex residual graph. -/

/- The same transport works for a non-surjective embedding, which is the
   form needed when a six-vertex residual set sits inside an n-vertex graph. -/
noncomputable def mapSupportFamilyEmbedding {s t : ℕ} (f : Fin s ↪ Fin t)
    (𝒜 : Finset (Finset (Fin s))) : Finset (Finset (Fin t)) := by
  classical
  exact 𝒜.image (fun I => I.map f)

theorem mapSupportFamilyEmbedding_map_injective {s t : ℕ} (f : Fin s ↪ Fin t) :
    Function.Injective (fun I : Finset (Fin s) => I.map f) := by
  exact Finset.map_injective f

theorem mapSupportFamilyEmbedding_map_injOn {s t : ℕ} (f : Fin s ↪ Fin t)
    (𝒜 : Finset (Finset (Fin s))) :
    Set.InjOn (fun I : Finset (Fin s) => I.map f) (𝒜 : Set _) := by
  intro I hI J hJ hIJ
  exact mapSupportFamilyEmbedding_map_injective f hIJ

theorem mapSupportFamilyEmbedding_card {s t : ℕ} (f : Fin s ↪ Fin t)
    (𝒜 : Finset (Finset (Fin s))) :
    (mapSupportFamilyEmbedding f 𝒜).card = 𝒜.card := by
  classical
  unfold mapSupportFamilyEmbedding
  exact Finset.card_image_of_injective _ (mapSupportFamilyEmbedding_map_injective f)

theorem supportWeight_mapSupportFamilyEmbedding {s t : ℕ} (f : Fin s ↪ Fin t)
    (𝒜 : Finset (Finset (Fin s))) :
    supportWeight (mapSupportFamilyEmbedding f 𝒜) = supportWeight 𝒜 := by
  classical
  unfold supportWeight mapSupportFamilyEmbedding
  rw [Finset.sum_image (mapSupportFamilyEmbedding_map_injOn f 𝒜)]
  simp [Finset.card_map]

theorem mapSupportFamilyEmbedding_disjoint_iff {s t : ℕ} (f : Fin s ↪ Fin t)
    (I J : Finset (Fin s)) :
    Disjoint (I.map f) (J.map f) ↔ Disjoint I J := by
  exact Finset.disjoint_map f

theorem supportHits_mapSupportFamilyEmbedding {s t : ℕ} (f : Fin s ↪ Fin t)
    (𝒜 : Finset (Finset (Fin s))) (I : Finset (Fin s)) :
    supportHits (mapSupportFamilyEmbedding f 𝒜) (I.map f) =
      supportHits 𝒜 I := by
  classical
  unfold supportHits mapSupportFamilyEmbedding
  rw [Finset.sum_image (mapSupportFamilyEmbedding_map_injOn f 𝒜)]
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [mapSupportFamilyEmbedding_disjoint_iff]

theorem supportCross_mapSupportFamilyEmbedding {s t : ℕ} (f : Fin s ↪ Fin t)
    (𝒜 ℬ : Finset (Finset (Fin s))) :
    supportCross (mapSupportFamilyEmbedding f 𝒜)
        (mapSupportFamilyEmbedding f ℬ) = supportCross 𝒜 ℬ := by
  classical
  unfold supportCross
  rw [show mapSupportFamilyEmbedding f ℬ =
      ℬ.image (fun I => I.map f) by rfl]
  rw [Finset.sum_image (mapSupportFamilyEmbedding_map_injOn f ℬ)]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [supportHits_mapSupportFamilyEmbedding]

theorem supportSurplus_mapSupportFamilyEmbedding {s t : ℕ} (f : Fin s ↪ Fin t)
    (𝒜 ℬ : Finset (Finset (Fin s))) :
    supportSurplus (mapSupportFamilyEmbedding f 𝒜)
        (mapSupportFamilyEmbedding f ℬ) = supportSurplus 𝒜 ℬ := by
  unfold supportSurplus
  rw [supportWeight_mapSupportFamilyEmbedding,
    supportWeight_mapSupportFamilyEmbedding,
    supportCross_mapSupportFamilyEmbedding]

end Erdos1011

end Web_Erdos1011_SupportEquiv
