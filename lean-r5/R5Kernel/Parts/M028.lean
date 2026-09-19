import R5Kernel.Parts.M027

/- Source module: Erdos1011.R5S6Support. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_R5S6Support


namespace Erdos1011

open SimpleGraph

/-! Graph-to-table transport for the remaining `s = 6` branch.  The finite
    table in `S6Capacity` is stated using the relation `s6c5Adj`; this file
    proves that any actual support family whose residual graph is labelled by
    `C₅ ⊔ K₁` pulls back into precisely that finite support universe.  The
    mandatory `T`-family and V/D-count are intentionally separate hypotheses:
    this layer does not silently assume that the extremal graph realizes them. -/

def s6c5Graph : SimpleGraph (Fin 6) := SimpleGraph.fromRel s6c5Adj

instance s6c5Graph_decidable : DecidableRel s6c5Graph.Adj := by
  intro x y
  change Decidable (x ≠ y ∧ (s6c5Adj x y ∨ s6c5Adj y x))
  infer_instance

theorem s6c5Adj_implies_graph_adj {x y : Fin 6}
    (hxy : s6c5Adj x y) : s6c5Graph.Adj x y := by
  change x ≠ y ∧ (s6c5Adj x y ∨ s6c5Adj y x)
  have hne : x ≠ y := by
    intro h
    subst y
    unfold s6c5Adj at hxy
    omega
  exact ⟨hne, Or.inl hxy⟩

/- The particular T-type singled out by the first six-vertex colouring.  The
   name is public here because `S6Capacity` keeps its table entries private. -/
def s6T0 : Finset (Fin 6) := {5, 4, 1}

def s6CoreColorT0 (x : Fin 6) : Fin 3 :=
  if x.val = 0 then 2 else if x.val = 1 then 0
  else if x.val = 2 then 1 else if x.val = 3 then 0
  else if x.val = 4 then 1 else 2

/- Every independent set other than T₀ sees at most two colours in this
   colouring.  This is the finite statement used to force T₀ on each side. -/

def s6Prev (i : Fin 5) : Fin 5 :=
  ⟨(i.val + 4) % 5, Nat.mod_lt _ (by omega)⟩

def s6Embed5 (i : Fin 5) : Fin 6 := ⟨i.val, by omega⟩

def s6Ti (i : Fin 5) : Finset (Fin 6) :=
  {5, s6Embed5 (s6Prev i), s6Embed5 (s6Next i)}

def s6ShiftBack (i : Fin 5) (x : Fin 6) : Fin 6 :=
  if x.val < 5 then
    ⟨(x.val + 5 - i.val) % 5, by omega⟩
  else 5

def s6CoreColorTi (i : Fin 5) (x : Fin 6) : Fin 3 :=
  s6CoreColorT0 (s6ShiftBack i x)

theorem s6TFamily_eq_image_s6Ti :
    s6TFamily = (Finset.univ : Finset (Fin 5)).image s6Ti := by
  decide +kernel

theorem s6CoreColorTi_proper :
    ∀ i : Fin 5, ∀ x y : Fin 6, s6c5Graph.Adj x y →
      s6CoreColorTi i x ≠ s6CoreColorTi i y := by
  decide +kernel +revert

theorem s6CoreColorTi_nonTi_image_le_two :
    ∀ i : Fin 5, ∀ I : Finset (Fin 6), s6c5Independent I →
      I ≠ s6Ti i → (I.image (s6CoreColorTi i)).card ≤ 2 := by
  decide +kernel +revert

/- Rotate the four-colour table back to the unrotated one.  The same shift
   used for the Tᵢ colourings is injective on `Fin 6`, so it can map support
   finsets. -/
theorem s6ShiftBack_injective : ∀ j : Fin 5, Function.Injective (s6ShiftBack j) := by
  decide +kernel +revert

def s6ShiftBackEmbedding (j : Fin 5) : Fin 6 ↪ Fin 6 :=
  ⟨s6ShiftBack j, s6ShiftBack_injective j⟩

def s6CoreColorJ (j : Fin 5) (x : Fin 6) : Fin 4 :=
  s6CoreColor0 (s6ShiftBack j x)

def s6AColorJ (j : Fin 5) (I : Finset (Fin 6)) : Fin 4 :=
  s6AColor0 (I.map (s6ShiftBackEmbedding j))

def s6BColorJ (j : Fin 5) (I : Finset (Fin 6)) : Fin 4 :=
  s6BColor0 (I.map (s6ShiftBackEmbedding j))

def s6VType (j : Fin 5) : Finset (Fin 6) := {s6Embed5 j}

def s6DType (j : Fin 5) : Finset (Fin 6) :=
  {s6Embed5 (s6Prev j), s6Embed5 (s6Next j)}

def s6ForbiddenAType (j : Fin 5) : Finset (Finset (Fin 6)) :=
  {s6VType j, s6DType (s6Next j)}

def s6ForbiddenBType (j : Fin 5) : Finset (Finset (Fin 6)) :=
  {s6VType (s6Next j), s6DType j}

theorem s6_table_core_J_proper :
    ∀ j : Fin 5, ∀ x y : Fin 6, s6c5Graph.Adj x y →
      s6CoreColorJ j x ≠ s6CoreColorJ j y := by
  decide +kernel +revert

theorem s6_table_A_core_J_compatible :
    ∀ j : Fin 5, ∀ I : Finset (Fin 6), I ∈ s6Supports →
      I ∉ s6ForbiddenAType j → ∀ x ∈ I,
        s6CoreColorJ j x ≠ s6AColorJ j I := by
  decide +kernel +revert

theorem s6_table_B_core_J_compatible :
    ∀ j : Fin 5, ∀ I : Finset (Fin 6), I ∈ s6Supports →
      I ∉ s6ForbiddenBType j → ∀ x ∈ I,
        s6CoreColorJ j x ≠ s6BColorJ j I := by
  decide +kernel +revert

theorem s6_table_cross_J_compatible :
    ∀ j : Fin 5, ∀ I J : Finset (Fin 6), I ∈ s6Supports →
      J ∈ s6Supports → I ∉ s6ForbiddenAType j → J ∉ s6ForbiddenBType j →
      Disjoint I J → s6AColorJ j I ≠ s6BColorJ j J := by
  decide +kernel +revert

theorem s6_table_A_colorJ_ne_one :
    ∀ j : Fin 5, ∀ I : Finset (Fin 6), I ∈ s6Supports →
      I ∉ s6ForbiddenAType j → s6AColorJ j I ≠ 1 := by
  decide +kernel +revert

theorem s6_table_B_colorJ_ne_zero :
    ∀ j : Fin 5, ∀ I : Finset (Fin 6), I ∈ s6Supports →
      I ∉ s6ForbiddenBType j → s6BColorJ j I ≠ 0 := by
  decide +kernel +revert

theorem s6_vd_disjoint_T : Disjoint s6VDFamily s6TFamily := by
  decide +kernel

theorem s6_forbiddenA_type_code :
    ∀ j : Fin 5, ∀ I : Finset (Fin 6),
      I ∈ s6ForbiddenAType j → s6VDCode I ∈ s6ForbiddenA j := by
  decide +kernel +revert

theorem s6_forbiddenB_type_code :
    ∀ j : Fin 5, ∀ I : Finset (Fin 6),
      I ∈ s6ForbiddenBType j → s6VDCode I ∈ s6ForbiddenB j := by
  decide +kernel +revert

theorem s6VType_mem_VDFamily : ∀ j : Fin 5, s6VType j ∈ s6VDFamily := by
  decide +kernel +revert

theorem s6DType_mem_VDFamily : ∀ j : Fin 5, s6DType j ∈ s6VDFamily := by
  decide +kernel +revert

theorem s6_vd_index_card_eq_indicator_sum
    (𝒜 : Finset (Finset (Fin 6))) :
    (s6VDIndexFamily 𝒜).card =
      ∑ I ∈ 𝒜 \ s6TFamily, if I ∈ s6VDFamily then 1 else 0 := by
  have hfilter : 𝒜.filter (fun I => I ∈ s6VDFamily) =
      (𝒜 \ s6TFamily).filter (fun I => I ∈ s6VDFamily) := by
    ext I
    constructor
    · intro hI
      have h := Finset.mem_filter.mp hI
      have hnotT : I ∉ s6TFamily := by
        intro hT
        exact (Finset.disjoint_left.mp s6_vd_disjoint_T h.2 hT)
      exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨h.1, hnotT⟩, h.2⟩
    · intro hI
      have h := Finset.mem_filter.mp hI
      exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp h.1).1, h.2⟩
  rw [s6VDIndexFamily_card, hfilter, Finset.card_filter]

theorem s6_vd_rotation_avoids_of_indicator_sum_le_four
    {𝒜 ℬ : Finset (Finset (Fin 6))}
    (hcount :
      (∑ I ∈ 𝒜 \ s6TFamily, if I ∈ s6VDFamily then 1 else 0) +
      (∑ J ∈ ℬ \ s6TFamily, if J ∈ s6VDFamily then 1 else 0) ≤ 4) :
    ∃ j : Fin 5,
      Disjoint (s6VDIndexFamily 𝒜) (s6ForbiddenA j) ∧
      Disjoint (s6VDIndexFamily ℬ) (s6ForbiddenB j) := by
  apply s6_vd_rotation_cover
  rw [s6_vd_index_card_eq_indicator_sum, s6_vd_index_card_eq_indicator_sum]
  exact hcount

theorem s6_vd_rotation_type_avoids
    {𝒜 ℬ : Finset (Finset (Fin 6))}
    {j : Fin 5}
    (hA : Disjoint (s6VDIndexFamily 𝒜) (s6ForbiddenA j))
    (hB : Disjoint (s6VDIndexFamily ℬ) (s6ForbiddenB j)) :
    (∀ I ∈ 𝒜, I ∉ s6ForbiddenAType j) ∧
      (∀ I ∈ ℬ, I ∉ s6ForbiddenBType j) := by
  constructor
  · intro I hI hfor
    have hforcode := s6_forbiddenA_type_code j I hfor
    have hIvd : I ∈ s6VDFamily := by
      rcases Finset.mem_insert.mp hfor with h | h
      · subst I
        exact s6VType_mem_VDFamily j
      · rcases Finset.mem_singleton.mp h with rfl
        exact s6DType_mem_VDFamily (s6Next j)
    have hidx : s6VDCode I ∈ s6VDIndexFamily 𝒜 := by
      unfold s6VDIndexFamily
      exact Finset.mem_image.mpr ⟨I,
        Finset.mem_filter.mpr ⟨hI, hIvd⟩, rfl⟩
    exact (Finset.disjoint_left.mp hA hidx) hforcode
  · intro I hI hfor
    have hforcode := s6_forbiddenB_type_code j I hfor
    have hIvd : I ∈ s6VDFamily := by
      rcases Finset.mem_insert.mp hfor with h | h
      · subst I
        exact s6VType_mem_VDFamily (s6Next j)
      · rcases Finset.mem_singleton.mp h with rfl
        exact s6DType_mem_VDFamily j
    have hidx : s6VDCode I ∈ s6VDIndexFamily ℬ := by
      unfold s6VDIndexFamily
      exact Finset.mem_image.mpr ⟨I,
        Finset.mem_filter.mpr ⟨hI, hIvd⟩, rfl⟩
    exact (Finset.disjoint_left.mp hB hidx) hforcode

/- A graph isomorphism from the residual induced graph to `C₅ ⊔ K₁`
   canonically gives an embedding of the six model vertices back into the
   ambient `Fin n` vertex type. -/
noncomputable def residualSixEmbeddingOfC5Iso
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (e : (G.induce (residualSet G u v)) ≃g s6c5Graph) : Fin 6 ↪ Fin n :=
  e.symm.toEquiv.toEmbedding.trans (Function.Embedding.subtype _)

theorem residualSixEmbeddingOfC5Iso_mem
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (e : (G.induce (residualSet G u v)) ≃g s6c5Graph) (i : Fin 6) :
    residualSixEmbeddingOfC5Iso e i ∈ residualSet G u v := by
  exact (e.symm.toEquiv i).property

theorem residualSixEmbeddingOfC5Iso_range
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (e : (G.induce (residualSet G u v)) ≃g s6c5Graph) :
    Set.range (residualSixEmbeddingOfC5Iso e) = residualSet G u v := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact residualSixEmbeddingOfC5Iso_mem e i
  · intro hx
    let y : residualSet G u v := ⟨x, hx⟩
    refine ⟨e.toEquiv y, ?_⟩
    dsimp [residualSixEmbeddingOfC5Iso]
    simp [y]

theorem residualSixEmbeddingOfC5Iso_graph
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (e : (G.induce (residualSet G u v)) ≃g s6c5Graph) :
    ∀ x y : Fin 6,
      G.Adj (residualSixEmbeddingOfC5Iso e x)
        (residualSixEmbeddingOfC5Iso e y) ↔ s6c5Graph.Adj x y := by
  intro x y
  change (G.induce (residualSet G u v)).Adj
      (e.symm.toEquiv x) (e.symm.toEquiv y) ↔ s6c5Graph.Adj x y
  exact e.symm.map_rel_iff

noncomputable def residualSetSwapEquiv
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    residualSet G v u ≃ residualSet G u v :=
  Equiv.subtypeEquivProp <| (residualSet_swap G u v) ▸ rfl

noncomputable def residualInducedSwapIso
    {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    (G.induce (residualSet G v u)) ≃g (G.induce (residualSet G u v)) :=
  { toEquiv := residualSetSwapEquiv G u v
    map_rel_iff' := by
      intro x y
      simp only [SimpleGraph.induce_adj]
      rfl }

/- If the distinguished T₀ support is absent on the B-side, the explicit
   residual colouring above supplies a missing colour for every B-type.  The
   general extension lemma then gives a 4-colouring of the ambient graph. -/
theorem r5_s6_c5_isolated_four_colorable_of_support_absent
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (htri : G.CliqueFree 3) {u v : Fin n} (huv : G.Adj u v)
    (e : (G.induce (residualSet G u v)) ≃g s6c5Graph)
    (T₀ : Finset (Fin 6)) (c₀ : Fin 6 → Fin 3)
    (hcproper : ∀ x y : Fin 6, s6c5Graph.Adj x y → c₀ x ≠ c₀ y)
    (hcnonT : ∀ I : Finset (Fin 6), s6c5Independent I → I ≠ T₀ →
      (I.image c₀).card ≤ 2)
    (hnot : T₀ ∉
      pullSupportFamilyEmbedding (residualSixEmbeddingOfC5Iso e)
        (supportFamilyB G u v)) :
    G.Colorable 4 := by
  classical
  let f := residualSixEmbeddingOfC5Iso e
  let cRes : residualSet G u v → Fin 3 :=
    fun z => c₀ (e.toEquiv z)
  have hcRes : ∀ {x y : residualSet G u v},
      (G.induce (residualSet G u v)).Adj x y → cRes x ≠ cRes y := by
    intro x y hxy
    exact hcproper _ _ ((e.map_rel_iff).mpr hxy)
  let C : (G.induce (residualSet G u v)).Coloring (Fin 3) :=
    Coloring.mk cRes hcRes
  have hmissing : ∀ y, y ∈ edgeSideBSet G u v →
      ∃ d : Fin 3, ∀ z : residualSet G u v,
        (z : Fin n) ∈ residualType G u v y → C z ≠ d := by
    intro y hy
    by_cases hnon : (residualType G u v y).Nonempty
    · let I : Finset (Fin n) := residualTypeFinset G u v y
      have hIy : I ∈ supportFamilyB G u v := by
        apply mem_supportFamilyB_iff.mpr
        refine ⟨y, ?_, rfl⟩
        exact mem_nonemptyBTypeVertices_iff.mpr ⟨hy, hnon⟩
      let J : Finset (Fin 6) := I.preimage f f.injective.injOn
      have hJpull : J ∈ pullSupportFamilyEmbedding f
          (supportFamilyB G u v) := by
        exact Finset.mem_image.mpr ⟨I, hIy, rfl⟩
      have hJnot : J ≠ T₀ := by
        intro hEq
        apply hnot
        rw [← hEq]
        exact hJpull
      have hJind : s6c5Independent J := by
        intro a ha b hb hab
        have ha' : f a ∈ I := Finset.mem_preimage.mp ha
        have hb' : f b ∈ I := Finset.mem_preimage.mp hb
        intro hab6
        have hGadj : G.Adj (f a) (f b) :=
          (residualSixEmbeddingOfC5Iso_graph e a b).mpr
            (s6c5Adj_implies_graph_adj hab6)
        exact (supportFamilyB_independent htri hIy) ha' hb'
          (fun h => hab (f.injective h)) hGadj
      have hJcard := hcnonT J hJind hJnot
      let T : Set (residualSet G u v) :=
        (fun z : residualSet G u v => (z : Fin n)) ⁻¹'
          residualType G u v y
      let hTfinite : T.Finite := Set.toFinite T
      let IT : Finset (residualSet G u v) := hTfinite.toFinset
      have himagesub : IT.image (fun z => C z) ⊆ J.image c₀ := by
        intro d hd
        rcases Finset.mem_image.mp hd with ⟨z, hz, rfl⟩
        have hzT : z ∈ T := hTfinite.mem_toFinset.mp hz
        change (z : Fin n) ∈ residualType G u v y at hzT
        have hzres : (z : Fin n) ∈ residualSet G u v :=
          hzT.2
        have hzrange : (z : Fin n) ∈ Set.range f := by
          rw [residualSixEmbeddingOfC5Iso_range e]
          exact hzres
        obtain ⟨a, ha⟩ := hzrange
        have hza : z = e.symm.toEquiv a := by
          apply Subtype.ext
          exact ha.symm
        have heqa : e.toEquiv z = a := by
          rw [hza]
          simp
        have hzI : (z : Fin n) ∈ I := by
          exact mem_residualTypeFinset_iff.mpr hzT
        have haI : f a ∈ I := by simpa [ha] using hzI
        have haJ : a ∈ J := Finset.mem_preimage.mpr haI
        apply Finset.mem_image.mpr
        refine ⟨a, haJ, ?_⟩
        change c₀ a = c₀ (e.toEquiv z)
        rw [heqa]
      have hcard : (IT.image (fun z => C z)).card ≤ 2 :=
        (Finset.card_le_card himagesub).trans hJcard
      obtain ⟨d, hd⟩ :=
        exists_fin3_color_avoiding_of_image_card_le_two
          (fun z : residualSet G u v => C z) hTfinite (by simpa [IT] using hcard)
      refine ⟨d, ?_⟩
      intro z hz
      exact hd z hz
    · refine ⟨0, ?_⟩
      intro z hz
      exfalso
      exact hnon ⟨(z : Fin n), hz⟩
  exact colorable_four_of_residual_missing_color htri huv C hmissing

theorem r5_s6_c5_isolated_four_colorable_of_Ti_absent
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (htri : G.CliqueFree 3) {u v : Fin n} (huv : G.Adj u v)
    (e : (G.induce (residualSet G u v)) ≃g s6c5Graph) (i : Fin 5)
    (hnot : s6Ti i ∉
      pullSupportFamilyEmbedding (residualSixEmbeddingOfC5Iso e)
        (supportFamilyB G u v)) :
    G.Colorable 4 := by
  exact r5_s6_c5_isolated_four_colorable_of_support_absent htri huv e
    (s6Ti i) (s6CoreColorTi i) (s6CoreColorTi_proper i)
    (s6CoreColorTi_nonTi_image_le_two i) hnot

theorem r5_s6_c5_isolated_high_five_forces_Ti_B
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : HighChromaticTriangleFree 5 n G) {u v : Fin n}
    (huv : G.Adj u v)
    (e : (G.induce (residualSet G u v)) ≃g s6c5Graph) (i : Fin 5) :
    s6Ti i ∈ pullSupportFamilyEmbedding (residualSixEmbeddingOfC5Iso e)
      (supportFamilyB G u v) := by
  by_contra hnot
  have h4 := r5_s6_c5_isolated_four_colorable_of_Ti_absent hG.1 huv e i hnot
  have hbad : (5 : ℕ∞) ≤ 4 := hG.2.trans h4.chromaticNumber_le
  norm_num at hbad

theorem r5_s6_c5_isolated_high_five_forces_Ti_A
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : HighChromaticTriangleFree 5 n G) {u v : Fin n}
    (huv : G.Adj u v)
    (e : (G.induce (residualSet G u v)) ≃g s6c5Graph) (i : Fin 5) :
    s6Ti i ∈ pullSupportFamilyEmbedding (residualSixEmbeddingOfC5Iso e)
      (supportFamilyA G u v) := by
  let eSwap : (G.induce (residualSet G v u)) ≃g s6c5Graph :=
    (residualInducedSwapIso G u v).trans e
  have hforced := r5_s6_c5_isolated_high_five_forces_Ti_B hG huv.symm eSwap i
  have hfeq : residualSixEmbeddingOfC5Iso eSwap =
      residualSixEmbeddingOfC5Iso e := by
    apply Function.Embedding.ext
    intro j
    dsimp [residualSixEmbeddingOfC5Iso, eSwap, residualInducedSwapIso,
      residualSetSwapEquiv]
    rfl
  rw [hfeq] at hforced
  simpa [supportFamilyB_swap_eq_supportFamilyA] using hforced

theorem r5_s6_c5_isolated_high_five_forces_TFamily_B
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : HighChromaticTriangleFree 5 n G) {u v : Fin n}
    (huv : G.Adj u v)
    (e : (G.induce (residualSet G u v)) ≃g s6c5Graph) :
    s6TFamily ⊆ pullSupportFamilyEmbedding (residualSixEmbeddingOfC5Iso e)
      (supportFamilyB G u v) := by
  rw [s6TFamily_eq_image_s6Ti]
  intro T hT
  rcases Finset.mem_image.mp hT with ⟨i, hi, rfl⟩
  exact r5_s6_c5_isolated_high_five_forces_Ti_B hG huv e i

theorem r5_s6_c5_isolated_high_five_forces_TFamily_A
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : HighChromaticTriangleFree 5 n G) {u v : Fin n}
    (huv : G.Adj u v)
    (e : (G.induce (residualSet G u v)) ≃g s6c5Graph) :
    s6TFamily ⊆ pullSupportFamilyEmbedding (residualSixEmbeddingOfC5Iso e)
      (supportFamilyA G u v) := by
  rw [s6TFamily_eq_image_s6Ti]
  intro T hT
  rcases Finset.mem_image.mp hT with ⟨i, hi, rfl⟩
  exact r5_s6_c5_isolated_high_five_forces_Ti_A hG huv e i

/- Any support type is contained in the residual set.  Consequently an
   embedding whose range is the residual set maps every support family into
   its image, which is the premise needed by `SupportPull`. -/
theorem supportFamily_maps_to_residual_embedding
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (f : Fin 6 ↪ Fin n)
    (hrange : Set.range f = residualSet G u v) :
    familyMapsToEmbedding f (supportFamilyA G u v) ∧
      familyMapsToEmbedding f (supportFamilyB G u v) := by
  constructor
  · intro I hI z hz
    rcases mem_supportFamilyA_iff.mp hI with ⟨x, hx, hIx⟩
    subst I
    rw [hrange]
    exact (mem_residualTypeFinset_iff.mp hz).2
  · intro I hI z hz
    rcases mem_supportFamilyB_iff.mp hI with ⟨x, hx, hIx⟩
    subst I
    rw [hrange]
    exact (mem_residualTypeFinset_iff.mp hz).2

theorem s6_pull_supports_subset_of_residual_embedding
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (htri : G.CliqueFree 3) {u v : Fin n}
    (f : Fin 6 ↪ Fin n)
    (hrange : Set.range f = residualSet G u v)
    (hgraph : ∀ x y : Fin 6,
      G.Adj (f x) (f y) ↔ s6c5Graph.Adj x y) :
    pullSupportFamilyEmbedding f (supportFamilyA G u v) ⊆ s6Supports ∧
      pullSupportFamilyEmbedding f (supportFamilyB G u v) ⊆ s6Supports := by
  classical
  have hmaps := supportFamily_maps_to_residual_embedding f hrange
  have hsubA : pullSupportFamilyEmbedding f
      (supportFamilyA G u v) ⊆ s6Supports := by
    intro J hJ
    rcases Finset.mem_image.mp hJ with ⟨I, hI, rfl⟩
    have hInon : I.Nonempty := supportFamilyA_nonempty hI
    have hJnon : (I.preimage f f.injective.injOn).Nonempty := by
      rcases hInon with ⟨z, hz⟩
      obtain ⟨a, ha⟩ := hmaps.1 I hI z hz
      refine ⟨a, Finset.mem_preimage.mpr ?_⟩
      simpa [ha] using hz
    have hJind : s6c5Independent (I.preimage f f.injective.injOn) := by
      intro a ha b hb hab
      have ha' : f a ∈ I := Finset.mem_preimage.mp ha
      have hb' : f b ∈ I := Finset.mem_preimage.mp hb
      intro hab6
      have hgraph' : s6c5Graph.Adj a b := s6c5Adj_implies_graph_adj hab6
      have hGadj : G.Adj (f a) (f b) := (hgraph a b).mpr hgraph'
      exact (supportFamilyA_independent htri hI) ha' hb'
        (fun h => hab (f.injective h)) hGadj
    exact s6_nonempty_independent_classification hJnon hJind
  have hsubB : pullSupportFamilyEmbedding f
      (supportFamilyB G u v) ⊆ s6Supports := by
    intro J hJ
    rcases Finset.mem_image.mp hJ with ⟨I, hI, rfl⟩
    have hInon : I.Nonempty := supportFamilyB_nonempty hI
    have hJnon : (I.preimage f f.injective.injOn).Nonempty := by
      rcases hInon with ⟨z, hz⟩
      obtain ⟨a, ha⟩ := hmaps.2 I hI z hz
      refine ⟨a, Finset.mem_preimage.mpr ?_⟩
      simpa [ha] using hz
    have hJind : s6c5Independent (I.preimage f f.injective.injOn) := by
      intro a ha b hb hab
      have ha' : f a ∈ I := Finset.mem_preimage.mp ha
      have hb' : f b ∈ I := Finset.mem_preimage.mp hb
      intro hab6
      have hgraph' : s6c5Graph.Adj a b := s6c5Adj_implies_graph_adj hab6
      have hGadj : G.Adj (f a) (f b) := (hgraph a b).mpr hgraph'
      exact (supportFamilyB_independent htri hI) ha' hb'
        (fun h => hab (f.injective h)) hGadj
    exact s6_nonempty_independent_classification hJnon hJind
  exact ⟨hsubA, hsubB⟩

/- Once the finite mandatory family and the V/D count have been obtained from
   the structural part of the proof, the table now discharges the actual
   graph-level surplus bound.  This is the precise remaining interface for
   the `C₅ ⊔ K₁` branch. -/
theorem r5_s6_support_surplus_nonpositive_of_residual_embedding
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (htri : G.CliqueFree 3) {u v : Fin n}
    (f : Fin 6 ↪ Fin n)
    (hrange : Set.range f = residualSet G u v)
    (hgraph : ∀ x y : Fin 6,
      G.Adj (f x) (f y) ↔ s6c5Graph.Adj x y)
    (h𝒜T : s6TFamily ⊆
      pullSupportFamilyEmbedding f (supportFamilyA G u v))
    (hℬT : s6TFamily ⊆
      pullSupportFamilyEmbedding f (supportFamilyB G u v))
    (hcount : 5 ≤
      (∑ I ∈ pullSupportFamilyEmbedding f (supportFamilyA G u v) \ s6TFamily,
        if I ∈ s6VDFamily then 1 else 0) +
      (∑ J ∈ pullSupportFamilyEmbedding f (supportFamilyB G u v) \ s6TFamily,
        if J ∈ s6VDFamily then 1 else 0)) :
    supportSurplus (supportFamilyA G u v)
      (supportFamilyB G u v) ≤ 0 := by
  have hmaps := supportFamily_maps_to_residual_embedding f hrange
  let 𝒜 := pullSupportFamilyEmbedding f (supportFamilyA G u v)
  let ℬ := pullSupportFamilyEmbedding f (supportFamilyB G u v)
  have hAmap : mapSupportFamilyEmbedding f 𝒜 = supportFamilyA G u v := by
    simpa [𝒜] using map_pullSupportFamilyEmbedding_eq f hmaps.1
  have hBmap : mapSupportFamilyEmbedding f ℬ = supportFamilyB G u v := by
    simpa [ℬ] using map_pullSupportFamilyEmbedding_eq f hmaps.2
  have hsub := s6_pull_supports_subset_of_residual_embedding htri f hrange hgraph
  have hs := r5_s6_support_surplus_nonpositive_of_embedded_certificate
    f (𝒜 := 𝒜) (ℬ := ℬ) (𝒜' := supportFamilyA G u v)
    (ℬ' := supportFamilyB G u v) hAmap.symm hBmap.symm hsub.1 hsub.2
    h𝒜T hℬT hcount
  exact hs

run_cmd R5Kernel.checkStandardAxioms ``s6_table_cross_J_compatible
run_cmd R5Kernel.checkStandardAxioms ``r5_s6_support_surplus_nonpositive_of_residual_embedding

end Erdos1011

end Web_Erdos1011_R5S6Support
