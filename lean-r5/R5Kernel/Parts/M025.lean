import R5Kernel.Parts.M024
import R5Kernel.SmallGraphColoring

/- Source module: Erdos1011.SmallResidual. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_SmallResidual


namespace Erdos1011

open SimpleGraph

/-! Structural small-graph bridge for the residual graph. The legacy encoded
    statements are retained, but follow from odd-cycle extraction and the
    fixed pentagon instead of enumerating all graphs and all colourings.
    The result is not the final support-capacity argument, but isolates the
    only possible small non-bipartite residual: it is still 3-colourable. -/

private def triangleFreeFinite {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ x y z : Fin n, G.Adj x y → G.Adj x z → G.Adj y z → False

private def properColoringFinite {n k : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ c : Fin n → Fin k, ∀ x y : Fin n, G.Adj x y → c x ≠ c y

private def independentFinite {n : ℕ} (G : SimpleGraph (Fin n))
    (I : Finset (Fin n)) : Prop :=
  ∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ G.Adj x y

private theorem exists_fin3_color_avoiding
    {V : Type*} [Finite V] {H : SimpleGraph V}
    (C : H.Coloring (Fin 3)) {T : Set V} (hT : T.ncard ≤ 2) :
    ∃ c : Fin 3, ∀ x : V, x ∈ T → C x ≠ c := by
  classical
  by_contra h
  have hcover : ∀ c : Fin 3, ∃ x : T, C x = c := by
    intro c
    by_contra hc
    push_neg at hc
    apply h
    refine ⟨c, ?_⟩
    intro x hx
    exact hc ⟨x, hx⟩
  choose f hf using hcover
  have hinj : Function.Injective f := by
    intro a b hab
    calc
      a = C (f a) := (hf a).symm
      _ = C (f b) := congrArg (fun x : T => C x.1) hab
      _ = b := hf b
  have hcard : Nat.card (Fin 3) ≤ Nat.card T :=
    Nat.card_le_card_of_injective f hinj
  have hcard' : 3 ≤ T.ncard := by simpa using hcard
  omega

private instance triangleFreeFinite_decidable {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Decidable (triangleFreeFinite G) := by
  unfold triangleFreeFinite
  infer_instance

private instance properColoringFinite_decidable {n k : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Decidable (properColoringFinite (k := k) G) := by
  unfold properColoringFinite
  apply Fintype.decidableExistsFintype

private instance independentFinite_decidable {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (I : Finset (Fin n)) :
    Decidable (independentFinite G I) := by
  unfold independentFinite
  infer_instance

private theorem cliqueFree_three_iff_triangleFreeFinite
    {n : ℕ} {G : SimpleGraph (Fin n)} :
    G.CliqueFree 3 ↔ triangleFreeFinite G := by
  constructor
  · intro h x y z hxy hxz hyz
    exact h _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy, hxz, hyz⟩)
  · intro h s hs
    rcases SimpleGraph.is3Clique_iff.mp hs with ⟨x, y, z, hxy, hxz, hyz, _⟩
    exact h x y z hxy hxz hyz

private theorem properColoringFinite_iff_colorable
    {n k : ℕ} {G : SimpleGraph (Fin n)} :
    properColoringFinite (k := k) G ↔ G.Colorable k := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨Coloring.mk c (fun {v w} h => hc v w h)⟩
  · rintro ⟨C⟩
    exact ⟨C, fun {v w} hxy => C.valid hxy⟩

private abbrev EdgeCode (n : ℕ) := {e : Sym2 (Fin n) // ¬ e.IsDiag}

private def edgeCodeSet {n : ℕ} (E : Finset (EdgeCode n)) :
    Set (Sym2 (Fin n)) := ((E.image Subtype.val : Finset (Sym2 (Fin n))) : Set _)

private instance edgeCodeSet_decidable {n : ℕ} (E : Finset (EdgeCode n)) :
    DecidablePred (· ∈ edgeCodeSet E) := by
  intro z
  change Decidable (z ∈ E.image Subtype.val)
  infer_instance

private def finiteCodeGraph {n : ℕ} (E : Finset (EdgeCode n)) :
    SimpleGraph (Fin n) := SimpleGraph.fromEdgeSet (edgeCodeSet E)

private instance finiteCodeGraph_decidable {n : ℕ}
    (E : Finset (EdgeCode n)) : DecidableRel (finiteCodeGraph E).Adj := by
  intro x y
  change Decidable (s(x, y) ∈ edgeCodeSet E ∧ x ≠ y)
  infer_instance

theorem finite_code_fin5_triangle_free_colorable_three :
    ∀ E : Finset (EdgeCode 5),
      triangleFreeFinite (finiteCodeGraph E) →
        properColoringFinite (k := 3) (finiteCodeGraph E) := by
  intro E htri
  exact properColoringFinite_iff_colorable.mpr
    (kernel_fin5_triangle_free_colorable_three
      (cliqueFree_three_iff_triangleFreeFinite.mpr htri))

theorem finite_code_fin5_nonbip_independent_card_le_two :
    ∀ E : Finset (EdgeCode 5),
      triangleFreeFinite (finiteCodeGraph E) →
      ¬ properColoringFinite (k := 2) (finiteCodeGraph E) →
      ∀ I : Finset (Fin 5), independentFinite (finiteCodeGraph E) I →
        I.card ≤ 2 := by
  intro E htri hnot I hI
  exact kernel_fin5_nonbip_independent_card_le_two
    (cliqueFree_three_iff_triangleFreeFinite.mpr htri)
    (fun h => hnot (properColoringFinite_iff_colorable.mpr h)) hI

theorem finite_code_fin3_triangle_free_colorable_three :
    ∀ E : Finset (EdgeCode 3),
      triangleFreeFinite (finiteCodeGraph E) →
        properColoringFinite (k := 3) (finiteCodeGraph E) := by
  intro E _
  exact properColoringFinite_iff_colorable.mpr
    (SimpleGraph.colorable_of_fintype (finiteCodeGraph E))

theorem finite_code_fin4_triangle_free_colorable_three :
    ∀ E : Finset (EdgeCode 4),
      triangleFreeFinite (finiteCodeGraph E) →
        properColoringFinite (k := 3) (finiteCodeGraph E) := by
  intro E htri
  exact properColoringFinite_iff_colorable.mpr
    ((kernel_triangle_free_fin_le_four_colorable_two (by omega)
      (cliqueFree_three_iff_triangleFreeFinite.mpr htri)).mono (by omega))

theorem finite_code_fin4_triangle_free_colorable_two :
    ∀ E : Finset (EdgeCode 4),
      triangleFreeFinite (finiteCodeGraph E) →
        properColoringFinite (k := 2) (finiteCodeGraph E) := by
  intro E htri
  exact properColoringFinite_iff_colorable.mpr
    (kernel_triangle_free_fin_le_four_colorable_two (by omega)
      (cliqueFree_three_iff_triangleFreeFinite.mpr htri))

theorem finite_code_fin3_triangle_free_colorable_two :
    ∀ E : Finset (EdgeCode 3),
      triangleFreeFinite (finiteCodeGraph E) →
        properColoringFinite (k := 2) (finiteCodeGraph E) := by
  intro E htri
  exact properColoringFinite_iff_colorable.mpr
    (kernel_triangle_free_fin_le_four_colorable_two (by omega)
      (cliqueFree_three_iff_triangleFreeFinite.mpr htri))

private def edgeCodeOfGraph {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : Finset (EdgeCode n) :=
  G.edgeFinset.attach.image (fun e =>
    (⟨e.1, G.not_isDiag_of_mem_edgeFinset e.2⟩ : EdgeCode n))

private theorem finiteCodeGraph_edgeCodeOfGraph {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    finiteCodeGraph (edgeCodeOfGraph G) = G := by
  ext x y
  constructor
  · intro h
    change (SimpleGraph.fromEdgeSet (edgeCodeSet (edgeCodeOfGraph G))).Adj x y at h
    rw [SimpleGraph.fromEdgeSet_adj] at h
    rcases h with ⟨hE, hxy⟩
    change s(x, y) ∈
      ((edgeCodeOfGraph G).image Subtype.val : Finset (Sym2 (Fin n))) at hE
    rw [Finset.mem_image] at hE
    rcases hE with ⟨e, he, heq⟩
    rcases Finset.mem_image.mp he with ⟨e', he', heeq⟩
    have hefin : e'.1 ∈ G.edgeFinset := e'.2
    have heq' : e'.1 = e.1 := by simpa using congrArg Subtype.val heeq
    have hval : e'.1 = s(x, y) := heq'.trans heq
    have : s(x, y) ∈ G.edgeFinset := by simpa [hval] using hefin
    exact (SimpleGraph.mem_edgeFinset.mp this)
  · intro hxy
    have hne : x ≠ y := G.ne_of_adj hxy
    change (SimpleGraph.fromEdgeSet (edgeCodeSet (edgeCodeOfGraph G))).Adj x y
    rw [SimpleGraph.fromEdgeSet_adj]
    refine ⟨?_, hne⟩
    change s(x, y) ∈
      ((edgeCodeOfGraph G).image Subtype.val : Finset (Sym2 (Fin n)))
    apply Finset.mem_image.mpr
    let e : G.edgeFinset := ⟨s(x, y), SimpleGraph.mem_edgeFinset.mpr hxy⟩
    let ec : EdgeCode n := ⟨e.1, G.not_isDiag_of_mem_edgeFinset e.2⟩
    refine ⟨ec, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨e, by simp, rfl⟩
    · rfl

private theorem fin_triangle_free_colorable_of_code
    {n k : ℕ}
    (hcode : ∀ E : Finset (EdgeCode n),
      triangleFreeFinite (finiteCodeGraph E) →
        properColoringFinite (k := k) (finiteCodeGraph E))
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (htri : G.CliqueFree 3) : G.Colorable k := by
  let E := edgeCodeOfGraph G
  have hEq : finiteCodeGraph E = G := finiteCodeGraph_edgeCodeOfGraph G
  have htriE : (finiteCodeGraph E).CliqueFree 3 := hEq.symm ▸ htri
  have hfin := hcode E
    (cliqueFree_three_iff_triangleFreeFinite.mp htriE)
  have hproper : properColoringFinite (k := k) G := by
    rw [← finiteCodeGraph_edgeCodeOfGraph G]
    exact hfin
  exact properColoringFinite_iff_colorable.mp hproper

theorem fin5_nonbip_independent_card_le_two
    {G : SimpleGraph (Fin 5)} [DecidableRel G.Adj]
    (htri : G.CliqueFree 3) (hnot2 : ¬ G.Colorable 2)
    {I : Finset (Fin 5)} (hI : G.IsIndepSet (I : Set (Fin 5))) :
    I.card ≤ 2 := by
  let E := edgeCodeOfGraph G
  have hEq : finiteCodeGraph E = G := finiteCodeGraph_edgeCodeOfGraph G
  have htriE : (finiteCodeGraph E).CliqueFree 3 := hEq.symm ▸ htri
  have hnot2E : ¬ properColoringFinite (k := 2) (finiteCodeGraph E) := by
    intro hp
    apply hnot2
    have hpG : properColoringFinite (k := 2) G := by
      rw [← hEq]
      exact hp
    exact properColoringFinite_iff_colorable.mp hpG
  apply finite_code_fin5_nonbip_independent_card_le_two E
    (cliqueFree_three_iff_triangleFreeFinite.mp htriE) hnot2E
  intro x hx y hy hxy
  intro hAdj
  apply hI hx hy hxy
  simpa [hEq] using hAdj

private theorem induced_fin5_independent_card_le_two
    {n : ℕ} {G : SimpleGraph (Fin n)} {S : Set (Fin n)}
    (htri : G.CliqueFree 3) (hScard : S.ncard = 5)
    (hnot2 : ¬ (G.induce S).Colorable 2)
    {I : Finset S} (hI : (G.induce S).IsIndepSet (I : Set S)) :
    I.card ≤ 2 := by
  classical
  letI : Fintype S := Fintype.ofFinite _
  have hcard : Fintype.card S = 5 := by simpa using hScard
  let H : SimpleGraph (Fin 5) := (G.induce S).overFin hcard
  let e : (G.induce S) ≃g H := (G.induce S).overFinIso hcard
  have hHtri : H.CliqueFree 3 :=
    cliqueFree_three_of_hom e.symm.toHom (by
      intro t ht
      exact htri (t.map (.subtype S))
        ((SimpleGraph.isNClique_induce_iff (G := G) S t 3).mp ht))
  have hHnot2 : ¬ H.Colorable 2 := by
    intro hc
    apply hnot2
    exact SimpleGraph.Colorable.of_hom e.toHom hc
  let J : Finset (Fin 5) := I.image e.toEquiv
  have hJcard : J.card = I.card := by
    exact Finset.card_image_of_injective I e.toEquiv.injective
  have hJind : H.IsIndepSet (J : Set (Fin 5)) := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
    have hab : a ≠ b := by
      intro hab
      exact hxy (congrArg e.toEquiv hab)
    intro hAdj
    have hxy' : (G.induce S).Adj a b :=
      (e.map_rel_iff).mp hAdj
    exact hI ha hb hab hxy'
  have hJind' : independentFinite H J := by
    intro x hx y hy hne
    exact hJind hx hy hne
  have hJ : J.card ≤ 2 := by
    apply fin5_nonbip_independent_card_le_two hHtri hHnot2
    exact hJind'
  omega

theorem induced_independent_ncard_le_two_of_ncard_eq_five
    {n : ℕ} {G : SimpleGraph (Fin n)} {S : Set (Fin n)}
    (htri : G.CliqueFree 3) (hScard : S.ncard = 5)
    (hnot2 : ¬ (G.induce S).Colorable 2)
    {I : Set S} (hI : (G.induce S).IsIndepSet I) :
    I.ncard ≤ 2 := by
  classical
  letI : Fintype S := Fintype.ofFinite _
  let IF : Finset S := (Set.toFinite I).toFinset
  have hIF : (G.induce S).IsIndepSet (IF : Set S) := by
    intro a ha b hb hab
    have haI : a ∈ I := by
      apply (Set.toFinite I).mem_toFinset.mp
      exact ha
    have hbI : b ∈ I := by
      apply (Set.toFinite I).mem_toFinset.mp
      exact hb
    apply hI haI hbI hab
  have hcard : IF.card ≤ 2 :=
    induced_fin5_independent_card_le_two htri hScard hnot2 hIF
  have hnc : I.ncard = IF.card := by
    exact Set.ncard_eq_toFinset_card I (Set.toFinite I)
  omega

theorem fin5_triangle_free_colorable_three
    {G : SimpleGraph (Fin 5)} [DecidableRel G.Adj]
    (htri : G.CliqueFree 3) : G.Colorable 3 :=
  fin_triangle_free_colorable_of_code finite_code_fin5_triangle_free_colorable_three htri

theorem fin4_triangle_free_colorable_three
    {G : SimpleGraph (Fin 4)} [DecidableRel G.Adj]
    (htri : G.CliqueFree 3) : G.Colorable 3 :=
  fin_triangle_free_colorable_of_code finite_code_fin4_triangle_free_colorable_three htri

theorem fin3_triangle_free_colorable_three
    {G : SimpleGraph (Fin 3)} [DecidableRel G.Adj]
    (htri : G.CliqueFree 3) : G.Colorable 3 :=
  fin_triangle_free_colorable_of_code finite_code_fin3_triangle_free_colorable_three htri

theorem fin4_triangle_free_colorable_two
    {G : SimpleGraph (Fin 4)} [DecidableRel G.Adj]
    (htri : G.CliqueFree 3) : G.Colorable 2 :=
  fin_triangle_free_colorable_of_code finite_code_fin4_triangle_free_colorable_two htri

theorem fin3_triangle_free_colorable_two
    {G : SimpleGraph (Fin 3)} [DecidableRel G.Adj]
    (htri : G.CliqueFree 3) : G.Colorable 2 :=
  fin_triangle_free_colorable_of_code finite_code_fin3_triangle_free_colorable_two htri

theorem triangle_free_fin_le_five_colorable_three
    {n : ℕ} (hn : n ≤ 5) {G : SimpleGraph (Fin n)}
    (htri : G.CliqueFree 3) : G.Colorable 3 := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  interval_cases n
  · exact (SimpleGraph.colorable_of_fintype G).mono (by simp)
  · exact (SimpleGraph.colorable_of_fintype G).mono (by simp)
  · exact (SimpleGraph.colorable_of_fintype G).mono (by simp)
  · exact fin3_triangle_free_colorable_three htri
  · exact fin4_triangle_free_colorable_three htri
  · exact fin5_triangle_free_colorable_three htri

theorem triangle_free_fin_le_four_colorable_two
    {n : ℕ} (hn : n ≤ 4) {G : SimpleGraph (Fin n)}
    (htri : G.CliqueFree 3) : G.Colorable 2 := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  interval_cases n
  · exact (SimpleGraph.colorable_of_fintype G).mono (by simp)
  · exact (SimpleGraph.colorable_of_fintype G).mono (by simp)
  · exact (SimpleGraph.colorable_of_fintype G).mono (by simp)
  · exact fin3_triangle_free_colorable_two htri
  · exact fin4_triangle_free_colorable_two htri

theorem induced_triangle_free_colorable_three_of_ncard_le_five
    {n : ℕ} {G : SimpleGraph (Fin n)} {S : Set (Fin n)}
    (htri : G.CliqueFree 3) (hS : S.ncard ≤ 5) :
    (G.induce S).Colorable 3 := by
  classical
  letI : Fintype S := Fintype.ofFinite _
  have hcard : Fintype.card S = S.ncard := by simp
  have hcard_le : Fintype.card S ≤ 5 := by simpa [hcard] using hS
  let H : SimpleGraph (Fin (Fintype.card S)) :=
    (G.induce S).overFin rfl
  have hIso : (G.induce S) ≃g H := (G.induce S).overFinIso rfl
  have hInd : (G.induce S).CliqueFree 3 := by
    intro t ht
    exact htri (t.map (.subtype S))
      ((SimpleGraph.isNClique_induce_iff (G := G) S t 3).mp ht)
  have hHtri : H.CliqueFree 3 := by
    exact cliqueFree_three_of_hom hIso.symm.toHom hInd
  have hHcol : H.Colorable 3 :=
    triangle_free_fin_le_five_colorable_three hcard_le hHtri
  exact SimpleGraph.Colorable.of_hom hIso.toHom hHcol

theorem induced_triangle_free_colorable_two_of_ncard_le_four
    {n : ℕ} {G : SimpleGraph (Fin n)} {S : Set (Fin n)}
    (htri : G.CliqueFree 3) (hS : S.ncard ≤ 4) :
    (G.induce S).Colorable 2 := by
  classical
  letI : Fintype S := Fintype.ofFinite _
  have hcard : Fintype.card S = S.ncard := by simp
  have hcard_le : Fintype.card S ≤ 4 := by simpa [hcard] using hS
  let H : SimpleGraph (Fin (Fintype.card S)) :=
    (G.induce S).overFin rfl
  have hIso : (G.induce S) ≃g H := (G.induce S).overFinIso rfl
  have hInd : (G.induce S).CliqueFree 3 := by
    intro t ht
    exact htri (t.map (.subtype S))
      ((SimpleGraph.isNClique_induce_iff (G := G) S t 3).mp ht)
  have hHtri : H.CliqueFree 3 :=
    cliqueFree_three_of_hom hIso.symm.toHom hInd
  have hHcol : H.Colorable 2 :=
    triangle_free_fin_le_four_colorable_two hcard_le hHtri
  exact SimpleGraph.Colorable.of_hom hIso.toHom hHcol

theorem high_five_residual_ncard_ge_five
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (hG : HighChromaticTriangleFree 5 n G) (huv : G.Adj u v) :
    5 ≤ (residualSet G u v).ncard := by
  by_contra hsmall
  have hS : (residualSet G u v).ncard ≤ 4 := by omega
  have hcol := induced_triangle_free_colorable_two_of_ncard_le_four hG.1 hS
  exact residual_not_colorable_two_of_high_five hG huv hcol

/-! If the residual graph has a 3-colouring and every `B`-side vertex sees at
    most two residual colours, the endpoint/sides/residual partition gives a
    four-colouring of the whole graph.  This is the formal version of the
    paper's `s = 5` exclusion step (the missing residual colour is assigned to
    each `B` vertex separately). -/

theorem colorable_four_of_residual_missing_color
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (htri : G.CliqueFree 3) (huv : G.Adj u v)
    (C : (G.induce (residualSet G u v)).Coloring (Fin 3))
    (hmissing : ∀ y, y ∈ edgeSideBSet G u v →
      ∃ d : Fin 3, ∀ z : residualSet G u v,
        (z : Fin n) ∈ residualType G u v y → C z ≠ d) :
    G.Colorable 4 := by
  classical
  choose missing hmissing_spec using hmissing
  let c : Fin n → Fin 4 := fun z =>
    if z = u then 0
    else if z = v then 1
    else if z ∈ edgeSideASet G u v then 0
    else if hz : z ∈ edgeSideBSet G u v then Fin.succ (missing z hz)
    else if hz : z ∈ residualSet G u v then Fin.succ (C ⟨z, hz⟩)
    else 0
  have huv_ne : u ≠ v := huv.ne
  have hcu : c u = 0 := by simp only [c, if_pos rfl]
  have hcv : c v = 1 := by simp [c, huv_ne, huv_ne.symm]
  have hca {x : Fin n} (hx : x ∈ edgeSideASet G u v) : c x = 0 := by
    have hxu : x ≠ u := hx.2
    have hxv : x ≠ v := by
      intro h
      subst x
      exact G.loopless.irrefl v hx.1
    simp only [c, if_neg hxu, if_neg hxv, if_pos hx]
  have hcb {x : Fin n} (hx : x ∈ edgeSideBSet G u v) :
      c x = Fin.succ (missing x hx) := by
    have hxv : x ≠ v := hx.2
    have hxu : x ≠ u := by
      intro h
      subst x
      exact G.loopless.irrefl u hx.1
    have hxa : x ∉ edgeSideASet G u v := by
      intro h
      exact Set.disjoint_left.mp (edgeSide_sets_disjoint htri huv) h hx
    simp only [c, if_neg hxu, if_neg hxv, if_neg hxa, dif_pos hx]
  have hcs {x : Fin n} (hx : x ∈ residualSet G u v) :
      c x = Fin.succ (C ⟨x, hx⟩) := by
    have hxa : x ∉ edgeSideASet G u v := by
      intro h
      exact hx.2.2.2 h.1
    have hxb : x ∉ edgeSideBSet G u v := by
      intro h
      exact hx.2.2.1 h.1
    simp only [c, if_neg hx.1, if_neg hx.2.1, if_neg hxa, dif_neg hxb, dif_pos hx]
  have h0shift (a : Fin 3) : (0 : Fin 4) ≠ Fin.succ a := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  have hshift0 (a : Fin 3) : Fin.succ a ≠ (0 : Fin 4) := (h0shift a).symm
  have hshift_ne {a b : Fin 3} (hab : a ≠ b) :
      Fin.succ a ≠ Fin.succ b := by
    intro h
    apply hab
    apply Fin.ext
    simpa using congrArg Fin.val h
  have hsucc_inj {a b : Fin 3} (h : Fin.succ a = Fin.succ b) : a = b := by
    apply Fin.ext
    simpa using congrArg Fin.val h
  have hvalid : ∀ {x y : Fin n}, G.Adj x y → c x ≠ c y := by
    intro x y hxy
    have hxy_ne : x ≠ y := hxy.ne
    have hpart (z : Fin n) :
        z = u ∨ z = v ∨ z ∈ edgeSideASet G u v ∨
          z ∈ edgeSideBSet G u v ∨ z ∈ residualSet G u v := by
      have heq := residualSet_eq_compl_endpoints_union_sides G u v
      by_cases hzu : z = u
      · exact Or.inl hzu
      by_cases hzv : z = v
      · exact Or.inr (Or.inl hzv)
      by_cases hzA : z ∈ edgeSideASet G u v
      · exact Or.inr (Or.inr (Or.inl hzA))
      by_cases hzB : z ∈ edgeSideBSet G u v
      · exact Or.inr (Or.inr (Or.inr (Or.inl hzB)))
      right; right; right; right
      rw [heq]
      simp [hzu, hzv, hzA, hzB]
    have hnot_u_A {z : Fin n} (hzA : z ∈ edgeSideASet G u v)
        (huz : G.Adj u z) : False := by
      exact htri _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨huv, huz, hzA.1⟩)
    have hnot_v_B {z : Fin n} (hzB : z ∈ edgeSideBSet G u v)
        (hvz : G.Adj v z) : False := by
      exact htri _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨huv.symm, hvz, hzB.1⟩)
    rcases hpart x with hxu | hxv | hxA | hxB | hxS
    · subst x
      rcases hpart y with hyu | hyv | hyA | hyB | hyS
      · exact (hxy_ne hyu.symm).elim
      · subst y; rw [hcu, hcv]; decide
      · exact (hnot_u_A hyA hxy).elim
      · rw [hcu, hcb hyB]; exact h0shift _
      · exact (hyS.2.2.1 hxy).elim
    · subst x
      rcases hpart y with hyu | hyv | hyA | hyB | hyS
      · subst y; rw [hcv, hcu]; decide
      · exact (hxy_ne hyv.symm).elim
      · rw [hcv, hca hyA]; decide
      · exact (hnot_v_B hyB hxy).elim
      · exact (hyS.2.2.2 hxy).elim
    · rcases hpart y with hyu | hyv | hyA | hyB | hyS
      · subst y; exact (hnot_u_A hxA hxy.symm).elim
      · subst y; rw [hca hxA, hcv]; decide
      · exact ((edgeSideASet_independent htri u v hxA hyA hxy_ne) hxy).elim
      · rw [hca hxA, hcb hyB]; exact h0shift _
      · rw [hca hxA, hcs hyS]; exact h0shift _
    · rcases hpart y with hyu | hyv | hyA | hyB | hyS
      · subst y; rw [hcb hxB, hcu]; exact hshift0 _
      · subst y; exact (hnot_v_B hxB hxy.symm).elim
      · rw [hcb hxB, hca hyA]; exact hshift0 _
      · exact ((edgeSideBSet_independent htri u v hxB hyB hxy_ne) hxy).elim
      · have hty : y ∈ residualType G u v x := ⟨hxy, hyS⟩
        rw [hcb hxB, hcs hyS]
        intro heq
        apply hmissing_spec x hxB ⟨y, hyS⟩ hty
        exact hsucc_inj heq.symm
    · rcases hpart y with hyu | hyv | hyA | hyB | hyS
      · subst y; exact (hxS.2.2.1 hxy.symm).elim
      · subst y; exact (hxS.2.2.2 hxy.symm).elim
      · rw [hcs hxS, hca hyA]; exact hshift0 _
      · have hty : x ∈ residualType G u v y := ⟨hxy.symm, hxS⟩
        rw [hcs hxS, hcb hyB]
        intro heq
        apply hmissing_spec y hyB ⟨x, hxS⟩ hty
        exact hsucc_inj heq
      · have hC : C ⟨x, hxS⟩ ≠ C ⟨y, hyS⟩ := by
          apply C.valid
          simpa only [SimpleGraph.induce_adj] using hxy
        rw [hcs hxS, hcs hyS]
        exact hshift_ne hC
  exact ⟨Coloring.mk c hvalid⟩

/- The original cardinal formulation is retained as a wrapper. -/
theorem colorable_four_of_residual_colorable_three_and_B_type_le_two
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (htri : G.CliqueFree 3) (huv : G.Adj u v)
    (hS : (G.induce (residualSet G u v)).Colorable 3)
    (hType : ∀ y, y ∈ edgeSideBSet G u v →
      (residualType G u v y).ncard ≤ 2) :
    G.Colorable 4 := by
  classical
  obtain ⟨C⟩ := hS
  have hmissing (y : Fin n) (hy : y ∈ edgeSideBSet G u v) :
      ∃ d : Fin 3, ∀ z : residualSet G u v,
        (z : Fin n) ∈ residualType G u v y → C z ≠ d := by
    let T : Set (residualSet G u v) :=
      (fun z : residualSet G u v => (z : Fin n)) ⁻¹' residualType G u v y
    have hTcard : T.ncard ≤ 2 := by
      have himage : (fun z : residualSet G u v => (z : Fin n)) '' T =
          residualType G u v y := by
        ext z
        constructor
        · rintro ⟨w, hw, rfl⟩
          exact hw
        · intro hz
          refine ⟨⟨z, hz.2⟩, ?_, rfl⟩
          exact hz
      have hTc' : ((fun z : residualSet G u v => (z : Fin n)) '' T).ncard = T.ncard :=
        Set.ncard_image_of_injective T Subtype.val_injective
      rw [himage] at hTc'
      rw [← hTc']
      exact hType y hy
    obtain ⟨d, hd⟩ := exists_fin3_color_avoiding C hTcard
    refine ⟨d, ?_⟩
    intro z hz
    have hzT : z ∈ T := by
      change (z : Fin n) ∈ residualType G u v y
      exact hz
    exact hd z hzT
  exact colorable_four_of_residual_missing_color htri huv C hmissing

theorem no_five_residual_of_high_five
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (hG : HighChromaticTriangleFree 5 n G) (huv : G.Adj u v) :
    (residualSet G u v).ncard ≠ 5 := by
  intro hs5
  have hScol : (G.induce (residualSet G u v)).Colorable 3 :=
    induced_triangle_free_colorable_three_of_ncard_le_five hG.1 (by omega)
  have hnot2 : ¬ (G.induce (residualSet G u v)).Colorable 2 :=
    residual_not_colorable_two_of_high_five hG huv
  have hType : ∀ y, y ∈ edgeSideBSet G u v →
      (residualType G u v y).ncard ≤ 2 := by
    intro y hy
    let T : Set (residualSet G u v) :=
      (fun z : residualSet G u v => (z : Fin n)) ⁻¹' residualType G u v y
    have hTind : (G.induce (residualSet G u v)).IsIndepSet T := by
      intro a ha b hb hab
      have ha' : (a : Fin n) ∈ residualType G u v y := ha
      have hb' : (b : Fin n) ∈ residualType G u v y := hb
      have hab' : (a : Fin n) ≠ (b : Fin n) := by
        intro heq
        apply hab
        exact Subtype.ext heq
      have hind := residualType_independent hG.1 (u := u) (v := v) y ha' hb' hab'
      intro hadj
      exact hind (by simpa only [SimpleGraph.induce_adj] using hadj)
    have hTcard := induced_independent_ncard_le_two_of_ncard_eq_five
      hG.1 hs5 hnot2 hTind
    have himage : (fun z : residualSet G u v => (z : Fin n)) '' T =
        residualType G u v y := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hz
        refine ⟨⟨z, hz.2⟩, ?_, rfl⟩
        exact hz
    have hTc' : ((fun z : residualSet G u v => (z : Fin n)) '' T).ncard = T.ncard :=
      Set.ncard_image_of_injective T Subtype.val_injective
    rw [himage] at hTc'
    omega
  have h4 := colorable_four_of_residual_colorable_three_and_B_type_le_two
    hG.1 huv hScol hType
  have hle : G.chromaticNumber ≤ 4 := h4.chromaticNumber_le
  have hbad : (5 : ℕ∞) ≤ 4 := hG.2.trans hle
  norm_num at hbad

theorem high_five_residual_ncard_ge_six
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (hG : HighChromaticTriangleFree 5 n G) (huv : G.Adj u v) :
    6 ≤ (residualSet G u v).ncard := by
  have hge5 := high_five_residual_ncard_ge_five hG huv
  have hne := no_five_residual_of_high_five hG huv
  omega

theorem high_extremal_residual_ncard_between_six_eleven
    {n : ℕ} (hn : 80 ≤ n) {G : SimpleGraph (Fin n)}
    (hG : HighExtremal 5 n G) {u v : Fin n} (huv : G.Adj u v)
    (hD : ∀ H a b, HighExtremalEdgePairs 5 n (H, (a, b)) →
      degreeSumPair (H, (a, b)) ≤ degreeSumPair (G, (u, v))) :
    6 ≤ (residualSet G u v).ncard ∧ (residualSet G u v).ncard ≤ 11 := by
  exact ⟨high_five_residual_ncard_ge_six hG.1 huv,
    high_extremal_residual_ncard_le_eleven_of_degree_sum_max hn hG huv hD⟩

run_cmd R5Kernel.checkStandardAxioms ``fin5_nonbip_independent_card_le_two
run_cmd R5Kernel.checkStandardAxioms ``triangle_free_fin_le_five_colorable_three
run_cmd R5Kernel.checkStandardAxioms ``high_five_residual_ncard_ge_six
run_cmd R5Kernel.checkStandardAxioms ``high_extremal_residual_ncard_between_six_eleven

end Erdos1011

end Web_Erdos1011_SmallResidual
