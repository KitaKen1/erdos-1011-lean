import R5Kernel.Parts.M028

/- Source module: Erdos1011.R5S6Coloring. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_R5S6Coloring


namespace Erdos1011

open SimpleGraph

/- A direct graph-level realization of the five rotated tables.  It is the
   colouring counterpart of the finite V/D rotation cover: if at most four
   V/D support types occur in total, one rotation avoids the two forbidden
   types and the table colours all of `G`. -/
theorem r5_s6_c5_isolated_four_colorable_of_vd_count_le_four
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (htri : G.CliqueFree 3)
    (hmax : IsEdgeMaximalTriangleFree G)
    {u v : Fin n} (huv : G.Adj u v)
    (e : (G.induce (residualSet G u v)) ≃g s6c5Graph)
    (hcount :
      (∑ I ∈ pullSupportFamilyEmbedding (residualSixEmbeddingOfC5Iso e)
          (supportFamilyA G u v) \ s6TFamily,
        if I ∈ s6VDFamily then 1 else 0) +
      (∑ J ∈ pullSupportFamilyEmbedding (residualSixEmbeddingOfC5Iso e)
          (supportFamilyB G u v) \ s6TFamily,
        if J ∈ s6VDFamily then 1 else 0) ≤ 4) :
    G.Colorable 4 := by
  classical
  let f := residualSixEmbeddingOfC5Iso e
  let 𝒜 := pullSupportFamilyEmbedding f (supportFamilyA G u v)
  let ℬ := pullSupportFamilyEmbedding f (supportFamilyB G u v)
  have hrange : Set.range f = residualSet G u v :=
    residualSixEmbeddingOfC5Iso_range e
  have hgraph : ∀ x y : Fin 6,
      G.Adj (f x) (f y) ↔ s6c5Graph.Adj x y :=
    residualSixEmbeddingOfC5Iso_graph e
  have hsub := s6_pull_supports_subset_of_residual_embedding htri f hrange hgraph
  have hrot := s6_vd_rotation_avoids_of_indicator_sum_le_four
    (𝒜 := 𝒜) (ℬ := ℬ) (by simpa [𝒜, ℬ] using hcount)
  obtain ⟨j, hAj, hBj⟩ := hrot
  have havoid := s6_vd_rotation_type_avoids hAj hBj
  have hAavoid (I : Finset (Fin 6)) (hI : I ∈ 𝒜) :
      I ∉ s6ForbiddenAType j := havoid.1 I hI
  have hBavoid (I : Finset (Fin 6)) (hI : I ∈ ℬ) :
      I ∉ s6ForbiddenBType j := havoid.2 I hI
  have hAcolor_ne_one (I : Finset (Fin 6)) (hI : I ∈ 𝒜) :
      s6AColorJ j I ≠ 1 :=
    s6_table_A_colorJ_ne_one j I (hsub.1 hI) (hAavoid I hI)
  have hBcolor_ne_zero (I : Finset (Fin 6)) (hI : I ∈ ℬ) :
      s6BColorJ j I ≠ 0 :=
    s6_table_B_colorJ_ne_zero j I (hsub.2 hI) (hBavoid I hI)
  let aPull : ∀ (x : Fin n), x ∈ edgeSideASet G u v →
      (residualType G u v x).Nonempty → 𝒜 := fun x hxA hne => by
    refine ⟨(residualTypeFinset G u v x).preimage f f.injective.injOn, ?_⟩
    dsimp [𝒜]
    apply Finset.mem_image.mpr
    exact ⟨residualTypeFinset G u v x,
      mem_supportFamilyA_iff.mpr ⟨x,
        mem_nonemptyATypeVertices_iff.mpr ⟨hxA, hne⟩, rfl⟩, rfl⟩
  let bPull : ∀ (y : Fin n), y ∈ edgeSideBSet G u v →
      (residualType G u v y).Nonempty → ℬ := fun y hyB hne => by
    refine ⟨(residualTypeFinset G u v y).preimage f f.injective.injOn, ?_⟩
    dsimp [ℬ]
    apply Finset.mem_image.mpr
    exact ⟨residualTypeFinset G u v y,
      mem_supportFamilyB_iff.mpr ⟨y,
        mem_nonemptyBTypeVertices_iff.mpr ⟨hyB, hne⟩, rfl⟩, rfl⟩
  let colorA : Fin n → Fin 4 := fun x =>
    if hxA : x ∈ edgeSideASet G u v then
      if hne : (residualType G u v x).Nonempty then
        s6AColorJ j (aPull x hxA hne)
      else 0
    else 0
  let colorB : Fin n → Fin 4 := fun y =>
    if hyB : y ∈ edgeSideBSet G u v then
      if hne : (residualType G u v y).Nonempty then
        s6BColorJ j (bPull y hyB hne)
      else 1
    else 1
  let c : Fin n → Fin 4 := fun z =>
    if z = u then 0
    else if z = v then 1
    else if z ∈ edgeSideASet G u v then colorA z
    else if z ∈ edgeSideBSet G u v then colorB z
    else if hz : z ∈ residualSet G u v then
      s6CoreColorJ j (e.toEquiv ⟨z, hz⟩)
    else 0
  have huv_ne : u ≠ v := huv.ne
  have hcu : c u = 0 := by simp only [c, if_pos rfl]
  have hcv : c v = 1 := by simp [c, huv_ne.symm]
  have hca {x : Fin n} (hxA : x ∈ edgeSideASet G u v) :
      c x = colorA x := by
    have hxu : x ≠ u := hxA.2
    have hxv : x ≠ v := by
      intro h
      subst x
      exact G.loopless.irrefl v hxA.1
    simp only [c, if_neg hxu, if_neg hxv, if_pos hxA]
  have hcb {y : Fin n} (hyB : y ∈ edgeSideBSet G u v) :
      c y = colorB y := by
    have hyv : y ≠ v := hyB.2
    have hyu : y ≠ u := by
      intro h
      subst y
      exact G.loopless.irrefl u hyB.1
    have hya : y ∉ edgeSideASet G u v := by
      intro h
      exact Set.disjoint_left.mp (edgeSide_sets_disjoint htri huv) h hyB
    simp only [c, if_neg hyu, if_neg hyv, if_neg hya, if_pos hyB]
  have hcs {z : Fin n} (hz : z ∈ residualSet G u v) :
      c z = s6CoreColorJ j (e.toEquiv ⟨z, hz⟩) := by
    have hza : z ∉ edgeSideASet G u v := fun h => hz.2.2.2 h.1
    have hzb : z ∉ edgeSideBSet G u v := fun h => hz.2.2.1 h.1
    simp only [c, if_neg hz.1, if_neg hz.2.1, if_neg hza, if_neg hzb,
      dif_pos hz]
  have hAempty {x : Fin n} (hxA : x ∈ edgeSideASet G u v)
      (hne : ¬ (residualType G u v x).Nonempty) : colorA x = 0 := by
    simp [colorA, hne]
  have hBempty {y : Fin n} (hyB : y ∈ edgeSideBSet G u v)
      (hne : ¬ (residualType G u v y).Nonempty) : colorB y = 1 := by
    simp [colorB, hne]
  have hAcolor_eq {x : Fin n} (hxA : x ∈ edgeSideASet G u v)
      (hne : (residualType G u v x).Nonempty) :
      colorA x = s6AColorJ j (aPull x hxA hne) := by
    simp only [colorA, dif_pos hxA, dif_pos hne]
  have hBcolor_eq {y : Fin n} (hyB : y ∈ edgeSideBSet G u v)
      (hne : (residualType G u v y).Nonempty) :
      colorB y = s6BColorJ j (bPull y hyB hne) := by
    simp only [colorB, dif_pos hyB, dif_pos hne]
  have hAcolor {x : Fin n} (hxA : x ∈ edgeSideASet G u v)
      (hne : (residualType G u v x).Nonempty)
      {z : Fin n} (hz : z ∈ residualSet G u v)
      (hxz : G.Adj x z) :
      colorA x ≠ s6CoreColorJ j (e.toEquiv ⟨z, hz⟩) := by
    have htype : z ∈ residualType G u v x := ⟨hxz, hz⟩
    have hpre : e.toEquiv ⟨z, hz⟩ ∈
        (residualTypeFinset G u v x).preimage f f.injective.injOn := by
      apply Finset.mem_preimage.mpr
      have hfz : f (e.toEquiv ⟨z, hz⟩) = z := by
        dsimp [f, residualSixEmbeddingOfC5Iso]
        exact congrArg Subtype.val (e.symm_apply_apply ⟨z, hz⟩)
      rw [hfz]
      exact mem_residualTypeFinset_iff.mpr htype
    have hh := s6_table_A_core_J_compatible j
      (aPull x hxA hne) (hsub.1 (aPull x hxA hne).property)
      (hAavoid _ (aPull x hxA hne).property)
      (e.toEquiv ⟨z, hz⟩) hpre
    have hcolor : colorA x = s6AColorJ j (aPull x hxA hne) := by
      simp only [colorA, dif_pos hxA, dif_pos hne]
    rw [hcolor]
    exact hh.symm
  have hBcolor {y : Fin n} (hyB : y ∈ edgeSideBSet G u v)
      (hne : (residualType G u v y).Nonempty)
      {z : Fin n} (hz : z ∈ residualSet G u v)
      (hyz : G.Adj y z) :
      colorB y ≠ s6CoreColorJ j (e.toEquiv ⟨z, hz⟩) := by
    have htype : z ∈ residualType G u v y := ⟨hyz, hz⟩
    have hpre : e.toEquiv ⟨z, hz⟩ ∈
        (residualTypeFinset G u v y).preimage f f.injective.injOn := by
      apply Finset.mem_preimage.mpr
      have hfz : f (e.toEquiv ⟨z, hz⟩) = z := by
        dsimp [f, residualSixEmbeddingOfC5Iso]
        exact congrArg Subtype.val (e.symm_apply_apply ⟨z, hz⟩)
      rw [hfz]
      exact mem_residualTypeFinset_iff.mpr htype
    have hh := s6_table_B_core_J_compatible j
      (bPull y hyB hne) (hsub.2 (bPull y hyB hne).property)
      (hBavoid _ (bPull y hyB hne).property)
      (e.toEquiv ⟨z, hz⟩) hpre
    have hcolor : colorB y = s6BColorJ j (bPull y hyB hne) := by
      simp only [colorB, dif_pos hyB, dif_pos hne]
    rw [hcolor]
    exact hh.symm
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
      · rw [hcu, hcb hyB]
        by_cases hne : (residualType G u v y).Nonempty
        · rw [hBcolor_eq hyB hne]
          exact (hBcolor_ne_zero (bPull y hyB hne)
            (bPull y hyB hne).property).symm
        · rw [hBempty hyB hne]
          decide
      · exact (hyS.2.2.1 hxy).elim
    · subst x
      rcases hpart y with hyu | hyv | hyA | hyB | hyS
      · subst y; rw [hcv, hcu]; decide
      · exact (hxy_ne hyv.symm).elim
      · rw [hcv, hca hyA]
        by_cases hne : (residualType G u v y).Nonempty
        · rw [hAcolor_eq hyA hne]
          exact (hAcolor_ne_one (aPull y hyA hne)
            (aPull y hyA hne).property).symm
        · rw [hAempty hyA hne]
          decide
      · exact (hnot_v_B hyB hxy).elim
      · exact (hyS.2.2.2 hxy).elim
    · rcases hpart y with hyu | hyv | hyA | hyB | hyS
      · subst y; exact (hnot_u_A hxA hxy.symm).elim
      · subst y; rw [hca hxA, hcv]
        by_cases hne : (residualType G u v x).Nonempty
        · rw [hAcolor_eq hxA hne]
          exact hAcolor_ne_one (aPull x hxA hne)
            (aPull x hxA hne).property
        · rw [hAempty hxA hne]
          decide
      · exact ((edgeSideASet_independent htri u v hxA hyA hxy_ne) hxy).elim
      · rw [hca hxA, hcb hyB]
        by_cases hneA : (residualType G u v x).Nonempty
        · by_cases hneB : (residualType G u v y).Nonempty
          · have hdis : Disjoint (aPull x hxA hneA).1 (bPull y hyB hneB).1 := by
              have hdis0 := (cross_adj_iff_residual_disjoint hmax huv hxA hyB).mp hxy
              rw [Finset.disjoint_left]
              intro q hqA hqB
              apply Set.disjoint_left.mp hdis0
              change q ∈ (residualTypeFinset G u v x).preimage f f.injective.injOn at hqA
              change q ∈ (residualTypeFinset G u v y).preimage f f.injective.injOn at hqB
              · exact mem_residualTypeFinset_iff.mp
                  ((Finset.mem_preimage (f := f)
                    (s := residualTypeFinset G u v x)
                    (hf := f.injective.injOn) (x := q)).mp hqA)
              · exact mem_residualTypeFinset_iff.mp
                  ((Finset.mem_preimage (f := f)
                    (s := residualTypeFinset G u v y)
                    (hf := f.injective.injOn) (x := q)).mp hqB)
            rw [hAcolor_eq hxA hneA, hBcolor_eq hyB hneB]
            apply s6_table_cross_J_compatible j (aPull x hxA hneA) (bPull y hyB hneB)
            · exact hsub.1 (aPull x hxA hneA).property
            · exact hsub.2 (bPull y hyB hneB).property
            · exact hAavoid _ (aPull x hxA hneA).property
            · exact hBavoid _ (bPull y hyB hneB).property
            · exact hdis
          · rw [hBempty hyB hneB]
            rw [hAcolor_eq hxA hneA]
            exact hAcolor_ne_one (aPull x hxA hneA)
              (aPull x hxA hneA).property
        · rw [hAempty hxA hneA]
          by_cases hneB : (residualType G u v y).Nonempty
          · rw [hBcolor_eq hyB hneB]
            exact (hBcolor_ne_zero (bPull y hyB hneB)
              (bPull y hyB hneB).property).symm
          · rw [hBempty hyB hneB]
            decide
      · rw [hca hxA, hcs hyS]
        by_cases hne : (residualType G u v x).Nonempty
        · exact hAcolor hxA hne hyS hxy
        · exact (hne ⟨y, hxy, hyS⟩).elim
    · rcases hpart y with hyu | hyv | hyA | hyB | hyS
      · subst y; rw [hcb hxB, hcu]
        by_cases hne : (residualType G u v x).Nonempty
        · rw [hBcolor_eq hxB hne]
          exact hBcolor_ne_zero (bPull x hxB hne)
            (bPull x hxB hne).property
        · rw [hBempty hxB hne]
          decide
      · subst y; exact (hnot_v_B hxB hxy.symm).elim
      · rw [hcb hxB, hca hyA]
        by_cases hneA : (residualType G u v x).Nonempty
        · by_cases hneB : (residualType G u v y).Nonempty
          · have hdis : Disjoint (aPull y hyA hneB).1 (bPull x hxB hneA).1 := by
              have hdis0 := (cross_adj_iff_residual_disjoint hmax huv hyA hxB).mp hxy.symm
              rw [Finset.disjoint_left]
              intro q hqA hqB
              apply Set.disjoint_left.mp hdis0
              change q ∈ (residualTypeFinset G u v y).preimage f f.injective.injOn at hqA
              change q ∈ (residualTypeFinset G u v x).preimage f f.injective.injOn at hqB
              · exact mem_residualTypeFinset_iff.mp
                  ((Finset.mem_preimage (f := f)
                    (s := residualTypeFinset G u v y)
                    (hf := f.injective.injOn) (x := q)).mp hqA)
              · exact mem_residualTypeFinset_iff.mp
                  ((Finset.mem_preimage (f := f)
                    (s := residualTypeFinset G u v x)
                    (hf := f.injective.injOn) (x := q)).mp hqB)
            rw [hBcolor_eq hxB hneA, hAcolor_eq hyA hneB]
            exact (s6_table_cross_J_compatible j (aPull y hyA hneB) (bPull x hxB hneA)
              (hsub.1 (aPull y hyA hneB).property) (hsub.2 (bPull x hxB hneA).property)
              (hAavoid _ (aPull y hyA hneB).property)
              (hBavoid _ (bPull x hxB hneA).property) hdis).symm
          · rw [hAempty hyA hneB]
            rw [hBcolor_eq hxB hneA]
            exact hBcolor_ne_zero (bPull x hxB hneA)
              (bPull x hxB hneA).property
        · rw [hBempty hxB hneA]
          by_cases hneB : (residualType G u v y).Nonempty
          · rw [hAcolor_eq hyA hneB]
            exact (hAcolor_ne_one (aPull y hyA hneB)
              (aPull y hyA hneB).property).symm
          · rw [hAempty hyA hneB]
            decide
      · exact ((edgeSideBSet_independent htri u v hxB hyB hxy_ne) hxy).elim
      · rw [hcb hxB, hcs hyS]
        by_cases hne : (residualType G u v x).Nonempty
        · exact hBcolor hxB hne hyS hxy
        · exact (hne ⟨y, hxy, hyS⟩).elim
    · rcases hpart y with hyu | hyv | hyA | hyB | hyS
      · subst y; exact (hxS.2.2.1 hxy.symm).elim
      · subst y; exact (hxS.2.2.2 hxy.symm).elim
      · rw [hcs hxS, hca hyA]
        by_cases hne : (residualType G u v y).Nonempty
        · exact (hAcolor hyA hne hxS hxy.symm).symm
        · exact (hne ⟨x, hxy.symm, hxS⟩).elim
      · rw [hcs hxS, hcb hyB]
        by_cases hne : (residualType G u v y).Nonempty
        · exact (hBcolor hyB hne hxS hxy.symm).symm
        · exact (hne ⟨x, hxy.symm, hxS⟩).elim
      · have hHxy : s6c5Graph.Adj
          (e.toEquiv ⟨x, hxS⟩) (e.toEquiv ⟨y, hyS⟩) := by
          have hfx : f (e.toEquiv ⟨x, hxS⟩) = x := by
            dsimp [f, residualSixEmbeddingOfC5Iso]
            exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hxS⟩)
          have hfy : f (e.toEquiv ⟨y, hyS⟩) = y := by
            dsimp [f, residualSixEmbeddingOfC5Iso]
            exact congrArg Subtype.val (e.symm_apply_apply ⟨y, hyS⟩)
          apply (hgraph _ _).mp
          have hxy' : G.Adj (f (e.toEquiv ⟨x, hxS⟩))
              (f (e.toEquiv ⟨y, hyS⟩)) := by
            rw [hfx, hfy]
            exact hxy
          exact hxy'
        rw [hcs hxS, hcs hyS]
        exact s6_table_core_J_proper j _ _ hHxy
  exact ⟨Coloring.mk c hvalid⟩

run_cmd R5Kernel.checkStandardAxioms ``r5_s6_c5_isolated_four_colorable_of_vd_count_le_four

end Erdos1011

end Web_Erdos1011_R5S6Coloring
