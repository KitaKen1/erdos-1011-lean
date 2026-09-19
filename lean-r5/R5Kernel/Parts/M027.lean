import R5Kernel.Parts.M026

/- Source module: Erdos1011.R5FiniteSixBridge. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_R5FiniteSixBridge


namespace Erdos1011

open SimpleGraph

/- A colour-image set with at most two colours misses one of the three
   colours.  Unlike the older cardinal lemma in `SmallResidual`, the domain
   `T` itself may be large; only its image under `C` is bounded. -/
theorem exists_fin3_color_avoiding_of_image_card_le_two
    {V : Type*} [Finite V] [DecidableEq V]
    (C : V → Fin 3) {T : Set V} (hT : T.Finite)
    (hcard : (hT.toFinset.image C).card ≤ 2) :
    ∃ d : Fin 3, ∀ x : V, x ∈ T → C x ≠ d := by
  classical
  by_contra h
  have hcover : ∀ d : Fin 3, ∃ x : V, x ∈ T ∧ C x = d := by
    intro d
    by_contra hd
    push_neg at hd
    apply h
    refine ⟨d, ?_⟩
    intro x hx
    exact hd x hx
  have himage : ∀ d : Fin 3, d ∈ hT.toFinset.image C := by
    intro d
    rcases hcover d with ⟨x, hx, hxd⟩
    exact Finset.mem_image.mpr ⟨x, hT.mem_toFinset.mpr hx, hxd⟩
  have hcard3 : 3 ≤ (hT.toFinset.image C).card := by
    have hsub : (Finset.univ : Finset (Fin 3)) ⊆ hT.toFinset.image C := by
      intro d hd
      exact himage d
    have hle := Finset.card_le_card hsub
    simpa using hle
  omega
open scoped BigOperators

/-! First graph-level consequences of the six-vertex finite certificate.

The finite certificate itself is deliberately agnostic about how the six
vertices arose.  This file starts the transport layer: it exposes the
ordinary 3-colourability consequence and records the finite relabelling lemma
needed to put an arbitrary labelled C₅ plus one vertex into the fixed model.
-/

theorem fin6_equiv_of_fin5_injective_outside
    {f : Fin 5 → Fin 6} (hf : Function.Injective f)
    {z : Fin 6} (hz : ∀ i : Fin 5, z ≠ f i) :
    ∃ e : Fin 6 ≃ Fin 6,
      (∀ i : Fin 5, e ⟨i.1, by omega⟩ = f i) ∧ e 5 = z := by
  let g : Fin 6 → Fin 6 := fun i =>
    if hi : i.val < 5 then f ⟨i.val, hi⟩ else z
  have hg_inj : Function.Injective g := by
    intro i j hij
    by_cases hi : i.val < 5
    · by_cases hj : j.val < 5
      · have hfj : f ⟨i.val, hi⟩ = f ⟨j.val, hj⟩ := by
          simpa [g, hi, hj] using hij
        have hji : (⟨i.val, hi⟩ : Fin 5) = ⟨j.val, hj⟩ := hf hfj
        have hv := congrArg Fin.val hji
        apply Fin.ext
        simpa using hv
      · have hj5 : j = 5 := by
          apply Fin.ext
          omega
        rw [hj5] at hij ⊢
        have : f ⟨i.val, hi⟩ ≠ z := (hz ⟨i.val, hi⟩).symm
        simpa [g, hi] using (this (by simpa [g, hi] using hij))
    · have hi5 : i = 5 := by
        apply Fin.ext
        omega
      rw [hi5] at hij ⊢
      by_cases hj : j.val < 5
      · have : z ≠ f ⟨j.val, hj⟩ := hz ⟨j.val, hj⟩
        simpa [g, hj] using (this (by simpa [g, hj] using hij))
      · have hjval : j.val = 5 := by omega
        apply Fin.ext
        omega
  have hg_surj : Function.Surjective g :=
    (Finite.injective_iff_surjective).mp hg_inj
  have hg : Function.Bijective g := ⟨hg_inj, hg_surj⟩
  let e : Fin 6 ≃ Fin 6 := Equiv.ofBijective g hg
  refine ⟨e, ?_, ?_⟩
  · intro i
    dsimp [e, g]
    simp [show i.val < 5 by omega]
  · dsimp [e, g]

theorem exists_fin5_bitmask
    (P : Fin 5 → Prop) [DecidablePred P] :
    ∃ k : Fin 32, ∀ i : Fin 5, attachBit5 k i ↔ P i := by
  classical
  let kNat : ℕ := ∑ i : Fin 5, if P i then 2 ^ i.1 else 0
  have hk_le : kNat ≤ 31 := by
    dsimp [kNat]
    calc
      (∑ i : Fin 5, if P i then 2 ^ i.1 else 0) ≤
          ∑ i : Fin 5, 2 ^ i.1 := by
            apply Finset.sum_le_sum
            intro i hi
            split
            · rfl
            · exact Nat.zero_le _
      _ = 31 := by decide +kernel
  refine ⟨⟨kNat, by omega⟩, ?_⟩
  intro i
  have huniv : (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} := by
    decide +kernel
  fin_cases i <;>
    by_cases h0 : P 0 <;> by_cases h1 : P 1 <;>
      by_cases h2 : P 2 <;> by_cases h3 : P 3 <;>
        by_cases h4 : P 4 <;>
          simp [attachBit5, kNat, huniv, h0, h1, h2, h3, h4] <;> norm_num

theorem attached_c5_fin6_canonical
    {H : SimpleGraph (Fin 6)}
    (htri : triangleFree6 H) (hatt : attachedC5In6 H) :
    ∃ e : Fin 6 ≃ Fin 6, ∃ k : Fin 32,
      (∀ x y : Fin 6,
        H.Adj (e x) (e y) ↔ (canonicalC5Graph5 k).Adj x y) ∧
      good6 (canonicalC5Graph5 k) := by
  classical
  letI : DecidableRel H.Adj := Classical.decRel _
  rcases hatt with ⟨f, z, hf, hcycle, hz, ⟨i, hzi⟩⟩
  obtain ⟨e, hecycle, hez⟩ := fin6_equiv_of_fin5_injective_outside hf hz
  let P : Fin 5 → Prop := fun j => H.Adj z (f j)
  letI : DecidablePred P := fun j => inferInstanceAs (Decidable (P j))
  obtain ⟨k, hk⟩ := exists_fin5_bitmask P
  have hattk : canonicalC5Attached5 k := by
    refine ⟨i, ?_⟩
    change (5 : Fin 6) ≠ ⟨i.1, by omega⟩ ∧
      (canonicalC5Rel5 k 5 ⟨i.1, by omega⟩ ∨
        canonicalC5Rel5 k ⟨i.1, by omega⟩ 5)
    refine ⟨?_, Or.inl (Or.inr ?_)⟩
    · intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    · refine ⟨rfl, ?_⟩
      exact ⟨i.isLt, (hk i).mpr hzi⟩
  have hc0 : H.Adj (f 0) (f 1) := by simpa using hcycle 0
  have hc1 : H.Adj (f 1) (f 2) := by simpa using hcycle 1
  have hc2 : H.Adj (f 2) (f 3) := by simpa using hcycle 2
  have hc3 : H.Adj (f 3) (f 4) := by simpa using hcycle 3
  have hc4 : H.Adj (f 4) (f 0) := by simpa using hcycle 4
  have hc4' : H.Adj (f 0) (f 4) := by
    simpa only [H.adj_comm] using hc4
  have hn02 : ¬ H.Adj (f 0) (f 2) := by
    intro h02
    exact htri (f 0) (f 1) (f 2) hc0 h02 hc1
  have hn03 : ¬ H.Adj (f 0) (f 3) := by
    intro h03
    exact htri (f 0) (f 4) (f 3) hc4.symm h03 hc3.symm
  have hn13 : ¬ H.Adj (f 1) (f 3) := by
    intro h13
    exact htri (f 1) (f 2) (f 3) hc1 h13 hc2
  have hn14 : ¬ H.Adj (f 1) (f 4) := by
    intro h14
    exact htri (f 1) (f 0) (f 4) hc0.symm h14 hc4.symm
  have hn24 : ¬ H.Adj (f 2) (f 4) := by
    intro h24
    exact htri (f 2) (f 3) (f 4) hc2 h24 hc3
  have he0 : e (0 : Fin 6) = f 0 := by simpa using hecycle 0
  have he1 : e (1 : Fin 6) = f 1 := by simpa using hecycle 1
  have he2 : e (2 : Fin 6) = f 2 := by simpa using hecycle 2
  have he3 : e (3 : Fin 6) = f 3 := by simpa using hecycle 3
  have he4 : e (4 : Fin 6) = f 4 := by simpa using hecycle 4
  have he5 : e (5 : Fin 6) = z := hez
  have hb0 : H.Adj z (f 0) ↔ (k.1 % 2 = 1) := by
    simpa [P, attachBit5] using (hk 0).symm
  have hb1 : H.Adj z (f 1) ↔ (k.1 / 2 % 2 = 1) := by
    simpa [P, attachBit5] using (hk 1).symm
  have hb2 : H.Adj z (f 2) ↔ (k.1 / 4 % 2 = 1) := by
    simpa [P, attachBit5] using (hk 2).symm
  have hb3 : H.Adj z (f 3) ↔ (k.1 / 8 % 2 = 1) := by
    simpa [P, attachBit5] using (hk 3).symm
  have hb4 : H.Adj z (f 4) ↔ (k.1 / 16 % 2 = 1) := by
    simpa [P, attachBit5] using (hk 4).symm
  have hgraph : ∀ x y : Fin 6,
      H.Adj (e x) (e y) ↔ (canonicalC5Graph5 k).Adj x y := by
    intro x y
    fin_cases x <;> fin_cases y
    all_goals simp only [canonicalC5Graph5, SimpleGraph.fromRel_adj,
      canonicalC5Rel5, cycleRel, attachBit5Fin6, attachBit5]
    all_goals simp [he0, he1, he2, he3, he4, he5, P, hk, hb0, hb1, hb2, hb3, hb4,
      hc0, hc1, hc2, hc3, hc4, hc4', hn02, hn03, hn13, hn14, hn24,
      SimpleGraph.adj_comm]
  have htriK : triangleFree6 (canonicalC5Graph5 k) := by
    intro x y z hxy hxz hyz
    apply htri (e x) (e y) (e z)
    · exact (hgraph x y).mpr hxy
    · exact (hgraph x z).mpr hxz
    · exact (hgraph y z).mpr hyz
  have hgood := finite_canonical_c5_attached_good k htriK hattk
  exact ⟨e, k, hgraph, hgood⟩

/- The extra `good6` condition is invariant under relabelling.  This is kept
   explicit because the independent-set colour-image bound is stronger than
   ordinary 3-colourability. -/
theorem good6_of_iso {H K : SimpleGraph (Fin 6)} (e : H ≃g K)
    (hK : good6 K) : good6 H := by
  classical
  rcases hK with ⟨C, hCproper, hCgood⟩
  let c : Fin 6 → Fin 3 := fun x => C (e.toEquiv x)
  have hproper : ∀ x y : Fin 6, H.Adj x y → c x ≠ c y := by
    intro x y hxy
    exact hCproper (e.toEquiv x) (e.toEquiv y) ((e.map_rel_iff).mpr hxy)
  have himage : ∀ I : Finset (Fin 6), H.IsIndepSet (I : Set (Fin 6)) →
      (I.image c).card ≤ 2 := by
    intro I hI
    let J : Finset (Fin 6) := I.image e.toEquiv
    have hJind : K.IsIndepSet (J : Set (Fin 6)) := by
      intro x hx y hy hxy
      rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
      have hab : a ≠ b := by
        intro hab
        exact hxy (congrArg e.toEquiv hab)
      intro hAdj
      exact hI ha hb hab ((e.map_rel_iff).mp hAdj)
    have hbound := hCgood J hJind
    simpa [J, c, Function.comp_def, Finset.image_image] using hbound
  exact ⟨c, hproper, himage⟩

theorem attached_c5_fin6_good
    {H : SimpleGraph (Fin 6)}
    (htri : triangleFree6 H) (hatt : attachedC5In6 H) : good6 H := by
  rcases attached_c5_fin6_canonical htri hatt with ⟨e, k, hgraph, hK⟩
  let iso : canonicalC5Graph5 k ≃g H :=
    { toEquiv := e
      map_rel_iff' := by
        intro x y
        exact hgraph x y }
  exact good6_of_iso iso.symm hK

/- Export the colouring part in a form whose domain may be an arbitrary
   finite residual subtype. -/
theorem good_coloring_of_iso
    {V : Type*} {H : SimpleGraph V} {K : SimpleGraph (Fin 6)}
    (e : H ≃g K) (hK : good6 K) :
    ∃ C : H.Coloring (Fin 3),
      ∀ I : Finset V, H.IsIndepSet (I : Set V) →
        (I.image C).card ≤ 2 := by
  classical
  rcases hK with ⟨c, hCproper, hCgood⟩
  let cf : V → Fin 3 := fun x => c (e.toEquiv x)
  have hproper : ∀ {x y : V}, H.Adj x y → cf x ≠ cf y := by
    intro x y hxy
    exact hCproper (e.toEquiv x) (e.toEquiv y) ((e.map_rel_iff).mpr hxy)
  have himage : ∀ I : Finset V, H.IsIndepSet (I : Set V) →
      (I.image cf).card ≤ 2 := by
    intro I hI
    let J : Finset (Fin 6) := I.image e.toEquiv
    have hJind : K.IsIndepSet (J : Set (Fin 6)) := by
      intro x hx y hy hxy
      rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
      have hab : a ≠ b := by
        intro hab
        exact hxy (congrArg e.toEquiv hab)
      intro hAdj
      exact hI ha hb hab ((e.map_rel_iff).mp hAdj)
    have hbound := hCgood J hJind
    simpa [J, cf, Function.comp_def, Finset.image_image] using hbound
  exact ⟨Coloring.mk cf hproper, himage⟩

theorem induced_good_coloring_of_attached_c5
    {n : ℕ} {G : SimpleGraph (Fin n)} {S : Set (Fin n)}
    (htri : G.CliqueFree 3) {H : SimpleGraph (Fin 6)}
    (e : (G.induce S) ≃g H) (hatt : attachedC5In6 H) :
    ∃ C : (G.induce S).Coloring (Fin 3),
      ∀ I : Finset S, (G.induce S).IsIndepSet (I : Set S) →
        (I.image C).card ≤ 2 := by
  classical
  have hInd : (G.induce S).CliqueFree 3 := by
    intro t ht
    exact htri (t.map (.subtype S))
      ((SimpleGraph.isNClique_induce_iff (G := G) S t 3).mp ht)
  have hHtri : H.CliqueFree 3 := cliqueFree_three_of_hom e.symm.toHom hInd
  have hHtri6 : triangleFree6 H := by
    intro x y z hxy hxz hyz
    exact hHtri _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy, hxz, hyz⟩)
  have hgood : good6 H := by
    exact attached_c5_fin6_good hHtri6 hatt
  exact good_coloring_of_iso e hgood

/- Convert the finite colour-image certificate into the missing-colour
   hypothesis consumed by the endpoint/sides extension lemma. -/
theorem residual_good_coloring_missing_colors
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (htri : G.CliqueFree 3) (huv : G.Adj u v)
    (C : (G.induce (residualSet G u v)).Coloring (Fin 3))
    (hImage : ∀ I : Finset (residualSet G u v),
      (G.induce (residualSet G u v)).IsIndepSet (I : Set (residualSet G u v)) →
      (I.image C).card ≤ 2) :
    ∀ y, y ∈ edgeSideBSet G u v →
      ∃ d : Fin 3, ∀ z : residualSet G u v,
        (z : Fin n) ∈ residualType G u v y → C z ≠ d := by
  classical
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
    have hind := residualType_independent htri (u := u) (v := v) y ha' hb' hab'
    intro hadj
    exact hind (by simpa only [SimpleGraph.induce_adj] using hadj)
  let hTfinite : T.Finite := Set.toFinite T
  let IT : Finset (residualSet G u v) := hTfinite.toFinset
  have hIT : (G.induce (residualSet G u v)).IsIndepSet (IT : Set (residualSet G u v)) := by
    intro a ha b hb hab
    apply hTind
    · exact hTfinite.mem_toFinset.mp ha
    · exact hTfinite.mem_toFinset.mp hb
    · exact hab
  have hcard : (hTfinite.toFinset.image C).card ≤ 2 := by
    exact hImage IT hIT
  obtain ⟨d, hd⟩ :=
    exists_fin3_color_avoiding_of_image_card_le_two C hTfinite hcard
  refine ⟨d, ?_⟩
  intro z hz
  exact hd z hz

run_cmd R5Kernel.checkStandardAxioms ``attached_c5_fin6_good
run_cmd R5Kernel.checkStandardAxioms ``residual_good_coloring_missing_colors

end Erdos1011

end Web_Erdos1011_R5FiniteSixBridge
