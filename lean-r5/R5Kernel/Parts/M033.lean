import R5Kernel.Parts.M030

/- Source module: Erdos1011Final. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011Final


/-!
# Verified lower-bound fragment

This file contains the currently solved Lean fragment: the blow-up edge
polynomial identity, the explicit r=5 graph construction, and its all-`n`
lower-bound witnesses.  The graph-theoretic upper bounds and the
6408/2503/858 certificate claims remain explicit candidate theorems in
`Erdos1011Target.lean` until their proof assets are recovered.
-/

namespace Erdos1011

open SimpleGraph

/-! The S9-C5 vertical slice is now replayable from the generated tables:
    profile data, all signature-level D3 checks, and all row-level D4/direct/
    metadata checks are exposed as one kernel-checked conjunction. -/

/- The two S10 labelled/non-cycle universes are now checked in the same
   final environment as the imported pure-cycle slices.  Their finite
   universes are explicit independent-set Finsets, so no cycle parametrisation
   is being assumed here. -/

/- Alias the full finite S9--S11 generated gate in the final namespace.  The
   statement is inferred from the already checked aggregate theorem, avoiding
   a second copy of its large conjunction in this file. -/

/- A compact final gate for the imported profile-compressed slices.  The
   remaining pure-cycle files are audited one at a time by
   `tools/audit_r5_dual_cycle_cases.py`; keeping this gate to the imported
   modules bounds the default elaboration footprint on the 24GB workstation. -/

/- The September 10 all-`n` candidate has a different small branch.  The
   standard double-Mycielski construction is already sufficient from n=27;
   the 22-point 72-edge lower witness and the 24--27 exceptional lower
   witnesses are now checked; the 23-point 80-edge witness is obtained by a
   checked twin extension of the 22-point kernel, while all small-order upper
   certificates remain separate finite-data tasks. -/

/- The 22-point, 70-edge kernel from the GKV construction is checked as
   finite data.  Its no-4-colouring obstruction is imported from the separate
   LRAT certificate module below. -/

/- The independently selected 72-edge member of the complete 22-vertex
   triangle-free 5-chromatic graph list is now also kernel-checked. -/

/- The 15-row MTF-22 catalogue has the same checked edge-bound and saturation
   interface as the larger 23-row catalogue. -/

/- It is enough to enumerate the edge-maximal triangle-free members.  Any
   high graph can be extended to such a member on the same vertex set, while
   preserving the chromatic lower bound. -/

/- The finite-catalogue upper interface for the 23-point branch.  A complete
   MTF catalogue only has to discharge `hcatalog`; the extremal reduction from
   arbitrary high-five graphs to an edge-maximal one is proved here. -/

/- A concrete-catalogue interface for the remaining finite upper-bound step.
   The 2729 graph6 entries can later be decoded into `graph`; the theorem
   itself only trusts the explicit completeness and per-entry edge bound
   fields, keeping the external enumeration premise visible. -/

/- For the numerical upper bound, the `high` and `maximal` fields of the full
   catalogue certificate are not needed: completeness is stated only for the
   already-high input graph, and the edge bound is the sole property used on
   the selected representative.  This lightweight certificate is the shortest
   path to the 23-vertex equality. -/

/- The embedded House-of-Graphs rows already carry their per-entry edge
   checks.  Only the non-formalized completeness/isomorphism premise remains
   in this concrete bridge. -/

/- As for order 22, the natural HoG premise classifies only the maximal
   triangle-free high graphs.  The generic finite-catalogue bridge then turns
   that premise into the numerical upper bound without importing 315457
   non-maximal rows. -/

/- The first 80-edge entry reported by the audit is row 33 (zero-based).  Its
   graph6 payload is the selected twinized witness, so the lower-bound object
   is visibly present in the embedded catalogue. -/

/- Once an external audit supplies the 4-colour obstructions and the
   completeness/isomorphism map, all fields of the catalogue certificate are
   filled by checked data above. -/

/- A full certificate record for the 22-vertex catalogue.  The only
   non-local premise is completeness up to graph isomorphism; all fifteen
   candidate rows, their maximality/edge bounds, and their 4-colour
   obstructions are kernel-checked in the imported modules. -/

/- The checked witnesses now cover the complete conjectural lower-bound
   branch from the first admissible order.  This theorem deliberately proves
   only the lower inequality: the matching upper certificates for 22--27 and
   the residual all-`n` upper argument are separate obligations below. -/

/- The inequality above can be strengthened to the witness form expected by
   the final `IsGreatest` wrapper.  Every finite exceptional case is supplied
   by its checked kernel/twin graph; the tail uses the parameterized
   double-Mycielski construction. -/

/- Final upper-bound assembler.  The first two arguments are precisely the
   maximal House-of-Graphs completeness maps; the latter three arguments are
   the finite exceptional, 28--79, and residual-tail certificates.  Keeping
   these as explicit inputs makes the remaining proof obligations auditable. -/

/- Once the pointwise upper certificate is supplied, this is the single
   invocation that closes the complete piecewise r=5 statement. -/

/- The finite model card table is exported through the root verification file
   so certificate generators can depend on one checked interface.  The
   underlying proofs enumerate only subsets of `Fin 10`/`Fin 11`; no graph
   enumeration on the ambient `Fin n` is involved. -/

/- A graph-level wrapper for the arithmetic dispatcher.  Once the extremal
   edge, the finite residual certificate, and the support-surplus bound have
   been supplied, the candidate upper bound is an immediate kernel theorem.
   The additive edge identity handles either ordering of the cross term and
   total support weight, so no hidden subtraction-side condition is needed. -/

/- The arithmetic endgame for the six-point residual branch.  The finite
   S₆ certificate is deliberately supplied separately: this theorem records
   exactly how its `e ≤ 5` and `F ≤ 0` outputs close the r=5 candidate.
   The remaining work is structural (constructing `f` and the two transported
   support-family equalities, and proving the V/D count condition).
-/

/- The six-point arithmetic itself only needs n ≥ 80.  This direct version
   bypasses the common s=6,...,11 dispatcher, whose shared threshold is still
   1248 for the larger residual cases. -/
theorem verified_r5_upper_from_residual_s6_certificate_80
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n}
    (hmax : IsEdgeMaximalTriangleFree G)
    (huv : G.Adj u v)
    (hnoA : ∀ x x', x ∈ edgeSideASet G u v →
      x' ∈ edgeSideASet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    (hnoB : ∀ x x', x ∈ edgeSideBSet G u v →
      x' ∈ edgeSideBSet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    (hn : 80 ≤ n)
    (hS : (residualSet G u v).ncard = 6)
    (he : (G.induce (residualFinset G u v : Set (Fin n))).edgeFinset.card ≤ 5)
    (hq : supportSurplus (supportFamilyA G u v)
      (supportFamilyB G u v) ≤ 0) :
    edgeCount G ≤ fiveCandidate n := by
  have hsum := full_side_degree_residual_card_sum hmax.1 huv
  rw [hS] at hsum
  have hdecomp := edgeCount_le_full_product_plus_residual_bound_of_additive
    (G := G) hmax huv hnoA hnoB (e := 5) (q := 0) he hq
  apply residual_decomposition_bound_s6 hn
    (a := (sideAFinset G u v).card.succ)
    (b := (sideBFinset G u v).card.succ)
    (e := 5) (q := 0) (m := edgeCount G)
  · exact hsum
  · omega
  · omega
  · simpa using hdecomp

/- A graph-level consequence of the finite six-vertex colouring certificate:
   if the six-point residual is identified with a triangle-free C₅ plus an
   attached sixth vertex, the ambient graph is four-colourable, contradicting
   a high-five witness.  This closes that structural subcase; it does not yet
   supply the support-family certificate for the remaining C₅ ⊔ K₁ case. -/
theorem verified_r5_s6_attached_c5_impossible
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : HighChromaticTriangleFree 5 n G) {u v : Fin n} (huv : G.Adj u v)
    {H : SimpleGraph (Fin 6)}
    (e : (G.induce (residualSet G u v)) ≃g H)
    (hatt : attachedC5In6 H) : False := by
  obtain ⟨C, hImage⟩ := induced_good_coloring_of_attached_c5 hG.1 e hatt
  have hmissing := residual_good_coloring_missing_colors hG.1 huv C hImage
  have h4 := colorable_four_of_residual_missing_color hG.1 huv C hmissing
  have hbad : (5 : ℕ∞) ≤ 4 := hG.2.trans h4.chromaticNumber_le
  norm_num at hbad

/- The finite shape certificate now applies directly to any six-point
   residual of a high-five triangle-free graph.  The attached branch is
   eliminated by the theorem above; the remaining branch is exactly the
   isolated-C₅ support interface below. -/
theorem verified_r5_s6_shape_of_high_five
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : HighChromaticTriangleFree 5 n G) {u v : Fin n} (huv : G.Adj u v)
    {H : SimpleGraph (Fin 6)} [DecidableRel H.Adj]
    (e : (G.induce (residualSet G u v)) ≃g H) :
    attachedC5In6 H ∨ graphIsoS6C5 H := by
  exact induced_six_shape_classification hG.1 e
    (residual_not_colorable_two_of_high_five hG huv)

/- The isolated C₅ branch is likewise impossible whenever the transported
   V/D support count is at most four: the explicit rotated table gives a
   four-colouring of the whole ambient graph. -/

/- The complementary six-vertex shape `C₅ ⊔ K₁` now has a graph-to-capacity
   interface as well.  The hypotheses `h𝒜T`, `hℬT`, and `hcount` are exactly
   the structural outputs still to be proved from the extremal reduction; the
   finite support table itself is no longer hidden behind an abstract q bound. -/

/- The preceding interface is often supplied by a residual graph isomorphism
   rather than by an explicitly chosen ambient embedding.  This wrapper makes
   that conversion definitional and records no additional mathematical
   assumption. -/

/- In the high-five setting the three structural hypotheses of the previous
   wrapper are automatic.  The two T-family inclusions are forced by the
   rotated colouring obstruction; the V/D count is forced because a count at
   most four would give the forbidden four-colouring. -/
theorem verified_r5_s6_c5_isolated_vd_count_ge_five
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : HighChromaticTriangleFree 5 n G)
    (hmax : IsEdgeMaximalTriangleFree G)
    {u v : Fin n} (huv : G.Adj u v)
    (e : (G.induce (residualSet G u v)) ≃g s6c5Graph) :
    5 ≤
      (∑ I ∈ pullSupportFamilyEmbedding (residualSixEmbeddingOfC5Iso e)
          (supportFamilyA G u v) \ s6TFamily,
        if I ∈ s6VDFamily then 1 else 0) +
      (∑ J ∈ pullSupportFamilyEmbedding (residualSixEmbeddingOfC5Iso e)
          (supportFamilyB G u v) \ s6TFamily,
        if J ∈ s6VDFamily then 1 else 0) := by
  by_contra hlt
  have hle :
      (∑ I ∈ pullSupportFamilyEmbedding (residualSixEmbeddingOfC5Iso e)
          (supportFamilyA G u v) \ s6TFamily,
        if I ∈ s6VDFamily then 1 else 0) +
      (∑ J ∈ pullSupportFamilyEmbedding (residualSixEmbeddingOfC5Iso e)
          (supportFamilyB G u v) \ s6TFamily,
        if J ∈ s6VDFamily then 1 else 0) ≤ 4 := by
    omega
  have h4 := r5_s6_c5_isolated_four_colorable_of_vd_count_le_four
    hG.1 hmax huv e hle
  have hbad : (5 : ℕ∞) ≤ 4 := hG.2.trans h4.chromaticNumber_le
  norm_num at hbad

theorem verified_r5_upper_from_residual_s6_c5_isolated_auto
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n}
    (hG : HighChromaticTriangleFree 5 n G)
    (hmax : IsEdgeMaximalTriangleFree G)
    (huv : G.Adj u v)
    (hnoA : ∀ x x', x ∈ edgeSideASet G u v →
      x' ∈ edgeSideASet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    (hnoB : ∀ x x', x ∈ edgeSideBSet G u v →
      x' ∈ edgeSideBSet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    (hn : 80 ≤ n)
    (hS : (residualSet G u v).ncard = 6)
    (he : (G.induce (residualFinset G u v : Set (Fin n))).edgeFinset.card ≤ 5)
    (e : (G.induce (residualSet G u v)) ≃g s6c5Graph) :
    edgeCount G ≤ fiveCandidate n := by
  have h𝒜T := r5_s6_c5_isolated_high_five_forces_TFamily_A hG huv e
  have hℬT := r5_s6_c5_isolated_high_five_forces_TFamily_B hG huv e
  have hcount := verified_r5_s6_c5_isolated_vd_count_ge_five hG hmax huv e
  let f := residualSixEmbeddingOfC5Iso e
  have hq : supportSurplus (supportFamilyA G u v)
      (supportFamilyB G u v) ≤ 0 :=
    r5_s6_support_surplus_nonpositive_of_residual_embedding hmax.1 f
      (residualSixEmbeddingOfC5Iso_range e)
      (residualSixEmbeddingOfC5Iso_graph e) h𝒜T hℬT hcount
  exact verified_r5_upper_from_residual_s6_certificate_80 hmax huv hnoA hnoB
    hn hS he hq

/- The shape theorem can be composed with the residual labelling: under a
   high-five hypothesis the attached branch is impossible, so every six-point
   residual graph is actually isomorphic to the fixed isolated-C₅ model. -/
theorem verified_r5_s6_isolated_iso_nonempty_of_high_five
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : HighChromaticTriangleFree 5 n G)
    {u v : Fin n} (huv : G.Adj u v)
    {H : SimpleGraph (Fin 6)} [DecidableRel H.Adj]
    (eH : (G.induce (residualSet G u v)) ≃g H) :
    Nonempty ((G.induce (residualSet G u v)) ≃g s6c5Graph) := by
  rcases verified_r5_s6_shape_of_high_five hG huv eH with hatt | hiso
  · exact (verified_r5_s6_attached_c5_impossible hG huv eH hatt).elim
  · exact ⟨eH.trans (graphIsoS6C5Iso hiso).symm⟩

noncomputable def verified_r5_s6_isolated_iso_of_high_five
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : HighChromaticTriangleFree 5 n G)
    {u v : Fin n} (huv : G.Adj u v)
    {H : SimpleGraph (Fin 6)} [DecidableRel H.Adj]
    (eH : (G.induce (residualSet G u v)) ≃g H) :
    (G.induce (residualSet G u v)) ≃g s6c5Graph :=
  Classical.choice (verified_r5_s6_isolated_iso_nonempty_of_high_five hG huv eH)

/- The isolated model has exactly five residual edges.  Transporting its
   labelled embedding through the finite residual set gives the edge bound
   required by the decomposition identity, so this hypothesis need not be
   supplied separately once the model is known. -/
theorem verified_r5_s6_edge_count_le_five_of_iso
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n}
    (e : (G.induce (residualSet G u v)) ≃g s6c5Graph) :
    (G.induce (residualFinset G u v : Set (Fin n))).edgeFinset.card ≤ 5 := by
  let f := residualSixEmbeddingOfC5Iso e
  let T := residualFinset G u v
  have hrange : Set.range f = (T : Set (Fin n)) := by
    rw [residualSixEmbeddingOfC5Iso_range e]
    ext z
    exact (mem_residualFinset_iff (G := G) (u := u) (v := v)).symm
  let g : Fin 6 → (T : Set (Fin n)) := fun i =>
    ⟨f i, by
      have hi : f i ∈ (T : Set (Fin n)) := by
        rw [← hrange]
        exact ⟨i, rfl⟩
      exact hi⟩
  have hginj : Function.Injective g := by
    intro i j hij
    have hf : f i = f j := by
      simpa [g] using congrArg Subtype.val hij
    exact f.injective hf
  have hgsurj : Function.Surjective g := by
    intro y
    have hyT : y.1 ∈ (T : Set (Fin n)) := y.2
    have hyrange : y.1 ∈ Set.range f := by
      rw [hrange]
      exact hyT
    rcases Set.mem_range.mp hyrange with ⟨i, hi⟩
    refine ⟨i, Subtype.ext ?_⟩
    exact hi
  let eS : Fin 6 ≃ (T : Set (Fin n)) := Equiv.ofBijective g ⟨hginj, hgsurj⟩
  let isoT : G.comap f ≃g G.induce (T : Set (Fin n)) :=
    { toEquiv := eS
      map_rel_iff' := by
        intro i j
        change G.Adj (f i) (f j) ↔
          (G.induce (T : Set (Fin n))).Adj (eS i) (eS j)
        change G.Adj (f i) (f j) ↔ G.Adj (eS i).1 (eS j).1
        have hi : (eS i).1 = f i := by rfl
        have hj : (eS j).1 = f j := by rfl
        rw [hi, hj] }
  have hcardT : (G.comap f).edgeFinset.card =
      (G.induce (T : Set (Fin n))).edgeFinset.card := by
    exact isoT.card_edgeFinset_eq
  have hcardT' : (G.comap f).edgeFinset.card =
      (G.induce (residualFinset G u v : Set (Fin n))).edgeFinset.card := by
    simpa [T] using hcardT
  let isoS : s6c5Graph ≃g G.comap f :=
    { toEquiv := Equiv.refl (Fin 6)
      map_rel_iff' := by
        intro i j
        change G.Adj (f i) (f j) ↔ s6c5Graph.Adj i j
        exact residualSixEmbeddingOfC5Iso_graph e i j }
  have hcardS : s6c5Graph.edgeFinset.card =
      (G.comap f).edgeFinset.card := by
    exact isoS.card_edgeFinset_eq
  have hs6 : s6c5Graph.edgeFinset.card = 5 := by decide +kernel
  omega

/- A cardinality-six residual set can be labelled by `Fin 6` without any
   graph-shape assumption.  This is the generic counterpart of
   `residualSixEmbeddingOfC5Iso`; the latter is reserved for the isolated-C5
   branch after the finite shape classification has fired. -/
noncomputable def residualSixEmbeddingOfCardEq
    {n : ℕ} (T : Finset (Fin n)) (hT : T.card = 6) : Fin 6 ↪ Fin n :=
  (T.equivFinOfCardEq hT).symm.toEmbedding.trans
    (Function.Embedding.subtype _)

theorem residualSixEmbeddingOfCardEq_mem
    {n : ℕ} (T : Finset (Fin n)) (hT : T.card = 6) (i : Fin 6) :
    residualSixEmbeddingOfCardEq T hT i ∈ T := by
  dsimp [residualSixEmbeddingOfCardEq]
  exact (T.equivFinOfCardEq hT).symm i |>.property

theorem residualSixEmbeddingOfCardEq_range
    {n : ℕ} (T : Finset (Fin n)) (hT : T.card = 6) :
    Set.range (residualSixEmbeddingOfCardEq T hT) = (T : Set (Fin n)) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact residualSixEmbeddingOfCardEq_mem T hT i
  · intro hx
    let e : T ≃ Fin 6 := T.equivFinOfCardEq hT
    let y : T := ⟨x, hx⟩
    refine ⟨e y, ?_⟩
    dsimp [residualSixEmbeddingOfCardEq, e, y]
    simp

/- The same finite labelling interface for the seven-point residual branch.
   Keeping this separate from the canonical C5 embedding is intentional: the
   cardinality certificate only labels the residual set, while the later S7
   certificate supplies the graph shape and the C5-compatible relabelling. -/
noncomputable def residualSevenEmbeddingOfCardEq
    {n : ℕ} (T : Finset (Fin n)) (hT : T.card = 7) : Fin 7 ↪ Fin n :=
  (T.equivFinOfCardEq hT).symm.toEmbedding.trans
    (Function.Embedding.subtype _)

theorem residualSevenEmbeddingOfCardEq_mem
    {n : ℕ} (T : Finset (Fin n)) (hT : T.card = 7) (i : Fin 7) :
    residualSevenEmbeddingOfCardEq T hT i ∈ T := by
  dsimp [residualSevenEmbeddingOfCardEq]
  exact (T.equivFinOfCardEq hT).symm i |>.property

theorem residualSevenEmbeddingOfCardEq_range
    {n : ℕ} (T : Finset (Fin n)) (hT : T.card = 7) :
    Set.range (residualSevenEmbeddingOfCardEq T hT) = (T : Set (Fin n)) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact residualSevenEmbeddingOfCardEq_mem T hT i
  · intro hx
    let e : T ≃ Fin 7 := T.equivFinOfCardEq hT
    let y : T := ⟨x, hx⟩
    refine ⟨e y, ?_⟩
    dsimp [residualSevenEmbeddingOfCardEq, e, y]
    simp

theorem residualSevenComap_iso_induce
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (T : Finset (Fin n)) (hT : T.card = 7) :
    Nonempty (G.comap (residualSevenEmbeddingOfCardEq T hT) ≃g
      G.induce (T : Set (Fin n))) := by
  classical
  let f := residualSevenEmbeddingOfCardEq T hT
  let g : Fin 7 → (T : Set (Fin n)) := fun i =>
    ⟨f i, residualSevenEmbeddingOfCardEq_mem T hT i⟩
  have hginj : Function.Injective g := by
    intro i j hij
    apply f.injective
    exact congrArg Subtype.val hij
  have hgsurj : Function.Surjective g := by
    intro y
    have hyT : y.1 ∈ (T : Set (Fin n)) := y.2
    have hyrange : y.1 ∈ Set.range f := by
      rw [residualSevenEmbeddingOfCardEq_range T hT]
      exact hyT
    rcases Set.mem_range.mp hyrange with ⟨i, hi⟩
    refine ⟨i, Subtype.ext ?_⟩
    exact hi
  let eS : Fin 7 ≃ (T : Set (Fin n)) :=
    Equiv.ofBijective g ⟨hginj, hgsurj⟩
  refine ⟨{ toEquiv := eS, map_rel_iff' := ?_ }⟩
  intro i j
  change G.Adj (f i) (f j) ↔ G.Adj (eS i).1 (eS j).1
  have hi : (eS i).1 = f i := by rfl
  have hj : (eS j).1 = f j := by rfl
  rw [hi, hj]

/- The full pairwise C5 relation need not be supplied by an external
   certificate.  In a triangle-free ambient graph, the five cycle edges on
   the labelled copy force all non-cycle pairs to be non-adjacent. -/

/- The high-five S6 theorem can now be invoked from the residual cardinality
   alone.  We build the induced-to-comap graph isomorphism explicitly, then
   reuse the finite shape classification and the isolated-branch arithmetic
   wrapper. -/
theorem verified_r5_upper_from_residual_s6_high_five_cardinality
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : HighChromaticTriangleFree 5 n G)
    (hmax : IsEdgeMaximalTriangleFree G)
    {u v : Fin n} (huv : G.Adj u v)
    (hnoA : ∀ x x', x ∈ edgeSideASet G u v →
      x' ∈ edgeSideASet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    (hnoB : ∀ x x', x ∈ edgeSideBSet G u v →
      x' ∈ edgeSideBSet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    (hn : 80 ≤ n)
    (hS : (residualSet G u v).ncard = 6) :
    edgeCount G ≤ fiveCandidate n := by
  let T := residualFinset G u v
  have hT : T.card = 6 := by
    dsimp [T]
    rw [residualFinset_card_eq_ncard]
    exact hS
  let f := residualSixEmbeddingOfCardEq T hT
  have hrangeT : Set.range f = (T : Set (Fin n)) :=
    residualSixEmbeddingOfCardEq_range T hT
  have hrangeS : Set.range f = residualSet G u v := by
    rw [hrangeT]
    ext z
    change z ∈ residualFinset G u v ↔ z ∈ residualSet G u v
    exact mem_residualFinset_iff (G := G) (u := u) (v := v)
  let g : Fin 6 → residualSet G u v := fun i =>
    ⟨f i, by
      rw [← hrangeS]
      exact ⟨i, rfl⟩⟩
  have hginj : Function.Injective g := by
    intro i j hij
    have hf : f i = f j := by
      simpa [g] using congrArg Subtype.val hij
    exact f.injective hf
  have hgsurj : Function.Surjective g := by
    intro y
    have hyrange : y.1 ∈ Set.range f := by
      rw [hrangeS]
      exact y.2
    rcases Set.mem_range.mp hyrange with ⟨i, hi⟩
    refine ⟨i, Subtype.ext ?_⟩
    exact hi
  let eS : Fin 6 ≃ residualSet G u v :=
    Equiv.ofBijective g ⟨hginj, hgsurj⟩
  let eH : (G.induce (residualSet G u v)) ≃g G.comap f :=
    { toEquiv := eS.symm
      map_rel_iff' := by
        intro x y
        change G.Adj (f (eS.symm x)) (f (eS.symm y)) ↔
          G.Adj x.1 y.1
        have hx : f (eS.symm x) = x.1 := by
          exact congrArg Subtype.val (eS.apply_symm_apply x)
        have hy : f (eS.symm y) = y.1 := by
          exact congrArg Subtype.val (eS.apply_symm_apply y)
        rw [hx, hy] }
  have eIso := verified_r5_s6_isolated_iso_of_high_five hG huv eH
  have he := verified_r5_s6_edge_count_le_five_of_iso eIso
  exact verified_r5_upper_from_residual_s6_c5_isolated_auto hG hmax huv
    hnoA hnoB hn hS he eIso

/- Extremal-choice wrapper for the cardinality-only S6 bridge.  The
   edge-maximality fact is a consequence of `HighExtremal`, so callers that
   already work with the chosen extremal graph need not thread it separately. -/
theorem verified_r5_upper_from_residual_s6_cardinality_of_extremal_choice
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : HighExtremal 5 n G)
    {u v : Fin n} (huv : G.Adj u v)
    (hnoA : ∀ x x', x ∈ edgeSideASet G u v →
      x' ∈ edgeSideASet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    (hnoB : ∀ x x', x ∈ edgeSideBSet G u v →
      x' ∈ edgeSideBSet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    (hn : 80 ≤ n)
    (hS : (residualSet G u v).ncard = 6) :
    edgeCount G ≤ fiveCandidate n := by
  have hmax : IsEdgeMaximalTriangleFree G :=
    edge_maximal_of_edgeCount_max hG.1 hG.2
  exact verified_r5_upper_from_residual_s6_high_five_cardinality
    hG.1 hmax huv hnoA hnoB hn hS

run_cmd R5Kernel.checkStandardAxioms ``verified_r5_upper_from_residual_s6_cardinality_of_extremal_choice

/- General certificate wrapper for an extremal choice.  This is the common
   entry point for the future s=7,...,11 finite tables: once a table supplies
   `e`, `q`, and the residual-size case, the graph-level upper bound follows
   without repeating the maximal-edge and degree-compatibility plumbing. -/

/- S7 capacity table wrappers.  These are intentionally local statements:
   the remaining structural work must still construct the labelled support
   families and verify the displayed cardinality/weight hypotheses. -/

/- Sharpened S7 capacity wrappers.  The first one is the bare
   `C₅ ⊔ 2K₁` range-split bound; the second is the explicit two-spoke model.
   They are exposed here so future structural certificates can use the new
   constants without importing the implementation module directly. -/

/- A five-edge S7 residual is forced to be the bare C5: the two outside
   vertices have no cycle attachments and are not adjacent.  This is a small
   executable audit, useful when an external certificate reports the sharp
   residual edge bound e ≤ 5. -/

/- The executable S7 classification also closes the labelled-cycle boundary:
   triangle-free + at most five edges + non-two-colourable already forces the
   entire seven-vertex graph to be a bare C₅ with two isolated vertices. -/

/- The same finite classification applies directly to an induced seven-point
   residual once its non-bipartiteness and sharp edge bound are available. -/

/- The upstream extremal-choice tuple already supplies the missing
   non-bipartiteness of a residual (via `residual_not_colorable_two_of_high_five`).
   This adapter therefore needs only the residual cardinality and the sharp
   five-edge bound: the finite S7 classifier supplies the bare-C5 isomorphism
   without a separately labelled cycle certificate. -/

/- A structural sharpening of the S7 interface.  Once a triangle-free
   seven-vertex residual contains a labelled C5 and has at most five edges,
   the finite parameter audit forces both attachment masks and the 5--6 edge
   bit to vanish.  Thus the residual is not merely canonical: it is the bare
   C5 with two isolated vertices. -/

/- The preceding canonicalization can consume the sharp edge bound directly.
   This version is the structural S7 endpoint used by the future residual
   certificate: no attachment masks or graph parameters need be supplied by
   the enumerator. -/

/- Direct structural-to-capacity bridge for the canonical seven-point model:
   once every support in A is known to be a nonempty independent set of the
   model, the coarse q ≤ 104 bound is immediate. -/

/- Residual transport for the canonical seven-point model.  The induced
   residual graph isomorphism supplies a concrete embedding back into the
   ambient graph, so the support-family capacity proof can be performed on
   `canonicalC5Graph7` without any untracked relabelling premise. -/

/- The generic embedding bridge from `R5CapacityBridge` can be instantiated
   directly at the canonical seven-point residual.  Keeping this short
   wrapper next to the residual embedding is useful for the later s=8--11
   rows: their structural certificates need only provide the analogous
   labelled graph and the two support-family containment proofs. -/

/- A dimension-independent version of the residual embedding used by the
   finite S8 rows.  The isomorphism is from the induced residual graph back
   into the ambient `Fin n` graph; its range is definitionally the residual
   set, so support-family membership transports without an external relabeling
   certificate. -/
noncomputable def r5ResidualEmbeddingOfIso
    {s n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    {H : SimpleGraph (Fin s)}
    (e : (G.induce (residualSet G u v)) ≃g H) :
    Fin s ↪ Fin n :=
  e.symm.toEquiv.toEmbedding.trans (Function.Embedding.subtype _)

theorem r5ResidualEmbeddingOfIso_range
    {s n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    {H : SimpleGraph (Fin s)}
    (e : (G.induce (residualSet G u v)) ≃g H) :
    Set.range (r5ResidualEmbeddingOfIso e) = residualSet G u v := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact (e.symm.toEquiv i).property
  · intro hx
    let y : residualSet G u v := ⟨x, hx⟩
    refine ⟨e.toEquiv y, ?_⟩
    dsimp [r5ResidualEmbeddingOfIso]
    simp [y]

theorem r5ResidualEmbeddingOfIso_graph
    {s n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    {H : SimpleGraph (Fin s)}
    (e : (G.induce (residualSet G u v)) ≃g H) :
    ∀ x y : Fin s,
      G.Adj (r5ResidualEmbeddingOfIso e x)
        (r5ResidualEmbeddingOfIso e y) ↔ H.Adj x y := by
  intro x y
  change (G.induce (residualSet G u v)).Adj
      (e.symm.toEquiv x) (e.symm.toEquiv y) ↔ H.Adj x y
  exact e.symm.map_rel_iff

/- The C₇ residual has a uniform finite-universe bound.  Unlike the older
   row-specific bridge, this endpoint does not ask the producer for a bound
   on `B.card` or for a threshold: below weight `35` the generic minimum-
   weight estimate gives `q≤34`, while at weight `≥35` the kernel-checked
   C₇ table gives `q≤21`.  The only ambient input is the labelled residual
   isomorphism, which supplies the embedding and all support pullback data. -/

/- The first S8 row now has a graph-level capacity wrapper.  The only
   numerical input is the kernel-checked finite table
   `cycleCapacitySumK_c7_s8_t58`; all ambient bookkeeping is performed by the
   generic embedding bridge. -/

/- Raw structural certificate for the S8 C7 residual row.  The external
   enumerator supplies only the labelled residual isomorphism, the residual
   edge bound, and the finite A-family card/weight data; the B-family bound is
   not needed by the multiplier bridge above. -/

/- The sharper central S7 table transported through the same isomorphism.
   The numerical side conditions are stated on the ambient support families;
   card and weight invariance of the embedding pullback moves them to the
   finite `cycleTypes 7 5` table. -/

/- The range-split C₅ table gives one extra unit when the ambient support
   family is allowed the full `43` types and starts at weight `37`.  This is
   the graph-level transport theorem used by the sharpened S7 certificate;
   the proof is the same pullback argument as the central table above, with
   the sharper finite universe bound replayed in `R5SmallCore`. -/

/- The simplified paper tables close the arithmetic for every `n ≥ 201`.
   As with the earlier wrapper, the residual classification and its support
   certificate are explicit hypotheses; this theorem only performs the
   graph-to-arithmetic endgame. -/

/- The preceding C₇ estimate closes the long-order arithmetic endpoint with
   only the residual edge bound and the graph isomorphism.  In particular,
   the generated C₇ rows need not repeat their row-dependent support-card or
   threshold fields when they are used at `n≥201`. -/

/- The simplified seven-to-nine-point tables already close their arithmetic
   for every `n ≥ 80`.  As elsewhere in this file, the residual shape and the
   support-surplus bound are explicit hypotheses; this wrapper only transports
   them to the edge-count inequality. -/
theorem verified_r5_upper_from_residual_simplified_s7_s9
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n}
    (hmax : IsEdgeMaximalTriangleFree G)
    (huv : G.Adj u v)
    (hnoA : ∀ x x', x ∈ edgeSideASet G u v →
      x' ∈ edgeSideASet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    (hnoB : ∀ x x', x ∈ edgeSideBSet G u v →
      x' ∈ edgeSideBSet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    {e q : ℕ}
    (he : (G.induce (residualFinset G u v : Set (Fin n))).edgeFinset.card ≤ e)
    (hq : supportSurplus (supportFamilyA G u v)
      (supportFamilyB G u v) ≤ q)
    (hn : 80 ≤ n)
    (hcase :
      ((residualSet G u v).ncard = 7 ∧ e + q ≤ 42) ∨
      ((residualSet G u v).ncard = 8 ∧ e + q ≤ 77) ∨
      ((residualSet G u v).ncard = 9 ∧ e + q ≤ 114)) :
    edgeCount G ≤ fiveCandidate n := by
  have hsum := full_side_degree_residual_card_sum hmax.1 huv
  have hdecomp := edgeCount_le_full_product_plus_residual_bound_of_additive
    (G := G) hmax huv hnoA hnoB he hq
  apply edgeCount_le_fiveCandidate_of_simplified_s7_s9 hn
  refine ⟨(residualSet G u v).ncard,
    (sideAFinset G u v).card.succ,
    (sideBFinset G u v).card.succ, e, q, ?_, ?_, ?_⟩
  · exact hsum
  · exact hdecomp
  · exact hcase

/- The sharpened S7 arithmetic endpoint.  The new finite S7 capacity tables
   prove `e + q ≤ 41` in the relevant residual models; this wrapper keeps
   that one-unit improvement separate from the established S8/S9 endpoints.
   The structural choice of the S7 model is intentionally still an explicit
   hypothesis. -/
theorem verified_r5_upper_from_residual_s7_sharp_s8_s9
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {u v : Fin n}
    (hmax : IsEdgeMaximalTriangleFree G)
    (huv : G.Adj u v)
    (hnoA : ∀ x x', x ∈ edgeSideASet G u v →
      x' ∈ edgeSideASet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    (hnoB : ∀ x x', x ∈ edgeSideBSet G u v →
      x' ∈ edgeSideBSet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    {e q : ℕ}
    (he : (G.induce (residualFinset G u v : Set (Fin n))).edgeFinset.card ≤ e)
    (hq : supportSurplus (supportFamilyA G u v)
      (supportFamilyB G u v) ≤ q)
    (hn : 80 ≤ n)
    (hcase :
      ((residualSet G u v).ncard = 7 ∧ e + q ≤ 41) ∨
      ((residualSet G u v).ncard = 8 ∧ e + q ≤ 77) ∨
      ((residualSet G u v).ncard = 9 ∧ e + q ≤ 114)) :
    edgeCount G ≤ fiveCandidate n := by
  rcases hcase with h7 | h8 | h9
  · exact verified_r5_upper_from_residual_simplified_s7_s9
      hmax huv hnoA hnoB he hq hn
      (Or.inl ⟨h7.1, by omega⟩)
  · exact verified_r5_upper_from_residual_simplified_s7_s9
      hmax huv hnoA hnoB he hq hn
      (Or.inr (Or.inl h8))
  · exact verified_r5_upper_from_residual_simplified_s7_s9
      hmax huv hnoA hnoB he hq hn
      (Or.inr (Or.inr h9))

theorem verified_r5_upper_from_residual_s7_sharp_s8_s9_of_extremal_choice
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : HighExtremal 5 n G)
    {u v : Fin n} (huv : G.Adj u v)
    (hnoA : ∀ x x', x ∈ edgeSideASet G u v →
      x' ∈ edgeSideASet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    (hnoB : ∀ x x', x ∈ edgeSideBSet G u v →
      x' ∈ edgeSideBSet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    {e q : ℕ}
    (he : (G.induce (residualFinset G u v : Set (Fin n))).edgeFinset.card ≤ e)
    (hq : supportSurplus (supportFamilyA G u v)
      (supportFamilyB G u v) ≤ q)
    (hn : 80 ≤ n)
    (hcase :
      ((residualSet G u v).ncard = 7 ∧ e + q ≤ 41) ∨
      ((residualSet G u v).ncard = 8 ∧ e + q ≤ 77) ∨
      ((residualSet G u v).ncard = 9 ∧ e + q ≤ 114)) :
    edgeCount G ≤ fiveCandidate n := by
  have hmax : IsEdgeMaximalTriangleFree G :=
    edge_maximal_of_edgeCount_max hG.1 hG.2
  exact verified_r5_upper_from_residual_s7_sharp_s8_s9 hmax huv
    hnoA hnoB he hq hn hcase

/- Canonical-C₅ convenience wrapper for the sharpened endpoint.  Once the
   residual is known to be a canonical seven-vertex C₅ model, the transported
   table supplies `q≤36`; together with the five-edge residual bound this is
   exactly the `e+q≤41` branch above. -/

/- Extremal-choice wrapper for the simplified S7--S9 tables.  The finite
   shape-to-(e+q) certificate remains an explicit input, while the generic
   maximal-edge plumbing is discharged here. -/
theorem verified_r5_upper_from_residual_simplified_s7_s9_of_extremal_choice
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : HighExtremal 5 n G)
    {u v : Fin n} (huv : G.Adj u v)
    (hD : ∀ H a b, HighExtremalEdgePairs 5 n (H, (a, b)) →
      degreeSumPair (H, (a, b)) ≤ degreeSumPair (G, (u, v)))
    (hnoA : ∀ x x', x ∈ edgeSideASet G u v →
      x' ∈ edgeSideASet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    (hnoB : ∀ x x', x ∈ edgeSideBSet G u v →
      x' ∈ edgeSideBSet G u v → x ≠ x' →
      (residualType G u v x).Nonempty →
      residualType G u v x ≠ residualType G u v x')
    {e q : ℕ}
    (he : (G.induce (residualFinset G u v : Set (Fin n))).edgeFinset.card ≤ e)
    (hq : supportSurplus (supportFamilyA G u v)
      (supportFamilyB G u v) ≤ q)
    (hn : 80 ≤ n)
    (hcase :
      ((residualSet G u v).ncard = 7 ∧ e + q ≤ 42) ∨
      ((residualSet G u v).ncard = 8 ∧ e + q ≤ 77) ∨
      ((residualSet G u v).ncard = 9 ∧ e + q ≤ 114)) :
    edgeCount G ≤ fiveCandidate n := by
  have hmax : IsEdgeMaximalTriangleFree G :=
    edge_maximal_of_edgeCount_max hG.1 hG.2
  exact verified_r5_upper_from_residual_simplified_s7_s9 hmax huv
    hnoA hnoB he hq hn hcase

/- The same transport with the sharper n≥80 S10/S11 arithmetic endpoints.
   This leaves no arithmetic threshold gap between the small and coarse tables;
   only the corresponding finite structural certificates are still needed. -/

/- The residual-size part of the extremal reduction is already automatic:
   high five-chromaticity forces at least six residual vertices, while the
   degree-average inequality and the chosen extremal edge force at most eleven.
   Exposing this lemma here leaves the still-open certificate responsible only
   for the finite edge/support table at each size. -/
theorem verified_r5_residual_size_between_six_eleven
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : HighExtremal 5 n G)
    {u v : Fin n} (huv : G.Adj u v)
    (hD : ∀ H a b, HighExtremalEdgePairs 5 n (H, (a, b)) →
      degreeSumPair (H, (a, b)) ≤ degreeSumPair (G, (u, v)))
    (hn : 80 ≤ n) :
    6 ≤ (residualSet G u v).ncard ∧
      (residualSet G u v).ncard ≤ 11 := by
  exact high_extremal_residual_ncard_between_six_eleven hn hG huv hD

/- The standard blow-up witness is available from order 27, not only from the
   eventual `n ≥ 80` range.  Replaying its extremal comparison here removes
   that artificial threshold from the degree-average residual bound. -/

/- A certificate predicate for the still-open r=5 extremal residual step.
   The first branch is the fully automated six-point route.  The next branch
   records the n-independent seven-to-nine tables.  The final branch is the
   coarse n≥201 table; the missing 80≤n<201, s=10,11 certificates therefore
   remain visible instead of being hidden in an opaque theorem. -/

/- Once the residual certificate is available for the twinized extremal
   choice, this theorem lifts it to every high-five graph by extremal
   comparison.  It is the direct root-level reduction used by the target. -/

/- Named all-tail interface for certificate producers.  This is definitionally
   the residual premise consumed by the extremal lifting theorem, but naming it
   lets the final assembler accept one compact object instead of repeating the
   dependent function type at every call site. -/

/- The residual certificate with every ordinary S7 branch removed.  The
   canonical S7 transport below is now the unique owner of the s = 7 case,
   including the coarse n≥201 range. -/

/- A finite-row case bound in the same shape as the No-S7 dispatcher, but
   expressed in terms of the labelled model size `s`.  This is the arithmetic
   part of a row certificate; the structural part is carried by
   `R5ResidualDualRowCertificate` below. -/

/- This record is the direct insertion format for a finite residual row.  The
   producer supplies a labelled finite universe `U`, the two pullback maps,
   and a compact partial D1--D4 certificate.  All graph-independent
   bookkeeping, including the final `e + q` dispatcher, is checked below. -/

/- A finite-range dual row has a different arithmetic endpoint from the
   n-independent No-S7 dispatcher above.  Here `K` is the row-specific
   capacity bound

     supportSurplus A B ≤ K,

   and the producer checks the complete quantity

     |A-side|·|B-side| + e + K ≤ fiveCandidate n.

   This is the correct format for the 80≤n≤200 dual snapshot: its `K` is
   allowed to vary with `(n,a,b)`, so it must not be mistaken for the fixed
   constants 42, 77, 114, 149, 184 used by the simplified dispatcher.
   The structural fields intentionally mirror `R5ResidualDualRowCertificate`
   so that a future generated table can be switched between the two
   arithmetic endpoints without changing the D1--D4 replay. -/

/- The No-S7 residual format is a strict subformat of the original dispatcher:
   its ordinary S7 branch is supplied separately by the canonical certificate. -/

/- The S8-C7 certificate can now be fed directly to the full residual
   dispatcher.  Keeping this adapter next to the No-S7 conversion means a
   producer need not know which intermediate residual format the final
   assembly uses. -/

/- All-n assembler for the row format above.  A certificate producer can now
   emit one six-point witness or one labelled dual row for each twinized
   extremal edge, without reproducing the dependent dispatcher type by hand. -/

/- Direct finite-row analogue of `R5AllNResidualCertificateNoS7`.  It is
   intentionally separate because a row-specific `K` closes the edge bound
   by its own `(a,b,n)` arithmetic, rather than by the fixed No-S7 constants.
   The six-point branch is retained as a bare cardinality statement: the
   already proved S6 high-five bridge supplies its upper bound automatically. -/

/- Structural input for the ordinary S7 row.  It is deliberately separated
   from the numerical residual certificate: the field supplies only the
   canonical residual isomorphism and the hypotheses consumed by the central
   capacity table. -/

/- Reduced S7 input for enumerators that certify the residual edge bound
   directly.  The labelled C5/canonical-parameter fields are intentionally
   absent: the finite seven-vertex classifier plus
   `residualSeven_bare_canonical_iso_of_high_extremal_edge_bound` reconstructs
   the required canonical isomorphism. -/

/- Hybrid residual input for the final upper-bound assembler.  The ordinary
   No-S7 rows use the fixed simplified dispatcher; a finite dual row may
   instead use its row-specific direct arithmetic endpoint.  Keeping this as
   a sum makes the distinction explicit and prevents a varying finite `K`
   from being silently treated as one of the fixed dispatcher constants. -/

/- Pointwise structural input for the sharpened S7 route.  In contrast to
   the older central certificate, this records only the numerical pair `(e,q)`
   needed by the arithmetic endpoint.  Thus a generator may choose a
   different seven-vertex model (and a different pair of budgets) for each
   extremal edge; no global profile is being smuggled into the statement. -/

/- A more geometric producer format for the same sharp certificate.  The
   classifier returns a canonical seven-vertex C₅ model, the five-edge
   residual bound, and the relaxed support-card/weight hypotheses; the
   pullback theorem above then manufactures the numerical `(e,q)` pair. -/

/- The finite S7 classifier already reconstructs the bare canonical C₅
   model from the residual edge bound and the extremal non-2-colourability.
   This is therefore the smallest useful producer interface: a structural
   argument only has to establish the five-edge bound and the three local
   support inequalities. -/

/- The central certificate has strictly stronger numerical hypotheses than
   the sharpened interface.  This weakening is useful when an existing
   central proof is reused by the new arithmetic endpoint: no finite-table
   replay is needed a second time. -/

/- Hybrid S7 producer boundary.  A residual may be discharged either by the
   sharp five-edge/support inequalities or by one of the existing
   row-specific finite dual certificates.  This lets the structural search
   keep exceptional seven-vertex profiles finite without weakening the sharp
   arithmetic branch. -/

/- The sharp S7 provider plugs into the same all-n residual assembler as the
   existing finite-row certificate.  The S7 branch is dispatched with the
   improved `41` constant; all non-S7 branches retain their established
   hybrid certificate. -/

/- Hybrid-tail counterpart of the reduced S7 adapter.  This keeps the direct
   finite-row endpoint available when the non-S7 branch is supplied by a
   row-specific dual certificate. -/

/- The reduced S7 route may also be discharged by a row-specific finite dual
   certificate.  This is useful for the non-central seven-vertex models
   (C₅ with attachments/external edge, C₇, and the disjoint C₅ model): the
   structural classifier still handles the sharp five-edge central branch,
   while a generated `R5ResidualDualFiniteRowCertificate` can close any
   remaining S7 row with its own `(n,a,b)` budget. -/

/- External-facing raw certificate for the ordinary S7 branch.  Unlike
   `R5S7CentralCertificate`, this format records the seven-point set and the
   C5 witness on the finite `Fin 7` model, so it can be produced by an
   independent enumerator or proof-producing search. -/

/- Canonical variant for certificate generators: once the residual cardinality
   is known, the labelled seven-set is fixed to `residualFinset H u v`, so no
   separate finset or set-equality field has to be emitted. -/

/- A single data record for the remaining upper-bound work.  Its fields are
   mathematical certificates, not axioms hidden inside the final theorem. -/

/- Final insertion record for the r = 5 proof.  This is intentionally
   certificate-shaped: an external finite enumerator supplies the small-n
   tables, the 24--79 upper-bound table, the non-S7 residual rows, and the
   canonical S7 witness.  The last field is kept in its raw canonical form so
   that the central S7 theorem is reconstructed by the checked bridge above,
   rather than being accepted as an opaque proposition. -/

/- Variant of the final insertion record for a project that has already
   converted the finite `80≤n≤200` rows to the direct-dual endpoint.  The
   small-order and S7 fields are unchanged; only the residual tail field is
   replaced by the hybrid input above. -/

/- The final bundle only consumes the completeness maps for the 22/23
   catalogues.  This direct HoG constructor avoids forcing a producer to
   repackage already-checked row properties into `Mtf*CatalogCertificate`;
   those properties remain available through the separate catalogue
   bridges above. -/

/- Adapter for the catalogue certificate records already used by the local
   22/23-vertex bridges.  This keeps the final insertion site independent of
   the representation chosen for the two House-of-Graphs catalogues. -/

/- Direct final assembler for the reduced S7 payload.  This avoids forcing
   certificate generators to manufacture a labelled C5 witness solely to
   populate `R5AllNUpperComponents.s7_central`. -/

/- Target-shaped wrapper for the same reduced insertion path.  Once the
   component certificates are present, the exact `(M,f)` and offset statement
   follows from the common all-n lower-witness wrapper. -/

/- The same insertion point can be exposed at the pointwise level.  This is
   useful for certificate producers that want to validate the upper half
   before invoking the lower-witness wrapper: no target-level theorem has to
   reconstruct the piecewise 22/23/24--27/28--79/80+ split. -/

/- The corresponding r = 4 wrappers isolate the two residual cases that are
   not eliminated by the small-colouring argument. -/

/- The four-point finite dispatcher now transports the labelled capacity
   tables to an arbitrary residual four-set and returns the combined
   `e(H)+F ≤ 11` certificate. -/

/- The finite four-point dispatcher now plugs directly into the extremal
   graph decomposition.  This is deliberately a bridge theorem: it closes
   the s = 4 branch once the degree-sum-maximal edge and the small residual
   cardinality have been supplied, but it does not assert the missing global
   extremal-edge selection or the s ≤ 3 exclusion. -/

/- A residual of at most two vertices cannot occur at chromatic number four.
   The residual edge forced by `residual_has_edge_of_high_four` makes every
   independent residual type a singleton (or empty).  Hence any 2-colouring
   of the residual is automatically monochromatic on every B-type, and the
   sharpened three-colour reduction gives a contradiction. -/

/- The three-point residual capacity bridge.  For r=4 an edge in the
   residual graph is forced by non-3-colourability, so the finite `Fin 3`
   certificate applies without an additional graph-shape hypothesis. -/

/- If the labelled three-point residual has exactly one edge, the preceding
   `F ≤ 4` estimate combines with the exact residual edge count to give the
   sharp `e + F ≤ 5` certificate required by the arithmetic endgame. -/

/- The P₃ residual branch supplies the monochromatic-type hypothesis needed by
   the sharpened three-colour reduction.  The finite certificate is transported
   through the labelled residual embedding and its graph isomorphism. -/

/- Arithmetic bridge for the complete three-point residual branch.  After the
   P₃ case is excluded, the surviving one-edge case has the sharp `e+F ≤ 5`
   constant used by the four-colour candidate. -/

/- Fully instantiate the previous bridge from an extremal edge choice.  This
   closes the entire `s = 3` branch once the degree-sum maximal edge and its
   no-repeated-type hypotheses are available. -/

/- Instantiate the sharp three-point certificate when the residual graph has
   one edge.  The remaining two-edge `P₃` shape is intentionally not folded
   into this theorem: it must first be excluded by a separate 3-colouring
   argument, as in the paper proof. -/

/- Fully automatic three-point dispatch.  The residual has an edge, Turán's
   bound gives at most two edges, and the preceding P₃ contradiction forces
   the one-edge certificate. -/

/- The five-point residual branch now has a complete local dispatcher: Turán
   gives the six-edge residual bound, while the finite `K₂ ⊔ 3K₁` capacity table
   gives the support-surplus bound. -/

/- Once the extremal edge has been twinized, the degree-average estimate leaves
   only residual sizes 2 through 5.  The size-two case is impossible, and the
   preceding three-, four-, and five-point dispatchers close the remaining
   cases. -/

/- The twinization choice is only needed for the extremal graph.  This theorem
   compares that graph with an arbitrary high four-chromatic triangle-free
   graph, yielding the full r=4 upper bound for n ≥ 32. -/

/- Small finite arithmetic gaps used to extend the structural argument below
   n=32.  They are deliberately proved by `interval_cases`, not assumed from
   the computer enumeration. -/

/- If an extremal graph beats the candidate, the degree-average inequality
   rules out residual size at least five below n=32. -/

/- The same argument rules out residual size at least four for 12≤n<16,
   which is the only extra small range needed by the four-point dispatcher. -/

/- Full r=4 upper bound for an already twinized extremal edge at every n≥12.
   The only finite arithmetic input below 32 is the preceding two gap lemmas. -/

/- The twinization choice is only needed for the extremal graph.  Comparing it
   with an arbitrary high graph gives the complete r=4 upper inequality for
   every n≥12, pending only the separate 11-vertex finite case. -/

/- For the exceptional 11-vertex case, beating the claimed value 20 already
   forces the residual of a degree-sum-maximal edge down to three vertices.
   This is the arithmetic part of the paper's equality analysis; the final
   three-colouring of the equality configuration is kept separate. -/


end Erdos1011

end Web_Erdos1011Final
