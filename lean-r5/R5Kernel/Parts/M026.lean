import R5Kernel.Parts.M025

/- Source module: Erdos1011.R5FiniteSix. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_R5FiniteSix


namespace Erdos1011

open SimpleGraph

/-! Kernel-checked colour witnesses for the six-vertex residual step.
    The legacy edge-code interface is preserved, while the finite core uses
    only 32 attachment masks and explicit three-colour witnesses.
    This file deliberately proves only the finite colouring core; transporting
    a residual graph to the certificate and applying the colouring to the
    ambient graph are separate lemmas. -/

abbrev EdgeCode6 := {e : Sym2 (Fin 6) // ¬ e.IsDiag}

def edgeCodeSet6 (E : Finset EdgeCode6) : Set (Sym2 (Fin 6)) :=
  ((E.image Subtype.val : Finset (Sym2 (Fin 6))) : Set _)

instance edgeCodeSet6_decidable (E : Finset EdgeCode6) :
    DecidablePred (· ∈ edgeCodeSet6 E) := by
  intro z
  change Decidable (z ∈ E.image Subtype.val)
  infer_instance

def finiteCodeGraph6 (E : Finset EdgeCode6) : SimpleGraph (Fin 6) :=
  SimpleGraph.fromEdgeSet (edgeCodeSet6 E)

instance finiteCodeGraph6_decidable (E : Finset EdgeCode6) :
    DecidableRel (finiteCodeGraph6 E).Adj := by
  intro x y
  change Decidable (s(x, y) ∈ edgeCodeSet6 E ∧ x ≠ y)
  infer_instance

def triangleFree6 (H : SimpleGraph (Fin 6)) : Prop :=
  ∀ x y z : Fin 6, H.Adj x y → H.Adj x z → H.Adj y z → False

instance triangleFree6_decidable (H : SimpleGraph (Fin 6))
    [DecidableRel H.Adj] : Decidable (triangleFree6 H) := by
  unfold triangleFree6
  infer_instance

/- A two-colouring predicate for the encoded six-vertex graphs.  We keep this
   explicit rather than relying on `SimpleGraph.Colorable`, because the
   latter quantifies over an arbitrary colouring type and does not reduce to
   a closed finite computation without an additional finite codomain witness. -/
def proper2_6 (H : SimpleGraph (Fin 6)) : Prop :=
  ∃ c : Fin 6 → Fin 2, ∀ x y : Fin 6, H.Adj x y → c x ≠ c y

instance proper2_6_decidable (H : SimpleGraph (Fin 6))
    [DecidableRel H.Adj] : Decidable (proper2_6 H) := by
  unfold proper2_6
  apply Fintype.decidableExistsFintype

def good6 (H : SimpleGraph (Fin 6)) : Prop :=
  ∃ c : Fin 6 → Fin 3,
    (∀ x y : Fin 6, H.Adj x y → c x ≠ c y) ∧
    (∀ I : Finset (Fin 6), H.IsIndepSet (I : Set (Fin 6)) →
      (I.image c).card ≤ 2)

instance good6_decidable (H : SimpleGraph (Fin 6))
    [DecidableRel H.Adj] : Decidable (good6 H) := by
  unfold good6
  apply Fintype.decidableExistsFintype

def c5In6 (H : SimpleGraph (Fin 6)) : Prop :=
  ∃ f : Fin 5 → Fin 6, Function.Injective f ∧
    (∀ i : Fin 5, H.Adj (f i) (f ⟨(i.1 + 1) % 5, Nat.mod_lt _ (by omega)⟩))

/- The edge-code transport interface is retained for downstream callers.
   The shape classification is proved structurally in M030; no enumeration
   of all graphs on six vertices is needed. -/

/- Every decidable graph on `Fin 6` is represented by its finite edge code.
   This is the transport boundary for the executable certificate above. -/
def edgeCodeOfGraph6 (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj] :
    Finset EdgeCode6 :=
  G.edgeFinset.attach.image (fun e =>
    (⟨e.1, G.not_isDiag_of_mem_edgeFinset e.2⟩ : EdgeCode6))

theorem finiteCodeGraph6_edgeCodeOfGraph6
    (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj] :
    finiteCodeGraph6 (edgeCodeOfGraph6 G) = G := by
  ext x y
  constructor
  · intro h
    change (SimpleGraph.fromEdgeSet (edgeCodeSet6 (edgeCodeOfGraph6 G))).Adj x y at h
    rw [SimpleGraph.fromEdgeSet_adj] at h
    rcases h with ⟨hE, hxy⟩
    change s(x, y) ∈
      ((edgeCodeOfGraph6 G).image Subtype.val : Finset (Sym2 (Fin 6))) at hE
    rw [Finset.mem_image] at hE
    rcases hE with ⟨e, he, heq⟩
    rcases Finset.mem_image.mp he with ⟨e', he', heeq⟩
    have hefin : e'.1 ∈ G.edgeFinset := e'.2
    have heq' : e'.1 = e.1 := by simpa using congrArg Subtype.val heeq
    have hval : e'.1 = s(x, y) := heq'.trans heq
    have : s(x, y) ∈ G.edgeFinset := by simpa [hval] using hefin
    exact SimpleGraph.mem_edgeFinset.mp this
  · intro hxy
    have hne : x ≠ y := G.ne_of_adj hxy
    change (SimpleGraph.fromEdgeSet (edgeCodeSet6 (edgeCodeOfGraph6 G))).Adj x y
    rw [SimpleGraph.fromEdgeSet_adj]
    refine ⟨?_, hne⟩
    change s(x, y) ∈
      ((edgeCodeOfGraph6 G).image Subtype.val : Finset (Sym2 (Fin 6)))
    apply Finset.mem_image.mpr
    let e : G.edgeFinset := ⟨s(x, y), SimpleGraph.mem_edgeFinset.mpr hxy⟩
    let ec : EdgeCode6 := ⟨e.1, G.not_isDiag_of_mem_edgeFinset e.2⟩
    refine ⟨ec, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨e, by simp, rfl⟩
    · rfl

theorem proper2_6_iff_colorable_two {H : SimpleGraph (Fin 6)} :
    proper2_6 H ↔ H.Colorable 2 := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨Coloring.mk c (fun {x y} hxy => hc x y hxy)⟩
  · rintro ⟨C⟩
    exact ⟨C, fun x y hxy => C.valid hxy⟩

def attachedC5In6 (H : SimpleGraph (Fin 6)) : Prop :=
  ∃ f : Fin 5 → Fin 6, ∃ z : Fin 6,
    Function.Injective f ∧
    (∀ i : Fin 5, H.Adj (f i) (f ⟨(i.1 + 1) % 5, Nat.mod_lt _ (by omega)⟩)) ∧
    (∀ i : Fin 5, z ≠ f i) ∧
    (∃ i : Fin 5, H.Adj z (f i))

instance attachedC5In6_decidable (H : SimpleGraph (Fin 6))
    [DecidableRel H.Adj] : Decidable (attachedC5In6 H) := by
  unfold attachedC5In6
  apply Fintype.decidableExistsFintype

/- Fix the C₅ labels to `0,1,2,3,4` and use a ten-bit mask for the only
   remaining unordered pairs.  This removes the expensive search over all
   embeddings of a five-cycle; arbitrary labelled cycles are handled later by
   relabelling. -/
def extraBit (m : Fin 1024) (i : ℕ) : Prop :=
  (m.1 / (2 ^ i)) % 2 = 1

def fixedC5ExtraRel (m : Fin 1024) (x y : Fin 6) : Prop :=
  (x = 0 ∧ y = 2 ∧ extraBit m 0) ∨ (y = 0 ∧ x = 2 ∧ extraBit m 0) ∨
  (x = 0 ∧ y = 3 ∧ extraBit m 1) ∨ (y = 0 ∧ x = 3 ∧ extraBit m 1) ∨
  (x = 1 ∧ y = 3 ∧ extraBit m 2) ∨ (y = 1 ∧ x = 3 ∧ extraBit m 2) ∨
  (x = 1 ∧ y = 4 ∧ extraBit m 3) ∨ (y = 1 ∧ x = 4 ∧ extraBit m 3) ∨
  (x = 2 ∧ y = 4 ∧ extraBit m 4) ∨ (y = 2 ∧ x = 4 ∧ extraBit m 4) ∨
  (x = 0 ∧ y = 5 ∧ extraBit m 5) ∨ (y = 0 ∧ x = 5 ∧ extraBit m 5) ∨
  (x = 1 ∧ y = 5 ∧ extraBit m 6) ∨ (y = 1 ∧ x = 5 ∧ extraBit m 6) ∨
  (x = 2 ∧ y = 5 ∧ extraBit m 7) ∨ (y = 2 ∧ x = 5 ∧ extraBit m 7) ∨
  (x = 3 ∧ y = 5 ∧ extraBit m 8) ∨ (y = 3 ∧ x = 5 ∧ extraBit m 8) ∨
  (x = 4 ∧ y = 5 ∧ extraBit m 9) ∨ (y = 4 ∧ x = 5 ∧ extraBit m 9)

def fixedC5Rel (m : Fin 1024) (x y : Fin 6) : Prop :=
  cycleRel 6 5 x y ∨ fixedC5ExtraRel m x y

def fixedC5Graph (m : Fin 1024) : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel (fixedC5Rel m)

def fixedC5Attached (m : Fin 1024) : Prop :=
  ∃ i : Fin 5, (fixedC5Graph m).Adj 5 ⟨i.1, by omega⟩

/- A smaller canonical presentation is useful for graph-level transport.  The
   C₅ labels are fixed, and a five-bit mask records only the possible edges
   from the sixth vertex to the cycle.  Triangle-freeness itself rules out
   all five cycle chords, so this model has exactly the degrees of freedom
   needed after a C₅ embedding has been relabelled. -/
def attachBit5 (k : Fin 32) (i : Fin 5) : Prop :=
  (k.1 / (2 ^ i.1)) % 2 = 1

instance attachBit5_decidable (k : Fin 32) (i : Fin 5) :
    Decidable (attachBit5 k i) := by
  unfold attachBit5
  infer_instance

def attachBit5Fin6 (k : Fin 32) (y : Fin 6) : Prop :=
  y.1 < 5 ∧ (k.1 / (2 ^ y.1)) % 2 = 1

instance attachBit5Fin6_decidable (k : Fin 32) (y : Fin 6) :
    Decidable (attachBit5Fin6 k y) := by
  unfold attachBit5Fin6
  infer_instance

def canonicalC5Rel5 (k : Fin 32) (x y : Fin 6) : Prop :=
  cycleRel 6 5 x y ∨
    (x = 5 ∧ attachBit5Fin6 k y)

instance canonicalC5Rel5_decidable (k : Fin 32) :
    DecidableRel (canonicalC5Rel5 k) := by
  intro x y
  unfold canonicalC5Rel5
  infer_instance

def canonicalC5Graph5 (k : Fin 32) : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel (canonicalC5Rel5 k)

instance canonicalC5Graph5_decidable (k : Fin 32) :
    DecidableRel (canonicalC5Graph5 k).Adj := by
  intro x y
  change Decidable (x ≠ y ∧
    (canonicalC5Rel5 k x y ∨ canonicalC5Rel5 k y x))
  infer_instance

def canonicalC5Attached5 (k : Fin 32) : Prop :=
  ∃ i : Fin 5, (canonicalC5Graph5 k).Adj 5 ⟨i.1, by omega⟩

instance canonicalC5Attached5_decidable (k : Fin 32) :
    Decidable (canonicalC5Attached5 k) := by
  unfold canonicalC5Attached5
  apply Fintype.decidableExistsFintype

/- Explicit candidate colourings remove the search over all 3^6 functions.
   Every row and every independent subset is checked by the kernel below. -/
def kernelS6AttachedColor (k : Fin 32) : Fin 6 → Fin 3 :=
  match k.val with
  | 1 => ![0, 1, 0, 1, 2, 2]
  | 2 => ![0, 1, 0, 1, 2, 0]
  | 4 => ![0, 1, 0, 1, 2, 1]
  | 5 => ![0, 1, 0, 1, 2, 1]
  | 8 => ![0, 1, 0, 1, 2, 2]
  | 9 => ![0, 1, 0, 1, 2, 2]
  | 10 => ![0, 1, 0, 1, 2, 0]
  | 16 => ![0, 1, 0, 1, 2, 0]
  | 18 => ![0, 1, 0, 1, 2, 0]
  | 20 => ![0, 1, 0, 1, 2, 1]
  | _ => ![0, 1, 0, 1, 2, 0]

set_option maxHeartbeats 2000000 in
theorem kernel_s6_attached_color_valid : ∀ k : Fin 32,
    triangleFree6 (canonicalC5Graph5 k) → canonicalC5Attached5 k →
    (∀ x y : Fin 6, (canonicalC5Graph5 k).Adj x y →
      kernelS6AttachedColor k x ≠ kernelS6AttachedColor k y) ∧
    (∀ I : Finset (Fin 6), (canonicalC5Graph5 k).IsIndepSet (I : Set (Fin 6)) →
      (I.image (kernelS6AttachedColor k)).card ≤ 2) := by
  decide +kernel

theorem finite_canonical_c5_attached_good :
    ∀ k : Fin 32,
      triangleFree6 (canonicalC5Graph5 k) →
      canonicalC5Attached5 k →
      good6 (canonicalC5Graph5 k) := by
  intro k htri hatt
  exact ⟨kernelS6AttachedColor k, kernel_s6_attached_color_valid k htri hatt⟩

run_cmd R5Kernel.checkStandardAxioms ``finite_canonical_c5_attached_good

end Erdos1011

end Web_Erdos1011_R5FiniteSix
