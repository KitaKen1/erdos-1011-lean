import R5Kernel.Parts.M002

/- Source module: Erdos1011.R5. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_R5


/-!
# The r = 5 kernel and lower-bound arithmetic

`qKernelExplicit` is the double Mycielski graph of the explicit Grötzsch
graph from `R4`.  This replaces the former opaque `qKernel` in the
construction branch; the extremal upper-bound theorem is still a separate
target.
-/

namespace Erdos1011

open SimpleGraph

def qKernelRel (x y : Fin 23) : Prop :=
  let a := x.1
  let b := y.1
  (a < 11 ∧ b < 11 ∧
      grotzschRel ⟨a % 11, by exact Nat.mod_lt _ (by decide)⟩
        ⟨b % 11, by exact Nat.mod_lt _ (by decide)⟩) ∨
  (a < 11 ∧ 11 ≤ b ∧ b < 22 ∧
      grotzschRel ⟨a % 11, by exact Nat.mod_lt _ (by decide)⟩
        ⟨b % 11, by exact Nat.mod_lt _ (by decide)⟩) ∨
  (11 ≤ a ∧ a < 22 ∧ b < 11 ∧
      grotzschRel ⟨b % 11, by exact Nat.mod_lt _ (by decide)⟩
        ⟨a % 11, by exact Nat.mod_lt _ (by decide)⟩) ∨
  (a = 22 ∧ 11 ≤ b ∧ b < 22) ∨
  (b = 22 ∧ 11 ≤ a ∧ a < 22)

def qKernelExplicit : SimpleGraph (Fin 23) := SimpleGraph.fromRel qKernelRel

instance : DecidableRel qKernelRel := by
  intro x y
  dsimp [qKernelRel]
  infer_instance

instance : DecidableRel qKernelExplicit.Adj := by
  intro x y
  change Decidable (x ≠ y ∧ (qKernelRel x y ∨ qKernelRel y x))
  infer_instance

def qBase (v : Fin 11) : Fin 23 := ⟨v.1, by omega⟩

def qCopy (v : Fin 11) : Fin 23 := ⟨v.1 + 11, by omega⟩

def qApex : Fin 23 := ⟨22, by decide⟩

theorem qKernel_base_adj : ∀ u v : Fin 11,
    grotzsch.Adj u v → qKernelExplicit.Adj (qBase u) (qBase v) := by
  decide +kernel

theorem qKernel_base_copy_adj : ∀ u v : Fin 11,
    grotzsch.Adj u v → qKernelExplicit.Adj (qBase u) (qCopy v) := by
  decide +kernel

theorem qKernel_copy_base_adj : ∀ u v : Fin 11,
    grotzsch.Adj u v → qKernelExplicit.Adj (qCopy u) (qBase v) := by
  decide +kernel

theorem qKernel_apex_copy_adj : ∀ u : Fin 11,
    qKernelExplicit.Adj qApex (qCopy u) := by
  decide +kernel

def dropFin4 (p c : Fin 4) (h : c.1 ≠ p.1) : Fin 3 :=
  if hc : c.1 < p.1 then
    ⟨c.1, by omega⟩
  else
    ⟨c.1 - 1, by omega⟩

theorem dropFin4_injective {p c d : Fin 4}
    (hc : c.1 ≠ p.1) (hd : d.1 ≠ p.1) :
    dropFin4 p c hc = dropFin4 p d hd → c = d := by
  intro h
  by_cases hclt : c.1 < p.1 <;>
    by_cases hdlt : d.1 < p.1 <;>
    simp [dropFin4, hclt, hdlt] at h
  · apply Fin.ext
    omega
  · apply Fin.ext
    omega
  · apply Fin.ext
    omega
  · apply Fin.ext
    omega

theorem qKernel_not_four_colorable : ¬ qKernelExplicit.Colorable 4 := by
  rintro ⟨C⟩
  let p : Fin 4 := C qApex
  let color : Fin 11 → Fin 3 := fun v =>
    if hbase : (C (qBase v)).1 = p.1 then
      dropFin4 p (C (qCopy v)) (by
        have hne : C qApex ≠ C (qCopy v) := C.valid (qKernel_apex_copy_adj v)
        intro heq
        apply hne
        apply Fin.ext
        dsimp [p] at heq ⊢
        exact heq.symm)
    else
      dropFin4 p (C (qBase v)) hbase
  have hcolor : grotzsch.Colorable 3 := by
    refine ⟨Coloring.mk color ?_⟩
    intro u v huv
    have hBB := qKernel_base_adj u v huv
    have hBC := qKernel_base_copy_adj u v huv
    have hCB := qKernel_copy_base_adj u v huv
    have hbase_ne : C (qBase u) ≠ C (qBase v) := C.valid hBB
    by_cases hu : (C (qBase u)).1 = p.1
    · by_cases hv : (C (qBase v)).1 = p.1
      · exfalso
        apply hbase_ne
        apply Fin.ext
        omega
      · have hcopy_ne : (C (qCopy u)).1 ≠ p.1 := by
          have hne : C qApex ≠ C (qCopy u) := C.valid (qKernel_apex_copy_adj u)
          intro heq
          apply hne
          apply Fin.ext
          dsimp [p] at heq ⊢
          exact heq.symm
        have hcross : C (qCopy u) ≠ C (qBase v) := C.valid hCB
        simp [color, hu, hv]
        intro heq
        apply hcross
        apply Fin.ext
        exact congrArg (fun z : Fin 4 => z.1)
          (dropFin4_injective hcopy_ne hv heq)
    · by_cases hv : (C (qBase v)).1 = p.1
      · have hcopy_ne : (C (qCopy v)).1 ≠ p.1 := by
          have hne : C qApex ≠ C (qCopy v) := C.valid (qKernel_apex_copy_adj v)
          intro heq
          apply hne
          apply Fin.ext
          dsimp [p] at heq ⊢
          exact heq.symm
        have hcross : C (qBase u) ≠ C (qCopy v) := C.valid hBC
        simp [color, hu, hv]
        intro heq
        apply hcross
        apply Fin.ext
        exact congrArg (fun z : Fin 4 => z.1)
          (dropFin4_injective hu hcopy_ne heq)
      · have hcross : C (qBase u) ≠ C (qBase v) := hbase_ne
        simp [color, hu, hv]
        intro heq
        apply hcross
        apply Fin.ext
        exact congrArg (fun z : Fin 4 => z.1)
          (dropFin4_injective hu hv heq)
  exact grotzsch_not_three_colorable hcolor

theorem qKernel_triangle_free : qKernelExplicit.CliqueFree 3 := by
  intro t ht
  rcases (SimpleGraph.is3Clique_iff.mp ht) with
    ⟨a, b, c, hab, hac, hbc, _⟩
  have hno : ∀ a b c : Fin 23,
      ¬ (qKernelExplicit.Adj a b ∧ qKernelExplicit.Adj a c ∧
        qKernelExplicit.Adj b c) := by
    decide +kernel
  exact hno a b c ⟨hab, hac, hbc⟩

theorem qKernel_chromatic_at_least_five :
    (5 : ℕ∞) ≤ qKernelExplicit.chromaticNumber := by
  change (↑(5 : ℕ) : ℕ∞) ≤ qKernelExplicit.chromaticNumber
  rw [SimpleGraph.le_chromaticNumber_iff_colorable]
  intro k hk
  by_contra h
  have hk' : k ≤ 4 := by omega
  have h4 : qKernelExplicit.Colorable 4 :=
    SimpleGraph.Colorable.mono hk' hk
  exact qKernel_not_four_colorable h4

/-! The variable-size lower-bound graph.  The adjacent vertices
`qCopy 10` (degree 6 in Q) and `qApex` (degree 11 in Q) are replaced by
independent classes of sizes `a` and `b`; all other 21 vertices remain single.
The graph is defined through the base map, so triangle-freeness is inherited
by a graph homomorphism exactly as in the r=4 construction. -/

abbrev QBlowupVertex (a b : ℕ) := Fin 21 ⊕ (Fin a ⊕ Fin b)

def qBlowupBaseVertex {a b : ℕ} : QBlowupVertex a b → Fin 23
  | Sum.inl i => ⟨i.1, by omega⟩
  | Sum.inr (Sum.inl _) => qCopy ⟨10, by decide⟩
  | Sum.inr (Sum.inr _) => qApex

def qBlowupRel {a b : ℕ} (x y : QBlowupVertex a b) : Prop :=
  qKernelRel (qBlowupBaseVertex x) (qBlowupBaseVertex y)

def qBlowup (a b : ℕ) : SimpleGraph (QBlowupVertex a b) :=
  SimpleGraph.fromRel (qBlowupRel (a := a) (b := b))

instance {a b : ℕ} : DecidableRel (qBlowupRel (a := a) (b := b)) := by
  intro x y
  dsimp [qBlowupRel, qBlowupBaseVertex]
  infer_instance

instance {a b : ℕ} : DecidableRel (qBlowup a b).Adj := by
  intro x y
  change Decidable (x ≠ y ∧
    (qBlowupRel (a := a) (b := b) x y ∨
      qBlowupRel (a := a) (b := b) y x))
  infer_instance

def qBlowupSection {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (v : Fin 23) : QBlowupVertex a b :=
  if h21 : v.1 = 21 then
    Sum.inr (Sum.inl ⟨0, by omega⟩)
  else if h22 : v.1 = 22 then
    Sum.inr (Sum.inr ⟨0, by omega⟩)
  else
    Sum.inl ⟨v.1, by omega⟩

theorem qBlowupBaseVertex_section {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (v : Fin 23) :
    qBlowupBaseVertex (qBlowupSection ha hb v) = v := by
  by_cases h21 : v.1 = 21
  · apply Fin.ext
    simp [qBlowupSection, h21, qBlowupBaseVertex, qCopy]
  by_cases h22 : v.1 = 22
  · apply Fin.ext
    simp [qBlowupSection, h21, h22, qBlowupBaseVertex, qApex]
  · apply Fin.ext
    simp [qBlowupSection, h21, h22, qBlowupBaseVertex]

def qBlowupSectionHom {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    qKernelExplicit →g qBlowup a b :=
  { toFun := qBlowupSection ha hb
    map_rel' := by
      intro x y hxy
      have hxy' : x ≠ y ∧ (qKernelRel x y ∨ qKernelRel y x) := by
        simpa [qKernelExplicit, SimpleGraph.fromRel_adj] using hxy
      refine (SimpleGraph.fromRel_adj _ _ _).2 ⟨?_, ?_⟩
      · intro heq
        apply hxy'.1
        have hbase := congrArg (qBlowupBaseVertex (a := a) (b := b)) heq
        simpa [qBlowupBaseVertex_section ha hb] using hbase
      · change qKernelRel (qBlowupBaseVertex (qBlowupSection ha hb x))
          (qBlowupBaseVertex (qBlowupSection ha hb y)) ∨
          qKernelRel (qBlowupBaseVertex (qBlowupSection ha hb y))
            (qBlowupBaseVertex (qBlowupSection ha hb x))
        simpa [qBlowupBaseVertex_section ha hb] using hxy'.2
  }

theorem qKernelRel_irrefl : ∀ x : Fin 23, ¬ qKernelRel x x := by
  decide +kernel

def qBlowupHom (a b : ℕ) : qBlowup a b →g qKernelExplicit :=
  { toFun := qBlowupBaseVertex
    map_rel' := by
      intro x y hxy
      have hxy' : x ≠ y ∧
          (qKernelRel (qBlowupBaseVertex x) (qBlowupBaseVertex y) ∨
            qKernelRel (qBlowupBaseVertex y) (qBlowupBaseVertex x)) := by
        simpa [qBlowup, qBlowupRel, SimpleGraph.fromRel_adj] using hxy
      refine (SimpleGraph.fromRel_adj _ _ _).2 ⟨?_, hxy'.2⟩
      intro hsame
      rcases hxy'.2 with h | h
      · exact (qKernelRel_irrefl _ (hsame ▸ h))
      · exact (qKernelRel_irrefl _ (hsame ▸ h))
  }

theorem qBlowup_triangle_free (a b : ℕ) :
    (qBlowup a b).CliqueFree 3 := by
  exact cliqueFree_three_of_hom (qBlowupHom a b) qKernel_triangle_free

theorem qBlowup_chromatic_at_least_five
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (5 : ℕ∞) ≤ (qBlowup a b).chromaticNumber := by
  change (↑(5 : ℕ) : ℕ∞) ≤ (qBlowup a b).chromaticNumber
  exact le_trans qKernel_chromatic_at_least_five
    (SimpleGraph.chromaticNumber_mono_of_hom (qBlowupSectionHom ha hb))

/- Adjacency lemmas used to count the variable-size family.  The singleton
vertices are indexed by the first 21 vertices of Q; the left class is the
copy of Grötzsch vertex 10, and the right class is the apex. -/
lemma q_adj_a_singleton (a b : ℕ) (x : Fin a) (y : Fin 21) :
    (qBlowup a b).Adj (Sum.inr (Sum.inl x)) (Sum.inl y) ↔
      (y.1 < 10 ∧ 5 ≤ y.1) := by
  by_cases hy : y.1 < 10 <;>
    simp [qBlowup, SimpleGraph.fromRel_adj, qBlowupRel,
      qBlowupBaseVertex, qCopy, qApex, qKernelRel, grotzschRel, c5Adj, hy] <;> omega

lemma q_adj_a_b (a b : ℕ) (x : Fin a) (y : Fin b) :
    (qBlowup a b).Adj (Sum.inr (Sum.inl x)) (Sum.inr (Sum.inr y)) := by
  simp [qBlowup, SimpleGraph.fromRel_adj, qBlowupRel,
    qBlowupBaseVertex, qCopy, qApex, qKernelRel]

lemma q_adj_b_singleton (a b : ℕ) (x : Fin b) (y : Fin 21) :
    (qBlowup a b).Adj (Sum.inr (Sum.inr x)) (Sum.inl y) ↔
      11 ≤ y.1 := by
  simp [qBlowup, SimpleGraph.fromRel_adj, qBlowupRel,
    qBlowupBaseVertex, qCopy, qApex, qKernelRel]
  omega

lemma q_not_adj_a_a (a b : ℕ) (x z : Fin a) :
    ¬ (qBlowup a b).Adj (Sum.inr (Sum.inl x)) (Sum.inr (Sum.inl z)) := by
  simp [qBlowup, SimpleGraph.fromRel_adj, qBlowupRel,
    qBlowupBaseVertex, qCopy, qApex, qKernelRel]

lemma q_not_adj_b_b (a b : ℕ) (x z : Fin b) :
    ¬ (qBlowup a b).Adj (Sum.inr (Sum.inr x)) (Sum.inr (Sum.inr z)) := by
  simp [qBlowup, SimpleGraph.fromRel_adj, qBlowupRel,
    qBlowupBaseVertex, qCopy, qApex, qKernelRel]

lemma q_adj_b_a (a b : ℕ) (x : Fin b) (y : Fin a) :
    (qBlowup a b).Adj (Sum.inr (Sum.inr x)) (Sum.inr (Sum.inl y)) := by
  exact (q_adj_a_b a b y x).symm

lemma q_adj_singleton_a (a b : ℕ) (y : Fin 21) (x : Fin a) :
    (qBlowup a b).Adj (Sum.inl y) (Sum.inr (Sum.inl x)) ↔
      (y.1 < 10 ∧ 5 ≤ y.1) := by
  simpa [SimpleGraph.adj_comm] using (q_adj_a_singleton a b x y)

lemma q_adj_singleton_b (a b : ℕ) (y : Fin 21) (x : Fin b) :
    (qBlowup a b).Adj (Sum.inl y) (Sum.inr (Sum.inr x)) ↔
      11 ≤ y.1 := by
  simpa [SimpleGraph.adj_comm] using (q_adj_b_singleton a b x y)

def qSingletonBaseVertex (y : Fin 21) : Fin 23 :=
  qBlowupBaseVertex (a := 1) (b := 1) (Sum.inl y)

def qSingletonBaseDegree (y : Fin 21) : ℕ :=
  (Finset.univ.filter (fun z : Fin 21 =>
    y ≠ z ∧
      (qKernelRel (qSingletonBaseVertex y) (qSingletonBaseVertex z) ∨
       qKernelRel (qSingletonBaseVertex z) (qSingletonBaseVertex y)))).card

lemma q_adj_singletons (a b : ℕ) (y z : Fin 21) :
    (qBlowup a b).Adj (Sum.inl y) (Sum.inl z) ↔
      (y ≠ z ∧
        (qKernelRel (qSingletonBaseVertex y) (qSingletonBaseVertex z) ∨
         qKernelRel (qSingletonBaseVertex z) (qSingletonBaseVertex y))) := by
  simp [qBlowup, SimpleGraph.fromRel_adj, qBlowupRel,
    qBlowupBaseVertex, qSingletonBaseVertex]

lemma q_degree_a (a b : ℕ) (x : Fin a) :
    (qBlowup a b).degree (Sum.inr (Sum.inl x)) = 5 + b := by
  change ((qBlowup a b).neighborFinset (Sum.inr (Sum.inl x))).card = _
  rw [SimpleGraph.neighborFinset_eq_filter]
  change (Finset.univ.filter
    (fun w => (qBlowup a b).Adj (Sum.inr (Sum.inl x)) w)).card = _
  rw [Finset.card_filter]
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_sum_type]
  simp_rw [q_adj_a_singleton, q_adj_a_b, q_not_adj_a_a]
  have hc : (∑ y : Fin 21, if y.1 < 10 ∧ 5 ≤ y.1 then 1 else 0) = 5 := by
    decide +kernel
  simp [hc]

lemma q_degree_b (a b : ℕ) (x : Fin b) :
    (qBlowup a b).degree (Sum.inr (Sum.inr x)) = 10 + a := by
  change ((qBlowup a b).neighborFinset (Sum.inr (Sum.inr x))).card = _
  rw [SimpleGraph.neighborFinset_eq_filter]
  change (Finset.univ.filter
    (fun w => (qBlowup a b).Adj (Sum.inr (Sum.inr x)) w)).card = _
  rw [Finset.card_filter]
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_sum_type]
  simp_rw [q_adj_b_singleton, q_adj_b_a, q_not_adj_b_b]
  have hc : (∑ y : Fin 21, if 11 ≤ y.1 then 1 else 0) = 10 := by
    decide +kernel
  simp [hc]

lemma q_degree_singleton (a b : ℕ) (y : Fin 21) :
    (qBlowup a b).degree (Sum.inl y) =
      qSingletonBaseDegree y + (if y.1 < 10 ∧ 5 ≤ y.1 then a else 0) +
        (if 11 ≤ y.1 then b else 0) := by
  change ((qBlowup a b).neighborFinset (Sum.inl y)).card = _
  rw [SimpleGraph.neighborFinset_eq_filter]
  change (Finset.univ.filter
    (fun w => (qBlowup a b).Adj (Sum.inl y) w)).card = _
  rw [Finset.card_filter]
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_sum_type]
  simp_rw [q_adj_singletons, q_adj_singleton_a, q_adj_singleton_b]
  simp [qSingletonBaseDegree, Nat.add_assoc]

lemma q_singleton_base_degree_sum :
    (∑ y : Fin 21, qSingletonBaseDegree y) = 110 := by
  unfold qSingletonBaseDegree qSingletonBaseVertex qBlowupBaseVertex qCopy qApex
  decide +kernel

lemma q_singleton_a_weight_sum (a : ℕ) :
    (∑ y : Fin 21, if y.1 < 10 ∧ 5 ≤ y.1 then a else 0) = 5 * a := by
  classical
  have hc : (∑ y : Fin 21, if y.1 < 10 ∧ 5 ≤ y.1 then 1 else 0) = 5 := by
    decide +kernel
  calc
    (∑ y : Fin 21, if y.1 < 10 ∧ 5 ≤ y.1 then a else 0) =
        a * (∑ y : Fin 21, if y.1 < 10 ∧ 5 ≤ y.1 then 1 else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          by_cases h : y.1 < 10 ∧ 5 ≤ y.1 <;> simp [h]
    _ = 5 * a := by rw [hc]; ring

lemma q_singleton_b_weight_sum (b : ℕ) :
    (∑ y : Fin 21, if 11 ≤ y.1 then b else 0) = 10 * b := by
  classical
  have hc : (∑ y : Fin 21, if 11 ≤ y.1 then 1 else 0) = 10 := by
    decide +kernel
  calc
    (∑ y : Fin 21, if 11 ≤ y.1 then b else 0) =
        b * (∑ y : Fin 21, if 11 ≤ y.1 then 1 else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          by_cases h : 11 ≤ y.1 <;> simp [h]
    _ = 10 * b := by rw [hc]; ring

theorem qBlowup_vertex_card (a b : ℕ) :
    Fintype.card (QBlowupVertex a b) = 21 + a + b := by
  simp [QBlowupVertex, Nat.add_assoc]

theorem qBlowup_edgeFinset_card_formula (a b : ℕ) :
    (qBlowup a b).edgeFinset.card = doubleMycielskiBlowupEdges a b := by
  have h := (qBlowup a b).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_sum_type] at h
  rw [Fintype.sum_sum_type] at h
  simp_rw [q_degree_singleton, q_degree_a, q_degree_b] at h
  simp only [Finset.sum_add_distrib] at h
  rw [q_singleton_base_degree_sum, q_singleton_a_weight_sum,
    q_singleton_b_weight_sum] at h
  have h5 : (∑ x : Fin a, 5) = 5 * a := by simp; ring
  have hba : (∑ x : Fin a, b) = b * a := by simp; ring
  have h10 : (∑ x : Fin b, 10) = 10 * b := by simp; ring
  have hab : (∑ x : Fin b, a) = a * b := by simp; ring
  rw [h5, hba, h10, hab] at h
  ring_nf at h
  rw [doubleMycielskiBlowupEdges] at ⊢
  omega

theorem qBlowup_fin_witness
    {a b n : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hn : 21 + a + b = n) :
    ∃ G : SimpleGraph (Fin n), HighChromaticTriangleFree 5 n G ∧
      edgeCount G = doubleMycielskiBlowupEdges a b := by
  let hc : Fintype.card (QBlowupVertex a b) = n := by
    rw [qBlowup_vertex_card]
    exact hn
  let H : SimpleGraph (Fin n) := (qBlowup a b).overFin hc
  let e : qBlowup a b ≃g H := (qBlowup a b).overFinIso hc
  have htf : H.CliqueFree 3 := by
    exact cliqueFree_three_of_hom e.symm.toHom (qBlowup_triangle_free a b)
  have hchi : (5 : ℕ∞) ≤ H.chromaticNumber := by
    exact le_trans (qBlowup_chromatic_at_least_five ha hb)
      (SimpleGraph.chromaticNumber_mono_of_hom e.toHom)
  have hedge : edgeCount H = doubleMycielskiBlowupEdges a b := by
    letI : DecidableRel H.Adj := by
      intro x y
      dsimp [H, SimpleGraph.overFin]
      infer_instance
    have he := e.card_edgeFinset_eq
    rw [edgeCount_eq_edgeFinset_card_r4]
    rw [← he]
    exact qBlowup_edgeFinset_card_formula a b
  exact ⟨H, ⟨htf, hchi⟩, hedge⟩

theorem fiveCandidate_recenter {n : ℕ} (hn : 80 ≤ n) :
    fiveCandidate n = (n - 6) ^ 2 / 4 + 5 := by
  rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
  · have hd := Nat.div_add_mod n 2
    have hnform : n = 2 * (n / 2) := by omega
    have hq : 3 ≤ n / 2 := by omega
    have hsub : n - 6 = 2 * (n / 2 - 3) := by omega
    have hsquare : (n - 6)^2 = 4 * (n / 2 - 3)^2 := by
      rw [hsub]
      ring
    have hdiv : (n - 6)^2 / 4 = (n / 2 - 3)^2 := by
      rw [hsquare]
      simp
    have hnsq : n^2 / 4 = (n / 2)^2 := by
      have hs : n^2 = 4 * (n / 2)^2 := by
        calc
          n^2 = (2 * (n / 2))^2 := congrArg (fun t : ℕ => t^2) hnform
          _ = 4 * (n / 2)^2 := by ring
      rw [hs]
      omega
    simp only [fiveCandidate]
    rw [hdiv, hnsq]
    have hlin : 3 * n = 6 * (n / 2) := by omega
    rw [hlin]
    have hq3 : 3 ≤ n / 2 := by omega
    let t : ℕ := n / 2 - 3
    have hqeq : n / 2 = t + 3 := by
      dsimp [t]
      omega
    have hpoly : (n / 2)^2 + 9 = t^2 + 6 * (n / 2) := by
      rw [hqeq]
      ring
    have hq6 : 6 ≤ n / 2 := by omega
    have hle : 6 * (n / 2) ≤ (n / 2)^2 := by
      simpa [pow_two] using (Nat.mul_le_mul_right (n / 2) hq6)
    change (n / 2)^2 - 6 * (n / 2) + 14 = t^2 + 5
    omega
  · have hd := Nat.div_add_mod n 2
    have hnform : n = 2 * (n / 2) + 1 := by omega
    have hq : 3 ≤ n / 2 := by omega
    have hsub : n - 6 = 2 * (n / 2 - 3) + 1 := by omega
    have hsquare : (n - 6)^2 = 4 * ((n / 2 - 3)^2 + (n / 2 - 3)) + 1 := by
      rw [hsub]
      ring
    have hdiv : (n - 6)^2 / 4 = (n / 2 - 3)^2 + (n / 2 - 3) := by
      rw [hsquare]
      omega
    have hnsq : n^2 / 4 = (n / 2)^2 + (n / 2) := by
      have hs : n^2 = 4 * ((n / 2)^2 + (n / 2)) + 1 := by
        calc
          n^2 = (2 * (n / 2) + 1)^2 := congrArg (fun t : ℕ => t^2) hnform
          _ = 4 * ((n / 2)^2 + (n / 2)) + 1 := by ring
      rw [hs]
      omega
    simp only [fiveCandidate]
    rw [hdiv, hnsq]
    have hlin : 3 * n = 6 * (n / 2) + 3 := by omega
    rw [hlin]
    have hq3 : 3 ≤ n / 2 := by omega
    let t : ℕ := n / 2 - 3
    have hqeq : n / 2 = t + 3 := by
      dsimp [t]
      omega
    have hpoly : (n / 2)^2 + (n / 2) + 6 =
        t^2 + t + 6 * (n / 2) := by
      rw [hqeq]
      ring
    have hq6 : 6 ≤ n / 2 := by omega
    have hle : 6 * (n / 2) + 3 ≤ (n / 2)^2 + (n / 2) := by
      have hmul : 6 * (n / 2) ≤ (n / 2)^2 := by
        simpa [pow_two] using (Nat.mul_le_mul_right (n / 2) hq6)
      omega
    change (n / 2)^2 + (n / 2) - (6 * (n / 2) + 3) + 14 = t^2 + t + 5
    omega

theorem five_blowup_parameters
    {n : ℕ} (hn : 80 ≤ n) :
    ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ 21 + a + b = n ∧
      doubleMycielskiBlowupEdges a b = fiveCandidate n := by
  let N := n - 6
  let q := N / 2
  let a := q - 10
  let b := (N - q) - 5
  have hN : 74 ≤ N := by dsimp [N]; omega
  have hq : 37 ≤ q := by dsimp [q]; omega
  have hceil : 37 ≤ N - q := by dsimp [q]; omega
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · dsimp [a]
    omega
  · dsimp [b]
    omega
  · dsimp [a, b, N]
    omega
  · rw [doubleMycielskiBlowupEdges_recenter]
    have ha : q - 10 + 10 = q := by omega
    have hb : N - q - 5 + 5 = N - q := by omega
    rw [ha, hb]
    have hh := nat_half_mul_ceil_half N
    change q * (N - q) + 5 = fiveCandidate n
    rw [hh]
    exact (fiveCandidate_recenter hn).symm

/-! The explicit family now reaches the extremal functions themselves.  These
lemmas keep the one-edge distinction between `M` and `f` visible: a witness
with exactly `fiveCandidate n` edges gives the lower bound for `M`, and hence
only the strict lower bound for the forcing threshold `f`. -/

/- This is the arithmetic part of the double-Mycielski blow-up family.
The two blown-up vertices are adjacent and have degrees 6 and 11 in Q. -/

end Erdos1011

end Web_Erdos1011_R5
