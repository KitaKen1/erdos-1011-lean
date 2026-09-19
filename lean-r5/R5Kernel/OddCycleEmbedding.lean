import R5Kernel.Parts.M014
import R5Kernel.Probes.S11C5CanonicalDefinitions
import R5Kernel.Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxHeartbeats 3000000

/- Structural odd-cycle extraction, isolated from the finite table chain.
The proofs are transported from M035/M036 with fresh declaration names. -/
namespace Erdos1011
open SimpleGraph

theorem kernel_exists_odd_closed_walk_of_not_colorable_two
    {α : Type*} {H : SimpleGraph α}
    (hnot2 : ¬ H.Colorable 2) :
    ∃ u : α, ∃ w : H.Walk u u, Odd w.length := by
  have hnot : ¬ (∀ u, ∀ w : H.Walk u u, Even w.length) := by
    intro hall
    exact hnot2 ((SimpleGraph.two_colorable_iff_forall_loop_even).2 hall)
  push Not at hnot
  rcases hnot with ⟨u, w, hw⟩
  exact ⟨u, w, Nat.not_even_iff_odd.mp hw⟩

/- A shortest odd closed walk has no repeated interior vertex.  The proof uses
   `take`/`drop` at two repeated positions: the intervening loop and the
   complementary loop have lengths summing to the original odd length, so one
   is a strictly shorter odd closed walk, contradicting minimality. -/
theorem kernel_exists_odd_cycle_of_exists_odd_closed_walk
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (h : ∃ u : V, ∃ w : G.Walk u u, Odd w.length) :
    ∃ u : V, ∃ p : G.Walk u u, p.IsCycle ∧ Odd p.length := by
  classical
  let P : ℕ → Prop := fun k =>
    ∃ u : V, ∃ w : G.Walk u u, Odd w.length ∧ w.length = k
  have hP : ∃ k, P k := by
    rcases h with ⟨u, w, hw⟩
    exact ⟨w.length, u, w, hw, rfl⟩
  let k := Nat.find hP
  obtain ⟨u, w, hwodd, hwlen⟩ := Nat.find_spec hP
  have hnon_nil : ¬ w.Nil := by
    intro hnil
    have : w.length = 0 := by simpa [Walk.Nil.eq_nil hnil]
    rcases hwodd with ⟨j, hj⟩
    omega
  have hlen_ne_one : w.length ≠ 1 := by
    intro h1
    exact (Walk.adj_of_length_eq_one h1).ne rfl
  have hlen3 : 3 ≤ w.length := by
    rcases hwodd with ⟨j, hj⟩
    have hpos : 0 < w.length := by omega
    omega
  have hcycle : w.IsCycle := by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    constructor
    · by_contra htail
      have hnd : ¬ w.tail.support.Nodup := by
        intro hnd'
        exact htail ((Walk.isPath_def _).2 hnd')
      obtain ⟨x, hxd⟩ := (List.exists_duplicate_iff_not_nodup).2 hnd
      obtain ⟨i, j, hij, hi, hj⟩ :=
        (List.duplicate_iff_exists_distinct_get).1 hxd
      have hi_le : (i : ℕ) ≤ w.tail.length := by
        have hs := w.tail.length_support
        omega
      have hj_le : (j : ℕ) ≤ w.tail.length := by
        have hs := w.tail.length_support
        omega
      have hti : w.tail.getVert (i : ℕ) = x := by
        rw [w.tail.getVert_eq_support_getElem hi_le]
        exact hi.symm
      have htj : w.tail.getVert (j : ℕ) = x := by
        rw [w.tail.getVert_eq_support_getElem hj_le]
        exact hj.symm
      let a : ℕ := (i : ℕ) + 1
      let b : ℕ := (j : ℕ) + 1
      have hab : a < b := by
        dsimp [a, b]
        omega
      have haL : a ≤ w.length := by
        dsimp [a]
        rw [← w.length_tail_add_one hnon_nil]
        omega
      have hbL : b ≤ w.length := by
        dsimp [b]
        rw [← w.length_tail_add_one hnon_nil]
        omega
      have habv : w.getVert a = w.getVert b := by
        dsimp [a, b]
        simpa [Walk.getVert_tail] using hti.trans htj.symm
      let q0 := (w.drop a).take (b - a)
      have hdrop : b - a ≤ (w.drop a).length := by
        rw [Walk.drop_length]
        have hLsub : w.length - a + a = w.length := Nat.sub_add_cancel haL
        omega
      have hq0len : q0.length = b - a := by
        dsimp [q0]
        rw [Walk.take_length, Nat.min_eq_left hdrop]
      have hqend : (w.drop a).getVert (b - a) = w.getVert a := by
        rw [Walk.drop_getVert]
        rw [Nat.add_sub_of_le (Nat.le_of_lt hab)]
        exact habv.symm
      let q : G.Walk (w.getVert a) (w.getVert a) := q0.copy rfl hqend
      have hqlen : q.length = b - a := by
        simp [q, hq0len]
      let r0 := (w.drop b).append (w.take a)
      have hrlen : r0.length = (w.length - b) + a := by
        simp [r0, Walk.drop_length, Walk.take_length,
          Nat.min_eq_left haL]
      let r : G.Walk (w.getVert a) (w.getVert a) := r0.copy habv.symm rfl
      have hrlen' : r.length = (w.length - b) + a := by
        simp [r, hrlen]
      have hsum : q.length + r.length = w.length := by
        rw [hqlen, hrlen']
        omega
      have hq_lt : q.length < w.length := by
        rw [hqlen]
        omega
      have hr_lt : r.length < w.length := by
        rw [hrlen']
        omega
      have hoddSum : Odd (q.length + r.length) := by
        exact hsum ▸ hwodd
      rcases (Nat.even_or_odd q.length) with hqe | hqo
      · have hro : Odd r.length := (Nat.odd_add').mp hoddSum |>.mpr hqe
        have hmin : ¬ P r.length := by
          apply Nat.find_min
          rw [← hwlen]
          exact hr_lt
        exact (hmin ⟨_, r, hro, rfl⟩).elim
      · have hmin : ¬ P q.length := by
          apply Nat.find_min
          rw [← hwlen]
          exact hq_lt
        exact (hmin ⟨_, q, hqo, rfl⟩).elim
    · exact hlen3
  exact ⟨u, w, hcycle, hwodd⟩

/- The same extraction applied to the residual graph selected by an edge in a
   high-chromatic triangle-free graph.  This is the first fully generic S7
   residual witness; later work only has to shorten the odd walk to a simple
   odd cycle and then invoke the finite seven-vertex classifier. -/
theorem kernel_residual_exists_odd_closed_walk_of_high_five
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (hG : HighChromaticTriangleFree 5 n G) (huv : G.Adj u v) :
    ∃ x : {x : Fin n // x ∈ residualSet G u v},
      ∃ w : (G.induce (residualSet G u v)).Walk x x, Odd w.length := by
  exact kernel_exists_odd_closed_walk_of_not_colorable_two
    (residual_not_colorable_two_of_high_five hG huv)

theorem kernel_residual_exists_odd_cycle_of_high_five
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (hG : HighChromaticTriangleFree 5 n G) (huv : G.Adj u v) :
    ∃ x : {x : Fin n // x ∈ residualSet G u v},
      ∃ p : (G.induce (residualSet G u v)).Walk x x,
        p.IsCycle ∧ Odd p.length := by
  classical
  exact kernel_exists_odd_cycle_of_exists_odd_closed_walk
    (kernel_residual_exists_odd_closed_walk_of_high_five hG huv)

/- On the sharp seven-vertex branch, the odd-walk witness is already enough
   to feed the existing finite classifier: it implies non-2-colourability,
   and the five-edge bound then forces the bare C₅ model. -/

/-! On seven vertices, a triangle-free simple cycle which is odd can only
    have length five or seven.  This is the graph-theoretic fork used by the
    S7 structural dispatcher: length five enters the C5 attachment tables,
    while length seven enters the pure C7 table.  The lemma intentionally
    takes an explicit cycle witness; the generic extraction theorem is kept
    separate so that arbitrary finite graphs do not trigger an expensive
    enumeration of all `2^21` seven-vertex graphs on the 24GB development
    machine.  The high-five residual case is transported in
    `R5S7OddCycleBridge.lean`. -/
theorem kernel_r5_odd_cycle_length_le_card
    {s : ℕ} {H : SimpleGraph (Fin s)} [DecidableRel H.Adj]
    {u : Fin s} (p : H.Walk u u) (hcyc : p.IsCycle) :
    p.length ≤ s := by
  have htail : p.tail.length < Fintype.card (Fin s) :=
    hcyc.isPath_tail.length_lt
  have hlt : p.length ≤ s := by
    simp only [Fintype.card_fin] at htail
    have htail' : p.length - 1 < s := by
      simpa only [Walk.length_tail] using htail
    omega
  exact hlt

theorem kernel_r5_odd_cycle_length_cases_fin11
    {H : SimpleGraph (Fin 11)} [DecidableRel H.Adj]
    (htri : H.CliqueFree 3) {u : Fin 11} (p : H.Walk u u)
    (hcyc : p.IsCycle) (hodd : Odd p.length) :
    p.length = 5 ∨ p.length = 7 ∨ p.length = 9 ∨ p.length = 11 := by
  have hle := kernel_r5_odd_cycle_length_le_card p hcyc
  have hnot3 : p.length ≠ 3 := by
    intro hp3
    rcases (is3Clique_iff_exists_cycle_length_three (G := H)).mpr
      ⟨u, p, hcyc, hp3⟩ with ⟨s, hs⟩
    exact htri s hs
  rcases hodd with ⟨k, hk⟩
  have hlow : 3 ≤ p.length := hcyc.three_le_length
  omega

noncomputable def kernel_residualEmbeddingOfCardEq
    {n s : ℕ} (T : Finset (Fin n)) (hT : T.card = s) : Fin s ↪ Fin n :=
  (T.equivFinOfCardEq hT).symm.toEmbedding.trans
    (Function.Embedding.subtype _)

theorem kernel_residualEmbeddingOfCardEq_mem
    {n s : ℕ} (T : Finset (Fin n)) (hT : T.card = s) (i : Fin s) :
    kernel_residualEmbeddingOfCardEq T hT i ∈ T := by
  dsimp [kernel_residualEmbeddingOfCardEq]
  exact (T.equivFinOfCardEq hT).symm i |>.property

theorem kernel_residualEmbeddingOfCardEq_range
    {n s : ℕ} (T : Finset (Fin n)) (hT : T.card = s) :
    Set.range (kernel_residualEmbeddingOfCardEq T hT) = (T : Set (Fin n)) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact kernel_residualEmbeddingOfCardEq_mem T hT i
  · intro hx
    let e : T ≃ Fin s := T.equivFinOfCardEq hT
    let y : T := ⟨x, hx⟩
    refine ⟨e y, ?_⟩
    dsimp [kernel_residualEmbeddingOfCardEq, e, y]
    simp

/- A cycle embedding on the first `ell` labels can be extended to a
   permutation of all `s` labels.  The extension is deliberately
   noncomputable: only existence is needed, and `Equiv.extendSubtype` keeps
   the prescribed values on the cycle while bijectively filling the
   complement. -/
noncomputable def kernel_r5ExtendEmbeddingToPerm
    {s ell : ℕ} (hEll : ell ≤ s) (g : Fin ell ↪ Fin s) :
    Fin s ≃ Fin s := by
  let e : {x : Fin s // x.val < ell} ≃ Set.range g := by
    let h : {x : Fin s // x.val < ell} → Set.range g := fun x =>
      ⟨g ⟨x.1.val, x.2⟩, Set.mem_range_self _⟩
    have hinj : Function.Injective h := by
      intro x y hxy
      apply Subtype.ext
      apply Fin.ext
      have hfin : (⟨x.1.val, x.2⟩ : Fin ell) = ⟨y.1.val, y.2⟩ :=
        g.injective (congrArg Subtype.val hxy)
      exact congrArg (fun z : Fin ell => z.val) hfin
    have hsurj : Function.Surjective h := by
      intro z
      rcases z.property with ⟨i, hi⟩
      refine ⟨⟨⟨i.val, Nat.lt_of_lt_of_le i.isLt hEll⟩, ?_⟩, ?_⟩
      · exact i.isLt
      · apply Subtype.ext
        simpa [h] using hi
    exact Equiv.ofBijective h ⟨hinj, hsurj⟩
  exact e.extendSubtype

theorem kernel_r5ExtendEmbeddingToPerm_apply
    {s ell : ℕ} (hEll : ell ≤ s) (g : Fin ell ↪ Fin s)
    (i : Fin ell) :
    kernel_r5ExtendEmbeddingToPerm hEll g
      ⟨i.val, Nat.lt_of_lt_of_le i.isLt hEll⟩ = g i := by
  let e : {x : Fin s // x.val < ell} ≃ Set.range g := by
    let h : {x : Fin s // x.val < ell} → Set.range g := fun x =>
      ⟨g ⟨x.1.val, x.2⟩, Set.mem_range_self _⟩
    have hinj : Function.Injective h := by
      intro x y hxy
      apply Subtype.ext
      apply Fin.ext
      have hfin : (⟨x.1.val, x.2⟩ : Fin ell) = ⟨y.1.val, y.2⟩ :=
        g.injective (congrArg Subtype.val hxy)
      exact congrArg (fun z : Fin ell => z.val) hfin
    have hsurj : Function.Surjective h := by
      intro z
      rcases z.property with ⟨j, hj⟩
      refine ⟨⟨⟨j.val, Nat.lt_of_lt_of_le j.isLt hEll⟩, ?_⟩, ?_⟩
      · exact j.isLt
      · apply Subtype.ext
        simpa [h] using hj
    exact Equiv.ofBijective h ⟨hinj, hsurj⟩
  change e.extendSubtype ⟨i.val, Nat.lt_of_lt_of_le i.isLt hEll⟩ = g i
  rw [Equiv.extendSubtype_apply_of_mem e _ i.isLt]
  rfl

/- One-way edge transport for the canonical cycle-plus-isolates universe.
   The reverse direction is intentionally not required: extra edges in the
   residual graph only remove independent sets. -/
theorem kernel_r5CycleGraphAdj_of_succ
    {β : Type*} {s ell : ℕ} {H : SimpleGraph β}
    (hEll : ell ≤ s) (hEll0 : 0 < ell)
    (F : Fin s → β)
    (hcycle : ∀ i : Fin ell,
      H.Adj (F ⟨i.val, Nat.lt_of_lt_of_le i.isLt hEll⟩)
        (F ⟨(i.val + 1) % ell,
          Nat.lt_of_lt_of_le (Nat.mod_lt _ hEll0) hEll⟩)) :
    ∀ {x y : Fin s}, (cycleGraph s ell).Adj x y → H.Adj (F x) (F y) := by
  intro x y hxy
  change x ≠ y ∧ (cycleRel s ell x y ∨ cycleRel s ell y x) at hxy
  rcases hxy with ⟨_, hxyrel | hyxrel⟩
  · rcases hxyrel with ⟨hx, hy, hsucc | hprev⟩
    · let hi : Fin ell := ⟨x.val, hx⟩
      let hj : Fin ell := ⟨y.val, hy⟩
      have hxi : x = ⟨hi.val, Nat.lt_of_lt_of_le hi.isLt hEll⟩ := by
        apply Fin.ext
        simp [hi]
      have hyj : y = ⟨hj.val, Nat.lt_of_lt_of_le hj.isLt hEll⟩ := by
        apply Fin.ext
        simp [hj]
      have heq : ⟨(hi.val + 1) % ell, Nat.mod_lt _ hEll0⟩ = hj := by
        apply Fin.ext
        simpa [hi, hj] using hsucc
      rw [hxi, hyj, ← heq]
      exact hcycle hi
    · let hi : Fin ell := ⟨y.val, hy⟩
      let hj : Fin ell := ⟨x.val, hx⟩
      have hxi : x = ⟨hj.val, Nat.lt_of_lt_of_le hj.isLt hEll⟩ := by
        apply Fin.ext
        simp [hj]
      have hyj : y = ⟨hi.val, Nat.lt_of_lt_of_le hi.isLt hEll⟩ := by
        apply Fin.ext
        simp [hi]
      have heq : ⟨(hi.val + 1) % ell, Nat.mod_lt _ hEll0⟩ = hj := by
        apply Fin.ext
        simpa [hi, hj] using hprev
      rw [hxi, hyj, ← heq]
      exact (hcycle hi).symm
  · rcases hyxrel with ⟨hy, hx, hsucc | hprev⟩
    · let hi : Fin ell := ⟨y.val, hy⟩
      let hj : Fin ell := ⟨x.val, hx⟩
      have hxi : x = ⟨hj.val, Nat.lt_of_lt_of_le hj.isLt hEll⟩ := by
        apply Fin.ext
        simp [hj]
      have hyj : y = ⟨hi.val, Nat.lt_of_lt_of_le hi.isLt hEll⟩ := by
        apply Fin.ext
        simp [hi]
      have heq : ⟨(hi.val + 1) % ell, Nat.mod_lt _ hEll0⟩ = hj := by
        apply Fin.ext
        simpa [hi, hj] using hsucc
      rw [hxi, hyj, ← heq]
      exact (hcycle hi).symm
    · let hi : Fin ell := ⟨x.val, hx⟩
      let hj : Fin ell := ⟨y.val, hy⟩
      have hxi : x = ⟨hi.val, Nat.lt_of_lt_of_le hi.isLt hEll⟩ := by
        apply Fin.ext
        simp [hi]
      have hyj : y = ⟨hj.val, Nat.lt_of_lt_of_le hj.isLt hEll⟩ := by
        apply Fin.ext
        simp [hj]
      have heq : ⟨(hi.val + 1) % ell, Nat.mod_lt _ hEll0⟩ = hj := by
        apply Fin.ext
        simpa [hi, hj] using hprev
      rw [hxi, hyj, ← heq]
      exact hcycle hi

theorem kernel_r5WalkCycleAdj_mod
    {β : Type*} {ell : ℕ} {H : SimpleGraph β} {u : β}
    (q : H.Walk u u) (_hcyc : q.IsCycle) (hlen : q.length = ell)
    (hell0 : 0 < ell) :
    ∀ i : Fin ell,
      H.Adj (q.getVert i.val)
        (q.getVert ((i.val + 1) % ell)) := by
  intro i
  by_cases hlt : i.val + 1 < ell
  · have hiq : i.val < q.length := by
      rw [hlen]
      omega
    have hadj := q.adj_getVert_succ (i := i.val) hiq
    have hmod : (i.val + 1) % ell = i.val + 1 := Nat.mod_eq_of_lt hlt
    simpa [hmod] using hadj
  · have hiq : i.val < q.length := by
      rw [hlen]
      omega
    have hadj := q.adj_getVert_succ (i := i.val) hiq
    have heq : i.val + 1 = ell := by omega
    have hmod : (i.val + 1) % ell = 0 := by
      rw [heq]
      exact Nat.mod_self ell
    rw [hmod, q.getVert_zero]
    have hlen' : q.getVert ell = u := by simpa [hlen] using q.getVert_length
    simpa [heq, hlen'] using hadj

/- Main spanning-embedding bridge.  A simple odd cycle in the labelled
   residual comap is extended to all residual vertices, yielding precisely the
   embedding shape consumed by the generated S9--S11 row certificates. -/
theorem kernel_r5SpanningEmbeddingOfCycle
    {n s ell : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (T : Finset (Fin n)) (hT : T.card = s) {u : Fin s}
    (q : (G.comap (kernel_residualEmbeddingOfCardEq T hT)).Walk u u)
    (hcyc : q.IsCycle) (hlen : q.length = ell)
    (hEll : ell ≤ s) (hEll0 : 0 < ell) :
    ∃ f : Fin s ↪ Fin n,
      Set.range f = (T : Set (Fin n)) ∧
      ∀ {x y : Fin s}, (cycleGraph s ell).Adj x y →
        G.Adj (f x) (f y) := by
  let g0 : Fin s ↪ Fin n := kernel_residualEmbeddingOfCardEq T hT
  let cyc : Fin ell ↪ Fin s :=
    { toFun := fun i => q.getVert i.val
      inj' := by
        intro i j hij
        apply Fin.ext
        apply hcyc.getVert_injOn'
        · rw [hlen]
          change i.val ≤ ell - 1
          omega
        · rw [hlen]
          change j.val ≤ ell - 1
          omega
        simpa using hij }
  let P : Fin s ≃ Fin s := kernel_r5ExtendEmbeddingToPerm hEll cyc
  let f : Fin s ↪ Fin n := P.toEmbedding.trans g0
  have hfrange : Set.range f = Set.range g0 := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨P i, rfl⟩
    · intro hz
      rcases hz with ⟨j, rfl⟩
      refine ⟨P.symm j, ?_⟩
      simp [f]
  have hFcycle : ∀ i : Fin ell,
      f ⟨i.val, Nat.lt_of_lt_of_le i.isLt hEll⟩ = g0 (cyc i) := by
    intro i
    simp [f, P, kernel_r5ExtendEmbeddingToPerm_apply hEll cyc i]
  have hcycle : ∀ i : Fin ell,
      G.Adj (f ⟨i.val, Nat.lt_of_lt_of_le i.isLt hEll⟩)
        (f ⟨(i.val + 1) % ell,
          Nat.lt_of_lt_of_le (Nat.mod_lt _ hEll0) hEll⟩) := by
    intro i
    have hadj := kernel_r5WalkCycleAdj_mod q hcyc hlen hEll0 i
    change G.Adj (g0 (q.getVert i.val))
      (g0 (q.getVert ((i.val + 1) % ell))) at hadj
    let j : Fin ell := ⟨(i.val + 1) % ell, Nat.mod_lt _ hEll0⟩
    rw [hFcycle i, hFcycle j]
    change G.Adj (g0 (q.getVert i.val)) (g0 (q.getVert j.val))
    simpa [j] using hadj
  refine ⟨f, ?_, ?_⟩
  · rw [hfrange, kernel_residualEmbeddingOfCardEq_range T hT]
  · intro x y hxy
    exact kernel_r5CycleGraphAdj_of_succ hEll hEll0 f hcycle hxy

theorem kernel_residualComap_iso_induce
    {n s : ℕ} {G : SimpleGraph (Fin n)}
    (T : Finset (Fin n)) (hT : T.card = s) :
    Nonempty (G.comap (kernel_residualEmbeddingOfCardEq T hT) ≃g
      G.induce (T : Set (Fin n))) := by
  classical
  let f := kernel_residualEmbeddingOfCardEq T hT
  let g : Fin s → (T : Set (Fin n)) := fun i =>
    ⟨f i, kernel_residualEmbeddingOfCardEq_mem T hT i⟩
  have hginj : Function.Injective g := by
    intro i j hij
    apply f.injective
    exact congrArg Subtype.val hij
  have hgsurj : Function.Surjective g := by
    intro y
    have hyT : y.1 ∈ (T : Set (Fin n)) := y.2
    have hyrange : y.1 ∈ Set.range f := by
      rw [kernel_residualEmbeddingOfCardEq_range T hT]
      exact hyT
    rcases Set.mem_range.mp hyrange with ⟨i, hi⟩
    refine ⟨i, Subtype.ext ?_⟩
    exact hi
  let eS : Fin s ≃ (T : Set (Fin n)) :=
    Equiv.ofBijective g ⟨hginj, hgsurj⟩
  refine ⟨{ toEquiv := eS, map_rel_iff' := ?_ }⟩
  intro i j
  change G.Adj (f i) (f j) ↔ G.Adj (eS i).1 (eS j).1
  rfl

theorem kernel_r5_odd_cycle_of_induced_cycle_generic
    {n s : ℕ} {G : SimpleGraph (Fin n)}
    (T : Finset (Fin n)) (hT : T.card = s)
    {x : (T : Set (Fin n))}
    (p : (G.induce (T : Set (Fin n))).Walk x x)
    (hcyc : p.IsCycle) (hodd : Odd p.length) :
    ∃ u : Fin s, ∃ q :
      (G.comap (kernel_residualEmbeddingOfCardEq T hT)).Walk u u,
      q.IsCycle ∧ Odd q.length := by
  classical
  let f := kernel_residualEmbeddingOfCardEq T hT
  obtain ⟨isoT⟩ := kernel_residualComap_iso_induce T hT
  let q : (G.comap f).Walk (isoT.symm.toEquiv x) (isoT.symm.toEquiv x) :=
    p.map isoT.symm.toHom
  have hqcyc : q.IsCycle := hcyc.map isoT.symm.toEquiv.injective
  have hqodd : Odd q.length := by
    simpa [q] using hodd
  exact ⟨isoT.symm.toEquiv x, q, hqcyc, hqodd⟩

/- Ambient residual handoff for arbitrary finite residual size.  The odd cycle
   forced by high five-chromaticity is first transported from `residualSet` to
   its cardinality-labelled finset, then to the canonical `Fin s` comap. -/
theorem kernel_r5_odd_cycle_of_high_extremal_residual_card_generic
    {n s : ℕ} {G : SimpleGraph (Fin n)}
    (hG : HighChromaticTriangleFree 5 n G) {u v : Fin n}
    (huv : G.Adj u v)
    (hS : (residualSet G u v).ncard = s) :
    ∃ hT : (residualFinset G u v).card = s,
      ∃ u' : Fin s, ∃ q :
        (G.comap (kernel_residualEmbeddingOfCardEq (residualFinset G u v) hT)).Walk u' u',
        q.IsCycle ∧ Odd q.length := by
  classical
  let T := residualFinset G u v
  have hT : T.card = s := by
    dsimp [T]
    rw [residualFinset_card_eq_ncard]
    exact hS
  have hTset : (T : Set (Fin n)) = residualSet G u v := by
    dsimp [T]
    ext x
    exact mem_residualFinset_iff (G := G) (u := u) (v := v)
  let g : residualSet G u v → (T : Set (Fin n)) := fun y =>
    ⟨y.1, by rw [hTset]; exact y.2⟩
  have hginj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    simpa [g] using congrArg Subtype.val hab
  have hgsurj : Function.Surjective g := by
    intro y
    refine ⟨⟨y.1, hTset ▸ y.2⟩, ?_⟩
    rfl
  let eS : residualSet G u v ≃ (T : Set (Fin n)) :=
    Equiv.ofBijective g ⟨hginj, hgsurj⟩
  let eInd : (G.induce (residualSet G u v)) ≃g
      G.induce (T : Set (Fin n)) :=
    { toEquiv := eS
      map_rel_iff' := by
        intro a b
        change G.Adj a.1 b.1 ↔ G.Adj (eS a).1 (eS b).1
        rfl }
  obtain ⟨x, p, hcyc, hodd⟩ := kernel_residual_exists_odd_cycle_of_high_five hG huv
  let pT := p.map eInd.toHom
  have hcycT : pT.IsCycle := hcyc.map eInd.toEquiv.injective
  have hoddT : Odd pT.length := by simpa [pT] using hodd
  obtain ⟨u', q, hqcyc, hqodd⟩ :=
    kernel_r5_odd_cycle_of_induced_cycle_generic T hT (x := eInd x)
      pT hcycT hoddT
  simpa [T] using ⟨hT, u', q, hqcyc, hqodd⟩

theorem kernel_r5_odd_cycle_profile_cases_of_high_extremal_residual_card_fin11
    {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (hG : HighChromaticTriangleFree 5 n G) (huv : G.Adj u v)
    (hS : (residualSet G u v).ncard = 11) :
    ∃ hT : (residualFinset G u v).card = 11,
      ∃ u' : Fin 11, ∃ q :
        (G.comap (kernel_residualEmbeddingOfCardEq (residualFinset G u v) hT)).Walk u' u',
        q.IsCycle ∧ Odd q.length ∧
          (q.length = 5 ∨ q.length = 7 ∨ q.length = 9 ∨ q.length = 11) := by
  classical
  obtain ⟨hT, u', q, hqcyc, hqodd⟩ :=
    kernel_r5_odd_cycle_of_high_extremal_residual_card_generic hG huv hS
  let f := kernel_residualEmbeddingOfCardEq (residualFinset G u v) hT
  letI : DecidableRel (G.comap f).Adj := Classical.decRel _
  have htri11 : (G.comap f).CliqueFree 3 := by
    exact SimpleGraph.CliqueFree.comap
      (SimpleGraph.Embedding.comap f G).isContained hG.1
  exact ⟨hT, u', q, hqcyc, hqodd,
    kernel_r5_odd_cycle_length_cases_fin11 htri11 q hqcyc hqodd⟩

theorem kernel_r5_high_extremal_spanning_embedding_fin11
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {u v : Fin n}
    (hG : HighChromaticTriangleFree 5 n G) (huv : G.Adj u v)
    (hS : (residualSet G u v).ncard = 11) :
    ∃ hT : (residualFinset G u v).card = 11,
      ∃ u' : Fin 11, ∃ q :
        (G.comap (kernel_residualEmbeddingOfCardEq (residualFinset G u v) hT)).Walk u' u',
        q.IsCycle ∧ Odd q.length ∧
        ((∃ f : Fin 11 ↪ Fin n,
            Set.range f = residualSet G u v ∧
            ∀ {x y : Fin 11}, (cycleGraph 11 5).Adj x y →
              G.Adj (f x) (f y)) ∨
         (∃ f : Fin 11 ↪ Fin n,
            Set.range f = residualSet G u v ∧
            ∀ {x y : Fin 11}, (cycleGraph 11 7).Adj x y →
              G.Adj (f x) (f y)) ∨
         (∃ f : Fin 11 ↪ Fin n,
            Set.range f = residualSet G u v ∧
            ∀ {x y : Fin 11}, (cycleGraph 11 9).Adj x y →
              G.Adj (f x) (f y)) ∨
         (∃ f : Fin 11 ↪ Fin n,
            Set.range f = residualSet G u v ∧
            ∀ {x y : Fin 11}, (cycleGraph 11 11).Adj x y →
              G.Adj (f x) (f y))) := by
  rcases kernel_r5_odd_cycle_profile_cases_of_high_extremal_residual_card_fin11 hG huv hS with
    ⟨hT, u', q, hqcyc, hqodd, hlen5 | hlen7 | hlen9 | hlen11⟩
  · have hTset : (residualFinset G u v : Set (Fin n)) = residualSet G u v := by
      ext x
      exact mem_residualFinset_iff (G := G) (u := u) (v := v)
    refine ⟨hT, u', q, hqcyc, hqodd, ?_⟩
    let hs := kernel_r5SpanningEmbeddingOfCycle (residualFinset G u v) hT q hqcyc
      hlen5 (by norm_num) (by norm_num)
    let f : Fin 11 ↪ Fin n := Classical.choose hs
    have hf := Classical.choose_spec hs
    exact Or.inl ⟨f, by rw [hf.1, hTset], hf.2⟩
  · have hTset : (residualFinset G u v : Set (Fin n)) = residualSet G u v := by
      ext x
      exact mem_residualFinset_iff (G := G) (u := u) (v := v)
    refine ⟨hT, u', q, hqcyc, hqodd, ?_⟩
    let hs := kernel_r5SpanningEmbeddingOfCycle (residualFinset G u v) hT q hqcyc
      hlen7 (by norm_num) (by norm_num)
    let f : Fin 11 ↪ Fin n := Classical.choose hs
    have hf := Classical.choose_spec hs
    exact Or.inr (Or.inl ⟨f, by rw [hf.1, hTset], hf.2⟩)
  · have hTset : (residualFinset G u v : Set (Fin n)) = residualSet G u v := by
      ext x
      exact mem_residualFinset_iff (G := G) (u := u) (v := v)
    refine ⟨hT, u', q, hqcyc, hqodd, ?_⟩
    let hs := kernel_r5SpanningEmbeddingOfCycle (residualFinset G u v) hT q hqcyc
      hlen9 (by norm_num) (by norm_num)
    let f : Fin 11 ↪ Fin n := Classical.choose hs
    have hf := Classical.choose_spec hs
    exact Or.inr (Or.inr (Or.inl ⟨f, by rw [hf.1, hTset], hf.2⟩))
  · have hTset : (residualFinset G u v : Set (Fin n)) = residualSet G u v := by
      ext x
      exact mem_residualFinset_iff (G := G) (u := u) (v := v)
    refine ⟨hT, u', q, hqcyc, hqodd, ?_⟩
    let hs := kernel_r5SpanningEmbeddingOfCycle (residualFinset G u v) hT q hqcyc
      hlen11 (by norm_num) (by norm_num)
    let f : Fin 11 ↪ Fin n := Classical.choose hs
    have hf := Classical.choose_spec hs
    exact Or.inr (Or.inr (Or.inr ⟨f, by rw [hf.1, hTset], hf.2⟩))


run_cmd R5Kernel.checkStandardAxioms ``kernel_residual_exists_odd_cycle_of_high_five
run_cmd R5Kernel.checkStandardAxioms ``kernel_r5SpanningEmbeddingOfCycle
run_cmd R5Kernel.checkStandardAxioms ``kernel_r5_high_extremal_spanning_embedding_fin11

end Erdos1011

