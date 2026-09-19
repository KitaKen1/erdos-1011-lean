import R5Kernel.Parts.M001

/- Source module: Erdos1011.R4. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_R4


/-!
# The r = 4 base construction

This file starts the paper-formalization of the fixed four-colour part of
Erdos #1011.  It deliberately begins with an explicit 11-vertex Grötzsch
graph, rather than hiding the construction behind an opaque constant.
-/

namespace Erdos1011

open SimpleGraph

def c5Adj (i j : Nat) : Prop :=
  i < 5 ∧ j < 5 ∧ i ≠ j ∧ ((i + 1) % 5 = j ∨ (j + 1) % 5 = i)

def grotzschRel (x y : Fin 11) : Prop :=
  let a := x.1
  let b := y.1
  (c5Adj a b) ∨
  (a < 5 ∧ 5 ≤ b ∧ b < 10 ∧ c5Adj a (b - 5)) ∨
  (5 ≤ a ∧ a < 10 ∧ b < 5 ∧ c5Adj b (a - 5)) ∨
  (a = 10 ∧ 5 ≤ b ∧ b < 10) ∨
  (b = 10 ∧ 5 ≤ a ∧ a < 10)

def grotzsch : SimpleGraph (Fin 11) := SimpleGraph.fromRel grotzschRel

instance : DecidableRel grotzschRel := by
  intro x y
  dsimp [grotzschRel, c5Adj]
  infer_instance

/- A computable directed incidence count for explicit finite graphs.  We use
this during construction verification; the generic identification with the
noncomputable `edgeCount` is a separate counting lemma. -/

/- The extremal blow-up used by the fixed-4 formula replaces an adjacent
shadow/apex pair.  Their degrees in the 11-vertex graph are 3 and 5.  After
blowing them up to sizes `a` and `b`, the other 9 vertices stay singletons. -/

theorem edgeCount_eq_edgeFinset_card_r4 {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    edgeCount G = G.edgeFinset.card := by
  classical
  rw [edgeCount]
  rw [← Set.fintypeCard_eq_ncard]
  exact SimpleGraph.edgeFinset_card.symm

theorem nat_half_mul_ceil_half (N : ℕ) :
    (N / 2) * (N - N / 2) = N ^ 2 / 4 := by
  rcases Nat.mod_two_eq_zero_or_one N with h | h
  · have hd := Nat.div_add_mod N 2
    have hN : N = 2 * (N / 2) := by omega
    rw [hN]
    have hdiv : (2 * (N / 2)) / 2 = N / 2 := by omega
    rw [hdiv]
    have hsub : 2 * (N / 2) - N / 2 = N / 2 := by omega
    rw [hsub]
    have hsq : (2 * (N / 2)) ^ 2 = 4 * (N / 2) ^ 2 := by ring
    rw [hsq]
    simp [pow_two]
  · have hd := Nat.div_add_mod N 2
    have hN : N = 2 * (N / 2) + 1 := by omega
    rw [hN]
    have hdiv : (2 * (N / 2) + 1) / 2 = N / 2 := by omega
    rw [hdiv]
    have hsub : 2 * (N / 2) + 1 - N / 2 = N / 2 + 1 := by omega
    rw [hsub]
    have hmul : (N / 2) * (N / 2 + 1) = (N / 2) ^ 2 + N / 2 := by ring
    rw [hmul]
    have hsq : (2 * (N / 2) + 1) ^ 2 =
        4 * ((N / 2) ^ 2 + N / 2) + 1 := by ring
    have hdiv : (4 * ((N / 2) ^ 2 + N / 2) + 1) / 4 =
        (N / 2) ^ 2 + N / 2 := by omega
    rw [hsq]
    exact hdiv.symm

instance : DecidableRel grotzsch.Adj := by
  change DecidableRel (SimpleGraph.fromRel grotzschRel).Adj
  infer_instance

theorem grotzsch_not_three_colorable : ¬ grotzsch.Colorable 3 := by
  intro hc
  rcases hc with ⟨C⟩
  let v : Fin 5 → Fin 11 := fun i => ⟨i.1, by omega⟩
  let u : Fin 5 → Fin 11 := fun i => ⟨i.1 + 5, by omega⟩
  let w : Fin 11 := 10
  have hc5symm {i j : Fin 5} (h : c5Adj i j) : c5Adj j i := by
    refine ⟨j.2, i.2, ?_, ?_⟩
    · exact fun hij => h.2.2.1 hij.symm
    · rcases h.2.2.2 with h | h
      · exact Or.inr h
      · exact Or.inl h
  have hvv {i j : Fin 5} (h : c5Adj i j) :
      grotzsch.Adj (v i) (v j) := by
    rw [grotzsch, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ?_⟩
    · intro hij
      exact h.2.2.1 (congrArg (fun x : Fin 11 => x.val) hij)
    · dsimp only [grotzschRel, v]
      exact Or.inl h
  have huv {i j : Fin 5} (h : c5Adj i j) :
      grotzsch.Adj (u i) (v j) := by
    rw [grotzsch, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ?_⟩
    · intro hij
      have hijv := congrArg Fin.val hij
      dsimp [u, v] at hijv
      omega
    · have hs := hc5symm h
      simp only [grotzschRel, u, v]
      right
      right
      left
      refine ⟨by omega, by omega, j.2, ?_⟩
      simpa using hs
  have huw (i : Fin 5) : grotzsch.Adj (u i) w := by
    rw [grotzsch, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ?_⟩
    · intro hiw
      have hiwv := congrArg Fin.val hiw
      dsimp [u, w] at hiwv
      omega
    · simp only [grotzschRel, u, w]
      right
      right
      right
      right
      exact ⟨rfl, by omega, by omega⟩
  let d : Fin 5 → Fin 3 := fun i =>
    if C (v i) = C w then C (u i) else C (v i)
  have hdw (i : Fin 5) : d i ≠ C w := by
    by_cases hi : C (v i) = C w
    · simpa [d, hi] using C.valid (huw i)
    · simpa [d, hi] using hi
  have hd {i j : Fin 5} (h : c5Adj i j) : d i ≠ d j := by
    by_cases hi : C (v i) = C w
    · by_cases hj : C (v j) = C w
      · exact (C.valid (hvv h)) (hi.trans hj.symm) |>.elim
      · simpa [d, hi, hj] using C.valid (huv h)
    · by_cases hj : C (v j) = C w
      · have hji := huv (hc5symm h)
        simpa [d, hi, hj, ne_eq] using (C.valid hji).symm
      · simpa [d, hi, hj] using C.valid (hvv h)
  have htwoStep : ∀ a x y z : Fin 3,
      x ≠ a → y ≠ a → z ≠ a → x ≠ y → y ≠ z → x = z := by
    intro a x y z hxa hya hza hxy hyz
    fin_cases a <;> fin_cases x <;> fin_cases y <;> fin_cases z <;> simp_all
  have h01 : d 0 ≠ d 1 := hd (by norm_num [c5Adj])
  have h12 : d 1 ≠ d 2 := hd (by norm_num [c5Adj])
  have h23 : d 2 ≠ d 3 := hd (by norm_num [c5Adj])
  have h34 : d 3 ≠ d 4 := hd (by norm_num [c5Adj])
  have h40 : d 4 ≠ d 0 := hd (by norm_num [c5Adj])
  have h02 : d 0 = d 2 :=
    htwoStep (C w) (d 0) (d 1) (d 2) (hdw 0) (hdw 1) (hdw 2) h01 h12
  have h24 : d 2 = d 4 :=
    htwoStep (C w) (d 2) (d 3) (d 4) (hdw 2) (hdw 3) (hdw 4) h23 h34
  exact h40 (h24.symm.trans h02.symm)

end Erdos1011

end Web_Erdos1011_R4
