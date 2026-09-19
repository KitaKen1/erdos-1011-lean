import R5Kernel.Common

/- Source module: Erdos1011.Basic. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

section Web_Erdos1011_Basic


/-!
# Basic definitions for Erdős Problem #1011

The official question asks for the triangle-forcing threshold `f_r(n)`.  It is
more convenient for extremal graph theory to use `M r n`, the largest edge
count of an `n`-vertex triangle-free graph with chromatic number at least `r`.
When the extremal class is nonempty, the two conventions differ by one:
`f_r(n) = M r n + 1`.  We keep the definitions separate so that this offset
cannot be hidden by notation.

The predicates below are deliberately finite-graph predicates on `Fin n`.
They are suitable for a future Formal Conjectures PR and for importing
enumeration certificates, but do not themselves assert that the reported
computer-assisted bounds have been checked.
-/

namespace Erdos1011

open scoped BigOperators ENat

/-- A triangle-free graph on `Fin n` with chromatic number at least `r`. -/
def HighChromaticTriangleFree (r n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  G.CliqueFree 3 ∧ (r : ℕ∞) ≤ G.chromaticNumber

/-- The edge count of a finite graph.  Using the cardinality of the edge set
directly avoids making the value depend on a particular `Fintype` instance. -/
noncomputable def edgeCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  G.edgeSet.ncard

/-- `m` is a triangle-forcing threshold for the pair `(r,n)`. -/
def IsThreshold (r n m : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    m ≤ edgeCount G →
      (r : ℕ∞) ≤ G.chromaticNumber →
        ¬ G.CliqueFree 3

/- A direct formalization of what it means to have determined all the
thresholds.  This is intentionally separate from the definition of `f`: the
`sInf` definition is useful notation, but the extremal problem asks for a
value together with its minimality properties. -/

/-- The minimum threshold, when viewed as a natural number infimum. -/
noncomputable def f (r n : ℕ) : ℕ :=
  sInf {m : ℕ | IsThreshold r n m}

/-- The extremal triangle-free edge count, using `0` for an empty class. -/
noncomputable def M (r n : ℕ) : ℕ :=
  sSup {m : ℕ |
    ∃ G : SimpleGraph (Fin n), HighChromaticTriangleFree r n G ∧ edgeCount G = m}

/- The usual `f = M + 1` convention is recorded as a separate proposition.
It is not silently built into either definition, since the empty-extremal-class
and existence hypotheses belong to the eventual extremal theorem. -/
def ThresholdExtremalOffset (r n : ℕ) : Prop :=
  f r n = M r n + 1

/- A witness with `m` edges forces the threshold strictly above `m`.  This is
the lower-bound counterpart to `f_eq_succ_and_M_eq_of_isGreatest`; it is useful
for keeping the `M`/`f` one-edge offset explicit. -/

/- A graph homomorphism cannot create a triangle.  This small lemma is useful
for blow-ups: every blown-up edge is mapped back to its shadow edge, so the
triangle-free proof is reduced to the finite shadow graph.  The proof is
spelled out at the 3-clique level rather than relying on a certificate. -/
theorem cliqueFree_three_of_hom
    {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}
    (φ : G →g H) (hH : H.CliqueFree 3) : G.CliqueFree 3 := by
  classical
  intro s hs
  rcases (SimpleGraph.is3Clique_iff.mp hs) with
    ⟨a, b, c, hab, hac, hbc, _⟩
  exact hH _ (SimpleGraph.is3Clique_triple_iff.mpr
    ⟨φ.map_adj hab, φ.map_adj hac, φ.map_adj hbc⟩)

/- The offset between the extremal edge count and the forcing threshold is a
generic finite-graph fact.  Isolating it here prevents every fixed-r theorem
from reproving the same order-theoretic argument. -/
theorem f_eq_succ_and_M_eq_of_isGreatest
    {r n m : ℕ}
    (hM : IsGreatest
      {k : ℕ | ∃ G : SimpleGraph (Fin n),
        HighChromaticTriangleFree r n G ∧ edgeCount G = k} m) :
    f r n = m + 1 ∧ M r n = m := by
  let T : Set ℕ := {k | IsThreshold r n k}
  have hTup : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ T → k₂ ∈ T := by
    intro k₁ k₂ hk h₁
    change IsThreshold r n k₁ at h₁
    change IsThreshold r n k₂
    intro G hG hχ
    exact h₁ G (hk.trans hG) hχ
  have hplus : m + 1 ∈ T := by
    change IsThreshold r n (m + 1)
    intro G hG hχ htriangle
    have hs : ∃ H : SimpleGraph (Fin n),
        HighChromaticTriangleFree r n H ∧ edgeCount H = edgeCount G :=
      ⟨G, ⟨htriangle, hχ⟩, rfl⟩
    have hle : edgeCount G ≤ m := hM.2 hs
    omega
  have hnot : m ∉ T := by
    change ¬ IsThreshold r n m
    intro hm
    obtain ⟨G, hG, hE⟩ := hM.1
    have hbad : ¬ G.CliqueFree 3 := hm G (by simpa [hE]) hG.2
    exact hbad hG.1
  have hfs : sInf T = m + 1 :=
    (Nat.sInf_upward_closed_eq_succ_iff (s := T) hTup m).2 ⟨hplus, hnot⟩
  constructor
  · simpa [f, T] using hfs
  · simpa [M] using hM.csSup_eq

/- A witness predicate is useful for recording the lower-bound half of a
computer-assisted extremal claim without pretending that a construction has
already been checked. -/

/- Isomorphism-complete finite lists are the right interface for the reported
"8 even / 12 odd" classification.  The actual lists belong to the recovered
enumeration certificate, not to this statement layer. -/

/-- The candidate fixed-5 value reported in rounds 02 and 03. -/
def fiveCandidate (n : ℕ) : ℕ := n ^ 2 / 4 - 3 * n + 14

/-- The corresponding threshold convention is one larger. -/
def fiveThresholdCandidate (n : ℕ) : ℕ := fiveCandidate n + 1

/- These are propositions rather than theorems: they are the exact places
where a recovered finite certificate has to be plugged in. -/

def FixedFivePairCandidate : Prop :=
  ∀ n : ℕ, 80 ≤ n →
    M 5 n = fiveCandidate n ∧ f 5 n = fiveThresholdCandidate n ∧
      ThresholdExtremalOffset 5 n

/-- The edge polynomial for the double-Mycielski blow-up lower-bound family. -/
def doubleMycielskiBlowupEdges (a b : ℕ) : ℕ :=
  55 + a * b + 5 * a + 10 * b

/-- Recenter the blow-up polynomial; this is the arithmetic core of the lower construction. -/
theorem doubleMycielskiBlowupEdges_recenter (a b : ℕ) :
    doubleMycielskiBlowupEdges a b = (a + 10) * (b + 5) + 5 := by
  simp [doubleMycielskiBlowupEdges]
  ring

end Erdos1011

end Web_Erdos1011_Basic
