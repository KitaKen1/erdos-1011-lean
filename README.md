# Erdős Problem #1011 in Lean

This repository has two contributions: one statement catalog and one complete
fixed-parameter result.

1. **Contribution 1 — Prospective Formal Conjectures formalization.**
   [`FClikeLean.lean`](FClikeLean.lean) formalizes the original all-`r`,
   all-`n` problem and its fixed variants `r = 1, 2, 3, 4, 5`. Every target
   asks for an unknown function through a function-valued `answer(...)` slot;
   no candidate formula is built into the problem statement.
2. **Contribution 2 — Complete `r = 4` result.**
   The Lean proof determines both the maximum triangle-free edge count
   `M 4 n` and the triangle-forcing threshold `f 4 n` for every natural-number
   order `n`, including `n ≤ 10` and the exceptional value `n = 11`.

In particular, the main proved result is the complete formula

```text
f₄(n) = 0                         if n ≤ 10,
        = 21                        if n = 11,
        = ⌊(n - 3)² / 4⌋ + 6           if n ≥ 12.
```

Here `f₄(n)` is an **edge threshold**: it is the least number of edges that
forces a triangle in an `n`-vertex graph of chromatic number at least four.
The Lean development proves this formula for every `n ∈ ℕ`.

**Try it in Lean4Web:**

- [Contribution 2 — complete `r = 4` proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ferdos-1011-lean%2Frefs%2Fheads%2Fmain%2Flean4web%2FErdos1011R4Lean4Web.lean)

Contribution 2 proves the actual finite-graph threshold statement, not only
an arithmetic kernel with the graph-theoretic conclusion supplied as a
hypothesis. The proof includes the explicit lower constructions, the general
upper-bound reduction, and kernel-checked finite certificates.

The original all-`r` problem and the fixed `r = 5` variant are formalized but
not claimed as proved here.

## Formal Conjectures-shaped proved target

The prospective FC statement asks the solver to provide the function itself:

```lean
theorem erdos_1011.variants.r4 :
    DeterminesThresholdsFor 4 (answer(sorry) : ℕ → ℕ) := by
  sorry
```

The completed implementation supplies that function in the theorem body:

```lean
theorem formal_target_r4 :
    ∃ F : ℕ → ℕ, Erdos1011.DeterminesThresholdsFor 4 F := by
  refine ⟨(fun n =>
    if n ≤ 10 then 0 else if n = 11 then 21
    else (n - 3) ^ 2 / 4 + 6), ?_⟩
  intro n
  apply Erdos1011.isExactThresholdValue_of_f_eq
  exact (Erdos1011.verified_fixed_four_all_n n).2
```

Here `DeterminesThresholdsFor 4 F` says that, for every `n`, `F n` is the
**least** number of edges that forces a triangle in every `n`-vertex graph
whose chromatic number is at least four.

The formalization deliberately keeps the two edge quantities separate:

- `M r n` is the maximum number of edges in a triangle-free `n`-vertex graph
  with chromatic number at least `r`;
- `f r n` is the least edge count that forces a triangle under the same
  chromatic-number condition.

Thus `n` counts vertices, while `M r n` and `f r n` count edges. The usual
relation is `f r n = M r n + 1` only when the extremal class is nonempty.

The proved formulas are

```text
M₄(n) = 0                         if n ≤ 10,
        = 20                        if n = 11,
        = ⌊(n - 3)² / 4⌋ + 5           if n ≥ 12,

f₄(n) = 0                         if n ≤ 10,
        = 21                        if n = 11,
        = ⌊(n - 3)² / 4⌋ + 6           if n ≥ 12.
```

For `n ≤ 10`, the high-chromatic triangle-free class is empty, so both
semantic natural-number extrema are zero; one must not apply the `+1` rule in
that range.

The final audit is part of the standalone proof:

```lean
#check formal_target_r4
#print axioms formal_target_r4
```

Its output is exactly

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx`, project-specific mathematical axiom, or
`native_decide` axiom in the dependency closure of the proved target. The
`sorry` expressions in `FClikeLean.lean` are intentional answer/proof slots in
the prospective problem statement and are not imported by the completed
proof.

## Directory layout

| Path | Contents |
|---|---|
| [`FClikeLean.lean`](FClikeLean.lean) | Unofficial FC-style original problem and fixed variants `r = 1, 2, 3, 4, 5` |
| [`lean/`](lean/) | Local project containing one standalone, complete `r = 4` proof |
| [`lean4web/`](lean4web/) | One copy-and-paste Lean4Web file for the same `r = 4` proof |

No final `r = 5` threshold theorem is exported or claimed by the proof
directories. The weaker `r5_eventual` statement has also been omitted from
the FC-style catalog.

## Verification

```bash
cd lean
lake update
lake exe cache get
lake build
```

The Lean4Web file can be checked directly in the same environment:

```bash
cd lean
lake env lean ../lean4web/Erdos1011R4Lean4Web.lean
```

For public Lean4Web, select **Latest Mathlib with Lean v4.34.0-rc2** and load
the complete contents of
[`lean4web/Erdos1011R4Lean4Web.lean`](lean4web/Erdos1011R4Lean4Web.lean).
The file embeds the finite CNF/LRAT data, so no filesystem write or external
SAT solver is required during checking.

The released local and Lean4Web proof files are byte-for-byte identical. The
verified SHA-256 is

```text
9a242885eb9c2b7e218357322a136ed8872f2b7235fded80d288f35d0a798973
```

## Mathematical Explanation (AI generated)

### The range `n ≤ 10`

The required fact is that every triangle-free graph on at most ten vertices
is 3-colourable. The proof relabels a maximum-degree vertex as vertex zero
and normalizes its neighbourhood. One guarded CNF covers the possible
maximum degrees, and a pre-generated LRAT refutation is checked inside Lean.
A padding argument transports the ten-vertex statement to every smaller
order. The external SAT solver used to discover the certificate is not a
trusted proof step.

Consequently, no triangle-free graph in this range has chromatic number at
least four, and the natural-number values are `M₄(n) = f₄(n) = 0`.

### The exceptional order `n = 11`

The Grötzsch graph gives a triangle-free 4-chromatic graph with 20 edges. The
upper-bound argument shows that every triangle-free 4-chromatic graph on
eleven vertices has at most 20 edges. Hence

```text
M₄(11) = 20,    f₄(11) = 21.
```

### The range `n ≥ 12`

Explicit constructions give the lower bound
`⌊(n - 3)²/4⌋ + 5`. For the upper bound, the proof chooses an extremal
graph, performs the twinization and support reductions, and reduces the
remaining residual-neighbourhood cases to finite capacity computations.
Those computations are checked by Lean's kernel. The result is

```text
M₄(n) = ⌊(n - 3)²/4⌋ + 5.
```

Since the extremal class is nonempty here, the forcing threshold is exactly
one larger:

```text
f₄(n) = ⌊(n - 3)²/4⌋ + 6.
```

## References

- [Erdős Problem #1011](https://www.erdosproblems.com/1011)
- [Google DeepMind Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
- [Ren–Wang–Wang–Yang, *Extremal triangle-free graphs with chromatic number at least four*](https://arxiv.org/abs/2404.07486)
- [`erdos-612-lean`](https://github.com/KitaKen1/erdos-612-lean), used as the README and repository-layout model

## AI usage disclosure

This formalization, computer-assisted proof development, and documentation
were produced with assistance from OpenAI Codex and ChatGPT Astra under the
direction of KitaKen1 (Kenta Kitamura).

## Appendix A — Status by chromatic parameter

| Target | Status in the FC-style catalog |
|---|---|
| Original all-`r`, all-`n` problem | **OPEN** |
| Fixed `r = 1` | SOLVED |
| Fixed `r = 2` | SOLVED |
| Fixed `r = 3` | SOLVED |
| Fixed `r = 4` | **SOLVED · This project claim** |
| Fixed `r = 5` | **OPEN** |

### This project's proved contribution

| Target | Result |
|---|---|
| Fixed `r = 4`, every `n ∈ ℕ` | Complete piecewise formula for both `M₄(n)` and `f₄(n)` |

## Appendix B — Conjecture formalization in FClikeLean

The original determine-the-function target is

```lean
theorem erdos_1011.formal_target :
    DeterminesThresholds (answer(sorry) : ℕ → ℕ → ℕ) := by
  sorry
```

The unknown answer is the two-argument function `F r n`. Each fixed variant
specializes `r` and asks for a one-argument function `F n`. The candidate
formula does not occur in the target's hypotheses; supplying it is part of
solving the problem.
