# Erdős Problem #1011 in Lean

This repository has three contributions: one statement catalog, a complete
`r = 4` result, and an `r = 5` result for every `n ≥ 80`.

1. **Contribution 1 — Prospective Formal Conjectures formalization.**
   [`FClikeLean.lean`](FClikeLean.lean) formalizes the original all-`r`,
   all-`n` problem and its fixed variants `r = 1, 2, 3, 4, 5`. Every target
   asks for an unknown function through a function-valued `answer(...)` slot;
   no candidate formula is built into the problem statement.
2. **Contribution 2 — Complete `r = 4` result.**
   The Lean proof determines both the maximum triangle-free edge count
   `M 4 n` and the triangle-forcing threshold `f 4 n` for every natural-number
   order `n`, including `n ≤ 10` and the exceptional value `n = 11`.
3. **Contribution 3 — `r = 5`, every `n ≥ 80`.**
   The standalone proof determines `M 5 n` and `f 5 n` throughout this range:
   `M₅(n) = ⌊n²/4⌋ - 3n + 14` and `f₅(n) = ⌊n²/4⌋ - 3n + 15`.
   The modular proof and the standalone Lean4Web source use only the three
   standard axioms: `propext`, `Classical.choice`, and `Quot.sound`.
   The standalone file passed a complete local check of all 359 embedded
   modules on 2026-09-18; the source-bound result and log are included.

For `r = 4`, the complete formula is

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
- [Contribution 3 — `r = 5`, `n ≥ 80` proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ferdos-1011-lean%2Frefs%2Fheads%2Fmain%2Flean4web%2FErdos1011R5KernelLean4Web.lean)
  ([standalone source](lean4web/Erdos1011R5KernelLean4Web.lean),
  [verification instructions and evidence](verification/r5-kernel/README.md)).

Contribution 2 proves the actual finite-graph threshold statement, not only
an arithmetic kernel with the graph-theoretic conclusion supplied as a
hypothesis. The proof includes the explicit lower constructions, the general
upper-bound reduction, and kernel-checked finite certificates.

The original all-`r`, all-`n` problem and the **all-`n`** fixed `r = 5`
variant are not claimed as proved here. Contribution 3 covers `n ≥ 80`
only; it does not settle the remaining `r = 5`, `n < 80` range.

## Formal Conjectures-shaped proved target (`r = 4`)

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

## Proved target for `r = 5`, `n ≥ 80`

The final standalone theorem is:

```lean
namespace Erdos1011KernelLean4Web

theorem formal_target_r5_ge80 :
    ∀ n : ℕ, 80 ≤ n →
      Erdos1011.M 5 n = n ^ 2 / 4 - 3 * n + 14 ∧
      Erdos1011.f 5 n = (n ^ 2 / 4 - 3 * n + 14) + 1 ∧
      Erdos1011.ThresholdExtremalOffset 5 n :=
  Erdos1011Kernel.formal_target_r5_ge80

end Erdos1011KernelLean4Web
```

The modular entry point is
[`R5Kernel/Final.lean`](lean-r5/R5Kernel/Final.lean).
Division and subtraction are natural-number operations. For `n ≥ 80`,
these formulas are exactly `⌊n²/4⌋ - 3n + 14` and one more, respectively.
`ThresholdExtremalOffset 5 n` states `f 5 n = M 5 n + 1`.

The proof includes the graph-theoretic upper bound and explicit lower
witnesses. No certificate hypothesis or near-extremal isomorphism
classification is assumed. The separate `n ≥ 118` classification is not
part of this theorem.

The final dependency audit is:

```text
[propext, Classical.choice, Quot.sound]
R5_KERNEL_PASS Erdos1011KernelLean4Web.formal_target_r5_ge80: standard=3, extra=0, sorryAx=0
R5_KERNEL_WEB_FINISHED standard=3, extra=0, sorryAx=0
```

There are no native-computation or project-specific axioms in this target's
dependency closure. The standalone source re-elaborates all 359 complete
module bodies in import order and imports only Lean/Mathlib, not local
project `.olean` files.

The [verification record](verification/r5-kernel/kernel_web_local_06.json)
and [complete local log](verification/r5-kernel/kernel_web_local_06.log)
record exit code 0, 359/359 modules, and the strict final audit.
See [verification details](verification/r5-kernel/README.md) and the
[small-residual certificate explanation](verification/r5-kernel/UNIFORM_WEIGHTS.md).

## Directory layout

| Path | Contents |
|---|---|
| [`FClikeLean.lean`](FClikeLean.lean) | Prospective all-`r` and fixed-`r` statement catalog |
| [`lean/`](lean/) | Complete `r = 4` local proof, Lean 4.34.0-rc2 |
| [`lean-r5/`](lean-r5/) | Three-axiom `r = 5`, `n ≥ 80` modular proof, Lean 4.34.0 |
| [`lean4web/`](lean4web/) | Standalone sources for the two separate results |
| [`verification/r5-kernel/`](verification/r5-kernel/) | Final `r = 5` source manifest, local verification evidence and notes |
| [`tools/`](tools/) | Reproducible packaging, bounded checkers, witness generators and regression tests |

The proof projects have separate environments. Their standalone sources
repeat shared definitions, so do not import both into one Lean module.
Only the current three-axiom `r = 5` proof is distributed here; superseded
native proofs, unused experiments, intermediate logs and local caches are
not required to reproduce the result.

## Verification

### `r = 4` (existing project)

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

The `r = 4` local and Lean4Web proof files are byte-for-byte identical. The
verified `r = 4` SHA-256 is

```text
9a242885eb9c2b7e218357322a136ed8872f2b7235fded80d288f35d0a798973
```

### `r = 5`, `n ≥ 80`: three-axiom proof

Install the pinned Lean toolchain and fetch the pinned dependencies/cache:

```bash
cd lean-r5
lake exe cache get
cd ..
```

Keep `lean-toolchain` and `lake-manifest.json` unchanged; do not run
`lake update` to reproduce the recorded environment.

For a quick offline packaging/evidence check from the repository root:

```bash
python3 tools/prepare_r5_kernel_web.py --check
python3 tools/check_r5_kernel_web_local.py kernel_web_local_06 --verify-only
python3 -m unittest discover -s tools -p 'test_*.py'
```

These commands check source reproduction, hashes, recorded diagnostics and
Python regressions. They do **not** rerun Lean.

To independently recheck the entire standalone source locally:

```bash
python3 tools/check_r5_kernel_web_local.py recheck_01 --timeout 1800
```

Use a fresh label on every run; existing evidence is never overwritten.
This invokes one Lean checker with `-j1 -M6144`. The recorded run took about
15 minutes; time and total memory use depend on the machine. Do not run
another heavy Lean build concurrently.

For an incremental modular build, use the serial builder:

```bash
python3 tools/build_r5_kernel_serial.py modular_recheck_01 R5Kernel.Final --timeout 600
```

The default Lake target is now `R5Kernel`. Prefer the serial command above
over plain `lake build` to avoid concurrent compilation of heavy modules.
Dependency setup downloads packages; local checks do not upload the proof.

For Lean4Web, load the entire
[`Erdos1011R5KernelLean4Web.lean`](lean4web/Erdos1011R5KernelLean4Web.lean)
and wait for the final axiom audit and `R5_KERNEL_WEB_FINISHED`.
The preserved hash-bound verification environment is Lean 4.34.0; browser
version notes and the distinction between browser and local evidence are
documented in the [verification notes](verification/r5-kernel/README.md).

The standalone `r = 5` SHA-256 is:

```text
33214237de69bdf664c0082ea20e05531a85c74093096a1bc2ff3c9f3e69363e
```

## Mathematical Explanation (AI generated)

The following three subsections explain the existing `r = 4` result.

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
| Fixed `r = 5`, every `n ≥ 80` | `M₅(n) = ⌊n²/4⌋ - 3n + 14`, `f₅(n) = ⌊n²/4⌋ - 3n + 15`; standard three axioms only |

The **OPEN** entry for fixed `r = 5` in the FC-style catalog refers to its
all-`n` target; the new theorem only covers `n ≥ 80`.

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
