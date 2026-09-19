# Small-residual uniform-weight certificates

This note records the mathematical simplification used by the S8–S10 modules.
The final verification evidence is described in [README.md](README.md).
Experimental integer calculations are not being treated as Lean proofs.

Let `U = cycleTypes s ell`, let `R` be a vertex subset, and let `b` bound the
cardinality of every independent set contained in `R`. With scale 2 and
the same nonnegative integer weight `w` at every vertex, the dual expression is

```
D(U,R,b,w) = b * |R| * w
            + sum over I in U with I ∩ R nonempty of
                max(0, 2 * |I| - w * |I ∩ R|).
```

`kernel_dualValue_uniform` proves that this is exactly the existing dual
expression, including natural-number truncated subtraction. The previously
proved minimal-support argument then gives `2 * supportSurplus A B ≤ K`
whenever every nonempty `R` has a valid certificate with `D ≤ K`.
The half-integer weight is `w/2`; the checker needs only natural arithmetic.

The new method does not attempt to retain the tightest old intermediate
bounds. It only needs the final `n ≥ 80` budget. The following bounds,
first found by integer exploration, now have Lean proofs:

| residual size | cycle | scaled bound K | integer surplus bound floor(K/2) | Mantel + surplus | available final budget |
|---|---|---:|---:|---:|---:|
| 8 | C5 | 114 | 57 | 73 | 77 |
| 8 | C7 | 93 | 46 | 62 | 77 |
| 9 | C5 | 164 | 82 | 102 | 114 |
| 9 | C7 | 146 | 73 | 93 | 114 |
| 9 | C9 | 120 | 60 | 80 | 114 |
| 10 | C5 | 226 | 113 | 138 | 149 |
| 10 | C7 | 214 | 107 | 132 | 149 |
| 10 | C9 | 184 | 92 | 117 | 149 |

`tools/analyze_small_uniform.py` reproduces these values with exact integers,
without network access or file writes. It searches `0 ≤ w ≤ 2*s` and chooses
the smallest weight at a tie. Global optimality is not needed or asserted.
S9 is checked by `R5Kernel/S9PartialCertificates.lean` and
`R5Kernel/S9Dispatcher.lean` (standard three axioms only).
S10 is checked by `R5Kernel/S10C5Certificates.lean`, `S10C7Certificates.lean`,
`S10C9Certificates.lean`, and `S10Dispatcher.lean`, also using only the
standard three axioms. All these modules are included in the preserved
[complete standalone check](kernel_web_local_06.log).

For S10, direct evaluation of the large finite-set definitions was replaced
by a structural product cover. The cycle-independent sets (including empty)
are paired with all subsets of the isolated vertices: 11 × 32, 29 × 8,
and 76 × 2 for C5/C7/C9. The proof only needs coverage and nonnegativity;
it does not rely on asserting an exact count or the absence of duplicates.
Dihedral symmetry on the cycle and arbitrary isolated-vertex permutations
reduce the nonempty masks to 47/71/91 representatives. Each numerical chunk
checks at most eight representatives with `decide +kernel`; graph-isomorphism
transport supplies all nonempty certificates. All candidate beta/weight
values are rechecked in Lean, not trusted because Python produced them.

For S8, `S8UniformData.lean` contains candidate `(b,w)` values and explicit
independent-set lists (87 for C5 + 3 isolated vertices, 57 for C7 + 1).
Lean checks that these lists equal `cycleTypes`, checks finite subset
encoding/decoding, and checks every beta condition and dual bound in
16-mask chunks. The numerical data is not a trusted external certificate.
The aggregate theorem uses all 16 chunks per cycle, covering masks 0–255.

`SmallCycleEndpoint.lean` separately proves that the residual graph contains
an odd cycle of length between 5 and its vertex count, extends it to a
spanning vertex labelling, and combines support bounds with Mantel's theorem
and the product bound. This avoids enumerating all labelled residual graphs.
The S8 dispatcher discharges both C5 and C7 from the ordinary
internal extremal-edge hypotheses, without a supplied embedding or table.
Its audit is included in the complete standalone check: exactly three
standard axioms, no extra axioms, and no `sorryAx`.
