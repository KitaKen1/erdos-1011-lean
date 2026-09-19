# Verification of r = 5, n ≥ 80

The delivered proof uses exactly `propext`, `Classical.choice`, and
`Quot.sound`. It does not rely on the superseded native-computation proof.

## Preserved final evidence

- [Standalone proof](../../lean4web/Erdos1011R5KernelLean4Web.lean):
  1,687,346 bytes, 359 complete embedded modules.
- [Bundle manifest](R5_KERNEL_WEB_BUNDLE_MANIFEST.json): per-module source
  hashes, imports, pinned environment, and standalone hash.
- [Local verification result](kernel_web_local_06.json):
  PASS, exit 0, 359/359 modules, 895.676 seconds, completed 2026-09-18.
- [Complete local output](kernel_web_local_06.log): sequential module
  markers, exact target type, three-axiom output, and end-of-file audit.

The local check used Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, with one checker process,
`-j1 -M6144`. It re-elaborated the complete standalone source, importing
only cached Lean/Mathlib dependencies, not project `.olean` files.

Source SHA-256:

```text
33214237de69bdf664c0082ea20e05531a85c74093096a1bc2ff3c9f3e69363e
```

The manifest's `GENERATED_NOT_VERIFIED` status describes the packaging
stage, not the subsequent result. The separate local result records PASS.
Recorded commands retain the original absolute checkout path as provenance;
the offline checker accepts a different checkout location while requiring
the same relative source, source/manifest/log hashes, and bounded command.

## Reproduction

From the repository root, without starting Lean:

```bash
python3 tools/prepare_r5_kernel_web.py --check
python3 tools/check_r5_kernel_web_local.py kernel_web_local_06 --verify-only
python3 -m unittest discover -s tools -p 'test_*.py'
```

For a fresh Lean check, install the pinned dependencies as described in the
[main README](../../README.md), then choose an unused label:

```bash
python3 tools/check_r5_kernel_web_local.py recheck_01 --timeout 1800
```

Offline evidence validation is not a new kernel check and is not a
cryptographic attestation of how the historic run was performed. A fresh
Lean check is the way to independently verify the proof.

## Lean4Web

The maintainer's supplied screenshot shows Lean4Web on Lean 4.35.0-rc2,
the final target, the exact three axioms, and
`R5_KERNEL_WEB_FINISHED standard=3, extra=0, sorryAx=0`.
That screenshot is separate from this repository's hash-bound local
record; no byte-for-byte browser transcript for that screenshot is bundled.
The displayed goal-fetch connection error is not a Lean proof diagnostic.

To check in the browser, load the complete standalone file, wait for its
final audit, and inspect all messages for proof errors. Browser versions
and dependency snapshots can differ from the pinned local environment.

## Scope

This proves the exact values of `M 5 n` and `f 5 n`, and their offset
relation, for every `n ≥ 80`. It does not prove the all-`n`, `r = 5`
catalog target or an extremal isomorphism classification.

On 2026-09-19, repository cleanup moved old proofs and intermediate
experiments outside the repository. The 359 included module sources, final
standalone file, pinned environment files, manifest and final log/result
were left byte-for-byte unchanged. Cleanup checks did not rerun Lean.
