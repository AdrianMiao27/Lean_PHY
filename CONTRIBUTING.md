# Contributing to LeanPhy

LeanPhy accepts contributions that improve reusable formalisation, proof
diagnostics, documentation, or reproducibility.  The project values a precise
boundary between a mathematical consequence and an external physical premise.

## Before opening a pull request

```bash
lake build
./scripts/verify.sh
```

When working on a mounted or network filesystem, use a local build directory
if Lake or mathlib cache traversal becomes slow.

## Mathematical requirements

- State every analytic condition that a theorem needs: domains, measurability,
  integrability, completeness, positivity, uniformity, or convergence.
- Do not use `sorry`, `admit`, an unchecked axiom, or a runtime Boolean as a
  substitute for a proof.
- Keep physical model adequacy and experimental calibration as explicit
  assumptions or open obligations.
- Prefer a reusable certificate/theorem in `LeanPhy/Mathematics` over copying a
  proof into a domain example.

## Tests and documentation

Add a smoke example for the supported path and a negative fixture when the new
API has a type-level safety boundary.  Update the relevant entry profile,
`VERIFIED.md`, and the roadmap or scope documentation when the verified
boundary changes.  Keep generated `.lake` artifacts out of commits.

## Commit and review guidance

Use a focused commit and describe the assumptions consumed by each new checked
claim.  Reviewers should be able to reproduce the result from the pinned
toolchain and inspect the generated package JSON without relying on external
state.

