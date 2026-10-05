# Changelog

## Unreleased

- add a finite `2 × 2` CAR ghost–antighost adapter with an explicit parity
  grading, signed Leibniz law, square-zero differential, and kernel-checked
  closed/exact witnesses;
- export the adapter through the gauge entry point and add positive, axiom,
  and negative elaboration regressions;
- document the finite adapter and keep full ghost-polynomial, BV, continuum,
  anomaly, and physical-equivalence claims as explicit future obligations.

## 1.0.0 — LeanPhy v1

This release migrates the complete `Inspirations/Lean_phy` research prototype
into a standalone repository layout.  It includes:

- the reusable quantum, field-theory, condensed-matter, statistical, gauge,
  classical, relativistic, optics, fluid, and analysis modules;
- proof-bearing research-package and cross-package dependency ledgers;
- continuous-analysis, operator, spectral, approximation, path-integral, PDE,
  and regulator certificate interfaces;
- the `physics` and `physics_search` public tactics, Dirac/index/quantity
  surface layers, CLI reports, scaffolding, smoke tests, and negative tests;
- pinned Lean 4.34.0 and mathlib v4.34.0 dependencies;
- a release verification script and GitHub Actions workflow.

The release is conditionally verified.  Open analytic and physical obligations
remain visible in the generated ledgers and are not represented as proved
claims.
