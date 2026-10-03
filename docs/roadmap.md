# LeanPhy roadmap

The v1 boundary is intentionally honest.  Work is prioritized by how many
research workflows a result unlocks, not by the number of isolated examples.

## v1.x priorities

1. **Unbounded Hilbert operators**: connect the existing dense-domain wrapper
   to mathlib's `LinearPMap`, expose closedness and adjoint compatibility, and
   add explicit self-adjoint-extension obligations.
2. **Continuous dynamics**: strengthen the bounded-flow and Duhamel interfaces,
   then connect a supplied generator/resolvent estimate to semigroup stability
   and exponential decay certificates.
3. **PDE and approximation**: add reusable Sobolev/distribution weak-form
   contracts and composable stability-plus-consistency-to-error bridges for
   finite volume, finite element, Galerkin, and lattice approximations.
4. **Spectral and statistical limits**: formalize more compact/resolvent
   perturbation lemmas and finite-volume-to-limit obligations while retaining
   all uniformity and tightness hypotheses explicitly.
5. **Path integrals and QFT**: extend finite Schwinger–Dyson, Ward, reflection,
   and renormalization certificates to function-space interfaces; measure
   existence and Osterwalder–Schrader reconstruction remain separate obligations.
6. **Research usability**: stabilize Dirac/index elaboration, improve Chinese
   diagnostics and semantic lemma search, add real-paper end-to-end benchmarks,
   and preserve native Lean interoperability.

## Deferred topics

General Borel functional calculus, full LSZ/scattering theory, gravity and
string path integrals, global anomaly classification, turbulent closure without
an explicit model, and non-perturbative QFT existence are deferred until the
required mathlib foundations and reusable certificates exist.  They belong in
the open-obligation ledger rather than in unchecked convenience APIs.

## Acceptance rule for new modules

Every new public module should provide:

- a theorem whose proof is checked by the Lean kernel;
- a clear list of hypotheses and an explicit out-of-scope boundary;
- a positive smoke regression and a negative elaboration regression where a
  safety boundary can be violated;
- an entry-point export and documentation showing how the theorem composes
  with existing models or certificates;
- a passing `scripts/verify.sh` run.

