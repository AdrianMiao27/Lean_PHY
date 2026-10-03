import Mathlib.Topology.MetricSpace.Contracting

/-!
# Contraction and fixed-point certificates

This module exposes the Banach contraction principle through a physics-facing
certificate.  A contraction is the common analytic core of finite-volume RG
fixed points, Picard iteration for nonlinear evolution, dissipative closures
and iterative numerical solvers.  The contraction factor, forward invariance
and completeness are kept visible in the types and typeclass assumptions.

The theorems below do not assert that a physical map is contractive.  They
consume a `ContractingWith` proof checked by the Lean kernel and return the
fixed point, convergence, a posteriori error bounds, and stability under a
uniform perturbation of the map.
-/

namespace LeanPhy.Mathematics

open Filter Function NNReal ENNReal Set
open scoped Topology

universe u

section CompleteMetric

variable {α : Type u} [MetricSpace α] [CompleteSpace α] [Nonempty α]

/-- A named proof that `f` is a contraction with factor `K`.

`ContractingWith K f` contains both `K < 1` and the Lipschitz estimate.  The
wrapper gives downstream research packages a stable field to register as an
assumption or an external analytic certificate.
-/
structure ContractionCertificate (f : α → α) (K : ℝ≥0) : Prop where
  contraction : ContractingWith K f

namespace ContractionCertificate

variable {f : α → α} {K : ℝ≥0}

theorem factor_lt_one (h : ContractionCertificate f K) : K < 1 :=
  h.contraction.1

theorem dist_le_mul (h : ContractionCertificate f K) (x y : α) :
    dist (f x) (f y) ≤ (K : ℝ) * dist x y :=
  h.contraction.dist_le_mul x y

theorem one_sub_pos (h : ContractionCertificate f K) :
    0 < (1 : ℝ) - K :=
  h.contraction.one_sub_K_pos

/-- The canonical fixed point selected by mathlib's contraction theorem. -/
noncomputable def fixedPoint (h : ContractionCertificate f K) : α :=
  h.contraction.fixedPoint f

theorem fixedPoint_isFixedPt (h : ContractionCertificate f K) :
    IsFixedPt f h.fixedPoint :=
  h.contraction.fixedPoint_isFixedPt

theorem fixedPoint_unique (h : ContractionCertificate f K) {x : α}
    (hx : IsFixedPt f x) :
    x = h.fixedPoint :=
  h.contraction.fixedPoint_unique hx

/-- Picard iteration converges to the certified fixed point from any initial
state.  This is the exact convergence statement used by iterative physics
models; no numerical stopping criterion is inferred from a Boolean flag.
-/
theorem iterate_tendsto_fixedPoint (h : ContractionCertificate f K)
    (x : α) :
    Tendsto (fun n => f^[n] x) atTop (𝓝 h.fixedPoint) :=
  h.contraction.tendsto_iterate_fixedPoint x

/-- A posteriori error bound: the distance to the fixed point is bounded by
the latest update divided by `1 - K`. -/
theorem iterate_error_aposteriori (h : ContractionCertificate f K)
    (x : α) (n : ℕ) :
    dist (f^[n] x) h.fixedPoint ≤
      dist (f^[n] x) (f^[n + 1] x) / (1 - K) :=
  h.contraction.aposteriori_dist_iterate_fixedPoint_le x n

/-- A priori geometric error bound from the initial residual. -/
theorem iterate_error_apriori (h : ContractionCertificate f K)
    (x : α) (n : ℕ) :
    dist (f^[n] x) h.fixedPoint ≤
      dist x (f x) * (K : ℝ) ^ n / (1 - K) :=
  h.contraction.apriori_dist_iterate_fixedPoint_le x n

/-- A fixed point is stable under a uniformly bounded perturbation of the map.
Both maps must carry their own contraction certificate; the shared factor is
what makes the explicit `C / (1-K)` bound valid.
-/
theorem fixedPoint_stable_under_map_error
    {g : α → α} (h : ContractionCertificate f K)
    (hg : ContractionCertificate g K) {C : ℝ}
    (hfg : ∀ z, dist (f z) (g z) ≤ C) :
    dist h.fixedPoint hg.fixedPoint ≤ C / (1 - K) :=
  h.contraction.fixedPoint_lipschitz_in_map hg.contraction hfg

/-- A local residual gives an explicit enclosure of the true fixed point. -/
theorem fixedPoint_error_of_residual
    (h : ContractionCertificate f K) (x : α) :
    dist x h.fixedPoint ≤ dist x (f x) / (1 - K) :=
  h.contraction.dist_fixedPoint_le x

end ContractionCertificate

end CompleteMetric

section CompleteInvariantSubset

variable {α : Type u} [MetricSpace α]

/-- A contraction certificate on a complete forward-invariant subset.  This
is the form needed for bounded fields, positivity cones and truncated model
spaces where the ambient metric space itself need not be complete. -/
structure InvariantContractionCertificate (f : α → α) (s : Set α)
    (K : ℝ≥0) : Prop where
  complete : IsComplete s
  invariant : MapsTo f s s
  contraction : ContractingWith K (invariant.restrict f s s)

namespace InvariantContractionCertificate

variable {f : α → α} {s : Set α} {K : ℝ≥0}

noncomputable def fixedPoint
    (h : InvariantContractionCertificate f s K) (x : α) (hx : x ∈ s) : α :=
  ContractingWith.efixedPoint' f h.complete h.invariant h.contraction x hx
    (edist_ne_top x (f x))

theorem fixedPoint_mem
    (h : InvariantContractionCertificate f s K) {x : α} (hx : x ∈ s) :
    h.fixedPoint x hx ∈ s :=
  ContractingWith.efixedPoint_mem' h.complete h.invariant h.contraction hx
    (edist_ne_top x (f x))

theorem fixedPoint_isFixedPt
    (h : InvariantContractionCertificate f s K) {x : α} (hx : x ∈ s) :
    IsFixedPt f (h.fixedPoint x hx) :=
  ContractingWith.efixedPoint_isFixedPt' h.complete h.invariant h.contraction hx
    (edist_ne_top x (f x))

theorem iterate_tendsto_fixedPoint
    (h : InvariantContractionCertificate f s K) {x : α} (hx : x ∈ s) :
    Tendsto (fun n => f^[n] x) atTop (𝓝 (h.fixedPoint x hx)) :=
  ContractingWith.tendsto_iterate_efixedPoint' h.complete h.invariant h.contraction hx
    (edist_ne_top x (f x))

theorem iterate_error_apriori
    (h : InvariantContractionCertificate f s K) {x : α} (hx : x ∈ s)
    (n : ℕ) :
    edist (f^[n] x) (h.fixedPoint x hx) ≤
      edist x (f x) * (K : ℝ≥0∞) ^ n / (1 - K) :=
  ContractingWith.apriori_edist_iterate_efixedPoint_le' h.complete h.invariant
    h.contraction hx (edist_ne_top x (f x)) n

end InvariantContractionCertificate

end CompleteInvariantSubset

end LeanPhy.Mathematics
