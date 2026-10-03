import LeanPhy.Mathematics.CertifiedResidual
import Mathlib.Tactic

/-!
# Finite weak forms and PDE residuals

A continuum PDE becomes a finite algebraic problem after choosing a mesh,
finite-element basis, lattice or truncated mode set.  This module records the
common part without pretending that discretisation converges: a finite
incidence/gradient table defines a weak operator, its energy and a residual
certificate.  The kernel proves the summation-by-parts identity, positivity of
the stiffness form and the constant zero mode when the incidence rows sum to
zero.

Regularity, boundary conditions, coercivity, stability, convergence rates and
existence of a continuum solution remain explicit inputs to a higher layer.
-/

namespace LeanPhy.Mathematics

open scoped BigOperators

universe u v

/-- A finite gradient/incidence table from vertex fields to edge/element
fields.  The row-sum condition is the discrete analogue of a derivative of a
constant vanishing. -/
structure FiniteGradient (V : Type u) (E : Type v)
    [Fintype V] [Fintype E] where
  incidence : E → V → ℝ
  incidence_sum_zero : ∀ e, ∑ x, incidence e x = 0

namespace FiniteGradient

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]

/-- Finite gradient of a vertex field. -/
def gradient (G : FiniteGradient V E) (u : V → ℝ) : E → ℝ :=
  fun e => ∑ x, G.incidence e x * u x

@[simp] theorem gradient_apply (G : FiniteGradient V E) (u : V → ℝ) (e : E) :
    G.gradient u e = ∑ x, G.incidence e x * u x := rfl

/-- The finite stiffness/Dirichlet bilinear form. -/
def energy (G : FiniteGradient V E) (u v : V → ℝ) : ℝ :=
  ∑ e, G.gradient u e * G.gradient v e

@[simp] theorem energy_apply (G : FiniteGradient V E) (u v : V → ℝ) :
    G.energy u v = ∑ e, G.gradient u e * G.gradient v e := rfl

/-- The positive finite weak operator `Bᵀ B`. -/
def laplacian (G : FiniteGradient V E) (u : V → ℝ) : V → ℝ :=
  fun x => ∑ e, G.incidence e x * G.gradient u e

@[simp] theorem laplacian_apply (G : FiniteGradient V E) (u : V → ℝ) (x : V) :
    G.laplacian u x = ∑ e, G.incidence e x * G.gradient u e := rfl

/-- The stiffness form is nonnegative on the diagonal. -/
theorem energy_nonneg (G : FiniteGradient V E) (u : V → ℝ) :
    0 ≤ G.energy u u := by
  unfold energy
  exact Finset.sum_nonneg (fun e he => mul_self_nonneg _)

/-- Finite summation by parts: the edge energy equals the vertex pairing with
`BᵀB`.  This is the algebraic core shared by finite-element and lattice PDEs.
-/
theorem energy_eq_pairing_laplacian (G : FiniteGradient V E)
    (u v : V → ℝ) :
    G.energy u v = ∑ x, u x * G.laplacian v x := by
  unfold energy laplacian gradient
  calc
    (∑ e, (∑ x, G.incidence e x * u x) *
        (∑ y, G.incidence e y * v y)) =
        ∑ e, ∑ x, ∑ y,
          (G.incidence e x * u x) * (G.incidence e y * v y) := by
      apply Finset.sum_congr rfl
      intro e he
      calc
        (∑ x, G.incidence e x * u x) *
            (∑ y, G.incidence e y * v y) =
            ∑ x, (G.incidence e x * u x) *
              (∑ y, G.incidence e y * v y) := by
                rw [Finset.sum_mul]
        _ = ∑ x, ∑ y,
              (G.incidence e x * u x) * (G.incidence e y * v y) := by
                apply Finset.sum_congr rfl
                intro x hx
                rw [Finset.mul_sum]
    _ = ∑ x, ∑ e, ∑ y,
          (G.incidence e x * u x) * (G.incidence e y * v y) := by
      rw [Finset.sum_comm]
    _ = ∑ x, u x * (∑ e, G.incidence e x * (∑ y, G.incidence e y * v y)) := by
      apply Finset.sum_congr rfl
      intro x hx
      calc
        (∑ e, ∑ y, (G.incidence e x * u x) *
            (G.incidence e y * v y)) =
            ∑ e, (G.incidence e x * u x) *
              (∑ y, G.incidence e y * v y) := by
                apply Finset.sum_congr rfl
                intro e he
                rw [Finset.mul_sum]
        _ = ∑ e, u x * (G.incidence e x *
              (∑ y, G.incidence e y * v y)) := by
                apply Finset.sum_congr rfl
                intro e he
                ring
        _ = u x * (∑ e, G.incidence e x *
              (∑ y, G.incidence e y * v y)) := by
                rw [Finset.mul_sum]

/-- Constants have zero finite gradient. -/
theorem gradient_const (G : FiniteGradient V E) (c : ℝ) :
    G.gradient (fun _ => c) = 0 := by
  funext e
  unfold gradient
  change (∑ x, G.incidence e x * c) = 0
  rw [← Finset.sum_mul]
  rw [G.incidence_sum_zero]
  simp

/-- Constants are in the kernel of the finite weak Laplacian. -/
theorem laplacian_const (G : FiniteGradient V E) (c : ℝ) :
    G.laplacian (fun _ => c) = 0 := by
  funext x
  unfold laplacian
  rw [G.gradient_const c]
  simp

/-- The Laplacian quadratic form is nonnegative. -/
theorem laplacian_pairing_nonneg (G : FiniteGradient V E) (u : V → ℝ) :
    0 ≤ ∑ x, u x * G.laplacian u x := by
  rw [← G.energy_eq_pairing_laplacian]
  exact G.energy_nonneg u

/-- A finite Poisson residual.  The sign convention is the positive operator
`BᵀB`; changing to the continuum `Δ` is an explicit convention at the adapter
layer. -/
def poissonResidual (G : FiniteGradient V E)
    (u source : V → ℝ) : V → ℝ :=
  fun x => G.laplacian u x - source x

/-- An exact finite Poisson solution has a zero residual certificate. -/
theorem poissonResidual_zero (G : FiniteGradient V E)
    (u source : V → ℝ)
    (h : G.laplacian u = source) :
    EquationResidual (fun v => G.poissonResidual v source) u 0 := by
  apply equationResidual_zero
  funext x
  have hx := congrFun h x
  change G.laplacian u x - source x = 0
  rw [hx]
  simp

end FiniteGradient

/-- A generic finite linear PDE, useful when a discretization is supplied as a
matrix rather than an incidence table. -/
structure FiniteLinearPDE (ι : Type u) [Fintype ι] where
  operator : Matrix ι ι ℝ
  source : ι → ℝ

namespace FiniteLinearPDE

variable {ι : Type u} [Fintype ι]

def residual (P : FiniteLinearPDE ι) (u : ι → ℝ) : ι → ℝ :=
  P.operator.mulVec u - P.source

def IsSolution (P : FiniteLinearPDE ι) (u : ι → ℝ) : Prop :=
  P.operator.mulVec u = P.source

theorem residual_zero (P : FiniteLinearPDE ι) (u : ι → ℝ)
    (h : P.IsSolution u) :
    EquationResidual (fun v => P.residual v) u 0 := by
  apply equationResidual_zero
  funext i
  have hi := congrFun h i
  simp [residual, hi]

theorem residual_weaken {P : FiniteLinearPDE ι} {u : ι → ℝ}
    {ε δ : ℝ} (h : EquationResidual (fun v => P.residual v) u ε) (hεδ : ε ≤ δ) :
    EquationResidual (fun v => P.residual v) u δ :=
  equationResidual_weaken h hεδ

/-- The quadratic form associated with a finite linear operator.  It is kept
as a separate definition so a coercivity or stability estimate can be supplied
as an explicit certificate rather than inferred from the word "elliptic". -/
def quadratic (P : FiniteLinearPDE ι) (u : ι → ℝ) : ℝ :=
  ∑ i, u i * (P.operator.mulVec u) i

@[simp] theorem quadratic_apply (P : FiniteLinearPDE ι) (u : ι → ℝ) :
    P.quadratic u = ∑ i, u i * (P.operator.mulVec u) i := rfl

/-- A finite coercivity certificate.  The constant and the inequality are
inputs: this records precisely the stability fact needed by a later PDE layer
without claiming that an arbitrary discretisation is coercive. -/
structure CoercivityCertificate (P : FiniteLinearPDE ι) where
  modulus : ℝ
  modulus_pos : 0 < modulus
  bound : ∀ u, modulus * (∑ i, u i ^ 2) ≤ P.quadratic u

theorem quadratic_zero_of_operator_zero (P : FiniteLinearPDE ι)
    {u : ι → ℝ} (hu : P.operator.mulVec u = 0) :
    P.quadratic u = 0 := by
  unfold quadratic
  simp [hu]

/-- A coercivity certificate rules out a nonzero null vector. -/
theorem coercive_operator_eq_zero (P : FiniteLinearPDE ι)
    (C : CoercivityCertificate P) {u : ι → ℝ}
    (hu : P.operator.mulVec u = 0) : u = 0 := by
  have hq : P.quadratic u = 0 := P.quadratic_zero_of_operator_zero hu
  have hsum_nonneg : 0 ≤ ∑ i, u i ^ 2 :=
    Finset.sum_nonneg (fun i hi => sq_nonneg (u i))
  have hbound := C.bound u
  rw [hq] at hbound
  have hsum_le : ∑ i, u i ^ 2 ≤ 0 := by
    nlinarith [C.modulus_pos, hbound]
  have hsum : ∑ i, u i ^ 2 = 0 := le_antisymm hsum_le hsum_nonneg
  funext i
  have hterm_le : u i ^ 2 ≤ ∑ j, u j ^ 2 := by
    exact Finset.single_le_sum (fun j hj => sq_nonneg (u j))
      (Finset.mem_univ i)
  have hterm : u i ^ 2 = 0 := by
    have hterm_nonneg : 0 ≤ u i ^ 2 := sq_nonneg (u i)
    exact le_antisymm (hterm_le.trans_eq hsum) hterm_nonneg
  exact (sq_eq_zero_iff).mp hterm

theorem solution_unique_of_coercive (P : FiniteLinearPDE ι)
    (C : CoercivityCertificate P) {u v : ι → ℝ}
    (hu : P.IsSolution u) (hv : P.IsSolution v) : u = v := by
  apply sub_eq_zero.mp
  apply P.coercive_operator_eq_zero C
  funext i
  have hi := congrFun hu i
  have hj := congrFun hv i
  simp [Matrix.mulVec_sub, hi, hj]

end FiniteLinearPDE

/-- Boundary data are represented separately from the operator.  This makes
Dirichlet values and the portion of the boundary used by a discretisation
visible in a proof state. -/
structure FiniteBoundaryData (ι : Type u) where
  isBoundary : ι → Prop
  value : ι → ℝ

def SatisfiesBoundary {ι : Type u} (B : FiniteBoundaryData ι)
    (u : ι → ℝ) : Prop :=
  ∀ i, B.isBoundary i → u i = B.value i

/-! Numerical boundary data need their own residual budget.  A pointwise
certificate is used so a discretisation can report which boundary nodes are
responsible for the error; exact boundary satisfaction is recovered only at
zero radius. -/

structure FiniteBoundaryResidualCertificate {ι : Type u} [Fintype ι]
    (B : FiniteBoundaryData ι) (u : ι → ℝ) where
  radius : ι → ℝ
  radius_nonneg : ∀ i, 0 ≤ radius i
  bound : ∀ i, B.isBoundary i → |u i - B.value i| ≤ radius i

namespace FiniteBoundaryResidualCertificate

variable {ι : Type u} [Fintype ι]

/-- Exact Dirichlet data are represented by a zero-radius certificate. -/
def exact (B : FiniteBoundaryData ι) (u : ι → ℝ)
    (h : SatisfiesBoundary B u) :
    FiniteBoundaryResidualCertificate B u :=
  { radius := fun _ => 0
    radius_nonneg := fun _ => le_rfl
    bound := by
      intro i hi
      rw [h i hi]
      simp }

/-- Widening pointwise boundary budgets preserves the certificate. -/
def weaken {B : FiniteBoundaryData ι} {u : ι → ℝ}
    (C : FiniteBoundaryResidualCertificate B u) {radius : ι → ℝ}
    (h : ∀ i, C.radius i ≤ radius i) :
    FiniteBoundaryResidualCertificate B u :=
  { radius := radius
    radius_nonneg := fun i => (C.radius_nonneg i).trans (h i)
    bound := fun i hi => (C.bound i hi).trans (h i) }

/-- Independent boundary error sources are added pointwise. -/
def combine {B : FiniteBoundaryData ι} {u : ι → ℝ}
    (C₁ C₂ : FiniteBoundaryResidualCertificate B u) :
    FiniteBoundaryResidualCertificate B u :=
  { radius := fun i => C₁.radius i + C₂.radius i
    radius_nonneg := fun i =>
      add_nonneg (C₁.radius_nonneg i) (C₂.radius_nonneg i)
    bound := fun i hi =>
      (C₁.bound i hi).trans (le_add_of_nonneg_right (C₂.radius_nonneg i)) }

/-- Zero boundary radius is strong enough to recover exact Dirichlet data. -/
theorem satisfies_of_zero {B : FiniteBoundaryData ι} {u : ι → ℝ}
    (C : FiniteBoundaryResidualCertificate B u)
    (hzero : ∀ i, C.radius i = 0) : SatisfiesBoundary B u := by
  intro i hi
  have hb := C.bound i hi
  rw [hzero i] at hb
  have hz : |u i - B.value i| = 0 := le_antisymm hb (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp hz)

end FiniteBoundaryResidualCertificate

theorem boundary_values_agree {ι : Type u} (B : FiniteBoundaryData ι)
    {u v : ι → ℝ} (hu : SatisfiesBoundary B u)
    (hv : SatisfiesBoundary B v) :
    ∀ i, B.isBoundary i → u i = v i := by
  intro i hi
  rw [hu i hi, hv i hi]

def SatisfiesHomogeneousBoundary {ι : Type u} (B : FiniteBoundaryData ι)
    (u : ι → ℝ) : Prop :=
  ∀ i, B.isBoundary i → u i = 0

theorem sub_satisfies_homogeneous_boundary {ι : Type u}
    (B : FiniteBoundaryData ι) {u v : ι → ℝ}
    (hu : SatisfiesBoundary B u) (hv : SatisfiesBoundary B v) :
    SatisfiesHomogeneousBoundary B (u - v) := by
  intro i hi
  simp [hu i hi, hv i hi]

/-- Coercivity on the homogeneous Dirichlet subspace.  This is the form used
by finite-element and finite-difference uniqueness arguments: coercivity is
only required for perturbations that vanish on the prescribed boundary. -/
structure BoundaryCoercivityCertificate {ι : Type u} [Fintype ι]
    (P : FiniteLinearPDE ι) (B : FiniteBoundaryData ι) where
  modulus : ℝ
  modulus_pos : 0 < modulus
  bound : ∀ u, SatisfiesHomogeneousBoundary B u →
    modulus * (∑ i, u i ^ 2) ≤ P.quadratic u

namespace FiniteLinearPDE

theorem solution_unique_of_boundary_coercive {ι : Type u} [Fintype ι]
    (P : FiniteLinearPDE ι) (B : FiniteBoundaryData ι)
    (C : BoundaryCoercivityCertificate P B) {u v : ι → ℝ}
    (hu : P.IsSolution u) (hv : P.IsSolution v)
    (huB : SatisfiesBoundary B u) (hvB : SatisfiesBoundary B v) : u = v := by
  apply sub_eq_zero.mp
  have hzero : P.operator.mulVec (u - v) = 0 := by
    funext i
    have hi := congrFun hu i
    have hj := congrFun hv i
    simp [Matrix.mulVec_sub, hi, hj]
  have hq : P.quadratic (u - v) = 0 :=
    P.quadratic_zero_of_operator_zero hzero
  have hhom : SatisfiesHomogeneousBoundary B (u - v) :=
    sub_satisfies_homogeneous_boundary B huB hvB
  have hsum_nonneg : 0 ≤ ∑ i, (u - v) i ^ 2 :=
    Finset.sum_nonneg (fun i hi => sq_nonneg ((u - v) i))
  have hbound := C.bound (u - v) hhom
  rw [hq] at hbound
  have hsum_le : ∑ i, (u - v) i ^ 2 ≤ 0 := by
    nlinarith [C.modulus_pos, hbound]
  have hsum : ∑ i, (u - v) i ^ 2 = 0 :=
    le_antisymm hsum_le hsum_nonneg
  funext i
  have hterm_le : (u - v) i ^ 2 ≤ ∑ j, (u - v) j ^ 2 := by
    exact Finset.single_le_sum (fun j hj => sq_nonneg ((u - v) j))
      (Finset.mem_univ i)
  have hterm : (u - v) i ^ 2 = 0 := by
    have hterm_nonneg : 0 ≤ (u - v) i ^ 2 := sq_nonneg ((u - v) i)
    exact le_antisymm (hterm_le.trans_eq hsum) hterm_nonneg
  exact (sq_eq_zero_iff).mp hterm

end FiniteLinearPDE

structure FiniteEllipticProblem (ι : Type u) [Fintype ι] where
  equation : FiniteLinearPDE ι
  boundary : FiniteBoundaryData ι

def FiniteEllipticProblem.IsSolution {ι : Type u} [Fintype ι]
    (P : FiniteEllipticProblem ι) (u : ι → ℝ) : Prop :=
  P.equation.IsSolution u ∧ SatisfiesBoundary P.boundary u

/-! A single auditable certificate for a finite elliptic calculation.  The
residual radius and boundary condition are kept together so an adapter cannot
silently use a numerical residual while forgetting the boundary data. -/

structure FiniteEllipticCertificate {ι : Type u} [Fintype ι]
    (P : FiniteEllipticProblem ι) (u : ι → ℝ) where
  residualRadius : ℝ
  residual_nonneg : 0 ≤ residualRadius
  residual : EquationResidual (fun v => P.equation.residual v) u residualRadius
  boundary : SatisfiesBoundary P.boundary u

namespace FiniteEllipticCertificate

variable {ι : Type u} [Fintype ι]

/-- An exact finite solution is the zero-radius certificate. -/
def exact (P : FiniteEllipticProblem ι) (u : ι → ℝ)
    (h : P.IsSolution u) : FiniteEllipticCertificate P u :=
  { residualRadius := 0
    residual_nonneg := le_rfl
    residual := P.equation.residual_zero u h.1
    boundary := h.2 }

/-- A certificate may be weakened when an additional error budget is allowed. -/
def weaken {P : FiniteEllipticProblem ι} {u : ι → ℝ}
    (C : FiniteEllipticCertificate P u) {δ : ℝ}
    (hδ : C.residualRadius ≤ δ) : FiniteEllipticCertificate P u :=
  { residualRadius := δ
    residual_nonneg := C.residual_nonneg.trans hδ
    residual := equationResidual_weaken C.residual hδ
    boundary := C.boundary }

/-- Independent residual budgets can be accumulated explicitly.  This is a
small bookkeeping theorem, but keeping it in the kernel prevents an adapter
from dropping one of its error sources. -/
def combine {P : FiniteEllipticProblem ι} {u : ι → ℝ}
    (C₁ C₂ : FiniteEllipticCertificate P u) : FiniteEllipticCertificate P u :=
  { residualRadius := C₁.residualRadius + C₂.residualRadius
    residual_nonneg := add_nonneg C₁.residual_nonneg C₂.residual_nonneg
    residual := equationResidual_weaken C₁.residual (by
      linarith [C₂.residual_nonneg])
    boundary := C₁.boundary }

theorem isSolution_of_radius_zero {P : FiniteEllipticProblem ι}
    {u : ι → ℝ} (C : FiniteEllipticCertificate P u)
    (hzero : C.residualRadius = 0) : P.IsSolution u := by
  have hr : P.equation.residual u = 0 := by
    apply dist_eq_zero.mp
    have hupper := C.residual.bound
    rw [hzero] at hupper
    exact le_antisymm hupper dist_nonneg
  refine ⟨?_, C.boundary⟩
  funext i
  have hi := congrFun hr i
  change P.equation.operator.mulVec u i = P.equation.source i
  change P.equation.operator.mulVec u i - P.equation.source i = 0 at hi
  linarith

end FiniteEllipticCertificate

/-! A finite elliptic calculation may have both an equation residual and a
boundary residual.  Keeping them in one certificate prevents numerical
adapters from reporting a small PDE residual while dropping a boundary error.
The zero-radius theorem below is the only path back to an exact solution. -/

structure FiniteEllipticApproximationCertificate {ι : Type u} [Fintype ι]
    (P : FiniteEllipticProblem ι) (u : ι → ℝ) where
  residualRadius : ℝ
  residual_nonneg : 0 ≤ residualRadius
  residual : EquationResidual (fun v => P.equation.residual v) u residualRadius
  boundary : FiniteBoundaryResidualCertificate P.boundary u

namespace FiniteEllipticApproximationCertificate

variable {ι : Type u} [Fintype ι]

/-- Exact finite solutions construct the joint zero-radius certificate. -/
def exact (P : FiniteEllipticProblem ι) (u : ι → ℝ)
    (h : P.IsSolution u) : FiniteEllipticApproximationCertificate P u :=
  { residualRadius := 0
    residual_nonneg := le_rfl
    residual := P.equation.residual_zero u h.1
    boundary := FiniteBoundaryResidualCertificate.exact P.boundary u h.2 }

/-- Widen equation and boundary budgets without changing the candidate field. -/
def weaken {P : FiniteEllipticProblem ι} {u : ι → ℝ}
    (C : FiniteEllipticApproximationCertificate P u) {δ : ℝ}
    {radius : ι → ℝ}
    (hδ : C.residualRadius ≤ δ)
    (hr : ∀ i, C.boundary.radius i ≤ radius i) :
    FiniteEllipticApproximationCertificate P u :=
  { residualRadius := δ
    residual_nonneg := C.residual_nonneg.trans hδ
    residual := equationResidual_weaken C.residual hδ
    boundary := C.boundary.weaken hr }

/-- Independent equation and boundary error budgets add componentwise. -/
def combine {P : FiniteEllipticProblem ι} {u : ι → ℝ}
    (C₁ C₂ : FiniteEllipticApproximationCertificate P u) :
    FiniteEllipticApproximationCertificate P u :=
  { residualRadius := C₁.residualRadius + C₂.residualRadius
    residual_nonneg := add_nonneg C₁.residual_nonneg C₂.residual_nonneg
    residual := equationResidual_weaken C₁.residual (by
      linarith [C₂.residual_nonneg])
    boundary := C₁.boundary.combine C₂.boundary }

/-- Both zero-radius components recover the exact finite PDE and boundary data. -/
theorem isSolution_of_zero
    {P : FiniteEllipticProblem ι} {u : ι → ℝ}
    (C : FiniteEllipticApproximationCertificate P u)
    (hres : C.residualRadius = 0)
    (hboundary : ∀ i, C.boundary.radius i = 0) : P.IsSolution u := by
  have hboundary' : SatisfiesBoundary P.boundary u :=
    C.boundary.satisfies_of_zero hboundary
  have hresidual : P.equation.residual u = 0 := by
    apply dist_eq_zero.mp
    have hupper := C.residual.bound
    rw [hres] at hupper
    exact le_antisymm hupper dist_nonneg
  refine ⟨?_, hboundary'⟩
  funext i
  have hi := congrFun hresidual i
  change P.equation.operator.mulVec u i = P.equation.source i
  change P.equation.operator.mulVec u i - P.equation.source i = 0 at hi
  linarith

end FiniteEllipticApproximationCertificate

/-! Stability is deliberately an input.  Coercivity alone proves uniqueness,
while a residual-to-solution estimate is the additional numerical fact needed
to turn a residual radius into a quantitative solution error. -/

structure FinitePDEResidualStability {ι : Type u} [Fintype ι]
    (P : FiniteLinearPDE ι) (B : FiniteBoundaryData ι) where
  modulus : ℝ
  modulus_nonneg : 0 ≤ modulus
  bound : ∀ u v, SatisfiesHomogeneousBoundary B (u - v) →
    dist u v ≤ modulus * dist (P.residual u) (P.residual v)

/-! A residual estimate for a non-exact boundary calculation needs a second
modulus.  The boundary error is deliberately the finite `l1` sum over marked
boundary nodes; the stability estimate itself remains an explicit input from
a numerical-analysis argument. -/

noncomputable def boundaryResidualNorm {ι : Type u} [Fintype ι]
    (B : FiniteBoundaryData ι) (u v : ι → ℝ) : ℝ :=
  by
    classical
    exact ∑ i, if B.isBoundary i then |u i - v i| else 0

noncomputable def boundaryResidualBudget {ι : Type u} [Fintype ι]
    (B : FiniteBoundaryData ι) (radius : ι → ℝ) : ℝ :=
  by
    classical
    exact ∑ i, if B.isBoundary i then radius i else 0

theorem boundaryResidualBudget_nonneg {ι : Type u} [Fintype ι]
    (B : FiniteBoundaryData ι) (radius : ι → ℝ)
    (hr : ∀ i, 0 ≤ radius i) :
    0 ≤ boundaryResidualBudget B radius := by
  classical
  unfold boundaryResidualBudget
  apply Finset.sum_nonneg
  intro i hi
  by_cases hbi : B.isBoundary i
  · simp [hbi, hr i]
  · simpa [hbi] using (le_refl (0 : ℝ))

structure FiniteEllipticResidualStability {ι : Type u} [Fintype ι]
    (P : FiniteEllipticProblem ι) where
  equationModulus : ℝ
  boundaryModulus : ℝ
  equationModulus_nonneg : 0 ≤ equationModulus
  boundaryModulus_nonneg : 0 ≤ boundaryModulus
  bound : ∀ u v,
    dist u v ≤
      equationModulus *
          dist (P.equation.residual u) (P.equation.residual v) +
        boundaryModulus * boundaryResidualNorm P.boundary u v

/-! A more structured source of stability.  The caller supplies a candidate
left inverse of the finite operator, proves its left-inverse identity on the
homogeneous Dirichlet subspace, and supplies its Lipschitz modulus.  The
residual-to-solution inequality is then derived by the kernel. -/

structure FinitePDELeftInverseCertificate {ι : Type u} [Fintype ι]
    (P : FiniteLinearPDE ι) (B : FiniteBoundaryData ι) where
  solve : (ι → ℝ) → (ι → ℝ)
  modulus : ℝ
  modulus_nonneg : 0 ≤ modulus
  left_inverse : ∀ w, SatisfiesHomogeneousBoundary B w →
    solve (P.operator.mulVec w) = w
  lipschitz : ∀ r s, dist (solve r) (solve s) ≤ modulus * dist r s

namespace FinitePDELeftInverseCertificate

variable {ι : Type u} [Fintype ι]

def toResidualStability {P : FiniteLinearPDE ι} {B : FiniteBoundaryData ι}
    (I : FinitePDELeftInverseCertificate P B) :
    FinitePDEResidualStability P B := by
  have hzeroBoundary : SatisfiesHomogeneousBoundary B (0 : ι → ℝ) := by
    intro i hi
    simp
  have hzero : I.solve 0 = 0 := by
    have h := I.left_inverse 0 hzeroBoundary
    simpa using h
  refine { modulus := I.modulus, modulus_nonneg := I.modulus_nonneg, bound := ?_ }
  intro u v hhom
  have hA : P.operator.mulVec (u - v) =
      P.residual u - P.residual v := by
    funext i
    simp [FiniteLinearPDE.residual, Matrix.mulVec_sub]
  have hleft : I.solve (P.operator.mulVec (u - v)) = u - v :=
    I.left_inverse (u - v) hhom
  have hdist : dist (u - v) 0 ≤
      I.modulus * dist (P.residual u - P.residual v) 0 := by
    calc
      dist (u - v) 0 =
          dist (I.solve (P.operator.mulVec (u - v))) (I.solve 0) := by
        rw [hleft, hzero]
      _ ≤ I.modulus * dist (P.operator.mulVec (u - v)) 0 :=
        I.lipschitz _ _
      _ = I.modulus * dist (P.residual u - P.residual v) 0 := by
        rw [hA]
  simpa [dist_eq_norm] using hdist

end FinitePDELeftInverseCertificate

theorem FiniteEllipticCertificate.error_to_exact
    {ι : Type u} [Fintype ι]
    {P : FiniteEllipticProblem ι} {u v : ι → ℝ}
    (C : FiniteEllipticCertificate P u)
    (hv : P.IsSolution v)
    (S : FinitePDEResidualStability P.equation P.boundary) :
    ErrorCertificate u v (S.modulus * C.residualRadius) := by
  have hres_v : EquationResidual (fun w => P.equation.residual w) v 0 :=
    P.equation.residual_zero v hv.1
  have hres : ErrorCertificate (P.equation.residual u)
      (P.equation.residual v) C.residualRadius := by
    have h := ErrorCertificate.trans C.residual
      (ErrorCertificate.symmetric hres_v)
    simpa [add_zero] using h
  refine ⟨mul_nonneg S.modulus_nonneg C.residual_nonneg, ?_⟩
  have hbound := S.bound u v
    (sub_satisfies_homogeneous_boundary P.boundary C.boundary hv.2)
  exact hbound.trans
    (mul_le_mul_of_nonneg_left hres.bound S.modulus_nonneg)

theorem FiniteEllipticCertificate.toFiniteApproximation
    {ι : Type u} [Fintype ι]
    {P : FiniteEllipticProblem ι} {u v : ι → ℝ}
    (C : FiniteEllipticCertificate P u)
    (hv : P.IsSolution v)
    (S : FinitePDEResidualStability P.equation P.boundary) :
    FiniteApproximation v u (S.modulus * C.residualRadius) := by
  exact ⟨(C.error_to_exact hv S).symmetric⟩

theorem FiniteEllipticApproximationCertificate.error_to_exact
    {ι : Type u} [Fintype ι]
    {P : FiniteEllipticProblem ι} {u v : ι → ℝ}
    (C : FiniteEllipticApproximationCertificate P u)
    (hv : P.IsSolution v)
    (S : FiniteEllipticResidualStability P) :
    ErrorCertificate u v
      (S.equationModulus * C.residualRadius +
        S.boundaryModulus *
          boundaryResidualBudget P.boundary C.boundary.radius) := by
  classical
  have hres_v : EquationResidual (fun w => P.equation.residual w) v 0 :=
    P.equation.residual_zero v hv.1
  have hres : ErrorCertificate (P.equation.residual u)
      (P.equation.residual v) C.residualRadius := by
    have h := ErrorCertificate.trans C.residual
      (ErrorCertificate.symmetric hres_v)
    simpa [add_zero] using h
  have hboundary :
      boundaryResidualNorm P.boundary u v ≤
        boundaryResidualBudget P.boundary C.boundary.radius := by
    unfold boundaryResidualNorm boundaryResidualBudget
    apply Finset.sum_le_sum
    intro i hi
    by_cases hbi : P.boundary.isBoundary i
    · have huv : |u i - v i| ≤ C.boundary.radius i := by
        have hu := C.boundary.bound i hbi
        simpa [hv.2 i hbi] using hu
      simp only [hbi, ↓reduceIte]
      exact huv
    · simp only [hbi, ↓reduceIte]
      exact le_rfl
  have hbound := S.bound u v
  have hres_bound :
      dist (P.equation.residual u) (P.equation.residual v) ≤
        C.residualRadius := hres.bound
  have hboundary_nonneg :
      0 ≤ boundaryResidualBudget P.boundary C.boundary.radius :=
    boundaryResidualBudget_nonneg P.boundary C.boundary.radius
      C.boundary.radius_nonneg
  have hstable :
    dist u v ≤
        S.equationModulus * C.residualRadius +
          S.boundaryModulus *
            boundaryResidualBudget P.boundary C.boundary.radius := by
    calc
      dist u v ≤
          S.equationModulus *
              dist (P.equation.residual u) (P.equation.residual v) +
            S.boundaryModulus * boundaryResidualNorm P.boundary u v :=
        hbound
      _ ≤ S.equationModulus * C.residualRadius +
          S.boundaryModulus * boundaryResidualNorm P.boundary u v := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hres_bound S.equationModulus_nonneg)
          (le_refl _)
      _ ≤ S.equationModulus * C.residualRadius +
          S.boundaryModulus *
            boundaryResidualBudget P.boundary C.boundary.radius := by
        exact add_le_add
          (le_refl _)
          (mul_le_mul_of_nonneg_left hboundary S.boundaryModulus_nonneg)
  refine ⟨add_nonneg
      (mul_nonneg S.equationModulus_nonneg C.residual_nonneg)
      (mul_nonneg S.boundaryModulus_nonneg hboundary_nonneg), ?_⟩
  exact hstable

theorem FiniteEllipticApproximationCertificate.toFiniteApproximation
    {ι : Type u} [Fintype ι]
    {P : FiniteEllipticProblem ι} {u v : ι → ℝ}
    (C : FiniteEllipticApproximationCertificate P u)
    (hv : P.IsSolution v)
    (S : FiniteEllipticResidualStability P) :
    FiniteApproximation v u
      (S.equationModulus * C.residualRadius +
        S.boundaryModulus *
          boundaryResidualBudget P.boundary C.boundary.radius) := by
  exact ⟨(C.error_to_exact hv S).symmetric⟩

end LeanPhy.Mathematics

/-! Physics-facing adapters for the same finite weak/PDE contracts. -/

namespace LeanPhy

namespace Classical
abbrev FiniteWeakPDEGradient {V E : Type*} [Fintype V] [Fintype E] :=
  Mathematics.FiniteGradient V E
abbrev FinitePoissonResidual {V E : Type*} [Fintype V] [Fintype E] :=
  Mathematics.FiniteGradient.poissonResidual (V := V) (E := E)
end Classical

namespace Condensed
abbrev LatticeStiffnessOperator {V E : Type*} [Fintype V] [Fintype E] :=
  Mathematics.FiniteGradient V E
end Condensed

namespace GaugeTheory
abbrev DiscreteGaugeGradient {V E : Type*} [Fintype V] [Fintype E] :=
  Mathematics.FiniteGradient V E
end GaugeTheory

namespace FieldTheory
abbrev FiniteFieldPDE {ι : Type*} [Fintype ι] :=
  Mathematics.FiniteLinearPDE ι
end FieldTheory

namespace Quantum
abbrev FiniteSchrodingerResidual {ι : Type*} [Fintype ι] :=
  Mathematics.FiniteLinearPDE ι
abbrev FiniteSchrodingerStability {ι : Type*} [Fintype ι]
    (P : Mathematics.FiniteEllipticProblem ι) :=
  Mathematics.FiniteEllipticResidualStability P
end Quantum

namespace Classical
abbrev FiniteEllipticBoundary {ι : Type*} :=
  Mathematics.FiniteBoundaryData ι
abbrev FiniteEllipticBoundaryError {ι : Type*} [Fintype ι]
    (B : Mathematics.FiniteBoundaryData ι) (u : ι → ℝ) :=
  Mathematics.FiniteBoundaryResidualCertificate B u
abbrev FiniteEllipticModel {ι : Type*} [Fintype ι] :=
  Mathematics.FiniteEllipticProblem ι
abbrev FiniteEllipticApproximation {ι : Type*} [Fintype ι]
    (P : Mathematics.FiniteEllipticProblem ι) (u : ι → ℝ) :=
  Mathematics.FiniteEllipticApproximationCertificate P u
abbrev FiniteEllipticResidualStability {ι : Type*} [Fintype ι]
    (P : Mathematics.FiniteEllipticProblem ι) :=
  Mathematics.FiniteEllipticResidualStability P
end Classical

namespace Condensed
abbrev FiniteLatticeEllipticProblem {ι : Type*} [Fintype ι] :=
  Mathematics.FiniteEllipticProblem ι
abbrev FiniteLatticeBoundaryError {ι : Type*} [Fintype ι]
    (B : Mathematics.FiniteBoundaryData ι) (u : ι → ℝ) :=
  Mathematics.FiniteBoundaryResidualCertificate B u
abbrev FiniteLatticeEllipticApproximation {ι : Type*} [Fintype ι]
    (P : Mathematics.FiniteEllipticProblem ι) (u : ι → ℝ) :=
  Mathematics.FiniteEllipticApproximationCertificate P u
abbrev FiniteLatticeEllipticStability {ι : Type*} [Fintype ι]
    (P : Mathematics.FiniteEllipticProblem ι) :=
  Mathematics.FiniteEllipticResidualStability P
end Condensed

namespace FieldTheory
abbrev FiniteModeEllipticProblem {ι : Type*} [Fintype ι] :=
  Mathematics.FiniteEllipticProblem ι
abbrev FiniteModeBoundaryError {ι : Type*} [Fintype ι]
    (B : Mathematics.FiniteBoundaryData ι) (u : ι → ℝ) :=
  Mathematics.FiniteBoundaryResidualCertificate B u
abbrev FiniteModeEllipticApproximation {ι : Type*} [Fintype ι]
    (P : Mathematics.FiniteEllipticProblem ι) (u : ι → ℝ) :=
  Mathematics.FiniteEllipticApproximationCertificate P u
abbrev FiniteModeEllipticStability {ι : Type*} [Fintype ι]
    (P : Mathematics.FiniteEllipticProblem ι) :=
  Mathematics.FiniteEllipticResidualStability P
end FieldTheory

end LeanPhy
