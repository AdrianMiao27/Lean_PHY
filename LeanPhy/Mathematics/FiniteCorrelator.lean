import LeanPhy.Mathematics.FinitePathIntegral
import Mathlib.Tactic

/-!
# Finite correlation functions

Correlation functions are the observables most often transported through a
finite Euclidean path integral or a blocking map.  This module defines the
two-point and connected two-point functions over a finite configuration
space, and proves their algebraic symmetry, linearity and constant-shift
properties.  It deliberately does not identify a finite correlator with a
continuum distribution or a time-ordered field product.
-/

namespace LeanPhy.Mathematics

open scoped BigOperators

universe u

namespace FinitePathIntegral

variable {ι : Type u} [Fintype ι]

/-! The ordinary and connected two-point functions. -/

noncomputable def correlator (P : FinitePathIntegral ι) (O Q : ι → ℂ) : ℂ :=
  P.expectation (fun i => O i * Q i)

noncomputable def connectedCorrelator (P : FinitePathIntegral ι) (O Q : ι → ℂ) : ℂ :=
  P.correlator O Q - P.expectation O * P.expectation Q

@[simp] theorem correlator_apply (P : FinitePathIntegral ι)
    (O Q : ι → ℂ) :
    P.correlator O Q = P.expectation (fun i => O i * Q i) := rfl

@[simp] theorem connectedCorrelator_apply (P : FinitePathIntegral ι)
    (O Q : ι → ℂ) :
    P.connectedCorrelator O Q =
      P.expectation (fun i => O i * Q i) - P.expectation O * P.expectation Q := rfl

theorem correlator_swap (P : FinitePathIntegral ι) (O Q : ι → ℂ) :
    P.correlator O Q = P.correlator Q O := by
  unfold correlator
  congr 1
  funext i
  ring

theorem connectedCorrelator_swap (P : FinitePathIntegral ι)
    (O Q : ι → ℂ) :
    P.connectedCorrelator O Q = P.connectedCorrelator Q O := by
  unfold connectedCorrelator
  rw [P.correlator_swap O Q]
  ring

theorem correlator_add_left (P : FinitePathIntegral ι)
    (O R Q : ι → ℂ) :
    P.correlator (fun i => O i + R i) Q =
      P.correlator O Q + P.correlator R Q := by
  unfold correlator
  rw [show (fun i => (O i + R i) * Q i) =
      (fun i => O i * Q i + R i * Q i) by
        funext i
        ring]
  exact P.expectation_add _ _

theorem correlator_add_right (P : FinitePathIntegral ι)
    (O Q R : ι → ℂ) :
    P.correlator O (fun i => Q i + R i) =
      P.correlator O Q + P.correlator O R := by
  unfold correlator
  rw [show (fun i => O i * (Q i + R i)) =
      (fun i => O i * Q i + O i * R i) by
        funext i
        ring]
  exact P.expectation_add _ _

theorem correlator_smul_left (P : FinitePathIntegral ι)
    (c : ℂ) (O Q : ι → ℂ) :
    P.correlator (fun i => c * O i) Q = c * P.correlator O Q := by
  unfold correlator
  rw [show (fun i => (c * O i) * Q i) =
      (fun i => c * (O i * Q i)) by
        funext i
        ring]
  exact P.expectation_smul c (fun i => O i * Q i)

theorem correlator_smul_right (P : FinitePathIntegral ι)
    (c : ℂ) (O Q : ι → ℂ) :
    P.correlator O (fun i => c * Q i) = c * P.correlator O Q := by
  unfold correlator
  rw [show (fun i => O i * (c * Q i)) =
      (fun i => c * (O i * Q i)) by
        funext i
        ring]
  exact P.expectation_smul c (fun i => O i * Q i)

theorem connectedCorrelator_add_left (P : FinitePathIntegral ι)
    (O R Q : ι → ℂ) :
    P.connectedCorrelator (fun i => O i + R i) Q =
      P.connectedCorrelator O Q + P.connectedCorrelator R Q := by
  unfold connectedCorrelator
  rw [P.correlator_add_left O R Q]
  rw [P.expectation_add O R]
  ring

theorem connectedCorrelator_add_right (P : FinitePathIntegral ι)
    (O Q R : ι → ℂ) :
    P.connectedCorrelator O (fun i => Q i + R i) =
      P.connectedCorrelator O Q + P.connectedCorrelator O R := by
  rw [P.connectedCorrelator_swap O (fun i => Q i + R i)]
  rw [P.connectedCorrelator_add_left Q R O]
  rw [P.connectedCorrelator_swap Q O, P.connectedCorrelator_swap R O]

theorem connectedCorrelator_smul_left (P : FinitePathIntegral ι)
    (c : ℂ) (O Q : ι → ℂ) :
    P.connectedCorrelator (fun i => c * O i) Q =
      c * P.connectedCorrelator O Q := by
  unfold connectedCorrelator
  rw [P.correlator_smul_left c O Q]
  rw [show P.expectation (fun i => c * O i) = c * P.expectation O by
    exact P.expectation_smul c O]
  ring

theorem connectedCorrelator_smul_right (P : FinitePathIntegral ι)
    (c : ℂ) (O Q : ι → ℂ) :
    P.connectedCorrelator O (fun i => c * Q i) =
      c * P.connectedCorrelator O Q := by
  rw [P.connectedCorrelator_swap O (fun i => c * Q i)]
  rw [P.connectedCorrelator_smul_left c Q O]
  rw [P.connectedCorrelator_swap Q O]

theorem connectedCorrelator_const_left (P : FinitePathIntegral ι)
    (c : ℂ) (Q : ι → ℂ) :
    P.connectedCorrelator (fun _ => c) Q = 0 := by
  unfold connectedCorrelator correlator
  rw [P.expectation_smul c Q, P.expectation_const c]
  ring

theorem connectedCorrelator_const_right (P : FinitePathIntegral ι)
    (O : ι → ℂ) (c : ℂ) :
    P.connectedCorrelator O (fun _ => c) = 0 := by
  rw [P.connectedCorrelator_swap O (fun _ => c)]
  exact P.connectedCorrelator_const_left c O

theorem connectedCorrelator_shift_left (P : FinitePathIntegral ι)
    (O Q : ι → ℂ) (c : ℂ) :
    P.connectedCorrelator (fun i => O i + c) Q =
      P.connectedCorrelator O Q := by
  rw [show (fun i => O i + c) = (fun i => O i + (fun _ => c) i) by rfl]
  rw [P.connectedCorrelator_add_left O (fun _ => c) Q]
  rw [P.connectedCorrelator_const_left c Q, add_zero]

theorem connectedCorrelator_shift_right (P : FinitePathIntegral ι)
    (O Q : ι → ℂ) (c : ℂ) :
    P.connectedCorrelator O (fun i => Q i + c) =
      P.connectedCorrelator O Q := by
  rw [show (fun i => Q i + c) = (fun i => Q i + (fun _ => c) i) by rfl]
  rw [P.connectedCorrelator_add_right O Q (fun _ => c)]
  rw [P.connectedCorrelator_const_right O c, add_zero]

theorem connectedCorrelator_eq_zero_of_factorizes
    (P : FinitePathIntegral ι) (O Q : ι → ℂ)
    (h : P.correlator O Q = P.expectation O * P.expectation Q) :
    P.connectedCorrelator O Q = 0 := by
  unfold connectedCorrelator
  rw [h]
  ring

/-! General finite n-point insertions.  A list is used so that the number of
insertions is explicit in the term; permutation invariance is proved from
commutativity of the scalar coefficient ring. -/

noncomputable def observableProduct (observables : List (ι → ℂ)) : ι → ℂ :=
  fun i => (observables.map (fun O => O i)).prod

noncomputable def multiCorrelator (P : FinitePathIntegral ι)
    (observables : List (ι → ℂ)) : ℂ :=
  P.expectation (observableProduct observables)

@[simp] theorem multiCorrelator_nil (P : FinitePathIntegral ι) :
    P.multiCorrelator [] = 1 := by
  change P.expectation (fun _ => 1) = 1
  exact P.expectation_const 1

theorem observableProduct_perm {xs ys : List (ι → ℂ)}
    (h : xs.Perm ys) :
    observableProduct xs = observableProduct ys := by
  funext i
  exact (h.map (fun O => O i)).prod_eq

theorem multiCorrelator_perm (P : FinitePathIntegral ι)
    {xs ys : List (ι → ℂ)} (h : xs.Perm ys) :
    P.multiCorrelator xs = P.multiCorrelator ys := by
  rw [multiCorrelator, multiCorrelator, observableProduct_perm h]

theorem observableProduct_append (xs ys : List (ι → ℂ)) :
    observableProduct (xs ++ ys) = fun i =>
      observableProduct xs i * observableProduct ys i := by
  funext i
  simp [observableProduct, List.map_append, List.prod_append]

theorem multiCorrelator_append (P : FinitePathIntegral ι)
    (xs ys : List (ι → ℂ)) :
    P.multiCorrelator (xs ++ ys) =
      P.expectation (fun i =>
        observableProduct xs i * observableProduct ys i) := by
  rw [multiCorrelator, observableProduct_append]

theorem multiCorrelator_coarsen {κ : Type*} [Fintype κ]
    (R : FinitePathIntegral.FiniteRGStep ι κ)
    (h : (∑ x, R.fineWeight x) ≠ 0)
    (observables : List (κ → ℂ)) :
    (R.coarsePathIntegral h).multiCorrelator observables =
      (R.finePathIntegral h).multiCorrelator
        (observables.map (fun O => fun x => O (R.coarse x))) := by
  unfold multiCorrelator
  have hp := R.expectation_preserved h (observableProduct observables)
  rw [hp]
  congr 1
  funext x
  simp [observableProduct, List.map_map, Function.comp_def]

end FinitePathIntegral

end LeanPhy.Mathematics

namespace LeanPhy

namespace FieldTheory
noncomputable abbrev FiniteTwoPointFunction {ι : Type*} [Fintype ι] :=
  Mathematics.FinitePathIntegral.correlator (ι := ι)
noncomputable abbrev FiniteConnectedTwoPointFunction {ι : Type*} [Fintype ι] :=
  Mathematics.FinitePathIntegral.connectedCorrelator (ι := ι)
abbrev FiniteWardSymmetry {ι : Type*} [Fintype ι] :=
  Mathematics.FinitePathIntegral.WeightSymmetry (ι := ι)
end FieldTheory

namespace Quantum
noncomputable abbrev FiniteEuclideanCorrelator {ι : Type*} [Fintype ι] :=
  Mathematics.FinitePathIntegral.correlator (ι := ι)
noncomputable abbrev FiniteConnectedCorrelator {ι : Type*} [Fintype ι] :=
  Mathematics.FinitePathIntegral.connectedCorrelator (ι := ι)
abbrev FiniteEuclideanWardSymmetry {ι : Type*} [Fintype ι] :=
  Mathematics.FinitePathIntegral.WeightSymmetry (ι := ι)
end Quantum

namespace Condensed
noncomputable abbrev FiniteLatticeCorrelator {ι : Type*} [Fintype ι] :=
  Mathematics.FinitePathIntegral.correlator (ι := ι)
abbrev FiniteLatticeWardSymmetry {ι : Type*} [Fintype ι] :=
  Mathematics.FinitePathIntegral.WeightSymmetry (ι := ι)
end Condensed

namespace StatMech
noncomputable abbrev FiniteThermalCorrelator {ι : Type*} [Fintype ι] :=
  Mathematics.FinitePathIntegral.correlator (ι := ι)
abbrev FiniteThermalWardSymmetry {ι : Type*} [Fintype ι] :=
  Mathematics.FinitePathIntegral.WeightSymmetry (ι := ι)
end StatMech

end LeanPhy
