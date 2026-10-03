import LeanPhy.Surface.DiracNotation
import LeanPhy.Surface.IndexCalculus
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Physics-facing tactic facade

The first release exposes existing mathlib automation through stable names used
by the physics DSL, and adds a few tactics whose steps come straight from a
hand derivation.  Domain-specific elaborators can later replace the wrappers
without changing user proofs.

The added tactics:

- `commutator_nf`: expand commutators and anticommutators via additivity and
  the Leibniz rule, then close the resulting ring identity;
- `dirac_unfold`: reveal the Dirac-notation surface wrappers (bracket, matrix
  element, bra) as their core definitions, so the core lemmas apply;
- `index_unfold`: reveal the Kronecker delta and Levi-Civita symbol.
-/

namespace LeanPhy

open LeanPhy.Quantum
open LeanPhy.IndexCalculus

syntax (name := physicsRing) "physics_ring" : tactic
macro_rules | `(tactic| physics_ring) => `(tactic| ring)

syntax (name := physicsLinear) "physics_linear" : tactic
macro_rules | `(tactic| physics_linear) => `(tactic| linarith)

syntax (name := physicsNoncommRing) "physics_noncomm_ring" : tactic
macro_rules | `(tactic| physics_noncomm_ring) => `(tactic| noncomm_ring)

syntax (name := physicsNormNum) "physics_norm_num" : tactic
macro_rules | `(tactic| physics_norm_num) => `(tactic| norm_num)

/-- Normalise a commutator expression: expand by additivity and the Leibniz
rule, drop self-commutators, and finish with additive normalisation. -/
syntax (name := commutatorNf) "commutator_nf" : tactic
macro_rules
  | `(tactic| commutator_nf) => `(tactic|
      (simp only [commutator_add_left, commutator_add_right, commutator_mul_left,
        commutator_mul_right, commutator_self, anticommutator, sub_self, add_zero, zero_add,
        mul_zero, zero_mul, sub_zero] <;> try abel))

/-- Reveal the Dirac-notation surface wrappers as their core definitions. -/
syntax (name := diracUnfold) "dirac_unfold" : tactic
macro_rules
  | `(tactic| dirac_unfold) => `(tactic|
      (simp only [bracket, bracketOp, braOf, braMulOp]))

/-- Reveal the index-calculus surface definitions (delta, epsilon). -/
syntax (name := indexUnfold) "index_unfold" : tactic
macro_rules
  | `(tactic| index_unfold) => `(tactic| (simp only [delta, epsilon]))

/-!
## The compositional physics tactic

The small tactics above are useful when a derivation is being debugged step by
step.  Research files also need one stable entry point that can be used in a
normal `by` proof without making the user know which algebraic layer owns the
next rewrite.  `physics` is that entry point.  It is deliberately a tactic
*macro*, rather than a second proof engine: every branch expands to ordinary
Lean/mathlib tactics and the final `done` requires that the kernel-facing goal
really closed.  In particular, a successful `simp` that leaves an obligation
behind cannot be reported as a successful physics proof.

The order is intentional.  Surface notation is exposed first, commutators are
normalised next, and then the usual commutative/non-commutative arithmetic
solvers are tried.  The final branch gives a domain-oriented message that
points users towards the three most common causes of a failed physical
derivation: a missing hypothesis, an index/dimension mismatch, or an algebraic
normalisation that has not yet been stated as a lemma.
-/

syntax (name := physics) "physics" : tactic
macro_rules
  | `(tactic| physics) => `(tactic|
      first
      | (abel <;> done)
      | (dirac_unfold <;> index_unfold <;> commutator_nf <;>
          simp <;> try abel <;> try ring <;> try linarith <;>
          try noncomm_ring <;> done)
      | (commutator_nf <;> try simp <;> try abel <;> try ring <;>
          try linarith <;> try noncomm_ring <;> done)
      | (dirac_unfold <;> try simp <;> try ring <;> try linarith <;> done)
      | (index_unfold <;> try simp <;> try ring <;> try linarith <;> done)
      | (simp only [sub_eq_add_neg, neg_smul, neg_neg] <;>
          try rw [← add_smul] <;> try module <;> try congr 1 <;>
          try ring <;> done)
      | (module <;> done)
      | (norm_num <;> done)
      | (positivity <;> done)
      | (field_simp <;> try ring <;> done)
      | (ring_nf <;> done)
      | (ring <;> done)
      | (linarith <;> done)
      | (noncomm_ring <;> done)
      | fail "physics 无法闭合目标：请检查假设、量纲/指标与对易子规范，或先添加缺失的领域引理")

/-!
`physics_search` is the discovery-oriented entry point.  `exact?` performs
Lean's normal environment search and therefore suggests an ordinary theorem
name that can be kept in a research file.  Falling back to `physics` makes the
same command useful after a surface notation or commutator has been expanded.
Both branches still end in `done`; a suggestion or a partially simplified
goal is never reported as a successful proof.
-/

syntax (name := physicsSearch) "physics_search" : tactic
macro_rules
  | `(tactic| physics_search) => `(tactic|
      first
      | (assumption <;> done)
      | (exact? <;> done)
      | (physics <;> done)
      | fail "physics_search 未找到可复用的已证明引理：请检查假设、导入相应 Entry profile，或先补充领域引理")

end LeanPhy
