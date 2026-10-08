import LeanPhy.FieldTheory.FermionPolynomial
import LeanPhy.FieldTheory.FiniteFermion

set_option autoImplicit false

/-! An injective assignment embeds a local interaction into any finite mode
system. It need not preserve the mode order: the target expression can be
normalized again in its own order. Colliding labels do not provide a CAR
subfamily and cannot consume an identity proved for independent modes. -/

namespace LeanPhy.FieldTheory.FermionPolynomial

open FermionWord

variable {R ι κ A : Type} [CommRing R]

def renameLetter (g : ι → κ) : Letter ι → Letter κ
  | Sum.inl i => cre (g i)
  | Sum.inr i => ann (g i)

def rename (g : ι → κ) (p : Expression R ι) : Expression R κ :=
  p.map (fun t => (t.1, t.2.map (renameLetter g)))

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Ring A]

def selectCAR (M : MultiModeCAR κ A) (g : ι → κ) (hg : Function.Injective g) :
    MultiModeCAR ι A where
  ann := M.ann ∘ g
  cre := M.cre ∘ g
  car_ann_cre := by intro i j; simpa only [Function.comp_apply, hg.eq_iff] using M.car_ann_cre (g i) (g j)
  car_ann_ann := fun i j => M.car_ann_ann (g i) (g j)
  car_cre_cre := fun i j => M.car_cre_cre (g i) (g j)

theorem eval_rename_word (M : MultiModeCAR κ A) (g : ι → κ) (hg : Function.Injective g)
    (w : Word ι) : FermionWord.eval M (w.map (renameLetter g)) =
      FermionWord.eval (selectCAR M g hg) w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [List.map_cons, FermionWord.eval_cons, ih]
    have ha : generator M (renameLetter g a) = generator (selectCAR M g hg) a := by
      cases a <;> rfl
    rw [ha]

theorem eval_rename [Algebra ℂ A] (f : R →+* ℂ) (M : MultiModeCAR κ A)
    (g : ι → κ) (hg : Function.Injective g) (p : Expression R ι) :
    eval f M (rename g p) = eval f (selectCAR M g hg) p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rcases t with ⟨c, w⟩
    simpa only [rename, List.map_cons, eval_cons, eval_rename_word M g hg] using
      congrArg (fun x => f c • FermionWord.eval (selectCAR M g hg) w + x) ih

omit [DecidableEq ι] in
theorem eq_of_local_certificate [LinearOrder ι] [Algebra ℂ A] [DecidableEq R]
    (f : R →+* ℂ) (M : MultiModeCAR κ A) (g : ι → κ) (hg : Function.Injective g)
    (p q : Expression R ι) (h : compile (sub p q) = []) :
    eval f M (rename g p) = eval f M (rename g q) := by
  rw [eval_rename f M g hg, eval_rename f M g hg]
  exact eq_of_compile_sub_eq_nil f (selectCAR M g hg) p q h

end LeanPhy.FieldTheory.FermionPolynomial
