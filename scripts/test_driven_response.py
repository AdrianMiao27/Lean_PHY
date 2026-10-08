#!/usr/bin/env python3
import argparse, subprocess, tempfile, unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
BUILD_ROOT=ROOT
class DrivenResponseTests(unittest.TestCase):
 def invoke(self,*args): return subprocess.run(['lake','exe','leanphy_dynamics_client',*args],cwd=BUILD_ROOT,text=True,capture_output=True,timeout=300)
 def test_project(self):
  r=self.invoke('--project-json'); self.assertEqual(r.returncode,0,r.stderr); self.assertIn('general driven response',r.stdout); self.assertIn('constructed continuous many-body pulse',r.stdout)
 def test_strict_rejects_unfinished_general_ode(self):
  r=self.invoke('--strict'); self.assertNotEqual(r.returncode,0); self.assertIn('remain open',r.stderr)
 def test_public_family_snippet(self):
  src='''import LeanPhy.Quantum.DrivenPulse\nopen LeanPhy.Quantum.TimeDependent\nopen scoped Matrix\nnoncomputable example {ι : Type} [Fintype ι] [DecidableEq ι] (U : Evolution (fun _ : ℝ => (0 : Matrix ι ι ℂ)) 0) (B : Matrix ι ι ℂ) (hB : B.IsHermitian) (f : ℝ → ℝ) (hf : Continuous f) : DrivenFamily (fun _ => (0 : Matrix ι ι ℂ)) (rotatingDrive U B f) 0 := pulseFamily U B hB f hf\n'''
  with tempfile.TemporaryDirectory() as d:
   p=Path(d)/'Check.lean'; p.write_text(src); r=subprocess.run(['lake','env','lean',str(p)],cwd=BUILD_ROOT,text=True,capture_output=True,timeout=300); self.assertEqual(r.returncode,0,r.stdout+r.stderr)
 def test_pauli_rotating_pulse_readout(self):
  src='''import LeanPhy.Examples.DynamicsResearch
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open LeanPhy.Quantum LeanPhy.Quantum.Dynamics LeanPhy.Mathematics
open LeanPhy.Examples.DynamicsResearch
open LeanPhy.Quantum.TimeDependent
open scoped Matrix Matrix.Norms.Operator
set_option maxHeartbeats 8000000
noncomputable def U0 : Evolution (fun _ : ℝ => (0 : Matrix (Fin 2) (Fin 2) ℂ)) (-1) :=
  autonomous 0 (by simp) (-1)
theorem hX : pauliX.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.conjTranspose_apply]
def f : ℝ → ℝ := fun t => t ^ 2
theorem hf : Continuous f := by unfold f; fun_prop
example : pulseArea f (-1) 1 = (2 / 3 : ℝ) := by
  norm_num [pulseArea, integral_pow, f]
theorem hObs : U0.observable pauliY 1 = pauliY := by
  exact autonomous_observable_of_commute 0 pauliY (by simp) (Commute.zero_left _) (-1) 1
example : Complex.I * commutatorResponse initialState.rho pauliX
    (U0.observable pauliY 1) = (-2 : ℂ) := by
  rw [hObs]
  norm_num [commutatorResponse, initialState, diagonalDensity, realDiagonal,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, pauliX, pauliY,
    Complex.I_mul_I, mul_add]
example : (∫ s in (-1 : ℝ)..1,
    (pulseFamily U0 pauliX hX f hf).kernel initialState.rho pauliY 1 s)
    = (-4 / 3 : ℂ) := by
  have h := pulseFamily_response (U := U0) (B := pauliX) hX f hf
    initialState.rho pauliY 1
  rw [h]
  rw [hObs]
  norm_num [pulseArea, integral_pow, f, commutatorResponse, initialState,
    diagonalDensity, realDiagonal, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
    pauliX, pauliY, Complex.I_mul_I]
  rw [mul_add, Complex.I_mul_I]
  norm_num
'''
  with tempfile.TemporaryDirectory() as d:
   p=Path(d)/'Check.lean'; p.write_text(src); r=subprocess.run(['lake','env','lean',str(p)],cwd=BUILD_ROOT,text=True,capture_output=True,timeout=300); self.assertEqual(r.returncode,0,r.stdout+r.stderr)
if __name__=='__main__':
 ap=argparse.ArgumentParser(add_help=False); ap.add_argument('--build-root',type=Path,default=ROOT); args,rest=ap.parse_known_args(); BUILD_ROOT=args.build_root; unittest.main(argv=[__file__]+rest)
