import LeanPhy

/-!
# LeanPhy closed-loop prototype executable

The library is the verifier: compiling this file checks every field of
`verifiedPrototype` with the Lean kernel.  The executable gives a compact
human-readable report for the same finite oscillator, evolution/energy and
Euclidean reflection workflow.
-/

open LeanPhy.Examples.ClosedLoop

def main : IO Unit := do
  let _ := verifiedPrototype
  IO.println "LeanPhy closed-loop prototype"
  IO.println "============================"
  IO.println "[proved] finite oscillator ladder identity"
  IO.println "[proved] shared evolution/energy finite-time bound"
  IO.println "[proved] two-node heat step maximum-principle bounds"
  IO.println "[proved] two-node heat step finite-time mass conservation"
  IO.println "[proved] positive finite path weight and partition"
  IO.println "[proved] reflected weighted Gram positivity"
  IO.println "All six obligations are checked by the Lean kernel."
