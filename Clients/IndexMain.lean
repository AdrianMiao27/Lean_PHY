import LeanPhy
import LeanPhy.Library.Index
import LeanPhy.Examples.ClientProject

/- The full library import closure is indexed at build time. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
physics_index leanphyDeclarations

def main (args : List String) : IO Unit :=
  LeanPhy.Library.runIndex leanphyDeclarations args
