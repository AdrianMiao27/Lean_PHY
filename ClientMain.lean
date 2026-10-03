import LeanPhy.Examples.ClientProject

/- A tiny executable wrapper that stands in for a downstream repository's
   `Main.lean`.  The actual project data and CLI call live in the client
   module, so this file contains no catalogue-specific LeanPhy code. -/

def main (args : List String) : IO Unit :=
  LeanPhy.Examples.ClientProject.main args
