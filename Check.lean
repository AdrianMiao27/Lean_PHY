import LeanPhy.CLI

/-!
# `leanphy_check`

The proof terms live in the imported theory packages and are checked while
Lean compiles them.  This executable only renders the resulting research
ledger: assumptions, kernel-checked claims and explicit scope boundaries.
-/

def main (args : List String) : IO Unit :=
  LeanPhy.CLI.runDefault args
