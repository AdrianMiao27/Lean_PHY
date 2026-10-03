import LeanPhy
import Lean.Util.CollectAxioms

open Lean Elab Command

elab "audit_all_leanphy" : command => do
  let env ← getEnv
  let mut bad : Array (Name × Array Name) := #[]
  let mut custom : Array Name := #[]
  for (name, info) in env.constants.map₂ do
    if name.toString.startsWith "LeanPhy." then
      match info with
      | .axiomInfo _ => custom := custom.push name
      | _ =>
        let axs ← liftCoreM <| Lean.collectAxioms name
        let forbidden := axs.filter (fun a =>
          a == ``sorryAx || a == ``Lean.ofReduceBool)
        if !forbidden.isEmpty then bad := bad.push (name, forbidden)
  if !custom.isEmpty then
    throwError m!"LeanPhy declares custom axioms: {custom}"
  if !bad.isEmpty then
    throwError m!"LeanPhy has forbidden axiom dependencies: {bad}"
  logInfo m!"LeanPhy full axiom audit passed."

audit_all_leanphy
