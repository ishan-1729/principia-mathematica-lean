import PrincipiaMathematica

/-!
# Axiom audit

Checks every declaration in the `PrincipiaMathematica` namespace and fails (with an error) if any of
them depends on an axiom other than Lean's standard `propext`, `Classical.choice` and
`Quot.sound`; in particular, on `sorryAx`. Run with `lake env lean scripts/AxiomsAudit.lean`.
-/

open Lean Elab Command

elab "#audit_axioms" : command => do
  let env ← getEnv
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut n : Nat := 0
  let mut bad : Array (Name × List Name) := #[]
  for (c, _) in env.constants.toList do
    if (`PrincipiaMathematica).isPrefixOf c && !c.isInternal then
      n := n + 1
      let axs ← liftCoreM <| Lean.collectAxioms c
      let extra := axs.toList.filter (fun a => !ok.contains a)
      if !extra.isEmpty then bad := bad.push (c, extra)
  for (c, e) in bad do
    logError m!"{c} depends on {e}"
  logInfo m!"checked {n} declarations; {bad.size} use non-standard axioms"

#audit_axioms
