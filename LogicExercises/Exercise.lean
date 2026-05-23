module

public meta import Lean.Elab.Term.TermElabM

open Lean Elab Term Meta

public section

/--
`exercise` is a placeholder for worksheet omissions.

In proof and term positions it behaves like `sorry` at the expected type. In type
positions where Lean has not fixed the universe yet, such as an omitted constructor
premise, it defaults to a proposition-shaped hole.
-/
elab "exercise" : term <= expectedType => do
  let expectedType ← instantiateMVars expectedType
  match expectedType with
  | .sort u =>
      if u.hasMVar then
        mkSorry (.sort .zero) true
      else
        mkSorry expectedType true
  | _ =>
      mkSorry expectedType true

syntax (name := exerciseTac) "exercise" : tactic

macro_rules
  | `(tactic| exercise) => `(tactic| sorry)
