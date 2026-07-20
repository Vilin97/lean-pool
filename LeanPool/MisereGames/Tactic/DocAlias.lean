/-
Copyright (c) 2026 Alfie Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies
-/
module

public meta import Lean.Elab.Command
public meta import Batteries.Tactic.Alias

/-!
# The `doc_alias` command

Intended for use within `Literature/` files to give paper-numbered names (e.g.
`theorem_2_1`) the docstrings of the declarations that they alias.
-/

public meta section

open Lean Elab Command

/--
`doc_alias new := target` creates `new` as an alias of `target`, copying
`target`'s docstring: `@[inherit_doc target] alias new := target`.
-/
elab "doc_alias " new:ident " := " target:ident : command => do
  -- Resolve `target` to its full name now, before `new` is declared, so the
  -- `@[inherit_doc]` lookup can't be made ambiguous by `new` itself.
  let fullName ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo target
  let target := mkCIdent fullName
  elabCommand (← `(command| @[inherit_doc $target] alias $new := $target))
