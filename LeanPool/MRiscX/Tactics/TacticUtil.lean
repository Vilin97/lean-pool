/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import Lean

/-!
# TacticUtil

This module provides small utilities shared by the MRiscX tactics.
-/
open Lean Meta

/-- Find the type of the local hypothesis named `n` in `ctx`, if present. -/
def findHypTypeM? (ctx : LocalContext) (n : Name) : MetaM (Option Expr) :=
  ctx.findDeclM? (fun decl =>
    if decl.userName == n then
      return some decl.type
    else
      return none)

/-- Find the type of the local hypothesis named `n` in `ctx`, throwing if absent. -/
def findHypTypeM (ctx : LocalContext) (n : Name): MetaM (Expr) := do
  let some res ← (findHypTypeM? ctx n)
      | throwError s!"Could not find {n} in hypothesis"
  return res
