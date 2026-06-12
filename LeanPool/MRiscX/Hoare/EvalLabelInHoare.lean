/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import LeanPool.MRiscX.AbstractSyntax.AbstractSyntax
import LeanPool.MRiscX.Elab.HandleExpr

/-!
# EvalLabelInHoare

This module provides label resolution inside MRiscX Hoare syntax.
-/
open Lean Elab

/-
This file contains a logic to replace the labelname with the actual pc index
within a hoare triple
-/
/-- The total number of nodes in a syntax tree, an upper bound on its depth. -/
private def syntaxSize : Syntax → Nat
  | .node _ _ args => 1 + args.foldl (fun acc s => acc + syntaxSize s) 0
  | _ => 1

/--
Auxiliary function for expanding the `labels[ident]`, similar to `expandCDot?`.
The `fuel` argument bounds the recursion depth over the (finite) syntax tree.
-/
private def replaceLabelsGo (fuel : Nat) :
    Syntax → StateT (LabelMap) TermElabM Syntax
  | _stx@`($s:str) => do
    let str := s.getString
    let mapEntryAtStr := (←get).get str
    match mapEntryAtStr with
    | some i => do
      return Syntax.mkNumLit (toString i)
    | none => throwError s!"No label found with name {str}"
  | stx => match fuel, stx with
    | fuel + 1, .node _ k args => do
      let args ← args.mapM (replaceLabelsGo fuel)
      return .node (.fromRef stx (canonical := true)) k args
    | _, stx => pure stx

/-- Replace each label name in `stx` with the program-counter index it maps to. -/
def replaceLabels (stx : Term) (labels : LabelMap) : TermElabM Syntax := do
  withFreshMacroScope do
    let (newStx, _) ← (replaceLabelsGo (syntaxSize stx) stx).run labels
    return newStx

/-- Resolve labels in `stx` using the label map embedded in the code expression `e`. -/
def replaceLabelsWithCodeExpr (stx : Term) (e : Expr) : TermElabM Syntax := do
  if e.isFVar then
    return stx
  let labels ← getLabelMapFromCodeExpr e
  return ←replaceLabels stx labels

/-- Resolve labels in `stx` using the code referred to by identifier `i`. -/
def replaceLabelsWithIdent (stx : Term) (i : Ident) : TermElabM Syntax := do
  let e ← Term.elabTerm i none
  replaceLabelsWithCodeExpr stx e
