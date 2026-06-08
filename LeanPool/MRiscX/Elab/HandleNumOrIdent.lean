/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import LeanPool.MRiscX.Parser.AssemblySyntax
import Lean

/-!
# HandleNumOrIdent

This module provides elaboration helpers for numeric/identifier operands.
-/
open Nat Lean PrettyPrinter Expr Meta Elab

/-
Next, we introduce utility functions to streamline the conversion of syntax into an Expr.
-/
/-- Build the `Expr` `UInt64.ofNat n` from a `Nat`. -/
def mkUIntOfNat (n:Nat):= Expr.app (.const `UInt64.ofNat []) (mkNatLit n)

/-- Build the `Expr` of the numeral denoting the `UInt64` `n`. -/
def mkUintOfNat (n:UInt64):= Expr.app (.const `OfNat.ofNat []) (mkNatLit n.toNat)


/-- Build the `Expr` of the `UInt64` literal `n`. -/
def mkUInt64Lit (n : UInt64) : Expr :=
  mkApp3
    (mkConst ``OfNat.ofNat [Level.zero])
    (mkConst ``UInt64)
    (mkRawNatLit n.toNat)
    (mkApp (mkConst ``UInt64.instOfNat) (mkRawNatLit n.toNat))

/-- Elaborate a `num`-or-`ident` syntax node into the term it denotes. -/
def parseMriscxNumOrIdentToTerm (s : Syntax) : TermElabM Term := do
  match s with
  | `(mriscxNumOrIdent | $a:num) =>
      return a
  | `(mriscxNumOrIdent | $a:ident) => do
      if let some decl := (← getLCtx).findFromUserName? a.getId then
        if ← isDefEq decl.type (mkConst ``UInt64) then
          return a
        else
          throwError "Expected type UInt64 for identifier"
      else
        throwError s!"Identifier {a} not found in context"
  | _ => throwError "Unexpected syntax"

/-- Reinterpret a term as `mriscxNumOrIdent` syntax. -/
def parseTermToMriscxNumOrIdent (s : TSyntax `term) : TSyntax `mriscxNumOrIdent :=
  match s with
  | `(mriscxNumOrIdent | $a:mriscxNumOrIdent) =>
      a
  -- | _ => throwError "Unexpected syntax"

/-
A flexible approach that allows us to write general statements
and theorems without depending on specific numerical literals is required. Simultaneously,
we want the ability to execute instructions with actual values. Therefore, we
need to support both abstract reasoning and concrete computation.

To achieve this, we use -/

/-- A function that first checks whether the given `num` or
`ident` is a numeric literal. If so, it returns the corresponding `UInt64` expression.
If not, it checks if the variable name has been declared as a `UInt64` in the current
context and, if found, returns it as an expression. If neither condition is met,
the function fails.
To be able to check if the variable has already been declared, the MetaM
Monad is required. For this reason, we return a TermElabM Expr, which has to be
lifted afterwards.
-/
def parseMriscxNumOrIdent (s : Syntax) : TermElabM Expr := do
  match s with
  | `(mriscxNumOrIdent | $a:num) =>
      return mkUIntOfNat a.getNat
  | `(mriscxNumOrIdent | $a:ident) => do
      if let some decl := (← getLCtx).findFromUserName? a.getId then
        if ← isDefEq decl.type (mkConst ``UInt64) then
          return decl.toExpr
        else
          throwError "Expected type UInt64 for identifier"
      else
        throwError s!"Identifier {a} not found in context"
  | _ => throwError "Unexpected syntax"

/--
Apply `parseMriscxNumOrIdent` on all elements inside an array
-/
def parseMriscxNumOrIdentArray (a : Array Syntax): (TermElabM (Array Expr)) := do
  let mut result := #[]
  for syn in a do
    result := result.push (←parseMriscxNumOrIdent syn)

  return result

/-
Since we need a similar functionality for the names of the labels, we
require the following functions, which check if the given ident is a
variable in the local context. If it is, the functions returns ident
as a variable and if it is not, they return ident as a string respectively.
-/
/-- Elaborate a label identifier into its string `Expr`, honouring the leading-dot form. -/
def parseLabelname (s : TSyntax `ident) (withDot : Bool) : TermElabM Expr := do
  if let some decl := (← getLCtx).findFromUserName? s.getId then
      return decl.toExpr
  else if withDot then
    return mkStrLit ("." ++ s.getId.getString!)
  return mkStrLit s.getId.getString!



/-- Turn a label identifier into the term naming its target, honouring the leading-dot form. -/
def checkIfVariableToTerm (t : TSyntax `ident) (identWithDot : Bool) : TermElabM Term := do
  if let some _ := (← getLCtx).findFromUserName? t.getId then
    return t
  else if identWithDot then
    return (← `(term| $(quote ("." ++ t.getId.getString!))))

  return (← `(term| $(quote t.getId.getString!)))

/-- Unexpand a term back into `mriscxNumOrIdent` surface syntax. -/
def numOrIdentToSyntax (t:TSyntax `term) : UnexpandM (TSyntax `mriscxNumOrIdent) := do
  match t with
  | `(UInt64.ofNat $n:num) => return ←`(mriscxNumOrIdent | $n:num)
  | `($n:num) =>
    return ←`(mriscxNumOrIdent | $n:num)
  | `($i:ident) => return ←`(mriscxNumOrIdent | $i:ident)
  | _ => throw ()
