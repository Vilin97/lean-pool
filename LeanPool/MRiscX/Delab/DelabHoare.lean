/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import LeanPool.MRiscX.Hoare.HoareCore
import LeanPool.MRiscX.Parser.HoareSyntax
import LeanPool.MRiscX.Elab.HandleNumOrIdent

/-!
# DelabHoare

This module provides delaborators for MRiscX Hoare triples.
-/
open Lean PrettyPrinter SubExpr Expr Nat Elab

/-
This file contains the delaboration of the hoare notation.

-/

-- identify Expr and initialize delaboration of MState functions
open Delaborator SubExpr in
def annotateStateFns (e : Expr) :  Expr :=
  e.replace fun e =>
    if (e.isAppOfArity ``MState.terminated 1 || e.isAppOfArity ``MState.getRegisterAt 2
      || e.isAppOfArity ``MState.getMemoryAt 2
      || e.isAppOfArity ``MState.pc 1 || e.isAppOfArity ``MState.getLabelAt 2)
    then
      mkAnnotation `hoareTripleDelabKey e
    else
      none


def termToIdent? (t : Term) : Option (TSyntax `ident) :=
  if t.raw.isIdent then some ⟨t.raw⟩ else none


def extractStringFromTerm? (t : Term) : Option (TSyntax `ident) :=
  if let some s := t.raw.isStrLit? then some (mkIdent (Name.mkSimple s)) else none

def termToMriscx_syntax? (t : Term) : Option (TSyntax `mriscx_syntax) :=
  if t.raw.getKind == `mriscx_syntaxMriscx__End
   then some ⟨t.raw⟩
  else none

def hoare_termToTerm (t : TSyntax `hoare_term) : Delaborator.DelabM Term :=
  return ⟨t.raw⟩


/-
Delaborate Expr of abstract syntax back to Term
-/
open Delaborator SubExpr in
@[delab mdata.hoareTripleDelabKey]
def stateFnsDelab : Delab := whenNotPPOption getPPExplicit <| withMDataExpr do
  if (← getExpr).isAppOfArity ``MState.terminated 1 then
    `(⸨terminated⸩)
  else if (← getExpr).isAppOfArity ``MState.getRegisterAt 2 then
    let n ← withAppArg delab
    let newN := parseTermToMriscxNumOrIdent n
    `(x[$newN])
  else if (← getExpr).isAppOfArity ``MState.getMemoryAt 2 then
    whenPPOption getPPNotation <| whenNotPPOption getPPExplicit <| withOverApp 2 do
      withNaryArg 1 do
        let e := annotateStateFns (← getExpr)
        let n ← withTheReader SubExpr (fun s => { s with expr := e }) do
          delab
        `(mem[$n])
  else if (← getExpr).isAppOfArity ``MState.pc 1 then
    `(⸨pc⸩)
  else if (← getExpr).isAppOfArity ``MState.getLabelAt 2 then
    let n ← withAppArg delab
    match extractStringFromTerm? n with
      | some id => `(labels[$id])
      | none => do throwError s!"fatal error, {n} is not a string"
  else
    do throwError "This Expression is not known for delaboration"


def hasNestedLambdaBody (e : Expr) : Bool :=
  if e.isLambda then
    e.bindingBody!.getAppFn.isLambda
  else
    false

/-
Delaborate Assertions, considering nested lambda functions for applying e.G.
Axiom of assignment (⦃⦃x[r] = v⦄ ⟦x[r] ← v ; pc++⟧⦄)
-/
open Delaborator SubExpr in
def mkAssertionAtN
    (n : Nat)
    (stName : Name)
    (withAnnotatedBody : Delab → Delab)
    : DelabM Term := do
    let synOld ← withNaryArg n <| do
      let e ← getExpr
      if e.isLambda then
        if e.bindingBody!.getAppFn.isLambda then
          withBindingBody' stName pure fun _ => do
            withAppFn <|(withAnnotatedBody (Lean.PrettyPrinter.Delaborator.delab))
        else
          withAnnotatedBody delab
      else
        delab
    let stateSyn? : Option Term ← withNaryArg n <| do
      if hasNestedLambdaBody (←getExpr) then
        some <$> withBindingBody' stName pure (fun _ =>
          withNaryArg 0 delab)
      else
        return none
    match stateSyn? with
    | none   => pure synOld
    | some t => `(⦃$synOld⦄ ⟦$t⟧)

/-
Delaboration of Hoare-Triples.
For more information about this code, have look into the
[Zulipchat discussion](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/.E2.9C.94.20Delaboration.20of.20function).
Thanks to Kyle Miller for his input!
-/
open Delaborator SubExpr in
@[app_delab hoare_triple_up]
def hoareTripleDelab : Delab :=
  whenPPOption getPPNotation <| whenNotPPOption getPPExplicit <| withOverApp 6 do
    let stName ← Core.mkFreshUserName `st
    let withAnnotatedBody (d : Delab) : Delab :=
      withBindingBody' stName pure fun _ => do
        let e := annotateStateFns (← getExpr)
        withTheReader SubExpr (fun s => { s with expr := e }) d
    let preSyn ← mkAssertionAtN 0 stName withAnnotatedBody
    let postSyn ← mkAssertionAtN 1 stName withAnnotatedBody
    let lSyn ← withNaryArg 2 <| delab
    let L_wSyn ← withNaryArg 3 <| delab
    let L_bSyn ← withNaryArg 4 <| delab
    let cSyn ← withNaryArg 5 <| delab
    match termToMriscx_syntax? cSyn with
    | none => pure ()
    | some c =>
      return ←hoare_termToTerm (←`(hoare_term | $c:mriscx_syntax
        ⦃$preSyn⦄ $lSyn ↦ ⟨$L_wSyn | $L_bSyn⟩ ⦃$postSyn⦄))
    match termToIdent? cSyn with
    | none => pure ()
    | some c => return ←hoare_termToTerm (←`(hoare_term | $c:ident
        ⦃$preSyn⦄ $lSyn ↦ ⟨$L_wSyn | $L_bSyn⟩ ⦃$postSyn⦄))
    match extractStringFromTerm? cSyn with
    | none => pure ()
    | some c => return ←hoare_termToTerm (←`(hoare_term | $c:ident
        ⦃$preSyn⦄ $lSyn ↦ ⟨$L_wSyn | $L_bSyn⟩ ⦃$postSyn⦄))
    logInfo s!"A problem occurred while delaborating {cSyn} was not of Expr Type ident
    or mriscx_syntax but it has type {cSyn.raw.getKind}, falling back to delab without code"
    hoare_termToTerm (←`(hoare_term | $(mkIdent `c?):ident
    ⦃$preSyn⦄ $lSyn ↦ ⟨$L_wSyn | $L_bSyn⟩ ⦃$postSyn⦄))




def isOnlyStateIdent (s : TSyntax `term) : Bool :=
  match s with
  | `(st) => true
  | _ => false


@[app_unexpander MState.incPc]
def IncPcUnexpander : Unexpander
  | `($_ $s) => do
    if isOnlyStateIdent s then
      `(hoare_assignment_chain | pc++)
    else
      `(hoare_assignment_chain | pc++ ; $s:term)
  | _ => throw Unit.unit


@[app_unexpander MState.addRegister]
def AddRegUnexpander : Unexpander
  | `($_ $s $rTerm:term $vTerm:term) => do
    let r ← numOrIdentToSyntax rTerm
    if isOnlyStateIdent s then
      `(hoare_assignment_chain | x[$r] ← $vTerm)
    else
      `(hoare_assignment_chain | x[$r] ← $vTerm ; $s:term)
  | _ => throw Unit.unit

@[app_unexpander MState.addMemory]
def AddMemUnexpander : Unexpander
  | `($_ $s $rTerm:term $vTerm:term) => do
    if isOnlyStateIdent s then
      `(hoare_assignment_chain | mem[$rTerm] ← $vTerm)
    else
      `(hoare_assignment_chain | mem[$rTerm] ← $vTerm ; $s:term)
  | _ => throw Unit.unit
