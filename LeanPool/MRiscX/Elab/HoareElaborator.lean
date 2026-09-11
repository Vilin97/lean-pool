/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
module

public import LeanPool.MRiscX.Elab.CodeElaborator
public import LeanPool.MRiscX.Hoare.EvalLabelInHoare
public import LeanPool.MRiscX.Hoare.HoareAssignmentElab
public import LeanPool.MRiscX.Parser.HoareSyntax
public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual
import LeanPool.MRiscX.Hoare.HoareCore
import Mathlib.Tactic.Finiteness.Attr

/-!
# HoareElaborator

This module provides the elaborator for MRiscX Hoare-triple syntax.
-/

public meta section


open Lean Meta Elab

/-
This file contains the definition of the Hoare Notation and elaboration.
The Syntax of the hoare triples is as close as possible to the notation from
the paper of lundberg et al.. Some exceptions had to be made since "[]" are already
widely known as lists.
-/

/-- Notation `a₁ ∧∧ a₂` for the conjunction `Assertion.And a₁ a₂` of two assertions. -/
macro  a₁:term " ∧∧ " a₂:term : term => do
  `(Assertion.And $a₁ $a₂)

/-- Notation `∼a` for the negation `Assertion.Not a` of an assertion. -/
macro "∼" a:ident : term =>
  `(Assertion.Not $a)

/-- Preprocess a parsed Hoare condition, expanding assignment chains and binding
the implicit state identifier `st`. -/
def processHoareTerm (stx : Term) : TermElabM Syntax := do
  withFreshMacroScope do
    let mut newStx ← (go stx)
    return newStx
where
  /-- Differentiate between a Hoare assignment and an ordinary term in a
  pre- or post-condition. -/
  go : Syntax → TermElabM Syntax
  | _stx@`(hoareAssignmentTerm | ⟦$h:hoareAssignmentChain⟧) => do
    return ←generateHoareAssignmentSyntax h
  | _stx@`($t:term) => do
    let mut newStx ← replaceKeywords t (←`($(mkIdent `st)))
    return newStx



/-- Elaborate a Hoare condition into the `MState → _` predicate it denotes. -/
def elabHoareTerm (stx : Term) : TermElabM (Term) := do
  let newStx ← processHoareTerm stx
  let stIdent := mkIdent `st
  return ←`(fun $stIdent : MState => ($(⟨newStx⟩)))


/-- Notation `⦃t⦄` elaborating a Hoare condition into its state predicate. -/
elab "⦃" t:term "⦄" : term => do
  let newTOpt ← elabHoareTerm t
  return ← Lean.Elab.Term.elabTerm (←`($newTOpt)) (some (.const ``String []))


/--
Some utility function which casts an `Array TSyntax mriscxLabel` to `TSyntax term`
-/
def mriscxSyntaxToTerm (stx : Array (TSyntax `mriscxLabel)) : TermElabM (TSyntax `term) := do
  let newStx : (TSyntax `term) := ←`(mriscx
                                      $stx*
                                     end)
  return newStx

/--
Some utility function which casts `TSyntax mriscxLabel` to `TSyntax term`
-/
def mriscxSpecToTerm (stx : (TSyntax `mriscxInstr)) : TermElabM (TSyntax `term) := do
  let newStx : (TSyntax `term) ←`(⟪$stx⟫)
  return ←`($newStx)


/--
Hoare-triples for specifications with only one instruction
-/
elab "hoare" syn:mriscxSpec linebreak
      "⦃" P:term "⦄" l:term "↦" "⟨" L_w:term "|" L_b:term "⟩" "⦃" Q:term "⦄"
      "end" : term => do
  let translatedP ← elabHoareTerm P
  let translatedQ ← elabHoareTerm Q
  match syn with
  | `(mriscxSpec | ⟪$i:mriscxInstr⟫) => do
    let synAsTerm ← mriscxSpecToTerm i
    return ←Lean.Elab.Term.elabTerm
        (←`($(mkIdent ``hoare_triple_up_1) $translatedP $translatedQ $l $L_w $L_b $synAsTerm)) none
  | _ => throwError "Expected syntax of type mriscxSpec with ⟪⟫ braces!"


/--
Regular Hoare-triple with concrete MRiscX syntax before the actual triple
-/
elab t:hoareTerm : term => do
  match t with
  | `(hoareTerm | $syn:mriscxSyntax
    ⦃ $P:term ⦄ $l:term ↦ ⟨ $L_w:term | $L_b:term ⟩ ⦃ $Q:term ⦄) =>
    let translatedP ← elabHoareTerm P
    let translatedQ ← elabHoareTerm Q
    let labels ← getLabelMapFromSyntax syn
    let evaluatedLw := ⟨(←replaceLabels L_w labels)⟩
    let evaluatedLb := ⟨(←replaceLabels L_b labels)⟩
    let evaluatedL := ⟨(←replaceLabels l labels)⟩
    match syn with
    | `(mriscxSyntax | mriscx
      $labelsSyn:mriscxLabel*
      end) => do
      let mriscxSyntaxAsTerm ← mriscxSyntaxToTerm labelsSyn
      return ←Lean.Elab.Term.elabTerm (←`($(mkIdent ``hoareTripleUp) $translatedP $translatedQ
        $evaluatedL $evaluatedLw $evaluatedLb $mriscxSyntaxAsTerm)) none
    | _ => throwError "expected mriscx syntax while elaborating hoare term"
  | _ => throwError "failure"

/--
Define the code beforehand, does not support the usage of variables
-/
elab id:ident withPosition(linebreak ppDedent(ppLine))
  "⦃" P:term "⦄" l:term "↦" "⟨" L_w:term "|" L_b:term "⟩" "⦃" Q:term "⦄"
   : term => do
  let translatedP ← elabHoareTerm P
  let translatedQ ← elabHoareTerm Q
  let evaluatedLw := ⟨(←replaceLabelsWithIdent L_w id)⟩
  let evaluatedLb := ⟨(←replaceLabelsWithIdent L_b id)⟩
  let evaluatedL := ⟨(←replaceLabelsWithIdent l id)⟩
  return ←Lean.Elab.Term.elabTerm
      (←`($(mkIdent ``hoareTripleUp) $translatedP $translatedQ $evaluatedL $evaluatedLw
          $evaluatedLb $id)) none


/--
To define the code beforehand with some some variables.
-/
elab codeTerm:term withPosition(linebreak ppDedent(ppLine))
    "⦃" P:term "⦄" l:term "↦" "⟨" L_w:term "|" L_b:term "⟩" "⦃" Q:term "⦄"
  : term => do
  let e ← Lean.Elab.Term.elabTerm codeTerm none
  let ty ← Lean.Meta.inferType e
  let ty ← Meta.whnf ty
  if (ty.isAppOf `Code) then
    let translatedP ← elabHoareTerm P
    let translatedQ ← elabHoareTerm Q
    let evaluatedLw := ⟨(←replaceLabelsWithCodeExpr L_w e)⟩
    let evaluatedLb := ⟨(←replaceLabelsWithCodeExpr L_b e)⟩
    let evaluatedL := ⟨(←replaceLabelsWithCodeExpr l e)⟩
    return ←Lean.Elab.Term.elabTerm
        (←`($(mkIdent ``hoareTripleUp) $translatedP $translatedQ $evaluatedL $evaluatedLw
            $evaluatedLb $codeTerm)) none
  else throwError  m!"Application type mismatch: The argument
  {codeTerm}
has type
  {ty}
but is expected to have type
  Code"


/--
Fallback elab if no Labelnames in l, L_w or L_b required
-/
elab id:ident withPosition(linebreak ppDedent(ppLine))
    "⦃" P:term "⦄" l:term "↦" "⟨" L_w:term "|" L_b:term "⟩" "⦃" Q:term "⦄"
    : term => do
  return ←Lean.Elab.Term.elabTerm
    (←`($(mkIdent ``hoareTripleUp) $P $Q $l $L_w $L_b $id)) none


/--
Elab of hoare assignment
-/
elab "⟦"stx:hoareAssignmentChain"⟧" : term => do
  return ←Lean.Elab.Term.elabTerm (← generateHoareAssignmentSyntax stx) none

/-- Notation `⟦⟧` for the identity assignment, denoting the unchanged state `st`. -/
elab "⟦⟧" : term => do
  return ←Lean.Elab.Term.elabTerm (← `($(mkIdent `st))) none
