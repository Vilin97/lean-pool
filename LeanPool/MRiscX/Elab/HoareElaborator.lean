/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import LeanPool.MRiscX.Hoare.HoareCore
import LeanPool.MRiscX.Elab.CodeElaborator
import LeanPool.MRiscX.Parser.HoareSyntax

/-!
# HoareElaborator

This module provides the elaborator for MRiscX Hoare-triple syntax.
-/


open Lean Meta Elab

/-
This file contains the definition of the Hoare Notation and elaboration.
The Syntax of the hoare triples is as close as possible to the notation from
the paper of lundberg et al.. Some exceptions had to be made since "[]" are already
widely known as lists.
-/

macro  a₁:term " ∧∧ " a₂:term : term => do
  `(Assertion.And $a₁ $a₂)

macro "∼" a:ident : term =>
  `(Assertion.Not $a)

def processHoareTerm (stx : Term) : TermElabM Syntax := do
  withFreshMacroScope do
    let mut newStx ← (go stx)
    return newStx
where
  /-
    Differentiate between hoare assignment and usual term in pre and post condition.
  -/
  go : Syntax → TermElabM Syntax
  | _stx@`(hoare_assignment_term | ⟦$h:hoare_assignment_chain⟧) => do
    return ←generateHoareAssignmentSyntax h
  | _stx@`($t:term) => do
    let mut newStx ← replaceKeywords t (←`($(mkIdent `st)))
    return newStx



def elabHoareTerm (stx : Term) : TermElabM (Term) := do
  let newStx ← processHoareTerm stx
  let stIdent := mkIdent `st
  return ←`(fun $stIdent : MState => ($(⟨newStx⟩)))


elab "⦃" t:term "⦄" : term => do
  let newTOpt ← elabHoareTerm t
  return ← Lean.Elab.Term.elabTerm (←`($newTOpt)) (some (.const ``String []))


/--
Some utility function which casts an `Array TSyntax mriscx_label` to `TSyntax term`
-/
def mriscxSyntaxToTerm (stx : Array (TSyntax `mriscx_label)) : TermElabM (TSyntax `term) := do
  let newStx : (TSyntax `term) := ←`(mriscx
                                      $stx*
                                     end)
  return newStx

/--
Some utility function which casts `TSyntax mriscx_label` to `TSyntax term`
-/
def mriscxSpecToTerm (stx : (TSyntax `mriscx_Instr)) : TermElabM (TSyntax `term) := do
  let newStx : (TSyntax `term) ←`(⟪$stx⟫)
  return ←`($newStx)


/--
Hoare-triples for specifications with only one instruction
-/
elab "hoare" syn:mriscx_spec linebreak
      "⦃" P:term "⦄" l:term "↦" "⟨" L_w:term "|" L_b:term "⟩" "⦃" Q:term "⦄"
      "end" : term => do
  let translatedP ← elabHoareTerm P
  let translatedQ ← elabHoareTerm Q
  match syn with
  | `(mriscx_spec | ⟪$i:mriscx_Instr⟫) => do
    let synAsTerm ← mriscxSpecToTerm i
    return ←Lean.Elab.Term.elabTerm
        (←`($(mkIdent ``hoare_triple_up_1) $translatedP $translatedQ $l $L_w $L_b $synAsTerm)) none
  | _ => throwError "Expected syntax of type mriscx_spec with ⟪⟫ braces!"


/--
Regular Hoare-triple with concrete MRiscX syntax before the actual triple
-/
elab t:hoare_term : term => do
  match t with
  | `(hoare_term | $syn:mriscx_syntax
    ⦃ $P:term ⦄ $l:term ↦ ⟨ $L_w:term | $L_b:term ⟩ ⦃ $Q:term ⦄) =>
    let translatedP ← elabHoareTerm P
    let translatedQ ← elabHoareTerm Q
    let labels ← getLabelMapFromSyntax syn
    let evaluatedLw := ⟨(←replaceLabels L_w labels)⟩
    let evaluatedLb := ⟨(←replaceLabels L_b labels)⟩
    let evaluatedL := ⟨(←replaceLabels l labels)⟩
    match syn with
    | `(mriscx_syntax | mriscx
      $labelsSyn:mriscx_label*
      end) => do
      let mriscxSyntaxAsTerm ← mriscxSyntaxToTerm labelsSyn
      return ←Lean.Elab.Term.elabTerm (←`($(mkIdent ``hoare_triple_up) $translatedP $translatedQ
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
      (←`($(mkIdent ``hoare_triple_up) $translatedP $translatedQ $evaluatedL $evaluatedLw
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
        (←`($(mkIdent ``hoare_triple_up) $translatedP $translatedQ $evaluatedL $evaluatedLw
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
    (←`($(mkIdent ``hoare_triple_up) $P $Q $l $L_w $L_b $id)) none


/--
Elab of hoare assignment
-/
elab "⟦"stx:hoare_assignment_chain"⟧" : term => do
  return ←Lean.Elab.Term.elabTerm (← generateHoareAssignmentSyntax stx) none

elab "⟦⟧" : term => do
  return ←Lean.Elab.Term.elabTerm (← `($(mkIdent `st))) none
