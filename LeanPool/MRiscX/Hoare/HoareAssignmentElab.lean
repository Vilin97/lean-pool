/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import Lean
import LeanPool.MRiscX.Elab.HandleNumOrIdent
import LeanPool.MRiscX.Parser.HoareSyntax

/-!
# HoareAssignmentElab

This module provides elaboration of MRiscX Hoare assignment chains.
-/
open Lean Elab

/-- The total number of nodes in a syntax tree, an upper bound on its depth. -/
private def assignmentSyntaxSize : Syntax → Nat
  | .node _ _ args => 1 + args.foldl (fun acc s => acc + assignmentSyntaxSize s) 0
  | _ => 1

/-
This file contains the elaboaration of the hoare assignment terms.
Essentially, there are two types of hoare terms.
The "regular" hoare term, which represents the terms within a hoare triple.
E.g. ⦃x[2] = 12 ∧ ¬⸨termnated⸩⦄
These hoare terms just have to be translated to the function calls.

Then there is the HoareAssignment is represented by the ⟦⟧ brackets. They mean the following:

There is an Assertion which is true under the condition, that
the term inside the ⟦⟧ brackets is fulfilled
Those terms are slightly different than the "regular" hoare terms, because the
meaning is not the same. E.g. we don't want to write something like
```
x[r] = v
```
because this could indicate that if the statement is true before the hoare triple acutally
begins, the Assertion is true afterwards as well.
But we want to imply, that this Assertion is just true, when this happens during this
hoare triple.
So instead, we introduce the syntax of
```
x[r] ← v
```
to underline the fact, that the register r is passed the value wihtin this hoare triple.
To archieve this, a certain state has to be passed in as well to indicate, on which state
the functioncalls should be made.
These HoareAssignments are used for the specification of the instruction.
-/



/-
This function is similar to expandCDot?.
It traverses the given syntax and searches for patterns to replace the keywords
defined as syntax terminals with the actual functions calls
-/
/--
Fuel-bounded core of `replaceKeywords`, expanding the `x[num]`, `mem[num]` and
`mem[x[num]]` notation. The `fuel` argument bounds the syntax-tree recursion.
-/
private def replaceKeywordsAux (fuel : Nat) (curState : TSyntax `term) :
    Syntax → TermElabM Syntax
  | _stx@`(⸨terminated⸩) =>
    return ←`(term | $(mkIdent `MState.terminated) ($curState))
  | _stx@`(x[$r:mriscxNumOrIdent]) => do
    let newR ← parseMriscxNumOrIdentToTerm r
    return ←`(term | $(mkIdent `MState.getRegisterAt) ($curState) $newR)
  | _stx@`(mem[$t:term]) => do
    let et ← match fuel with
      | fuel + 1 => replaceKeywordsAux fuel curState t
      | 0 => pure t.raw
    return ←`(term | $(mkIdent `MState.getMemoryAt) ($curState) ($(⟨et⟩)))
  | _stx@`(labels[$s:ident]) => do
    let newS ← checkIfVariableToTerm s false
    return ←`(term | $(mkIdent `MState.getLabelAt) ($curState) $newS)
  | _stx@`(labels[.$s:ident]) => do
    let newS ← checkIfVariableToTerm s true
    return ←`(term | $(mkIdent `MState.getLabelAt) ($curState) $newS)
  | _stx@`(⸨pc⸩) => do
    return ←`(term | $(mkIdent `MState.pc) ($curState))
  | stx => match fuel, stx with
    | fuel + 1, .node _ k args => do
      let args ← args.mapM (replaceKeywordsAux fuel curState)
      return .node (.fromRef stx (canonical := true)) k args
    | _, stx => pure stx

/--
Traverse `stx` and replace the keyword notations (`x[..]`, `mem[..]`, `labels[..]`,
`⸨pc⸩`, `⸨terminated⸩`) by the corresponding `MState` function calls on `curState`.
-/
def replaceKeywords (stx : Term) (curState : TSyntax `term) : TermElabM Syntax :=
  replaceKeywordsAux (assignmentSyntaxSize stx) curState stx

/-
Seperate all the assignemnts within the ⟦⟧ and store in one array
-/
/-- Fuel-bounded core of `getHoareAssignmentArray`; `fuel` bounds the recursion. -/
private def getHoareAssignmentArrayAux (fuel : Nat) (stx : TSyntax `hoareAssignmentChain)
    (curArr : Array (TSyntax `hoareAssignment)) :
    TermElabM (Array (TSyntax `hoareAssignment)) := do
  match stx with
  | `(hoareAssignmentChain | $t:hoareAssignment) =>
    return curArr.push t
  | `(hoareAssignmentChain | $t1:hoareAssignment; $t2:hoareAssignment) =>
    return (curArr.push t1).push t2
  | `(hoareAssignmentChain | $t:hoareAssignment; $s:hoareAssignmentChain) =>
    match fuel with
    | fuel + 1 => return ←(getHoareAssignmentArrayAux fuel s (curArr.push t))
    | 0 => throwError "Ran out of fuel while reading a hoare assignment chain"
  | _ => throwError s!"hoare assignment {stx} term not known!"

/-- Collect every assignment in the `⟦⟧` chain `stx` into a single array. -/
def getHoareAssignmentArray (stx: TSyntax `hoareAssignmentChain)
    (curArr: Array (TSyntax `hoareAssignment)): TermElabM (Array (TSyntax `hoareAssignment)) :=
  getHoareAssignmentArrayAux (assignmentSyntaxSize stx) stx curArr

/-
Parse the TSyntax to the actual function calls
-/
/-- Fold a single Hoare assignment onto the accumulated state-update term,
turning it into the corresponding `MState` mutation. -/
def foldTermArray (element: TSyntax `hoareAssignment) (curTerm: TSyntax `term) :
    TermElabM (TSyntax `term) := do
  match element with
  | `(hoareAssignment | x[$r:mriscxNumOrIdent] ← $t:term)
  | `(hoareAssignment | x[$r:mriscxNumOrIdent] <- $t:term) => do
    let newR ← parseMriscxNumOrIdentToTerm r
    let newT := ⟨←replaceKeywords t curTerm⟩
    -- let newV := ← parseMriscxNumOrIdentToTerm v
    return ←`(term | $(mkIdent `MState.addRegister) ($curTerm) $newR $newT)
  | `(hoareAssignment | mem[$m:term] ← $t:term)
  | `(hoareAssignment | mem[$m:term] <- $t:term) => do
    let newM := ⟨←replaceKeywords m curTerm⟩
    let newT := ⟨←replaceKeywords t curTerm⟩
    -- let newV := ← parseMriscxNumOrIdentToTerm v
    return ←`(term | $(mkIdent `MState.addMemory) ($curTerm) $newM $newT)
  | `(hoareAssignment | pc++) =>
    return ←`(term | $(mkIdent `MState.incPc) ($curTerm))
  | `(hoareAssignment | pc ← $i:term) => do
    return ←`(term | $(mkIdent `MState.setPc) ($curTerm) $i)
  | _ => throwError s!"{element}"

/-
Construct the final lambda term
-/
/-- Construct the final state-update lambda term from a chain of Hoare assignments. -/
def generateHoareAssignmentSyntax (stx: TSyntax `hoareAssignmentChain): TermElabM (Syntax)
    := do
  let termArray ← getHoareAssignmentArray stx #[]
  let result ← termArray.foldrM foldTermArray (←`($(mkIdent `st)))
  return result
