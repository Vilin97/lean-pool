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
partial def replaceKeywords (stx : Term) (curState : TSyntax `term) : TermElabM Syntax := do
  go stx
where
  /--
  Auxiliary function for expanding the `x[num]`, `mem[num]` and
  `mem[x[num]]` notation.
  If `stx` is a `x[num]`, `mem[num]` or `mem[x[num]]`,
  we return the corresponding functions on the state.
  Otherwise, we just return `stx`.
  -/
  go : Syntax → TermElabM Syntax
  | _stx@`(⸨terminated⸩) =>
    return ←`(term | $(mkIdent `MState.terminated) ($curState))
  | _stx@`(x[$r:mriscx_num_or_ident]) => do
    let newR ← parseMriscxNumOrIdentToTerm r
    return ←`(term | $(mkIdent `MState.getRegisterAt) ($curState) $newR)
  | _stx@`(mem[$t:term]) => do
    let et ← replaceKeywords t curState
    return ←`(term | $(mkIdent `MState.getMemoryAt) ($curState) ($(⟨et⟩)))
  | _stx@`(labels[$s:ident]) => do
    let newS ← checkIfVariableToTerm s false
    return ←`(term | $(mkIdent `MState.getLabelAt) ($curState) $newS)
  | _stx@`(labels[.$s:ident]) => do
    let newS ← checkIfVariableToTerm s true
    return ←`(term | $(mkIdent `MState.getLabelAt) ($curState) $newS)
  | _stx@`(⸨pc⸩) => do
    return ←`(term | $(mkIdent `MState.pc) ($curState))
  | stx => match stx with
    | .node _ k args => do
      let args ← args.mapM go
      return .node (.fromRef stx (canonical := true)) k args
    | _ => pure stx

/-
Seperate all the assignemnts within the ⟦⟧ and store in one array
-/
partial def getHoareAssignmentArray (stx: TSyntax `hoare_assignment_chain)
    (curArr: Array (TSyntax `hoare_assignment)): TermElabM (Array (TSyntax `hoare_assignment)) := do
  match stx with
  | `(hoare_assignment_chain | $t:hoare_assignment) =>
    return curArr.push t
  | `(hoare_assignment_chain | $t1:hoare_assignment ; $t2:hoare_assignment) =>
    return (curArr.push t1).push t2
  | `(hoare_assignment_chain | $t:hoare_assignment ; $s:hoare_assignment_chain) =>
    return ←(getHoareAssignmentArray s (curArr.push t))
  | _ => throwError s!"hoare assignment {stx} term not known!"

/-
Parse the TSyntax to the actual function calls
-/
def foldTermArray (element: TSyntax `hoare_assignment) (curTerm: TSyntax `term) :
    TermElabM (TSyntax `term) := do
  match element with
  | `(hoare_assignment | x[$r:mriscx_num_or_ident] ← $t:term)
  | `(hoare_assignment | x[$r:mriscx_num_or_ident] <- $t:term) => do
    let newR ← parseMriscxNumOrIdentToTerm r
    let newT := ⟨←replaceKeywords t curTerm⟩
    -- let newV := ← parseMriscxNumOrIdentToTerm v
    return ←`(term | $(mkIdent `MState.addRegister) ($curTerm) $newR $newT)
  | `(hoare_assignment | mem[$m:term] ← $t:term)
  | `(hoare_assignment | mem[$m:term] <- $t:term) => do
    let newM := ⟨←replaceKeywords m curTerm⟩
    let newT := ⟨←replaceKeywords t curTerm⟩
    -- let newV := ← parseMriscxNumOrIdentToTerm v
    return ←`(term | $(mkIdent `MState.addMemory) ($curTerm) $newM $newT)
  | `(hoare_assignment | pc++) =>
    return ←`(term | $(mkIdent `MState.incPc) ($curTerm))
  | `(hoare_assignment | pc ← $i:term) => do
    return ←`(term | $(mkIdent `MState.setPc) ($curTerm) $i)
  | _ => throwError s!"{element}"

/-
Construct the final lambda term
-/
partial def generateHoareAssignmentSyntax (stx: TSyntax `hoare_assignment_chain): TermElabM (Syntax)
    := do
  let termArray ← getHoareAssignmentArray stx #[]
  let result ← termArray.foldrM foldTermArray (←`($(mkIdent `st)))
  return result
