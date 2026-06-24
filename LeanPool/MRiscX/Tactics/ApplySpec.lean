/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import Lean.Elab.Tactic.Basic
import LeanPool.MRiscX.AbstractSyntax.Instr
import LeanPool.MRiscX.AbstractSyntax.AbstractSyntax
import LeanPool.MRiscX.Semantics.Specification
import LeanPool.MRiscX.Elab.HandleNumOrIdent
import LeanPool.MRiscX.Elab.HandleExpr
import LeanPool.MRiscX.Tactics.TacticUtil
import LeanPool.MRiscX.Tactics.GeneralCustomTactics
import LeanPool.MRiscX.Tactics.HelpCodeProofTactics

import Mathlib.Data.Set.Basic

/-!
# ApplySpec

This module provides the tactic applying per-instruction specifications.
-/

open Lean Meta Elab Parser Tactic Syntax Term


private def getSpecTacFromInstr (i : Instr) (pc : UInt64) (name? : Option Ident := none)
    : TacticM (TSyntax `tactic) := do
  let check (specName : Name) (tac : TSyntax `tactic) : TacticM (TSyntax `tactic) := do
    if let some n := name? then
      if n.getId != specName then
        throwError s!"Specification {n.getId} does not match instruction {i}"
    return tac
  let handleJump (trueName falseName : Name) (trueTac falseTac : TSyntax `tactic)
        (instrName : String)
      : TacticM (TSyntax `tactic) := do
    if let some n := name? then
      if n.getId == trueName then return trueTac
      else if n.getId == falseName then return falseTac
      else throwError s!"Specification {n.getId} does not match instruction {instrName}"
    else
      return (←`(tactic | first | $trueTac:tactic | $falseTac:tactic))
  match i with
  | Instr.LoadAddress dst addr =>
    check `specification_LoadAddress
      (←`(tactic | apply specification_LoadAddress
        (pc := $(mkNumLit s!"{pc}"))
                                                        (dst := $(mkNumLit s!"{dst}"))
                                                        (addr := $(mkNumLit s!"{addr}"))))
  | Instr.LoadImmediate dst val =>
    check `specification_LoadImmediate
      (←`(tactic | apply specification_LoadImmediate
        (pc := $(mkNumLit s!"{pc}"))
                                                          (dst := $(mkNumLit s!"{dst}"))
                                                          (val := $(mkNumLit s!"{val}"))))
  | Instr.CopyRegister dst src =>
    check `specification_CopyRegister
      (←`(tactic | apply specification_CopyRegister
        (pc := $(mkNumLit s!"{pc}"))
                                                          (dst := $(mkNumLit s!"{dst}"))
                                                          (src := $(mkNumLit s!"{src}"))))
  | Instr.AddImmediate dst reg val =>
    check `specification_AddImmediate
      (←`(tactic | apply specification_AddImmediate
        (pc := $(mkNumLit s!"{pc}"))
                                                          (dst := $(mkNumLit s!"{dst}"))
                                                          (regAddend := $(mkNumLit s!"{reg}"))
                                                          (val := $(mkNumLit s!"{val}"))))
  | Instr.Increment dst =>
    check `specification_Increment
      (←`(tactic | apply specification_Increment
        (pc := $(mkNumLit s!"{pc}"))
                                                      (dst := $(mkNumLit s!"{dst}"))))
  | Instr.AddRegister dst regAddend1 regAddend2 =>
    check `specification_AddRegister
      (←`(tactic | apply specification_AddRegister
        (pc := $(mkNumLit s!"{pc}"))
                                                        (dst := $(mkNumLit s!"{dst}"))
                                                        (regAddend1 :=
                                                          $(mkNumLit s!"{regAddend1}"))
                                                        (regAddend2 :=
                                                          $(mkNumLit s!"{regAddend2}"))))
  | Instr.SubImmediate dst reg imm =>
    check `specification_SubImmediate
      (←`(tactic | apply specification_SubImmediate
        (pc := $(mkNumLit s!"{pc}"))
                                                          (dst := $(mkNumLit s!"{dst}"))
                                                          (regMinuend := $(mkNumLit s!"{reg}"))
                                                          (subtrahend := $(mkNumLit s!"{imm}"))))
  | Instr.Decrement r =>
    check `specification_Decrement
      (←`(tactic | apply specification_Decrement
        (pc := $(mkNumLit s!"{pc}"))
                                                      (dst := $(mkNumLit s!"{r}"))))
  | Instr.SubRegister dst regMinuend regSubtrahend =>
    check `specification_SubRegister
      (←`(tactic | apply specification_SubRegister
        (pc := $(mkNumLit s!"{pc}"))
                                                        (dst := $(mkNumLit s!"{dst}"))
                                                        (regMinuend := $(mkNumLit s!"{regMinuend}"))
                                                        (regSubtrahend :=
                                                          $(mkNumLit s!"{regSubtrahend}"))))
  | Instr.XorImmediate dst reg val =>
    check `specification_XorImmediate
      (←`(tactic | apply specification_XorImmediate
        (pc := $(mkNumLit s!"{pc}"))
                                                             (dst := $(mkNumLit s!"{dst}"))
                                                             (reg := $(mkNumLit s!"{reg}"))
                                                             (val := $(mkNumLit s!"{val}"))))
  | Instr.XOR dst reg1 reg2 =>
    check `specification_XOR (←`(tactic | apply specification_XOR (pc := $(mkNumLit s!"{pc}"))
                                                (dst := $(mkNumLit s!"{dst}"))
                                                (reg1 := $(mkNumLit s!"{reg1}"))
                                                (reg2 := $(mkNumLit s!"{reg2}"))))
  | Instr.LoadWordImmediate dst addr =>
    check `specification_LoadWordImmediate
      (←`(tactic | apply specification_LoadWordImmediate
        (pc := $(mkNumLit s!"{pc}"))
                                                             (dst := $(mkNumLit s!"{dst}"))
                                                             (addr := $(mkNumLit s!"{addr}"))))
  | Instr.LoadWordReg dst regWithAddr =>
    check `specification_LoadWordReg
      (←`(tactic | apply specification_LoadWordReg
        (pc := $(mkNumLit s!"{pc}"))
                                                        (dst := $(mkNumLit s!"{dst}"))
                                                        (regWithAddr :=
                                                          $(mkNumLit s!"{regWithAddr}"))))
  | Instr.StoreWord regWithValue regWithAddr =>
    check `specification_StoreWordImmediate
      (←`(tactic | apply specification_StoreWordImmediate
        (pc := $(mkNumLit s!"{pc}"))
                                                      (regWithValue :=
                                                        $(mkNumLit s!"{regWithValue}"))
                                                      (regWithAddr :=
                                                        $(mkNumLit s!"{regWithAddr}"))))
  | Instr.Jump lbl =>
    check `specification_Jump (←`(tactic | apply specification_Jump (pc := $(mkNumLit s!"{pc}"))
                                                   (label := $(mkStrLit lbl))))
  | Instr.JumpEq reg1 reg2 lbl =>
    handleJump `specification_JumpEq_true `specification_JumpEq_false
      (←`(tactic | apply specification_JumpEq_true (pc := $(mkNumLit s!"{pc}"))
                                                        (reg1 := $(mkNumLit s!"{reg1}"))
                                                        (reg2 := $(mkNumLit s!"{reg2}"))
                                                        (s := $(mkStrLit lbl))))
      (←`(tactic | apply specification_JumpEq_false (pc := $(mkNumLit s!"{pc}"))
                                                        (reg1 := $(mkNumLit s!"{reg1}"))
                                                        (reg2 := $(mkNumLit s!"{reg2}"))
                                                        (s := $(mkStrLit lbl))))
      "JumpEq"
  | Instr.JumpNeq reg1 reg2 lbl =>
    handleJump `specification_JumpNeq_true `specification_JumpNeq_false
      (←`(tactic | apply specification_JumpNeq_true (pc := $(mkNumLit s!"{pc}"))
                                                        (reg1 := $(mkNumLit s!"{reg1}"))
                                                        (reg2 := $(mkNumLit s!"{reg2}"))
                                                        (s := $(mkStrLit lbl))))
      (←`(tactic | apply specification_JumpNeq_false (pc := $(mkNumLit s!"{pc}"))
                                                        (reg1 := $(mkNumLit s!"{reg1}"))
                                                        (reg2 := $(mkNumLit s!"{reg2}"))
                                                        (s := $(mkStrLit lbl))))
      "JumpNeq"
  | Instr.JumpGt reg1 reg2 lbl =>
    handleJump `specification_JumpGt_true `specification_JumpGt_false
      (←`(tactic | apply specification_JumpGt_true (pc := $(mkNumLit s!"{pc}"))
                                                        (reg1 := $(mkNumLit s!"{reg1}"))
                                                        (reg2 := $(mkNumLit s!"{reg2}"))
                                                        (s := $(mkStrLit lbl))))
      (←`(tactic | apply specification_JumpGt_false (pc := $(mkNumLit s!"{pc}"))
                                                        (reg1 := $(mkNumLit s!"{reg1}"))
                                                        (reg2 := $(mkNumLit s!"{reg2}"))
                                                        (s := $(mkStrLit lbl))))
      "JumpGt"
  | Instr.JumpLe reg1 reg2 lbl =>
    handleJump `specification_JumpLe_true `specification_JumpLe_false
      (←`(tactic | apply specification_JumpLe_true (pc := $(mkNumLit s!"{pc}"))
                                                        (reg1 := $(mkNumLit s!"{reg1}"))
                                                        (reg2 := $(mkNumLit s!"{reg2}"))
                                                        (s := $(mkStrLit lbl))))
      (←`(tactic | apply specification_JumpLe_false (pc := $(mkNumLit s!"{pc}"))
                                                        (reg1 := $(mkNumLit s!"{reg1}"))
                                                        (reg2 := $(mkNumLit s!"{reg2}"))
                                                        (s := $(mkStrLit lbl))))
      "JumpLe"
  | Instr.JumpEqZero reg lbl =>
    handleJump `specification_JumpEqZero_true `specification_JumpEqZero_false
      (←`(tactic | apply specification_JumpEqZero_true (pc := $(mkNumLit s!"{pc}"))
                                                        (reg := $(mkNumLit s!"{reg}"))
                                                        (label := $(mkStrLit lbl))))
      (←`(tactic | apply specification_JumpEqZero_false (pc := $(mkNumLit s!"{pc}"))
                                                        (reg := $(mkNumLit s!"{reg}"))
                                                        (label := $(mkStrLit lbl))))
      "JumpEqZero"
  | Instr.JumpNeqZero reg lbl =>
    handleJump `specification_JumpNeqZero_true `specification_JumpNeqZero_false
      (←`(tactic | apply specification_JumpNeqZero_true (pc := $(mkNumLit s!"{pc}"))
                                                        (reg := $(mkNumLit s!"{reg}"))
                                                        (s := $(mkStrLit lbl))))
      (←`(tactic | apply specification_JumpNeqZero_false (pc := $(mkNumLit s!"{pc}"))
                                                        (reg := $(mkNumLit s!"{reg}"))
                                                        (s := $(mkStrLit lbl))))
      "JumpNeqZero"
  | Instr.Panic =>
    throwError "Cannot apply a specification for the instruction `Panic`"



private def runSpecAndSolve (instr : Instr) (pc : UInt64) (name? : Option Ident := none) :
    TacticM Unit := do
  evalTactic (← getSpecTacFromInstr instr pc name?)


private def getInstrAtPc (ctx : Lean.LocalContext) (pc : UInt64) :
    TacticM Instr := do
  let codeEqExpr ← Meta.whnf (← findHypTypeM ctx `h_code')
  let codeExpr := codeEqExpr.getArg! 2
  let instrExpr ← getInstrFromCodeExpr codeExpr pc
  getInstrFromExpr instrExpr



/-- Apply an instruction specification to the first generated goal. -/
elab "applySpecFrstGoal" name?:(Lean.Parser.ident)? : tactic => do
  -- Since the pc in the first goal is (probably) always 0, we can
  -- just introduce everything and go through everything and, get
  -- the pc from the hypotheses `h_pc = n ` and apply the specification
  evalTactic (← `(tactic |
    intros $(mkIdent `h_inter)
            $(mkIdent `h_empty)
            $(mkIdent `s)
            $(mkIdent `h_code')
            $(mkIdent `h_pc)
            $(mkIdent `user_precondition)
  ))
  Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx
    let pcAs ← Meta.whnf (← findHypTypeM ctx `h_pc)
    let pcExpr := pcAs.getAppArgs[2]!
    let pc ← getUInt64FromExpr pcExpr
    let instr ← getInstrAtPc ctx pc
    evalTactic (← `(tactic | rw [← $(mkIdent `h_code')]))
    evalTactic (← `(tactic | splitCondis in $(mkIdent `user_precondition)))
    runSpecAndSolve instr pc name?


/-- Apply an instruction specification to the second generated goal. -/
elab "applySpecScdGoal" name?:(Lean.Parser.ident)? : tactic => do
  -- First phase: determine how we obtain pc
  let pcFromHyp ← Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx
    return ((← findHypTypeM? ctx `h_code') == none)
  -- If the code was not introduced, introduce it now
  if pcFromHyp then
    evalTactic (← `(tactic | prepareSecondSeq))
  -- After introducing new stuff into the hypotheses, we need to update the
  -- context
  Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx
    let pc ←
      -- If we had to introduce the hypotheses' ourlelves, there is only one
      -- h_pc, which we can just extract and parse
      if pcFromHyp then
        let pcEqExpr ← Meta.whnf (← findHypTypeM ctx `h_pc)
        let pcExpr := pcEqExpr.getAppArgs[2]!
        getUInt64FromExpr pcExpr
      -- Else, the hypotheses h_code and so on were already introduced.
      -- Now we cannot extract the pc from the hypotheses, because there are multiple
      -- instances of h_pc. In this case, we need to extract the correct value
      -- from l'
      else
        let g ← getMainGoal
        let goalType ← g.getType
        -- Since the goal is in the form of `∀ l' ∈ {...} → ...`, we
        -- just access the value in the Set and hope it is just one.
        -- (TODO: handle multiple values)
        let lExpr := goalType.bindingBody!.bindingDomain!.getAppArgs[3]!
        let pc ← parseSingletonExpr lExpr
        -- After obtaining the value of pc, we need to introduce the
        -- rest of the lemma and prepare everything for the application etc.
        evalTactic (← `(tactic | prepareSecondSeq))
        pure pc
    let instr ← getInstrAtPc ctx pc
    evalTactic (← `(tactic | intros $(mkIdent `user_precondition)))
    evalTactic (← `(tactic | splitCondis in $(mkIdent `user_precondition)))
    runSpecAndSolve instr pc name?
