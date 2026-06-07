/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import Lean
import LeanPool.MRiscX.Hoare.HoareCore
import LeanPool.MRiscX.AbstractSyntax.Instr
import LeanPool.MRiscX.AbstractSyntax.AbstractSyntax
import LeanPool.MRiscX.Elab.HandleNumOrIdent
import LeanPool.MRiscX.Elab.HandleExpr
import LeanPool.MRiscX.Tactics.TacticUtil
import Mathlib.Data.Set.Basic
open Lean Meta Elab Parser Tactic


def extractL_w'AndL_b'' (e : Expr) : MetaM (Expr × Expr) := do
  let whnf ← Meta.whnf e
  if whnf.isAppOf `Eq then
    let lam ← (Meta.whnf <| whnf.getArg! 1)
    if lam.isLambda then
      let body ← (Meta.whnf <| lam.bindingBody!)
      let L_w' ← (Meta.whnf <| body.getArg! 0)
      let L_w' ← (Meta.whnf <| L_w')
      let L_b'' ← (Meta.whnf <| body.getArg! 1)
      let L_b'' ← (Meta.whnf <| L_b'')


      return (L_w', L_b'')
  throwError "Expected Expr to be of type 'Eq' "

def extractQ (arr : PersistentArray (Option LocalDecl)) : MetaM (Expr) := do
  if arr.size == 0 then
    throwError "Could not find a declaration in hypothesis"
  for decl in arr do
    match decl with
    | some l =>
      let type := l.type
      if type.isAppOfArity `hoare_triple_up 6 then
        return type.getArg! 1
    | _  => pure ()
  throwError "Could not find a term of hoare_triple_up"


def incPcExpr (state : Expr) : Expr := Expr.app (.const `MState.incPc []) (state)

def getStateExpr (state?: Option Expr) : Expr :=
  match state? with
  | some state =>
    state
  | none =>
    (.bvar 0)


def getExprOfInstForR (instr : Instr) (oldState : Expr): MetaM Expr := do
  match instr with
  | Instr.LoadAddress r v
  | Instr.LoadImmediate r v =>
    return mkAppN (.const `MState.addRegister [])
      #[(incPcExpr oldState), mkUInt64Lit r, mkUInt64Lit v]
  | Instr.StoreWord reg dst =>
    return mkAppN (.const `MState.addMemory [])
      #[(incPcExpr oldState), mkUInt64Lit reg, mkUInt64Lit dst]
  | _ => throwError "Error while building R, the Instruction is not implemented yet
      for this feature"


def getExprOfInstrForRFromExpr (instr : Expr) (oldState : Expr) : MetaM Expr := do
  let e ← Meta.whnf instr
  if (e.isAppOfArity' `Instr.LoadImmediate 2
     || e.isAppOfArity' `Instr.LoadAddress 2)
  then
    let r := e.getArg! 0
    let v := e.getArg! 1

    return mkAppN (.const `MState.addRegister [])
      #[(incPcExpr oldState), r, v]
  else if instr.isAppOfArity' `Instr.StoreWord 2 then
    let r := e.getArg! 0
    let d := e.getArg! 1

    return mkAppN (.const `MState.addMemory [])
      #[(incPcExpr oldState), r, d]
  else
    throwError s!"Error while building R, the Instruction is not implemented yet for this feature"




def typeSetUInt64 : Expr :=
  mkApp (.const `Set [levelZero]) (.const `UInt64 [])


def mkSingletonOf (n : UInt64) : Expr :=
  let instSing := mkAppN (.const ``Set.instSingletonSet [levelZero]) #[(.const `UInt64 [])]
  let set := mkApp (.const `Set [levelZero]) (mkConst `UInt64)
  mkAppN (.const ``Singleton.singleton [levelZero, levelZero])
    #[(mkConst `UInt64), set, instSing, mkUInt64Lit n]


def getNeSet (n : UInt64) : Expr :=
  let lam := Expr.lam `n (.const `UInt64 []) (mkAppN (.const `Ne [levelOne])
      #[(Expr.const `UInt64 []), (.bvar 0), mkUInt64Lit n])
    BinderInfo.default
  mkAppN (.const `setOf [levelZero]) #[(mkConst `UInt64), lam]



def calcRExprDefault (Q: Expr) (lastInstrExpr : Expr): MetaM Expr := do
  let hasOneLam := Q.isLambda
  if !hasOneLam then
    throwError s!"Expected postcondition Q {Q} to be a λ-expression"
  let hasScdLam := Q.bindingBody!.getAppFn.isLambda

  let mstateInferredOld := ← match hasScdLam with
                | true => do
                  match Q.bindingBody!.getArg? 1 with
                  | some state => do
                    return state
                  | none => throwError "Expected Q with 2 λ-expressions to have 2 arguments"
                | false =>
                  return (.bvar 0)

  let qBody := ←match hasScdLam with
              | true => do
                return Q.bindingBody!.getAppFn
              | false => do
                return Q

  let assignmentToAdd ← getExprOfInstrForRFromExpr lastInstrExpr mstateInferredOld

  return Expr.lam `st (.const `MState []) (mkApp qBody assignmentToAdd)
    BinderInfo.default



elab "peel_last_instr" : tactic => do
  let originalGoal ← getMainGoal
  let oGoalType ← originalGoal.getType
  evalTactic (←`(tactic | intros $(mkIdent `h_L_w'_inter_L_b'') _ $(mkIdent `s)
                            $(mkIdent `h_code') $(mkIdent `h_pc) $(mkIdent `P)))

  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let f ← Meta.whnf <| ←goal.getType
    let currentQ := ((f.getArg! 1).bindingBody!.getAppArgs[1]!.getArg! 0).getAppFn

    let ctx ← Lean.MonadLCtx.getLCtx
    let P := oGoalType.getArg! 0
    let pcAsExpr := oGoalType.getArg! 2

    let L_w'_expr := oGoalType.getArg! 3
    let L_b''_expr  := oGoalType.getArg! 4
    let L_b_expr ← mkAppM ``Union.union #[L_b''_expr, L_w'_expr]

    let codeEqExpr ← Meta.whnf (←findHypTypeM ctx `h_code')
    let codeExpr := codeEqExpr.getArg! 2

    let L_w' ← parseSingletonExpr L_w'_expr
    let L_w_expr := mkSingletonOf (L_w' - 1)
    let L_b'asExpr := getNeSet L_w'

    let instrToSplit ← getInstrFromCodeExpr codeExpr (L_w' - 1)

    let newR ← calcRExprDefault currentQ instrToSplit
    let preMVar ← mkFreshExprMVar (some typeSetUInt64)
    let mut s_seq := mkAppN (mkConst `S_SEQ [])
      #[preMVar, P, newR, currentQ, codeExpr, pcAsExpr, L_w_expr, L_b_expr,
        L_w'_expr, L_b'asExpr]

    let mva ← goal.apply s_seq (term? := some m!"`{s_seq}`")
    Term.synthesizeSyntheticMVarsNoPostponing
    replaceMainGoal mva
