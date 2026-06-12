/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import LeanPool.MRiscX.AbstractSyntax.AbstractSyntax
import Lean

/-!
# HandleExpr

This module provides helpers reflecting Lean `Expr`s into MRiscX data.
-/
open Lean Meta Elab

/-
This file contains some utility functions when working with expressions
-/

/-- The number of sub-expressions in `e`, an upper bound on its recursion depth. -/
private def exprDepthBound : Expr → Nat
  | .app f a => 1 + exprDepthBound f + exprDepthBound a
  | .lam _ t b _ => 1 + exprDepthBound t + exprDepthBound b
  | .forallE _ t b _ => 1 + exprDepthBound t + exprDepthBound b
  | .letE _ t v b _ => 1 + exprDepthBound t + exprDepthBound v + exprDepthBound b
  | .mdata _ b => 1 + exprDepthBound b
  | .proj _ _ b => 1 + exprDepthBound b
  | _ => 1

/-- Fold the optional label expression `e?` into the running `labelmap` expression. -/
def unwrapWhileCreateLabelmap (e? : Option Expr) (labelmap: Expr) : MetaM Expr :=
  match e? with
  | some arg => pure arg
  | none => throwError s!"Experienced an index out of bounds while trying to create a labelmap
    from expr {labelmap}"


/-- Evaluate an `Expr` to the `UInt64` it denotes. -/
def getUInt64FromExpr (e : Expr) : MetaM UInt64 := do
  let e ← Meta.whnf e
  if e.isAppOfArity ``UInt64 1 then
    let val ← Meta.whnf <| e.getArg! 0
    let arg := val.getAppArgs[2]!
    let rawNat  ← Meta.whnf <| arg.getArg! 1
    let n := rawNat.rawNatLit?
    match n with
    | some i => return UInt64.ofNat i
    | _ => throwError "Used the wrong argument to get UInt64 from Expr"
  else if e.isAppOfArity' ``UInt64.ofBitVec 1 then
    let bitVecOfNat := e.getArg! 0
    -- this might fall apart when bitvectors are implemented1 slightly differently,
    -- probably should be refactored
    let bitVectorArg := bitVecOfNat.getArg! 1

    match bitVectorArg.rawNatLit? with
    | some i => return UInt64.ofNat i
    | none => pure ()

    if (bitVectorArg.isAppOfArity' ``OfNat.ofNat 3) then
      let bitVectorArg := bitVectorArg.getArg! 1
      match bitVectorArg.rawNatLit? with
          | some i => return UInt64.ofNat i
          | none => pure ()

    let bitVectorArg ← Meta.whnf <| ←unwrapWhileCreateLabelmap (bitVecOfNat.getAppArgs[1]?) e
    let ofNatArgs ← Meta.whnf <| ← unwrapWhileCreateLabelmap (bitVectorArg.getAppArgs[2]?) e
    let rawNat ← unwrapWhileCreateLabelmap ofNatArgs.getAppArgs[1]? e

    match rawNat.rawNatLit? with
    | some i => return UInt64.ofNat i
    | _ => throwError "Used the wrong argument to get UInt64 from Expr"
  else
    throwError "Not a UInt64 Expression"


/-- Evaluate an `Expr` to the `String` it denotes. -/
def getStrFromExpr (e : Expr) : MetaM String := do
  let e ← Meta.whnf e
  match e with
  | Expr.lit (Literal.strVal s) => return s
  | _ => throwError "Expected a string literal"


/-- Fuel-bounded core of `getLabelMapFromMapExpr`; `fuel` bounds the recursion. -/
private def getLabelMapFromMapExprAux (fuel : Nat) (e : Expr) : MetaM LabelMap := do
  let e ← Meta.whnf e
  if e.isAppOfArity ``PMap.empty 2 then
    return PMap.empty
  else if e.isAppOfArity ``PMap.put 5 then
    let labelNameExpr ← Meta.whnf <| e.getArg! 2
    let labelName ← getStrFromExpr labelNameExpr
    let val ← Meta.whnf <| e.getArg! 3
    let n ← getUInt64FromExpr val
    match fuel with
    | fuel + 1 => return PMap.put labelName n (←getLabelMapFromMapExprAux fuel (e.getArg! 4))
    | 0 => throwError "Ran out of fuel while reading a partial map"
  else
    throwError s!"{e} is not a partial map"

/-- Reflect a `PMap` value from its `Expr` representation `e`. -/
def getLabelMapFromMapExpr (e : Expr) : MetaM LabelMap :=
  getLabelMapFromMapExprAux (exprDepthBound e) e


/-- Reflect the `LabelMap` value out of an `Expr` of type `Code`. -/
def getLabelMapFromCodeExpr (e : Expr): MetaM LabelMap := do
  let e ← Meta.whnf e
  if e.isAppOfArity ``Code.mk 2 then
    let labelMapExpr ← Meta.whnf <| e.getArg! 2
    return ← getLabelMapFromMapExpr labelMapExpr
  throwError s!"{e} is no Expr of type Code!"



/--
Recursively search through a TMap Expr to find the Instr at the given line number.

This helper function navigates through the nested TMap.put structure to locate
the instruction at the specified program counter position.
The `fuel` argument bounds the recursion over the expression.
-/
private def getInstrExprFromMapExprAux (fuel : Nat) (mapExpr : Expr) (pc : UInt64) :
    MetaM Expr := do
  let mapExpr ← Meta.whnf mapExpr
  if mapExpr.isAppOfArity ``TMap.empty 3 then
    -- Return the panic instruction (default)
    return mkAppN (mkConst `Instr.Panic []) #[]
  else if mapExpr.isAppOfArity ``TMap.put 5 then
    let lineExpr ← Meta.whnf <| mapExpr.getArg! 2
    let line ← getUInt64FromExpr lineExpr
    if line = pc then
      -- Found the instruction at this line
      return ← Meta.whnf <| mapExpr.getArg! 3
    else
      -- Continue searching in the rest of the map
      match fuel with
      | fuel + 1 => return ← getInstrExprFromMapExprAux fuel (mapExpr.getArg! 4) pc
      | 0 => throwError "Ran out of fuel while searching a TMap expression"
  else
    throwError s!"Expected a TMap expression, got {mapExpr}"

/-- Look up the instruction expression at line `pc` in the map expression `mapExpr`. -/
private def getInstrExprFromMapExpr (mapExpr : Expr) (pc : UInt64) : MetaM Expr :=
  getInstrExprFromMapExprAux (exprDepthBound mapExpr) mapExpr pc


/--
Extract an Instr from a Code.mk Expr given a program counter value.

This function takes an Expr of type Code.mk and a program counter (UInt64),
and returns the Expr of the Instr at that program counter position.
-/
def getInstrFromCodeExpr (codeExpr : Expr) (pc : UInt64) : MetaM Expr := do
  let codeExpr ← Meta.whnf codeExpr
  if codeExpr.isAppOfArity ``Code.mk 2 then
    let instrMapExpr := codeExpr.getArg! 0
    return ← getInstrExprFromMapExpr instrMapExpr pc
  else
    throwError "Expected an Expr of type Code"


/-- Interpret the first `n` arguments as `UInt64` values, throwing otherwise. -/
def getArgsAsUIntsOrThrow (args : Array Expr) (n : Nat) : MetaM (List UInt64) := do
  if args.size < n then
    throwError "Expected at least {n} arguments, got {args.size}"
  (List.range n).mapM fun i => getUInt64FromExpr (args[i]!)

/-- Interpret two argument expressions as a pair of `UInt64` values. -/
def getTwoUIntFromExprValidated (args : Array Expr) : MetaM (UInt64 × UInt64) := do
  if args.size < 2 then
    throwError "Expected at least 2 arguments, got {args.size}"
  return (←getUInt64FromExpr args[0]!, ←getUInt64FromExpr args[1]!)

/-- Interpret three argument expressions as a triple of `UInt64` values. -/
def getThreeUIntFromExprValidated (args : Array Expr) : MetaM (UInt64 × UInt64 × UInt64) := do
  if args.size < 3 then
    throwError "Expected at least 3 arguments, got {args.size}"
  return (←getUInt64FromExpr args[0]!, ←getUInt64FromExpr args[1]!, ←getUInt64FromExpr args[2]!)

/-- Interpret two argument expressions as a `UInt64` and a `String`. -/
def getUIntStringFromExprValidated (args : Array Expr) : MetaM (UInt64 × String) := do
  if args.size < 2 then
    throwError "Expected at least 2 arguments, got {args.size}"
  return (←getUInt64FromExpr args[0]!, ←getStrFromExpr args[1]!)

/-- Interpret three argument expressions as two `UInt64` values and a `String`. -/
def getTwoUIntOneStringFromExprValidated (args : Array Expr) :
    MetaM (UInt64 × UInt64 × String) := do
  if args.size < 3 then
    throwError "Expected at least 3 arguments, got {args.size}"
  return (←getUInt64FromExpr args[0]!, ←getUInt64FromExpr args[1]!, ←getStrFromExpr args[2]!)

/-- Reflect the `Instr` value out of an `Expr`. -/
def getInstrFromExpr (e : Expr) : MetaM Instr := do
  let e ← Meta.whnf e
  if e.isAppOfArity ``Instr.LoadAddress 2 then
    let (reg, addr) ← getTwoUIntFromExprValidated e.getAppArgs
    return Instr.LoadAddress reg addr
  if e.isAppOfArity ``Instr.LoadImmediate 2 then
    let (reg, val) ← getTwoUIntFromExprValidated e.getAppArgs
    return Instr.LoadImmediate reg val
  if e.isAppOfArity ``Instr.CopyRegister 2 then
    let (dst, src) ← getTwoUIntFromExprValidated e.getAppArgs
    return Instr.CopyRegister dst src
  if e.isAppOfArity ``Instr.AddImmediate 3 then
    let (dst, reg, val) ← getThreeUIntFromExprValidated e.getAppArgs
    return Instr.AddImmediate dst reg val
  if e.isAppOfArity ``Instr.Increment 1 then
    let dst ←getUInt64FromExpr e.getAppArgs[0]!
    return Instr.Increment dst
  if e.isAppOfArity ``Instr.AddRegister 3 then
    let (dst, reg1, reg2) ← getThreeUIntFromExprValidated e.getAppArgs
    return Instr.AddRegister dst reg1 reg2
  if e.isAppOfArity ``Instr.SubImmediate 3 then
    let (dst, reg, val) ← getThreeUIntFromExprValidated e.getAppArgs
    return Instr.SubImmediate dst reg val
  if e.isAppOfArity ``Instr.Decrement 1 then
    let dst ←getUInt64FromExpr e.getAppArgs[0]!
    return Instr.Decrement dst
  if e.isAppOfArity ``Instr.SubRegister 3 then
    let (dst, reg1, reg2) ← getThreeUIntFromExprValidated e.getAppArgs
    return Instr.SubRegister dst reg1 reg2
  if e.isAppOfArity ``Instr.XorImmediate 3 then
    let (dst, reg, val) ← getThreeUIntFromExprValidated e.getAppArgs
    return Instr.XorImmediate dst reg val
  if e.isAppOfArity ``Instr.XOR 3 then
    let (dst, reg1, reg2) ← getThreeUIntFromExprValidated e.getAppArgs
    return Instr.XOR dst reg1 reg2
  if e.isAppOfArity ``Instr.LoadWordImmediate 2 then
    let (dst, reg) ← getTwoUIntFromExprValidated e.getAppArgs
    return Instr.LoadWordImmediate dst reg
  if e.isAppOfArity ``Instr.LoadWordReg 2 then
    let (dst, reg) ← getTwoUIntFromExprValidated e.getAppArgs
    return Instr.LoadWordReg dst reg
  if e.isAppOfArity ``Instr.StoreWord 2 then
    let (reg, dst) ← getTwoUIntFromExprValidated e.getAppArgs
    return Instr.StoreWord reg dst
  if e.isAppOfArity ``Instr.Jump 1 then
    let label ← getStrFromExpr e.getAppArgs[0]!
    return Instr.Jump label
  if e.isAppOfArity ``Instr.JumpEq 3 then
    let (reg1, reg2, label) ← getTwoUIntOneStringFromExprValidated e.getAppArgs
    return Instr.JumpEq reg1 reg2 label
  if e.isAppOfArity ``Instr.JumpNeq 3 then
    let (reg1, reg2, label) ← getTwoUIntOneStringFromExprValidated e.getAppArgs
    return Instr.JumpNeq reg1 reg2 label
  if e.isAppOfArity ``Instr.JumpGt 3 then
    let (reg1, reg2, label) ← getTwoUIntOneStringFromExprValidated e.getAppArgs
    return Instr.JumpGt reg1 reg2 label
  if e.isAppOfArity ``Instr.JumpLe 3 then
    let (reg1, reg2, label) ← getTwoUIntOneStringFromExprValidated e.getAppArgs
    return Instr.JumpLe reg1 reg2 label
  if e.isAppOfArity ``Instr.JumpEqZero 2 then
    let (reg, label) ← getUIntStringFromExprValidated e.getAppArgs
    return Instr.JumpEqZero reg label
  if e.isAppOfArity ``Instr.JumpNeqZero 2 then
    let (reg, label) ← getUIntStringFromExprValidated e.getAppArgs
    return Instr.JumpNeqZero reg label
  return Instr.Panic

/-- Fuel-bounded core of `getInstrMapFromExpr`; `fuel` bounds the recursion. -/
private def getInstrMapFromExprAux (fuel : Nat) (e : Expr) : MetaM InstructionMap := do
  let e ← Meta.whnf e
  if e.isAppOfArity ``TMap.empty 3 then
    return TMap.empty Instr.Panic
  else if e.isAppOfArity ``TMap.put 5 then
    let line ← getUInt64FromExpr <| ← Meta.whnf <| e.getArg! 2
    let instr_expr ← Meta.whnf <| e.getArg! 3
    let instr ← getInstrFromExpr instr_expr
    match fuel with
    | fuel + 1 => return TMap.put line instr (←getInstrMapFromExprAux fuel (e.getArg! 4))
    | 0 => throwError "Ran out of fuel while reading a TMap expression"
  else
    throwError s!"{e} is not a partial map"

/-- Reflect an `InstructionMap` value from its `Expr` representation `e`. -/
def getInstrMapFromExpr (e : Expr) : MetaM InstructionMap :=
  getInstrMapFromExprAux (exprDepthBound e) e


/-- Reflect the `InstructionMap` value out of an `Expr` of type `Code`. -/
def getInstrMapFromCodeExpr (e : Expr) : MetaM InstructionMap := do
  let e ← Meta.whnf e
  if e.isAppOfArity ``Code.mk 2 then
    return ← getInstrMapFromExpr (e.getArg! 0)
  throwError "Expected an Expr of type Code"

/--
Each parameter of a lambda function returns the function itself when `bindingBody!`.
So we traverse those "body's", until we hit the actual body
-/
private def getLambdaBody (e : Expr) (fuel : Nat) : MetaM Expr := do
  let e ← Meta.whnf e
  if !e.isLambda then
    return e
  match fuel with
  | 0 => throwError "There might be too many arguments in this function or an error occurred
                        during the extraction of the function body"
  | Nat.succ n' => do return ← getLambdaBody e.bindingBody! n'

/--
Return the actual binding body from a lambda function.
-/
def getCodeExprFromLambda (e : Expr) : MetaM Expr := do
  let e ← Meta.whnf e
  let ty ← inferType e
  if !e.isLambda then
    throwError m!"{e} is not a function!"
  else if (ty.getForallBody != (Expr.const `Code [])) then
    throwError s!"{e} is not a function which returns a Code"
  let FUEL := 100
  return ←getLambdaBody e FUEL

/-- Fuel-bounded core of `splitConjDisj`; `fuel` bounds the recursion. -/
private def splitConjDisjAux (fuel : Nat) (declType : Expr) :
    MetaM (TSyntax `rcasesPat) := do
  let e ← Meta.whnf declType
  match fuel with
  | fuel + 1 =>
    if e.isAppOfArity `Or 2 then
      let left ← splitConjDisjAux fuel (←Meta.whnf <| e.getArg! 0)
      let right ← splitConjDisjAux fuel (←Meta.whnf <| e.getArg! 1)
      return (←`(rcasesPat | ($left | $right)))
    if e.isAppOfArity `And 2 then
      let left ← splitConjDisjAux fuel (←Meta.whnf <| e.getArg! 0)
      let right ← splitConjDisjAux fuel (←Meta.whnf <| e.getArg! 1)
      return (←`(rcasesPat | ⟨$left , $right⟩))
    if e.isFVar then
      return (←`(rcasesPat | _))
    if e.isArrow then
      let arr? := e.arrow?
      match arr? with
      | some (_, _) =>
        return (←`(rcasesPat | _))
      | none =>
        throwError s!"{e} is an implication but theres missing an expr"
    return (←`(rcasesPat | _))
  | 0 => return (←`(rcasesPat | _))

/-- Split a conjunction/disjunction type `declType` into a matching `rcases` pattern. -/
def splitConjDisj (declType : Expr) : MetaM (TSyntax `rcasesPat) :=
  splitConjDisjAux (exprDepthBound declType) declType


/-- Evaluate a singleton argument expression to the `UInt64` it denotes. -/
def parseSingletonExpr (e : Expr) : MetaM (UInt64) := do
  if e.isAppOfArity ``Singleton.singleton 4 then
    let nRaw? := ((e.getArg! 3).getArg! 1).rawNatLit?
    match nRaw? with
    | some n => return UInt64.ofNat n
    | none => do throwError s!"Used the wrong argument to get UInt64 from Expr to create L_w' " ++
                    "from Expr"
  -- TODO: Solve Addition
  else
    throwError s!"It seems like {e} is not in correct shape. Please confirm that the whitelist " ++
      "consists of only one element like so: {1}"
