/-
Copyright (c) 2026 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
module

import Mathlib.Tactic.Convert

import Mathlib.Tactic.FinCases

import LeanPool.SetTheory.SimpAttr

public import LeanPool.SetTheory.RealizeCore

/-!
# Generating realization companion declarations

Build the formula, realization, and elementarity declarations registered by `@[realize]`.
The expression representation and its correctness lemmas live in `RealizeCore`.
-/

@[expose] public section

open Lean Parser Elab Term Meta Qq Std FirstOrder.Language

namespace BuildFormula

/-- The `classIdents` declaration. -/
def classIdents (typeLetter := "M") : BuildFormulaM (Array Ident) := do
  return (*...(← classParams).size).toArray.map
    fun i => mkIdent ("c" ++ typeLetter ++ (i + 1).toSubscriptString).toName

/-- The `varIdents` declaration. -/
def varIdents (adjust? := false) (varLetter := "x") : BuildFormulaM (Array Ident) := do
  return (Array.range (← numFreeVars adjust?)).map
    fun i => mkIdent (Name.mkStr1 (varLetter ++ (i + 1).toSubscriptString))

/-- The `hypothesisIdents` declaration. -/
def hypothesisIdents (hypothesisLetter := "h") : BuildFormulaM (Array Ident) := do
  return (Array.range (← numHypotheses)).map
    fun i => mkIdent (Name.mkStr1 (hypothesisLetter ++ (i + 1).toSubscriptString))

/-- The `identsBefore` declaration. -/
def identsBefore (i : Nat) (typeLetter := "M") (varLetter := "x") :
    BuildFormulaM (Array Ident) := do
  return prefixIdents typeLetter ++ (← classIdents typeLetter) ++
    (← varIdents false varLetter)[*...i]

/-- The `allIdentsWithHypotheses` declaration. -/
def allIdentsWithHypotheses
    (typeLetter := "M") (varLetter := "x") (hypothesisLetter := "h") :
    BuildFormulaM (Array Ident) := do
  let vars ← varIdents false varLetter
  let hypotheses ← hypothesisIdents hypothesisLetter
  let mut result := prefixIdents typeLetter ++ (← classIdents typeLetter)
  let mut (i, j) := (0, 0)
  for p in (← variableParams) do
    match p with
    | .freeVariable _ => result := result.push vars[i]!; i := i + 1
    | .hypothesis _ => result := result.push hypotheses[j]!; j := j + 1
  return result

/-- The `classParamBinders` declaration. -/
def classParamBinders (typeLetter : String := "M") :
    BuildFormulaM (TSyntaxArray ``bracketedBinder) := do
  let typeIdent := mkIdent typeLetter.toName
  let structIdent := mkIdent ("s" ++ typeLetter).toName
  return #[
    ← `(bracketedBinder | {$typeIdent : Type _}),
    ← `(bracketedBinder | [$structIdent : $(mkCIdent ``ZFStructure) $typeIdent])
  ] ++ (
  ← if (← isFunction) && (← numHypotheses) > 0 && !(← hasEmptyInstanceState) then
      pure #[← `(bracketedBinder | [$(mkCIdent ``HasEmpty) $typeIdent])]
    else
      pure #[]
  ) ++ (
  ← ((← classParams).zip (← classIdents typeLetter)).mapM
      fun (cls, id) => `(bracketedBinder | [$id : headBeta($cls $typeIdent $structIdent)])
  )

/-- The `mkBinders` declaration. -/
def mkBinders (adjust? := false) (typeLetter : String := "M") (varLetter : String := "x") :
    BuildFormulaM (TSyntaxArray ``bracketedBinder) := do
  let typeIdent := mkIdent typeLetter.toName
  (← varIdents adjust? varLetter).mapM fun var => `(bracketedBinder | ($var : $typeIdent))

/-- The `mkTermApp` declaration. -/
def mkTermApp (x : Term) (xs : Array Term) : BuildFormulaM Term :=
  `(headBeta($(Syntax.mkApp x xs)))

/-- The `mkParam` declaration. -/
def mkParam (i : Nat) (typeLetter : String := "M") (varLetter : String := "x") :
    BuildFormulaM Term := do
  mkTermApp (← getHypothesis i) (← identsBefore (← freeVarsBefore i) typeLetter varLetter)

/-- The `mkBindersWithHypotheses` declaration. -/
def mkBindersWithHypotheses
    (typeLetter : String := "M") (varLetter : String := "x") (hypothesisLetter := "h") :
    BuildFormulaM (TSyntaxArray ``bracketedBinder) := do
  let typeIdent := mkIdent typeLetter.toName
  let vars ← varIdents false varLetter
  let hypotheses ← hypothesisIdents hypothesisLetter
  let mut result := #[]
  let mut (i, j) := (0, 0)
  for p in (← variableParams) do
    match p with
    | .freeVariable info =>
      let v := vars[i]!
      result := result.push <| ← do
        match info with
        | .default => `(bracketedBinder | ($v : $typeIdent))
        | .implicit => `(bracketedBinder | {$v : $typeIdent})
        | .strictImplicit => `(bracketedBinder | ⦃$v : $typeIdent⦄)
        | .instImplicit => `(bracketedBinder | [$v : $typeIdent])
      i := i + 1
    | .hypothesis _ =>
      let param ← mkParam j typeLetter varLetter
      result := result.push <| ← `(bracketedBinder | ($(hypotheses[j]!) : $param))
      j := j + 1
  return result

/-- The `mkIdent'` declaration. -/
def mkIdent' (name : Name) : Ident := mkIdent (`_root_ ++ name)

/-- The `buildFunction` declaration. -/
def buildFunction (funcName : Name) : BuildFormulaM Unit := do
  let funcIdent := mkIdent' funcName
  let euIdent := mkIdent' ((← name) ++ `eu)
  let specIdent := mkIdent' ((← name) ++ `spec)
  let eqIffIdent := mkIdent' ((← name) ++ `eq_iff)
  let hyps ← hypothesisIdents "h"
  let euApply := Syntax.mkApp (← `(@$euIdent)) (← allIdentsWithHypotheses)
  let mut value ← `(Exists.choose $euApply)
  for i in (*...(← numHypotheses)).toArray.reverse do
    let param ← mkParam i
    value ← `(if $(hyps[i]!):ident : $param then $value else ∅)
  let fnApply := Syntax.mkApp funcIdent (← varIdents)
  let statement ← (explicitize (← definitionProp) ((← numAllVars) + 1)).toSyntax'
  let vars : Array Term ← allIdentsWithHypotheses
  let specStatement ← mkTermApp statement (vars.push fnApply)
  let identV := mkIdent `v
  let eqIffStatement ← mkTermApp statement (vars.push identV)
  let classParamBinders ← classParamBinders
  let mkBinders ← mkBinders
  let mkBindersWithHypotheses ← mkBindersWithHypotheses
  let identM := mkIdent `M
  -- When the function definition carries hypotheses, its body is a nested `dite`, so the
  -- proof must unfold the function and reduce the `dite` before applying `choose_spec`.
  -- Without hypotheses the body is a bare `Exists.choose`, defeq to the goal, so `exact`
  -- suffices (and `simp only` on the function would otherwise make no progress and fail).
  let specProof ← if (← numHypotheses) == 0 then
      `(tactic| exact $(euApply).choose_spec.1)
    else
      `(tactic| simpa only [$funcIdent:term, *, ↓reduceDIte] using $(euApply).choose_spec.1)
  let eqIffProof ← if (← numHypotheses) == 0 then
      `(tactic| exact $(euApply).choose_eq_iff)
    else
      `(tactic| simpa only [$funcIdent:term, *, ↓reduceDIte] using $(euApply).choose_eq_iff)
  let cmd ← `(
  open Classical in
  /-- The set-theoretic function automatically realized from its defining property. -/
  @[expose] public noncomputable def $funcIdent $classParamBinders* $mkBinders* : $identM :=
    $value
  public lemma $specIdent $classParamBinders* $mkBindersWithHypotheses* :
      $specStatement := by
    $specProof:tactic
  public lemma $eqIffIdent $classParamBinders* $mkBindersWithHypotheses* ($identV : $identM) :
      $fnApply = $identV ↔ $eqIffStatement := by
    $eqIffProof:tactic
  )
  liftCommandElabM (Command.elabCommand cmd)

/-- The `realizedTerm` declaration. -/
def realizedTerm (typeLetter := "M") : BuildFormulaM Term := do
  let realizedIdent := mkIdent' (← name)
  if (← numFreeVars) == 0 then
    let n ← forallTelescopeReducing
      ((← getEnv).find? (← name) |>.get! |>.type)
      fun vars _ => pure vars.size
    return Syntax.mkApp (← `(@$realizedIdent)) <|
      #[(mkIdent typeLetter.toName : Term)] ++ Array.replicate (n - 1) (← `(_))
  else
    `($realizedIdent)

/-- The `buildRealizeIff` declaration. -/
def buildRealizeIff (thmName : Name) : BuildFormulaM Unit := do
  let realizedIdent := mkIdent' (← name)
  let formulaIdent := mkIdent' ((← name) ++ `formula)
  let thmIdent := mkIdent' thmName
  let mut realizedApplyV ← realizedTerm
  for i in *...(← numFreeVars) do
    realizedApplyV ← `($realizedApplyV (v $(Syntax.mkNatLit i)))
  let mut realizedApplyV' := realizedApplyV
  if ← isFunction then
    realizedApplyV' ← `($realizedApplyV = v $(Syntax.mkNatLit (← numFreeVars)))
  let nVars := Syntax.mkNatLit (← numFreeVars true)
  let identM := mkIdent `M
  let cmd ← `(
  attribute [local implicit_reducible] ExistsUnique in
  @[realize_simps] public lemma $thmIdent
      $(← classParamBinders)* (v : Fin $nVars → $identM) :
      FirstOrder.Language.Formula.Realize $formulaIdent v ↔ $realizedApplyV' := by
    simp only [$formulaIdent:term, $realizedIdent:term, formula_builder_pre, formula_builder,
      FirstOrder.Language.Formula.Realize, ExistsUnique.choose_eq_iff, dite_eq_iff, exists_prop]
    simp (config := {unfoldPartialApp := true}) only [realize_simps]
    simp (config := {unfoldPartialApp := true, decide := true}) only [
      realize_simps, FirstOrder.Language.BoundedFormula.realize_isFormula,
      Fin.isValue, Fin.reduceLast, Matrix.cons_val, Sum.elim_inl, Sum.elim_inr,
      Fin.snoc, reduceDIte, cast_eq
    ]
  )
  liftCommandElabM (Command.elabCommand cmd)

/-- The `buildInstFormulaToFunction` declaration. -/
def buildInstFormulaToFunction (instName : Name) := do
  let formulaIdent := mkIdent' ((← name) ++ `formula)
  let instIdent := mkIdent' instName
  let mut realizedApplyV : Term ← realizedTerm
  for i in *...(← numFreeVars) do
    realizedApplyV ← `($realizedApplyV (v $(Syntax.mkNatLit i)))
  let nVars := Syntax.mkNatLit (← numFreeVars)
  let identM := mkIdent `M
  let cmd ← `(
  public instance $instIdent:ident $(← classParamBinders)* :
    FormulaToFunction $formulaIdent (fun v : Fin $nVars → $identM => $realizedApplyV) where
  )
  liftCommandElabM (Command.elabCommand cmd)

/-- The `mkVarVec` declaration. -/
def mkVarVec (typeLetter := "M") (varLetter : String := "x") : BuildFormulaM Term := do
  let vars ← varIdents true varLetter
  let mut varVec ← `(@$(mkCIdent ``Matrix.vecEmpty) $(mkIdent typeLetter.toName))
  for var in vars.reverse do
    varVec ← `($(mkCIdent ``Matrix.vecCons) $var $varVec)
  return varVec

/-- The `buildToRealize` declaration. -/
def buildToRealize (toRealizeName : Name) : BuildFormulaM Unit := do
  let formulaIdent := mkIdent' ((← name) ++ `formula)
  let toRealizeIdent := mkIdent' toRealizeName
  let vars ← varIdents true
  let mut applyX := Syntax.mkApp (← realizedTerm) vars[*...(← numFreeVars)]
  if ← isFunction then
    applyX ← `($applyX = $(vars[← numFreeVars]!))
  let cmd ← `(
  public lemma $toRealizeIdent $((← classParamBinders) ++ (← mkBinders true))* :
      $applyX ↔ $(mkCIdent ``FirstOrder.Language.Formula.Realize) $formulaIdent $(← mkVarVec) := by
    simp only [realize_simps, Matrix.cons_val, *]
  )
  liftCommandElabM (Command.elabCommand cmd)

/-- The `buildElementarity` declaration. -/
def buildElementarity (elementarityName : Name) : BuildFormulaM Unit := do
  let formulaIdent := mkIdent' ((← name) ++ `formula)
  let toRealizeIdent := mkIdent' ((← name) ++ `to_realize)
  let elementarityIdent := mkIdent' elementarityName
  let vars ← varIdents
  let identM := mkIdent `M
  let identN := mkIdent `N
  let identF := mkIdent `F
  let identJ := mkIdent `j
  let funLike := mkCIdent ``FunLike
  let eecClass := mkCIdent ``ElementaryEmbeddingClass
  let mapFormula := mkCIdent ``ElementaryEmbeddingClass.map_formula
  let vecCons := mkCIdent ``Matrix.vecCons
  let vecEmpty := mkCIdent ``Matrix.vecEmpty
  let realizeFn := mkCIdent ``FirstOrder.Language.Formula.Realize
  let mut applyJX ← realizedTerm "N"
  let mut applyX ← realizedTerm "M"
  for var in vars do
    applyJX ← `($applyJX ($identJ $var))
    applyX ← `($applyX $var)
  let cmd ← do
    if ← isFunction then
      let mut varVecSnocApply ← `($vecCons $applyX $vecEmpty)
      for var in vars.reverse do
        varVecSnocApply ← `($vecCons $var $varVecSnocApply)
      let convertTarget ← `($realizeFn $formulaIdent ($identJ ∘ $varVecSnocApply))
      let mapFormulaApp ← `($mapFormula $identJ)
      `(
      @[elementary_simps] public lemma $elementarityIdent
          $((← classParamBinders "M") ++ (← classParamBinders "N") ++ (← mkBinders false "M"))*
          {$identF : Type*} [$funLike $identF $identM $identN]
          [$eecClass $identF $identM $identN] ($identJ : $identF) :
          $applyJX = $identJ ($applyX) := by
        simp only [$toRealizeIdent:term]
        convert_to ($convertTarget) using 1
        · ext1 i; fin_cases i <;> rfl
        · simp only [$mapFormulaApp:term, ← $toRealizeIdent:term]
      attribute [elementary_simps_rev ←] $elementarityIdent
      )
    else
      let convertTerm ← `($mapFormula $identJ $formulaIdent $(← mkVarVec))
      `(
      @[elementary_simps] public lemma $elementarityIdent
          $((← classParamBinders "M") ++ (← classParamBinders "N") ++ (← mkBinders false "M"))*
          {$identF : Type*} [$funLike $identF $identM $identN]
          [$eecClass $identF $identM $identN] ($identJ : $identF) :
          $applyJX ↔ $applyX := by
        simp only [$toRealizeIdent:term]
        convert ($convertTerm) using 2
        ext1 i; fin_cases i <;> rfl
      attribute [elementary_simps_rev ←] $elementarityIdent
      )
  liftCommandElabM (Command.elabCommand cmd)

/-- The `runIfNotFound` declaration. -/
def runIfNotFound (names : List Name) (f : Name → BuildFormulaM Unit) : BuildFormulaM Unit := do
  if (← getEnv).contains names[0]! then return else f names[0]!
  for name in names do
    checkSorry name

/-- Build all the `Formula.Realize` companion declarations for the decl `attrDeclName`
tagged with `@[realize]`. -/
def realizeAttrAdd (attrDeclName : Name) : AttrM Unit := do
  let name := removeNameSuffix attrDeclName
  let go : BuildFormulaM Unit := do
    init
    if (← isFunction) then
      runIfNotFound [name, name ++ `spec, name ++ `eq_iff] buildFunction
    runIfNotFound [name ++ `formula] buildFormula
    runIfNotFound [name ++ `realize_iff] buildRealizeIff
    if (← isFunction) then
      runIfNotFound [name ++ `instFormulaToFunction] buildInstFormulaToFunction
    runIfNotFound [name ++ `to_realize] buildToRealize
    runIfNotFound [name ++ `elementarity] buildElementarity
  go.run' { attrDeclName } |>.run'

end BuildFormula

initialize
  registerBuiltinAttribute {
    name            := `realize
    descr           := "Automatically build `Formula.Realize` theorems"
    applicationTime := .afterCompilation
    add             := fun declName _ _ => BuildFormula.realizeAttrAdd declName
  }
