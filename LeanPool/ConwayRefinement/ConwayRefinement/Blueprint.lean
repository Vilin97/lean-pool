/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/

module

public import Lean
public meta import Batteries.Lean.NameMapAttribute

/-! # Blueprint -/

public meta section

open Lean Elab Command

namespace ConwayRefinement.Blueprint

/-- Mathematical phases used by the generated proof map. -/
meta def phases : Array String := #[
  "Algebraic and ordinal preliminaries",
  "Ordinal value and degree",
  "Cantor–Bendixson ranks of supports",
  "Algebraic independence in graded rings",
  "Translated truncations",
  "Limit ordinals in the degree induction",
  "Principal RV-elements",
  "Polynomial presentations",
  "Primality and factorisation for real exponents",
  "Finitely many Archimedean classes",
  "Refinement over Archimedean classes",
  "A cut criterion for Cauchy completeness",
  "Bounded generalised-power-series integer parts",
  "Surreal numbers and omnific integers",
]

/-- The mathematical account attached to one selected Lean declaration. -/
structure Node where
  name : Name
  label : String
  phase : String
  title : String
  statement : String
  proof : String
  highlight : Bool := false
deriving Inhabited, ToExpr

/-- Checked blueprint metadata, persisted with each compiled module. -/
initialize nodeExt : NameMapExtension Node ← registerNameMapExtension Node

syntax blueprintPhaseOption := "(" &"phase" " := " str ")"
syntax blueprintTitleOption := "(" &"title" " := " str ")"
syntax blueprintStatementOption := "(" &"statement" " := " plainDocComment ")"
syntax blueprintProofOption := "(" &"proof" " := " plainDocComment ")"
syntax blueprintHighlightOption := "(" &"highlight" ")"
syntax blueprintOptions :=
  str ppSpace blueprintPhaseOption ppSpace blueprintTitleOption
    ppSpace blueprintStatementOption ppSpace blueprintProofOption
    (ppSpace blueprintHighlightOption)?

/-- Internal attribute implementing proof-map metadata. -/
syntax (name := conwayRefinementBlueprint) "conway_refinement_blueprint" ppSpace
  blueprintOptions : attr

/-- Select a declaration for the mathematical proof map. -/
macro "blueprint" ppSpace options:blueprintOptions : attr =>
  `(attr| conway_refinement_blueprint $options:blueprintOptions)

def resultKindForLabel (label : String) : CoreM Unit := do
  unless #["def:", "thm:", "lem:", "prop:", "cor:", "fact:"].any
      (fun resultPrefix => label.startsWith resultPrefix) do
    throwError "blueprint label {label} has no recognized mathematical result kind"

def elaborateNode (name : Name) : Syntax → CoreM Node
  | `(attr| conway_refinement_blueprint $label:str
      (phase := $phase:str)
      (title := $title:str)
      (statement := $statement)
      (proof := $proof)
      $[$highlight:blueprintHighlightOption]?) => do
    let label := label.getString
    let phase := phase.getString
    unless phases.contains phase do
      throwError "unknown proof-map phase {phase}"
    resultKindForLabel label
    return {
      name
      label
      phase
      title := title.getString
      statement := (← getDocStringText statement).trimAscii.copy
      proof := (← getDocStringText proof).trimAscii.copy
      highlight := highlight.isSome
    }
  | _ => throwUnsupportedSyntax

initialize registerBuiltinAttribute {
  name := `conwayRefinementBlueprint
  descr := "selects a declaration for the mathematical proof map"
  applicationTime := .afterCompilation
  add := fun name stx kind => do
    unless kind == AttributeKind.global do
      throwError "invalid attribute 'blueprint', must be global"
    nodeExt.add name (← elaborateNode name stx)
}

private structure CollectContext where
  environment : Environment
  root : Name

private structure CollectState where
  visited : NameSet := {}
  selected : NameSet := {}

private abbrev CollectM := ReaderT CollectContext (StateM CollectState)

private def collectSelected : Nat → Name → CollectM Unit
  | 0, _ => pure ()
  | fuel + 1, name => do
    let state ← get
    unless state.visited.contains name do
      modify fun state => { state with visited := state.visited.insert name }
      let { environment, root } ← read
      if name != root && (nodeExt.find? environment name).isSome then
        modify fun state => { state with selected := state.selected.insert name }
      else
        let collectExpression (expression : Expr) : CollectM Unit :=
          expression.getUsedConstants.forM (collectSelected fuel)
        match environment.find? name with
        | some (.axiomInfo _) => pure ()
        | some (.defnInfo value) => collectExpression value.type *> collectExpression value.value
        | some (.thmInfo value) => collectExpression value.type *> collectExpression value.value
        | some (.opaqueInfo value) => collectExpression value.type *> collectExpression value.value
        | some (.quotInfo _) => pure ()
        | some (.ctorInfo value) => collectExpression value.type
        | some (.recInfo value) => collectExpression value.type
        | some (.inductInfo value) =>
            collectExpression value.type *> value.ctors.forM (collectSelected fuel)
        | none => pure ()

private def declarationType : ConstantInfo → Expr
  | .axiomInfo value | .defnInfo value | .thmInfo value | .opaqueInfo value |
      .ctorInfo value | .recInfo value | .inductInfo value => value.type
  | .quotInfo value => value.type

private def declarationValue? : ConstantInfo → Option Expr
  | .defnInfo value => some value.value
  | .thmInfo value => some value.value
  | .opaqueInfo value => some value.value
  | _ => none

private def collectDependencies (environment : Environment) (root : Name) :
    NameSet × NameSet := Id.run do
  let some info := environment.find? root | return ({}, {})
  let mut statementState : CollectState := {}
  for name in (declarationType info).getUsedConstants do
    (_, statementState) := ((collectSelected (environment.constants.toList.length + 1) name).run { environment, root }).run statementState
  let mut proofState := statementState
  if let some value := declarationValue? info then
    for name in value.getUsedConstants do
      (_, proofState) := ((collectSelected (environment.constants.toList.length + 1) name).run { environment, root }).run proofState
  return (statementState.selected, proofState.selected \ statementState.selected)

private def namesJson (names : NameSet) : Json :=
  .arr <| names.toArray.qsort Name.lt |>.map fun name => .str name.toString

private def positionJson (position : Position) : Json := Json.mkObj [
  ("line", position.line),
  ("column", position.column)
]

private def rangeJson (range : DeclarationRange) : Json := Json.mkObj [
  ("start", positionJson range.pos),
  ("end", positionJson range.endPos)
]

private def moduleOf (environment : Environment) (name : Name) : Name :=
  match environment.getModuleIdxFor? name with
  | some index => environment.allImportedModuleNames[index.toNat]!
  | none => environment.header.mainModule

private def nodeJson (node : Node) : CoreM Json := do
  let environment ← getEnv
  let moduleName := moduleOf environment node.name
  let range ← findDeclarationRanges? node.name
  let (statementDependencies, proofDependencies) :=
    collectDependencies environment node.name
  return Json.mkObj [
    ("name", node.name.toString),
    ("label", node.label),
    ("phase", node.phase),
    ("title", node.title),
    ("statement", node.statement),
    ("proof", node.proof),
    ("highlight", node.highlight),
    ("module", moduleName.toString),
    ("source", s!"{moduleName.toString.replace "." "/"}.lean"),
    ("range", range.map (fun ranges => rangeJson ranges.range) |>.getD Json.null),
    ("statementDependencies", namesJson statementDependencies),
    ("proofDependencies", namesJson proofDependencies)
  ]

private def blueprintJson : CoreM Json := do
  let environment ← getEnv
  let entries := (nodeExt.getState environment).get.toList.toArray
  let nodes := entries.map (·.2) |>.qsort fun left right =>
    left.name.toString < right.name.toString
  return .arr (← nodes.mapM nodeJson)

/-- Write checked blueprint metadata for the currently imported modules. -/
elab "#write_blueprint_data" path:str : command => do
  let json ← liftCoreM blueprintJson
  IO.FS.writeFile path.getString json.pretty

end ConwayRefinement.Blueprint
