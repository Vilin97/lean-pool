/-
Copyright (c) 2022 Mario Carneiro, 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Egor Lyfar
-/

import Lean.Elab.Command
import LeanPool.Erdos97ConvexOctagon.LRAT.Format
import LeanPool.Erdos97ConvexOctagon.MasterFormula

/-!
# Safe elaboration of the packed master LRAT certificate

Adapted from `Mathlib/Tactic/Sat/FromLRAT.lean` (Apache-2.0).  The
reconstruction reads typed project data, reconstructs unit propagation, and
stores every retained nonempty addition as a stable internal theorem so later
modules cross an ordinary imported-constant boundary.
-/

namespace Erdos97Octagon.LRAT

open Lean Elab Command
open Std

/-- Fuel for decoding one generated list of at most 500 string literals. -/
def embeddedCertificatePartFuel : ℕ := 640

/--
Exact maximum number of compiled expression nodes traversed while decoding a
committed generated certificate part.
-/
def embeddedCertificatePartMaximumExpressionSteps : ℕ := 616

instance : ToExpr Literal where
  toTypeExpr := mkConst ``Literal
  toExpr
    | .positive index => mkApp (mkConst ``Literal.positive) (mkRawNatLit index)
    | .negative index => mkApp (mkConst ``Literal.negative) (mkRawNatLit index)

/-- A proved clause in the elaborator database. -/
private structure GlobalClause where
  literals : Array Int
  expression : Expr
  proof : Expr

/-- A referenced clause represented by a local proof variable. -/
private structure LocalClause where
  literals : Array Int
  expression : Expr
  binderDepth : ℕ

private def buildClause (literals : Array Int) : Expr :=
  let literalType := mkConst ``Literal
  let empty := mkApp (mkConst ``List.nil [0]) literalType
  let prepend := mkApp (mkConst ``List.cons [0]) literalType
  literals.foldr
    (fun literal clause =>
      mkApp2 prepend (toExpr <| Literal.ofInt literal) clause)
    empty

private def buildProofStep
    (database : HashMap ℕ GlobalClause) (newLiterals : Array Int)
    (antecedents : Array ℕ) (context clause : Expr) :
    Except String Expr := Id.run do
  let mut binderTypes := #[]
  let mut proofArguments := #[]
  let mut localDatabase : HashMap ℕ LocalClause := {}
  for identifier in antecedents do
    let some referenced := database[identifier]?
      | return .error s!"missing antecedent clause {identifier}"
    unless localDatabase.contains identifier do
      binderTypes := binderTypes.push
        (mkApp2 (mkConst ``Formula.Proves) context referenced.expression)
      proofArguments := proofArguments.push referenced.proof
      localDatabase := localDatabase.insert identifier {
        literals := referenced.literals
        expression := referenced.expression
        binderDepth := proofArguments.size
      }
  let argumentCount := proofArguments.size
  let mut finish :=
    (mkAppN · proofArguments) ∘
    binderTypes.foldr (mkLambda `clause default) ∘
    mkLambda `valuation default (mkConst ``Valuation) ∘
    mkLambda `satisfies default
      (mkApp2 (mkConst ``Valuation.SatisfiesFormula) (mkBVar 0) context)
  let valuation depth := mkBVar (depth + 1)
  let satisfies depth := mkBVar depth
  binderTypes := #[]
  let mut remainingClause := clause
  let mut depth := 0
  let mut literalContext : HashMap Int ℕ := {}
  for literal in newLiterals do
    let literalExpression := remainingClause.appFn!.appArg!
    remainingClause := remainingClause.appArg!
    binderTypes := binderTypes.push
      (mkApp2 (mkConst ``Valuation.falsifies)
        (valuation depth) literalExpression)
    depth := depth + 1
    literalContext := literalContext.insert literal depth
  finish := finish ∘ binderTypes.foldr (mkLambda `falsified default)
  for identifier in antecedents do
    let some referenced := localDatabase[identifier]?
      | return .error s!"missing local antecedent clause {identifier}"
    let mut unitLiteral : Option Int := none
    for literal in referenced.literals do
      unless literalContext.contains literal do
        if unitLiteral.isSome then
          return .error s!"antecedent {identifier} is not unit"
        depth := depth + 1
        unitLiteral := some literal
    let proofVariable :=
      mkBVar (depth + argumentCount + 2 - referenced.binderDepth)
    let mut refutation :=
      mkApp2 proofVariable (valuation depth) (satisfies depth)
    for literal in referenced.literals do
      let binderIndex :=
        match literalContext[literal]? with
        | some binderDepth => depth - binderDepth
        | none => 0
      refutation := mkApp refutation (mkBVar binderIndex)
    let some literal := unitLiteral
      | return .ok <| finish refutation
    let literalExpression := toExpr <| Literal.ofInt literal
    let negatedExpression := toExpr <| Literal.ofInt (-literal)
    let priorDepth := depth - 1
    let propagation :=
      mkApp3 (mkConst ``Valuation.propagateCases)
        (valuation priorDepth) negatedExpression <|
      mkLambda `falsified default
        (mkApp2 (mkConst ``Valuation.falsifies)
          (valuation priorDepth) literalExpression)
        refutation
    let domain :=
      mkApp2 (mkConst ``Valuation.falsifies)
        (valuation priorDepth) negatedExpression
    finish := fun expression =>
      finish <| mkApp propagation <| mkLambda `falsified default domain expression
    literalContext := literalContext.insert (-literal) depth
  return .error s!"antecedents do not refute clause {newLiterals}"

private structure DecodedStringList where
  strings : List String
  expressionSteps : ℕ

private def decodeStringListWithFuel :
    ℕ → Expr → Except String DecodedStringList
  | 0, _ => throw "embedded string list exceeds its structural bound"
  | fuel + 1, .letE _ _ value body _ => do
      let decoded ← decodeStringListWithFuel fuel (body.instantiate1 value)
      pure {
        strings := decoded.strings
        expressionSteps := decoded.expressionSteps + 1
      }
  | fuel + 1, .mdata _ expression => do
      let decoded ← decodeStringListWithFuel fuel expression
      pure {
        strings := decoded.strings
        expressionSteps := decoded.expressionSteps + 1
      }
  | fuel + 1, expression =>
      let function := expression.getAppFn
      if function.isConstOf ``List.nil then
        pure {
          strings := []
          expressionSteps := 1
        }
      else if function.isConstOf ``List.cons then
        let arguments := expression.getAppArgs
        if arguments.size ≠ 3 then
          throw "malformed embedded string list"
        else
          match arguments[1]!, decodeStringListWithFuel fuel arguments[2]! with
          | .lit (.strVal value), .ok remaining =>
              pure {
                strings := value :: remaining.strings
                expressionSteps := remaining.expressionSteps + 1
              }
          | .lit (.strVal _), .error message => throw message
          | _, _ => throw "embedded certificate part is not a literal string"
      else
        throw "embedded certificate data is not a string list"

private def readEmbeddedParts
    (declarationNames : List Name) : CommandElabM String := do
  unless embeddedCertificatePartMaximumExpressionSteps ≤
      embeddedCertificatePartFuel do
    throwError "measured string-list expression bound exceeds decoder fuel"
  let mut result := ""
  let mut measuredMaximum := 0
  for declarationName in declarationNames do
    let information ← getConstInfo declarationName
    let some value := information.value?
      | throwError "embedded certificate part has no value"
    let decoded ←
      match decodeStringListWithFuel embeddedCertificatePartFuel value with
      | .ok decoded => pure decoded
      | .error message => throwError message
    if embeddedCertificatePartMaximumExpressionSteps <
        decoded.expressionSteps then
      throwError
        "embedded string-list expression exceeds its measured maximum"
    measuredMaximum := max measuredMaximum decoded.expressionSteps
    result := result ++ String.join decoded.strings
  unless measuredMaximum =
      embeddedCertificatePartMaximumExpressionSteps do
    throwError
      "embedded string-list expression maximum does not match its committed bound"
  pure result

private def literalInteger : Literal → Int
  | .positive index => Int.ofNat (index + 1)
  | .negative index => -Int.ofNat (index + 1)

private def clauseLiterals (clause : Clause) : Array Int :=
  clause.toArray.map literalInteger

private def masterClauses : Array (Array Int) :=
  RawIncidence.masterFormula.toArray.map clauseLiterals

private def masterBaseReferences : Array ℕ :=
  RawIncidence.masterReferences.toArray

private def masterExcludedMasks : Array ℕ :=
  ((List.range 256).filter fun mask =>
    decide (RawIncidence.packedRow (UInt64.ofNat mask) ∉
      RawIncidence.canonicalRows)).toArray

private def certificateProofType (clause : Expr) : Expr :=
  mkApp2 (mkConst ``Formula.Proves)
    (mkConst ``RawIncidence.masterFormula) clause

private def certificateClauseName (baseName : Name) (identifier : ℕ) : Name :=
  Name.str baseName s!"_c{identifier}"

private def requireTheoremWithType (name : Name) (expectedType : Expr) :
    MetaM Unit := do
  let information ← getConstInfo name
  match information with
  | .thmInfo _ => pure ()
  | _ => throwError "imported certificate declaration is not a theorem: {name}"
  unless information.type == expectedType do
    throwError "imported certificate theorem has the wrong clause type: {name}"

private def truthProof : Expr :=
  mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)

private def clauseReflexivity (clause : Expr) : Expr :=
  mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Clause) clause

private def checkedSourceProof (proof clause : Expr) : MetaM Expr := do
  let inferredType ← Meta.inferType proof
  unless inferredType == certificateProofType clause do
    throwError "source-clause theorem did not infer the exact certificate clause type"
  pure proof

private def checkSourceMetadata
    (clauses : Array (Array Int)) : Except String Unit := do
  unless masterBaseReferences.size = 6333 do
    throw "master reference count does not match its committed source metadata"
  unless masterExcludedMasks.size = 249 do
    throw "excluded-row count does not match its committed source metadata"
  unless masterBaseReferences.size + masterExcludedMasks.size = clauses.size do
    throw "source metadata does not partition the master formula"
  let excludedRows := masterExcludedMasks.toList.map fun mask =>
    RawIncidence.packedRow (UInt64.ofNat mask)
  unless excludedRows == RawIncidence.excludedRows do
    throw "excluded-row masks do not match the master formula order"

private def additionIndices
    (initialClauseCount : ℕ) (additions : Array Addition) :
    Except String (HashMap ℕ ℕ) := do
  let mut indices : HashMap ℕ ℕ := {}
  let mut previous := initialClauseCount
  for index in [0:additions.size] do
    let some addition := additions[index]?
      | throw "certificate addition index is out of range"
    unless previous < addition.identifier do
      throw "certificate addition identifiers are not strictly increasing"
    if indices.contains addition.identifier then
      throw "certificate contains a duplicate addition identifier"
    indices := indices.insert addition.identifier index
    previous := addition.identifier
  pure indices

private def neededStageClauses
    (initialClauseCount start stop : ℕ) (additions : Array Addition)
    (indices : HashMap ℕ ℕ) :
    Except String (Array ℕ × Array ℕ) := do
  let mut initialSeen : HashMap ℕ Unit := {}
  let mut importedSeen : HashMap ℕ Unit := {}
  let mut initialIdentifiers := #[]
  let mut importedIdentifiers := #[]
  for index in [start:stop] do
    let some addition := additions[index]?
      | throw "certificate addition index is out of range"
    for antecedent in addition.antecedents do
      if antecedent = 0 then
        throw "certificate antecedent identifier cannot be zero"
      else if antecedent ≤ initialClauseCount then
        unless initialSeen.contains antecedent do
          initialSeen := initialSeen.insert antecedent ()
          initialIdentifiers := initialIdentifiers.push antecedent
      else
        let some antecedentIndex := indices[antecedent]?
          | throw s!"certificate antecedent {antecedent} is not a retained addition"
        unless antecedentIndex < index do
          throw s!"certificate antecedent {antecedent} is not earlier than its use"
        if antecedentIndex < start then
          unless importedSeen.contains antecedent do
            importedSeen := importedSeen.insert antecedent ()
            importedIdentifiers := importedIdentifiers.push antecedent
  pure (initialIdentifiers, importedIdentifiers)

private def sourceInitialClause
    (clauses : Array (Array Int)) (identifier : ℕ) : MetaM GlobalClause := do
  if identifier = 0 ∨ clauses.size < identifier then
    throwError "initial certificate clause identifier is out of range"
  let index := identifier - 1
  let some literals := clauses[index]?
    | throwError "initial certificate clause index is out of range"
  let clause := buildClause literals
  if index < masterBaseReferences.size then
    let some reference := masterBaseReferences[index]?
      | throwError "master reference index is out of range"
    let tag := RawIncidence.tagOfRef 0 0 reference
    unless reference < 20659 ∧ tag.validB do
      throwError "master reference metadata is not valid and in range"
    unless clauseLiterals tag.toClause == literals do
      throwError "master reference clause does not match the certificate formula order"
    let proof := mkAppN (mkConst ``RawIncidence.masterBaseClause_proves)
      #[mkRawNatLit reference, truthProof, truthProof, clause,
        clauseReflexivity clause]
    pure {
      literals
      expression := clause
      proof := ← checkedSourceProof proof clause
    }
  else
    let maskIndex := index - masterBaseReferences.size
    let some mask := masterExcludedMasks[maskIndex]?
      | throwError "excluded-row mask index is out of range"
    let row := RawIncidence.packedRow (UInt64.ofNat mask)
    unless mask < 256 ∧ decide (row ∉ RawIncidence.canonicalRows) do
      throwError "excluded-row metadata is not noncanonical and in range"
    unless clauseLiterals (RawIncidence.rowExclusionClause row) == literals do
      throwError "excluded-row clause does not match the certificate formula order"
    let proof := mkAppN (mkConst ``RawIncidence.canonicalRowClause_proves)
      #[mkRawNatLit mask, truthProof, truthProof, clause,
        clauseReflexivity clause]
    pure {
      literals
      expression := clause
      proof := ← checkedSourceProof proof clause
    }

private def importedAdditionClause
    (additions : Array Addition) (indices : HashMap ℕ ℕ)
    (clausePrefix : Name) (identifier : ℕ) : MetaM GlobalClause := do
  let some index := indices[identifier]?
    | throwError "imported certificate identifier is not a retained addition"
  let some addition := additions[index]?
    | throwError "imported certificate addition index is out of range"
  if addition.literals.isEmpty then
    throwError "empty clause cannot be imported as an intermediate theorem"
  let clause := buildClause addition.literals
  let theoremName := certificateClauseName clausePrefix identifier
  requireTheoremWithType theoremName (certificateProofType clause)
  pure {
    literals := addition.literals
    expression := clause
    proof := mkConst theoremName
  }

private def reconstructStage
    (clauses : Array (Array Int)) (additions : Array Addition)
    (start stop : ℕ) (clausePrefix finalTheorem : Name) : MetaM Unit := do
  unless start < stop ∧ stop ≤ additions.size do
    throwError "certificate stage range is invalid"
  unless (certificateClauseName clausePrefix 0).isInternal do
    throwError "certificate clause names must be stable internal declarations"
  match checkSourceMetadata clauses with
  | .ok () => pure ()
  | .error message => throwError message
  let indices ←
    match additionIndices clauses.size additions with
    | .ok indices => pure indices
    | .error message => throwError message
  let (initialIdentifiers, importedIdentifiers) ←
    match neededStageClauses clauses.size start stop additions indices with
    | .ok identifiers => pure identifiers
    | .error message => throwError message
  let mut database : HashMap ℕ GlobalClause := {}
  for identifier in initialIdentifiers do
    database := database.insert identifier
      (← sourceInitialClause clauses identifier)
  for identifier in importedIdentifiers do
    database := database.insert identifier
      (← importedAdditionClause additions indices clausePrefix identifier)
  let context := mkConst ``RawIncidence.masterFormula
  let mut derivedEmpty := false
  for index in [start:stop] do
    let some addition := additions[index]?
      | throwError "certificate addition index is out of range"
    let clause := buildClause addition.literals
    let proof ←
      match buildProofStep database addition.literals addition.antecedents
          context clause with
      | .ok proof => pure proof
      | .error message => throwError message
    if addition.literals.isEmpty then
      unless index + 1 = additions.size ∧ stop = additions.size do
        throwError "empty clause occurs before the final certificate addition"
      addDecl <| Declaration.thmDecl {
        name := finalTheorem
        levelParams := []
        type := certificateProofType clause
        value := proof
      }
      addDocStringCore finalTheorem
        "Unsatisfiability of the 6,582-clause master coverage formula."
      derivedEmpty := true
    else
      let theoremName := certificateClauseName clausePrefix addition.identifier
      addDecl <| Declaration.thmDecl {
        name := theoremName
        levelParams := []
        type := certificateProofType clause
        value := proof
      }
      database := database.insert addition.identifier {
        literals := addition.literals
        expression := clause
        proof := mkConst theoremName
      }
  if stop = additions.size then
    unless derivedEmpty do
      throwError "final certificate stage does not derive the empty clause"
  else if derivedEmpty then
    throwError "nonfinal certificate stage derived the empty clause"

/--
Decode one contiguous range of the packed master certificate. Every nonempty
addition becomes a stable theorem constant for the following stage.
-/
syntax "master_lrat_stage"
  " initial_clauses " num " additions " num
  " stage_start " num " stage_stop " num
  " clause_prefix " ident " final_theorem " ident
  " data_parts " ident* : command

elab_rules : command
  | `(master_lrat_stage
        initial_clauses $initialCount:num additions $additionCount:num
        stage_start $stageStartSyntax:num stage_stop $stageStopSyntax:num
        clause_prefix $clausePrefixSyntax:ident
        final_theorem $finalTheoremSyntax:ident
        data_parts $parts:ident*) => do
      let initialCount := initialCount.getNat
      let additionCount := additionCount.getNat
      let start := stageStartSyntax.getNat
      let stop := stageStopSyntax.getNat
      unless masterClauses.size = initialCount do
        throwError "master formula clause count does not match certificate metadata"
      let currentNamespace ← getCurrNamespace
      let partNames := parts.toList.map fun part =>
        currentNamespace ++ part.getId
      let encoded ← readEmbeddedParts partNames
      let bytes ←
        match decodeBase64 encoded with
        | .ok bytes => pure bytes
        | .error message => throwError message
      let decodedAdditions ←
        match decodeAdditions initialCount additionCount bytes with
        | .ok result => pure result
        | .error message => throwError message
      let clausePrefix := currentNamespace ++ clausePrefixSyntax.getId
      let finalTheorem := currentNamespace ++ finalTheoremSyntax.getId
      Command.liftTermElabM do
        reconstructStage masterClauses decodedAdditions start stop
          clausePrefix finalTheorem

end Erdos97Octagon.LRAT
