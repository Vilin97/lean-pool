/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.LRAT.Elab

/-!
# Deterministic master-certificate regeneration

Run from the repository root, replacing the two executable paths:

```
lake env lean --stdin <<'EOF'
import LeanPool.Erdos97ConvexOctagon.Regenerate
regenerate_erdos97 "check" "." "/path/to/cadical" "/path/to/drat-trim"
EOF
```

Use `write` instead of `check` to replace generated Lean modules.  The supplied
executables must come from the pinned source commits recorded below.  Ordinary
library builds only check the committed packed certificate and never run
external tools.
-/

namespace Erdos97Octagon.Regenerate

open LRAT RawIncidence
open System

private def cadicalCommit :=
  "c60730422e758ef1cebe7aeddf2dda31c996bf04"

private def dratTrimCommit :=
  "2e3b2dc0ecf938addbd779d42877b6ed69d9a985"

private def initialClauseCount := 6582
private def additionCount := 11139
private def deletionCount := 8677
private def actionCount := 19816
private def additionsPerStage := 700
private def encodedLineWidth := 88
private def linesPerDataModule := 500

private def stageCount : ℕ :=
  (additionCount + additionsPerStage - 1) / additionsPerStage

private def stageStart (index : ℕ) : ℕ :=
  index * additionsPerStage

private def stageStop (index : ℕ) : ℕ :=
  min additionCount ((index + 1) * additionsPerStage)

private inductive Mode where
  | check
  | write

private def Mode.text : Mode → String
  | .check => "check"
  | .write => "write"

private structure Configuration where
  mode : Mode
  repository : FilePath
  cadical : FilePath
  dratTrim : FilePath

private inductive ParsedAction where
  | deletion
  | addition (value : Addition)

private structure ParsedCertificate where
  proofSteps : Array Addition
  actions : ℕ
  deletions : ℕ

private def parseNatural (token : String) : Except String ℕ :=
  match token.toNat? with
  | some value => pure value
  | none => throw s!"expected a natural number, got '{token}'"

private def parseInteger (token : String) : Except String Int :=
  match token.toInt? with
  | some value => pure value
  | none => throw s!"expected an integer, got '{token}'"

private def takeIntegersUntilZero :
    List String → Except String (Array Int × List String)
  | [] => throw "unterminated integer sequence"
  | token :: remaining => do
      let value ← parseInteger token
      if value = 0 then
        pure (#[], remaining)
      else
        let (values, remaining) ← takeIntegersUntilZero remaining
        pure (values.insertIdx 0 value, remaining)

private def takeNaturalsUntilZero :
    List String → Except String (Array ℕ × List String)
  | [] => throw "unterminated natural-number sequence"
  | token :: remaining => do
      let value ← parseNatural token
      if value = 0 then
        pure (#[], remaining)
      else
        let (values, remaining) ← takeNaturalsUntilZero remaining
        pure (values.insertIdx 0 value, remaining)

private def lineTokens (line : String) : List String :=
  (line.trimAscii.copy.splitOn " ").filter fun token => !token.isEmpty

private def parseActionLine (line : String) : Except String ParsedAction := do
  let tokens := lineTokens line
  let identifierToken :: remaining := tokens
    | throw "empty LRAT action"
  let identifier ← parseNatural identifierToken
  match remaining with
  | "d" :: deletionTokens =>
      let (_, trailing) ← takeNaturalsUntilZero deletionTokens
      unless trailing.isEmpty do
        throw "trailing tokens after LRAT deletion"
      pure .deletion
  | _ =>
      let (literals, remaining) ← takeIntegersUntilZero remaining
      let (antecedents, trailing) ← takeNaturalsUntilZero remaining
      unless trailing.isEmpty do
        throw "trailing tokens after LRAT addition"
      pure <| .addition { identifier, literals, antecedents }

private def parseCertificate (text : String) : Except String ParsedCertificate := do
  let mut proofSteps := #[]
  let mut actions := 0
  let mut deletions := 0
  for line in text.splitOn "\n" do
    unless line.trimAscii.isEmpty do
      actions := actions + 1
      match ← parseActionLine line with
      | .deletion => deletions := deletions + 1
      | .addition addition => proofSteps := proofSteps.push addition
  pure { proofSteps, actions, deletions }

private def packedLiteralCode (literal : Int) : Except String ℕ :=
  if literal = 0 then
    throw "zero is not a literal"
  else if literal < 0 then
    pure (2 * ((-literal).toNat - 1) + 1)
  else
    pure (2 * (literal.toNat - 1))

private def varintByteCountWithFuel :
    ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, value =>
      if value < 128 then
        some 1
      else
        (varintByteCountWithFuel fuel (value / 128)).map Nat.succ

private def packedNaturalValues
    (initialClauses : ℕ) (steps : Array Addition) :
    Except String (Array ℕ) := do
  let mut previous := initialClauses
  let mut values := #[]
  for addition in steps do
    values := values.push (addition.identifier - previous)
    values := values.push addition.literals.size
    for literal in addition.literals do
      values := values.push (← packedLiteralCode literal)
    values := values.push addition.antecedents.size
    for antecedent in addition.antecedents do
      values := values.push (addition.identifier - antecedent)
    previous := addition.identifier
  pure values

private def maximumVarintByteCount
    (initialClauses : ℕ) (steps : Array Addition) :
    Except String ℕ := do
  let values ← packedNaturalValues initialClauses steps
  let mut maximum := 0
  for value in values do
    let some count :=
        varintByteCountWithFuel packedVarintByteBound value
      | throw "packed natural exceeds the decoder byte bound"
    maximum := max maximum count
  pure maximum

private def literalInteger : Literal → Int
  | .positive index => Int.ofNat (index + 1)
  | .negative index => -Int.ofNat (index + 1)

private def renderClause (clause : Clause) : String :=
  let literals := clause.map fun literal => toString (literalInteger literal)
  String.intercalate " " literals ++ " 0\n"

private def renderMasterCnf : Except String String := do
  unless masterFormula.length = initialClauseCount do
    throw s!"expected {initialClauseCount} master clauses, got {masterFormula.length}"
  pure <| s!"p cnf 64 {initialClauseCount}\n" ++
    String.join (masterFormula.map renderClause)

private def processOutput
    (executable : FilePath) (arguments : Array String) : IO IO.Process.Output :=
  IO.Process.output {
    cmd := executable.toString
    args := arguments
    stdout := .piped
    stderr := .piped
  }

private def verifySourceCommit
    (executable : FilePath) (expected : String) : IO Unit := do
  let immediateParent := executable.parent.getD "."
  let sourceDirectory :=
    if executable.fileName.getD "" = "cadical" then
      immediateParent.parent.getD "."
    else
      immediateParent
  let output ← processOutput "git"
    #["-C", sourceDirectory.toString, "rev-parse", "HEAD"]
  unless output.exitCode = 0 do
    throw <| IO.userError s!"cannot read tool commit:\n{output.stderr}"
  let actual := output.stdout.trimAscii.copy
  unless actual = expected do
    throw <| IO.userError
      s!"tool at {sourceDirectory} is {actual}; expected {expected}"

private def runCertificateTools
    (configuration : Configuration) (directory : FilePath) :
    IO (FilePath × FilePath × FilePath) := do
  verifySourceCommit configuration.cadical cadicalCommit
  verifySourceCommit configuration.dratTrim dratTrimCommit
  let cnfPath := directory / "master.cnf"
  let dratPath := directory / "master.drat"
  let lratPath := directory / "master.lrat"
  IO.FS.writeFile cnfPath (← IO.ofExcept renderMasterCnf)
  let solver ← processOutput configuration.cadical
    #[cnfPath.toString, dratPath.toString]
  unless solver.exitCode = 20 do
    throw <| IO.userError
      s!"CaDiCaL failed with {solver.exitCode}:\n{solver.stderr}"
  let converter ← processOutput configuration.dratTrim
    #[cnfPath.toString, dratPath.toString, "-L", lratPath.toString]
  unless converter.exitCode = 0 do
    throw <| IO.userError
      s!"drat-trim failed with {converter.exitCode}:\n{converter.stderr}"
  pure (cnfPath, dratPath, lratPath)

private def hashOutput (executable : FilePath) (arguments : Array String) :
    IO (Option String) := do
  try
    let output ← processOutput executable arguments
    if output.exitCode = 0 then
      pure <| (output.stdout.trimAscii.copy.splitOn " ").head?
    else
      pure none
  catch _ =>
    pure none

private def sha256 (path : FilePath) : IO String := do
  if let some digest ← hashOutput "sha256sum" #[path.toString] then
    pure digest
  else if let some digest ← hashOutput "shasum" #["-a", "256", path.toString] then
    pure digest
  else
    throw <| IO.userError "neither sha256sum nor shasum is available"

private def chunksOfWithFuel :
    ℕ → ℕ → List α → List (List α)
  | 0, _, _ => []
  | _, _, [] => []
  | _fuel + 1, 0, _ => []
  | fuel + 1, size, values =>
      values.take size :: chunksOfWithFuel fuel size (values.drop size)

private def chunksOf (size : ℕ) (values : List α) : List (List α) :=
  chunksOfWithFuel (values.length + 1) size values

private def encodedLines (encoded : String) : Except String (List String) := do
  let bytes := encoded.toUTF8
  let mut result := #[]
  for block in [0:(bytes.size + encodedLineWidth - 1) / encodedLineWidth] do
    let start := block * encodedLineWidth
    let stop := min bytes.size (start + encodedLineWidth)
    let mut line := ByteArray.empty
    for index in [start:stop] do
      let some byte := bytes[index]?
        | throw "encoded certificate line index is out of range"
      line := line.push byte
    let some text := String.fromUTF8? line
      | throw "encoded certificate line is not valid UTF-8"
    result := result.push text
  pure result.toList

private def header : String :=
  "/-\n" ++
  "Copyright (c) 2026 Egor Lyfar. All rights reserved.\n" ++
  "Released under Apache 2.0 license as described in the file LICENSE.\n" ++
  "Authors: Egor Lyfar\n" ++
  "-/\n\n"

private def renderDataModule
    (moduleIndex : ℕ) (lines : List String) : String :=
  let name := s!"masterCertificatePart{moduleIndex}"
  let body := lines.map fun line => s!"  \"{line}\",\n"
  header ++
    "import LeanPool.Erdos97ConvexOctagon.LRAT.Format\n\n" ++
    "/-! # Generated packed master-certificate data -/\n\n" ++
    "namespace Erdos97Octagon.RawIncidence\n\n" ++
    s!"/-- Packed certificate data part {moduleIndex}. -/\n" ++
    s!"def {name} : List String := [\n" ++
    String.join body ++
    "]\n\nend Erdos97Octagon.RawIncidence\n"

private def dataModuleName (index : ℕ) : String :=
  s!"MasterCertificateData{index}"

private def stageModuleName (index : ℕ) : String :=
  if index < 10 then
    s!"MasterCertificateStage0{index}"
  else
    s!"MasterCertificateStage{index}"

private def renderNaturalList (values : List ℕ) : String :=
  "[" ++ String.intercalate ", " (values.map toString) ++ "]"

private def renderManifest
    (dataModuleCount packedByteCount encodedCharacterCount maximumVarintBytes : ℕ)
    (cnfHash lratHash packedHash : String) : String :=
  let stageCounts := (List.range stageCount).map fun index =>
    stageStop index - stageStart index
  let stageBoundaries :=
    (List.range stageCount).map stageStart ++ [additionCount]
  let stageBoundarySplit := (stageBoundaries.length + 1) / 2
  header ++
    "import LeanPool.Erdos97ConvexOctagon.LRAT.Format\n\n" ++
    "/-! # Generated master-certificate manifest -/\n\n" ++
    "namespace Erdos97Octagon.RawIncidence\n\n" ++
    "/-- Packed certificate format version. -/\n" ++
    "def masterCertificateFormatVersion : ℕ := 1\n\n" ++
    "/-- Number of initial clauses. -/\n" ++
    s!"def masterCertificateInitialClauses : ℕ := {initialClauseCount}\n\n" ++
    "/-- Number of retained LRAT additions. -/\n" ++
    s!"def masterCertificateAdditions : ℕ := {additionCount}\n\n" ++
    "/-- Number of omitted LRAT deletion records. -/\n" ++
    s!"def masterCertificateDeletions : ℕ := {deletionCount}\n\n" ++
    "/-- Total number of actions in the generated LRAT text. -/\n" ++
    s!"def masterCertificateActions : ℕ := {actionCount}\n\n" ++
    "/-- Number of packed bytes. -/\n" ++
    s!"def masterCertificatePackedBytes : ℕ := {packedByteCount}\n\n" ++
    "/-- Number of base64 characters. -/\n" ++
    s!"def masterCertificateEncodedCharacters : ℕ := {encodedCharacterCount}\n\n" ++
    "/-- Number of generated data modules. -/\n" ++
    s!"def masterCertificateDataModules : ℕ := {dataModuleCount}\n\n" ++
    "/-- Number of sequential proof-stage modules. -/\n" ++
    s!"def masterCertificateStageModules : ℕ := {stageCount}\n\n" ++
    "/-- Maximum retained additions reconstructed in one proof stage. -/\n" ++
    s!"def masterCertificateMaximumAdditionsPerStage : ℕ := {additionsPerStage}\n\n" ++
    "/-- Retained additions reconstructed by each sequential proof stage. -/\n" ++
    "def masterCertificateStageAdditionCounts : List ℕ :=\n" ++
    s!"  {renderNaturalList stageCounts}\n\n" ++
    "/-- Zero-based addition boundaries of the sequential proof stages. -/\n" ++
    "def masterCertificateStageBoundaries : List ℕ :=\n" ++
    s!"  {renderNaturalList (stageBoundaries.take stageBoundarySplit)} ++\n" ++
    s!"    {renderNaturalList (stageBoundaries.drop stageBoundarySplit)}\n\n" ++
    "/-- Maximum measured bytes used by one packed natural number. -/\n" ++
    s!"def masterCertificateMaximumVarintBytes : ℕ := {maximumVarintBytes}\n\n" ++
    "/-- Decoder byte bound for one packed natural number. -/\n" ++
    s!"def masterCertificateVarintByteBound : ℕ := {packedVarintByteBound}\n\n" ++
    "/-- Maximum string literals emitted in one generated data part. -/\n" ++
    s!"def masterCertificateMaximumStringsPerPart : ℕ := {linesPerDataModule}\n\n" ++
    "/-- Maximum measured compiled-expression steps used by one generated data part. -/\n" ++
    "def masterCertificateMaximumStringListExpressionSteps : ℕ := " ++
    s!"{embeddedCertificatePartMaximumExpressionSteps}\n\n" ++
    "/-- Structural fuel used to decode one generated string-list part. -/\n" ++
    s!"def masterCertificateStringListFuel : ℕ := {embeddedCertificatePartFuel}\n\n" ++
    "/-- SHA-256 of the generated DIMACS formula. -/\n" ++
    "def masterCertificateCnfSha256 : String :=\n" ++
    s!"  \"{cnfHash}\"\n\n" ++
    "/-- SHA-256 of the normalized LRAT text. -/\n" ++
    "def masterCertificateLratSha256 : String :=\n" ++
    s!"  \"{lratHash}\"\n\n" ++
    "/-- SHA-256 of the packed certificate bytes. -/\n" ++
    "def masterCertificatePackedSha256 : String :=\n" ++
    s!"  \"{packedHash}\"\n\n" ++
    "/-- Pinned CaDiCaL source commit. -/\n" ++
    "def masterCertificateCadicalCommit : String :=\n" ++
    s!"  \"{cadicalCommit}\"\n\n" ++
    "/-- Pinned drat-trim source commit. -/\n" ++
    "def masterCertificateDratTrimCommit : String :=\n" ++
    s!"  \"{dratTrimCommit}\"\n\n" ++
    "end Erdos97Octagon.RawIncidence\n"

private def renderStageModule
    (dataModuleCount stageIndex : ℕ) : String :=
  let imports := (List.range dataModuleCount).map fun index =>
    s!"import LeanPool.Erdos97ConvexOctagon.{dataModuleName index}\n"
  let parts := (List.range dataModuleCount).map fun index =>
    s!"    masterCertificatePart{index}\n"
  let dependencyImport :=
    if stageIndex = 0 then
      "import LeanPool.Erdos97ConvexOctagon.LRAT.Elab\n" ++
        String.join imports
    else
      s!"import LeanPool.Erdos97ConvexOctagon." ++
        s!"{stageModuleName (stageIndex - 1)}\n"
  header ++
    dependencyImport ++
    s!"\n/-! # Master-certificate proof stage {stageIndex} -/\n\n" ++
    "namespace Erdos97Octagon.RawIncidence\n\n" ++
    "master_lrat_stage\n" ++
    s!"  initial_clauses {initialClauseCount}\n" ++
    s!"  additions {additionCount}\n" ++
    s!"  stage_start {stageStart stageIndex}\n" ++
    s!"  stage_stop {stageStop stageIndex}\n" ++
    "  clause_prefix masterCertificateClause\n" ++
    "  final_theorem masterFormula_unsatisfiable\n" ++
    "  data_parts\n" ++
    String.join parts ++
    "\n\nend Erdos97Octagon.RawIncidence\n"

private def renderCertificateModule : String :=
  header ++
    s!"import LeanPool.Erdos97ConvexOctagon." ++
    s!"{stageModuleName (stageCount - 1)}\n\n" ++
    "/-! # Kernel-checked master coverage certificate -/\n"

private def generatedDirectory (repository : FilePath) : FilePath :=
  repository / "LeanPool" / "Erdos97ConvexOctagon"

private def reconcileFile
    (mode : Mode) (path : FilePath) (expected : String) : IO Unit := do
  match mode with
  | .write => IO.FS.writeFile path expected
  | .check =>
      let fileExists ← path.pathExists
      unless fileExists do
        throw <| IO.userError s!"generated file is missing: {path}"
      let actual ← IO.FS.readFile path
      unless actual = expected do
        throw <| IO.userError s!"generated file differs: {path}"

private def removeOrRejectExtraModules
    (configuration : Configuration) (stem : String) (expectedCount : ℕ) :
    IO Unit := do
  let directory := generatedDirectory configuration.repository
  for entry in ← directory.readDir do
    let name := entry.fileName
    if name.startsWith stem ∧ name.endsWith ".lean" then
      let suffix := ((name.drop stem.length).dropEnd 5).copy
      let isExpected : Bool :=
        match suffix.toNat? with
        | some index => decide (index < expectedCount)
        | none => false
      unless isExpected do
        match configuration.mode with
        | .write => IO.FS.removeFile entry.path
        | .check =>
            throw <| IO.userError s!"obsolete generated file remains: {entry.path}"

private def removeOrRejectObsoleteFile
    (configuration : Configuration) (path : FilePath) : IO Unit := do
  if ← path.pathExists then
    match configuration.mode with
    | .write => IO.FS.removeFile path
    | .check => throw <| IO.userError s!"obsolete generated file remains: {path}"

private def generate
    (configuration : Configuration) (temporaryDirectory : FilePath) : IO Unit := do
  let (cnfPath, _, lratPath) ←
    runCertificateTools configuration temporaryDirectory
  let lratText ← IO.FS.readFile lratPath
  let certificate ← IO.ofExcept <| parseCertificate lratText
  unless certificate.actions = actionCount do
    throw <| IO.userError
      s!"expected {actionCount} LRAT actions, got {certificate.actions}"
  unless certificate.deletions = deletionCount do
    throw <| IO.userError
      s!"expected {deletionCount} LRAT deletions, got {certificate.deletions}"
  let proofAdditions := certificate.proofSteps
  unless proofAdditions.size = additionCount do
    throw <| IO.userError
      s!"expected {additionCount} LRAT additions, got {proofAdditions.size}"
  for index in [0:proofAdditions.size] do
    let some addition := proofAdditions[index]?
      | throw <| IO.userError "LRAT addition index is out of range"
    if addition.literals.isEmpty ∧ index + 1 ≠ proofAdditions.size then
      throw <| IO.userError "empty clause occurs before the final LRAT addition"
  let some finalAddition := proofAdditions[proofAdditions.size - 1]?
    | throw <| IO.userError "LRAT certificate has no additions"
  unless finalAddition.literals.isEmpty do
    throw <| IO.userError "final LRAT addition is not the empty clause"
  let packed ← IO.ofExcept <|
    encodeAdditions initialClauseCount proofAdditions
  let encoded ← IO.ofExcept <| encodeBase64 packed
  let maximumVarintBytes ← IO.ofExcept <|
    maximumVarintByteCount initialClauseCount proofAdditions
  let roundTripBytes ← IO.ofExcept <| decodeBase64 encoded
  let roundTrip ← IO.ofExcept <|
    decodeAdditions initialClauseCount additionCount roundTripBytes
  unless roundTrip == proofAdditions do
    throw <| IO.userError "packed certificate round trip changed an action"
  let packedPath := temporaryDirectory / "master.packed"
  IO.FS.writeBinFile packedPath packed
  let lines ← IO.ofExcept <| encodedLines encoded
  let lineModules := chunksOf linesPerDataModule lines
  let directory := generatedDirectory configuration.repository
  for index in List.range lineModules.length do
    let lines := lineModules.getD index []
    reconcileFile configuration.mode
      (directory / s!"{dataModuleName index}.lean")
      (renderDataModule index lines)
  removeOrRejectExtraModules configuration
    "MasterCertificateData" lineModules.length
  removeOrRejectObsoleteFile configuration
    (directory / "MasterCertificateContext.lean")
  for index in List.range stageCount do
    reconcileFile configuration.mode
      (directory / s!"{stageModuleName index}.lean")
      (renderStageModule lineModules.length index)
  removeOrRejectExtraModules configuration
    "MasterCertificateStage" stageCount
  reconcileFile configuration.mode
    (directory / "MasterCertificateManifest.lean")
    (renderManifest lineModules.length packed.size encoded.length maximumVarintBytes
      (← sha256 cnfPath) (← sha256 lratPath) (← sha256 packedPath))
  reconcileFile configuration.mode
    (directory / "MasterCertificate.lean")
    renderCertificateModule
  IO.println <| s!"{configuration.mode.text}: {initialClauseCount} clauses, " ++
    s!"{certificate.actions} actions, {proofAdditions.size} additions, " ++
    s!"{packed.size} packed bytes, {lineModules.length} data modules, " ++
    s!"{stageCount} proof stages"

private def configuration (mode repository cadical dratTrim : String) :
    Except String Configuration := do
  let parsedMode ←
    match mode with
    | "check" => pure Mode.check
    | "write" => pure Mode.write
    | _ => throw "mode must be check or write"
  pure {
    mode := parsedMode
    repository
    cadical
    dratTrim
  }

/-- Run the deterministic master-certificate generator with explicit tool paths. -/
syntax (name := regenerateErdos97)
  "regenerate_erdos97 " str str str str : command

elab_rules : command
  | `(regenerate_erdos97 $mode:str $repository:str $cadical:str $dratTrim:str) => do
      let configuration ← IO.ofExcept <|
        configuration mode.getString repository.getString cadical.getString dratTrim.getString
      Lean.Elab.Command.liftIO <| IO.FS.withTempDir fun directory =>
        generate configuration directory

end Erdos97Octagon.Regenerate
