/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Lean

/-!
# Exposition extractor

Dumps every human-written declaration in the pool, together with its
intra-pool dependency edges, as JSONL. One line per declaration:

```json
{"id": "<full name>", "n": "<display name>", "m": "<module>", "k": "<kind>",
 "p": <private?>, "r": [startLine, startCol, endLine, endCol], "s": [nameLine, nameCol],
 "d": "<docstring?>", "deps": ["<id>", ...], "ext": <distinct external deps>}
```

Dependency edges follow the kernel closure: references to compiler-generated
auxiliaries (`match_*`, equation lemmas, `.rec`, constructors, projections, ...)
are expanded transitively until a human-written declaration is reached, so an
edge `A -> B` means "checking `A` requires `B`". `ext` counts distinct
declarations outside the pool (Mathlib/core) encountered on that boundary.

Usage: `lake env lean --run scripts/exposition/Extract.lean <out.jsonl>`
-/

open Lean Meta

namespace Exposition

/-- The library whose declarations we extract. -/
def poolRoot : Name := `LeanPool

/-- Is `module` one of the pool's own modules? -/
def isPoolModule (module : Name) : Bool :=
  poolRoot.isPrefixOf module

/-- Coarse declaration kind, used only as a fallback: the site generator
refines it from the source keyword (`lemma` vs `theorem`, `abbrev` vs `def`,
`instance`, `class`, ...). Extension-backed queries (`isClass`,
`Meta.isInstance`) are unavailable here because the environment is imported
without extension states (`loadExts := false`). -/
def kindOf (env : Environment) (name : Name) (info : ConstantInfo) : Option String :=
  match info with
  | .thmInfo _ => some "theorem"
  | .defnInfo _ => some "def"
  | .opaqueInfo _ => some "opaque"
  | .axiomInfo _ => some "axiom"
  | .inductInfo _ => if isStructure env name then some "structure" else some "inductive"
  | _ => none

/-- Mirrors the doc-gen4 / import-graph blacklist for generated declarations. -/
def isGenerated (env : Environment) (name : Name) : CoreM Bool := do
  let display := privateToUserName name
  if display.isInternalDetail then return true
  if isAuxRecursor env name || isNoConfusion env name then return true
  if (← isRec name) || (← Meta.isMatcher name) then return true
  if (env.getProjectionFnInfo? name).isSome then return true
  -- `declare_syntax_cat` generates a quotation parser `<cat>.quot`; the type
  -- guard keeps genuine user definitions that happen to be named `quot`.
  if let .str _ "quot" := display then
    if let some info := env.find? name then
      if info.type.isConstOf ``Lean.ParserDescr
          || info.type.isConstOf ``Lean.TrailingParserDescr then
        return true
  return false

/-- Should `name` appear as a node of the exposition? -/
def isExposed (env : Environment) (name : Name) (info : ConstantInfo) : CoreM Bool := do
  let some moduleIdx := env.getModuleIdxFor? name | return false
  unless isPoolModule env.header.moduleNames[moduleIdx.toNat]! do return false
  if (kindOf env name info).isNone then return false
  if ← isGenerated env name then return false
  return (← findDeclarationRanges? name).isSome

/-- Constants a declaration mentions, including constructor signatures for
inductives/structures (field types live in the constructor's type). -/
def directUses (env : Environment) (info : ConstantInfo) : Array Name :=
  match info with
  | .inductInfo v =>
    v.ctors.foldl (init := info.getUsedConstantsAsSet)
      (fun acc c => match env.find? c with
        | some ci => acc.insertMany ci.getUsedConstantsAsSet
        | none => acc)
      |>.toArray
  | _ => info.getUsedConstantsAsSet.toArray

/-- Expand a seed set of used constants, tunnelling through generated pool
auxiliaries, until exposed pool declarations (edges) or non-pool constants
(externals) are reached. -/
def resolveSeeds (env : Environment) (self : Name) (seeds : Array Name)
    (exposed : NameSet) : NameSet × Nat := Id.run do
  let mut edges : NameSet := {}
  let mut externals : NameSet := {}
  let mut visited : NameSet := {}
  let mut stack : Array Name := seeds
  while h : stack.size > 0 do
    let c := stack[stack.size - 1]
    stack := stack.pop
    if c == self || visited.contains c then continue
    visited := visited.insert c
    if exposed.contains c then
      edges := edges.insert c
      continue
    let inPool := match env.getModuleIdxFor? c with
      | some idx => isPoolModule env.header.moduleNames[idx.toNat]!
      | none => false
    if inPool then
      if let some ci := env.find? c then
        stack := stack ++ directUses env ci
    else
      externals := externals.insert c
  return (edges, externals.size)

def escapeName (n : Name) : String := n.toString

def declJson (env : Environment) (name : Name) (info : ConstantInfo)
    (exposed : NameSet) : CoreM (Option Json) := do
  let some ranges ← findDeclarationRanges? name | return none
  let some kind := kindOf env name info | return none
  let some moduleIdx := env.getModuleIdxFor? name | return none
  let module := env.header.moduleNames[moduleIdx.toNat]!
  let display := privateToUserName name
  let doc ← findDocString? env name
  let (edges, extCount) := resolveSeeds env name (directUses env info) exposed
  -- Statement-only dependencies for proof-carrying declarations: the minimal
  -- Lean file replaces their proofs by `sorry`, so only the type's
  -- dependencies must be present for it to elaborate.
  let typeEdges : Option NameSet := match info with
    | .thmInfo v => some (resolveSeeds env name v.type.getUsedConstants exposed).1
    | _ => none
  let r := ranges.range
  let s := ranges.selectionRange
  return some <| Json.mkObj <| [
    ("id", Json.str (escapeName name)),
    ("n", Json.str (escapeName display)),
    ("m", Json.str module.toString),
    ("k", Json.str kind),
    ("r", toJson [r.pos.line, r.pos.column, r.endPos.line, r.endPos.column]),
    ("s", toJson [s.pos.line, s.pos.column]),
    ("deps", Json.arr (edges.toArray.map (Json.str ∘ escapeName))),
    ("ext", Json.num extCount)
  ] ++ (match typeEdges with
    | some t => [("tdeps", Json.arr (t.toArray.map (Json.str ∘ escapeName)))]
    | none => [])
    ++ (if isPrivateName name then [("p", Json.bool true)] else [])
    ++ (match doc with | some d => [("d", Json.str d)] | none => [])

def extract (outPath : System.FilePath) : CoreM Unit := do
  let env ← getEnv
  -- Pass 1: collect the exposed node set.
  let mut exposed : NameSet := {}
  let mut names : Array Name := #[]
  for moduleIdx in [0:env.header.moduleNames.size] do
    unless isPoolModule env.header.moduleNames[moduleIdx]! do continue
    let moduleData : ModuleData := env.header.moduleData[moduleIdx]!
    for name in moduleData.constNames do
      -- A constant can appear in several modules' `constNames` when two files
      -- declare it textually; keep the first occurrence only.
      if exposed.contains name then continue
      let some info := env.find? name | continue
      if ← isExposed env name info then
        exposed := exposed.insert name
        names := names.push name
  -- Pass 2: emit one JSON line per exposed declaration.
  IO.FS.createDirAll (outPath.parent.getD ".")
  let handle ← IO.FS.Handle.mk outPath .write
  for name in names do
    let some info := env.find? name | continue
    if let some json ← declJson env name info exposed then
      handle.putStrLn json.compress
  handle.flush
  IO.println s!"exposition: wrote {names.size} declarations to {outPath}"

end Exposition

def main (args : List String) : IO UInt32 := do
  let outPath := args[0]?.getD "exposition-dump.jsonl"
  -- Further arguments override the imported modules (default: the whole pool);
  -- useful for testing against a partially built tree.
  let modules := if args.length > 1 then args.drop 1 |>.map (·.toName) else [Exposition.poolRoot]
  Lean.initSearchPath (← Lean.findSysroot)
  let imports := modules.toArray.map fun module => ({ module } : Lean.Import)
  let env ← Lean.importModules imports {} (trustLevel := 1024)
  let coreContext : Lean.Core.Context := {
    fileName := "<exposition-extract>",
    fileMap := default,
    maxHeartbeats := 0
  }
  let (result, _) ← (Exposition.extract outPath).toIO coreContext { env }
  let _ := result
  return 0
