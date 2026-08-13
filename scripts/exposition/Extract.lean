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

/-- Is `name` a notation/syntax parser descriptor? Notation commands are
replayed as *context* by the minimal-file builder (following LMLExposition),
so parser declarations are not exposition nodes. -/
def isParserDescr (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some info =>
    info.type.isConstOf ``Lean.ParserDescr
      || info.type.isConstOf ``Lean.TrailingParserDescr
  | none => false

/-- Mirrors the doc-gen4 / import-graph blacklist for generated declarations. -/
def isGenerated (env : Environment) (name : Name) : CoreM Bool := do
  let display := privateToUserName name
  if display.isInternalDetail then return true
  if isAuxRecursor env name || isNoConfusion env name then return true
  if (← isRec name) || (← Meta.isMatcher name) then return true
  if (env.getProjectionFnInfo? name).isSome then return true
  if isParserDescr env name then return true
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
    let base := v.ctors.foldl (init := info.getUsedConstantsAsSet)
      (fun acc c => match env.find? c with
        | some ci => acc.insertMany ci.getUsedConstantsAsSet
        | none => acc)
    -- Structure field defaults live in generated `<S>.<field>._default`
    -- functions; seeding them lets the resolver tunnel through their bodies.
    let withDefaults :=
      if (getStructureInfo? env v.name).isSome then
        (getStructureFields env v.name).foldl (init := base) fun acc field =>
          match getDefaultFnForField? env v.name field with
          | some defaultFn => acc.insert defaultFn
          | none => acc
      else base
    withDefaults.toArray
  | _ => info.getUsedConstantsAsSet.toArray

/-! The three dependency-recovery mechanisms below are ported from
LMLExposition's `Collect.lean` (Rémy Degenne,
https://github.com/LeanMachineLearning/exposition): coercion instances and
notation expansions leave no constant in elaborated terms, so
`getUsedConstants` alone misses them. -/

/-- Coercion type classes whose instances Lean unfolds at use sites; the
instance must still be present for the source's `↑`/`⇑` to elaborate. -/
def coercionClasses : List Name :=
  [``CoeFun, ``CoeSort, ``Coe, ``CoeTC, ``CoeHead, ``CoeTail, ``CoeHTCT,
   ``CoeOut, ``CoeDep]

/-- If `type` is, under binders, a coercion-class application `Cls Src …`,
the head constant of `Src` (the type coerced *from*). -/
partial def coercionSourceType? (type : Expr) : Option Name :=
  match type with
  | .forallE _ _ b _ => coercionSourceType? b
  | _ =>
    let (fn, args) := type.getAppFnArgs
    if coercionClasses.contains fn && args.size ≥ 1 then
      args[0]!.getAppFn.constName?
    else none

/-- The `String` a string-literal `Expr` holds, if `e` is one. -/
def exprStrLit? (e : Expr) : Option String :=
  match e with
  | .lit (.strVal s) => some s
  | _ => none

/-- Reconstructs the `Name` value `e` builds (notation/macro definitions
store the constants they expand to as pre-resolved `Name` data, invisible
to `getUsedConstants`). -/
partial def evalNameExpr? (e : Expr) : Option Name := do
  match e.getAppFnArgs with
  | (``Lean.Name.anonymous, _) => some .anonymous
  | (``Lean.Name.mkStr1, #[a]) => some (.str .anonymous (← exprStrLit? a))
  | (``Lean.Name.mkStr2, #[a, b]) =>
    some (.str (.str .anonymous (← exprStrLit? a)) (← exprStrLit? b))
  | (``Lean.Name.mkStr3, #[a, b, c]) =>
    some (.str (.str (.str .anonymous (← exprStrLit? a)) (← exprStrLit? b))
      (← exprStrLit? c))
  | (``Lean.Name.mkStr4, #[a, b, c, d]) =>
    some (.str (.str (.str (.str .anonymous (← exprStrLit? a))
      (← exprStrLit? b)) (← exprStrLit? c)) (← exprStrLit? d))
  | (``Lean.Name.str, #[p, s]) => some (.str (← evalNameExpr? p) (← exprStrLit? s))
  | (``Lean.Name.num, #[p, n]) =>
    match n with
    | .lit (.natVal k) => some (.num (← evalNameExpr? p) k)
    | _ => none
  | (``Lean.Name.mkNum, #[p, n]) =>
    match n with
    | .lit (.natVal k) => some (.num (← evalNameExpr? p) k)
    | _ => none
  | _ => none

/-- Every `Name` value embedded anywhere in `e`. -/
partial def collectEmbeddedNames (e : Expr) : Array Name := Id.run do
  let mut acc : Array Name := #[]
  if let some n := evalNameExpr? e then acc := acc.push n
  match e with
  | .app f a => return acc ++ collectEmbeddedNames f ++ collectEmbeddedNames a
  | .lam _ t b _ => return acc ++ collectEmbeddedNames t ++ collectEmbeddedNames b
  | .forallE _ t b _ => return acc ++ collectEmbeddedNames t ++ collectEmbeddedNames b
  | .letE _ t v b _ =>
    return acc ++ collectEmbeddedNames t ++ collectEmbeddedNames v
      ++ collectEmbeddedNames b
  | .mdata _ b => return acc ++ collectEmbeddedNames b
  | .proj _ _ b => return acc ++ collectEmbeddedNames b
  | _ => return acc

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

/-- Pool constants whose type is a coercion-class application, keyed by the
head constant of the type coerced *from*. Ported from LMLExposition
(`coercionInstancesByType`); membership in the instance table is not
consulted (extension states are not loaded), the type shape suffices. -/
def coercionInstancesByType (env : Environment) (exposed : NameSet) :
    Std.HashMap Name (Array Name) := Id.run do
  let mut m : Std.HashMap Name (Array Name) := {}
  for name in exposed.toArray do
    if let some info := env.find? name then
      if let some src := coercionSourceType? info.type then
        m := m.insert src ((m.getD src #[]).push name)
  return m

/-- Normalized notation-kind name: re-elaborated local notations get fresh
private prefixes, so kinds are matched modulo `privateToUserName` on both
the environment side and the parsed-syntax side. -/
def normalizeKind (n : Name) : Name := privateToUserName n

/-- All pool parser-descriptor constants (notation kinds, normalized), with
their defining module and range-start position. -/
def poolNotationKinds (env : Environment) : CoreM (Array (Name × Name × Position)) := do
  let mut acc : Array (Name × Name × Position) := #[]
  for moduleIdx in [0:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[moduleIdx]!
    unless isPoolModule moduleName do continue
    let moduleData : ModuleData := env.header.moduleData[moduleIdx]!
    for name in moduleData.constNames do
      if isParserDescr env name then
        if let some ranges ← findDeclarationRanges? name then
          acc := acc.push (normalizeKind name, moduleName, ranges.range.pos)
  return acc

/-- Maps each pool notation kind to the *exposed* constants its expansion
references (ported from LMLExposition's `notationExpansionDeps`): notation
macro definitions embed both the parser kind and the abbreviated constants
as pre-resolved `Name` data. -/
def notationExpansionDeps (env : Environment) (exposed : NameSet) :
    Std.HashMap Name (Array Name) := Id.run do
  let mut m : Std.HashMap Name (Array Name) := {}
  for moduleIdx in [0:env.header.moduleNames.size] do
    unless isPoolModule env.header.moduleNames[moduleIdx]! do continue
    let moduleData : ModuleData := env.header.moduleData[moduleIdx]!
    for name in moduleData.constNames do
      if let some (.defnInfo v) := env.find? name then
        let names := collectEmbeddedNames v.value
        let kinds := names.filter (isParserDescr env ·)
        unless kinds.isEmpty do
          let realDeps := names.filter (fun n => exposed.contains n)
          for k in kinds do
            let key := normalizeKind k
            m := m.insert key ((m.getD key #[]) ++ realDeps)
  return m

def declJson (env : Environment) (name : Name) (info : ConstantInfo)
    (exposed : NameSet) (coercionInsts : Std.HashMap Name (Array Name)) :
    CoreM (Option Json) := do
  let some ranges ← findDeclarationRanges? name | return none
  let some kind := kindOf env name info | return none
  let some moduleIdx := env.getModuleIdxFor? name | return none
  let module := env.header.moduleNames[moduleIdx.toNat]!
  let display := privateToUserName name
  let doc ← findDocString? env name
  -- Coercion instances are unfolded out of elaborated terms; re-attach the
  -- instances coercing *from* any referenced type (LMLExposition's
  -- `addCoercionInsts`).
  let addCoercion (edges : NameSet) : NameSet :=
    edges.toArray.foldl (init := edges) fun acc dep =>
      (coercionInsts.getD dep #[]).foldl (init := acc) fun acc2 inst =>
        if inst == name then acc2 else acc2.insert inst
  let (rawEdges, extCount) := resolveSeeds env name (directUses env info) exposed
  let edges := addCoercion rawEdges
  -- Statement-only dependencies for proof-carrying declarations: the minimal
  -- Lean file replaces their proofs by `sorry`, so only the type's
  -- dependencies must be present for it to elaborate.
  let typeEdges : Option NameSet := match info with
    | .thmInfo v =>
      some (addCoercion (resolveSeeds env name v.type.getUsedConstants exposed).1)
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

/-- Pass 1: the exposed node set, in module order. -/
def exposedDecls (env : Environment) : CoreM (NameSet × Array Name) := do
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
  return (exposed, names)

def extract (outPath : System.FilePath) (exposed : NameSet) (names : Array Name) :
    CoreM Unit := do
  let env ← getEnv
  let coercionInsts := coercionInstancesByType env exposed
  IO.FS.createDirAll (outPath.parent.getD ".")
  let handle ← IO.FS.Handle.mk outPath .write
  for name in names do
    let some info := env.find? name | continue
    if let some json ← declJson env name info exposed coercionInsts then
      handle.putStrLn json.compress
  handle.flush
  IO.println s!"exposition: wrote {names.size} declarations to {outPath}"

end Exposition

namespace Exposition.Commands

/-!
Per-module command classification for the minimal-file builder, ported from
LMLExposition's `Extract.lean` (Rémy Degenne, after Matthew Ballard's
`EmitStandalone.lean`). Each source file is parsed against the loaded
environment to recover per-command `Syntax` and byte ranges. Context commands
are re-elaborated because they can extend the parser or change its scope;
declaration commands are not, because their compiled declarations are already
in the environment. The output is one JSON line per module describing every
declaration command (with byte-exact `sorry`-surgery edits) and every
context command (`namespace`/`open`/`variable`/notation/...), which the
client-side builder assembles into standalone files.
-/

open Lean.Elab

/-- The `declVal` syntax node of a declaration, if present. -/
partial def findDeclValStx? (root : Syntax) : Option Syntax := Id.run do
  let mut worklist : Array Syntax := #[root]
  while !worklist.isEmpty do
    let stx := worklist.back!
    worklist := worklist.pop
    let k := stx.getKind
    if k == ``Parser.Command.declValSimple || k == ``Parser.Command.declValEqns
        || k == ``Parser.Command.whereStructInst then
      return some stx
    for arg in stx.getArgs do
      worklist := worklist.push arg
  return none

/-- True if `stx` declares a `theorem` or `lemma` (proof replaced by
`sorry`); sees through `open … in` wrapper commands. -/
partial def isTheoremDecl (stx : Syntax) : Bool := Id.run do
  let mut worklist : Array Syntax := #[stx]
  while !worklist.isEmpty do
    let s := worklist.back!
    worklist := worklist.pop
    let k := s.getKind
    if k == ``Parser.Command.theorem || k == `lemma then return true
    for arg in s.getArgs do
      worklist := worklist.push arg
  return false

/-- Byte ranges of the outermost `by …` blocks inside `root` (embedded
proofs in a definition's value, replaced by `sorry`). -/
partial def collectByBlocks (root : Syntax) : Array (String.Pos.Raw × String.Pos.Raw) := Id.run do
  let mut acc : Array (String.Pos.Raw × String.Pos.Raw) := #[]
  let mut worklist : Array Syntax := #[root]
  while !worklist.isEmpty do
    let stx := worklist.back!
    worklist := worklist.pop
    if stx.getKind == ``Lean.Parser.Term.byTactic then
      match stx.getPos?, stx.getTailPos? with
      | some s, some e => acc := acc.push (s, e)
      | _, _ => for arg in stx.getArgs do worklist := worklist.push arg
    else
      for arg in stx.getArgs do
        worklist := worklist.push arg
  return acc

/-- Every `SyntaxNodeKind` occurring in `stx` (notation uses show up as
nodes whose kind is the notation parser's name). -/
partial def collectSyntaxKinds (stx : Syntax) (acc : NameSet := {}) : NameSet := Id.run do
  let mut acc := acc
  let mut worklist : Array Syntax := #[stx]
  while !worklist.isEmpty do
    let s := worklist.back!
    worklist := worklist.pop
    acc := acc.insert s.getKind
    for arg in s.getArgs do
      worklist := worklist.push arg
  return acc

/-- Every identifier appearing anywhere in `stx`, as strings. -/
partial def collectIdents (stx : Syntax) : Array String := Id.run do
  let mut acc : Array String := #[]
  let mut worklist : Array Syntax := #[stx]
  while !worklist.isEmpty do
    let s := worklist.back!
    worklist := worklist.pop
    if s.isIdent then acc := acc.push s.getId.toString
    for a in s.getArgs do
      worklist := worklist.push a
  return acc

/-- Notation/syntax-defining command kinds, replayed as context so that
declarations using them still parse. Extends LMLExposition's set with the
Mathlib `notation3` command and `elab_rules`/`declare_syntax_cat`. -/
def isNotationCmdKind (k : SyntaxNodeKind) : Bool :=
  k == ``Parser.Command.«notation» || k == ``Parser.Command.«mixfix»
    || k == ``Parser.Command.«macro» || k == ``Parser.Command.«macro_rules»
    || k == ``Parser.Command.«syntax» || k == ``Parser.Command.«elab»
    || k == `Lean.Parser.Command.elab_rules || k == ``Parser.Command.syntaxCat
    || k == `Mathlib.Notation3.notation3 || k == `Lean.Parser.Command.binderPredicate
    -- Mathlib's `scoped[NS] infixl …` wrapper: dropping it loses the
    -- notation entirely, so declarations using it cannot be re-parsed.
    || k == `Mathlib.Tactic.scopedNS
    -- Attribute/extension registration commands (`register_simp_attr …`)
    -- must replay for inline `@[custom_attr]` uses to elaborate.
    || (match k with
        | .str _ "registerSimpAttr" => true
        | .str _ "registerLabelAttr" => true
        | _ => false)

/-- Short context tag for a command kind, or `none` when the command is
neither context nor (potentially) a declaration wrapper. -/
def contextTag (k : SyntaxNodeKind) : Option String :=
  if k == ``Parser.Command.namespace then some "ns"
  else if k == ``Parser.Command.«end» then some "end"
  else if k == ``Parser.Command.«open» then some "open"
  else if k == ``Parser.Command.«variable» then some "var"
  else if k == ``Parser.Command.«section»
      || k == `Lean.Parser.Command.noncomputableSection then some "sec"
  else if k == ``Parser.Command.«set_option» then some "opt"
  else if k == ``Parser.Command.universe then some "univ"
  else if isNotationCmdKind k then some "nota"
  else none

/-- Decomposes a `variable` command into binders as
`(startByte, endByte, identifiers)`. -/
def decomposeVariable (stx : Syntax) : Array (Nat × Nat × Array String) := Id.run do
  let binderNodes := if stx.getArgs.size ≥ 2 then stx[1].getArgs else #[]
  let mut res : Array (Nat × Nat × Array String) := #[]
  for b in binderNodes do
    match b.getPos?, b.getTailPos? with
    | some s, some e => res := res.push (s.byteIdx, e.byteIdx, collectIdents b)
    | _, _ => pure ()
  return res

/-- `open NS (a b c)`: the namespace as spelled and the listed identifiers. -/
def openOnlyParts (stx : Syntax) : Option (String × Array String) :=
  if stx.getKind == ``Parser.Command.«open» && stx.getArgs.size ≥ 2
      && stx[1].getKind == ``Parser.Command.openOnly && stx[1].getArgs.size ≥ 3 then
    some (stx[1][0].getId.toString, collectIdents stx[1][2])
  else none

/-- The individual declaration nodes of a command: a plain command yields
itself; a `mutual … end` yields each member, so surgery applies per member
(the previous whole-command scan found only the first `declVal`). -/
partial def declarationNodes (stx : Syntax) : Array Syntax := Id.run do
  if stx.getKind != ``Parser.Command.«mutual» then return #[stx]
  let mut acc : Array Syntax := #[]
  let mut worklist : Array Syntax := #[stx]
  while !worklist.isEmpty do
    let s := worklist.back!
    worklist := worklist.pop
    if s.getKind == ``Parser.Command.declaration || s.getKind == `lemma then
      acc := acc.push s
    else
      for arg in s.getArgs do
        worklist := worklist.push arg
  return if acc.isEmpty then #[stx] else acc

/-- Edits (byte range → replacement) that turn a declaration command into
its minimal-file form: theorem proofs become `:= sorry`; a definition keeps
its value but embedded `by` blocks become `sorry`. Mutual members are
handled individually. -/
def surgeryEdits (stx : Syntax) (cmdEnd : String.Pos.Raw) : Array (Nat × Nat × String) :=
  Id.run do
    let mut edits : Array (Nat × Nat) := #[]
    let mut sorried : Array (Nat × Nat × String) := #[]
    for node in declarationNodes stx do
      let nodeEnd := (node.getTailPos?).getD cmdEnd
      if isTheoremDecl node then
        if let some valStart := findDeclValStx? node >>= (·.getPos?) then
          sorried := sorried.push (valStart.byteIdx, nodeEnd.byteIdx, ":= sorry")
      else
        if let some v := findDeclValStx? node then
          for (s, e) in collectByBlocks v do
            -- Nested `byTactic` wrappers can yield the same byte range
            -- twice; duplicate edits would emit `sorrysorry`.
            if !edits.contains (s.byteIdx, e.byteIdx) then
              edits := edits.push (s.byteIdx, e.byteIdx)
              sorried := sorried.push (s.byteIdx, e.byteIdx, "sorry")
    return sorried

/-- Every identifier in `stx` paired with its start byte position. -/
partial def collectIdentsWithPos (stx : Syntax) : Array (String × Nat) := Id.run do
  let mut acc : Array (String × Nat) := #[]
  let mut worklist : Array Syntax := #[stx]
  while !worklist.isEmpty do
    let s := worklist.back!
    worklist := worklist.pop
    if s.isIdent then
      if let some pos := s.getPos? then
        acc := acc.push (s.getId.toString, pos.byteIdx)
    for a in s.getArgs do
      worklist := worklist.push a
  return acc

/-- Pool modules transitively imported by `module` (inclusive), from the
environment's import graph. Restricts the syntactic-deps scan to
declarations actually visible at the command — a short name matching a
declaration in a *sibling* namespace of an unimported module must not
resolve (it wouldn't in Lean either). -/
def moduleImportClosure (env : Environment) (module : Name) : NameSet := Id.run do
  let mut closure : NameSet := {}
  let mut stack : Array Name := #[module]
  while h : stack.size > 0 do
    let current := stack[stack.size - 1]
    stack := stack.pop
    if closure.contains current then continue
    closure := closure.insert current
    if let some idx := env.getModuleIdx? current then
      if h2 : idx.toNat < env.header.moduleData.size then
        for imported in env.header.moduleData[idx.toNat].imports do
          if isPoolModule imported.module then
            stack := stack.push imported.module
  return closure

/-- Exposed declarations a command's *source* mentions by (possibly
partially qualified) name, restricted to `visibleModules`. Elaborated terms
lose references that only exist syntactically — `simp only [name]` lists,
tactic arguments, reducible definitions inlined during elaboration — so the
builder needs this closure for commands whose bodies are kept. -/
def syntacticDeps (env : Environment) (stx : Syntax) (self : Array Name)
    (exposedByLast : Std.HashMap String (Array Name))
    (visibleModules : NameSet) : Array Name := Id.run do
  -- Scan only the parts that survive surgery: a theorem's proof is replaced
  -- by `sorry`, so identifiers at or past its `declVal` don't contribute.
  let mut idents : Array String := #[]
  for node in declarationNodes stx do
    let pairs := collectIdentsWithPos node
    match (if isTheoremDecl node then
        findDeclValStx? node >>= (·.getPos?) else none) with
    | none => idents := idents ++ pairs.map (·.1)
    | some valStart =>
      idents := idents
        ++ (pairs.filter (fun (_, pos) => pos < valStart.byteIdx)).map (·.1)
  let mut acc : NameSet := {}
  for ident in idents do
    let lastComponent := (ident.splitOn ".").getLastD ident
    for candidate in exposedByLast.getD lastComponent #[] do
      if self.contains candidate then continue
      let visible := match env.getModuleIdxFor? candidate with
        | some idx => visibleModules.contains env.header.moduleNames[idx.toNat]!
        | none => false
      unless visible do continue
      let cstr := candidate.toString
      if cstr == ident || cstr.endsWith ("." ++ ident) then
        acc := acc.insert candidate
  return acc.toArray

/-- True when `stx` contains the source range of an exposed declaration.
Declaration ranges come from the imported environment, so this recognizes
wrapper commands (`open ... in`, `mutual`, attributes, and so on) without
trying to duplicate Lean's declaration-command taxonomy. -/
def containsDeclaration (declPos : Std.HashMap Nat (Array Name)) (stx : Syntax) : Bool :=
  match stx.getPos?, stx.getTailPos? with
  | some start, some stop =>
    declPos.any fun pos _ => start.byteIdx ≤ pos && pos < stop.byteIdx
  | _, _ => false

/-- Parse a module while elaborating only commands that can affect the parser
or command scope. The module's compiled environment is already loaded, so
elaborating declarations is both redundant and incorrect for this use: public
declarations merely fail as already declared, while `private` declarations get
fresh internal names and may execute their proof terms again. Context commands
must still be elaborated so later commands see local notation, namespaces,
variables, options, and sections exactly as the original source did. -/
partial def parseCommands (declPos : Std.HashMap Nat (Array Name)) :
    Frontend.FrontendM Unit := do
  Frontend.updateCmdPos
  let cmdState ← Frontend.getCommandState
  let inputCtx ← Frontend.getInputContext
  let parserState ← Frontend.getParserState
  let scope := cmdState.scopes.head!
  let parserContext := {
    env := cmdState.env
    options := scope.opts
    currNamespace := scope.currNamespace
    openDecls := scope.openDecls
  }
  let (stx, nextParserState, messages) :=
    Parser.parseCommand inputCtx parserContext parserState cmdState.messages
  modify fun state => { state with commands := state.commands.push stx }
  Frontend.setParserState nextParserState
  Frontend.setMessages messages
  unless containsDeclaration declPos stx && !isNotationCmdKind stx.getKind do
    Frontend.elabCommandAtFrontend stx
  unless Parser.isTerminalCommand stx do
    parseCommands declPos

/-- Processes one module source: classifies each command and emits the JSON
entry list. `declPos` maps range-start byte indices to exposed declaration
names (several may share one range start); `notationKindsAt` maps range-start byte indices to pool parser-kind
names (so a notation command learns which kinds it defines);
`notationDeps` maps parser kinds to their expansion's exposed constants;
`allNotationKinds` is the pool-wide kind set for `usedNotations`. -/
def processFile (env : Environment) (source : String) (filePath : String)
    (declPos : Std.HashMap Nat (Array Name)) (notationKindsAt : Std.HashMap Nat Name)
    (notationDeps : Std.HashMap Name (Array Name)) (allNotationKinds : NameSet)
    (exposedByLast : Std.HashMap String (Array Name)) (visibleModules : NameSet) :
    IO (Array Json) := do
  let inputCtx := Parser.mkInputContext source filePath
  let (_, parserState, messages) ← Parser.parseHeader inputCtx
  let cmdState := Command.mkState env messages {}
  let initialState : Frontend.State := {
    commandState := cmdState
    parserState
    cmdPos := parserState.pos
  }
  let (_, s) ← (parseCommands declPos).run { inputCtx } |>.run initialState
  let mut entries : Array Json := #[]
  let mut nsPrefixStack : Array Name := #[Name.anonymous]
  for stx in s.commands do
    if stx.getKind == ``Parser.Module.header then continue
    let some cmdStart := stx.getPos? | continue
    let some cmdEnd := stx.getTailPos? | continue
    let mut declNames : Array Name := #[]
    for (pos, names) in declPos do
      if pos ≥ cmdStart.byteIdx && pos < cmdEnd.byteIdx then
        declNames := declNames ++ names
    let mut kindNames : Array Name := #[]
    for (pos, kindName) in notationKindsAt do
      if pos ≥ cmdStart.byteIdx && pos < cmdEnd.byteIdx then
        kindNames := kindNames.push kindName
    -- Notation/tactic-defining commands (`elab "casesPlayer" : tactic`,
    -- `macro …`) also *define* constants, but they must be replayed as
    -- context so the syntax they introduce still parses.
    if !declNames.isEmpty && !isNotationCmdKind stx.getKind then
      let used := (collectSyntaxKinds stx).toArray.map normalizeKind
        |>.filter allNotationKinds.contains
      let sd := syntacticDeps env stx declNames exposedByLast visibleModules
      entries := entries.push <| Json.mkObj <| [
        ("t", Json.str "d"),
        ("s", Json.num cmdStart.byteIdx),
        ("e", Json.num cmdEnd.byteIdx),
        ("n", toJson (declNames.map escapeName))
      ] ++ (let ed := surgeryEdits stx cmdEnd
            if ed.isEmpty then [] else
              [("ed", Json.arr (ed.map fun (a, b, r) =>
                Json.arr #[Json.num a, Json.num b, Json.str r]))])
        ++ (if used.isEmpty then [] else [("un", toJson (used.map escapeName))])
        ++ (if sd.isEmpty then [] else [("sd", toJson (sd.map escapeName))])
    else if let some tag := contextTag stx.getKind then
      let kind := stx.getKind
      let nsName? :=
        if kind == ``Parser.Command.namespace && stx.getArgs.size ≥ 2 then
          some stx[1].getId
        else if kind == ``Parser.Command.«end» && stx.getArgs.size ≥ 2 then
          -- `end A.B` names what it closes; the builder needs it to pop the
          -- right number of (dotted) scope components. The optional name may
          -- be a direct ident or wrapped in a null node.
          if stx[1].isIdent then some stx[1].getId
          else if stx[1].getNumArgs ≥ 1 && stx[1][0].isIdent then some stx[1][0].getId
          else none
        else none
      -- Only `namespace` commands qualify and push; `end`/`section` manage
      -- the stack without contributing a qualified name.
      let qualifiedNs? := if kind == ``Parser.Command.namespace then
        nsName?.map (nsPrefixStack.back! ++ ·) else none
      if let some ns := qualifiedNs? then
        nsPrefixStack := nsPrefixStack.push ns
      else if tag == "sec" then
        nsPrefixStack := nsPrefixStack.push nsPrefixStack.back!
      else if tag == "end" && nsPrefixStack.size > 1 then
        nsPrefixStack := nsPrefixStack.pop
      let mut fields : List (String × Json) := [
        ("t", Json.str "c"),
        ("s", Json.num cmdStart.byteIdx),
        ("e", Json.num cmdEnd.byteIdx),
        ("k", Json.str tag)
      ]
      if let some ns := nsName? then
        fields := fields ++ [("ns", Json.str ns.toString)]
      if let some qns := qualifiedNs? then
        fields := fields ++ [("q", Json.str qns.toString)]
      if tag == "var" then
        let binders := decomposeVariable stx
        fields := fields ++ [("b", Json.arr (binders.map fun (a, b, ids) =>
          Json.arr #[Json.num a, Json.num b, toJson ids]))]
      if let some (ns, ids) := openOnlyParts stx then
        fields := fields ++ [("on", Json.arr #[Json.str ns, toJson ids])]
      if tag == "nota" && !kindNames.isEmpty then
        fields := fields ++ [("kn", toJson (kindNames.map escapeName))]
        let deps := kindNames.foldl (init := #[]) fun acc k =>
          acc ++ notationDeps.getD k #[]
        unless deps.isEmpty do
          fields := fields ++ [("nd", toJson (deps.map escapeName))]
      entries := entries.push (Json.mkObj fields)
  return entries

/-- Writes the per-module command tables as JSONL:
`{"m": "<module>", "c": [<entry>, …]}` per line. Only modules containing
exposed declarations or pool notation kinds are emitted. -/
def emitCommands (outPath : System.FilePath) (exposed : NameSet) (names : Array Name) :
    CoreM Unit := do
  let env ← getEnv
  let notationKinds ← poolNotationKinds env
  let notationDeps := notationExpansionDeps env exposed
  let allNotationKinds : NameSet :=
    notationKinds.foldl (init := {}) fun acc (n, _, _) => acc.insert n
  -- Index exposed names by last component for the syntactic-deps scan.
  let exposedByLast : Std.HashMap String (Array Name) :=
    exposed.toArray.foldl (init := {}) fun acc name =>
      let key := name.components.getLastD name |>.toString
      acc.insert key ((acc.getD key #[]).push name)
  -- Group exposed declarations and notation kinds by module.
  let mut declsByModule : Std.HashMap Name (Array Name) := {}
  for name in names do
    if let some idx := env.getModuleIdxFor? name then
      let module := env.header.moduleNames[idx.toNat]!
      declsByModule := declsByModule.insert module
        ((declsByModule.getD module #[]).push name)
  let mut kindsByModule : Std.HashMap Name (Array (Name × Position)) := {}
  for (kindName, module, pos) in notationKinds do
    kindsByModule := kindsByModule.insert module
      ((kindsByModule.getD module #[]).push (kindName, pos))
  IO.FS.createDirAll (outPath.parent.getD ".")
  let handle ← IO.FS.Handle.mk outPath .write
  let mut written := 0
  for moduleIdx in [0:env.header.moduleNames.size] do
    let module := env.header.moduleNames[moduleIdx]!
    unless isPoolModule module do continue
    let moduleDecls := declsByModule.getD module #[]
    let moduleKinds := kindsByModule.getD module #[]
    if moduleDecls.isEmpty && moduleKinds.isEmpty then continue
    let path := System.mkFilePath (module.components.map (·.toString))
      |>.addExtension "lean"
    let some source ← (do
        try pure (some (← IO.FS.readFile path)) catch _ => pure none)
      | continue
    let fileMap := FileMap.ofString source
    -- One range start can carry several declarations (`irreducible_def`,
    -- mutual blocks), so map each position to every name declared there.
    let mut declPos : Std.HashMap Nat (Array Name) := {}
    for name in moduleDecls do
      if let some ranges ← findDeclarationRanges? name then
        let key := (fileMap.ofPosition ranges.range.pos).byteIdx
        declPos := declPos.insert key ((declPos.getD key #[]).push name)
    let mut notationKindsAt : Std.HashMap Nat Name := {}
    for (kindName, pos) in moduleKinds do
      notationKindsAt := notationKindsAt.insert (fileMap.ofPosition pos).byteIdx kindName
    let visibleModules := moduleImportClosure env module
    let entries ← processFile env source path.toString declPos notationKindsAt
      notationDeps allNotationKinds exposedByLast visibleModules
    handle.putStrLn (Json.mkObj [
      ("m", Json.str module.toString),
      ("c", Json.arr entries)
    ]).compress
    written := written + 1
  handle.flush
  IO.println s!"exposition: wrote command tables for {written} modules to {outPath}"

end Exposition.Commands

unsafe def main (args : List String) : IO UInt32 := do
  let outPath := args[0]?.getD "exposition-dump.jsonl"
  let commandsPath := args[1]?.getD "exposition-commands.jsonl"
  -- Further arguments override the imported modules (default: the whole pool);
  -- useful for testing against a partially built tree.
  let modules := if args.length > 2 then args.drop 2 |>.map (·.toName) else [Exposition.poolRoot]
  Lean.initSearchPath (← Lean.findSysroot)
  -- Extension states must be loaded (and initializers executed) so that
  -- `IO.processCommands` can parse Mathlib/pool notations (`Type*`, ...);
  -- without them, parse-error recovery silently truncates commands.
  Lean.enableInitializersExecution
  let imports := modules.toArray.map fun module => ({ module } : Lean.Import)
  let env ← Lean.importModules imports {} (trustLevel := 1024) (loadExts := true)
  let coreContext : Lean.Core.Context := {
    fileName := "<exposition-extract>",
    fileMap := default,
    maxHeartbeats := 0
  }
  let run : Lean.CoreM Unit := do
    let (exposed, names) ← Exposition.exposedDecls env
    Exposition.extract outPath exposed names
    Exposition.Commands.emitCommands commandsPath exposed names
  let (result, _) ← run.toIO coreContext { env }
  let _ := result
  return 0
