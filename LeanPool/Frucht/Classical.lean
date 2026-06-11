/-
Copyright (c) 2026 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
import Mathlib.Data.Set.Basic

/-!
# Choice-free metaprogramming infrastructure

This file sets up the `ChoiceFree` framework used throughout the Frucht development:
the abstract `collect`/`elements` axioms modelling sets as types, the `@[classical]`,
`@[replace]`, and `@[restrict]` attributes that audit a declaration against the
trusted axioms and register choice-free surrogates, and the `elim_choice` tactic
that mechanically rewrites a proof term to use those surrogates.
-/

universe u

axiom collect : ∀ {α : Type u}, (α → Type u) → Type u
@[coe] axiom elements : ∀ {α : Type u}, α → Type u
axiom elements_inj : ∀ {α : Type u}, Function.Injective (elements (α := α))
axiom collect_ext : ∀ {α β} (f : α → Type u) (g : β → Type u),
  collect f = collect g ↔ Set.range f = Set.range g
axiom collect_elements : ∀ {α : Type u}, collect (elements (α := α)) = α

noncomputable def Classical.uniqueChoice {α : Sort u}
  (hα : Nonempty α) (_ : Subsingleton α) : α := Classical.choice hα

namespace ChoiceFree

open Lean Meta Parser Std Elab Tactic

abbrev Graph (V : Type*) [BEq V] [Hashable V] := HashMap V (HashSet V)

namespace Graph
variable {V : Type*} [BEq V] [Hashable V] [Inhabited V]

def insert' (G : Graph V) (u v : V) := G.insert u <|
  match G[u]? with
  | some x => x.insert v
  | none => {v}

def reverse (G : Graph V) : Graph V := Id.run do
  let mut H : Graph V := {}
  for (u, V) in G do
    for v in V do H ← H.insert' v u
  return H

def Reachable (G : Graph V) (S : HashSet V) : HashSet V := Id.run do
  let mut visited : HashSet V := {}
  let mut stack := S.toArray
  while !stack.isEmpty do
    let u := stack.back!
    stack ← stack.pop
    visited ← visited.insert u
    if u ∈ G then
      for v in G[u]! do
        if v ∉ visited then stack ← stack.push v
  return visited

def reverseReachable (G : Graph V) (S : HashSet V) : HashSet V := Id.run do
  Reachable (reverse G) S

def derived (G : Graph V) (S : HashSet V) := Id.run do
  let mut H : Graph V := {}
  for (u, V) in G do
    for v in V do
      if u ∈ S ∧ v ∈ S then H ← H.insert' u v
  return H

def reverseReachableDerived (G : Graph V) (S : HashSet V) :=
  G.reverse.derived (G.reverseReachable S)

def inDegrees (G : Graph V) := Id.run do
  G.reverse.fold (fun deg k v => deg.insert k v.size) (G.map fun _ _ => 0)

def topologicalOrder (G : Graph V) [Repr V] : Array V := Id.run do
  let mut sorted := #[]
  let mut indeg := G.inDegrees
  let mut q : Queue V := .empty
  for (v, deg) in indeg do
    if deg == 0 then q := q.enqueue v
  while !q.isEmpty do
    let (v, q') := q.dequeue?.get!
    q := q'
    if indeg[v]! == 0 then sorted := sorted.push v
    if let some ws := G[v]? then
      for w in ws do
        indeg := indeg.insert w (indeg[w]! - 1)
        if indeg[w]! == 0 then q := q.enqueue w
  return sorted

end Graph

structure ReplaceItem where
  name : Name
  levelPerm : Option (Array Nat)
deriving Inhabited

abbrev ChoiceFreeReplacementExtension :=
  SimpleScopedEnvExtension (Name × ReplaceItem) (HashMap Name ReplaceItem)

abbrev CachedChoiceFreeExtension :=
  SimpleScopedEnvExtension Name (HashSet Name)

initialize choiceFreeReplacementExtension : ChoiceFreeReplacementExtension ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun s (k, v) => s.insert k v
  }

initialize cachedChoiceFreeExtension : CachedChoiceFreeExtension ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun s k => s.insert k
  }

def choiceFreeAlternative (name : Name) : CoreM ReplaceItem := do
  let map := choiceFreeReplacementExtension.getState (← getEnv)
  match map[name]? with
  | some replacement => return replacement
  | none => return ⟨name, none⟩

initialize
  registerBuiltinAttribute {
    name            := `replace
    descr           := s!"Replace a definition with its choice-free version"
    applicationTime := .afterCompilation
    add             := fun decl stx kind => do
      let ⟨decl, _⟩ ← choiceFreeAlternative decl
      let ident ← Attribute.Builtin.getIdent stx
      let name ← resolveGlobalConstNoOverload ident
      let old := ((← getEnv).find? name).get!
      let new := ((← getEnv).find? decl).get!
      if old.levelParams.length != new.levelParams.length then
        throwError "The replaced theorem must have the same number of universe parameters \
          as the original"
      let check : MetaM (Array Nat) := do
        let levelMVars ← mkFreshLevelMVarsFor old
        let oldType := old.type
        let newType := new.type.instantiateLevelParams new.levelParams levelMVars
        if !(← isDefEq oldType newType) then
          throwError "The replaced theorem must have the same type as the original."
        let perm ← levelMVars.toArray.mapM fun mvar => do
          let some lvl ← getLevelMVarAssignment? mvar.mvarId!
            | throwError "Not all universe metavariables were filled."
          let .param name := lvl
            | throwError "Filled metavariable {lvl} is not a level parameter."
          return old.levelParams.findIdx (· == name)
        return perm
      let perm ← check.run'
      choiceFreeReplacementExtension.add (name, ⟨decl, some perm⟩)
  }

def mkChoiceFreeName (name : Name) := `_choiceFree ++ name
def originalName := (Name.replacePrefix · `_choiceFree .anonymous)

def replaceExpr (e : Expr) : CoreM Expr :=
  Core.transform e fun e => do
    match e with
    | .const name us =>
      let ⟨name, perm⟩ ← choiceFreeAlternative name
      match perm with
      | none => return .done (.const name us)
      | some perm => return .done <| .const name <|
        (List.range perm.size).map fun i => us[perm[i]!]!
    | _ => return .continue

def replaceDeclaration (e : Name) (replaceType : Bool := true) : CoreM Unit := do
  if (choiceFreeReplacementExtension.getState (← getEnv)).contains e then return
  let replaceExpr' (e : Expr) : CoreM Expr :=
    if replaceType then replaceExpr e else return e
  let modified : Bool ← (do
    try
      match (← getEnv).find? e with
      | ConstantInfo.defnInfo v =>
        addDecl <| .defnDecl { v with
          name := mkChoiceFreeName v.name,
          type := ← replaceExpr' v.type, value := ← replaceExpr v.value }
        return true
      | ConstantInfo.thmInfo v =>
        addDecl <| .thmDecl { v with
          name := mkChoiceFreeName v.name,
          type := ← replaceExpr' v.type, value := ← replaceExpr v.value }
        return true
      | ConstantInfo.opaqueInfo v =>
        addDecl <| .opaqueDecl { v with
          name := mkChoiceFreeName v.name,
          type := ← replaceExpr' v.type, value := ← replaceExpr v.value }
        return true
      | _ => return false
    catch ex =>
      throwError m!"Error when replacing definition {e}:\n{ex.toMessageData}")
  if modified then
    choiceFreeReplacementExtension.add (e, ⟨mkChoiceFreeName e, none⟩)

namespace CollectAxioms

structure State where
  visited : HashSet Name := {}
  axioms : HashSet Name := {}
  dependencies : Graph Name := {}

abbrev M := StateT State CoreM

partial def collect (c : Name) (stopSet : HashSet Name) : M Unit := do
  let collectExpr (e : Expr) : M Unit := e.getUsedConstants.forM fun ident => do
    modify fun s => { s with dependencies := s.dependencies.insert' c ident }
    collect ident stopSet
  let s ← get
  unless s.visited.contains c do
    modify fun s => { s with visited := s.visited.insert c }
    if stopSet.contains c then
      modify fun s => { s with axioms := s.axioms.insert c }
    else
      match (← getEnv).checked.get.find? c with
      | some (ConstantInfo.axiomInfo v)  =>
        collectExpr v.type
        modify fun s => { s with axioms := s.axioms.insert c }
      | some (ConstantInfo.defnInfo v)   => collectExpr v.type *> collectExpr v.value
      | some (ConstantInfo.thmInfo v)    => collectExpr v.type *> collectExpr v.value
      | some (ConstantInfo.opaqueInfo v) => collectExpr v.type *> collectExpr v.value
      | some (ConstantInfo.quotInfo _)   => pure ()
      | some (ConstantInfo.ctorInfo v)   => collectExpr v.type
      | some (ConstantInfo.recInfo v)    => collectExpr v.type
      | some (ConstantInfo.inductInfo v) =>
        collectExpr v.type *> v.ctors.forM fun ctor => do
          modify fun s => { s with dependencies := s.dependencies.insert' c ctor }
          collect ctor stopSet
      | none                             => pure ()

def collectAxioms (constName : Name) (stopSet : HashSet Name) :
    CoreM (HashSet Name × Graph Name) := do
  let (_, s) ← (CollectAxioms.collect constName stopSet).run {}
  pure (s.axioms, s.dependencies)

end CollectAxioms

def allowedAxioms : HashSet Name := {
  ``sorryAx, ``propext, ``Quot.sound,
  ``Classical.em, ``Classical.uniqueChoice,
  ``collect, ``elements, ``elements_inj, ``collect_ext, ``collect_elements
}

def showDependencyGraph (dependencies : Graph Name) : Format :=
  let showName (name : Name) : Format :=
    .text (originalName name).toString
  let showNameSet (key : Name) (set : HashSet Name) : Format := .nest 2 (
    f!"{showName key} is used by:" ++ .line ++
    .nest 1 ("[" ++ Format.join ((set.toList.map showName).intersperse ("," ++ .line)) ++ "]")
  )
  let order := dependencies.topologicalOrder
  Format.join <| List.intersperse .line <|
    (order.toList.filterMap fun name => dependencies[name]?.map (showNameSet name))

def registerClassical (strict : Bool) (decl : Name) (stx : Syntax) (kind : AttributeKind) :
    AttrM Unit := do
  Attribute.Builtin.ensureNoArgs stx
  unless kind == AttributeKind.global do
    throwError "invalid attribute 'classical', must be global"
  let replaced := (choiceFreeReplacementExtension.getState (← getEnv)).keys.foldl
    Std.HashSet.insert {}
  let cached := cachedChoiceFreeExtension.getState (← getEnv)
  let (_, dependencies) ← CollectAxioms.collectAxioms decl
    (allowedAxioms ∪ replaced ∪ cached ∪ HashSet.ofArray (cached.toArray.map originalName))
  let dependencyOrder := dependencies.reverseReachableDerived replaced |>.topologicalOrder
  for defn in dependencyOrder do
    replaceDeclaration defn (!strict || defn != decl)
  let ⟨decl, _⟩ ← choiceFreeAlternative decl
  let (usedAxioms, dependencies) ←
    CollectAxioms.collectAxioms decl <|
    if strict then allowedAxioms else allowedAxioms ∪ cached
  let unallowedAxioms := usedAxioms.filter
    fun x => !(allowedAxioms.contains x || cached.contains x)
  if strict && usedAxioms.contains ``sorryAx then
    throwError f!"Strict mode doesn't allow `sorry`"
  if !unallowedAxioms.isEmpty then
    throwError (
      f!"invalid attribute 'classical', the definition used axioms {unallowedAxioms.toList}\n" ++
      showDependencyGraph dependencies
    )
  for (name, depends) in dependencies do
    cachedChoiceFreeExtension.add name
    for name' in depends do
      cachedChoiceFreeExtension.add name'

initialize
  registerBuiltinAttribute {
    name            := `classical
    descr           := s!"Ensure that the definition is in the classical ZF set theory"
    applicationTime := .afterCompilation
    add             := registerClassical false
  }

initialize
  registerBuiltinAttribute {
    name            := `classical!
    descr           := s!"Ensure that the definition is in the classical ZF set theory, \
      but not replacing the type of the theorem"
    applicationTime := .afterCompilation
    add             := registerClassical true
  }

section ElimChoiceTactic

abbrev ClassicalRestrictExtension :=
  SimpleScopedEnvExtension
    (Name × Name × Array Int)
    (HashMap Name (Array (Name × Array Int)))

def intLit := optional "-" >> numLit
@[attr_parser] def restrict :=
  leading_parser "restrict" >> ppSpace >> ident >> many (ppSpace >> intLit)

initialize classicalRestrictExtension : ClassicalRestrictExtension ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun s (k, v, pos) => s.insert k ((s.getD k #[]).push (v, pos))
  }

initialize
  registerBuiltinAttribute {
    name            := `restrict
    descr           := s!"Adding some restriction to get the theorem free of choice"
    applicationTime := .afterCompilation
    add             := fun decl stx kind => do
      let name ← resolveGlobalConstNoOverload stx[1]
      let pos := stx[2].getArgs.map <| fun x =>
        match x[0].getOptional? with
        | some _ => -x[1].toNat - 1
        | none => x[1].toNat
      classicalRestrictExtension.add (name, (decl, pos))
  }

def expandApp : Expr → Expr × Array Expr
  | .app f x => let (f, args) := expandApp f; (f, args.push x)
  | e => (e, #[])

def expandArgs' : Expr → Expr × Array Expr
  | .forallE _ type body _ => let (body, args) := expandArgs' body; (body, args.push type)
  | e => (e, #[])

def expandArgs (e : Expr) : Expr × Array Expr :=
  let (body, args) := expandArgs' e
  (body, args.reverse)

inductive Binder where
  | forallE (name : Name) (type : Expr) (info : BinderInfo)
  | letE (name : Name) (type : Expr) (value : Expr)
deriving Repr, Inhabited, BEq, Hashable

abbrev Binders := Array Binder

def dsimp' (e : Expr) : MetaM Expr := do
  let ctx ← Simp.mkContext (config := {dsimp := true})
  return (← Meta.dsimp e ctx).1

def reverts : Binders × Expr → Expr :=
  fun (xs, e) => reverts' (xs.toList, e)
where
  reverts' : (xs : List Binder × Expr) → Expr
    | (.forallE name type info :: xs, e) => .forallE name type (reverts' (xs, e)) info
    | (.letE name type value :: xs, e) => .letE name type value (reverts' (xs, e)) false
    | ([], e) => e

def appBVars (e : Expr) (ctx : Binders) :=
  (Array.range ctx.size).foldr (fun i e =>
    match ctx[i]! with
    | .forallE .. => mkApp e (.bvar i)
    | _ => e) e

def introsP (mvarId : MVarId) (maxVars : Nat) : MetaM (Array FVarId × MVarId) := do
  let type ← mvarId.getType
  let type ← instantiateMVars type
  let n := getIntrosSize type
  if n == 0 then
    return (#[], mvarId)
  else
    mvarId.introNP (min n maxVars)

structure ElimChoiceState where
  goals : Array MVarId := #[]
  mvars : HashMap Expr Expr := {}
  usings : Array Name := #[]

abbrev M := StateT ElimChoiceState MetaM

partial def elimChoice (ctx : Binders) (e : Expr) : M Expr :=
  let f := elimChoice ctx
  match e with
  | .app _ _ => do
    let (fn, args) := expandApp e
    let args ← args.mapM f
    match fn with
    | .const name us =>
      let map := classicalRestrictExtension.getState (← getEnv)
      match map[name]? with
      | some candidates => do
        let intersection := candidates.filter (·.1 ∈ (← get).usings)
        let (newfn, pos) :=
          if !intersection.isEmpty then intersection[0]!
          else candidates[0]!
        let expr : M (Option Expr) := do
          let newFnConstant := ((← getEnv).find? newfn).get!
          let (_, newArgs) := expandArgs newFnConstant.type
          let mut args := args
          let getMVar (i : Nat) : M Expr := do
            let holeType := newArgs[i]!
              |>.instantiateLevelParams newFnConstant.levelParams us
              |>.instantiateRevRange 0 i args
            let holeType ← dsimp' (reverts (ctx, holeType))
            for (type, mvar) in (← get).mvars do
              if ← isDefEq type holeType then return appBVars mvar ctx
            let mvar ← mkFreshExprMVar holeType
            let (_, newMVar) ← introsP mvar.mvarId! ctx.size
            modify fun s => { s with
              mvars := s.mvars.insert holeType mvar
              goals := s.goals.push newMVar
            }
            return appBVars mvar ctx
          for i in pos do
            if -args.size ≤ i ∧ i < 0 then args := args.eraseIdx! (i.natAbs - 1)
            else if i ≤ args.size then args := args.insertIdx! i.natAbs (← getMVar i.natAbs)
            else return none
          trace[ElimChoice.verbose] "Choice-free replacement used: {newfn}"
          return some (mkAppN (mkConst newfn us) args)
        match ← expr with
        | some e => return e
        | none => return mkAppN (← f fn) args
      | none => return mkAppN (← f fn) args
    | _ => return mkAppN (← f fn) args
  | .lam name type body info =>
    return .lam name (← f type)
      (← elimChoice (ctx.push (.forallE name type info)) body) info
  | .forallE name type body info =>
    return .forallE name (← f type)
      (← elimChoice (ctx.push (.forallE name type info)) body) info
  | .letE name type value body nondep =>
    return .letE name (← f type) (← f value)
      (← elimChoice (ctx.push (.letE name type value)) body) nondep
  | .mdata data expr =>
    return .mdata data (← f expr)
  | .proj name idx expr =>
    return .proj name idx (← f expr)
  | e => return e

def mkPrivateName' (module : Name) (name : Name) : Name :=
  Name.mkNum (privateHeader ++ module) 0 ++ name

syntax "elim_choice" term ("unfolding" (colGt ident)*)?
  ("private" ((colGt ident)+ "in" ident)+)? ("using" (colGt ident)+)? : tactic

elab_rules : tactic
| `(tactic| elim_choice $e $[unfolding $ids*]?
    $[private $[$[$privs]* in $modules]*]? $[using $usings*]?) =>
  withMainContext do
    let old ← Term.elabTermAndSynthesize e none
    let constNames :=
      match expandApp old with
      | (.const name _, _) => #[name]
      | (_, _) => #[]
    let mut ids := constNames ++ (← (ids.getD #[]).mapM resolveGlobalConstNoOverload)
    if privs.isSome then
      for (module, priv_of_ns) in modules.get!.zip privs.get! do
        for priv in priv_of_ns do
          ids := ids.push (mkPrivateName' module.getId priv.getId)
    let old ← whnf old
    let old ← deltaExpand (allowOpaque := true) old
      fun name => ids.any (fun id => id.isPrefixOf (privateToUserName name))
    let old ← dsimp' old
    let (new, result) ← (elimChoice {} old).run {
      usings := ← (usings.getD #[]).mapM resolveGlobalConstNoOverload
    }
    (← getMainGoal).assign new
    replaceMainGoal result.goals.toList

end ElimChoiceTactic

initialize
  registerTraceClass `ElimChoice.verbose

end ChoiceFree
