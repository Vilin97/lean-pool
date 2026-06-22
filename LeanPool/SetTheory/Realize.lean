/-
Copyright (c) 2026 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
import Mathlib.ModelTheory.ElementaryMaps
import Mathlib.ModelTheory.Semantics
import Mathlib.Tactic.FinCases
import LeanPool.SetTheory.SimpAttr

/-!
# Realization machinery for the ZF first-order language

This module sets up the first-order language `𝓛ZF` of ZF set theory with a single
membership relation, together with notation and metaprogramming infrastructure for
building and realizing bounded formulas in models of ZF.
-/

open Lean Parser Elab Term Meta Qq Std FirstOrder.Language

/-- The `memRel` type. -/
inductive memRel : ℕ → Type
  | mem : memRel 2
  deriving DecidableEq

open FirstOrder in
/-- The first-order language of ZF set theory, with a single binary membership relation. -/
def 𝓛ZF : FirstOrder.Language := ⟨fun _ => Empty, memRel⟩
deriving IsRelational

namespace FirstOrder.Language.BoundedFormula

open Language

variable {α n} {L : Language} {M} [L.Structure M] (v : α → M) (w : Fin n → M)

lemma realize_isFormula (φ : L.BoundedFormula α 0) (w : Fin 0 → M) :
    φ.Realize v w ↔ Formula.Realize φ v := by
  simp only [Formula.Realize]
  convert Iff.rfl

/-- The `exUnique` declaration. -/
protected def exUnique (φ : L.BoundedFormula α (n + 1)) : L.BoundedFormula α n :=
  ∃' (φ ⊓ ∀' (φ.liftAt 1 n ⟹ &(Fin.last (n + 1)) =' &((Fin.last n).castSucc)))

/-- The `ite` declaration. -/
protected def ite (φ ψ χ : L.BoundedFormula α n) : L.BoundedFormula α n :=
  (φ ⊓ ψ) ⊔ (∼φ ⊓ χ)

theorem realize_ite (φ ψ χ : L.BoundedFormula α n) :
    (φ.ite ψ χ).Realize v w ↔
      (φ.Realize v w ∧ ψ.Realize v w) ∨ (¬φ.Realize v w ∧ χ.Realize v w) := by
  simp [BoundedFormula.ite]

theorem realize_exUnique (φ : L.BoundedFormula α (n + 1)) :
    φ.exUnique.Realize v w ↔ ∃! a : M, φ.Realize v (Fin.snoc w a) := by
  have (x y : M) : Fin.snoc (Fin.snoc w x) y ∘
      (fun i : Fin (n + 1) => if (i : ℕ) < n then i.castSucc else i.succ)
      = Fin.snoc w y := by
    ext i
    simp only [Function.comp_apply]
    split_ifs with hi
    · simp [Fin.snoc, hi, _root_.le_of_lt hi]
    · replace hi := Decidable.not_imp_symm Fin.val_lt_last hi
      simp [hi]
  simp [BoundedFormula.exUnique, realize_liftAt_one, ExistsUnique, this]

variable {k} (φ : L.Formula (Fin (k + 1)))

/-- The `FormulaToFunction` type. -/
class _root_.FormulaToFunction (f : outParam ((Fin k → M) → M)) where
  realize_iff_fn {v : Fin (k + 1) → M} :
      φ.Realize v ↔ f (v ∘ Fin.castSucc) = v (.last k) := by
    simp only [Fin.reduceCastSucc, Fin.reduceLast, Nat.reduceAdd,
      realize_simps, implies_true]

variable (vars : Fin k → α ⊕ Fin n) (ψ : L.BoundedFormula α (n + 1))

/-- The `ofFunc` declaration. -/
def ofFunc := ∃' (BoundedFormula.relabel (k := 0)
  (Fin.snoc (Sum.map id Fin.castSucc ∘ vars) (.inr (.last n))) φ ⊓ ψ)

lemma realize_ofFunc {f} [FormulaToFunction φ f] :
    (ofFunc φ vars ψ).Realize v w ↔
    ψ.Realize v (Fin.snoc w (f (Sum.elim v w ∘ vars))) := by
  simp (unfoldPartialApp := true) [
    ofFunc, realize_isFormula, FormulaToFunction.realize_iff_fn,
    Function.comp, Sum.elim_map
  ]

attribute [realize_simps]
  realize_all realize_ex realize_bot realize_top realize_not realize_inf realize_sup
  realize_imp realize_iff realize_rel₂ realize_bdEqual realize_relabel realize_ite
  realize_exUnique realize_ofFunc Term.realize_var Function.comp

/-- The `#_` notation. -/
scoped[FirstOrder] prefix:arg "#" => Term.var ∘ Sum.inl
/-- The `_∈ᶻ'_` notation: membership in the ZF first-order language `𝓛ZF`. -/
scoped[FirstOrder] infix:88 " ∈ᶻ' " => Relations.boundedFormula₂ (L := 𝓛ZF) memRel.mem

/-- The `label` declaration. -/
declare_syntax_cat label
/-- The `label#_` declaration. -/
syntax "#" num : label
/-- The `label&_` declaration. -/
syntax "&" num : label
/-- The `Value_of_labels(_)` declaration. -/
syntax "value_of_labels(" label,* ")" : term
/-- The `_@(_)` notation. -/
syntax term "@(" label,* ")" : term
macro_rules
  | `($f:ident@($labels:label,*)) =>
    `(BoundedFormula.relabel
      value_of_labels($labels,*) $(mkIdent (f.getId ++ `formula)) (k := 0))
  | `(value_of_labels(#$n, $labels,*)) =>
    `(Matrix.vecCons (Sum.inl $n) value_of_labels($labels,*))
  | `(value_of_labels(&$n, $labels,*)) =>
    `(Matrix.vecCons (Sum.inr $n) value_of_labels($labels,*))
  | `(value_of_labels(#$n)) => `(Matrix.vecCons (Sum.inl $n) ![])
  | `(value_of_labels(&$n)) => `(Matrix.vecCons (Sum.inr $n) ![])
  | `(value_of_labels()) => `(Matrix.vecEmpty)

end FirstOrder.Language.BoundedFormula

section ZFStructure

open FirstOrder Language Structure

/-- The `ZFFormula` declaration. -/
abbrev ZFFormula (n : ℕ) := 𝓛ZF.Formula (Fin n)
/-- The `ZFStructure` declaration. -/
abbrev ZFStructure M := 𝓛ZF.Structure M

variable {M N : Type*} [sM : ZFStructure M] [sN : ZFStructure N]

instance (priority := high) instMembershipZFStructure : Membership M M where
  mem x y := sM.RelMap memRel.mem ![y, x]

instance instHasSubsetM : HasSubset M where
  Subset x y := ∀ ⦃z⦄, z ∈ x → z ∈ y

/-- The `ElementaryEmbeddingClass` type. -/
class ElementaryEmbeddingClass
    (F : Type*) (M N : outParam Type*)
    [ZFStructure M] [ZFStructure N] [FunLike F M N] : Prop where
  map_formula : ∀ (f : F) ⦃n⦄ (φ : 𝓛ZF.Formula (Fin n)) (x : Fin n → M),
    φ.Realize (f ∘ x) ↔ φ.Realize x

instance : ElementaryEmbeddingClass (M ↪ₑ[𝓛ZF] N) M N where
  map_formula := fun j => j.map_formula'

lemma Fin.two_def {α} (x : Fin 2 → α) : x = ![x 0, x 1] := by
  ext i; fin_cases i <;> simp

@[realize_simps] lemma relMap_mem_iff_membership {v : Fin 2 → M} :
    RelMap (L := 𝓛ZF) memRel.mem v ↔ v 0 ∈ v 1 := by
  conv_lhs => rw [Fin.two_def v]
  rfl

/-- The `HasEmpty` type. -/
class HasEmpty (M) [ZFStructure M] where
  exists_empty : ∃! x : M, ∀ y, y ∉ x

/-- The `EqEmptyN` declaration. -/
def EqEmptyN (n : ℕ) : ZFFormula (n + 1) := ∀' ∼(&0 ∈ᶻ' #(Fin.last n))

variable {n} [HasEmpty M]

noncomputable instance (priority := low) instEmptyCollectionM : EmptyCollection M where
  emptyCollection := HasEmpty.exists_empty.choose

@[realize_simps] lemma EqEmptyN.realize_iff {v : Fin (n + 1) → M} :
    (EqEmptyN n).Realize v ↔ ∅ = v (Fin.last n) := by
  simp only [EqEmptyN, Formula.Realize, realize_simps]
  rw [iff_comm]
  exact HasEmpty.exists_empty.choose_eq_iff

end ZFStructure

namespace EncodeExpr

/-- The `WeakLevel` type. -/
inductive WeakLevel where
  | a : WeakLevel
  | b : WeakLevel → WeakLevel
  | c : WeakLevel → WeakLevel → WeakLevel
  | d : WeakLevel → WeakLevel → WeakLevel
  | e : String → WeakLevel
deriving FromJson, ToJson, Inhabited, Repr

/-- The `WeakBinderInfo` type. -/
inductive WeakBinderInfo where
  | a | b | c | d
deriving FromJson, ToJson, Inhabited, Repr

/-- The `WeakExprItem` type. -/
inductive WeakExprItem where
  | a : Nat → WeakExprItem
  | b : WeakLevel → WeakExprItem
  | c : Nat → List WeakLevel → WeakExprItem
  | d : Nat → Nat → WeakExprItem
  | e : Nat → Nat → Nat → Nat → WeakExprItem
  | f : Nat → Nat → Nat → Nat → WeakExprItem
  | g : Nat → Nat → Nat → Nat → Bool → WeakExprItem
  | h : Nat → WeakExprItem
  | i : String → WeakExprItem
  | j : Nat → Nat → Nat → WeakExprItem
deriving FromJson, ToJson, Inhabited, Repr

/-- The `toWeakLevel` declaration. -/
def _root_.Lean.Level.toWeakLevel : Level → WeakLevel
  | .zero => .a
  | .succ u => .b u.toWeakLevel
  | .max u v => .c u.toWeakLevel v.toWeakLevel
  | .imax u v => .d u.toWeakLevel v.toWeakLevel
  | .param name => .e name.toString
  | .mvar _ => default

/-- The `toLevel` declaration. -/
def WeakLevel.toLevel : WeakLevel → Level
  | .a => .zero
  | .b u => .succ u.toLevel
  | .c u v => .max u.toLevel v.toLevel
  | .d u v => .imax u.toLevel v.toLevel
  | .e name => .param name.toName

/-- The `toNat` declaration. -/
def _root_.Lean.BinderInfo.toNat : BinderInfo → Nat
  | .default => 0
  | .implicit => 1
  | .strictImplicit => 2
  | .instImplicit => 3

/-- The `toBinderInfo` declaration. -/
def _root_.Nat.toBinderInfo : Nat → BinderInfo
  | 0 => .default
  | 1 => .implicit
  | 2 => .strictImplicit
  | 3 => .instImplicit
  | _ => .default

/-- The numeric encoding of binder information round-trips back to the original. -/
theorem _root_.Lean.BinderInfo.toNat_toBinderInfo (bi : BinderInfo) :
    bi.toNat.toBinderInfo = bi := by
  cases bi <;> rfl

/-- The numeric `BinderInfo` encoding is injective on the four valid binder kinds. -/
theorem _root_.Lean.BinderInfo.toNat_injective {bi bj : BinderInfo}
    (h : bi.toNat = bj.toNat) : bi = bj := by
  rw [← bi.toNat_toBinderInfo, ← bj.toNat_toBinderInfo, h]

/-- Mutable state threaded through expression serialization: deduplicating maps from
subexpressions and names to their indices, together with the output arrays. -/
structure WeakExprState where
  /-- Cache from already-serialized subexpressions to their indices. -/
  hashExpr : HashMap Expr Nat := {}
  /-- Cache from already-serialized names to their indices. -/
  hashName : HashMap Name Nat := {}
  /-- The serialized expression items, indexed in insertion order. -/
  arrayExpr : Array WeakExprItem := #[]
  /-- The serialized name strings, indexed in insertion order. -/
  arrayName : Array String := #[]

/-- A serialized closed expression: the array of expression items together with the
array of referenced name strings. -/
abbrev WeakExpr := Array WeakExprItem × Array String

/-- The serialization monad: a state monad over `WeakExprState` with failure. -/
abbrev SerializeM := OptionT (StateM WeakExprState)

/-- Append a new serialized item for `e`, recording its index in the cache. -/
def add (e : Expr) (i : WeakExprItem) : SerializeM Nat := do
  modify fun s => { s with
    hashExpr := s.hashExpr.insert e s.hashExpr.size,
    arrayExpr := s.arrayExpr.push i
  }
  return (← get).arrayExpr.size - 1

/-- Serialize a name, returning the index of its (deduplicated) string. -/
def addName (name : Name) : SerializeM Nat := do
  if let some n := (← get).hashName.get? name then return n
  modify fun s => { s with
    hashName := s.hashName.insert name s.hashName.size,
    arrayName := s.arrayName.push name.toString
  }
  return (← get).arrayName.size - 1

/-- Recursively serialize an expression into the state, returning its index. -/
def toWeakExprAux (e : Expr) : SerializeM Nat := do
  if let some n := (← get).hashExpr.get? e then return n
  match e with
  | .bvar n => add e (.a n)
  | .fvar _ => failure
  | .mvar _ => failure
  | .sort u => add e (.b u.toWeakLevel)
  | .const name levels => add e (.c (← addName name) (levels.map (·.toWeakLevel)))
  | .app s t => do add e (.d (← toWeakExprAux s) (← toWeakExprAux t))
  | .lam name type body info => do
    add e (.e (← addName name) (← toWeakExprAux type) (← toWeakExprAux body) info.toNat)
  | .forallE name type body info => do
    add e (.f (← addName name) (← toWeakExprAux type) (← toWeakExprAux body) info.toNat)
  | .letE name type value body nondep => do
    add e (.g (← addName name) (← toWeakExprAux type) (← toWeakExprAux value)
      (← toWeakExprAux body) nondep)
  | .lit (.natVal n) => add e (.h n)
  | .lit (.strVal str) => add e (.i str)
  | .mdata _ e => toWeakExprAux e
  | .proj name idx struct => do add e (.j (← addName name) idx (← toWeakExprAux struct))

/-- Serialize a closed expression into its `WeakExpr` representation. -/
def _root_.Lean.Expr.toWeakExpr (e : Expr) : WeakExpr :=
  let result := ((toWeakExprAux e).run {}).2
  (result.arrayExpr, result.arrayName)

/-- The `toExpr` declaration. -/
def WeakExpr.toExpr (e : WeakExpr) : Expr := Id.run do
  let (xs, names) := (e.1, e.2.map (·.toName))
  let mut es : Array Expr := #[]
  for i in *...xs.size do
    let value : Expr :=
      match xs[i]! with
      | .a n => .bvar n
      | .b u => .sort u.toLevel
      | .c name u => .const names[name]! (u.map (·.toLevel))
      | .d s t => .app es[s]! es[t]!
      | .e name type body info => .lam names[name]! es[type]! es[body]! info.toBinderInfo
      | .f name type body info => .forallE names[name]! es[type]! es[body]! info.toBinderInfo
      | .g name type value body nondep => .letE names[name]! es[type]! es[value]! es[body]! nondep
      | .h n => mkNatLit n
      | .i str => mkStrLit str
      | .j name idx struct => .proj names[name]! idx es[struct]!
    es := es.push value
  return es[es.size - 1]!

/-- The `HeadBeta(_)` declaration. -/
elab "headBeta(" t:term ")" : term => do
  let result ← elabTerm t none
  return result.headBeta

/-- The `Expr(_)` declaration. -/
elab "expr(" e:strLit ")" : term => do
  let e := ((Json.parse e.getString) >>= fromJson? : Except _ WeakExpr).toOption.get!.toExpr
  let levels := (collectLevelParams {} e).params.toList
  let mvars ← mkFreshLevelMVars levels.length
  return e.instantiateLevelParams levels mvars

/-- The `toSyntax'` declaration. -/
def _root_.Lean.Expr.toSyntax'
    {m} [Monad m] [MonadQuotation m] (e : Expr) : m Term := do
  let strLit := Syntax.mkStrLit (toString (toJson (e.toWeakExpr)))
  `(expr($strLit))

end EncodeExpr

/-- The `VariableParam` type. -/
inductive VariableParam where
  | freeVariable (binderInfo : BinderInfo)
  | hypothesis (t : Term)
deriving Inhabited

namespace VariableParam

/-- The `isFreeVariable` declaration. -/
def isFreeVariable : VariableParam → Bool
  | freeVariable _ => true
  | _ => false

/-- The `isHypothesis` declaration. -/
def isHypothesis : VariableParam → Bool
  | hypothesis _ => true
  | _ => false

/-- The `toTerm` declaration. -/
def toTerm : VariableParam → Term
  | hypothesis t => t
  | _ => default

/-- A variable parameter is a free variable exactly when it is not a hypothesis. -/
theorem isFreeVariable_eq_not_isHypothesis (p : VariableParam) :
    p.isFreeVariable = !p.isHypothesis := by
  cases p <;> rfl

end VariableParam

/-- The `VariableParams` declaration. -/
abbrev VariableParams := Array VariableParam

namespace VariableParams

variable (ps : VariableParams)

/-- The `numFreeVariables` declaration. -/
def numFreeVariables : Nat := ps.countP (·.isFreeVariable)
/-- The `numHypotheses` declaration. -/
def numHypotheses : Nat := ps.countP (·.isHypothesis)

/-- The `freeVarsBefore` declaration. -/
def freeVarsBefore (n : Nat) : Nat := Id.run do
  if n >= ps.numHypotheses then return 0
  let mut (i, j) := (0, 0)
  for p in ps do
    if p.isFreeVariable then
      i := i + 1
    else
      if j == n then break
      j := j + 1
  return i

end VariableParams

/-- The `BuildFormulaState` type. -/
structure BuildFormulaState where
  /-- The `attrDeclName` declaration. -/
  attrDeclName : Name
  /-- The `hasEmptyInstance?` declaration. -/
  hasEmptyInstance? : Bool := false
  /-- The `classParams` declaration. -/
  classParams : Array Term := #[]
  /-- The `variableParams` declaration. -/
  variableParams : VariableParams := #[]
  /-- The `variableType` declaration. -/
  variableType : Expr := default
  /-- The `localVars` declaration. -/
  localVars : Array Expr := #[]
  /-- The `Intermediates` declaration. -/
  termIntermediates : Array (Name × Array Nat) := #[]

/-- The `BuildFormulaM` declaration. -/
abbrev BuildFormulaM := StateT BuildFormulaState MetaM

namespace BuildFormula

/-- The `removeNameSuffix` declaration. -/
def removeNameSuffix (name : Name) : Name :=
  name.eraseSuffix? `eu <|>
  name.eraseSuffix? `formula <|>
  name.eraseSuffix? `realize_iff <|>
  name.eraseSuffix? `instFormulaToFunction <|>
  name.eraseSuffix? `to_realize <|>
  name.eraseSuffix? `elementarity |>.getD name

/-- Stripping the recognized suffixes from the anonymous name leaves it unchanged. -/
theorem removeNameSuffix_anonymous : removeNameSuffix .anonymous = .anonymous := rfl

/-- The `attrDeclName` declaration. -/
def attrDeclName : BuildFormulaM Name := do
  return (← get).attrDeclName

/-- The `name` declaration. -/
def name : BuildFormulaM Name := do
  return removeNameSuffix (← get).attrDeclName

/-- The `isFunction` declaration. -/
def isFunction : BuildFormulaM Bool := do
  return (← getEnv).contains ((← name) ++ `eu)

/-- The `isRealizeIffStage` declaration. -/
def isRealizeIffStage : BuildFormulaM Bool := do
  return (← attrDeclName).lastComponentAsString == "realize_iff"

/-- The `hasEmptyInstanceState` declaration. -/
def hasEmptyInstanceState : BuildFormulaM Bool := do
  return (← get).hasEmptyInstance?

/-- The `classParams` declaration. -/
def classParams : BuildFormulaM (Array Term) := do
  return (← get).classParams

/-- The `variableParams` declaration. -/
def variableParams : BuildFormulaM VariableParams := do
  return (← get).variableParams

/-- The `getHypothesis` declaration. -/
def getHypothesis (i : Nat) : BuildFormulaM Term := do
  return ((← variableParams).filter (·.isHypothesis))[i]!.toTerm

/-- The `freeVarsBefore` declaration. -/
def freeVarsBefore (i : Nat) : BuildFormulaM Nat := do
  return (← variableParams).freeVarsBefore i

/-- The `numFreeVars` declaration. -/
def numFreeVars (adjust? := false) : BuildFormulaM Nat := do
  return (← get).variableParams.numFreeVariables +
    if adjust? && (← isFunction) then 1 else 0

/-- The `numHypotheses` declaration. -/
def numHypotheses : BuildFormulaM Nat := do
  return (← get).variableParams.numHypotheses

/-- The `numAllVars` declaration. -/
def numAllVars : BuildFormulaM Nat := do
  return 2 + (← classParams).size + (← variableParams).size

/-- The `variableType` declaration. -/
def variableType : BuildFormulaM Expr := do
  return (← get).variableType

/-- The `localVars` declaration. -/
def localVars : BuildFormulaM (Array Expr) := do
  return (← get).localVars

/-- The `Intermediates` declaration. -/
def termIntermediates : BuildFormulaM (Array (Name × Array Nat)) := do
  return (← get).termIntermediates

/-- The `addIntermediate` declaration. -/
def addIntermediate (name : Name) (args : Array Nat) : BuildFormulaM Nat := do
  let xs ← termIntermediates
  modify fun s => { s with termIntermediates := xs.push (name, args) }
  return (← localVars).size + xs.size

/-- The `clearIntermediates` declaration. -/
def clearIntermediates : BuildFormulaM Unit := do
  modify fun s => { s with termIntermediates := #[] }

/-- The `findVar` declaration. -/
def findVar (e : Expr) : BuildFormulaM Nat := do
  match (← localVars).findIdx? (· == e) with
  | some n => return n
  | none => throwError m!"Can't find variable {e} in {← localVars}"

/-- The `getIndexSeq` declaration. -/
def getIndexSeq (extraBinders : Nat) (idx : Array Nat) : BuildFormulaM Expr := do
  let n₀ ← numFreeVars true
  let α ← `(Fin $(Syntax.mkNatLit n₀))
  let β ← `(Fin $(Syntax.mkNatLit ((← localVars).size + extraBinders - n₀)))
  let indexSyntax ← idx.mapM fun n => do
    let (op, i) := if n < n₀ then (`Sum.inl, n) else (`Sum.inr, n - n₀)
    let stx ← `($(mkIdent op) $(Syntax.mkNatLit i))
    return stx
  let mut stx ← `(Matrix.vecEmpty (α := $α ⊕ $β))
  for i in indexSyntax.reverse do
    stx ← `(Matrix.vecCons $i $stx)
  (elabTermAndSynthesize stx none).run'

/-- The `withNewVars` declaration. -/
def withNewVars {α} (vars : Array Expr) (f : BuildFormulaM α) : BuildFormulaM α := do
  let oldVars ← localVars
  modify fun s => { s with localVars := oldVars ++ vars }
  try f
  finally modify fun s => { s with localVars := oldVars }

/-- The empty parameter list contributes no free variables. -/
theorem numFreeVariables_empty : VariableParams.numFreeVariables #[] = 0 := rfl

/-- The `throwTranslateError` declaration. -/
def throwTranslateError {α} (e : Expr) : BuildFormulaM α := do
  throwError m!"Can't translate to formula: {e}, variables: {← localVars}"

/-- The `decomposeApp` declaration. -/
def decomposeApp (e : Expr) : BuildFormulaM (Name × Array Expr) := do
  let t ← variableType
  let mut (.const name _, args) := (e.getAppFn, e.getAppArgs) | throwTranslateError e
  let formulaName := name ++ `formula
  unless (← getEnv).contains formulaName do
    throwError "Formula {formulaName} not found"
  return (formulaName, ← args.filterM fun e => do isDefEq (← inferType e) t)

/-- Translate a term-level subexpression into an intermediate index, using `fuel` to
bound the recursion (any fuel at least the expression depth suffices). -/
def goTerm (fuel : Nat) (e : Expr) : BuildFormulaM Nat := do
  match fuel with
  | 0 => throwTranslateError e
  | fuel + 1 =>
    match e with
    | .app .. =>
      let (name, args) ← decomposeApp e
      addIntermediate name (← args.mapM (goTerm fuel))
    | .fvar .. => findVar e
    | _ => throwTranslateError e

/-- Translate a proposition into a `BoundedFormula`, using `fuel` to bound the
recursion (any fuel at least the expression depth suffices). -/
def go (fuel : Nat) (e : Expr) : BuildFormulaM Expr := do
  match fuel with
  | 0 => throwTranslateError e
  | fuel + 1 =>
    match e with
    | .forallE name type body info =>
      let newExpr : Expr := .lam name type body info
      let sort ← inferType type
      match sort.sortLevel! with
      | 0 => mkAppM ``BoundedFormula.imp #[← go fuel type, ← go fuel body]
      | _ => mkAppM ``BoundedFormula.all #[← go fuel newExpr]
    | .lam .. => lambdaTelescope e fun newVars e' => withNewVars newVars (go fuel e')
    | .app .. =>
      match_expr e with
      | Exists _ P => mkAppM ``BoundedFormula.ex #[← go fuel P]
      | ExistsUnique _ P => do mkAppM ``BoundedFormula.exUnique #[← go fuel P]
      | And p q => mkAppM ``min #[← go fuel p, ← go fuel q]
      | Or p q => mkAppM ``max #[← go fuel p, ← go fuel q]
      | Not p => mkAppM ``BoundedFormula.not #[← go fuel p]
      | Iff p q => mkAppM ``BoundedFormula.iff #[← go fuel p, ← go fuel q]
      | _ =>
        let (name, args) ← decomposeApp e
        let argsIdx ← args.mapM (goTerm fuel)
        let mut formula ← mkAppOptM ``BoundedFormula.relabel #[
          none, none, none, none, ← getIndexSeq (← termIntermediates).size argsIdx,
          toExpr 0, mkConst name
        ]
        for ((name, idx), i) in (← termIntermediates).zipIdx.reverse do
          formula ← mkAppM ``BoundedFormula.ofFunc #[mkConst name, ← getIndexSeq i idx, formula]
        clearIntermediates
        return formula
    | _ => throwTranslateError e

/-- The `checkSorry` declaration. -/
def checkSorry (name : Name) : BuildFormulaM Unit := do
  match (← getEnv).findAsync? name false with
  | some const => do
    let reportError (const : ConstantInfo) : CoreM Unit := do
      if const.toDeclaration!.hasSorry then
        throwError m!"Definition {name} has sorry"
    let cancelTk ← IO.CancelToken.new
    let checkAct ← Core.wrapAsyncAsSnapshot reportError cancelTk
    let t ← BaseIO.mapTask checkAct const.constInfo
    Core.logSnapshotTask {
      stx? := none, reportingRange := .skip, task := t, cancelTk? := cancelTk
    }
  | none => throwError m!"Definition {name} not found"

/-- The `addDeclSimple` declaration. -/
def addDeclSimple (name : Name) (type value : Expr) : BuildFormulaM Unit := do
  let value ← instantiateMVars value
  let env ← getEnv
  let result ← Closure.mkValueTypeClosure type value false
  let hints := ReducibilityHints.regular (getMaxHeight env value + 1)
  let decl := Declaration.defnDecl (mkDefinitionValEx
    name result.levelParams.toList result.type result.value
    hints DefinitionSafety.safe [name]
  )
  addDecl decl
  Lean.addDocStringCore name
    "The first-order formula automatically realized for this set-theoretic predicate."
  warnIfUsesSorry decl
  enableRealizationsForConst name

/-- The `explicitize` declaration. -/
def explicitize : Expr → Nat → Expr
  | .lam name type body _, n + 1 => .lam name type (explicitize body n) .default
  | e, _ => e

/-- The `mkLambdaFVarsExplicit` declaration. -/
def mkLambdaFVarsExplicit (xs : Array Expr) (e : Expr) : BuildFormulaM Expr := do
  let e' ← mkLambdaFVars xs e
  if e'.hasFVar || e'.hasMVar then
    throwError "{e'} depends on variables not in {xs}"
  return explicitize e' xs.size

/-- The `init` declaration. -/
def init : BuildFormulaM Unit := do
  let constInfo := (← getEnv).find? (← attrDeclName) |>.get!
  forallTelescopeReducing constInfo.type fun vars _ => do
    unless vars.size ≥ 2 do
      throwError m!"Variable list {vars} doesn't starts with `\{M} [ZFStructure M] ...`"
    let variableType := vars[0]!
    let mut classVars : Array Expr := #[]
    let mut classParams : Array Term := #[]
    let mut freeVars : Array Expr := #[]
    let mut variableParams : VariableParams := #[]
    let hasEmpty ← mkAppOptM ``HasEmpty #[vars[0]!, vars[1]!]
    for i in 2...vars.size do
      let type ← inferType vars[i]!
      if (← vars[i]!.fvarId!.getBinderInfo) == .instImplicit then
        if freeVars.size != 0 then
          throwError m!"Free variables must occur after all instance parameters"
        classVars := classVars.push vars[i]!
        classParams := classParams.push <|
          ← (← mkLambdaFVarsExplicit vars[*...2] type).toSyntax'
        if (← isDefEq type hasEmpty) then
          modify fun s => { s with hasEmptyInstance? := true}
      else
        if ← isRealizeIffStage then continue
        if ← isDefEq type variableType then
          freeVars := freeVars.push vars[i]!
          variableParams := variableParams.push <| .freeVariable <| vars[i]!.binderInfo
        else
          unless (← isFunction) do
            throwError "Only function definitions allow hypotheses"
          variableParams := variableParams.push <| .hypothesis
            (← (← mkLambdaFVarsExplicit (vars[*...2] ++ classVars ++ freeVars) type).toSyntax')
    if ← isRealizeIffStage then
      let formulaType := ((← getEnv).find? ((← name) ++ `formula)).get!.type
      let_expr ZFFormula n := formulaType | throwError "Formula must be of `ZFFormula` type"
      let some numFreeVars ← (Lean.Meta.evalNat (← whnf n)).run
        | throwError "Formula index is not a literal natural number"
      modify fun s => { s with
        classParams, variableParams := .replicate numFreeVars (.freeVariable .default)
      }
    else
      modify fun s => { s with
        classParams, variableParams
      }

/-- The `simpFormulaPre` declaration. -/
def simpFormulaPre (e : Expr) : BuildFormulaM Expr := do
  let some ext ← getSimpExtension? `formula_builder_pre | failure
  let ctx ← Simp.mkContext {} #[← ext.getTheorems]
  return (← simp e ctx).1.expr

/-- The `simpFormula` declaration. -/
def simpFormula (e : Expr) : BuildFormulaM Expr := do
  let some ext ← getSimpExtension? `formula_builder | failure
  let ctx ← Simp.mkContext {} #[← ext.getTheorems]
  return (← simp e ctx).1.expr

/-- The `definitionProp` declaration. -/
def definitionProp : BuildFormulaM Expr := do
  if ← isFunction then
    let constInfo := (← getEnv).find? ((← name) ++ `eu) |>.get!
    forallTelescopeReducing (← simpFormulaPre constInfo.type) fun vars type => do
      match_expr type with
      | ExistsUnique _ P => mkLambdaFVars vars P
      | _ => throwError m!"Function definition should has type with form `∃!, ...`"
  else
    let definition := ((← getEnv).find? (← name)).get!
    let some value := definition.value?
      | throwError m!"Definition {← name} doesn't have value"
    simpFormulaPre value

/-- The `buildFormula` declaration. -/
def buildFormula (formulaName : Name) : BuildFormulaM Unit := do
  let isFunction ← isFunction
  let formula ← lambdaTelescope (← definitionProp) fun vars value => do
    let varsInDecl := if isFunction then vars.pop else vars
    let variableParams ← variableParams
    let freeVarsInDecl := varsInDecl.drop (varsInDecl.size - variableParams.size)
      |>.zipIdx
      |>.filter (fun (_, i) => variableParams[i]!.isFreeVariable)
      |>.map (·.1)
    let formulaVars := if isFunction then freeVarsInDecl ++ #[vars.back!] else freeVarsInDecl
    modify fun s => { s with
      variableType := vars[0]!
      localVars := formulaVars
    }
    let value ← simpFormula value
    let mut formula ← go (value.approxDepth.toNat + 1) value
    for i in (*...(← numHypotheses)).toArray.reverse do
      let e ← (elabTermAndSynthesize (← getHypothesis i) none).run'
      let e := e.beta <|
        vars[*...2 + (← classParams).size] ++ formulaVars[*...(← freeVarsBefore i)]
      let e ← simpFormula e
      formula ← mkAppM ``BoundedFormula.ite #[
        ← go (e.approxDepth.toNat + 1) e, formula, ← mkAppM ``EqEmptyN #[toExpr (← numFreeVars)]
      ]
    return formula
  addDeclSimple formulaName (← mkAppM ``ZFFormula #[toExpr (← numFreeVars true)]) formula
  applyAttributes formulaName #[{name := `irreducible}] |>.run'

/-- The `prefixIdents` declaration. -/
def prefixIdents (typeLetter := "M") : Array Ident :=
  #[mkIdent typeLetter.toName, mkIdent ("s" ++ typeLetter).toName]

/-- The prefix identifiers are exactly the carrier type and its structure instance. -/
theorem prefixIdents_size (typeLetter : String) : (prefixIdents typeLetter).size = 2 := rfl

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
  noncomputable def $funcIdent $classParamBinders* $mkBinders* : $identM :=
    $value
  lemma $specIdent $classParamBinders* $mkBindersWithHypotheses* :
      $specStatement := by
    $specProof:tactic
  lemma $eqIffIdent $classParamBinders* $mkBindersWithHypotheses* ($identV : $identM) :
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
  @[realize_simps] lemma $thmIdent
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
  instance $instIdent:ident $(← classParamBinders)* :
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
  lemma $toRealizeIdent $((← classParamBinders) ++ (← mkBinders true))* :
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
      @[elementary_simps] lemma $elementarityIdent
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
      @[elementary_simps] lemma $elementarityIdent
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
