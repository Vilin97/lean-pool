/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import Lean
import Batteries.Util.ExtendedBinder
import LeanPool.Lentil.Util
import LeanPool.Lentil.Foldable

open Lean LentilLib

/-! ## A Shallow-Embedding of TLA -/

namespace TLA

/-! NOTE: There are multiple ways to formalize the concept of infinite sequences.
    Here, we follow the definition from `coq-tla`, while an alternative is to define
    infinite sequence as a coinductive datatype (like `Stream` in Rocq/Agda).

    Lean also comes with a definition of `Stream`, but it is a type class instead of
    a datatype, and the sequences generated from it are not necessarily infinite
    (in the sense that it may generate finite sequences). So here we do not use it.
-/

/-- An execution: an infinite sequence of states indexed by `Nat`. -/
def exec (σ : Type u) := Nat → σ
/-- A temporal predicate: a property of executions. -/
def pred (σ : Type u) := exec σ → Prop
/-- Lift a state property to the temporal predicate that holds at the first state. -/
def statePred {σ : Type u} (f : σ → Prop) : pred σ :=
  fun e => f (e 0)
/-- An action: a binary relation between the current and next state. -/
def action (σ : Type u) := σ → σ → Prop
/-- Lift an action to the temporal predicate that holds on the first two states. -/
def actionPred {σ : Type u} (a : action σ) : pred σ :=
  fun e => a (e 0) (e 1)

/-- Lift a `Prop` to the temporal predicate that holds iff the `Prop` does. -/
def purePred {α : Type u} (p : Prop) : pred α := statePred (fun _ => p)
/-- The temporal predicate that always holds. -/
def tlaTrue {α : Type u} : pred α := purePred True
/-- The temporal predicate that never holds. -/
def tlaFalse {α : Type u} : pred α := purePred False

/-- Conjunction of temporal predicates. -/
def tlaAnd {α : Type u} (p q : pred α) : pred α := fun σ => p σ ∧ q σ
/-- Disjunction of temporal predicates. -/
def tlaOr {α : Type u} (p q : pred α) : pred α := fun σ => p σ ∨ q σ
/-- Implication of temporal predicates. -/
def tlaImplies {α : Type u} (p q : pred α) : pred α := fun σ => p σ → q σ
/-- Negation of a temporal predicate. -/
def tlaNot {α : Type u} (p : pred α) : pred α := fun σ => ¬ p σ
/-- Universal quantification over temporal predicates. -/
def tlaForall {α : Sort u} {β : Type v} (p : α → pred β) : pred β := fun σ => ∀ x, p x σ
/-- Existential quantification over temporal predicates. -/
def tlaExists {α : Sort u} {β : Type v} (p : α → pred β) : pred β := fun σ => ∃ x, p x σ

-- NOTE: this all could be automatically lifted, but to avoid dependency circles, we don't do that
instance {α : Type u} : Std.Commutative (@tlaAnd α) := by
  constructor; intros; unfold tlaAnd; funext e; ac_rfl

instance {α : Type u} : Std.Associative (@tlaAnd α) := by
  constructor; intros; unfold tlaAnd; funext e; ac_rfl

instance {α : Type u} : Std.Commutative (@tlaOr α) := by
  constructor; intros; unfold tlaOr; funext e; ac_rfl

instance {α : Type u} : Std.Associative (@tlaOr α) := by
  constructor; intros; unfold tlaOr; funext e; ac_rfl

/-- Drop the first `k` states of an execution. -/
def exec.drop {α : Type u} (k : Nat) (σ : exec α) : exec α := λ n => σ (n + k)
/-- The list of the first `k` states of an execution. -/
def exec.take {α : Type u} (k : Nat) (σ : exec α) : List α := List.range k |>.map σ
/-- The list of `k` states of an execution starting at index `start`. -/
def exec.takeFrom {α : Type u} (start k : Nat) (σ : exec α) : List α := List.range' start k |>.map σ

/-- The `always` (box) modality: `p` holds on every suffix. -/
def always {α : Type u} (p : pred α) : pred α := λ σ => ∀ k, p <| σ.drop k
/-- The `eventually` (diamond) modality: `p` holds on some suffix. -/
def eventually {α : Type u} (p : pred α) : pred α := λ σ => ∃ k, p <| σ.drop k
/-- The `later` (next) modality: `p` holds on the suffix dropping one state. -/
def later {α : Type u} (p : pred α) : pred α := λ σ => p <| σ.drop 1

/-- An execution satisfies a temporal predicate. -/
def exec.satisfies {α : Type u} (p : pred α) (σ : exec α) : Prop := p σ
/-- A temporal predicate is valid: it holds on every execution. -/
def valid {α : Type u} (p : pred α) : Prop := ∀ (σ : exec α), σ.satisfies p
/-- Entailment between temporal predicates over all executions. -/
def predImplies {α : Type u} (p q : pred α) : Prop := ∀ (σ : exec α), σ.satisfies p → σ.satisfies q

/-- An action is enabled at a state if some successor state exists. -/
def enabled {α : Type u} (a : action α) (s : α) : Prop := ∃ s', a s s'
/-- The temporal predicate asserting that an action is enabled. -/
def tlaEnabled {α : Type u} (a : action α) : pred α := statePred (enabled a)

/-- Big conjunction of temporal predicates over a foldable collection. -/
def tlaBigwedge {α : Type u} {β : Type v} {c} [Foldable c] (f : β → pred α) (s : c β) : pred α :=
  Foldable.fold tlaAnd tlaTrue f s

/-- Big disjunction of temporal predicates over a foldable collection. -/
def tlaBigvee {α : Type u} {β : Type v} {c} [Foldable c] (f : β → pred α) (s : c β) : pred α :=
  Foldable.fold tlaOr tlaFalse f s

/-- The `until` modality: `p` holds until `q` becomes true. -/
def tlaUntil {α : Type u} (p q : pred α) : pred α := λ σ => ∃ i, (q <| σ.drop i) ∧ ∀ j < i, (p <| σ.drop j)

end TLA

/-! ## Syntax for TLA Notations

    Our notations for TLA formulas intersect with those for plain Lean terms,
    so to avoid potentially ambiguity(?), we define a new syntax category `tlafml`
    for TLA formulas and define macro rules for expanding formulas in `tlafml` into
    Lean terms.
-/

/-- Syntax category for TLA formulas. -/
declare_syntax_cat tlafml
/-- Embed a term as a TLA formula. -/
syntax (priority := low) term:max : tlafml
/-- Parenthesized TLA formula. -/
syntax "(" tlafml ")" : tlafml
/-- State-predicate TLA formula `⌜ p ⌝`. -/
syntax "⌜ " term " ⌝" : tlafml
/-- Pure-predicate TLA formula `⌞ p ⌟`. -/
syntax "⌞ " term " ⌟" : tlafml
/-- Action-predicate TLA formula `⟨ a ⟩`. -/
syntax "⟨ " term " ⟩" : tlafml
/-- The `⊤` TLA formula. -/
syntax "⊤" : tlafml
/-- The `⊥` TLA formula. -/
syntax "⊥" : tlafml
/-- Unary heading operators on TLA formulas (`¬`, `□`, `◇`, `◯`). -/
syntax tlafmlHeadingOp := "¬" <|> "□" <|> "◇" <|> "◯"
/-- Apply a unary heading operator to a TLA formula. -/
syntax:max tlafmlHeadingOp tlafml:40 : tlafml
/-- The `Enabled a` TLA formula. -/
syntax:max "Enabled" term:40 : tlafml
-- HMM why `syntax:arg ... ...:max` does not work, when we need multiple layers like `□ ◇ p`?
/-- Implication of TLA formulas. -/
syntax:15 tlafml:16 " → " tlafml:15 : tlafml
/-- Conjunction of TLA formulas. -/
syntax:35 tlafml:36 " ∧ " tlafml:35 : tlafml
/-- Disjunction of TLA formulas. -/
syntax:30 tlafml:31 " ∨ " tlafml:30 : tlafml
/-- Leads-to (`↝`) of TLA formulas. -/
syntax:20 tlafml:21 " ↝ " tlafml:20 : tlafml
/-- Until (`𝑈`) of TLA formulas. -/
syntax:25 tlafml:26 " 𝑈 " tlafml:25 : tlafml
/-- Always-implies (`⇒`) of TLA formulas. -/
syntax:17 tlafml:18 " ⇒ " tlafml:17 : tlafml
/-- Weak-fairness (`𝒲ℱ`) of an action as a TLA formula. -/
syntax:arg "𝒲ℱ" term:max : tlafml

-- the way how binders are defined and how they are expanded is taken from `Mathlib.Order.SetNotation`
open Batteries.ExtendedBinder in
/-- Universally quantified TLA formula. -/
syntax "∀ " extBinder ", " tlafml:51 : tlafml
open Batteries.ExtendedBinder in
/-- Existentially quantified TLA formula. -/
syntax "∃ " extBinder ", " tlafml:51 : tlafml

/-- Big-operator heads (`⋀`, `⋁`) for TLA formulas. -/
syntax tlafmlBigop := "⋀ " <|> "⋁ "
/-- Big conjunction/disjunction of a TLA formula over a collection. -/
syntax tlafmlBigop binderIdent " ∈ " term ", " tlafml : tlafml

/-- Elaborate a TLA formula into a term. -/
syntax "[tlafml|" tlafml "]" : term

macro_rules
  | `([tlafml| ( $f:tlafml ) ]) => `([tlafml| $f ])
  | `([tlafml| ⌜ $t:term ⌝ ]) => `(TLA.statePred $t)
  | `([tlafml| ⌞ $t:term ⌟ ]) => `(TLA.purePred $t)
  | `([tlafml| ⟨ $t:term ⟩ ]) => `(TLA.actionPred $t)
  | `([tlafml| ⊤ ]) => `(TLA.tlaTrue)
  | `([tlafml| ⊥ ]) => `(TLA.tlaFalse)
  | `([tlafml| $op:tlafmlHeadingOp $f:tlafml ]) => do
    let opterm ← match op with
      | `(tlafmlHeadingOp|¬) => `(TLA.tlaNot)
      | `(tlafmlHeadingOp|□) => `(TLA.always)
      | `(tlafmlHeadingOp|◇) => `(TLA.eventually)
      | `(tlafmlHeadingOp|◯) => `(TLA.later)
      | _ => Macro.throwUnsupported
    `($opterm [tlafml| $f ])
  | `([tlafml| Enabled $t:term ]) => `(TLA.tlaEnabled $t)
  | `([tlafml| $f1:tlafml → $f2:tlafml ]) => `(TLA.tlaImplies [tlafml| $f1 ] [tlafml| $f2 ])
  | `([tlafml| $f1:tlafml ∧ $f2:tlafml ]) => `(TLA.tlaAnd [tlafml| $f1 ] [tlafml| $f2 ])
  | `([tlafml| $f1:tlafml ∨ $f2:tlafml ]) => `(TLA.tlaOr [tlafml| $f1 ] [tlafml| $f2 ])
  | `([tlafml| $f1:tlafml 𝑈 $f2:tlafml ]) => `(TLA.tlaUntil [tlafml| $f1 ] [tlafml| $f2 ])
  | `([tlafml| ∀ $x:ident, $f:tlafml]) => `(TLA.tlaForall fun $x:ident => [tlafml| $f ])
  | `([tlafml| ∀ $x:ident : $t, $f:tlafml]) => `(TLA.tlaForall fun $x:ident : $t => [tlafml| $f ])
  | `([tlafml| ∃ $x:ident, $f:tlafml]) => `(TLA.tlaExists fun $x:ident => [tlafml| $f ])
  | `([tlafml| ∃ $x:ident : $t, $f:tlafml]) => `(TLA.tlaExists fun $x:ident : $t => [tlafml| $f ])
  | `([tlafml| $op:tlafmlBigop $x:binderIdent ∈ $l:term, $f:tlafml]) =>
    -- HMM why the `⟨x.raw⟩` coercion does not work here, so that we have to define `binderIdentToFunBinder`?
    match op with
    | `(tlafmlBigop|⋀ ) => do `(TLA.tlaBigwedge (fun $(← binderIdentToFunBinder x) => [tlafml| $f ]) $l)
    | `(tlafmlBigop|⋁ ) => do `(TLA.tlaBigvee (fun $(← binderIdentToFunBinder x) => [tlafml| $f ]) $l)
    | _ => Macro.throwUnsupported
  | `([tlafml| $t:term ]) => `($t)

-- these definitions are not necessarily required, but for delaboration purposes
/-- The leads-to operator `p ↝ q`, defined as `□ (p → ◇ q)`. -/
def TLA.leadsTo {α : Type u} (p q : TLA.pred α) : TLA.pred α := [tlafml| □ (p → ◇ q) ]
/-- The always-implies operator `p ⇒ q`, defined as `□ (p → q)`. -/
def TLA.alwaysImplies {α : Type u} (p q : TLA.pred α) : TLA.pred α := [tlafml| □ (p → q) ]
/-- Weak fairness of an action. -/
def TLA.weakFairness {α : Type u} (a : action α) : pred α := [tlafml| □ ((□ (Enabled a)) → ◇ ⟨a⟩)]

macro_rules
  | `([tlafml| $f1:tlafml ↝ $f2:tlafml ]) => `(TLA.leadsTo [tlafml| $f1 ] [tlafml| $f2 ])
  | `([tlafml| $f1:tlafml ⇒ $f2:tlafml ]) => `(TLA.alwaysImplies [tlafml| $f1 ] [tlafml| $f2 ])
  | `([tlafml| 𝒲ℱ $t:term ]) => `(TLA.weakFairness $t)

/- NOTE: we can use something fancier like `ᴛʟᴀ`, but currently these characters cannot be
   easily typed in Lean VSCode extension, so anyway -/
/-- Sequent notation `p |-tla- q` for entailment. -/
syntax:max tlafml:max " |-tla- " tlafml:max : term
/-- Validity notation `|-tla- p`. -/
syntax:max "|-tla- " tlafml:max : term
/-- Equality notation `p =tla= q` between TLA formulas. -/
syntax:max tlafml:max " =tla= " tlafml:max : term
/-- Satisfaction notation `e |=tla= p`. -/
syntax term " |=tla= " tlafml : term

macro_rules
  | `($f1:tlafml |-tla- $f2:tlafml) => `(TLA.predImplies [tlafml| $f1 ] [tlafml| $f2 ])
  | `(|-tla- $f1:tlafml) => `(TLA.valid [tlafml| $f1 ])
  | `($f1:tlafml =tla= $f2:tlafml) => `([tlafml| $f1 ] = [tlafml| $f2 ])
  | `($e:term |=tla= $f:tlafml) => `(TLA.exec.satisfies [tlafml| $f ] $e)

/-! ## Pretty-Printing for TLA Notations -/

/-- Converting a syntax in `term` category into `tlafml`.
    This is useful in the cases where we want to eliminate the redundant `[tlafml| ... ]`
    wrapper of some sub-formula when it is inside a `tlafml`. -/
def TLA.syntaxTermToTlafml [Monad m] [MonadQuotation m] (stx : TSyntax `term) : m (TSyntax `tlafml) := do
  match stx with
  | `([tlafml| $f:tlafml ]) => pure f
  | `(term|$t:term) => `(tlafml| $t:term )

/-- Converting a syntax in `term` category into `tlafml`,
    by inserting `[tlafml| ... ]` wrapper if needed.  -/
def TLA.syntaxTlafmlToTerm [Monad m] [MonadQuotation m] (stx : TSyntax `tlafml) : m (TSyntax `term) := do
  match stx with
  | `(tlafml| $t:term ) => pure t
  | f => `(term|[tlafml| $f:tlafml ])

-- taken from https://github.com/leanprover/vstte2024/blob/main/Imp/Expr/Delab.lean
open PrettyPrinter.Delaborator SubExpr in
/-- Annotate the syntax with term info for the delaborator. -/
def TLA.annAsTerm {any} (stx : TSyntax any) : DelabM (TSyntax any) :=
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

-- heavily inspired by https://github.com/leanprover/vstte2024/blob/main/Imp/Expr/Delab.lean
open PrettyPrinter.Delaborator SubExpr in
/-- Delaborate the current expression into `tlafml` syntax. `fuel` bounds the
    recursion depth; each recursive call descends into a strict subexpression,
    so seeding it with the expression's depth always suffices. -/
def TLA.delabTlafmlAux (fuel : Nat) : DelabM (TSyntax `tlafml) := do
  let e ← getExpr
  let stx ← do
    /- NOTE: we could get rid of the nesting of `withAppFn` and `withAppArg`
       by having something more general, but currently doing so does not
       give much benefit -/
    let fn := e.getAppFn'.constName
    match fuel, fn with
    | _, ``TLA.tlaTrue => `(tlafml| ⊤ )
    | _, ``TLA.tlaFalse => `(tlafml| ⊥ )
    | _, ``TLA.statePred | _, ``TLA.purePred | _, ``TLA.actionPred
    | _, ``TLA.tlaEnabled | _, ``TLA.weakFairness =>
      let t ← withAppArg delab
      match fn with
      | ``TLA.statePred => `(tlafml| ⌜ $t:term ⌝ )
      | ``TLA.purePred => `(tlafml| ⌞ $t:term ⌟ )
      | ``TLA.actionPred => `(tlafml| ⟨ $t:term ⟩ )
      | ``TLA.tlaEnabled => `(tlafml| Enabled $t:term )
      | ``TLA.weakFairness => `(tlafml| 𝒲ℱ $t:term )
      | _ => unreachable!
    | fuel + 1, ``TLA.tlaNot | fuel + 1, ``TLA.always
    | fuel + 1, ``TLA.eventually | fuel + 1, ``TLA.later =>
      let f ← withAppArg (TLA.delabTlafmlAux fuel)
      match fn with
      | ``TLA.tlaNot => `(tlafml| ¬ $f:tlafml )
      | ``TLA.always => `(tlafml| □ $f:tlafml )
      | ``TLA.eventually => `(tlafml| ◇ $f:tlafml )
      | ``TLA.later => `(tlafml| ◯ $f:tlafml )
      | _ => unreachable!
    | fuel + 1, ``TLA.tlaAnd | fuel + 1, ``TLA.tlaOr | fuel + 1, ``TLA.tlaImplies
    | fuel + 1, ``TLA.leadsTo | fuel + 1, ``TLA.tlaUntil | fuel + 1, ``TLA.alwaysImplies =>
      let f1 ← withAppFn <| withAppArg (TLA.delabTlafmlAux fuel)
      let f2 ← withAppArg (TLA.delabTlafmlAux fuel)
      match fn with
      | ``TLA.tlaAnd => `(tlafml| $f1:tlafml ∧ $f2:tlafml)
      | ``TLA.tlaOr => `(tlafml| $f1:tlafml ∨ $f2:tlafml)
      | ``TLA.tlaImplies => `(tlafml| $f1:tlafml → $f2:tlafml)
      | ``TLA.leadsTo => `(tlafml| $f1:tlafml ↝ $f2:tlafml)
      | ``TLA.tlaUntil => `(tlafml| $f1:tlafml 𝑈 $f2:tlafml)
      | ``TLA.alwaysImplies => `(tlafml| $f1:tlafml ⇒ $f2:tlafml)
      | _ => unreachable!
    | _, ``TLA.tlaForall | _, ``TLA.tlaExists =>
      /- we are not sure about whether the argument is a `fun _ => _` or something else,
         so here we first `delab` the argument and then look into it;
         this seems to work, as `delab` would also call `TLA.delabTlafmlAux` on the argument,
         so that we can match the inner syntax of `f` and use `TLA.syntaxTermToTlafml`? -/
      let body ← withAppArg delab
      let (a, stx) ← getBindernameFunbody body
      match fn with
      | ``TLA.tlaForall => do `(tlafml| ∀ $a:ident, $stx )
      | ``TLA.tlaExists => do `(tlafml| ∃ $a:ident, $stx )
      | _ => unreachable!
    | _, ``TLA.tlaBigwedge | _, ``TLA.tlaBigvee =>
      let body ← withAppFn <| withAppArg delab
      let l ← withAppArg delab
      let (a, stx) ← getBindernameFunbody body
      match fn with
      | ``TLA.tlaBigwedge => do `(tlafml| ⋀ $a:ident ∈ $l, $stx )
      | ``TLA.tlaBigvee => do `(tlafml| ⋁ $a:ident ∈ $l, $stx )
      | _ => unreachable!
    | _, _ =>
      -- in this case, `e` may not even be an `.app`, so directly delab it
      `(tlafml| $(← delab):term )
  TLA.annAsTerm stx
where
  /-- Extract the binder name and body of a delaborated lambda. -/
  getBindernameFunbody (body : Term) : DelabM (Ident × TSyntax `tlafml) := do
  match body with
  | `(fun $a:ident => $stx) | `(fun ($a:ident : $_) => $stx) => pure (a, (← TLA.syntaxTermToTlafml stx))
  | _ =>
    -- we cannot go back to call `delab` on the whole term since that would result in dead recursion!
    -- FIXME: it seems that the terminfo on `x` and `bodyapp` can get wrong here
    let x := mkIdent <| .mkSimple "x"
    let bodyapp ← `(term| $body $x )
    pure (x, (← `(tlafml| $bodyapp:term )))

open PrettyPrinter.Delaborator SubExpr in
/-- Delaborate the current expression into `tlafml` syntax, seeding the depth
    fuel from the expression's own approximate depth. -/
def TLA.delabTlafmlInner : DelabM (TSyntax `tlafml) := do
  TLA.delabTlafmlAux ((← getExpr).approxDepth.toNat + 1)

open PrettyPrinter.Delaborator SubExpr in
/-- Delaborator turning TLA predicate applications back into `tlafml` notation. -/
def TLA.delabTlafml : Delab := whenPPOption (fun o => o.get lentil.pp.useDelab.name true) do
  let e ← getExpr
  let fn := e.getAppFn.constName
  -- need to consider implicit arguments below in comparing `e.getAppNumArgs'`
  let check_applicable (offset : Nat) :=
    (List.elem fn [``TLA.statePred, ``TLA.purePred, ``TLA.actionPred, ``TLA.tlaEnabled, ``TLA.weakFairness,
        ``TLA.tlaNot, ``TLA.always, ``TLA.eventually, ``TLA.later]
      && e.getAppNumArgs' == 2 + offset) ||
    (List.elem fn [``TLA.tlaAnd, ``TLA.tlaOr, ``TLA.tlaImplies, ``TLA.leadsTo, ``TLA.tlaUntil, ``TLA.alwaysImplies,
        ``TLA.tlaForall, ``TLA.tlaExists]
      && e.getAppNumArgs' == 3 + offset) ||
    (List.elem fn [``TLA.tlaTrue, ``TLA.tlaFalse]
      && e.getAppNumArgs' == 1 + offset) ||
    (List.elem fn [``TLA.tlaBigwedge, ``TLA.tlaBigvee]
      && e.getAppNumArgs' == 6 + offset)
  if check_applicable 0
  then TLA.delabTlafmlInner >>= TLA.syntaxTlafmlToTerm
  else whenPPOption (fun o => o.get lentil.pp.autoRenderSatisfies.name true) do
    if check_applicable 1
    then
      let res ← withAppFn TLA.delabTlafmlInner
      let e ← withAppArg delab
      `(term| $e |=tla= $res)
    else failure

attribute [delab app.TLA.statePred, delab app.TLA.purePred, delab app.TLA.actionPred, delab app.TLA.tlaEnabled, delab app.TLA.weakFairness] TLA.delabTlafml
attribute [delab app.TLA.tlaNot, delab app.TLA.always, delab app.TLA.eventually, delab app.TLA.later] TLA.delabTlafml
attribute [delab app.TLA.tlaAnd, delab app.TLA.tlaOr, delab app.TLA.tlaImplies, delab app.TLA.leadsTo, delab app.TLA.tlaUntil, delab app.TLA.alwaysImplies] TLA.delabTlafml
attribute [delab app.TLA.tlaTrue, delab app.TLA.tlaFalse] TLA.delabTlafml
attribute [delab app.TLA.tlaForall, delab app.TLA.tlaExists] TLA.delabTlafml
attribute [delab app.TLA.tlaBigwedge, delab app.TLA.tlaBigvee] TLA.delabTlafml

/-- Unexpander rendering `predImplies` as the `|-tla-` sequent notation. -/
@[app_unexpander TLA.predImplies] def TLA.unexpandPredImplies : Lean.PrettyPrinter.Unexpander
  | `($_ $stx1 $stx2) => do `(($(← TLA.syntaxTermToTlafml stx1)) |-tla- ($(← TLA.syntaxTermToTlafml stx2)))
  | _ => throw ()

/-- Unexpander rendering `valid` as the `|-tla-` notation. -/
@[app_unexpander TLA.valid] def TLA.unexpandValid : Lean.PrettyPrinter.Unexpander
  | `($_ $stx) => do `(|-tla- ($(← TLA.syntaxTermToTlafml stx)))
  | _ => throw ()

/-- Unexpander rendering `satisfies` as the `|=tla=` notation. -/
@[app_unexpander TLA.exec.satisfies] def TLA.unexpandSatisfies : Lean.PrettyPrinter.Unexpander
  | `($_ $stx1 $stx2) => do `($stx2 |=tla= $(← TLA.syntaxTermToTlafml stx1))
  | _ => throw ()

/-- Unexpander rendering equalities between TLA formulas with `=tla=`. -/
@[app_unexpander Eq] def TLA.unexpandTlaEq : Lean.PrettyPrinter.Unexpander
  | `($_ [tlafml| $f1:tlafml ] [tlafml| $f2:tlafml ]) => `(($f1) =tla= ($f2))
  | `($_ [tlafml| $f1:tlafml ] $t2:term) => do `(($f1) =tla= ($(← `(tlafml| $t2:term ))))
  | `($_ $t1:term [tlafml| $f2:tlafml ]) => do `(($(← `(tlafml| $t1:term ))) =tla= ($f2))
  | _ => throw ()       -- NOTE: we don't want all equalities to be rendered into equalities between TLA formulas!

-- taken from https://github.com/leanprover/vstte2024/blob/main/Imp/Expr/Syntax.lean
open PrettyPrinter Parenthesizer in
@[category_parenthesizer tlafml]
def tlafml.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `tlafml true wrapParens prec $
    parenthesizeCategoryCore `tlafml prec
where
  /-- Wrap a piece of syntax in parentheses. -/
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)

/-! ## Basic lemmas about executions and entailment -/

namespace TLA

theorem exec.take_length {α : Type u} (k : Nat) (σ : exec α) : (σ.take k).length = k := by
  simp [exec.take]

theorem exec.drop_drop {α : Type u} (k l : Nat) (σ : exec α) :
    (σ.drop k).drop l = σ.drop (k + l) := by
  funext n; simp [exec.drop]; ac_rfl

@[refl] theorem pred_implies_refl {α : Type u} (p : pred α) : predImplies p p := (fun _ => id)

theorem pred_implies_trans {p q r : pred α} :
    predImplies p q → predImplies q r → predImplies p r := by
  intros h1 h2 e hp; apply h2; apply h1; assumption

end TLA
