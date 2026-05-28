/-
Copyright (c) 2026 Andrej Bauer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrej Bauer
-/
import Mathlib.Data.Finset.Basic
import LeanPool.PartialCombinatoryAlgebras.Basic

/-!
# Partial combinatory algebras

A partial combinatory algebra is a set equipped with a partial binary operation,
which has the so-called combinators `K` and `S`. We formalize it in two stages.

We first define the class `PartialApplication` which equips a given set `A` with
a partial binary operation. One might expect such an operation to have type
`A → A → Part A`, but this leads to complications because it is not composable.
So instead we specify that a partial operation is a map of type `Part A → Part A → Part A`.
In other words, we *always* work with partial elements, and separately state that they are
total as necessary.

(It would be natural to require that the applications be strict, i.e., if the result is defined
so are its arguments. An early version did so, but the assumption of strictness was never used.)

We then define the class `PCA` (partial combinatory algebra) to be an extension of
`PartialApplication`. It prescribed combinators `K` and `S` satisfying the usual properties.
Following our strategy, `K` and `S` are again partial elements on the carrier set,
with a separate claim that they are total.

-/

namespace LeanPool.PartialCombinatoryAlgebras

/-- The partial combinatory structure on a set `A`. -/
class PCA (A : Type*) extends PartialApplication A where
  /-- The `K` combinator as a partial element. -/
  K : Part A
  /-- The `S` combinator as a partial element. -/
  S : Part A
  /-- The `K` combinator is total. -/
  df_K₀ : K ⇓
  /-- Applying `K` to a total argument is total. -/
  df_K₁ : ∀ {u : Part A}, u ⇓ → (K ⬝ u) ⇓
  /-- The `S` combinator is total. -/
  df_S₀ : S ⇓
  /-- Applying `S` to one total argument is total. -/
  df_S₁ : ∀ {u : Part A}, u ⇓ → (S ⬝ u) ⇓
  /-- Applying `S` to two total arguments is total. -/
  df_S₂ : ∀ {u v : Part A}, u ⇓ → v ⇓ → (S ⬝ u ⬝ v) ⇓
  /-- The defining equation of `K`. -/
  eq_K : ∀ (u v : Part A), u ⇓ → v ⇓ → (K ⬝ u ⬝ v) = u
  /-- The defining equation of `S`. -/
  eq_S : ∀ (u v w : Part A), u ⇓ → v ⇓ → w ⇓ → S ⬝ u ⬝ v ⬝ w = (u ⬝ w) ⬝ (v ⬝ w)

attribute [simp] PCA.df_K₀
attribute [simp] PCA.df_K₁
attribute [simp] PCA.df_S₀
attribute [simp] PCA.df_S₁
attribute [simp] PCA.df_S₂

namespace PCA

/-- Every PCA is inhabited. We pick K as its default element. -/
instance inhabited {A : Type*} [PCA A] : Inhabited A where
  default := PCA.K.get PCA.df_K₀

end PCA

/-! `Expr Γ A` is the type of expressions built inductively from
    constants `K` and `S`, variables in `Γ` (the variable context),
    the elements of a carrier set `A`, and formal binary application.

    The usual accounts of PCAs typically do not introduce `K` and `S`
    as separate constants, because a PCA `A` already contains such combinators.
    However, as we defined the combinators to be partial elements, it is more
    convenient to have separate primitive constants denoting them.
    Also, this way `A` need not be an applicative structure.
-/

namespace PCA

/-- Expressions with variables from context `Γ` and elements from `A`. -/
inductive Expr (Γ A : Type*) where
/-- Formal expression denoting the K combinator -/
| K : Expr Γ A
/-- Formal expression denoting the S combinator -/
| S : Expr Γ A
/-- An element as a formal expression -/
| elm : A → Expr Γ A
/-- A variable as a formal expression -/
| var : Γ → Expr Γ A
/-- Formal expression application -/
| app : Expr Γ A → Expr Γ A → Expr Γ A

namespace Expr

/-- Formal application as a binary operation `·` -/
instance hasDot {Γ A : Type*} : HasDot (Expr Γ A) where
  dot := Expr.app

end Expr

section

universe u v
variable {Γ : Type u} [DecidableEq Γ]
variable {A : Type v} [PCA A]

/-- A valuation `η : Γ → A` assigning elements to variables,
    with the value of `x` overridden to be `a`. -/
@[reducible]
def override (x : Γ) (a : A) (η : Γ → A) (y : Γ) : A :=
  if y = x then a else η y

/-- Evaluate an expression with respect to a given valuation `η`. -/
def eval (η : Γ → A) : Expr Γ A → Part A
  | .K => PCA.K
  | .S => PCA.S
  | .elm a => .some a
  | .var x => .some (η x)
  | .app e₁ e₂ => (eval η e₁) ⬝ (eval η e₂)

/-- An expression is said to be defined when it is defined at every valuation. -/
def defined (e : Expr Γ A) := ∀ (η : Γ → A), (eval η e) ⇓

/-- The substitution of an element for the extra variable. -/
def subst (x : Γ) (a : A) : Expr Γ A → Expr Γ A
  | .K => .K
  | .S => .S
  | .elm b => .elm b
  | .var y => if y = x then .elm a else .var y
  | .app e₁ e₂ => (subst x a e₁) ⬝ (subst x a e₂)

/-- `abstr e` is an expression with one fewer variables than
    the expression `e`, which works similarly to function
    abastraction in the λ-calculus. It is at the heart of
    combinatory completeness. -/
def abstr (x : Γ) : Expr Γ A → Expr Γ A
  | .K => .K ⬝ .K
  | .S => .K ⬝ .S
  | .elm a => .K ⬝ .elm a
  | .var y => if y = x then .S ⬝ .K ⬝ .K else .K ⬝ .var y
  | .app e₁ e₂ => .S ⬝ (abstr x e₁) ⬝ (abstr x e₂)

/-- An abstraction is defined. -/
@[simp]
lemma df_abstr (x : Γ) (e : Expr Γ A) : defined (abstr x e) := by
  intro η
  induction e
  case K => simp [eval, abstr]
  case S => simp [eval, abstr]
  case elm => simp [eval, abstr]
  case var y =>
    cases (decEq y x)
    case isFalse h => simp [abstr, eval, h]
    case isTrue h => simp [abstr, eval, h]
  case app e₁ e₂ ih₁ ih₂ => simp [eval, abstr, ih₁, ih₂]

/-- `eval_abstr e` behaves like abstraction in the extra variable.
    This is known as *combinatory completeness*. -/
lemma eval_abstr (x : Γ) (e : Expr Γ A) (a : A) (η : Γ → A) :
    eval η (abstr x e ⬝ .elm a) = eval (override x a η) e := by
  induction e
  case K => simp [eq_K, eval, abstr]
  case S => simp [eq_K, eval, abstr]
  case elm => simp [eq_K, eval, abstr]
  case var y =>
    cases (decEq y x)
    case isFalse h => simp [eq_K, eval, abstr, override, h]
    case isTrue h => simp [eq_S, eq_K, eval, abstr, override, h]
  case app e₁ e₂ ih₁ ih₂ =>
    simp [eval] at ih₁
    simp [eval] at ih₂
    simp [eq_S, abstr, eval, df_abstr x _ η, ih₁, ih₂]

/-- Like `eval_abstr` but with the application on the outside of `eval`. -/
lemma eval_abstr_app (η : Γ → A) (x : Γ) (e : Expr Γ A) (u : Part A) (hu : u ⇓) :
    eval η (abstr x e) ⬝ u = eval (override x (u.get hu) η) e := by
  calc
    _ = eval η (abstr x e ⬝ .elm (u.get hu)) := by simp [eval]
    _ = eval (override x (u.get hu) η) e := by apply eval_abstr

@[simp]
lemma eval_override (η : Γ → A) (x : Γ) (a : A) (e : Expr Γ A) :
    eval (override x a η) e = eval η (subst x a e) := by
  induction e
  case K => simp [eval, subst]
  case S => simp [eval, subst]
  case elm => simp [eval, subst]
  case var y =>
    cases (decEq y x)
    case isFalse p => simp [eval, subst, p]
    case isTrue p => simp [eval, subst, p]
  case app e₁ e₂ ih₁ ih₂ => simp [eval, subst, ih₁, ih₂]

/-- Compile an expression to a partial element, substituting
    the default value for any variables occurring in e. -/
@[simp]
def compile (e : Expr Γ A) : Part A :=
  eval (fun _ => default) e

/-- Evaluate an expression under the assumption that it is closed.
    Return `inl x` if variable `x` is encountered, otherwise `inr u`
    where `u` is the partial element so obtained. -/
def eval_closed : Expr Γ A → Sum Γ (Part A)
  | .K => .inr K
  | .S => .inr S
  | .elm a => .inr (.some a)
  | .var x => .inl x
  | .app e₁ e₂ =>
    match eval_closed e₁ with
    | .inl x => .inl x
    | .inr a₁ =>
      match eval_closed e₂ with
      | .inl x => .inl x
      | .inr a₂ => .inr (a₁ ⬝ a₂)

/-- Notation for combinatory abstraction in an expression. -/
syntax:20 "≪" term "≫" term:20 : term

macro_rules
  | `(≪ $x:term ≫ $a:term) => `(LeanPool.PartialCombinatoryAlgebras.PCA.abstr $x $a)

/-- Notation for compiling a closed PCA expression to a partial element. -/
syntax "[pca: " term "]" : term

macro_rules
  | `([pca: $e:term ]) =>
    `(LeanPool.PartialCombinatoryAlgebras.PCA.compile (Γ := Lean.Name) $e)

end

end PCA

end LeanPool.PartialCombinatoryAlgebras
