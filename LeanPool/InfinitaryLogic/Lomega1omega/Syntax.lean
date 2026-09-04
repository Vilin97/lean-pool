/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Mathlib.ModelTheory.Infinitary.Syntax
import Mathlib.Logic.Encodable.Basic

/-!
# Lω₁ω Syntax — compatibility facade over the fixed-carrier syntax

`BoundedFormulaω`, `Formulaω` and `Sentenceω` are no longer declared here. They come from
`Mathlib.ModelTheory.Infinitary.Syntax`, where `BoundedFormulaω L α n` is an **abbrev** for
`BoundedFormulaInf L ℕ α n`. This file re-exports that syntax under the module path and namespace
the project already uses, and adds only what Mathlib does not provide.

## Why an abbrev and not a `def`

The specialization must stay *definitional*, not merely propositional. Since Lean 4.34 a goal has
to be type-correct at `implicit` transparency before `rw`/`simp` will act on it, so a semireducible
wrapper around `BoundedFormulaInf ℕ` would silently break rewriting across the whole ω consumer
surface. The probes at the end of this file certify the identification with no `change`, rewrite,
or explicit cast — their *absence* is the certification.

## What this file still owns

- the qualified `BoundedFormulaω.*` constructor surface, for consumers that name constructors
  explicitly rather than through dot-notation (dot-notation resolves through the head symbol
  `BoundedFormulaInf` and needs no help);
- the derived connectives Mathlib does not define: `and`, `or`, `iff`, with their `Min`/`Max`
  instances;
- the `Encodable`-indexed connectives `einf`/`esup` and their explicit-encoding forms
  `einfWith`/`esupWith`;
- the scoped notation.

`Bot`, `Top`, `Inhabited`, `not` and `ex` now come from Mathlib and are deliberately **not**
redeclared. `BoundedFormulaInf.verum` plays the role of the old `top` and is definitionally equal to it
(`not falsum` reduces to `imp falsum falsum`).
-/

universe u v u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {α : Type u'} {n : ℕ}

namespace BoundedFormulaω

/-! ### Qualified constructor surface

The constructors live in the `BoundedFormulaInf` namespace. Dot-notation on a
`BoundedFormulaω` already resolves there, but consumers naming a constructor explicitly as
`BoundedFormulaω.falsum` need these. Each is an `abbrev`, so it unfolds by `rfl`, and each is
`@[match_pattern]`, so it may still be used in pattern position. -/

@[match_pattern] abbrev falsum : L.BoundedFormulaω α n := BoundedFormulaInf.falsum

@[match_pattern] abbrev equal (t₁ t₂ : L.Term (α ⊕ Fin n)) : L.BoundedFormulaω α n :=
  BoundedFormulaInf.equal t₁ t₂

@[match_pattern] abbrev rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    L.BoundedFormulaω α n :=
  BoundedFormulaInf.rel R ts

@[match_pattern] abbrev imp (φ ψ : L.BoundedFormulaω α n) : L.BoundedFormulaω α n :=
  BoundedFormulaInf.imp φ ψ

@[match_pattern] abbrev all (φ : L.BoundedFormulaω α (n + 1)) : L.BoundedFormulaω α n :=
  BoundedFormulaInf.all φ

@[match_pattern] abbrev iSup (φs : ℕ → L.BoundedFormulaω α n) : L.BoundedFormulaω α n :=
  BoundedFormulaInf.iSup φs

@[match_pattern] abbrev iInf (φs : ℕ → L.BoundedFormulaω α n) : L.BoundedFormulaω α n :=
  BoundedFormulaInf.iInf φs

/-- Negation, as a qualified name. `BoundedFormulaInf.not` is the definition. -/
@[match_pattern] protected abbrev not (φ : L.BoundedFormulaω α n) : L.BoundedFormulaω α n :=
  BoundedFormulaInf.not φ

/-- Existential quantification, as a qualified name. -/
@[match_pattern] protected abbrev ex (φ : L.BoundedFormulaω α (n + 1)) : L.BoundedFormulaω α n :=
  BoundedFormulaInf.ex φ

/-- The true formula. Mathlib calls it `verum`; this is the project's historical name for it, and
the two are definitionally equal (`not falsum` reduces to `imp falsum falsum`). -/
protected abbrev top : L.BoundedFormulaω α n := BoundedFormulaInf.verum

/-! Production's `not` and `ex` were `@[match_pattern]`; Mathlib's are not, and the attribute
**cannot** be added downstream ("cannot add attribute to a declaration in an imported module").
The qualified `BoundedFormulaω.not`/`.ex` above are declared here and so do carry it, which covers
consumers that name them explicitly; dot-notation *patterns* (`| .not φ => …`) resolve through the
head symbol to `BoundedFormulaInf.not` and are therefore not available. If a consumer needs them,
the fix belongs upstream on the fork, not here. -/

/-! ### Derived connectives Mathlib does not provide -/

/-- Conjunction of two formulas, defined via De Morgan. -/
@[match_pattern]
protected def and (φ ψ : L.BoundedFormulaω α n) : L.BoundedFormulaω α n :=
  (φ.imp ψ.not).not

instance : Min (L.BoundedFormulaω α n) := ⟨BoundedFormulaω.and⟩

/-- Disjunction of two formulas. -/
@[match_pattern]
protected def or (φ ψ : L.BoundedFormulaω α n) : L.BoundedFormulaω α n :=
  φ.not.imp ψ

instance : Max (L.BoundedFormulaω α n) := ⟨BoundedFormulaω.or⟩

/-- Biconditional between formulas. -/
protected def iff (φ ψ : L.BoundedFormulaω α n) : L.BoundedFormulaω α n :=
  (φ.imp ψ) ⊓ (ψ.imp φ)

/-- Indexed conjunction over any `Encodable` type. This extends `iInf` from ℕ-indexed
to general countable indices by encoding. -/
def einf {ι : Type*} [Encodable ι] (φs : ι → L.BoundedFormulaω α n) :
    L.BoundedFormulaω α n :=
  iInf fun k => match Encodable.decode (α := ι) k with
    | some i => φs i
    | none => ⊤

/-- Indexed disjunction over any `Encodable` type. This extends `iSup` from ℕ-indexed
to general countable indices by encoding. -/
def esup {ι : Type*} [Encodable ι] (φs : ι → L.BoundedFormulaω α n) :
    L.BoundedFormulaω α n :=
  iSup fun k => match Encodable.decode (α := ι) k with
    | some i => φs i
    | none => ⊥

/-! ### Explicit-encoding forms

`einf`/`esup` take their encoding by instance search.  A consumer that must use a *specific*
enumeration — one supplied as data rather than found — is otherwise forced into a local `letI`,
which is fragile and makes the resulting syntax look instance-dependent when it is not.

These are **thin wrappers**, deliberately: `einf`/`esup` are *not* redefined in terms of them.
Reversing that dependency would disturb definitional reductions across many existing consumers. -/

/-- `einf` along an explicitly supplied encoding. -/
def einfWith {ι : Type*} (e : Encodable ι) (φs : ι → L.BoundedFormulaω α n) :
    L.BoundedFormulaω α n :=
  @einf L α n ι e φs

/-- `esup` along an explicitly supplied encoding. -/
def esupWith {ι : Type*} (e : Encodable ι) (φs : ι → L.BoundedFormulaω α n) :
    L.BoundedFormulaω α n :=
  @esup L α n ι e φs

@[simp] theorem einfWith_eq {ι : Type*} (e : Encodable ι) (φs : ι → L.BoundedFormulaω α n) :
    einfWith e φs = @einf L α n ι e φs := rfl

@[simp] theorem esupWith_eq {ι : Type*} (e : Encodable ι) (φs : ι → L.BoundedFormulaω α n) :
    esupWith e φs = @esup L α n ι e φs := rfl

end BoundedFormulaω

-- Notation
scoped[Lomega1omega] infixr:62 " ⟹ω " => FirstOrder.Language.BoundedFormulaω.imp

scoped[Lomega1omega] prefix:110 "∀'ω " => FirstOrder.Language.BoundedFormulaω.all

scoped[Lomega1omega] prefix:arg "∼ω" => FirstOrder.Language.BoundedFormulaω.not

scoped[Lomega1omega] prefix:110 "∃'ω " => FirstOrder.Language.BoundedFormulaω.ex

scoped[Lomega1omega] infixl:61 " ⇔ω " => FirstOrder.Language.BoundedFormulaω.iff

/-! ## Facade transparency gates

These must elaborate with **no** `change`, rewrite, or explicit cast. That is precisely what
certifies that the ω names remain a definitional specialization — the property Lean 4.34's
`implicit`-transparency requirement makes load-bearing for every `rw`/`simp` in the ω tower. -/

section Gates

example (L : Language.{u, v}) (α : Type u') (n : ℕ) :
    L.BoundedFormulaω α n = L.BoundedFormulaInf ℕ α n := rfl

example (φ : L.BoundedFormulaω α n) : L.BoundedFormulaInf ℕ α n := φ

example (φ : L.BoundedFormulaInf ℕ α n) : L.BoundedFormulaω α n := φ

/-- Exact universe ascription: the ω syntax must land in `Type max u v u'`, with no `uι` bump. -/
example (L : Language.{u, v}) (α : Type u') (n : ℕ) : Type max u v u' := L.BoundedFormulaω α n

example (L : Language.{u, v}) (α : Type u') : L.Formulaω α = L.BoundedFormulaω α 0 := rfl

example (L : Language.{u, v}) : L.Sentenceω = L.Formulaω Empty := rfl

/-- The qualified ω aliases remain usable in **pattern** position. This is what the lost
`@[match_pattern]` on `BoundedFormulaInf.not`/`.ex` does *not* cost us: the aliases
declared in this file carry the attribute themselves. -/
example (φ : L.BoundedFormulaω α n) : Bool :=
  match φ with
  | BoundedFormulaω.falsum => false
  | BoundedFormulaω.equal _ _ => true
  | BoundedFormulaω.rel _ _ => true
  | BoundedFormulaω.imp _ _ => true
  | BoundedFormulaω.all _ => true
  | BoundedFormulaω.iSup _ => true
  | BoundedFormulaω.iInf _ => true

/-- Induction through the abbreviation: the recursor is reachable and its case names are the ones
the ω consumers already write. -/
example (φ : L.BoundedFormulaω α n) : True := by
  induction φ with
  | falsum => trivial
  | equal _ _ => trivial
  | rel _ _ => trivial
  | imp _ _ _ _ => trivial
  | all _ _ => trivial
  | iSup _ _ => trivial
  | iInf _ _ => trivial

end Gates

end Language

end FirstOrder
