/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Lomega1omega.Syntax
import LeanPool.InfinitaryLogic.Mathlib.ModelTheory.Infinitary.Semantics
/-!
# Lω₁ω Semantics — compatibility facade over the fixed-carrier semantics

The three realization *definitions* are no longer given here. They come from
`Mathlib.ModelTheory.Infinitary.Semantics`, whose `BoundedFormulaInf.Realize` is the single
structural recursion serving every index carrier. This file re-exports that semantics under the
qualified names the project already uses, and keeps only what Mathlib does not provide.

## Why the definitions had to be adopted, not merely paralleled

`Lomega1omega/Syntax.lean` already identifies `BoundedFormulaω` with `BoundedFormulaInf ℕ`
definitionally. Keeping a *separate* recursive `Realize` here would leave two definitionally
distinct semantics for one and the same formula type: dot-notation `φ.Realize` resolves through
the head symbol to `BoundedFormulaInf.Realize`, while the qualified `BoundedFormulaω.Realize`
would name the other one. Every later operation would then have to pick, and would pick wrong.

## What this file still owns

- the qualified `Realize` names, as **reducible aliases** — 100-odd files name
  `BoundedFormulaω.Realize` / `Formulaω.Realize` / `Sentenceω.Realize` explicitly, many in
  `@`-applied form, so the aliases reproduce Mathlib's semantics at the project's historical
  argument order;
- compatibility wrappers carrying the project's realization theorem names, with the project's
  **explicit** argument convention (Mathlib states these with implicit arguments);
- realization for the connectives Mathlib does not define: `and`/`or`/`iff` and the
  `Encodable`-indexed `einf`/`esup` with their explicit-encoding forms;
- the `⊨ω` notation.

The gates at the end certify by `Iff.rfl` — no rewriting, no casts — that each alias *is* the
Mathlib semantics, and that the historical `Fin.elim0` spellings of the arity-0 cases still
agree with Mathlib's `default`.
-/

universe u v w u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}
variable {M : Type w} [L.Structure M]
variable {α : Type u'} {n : ℕ}

open FirstOrder Structure Fin

namespace BoundedFormulaω

/-- Realization of a bounded Lω₁ω formula, as a qualified name.
`Mathlib`'s `BoundedFormulaInf.Realize` is the definition; this alias is `@[reducible]` and
reproduces the project's historical argument order `L M inst α n φ v xs`. -/
abbrev Realize (φ : L.BoundedFormulaω α n) (v : α → M) (xs : Fin n → M) : Prop :=
  BoundedFormulaInf.Realize φ v xs

variable {v : α → M} {xs : Fin n → M}

/-! ### Primitive connectives

Mathlib states each of these with implicit arguments; the project's consumers supply them
explicitly (`realize_rel R ts`, `realize_imp φ ψ`, …), so the wrappers keep that convention. -/

@[simp]
theorem realize_falsum : (falsum : L.BoundedFormulaω α n).Realize v xs ↔ False :=
  BoundedFormulaInf.realize_falsum

@[simp]
theorem realize_bot : (⊥ : L.BoundedFormulaω α n).Realize v xs ↔ False :=
  BoundedFormulaInf.realize_bot

@[simp]
theorem realize_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (equal t₁ t₂ : L.BoundedFormulaω α n).Realize v xs ↔
      t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs) :=
  BoundedFormulaInf.realize_equal

@[simp]
theorem realize_rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (rel R ts : L.BoundedFormulaω α n).Realize v xs ↔
      RelMap R fun i => (ts i).realize (Sum.elim v xs) :=
  BoundedFormulaInf.realize_rel

@[simp]
theorem realize_imp (φ ψ : L.BoundedFormulaω α n) :
    (imp φ ψ).Realize v xs ↔ (φ.Realize v xs → ψ.Realize v xs) :=
  BoundedFormulaInf.realize_imp

@[simp]
theorem realize_all (φ : L.BoundedFormulaω α (n + 1)) :
    (all φ).Realize v xs ↔ ∀ x : M, φ.Realize v (snoc xs x) :=
  BoundedFormulaInf.realize_all

@[simp]
theorem realize_iSup (φs : ℕ → L.BoundedFormulaω α n) :
    (iSup φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs :=
  BoundedFormulaInf.realize_iSup

@[simp]
theorem realize_iInf (φs : ℕ → L.BoundedFormulaω α n) :
    (iInf φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs :=
  BoundedFormulaInf.realize_iInf

@[simp]
theorem realize_top : (⊤ : L.BoundedFormulaω α n).Realize v xs ↔ True :=
  BoundedFormulaInf.realize_top

@[simp]
theorem realize_not (φ : L.BoundedFormulaω α n) :
    φ.not.Realize v xs ↔ ¬φ.Realize v xs :=
  BoundedFormulaInf.realize_not

@[simp]
theorem realize_ex (φ : L.BoundedFormulaω α (n + 1)) :
    φ.ex.Realize v xs ↔ ∃ x : M, φ.Realize v (snoc xs x) :=
  BoundedFormulaInf.realize_ex

/-! ### Connectives the project owns -/

@[simp]
theorem realize_and (φ ψ : L.BoundedFormulaω α n) :
    (φ.and ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs := by
  simp only [BoundedFormulaω.and, realize_not, realize_imp]
  tauto

@[simp]
theorem realize_inf (φ ψ : L.BoundedFormulaω α n) :
    (φ ⊓ ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs :=
  realize_and φ ψ

@[simp]
theorem realize_or (φ ψ : L.BoundedFormulaω α n) :
    (φ.or ψ).Realize v xs ↔ φ.Realize v xs ∨ ψ.Realize v xs := by
  simp only [BoundedFormulaω.or, realize_not, realize_imp]
  tauto

@[simp]
theorem realize_sup (φ ψ : L.BoundedFormulaω α n) :
    (φ ⊔ ψ).Realize v xs ↔ φ.Realize v xs ∨ ψ.Realize v xs :=
  realize_or φ ψ

@[simp]
theorem realize_iff (φ ψ : L.BoundedFormulaω α n) :
    (φ.iff ψ).Realize v xs ↔ (φ.Realize v xs ↔ ψ.Realize v xs) := by
  simp only [BoundedFormulaω.iff, realize_inf, realize_imp, iff_def]

@[simp]
theorem realize_einf {ι : Type*} [Encodable ι] (φs : ι → L.BoundedFormulaω α n) :
    (einf φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs := by
  simp only [einf, realize_iInf]
  constructor
  · intro h i
    simpa only [Encodable.encodek] using h (Encodable.encode i)
  · intro h k
    cases hd : Encodable.decode (α := ι) k with
    | none => simp only [realize_top]
    | some i => exact h i

@[simp]
theorem realize_esup {ι : Type*} [Encodable ι] (φs : ι → L.BoundedFormulaω α n) :
    (esup φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs := by
  simp only [esup, realize_iSup]
  constructor
  · rintro ⟨k, hk⟩
    cases hd : Encodable.decode (α := ι) k with
    | none => simp only [hd, realize_bot] at hk
    | some i =>
      exact ⟨i, by simpa only [hd] using hk⟩
  · rintro ⟨i, hi⟩
    use Encodable.encode i
    simp only [Encodable.encodek, hi]

/-- Realization of `einfWith`: the supplied encoding does not affect the semantics. -/
@[simp] theorem realize_einfWith {ι : Type*} (e : Encodable ι) (φs : ι → L.BoundedFormulaω α n) :
    (einfWith e φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs :=
  @realize_einf L M _ α n v xs ι e φs

/-- Realization of `esupWith`. -/
@[simp] theorem realize_esupWith {ι : Type*} (e : Encodable ι) (φs : ι → L.BoundedFormulaω α n) :
    (esupWith e φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs :=
  @realize_esup L M _ α n v xs ι e φs

end BoundedFormulaω

namespace Formulaω

/-- Realization of an Lω₁ω formula, as a qualified name. Mathlib's `FormulaInf.Realize` is the
definition; it fills the arity-0 valuation with `default`, which is definitionally the project's
historical `Fin.elim0` (gated below). -/
abbrev Realize (φ : L.Formulaω α) (v : α → M) : Prop :=
  FormulaInf.Realize φ v

variable {φ : L.Formulaω α} {v : α → M}

/-- The level-crossing lemma: formula realization *is* bounded-formula realization at the empty
tuple.

`FormulaInf.Realize` is a plain definition upstream, not a reducible abbreviation (matching the
finitary `Formula.Realize`), so neither `rw` nor `simp` can see a `BoundedFormulaω` realization
lemma through it. Supply this lemma explicitly — `simp only [Formulaω.realize_def, realize_not]` —
in place of unfolding `Formulaω.Realize`, which lands on the opaque `FormulaInf.Realize` and makes
every bounded-formula lemma inapplicable. Deliberately not `@[simp]`: the formula-level lemmas
below are the normal interface, and this escape hatch should be visible where it is used. -/
theorem realize_def (φ : L.Formulaω α) (v : α → M) :
    Realize φ v ↔ BoundedFormulaω.Realize φ v Fin.elim0 := Iff.rfl

@[simp]
theorem realize_not : Realize φ.not v ↔ ¬Realize φ v := BoundedFormulaω.realize_not φ

@[simp]
theorem realize_bot : Realize (⊥ : L.Formulaω α) v ↔ False := BoundedFormulaω.realize_bot

@[simp]
theorem realize_top : Realize (⊤ : L.Formulaω α) v ↔ True := BoundedFormulaω.realize_top

@[simp]
theorem realize_imp (φ ψ : L.Formulaω α) :
    Realize (φ.imp ψ) v ↔ (Realize φ v → Realize ψ v) := BoundedFormulaω.realize_imp φ ψ

@[simp]
theorem realize_inf (φ ψ : L.Formulaω α) :
    Realize (φ ⊓ ψ) v ↔ Realize φ v ∧ Realize ψ v := BoundedFormulaω.realize_inf φ ψ

@[simp]
theorem realize_sup (φ ψ : L.Formulaω α) :
    Realize (φ ⊔ ψ) v ↔ Realize φ v ∨ Realize ψ v := BoundedFormulaω.realize_sup φ ψ

@[simp]
theorem realize_einf {ι : Type*} [Encodable ι] (φs : ι → L.Formulaω α) :
    Realize (BoundedFormulaω.einf φs) v ↔ ∀ i, Realize (φs i) v := BoundedFormulaω.realize_einf φs

@[simp]
theorem realize_esup {ι : Type*} [Encodable ι] (φs : ι → L.Formulaω α) :
    Realize (BoundedFormulaω.esup φs) v ↔ ∃ i, Realize (φs i) v := BoundedFormulaω.realize_esup φs

end Formulaω

namespace Sentenceω

/-- Truth of an Lω₁ω sentence in a structure, as a qualified name. Mathlib's
`SentenceInf.Realize` is the definition. -/
abbrev Realize (φ : L.Sentenceω) (M : Type w) [L.Structure M] : Prop :=
  SentenceInf.Realize φ M

/-- The level-crossing lemma: sentence truth *is* bounded-formula realization at the empty
valuation and the empty tuple. See `Formulaω.realize_def` for why this is needed and why it is
not a `simp` lemma. -/
theorem realize_def (φ : L.Sentenceω) (M : Type w) [L.Structure M] :
    Realize φ M ↔ BoundedFormulaω.Realize φ (Empty.elim : Empty → M) Fin.elim0 := Iff.rfl

/-- Notation for a structure satisfying a sentence. -/
scoped notation:51 M " ⊨ω " φ:51 => Sentenceω.Realize φ M

end Sentenceω

/-! ## Facade semantics gates

Each must close by `Iff.rfl` — no `change`, no rewriting, no explicit cast. That is what
certifies that the qualified ω names *are* Mathlib's semantics rather than a parallel copy of
it, and that the arity-0 spellings the project has used throughout (`Fin.elim0`, `Empty.elim`)
still agree with Mathlib's `default`. -/

section Gates

variable {v : α → M} {xs : Fin n → M}

/-- The bounded alias is Mathlib's realization. -/
example (φ : L.BoundedFormulaω α n) :
    BoundedFormulaω.Realize φ v xs ↔ BoundedFormulaInf.Realize φ v xs := Iff.rfl

/-- The formula alias is Mathlib's realization. -/
example (φ : L.Formulaω α) : Formulaω.Realize φ v ↔ FormulaInf.Realize φ v := Iff.rfl

/-- The sentence alias is Mathlib's realization. -/
example (φ : L.Sentenceω) : Sentenceω.Realize φ M ↔ SentenceInf.Realize φ M := Iff.rfl

/-- Dot-notation, which resolves through the head symbol `BoundedFormulaInf`, agrees with the
qualified alias. -/
example (φ : L.BoundedFormulaω α n) : φ.Realize v xs ↔ BoundedFormulaω.Realize φ v xs := Iff.rfl

/-- The historical arity-0 spelling: Mathlib's `default : Fin 0 → M` is `Fin.elim0`. -/
example (φ : L.Formulaω α) :
    Formulaω.Realize φ v ↔ BoundedFormulaω.Realize φ v Fin.elim0 := Iff.rfl

/-- The historical sentence spelling, on which many `show` steps in the tower depend. -/
example (φ : L.Sentenceω) :
    Sentenceω.Realize φ M ↔
      BoundedFormulaω.Realize φ (Empty.elim : Empty → M) Fin.elim0 := Iff.rfl

/-- The `@`-applied argument order used by 40-odd consumer sites is unchanged:
`L`, `M`, the instance, `α`, `n`, then the formula and both valuations. -/
example (inst : L.Structure M) (φ : L.BoundedFormulaω α n) (v : α → M) (xs : Fin n → M) :
    @BoundedFormulaω.Realize L M inst α n φ v xs ↔
      @BoundedFormulaInf.Realize L ℕ α M inst n φ v xs := Iff.rfl

end Gates

end Language

end FirstOrder
