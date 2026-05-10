/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/

/-!
# Reader Selection Monad

A pure mathematical monad: a family of functions indexed by ι, composed with
a data-dependent selector. This is the Reader monad with indexed selection.

The three monad laws hold definitionally (by `rfl`).

This structure underlies MeasurableBatchLearner composition in the learning
theory layer, but the monad itself is pure mathematics with zero dependencies.
-/

universe u v w

/-- A reader-selection computation: family indexed by ι, selected by data. -/
structure ReaderSel (ι : Type u) (α : Type v) (γ : Type w) where
  /-- Family of functions available to the selector. -/
  family : ι → α → γ
  /-- Data-dependent selector for the family index. -/
  sel : α → ι

/-- Evaluate: apply the selected family member. -/
def ReaderSel.eval {ι : Type u} {α : Type v} {γ : Type w}
    (r : ReaderSel ι α γ) (a : α) : γ :=
  r.family (r.sel a) a

/-- Pure: constant family (selector is irrelevant). -/
def ReaderSel.pure {ι : Type u} {α : Type v} {γ : Type w}
    (i₀ : ι) (f : α → γ) : ReaderSel ι α γ where
  family := fun _ => f
  sel := fun _ => i₀

/-- Bind: the second computation may depend on the first's output.
    eval (bind r f) a = eval (f (eval r a)) a -/
def ReaderSel.bind {ι : Type u} {α : Type v} {γ : Type w}
    (r : ReaderSel ι α γ) (f : γ → ReaderSel ι α γ) :
    ReaderSel ι α γ where
  family := fun i a => (f (r.family (r.sel a) a)).family i a
  sel := fun a => (f (r.family (r.sel a) a)).sel a

/-- Left unit: bind (pure f) g a = (g (f a)).eval a -/
theorem ReaderSel.left_unit {ι : Type u} {α : Type v} {γ : Type w}
    (i₀ : ι) (f : α → γ)
    (g : γ → ReaderSel ι α γ) (a : α) :
    (ReaderSel.pure i₀ f |>.bind g).eval a = (g (f a)).eval a := by
  rfl

/-- Right unit: bind r (fun v => pure (const v)) a = r.eval a -/
theorem ReaderSel.right_unit {ι : Type u} {α : Type v} {γ : Type w}
    (r : ReaderSel ι α γ) (i₀ : ι) (a : α) :
    (r.bind (fun v => ReaderSel.pure i₀ (fun _ => v))).eval a = r.eval a := by
  rfl

/-- Associativity: bind (bind r f) g = bind r (fun v => bind (f v) g) -/
theorem ReaderSel.assoc {ι : Type u} {α : Type v} {γ : Type w}
    (r : ReaderSel ι α γ)
    (f : γ → ReaderSel ι α γ) (g : γ → ReaderSel ι α γ) (a : α) :
    ((r.bind f).bind g).eval a = (r.bind (fun v => (f v).bind g)).eval a := by
  rfl
