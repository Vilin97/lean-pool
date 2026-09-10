/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Descriptive.SatisfactionBorelOn
/-!
# Satisfaction of Lω₁ω Formulas is Borel

This file specializes the carrier-parametric result to structures on `ℕ`.

## Main Definitions

- `ModelsOfBounded`: The set of codes where a bounded formula is realized.
- `ModelsOf`: The set of codes where a sentence is realized.

## Main Results

- `modelsOf_measurableSet`: Satisfaction of any Lω₁ω sentence is measurable.
-/

universe u v u'

namespace FirstOrder

namespace Language

open Structure MeasureTheory

variable {L : Language.{u, v}}

section Measurability

variable [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- The set of codes where a bounded formula is realized, given variable assignments. -/
def ModelsOfBounded
    {α : Type u'} {n : ℕ}
    (φ : L.BoundedFormulaω α n) (v : α → ℕ) (xs : Fin n → ℕ) :
    Set (StructureSpace L) :=
  {c | @BoundedFormulaω.Realize L ℕ c.toStructure α n φ v xs}

/-- The set of codes where a sentence is realized. -/
def ModelsOf (φ : L.Sentenceω) : Set (StructureSpace L) :=
  ModelsOfBounded φ Empty.elim Fin.elim0

omit [Countable (Σ l, L.Relations l)] in
/-- Satisfaction of any Lω₁ω sentence in a countable relational language
is measurable on the structure space. -/
theorem modelsOf_measurableSet (φ : L.Sentenceω) :
    MeasurableSet (ModelsOf φ) := by
  change MeasurableSet (ModelsOfOn (α := ℕ) φ)
  exact modelsOfOn_measurableSet φ

end Measurability

end Language

end FirstOrder
