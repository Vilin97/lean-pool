/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import LeanPool.DomainTheory.Neighborhood.Theorem41
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

/-!
# Exercise 4.20 (Scott 1981, PRG-19, Lecture IV)

For approximable `f, g : 𝒟 → 𝒟` prove that

  `fix(f ∘ g) = f(fix(g ∘ f))`.

In this development `f ∘ g` is `f.comp g`, whose elementwise action is
`f.toElementMap ∘ g.toElementMap` (`toElementMap_comp`). The least fixed point of
an endomap is
`fixElement` (Theorem 4.1), with its fixed-point equation
`toElementMap_fixElement` and its
least-pre-fixed-point characterization `fixElement_le_of_toElementMap_le`.

The proof is the classical "rolling rule" / dinaturality of the fixed-point
operator:
`f(fix(g ∘ f))` is a fixed point of `f ∘ g`, hence `⊒` the least one, and a
symmetric argument
gives the reverse inclusion. Everything stays at the level of `V.Element`, so the
whole file is
**choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

@[expose] public section

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- `f(fix(g ∘ f))` is a fixed point of `f ∘ g`:
`(f ∘ g)(f(fix(g∘f))) = f((g∘f)(fix(g∘f))) = f(fix(g∘f))`. -/
theorem comp_fixElement_isFixed (f g : ApproximableMap V V) :
    (f.comp g).toElementMap (f.toElementMap (g.comp f).fixElement)
      = f.toElementMap (g.comp f).fixElement := by
  rw [toElementMap_comp]
  -- `g(f(fix(g∘f))) = (g∘f)(fix(g∘f)) = fix(g∘f)`
  have h : g.toElementMap (f.toElementMap (g.comp f).fixElement) = (g.comp f).fixElement := by
    rw [← toElementMap_comp]
    exact toElementMap_fixElement (g.comp f)
  rw [h]

/-- **Exercise 4.20 (Scott 1981, PRG-19).** `fix(f ∘ g) = f(fix(g ∘ f))`. -/
theorem fixElement_comp_comm (f g : ApproximableMap V V) :
    (f.comp g).fixElement = f.toElementMap (g.comp f).fixElement := by
  apply le_antisymm
  · -- `fix(f∘g) ⊑ f(fix(g∘f))` since the latter is a (pre-)fixed point of `f∘g`.
    exact fixElement_le_of_toElementMap_le (f.comp g)
      (le_of_eq (comp_fixElement_isFixed f g))
  · -- `f(fix(g∘f)) ⊑ fix(f∘g)`. First, `fix(g∘f) ⊑ g(fix(f∘g))`.
    have hga : (g.comp f).fixElement ≤ g.toElementMap (f.comp g).fixElement := by
      apply fixElement_le_of_toElementMap_le (g.comp f)
      have : (g.comp f).toElementMap (g.toElementMap (f.comp g).fixElement)
          = g.toElementMap (f.comp g).fixElement := comp_fixElement_isFixed g f
      exact le_of_eq this
    -- apply `f` and use `f(g(fix(f∘g))) = (f∘g)(fix(f∘g)) = fix(f∘g)`.
    calc f.toElementMap (g.comp f).fixElement
        ≤ f.toElementMap (g.toElementMap (f.comp g).fixElement) := f.toElementMap_mono hga
      _ = (f.comp g).toElementMap (f.comp g).fixElement := by rw [toElementMap_comp]
      _ = (f.comp g).fixElement := toElementMap_fixElement (f.comp g)

end ApproximableMap

end Domain.Neighborhood
