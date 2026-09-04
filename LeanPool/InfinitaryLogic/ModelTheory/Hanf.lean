/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Lomega1omega.Theory
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Aleph
/-!
# Hanf Numbers

This file defines Hanf numbers for Lω₁ω sentences and states the fundamental
existence theorem and the Morley-Hanf bound.

## Main Definitions

- `HasArbLargeModels`: A sentence has arbitrarily large models.
- `IsHanfBound`: A cardinal κ is a Hanf bound for a sentence φ if having a model
  of size ≥ κ implies having arbitrarily large models.
- `HanfNumber`: The least Hanf bound for a sentence.

## Main Results

- `hanf_existence`: Every Lω₁ω sentence has a Hanf number.
- The universal property of `HanfNumber`: `hanfNumber_isHanfBound`,
  `hanfNumber_le_of_isHanfBound`, `hanfNumber_le_iff_isHanfBound`, `IsHanfBound.mono`.

The Morley-Hanf bound itself — `morley_hanf : IsHanfBound φ (ℶ_ω₁)`, unconditional over an
arbitrary language — is proved in `Conditional/MorleyHanfSchemaDischarge.lean` and exposed
(with its `HanfNumber` corollaries) through `ModelTheory/MorleyHanf.lean`.

## References

- [KK04], §1.6
- [Mar16], §5
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure Cardinal Ordinal

/-- A sentence has arbitrarily large models if for every cardinal κ, there
exists a model of size ≥ κ. -/
def HasArbLargeModels (φ : L.Sentenceω) : Prop :=
  ∀ κ : Cardinal, ∃ (M : Type) (_ : L.Structure M),
    Sentenceω.Realize φ M ∧ Cardinal.mk M ≥ κ

/-- A cardinal κ is a Hanf bound for a sentence φ if the existence of a model
of size ≥ κ implies that φ has arbitrarily large models. -/
def IsHanfBound (φ : L.Sentenceω) (κ : Cardinal) : Prop :=
  (∃ (M : Type) (_ : L.Structure M),
    Sentenceω.Realize φ M ∧ Cardinal.mk M ≥ κ) →
  HasArbLargeModels φ

/-! ## The universal property of the Hanf number -/

/-- A Hanf bound stays a bound at every larger cardinal — the premise only weakens. -/
theorem IsHanfBound.mono {φ : L.Sentenceω} {κ μ : Cardinal}
    (hκ : IsHanfBound φ κ) (hκμ : κ ≤ μ) : IsHanfBound φ μ :=
  fun ⟨M, hStr, hφ, hge⟩ => hκ ⟨M, hStr, hφ, le_trans hκμ hge⟩

end Language

end FirstOrder
