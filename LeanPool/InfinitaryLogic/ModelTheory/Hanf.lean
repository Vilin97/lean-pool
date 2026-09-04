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

/-- The Hanf number of a sentence is the least cardinal that is a Hanf bound. -/
noncomputable def HanfNumber (φ : L.Sentenceω) : Cardinal :=
  sInf {κ : Cardinal | IsHanfBound φ κ}

/-- Every Lω₁ω sentence has a Hanf number (i.e., a Hanf bound exists).

This is a fundamental structural result about Lω₁ω. -/
theorem hanf_existence (φ : L.Sentenceω) : ∃ κ, IsHanfBound φ κ := by
  by_cases h : HasArbLargeModels φ
  · -- Any κ works: the conclusion `HasArbLargeModels φ` is always true
    exact ⟨0, fun _ => h⟩
  · -- ¬HasArbLargeModels: ∃ κ₀ with no model of size ≥ κ₀, so premise is vacuously false
    simp only [HasArbLargeModels, not_forall] at h
    obtain ⟨κ₀, hκ₀⟩ := h
    push Not at hκ₀
    exact ⟨κ₀, fun ⟨M, hStr, hM, hge⟩ => absurd hge (not_le.mpr (hκ₀ M hStr hM))⟩

/-! ## The universal property of the Hanf number -/

/-- A Hanf bound stays a bound at every larger cardinal — the premise only weakens. -/
theorem IsHanfBound.mono {φ : L.Sentenceω} {κ μ : Cardinal}
    (hκ : IsHanfBound φ κ) (hκμ : κ ≤ μ) : IsHanfBound φ μ :=
  fun ⟨M, hStr, hφ, hge⟩ => hκ ⟨M, hStr, hφ, le_trans hκμ hge⟩

/-- **The Hanf number is itself a Hanf bound**: the set of bounds is nonempty
(`hanf_existence`), and an infimum of cardinals is attained. -/
theorem hanfNumber_isHanfBound (φ : L.Sentenceω) : IsHanfBound φ (HanfNumber φ) :=
  show HanfNumber φ ∈ {κ : Cardinal | IsHanfBound φ κ} from
    csInf_mem ⟨(hanf_existence φ).choose, (hanf_existence φ).choose_spec⟩

/-- The Hanf number is the least Hanf bound. -/
theorem hanfNumber_le_of_isHanfBound {φ : L.Sentenceω} {κ : Cardinal}
    (hκ : IsHanfBound φ κ) : HanfNumber φ ≤ κ :=
  csInf_le' hκ

/-- The universal property: `HanfNumber φ ≤ κ` exactly when `κ` is a Hanf bound (bounds are
upward closed and the Hanf number is the least one). -/
theorem hanfNumber_le_iff_isHanfBound {φ : L.Sentenceω} {κ : Cardinal} :
    HanfNumber φ ≤ κ ↔ IsHanfBound φ κ :=
  ⟨fun h => (hanfNumber_isHanfBound φ).mono h, hanfNumber_le_of_isHanfBound⟩

/-- The strict dual of the universal property — the bounded-spectrum witness-consumption
interface: refuting the bound at `κ` is exactly the strict lower bound `κ < HanfNumber φ`. -/
theorem lt_hanfNumber_iff_not_isHanfBound {φ : L.Sentenceω} {κ : Cardinal} :
    κ < HanfNumber φ ↔ ¬IsHanfBound φ κ := by
  rw [← not_le, hanfNumber_le_iff_isHanfBound]

end Language

end FirstOrder
