/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Wedhorn Localization Denominator Clearing

Algebraic step on the Wedhorn 8.34(ii) supplier-core route: every element
of `Localization.Away s` admits a denominator-clearing identity
`x * s ^ n = algebraMap a` for some `a : A, n : ℕ`. This is direct
`IsLocalization.surj` plus `Submonoid.powers` unpacking, but isolating it
as a named lemma is what `WedhornC1StrongSupplierCore.lean` consumes when
turning the Cor 7.32 dominating unit (defined in the localization) into
an `A`-element after multiplication by a power of the base denominator.

## What this file provides

* `exists_away_denominator_cleared` — for every `x : Localization.Away s`,
  some `(a : A, n : ℕ)` satisfies
  `x * (algebraMap s) ^ n = algebraMap a`. Proof: `IsLocalization.surj`
  gives `(a, c) : A × Submonoid.powers s` with `x * algebraMap c.val =
  algebraMap a`; `c.property` produces `n : ℕ` with `s ^ n = c.val`, and
  `map_pow` finishes.

* `exists_unit_away_denominator_cleared` — direct specialisation to units
  `u : (Localization.Away s)ˣ`. Identical conclusion shape with `(u : _)`
  in place of an arbitrary `x`. Used by the supplier-core path where the
  Cor 7.32 dominating unit `σ_loc` is by construction a unit in the
  localization.

* `exists_unit_away_denominator_cleared_with_invariant` — a slightly
  strengthened variant exposing the witness `(a, n)` together with the
  underlying surjection identity, suitable for downstream consumers that
  need to compute `σ_A := σ_loc * s ^ n` in the localization before
  comparing to `algebraMap a`.

## Notes

* Imports only `Mathlib.RingTheory.Localization.Away.Basic` — pure
  Mathlib content, no project-internal dependencies.
* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness content.
* Does not edit Tertiary's `WedhornValuationLocalizationLift.lean`,
  `WedhornC1StrongSupplierCore.lean`, or any other in-flight file.
-/

@[expose] public section

namespace ValuationSpectrum

/-- **Denominator clearing in `Localization.Away s`** — every element of
the localization admits an `A`-witness after multiplication by a power
of `s`. This is the "Step 3" algebraic step required by
`WedhornC1StrongSupplierCore.lean` when transferring Cor 7.32 dominating
units back to `A`. -/
theorem exists_away_denominator_cleared
    {A : Type*} [CommRing A] (s : A) (x : Localization.Away s) :
    ∃ (a : A) (n : ℕ),
      x * (algebraMap A (Localization.Away s) s) ^ n =
        algebraMap A (Localization.Away s) a := by
  obtain ⟨⟨a, c⟩, hac⟩ := IsLocalization.surj (Submonoid.powers s) x
  obtain ⟨n, hn⟩ := c.property
  change s ^ n = (↑c : A) at hn
  refine ⟨a, n, ?_⟩
  rw [← map_pow, hn]
  exact hac

/-- **Denominator clearing for units in `Localization.Away s`** —
specialisation of `exists_away_denominator_cleared` to a unit
`u : (Localization.Away s)ˣ`. This matches the supplier-core callsite
where the dominating unit `σ_loc` from Cor 7.32 enters as a unit in the
localized ring. -/
theorem exists_unit_away_denominator_cleared
    {A : Type*} [CommRing A] (s : A) (u : (Localization.Away s)ˣ) :
    ∃ (a : A) (n : ℕ),
      (u : Localization.Away s) * (algebraMap A (Localization.Away s) s) ^ n =
        algebraMap A (Localization.Away s) a :=
  exists_away_denominator_cleared s (u : Localization.Away s)

/-- **Denominator clearing for units, with invariant**. Exposes the
witness `(a, n)` together with the explicit surjection identity, in the
form most directly usable downstream of the Cor 7.32 dominating unit:
the cleared element `σ_A := a` represents `σ_loc * s ^ n`. -/
theorem exists_unit_away_denominator_cleared_with_invariant
    {A : Type*} [CommRing A] (s : A) (u : (Localization.Away s)ˣ) :
    ∃ (a : A) (n : ℕ),
      (u : Localization.Away s) * (algebraMap A (Localization.Away s) s) ^ n =
        algebraMap A (Localization.Away s) a ∧
      (algebraMap A (Localization.Away s) a) =
        (u : Localization.Away s) * (algebraMap A (Localization.Away s) s) ^ n := by
  obtain ⟨a, n, h⟩ := exists_unit_away_denominator_cleared s u
  exact ⟨a, n, h, h.symm⟩

end ValuationSpectrum
