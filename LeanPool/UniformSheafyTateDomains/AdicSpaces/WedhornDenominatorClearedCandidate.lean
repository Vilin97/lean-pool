/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalizationDenominatorUnit

/-!
# Wedhorn Denominator-Cleared Candidate Package

Packages the denominator-cleared local unit into the exact base-side
candidate data consumed by Wedhorn 8.34(ii). Composes:

* `exists_unit_away_denominator_cleared`
  (`WedhornLocalizationDenominatorClearing.lean`),
* `not_vle_zero_base_of_unit_away_denominator_cleared`
  (`WedhornLocalizationDenominatorUnit.lean`),
* `not_vle_zero_mul_pow`
  (`WedhornLocalizationDenominatorUnit.lean`).

The output is the precise input needed by the Wedhorn 8.34(ii)
candidate-construction step: an `A`-element clearing a `(Localization.Away
s)`-unit, non-zero under the base valuation `v` (via `comap`), and
optionally non-zero after multiplying by a power of a denominator
`d : A`.

## What this file provides

* `exists_base_nondegenerate_denominator_clear_of_local_unit` — for any
  unit `u : (Localization.Away s)ˣ` and any `v : Spv A` such that
  `comap (algebraMap A _) w = v`, produce `(a, n)` with the cleared
  identity and `¬ v.vle a 0`.

* `exists_base_nondegenerate_denominator_clear_mul_pow_of_local_unit` —
  `f := a * d^N` form: the cleared `a` multiplied by a power of a
  base-nondegenerate `d` is itself non-zero under `v`. Directly matches
  the `σ_A * D.s^N` candidate shape in Wedhorn 8.34(ii).

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness content.
* Does not edit Tertiary's `WedhornValuationLocalizationLift.lean`,
  `WedhornLocalizationLiftContinuity.lean`, `WedhornC1StrongSupplierCore.lean`,
  or any other in-flight file.
* Imports only `WedhornLocalizationDenominatorUnit` (which transitively
  imports `WedhornLocalizationDenominatorClearing` and the project
  valuation API).
-/

namespace ValuationSpectrum

/-- **Base-nondegenerate denominator-cleared candidate**.

For any unit `u : (Localization.Away s)ˣ` and any base valuation
`v : Spv A` arising via `comap` from a localization valuation `w`, the
denominator-clearing identity produces a base element `a : A` together
with an exponent `n : ℕ` such that
`u * (algebraMap s)^n = algebraMap a` and `¬ v.vle a 0`. -/
theorem exists_base_nondegenerate_denominator_clear_of_local_unit
    {A : Type*} [CommRing A] (s : A)
    {w : Spv (Localization.Away s)} {v : Spv A}
    (hcomap : comap (algebraMap A (Localization.Away s)) w = v)
    (u : (Localization.Away s)ˣ) :
    ∃ (a : A) (n : ℕ),
      (u : Localization.Away s) * (algebraMap A (Localization.Away s) s) ^ n =
        algebraMap A (Localization.Away s) a ∧
      ¬ v.vle a 0 := by
  obtain ⟨a, n, h⟩ := exists_unit_away_denominator_cleared s u
  exact ⟨a, n, h, not_vle_zero_base_of_unit_away_denominator_cleared s hcomap u h⟩

/-- **Product-power candidate form** `f := a * d^N` for Wedhorn 8.34(ii).

Given the base-nondegenerate cleared element from
`exists_base_nondegenerate_denominator_clear_of_local_unit` and an
additional base-nondegenerate `d : A` (e.g., `D.s`), the product
`a * d^N` is itself non-zero under `v`. This matches the candidate
`f := σ_A * D.s^N` shape in Wedhorn 8.34(ii). -/
theorem exists_base_nondegenerate_denominator_clear_mul_pow_of_local_unit
    {A : Type*} [CommRing A] (s : A)
    {w : Spv (Localization.Away s)} {v : Spv A}
    (hcomap : comap (algebraMap A (Localization.Away s)) w = v)
    (u : (Localization.Away s)ˣ) {d : A} (hd : ¬ v.vle d 0) (N : ℕ) :
    ∃ (a : A) (n : ℕ),
      (u : Localization.Away s) * (algebraMap A (Localization.Away s) s) ^ n =
        algebraMap A (Localization.Away s) a ∧
      ¬ v.vle (a * d ^ N) 0 := by
  obtain ⟨a, n, h, ha⟩ :=
    exists_base_nondegenerate_denominator_clear_of_local_unit s hcomap u
  exact ⟨a, n, h, not_vle_zero_mul_pow ha hd N⟩

end ValuationSpectrum
