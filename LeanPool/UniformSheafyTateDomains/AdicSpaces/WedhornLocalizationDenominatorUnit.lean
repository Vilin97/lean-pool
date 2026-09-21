/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalizationDenominatorClearing
import LeanPool.UniformSheafyTateDomains.AdicSpaces.ValuationSpectrum

/-!
# Wedhorn Localization Denominator-Cleared Unit Nondegeneracy

Algebraic + valuation consequence of the denominator clearing identity
`u * s^n = algebraMap a` for a unit `u : (Localization.Away s)ˣ`: the
cleared element `a : A` is a non-zero divisor in `A` (its `algebraMap`
is a unit), and consequently has nonzero valuation under any
valuation on the localization or on `A`.

This is the "Step 4" follow-up to
`WedhornLocalizationDenominatorClearing` on the Wedhorn 8.34(ii)
supplier-core route.

## What this file provides

* `isUnit_algebraMap_of_unit_away_denominator_cleared` — algebraic
  unit-product of `u` and `(algebraMap s)^n`.
* `not_vle_zero_algebraMap_of_unit_away_denominator_cleared` — local
  valuation form: any `Spv (Localization.Away s)` valuation has nonzero
  value at the cleared `algebraMap a`.
* `not_vle_zero_base_of_unit_away_denominator_cleared` — base form via
  `comap`: under `comap (algebraMap A _) w = v`, the base valuation `v`
  satisfies `¬ v.vle a 0`.
* `not_vle_zero_pow` — pow-stability of nonzero valuation:
  `¬ v.vle s 0 → ¬ v.vle (s^n) 0` for any `v : Spv A, s : A, n : ℕ`.
* `not_vle_zero_mul_pow` — product form `¬ v.vle (f * s^n) 0` from
  `¬ v.vle f 0` and `¬ v.vle s 0`. Directly usable when constructing
  the Wedhorn 8.34(ii) `f := σ_A * D.s^N` candidate.

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness content.
* Does not edit Tertiary's `WedhornValuationLocalizationLift.lean`,
  `WedhornC1StrongSupplierCore.lean`, or any other in-flight file.
-/

namespace ValuationSpectrum

/-- **Algebraic unit form**. From the denominator-clearing identity for
a unit, the `algebraMap` of the cleared element `a` is itself a unit
(product of two units `u` and `(algebraMap s)^n`). -/
theorem isUnit_algebraMap_of_unit_away_denominator_cleared
    {A : Type*} [CommRing A] (s : A) (u : (Localization.Away s)ˣ)
    {a : A} {n : ℕ}
    (h : (u : Localization.Away s) * (algebraMap A (Localization.Away s) s) ^ n =
        algebraMap A (Localization.Away s) a) :
    IsUnit (algebraMap A (Localization.Away s) a) := by
  rw [← h]
  refine u.isUnit.mul ?_
  exact (IsLocalization.map_units (Localization.Away s)
    ⟨s, Submonoid.mem_powers s⟩).pow n

/-- **Local valuation form**. From `IsUnit (algebraMap a)`, no valuation
on `Localization.Away s` sends `algebraMap a` to zero. -/
theorem not_vle_zero_algebraMap_of_unit_away_denominator_cleared
    {A : Type*} [CommRing A] (s : A) (u : (Localization.Away s)ˣ)
    {a : A} {n : ℕ}
    (h : (u : Localization.Away s) * (algebraMap A (Localization.Away s) s) ^ n =
        algebraMap A (Localization.Away s) a)
    (w : Spv (Localization.Away s)) :
    ¬ w.vle (algebraMap A (Localization.Away s) a) 0 :=
  not_vle_zero_of_isUnit (isUnit_algebraMap_of_unit_away_denominator_cleared s u h) w

/-- **Base form via `comap`**. Under the `comap` relation
`comap (algebraMap A (Localization.Away s)) w = v`, the local
nondegeneracy of `w` at `algebraMap a` transfers to the base: `¬ v.vle a 0`. -/
theorem not_vle_zero_base_of_unit_away_denominator_cleared
    {A : Type*} [CommRing A] (s : A)
    {w : Spv (Localization.Away s)} {v : Spv A}
    (hcomap : comap (algebraMap A (Localization.Away s)) w = v)
    (u : (Localization.Away s)ˣ) {a : A} {n : ℕ}
    (h : (u : Localization.Away s) * (algebraMap A (Localization.Away s) s) ^ n =
        algebraMap A (Localization.Away s) a) :
    ¬ v.vle a 0 := by
  intro hv
  apply not_vle_zero_algebraMap_of_unit_away_denominator_cleared s u h w
  rw [← map_zero (algebraMap A (Localization.Away s)), ← comap_vle, hcomap]
  exact hv

/-- **Pow-stability of nonzero valuation**: a non-zero element raised to
any power is non-zero. -/
theorem not_vle_zero_pow
    {A : Type*} [CommRing A] {v : Spv A} {s : A}
    (hs : ¬ v.vle s 0) (n : ℕ) : ¬ v.vle (s ^ n) 0 := by
  let : ValuativeRel A := v.toValuativeRel
  induction n with
  | zero =>
      rw [pow_zero]
      exact v.not_vle_one_zero
  | succ k ih =>
      rw [pow_succ]
      exact ValuativeRel.zero_vlt_mul ih hs

/-- **Product-power nondegeneracy**: combine a non-zero `f` with a
non-zero power of `s` into a non-zero product `f * s^n`. Directly usable
when assembling the Wedhorn 8.34(ii) candidate `f := σ_A * D.s^N`. -/
theorem not_vle_zero_mul_pow
    {A : Type*} [CommRing A] {v : Spv A} {f s : A}
    (hf : ¬ v.vle f 0) (hs : ¬ v.vle s 0) (n : ℕ) :
    ¬ v.vle (f * s ^ n) 0 := by
  let : ValuativeRel A := v.toValuativeRel
  exact ValuativeRel.zero_vlt_mul hf (not_vle_zero_pow hs n)

end ValuationSpectrum
