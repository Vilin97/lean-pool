/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornValuationLocalizationLift
import LeanPool.UniformSheafyTateDomains.AdicSpaces.ContinuousValuations

/-!
# Continuity of the localization-lifted valuation under `locTopology`

The single remaining residual identified in
`WedhornValuationLocalizationLift.lean`:

```
theorem isContinuous_localizationLift_locTopology
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    {v : Spv A} (hv : v ∈ Cont A) (hvs : ¬ v.vle s 0)
    (hS : Submonoid.powers s ≤ v.supp.primeCompl) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    (localizationLift (Submonoid.powers s) (Localization.Away s) v hS).IsContinuous
```

## Audit and reduction

By `ValuationSpectrum.isContinuous_ofValuation_of` (`ContinuousValuations.lean:93`),
since `localizationLift = ofValuation (ν.extendToLocalization)`, the
continuity of the lift as a Spv reduces to the continuity of the
**extended valuation** `ν.extendToLocalization` as a Mathlib Valuation
`B → Γ` (with B = Localization.Away s, Γ = ValueGroupWithZero A).

The extended-valuation continuity is the **genuinely analytic content**:
for every γ in the value group, the set
`{b ∈ Localization.Away s | (ν.extendToLocalization) b < γ}` must be
open in `locTopology P T s hopen`.

## What this file provides

This file lands a **named reduction lemma**
(`localizationLift_isContinuous_iff_extension`) and a documented
residual for the genuinely analytic content. The reduction lemma
isolates the precise remaining obligation from the structural
reformulations.

## Documented residual after the reduction

The smallest remaining Lean lemma needed for the full continuity:

```
theorem extendToLocalization_isContinuous_locTopology
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (ν : Valuation A Γ) (hν_cont : ν.IsContinuous)
    (hS : Submonoid.powers s ≤ ν.supp.primeCompl) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    (ν.extendToLocalization hS (Localization.Away s)).IsContinuous
```

This is the genuinely-missing analytic content. Its proof requires:
* For each γ, exhibit an `m` such that `algebraMap (P.I^m) ⊆
  {a | ν(a) < γ}` (from ν's continuity at 0 in A, via `P.hasBasis_nhds_zero`).
* Bound the extended valuation on `locNhd P T s m'` for some `m'`,
  which requires careful handling of the `(locIdeal)^m'`-image
  representation as `∑ a_i · algebraMap(b_i)` with `a_i ∈ locSubring`
  and `b_i ∈ P.I^m'`.
* The bound on `(extendToLocalization ν)(a_i · algebraMap(b_i)) =
  (extendToLocalization ν)(a_i) · ν(b_i)` requires either:
  - A uniform bound on `(extendToLocalization ν)(locSubring)` (NOT
    available in general — locSubring elements `t/s` can have arbitrary
    values).
  - Or an absorptive trick: shrink m' so that ν(b_i) compensates the
    locSubring growth — which requires a uniform "growth rate" of
    `(extendToLocalization ν)` on `locSubring`'s generators `t/s`,
    bounded by `(ν(t)/ν(s))` per generator.

The proof is structurally similar to Wedhorn's Proposition 5.51
(universal property of `locTopology`) but for VALUATIONS rather than
ring homomorphisms. The technical difficulty is the same: bounding
multi-generator polynomial expressions in the value group.

## Notes

* No root import; leaf-level file.
* No edits to `ValuationSpectrum.lean`, `ContinuousValuations.lean`, or
  any committed bridge file.
* No Lane B / Cor 8.32 / Jacobson / T001 / faithful-flatness /
  final-acyclicity content. -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

omit [TopologicalSpace A] [IsTopologicalRing A] in
/-- **Reduction lemma**: continuity of the localization-lifted Spv
reduces to continuity of the extended Mathlib Valuation.

Given `v : Spv A`, the lift `localizationLift S B v hS : Spv B` is
defined as `ofValuation (ν.extendToLocalization hS' B)` where ν is the
canonical valuation of v's underlying ValuativeRel and hS' is the
corresponding precondition.

By `ValuationSpectrum.isContinuous_ofValuation_of`, the Spv-level
`IsContinuous` of the lift reduces to the Valuation-level `IsContinuous`
of the extension. This lemma packages that reduction in a form ready
for the direct continuity proof (`extendToLocalization_isContinuous_locTopology`,
documented as the next residual).

**Plug-in callsite**: once the extension's continuity is proved (the
trailing-docblock target), this reduction discharges the Spv-level
continuity needed by `valuationLocalizationLift_via_continuity`. -/
theorem localizationLift_isContinuous_iff_extension
    {v : Spv A} (S : Submonoid A) (B : Type*) [CommRing B] [Algebra A B]
    [IsLocalization S B] [TopologicalSpace B]
    (hS : S ≤ v.supp.primeCompl)
    (h_ext :
      letI : ValuativeRel A := v.toValuativeRel
      have hS' : S ≤ (ValuativeRel.valuation A).supp.primeCompl := by
        intro x hx hxs
        exact hS hx (by
          rw [show (ValuativeRel.valuation A).supp =
            @ValuativeRel.supp A _ v.toValuativeRel from
            ValuativeRel.supp_eq_valuation_supp.symm] at hxs; exact hxs)
      ((ValuativeRel.valuation A).extendToLocalization hS' B).IsContinuous) :
    (localizationLift S B v hS).IsContinuous := by
  letI : ValuativeRel A := v.toValuativeRel
  unfold localizationLift
  exact isContinuous_ofValuation_of _ h_ext

end ValuationSpectrum
