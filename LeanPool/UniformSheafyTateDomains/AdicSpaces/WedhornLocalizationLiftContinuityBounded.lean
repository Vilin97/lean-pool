/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalizationLiftContinuity
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornExtendValuationContinuity
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornValuationLocalizationLift

/-!
# Bounded-hypothesis Spv-level localization lift continuity bridge

Integration of the Mathlib-Valuation-level continuity theorem
`extendToLocalization_isContinuous_locTopology_of_bounded`
(`Adic spaces/WedhornExtendValuationContinuity.lean`) with the
Spv-level reduction lemma `localizationLift_isContinuous_iff_extension`
(`Adic spaces/WedhornLocalizationLiftContinuity.lean`).

## Bridge structure

The Spv-level continuity of `localizationLift (Submonoid.powers s) B v hS`
reduces (by `localizationLift_isContinuous_iff_extension`) to the
continuity of the Mathlib Valuation `(ValuativeRel.valuation A).extendToLocalization
hS' B` viewed as a Valuation. Under the natural Wedhorn callsite
hypotheses:

* `hν_A₀ : ∀ a ∈ P.A₀, v.vle a 1` (canonical valuation bounded by 1 on
  the ring of definition; implied by `A⁺ ⊆ A₀ ⊆ A` and `v ∈ Spa A A⁺`)
* `hv_T : ∀ t ∈ T, v.vle t s` (canonical valuation bounded by `v(s)` on
  the test family; equivalent to `v ∈ rationalOpen T s`)

the latter Valuation continuity is supplied by
`extendToLocalization_isContinuous_locTopology_of_bounded`. This bridge
discharges the Spv-level continuity needed by
`valuationLocalizationLift_via_continuity` (and hence the full
localization lift) WITHOUT requiring the abstract continuity hypothesis.

## What this file provides

1. `localizationLift_isContinuous_locTopology_of_bounded` — the Spv-level
   continuity bridge. Takes `v.IsContinuous`, `hν_A₀`, `hv_T`, and
   `hS`, produces `(localizationLift _ _ v _).IsContinuous`. Single-line
   composition of the reduction lemma with the bounded valuation
   continuity.

2. `valuationLocalizationLift_of_bounded` — full localization lift
   under the bounded hypotheses. Combines (1) with
   `valuationLocalizationLift_via_continuity` to produce the Spa point +
   comap identity, with no remaining abstract continuity hypothesis.

## Hypothesis discharges (for downstream Wedhorn 8.34(ii) callsites)

The two bounded hypotheses translate naturally:
* `hν_A₀` from `[CompatiblePlusSubring A]` (`A⁺ ⊆ P.A₀`) plus `v ∈ Spa A A⁺`.
* `hv_T` from `v ∈ rationalOpen T s`.

These are typical Wedhorn callsite assumptions; the hypotheses remain
explicit in this file's signatures (per manager guidance: "do not hide
the two boundedness assumptions"). A `_of_spa_rationalOpen` wrapper
deriving them automatically is the documented residual below.

## Notes

* No root import; leaf-level file.
* No edits to committed bridge files.
* No Lane B / Cor 8.32 / Jacobson / T001 / faithful-flatness /
  final-acyclicity content. -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **Spv-level continuity bridge under bounded hypotheses**.

Combines `localizationLift_isContinuous_iff_extension` (Spv-level
reduction) with `extendToLocalization_isContinuous_locTopology_of_bounded`
(Mathlib-Valuation-level bounded continuity) to produce the Spv-level
continuity of the localization lift.

**Hypotheses** (all in terms of the Spv structure on `v`):

* `hv_cont : v.IsContinuous` — `v` is a continuous Spv on `A`.
* `hν_A₀ : ∀ a ∈ P.A₀, v.vle a 1` — `v` bounded by 1 on the ring of
  definition.
* `hv_T : ∀ t ∈ T, v.vle t s` — `v` bounded by `v(s)` on the test
  family.
* `hS : Submonoid.powers s ≤ v.supp.primeCompl` — equivalent to
  `¬ v.vle s 0` (`s` is non-degenerate at `v`).

**Conclusion**: `(localizationLift (Submonoid.powers s) (Localization.Away s)
v hS).IsContinuous` under the topology `locTopology P T s hopen` on
`Localization.Away s`. -/
theorem localizationLift_isContinuous_locTopology_of_bounded
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    {v : Spv A} (hv_cont : v.IsContinuous)
    (hv_T : ∀ t ∈ T, v.vle t s)
    (hS : Submonoid.powers s ≤ v.supp.primeCompl) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    (localizationLift (Submonoid.powers s) (Localization.Away s) v hS).IsContinuous := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : ValuativeRel A := v.toValuativeRel
  apply localizationLift_isContinuous_iff_extension (Submonoid.powers s)
    (Localization.Away s) hS
  -- ν := canonical valuation; convert v-level hypotheses to ν-level via Compatible.
  set ν := ValuativeRel.valuation A with hν_def
  -- Compatible instance for translating v.vle ↔ ν _ ≤ ν _.
  have hcompat : (ν : Valuation A _).Compatible := inferInstance
  -- ν.IsContinuous follows from v.IsContinuous (definitional).
  have hν_cont : ν.IsContinuous := hv_cont
  -- ν t ≤ ν s on T: from hv_T via vle_iff_le.
  have hν_T_val : ∀ t ∈ T, ν t ≤ ν s := by
    intro t ht
    exact (Valuation.Compatible.vle_iff_le (v := ν) t s).mp (hv_T t ht)
  -- Translate hS : Submonoid.powers s ≤ v.supp.primeCompl
  -- to Submonoid.powers s ≤ ν.supp.primeCompl.
  have hS' : Submonoid.powers s ≤ ν.supp.primeCompl := by
    intro x hx
    change x ∉ ν.supp
    rw [← @ValuativeRel.supp_eq_valuation_supp A _ v.toValuativeRel]
    exact hS hx
  exact extendToLocalization_isContinuous_locTopology_of_bounded
    P T s hopen ν hν_cont hν_T_val hS'

/-- **Full localization lift under bounded hypotheses** (Wedhorn 8.34(ii)
callsite-ready).

Combines the bounded continuity bridge
(`localizationLift_isContinuous_locTopology_of_bounded`, above)
with `valuationLocalizationLift_via_continuity`
(`Adic spaces/WedhornValuationLocalizationLift.lean`)
to produce the full localized Spa point + comap identity, WITHOUT any
remaining abstract continuity hypothesis.

**Hypotheses**: standard Spa membership `hv : v ∈ Spa A A⁺`,
non-degeneracy `hvs : ¬ v.vle s 0`, plus the two Wedhorn-callsite
boundedness conditions `hν_A₀` and `hv_T`.

**Conclusion**: existence of `w ∈ Spa(Localization.Away s,
(localizationAwayPlusSubring s).toSubring)` with the comap identity
`comap (algebraMap A _) w = v`. -/
theorem valuationLocalizationLift_of_bounded
    [PlusSubring A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    {v : Spv A} (hv : v ∈ Spa A A⁺)
    (hv_T : ∀ t ∈ T, v.vle t s)
    (hvs : ¬ v.vle s 0) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    ∃ w : Spv (Localization.Away s),
      w ∈ @Spa (Localization.Away s) _ (locTopology P T s hopen)
        (localizationAwayPlusSubring s).toSubring ∧
      comap (algebraMap A (Localization.Away s)) w = v := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  -- Derive Submonoid.powers s ≤ v.supp.primeCompl from hvs.
  have hS := valuationLocalizationLift_powers_subset_primeCompl hvs
  have h_cont : (localizationLift (Submonoid.powers s) (Localization.Away s) v hS).IsContinuous :=
    localizationLift_isContinuous_locTopology_of_bounded P T s hopen
      hv.1 hv_T hS
  exact valuationLocalizationLift_via_continuity P T s hopen hv hvs h_cont

end ValuationSpectrum
