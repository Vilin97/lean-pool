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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Cor732
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Prop752
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornExtendValuationContinuity
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornSpaRationalOpenLiftWrapper

/-!
# Wedhorn 8.34(ii): Localized plus-subring choice and lift upgrade

The previous wrapper `valuationLocalizationLift_of_spa_rationalOpen`
(`Adic spaces/WedhornSpaRationalOpenLiftWrapper.lean`) lands in
`Spa(Localization.Away s, localizationAwayPlusSubring s)` — but
`localizationAwayPlusSubring` is the IMAGE of `A⁺` only, NOT the local
ring of definition `locSubring P T s`. For the Wedhorn 8.34(ii)
σ-construction, the right plus subring on the localization is
`locSubring`, so that `locPairOfDefinition.A₀ = locSubring ≤ B⁺` is
trivial and `Cor732.exists_dominating_unit` becomes applicable.

## What this file provides

1. **`PlusSubring (Localization.Away s)` instance with `locSubring`** —
   `localizationLocSubringPlusSubring P T s`. Differs from
   `localizationAwayPlusSubring` (image of `A⁺` only) — this one is
   the LOCAL ring of definition itself.

2. **Upgraded localization lift** —
   `valuationLocalizationLift_of_spa_rationalOpen_locSubring`. Same
   conclusion as `valuationLocalizationLift_of_spa_rationalOpen` but
   landing in `Spa(_, locSubring)` instead of `Spa(_, image-of-A⁺)`.
   Uses `extendToLocalization_le_one_of_locSubring` (committed
   `4ce4d99`) to discharge the `locSubring`-plus-bound on the lifted
   valuation.

## Cor 7.32 application gap (single residual)

The localized Cor 7.32 application requires LOCALIZED Wedhorn-Tate
hypotheses (pseudo-uniformizer, topologically nilpotent, unit,
MulArchimedean value groups, no-common-zero on the localized Spa).
With the local plus subring `locSubring P T s` from this file, the
`A₀ ≤ B⁺` direction becomes `locSubring ≤ locSubring = le_refl`. The
remaining gap: deriving the localized Wedhorn-Tate setup from `A`'s
hypotheses (`Localization.Away.IsTateRing`-style preservation lemma).

The Cor 7.32 application target signature, with the local plus subring
in place:

```
theorem exists_dominating_unit_in_localization
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    -- Localized Wedhorn-Tate setup (the remaining gap):
    (π_loc : (locPairOfDefinition P T s hopen).A₀)
    (hI_loc : (locPairOfDefinition P T s hopen).I = Ideal.span {π_loc})
    (hπ_loc_tn : IsTopologicallyNilpotent (...subtype π_loc))
    (hπ_loc_unit : IsUnit (...subtype π_loc))
    (hArch_loc : ∀ w : Spv (Localization.Away s), MulArchimedean ...)
    (T_loc : Finset (Localization.Away s))
    (hT_loc : ∀ w ∈ Spa _ (locSubring P T s), ∃ τ ∈ T_loc, ¬ w.vle τ 0) :
    ∃ σ : (Localization.Away s)ˣ,
      ∀ w ∈ Spa _ (locSubring P T s), ∃ τ ∈ T_loc,
        w.vle (σ : Localization.Away s) τ ∧ ¬ w.vle τ (σ : Localization.Away s)
```

Proof would be a one-line application of `Cor732.exists_dominating_unit`
to `locPairOfDefinition P T s hopen` with the local plus subring; the
`A₀ ≤ B⁺` direction is `le_refl _`. The genuine difficulty is the
localized hypotheses' derivation from `A`'s setup.

## Notes

* No root import; leaf-level file.
* No edits to committed bridge files or
  `WedhornSigmaPowerDecay.lean` (Secondary).
* No Lane B / Cor 8.32 / Jacobson / T001 / faithful-flatness /
  final-acyclicity content. -/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

/-- **Local plus-subring choice using `locSubring`**.

The PlusSubring on `Localization.Away s` whose underlying subring is
the local ring of definition `locSubring P T s = A₀[t/s : t ∈ T]`. This
is the appropriate plus subring for the Wedhorn 8.34(ii) localized
σ-construction:
* `locPairOfDefinition.A₀ = locSubring`, so `A₀ ≤ B⁺` is `le_refl _`.
* `Cor732.exists_dominating_unit` becomes applicable on
  `Spa(Localization.Away s, locSubring)`.

Provided as `noncomputable def` (not `instance`) to avoid global
instance-resolution interference; consumers introduce locally via
`letI`. -/
@[reducible]
noncomputable def localizationLocSubringPlusSubring
    (P : PairOfDefinition A) (T : Finset A) (s : A) :
    PlusSubring (Localization.Away s) where
  toSubring := locSubring P T s

/-- **Upgraded rational-open lift landing in `Spa(_, locSubring)`**.

Same hypotheses as `valuationLocalizationLift_of_spa_rationalOpen`
(`hopen`, `hA₀_le : P.A₀ ≤ A⁺`, `hv_rat : v ∈ rationalOpen T s`), but
the conclusion lands in `Spa(Localization.Away s, locSubring P T s)`
instead of `Spa(_, localizationAwayPlusSubring s)`.

**Proof structure**:

1. The lift `w := localizationLift (Submonoid.powers s) (Localization.Away s) v hS`
   is continuous w.r.t. `locTopology` (from
   `localizationLift_isContinuous_locTopology_of_bounded`, committed
   `187bfe2`, after the `hν_A₀` / `hv_T` discharges from
   `WedhornSpaRationalOpenLiftWrapper`).

2. The plus-bound on `locSubring` follows from
   `extendToLocalization_le_one_of_locSubring` (committed `4ce4d99`)
   plus the definitional unfolding `(ofValuation v_ext).vle x y` =
   `v_ext x ≤ v_ext y` (used via `change`).

3. The comap identity `comap (algebraMap A _) w = v` from
   `comap_localizationLift`. -/
theorem valuationLocalizationLift_of_spa_rationalOpen_locSubring
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (hA₀_le : P.A₀ ≤ A⁺)
    {v : Spv A} (hv_rat : v ∈ rationalOpen T s) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    ∃ w : Spv (Localization.Away s),
      w ∈ @Spa (Localization.Away s) _ (locTopology P T s hopen)
        (locSubring P T s) ∧
      comap (algebraMap A (Localization.Away s)) w = v := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  obtain ⟨hv, hv_T, hvs⟩ := hv_rat
  have hS := valuationLocalizationLift_powers_subset_primeCompl hvs
  have hν_A₀ : ∀ a ∈ P.A₀, v.vle a 1 := fun a ha ↦
    vle_one_of_mem_spa hv (hA₀_le ha)
  have h_cont : (localizationLift (Submonoid.powers s) (Localization.Away s) v hS).IsContinuous :=
    localizationLift_isContinuous_locTopology_of_bounded P T s hopen
      hv.1 hv_T hS
  refine ⟨localizationLift (Submonoid.powers s) (Localization.Away s) v hS,
    ?_, comap_localizationLift _ _ v _⟩
  refine ⟨h_cont, fun f hf ↦ ?_⟩
  -- f ∈ locSubring P T s. Need (lift v).vle f 1.
  letI : ValuativeRel A := v.toValuativeRel
  set ν := ValuativeRel.valuation A with hν_def
  have hν_A₀_val : ∀ a ∈ P.A₀, ν a ≤ 1 := by
    intro a ha
    have h_eq := (Valuation.Compatible.vle_iff_le (v := ν) a 1).mp (hν_A₀ a ha)
    rw [map_one] at h_eq; exact h_eq
  have hν_T_val : ∀ t ∈ T, ν t ≤ ν s := fun t ht ↦
    (Valuation.Compatible.vle_iff_le (v := ν) t s).mp (hv_T t ht)
  have hS' : Submonoid.powers s ≤ ν.supp.primeCompl := by
    intro x hx
    change x ∉ ν.supp
    rw [← @ValuativeRel.supp_eq_valuation_supp A _ v.toValuativeRel]
    exact hS hx
  have hext_bound : (ν.extendToLocalization hS' (Localization.Away s)) f ≤ 1 :=
    extendToLocalization_le_one_of_locSubring P T s ν hν_A₀_val hν_T_val hS' hf
  -- localizationLift = ofValuation (ν.extendToLocalization). The vle on
  -- ofValuation reduces to value comparison via `change`.
  show (localizationLift (Submonoid.powers s) (Localization.Away s) v hS).vle f 1
  unfold localizationLift
  change (ν.extendToLocalization hS' (Localization.Away s)) f ≤
    (ν.extendToLocalization hS' (Localization.Away s)) 1
  rw [map_one]; exact hext_bound

end ValuationSpectrum
