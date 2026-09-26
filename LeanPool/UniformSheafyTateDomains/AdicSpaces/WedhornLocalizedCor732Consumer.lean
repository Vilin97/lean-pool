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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalizedCor732Application
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalizedTateData

/-!
# Localized Cor 7.32 consumer wrapper

The localized Cor 7.32 application
(`exists_dominating_unit_in_localization`, commit `9b43844`) takes
five localized hypotheses (`π_loc`, `hI_loc`, `hπ_loc_tn`,
`hπ_loc_unit`, `hArch_loc`, `T_loc`, `hT_loc`). The first three are
derivable from global pair-of-definition data via
`WedhornLocalizedTateData` (commit `21b0a3e`). This file packages the
chain: takes only the GLOBAL pseudo-uniformizer data plus the genuine
remaining external hypotheses, produces the localized σ-domination
output.

## What this file provides

`exists_dominating_unit_in_localization_via_global_pi` — consumer
wrapper. Inputs:

* Global pseudo-uniformizer `π : P.A₀` with `P.I = Ideal.span {π}`,
  `IsTopologicallyNilpotent (P.A₀.subtype π)`, `IsUnit (P.A₀.subtype π)`.
* Localization data `(T : Finset A) (s : A) (hopen : ...)`.
* Genuine remaining external hypotheses: `hArch_loc` (MulArchimedean
  on Spv localized), `T_loc` (test family on `Localization.Away s`),
  `hT_loc` (no common zero of `T_loc` on localized Spa).

Output: dominating unit `σ ∈ (Localization.Away s)ˣ` on the localized
Spa.

## Notes

* No root import; leaf-level file.
* No edits to committed bridge files.
* No Lane B / Cor 8.32 / Jacobson / T001 / faithful-flatness /
  final-acyclicity content. -/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

omit [PlusSubring A] in
/-- **Localized Cor 7.32 consumer wrapper**.

Discharges three of the five Wedhorn-Tate hypotheses to
`exists_dominating_unit_in_localization` from global pair-of-definition
data:

* `π_loc := algebraMapD P T s π`.
* `hI_loc` from `locIdeal_eq_span_singleton_of_principal` + `hI`.
* `hπ_loc_tn` from `isTopologicallyNilpotent_algebraMapD_of_isTopologicallyNilpotent`
  + `hπ_tn`.
* `hπ_loc_unit` from `isUnit_algebraMapD_of_isUnit` + `hπ_unit`.

Remaining external inputs (the genuine residuals): `hArch_loc`, `T_loc`,
`hT_loc`. -/
theorem exists_dominating_unit_in_localization_via_global_pi
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π)) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    ∀ (_hArch_loc : ∀ w : Spv (Localization.Away s),
        letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero (Localization.Away s)))
      (T_loc : Finset (Localization.Away s))
      (_hT_loc : ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ T_loc, ¬ w.vle τ 0),
      ∃ σ : (Localization.Away s)ˣ,
        ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
          ∃ τ ∈ T_loc, w.vle (σ : Localization.Away s) τ ∧
            ¬ w.vle τ (σ : Localization.Away s) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  intro hArch_loc T_loc hT_loc
  set π_loc := algebraMapD P T s π with hπ_loc_def
  have hI_loc :
      (locPairOfDefinition P T s hopen).I = Ideal.span {π_loc} :=
    locIdeal_eq_span_singleton_of_principal P T s hopen π hI
  have hπ_loc_tn :
      IsTopologicallyNilpotent
        ((locPairOfDefinition P T s hopen).A₀.subtype π_loc) :=
    isTopologicallyNilpotent_algebraMapD_of_isTopologicallyNilpotent P T s hopen π hπ_tn
  have hπ_loc_unit :
      IsUnit ((locPairOfDefinition P T s hopen).A₀.subtype π_loc) :=
    isUnit_algebraMapD_of_isUnit P T s hopen π hπ_unit
  exact exists_dominating_unit_in_localization P T s hopen
    π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_loc hT_loc

end ValuationSpectrum
