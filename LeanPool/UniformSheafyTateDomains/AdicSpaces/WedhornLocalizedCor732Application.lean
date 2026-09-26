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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalizedCor732Bridge
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Cor732

/-!
# Localized Cor 7.32 application via the local plus-subring bridge

The one-line application of `ValuationSpectrum.exists_dominating_unit`
(`Adic spaces/Cor732.lean:206`) inside `Spa(Localization.Away s,
locSubring P T s)`, using the local plus-subring bridge from
`WedhornLocalizedCor732Bridge.lean` (commit `98928e5`).

## Why this works

With the local plus subring `localizationLocSubringPlusSubring P T s`
(underlying subring `locSubring P T s`) on `Localization.Away s`:

* `(locPairOfDefinition P T s hopen).A₀ = locSubring P T s = (Localization.Away s)⁺`,
  so the `A₀ ≤ B⁺` Cor732 hypothesis is `le_refl _`.
* The remaining Cor732 hypotheses (`π_loc`, `hI_loc`, `hπ_loc_tn`,
  `hπ_loc_unit`, `hArch_loc`, `T_loc`, `hT_loc`) are taken as
  **explicit hypotheses**: this file does NOT derive them from `A`'s
  Wedhorn-Tate hypotheses (that is the deferred Tate-preservation lane).
* `IsLinearTopology (Localization.Away s) (Localization.Away s)` is
  **NOT required**: `Cor732.exists_dominating_unit` invokes
  `instCompactSpace_spa_of_tate_pseudouniformizer` which has explicit
  `omit [IsLinearTopology A A] in`. The Cor 7.32 capstone via
  pseudo-uniformizer compactness does not need linear topology
  structure on the ambient ring.

## What this file provides

`exists_dominating_unit_in_localization` — the localized Cor 7.32
application. Single-line proof: `exact exists_dominating_unit
(locPairOfDefinition P T s hopen) (le_refl _) ...`.

## Single next residual

Deriving the localized Wedhorn-Tate hypotheses from `A`'s global Tate
setup:

* `π_loc : (locPairOfDefinition P T s hopen).A₀` and
  `hI_loc : locIdeal P T s = Ideal.span {π_loc}` — the local ideal of
  definition is principal.
* `hπ_loc_tn` — `π_loc` topologically nilpotent in
  `Localization.Away s` under `locTopology`.
* `hπ_loc_unit` — `π_loc` is a unit in `Localization.Away s`.
* `hArch_loc` — MulArchimedean value groups for points in
  `Spa(Localization.Away s, locSubring P T s)`.
* `hT_loc` — no common zero of the test family on the localized Spa.

These collectively form a `Localization.Away.IsTateRing`-style
preservation lemma, OUT OF SCOPE for this bridge. With them in hand,
this file's theorem becomes the genuine Wedhorn 8.34(ii) σ-extraction
on the localized side.

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
/-- **Localized Cor 7.32 application** through the local plus-subring
bridge (`localizationLocSubringPlusSubring`).

Applies `exists_dominating_unit` to `locPairOfDefinition P T s hopen`
with `B⁺ := locSubring P T s`. The `A₀ ≤ B⁺` direction is `le_refl _`
since `locPairOfDefinition.A₀ = locSubring`.

**All Wedhorn-Tate hypotheses on the localized side are explicit
inputs** (this file does not derive them from `A`'s setup; that is
the deferred Tate-preservation lane).

**Output**: dominating unit `σ ∈ (Localization.Away s)ˣ` strictly
dominating some test element `τ ∈ T_loc` at every point of the
localized Spa. -/
theorem exists_dominating_unit_in_localization
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    ∀ (π_loc : (locPairOfDefinition P T s hopen).A₀)
      (_hI_loc : (locPairOfDefinition P T s hopen).I = Ideal.span {π_loc})
      (_hπ_loc_tn : IsTopologicallyNilpotent
        ((locPairOfDefinition P T s hopen).A₀.subtype π_loc))
      (_hπ_loc_unit : IsUnit
        ((locPairOfDefinition P T s hopen).A₀.subtype π_loc))
      (_hArch_loc : ∀ w : Spv (Localization.Away s),
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
  haveI : IsTopologicalRing (Localization.Away s) :=
    (locBasis P T s hopen).toRingFilterBasis.isTopologicalRing
  letI : PlusSubring (Localization.Away s) := localizationLocSubringPlusSubring P T s
  intro π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_loc hT_loc
  -- locPairOfDefinition.A₀ = locSubring P T s = (Localization.Away s)⁺ by construction.
  have hA₀_le_loc : (locPairOfDefinition P T s hopen).A₀ ≤
      PlusSubring.toSubring (A := Localization.Away s) := le_refl _
  exact exists_dominating_unit (locPairOfDefinition P T s hopen) hA₀_le_loc
    π_loc hI_loc hπ_loc_tn hπ_loc_unit hArch_loc T_loc hT_loc

end ValuationSpectrum
