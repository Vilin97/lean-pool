/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornC1PerCallSupplyHonest

/-!
# Wedhorn 8.34(ii) — Honest per-call supply assembly

Theorem-level assembly layer producing
`WedhornC1PerCallSupplyHonest` (commit `635a2c5`) from the seven
explicit per-call components: σ-strict-domination, denominator-cleared
algebraic identity, base-side rational-open membership, and the
honest σ-factored structural supplier
`WedhornMPowerStructuralDataHonest` as the only mathematical residual.

## Delegation note

`WedhornMPowerStructuralDataHonest` is the genuinely-new Wedhorn
8.34(ii) Route B per-`t'` content. **Tertiary owns the proof of this
honest structural supplier** in their structural-data lane. This file
does not prove or duplicate that residual; it consumes it as an
external hypothesis at the per-call layer.

## What this file provides

* `WedhornC1PerCallSupplyHonest_of_components` — packaging assembly:
  given the seven components (σ_loc, f, h_alg, h_dom, h_honest,
  hv_in_plus, hvf_nz), produce
  `WedhornC1PerCallSupplyHonest P C hopen_base D v`. The honest
  structural supplier `h_honest` is the only mathematical residual;
  the other six are routine Cor 7.32 / denominator-clearing /
  base-side data. Trivial existential constructor under the hood.

* `C1SupplierStrong_local_via_honest_per_call_assembly` — top-level
  caller producing `C1SupplierStrong_local C`. Composes
  `WedhornC1PerCallSupplyHonest_of_components` with the previously
  landed bridge `C1SupplierStrong_local_via_honest_residuals`
  (commit `635a2c5`). Takes a per-call function delivering the seven
  components for every `(D ∈ C.covers, v ∈ rationalOpen D.T D.s,
  t ∈ D.T)` triple, plus the standard supplier hypotheses.

## Notes

* No root import; leaf-level.
* Imports only `WedhornC1PerCallSupplyHonest` (and its transitive
  closure through `WedhornStrengthenedC1` and
  `WedhornMPowerStructuralDataHonest`). Disjoint scope from
  Tertiary's structural-data leaf.
* No edits to Primary's assembly files, Tertiary's value-group
  files, root imports, or final theorem signatures.
* No T001, Lane B, Cor 8.32, Jacobson, faithful-flatness, Zavyalov,
  or bivariate-overlap content.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **Honest per-call supply assembly — packaging from components**.

Given the seven components of the honest per-call supply
(σ_loc, f, h_alg, h_dom, h_honest, hv_in_plus, hvf_nz), package them
into the predicate `WedhornC1PerCallSupplyHonest P C hopen_base D v`.

The honest structural supplier `h_honest` is the **only mathematical
residual** (delegated to Tertiary's structural-data lane). The other
six components are routine Wedhorn 8.34(ii) per-call data:

* `σ_loc`, `h_dom` — Cor 7.32 dominating unit and σ-strict-domination
  on `Spa(Localization.Away C.base.s, locSubring P C.base.T C.base.s)`.
* `f`, `h_alg` — denominator-cleared base candidate and the algebraic
  identity `algebraMap f = σ_loc · ∏ D.T.image`.
* `hv_in_plus`, `hvf_nz` — base-side rational-open membership of `v`
  and non-degeneracy of `f` at `v`.

Trivial existential constructor under the hood. -/
theorem WedhornC1PerCallSupplyHonest_of_components
    [DecidableEq A]
    (P : PairOfDefinition A) (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (D : RationalLocData A) (v : Spv A) :
    letI : TopologicalSpace (Localization.Away C.base.s) :=
      locTopology P C.base.T C.base.s hopen_base
    letI : PlusSubring (Localization.Away C.base.s) :=
      localizationLocSubringPlusSubring P C.base.T C.base.s
    letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
    ∀ (σ_loc : (Localization.Away C.base.s)ˣ) (f : A)
      (_h_alg : algebraMap A (Localization.Away C.base.s) f =
        (σ_loc : Localization.Away C.base.s) *
          (∏ τ ∈ D.T.image (algebraMap A (Localization.Away C.base.s)), τ))
      (_h_dom : ∀ w ∈ Spa (Localization.Away C.base.s)
          (Localization.Away C.base.s)⁺,
        ∃ τ ∈ localizedTestFamily C.base.s D.T D.s,
          w.vle (σ_loc : Localization.Away C.base.s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away C.base.s))
      (_h_honest : WedhornMPowerStructuralDataHonest P C.base.T C.base.s
        hopen_base D.T D.s σ_loc)
      (_hv_in_plus : v ∈ rationalOpen (insert f C.base.T) C.base.s)
      (_hvf_nz : ¬ v.vle f 0),
      WedhornC1PerCallSupplyHonest P C hopen_base D v := by
  intro σ_loc f h_alg h_dom h_honest hv_in_plus hvf_nz
  exact ⟨σ_loc, f, h_alg, h_dom, h_honest, hv_in_plus, hvf_nz⟩

/-- **`C1SupplierStrong_local C` via honest per-call assembly**.

Top-level caller composing
`WedhornC1PerCallSupplyHonest_of_components` and
`C1SupplierStrong_local_via_honest_residuals` (commit `635a2c5`).
Inputs: a per-call function delivering the seven honest-supply
components for every `(D ∈ C.covers, v ∈ rationalOpen D.T D.s,
t ∈ D.T)` triple under the standard supplier hypotheses.

The honest structural supplier embedded in the per-call function is
the only mathematical residual; everything else composes
mechanically. -/
theorem C1SupplierStrong_local_via_honest_per_call_assembly
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (C : RationalCoveringData A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (h_per_call_components :
      letI : TopologicalSpace (Localization.Away C.base.s) :=
        locTopology P C.base.T C.base.s hopen_base
      letI : PlusSubring (Localization.Away C.base.s) :=
        localizationLocSubringPlusSubring P C.base.T C.base.s
      letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
      ∃ (σ_loc : (Localization.Away C.base.s)ˣ) (f : A),
        algebraMap A (Localization.Away C.base.s) f =
          (σ_loc : Localization.Away C.base.s) *
            (∏ τ ∈ D.T.image (algebraMap A (Localization.Away C.base.s)), τ) ∧
        (∀ w ∈ Spa (Localization.Away C.base.s)
            (Localization.Away C.base.s)⁺,
          ∃ τ ∈ localizedTestFamily C.base.s D.T D.s,
            w.vle (σ_loc : Localization.Away C.base.s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away C.base.s)) ∧
        WedhornMPowerStructuralDataHonest P C.base.T C.base.s hopen_base
          D.T D.s σ_loc ∧
        v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
        ¬ v.vle f 0) :
    C1SupplierStrong_local C := by
  refine C1SupplierStrong_local_via_honest_residuals P hA₀_le C hopen_base ?_
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨σ_loc, f, h_alg, h_dom, h_honest, hv_in_plus, hvf_nz⟩ :=
    h_per_call_components D hD v hv t ht hvt hvD_s
  exact WedhornC1PerCallSupplyHonest_of_components P C hopen_base D v
    σ_loc f h_alg h_dom h_honest hv_in_plus hvf_nz

end ValuationSpectrum
