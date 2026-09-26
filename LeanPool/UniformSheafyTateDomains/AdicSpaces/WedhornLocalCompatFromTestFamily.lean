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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalPerBranchChain
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalizedCor732Application
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornMultiDominatingUnit
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornStandardCoverRefinement

/-!
# Wedhorn local-compatibility from canonical test family

Defines the canonical localized Wedhorn 8.34(ii) test family
`T_test_loc := insert (algebraMap s_D) (T_D.image algebraMap)` on
`Localization.Away s` and lands the per-branch compatibility theorems
needed to consume `rationalOpen_subset_base_via_local_Cor732_chain`
(commit `4197d87`).

## Strategy

The Wedhorn 8.34(ii) σ-construction uses a finite test family
`T_test_loc` on the localized Spa. The natural canonical choice is

`T_test_loc := insert (algebraMap s_D) (T_D.image algebraMap)`

— the image of `T_D` plus the `algebraMap` of the cover-piece
denominator `s_D`. With this choice, the σ-strict-domination output of
`exists_dominating_unit_in_localization` (commit accepted upstream)
gives, at every `w ∈ Spa(A_loc, locSubring)`:

* either `τ = algebraMap s_D` (the **`α_s_D` branch**),
* or `τ ∈ T_D.image algebraMap` (the **`α_T_D` branches**).

The `¬ w.vle (algebraMap s_D) 0` half of the per-branch conclusion
**discharges automatically** in the `α_s_D` branch via
`not_vle_zero_of_strict_dominator` (`WedhornMultiDominatingUnit.lean:189`).
For the `α_T_D` branches, both halves are taken as explicit inputs;
that is the genuine Wedhorn-content residual at this lane.

## What this file provides

* `localizedTestFamily` — the canonical test family
  `insert (algebraMap s_D) (T_D.image algebraMap)` on
  `Localization.Away s`.

* `h_T_test_compat_loc_branch_α_s_D` — single-branch compatibility for
  `τ = algebraMap s_D`. The `¬ w.vle (algebraMap s_D) 0` half is
  automatic; the per-`t'` half is the explicit input.

* `h_T_test_compat_loc_branch_α_T_D` — single-branch compatibility for
  `τ ∈ T_D.image algebraMap`. Both per-`t'` and `¬ w.vle (algebraMap s_D) 0`
  halves are explicit inputs.

* `h_T_test_compat_loc_canonical` — combined compatibility for the
  canonical test family `localizedTestFamily`, dispatching on the
  branch via `Finset.mem_insert`.

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness / Zavyalov / bivariate-overlap content.
* Reuses `not_vle_zero_of_strict_dominator`
  (`WedhornMultiDominatingUnit.lean:189`).
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

/-- **Canonical localized test family for Wedhorn 8.34(ii)**:
`insert (algebraMap s_D) (T_D.image algebraMap)` on `Localization.Away s`.

The natural test family for the σ-construction at the localization:
contains the `algebraMap`-image of every `t ∈ T_D` (for the test family's
"main" branch) plus `algebraMap s_D` (for the cover-piece-denominator
branch). Used as `T_test_loc` in
`rationalOpen_subset_base_via_local_Cor732_chain`. -/
noncomputable def localizedTestFamily
    (s : A) (T_D : Finset A) (s_D : A) : Finset (Localization.Away s) :=
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  insert (algebraMap A (Localization.Away s) s_D)
    (T_D.image (algebraMap A (Localization.Away s)))

omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] in
/-- Membership lemma for `localizedTestFamily`: an element belongs
either via the `algebraMap s_D` slot or via `T_D.image`. -/
theorem mem_localizedTestFamily_iff
    (s : A) (T_D : Finset A) (s_D : A) (x : Localization.Away s) :
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    x ∈ localizedTestFamily s T_D s_D ↔
      x = algebraMap A (Localization.Away s) s_D ∨
      x ∈ T_D.image (algebraMap A (Localization.Away s)) := by
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  unfold localizedTestFamily
  exact Finset.mem_insert

omit [PlusSubring A] in
/-- **Single-branch compatibility for `τ = algebraMap s_D`**.

The `¬ w.vle (algebraMap s_D) 0` half is **discharged automatically**
via `not_vle_zero_of_strict_dominator`: strict σ-domination of
`algebraMap s_D` (i.e., `¬ w.vle (algebraMap s_D) (σ_loc : _)`) implies
`¬ w.vle (algebraMap s_D) 0`. The per-`t'` half is the explicit
Wedhorn-content residual at this branch. -/
theorem h_T_test_compat_loc_branch_α_s_D
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_per_t_chain :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s)
            (algebraMap A (Localization.Away s) s_D) ∧
          ¬ w.vle (algebraMap A (Localization.Away s) s_D)
            (σ_loc : Localization.Away s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle t' (algebraMap A (Localization.Away s) s_D)) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w.vle ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
        (algebraMap A (Localization.Away s) s) →
      w.vle (σ_loc : Localization.Away s)
          (algebraMap A (Localization.Away s) s_D) ∧
        ¬ w.vle (algebraMap A (Localization.Away s) s_D)
          (σ_loc : Localization.Away s) →
        (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
            w.vle t' (algebraMap A (Localization.Away s) s_D)) ∧
          ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa hw_f hστ
  exact ⟨h_per_t_chain w hw_spa hw_f hστ,
    not_vle_zero_of_strict_dominator hστ.2⟩

omit [PlusSubring A] in
/-- **Single-branch compatibility for `τ ∈ T_D.image algebraMap`**.

For the `α_T_D` branches, both per-`t'` and `¬ w.vle (algebraMap s_D) 0`
halves are taken as explicit inputs; neither is automatic from
σ-strict-domination at this τ alone. -/
theorem h_T_test_compat_loc_branch_α_T_D
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_per_t_chain :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
        ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
          w.vle ((σ_loc : Localization.Away s) *
              (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
            (algebraMap A (Localization.Away s) s) →
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s) →
          ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
            w.vle t' (algebraMap A (Localization.Away s) s_D))
    (h_per_α_T_D_s_D_ne :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
        ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
          w.vle ((σ_loc : Localization.Away s) *
              (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
            (algebraMap A (Localization.Away s) s) →
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s) →
          ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
          (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
              w.vle t' (algebraMap A (Localization.Away s) s_D)) ∧
            ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro τ hτ w hw_spa hw_f hστ
  exact ⟨h_per_t_chain τ hτ w hw_spa hw_f hστ,
    h_per_α_T_D_s_D_ne τ hτ w hw_spa hw_f hστ⟩

omit [PlusSubring A] in
/-- **Combined canonical compatibility theorem** — composes the two
branch compatibility theorems above to produce a `h_T_test_compat_loc`
witness for the canonical test family `localizedTestFamily s T_D s_D`,
ready for direct consumption by
`rationalOpen_subset_base_via_local_Cor732_chain`.

The per-branch chain hypotheses are split: one for the `α_s_D` branch
(per-`t'` only — `¬ w.vle (algebraMap s_D) 0` is automatic), and two
for the `α_T_D` branches (per-`t'` and explicit `¬ w.vle (algebraMap s_D) 0`).
This is the cleanest factoring honoring the strict-domination
auto-discharge available only at the `α_s_D` branch. -/
theorem h_T_test_compat_loc_canonical
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_α_s_D_per_t :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s)
            (algebraMap A (Localization.Away s) s_D) ∧
          ¬ w.vle (algebraMap A (Localization.Away s) s_D)
            (σ_loc : Localization.Away s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle t' (algebraMap A (Localization.Away s) s_D))
    (h_α_T_D_per_t :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
        ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
          w.vle ((σ_loc : Localization.Away s) *
              (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
            (algebraMap A (Localization.Away s) s) →
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s) →
          ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
            w.vle t' (algebraMap A (Localization.Away s) s_D))
    (h_α_T_D_s_D_ne :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
        ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
          w.vle ((σ_loc : Localization.Away s) *
              (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
            (algebraMap A (Localization.Away s) s) →
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s) →
          ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ τ ∈ localizedTestFamily s T_D s_D,
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
          (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
              w.vle t' (algebraMap A (Localization.Away s) s_D)) ∧
            ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro τ hτ w hw_spa hw_f hστ
  rw [mem_localizedTestFamily_iff] at hτ
  rcases hτ with rfl | hτ_in_T_D
  · -- Branch α_s_D.
    exact ⟨h_α_s_D_per_t w hw_spa hw_f hστ,
      not_vle_zero_of_strict_dominator hστ.2⟩
  · -- Branch α_T_D.
    exact ⟨h_α_T_D_per_t τ hτ_in_T_D w hw_spa hw_f hστ,
      h_α_T_D_s_D_ne τ hτ_in_T_D w hw_spa hw_f hστ⟩

omit [PlusSubring A] in
/-- **T168: `h_α_T_D_s_D_ne` supplier via Cor 7.32 σ-strict-dom branch
splitting + the corrected multi-dominating-unit inequality**.

Produces the α_T_D branch s_D non-vanishing supplier consumed by
`h_T_test_compat_loc_canonical` (third parameter, line 261) and
`h_T_test_compat_loc_branch_α_T_D` (second parameter), using the
**corrected branch-clearing route** (Wedhorn 8.34(ii) Route B, PDF
page 84) — combining:

* **Cor 7.32 σ-strict-domination branch splitting** via
  `not_vle_zero_of_strict_dominator` applied to `hστ.2`: at the α_T_D
  branch (τ ∈ T_D.image), σ-strict-dom hands `¬ w.vle τ 0`.

* **Multi-dominating-unit inequality** via
  `vle_of_dominating_unit_multi_corrected_at` (in
  `WedhornDominatingUnitInequality.lean`): from a multi-element bound
  `w.vle (∏ T_D.image) (algebraMap s_D)` and a per-element lower bound
  `∀ t' ∈ T_D.image, w.vle 1 t'`, the first conjunct yields the per-`t'`
  upper bound `∀ t' ∈ T_D.image, w.vle t' (algebraMap s_D)`. Specialised
  at the σ-strict-dom witness `τ ∈ T_D.image` together with `¬ w.vle τ 0`,
  transitivity through `w.vle (algebraMap s_D) 0` produces a contradiction
  — yielding `¬ w.vle (algebraMap s_D) 0`.

Replaces the previously-attempted T021/T023 σ-power-decay residual
(`AlphaT_DBranchPerTSigmaPowerDecay`, parked at commit `1cdea0d`): T023
showed the σ-power-decay shape is mathematically false uniformly on Spa
(`vle_of_dominating_unit_multi` counter-example documented in
`WedhornDominatingUnitInequality.lean`); the corrected approach uses the
multi-element bound + per-element lower bound, which is exactly the
data naturally available in the cover plus-piece via Wedhorn's Laurent
cover refinement.

Hypotheses match the existing per-w consumer pattern: f-membership and
σ-strict-dom-by-τ both available at `w`, plus the corrected-route
suppliers for the multi-element bound and per-element lower bound at
`w`. -/
theorem h_α_T_D_s_D_ne_via_multi_corrected
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_T_D_multi_bound :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)
              (algebraMap A (Localization.Away s) s_D))
    (h_T_D_lower_bound :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle (1 : Localization.Away s) t') :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
        ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro τ hτ w hw_spa hw_f hστ
  -- Cor 7.32 σ-strict-dom branch splitting at τ ∈ T_D.image: τ is
  -- non-vanishing at w (via `not_vle_zero_of_strict_dominator` from `hστ.2`).
  have h_τ_ne : ¬ w.vle τ 0 := not_vle_zero_of_strict_dominator hστ.2
  -- Corrected multi-dominating-unit inequality's first conjunct: per-`t'`
  -- upper bound by `algebraMap s_D` (using the multi-element bound +
  -- per-element lower bound at this `w`).
  have h_per_t' :
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle t' (algebraMap A (Localization.Away s) s_D) :=
    (vle_of_dominating_unit_multi_corrected_at w
      (h_T_D_multi_bound w hw_spa hw_f)
      (h_T_D_lower_bound w hw_spa hw_f)).1
  -- Specialize the per-t' upper bound at the σ-strict-dom witness τ.
  have h_τ_le_s_D :
      w.vle τ (algebraMap A (Localization.Away s) s_D) :=
    h_per_t' τ hτ
  -- Combine via transitivity: if `w.vle (algebraMap s_D) 0` then
  -- `w.vle τ 0`, contradicting `h_τ_ne`.
  intro h_s_D_zero
  exact h_τ_ne (w.vle_trans h_τ_le_s_D h_s_D_zero)

omit [PlusSubring A] in
/-- **T168: `h_α_T_D_per_t` supplier via the corrected multi-dominating-unit
inequality**.

Companion to `h_α_T_D_s_D_ne_via_multi_corrected` above: produces the
α_T_D branch per-`t'` upper-bound supplier consumed by
`h_T_test_compat_loc_canonical` (second parameter, line 247) and
`h_T_test_compat_loc_branch_α_T_D` (first parameter), using the same
**corrected branch-clearing route** as the s_D-nonvanishing branch.

The conclusion `∀ t' ∈ T_D.image, w.vle t' (algebraMap s_D)` is exactly
the **first conjunct** of `vle_of_dominating_unit_multi_corrected_at`
applied to the multi-element bound + per-element lower bound at `w`.
The σ-strict-dom-by-τ premise is **not used** in the proof: the
per-`t'` upper bound is uniform over `T_D.image`, independent of which
τ ∈ T_D.image won σ-domination at `w`.

Hypotheses match `h_α_T_D_s_D_ne_via_multi_corrected` exactly: the
multi-element bound and per-element lower bound at each `w` in the
cover plus-piece (under f-membership). This shared hypothesis shape is
the natural interface for the corrected-route producers, so a single
pair `(h_T_D_multi_bound, h_T_D_lower_bound)` discharges both α_T_D
branch suppliers consumed by `h_T_test_compat_loc_branch_α_T_D`. -/
theorem h_α_T_D_per_t_via_multi_corrected
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_T_D_multi_bound :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)
              (algebraMap A (Localization.Away s) s_D))
    (h_T_D_lower_bound :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle (1 : Localization.Away s) t') :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle t' (algebraMap A (Localization.Away s) s_D) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro _τ _hτ w hw_spa hw_f _hστ
  -- First conjunct of vle_of_dominating_unit_multi_corrected_at.
  exact (vle_of_dominating_unit_multi_corrected_at w
    (h_T_D_multi_bound w hw_spa hw_f)
    (h_T_D_lower_bound w hw_spa hw_f)).1

omit [PlusSubring A] in
/-- **T168: α_T_D branch closed via the corrected multi-dominating-unit
inequality**.

Reusable theorem packaging the α_T_D branch single-branch compatibility
output by feeding the two corrected-route suppliers
(`h_α_T_D_per_t_via_multi_corrected` and
`h_α_T_D_s_D_ne_via_multi_corrected`) into
`h_T_test_compat_loc_branch_α_T_D`. The α_T_D branch is now closed
**modulo the corrected-route hypotheses** (multi-element bound +
per-element lower bound at each `w` in the cover plus-piece, under
f-membership).

After this lemma, the remaining content for the α_T_D branch is the
**Laurent cover refinement producer** for `h_T_D_multi_bound` and
`h_T_D_lower_bound` — Wedhorn's actual cover-piece data on
`V_{D_s} = {w | ∀ t ∈ insert D_s T_D, w.vle t D_s}` (PDF page 84 /
Lemma 8.33). That producer is the genuine remaining T168 content; this
branch closure makes it the **single** open input. -/
theorem h_T_test_compat_loc_branch_α_T_D_via_multi_corrected
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_T_D_multi_bound :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)
              (algebraMap A (Localization.Away s) s_D))
    (h_T_D_lower_bound :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle (1 : Localization.Away s) t') :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
          (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
              w.vle t' (algebraMap A (Localization.Away s) s_D)) ∧
            ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 :=
  h_T_test_compat_loc_branch_α_T_D P T s hopen T_D s_D σ_loc
    (h_α_T_D_per_t_via_multi_corrected P T s hopen T_D s_D σ_loc
      h_T_D_multi_bound h_T_D_lower_bound)
    (h_α_T_D_s_D_ne_via_multi_corrected P T s hopen T_D s_D σ_loc
      h_T_D_multi_bound h_T_D_lower_bound)

omit [PlusSubring A] in
/-- **T168: localized Laurent-piece producer for the corrected-route
suppliers** `h_T_D_multi_bound` and `h_T_D_lower_bound`.

Localized analogue of T051's `T050_supplier_via_laurent_piece_membership`
(in `WedhornLaurentProductBoundSupplier.lean`), specialised at
`A := Localization.Away s` with the localized topology / plus-subring
instances. From per-`w` Laurent-piece rationalOpen data on
`Spa(Loc s, ⁺)`:

* `w ∈ rationalOpen ({∏ T_D.image (algebraMap)} : Finset (Loc s))
    (algebraMap s_D)` — singleton-product upper bound at `α s_D`;
* `∀ t' ∈ T_D.image (algebraMap), w ∈ rationalOpen ({(1 : Loc s)})
    t'` — per-element lower bound at `1`,

derive the corrected-route hypothesis pair consumed by
`h_α_T_D_per_t_via_multi_corrected` and
`h_α_T_D_s_D_ne_via_multi_corrected`:

```
w.vle (∏ T_D.image (algebraMap)) (algebraMap s_D) ∧
∀ t' ∈ T_D.image (algebraMap), w.vle (1 : Loc s) t'
```

**Proof**: at each `w` satisfying f-membership, extract the supplied
Laurent-piece data; the multi-element bound and per-element lower bound
follow from the singleton-element rationalOpen membership conjunct
(`v.vle t s` for the singleton `t`).

This is the **localized analogue** of the natural Wedhorn 8.34(ii)
Laurent-cover-refinement output at the base side (PDF page 84 /
Lemma 8.33), expressed in localized rationalOpen vocabulary and
matching the `h_T_D_multi_bound` / `h_T_D_lower_bound` interface
exactly.

After this producer, the **single open input** for the α_T_D branch
closure is the per-`w` localized Laurent-piece rationalOpen data —
paralleling `localized_cor732_laurent_piece_membership_at` (in
`WedhornLocalCor732ToFactoredChain.lean`) for the σ-strict-domination
output. -/
theorem T_D_multi_and_lower_bound_via_localized_laurent_piece
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_per_w_laurent_piece :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w ∈ rationalOpen
            ({∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t}
              : Finset (Localization.Away s))
            (algebraMap A (Localization.Away s) s_D) ∧
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w ∈ rationalOpen
            ({(1 : Localization.Away s)} : Finset (Localization.Away s)) t') :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w.vle ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
        (algebraMap A (Localization.Away s) s) →
        w.vle (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)
              (algebraMap A (Localization.Away s) s_D) ∧
        (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle (1 : Localization.Away s) t') := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa hw_f
  obtain ⟨h_prod_open, h_per_t_open⟩ :=
    h_per_w_laurent_piece w hw_spa hw_f
  refine ⟨?_, ?_⟩
  · -- Multi-element bound: extract from singleton-product rationalOpen.
    obtain ⟨_hw_spa', h_bound, _h_α_s_D_ne⟩ := h_prod_open
    exact h_bound _ (Finset.mem_singleton.mpr rfl)
  · -- Per-element lower bound: extract from each per-element rationalOpen.
    intro t' ht'
    obtain ⟨_hw_spa', h_bound, _h_t'_ne⟩ := h_per_t_open t' ht'
    exact h_bound _ (Finset.mem_singleton.mpr rfl)

omit [PlusSubring A] in
/-- **T168: end-to-end α_T_D branch closure from localized Laurent-piece
data**.

Composes the localized Laurent-piece producer
`T_D_multi_and_lower_bound_via_localized_laurent_piece` with the α_T_D
branch closer `h_T_test_compat_loc_branch_α_T_D_via_multi_corrected`
to produce the α_T_D branch's full single-branch compatibility output
directly from per-`w` localized Laurent-piece rationalOpen data.

This is the **end-to-end α_T_D branch theorem** for the corrected
branch-clearing route: the only remaining input is the natural Wedhorn
8.34(ii) Laurent-cover-refinement output at the localized base side,
which parallels `localized_cor732_laurent_piece_membership_at` for the
σ-strict-domination output.

After this theorem, the T168 α_T_D branch is closed modulo a single
named per-`w` localized Laurent-piece rationalOpen data hypothesis —
the natural Wedhorn 8.34(ii) PDF page 84 / Lemma 8.33 Laurent-piece
output expressed in localized rationalOpen vocabulary. -/
theorem h_T_test_compat_loc_branch_α_T_D_via_localized_laurent_piece
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_per_w_laurent_piece :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w ∈ rationalOpen
            ({∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t}
              : Finset (Localization.Away s))
            (algebraMap A (Localization.Away s) s_D) ∧
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w ∈ rationalOpen
            ({(1 : Localization.Away s)} : Finset (Localization.Away s)) t') :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
          (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
              w.vle t' (algebraMap A (Localization.Away s) s_D)) ∧
            ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  -- Extract the corrected-route hypothesis pair from Laurent-piece data.
  have h_pair :=
    T_D_multi_and_lower_bound_via_localized_laurent_piece P T s hopen
      T_D s_D σ_loc h_per_w_laurent_piece
  -- Feed the two halves into h_T_test_compat_loc_branch_α_T_D_via_multi_corrected.
  exact h_T_test_compat_loc_branch_α_T_D_via_multi_corrected P T s hopen
    T_D s_D σ_loc
    (fun w hw_spa hw_f ↦ (h_pair w hw_spa hw_f).1)
    (fun w hw_spa hw_f ↦ (h_pair w hw_spa hw_f).2)

omit [PlusSubring A] in
/-- **T169: localized Laurent-piece rationalOpen producer**
(`h_per_w_laurent_piece_target`).

Produces the per-`w` localized Laurent-piece rationalOpen data consumed
by `h_T_test_compat_loc_branch_α_T_D_via_localized_laurent_piece` (and
its underlying `T_D_multi_and_lower_bound_via_localized_laurent_piece`)
from the **natural Wedhorn 8.34(ii) Laurent cover refinement output at
the localized level**: the pair

* `h_T_D_multi_bound` — multi-element bound at `α s_D`:
  `w.vle (∏ T_D.image (algebraMap)) (algebraMap s_D)` per `w` under
  f-membership;
* `h_T_D_lower_bound` — per-element lower bound at `1`:
  `∀ t' ∈ T_D.image (algebraMap), w.vle 1 t'` per `w` under
  f-membership.

These are the same two hypotheses consumed by the corrected-route
α_T_D-branch suppliers `h_α_T_D_per_t_via_multi_corrected` /
`h_α_T_D_s_D_ne_via_multi_corrected` (from T168 commits `8316474` /
`d954344`). Wedhorn's actual cover-refinement (PDF page 84 / Lemma 8.33)
produces exactly this pair on each Laurent piece by construction; this
producer **packages** it into the rationalOpen vocabulary used by the
downstream T168 caller.

The rationalOpen non-vanishing clauses follow:

* `¬ w.vle (algebraMap s_D) 0` — the second conjunct of
  `vle_of_dominating_unit_multi_corrected_at` (in
  `WedhornDominatingUnitInequality.lean`), derived from
  `h_T_D_multi_bound + h_T_D_lower_bound` via the chain
  `1 ≤ (∏ T_D.image) ≤ algebraMap s_D` plus `not_vle_one_zero`.

* `¬ w.vle t' 0` for each `t' ∈ T_D.image (algebraMap)` — derived from
  `h_T_D_lower_bound` via the chain `1 ≤ t'` (under `w.vle 1 t'`) plus
  `not_vle_one_zero` and transitivity.

This is the **inverse direction** of T168's
`T_D_multi_and_lower_bound_via_localized_laurent_piece`: that lemma
unwraps the rationalOpen form into multi+lower bounds; this lemma
wraps multi+lower bounds back into the rationalOpen form. Both
directions are honest Wedhorn 8.34(ii) packaging, with no σ-power-decay,
locSubring integrality, or product-from-per-t bound. -/
theorem h_per_w_laurent_piece_target
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_T_D_multi_bound :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)
              (algebraMap A (Localization.Away s) s_D))
    (h_T_D_lower_bound :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle (1 : Localization.Away s) t') :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w.vle ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
        (algebraMap A (Localization.Away s) s) →
      w ∈ rationalOpen
          ({∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t}
            : Finset (Localization.Away s))
          (algebraMap A (Localization.Away s) s_D) ∧
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w ∈ rationalOpen
            ({(1 : Localization.Away s)} : Finset (Localization.Away s)) t' := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa hw_f
  have h_prod := h_T_D_multi_bound w hw_spa hw_f
  have h_lower := h_T_D_lower_bound w hw_spa hw_f
  -- s_D non-vanishing: second conjunct of vle_of_dominating_unit_multi_corrected_at.
  have h_s_D_ne : ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 :=
    (vle_of_dominating_unit_multi_corrected_at w h_prod h_lower).2
  refine ⟨⟨hw_spa, ?_, h_s_D_ne⟩, ?_⟩
  · -- Singleton-product upper bound: w.vle (∏ T_D.image) (algebraMap s_D).
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact h_prod
  · -- Per-element lower bound + non-vanishing for each t' ∈ T_D.image.
    intro t' ht'
    refine ⟨hw_spa, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      exact h_lower t' ht'
    · -- ¬ w.vle t' 0: from w.vle 1 t' + not_vle_one_zero.
      intro h_t'_zero
      have h_one_zero : w.vle (1 : Localization.Away s) 0 :=
        w.vle_trans (h_lower t' ht') h_t'_zero
      exact w.not_vle_one_zero h_one_zero

omit [PlusSubring A] in
/-- **T169 caller: end-to-end α_T_D branch closure from
multi+lower bounds**.

Composes T169's `h_per_w_laurent_piece_target` with T168's
`h_T_test_compat_loc_branch_α_T_D_via_localized_laurent_piece` to give
the α_T_D branch's full single-branch compatibility output directly
from the per-`w` multi-element bound + per-element lower bound
hypotheses. This shows T169's producer feeds the T168 caller as
intended.

After this caller, the α_T_D branch closure consumes only the natural
Wedhorn 8.34(ii) Laurent cover refinement output (the multi-element
bound + per-element lower bound at each `w` in the cover plus-piece);
no further rationalOpen-shape conversion is needed downstream. -/
theorem h_T_test_compat_loc_branch_α_T_D_via_multi_lower
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_T_D_multi_bound :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)
              (algebraMap A (Localization.Away s) s_D))
    (h_T_D_lower_bound :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle (1 : Localization.Away s) t') :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
          (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
              w.vle t' (algebraMap A (Localization.Away s) s_D)) ∧
            ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 :=
  h_T_test_compat_loc_branch_α_T_D_via_localized_laurent_piece P T s hopen
    T_D s_D σ_loc
    (h_per_w_laurent_piece_target P T s hopen T_D s_D σ_loc
      h_T_D_multi_bound h_T_D_lower_bound)

omit [PlusSubring A] in
/-- **T169 (continued): localized Wedhorn 8.34(ii) Laurent cover-refinement
producer for the multi+lower pair**.

Honest cover-decomposition theorem: from
1. **Cor 7.32 σ-strict-domination** over `localizedTestFamily s T_D s_D`
   (the standard `exists_dominating_unit_in_localization` output), and
2. **Per-Laurent-piece structural data**: at each
   `τ ∈ localizedTestFamily s T_D s_D` and each
   `w ∈ Spa (Loc s) (Loc s)⁺` lying in the σ_loc-rescaled Laurent piece
   `rationalOpen ({1}) (σ_loc⁻¹ · τ)` under f-membership, the
   multi-element bound `w.vle (∏ T_D.image) (α s_D)` and per-element
   lower bound `∀ t' ∈ T_D.image, w.vle 1 t'` hold,

derive the **global** multi+lower pair:

* `h_T_D_multi_bound`: `∀ w ∈ Spa, w.vle (σ_loc · ∏ T_D.image) (α s) →
  w.vle (∏ T_D.image) (α s_D)`,
* `h_T_D_lower_bound`: `∀ w ∈ Spa, w.vle (σ_loc · ∏ T_D.image) (α s) →
  ∀ t' ∈ T_D.image, w.vle 1 t'`.

**Proof** (cover decomposition): at any `w ∈ Spa` under f-membership,
`localized_cor732_laurent_piece_membership_at` (commit `4197d87`,
`WedhornLocalCor732ToFactoredChain.lean`) supplies a Laurent-piece
membership: `∃ τ ∈ localizedTestFamily, w ∈ rationalOpen ({1}) (σ_loc⁻¹ · τ)`.
Apply the per-piece structural hypothesis `h_per_piece_multi_lower` at
that `τ` to extract the multi+lower bound at `w`. The cover-decomposition
glues per-piece bounds into global bounds via the Laurent cover.

**Why this is honest cover-refinement content**: the per-piece structural
hypothesis is **strictly piece-restricted** — it asks for the multi+lower
bound only on each Laurent piece V_τ (which is geometrically smaller
than `Spa`), not globally. The cover {V_τ}_τ is the natural Wedhorn
8.34(ii) Laurent cover refinement (PDF page 84 / Lemma 8.33), and the
producer captures the cover-decomposition step of Wedhorn's proof.

**First exact obstruction (per-piece arithmetic, not discharged here)**:
on each piece V_τ for τ ∈ localizedTestFamily, deriving multi+lower
from the available data (V_τ membership = `w.vle σ_loc τ`, f-membership
= `w.vle (σ_loc · ∏ T_D.image) (α s)`, σ-strict-domination at τ) requires
**Wedhorn 8.34(ii) per-piece arithmetic** that the project does not
yet supply:

* For τ = `algebraMap s_D` (V_{α s_D} piece): `w.vle σ_loc (α s_D)` plus
  f-membership does NOT directly imply `w.vle (∏ T_D.image) (α s_D)`
  — that would require a relation like `α s ≤ σ_loc · α s_D`, the
  converse of σ_loc ≤ α s_D, which is not free.

* For τ ∈ T_D.image (V_τ piece, K-nonempty case): `w.vle σ_loc τ` plus
  f-membership does NOT directly imply `w.vle (∏ T_D.image) (α s_D)` —
  T168 (`vle_of_dominating_unit_multi`) documented this implication is
  false in general; the V_K-nonempty residual
  (`WedhornCoverPieceVKAlphaTDMaxBound`) only delivers per-element
  upper bounds, not the multi-element bound.

The genuine remaining content is therefore a per-piece arithmetic lemma
relating `w.vle σ_loc τ` (for each τ case) to the multi-element bound
under additional cover-refinement structural data (e.g., a specific
factorization of `algebraMap s` through `σ_loc · α s_D · ∏ T_D.image`,
matching Wedhorn's cover-refinement element construction). Producing
this per-piece arithmetic from the project's existing API is the next
theorem-sized step beyond T169.

**Use**: apply this theorem with the σ-strict-dom output and per-piece
structural data to produce `(h_T_D_multi_bound, h_T_D_lower_bound)`,
then feed the pair to `h_per_w_laurent_piece_target` (commit `f4f3b70`)
to obtain the per-`w` localized Laurent-piece rationalOpen data
consumed by `h_T_test_compat_loc_branch_α_T_D_via_localized_laurent_piece`. -/
theorem h_T_D_multi_and_lower_bound_via_laurent_cover_refinement
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (hσ_loc_dom :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s))
    (h_per_piece_multi_lower :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ τ ∈ localizedTestFamily s T_D s_D,
        ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
          w ∈ rationalOpen
              ({(1 : Localization.Away s)} : Finset (Localization.Away s))
              (((σ_loc⁻¹ : (Localization.Away s)ˣ) : Localization.Away s) *
                τ) →
          w.vle ((σ_loc : Localization.Away s) *
              (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
            (algebraMap A (Localization.Away s) s) →
          w.vle (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)
                (algebraMap A (Localization.Away s) s_D) ∧
          (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
              w.vle (1 : Localization.Away s) t')) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    (∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)
              (algebraMap A (Localization.Away s) s_D)) ∧
    (∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle (1 : Localization.Away s) t') := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  -- Common per-`w` cover-refinement step: dispatch to the Laurent piece
  -- containing `w`, then apply the per-piece hypothesis.
  have h_at_w : ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w.vle ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
        (algebraMap A (Localization.Away s) s) →
      w.vle (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)
            (algebraMap A (Localization.Away s) s_D) ∧
      (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle (1 : Localization.Away s) t') := by
    intro w hw_spa hw_f
    -- Specialize the general `cor732_laurent_piece_membership_at`
    -- (in `WedhornStandardCoverRefinement.lean`) at
    -- `A := Localization.Away s` and `T := localizedTestFamily s T_D s_D`.
    obtain ⟨τ, hτ, hw_piece⟩ :=
      cor732_laurent_piece_membership_at hσ_loc_dom hw_spa
    exact h_per_piece_multi_lower τ hτ w hw_spa hw_piece hw_f
  refine ⟨?_, ?_⟩
  · intro w hw_spa hw_f
    exact (h_at_w w hw_spa hw_f).1
  · intro w hw_spa hw_f t' ht'
    exact (h_at_w w hw_spa hw_f).2 t' ht'

omit [PlusSubring A] in
/-- **T170: case-wise multi-element bound from cover-refinement
factorization** (multi half of `h_per_piece_multi_lower`).

**Honest case-wise arithmetic theorem** discharging the multi-element
bound clause of T169's `h_per_piece_multi_lower` from two **non-generic
structural hypotheses**:

1. **Cover-refinement element factorization (Wedhorn 8.34(ii) / Lemma
   8.33)**:
   ```
   algebraMap A (Localization.Away s) s =
     (σ_loc : Localization.Away s)
       * algebraMap A (Localization.Away s) s_D
       * ∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t
   ```
   This is the natural Wedhorn 8.34(ii) factorization: the cover base
   denominator `algebraMap s` factors through `σ_loc` (the Cor 7.32
   dominating unit), `algebraMap s_D` (the cover-piece denominator),
   and the product over `T_D.image` (the cover-piece test family,
   imaged into `Localization.Away s`). Compare
   `WedhornStandardCoverRefinement.exists_single_f_refinement_at_t_via_dominating_unit`
   target signature
   (`Adic spaces/WedhornStandardCoverRefinement.lean:419–462`):
   `f := (σ : A) * t * D.s ^ (N - 1)` for some `N`. Our `N = 0` form
   matches the natural multi-element extension of that template.

2. **Per-element integrality of `T_D` at `w`** (`T_D` images bounded
   by `1`):
   ```
   ∀ w ∈ Spa, ∀ t ∈ T_D, w.vle (algebraMap A (Localization.Away s) t) 1
   ```
   The natural Tate condition: each `t ∈ T_D` is power-bounded
   (integral) at `w`. Comes from the cover-piece structure
   `D.T ⊆ A⁺` plus continuity of `algebraMap`; equivalently, the
   `algebraMap`-image of `T_D` lies in the integers of `w`.

**Conclusion**: at every `w ∈ Spa(Localization.Away s, ⁺)` under
f-membership, the multi-element bound
`w.vle (∏ T_D.image (algebraMap)) (algebraMap s_D)` holds.

**Proof**: pure valuation arithmetic.

* From the factorization plus f-membership, after `vle_iff_mul_unit_left`
  cancellation of `σ_loc`, the chain `w.vle (∏) (algebraMap s_D · ∏)`.
* Per-element integrality + `Spv.vle_prod_of_pointwise` (in
  `WedhornMultiDominatingUnit.lean`) → `w.vle (∏ T_D.image) 1`.
* Case-split on `w.vle (∏) 0`: if `(∏) = 0` at `w`, transitivity through
  `ValuativeRel.zero_vle` gives the multi-bound; otherwise,
  `ValuativeRel.vle_mul_cancel` on `w.vle (∏) (algebraMap s_D · ∏)`
  yields `w.vle 1 (algebraMap s_D)`, then transitivity through
  `w.vle (∏) 1` gives the multi-bound.

**Strictly stronger than a wrapper**: the multi-element bound is
**derived** from the factorization + per-element integrality, not
assumed.

**First exact missing algebraic/factorization fact (per-element lower
bound)**: the *lower-bound clause* of `h_per_piece_multi_lower`,
`∀ t' ∈ T_D.image (algebraMap), w.vle 1 t'` per `w` under f-membership,
is the **genuinely missing per-piece content** that this theorem does
not deliver. T054's `WedhornMultiPieceLaurentRefinement.lean` documents
that this universal-over-`T_D.image` form is **not derivable from
the Cor 7.32 σ-strict-domination + cover-refinement Laurent piece
structure alone**: at any `w ∈ V_τ`, only `σ_loc⁻¹ · τ` satisfies the
lower bound `w.vle 1 (σ_loc⁻¹ · τ)`, not other `σ_loc⁻¹ · τ'` for
`τ' ≠ τ` (T035 counter-example). The same obstruction applies to the
unrescaled per-element bound `w.vle 1 t'` for `t' ∈ T_D.image`. The
lower bound therefore requires either:

* **A finer Laurent cover refinement** where each piece simultaneously
  pins all `t' ∈ T_D.image` to the lower bound (Wedhorn 8.33 binary
  Laurent acyclicity iterated; the n-fold piece refinement); OR

* **A structural fact about `T_D.image`** that the cover-refinement
  element construction guarantees `T_D.image ⊆` (some specific
  unit-bounded subring) at every `w ∈` (cover plus-piece) — concretely,
  a Wedhorn 7.45-style result tying `T_D.image` valuations to the
  cover-refinement element's `algebraMap`-image structure.

**Use**: combine with the per-element lower bound (as a separate
hypothesis or downstream input) to form the full
`h_per_piece_multi_lower`, then feed
`h_T_D_multi_and_lower_bound_via_laurent_cover_refinement` (commit
`9d990df`) and `h_per_w_laurent_piece_target` (commit `f4f3b70`) to
obtain the per-`w` localized rationalOpen Laurent-piece data consumed
by `h_T_test_compat_loc_branch_α_T_D_via_localized_laurent_piece`. -/
theorem multi_bound_via_cover_refinement_factorization
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_factorization :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      algebraMap A (Localization.Away s) s =
        (σ_loc : Localization.Away s) *
          algebraMap A (Localization.Away s) s_D *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
    (h_T_D_image_int :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle t' (1 : Localization.Away s)) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w.vle ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
        (algebraMap A (Localization.Away s) s) →
      w.vle (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)
            (algebraMap A (Localization.Away s) s_D) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa hw_f
  letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
  -- Step 1: Substitute the factorization in f-membership.
  set P_im := ∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t with hP_im_def
  have hf' : w.vle ((σ_loc : Localization.Away s) * P_im)
      ((σ_loc : Localization.Away s) *
        (algebraMap A (Localization.Away s) s_D * P_im)) := by
    rw [show (σ_loc : Localization.Away s) *
            (algebraMap A (Localization.Away s) s_D * P_im) =
          (σ_loc : Localization.Away s) *
            algebraMap A (Localization.Away s) s_D * P_im from by ring,
      ← h_factorization]
    exact hw_f
  -- Step 2: Cancel σ_loc on the left via vle_iff_mul_unit_left.
  have hP_im_chain : w.vle P_im
      (algebraMap A (Localization.Away s) s_D * P_im) :=
    (vle_iff_mul_unit_left w σ_loc P_im
      (algebraMap A (Localization.Away s) s_D * P_im)).mp hf'
  -- Step 3: Per-element integrality + Spv.vle_prod_of_pointwise →
  -- product is integral at w (∏ ≤ 1).
  have hP_im_int : w.vle P_im (1 : Localization.Away s) := by
    have h_pw : ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle t' (1 : Localization.Away s) := h_T_D_image_int w hw_spa
    have h_prod : w.vle
        (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)
        (∏ _t ∈ T_D.image (algebraMap A (Localization.Away s)),
          (1 : Localization.Away s)) :=
      Spv.vle_prod_of_pointwise w (T_D.image (algebraMap A (Localization.Away s)))
        h_pw
    rwa [Finset.prod_const_one] at h_prod
  -- Step 4: Case-split on whether P_im is `0`-related at w.
  by_cases hP_im_zero : w.vle P_im 0
  · -- P_im is `0` at w: multi-bound is trivial via transitivity through 0.
    exact w.vle_trans hP_im_zero
      (ValuativeRel.zero_vle (algebraMap A (Localization.Away s) s_D))
  · -- P_im is non-vanishing at w: cancel P_im in hP_im_chain to get
    -- w.vle 1 (algebraMap s_D), then transitivity with hP_im_int.
    have h_one_le_s_D : w.vle (1 : Localization.Away s)
        (algebraMap A (Localization.Away s) s_D) := by
      have h_chain' : w.vle ((1 : Localization.Away s) * P_im)
          (algebraMap A (Localization.Away s) s_D * P_im) := by
        rw [one_mul]; exact hP_im_chain
      exact w.vle_mul_cancel hP_im_zero h_chain'
    exact w.vle_trans hP_im_int h_one_le_s_D

omit [PlusSubring A] in
/-- **T170 chained caller**: combine the case-wise multi-bound theorem
with a separately-supplied per-element lower bound to discharge T169's
`h_per_piece_multi_lower`, then feed it through
`h_T_D_multi_and_lower_bound_via_laurent_cover_refinement` (T169) and
`h_per_w_laurent_piece_target` (T169 commit `f4f3b70`) to produce the
per-`w` localized rationalOpen Laurent-piece data.

Demonstrates that T170's case-wise multi-bound theorem composes
cleanly with the existing T169 chain:

```
h_factorization + h_T_D_image_int        h_per_element_lower
              ↓                                   ↓
    multi_bound_via_…_factorization              ↓
              ↓                                   ↓
              └────────── h_per_piece_multi_lower
                           ↓
              h_T_D_multi_and_lower_bound_via_laurent_cover_refinement
                           ↓
                  (h_T_D_multi_bound, h_T_D_lower_bound)
                           ↓
                 h_per_w_laurent_piece_target
                           ↓
                 per-`w` rationalOpen Laurent-piece data
                           ↓
       (consumed by h_T_test_compat_loc_branch_α_T_D_via_localized_laurent_piece)
```

The `h_per_element_lower` hypothesis is the **first exact missing
algebraic/factorization fact** named in
`multi_bound_via_cover_refinement_factorization`'s docstring; this
caller passes it through unchanged. Discharging it requires either a
finer Laurent cover refinement (Wedhorn 8.33 iterated) or a Wedhorn
7.45-style structural fact about `T_D.image` valuations, neither of
which is currently in the project. -/
theorem h_T_D_multi_and_lower_bound_via_factorization_and_lower
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (hσ_loc_dom :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s))
    (h_factorization :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      algebraMap A (Localization.Away s) s =
        (σ_loc : Localization.Away s) *
          algebraMap A (Localization.Away s) s_D *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
    (h_T_D_image_int :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle t' (1 : Localization.Away s))
    (h_per_element_lower :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ τ ∈ localizedTestFamily s T_D s_D,
        ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
          w ∈ rationalOpen
              ({(1 : Localization.Away s)} : Finset (Localization.Away s))
              (((σ_loc⁻¹ : (Localization.Away s)ˣ) : Localization.Away s) *
                τ) →
          w.vle ((σ_loc : Localization.Away s) *
              (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
            (algebraMap A (Localization.Away s) s) →
          ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
            w.vle (1 : Localization.Away s) t') :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    (∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)
              (algebraMap A (Localization.Away s) s_D)) ∧
    (∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle (1 : Localization.Away s) t') := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  -- Multi-element bound: from T170's case-wise factorization theorem.
  have h_multi := multi_bound_via_cover_refinement_factorization
    P T s hopen T_D s_D σ_loc h_factorization h_T_D_image_int
  -- Assemble per-piece multi+lower from multi-bound (proved) and
  -- per-element lower bound (hypothesis), then dispatch via the
  -- T169 cover-decomposition theorem.
  have h_per_piece_multi_lower :
      ∀ τ ∈ localizedTestFamily s T_D s_D,
        ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
          w ∈ rationalOpen
              ({(1 : Localization.Away s)} : Finset (Localization.Away s))
              (((σ_loc⁻¹ : (Localization.Away s)ˣ) : Localization.Away s) *
                τ) →
          w.vle ((σ_loc : Localization.Away s) *
              (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
            (algebraMap A (Localization.Away s) s) →
          w.vle (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)
                (algebraMap A (Localization.Away s) s_D) ∧
          (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
              w.vle (1 : Localization.Away s) t') := by
    intro τ hτ w hw_spa hw_piece hw_f
    exact ⟨h_multi w hw_spa hw_f,
      h_per_element_lower τ hτ w hw_spa hw_piece hw_f⟩
  exact h_T_D_multi_and_lower_bound_via_laurent_cover_refinement
    P T s hopen T_D s_D σ_loc hσ_loc_dom h_per_piece_multi_lower

end ValuationSpectrum
