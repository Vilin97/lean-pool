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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalArithmeticPerTChain
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalCompatFromTestFamily
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalPerBranchChain

/-!
# Wedhorn local-subset consumer via σ-factored chains

Caller-shaped composition of the localized Wedhorn 8.34(ii) supplier
files into a single base rational-open subset inclusion theorem. After
this commit, future callers no longer need to manually thread
`localizedTestFamily` and the per-branch compatibility theorem into
the base-subset pullback.

## Composition

This file composes:

1. `localizedTestFamily` (commit `6fc4d08`) as the `T_test_loc`
   choice.
2. `h_T_test_compat_loc_canonical_via_factored_chains` (commit
   `83f2964`) — produces the per-branch compatibility from σ-factored
   chain inputs.
3. `rationalOpen_subset_base_via_local_Cor732_chain` (commit `4197d87`)
   — pulls back the local rational-open inclusion to the base.

## What this file provides

* `rationalOpen_subset_base_via_factored_chains` — the **caller-shaped
  composed theorem**: given the denominator-cleared identity, σ-strict-
  domination over the canonical test family, and the σ-factored
  per-branch chain hypotheses, derive the base rational-open inclusion
  `rationalOpen (insert f T_base) s ⊆ rationalOpen T_D s_D`.

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness / Zavyalov / bivariate-overlap content.
* Does not edit Tertiary's localized Cor 7.32 consumer file or any
  in-flight file.
* Pure composition — no new mathematical content; reuses
  `h_T_test_compat_loc_canonical_via_factored_chains` and
  `rationalOpen_subset_base_via_local_Cor732_chain` directly.
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

/-- **Composed Wedhorn 8.34(ii) base-subset consumer via σ-factored
chains**.

Given:
* `f : A` denominator-cleared candidate with
  `algebraMap f = σ_loc · (∏ T_D.image algebraMap)` (`h_alg`);
* localized strict-σ-domination over the canonical test family
  `localizedTestFamily s T_D s_D` (`hσ_loc`);
* σ-factored per-branch chain hypotheses for the `α_s_D` branch
  (`h_α_s_D_factored`) and the `α_T_D` branches (`h_α_T_D_factored`);
* explicit `α_T_D`-branch `¬ w.vle (algebraMap s_D) 0` discharger
  (`h_α_T_D_s_D_ne`),

derive the base rational-open inclusion
`rationalOpen (insert f T_base) s ⊆ rationalOpen T_D s_D`.

The σ-factored form of the per-branch chains matches the natural shape
of Wedhorn 8.34(ii) candidate data (the candidate
`f := σ_loc · (∏ T_D.image algebraMap)` makes the σ_loc factor manifest);
the cancellation back to the unfactored form is handled internally by
`h_T_test_compat_loc_canonical_via_factored_chains`. -/
theorem rationalOpen_subset_base_via_factored_chains
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (hA₀_le : P.A₀ ≤ A⁺)
    (T_base T_D : Finset A) (s_D : A)
    (h_T_le_T_base : T ⊆ T_base)
    (f : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_alg :
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      algebraMap A (Localization.Away s) f =
       (σ_loc : Localization.Away s) *
         (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
    (hσ_loc :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s))
    (h_α_s_D_factored :
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
          w.vle (t' * (σ_loc : Localization.Away s))
            ((algebraMap A (Localization.Away s) s_D) *
              (σ_loc : Localization.Away s)))
    (h_α_T_D_factored :
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
            w.vle (t' * (σ_loc : Localization.Away s))
              ((algebraMap A (Localization.Away s) s_D) *
                (σ_loc : Localization.Away s)))
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
    rationalOpen (insert f T_base) s ⊆ rationalOpen T_D s_D :=
  rationalOpen_subset_base_via_local_Cor732_chain P T s hopen hA₀_le
    T_base T_D s_D h_T_le_T_base f σ_loc h_alg
    (localizedTestFamily s T_D s_D) hσ_loc
    (h_T_test_compat_loc_canonical_via_factored_chains P T s hopen T_D s_D
      σ_loc h_α_s_D_factored h_α_T_D_factored h_α_T_D_s_D_ne)

end ValuationSpectrum
