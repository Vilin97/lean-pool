/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocalCompatFromTestFamily
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornMultiBranchSubsetInequality

/-!
# Wedhorn local arithmetic per-`t'` chain — σ-factor cancellation
reduction

Provides the local arithmetic bridge feeding `h_T_test_compat_loc_canonical`
(commit `6fc4d08`), reducing the per-`t'` chain hypotheses for both
branches (`α_s_D` and `α_T_D`) to their σ_loc-factored counterparts via
unit-cancellation.

## Why σ-factor cancellation

For each branch, the per-`t'` chain conclusion
`∀ t' ∈ T_D.image algebraMap, w.vle t' (algebraMap s_D)` is
**equivalent** (under `σ_loc : (Localization.Away s)ˣ`) to its
σ_loc-factored form
`∀ t' ∈ T_D.image algebraMap, w.vle (t' * σ_loc) (algebraMap s_D * σ_loc)`,
via `vle_iff_mul_unit_right` (committed `3bb87eb`). The factored form
is a useful intermediate when assembling the chain from concrete
Wedhorn 8.34(ii) candidate data because the σ_loc factor naturally
appears as part of the candidate
`f := σ_loc * (∏ T_D.image algebraMap)`.

This file does NOT close the genuinely-Wedhorn-content gap (the
factored chain itself is the residual); it provides a clean
σ-cancellation REDUCTION so the residual is stated in the σ-factored
form, which matches the natural structural form of Wedhorn 8.34(ii)
candidate data.

## What this file provides

* `per_t_inequality_via_sigma_factor` — pointwise σ-cancellation:
  `w.vle (t' * σ_loc) (a * σ_loc) ↔ w.vle t' a` for `σ_loc : Aˣ`.

* `h_α_s_D_per_t_via_factored_chain` — `α_s_D` branch supplier
  produced by σ-cancelling a factored per-`t'` chain hypothesis.

* `h_α_T_D_per_t_via_factored_chain` — `α_T_D` branch supplier
  produced by σ-cancelling a factored per-`t'` chain hypothesis.

* `h_T_test_compat_loc_canonical_via_factored_chains` — the **full
  composed theorem**: takes σ-factored per-branch chain hypotheses
  for both branches plus the explicit `α_T_D` `s_D` non-degeneracy,
  and produces `h_T_test_compat_loc_canonical`-shape output ready for
  `rationalOpen_subset_base_via_local_Cor732_chain`.

## Honest residual statement

The σ-factored per-`t'` chain itself remains the genuinely-Wedhorn
residual. It is now a single named theorem-level statement with
explicit branch-specific structural data, rather than a `sorry` blob:
see the documented residual at the bottom of this file.

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness / Zavyalov / bivariate-overlap content.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] in
/-- **Pointwise σ-cancellation for `vle`**: for `σ : Aˣ`, the inequality
`w.vle (t * σ) (a * σ)` is equivalent to `w.vle t a`. Direct application
of `vle_iff_mul_unit_right` (committed `3bb87eb`). -/
theorem per_t_inequality_via_sigma_factor
    (w : Spv A) (σ : Aˣ) (t a : A) :
    w.vle (t * (σ : A)) (a * (σ : A)) ↔ w.vle t a :=
  vle_iff_mul_unit_right w σ t a

omit [PlusSubring A] in
/-- **`α_s_D` branch supplier via σ-factored chain**.

Given a σ_loc-factored per-`t'` chain hypothesis for the `α_s_D`
branch, produce the un-factored form consumed by
`h_T_test_compat_loc_canonical`. The reduction is one-line via
`per_t_inequality_via_sigma_factor` per-`t'`. -/
theorem h_α_s_D_per_t_via_factored_chain
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_factored :
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
              (σ_loc : Localization.Away s))) :
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
        w.vle t' (algebraMap A (Localization.Away s) s_D) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa hw_f hστ t' ht'
  have h_factored_t' := h_factored w hw_spa hw_f hστ t' ht'
  exact (per_t_inequality_via_sigma_factor w σ_loc t'
    (algebraMap A (Localization.Away s) s_D)).mp h_factored_t'

omit [PlusSubring A] in
/-- **`α_T_D` branch supplier via σ-factored chain**. Symmetric to
`h_α_s_D_per_t_via_factored_chain` but for `τ ∈ T_D.image algebraMap`
branches. -/
theorem h_α_T_D_per_t_via_factored_chain
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_factored :
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
                (σ_loc : Localization.Away s))) :
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
  intro τ hτ w hw_spa hw_f hστ t' ht'
  have h_factored_t' := h_factored τ hτ w hw_spa hw_f hστ t' ht'
  exact (per_t_inequality_via_sigma_factor w σ_loc t'
    (algebraMap A (Localization.Away s) s_D)).mp h_factored_t'

omit [PlusSubring A] in
/-- **Composed canonical theorem**: takes σ-factored per-branch chain
hypotheses for both branches plus the explicit `α_T_D`-branch
non-degeneracy `h_α_T_D_s_D_ne`, and produces a
`h_T_test_compat_loc_canonical`-shape output ready for
`rationalOpen_subset_base_via_local_Cor732_chain`.

The factored chains are still genuine Wedhorn content (not algebraically
trivialised), but their CANONICAL FORM matches the natural structure
of Wedhorn 8.34(ii) candidate data: the candidate
`f := σ_loc * (∏ T_D.image algebraMap)` makes the σ_loc factor manifest.
-/
theorem h_T_test_compat_loc_canonical_via_factored_chains
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
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
            ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 :=
  h_T_test_compat_loc_canonical P T s hopen T_D s_D σ_loc
    (h_α_s_D_per_t_via_factored_chain P T s hopen T_D s_D σ_loc h_α_s_D_factored)
    (h_α_T_D_per_t_via_factored_chain P T s hopen T_D s_D σ_loc h_α_T_D_factored)
    h_α_T_D_s_D_ne

/-! ### Remaining residual (one named theorem-level statement)

The σ-factored per-`t'` chain itself remains the Wedhorn-content
residual. It is a single named theorem with explicit structural data,
not a `sorry` blob:

```
theorem per_t_factored_chain_local_at
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (τ : Localization.Away s)
    (w : Spv (Localization.Away s))
    (hw_spa :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      w ∈ Spa (Localization.Away s) (Localization.Away s)⁺)
    (hw_f : w.vle ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
        (algebraMap A (Localization.Away s) s))
    (hστ : w.vle (σ_loc : Localization.Away s) τ ∧
        ¬ w.vle τ (σ_loc : Localization.Away s))
    -- Branch-specific structural relation:
    (h_branch_link : sorry)  -- see structural cases below
    (t' : Localization.Away s)
    (ht' : t' ∈ T_D.image (algebraMap A (Localization.Away s))) :
    w.vle (t' * (σ_loc : Localization.Away s))
      ((algebraMap A (Localization.Away s) s_D) *
        (σ_loc : Localization.Away s))
```

The `h_branch_link` premise carries the genuine Wedhorn 8.34(ii)
arithmetic — the two structural cases:

* **`α_s_D` branch case** (`τ = algebraMap s_D`): `h_branch_link`
  provides the structural fact relating `w(σ_loc)`, `w(α s_D)`, and
  `w(∏ T_D.image α)` that allows extracting the per-`t'` ratio. The
  exact form depends on the `σ_loc = π_loc^(M+1)` Cor 7.32 construction
  + the choice of `M` from compactness.

* **`α_T_D` branch case** (`τ ∈ T_D.image algebraMap`): similar
  structural fact but referencing the dominating `τ ∈ T_D.image`
  instead of `α s_D`.

Per the existing audit at
`WedhornMultiDominatingUnit.lean:234–304`, neither branch's per-`t'`
discharge reduces to σ-strict-domination alone. The genuinely-new
Wedhorn content (next ticket) is the construction of `h_branch_link`
from the localized Tate / Cor 7.32 setup. -/

end ValuationSpectrum
