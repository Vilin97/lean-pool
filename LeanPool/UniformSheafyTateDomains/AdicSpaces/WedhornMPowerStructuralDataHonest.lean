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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornMultiBranchSubsetInequality
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornStructuralInequalityFromSigmaPower

/-!
# Wedhorn M-power-decay: honest supplier without T_D non-vanishing

Replaces the bundled `WedhornMPowerStructuralData` (commit `c8e8fad`)
with the **weakest honest structural supplier** actually needed by
the M-power-decay bridge, dropping the T_D non-vanishing conjunct
which the audit (per manager directive) flagged as not part of
Wedhorn 8.34(ii)'s natural argument.

## Audit findings

The previous bundled supplier had two conjuncts at each `(w, τ)`:

1. **Wedhorn structural inequality**: `∀ t' ∈ T_D.image algebraMap,
   w.vle (algebraMap s) (algebraMap s_D * σ_loc * ∏ erase t')`.
2. **T_D non-vanishing**: `∀ t'' ∈ T_D.image algebraMap, ¬ w.vle t'' 0`.

Conjunct (2) is **not part of Wedhorn 8.34(ii)'s natural argument**:

* For `w ∈ rationalOpen T_D s_D`, the rational-open conditions give
  `w.vle t'' s_D` for each `t''` and `¬ w.vle s_D 0`, but NOT
  `¬ w.vle t'' 0` (numerators can vanish at v).
* The previous chain consumed (2) only because of the multi-element
  product cancellation `mul_vle_mul_iff_left` over `∏ erase t'`,
  which requires the `erase`'d product to be nonzero. This is a
  scaffolding artifact of the existing reducer
  `rationalOpen_subset_via_strict_sigma_domination`'s multi-element
  candidate `f := σ * (∏ T_D)`; Wedhorn's actual single-`t` candidate
  `f := σ * t * D_s ^ (N-1)` doesn't require this.

The honest replacement: provide the **σ-factored per-`t'` inequality**
directly as the supplier (equivalent under σ-cancellation to the
unfactored conclusion `w.vle t' (algebraMap s_D)`):

```
∀ t' ∈ T_D.image algebraMap, w.vle (t' * σ_loc) (algebraMap s_D * σ_loc)
```

This avoids the `∏ erase t'` cancellation entirely; T_D non-vanishing
is not required.

## Auto-derivation of `s_D` non-vanishing

The bridge **fully auto-derives `¬ w.vle (algebraMap s_D) 0`** for
both branches without T_D non-vanishing:

* **α_s_D branch** (`τ = algebraMap s_D`): direct via
  `not_vle_zero_of_strict_dominator` from σ-strict-domination of
  `algebraMap s_D`.
* **α_T_D branch** (`τ ∈ T_D.image algebraMap`): contradiction
  argument using only the σ-factored supplier output for `t' = τ`
  (the σ-dominator at this `w`):
  - Suppose `w.vle (algebraMap s_D) 0`.
  - Multiply by σ_loc: `w.vle (algebraMap s_D * σ_loc) 0`.
  - From supplier at `t' = τ`: `w.vle (τ * σ_loc) (algebraMap s_D * σ_loc)`.
  - Chain via `vle_trans`: `w.vle (τ * σ_loc) 0`.
  - Cancel σ_loc via `vle_iff_mul_unit_right` (after rewriting
    `0 = 0 * σ_loc` and `mul_zero`): `w.vle τ 0`.
  - Contradicts `not_vle_zero_of_strict_dominator hστ.2`.

## What this file provides

* `WedhornMPowerStructuralDataHonest` — the honest one-conjunct
  bundled supplier (just the σ-factored per-`t'` inequality).

* `h_M_power_decay_from_honest_structural_data` — caller-facing bridge
  consuming the honest supplier; produces the unified M-power-decay
  output by σ-cancellation for the per-`t'` conclusion and the
  contradiction argument for s_D non-vanishing.

The single named residual is the σ-factored per-`t'` inequality
itself, which is Wedhorn's natural per-`t'` output (equivalent to
`w.vle t' (algebraMap s_D)` under σ-cancellation).

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness / Zavyalov / bivariate-overlap content.
* Reuses `not_vle_zero_of_strict_dominator`,
  `vle_iff_mul_unit_right` (commit `3bb87eb`),
  `mem_localizedTestFamily_iff` (commit `6fc4d08`),
  `Spv.mul_vle_mul_left` (`ValuationSpectrum`).
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

/-- **Honest weakest structural supplier** — single conjunct, the
σ-factored per-`t'` inequality.

Equivalent under σ-cancellation to the unfactored conclusion
`w.vle t' (algebraMap s_D)`. Provided as a `Prop` for caller use. -/
def WedhornMPowerStructuralDataHonest
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    w.vle ((σ_loc : Localization.Away s) *
        (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
      (algebraMap A (Localization.Away s) s) →
    ∀ τ ∈ localizedTestFamily s T_D s_D,
      w.vle (σ_loc : Localization.Away s) τ ∧
        ¬ w.vle τ (σ_loc : Localization.Away s) →
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle (t' * (σ_loc : Localization.Away s))
          (algebraMap A (Localization.Away s) s_D *
            (σ_loc : Localization.Away s))

omit [PlusSubring A] in
/-- **Bridge from the honest supplier to M-power-decay output**.

Consumes the σ-factored per-`t'` inequality and produces the per-`t'`
conclusion (via σ-cancellation) plus s_D non-vanishing for both
branches (auto-derived: α_s_D via `not_vle_zero_of_strict_dominator`;
α_T_D via contradiction using just the σ-factored supplier output for
the σ-dominator τ).

**No T_D non-vanishing is required.** -/
theorem h_M_power_decay_from_honest_structural_data
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_honest : WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc) :
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
  have h_sigma_factored := h_honest w hw_spa hw_f τ hτ hστ
  have h_per_t : ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      w.vle t' (algebraMap A (Localization.Away s) s_D) := fun t' ht' ↦
    (vle_iff_mul_unit_right w σ_loc t'
      (algebraMap A (Localization.Away s) s_D)).mp (h_sigma_factored t' ht')
  refine ⟨h_per_t, ?_⟩
  rw [mem_localizedTestFamily_iff] at hτ
  rcases hτ with rfl | hτ_in_T_D
  · exact not_vle_zero_of_strict_dominator hστ.2
  · intro h_α_s_D_zero
    exact not_vle_zero_of_strict_dominator hστ.2
      (w.vle_trans (h_per_t τ hτ_in_T_D) h_α_s_D_zero)

/-- **Caller-facing bridge from the honest supplier to rational-open
containment**.

From the honest σ-factored supplier `WedhornMPowerStructuralDataHonest`,
the localized Cor 7.32 σ-strict-domination output (over the canonical
test family `localizedTestFamily`), and the denominator-cleared
algebraic identity, derive the base rational-open inclusion
`rationalOpen (insert f T_base) s ⊆ rationalOpen T_D s_D`.

**No `T_D` non-vanishing in the public interface.** This is the
honest-supplier counterpart to `rationalOpen_subset_base_via_M_power_decay`
(commit `ab55d85`): it bypasses the old M-power-decay shape entirely,
feeding `h_M_power_decay_from_honest_structural_data` directly into
`rationalOpen_subset_base_via_local_Cor732_chain` since the bridge's
output already coincides with the chain's `_h_T_test_compat_loc`
canonical compat input. -/
theorem rationalOpen_subset_base_via_honest_structural_data
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
    (hσ_loc_dominates :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s))
    (h_honest : WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc) :
    rationalOpen (insert f T_base) s ⊆ rationalOpen T_D s_D :=
  rationalOpen_subset_base_via_local_Cor732_chain P T s hopen hA₀_le
    T_base T_D s_D h_T_le_T_base f σ_loc h_alg
    (localizedTestFamily s T_D s_D) hσ_loc_dominates
    (h_M_power_decay_from_honest_structural_data P T s hopen T_D s_D
      σ_loc h_honest)

end ValuationSpectrum
