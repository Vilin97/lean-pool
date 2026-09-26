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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornMPowerDecayFromStructural
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornPerTFactoredBranchLink

/-!
# Wedhorn structural inequality from σ-power-structural data

Tightens the M-power-decay residual exposed by
`WedhornMPowerDecayFromStructural` (commit `9e0a147`) into a
**single bundled structural supplier** with TWO conjuncts (Wedhorn
structural inequality + T_D non-vanishing). The third conjunct
(`¬ w.vle (algebraMap s_D) 0`) is **fully auto-derived** for **both
branches** of the canonical test family, including the previously-residual
`α_T_D` case.

## Auto-derivation analysis

The previous bridge (`h_M_power_decay_via_Wedhorn_structural_inequality`,
commit `9e0a147`) auto-derived only the `α_s_D` branch's `s_D`
non-vanishing via `not_vle_zero_of_strict_dominator` and required the
`α_T_D` branch as a separate explicit hypothesis.

This file proves the `α_T_D` branch's `s_D` non-vanishing as well, by
**contradiction** using:

1. The Wedhorn structural inequality (per-`t'`):
   `w.vle (algebraMap s) (algebraMap s_D * σ_loc * ∏ erase t')`.
2. The T_D non-vanishing: `∀ t'' ∈ T_D.image algebraMap, ¬ w.vle t'' 0`.
3. The f-membership: `w.vle (σ_loc * ∏) (algebraMap s)`.
4. σ_loc is a unit.

Suppose `w.vle (algebraMap s_D) 0`. Then multiplying the structural
inequality's RHS by zero (using `mul_vle_mul_left`) gives
`w.vle (algebraMap s_D * σ_loc * ∏ erase τ) 0`; chaining through the
structural inequality and the f-membership produces
`w.vle (σ_loc * ∏) 0`; cancelling σ_loc (via
`ValuativeRel.mul_vle_mul_iff_right` with σ_loc-non-vanishing from
`not_vle_zero_of_isUnit`) yields `w.vle (∏) 0`; then
`not_vle_zero_prod_of_pointwise` (commit `77e66a2`) plus T_D non-vanishing
contradict.

Both branches of the canonical test family share this contradiction
template: the `α_s_D` branch additionally has the simpler
`not_vle_zero_of_strict_dominator` route, but the contradiction
argument works uniformly.

## What this file provides

* `WedhornMPowerStructuralData` — bundled structural supplier
  Prop carrying the Wedhorn structural inequality + T_D non-vanishing
  per-`(w, τ)`.

* `h_M_power_decay_from_sigma_power_structural_data` — caller-facing
  bridge consuming **one** structural supplier (`WedhornMPowerStructuralData`)
  and producing the unified M-power-decay output, with the
  `s_D` non-vanishing fully auto-derived.

The bundled supplier is the **single canonical residual**, strictly
smaller than the prior three-supplier boundary in commit `9e0a147`.

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness / Zavyalov / bivariate-overlap content.
* Reuses helpers from existing committed infrastructure:
  `not_vle_zero_of_strict_dominator` (`WedhornMultiDominatingUnit`),
  `not_vle_zero_prod_of_pointwise` (`WedhornPerTFactoredBranchLink`),
  `mem_localizedTestFamily_iff` (`WedhornLocalCompatFromTestFamily`),
  `not_vle_zero_of_isUnit` (`ValuationSpectrum`),
  `Spv.mul_vle_mul_left` (`ValuationSpectrum`),
  `ValuativeRel.mul_vle_mul_iff_right` (Mathlib).
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

/-- **Bundled Wedhorn structural supplier** — single named Prop carrying
the Wedhorn 8.34(ii) Route B M-power structural data:

* the Wedhorn structural inequality (per-`t'`): `w.vle (algebraMap s)
  (algebraMap s_D * σ_loc * ∏ erase t')`;
* the T_D non-vanishing.

Quantified over `w ∈ Spa(Localization.Away s, locSubring P T s)` with
f-membership and σ-strict-domination by some `τ ∈ localizedTestFamily
s T_D s_D`. The third conjunct (`¬ w.vle (algebraMap s_D) 0`) is NOT
included here — it is auto-derived inside the bridge. -/
def WedhornMPowerStructuralData
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
        (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
            w.vle (algebraMap A (Localization.Away s) s)
              (algebraMap A (Localization.Away s) s_D *
                (σ_loc : Localization.Away s) *
                (∏ t ∈ (T_D.image
                  (algebraMap A (Localization.Away s))).erase t', t))) ∧
        (∀ t'' ∈ T_D.image (algebraMap A (Localization.Away s)),
            ¬ w.vle t'' 0)

omit [PlusSubring A] in
/-- **Caller-facing bridge** — consumes the single bundled structural
supplier `WedhornMPowerStructuralData` and produces the unified
M-power-decay output, with the `s_D` non-vanishing
**fully auto-derived for both branches**.

The `α_s_D` branch's `s_D` non-vanishing follows from
`not_vle_zero_of_strict_dominator` applied to the σ-strict-domination
of `algebraMap s_D`. The `α_T_D` branch's `s_D` non-vanishing follows
from the contradiction argument: assuming `w.vle (algebraMap s_D) 0`
combined with the structural inequality + T_D non-vanishing +
f-membership + σ_loc unit yields `w.vle (∏ T_D.image algebraMap) 0`,
contradicting T_D non-vanishing via `not_vle_zero_prod_of_pointwise`. -/
theorem h_M_power_decay_from_sigma_power_structural_data
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_structural_data : WedhornMPowerStructuralData P T s hopen T_D s_D σ_loc) :
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
          (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
              w.vle (algebraMap A (Localization.Away s) s)
                (algebraMap A (Localization.Away s) s_D *
                  (σ_loc : Localization.Away s) *
                  (∏ t ∈ (T_D.image
                    (algebraMap A (Localization.Away s))).erase t', t))) ∧
          (∀ t'' ∈ T_D.image (algebraMap A (Localization.Away s)),
              ¬ w.vle t'' 0) ∧
          ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa hw_f τ hτ hστ
  obtain ⟨h_struct, h_T_D_ne⟩ := h_structural_data w hw_spa hw_f τ hτ hστ
  refine ⟨h_struct, h_T_D_ne, ?_⟩
  -- Auto-derive `¬ w.vle (algebraMap s_D) 0` via case split on τ.
  rw [mem_localizedTestFamily_iff] at hτ
  rcases hτ with rfl | hτ_in_T_D
  · -- α_s_D branch: simple direct argument.
    exact not_vle_zero_of_strict_dominator hστ.2
  · -- α_T_D branch: contradiction argument.
    intro h_α_s_D_zero
    -- The bundled supplier guarantees T_D.image algebraMap is nonempty
    -- (it contains `τ`), so we can pick `τ` itself for the structural
    -- inequality.
    have h_struct_τ := h_struct τ hτ_in_T_D
    -- h_struct_τ : w.vle (α s) (α s_D * σ_loc * ∏ erase τ)
    -- Step 1: from h_α_s_D_zero, derive
    --   w.vle (α s_D * σ_loc * ∏ erase τ) 0
    -- by multiplying on the right by σ_loc and then by ∏ erase τ.
    have h1a : w.vle (algebraMap A (Localization.Away s) s_D *
        (σ_loc : Localization.Away s)) 0 := by
      have := w.mul_vle_mul_left h_α_s_D_zero (σ_loc : Localization.Away s)
      rwa [zero_mul] at this
    have h1 : w.vle (algebraMap A (Localization.Away s) s_D *
        (σ_loc : Localization.Away s) *
        (∏ t ∈ (T_D.image
          (algebraMap A (Localization.Away s))).erase τ, t)) 0 := by
      have := w.mul_vle_mul_left h1a
        (∏ t ∈ (T_D.image
          (algebraMap A (Localization.Away s))).erase τ, t)
      rwa [zero_mul] at this
    -- Steps 2-3: chain through h_struct_τ and then hw_f.
    have h_σ_prod_zero : w.vle ((σ_loc : Localization.Away s) *
        (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)) 0 :=
      w.vle_trans hw_f (w.vle_trans h_struct_τ h1)
    -- Step 4: cancel σ_loc on the left.
    letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
    have hσ_ne : ¬ ((σ_loc : Localization.Away s) ≤ᵥ 0) :=
      not_vle_zero_of_isUnit (σ_loc.isUnit) w
    rw [show (0 : Localization.Away s) =
          (σ_loc : Localization.Away s) * 0 from (mul_zero _).symm,
        ValuativeRel.mul_vle_mul_iff_right hσ_ne] at h_σ_prod_zero
    -- h_σ_prod_zero : w.vle (∏ T_D.image α) 0
    -- Step 5: contradict T_D non-vanishing.
    exact not_vle_zero_prod_of_pointwise w
      (T_D.image (algebraMap A (Localization.Away s))) id h_T_D_ne
      h_σ_prod_zero

end ValuationSpectrum
