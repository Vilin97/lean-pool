/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Card
import Mathlib.Topology.Algebra.InfiniteSum.Real
import LeanPool.LiCriterion.Hadamard.OrderOne.CofiniteControl
import LeanPool.LiCriterion.Hadamard.OrderOne.ZeroCountingBounds

/-! ### Dyadic ball finsets under `∑ 1/‖z ρ‖² < ∞` -/

open scoped BigOperators

-- This module bundles several long tail-estimate developments.

namespace Hadamard

namespace OrderOne

open Real

/-- The finite set of indices with `‖Z.z ρ‖ ≤ 2^n`. -/
theorem zerosBallFinite {f : ℂ → ℂ} (Z : ZeroSet f)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0)
    (h_summable : Summable (fun ρ : Z.Zero => (1 : ℝ) / ‖Z.z ρ‖ ^ 2))
    (n : ℕ) : ({ρ : Z.Zero | ‖Z.z ρ‖ ≤ (2 : ℝ) ^ n} : Set Z.Zero).Finite :=
  Hadamard.OrderOne.finite_norm_le_of_summable_inv_norm_sq
    (z := Z.z) (hz0 := h_z_ne_zero) h_summable (R := (2 : ℝ) ^ n) (by positivity)

/-- The set of indices with `‖Z.z ρ‖ ≤ 2^n`, as a `Finset`. -/
noncomputable def zerosBallFinset {f : ℂ → ℂ} (Z : ZeroSet f)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0)
    (h_summable : Summable (fun ρ : Z.Zero => (1 : ℝ) / ‖Z.z ρ‖ ^ 2))
    (n : ℕ) : Finset Z.Zero :=
  (zerosBallFinite Z h_z_ne_zero h_summable n).toFinset

@[simp]
lemma mem_zerosBallFinset_iff {f : ℂ → ℂ} (Z : ZeroSet f)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0)
    (h_summable : Summable (fun ρ : Z.Zero => (1 : ℝ) / ‖Z.z ρ‖ ^ 2))
    (n : ℕ) (ρ : Z.Zero) :
    ρ ∈ zerosBallFinset Z h_z_ne_zero h_summable n ↔ ‖Z.z ρ‖ ≤ (2 : ℝ) ^ n := by
  classical
  simp [zerosBallFinset]

@[simp]
lemma card_zerosBallFinset {f : ℂ → ℂ} (Z : ZeroSet f)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0)
    (h_summable : Summable (fun ρ : Z.Zero => (1 : ℝ) / ‖Z.z ρ‖ ^ 2))
    (n : ℕ) :
    (zerosBallFinset Z h_z_ne_zero h_summable n).card =
      ({ρ : Z.Zero | ‖Z.z ρ‖ ≤ (2 : ℝ) ^ n} : Set Z.Zero).ncard := by
  classical
  simpa [zerosBallFinset] using
    (Set.ncard_eq_toFinset_card ({ρ : Z.Zero | ‖Z.z ρ‖ ≤ (2 : ℝ) ^ n} : Set Z.Zero)
          (zerosBallFinite Z h_z_ne_zero h_summable n)).symm

/-!
Tail estimates for genus‑1 canonical products (order‑≤1 regime).

This module will eventually house the dyadic-shell bounds (Conway XI §1–2) used in the growth
analysis. For now, we start by packaging a convenient `O(r^(1+ε))` bound for the zero-counting
function coming from `ZeroCountingBounds`.
-/

theorem ncard_zeros_le_rpow
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (hf_finite : hasFiniteOrder f) (hf_order_le : order f ≤ 1)
    (Z : ZeroSet f) [Countable Z.Zero]
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0)
    (h_simple : ∀ ρ : Z.Zero, deriv f (Z.z ρ) ≠ 0) :
    ∀ ε : ℝ, 0 < ε →
      ∃ R₀ C : ℝ, 0 ≤ C ∧
        ∀ r : ℝ, R₀ ≤ r →
          (({ρ : Z.Zero | ‖Z.z ρ‖ ≤ r} : Set Z.Zero).ncard : ℝ) ≤ C * r ^ ((1 : ℝ) + ε) := by
  intro ε hε
  obtain ⟨R₁, hR₁⟩ :=
    ncard_zeros_le_of_order_le_one (f := f) hf_entire hf_finite hf_order_le Z h_zeros_only h_inj
      h_z_ne_zero h_simple ε hε
  have hlog2_pos : 0 < Real.log 2 := by
    simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2)
  let C : ℝ := ((2 : ℝ) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|) / Real.log 2
  refine ⟨max R₁ 1, C, ?_, ?_⟩
  · have hC_nonneg : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖| := by
      have hpow : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) + ε) := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
      exact add_nonneg hpow (abs_nonneg _)
    exact div_nonneg hC_nonneg (le_of_lt hlog2_pos)
  intro r hr
  have hr_ge_R1 : R₁ ≤ r := le_trans (le_max_left _ _) hr
  have hr_ge1 : (1 : ℝ) ≤ r := le_trans (le_max_right _ _) hr
  have hr_nonneg : 0 ≤ r := le_trans (by norm_num : (0 : ℝ) ≤ 1) hr_ge1
  have hcount := hR₁ r hr_ge_R1
  -- First, replace `-log ‖f 0‖` by `|log ‖f 0‖|`.
  have hnum_le :
      (2 * r) ^ ((1 : ℝ) + ε) - Real.log ‖f 0‖
        ≤ (2 * r) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖| := by
    have : -Real.log ‖f 0‖ ≤ |Real.log ‖f 0‖| := by
      simpa using (neg_le_abs (Real.log ‖f 0‖))
    linarith
  have hcount' :
      (({ρ : Z.Zero | ‖Z.z ρ‖ ≤ r} : Set Z.Zero).ncard : ℝ)
        ≤ ((2 * r) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|) / Real.log 2 := by
    have hfrac_le :
        ((2 * r) ^ ((1 : ℝ) + ε) - Real.log ‖f 0‖) / Real.log 2
          ≤ ((2 * r) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|) / Real.log 2 :=
      div_le_div_of_nonneg_right hnum_le (le_of_lt hlog2_pos)
    exact le_trans hcount hfrac_le
  -- Rewrite `(2*r)^(1+ε)` and absorb the constant using `r^(1+ε) ≥ 1`.
  have hrpow_ge1 : (1 : ℝ) ≤ r ^ ((1 : ℝ) + ε) :=
    Real.one_le_rpow hr_ge1 (by linarith [hε] : (0 : ℝ) ≤ (1 : ℝ) + ε)
  have hmul_rpow :
      (2 * r) ^ ((1 : ℝ) + ε)
        = (2 : ℝ) ^ ((1 : ℝ) + ε) * r ^ ((1 : ℝ) + ε) := by
    simpa using
      (Real.mul_rpow (x := (2 : ℝ)) (y := r) (by norm_num : (0 : ℝ) ≤ (2 : ℝ)) hr_nonneg
        (z := (1 : ℝ) + ε))
  have hnum2 :
      (2 * r) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|
        ≤ ((2 : ℝ) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|) * r ^ ((1 : ℝ) + ε) := by
    have habs_mul : |Real.log ‖f 0‖| ≤ |Real.log ‖f 0‖| * r ^ ((1 : ℝ) + ε) :=
      le_mul_of_one_le_right (abs_nonneg _) hrpow_ge1
    calc
      (2 * r) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|
          = (2 : ℝ) ^ ((1 : ℝ) + ε) * r ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖| := by
              simp [hmul_rpow]
      _ ≤ (2 : ℝ) ^ ((1 : ℝ) + ε) * r ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖| * r ^ ((1 : ℝ) + ε) := by
              gcongr
      _ = ((2 : ℝ) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|) * r ^ ((1 : ℝ) + ε) := by
              ring
  have hfrac2 :
      ((2 * r) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|) / Real.log 2
        ≤ (((2 : ℝ) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|) / Real.log 2) * r ^ ((1 : ℝ) + ε) := by
    have := div_le_div_of_nonneg_right hnum2 (le_of_lt hlog2_pos)
    simpa [div_mul_eq_mul_div, mul_assoc] using this
  have := le_trans hcount' hfrac2
  simpa [C, mul_assoc] using this

/-- **General-order multiplicity-weighted zero counting, clean form.**

The `order f ≤ lam` analogue of `sum_multiplicity_zeros_le_rpow`, giving a
constant bound of the form `C * r ^ (lam + ε)` for `r` large. Obtained by
composing the general-order Jensen bound with a rewrite to absorb the
`log ‖f 0‖` term.

This is Step 1 of `tmp-conway/HadamardGeneral.lean` (used to derive
summability of `∑ mult(ρ) / ‖ρ‖^(p+1)` under order `≤ lam`). -/
theorem sum_multiplicity_zeros_le_rpow_of_order_le
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (hf_finite : hasFiniteOrder f) {lam : ℝ} (hf_order_le : order f ≤ lam)
    (hlam_nonneg : 0 ≤ lam)
    (Z : ZeroSet f) [Countable Z.Zero]
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0) :
    ∀ ε : ℝ, 0 < ε →
      ∃ R₀ C : ℝ, 0 ≤ C ∧
        ∀ r : ℝ, R₀ ≤ r →
          (∑ᶠ ρ : Z.Zero, if ‖Z.z ρ‖ ≤ r then (analyticOrderNatAt f (Z.z ρ) : ℝ) else 0) ≤
            C * r ^ (lam + ε) := by
  intro ε hε
  obtain ⟨R₁, hR₁⟩ :=
    OrderOne.sum_multiplicity_zeros_le_of_order_le (f := f) hf_entire hf_finite hf_order_le Z
      h_zeros_only h_inj h_z_ne_zero ε hε
  have hlog2_pos : 0 < Real.log 2 := by
    simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2)
  let C : ℝ := ((2 : ℝ) ^ (lam + ε) + |Real.log ‖f 0‖|) / Real.log 2
  refine ⟨max R₁ 1, C, ?_, ?_⟩
  · have hC_nonneg : 0 ≤ (2 : ℝ) ^ (lam + ε) + |Real.log ‖f 0‖| := by
      have hpow : 0 ≤ (2 : ℝ) ^ (lam + ε) := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
      exact add_nonneg hpow (abs_nonneg _)
    exact div_nonneg hC_nonneg (le_of_lt hlog2_pos)
  intro r hr
  have hr_ge_R1 : R₁ ≤ r := le_trans (le_max_left _ _) hr
  have hr_ge1 : (1 : ℝ) ≤ r := le_trans (le_max_right _ _) hr
  have hr_nonneg : 0 ≤ r := le_trans (by norm_num : (0 : ℝ) ≤ 1) hr_ge1
  have hcount := hR₁ r hr_ge_R1
  have hnum_le :
      (2 * r) ^ (lam + ε) - Real.log ‖f 0‖
        ≤ (2 * r) ^ (lam + ε) + |Real.log ‖f 0‖| := by
    have : -Real.log ‖f 0‖ ≤ |Real.log ‖f 0‖| := by
      simpa using (neg_le_abs (Real.log ‖f 0‖))
    linarith
  have hcount' :
      (∑ᶠ ρ : Z.Zero, if ‖Z.z ρ‖ ≤ r then (analyticOrderNatAt f (Z.z ρ) : ℝ) else 0)
        ≤ ((2 * r) ^ (lam + ε) + |Real.log ‖f 0‖|) / Real.log 2 := by
    have hfrac_le :
        ((2 * r) ^ (lam + ε) - Real.log ‖f 0‖) / Real.log 2
          ≤ ((2 * r) ^ (lam + ε) + |Real.log ‖f 0‖|) / Real.log 2 :=
      div_le_div_of_nonneg_right hnum_le (le_of_lt hlog2_pos)
    exact le_trans hcount hfrac_le
  have hlam_eps_nonneg : (0 : ℝ) ≤ lam + ε := add_nonneg hlam_nonneg (le_of_lt hε)
  have hrpow_ge1 : (1 : ℝ) ≤ r ^ (lam + ε) :=
    Real.one_le_rpow hr_ge1 hlam_eps_nonneg
  have hmul_rpow :
      (2 * r) ^ (lam + ε) =
        (2 : ℝ) ^ (lam + ε) * r ^ (lam + ε) := by
    simpa using
      (Real.mul_rpow (x := (2 : ℝ)) (y := r) (by norm_num : (0 : ℝ) ≤ (2 : ℝ)) hr_nonneg
        (z := lam + ε))
  have hnum2 :
      (2 * r) ^ (lam + ε) + |Real.log ‖f 0‖|
        ≤ ((2 : ℝ) ^ (lam + ε) + |Real.log ‖f 0‖|) * r ^ (lam + ε) := by
    have habs_mul : |Real.log ‖f 0‖| ≤ |Real.log ‖f 0‖| * r ^ (lam + ε) :=
      le_mul_of_one_le_right (abs_nonneg _) hrpow_ge1
    calc
      (2 * r) ^ (lam + ε) + |Real.log ‖f 0‖|
          = (2 : ℝ) ^ (lam + ε) * r ^ (lam + ε) + |Real.log ‖f 0‖| := by
              simp [hmul_rpow]
      _ ≤ (2 : ℝ) ^ (lam + ε) * r ^ (lam + ε) + |Real.log ‖f 0‖| * r ^ (lam + ε) := by
              gcongr
      _ = ((2 : ℝ) ^ (lam + ε) + |Real.log ‖f 0‖|) * r ^ (lam + ε) := by
              ring
  have hfrac2 :
      ((2 * r) ^ (lam + ε) + |Real.log ‖f 0‖|) / Real.log 2
        ≤ (((2 : ℝ) ^ (lam + ε) + |Real.log ‖f 0‖|) / Real.log 2) * r ^ (lam + ε) := by
    have := div_le_div_of_nonneg_right hnum2 (le_of_lt hlog2_pos)
    simpa [div_mul_eq_mul_div, mul_assoc] using this
  have := le_trans hcount' hfrac2
  simpa [C, mul_assoc] using this

theorem sum_multiplicity_zeros_le_rpow
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (hf_finite : hasFiniteOrder f) (hf_order_le : order f ≤ 1)
    (Z : ZeroSet f) [Countable Z.Zero]
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0) :
    ∀ ε : ℝ, 0 < ε →
      ∃ R₀ C : ℝ, 0 ≤ C ∧
        ∀ r : ℝ, R₀ ≤ r →
          (∑ᶠ ρ : Z.Zero, if ‖Z.z ρ‖ ≤ r then (analyticOrderNatAt f (Z.z ρ) : ℝ) else 0) ≤
            C * r ^ ((1 : ℝ) + ε) := by
  intro ε hε
  obtain ⟨R₁, hR₁⟩ :=
    OrderOne.sum_multiplicity_zeros_le_of_order_le_one (f := f) hf_entire hf_finite hf_order_le Z
      h_zeros_only h_inj h_z_ne_zero ε hε
  have hlog2_pos : 0 < Real.log 2 := by
    simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2)
  let C : ℝ := ((2 : ℝ) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|) / Real.log 2
  refine ⟨max R₁ 1, C, ?_, ?_⟩
  · have hC_nonneg : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖| := by
      have hpow : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) + ε) := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
      exact add_nonneg hpow (abs_nonneg _)
    exact div_nonneg hC_nonneg (le_of_lt hlog2_pos)
  intro r hr
  have hr_ge_R1 : R₁ ≤ r := le_trans (le_max_left _ _) hr
  have hr_ge1 : (1 : ℝ) ≤ r := le_trans (le_max_right _ _) hr
  have hr_nonneg : 0 ≤ r := le_trans (by norm_num : (0 : ℝ) ≤ 1) hr_ge1
  have hcount := hR₁ r hr_ge_R1
  -- First, replace `-log ‖f 0‖` by `|log ‖f 0‖|`.
  have hnum_le :
      (2 * r) ^ ((1 : ℝ) + ε) - Real.log ‖f 0‖
        ≤ (2 * r) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖| := by
    have : -Real.log ‖f 0‖ ≤ |Real.log ‖f 0‖| := by
      simpa using (neg_le_abs (Real.log ‖f 0‖))
    linarith
  have hcount' :
      (∑ᶠ ρ : Z.Zero, if ‖Z.z ρ‖ ≤ r then (analyticOrderNatAt f (Z.z ρ) : ℝ) else 0)
        ≤ ((2 * r) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|) / Real.log 2 := by
    have hfrac_le :
        ((2 * r) ^ ((1 : ℝ) + ε) - Real.log ‖f 0‖) / Real.log 2
          ≤ ((2 * r) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|) / Real.log 2 :=
      div_le_div_of_nonneg_right hnum_le (le_of_lt hlog2_pos)
    exact le_trans hcount hfrac_le
  -- Rewrite `(2*r)^(1+ε)` and absorb the constant using `r^(1+ε) ≥ 1`.
  have hrpow_ge1 : (1 : ℝ) ≤ r ^ ((1 : ℝ) + ε) :=
    Real.one_le_rpow hr_ge1 (by linarith [hε] : (0 : ℝ) ≤ (1 : ℝ) + ε)
  have hmul_rpow :
      (2 * r) ^ ((1 : ℝ) + ε) =
        (2 : ℝ) ^ ((1 : ℝ) + ε) * r ^ ((1 : ℝ) + ε) := by
    simpa using
      (Real.mul_rpow (x := (2 : ℝ)) (y := r) (by norm_num : (0 : ℝ) ≤ (2 : ℝ)) hr_nonneg
        (z := (1 : ℝ) + ε))
  have hnum2 :
      (2 * r) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|
        ≤ ((2 : ℝ) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|) * r ^ ((1 : ℝ) + ε) := by
    have habs_mul : |Real.log ‖f 0‖| ≤ |Real.log ‖f 0‖| * r ^ ((1 : ℝ) + ε) :=
      le_mul_of_one_le_right (abs_nonneg _) hrpow_ge1
    calc
      (2 * r) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|
          = (2 : ℝ) ^ ((1 : ℝ) + ε) * r ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖| := by
              simp [hmul_rpow]
      _ ≤ (2 : ℝ) ^ ((1 : ℝ) + ε) * r ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖| * r ^ ((1 : ℝ) + ε) := by
              gcongr
      _ = ((2 : ℝ) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|) * r ^ ((1 : ℝ) + ε) := by
              ring
  have hfrac2 :
      ((2 * r) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|) / Real.log 2
        ≤ (((2 : ℝ) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|) / Real.log 2) * r ^ ((1 : ℝ) + ε) := by
    have := div_le_div_of_nonneg_right hnum2 (le_of_lt hlog2_pos)
    simpa [div_mul_eq_mul_div, mul_assoc] using this
  have := le_trans hcount' hfrac2
  simpa [C, mul_assoc] using this

/-! ### A dyadic `O(r^ε)` bound for `∑_{‖ρ‖ ≤ r} 1/‖ρ‖` (finite sums) -/

theorem sum_invNorm_le_rpow_of_two_pow
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (hf_finite : hasFiniteOrder f) (hf_order_le : order f ≤ 1)
    (Z : ZeroSet f) [Countable Z.Zero]
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0)
    (h_simple : ∀ ρ : Z.Zero, deriv f (Z.z ρ) ≠ 0)
    (h_summable : Summable (fun ρ : Z.Zero => (1 : ℝ) / ‖Z.z ρ‖ ^ 2)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ n₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ n : ℕ, n₀ ≤ n →
          (∑ ρ ∈ zerosBallFinset Z h_z_ne_zero h_summable n, (1 : ℝ) / ‖Z.z ρ‖)
            ≤ C * ((2 : ℝ) ^ n) ^ ε := by
  classical
  intro ε hε
  -- Zero-counting bound `N(r) = O(r^(1+ε))`.
  obtain ⟨Rcount, Ccount, hCcount_nonneg, hN_le⟩ :=
    ncard_zeros_le_rpow (f := f) hf_entire hf_finite hf_order_le Z h_zeros_only h_inj h_z_ne_zero
      h_simple ε hε
  -- Choose `n₀` so that `max Rcount 1 ≤ 2^n₀`.
  let R0 : ℝ := max Rcount 1
  have hR0_le : ∃ n₀ : ℕ, R0 ≤ (2 : ℝ) ^ n₀ := by
    have h : ∃ n : ℕ, R0 < (2 : ℝ) ^ n := by
      simpa using (pow_unbounded_of_one_lt R0 (by norm_num : (1 : ℝ) < 2))
    refine ⟨Nat.find h, le_of_lt (Nat.find_spec h)⟩
  obtain ⟨n₀, hn₀⟩ := hR0_le
  have hRcount_le : Rcount ≤ (2 : ℝ) ^ n₀ := le_trans (le_max_left _ _) hn₀
  have hone_le : (1 : ℝ) ≤ (2 : ℝ) ^ n₀ := le_trans (le_max_right _ _) hn₀
  -- Define the constant `C`.
  let smallSum : ℝ := ∑ ρ ∈ zerosBallFinset Z h_z_ne_zero h_summable n₀, (1 : ℝ) / ‖Z.z ρ‖
  have hsmallSum_nonneg : 0 ≤ smallSum := by
    refine Finset.sum_nonneg ?_
    intro ρ hρ
    positivity
  let q : ℝ := (2 : ℝ) ^ ε
  have hq_pos : 0 < q := by
    simpa [q] using (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) ε)
  have hq_gt1 : 1 < q := by
    simpa [q] using (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hε)
  have hq_sub_pos : 0 < q - 1 := sub_pos.mpr hq_gt1
  have hq_sub_ne : q - 1 ≠ 0 := ne_of_gt hq_sub_pos
  let Ctail : ℝ := (2 * Ccount) * q / (q - 1)
  let C : ℝ := smallSum + Ctail
  have hC_nonneg : 0 ≤ C := by
    have hCtail_nonneg : 0 ≤ Ctail := by
      have : 0 ≤ (2 * Ccount) * q := by
        have : 0 ≤ (2 : ℝ) * Ccount := mul_nonneg (by norm_num) hCcount_nonneg
        exact mul_nonneg this (le_of_lt hq_pos)
      exact div_nonneg this (le_of_lt hq_sub_pos)
    exact add_nonneg hsmallSum_nonneg hCtail_nonneg
  refine ⟨n₀, C, hC_nonneg, ?_⟩
  intro n hn
  have hn_eq : n₀ + (n - n₀) = n := Nat.add_sub_of_le hn
  -- Induction on the offset `m = n - n₀`.
  have hmain :
      ∀ m : ℕ,
        (∑ ρ ∈ zerosBallFinset Z h_z_ne_zero h_summable (n₀ + m), (1 : ℝ) / ‖Z.z ρ‖)
          ≤ C * ((2 : ℝ) ^ (n₀ + m)) ^ ε := by
    intro m
    induction m with
    | zero =>
        -- Base case: `n = n₀`.
        have hpow_ge1 : (1 : ℝ) ≤ ((2 : ℝ) ^ n₀) ^ ε :=
          Real.one_le_rpow hone_le (le_of_lt hε)
        have hsmall_le_C : smallSum ≤ C := by
          have : 0 ≤ Ctail := by
            have : 0 ≤ (2 * Ccount) * q := by
              have : 0 ≤ (2 : ℝ) * Ccount := mul_nonneg (by norm_num) hCcount_nonneg
              exact mul_nonneg this (le_of_lt hq_pos)
            exact div_nonneg this (le_of_lt hq_sub_pos)
          simpa [C] using (le_add_of_nonneg_right (a := smallSum) (b := Ctail) this)
        -- `smallSum = sum over the ball at radius 2^n₀`.
        have hsmall_eq :
            (∑ ρ ∈ zerosBallFinset Z h_z_ne_zero h_summable n₀, ‖Z.z ρ‖⁻¹) = smallSum := by
          simp [smallSum, one_div]
        -- Conclude by `smallSum ≤ C * ((2^n₀)^ε)` since `((2^n₀)^ε) ≥ 1`.
        have : smallSum ≤ C * ((2 : ℝ) ^ n₀) ^ ε := by
          have : smallSum ≤ C := hsmall_le_C
          have : C ≤ C * ((2 : ℝ) ^ n₀) ^ ε := by
            exact le_mul_of_one_le_right hC_nonneg hpow_ge1
          exact le_trans hsmall_le_C this
        simpa [hsmall_eq] using this
    | succ m ih =>
        -- Step: `n := n₀ + m`.
        set k : ℕ := n₀ + m
        have hk_ge : n₀ ≤ k := Nat.le_add_right n₀ m
        let ball : ℕ → Finset Z.Zero := fun t => zerosBallFinset Z h_z_ne_zero h_summable t
        let fterm : Z.Zero → ℝ := fun ρ => (1 : ℝ) / ‖Z.z ρ‖
        have hsub : ball k ⊆ ball (k + 1) := by
          intro ρ hρ
          have hnorm : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ k :=
            (mem_zerosBallFinset_iff Z h_z_ne_zero h_summable k ρ).1 hρ
          have hk_le : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) :=
            pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ k)
          exact
            (mem_zerosBallFinset_iff Z h_z_ne_zero h_summable (k + 1) ρ).2
              (le_trans hnorm hk_le)
        have hdecomp :
            (∑ ρ ∈ ball (k + 1), fterm ρ) =
              (∑ ρ ∈ ball (k + 1) \ ball k, fterm ρ) + (∑ ρ ∈ ball k, fterm ρ) := by
          simpa [ball, fterm] using
            (Finset.sum_sdiff (s₁ := ball k) (s₂ := ball (k + 1)) (f := fterm) hsub).symm
        -- Bound the increment `ball (k+1) \ ball k`.
        have hdiff :
            (∑ ρ ∈ ball (k + 1) \ ball k, fterm ρ)
              ≤ (2 * Ccount) * ((2 : ℝ) ^ (k + 1)) ^ ε := by
          let diff : Finset Z.Zero := ball (k + 1) \ ball k
          have hterm_le : ∀ ρ, ρ ∈ diff → fterm ρ ≤ (1 : ℝ) / (2 : ℝ) ^ k := by
            intro ρ hρ
            have hρ' : ρ ∈ ball (k + 1) ∧ ρ ∉ ball k := by
              simpa [diff] using (Finset.mem_sdiff.1 hρ)
            have hnot : ¬ ‖Z.z ρ‖ ≤ (2 : ℝ) ^ k := by
              intro hle
              have : ρ ∈ ball k := (mem_zerosBallFinset_iff Z h_z_ne_zero h_summable k ρ).2 hle
              exact hρ'.2 this
            have hk_pos : 0 < (2 : ℝ) ^ k := by positivity
            have hk_le_norm : (2 : ℝ) ^ k ≤ ‖Z.z ρ‖ := le_of_lt (lt_of_not_ge hnot)
            have := one_div_le_one_div_of_le hk_pos hk_le_norm
            simpa [fterm] using this
          have hsum_le_card :
              (∑ ρ ∈ diff, fterm ρ) ≤ (diff.card : ℝ) * ((1 : ℝ) / (2 : ℝ) ^ k) := by
            have hsum_le : (∑ ρ ∈ diff, fterm ρ) ≤ ∑ ρ ∈ diff, (1 : ℝ) / (2 : ℝ) ^ k :=
              Finset.sum_le_sum hterm_le
            calc
              (∑ ρ ∈ diff, fterm ρ) ≤ ∑ ρ ∈ diff, (1 : ℝ) / (2 : ℝ) ^ k := hsum_le
              _ = (diff.card : ℝ) * ((1 : ℝ) / (2 : ℝ) ^ k) := by
                    simp
          have hball_card : ((ball (k + 1)).card : ℝ) =
              (({ρ : Z.Zero | ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1)} : Set Z.Zero).ncard : ℝ) := by
            exact_mod_cast (card_zerosBallFinset Z h_z_ne_zero h_summable (n := k + 1))
          have hRcount_le' : Rcount ≤ (2 : ℝ) ^ (k + 1) := by
            have hpow : (2 : ℝ) ^ n₀ ≤ (2 : ℝ) ^ (k + 1) :=
              pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_trans hk_ge (Nat.le_succ _))
            exact le_trans hRcount_le hpow
          have hcount_ball :
              (({ρ : Z.Zero | ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1)} : Set Z.Zero).ncard : ℝ)
                ≤ Ccount * ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + ε) :=
            hN_le ((2 : ℝ) ^ (k + 1)) hRcount_le'
          have hdiff_card_le :
              (diff.card : ℝ) ≤ Ccount * ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + ε) := by
            have hcard_le_ball : (diff.card : ℝ) ≤ ((ball (k + 1)).card : ℝ) := by
              exact_mod_cast
                (Finset.card_le_card (show diff ⊆ ball (k + 1) from Finset.sdiff_subset))
            have hball_le :
                ((ball (k + 1)).card : ℝ) ≤ Ccount * ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + ε) := by
              simpa [hball_card] using hcount_ball
            exact le_trans hcard_le_ball hball_le
          have hk_nonneg : 0 ≤ (1 : ℝ) / (2 : ℝ) ^ k := by positivity
          have hk_ne : (2 : ℝ) ^ k ≠ 0 := by
            have : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
            exact ne_of_gt this
          have hk1_pos : 0 < (2 : ℝ) ^ (k + 1) := by positivity
          have hrewrite :
              Ccount * ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + ε) * ((1 : ℝ) / (2 : ℝ) ^ k)
                = (2 * Ccount) * ((2 : ℝ) ^ (k + 1)) ^ ε := by
            -- Expand `r^(1+ε)` and cancel `2^k`.
            calc
              Ccount * ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + ε) * ((1 : ℝ) / (2 : ℝ) ^ k)
                  =
                    Ccount * (((2 : ℝ) ^ (k + 1)) * ((2 : ℝ) ^ (k + 1)) ^ ε) *
                      ((1 : ℝ) / (2 : ℝ) ^ k) := by
                      simp [Real.rpow_add hk1_pos, Real.rpow_one, mul_assoc]
              _ = Ccount * ((2 : ℝ) ^ (k + 1)) ^ ε * (((2 : ℝ) ^ (k + 1)) / ((2 : ℝ) ^ k)) := by
                      field_simp [hk_ne]
              _ = Ccount * ((2 : ℝ) ^ (k + 1)) ^ ε * (2 : ℝ) := by
                      have : ((2 : ℝ) ^ (k + 1)) / ((2 : ℝ) ^ k) = (2 : ℝ) := by
                        field_simp [hk_ne]
                        simp [pow_succ]
                      simp [this]
              _ = (2 * Ccount) * ((2 : ℝ) ^ (k + 1)) ^ ε := by ring
          -- Assemble.
          have hcalc :
              (∑ ρ ∈ diff, fterm ρ) ≤ (2 * Ccount) * ((2 : ℝ) ^ (k + 1)) ^ ε := by
            calc
              (∑ ρ ∈ diff, fterm ρ) ≤ (diff.card : ℝ) * ((1 : ℝ) / (2 : ℝ) ^ k) := hsum_le_card
              _ ≤ (Ccount * ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + ε)) * ((1 : ℝ) / (2 : ℝ) ^ k) := by
                    exact mul_le_mul_of_nonneg_right hdiff_card_le hk_nonneg
              _ = (2 * Ccount) * ((2 : ℝ) ^ (k + 1)) ^ ε := hrewrite
          simpa [diff] using hcalc
        -- Inductive inequality.
        have ih' : (∑ ρ ∈ ball k, fterm ρ) ≤ C * ((2 : ℝ) ^ k) ^ ε := by
          simpa [ball, fterm, k] using ih
        have hk_rpow : ((2 : ℝ) ^ (k + 1)) ^ ε = q * ((2 : ℝ) ^ k) ^ ε := by
          have hpos : 0 ≤ (2 : ℝ) ^ k := by positivity
          have : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k * (2 : ℝ) := by
            simp [pow_succ]
          simpa [q, this, mul_assoc, mul_left_comm, mul_comm] using
            (Real.mul_rpow
              (x := (2 : ℝ) ^ k) (y := (2 : ℝ))
              hpos (by positivity : 0 ≤ (2 : ℝ)) (z := ε))
        have hC_rec : (2 * Ccount) * q + C ≤ C * q := by
          have hCtail_le_C : Ctail ≤ C := by
            simpa [C] using (le_add_of_nonneg_left (a := Ctail) (b := smallSum) hsmallSum_nonneg)
          have hmul_le : Ctail * (q - 1) ≤ C * (q - 1) :=
            mul_le_mul_of_nonneg_right hCtail_le_C (le_of_lt hq_sub_pos)
          have hmul_eq : Ctail * (q - 1) = (2 * Ccount) * q := by
            dsimp [Ctail]
            field_simp [hq_sub_ne]
          have hmain : (2 * Ccount) * q ≤ C * (q - 1) := by
            simpa [hmul_eq] using hmul_le
          have hmain_add : (2 * Ccount) * q + C ≤ C * (q - 1) + C := by
            simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hmain C
          calc
            (2 * Ccount) * q + C ≤ C * (q - 1) + C := hmain_add
            _ = C * q := by ring
        -- Finish the step.
        calc
          (∑ ρ ∈ ball (k + 1), fterm ρ)
              = (∑ ρ ∈ ball (k + 1) \ ball k, fterm ρ) + (∑ ρ ∈ ball k, fterm ρ) := hdecomp
          _ ≤ (2 * Ccount) * ((2 : ℝ) ^ (k + 1)) ^ ε + C * ((2 : ℝ) ^ k) ^ ε := by
                gcongr
          _ = ((2 * Ccount) * q + C) * ((2 : ℝ) ^ k) ^ ε := by
                simp [hk_rpow, mul_add, mul_assoc, mul_comm]
          _ ≤ (C * q) * ((2 : ℝ) ^ k) ^ ε := by
                gcongr
          _ = C * ((2 : ℝ) ^ (k + 1)) ^ ε := by
                simp [hk_rpow, mul_assoc]
  -- Specialize to `m = n - n₀`.
  simpa [hn_eq] using hmain (n - n₀)

/-! ### Dyadic tail decay for `∑ 1/‖Z.z ρ‖²` -/

private lemma cofinal_zerosBallFinset
    {f : ℂ → ℂ} (Z : ZeroSet f)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0)
    (h_summable : Summable (fun ρ : Z.Zero => (1 : ℝ) / ‖Z.z ρ‖ ^ 2)) :
    ∀ t : Finset Z.Zero, ∃ n : ℕ, t ⊆ zerosBallFinset Z h_z_ne_zero h_summable n := by
  classical
  intro t
  by_cases ht : t = ∅
  · subst ht
    refine ⟨0, by simp⟩
  · have ht_ne : t.Nonempty := Finset.nonempty_iff_ne_empty.2 ht
    let t' : Finset ℝ := t.image (fun ρ : Z.Zero => ‖Z.z ρ‖)
    have ht'_ne : t'.Nonempty := ht_ne.image _
    let Rmax : ℝ := t'.max' ht'_ne
    have hRmax : ∀ ρ : Z.Zero, ρ ∈ t → ‖Z.z ρ‖ ≤ Rmax := by
      intro ρ hρ
      have : ‖Z.z ρ‖ ∈ t' := Finset.mem_image_of_mem _ hρ
      exact Finset.le_max' t' (‖Z.z ρ‖) this
    have hpow : ∃ n : ℕ, Rmax < (2 : ℝ) ^ n := by
      simpa using (pow_unbounded_of_one_lt Rmax (by norm_num : (1 : ℝ) < 2))
    refine ⟨Nat.find hpow, ?_⟩
    intro ρ hρ
    have hρ_le : ‖Z.z ρ‖ ≤ Rmax := hRmax ρ hρ
    have hρ_lt : ‖Z.z ρ‖ < (2 : ℝ) ^ (Nat.find hpow) := lt_of_le_of_lt hρ_le (Nat.find_spec hpow)
    exact (mem_zerosBallFinset_iff Z h_z_ne_zero h_summable _ ρ).2 (le_of_lt hρ_lt)

theorem tsum_invNorm_sq_tail_le_rpow_of_two_pow
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (hf_finite : hasFiniteOrder f) (hf_order_le : order f ≤ 1)
    (Z : ZeroSet f) [Countable Z.Zero]
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0)
    (h_simple : ∀ ρ : Z.Zero, deriv f (Z.z ρ) ≠ 0)
    (h_summable : Summable (fun ρ : Z.Zero => (1 : ℝ) / ‖Z.z ρ‖ ^ 2)) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ n₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ n : ℕ, n₀ ≤ n →
          (∑' ρ : ({ρ : Z.Zero | (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖} : Set Z.Zero),
              (1 : ℝ) / ‖Z.z ρ.val‖ ^ 2)
            ≤ C * ((2 : ℝ) ^ n) ^ (ε - 1) := by
  classical
  intro ε hε0 hε1
  -- Zero-counting bound `N(r) = O(r^(1+ε))`.
  obtain ⟨Rcount, Ccount, hCcount_nonneg, hN_le⟩ :=
    ncard_zeros_le_rpow (f := f) hf_entire hf_finite hf_order_le Z h_zeros_only h_inj h_z_ne_zero
      h_simple ε hε0
  -- Choose `n₀` so that `Rcount ≤ 2^n₀`.
  let R0 : ℝ := max Rcount 1
  have hR0_le : ∃ n₀ : ℕ, R0 ≤ (2 : ℝ) ^ n₀ := by
    have h : ∃ n : ℕ, R0 < (2 : ℝ) ^ n := by
      simpa using (pow_unbounded_of_one_lt R0 (by norm_num : (1 : ℝ) < 2))
    refine ⟨Nat.find h, le_of_lt (Nat.find_spec h)⟩
  obtain ⟨n₀, hn₀⟩ := hR0_le
  have hRcount_le_pow : Rcount ≤ (2 : ℝ) ^ n₀ := le_trans (le_max_left _ _) hn₀
  -- Geometric ratio `q = 2^(ε-1)` with `0 < q < 1` since `ε < 1`.
  let q : ℝ := (2 : ℝ) ^ (ε - 1)
  have hq_pos : 0 < q := by
    simpa [q] using Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (ε - 1)
  have hq_lt_one : q < 1 := by
    have hneg : ε - 1 < 0 := by linarith
    simpa [q] using Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) hneg
  -- Constant controlling the geometric tail.
  let C : ℝ := (2 : ℝ) ^ ((1 : ℝ) + ε) * Ccount * q / (1 - q)
  have hC_nonneg : 0 ≤ C := by
    have hpow_nonneg : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) + ε) :=
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
    have hq_nonneg : 0 ≤ q := le_of_lt hq_pos
    have hden_pos : 0 < (1 - q) := sub_pos.mpr hq_lt_one
    have hnum_nonneg : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) + ε) * Ccount * q :=
      mul_nonneg (mul_nonneg hpow_nonneg hCcount_nonneg) hq_nonneg
    exact div_nonneg hnum_nonneg (le_of_lt hden_pos)
  refine ⟨n₀, C, hC_nonneg, ?_⟩
  intro n hn
  -- Work with the indicator function on `Z.Zero`.
  let g : Z.Zero → ℝ := fun ρ =>
    if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0
  have hg_nonneg : ∀ ρ : Z.Zero, 0 ≤ g ρ := by
    intro ρ
    by_cases hρ : (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖
    · have : 0 ≤ (1 : ℝ) / ‖Z.z ρ‖ ^ 2 := by
        have h1 : 0 ≤ (1 : ℝ) := by norm_num
        have hden : 0 ≤ ‖Z.z ρ‖ ^ 2 := sq_nonneg _
        exact div_nonneg h1 hden
      simp [g, hρ]
    · simp [g, hρ]
  -- Bound dyadic-ball partial sums.
  have hball :
      ∀ m : ℕ,
        (∑ ρ ∈ zerosBallFinset Z h_z_ne_zero h_summable m, g ρ) ≤
          C * ((2 : ℝ) ^ n) ^ (ε - 1) := by
    classical
    intro m
    by_cases hm : m ≤ n + 1
    · have hsum0 :
          (∑ ρ ∈ zerosBallFinset Z h_z_ne_zero h_summable m, g ρ) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro ρ hρ
        have hnorm : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ m :=
          (mem_zerosBallFinset_iff Z h_z_ne_zero h_summable m ρ).1 hρ
        have hpow : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ (n + 1) :=
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm
        have : ¬ (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ := not_lt_of_ge (le_trans hnorm hpow)
        simp [g, this]
      have hrhs_nonneg : 0 ≤ C * ((2 : ℝ) ^ n) ^ (ε - 1) := by
        have : 0 ≤ ((2 : ℝ) ^ n) ^ (ε - 1) :=
          Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n) _
        exact mul_nonneg hC_nonneg this
      simpa [hsum0] using hrhs_nonneg
    · have hm_ge : n + 1 < m := lt_of_not_ge hm
      let ball : ℕ → Finset Z.Zero := fun t => zerosBallFinset Z h_z_ne_zero h_summable t
      have hsub_ball : ∀ k : ℕ, ball k ⊆ ball (k + 1) := by
        intro k ρ hρ
        have hnorm : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ k :=
          (mem_zerosBallFinset_iff Z h_z_ne_zero h_summable k ρ).1 hρ
        have hk_le : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) :=
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ k)
        exact
          (mem_zerosBallFinset_iff Z h_z_ne_zero h_summable (k + 1) ρ).2
            (le_trans hnorm hk_le)
      have hshell :
          ∀ k : ℕ, n + 1 ≤ k →
            (∑ ρ ∈ ball (k + 1) \ ball k, g ρ)
              ≤ (2 : ℝ) ^ ((1 : ℝ) + ε) * Ccount * q ^ k := by
        intro k hk
        let diff : Finset Z.Zero := ball (k + 1) \ ball k
        have hk_pow_le : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ k :=
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
        have hdiff_simp :
            (∑ ρ ∈ diff, g ρ) = ∑ ρ ∈ diff, (1 : ℝ) / ‖Z.z ρ‖ ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro ρ hρ
          have hnot : ¬ ‖Z.z ρ‖ ≤ (2 : ℝ) ^ k := by
            intro hle
            have : ρ ∈ ball k :=
              (mem_zerosBallFinset_iff Z h_z_ne_zero h_summable k ρ).2 hle
            exact (Finset.mem_sdiff.1 hρ).2 this
          have hlt : (2 : ℝ) ^ k < ‖Z.z ρ‖ := lt_of_not_ge hnot
          have hcond : (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ :=
            lt_of_lt_of_le (hk_pow_le.trans_lt hlt) (le_rfl)
          simp [g, hcond]
        have hterm_le :
            ∀ ρ, ρ ∈ diff → (1 : ℝ) / ‖Z.z ρ‖ ^ 2 ≤ (1 : ℝ) / ((2 : ℝ) ^ k) ^ 2 := by
          intro ρ hρ
          have hnot : ¬ ‖Z.z ρ‖ ≤ (2 : ℝ) ^ k := by
            intro hle
            have : ρ ∈ ball k :=
              (mem_zerosBallFinset_iff Z h_z_ne_zero h_summable k ρ).2 hle
            exact (Finset.mem_sdiff.1 hρ).2 this
          have hk_le_norm : (2 : ℝ) ^ k ≤ ‖Z.z ρ‖ := le_of_lt (lt_of_not_ge hnot)
          have hk2_pos : 0 < ((2 : ℝ) ^ k) ^ 2 := by positivity
          have hk2_le : ((2 : ℝ) ^ k) ^ 2 ≤ ‖Z.z ρ‖ ^ 2 :=
            pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k) hk_le_norm 2
          simpa [one_div, inv_pow] using (one_div_le_one_div_of_le hk2_pos hk2_le)
        have hsum_le_card :
            (∑ ρ ∈ diff, (1 : ℝ) / ‖Z.z ρ‖ ^ 2)
              ≤ (diff.card : ℝ) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2) := by
          have hsum_le :
              (∑ ρ ∈ diff, (1 : ℝ) / ‖Z.z ρ‖ ^ 2)
                ≤ ∑ ρ ∈ diff, (1 : ℝ) / ((2 : ℝ) ^ k) ^ 2 :=
            Finset.sum_le_sum hterm_le
          calc
            (∑ ρ ∈ diff, (1 : ℝ) / ‖Z.z ρ‖ ^ 2)
                ≤ ∑ ρ ∈ diff, (1 : ℝ) / ((2 : ℝ) ^ k) ^ 2 := hsum_le
            _ = (diff.card : ℝ) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2) := by simp
        have hRcount_le : Rcount ≤ (2 : ℝ) ^ (k + 1) := by
          have hRcount_le_R0 : Rcount ≤ R0 := le_max_left _ _
          have hn0_le_k : n₀ ≤ k := le_trans hn (le_trans (Nat.le_succ n) hk)
          have hn0_le_k1 : n₀ ≤ k + 1 := Nat.le_succ_of_le hn0_le_k
          have hpow : (2 : ℝ) ^ n₀ ≤ (2 : ℝ) ^ (k + 1) :=
            pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn0_le_k1
          exact le_trans (le_trans hRcount_le_R0 hn₀) hpow
        have hcount_ball :
            (({ρ : Z.Zero | ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1)} : Set Z.Zero).ncard : ℝ)
              ≤ Ccount * ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + ε) :=
          hN_le ((2 : ℝ) ^ (k + 1)) hRcount_le
        have hcard_ball :
            ((ball (k + 1)).card : ℝ)
              = (({ρ : Z.Zero | ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1)} : Set Z.Zero).ncard : ℝ) := by
          exact_mod_cast (card_zerosBallFinset Z h_z_ne_zero h_summable (n := k + 1))
        have hdiff_card_le :
            (diff.card : ℝ) ≤ Ccount * ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + ε) := by
          have hdiff_card_le_ball : (diff.card : ℝ) ≤ ((ball (k + 1)).card : ℝ) := by
            exact_mod_cast (Finset.card_le_card (Finset.sdiff_subset : diff ⊆ ball (k + 1)))
          have hball_le :
              ((ball (k + 1)).card : ℝ) ≤ Ccount * ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + ε) := by
            simpa [hcard_ball] using hcount_ball
          exact le_trans hdiff_card_le_ball hball_le
        have hqk : q ^ k = ((2 : ℝ) ^ k) ^ (ε - 1) := by
          simpa [q] using
            (Real.rpow_pow_comm (x := (2 : ℝ)) (hx := by positivity) (ε - 1) k)
        have hdiv :
            ((2 : ℝ) ^ k) ^ (ε - 1)
              = ((2 : ℝ) ^ k) ^ ((1 : ℝ) + ε) / ((2 : ℝ) ^ k) ^ (2 : ℕ) := by
          have hk_pos : 0 < (2 : ℝ) ^ k := by positivity
          have hsub : ((1 : ℝ) + ε) - (2 : ℝ) = ε - 1 := by ring
          simpa [hsub, (Real.rpow_natCast ((2 : ℝ) ^ k) 2)] using
            (Real.rpow_sub hk_pos ((1 : ℝ) + ε) (2 : ℝ))
        have hrewrite :
            Ccount * ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + ε) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2)
              = (2 : ℝ) ^ ((1 : ℝ) + ε) * Ccount * q ^ k := by
          have hpow_succ : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k * 2 := by
            simp [pow_succ]
          have hpowk_nonneg : 0 ≤ (2 : ℝ) ^ k := by positivity
          have h2_nonneg : 0 ≤ (2 : ℝ) := by norm_num
          calc
            Ccount * ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + ε) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2)
                = Ccount * (((2 : ℝ) ^ k * 2) ^ ((1 : ℝ) + ε)) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2) := by
                      simp [hpow_succ]
            _ = Ccount * (((2 : ℝ) ^ k) ^ ((1 : ℝ) + ε) * (2 : ℝ) ^ ((1 : ℝ) + ε)) *
                    ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2) := by
                      have hsplit :
                          ((2 : ℝ) ^ k * 2) ^ ((1 : ℝ) + ε)
                            = ((2 : ℝ) ^ k) ^ ((1 : ℝ) + ε) * (2 : ℝ) ^ ((1 : ℝ) + ε) := by
                        simpa using
                          (Real.mul_rpow (x := (2 : ℝ) ^ k) (y := (2 : ℝ)) (z := (1 : ℝ) + ε)
                            hpowk_nonneg h2_nonneg)
                      have hsplit' :
                          ((2 : ℝ) * (2 : ℝ) ^ k) ^ ((1 : ℝ) + ε)
                            = (2 : ℝ) ^ ((1 : ℝ) + ε) * ((2 : ℝ) ^ k) ^ ((1 : ℝ) + ε) := by
                        have h2_nonneg' : 0 ≤ (2 : ℝ) := by norm_num
                        have hpowk_nonneg' : 0 ≤ (2 : ℝ) ^ k := by positivity
                        simpa using
                          (Real.mul_rpow (x := (2 : ℝ)) (y := (2 : ℝ) ^ k) (z := (1 : ℝ) + ε)
                            h2_nonneg' hpowk_nonneg')
                      -- avoid simp-canceling `Ccount`
                      simp [hsplit', mul_assoc, mul_comm,
                        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
            _ = (2 : ℝ) ^ ((1 : ℝ) + ε) * Ccount *
                    (((2 : ℝ) ^ k) ^ ((1 : ℝ) + ε) / ((2 : ℝ) ^ k) ^ (2 : ℕ)) := by
                      -- Rearrange and rewrite `a * (1 / b)` as `a / b`,
                      -- but avoid simp-canceling `Ccount`.
                      simp [div_eq_mul_inv, mul_assoc, mul_comm,
                        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
            _ = (2 : ℝ) ^ ((1 : ℝ) + ε) * Ccount * (((2 : ℝ) ^ k) ^ (ε - 1)) := by
                      -- `x^(ε-1) = x^(1+ε) / x^2`
                      simpa [mul_assoc] using
                        congrArg
                          (fun t => (2 : ℝ) ^ ((1 : ℝ) + ε) * Ccount * t)
                          hdiv.symm
            _ = (2 : ℝ) ^ ((1 : ℝ) + ε) * Ccount * q ^ k := by
                      simp [hqk]
        have hcalc :
            (∑ ρ ∈ diff, g ρ)
              ≤ (2 : ℝ) ^ ((1 : ℝ) + ε) * Ccount * q ^ k := by
          calc
            (∑ ρ ∈ diff, g ρ) = ∑ ρ ∈ diff, (1 : ℝ) / ‖Z.z ρ‖ ^ 2 := hdiff_simp
            _ ≤ (diff.card : ℝ) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2) := hsum_le_card
            _ ≤ (Ccount * ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + ε)) *
                  ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2) := by
                    gcongr
            _ = (2 : ℝ) ^ ((1 : ℝ) + ε) * Ccount * q ^ k := by
                    simpa [mul_assoc, mul_left_comm, mul_comm] using hrewrite
        simpa [diff] using hcalc
      let t : ℕ := m - (n + 1)
      have hm_eq : n + 1 + t = m := Nat.add_sub_of_le (Nat.le_of_lt hm_ge)
      have hind :
          ∀ j : ℕ,
            (∑ ρ ∈ ball (n + 1 + j), g ρ) ≤
              (2 : ℝ) ^ ((1 : ℝ) + ε) * Ccount * (∑ i ∈ Finset.range j, q ^ (n + 1 + i)) := by
        intro j
        induction j with
        | zero =>
            have hsum0 : (∑ ρ ∈ ball (n + 1), g ρ) = 0 := by
              refine Finset.sum_eq_zero ?_
              intro ρ hρ
              have hnorm : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (n + 1) :=
                (mem_zerosBallFinset_iff Z h_z_ne_zero h_summable (n := n + 1) ρ).1 hρ
              have : ¬ (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ := not_lt_of_ge hnorm
              simp [g, this]
            -- `∑ i ∈ range 0, _ = 0`
            simp [ball, hsum0]
        | succ j ih =>
            set k : ℕ := n + 1 + j
            have hk : n + 1 ≤ k := Nat.le_add_right _ _
            have hsub : ball k ⊆ ball (k + 1) := hsub_ball k
            have hdecomp :=
              (Finset.sum_sdiff (s₁ := ball k) (s₂ := ball (k + 1)) (f := g) hsub).symm
            have hshell_le :
                (∑ ρ ∈ ball (k + 1) \ ball k, g ρ)
                  ≤ (2 : ℝ) ^ ((1 : ℝ) + ε) * Ccount * q ^ k := hshell k hk
            have hgeom :
                (∑ i ∈ Finset.range (j + 1), q ^ (n + 1 + i))
                  = (∑ i ∈ Finset.range j, q ^ (n + 1 + i)) + q ^ k := by
              -- `k = n+1+j` is the new last term.
              simpa [k, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                (Finset.sum_range_succ (f := fun i => q ^ (n + 1 + i)) j)
            have ih' : (∑ ρ ∈ ball k, g ρ) ≤
                (2 : ℝ) ^ ((1 : ℝ) + ε) * Ccount * (∑ i ∈ Finset.range j, q ^ (n + 1 + i)) := by
              simpa [k, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih
            calc
              (∑ ρ ∈ ball (k + 1), g ρ)
                  = (∑ ρ ∈ ball (k + 1) \ ball k, g ρ) + (∑ ρ ∈ ball k, g ρ) := by
                        simpa [k, add_assoc, add_comm, add_left_comm] using hdecomp
              _ ≤ (2 : ℝ) ^ ((1 : ℝ) + ε) * Ccount * q ^ k +
                    (2 : ℝ) ^ ((1 : ℝ) + ε) * Ccount * (∑ i ∈ Finset.range j, q ^ (n + 1 + i)) := by
                        gcongr
              _ = (2 : ℝ) ^ ((1 : ℝ) + ε) * Ccount *
                    ((∑ i ∈ Finset.range j, q ^ (n + 1 + i)) + q ^ k) := by
                        -- factor out the common scalar
                        set a : ℝ := (2 : ℝ) ^ ((1 : ℝ) + ε) * Ccount
                        have :
                            a * q ^ k + a * (∑ i ∈ Finset.range j, q ^ (n + 1 + i))
                              = a * ((∑ i ∈ Finset.range j, q ^ (n + 1 + i)) + q ^ k) := by
                          calc
                            a * q ^ k + a * (∑ i ∈ Finset.range j, q ^ (n + 1 + i))
                                = a * (q ^ k + (∑ i ∈ Finset.range j, q ^ (n + 1 + i))) := by
                                      simp [mul_add]
                            _ = a * ((∑ i ∈ Finset.range j, q ^ (n + 1 + i)) + q ^ k) := by
                                      simp [add_comm, add_left_comm]
                        -- unfold `a` and reassociate
                        simpa [a, mul_assoc, mul_left_comm, mul_comm] using this
              _ = (2 : ℝ) ^ ((1 : ℝ) + ε) * Ccount *
                    (∑ i ∈ Finset.range (j + 1), q ^ (n + 1 + i)) := by
                        -- avoid simp-canceling the common factor
                        rw [hgeom.symm]
      have hfinite_le :
          (∑ ρ ∈ ball m, g ρ)
            ≤ (2 : ℝ) ^ ((1 : ℝ) + ε) * Ccount *
                (∑ i ∈ Finset.range t, q ^ (n + 1 + i)) := by
        simpa [hm_eq, ball] using hind t
      have hgeom_le :
          (∑ i ∈ Finset.range t, q ^ (n + 1 + i))
            ≤ (q ^ (n + 1)) * (1 - q)⁻¹ := by
        have hsum : Summable (fun i : ℕ => q ^ i) :=
          summable_geometric_of_lt_one (le_of_lt hq_pos) hq_lt_one
        have hsum' : Summable (fun i : ℕ => q ^ (n + 1) * q ^ i) :=
          hsum.mul_left (q ^ (n + 1))
        have hnonneg : ∀ i : ℕ, 0 ≤ q ^ (n + 1) * q ^ i := by
          intro i
          positivity
        have hle_tsum :
            (∑ i ∈ Finset.range t, q ^ (n + 1) * q ^ i) ≤ ∑' i : ℕ, q ^ (n + 1) * q ^ i := by
          refine
            Summable.sum_le_tsum
              (s := Finset.range t) (f := fun i : ℕ => q ^ (n + 1) * q ^ i) ?_ hsum'
          intro i hi
          exact hnonneg i
        have hpow_add : ∀ i : ℕ, q ^ (n + 1 + i) = q ^ (n + 1) * q ^ i := by
          intro i
          simp [pow_add, mul_assoc]
        have hsum_eq :
            (∑ i ∈ Finset.range t, q ^ (n + 1 + i)) =
              (∑ i ∈ Finset.range t, q ^ (n + 1) * q ^ i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [hpow_add i]
        have htsum_eq :
            (∑' i : ℕ, q ^ (n + 1) * q ^ i) = (q ^ (n + 1)) * (1 - q)⁻¹ := by
          have hgeom0 : (∑' i : ℕ, q ^ i) = (1 - q)⁻¹ :=
            tsum_geometric_of_lt_one (h₁ := le_of_lt hq_pos) (h₂ := hq_lt_one)
          simp [tsum_mul_left, hgeom0]
        have : (∑ i ∈ Finset.range t, q ^ (n + 1 + i))
            ≤ (q ^ (n + 1)) * (1 - q)⁻¹ := by
          exact le_trans (by simpa [hsum_eq] using hle_tsum) (by simp [htsum_eq])
        exact this
      have hq_pow_comm : q ^ n = ((2 : ℝ) ^ n) ^ (ε - 1) := by
        simpa [q] using
          (Real.rpow_pow_comm (x := (2 : ℝ)) (hx := by positivity) (ε - 1) n)
      have hgeom_shift : q ^ (n + 1) = q * ((2 : ℝ) ^ n) ^ (ε - 1) := by
        calc
          q ^ (n + 1) = q ^ n * q := by simp [pow_succ]
          _ = ((2 : ℝ) ^ n) ^ (ε - 1) * q := by simp [hq_pow_comm]
          _ = q * ((2 : ℝ) ^ n) ^ (ε - 1) := by simp [mul_comm]
      have hconst :
          (2 : ℝ) ^ ((1 : ℝ) + ε) * Ccount * ((q ^ (n + 1)) * (1 - q)⁻¹)
            = C * ((2 : ℝ) ^ n) ^ (ε - 1) := by
        simp [C, hgeom_shift, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
      calc
        (∑ ρ ∈ ball m, g ρ)
            ≤ (2 : ℝ) ^ ((1 : ℝ) + ε) * Ccount *
                (∑ i ∈ Finset.range t, q ^ (n + 1 + i)) := hfinite_le
        _ ≤ (2 : ℝ) ^ ((1 : ℝ) + ε) * Ccount * ((q ^ (n + 1)) * (1 - q)⁻¹) := by
              gcongr
        _ = C * ((2 : ℝ) ^ n) ^ (ε - 1) := hconst
  have hfinset :
      ∀ t : Finset Z.Zero,
        (∑ ρ ∈ t, g ρ) ≤ C * ((2 : ℝ) ^ n) ^ (ε - 1) := by
    classical
    intro t
    obtain ⟨m, hm⟩ := cofinal_zerosBallFinset Z h_z_ne_zero h_summable t
    have hle_ball :
        (∑ ρ ∈ t, g ρ) ≤ ∑ ρ ∈ zerosBallFinset Z h_z_ne_zero h_summable m, g ρ := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hm ?_
      intro ρ hρ hρnot
      exact hg_nonneg ρ
    exact le_trans hle_ball (hball m)
  have ht_nonneg : 0 ≤ C * ((2 : ℝ) ^ n) ^ (ε - 1) := by
    have : 0 ≤ ((2 : ℝ) ^ n) ^ (ε - 1) :=
      Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n) _
    exact mul_nonneg hC_nonneg this
  have htsum_g :
      (∑' ρ : Z.Zero, g ρ) ≤ C * ((2 : ℝ) ^ n) ^ (ε - 1) :=
    tsum_le_of_sum_le' ht_nonneg hfinset
  have hsub :
      (∑' ρ : ({ρ : Z.Zero | (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖} : Set Z.Zero),
          (‖Z.z ρ.val‖ ^ 2)⁻¹)
        =
        ∑' ρ : Z.Zero, g ρ := by
    -- rewrite the subtype `tsum` as an indicator `tsum` on `Z.Zero`
    simpa [g, one_div, Set.indicator, Set.mem_ofPred_eq] using
      (tsum_subtype (s := ({ρ : Z.Zero | (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖} : Set Z.Zero))
        (f := fun ρ : Z.Zero => (‖Z.z ρ‖ ^ 2)⁻¹))
  -- work in the `inv` form, then switch back to `1 / _` by simp
  have htail_inv :
      (∑' ρ : ({ρ : Z.Zero | (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖} : Set Z.Zero),
          (‖Z.z ρ.val‖ ^ 2)⁻¹)
        ≤ C * ((2 : ℝ) ^ n) ^ (ε - 1) := by
    rw [hsub]
    exact htsum_g
  simpa [one_div] using htail_inv

  /-
  Obsolete ENNReal/iSup proof attempt (superseded by the proof above).
  -- Zero-counting bound `N(r) = O(r^(1+ε))`.
  obtain ⟨Rcount, Ccount, hCcount_nonneg, hN_le⟩ :=
    ncard_zeros_le_rpow (f := f) hf_entire hf_finite hf_order_le Z h_zeros_only h_inj h_z_ne_zero
      h_simple ε hε0
  -- Choose `n₀` so that `Rcount ≤ 2^(n₀+1)`.
  let R0 : ℝ := max Rcount 1
  have hR0_le : ∃ n₀ : ℕ, R0 ≤ (2 : ℝ) ^ n₀ := by
    have h : ∃ n : ℕ, R0 < (2 : ℝ) ^ n := by
      simpa using (pow_unbounded_of_one_lt R0 (by norm_num : (1 : ℝ) < 2))
    refine ⟨Nat.find h, le_of_lt (Nat.find_spec h)⟩
  obtain ⟨n₀, hn₀⟩ := hR0_le
  have hRcount_le : Rcount ≤ (2 : ℝ) ^ (n₀ + 1) := by
    have hRcount_le_R0 : Rcount ≤ R0 := le_max_left _ _
    have hpow : (2 : ℝ) ^ n₀ ≤ (2 : ℝ) ^ (n₀ + 1) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ _)
    exact le_trans (le_trans hRcount_le_R0 hn₀) hpow
  -- Geometric ratio `q = 2^(ε-1) = 2^(-(1-ε))`, with `0 < q < 1` since `ε < 1`.
  let q : ℝ := (2 : ℝ) ^ (ε - 1)
  have hq_pos : 0 < q := by
    have : 0 < (2 : ℝ) := by norm_num
    simpa [q] using Real.rpow_pos_of_pos this (ε - 1)
  have hq_lt_one : q < 1 := by
    -- Rewrite as an inverse of `2^(1-ε) > 1`.
    have hpos : 0 < (2 : ℝ) ^ (1 - ε) :=
      Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (1 - ε)
    have hone_lt : 1 < (2 : ℝ) ^ (1 - ε) := by
      have : 0 < (1 - ε) := sub_pos.mpr hε1
      simpa using Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) this
    have hq_inv : q = ((2 : ℝ) ^ (1 - ε))⁻¹ := by
      -- `ε - 1 = -(1 - ε)`.
      have : ε - 1 = -(1 - ε) := by ring
      simp [q, this, Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2) (1 - ε)]
    -- `inv` of something `> 1` is `< 1`.
    simpa [hq_inv] using (inv_lt_one_of_one_lt hone_lt)
  -- Define the tail series over the subtype.
  let tailSet : Set Z.Zero := {ρ : Z.Zero | (2 : ℝ) ^ (n₀ + 1) < ‖Z.z ρ‖}
  -- Constant controlling the geometric tail.
  let Cgeo : ℝ := (2 : ℝ) ^ (1 + ε) * Ccount * q / (1 - q)
  have hCgeo_nonneg : 0 ≤ Cgeo := by
    have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (1 + ε) := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
    have hq_nonneg : 0 ≤ q := le_of_lt hq_pos
    have hden_pos : 0 < (1 - q) := sub_pos.mpr hq_lt_one
    have hnum_nonneg : 0 ≤ (2 : ℝ) ^ (1 + ε) * Ccount * q :=
      mul_nonneg (mul_nonneg hpow_nonneg hCcount_nonneg) hq_nonneg
    exact div_nonneg hnum_nonneg (le_of_lt hden_pos)
  refine ⟨n₀, Cgeo, hCgeo_nonneg, ?_⟩
  intro n hn
  -- Rewrite the tail `tsum` as an `iSup` over dyadic ball finsets.
  -- We work in `ENNReal` to use monotone `iSup` formulas.
  have htail_nonneg :
      ∀ ρ : Z.Zero, 0 ≤ (if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0) := by
    intro ρ
    by_cases hρ : (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ <;> simp [hρ, one_div, inv_nonneg, pow_two]
  have htail_summable :
      Summable fun ρ : Z.Zero =>
        (if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0) := by
    -- dominated by the globally summable series `1/‖Z.z ρ‖²`
    refine Summable.of_nonneg_of_le (f := fun ρ : Z.Zero => (1 : ℝ) / ‖Z.z ρ‖ ^ 2)
      (g := fun ρ : Z.Zero =>
        if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0) ?_ ?_ h_summable
    · intro ρ
      by_cases hρ : (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ <;> simp [hρ, one_div, inv_nonneg, pow_two]
    · intro ρ
      by_cases hρ : (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ <;> simp [hρ]
  have hENN :
      ENNReal.ofReal
          (∑' ρ : ({ρ : Z.Zero | (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖} : Set Z.Zero),
              (1 : ℝ) / ‖Z.z ρ.val‖ ^ 2)
        =
        (⨆ m : ℕ,
          ∑ ρ ∈ zerosBallFinset Z h_z_ne_zero h_summable m,
            ENNReal.ofReal
              (if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0)) := by
    -- Convert the subtype sum to an indicator sum over `Z.Zero`,
    -- then apply `iSup` over cofinal balls.
    -- We use `ofReal_tsum_of_nonneg` to move between `ℝ` and `ENNReal`.
    have hsub :
        (∑' ρ : ({ρ : Z.Zero | (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖} : Set Z.Zero),
            (1 : ℝ) / ‖Z.z ρ.val‖ ^ 2)
          =
          ∑' ρ : Z.Zero,
            if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0 := by
      -- `tsum_subtype` with a `Set.indicator`.
      simpa [tsum_subtype, Set.indicator, Set.mem_ofPred_eq]
    -- Move to `ENNReal`.
    have hENN0 :
        ENNReal.ofReal
            (∑' ρ : Z.Zero,
              if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0)
          =
          ∑' ρ : Z.Zero,
            ENNReal.ofReal
              (if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0) := by
      simpa using
        (ENNReal.ofReal_tsum_of_nonneg (f := fun ρ : Z.Zero =>
            if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0)
          htail_nonneg htail_summable)
    -- Express the `ENNReal` tsum as an `iSup` over dyadic balls.
    have hcofinal := cofinal_zerosBallFinset Z h_z_ne_zero h_summable
    have htsum :
        (∑' ρ : Z.Zero,
            ENNReal.ofReal
              (if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0))
          =
          (⨆ m : ℕ,
            ∑ ρ ∈ zerosBallFinset Z h_z_ne_zero h_summable m,
              ENNReal.ofReal
                (if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0)) := by
      simpa using
        (ENNReal.tsum_eq_iSup_sum' (f := fun ρ : Z.Zero =>
              ENNReal.ofReal
                (if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0))
            (s := fun m : ℕ => zerosBallFinset Z h_z_ne_zero h_summable m) hcofinal)
    -- Combine.
    simpa [hsub] using (hENN0.trans htsum)
  -- Bound each partial sum uniformly by a geometric series (in `ℝ`), then convert back to `ℝ`.
  have hpartial :
      ∀ m : ℕ,
        (∑ ρ ∈ zerosBallFinset Z h_z_ne_zero h_summable m,
            (if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0))
          ≤ Cgeo * ((2 : ℝ) ^ n) ^ (ε - 1) := by
    intro m
    by_cases hm : m ≤ n + 1
    · -- Then every `ρ` in the dyadic ball has `‖Z.z ρ‖ ≤ 2^(n+1)`, so the indicator is zero.
      have : (∑ ρ ∈ zerosBallFinset Z h_z_ne_zero h_summable m,
            (if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0)) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro ρ hρ
        have hnorm : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ m :=
          (mem_zerosBallFinset_iff Z h_z_ne_zero h_summable m ρ).1 hρ
        have hpow : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ (n + 1) :=
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm
        have : ¬ (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ := by
          exact not_lt_of_ge (le_trans hnorm hpow)
        simp [this]
      -- Conclude by positivity.
      have hrhs_nonneg : 0 ≤ Cgeo * ((2 : ℝ) ^ n) ^ (ε - 1) := by
        have : 0 ≤ ((2 : ℝ) ^ n) ^ (ε - 1) :=
          Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n) _
        exact mul_nonneg hCgeo_nonneg this
      simpa [this] using hrhs_nonneg
    · have hmn : n + 1 < m := lt_of_not_ge hm
      -- We estimate by summing dyadic shells from `k = n+1` up to `m-1`.
      let ball : ℕ → Finset Z.Zero := fun t => zerosBallFinset Z h_z_ne_zero h_summable t
      have hsub : ball (n + 1) ⊆ ball m := by
        intro ρ hρ
        have hnorm : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (n + 1) :=
          (mem_zerosBallFinset_iff Z h_z_ne_zero h_summable (n + 1) ρ).1 hρ
        have hpow : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ m :=
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_of_lt hmn)
        exact (mem_zerosBallFinset_iff Z h_z_ne_zero h_summable m ρ).2 (le_trans hnorm hpow)
      have hdecomp :
          (∑ ρ ∈ ball m,
              (if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0))
            =
            (∑ ρ ∈ ball m \ ball (n + 1),
              (if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0)) := by
        have hzero :
            (∑ ρ ∈ ball (n + 1),
                (if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0)) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro ρ hρ
          have hnorm : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (n + 1) :=
            (mem_zerosBallFinset_iff Z h_z_ne_zero h_summable (n + 1) ρ).1 hρ
          have : ¬ (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ := not_lt_of_ge hnorm
          simp [this]
        -- `sum_sdiff + sum_ball = sum_ball`, so `sum_sdiff = sum_ball`.
        have := (Finset.sum_sdiff (s₁ := ball (n + 1)) (s₂ := ball m)
            (f := fun ρ : Z.Zero =>
              if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0) hsub)
        -- rearrange
        linarith
      -- Shell bound.
      have hshell :
          ∀ k : ℕ, n + 1 ≤ k → k + 1 ≤ m →
            (∑ ρ ∈ ball (k + 1) \ ball k, (1 : ℝ) / ‖Z.z ρ‖ ^ 2)
              ≤ (2 : ℝ) ^ (1 + ε) * Ccount * q ^ k := by
        intro k hk hkm
        let diff : Finset Z.Zero := ball (k + 1) \ ball k
        have hterm_le : ∀ ρ, ρ ∈ diff → (1 : ℝ) / ‖Z.z ρ‖ ^ 2 ≤ (1 : ℝ) / ((2 : ℝ) ^ k) ^ 2 := by
          intro ρ hρ
          have hρ' : ρ ∈ ball (k + 1) ∧ ρ ∉ ball k := by
            simpa [diff] using (Finset.mem_sdiff.1 hρ)
          have hnot : ¬ ‖Z.z ρ‖ ≤ (2 : ℝ) ^ k := by
            intro hle
            have : ρ ∈ ball k :=
              (mem_zerosBallFinset_iff Z h_z_ne_zero h_summable k ρ).2 hle
            exact hρ'.2 this
          have hk_pos : 0 < (2 : ℝ) ^ k := by positivity
          have hk_le_norm : (2 : ℝ) ^ k ≤ ‖Z.z ρ‖ := le_of_lt (lt_of_not_ge hnot)
          have hk2_pos : 0 < ((2 : ℝ) ^ k) ^ 2 := by positivity
          have hk2_le : ((2 : ℝ) ^ k) ^ 2 ≤ ‖Z.z ρ‖ ^ 2 :=
            pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k) hk_le_norm 2
          -- `1/‖ρ‖² ≤ 1/(2^k)²`
          simpa [one_div, inv_pow] using (one_div_le_one_div_of_le hk2_pos hk2_le)
        have hsum_le_card :
            (∑ ρ ∈ diff, (1 : ℝ) / ‖Z.z ρ‖ ^ 2)
              ≤ (diff.card : ℝ) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2) := by
          have hsum_le :
              (∑ ρ ∈ diff, (1 : ℝ) / ‖Z.z ρ‖ ^ 2)
                ≤ ∑ ρ ∈ diff, (1 : ℝ) / ((2 : ℝ) ^ k) ^ 2 :=
            Finset.sum_le_sum hterm_le
          calc
            (∑ ρ ∈ diff, (1 : ℝ) / ‖Z.z ρ‖ ^ 2)
                ≤ ∑ ρ ∈ diff, (1 : ℝ) / ((2 : ℝ) ^ k) ^ 2 := hsum_le
            _ = (diff.card : ℝ) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2) := by simp
        have hball_card : ((ball (k + 1)).card : ℝ) =
            (({ρ : Z.Zero | ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1)} : Set Z.Zero).ncard : ℝ) := by
          exact_mod_cast (card_zerosBallFinset Z h_z_ne_zero h_summable (n := k + 1))
        have hRcount_le' : Rcount ≤ (2 : ℝ) ^ (k + 1) := by
          have hpow : (2 : ℝ) ^ n₀ ≤ (2 : ℝ) ^ (k + 1) :=
            pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_trans hk (Nat.le_succ _))
          have hRcount_le_R0 : Rcount ≤ R0 := le_max_left _ _
          exact le_trans (le_trans hRcount_le_R0 hn₀) hpow
        have hcount_ball :
            (({ρ : Z.Zero | ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1)} : Set Z.Zero).ncard : ℝ)
              ≤ Ccount * ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + ε) :=
          hN_le ((2 : ℝ) ^ (k + 1)) hRcount_le'
        have hdiff_card_le :
            (diff.card : ℝ) ≤ Ccount * ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + ε) := by
          have hcard_le_ball : (diff.card : ℝ) ≤ ((ball (k + 1)).card : ℝ) := by
            exact_mod_cast (Finset.card_le_card (show diff ⊆ ball (k + 1) from Finset.sdiff_subset))
          have hball_le :
              ((ball (k + 1)).card : ℝ) ≤ Ccount * ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + ε) := by
            simpa [hball_card] using hcount_ball
          exact le_trans hcard_le_ball hball_le
        -- Simplify the expression into `const * q^k`.
        have hk1_pos : 0 < (2 : ℝ) ^ (k + 1) := by positivity
        have hk_pos' : 0 < (2 : ℝ) ^ k := by positivity
        have hrewrite :
            Ccount * ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + ε) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2)
              = (2 : ℝ) ^ (1 + ε) * Ccount * q ^ k := by
          -- `((2^(k+1))^(1+ε)) / (2^k)^2 = 2^(1+ε) * (2^(ε-1))^k`.
          have hpowk_pos : 0 < (2 : ℝ) ^ k := by positivity
          have hpowk1_pos : 0 < (2 : ℝ) ^ (k + 1) := by positivity
          -- Convert `q^k` into `2^((ε-1)*k)`.
          have hqk : q ^ k = (2 : ℝ) ^ ((ε - 1) * (k : ℝ)) := by
            -- `q = 2^(ε-1)`.
            have : q = (2 : ℝ) ^ (ε - 1) := rfl
            -- `((2^(ε-1))^k) = 2^((ε-1)*k)`.
            have hmul :
                (2 : ℝ) ^ ((ε - 1) * (k : ℝ)) = ((2 : ℝ) ^ (ε - 1)) ^ (k : ℝ) := by
              simpa [mul_assoc] using
                (Real.rpow_mul (x := (2 : ℝ)) (hx := by positivity) (y := (ε - 1)) (z := (k : ℝ)))
            simpa [q, Real.rpow_natCast] using hmul.symm
          -- Now compute both sides as powers of `2`.
          -- Left side:
          -- `((2^(k+1))^(1+ε)) / (2^k)^2 = 2^( (1+ε)*(k+1) - 2*k ) = 2^( (ε-1)*k + (1+ε) )`.
          have hleft :
              ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + ε) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2)
                = (2 : ℝ) ^ (1 + ε) * q ^ k := by
            have h2pos : 0 < (2 : ℝ) := by norm_num
            -- Rewrite `((2^(k+1))^(1+ε))` as `2^((1+ε)*(k+1))`.
            have hA :
                ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + ε)
                  = (2 : ℝ) ^ (((1 : ℝ) + ε) * ((k + 1 : ℕ) : ℝ)) := by
              -- `2^(k+1) = 2^((k+1):ℝ)` and use `rpow_mul`.
              have : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ ((k + 1 : ℕ) : ℝ) := by
                simpa using (Real.rpow_natCast (2 : ℝ) (k + 1)).symm
              calc
                ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + ε)
                    = ((2 : ℝ) ^ ((k + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) + ε) := by simp [this]
                _ = (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * ((1 : ℝ) + ε)) := by
                      simpa [mul_assoc] using
                        (Real.rpow_mul (x := (2 : ℝ)) (hx := by positivity) (y := ((k + 1 : ℕ) : ℝ))
                          (z := ((1 : ℝ) + ε))).symm
                _ = (2 : ℝ) ^ (((1 : ℝ) + ε) * ((k + 1 : ℕ) : ℝ)) := by
                      simp [mul_comm, mul_left_comm, mul_assoc]
            -- Rewrite `1 / (2^k)^2` as `2^(-2*k)`.
            have hB :
                (1 : ℝ) / ((2 : ℝ) ^ k) ^ 2 = (2 : ℝ) ^ (-(2 : ℝ) * (k : ℝ)) := by
              have hk2_pos : 0 < ((2 : ℝ) ^ k) ^ 2 := by positivity
              have : (1 : ℝ) / ((2 : ℝ) ^ k) ^ 2 = (((2 : ℝ) ^ k) ^ 2)⁻¹ := by
                simp [one_div]
              -- `(2^k)^2 = 2^(2*k)` and invert.
              have hk_pow : ((2 : ℝ) ^ k) ^ 2 = (2 : ℝ) ^ ((2 : ℝ) * (k : ℝ)) := by
                have : ((2 : ℝ) ^ k) ^ (2 : ℝ) = ((2 : ℝ) ^ k) ^ 2 := by
                  simpa using (Real.rpow_natCast ((2 : ℝ) ^ k) 2)
                -- `(2^k)^2 = (2^k)^(2:ℝ) = 2^((k:ℝ)*2)`.
                calc
                  ((2 : ℝ) ^ k) ^ 2 = ((2 : ℝ) ^ k) ^ (2 : ℝ) := by
                        simpa using (Real.rpow_natCast ((2 : ℝ) ^ k) 2).symm
                  _ = (2 : ℝ) ^ ((k : ℝ) * (2 : ℝ)) := by
                        -- `(2^k) = 2^(k:ℝ)` and use `rpow_mul`.
                        have : (2 : ℝ) ^ k = (2 : ℝ) ^ (k : ℝ) := by
                          simpa using (Real.rpow_natCast (2 : ℝ) k).symm
                        calc
                          ((2 : ℝ) ^ k) ^ (2 : ℝ) = ((2 : ℝ) ^ (k : ℝ)) ^ (2 : ℝ) := by simp [this]
                          _ = (2 : ℝ) ^ ((k : ℝ) * (2 : ℝ)) := by
                                simpa [mul_assoc] using
                                  (Real.rpow_mul
                                    (x := (2 : ℝ)) (hx := by positivity)
                                    (y := (k : ℝ)) (z := (2 : ℝ)))
                  _ = (2 : ℝ) ^ ((2 : ℝ) * (k : ℝ)) := by ring_nf
              -- Invert via `rpow_neg`.
              have hbase_nonneg : 0 ≤ (2 : ℝ) := by norm_num
              have : (((2 : ℝ) ^ ((2 : ℝ) * (k : ℝ))) : ℝ)⁻¹ = (2 : ℝ) ^ (-(2 : ℝ) * (k : ℝ)) := by
                simpa [Real.rpow_neg hbase_nonneg ((2 : ℝ) * (k : ℝ)), inv_eq_one_div] using
                  (Real.rpow_neg hbase_nonneg ((2 : ℝ) * (k : ℝ))).symm
              -- Combine.
              simp
                [hk_pow, one_div, Real.rpow_neg hbase_nonneg ((2 : ℝ) * (k : ℝ)),
                  mul_assoc, inv_eq_one_div]
            -- Combine powers.
            have hden_pos : 0 < (1 - q) := sub_pos.mpr hq_lt_one
            have : ((2 : ℝ) ^ (1 + ε) * q ^ k) = (2 : ℝ) ^ ((1 + ε) + (ε - 1) * (k : ℝ)) := by
              -- `q^k` is a power of 2.
              simp [hqk, Real.rpow_add (by norm_num : (0 : ℝ) < 2), mul_assoc]
            -- Use `rpow_add` on the LHS.
            -- We keep the final form as stated.
            -- This sub-proof is algebraic; we avoid over-simplification.
            -- A short `ring_nf` on exponents works after rewriting everything as `2^(_)`.
            have hmain :
                ((2 : ℝ) ^ (((1 : ℝ) + ε) * ((k + 1 : ℕ) : ℝ))) * ((2 : ℝ) ^ (-(2 : ℝ) * (k : ℝ)))
                  = (2 : ℝ) ^ ((1 + ε) + (ε - 1) * (k : ℝ)) := by
              -- Combine the exponents.
              have hpos2 : (0 : ℝ) < 2 := by norm_num
              -- `2^a * 2^b = 2^(a+b)`.
              calc
                (2 : ℝ) ^ (((1 : ℝ) + ε) * ((k + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ (-(2 : ℝ) * (k : ℝ))
                    = (2 : ℝ) ^ ((((1 : ℝ) + ε) * ((k + 1 : ℕ) : ℝ)) + (-(2 : ℝ) * (k : ℝ))) := by
                        simp [Real.rpow_add hpos2]
                _ = (2 : ℝ) ^ ((1 + ε) + (ε - 1) * (k : ℝ)) := by
                        -- arithmetic on the exponent
                        congr 1
                        ring_nf
            -- Finish.
            -- Replace the two factors using `hA` and `hB`.
            calc
              ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + ε) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2)
                  =
                    (2 : ℝ) ^ (((1 : ℝ) + ε) * ((k + 1 : ℕ) : ℝ)) *
                      (2 : ℝ) ^ (-(2 : ℝ) * (k : ℝ)) := by
                      simp [hA, hB]
              _ = (2 : ℝ) ^ ((1 + ε) + (ε - 1) * (k : ℝ)) := hmain
              _ = (2 : ℝ) ^ (1 + ε) * q ^ k := by
                      -- Split the exponent and rewrite `q^k`.
                      have hpos2 : (0 : ℝ) < 2 := by norm_num
                      simp
                        [Real.rpow_add hpos2, hqk,
                          Real.rpow_mul (le_of_lt hpos2) (ε - 1) (k : ℝ),
                          Real.rpow_natCast, q, mul_assoc, mul_comm, mul_left_comm]
          -- Put back the `Ccount` factor.
          calc
            Ccount * ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + ε) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2)
                =
                  Ccount *
                    (((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + ε) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2)) := by
                      ring
            _ = Ccount * ((2 : ℝ) ^ (1 + ε) * q ^ k) := by simp [hleft]
            _ = (2 : ℝ) ^ (1 + ε) * Ccount * q ^ k := by ring
        -- Assemble.
        have hcalc :
            (∑ ρ ∈ diff, (1 : ℝ) / ‖Z.z ρ‖ ^ 2)
              ≤ (2 : ℝ) ^ (1 + ε) * Ccount * q ^ k := by
          calc
            (∑ ρ ∈ diff, (1 : ℝ) / ‖Z.z ρ‖ ^ 2)
                ≤ (diff.card : ℝ) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2) := hsum_le_card
            _ ≤ (Ccount * ((2 : ℝ) ^ (k + 1)) ^ ((1 : ℝ) + ε)) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ 2) := by
                  -- multiply by a nonnegative constant
                  have hk_nonneg : 0 ≤ (1 : ℝ) / ((2 : ℝ) ^ k) ^ 2 := by positivity
                  exact mul_le_mul_of_nonneg_right hdiff_card_le hk_nonneg
            _ = (2 : ℝ) ^ (1 + ε) * Ccount * q ^ k := by
                  simpa [mul_assoc, mul_left_comm, mul_comm] using hrewrite
        simpa [diff] using hcalc
      -- Use shells up to `m-1`, and bound by a geometric sum.
      have hball_tail :
          (∑ ρ ∈ ball m \ ball (n + 1),
              (if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0))
            ≤ (2 : ℝ) ^ (1 + ε) * Ccount * (q ^ (n + 1)) / (1 - q) := by
        -- Each `ρ` in the shell difference satisfies the indicator, so we can drop it.
        have h_indicator :
            (∑ ρ ∈ ball m \ ball (n + 1),
                (if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0))
              = (∑ ρ ∈ ball m \ ball (n + 1), (1 : ℝ) / ‖Z.z ρ‖ ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro ρ hρ
          have hρ' : ρ ∈ ball m ∧ ρ ∉ ball (n + 1) := by
            simpa using (Finset.mem_sdiff.1 hρ)
          have hnot : ¬ ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (n + 1) := by
            intro hle
            have : ρ ∈ ball (n + 1) :=
              (mem_zerosBallFinset_iff Z h_z_ne_zero h_summable (n + 1) ρ).2 hle
            exact hρ'.2 this
          have : (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ := lt_of_not_ge hnot
          simp [this]
        -- Bound by summing shell bounds from `k = n+1` to `m-1`.
        -- We use a crude bound: each increment `ball (k+1) \\ ball k` is bounded by `const * q^k`,
        -- then sum a finite geometric progression.
        -- First, expand the finite sum over `ball m \\ ball (n+1)`
        -- as a telescoping sum of increments.
        have htel :
            (∑ ρ ∈ ball m \ ball (n + 1), (1 : ℝ) / ‖Z.z ρ‖ ^ 2)
              ≤ ∑ k ∈ Finset.range (m - (n + 1)),
                  (2 : ℝ) ^ (1 + ε) * Ccount * q ^ (n + 1 + k) := by
          -- Induction on `m - (n+1)` via telescoping.
          let d : ℕ := m - (n + 1)
          have hd : m = n + 1 + d := (Nat.add_sub_of_le (Nat.le_of_lt hmn)).symm
          -- We prove a stronger statement by induction on `d`.
          have hmain :
              ∀ d : ℕ,
                (∑ ρ ∈ ball (n + 1 + d) \ ball (n + 1), (1 : ℝ) / ‖Z.z ρ‖ ^ 2)
                  ≤ ∑ k ∈ Finset.range d, (2 : ℝ) ^ (1 + ε) * Ccount * q ^ (n + 1 + k) := by
            intro d
            induction d with
            | zero =>
                simp
            | succ d ih =>
                have hsub' : ball (n + 1 + d) ⊆ ball (n + 1 + d.succ) := by
                  intro ρ hρ
                  have hnorm : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (n + 1 + d) :=
                    (mem_zerosBallFinset_iff Z h_z_ne_zero h_summable (n + 1 + d) ρ).1 hρ
                  have hpow : (2 : ℝ) ^ (n + 1 + d) ≤ (2 : ℝ) ^ (n + 1 + d.succ) :=
                    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ _)
                  exact (mem_zerosBallFinset_iff Z h_z_ne_zero h_summable (n + 1 + d.succ) ρ).2
                    (le_trans hnorm hpow)
                -- Apply `sum_sdiff` to split the new shell.
                have hsplit :=
                  (Finset.sum_sdiff (s₁ := ball (n + 1 + d)) (s₂ := ball (n + 1 + d.succ))
                      (f := fun ρ : Z.Zero => (1 : ℝ) / ‖Z.z ρ‖ ^ 2) hsub')
                -- Rearrange and bound the shell term.
                have hshell_bound :
                    (∑ ρ ∈ ball (n + 1 + d.succ) \ ball (n + 1 + d), (1 : ℝ) / ‖Z.z ρ‖ ^ 2)
                      ≤ (2 : ℝ) ^ (1 + ε) * Ccount * q ^ (n + 1 + d) := by
                  have hn1_le : n + 1 ≤ n + 1 + d := Nat.le_add_right _ _
                  have hk_le : n + 1 + d ≤ n + 1 + d.succ := Nat.le_succ _
                  -- Use the shell lemma with `k = n+1+d`.
                  have := hshell (k := n + 1 + d) hn1_le (Nat.le_succ _)
                  simpa [ball] using this
                -- Combine with induction hypothesis.
                -- `sum(ball(n+1+d.succ)\\ball(n+1)) = shell + sum(ball(n+1+d)\\ball(n+1))`.
                have hrec :
                    (∑ ρ ∈ ball (n + 1 + d.succ) \ ball (n + 1), (1 : ℝ) / ‖Z.z ρ‖ ^ 2)
                      =
                    (∑ ρ ∈ ball (n + 1 + d.succ) \ ball (n + 1 + d), (1 : ℝ) / ‖Z.z ρ‖ ^ 2)
                      +
                    (∑ ρ ∈ ball (n + 1 + d) \ ball (n + 1), (1 : ℝ) / ‖Z.z ρ‖ ^ 2) := by
                  -- use `sdiff` associativity inside `ball (n+1+d.succ)`
                  have hsub1 : ball (n + 1) ⊆ ball (n + 1 + d) := by
                    intro ρ hρ
                    have hnorm : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (n + 1) :=
                      (mem_zerosBallFinset_iff Z h_z_ne_zero h_summable (n + 1) ρ).1 hρ
                    have hpow : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ (n + 1 + d) :=
                      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_add_right _ _)
                    exact (mem_zerosBallFinset_iff Z h_z_ne_zero h_summable (n + 1 + d) ρ).2
                      (le_trans hnorm hpow)
                  have hsub2 : ball (n + 1 + d) ⊆ ball (n + 1 + d.succ) := hsub'
                  -- `sdiff` as
                  -- `ball(n+1+d.succ) \\ ball(n+1)
                  --   = (ball(n+1+d.succ) \\ ball(n+1+d)) ∪ (ball(n+1+d) \\ ball(n+1))`
                  -- and the union is disjoint.
                  have hdisj :
                      Disjoint
                        (ball (n + 1 + d.succ) \ ball (n + 1 + d))
                        (ball (n + 1 + d) \ ball (n + 1)) := by
                    refine Finset.disjoint_left.2 ?_
                    intro ρ hρ1 hρ2
                    have hρ1' : ρ ∈ ball (n + 1 + d.succ) ∧ ρ ∉ ball (n + 1 + d) := by
                      simpa using (Finset.mem_sdiff.1 hρ1)
                    have hρ2' : ρ ∈ ball (n + 1 + d) ∧ ρ ∉ ball (n + 1) := by
                      simpa using (Finset.mem_sdiff.1 hρ2)
                    exact hρ1'.2 hρ2'.1
                  -- Use `sum_union` on the disjoint union.
                  have hunion :
                      (ball (n + 1 + d.succ) \ ball (n + 1 + d)) ∪ (ball (n + 1 + d) \ ball (n + 1))
                        = ball (n + 1 + d.succ) \ ball (n + 1) := by
                    -- `sdiff` with nested subsets.
                    ext ρ
                    simp [ball, hsub1, hsub2, Nat.le_add_right, Nat.le_succ]
                  -- Now sum.
                  have hsum_union :=
                    (Finset.sum_union (s₁ := ball (n + 1 + d.succ) \ ball (n + 1 + d))
                      (s₂ := ball (n + 1 + d) \ ball (n + 1))
                      (f := fun ρ : Z.Zero => (1 : ℝ) / ‖Z.z ρ‖ ^ 2)
                      hdisj)
                  -- rewrite and rearrange
                  simpa [hunion, add_comm, add_left_comm, add_assoc] using hsum_union.symm
                -- Apply the recursion with bounds.
                calc
                  (∑ ρ ∈ ball (n + 1 + d.succ) \ ball (n + 1), (1 : ℝ) / ‖Z.z ρ‖ ^ 2)
                      = (∑ ρ ∈ ball (n + 1 + d.succ) \ ball (n + 1 + d), (1 : ℝ) / ‖Z.z ρ‖ ^ 2)
                          + (∑ ρ ∈ ball (n + 1 + d) \ ball (n + 1), (1 : ℝ) / ‖Z.z ρ‖ ^ 2) := by
                          simpa using hrec
                  _ ≤ (2 : ℝ) ^ (1 + ε) * Ccount * q ^ (n + 1 + d) +
                        ∑ k ∈ Finset.range d, (2 : ℝ) ^ (1 + ε) * Ccount * q ^ (n + 1 + k) := by
                          gcongr
                  _ = ∑ k ∈ Finset.range d.succ, (2 : ℝ) ^ (1 + ε) * Ccount * q ^ (n + 1 + k) := by
                          simp [Finset.sum_range_succ, add_assoc, add_left_comm, add_comm]
          -- Specialize to `d = m - (n+1)`.
          simpa [d, hd] using hmain (m - (n + 1))
        -- Convert the finite sum to a geometric bound using `geom_sum_eq`.
        have hgeom :
            ∑ k ∈ Finset.range (m - (n + 1)), (2 : ℝ) ^ (1 + ε) * Ccount * q ^ (n + 1 + k)
              ≤ (2 : ℝ) ^ (1 + ε) * Ccount * (q ^ (n + 1)) / (1 - q) := by
          -- Pull out constants and reduce to `∑ q^(n+1+k)`.
          have hconst_nonneg : 0 ≤ (2 : ℝ) ^ (1 + ε) * Ccount := mul_nonneg
              (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) hCcount_nonneg
          -- Rewrite as `const * q^(n+1) * ∑ q^k`.
          have hsum :
              ∑ k ∈ Finset.range (m - (n + 1)), (2 : ℝ) ^ (1 + ε) * Ccount * q ^ (n + 1 + k)
                = (2 : ℝ) ^ (1 + ε) * Ccount * (q ^ (n + 1)) *
                    ∑ k ∈ Finset.range (m - (n + 1)), q ^ k := by
            simp [mul_assoc, mul_left_comm, mul_comm, pow_add, Finset.mul_sum]
          -- Bound the geometric sum by `1/(1-q)`.
          have hq_ne : q ≠ 1 := ne_of_lt hq_lt_one
          have hgeom_eq : ∑ k ∈ Finset.range (m - (n + 1)), q ^ k =
              (q ^ (m - (n + 1)) - 1) / (q - 1) := geom_sum_eq hq_ne (m - (n + 1))
          have hgeom_eq' :
              (q ^ (m - (n + 1)) - 1) / (q - 1) = (1 - q ^ (m - (n + 1))) / (1 - q) := by
            field_simp
            ring
          have hq_le1 : q ≤ 1 := le_of_lt hq_lt_one
          have hqpow_le1 : q ^ (m - (n + 1)) ≤ 1 := pow_le_one₀ (le_of_lt hq_pos) hq_le1
          have hnum_le : 1 - q ^ (m - (n + 1)) ≤ (1 : ℝ) := by linarith
          have hden_pos : 0 < (1 - q) := sub_pos.mpr hq_lt_one
          have hsum_q :
              (∑ k ∈ Finset.range (m - (n + 1)), q ^ k) ≤ (1 - q)⁻¹ := by
            -- Use the explicit formula and bound `1 - q^N ≤ 1`.
            calc
              (∑ k ∈ Finset.range (m - (n + 1)), q ^ k)
                  = (1 - q ^ (m - (n + 1))) / (1 - q) := by
                        simpa [hgeom_eq, hgeom_eq', div_eq_mul_inv, sub_eq_add_neg] using hgeom_eq
              _ ≤ (1 : ℝ) / (1 - q) := by
                        gcongr
              _ = (1 - q)⁻¹ := by simp [one_div]
          -- Assemble.
          calc
            ∑ k ∈ Finset.range (m - (n + 1)), (2 : ℝ) ^ (1 + ε) * Ccount * q ^ (n + 1 + k)
                = (2 : ℝ) ^ (1 + ε) * Ccount * (q ^ (n + 1)) *
                    ∑ k ∈ Finset.range (m - (n + 1)), q ^ k := hsum
            _ ≤ (2 : ℝ) ^ (1 + ε) * Ccount * (q ^ (n + 1)) * (1 - q)⁻¹ := by
                  gcongr
            _ = (2 : ℝ) ^ (1 + ε) * Ccount * (q ^ (n + 1)) / (1 - q) := by
                  simp [div_eq_mul_inv, mul_assoc]
        -- Finish.
        have h1 :
            (∑ ρ ∈ ball m \ ball (n + 1), (1 : ℝ) / ‖Z.z ρ‖ ^ 2)
              ≤ (2 : ℝ) ^ (1 + ε) * Ccount * (q ^ (n + 1)) / (1 - q) := by
          exact le_trans htel hgeom
        simpa [h_indicator] using h1
      -- Put the pieces together.
      -- `ball m` sum equals sdiff sum, and then apply shell bounds.
      have hsum0 :
          (∑ ρ ∈ ball m,
              (if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0))
            ≤ (2 : ℝ) ^ (1 + ε) * Ccount * (q ^ (n + 1)) / (1 - q) := by
        simpa [hdecomp] using hball_tail
      -- Finally relate the RHS to `Cgeo * (2^n)^(ε-1)` by comparing `q^(n+1)` to `(2^n)^(ε-1)`.
      have hq_pow :
          q ^ (n + 1) ≤ q * ((2 : ℝ) ^ n) ^ (ε - 1) := by
        -- `q^(n+1) = q * q^n`, and `q^n = (2^n)^(ε-1)`.
        have : q ^ (n + 1) = q * q ^ n := by simp [pow_succ, mul_assoc]
        -- `q^n = (2^n)^(ε-1)`.
        have hqn :
            q ^ n = ((2 : ℝ) ^ n) ^ (ε - 1) := by
          -- both sides equal `2^((ε-1)*n)`
          have hpos2 : (0 : ℝ) < 2 := by norm_num
          have hA : q ^ n = (2 : ℝ) ^ ((ε - 1) * (n : ℝ)) := by
            have hmul :
                (2 : ℝ) ^ ((ε - 1) * (n : ℝ)) = ((2 : ℝ) ^ (ε - 1)) ^ (n : ℝ) := by
              simpa [mul_assoc] using
                (Real.rpow_mul (x := (2 : ℝ)) (hx := by positivity) (y := (ε - 1)) (z := (n : ℝ)))
            simpa [q, Real.rpow_natCast] using hmul.symm
          have hB : ((2 : ℝ) ^ n) ^ (ε - 1) = (2 : ℝ) ^ (((n : ℕ) : ℝ) * (ε - 1)) := by
            have : (2 : ℝ) ^ n = (2 : ℝ) ^ ((n : ℕ) : ℝ) := by
              simpa using (Real.rpow_natCast (2 : ℝ) n).symm
            calc
              ((2 : ℝ) ^ n) ^ (ε - 1) = ((2 : ℝ) ^ ((n : ℕ) : ℝ)) ^ (ε - 1) := by simp [this]
              _ = (2 : ℝ) ^ (((n : ℕ) : ℝ) * (ε - 1)) := by
                    simpa [mul_assoc] using
                      (Real.rpow_mul (x := (2 : ℝ)) (hx := by positivity) (y := ((n : ℕ) : ℝ))
                        (z := (ε - 1))).symm
          have hmul' : (ε - 1) * (n : ℝ) = ((n : ℕ) : ℝ) * (ε - 1) := by ring
          simpa [hA, hB, hmul'] using rfl
        -- combine
        simpa [this, hqn, mul_assoc]
      have hCgeo_eq :
          (2 : ℝ) ^ (1 + ε) * Ccount * (q ^ (n + 1)) / (1 - q) ≤
            Cgeo * ((2 : ℝ) ^ n) ^ (ε - 1) := by
        -- unfold `Cgeo` and use `hq_pow`.
        have hden_pos : 0 < (1 - q) := sub_pos.mpr hq_lt_one
        have hden_nonneg : 0 ≤ (1 - q) := le_of_lt hden_pos
        have hqpow_le :
            (2 : ℝ) ^ (1 + ε) * Ccount * (q ^ (n + 1)) / (1 - q)
              ≤ (2 : ℝ) ^ (1 + ε) * Ccount * (q * ((2 : ℝ) ^ n) ^ (ε - 1)) / (1 - q) := by
          have hnonneg : 0 ≤ (2 : ℝ) ^ (1 + ε) * Ccount := mul_nonneg
              (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) hCcount_nonneg
          have :=
            mul_le_mul_of_nonneg_left hq_pow
              (mul_nonneg hnonneg (by positivity : 0 ≤ (1 : ℝ) / (1 - q)))
          -- `a*b/(1-q)` is monotone in `b` since denominator is positive.
          -- We use `gcongr` instead of rearranging by hand.
          gcongr
        -- Now rewrite to match `Cgeo`.
        have : (2 : ℝ) ^ (1 + ε) * Ccount * (q * ((2 : ℝ) ^ n) ^ (ε - 1)) / (1 - q)
              = Cgeo * ((2 : ℝ) ^ n) ^ (ε - 1) := by
          simp [Cgeo, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
        exact le_trans hqpow_le (by simpa [this])
      have hbound :
          (∑ ρ ∈ ball m,
              (if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0))
            ≤ Cgeo * ((2 : ℝ) ^ n) ^ (ε - 1) :=
        le_trans hsum0 hCgeo_eq
      -- Done.
      exact hbound
  have hENN_le :
      (⨆ m : ℕ,
          ∑ ρ ∈ zerosBallFinset Z h_z_ne_zero h_summable m,
            ENNReal.ofReal
              (if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0))
        ≤ ENNReal.ofReal (Cgeo * ((2 : ℝ) ^ n) ^ (ε - 1)) := by
    -- bound each term of the `iSup`
    refine iSup_le ?_
    intro m
    -- convert finite sum of `ofReal` back to a real sum
    have hsum_ofReal :
        (∑ ρ ∈ zerosBallFinset Z h_z_ne_zero h_summable m,
            ENNReal.ofReal
              (if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0))
          =
          ENNReal.ofReal
            (∑ ρ ∈ zerosBallFinset Z h_z_ne_zero h_summable m,
              (if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0)) := by
      apply sum_ofReal_eq_ofReal_sum
      intro ρ
      exact htail_nonneg ρ
    -- apply `ofReal` to the real bound
    have hreal_le := hpartial m
    have hENN_le' :
        ENNReal.ofReal
            (∑ ρ ∈ zerosBallFinset Z h_z_ne_zero h_summable m,
              (if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ 2 else 0))
          ≤ ENNReal.ofReal (Cgeo * ((2 : ℝ) ^ n) ^ (ε - 1)) :=
      ENNReal.ofReal_le_ofReal hreal_le
    simpa [hsum_ofReal] using hENN_le'
  -- From the ENNReal bound, conclude the real bound.
  have htsum_le :
      ENNReal.ofReal
          (∑' ρ : ({ρ : Z.Zero | (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖} : Set Z.Zero),
              (1 : ℝ) / ‖Z.z ρ.val‖ ^ 2)
        ≤ ENNReal.ofReal (Cgeo * ((2 : ℝ) ^ n) ^ (ε - 1)) := by
    -- Use `hENN` and then `hENN_le`.
    simpa [hENN] using hENN_le
  -- Finally, unwrap `ENNReal.ofReal` and finish.

-/
end OrderOne

end Hadamard
