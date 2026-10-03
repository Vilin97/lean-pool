/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/
module


public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import LeanPool.LiCriterion.Hadamard.DyadicBounds
public import LeanPool.LiCriterion.Hadamard.OrderOne.CofiniteControl
public import LeanPool.LiCriterion.Hadamard.OrderOne.ZeroCountingBounds

/-! ### Dyadic ball finsets under `∑ 1/‖z ρ‖² < ∞` -/

public section

open scoped BigOperators

-- This module bundles several long tail-estimate developments.

namespace Hadamard

namespace OrderOne

open Real Hadamard.DyadicBounds

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
    (Z : ZeroSet f)
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
    (Z : ZeroSet f)
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
    (Z : ZeroSet f)
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0) :
    ∀ ε : ℝ, 0 < ε →
      ∃ R₀ C : ℝ, 0 ≤ C ∧
        ∀ r : ℝ, R₀ ≤ r →
          (∑ᶠ ρ : Z.Zero, if ‖Z.z ρ‖ ≤ r then (analyticOrderNatAt f (Z.z ρ) : ℝ) else 0) ≤
            C * r ^ ((1 : ℝ) + ε) := by
  exact sum_multiplicity_zeros_le_rpow_of_order_le hf_entire hf_finite hf_order_le
    zero_le_one Z h_zeros_only h_inj h_z_ne_zero

theorem sum_invNorm_le_rpow_of_two_pow
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (hf_finite : hasFiniteOrder f) (hf_order_le : order f ≤ 1)
    (Z : ZeroSet f)
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
  exact dyadic_ball_cofinal Z.z _
    (fun k ρ => mem_zerosBallFinset_iff Z h_z_ne_zero h_summable k ρ)

theorem tsum_invNorm_sq_tail_le_rpow_of_two_pow
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (hf_finite : hasFiniteOrder f) (hf_order_le : order f ≤ 1)
    (Z : ZeroSet f)
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
    intro m
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
      have hRcount_le : Rcount ≤ (2 : ℝ) ^ (k + 1) := by
        exact hRcount_le_pow.trans
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega))
      have hcount : (∑ _ρ ∈ ball (k + 1), (1 : ℝ)) ≤
          Ccount * ((2 : ℝ) ^ (k + 1)) ^ (1 + ε) := by
        simpa [ball, card_zerosBallFinset] using hN_le ((2 : ℝ) ^ (k + 1)) hRcount_le
      have h := dyadic_shell_sum_bound Z.z (fun _ => (1 : ℝ)) (fun _ => by norm_num)
        ball (fun j ρ => mem_zerosBallFinset_iff Z h_z_ne_zero h_summable j ρ)
        1 n k hk Ccount 1 ε hcount
      simpa only [g, q, Nat.cast_one, Nat.reduceAdd,
        show (1 : ℝ) + ε - (1 + 1) = ε - 1 by ring] using h
    have hzero : ∀ k, k ≤ n + 1 → ∑ ρ ∈ ball k, g ρ = 0 := by
      intro k hk
      refine Finset.sum_eq_zero (fun ρ hρ => ?_)
      have hnorm := (mem_zerosBallFinset_iff Z h_z_ne_zero h_summable k ρ).1 hρ
      have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
      simp only [g, ite_eq_right (not_lt_of_ge (hnorm.trans hpow))]
    have hbound := sum_le_of_geometric_shells ball g
      ((2 : ℝ) ^ ((1 : ℝ) + ε) * Ccount) q
      (by positivity) hq_pos hq_lt_one n m hsub_ball hzero hshell
    have hqpow : q ^ n = ((2 : ℝ) ^ n) ^ (ε - 1) :=
      Real.rpow_pow_comm (x := (2 : ℝ)) (hx := by positivity) _ n
    simpa only [C, hqpow] using hbound
  have htsum_g :
      (∑' ρ : Z.Zero, g ρ) ≤ C * ((2 : ℝ) ^ n) ^ (ε - 1) :=
    tsum_le_of_cofinal_finset_bound (zerosBallFinset Z h_z_ne_zero h_summable) g
      (by positivity) hg_nonneg (cofinal_zerosBallFinset Z h_z_ne_zero h_summable) hball
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

end OrderOne

end Hadamard
