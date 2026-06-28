/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Exp
import LeanPool.OrdvecFormalization.BayesThreshold

/-!
# Exponential tilts on finite support

This file provides the first reusable source of MLR: a positive base weight on
the finite ordered support, tilted by `exp (θ * x)`, has monotone likelihood
ratio as `θ` increases.
-/

open scoped NNReal

namespace OrdvecFormalization

/-- Positive, not necessarily normalized, base weights on the finite support. -/
structure PosWeights (n : ℕ) where
  /-- The unnormalized weight at each support point. -/
  weight : Support n → ℝ≥0
  /-- Every base weight is strictly positive. -/
  pos : ∀ x, 0 < weight x

/-- The nonnegative real exponential. -/
noncomputable def nnexp (r : ℝ) : ℝ≥0 :=
  ⟨Real.exp r, (Real.exp_pos r).le⟩

@[simp]
theorem coe_nnexp (r : ℝ) : (nnexp r : ℝ) = Real.exp r :=
  rfl

@[simp]
theorem nnexp_zero : nnexp 0 = 1 := by
  exact Subtype.ext Real.exp_zero

/-- `nnexp` is strictly positive. -/
theorem nnexp_pos (r : ℝ) : 0 < nnexp r := by
  change (0 : ℝ) < Real.exp r
  exact Real.exp_pos r

/-- `nnexp` is monotone. -/
theorem nnexp_le_nnexp {a b : ℝ} (h : a ≤ b) : nnexp a ≤ nnexp b := by
  change Real.exp a ≤ Real.exp b
  exact Real.exp_le_exp.mpr h

/-- Multiplication of `nnexp`s adds exponents. -/
theorem nnexp_mul (a b : ℝ) : nnexp a * nnexp b = nnexp (a + b) := by
  apply NNReal.coe_injective
  simp [Real.exp_add]

/-- Unnormalized exponential-tilt weight. -/
noncomputable def tiltWeight {n : ℕ} (base : PosWeights n) (θ : ℝ) (x : Support n) : ℝ≥0 :=
  base.weight x * nnexp (θ * x.val)

/-- Tilt weights are strictly positive. -/
theorem tiltWeight_pos {n : ℕ} (base : PosWeights n) (θ : ℝ) (x : Support n) :
    0 < tiltWeight base θ x := by
  exact mul_pos (base.pos x) (nnexp_pos (θ * x.val))

/-- Normalizing constant for an exponential tilt. -/
noncomputable def tiltNormalizer {n : ℕ} (base : PosWeights n) (θ : ℝ) : ℝ≥0 :=
  Finset.univ.sum fun x : Support n => tiltWeight base θ x

/-- The normalizing constant is strictly positive. -/
theorem tiltNormalizer_pos {n : ℕ} (base : PosWeights n) (θ : ℝ) :
    0 < tiltNormalizer base θ := by
  unfold tiltNormalizer
  refine Finset.sum_pos (fun x _hx => tiltWeight_pos base θ x) ?_
  exact ⟨⟨0, Nat.succ_pos n⟩, by simp⟩

/-- The normalized exponential tilt as a positive PMF. -/
noncomputable def exponentialTilt {n : ℕ} (base : PosWeights n) (θ : ℝ) : PosPMF n where
  mass x := tiltWeight base θ x / tiltNormalizer base θ
  pos x := div_pos (tiltWeight_pos base θ x) (tiltNormalizer_pos base θ)
  sum_one := by
    rw [← Finset.sum_div]
    change tiltNormalizer base θ / tiltNormalizer base θ = 1
    exact div_self (ne_of_gt (tiltNormalizer_pos base θ))

/-- The exponential factor has MLR as the tilt parameter increases. -/
theorem nnexp_factor_mlr {n : ℕ} {θ₀ θ₁ : ℝ} (hθ : θ₀ ≤ θ₁)
    {x y : Support n} (hxy : x ≤ y) :
    nnexp (θ₁ * x.val) * nnexp (θ₀ * y.val) ≤
      nnexp (θ₁ * y.val) * nnexp (θ₀ * x.val) := by
  have hxyR : (x.val : ℝ) ≤ (y.val : ℝ) := by
    exact Nat.cast_le.mpr (Fin.le_iff_val_le_val.mp hxy)
  have hprod : 0 ≤ (θ₁ - θ₀) * ((y.val : ℝ) - x.val) :=
    mul_nonneg (sub_nonneg.mpr hθ) (sub_nonneg.mpr hxyR)
  have hlin : θ₁ * (x.val : ℝ) + θ₀ * (y.val : ℝ) ≤
      θ₁ * (y.val : ℝ) + θ₀ * (x.val : ℝ) := by
    nlinarith
  rw [nnexp_mul, nnexp_mul]
  exact nnexp_le_nnexp hlin

/-- Unnormalized exponential-tilt weights have MLR as the tilt parameter increases. -/
theorem tiltWeight_mlr {n : ℕ} (base : PosWeights n) {θ₀ θ₁ : ℝ} (hθ : θ₀ ≤ θ₁)
    {x y : Support n} (hxy : x ≤ y) :
    tiltWeight base θ₁ x * tiltWeight base θ₀ y ≤
      tiltWeight base θ₁ y * tiltWeight base θ₀ x := by
  have hExp := nnexp_factor_mlr hθ hxy
  have hScaled := mul_le_mul_left (mul_le_mul_left hExp (base.weight x)) (base.weight y)
  simpa [tiltWeight, mul_comm, mul_left_comm, mul_assoc] using hScaled

/-- Normalized exponential tilts have MLR as the tilt parameter increases. -/
theorem exponentialTilt_hasMLR {n : ℕ} (base : PosWeights n) {θ₀ θ₁ : ℝ}
    (hθ : θ₀ ≤ θ₁) :
    HasMLR (exponentialTilt base θ₀) (exponentialTilt base θ₁) := by
  intro x y hxy
  have hWeights := tiltWeight_mlr base hθ hxy
  have hScaled := mul_le_mul_left hWeights
    ((tiltNormalizer base θ₁)⁻¹ * (tiltNormalizer base θ₀)⁻¹)
  simpa [exponentialTilt, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hScaled

/-- Strict-parameter corollary for exponential tilts. -/
theorem exponentialTilt_hasMLR_of_lt {n : ℕ} (base : PosWeights n) {θ₀ θ₁ : ℝ}
    (hθ : θ₀ < θ₁) :
    HasMLR (exponentialTilt base θ₀) (exponentialTilt base θ₁) :=
  exponentialTilt_hasMLR base hθ.le

/-- Bayes admit sets for increasing exponential tilts are thresholds. -/
theorem exponentialTilt_bayesAdmit_isThreshold {n : ℕ} (base : PosWeights n)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ ≤ θ₁) (prior : Prior) :
    ∃ cut : Fin (n + 2), ∀ x : Support n,
      bayesAdmit (exponentialTilt base θ₀) (exponentialTilt base θ₁) prior x ↔
        x ∈ thresholdSet n cut :=
  bayesAdmit_isThreshold (exponentialTilt base θ₀) (exponentialTilt base θ₁) prior
    (exponentialTilt_hasMLR base hθ)

/-- Bayes risk for increasing exponential tilts is minimized by a threshold rule. -/
theorem exponentialTilt_threshold_bayesRisk_optimal {n : ℕ} (base : PosWeights n)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ ≤ θ₁) (prior : Prior) :
    ∃ cut : Fin (n + 2), ∀ R : Set (Support n),
      bayesRisk (exponentialTilt base θ₀) (exponentialTilt base θ₁) prior
          (thresholdSet n cut) ≤
        bayesRisk (exponentialTilt base θ₀) (exponentialTilt base θ₁) prior R :=
  threshold_bayesRisk_optimal (exponentialTilt base θ₀) (exponentialTilt base θ₁) prior
    (exponentialTilt_hasMLR base hθ)

/-- Cost-sensitive Bayes admit sets for increasing exponential tilts are thresholds. -/
theorem exponentialTilt_costedBayesAdmit_isThreshold {n : ℕ} (base : PosWeights n)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ ≤ θ₁) (prior : Prior) (costs : DecisionCosts) :
    ∃ cut : Fin (n + 2), ∀ x : Support n,
      costedBayesAdmit (exponentialTilt base θ₀) (exponentialTilt base θ₁) prior costs x ↔
        x ∈ thresholdSet n cut :=
  costedBayesAdmit_isThreshold (exponentialTilt base θ₀) (exponentialTilt base θ₁) prior
    costs (exponentialTilt_hasMLR base hθ)

/-- Cost-sensitive Bayes risk for increasing exponential tilts is minimized by a threshold rule. -/
theorem exponentialTilt_costed_threshold_bayesRisk_optimal {n : ℕ} (base : PosWeights n)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ ≤ θ₁) (prior : Prior) (costs : DecisionCosts) :
    ∃ cut : Fin (n + 2), ∀ R : Set (Support n),
      costedBayesRisk (exponentialTilt base θ₀) (exponentialTilt base θ₁) prior costs
          (thresholdSet n cut) ≤
        costedBayesRisk (exponentialTilt base θ₀) (exponentialTilt base θ₁) prior costs R :=
  costed_threshold_bayesRisk_optimal (exponentialTilt base θ₀) (exponentialTilt base θ₁) prior
    costs (exponentialTilt_hasMLR base hθ)

end OrdvecFormalization
