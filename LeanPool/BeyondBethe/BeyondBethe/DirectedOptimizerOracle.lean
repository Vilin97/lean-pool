/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.DirectedPairCost
public import LeanPool.BeyondBethe.BeyondBethe.Optimizer
public import LeanPool.BeyondBethe.BeyondBethe.NumericalAffine
public import Mathlib.Tactic

/-! # Directed Optimizer Oracle -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-!
# Directed rational values for the convex-optimization oracle

The weak optimization algorithm uses the convex function obtained by
negating the regularized Bethe objective.  This file gives rational lower and
upper endpoints for both a coordinate value and a coordinate of its gradient.
Every endpoint is executable and every error bound is stated in terms of the
prescribed dyadic precision.
-/

/-- Lower endpoint for one coordinate of the gradient of the negative
regularized Bethe objective. -/
def directedNegativeGradientLower
    (τ a x : ℚ) (p : ℕ) : ℚ :=
  -scheduledLogUpper a p +
    (1 + τ) * scheduledLogLower x p +
    scheduledLogLower (1 - x) p + (2 + τ)

/-- Upper endpoint for one coordinate of the gradient of the negative
regularized Bethe objective. -/
def directedNegativeGradientUpper
    (τ a x : ℚ) (p : ℕ) : ℚ :=
  -scheduledLogLower a p +
    (1 + τ) * scheduledLogUpper x p +
    scheduledLogUpper (1 - x) p + (2 + τ)

/-- The exact real coordinate of the negative gradient. -/
noncomputable def negativeRegularizedBetheGradientCoordinate
    (τ a x : ℝ) : ℝ :=
  -Real.log a + (1 + τ) * Real.log x +
    Real.log (1 - x) + (2 + τ)

theorem negativeRegularizedBetheGradientCoordinate_eq_neg
    {τ a x : ℝ} :
    negativeRegularizedBetheGradientCoordinate τ a x =
      -(Real.log a - (1 + τ) * Real.log x -
        Real.log (1 - x) - (2 + τ)) := by
  simp [negativeRegularizedBetheGradientCoordinate]
  ring

/-- A directed interval for the negative gradient has width at most four
dyadic units when `0 ≤ τ ≤ 1`. -/
theorem directedNegativeGradient_bounds
    {τ a x : ℚ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (ha : 0 < a) (hx0 : 0 < x) (hx1 : x < 1) (p : ℕ) :
    (directedNegativeGradientLower τ a x p : ℝ) ≤
        negativeRegularizedBetheGradientCoordinate
          (τ : ℝ) (a : ℝ) (x : ℝ) ∧
      negativeRegularizedBetheGradientCoordinate
          (τ : ℝ) (a : ℝ) (x : ℝ) ≤
        (directedNegativeGradientUpper τ a x p : ℝ) ∧
      (directedNegativeGradientUpper τ a x p : ℝ) -
          (directedNegativeGradientLower τ a x p : ℝ) ≤
        4 * (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) := by
  have hcx : 0 < 1 - x := sub_pos.mpr hx1
  have hAlo := scheduledLogLower_le_log ha p
  have hAup := log_le_scheduledLogUpper ha p
  have hXlo := scheduledLogLower_le_log hx0 p
  have hXup := log_le_scheduledLogUpper hx0 p
  have hClo := scheduledLogLower_le_log hcx p
  have hCup := log_le_scheduledLogUpper hcx p
  norm_num only [Rat.cast_sub, Rat.cast_one] at hClo hCup
  have hAgapQ := scheduledLog_width_le ha p
  have hXgapQ := scheduledLog_width_le hx0 p
  have hCgapQ := scheduledLog_width_le hcx p
  have hAgap :
      (scheduledLogUpper a p : ℝ) - (scheduledLogLower a p : ℝ) ≤
        (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) := by exact_mod_cast hAgapQ
  have hXgap :
      (scheduledLogUpper x p : ℝ) - (scheduledLogLower x p : ℝ) ≤
        (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) := by exact_mod_cast hXgapQ
  have hCgap :
      (scheduledLogUpper (1 - x) p : ℝ) -
          (scheduledLogLower (1 - x) p : ℝ) ≤
        (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) := by exact_mod_cast hCgapQ
  have hcoef0 : 0 ≤ (1 + τ : ℝ) := by exact_mod_cast (by linarith : (0 : ℚ) ≤ 1 + τ)
  have hcoef2 : (1 + τ : ℝ) ≤ 2 := by exact_mod_cast (by linarith : 1 + τ ≤ (2 : ℚ))
  have hscaledLower := mul_le_mul_of_nonneg_left hXlo hcoef0
  have hscaledUpper := mul_le_mul_of_nonneg_left hXup hcoef0
  have hdyadic : 0 ≤ ((((1 / 2 : ℚ) ^ p : ℚ)) : ℝ) := by positivity
  have hscaledGap :
      (1 + (τ : ℝ)) *
          ((scheduledLogUpper x p : ℝ) -
            (scheduledLogLower x p : ℝ)) ≤
        2 * (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) := by
    calc
      (1 + (τ : ℝ)) *
          ((scheduledLogUpper x p : ℝ) -
            (scheduledLogLower x p : ℝ)) ≤
          (1 + (τ : ℝ)) *
            (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_left hXgap hcoef0
      _ ≤ 2 * (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_right hcoef2 hdyadic
  constructor
  · rw [directedNegativeGradientLower,
      negativeRegularizedBetheGradientCoordinate]
    push_cast
    linarith
  constructor
  · rw [directedNegativeGradientUpper,
      negativeRegularizedBetheGradientCoordinate]
    push_cast
    linarith
  · rw [directedNegativeGradientUpper, directedNegativeGradientLower]
    push_cast
    norm_num only [Rat.cast_pow, Rat.cast_div, Rat.cast_one,
      Rat.cast_ofNat] at hAgap hCgap hscaledGap hdyadic ⊢
    linarith

/-- Lower endpoint for the negative of one regularized Bethe coordinate. -/
def directedNegativeObjectiveCoordinateLower
    (τ a x : ℚ) (p : ℕ) : ℚ :=
  -x * scheduledLogUpper a p +
    (1 + τ) * x * scheduledLogLower x p -
    (1 - x) * scheduledLogUpper (1 - x) p

/-- Upper endpoint for the negative of one regularized Bethe coordinate. -/
def directedNegativeObjectiveCoordinateUpper
    (τ a x : ℚ) (p : ℕ) : ℚ :=
  -x * scheduledLogLower a p +
    (1 + τ) * x * scheduledLogUpper x p -
    (1 - x) * scheduledLogLower (1 - x) p

/-- Exact negative coordinate value, written in logarithmic form on the
interior of the unit interval. -/
noncomputable def negativeRegularizedBetheCoordinate
    (τ a x : ℝ) : ℝ :=
  -x * Real.log a + (1 + τ) * x * Real.log x -
    (1 - x) * Real.log (1 - x)

theorem negativeRegularizedBetheCoordinate_eq_neg
    {τ a x : ℝ} :
    negativeRegularizedBetheCoordinate τ a x =
      -regularizedBetheCoordinate τ a x := by
  rw [negativeRegularizedBetheCoordinate, regularizedBetheCoordinate,
    Real.negMulLog_def]
  ring

/-- A directed interval for a negative objective coordinate has width at most
three dyadic units. -/
theorem directedNegativeObjectiveCoordinate_bounds
    {τ a x : ℚ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (ha : 0 < a) (hx0 : 0 < x) (hx1 : x < 1) (p : ℕ) :
    (directedNegativeObjectiveCoordinateLower τ a x p : ℝ) ≤
        negativeRegularizedBetheCoordinate (τ : ℝ) (a : ℝ) (x : ℝ) ∧
      negativeRegularizedBetheCoordinate (τ : ℝ) (a : ℝ) (x : ℝ) ≤
        (directedNegativeObjectiveCoordinateUpper τ a x p : ℝ) ∧
      (directedNegativeObjectiveCoordinateUpper τ a x p : ℝ) -
          (directedNegativeObjectiveCoordinateLower τ a x p : ℝ) ≤
        3 * (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) := by
  have hcx : 0 < 1 - x := sub_pos.mpr hx1
  have hAlo := scheduledLogLower_le_log ha p
  have hAup := log_le_scheduledLogUpper ha p
  have hXlo := scheduledLogLower_le_log hx0 p
  have hXup := log_le_scheduledLogUpper hx0 p
  have hClo := scheduledLogLower_le_log hcx p
  have hCup := log_le_scheduledLogUpper hcx p
  norm_num only [Rat.cast_sub, Rat.cast_one] at hClo hCup
  have hAgapQ := scheduledLog_width_le ha p
  have hXgapQ := scheduledLog_width_le hx0 p
  have hCgapQ := scheduledLog_width_le hcx p
  have hAgap :
      (scheduledLogUpper a p : ℝ) - (scheduledLogLower a p : ℝ) ≤
        (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) := by exact_mod_cast hAgapQ
  have hXgap :
      (scheduledLogUpper x p : ℝ) - (scheduledLogLower x p : ℝ) ≤
        (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) := by exact_mod_cast hXgapQ
  have hCgap :
      (scheduledLogUpper (1 - x) p : ℝ) -
          (scheduledLogLower (1 - x) p : ℝ) ≤
        (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) := by exact_mod_cast hCgapQ
  have hx0r : 0 ≤ (x : ℝ) := by exact_mod_cast hx0.le
  have hx1r : (x : ℝ) ≤ 1 := by exact_mod_cast hx1.le
  have hcx0r : 0 ≤ (1 - x : ℝ) := by exact_mod_cast (sub_nonneg.mpr hx1.le)
  have hcoef0 : 0 ≤ (1 + τ : ℝ) := by exact_mod_cast (by linarith : (0 : ℚ) ≤ 1 + τ)
  have hcoef2 : (1 + τ : ℝ) ≤ 2 := by exact_mod_cast (by linarith : 1 + τ ≤ (2 : ℚ))
  have hmiddle0 : 0 ≤ (1 + (τ : ℝ)) * (x : ℝ) := mul_nonneg hcoef0 hx0r
  have hmiddle2 : (1 + (τ : ℝ)) * (x : ℝ) ≤ 2 := by nlinarith
  have hdyadic : 0 ≤ ((((1 / 2 : ℚ) ^ p : ℚ)) : ℝ) := by positivity
  have hAweighted := mul_le_mul_of_nonneg_left hAgap hx0r
  have hXweighted := mul_le_mul_of_nonneg_left hXgap hmiddle0
  have hCweighted := mul_le_mul_of_nonneg_left hCgap hcx0r
  have hAweightBound :
      (x : ℝ) * (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) ≤
        (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) :=
    mul_le_of_le_one_left hdyadic hx1r
  have hXweightBound :
      ((1 + (τ : ℝ)) * (x : ℝ)) *
          (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) ≤
        2 * (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_right hmiddle2 hdyadic
  have hCweightBound :
      (1 - (x : ℝ)) * (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) ≤
        (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) :=
    mul_le_of_le_one_left hdyadic (by linarith)
  have hscaledXlo := mul_le_mul_of_nonneg_left hXlo hmiddle0
  have hscaledXup := mul_le_mul_of_nonneg_left hXup hmiddle0
  have hscaledAlo := mul_le_mul_of_nonneg_left hAlo hx0r
  have hscaledAup := mul_le_mul_of_nonneg_left hAup hx0r
  have hscaledClo := mul_le_mul_of_nonneg_left hClo hcx0r
  have hscaledCup := mul_le_mul_of_nonneg_left hCup hcx0r
  constructor
  · rw [directedNegativeObjectiveCoordinateLower,
      negativeRegularizedBetheCoordinate]
    push_cast
    linarith
  constructor
  · rw [directedNegativeObjectiveCoordinateUpper,
      negativeRegularizedBetheCoordinate]
    push_cast
    linarith
  · rw [directedNegativeObjectiveCoordinateUpper,
      directedNegativeObjectiveCoordinateLower]
    push_cast
    norm_num only [Rat.cast_pow, Rat.cast_div, Rat.cast_one,
      Rat.cast_ofNat] at hAweighted hXweighted hCweighted
        hAweightBound hXweightBound hCweightBound hdyadic ⊢
    nlinarith

/-- Rational lower endpoint for the complete negative objective. -/
def directedNegativeObjectiveLower {n : ℕ}
    (τ : ℚ) (A X : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) : ℚ :=
  ∑ i, ∑ j, directedNegativeObjectiveCoordinateLower τ (A i j) (X i j) p

/-- Rational upper endpoint for the complete negative objective. -/
def directedNegativeObjectiveUpper {n : ℕ}
    (τ : ℚ) (A X : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) : ℚ :=
  ∑ i, ∑ j, directedNegativeObjectiveCoordinateUpper τ (A i j) (X i j) p

/-- Summing the coordinate intervals yields an `3 n² 2⁻ᵖ` interval for the
complete negative objective. -/
theorem directedNegativeObjective_bounds
    {n : ℕ} {τ : ℚ} {A X : Matrix (Fin n) (Fin n) ℚ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hA : ∀ i j, 0 < A i j)
    (hX0 : ∀ i j, 0 < X i j) (hX1 : ∀ i j, X i j < 1) (p : ℕ) :
    (directedNegativeObjectiveLower τ A X p : ℝ) ≤
        -regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) (fun i j ↦ (X i j : ℝ)) ∧
      -regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) (fun i j ↦ (X i j : ℝ)) ≤
        (directedNegativeObjectiveUpper τ A X p : ℝ) ∧
      (directedNegativeObjectiveUpper τ A X p : ℝ) -
          (directedNegativeObjectiveLower τ A X p : ℝ) ≤
        3 * (n : ℝ) ^ 2 * (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) := by
  have hcoord := fun i j ↦ directedNegativeObjectiveCoordinate_bounds
    hτ0 hτ1 (hA i j) (hX0 i j) (hX1 i j) p
  rw [regularizedBetheObjective_eq_sum_coordinates (τ : ℝ)
    (fun i j => (A i j : ℝ)) (fun i j => (X i j : ℝ))]
  have hexact :
      -(∑ i, ∑ j, regularizedBetheCoordinate (τ : ℝ)
          (A i j : ℝ) (X i j : ℝ)) =
        ∑ i, ∑ j, negativeRegularizedBetheCoordinate
          (τ : ℝ) (A i j : ℝ) (X i j : ℝ) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact negativeRegularizedBetheCoordinate_eq_neg.symm
  rw [hexact]
  constructor
  · rw [directedNegativeObjectiveLower]
    push_cast
    exact Finset.sum_le_sum fun i _ ↦
      Finset.sum_le_sum fun j _ ↦ (hcoord i j).1
  constructor
  · rw [directedNegativeObjectiveUpper]
    push_cast
    exact Finset.sum_le_sum fun i _ ↦
      Finset.sum_le_sum fun j _ ↦ (hcoord i j).2.1
  · rw [directedNegativeObjectiveUpper, directedNegativeObjectiveLower]
    push_cast
    rw [← Finset.sum_sub_distrib]
    calc
      ∑ i, ((∑ j, (directedNegativeObjectiveCoordinateUpper τ
            (A i j) (X i j) p : ℝ)) -
          ∑ j, (directedNegativeObjectiveCoordinateLower τ
            (A i j) (X i j) p : ℝ)) ≤
          ∑ i, ∑ j, 3 * (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_le_sum fun j _ ↦ (hcoord i j).2.2
      _ = 3 * (n : ℝ) ^ 2 *
          (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) := by
        simp [Fintype.card_fin]
        ring
      _ = 3 * (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ p := by norm_num

end BeyondBethe
