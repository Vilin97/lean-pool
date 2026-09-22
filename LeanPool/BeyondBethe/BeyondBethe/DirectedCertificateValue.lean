/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.ExecutableTransfer
import LeanPool.BeyondBethe.BeyondBethe.DirectedPairCost
import Mathlib.Tactic

/-! # Directed Certificate Value -/

open scoped BigOperators

namespace BeyondBethe

/-!
# Directed evaluation of the executable certificate

At the nearby KKT matrix, the Bethe objective has a particularly simple
logarithmic form.  It uses only the rational point, rational row and column
potentials, and logarithms of `X_ij` and `1-X_ij`; the irrational nearby
matrix never has to be materialized.
-/

def directedNearbyCoordinateLower
    (τ x : ℚ) (p : ℕ) : ℚ :=
  scheduledLogLower (1 - x) p +
    τ * x * scheduledLogLower x p

def directedNearbyBetheLower {n : ℕ}
    (τ : ℚ) (X : Matrix (Fin n) (Fin n) ℚ)
    (R C : Fin n → ℚ) (p : ℕ) : ℚ :=
  (∑ i, R i) + (∑ j, C j) +
    ∑ i, ∑ j, directedNearbyCoordinateLower τ (X i j) p

theorem weighted_potentials_eq_sum
    {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : IsDoublyStochastic X) (R C : Fin n → ℝ) :
    (∑ i, ∑ j, X i j * (R i + C j)) =
      (∑ i, R i) + ∑ j, C j := by
  have hrow : (∑ i, ∑ j, X i j * R i) = ∑ i, R i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul, hX.row_sum i, one_mul]
  have hcol : (∑ i, ∑ j, X i j * C j) = ∑ j, C j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul, hX.col_sum j, one_mul]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hrow, hcol]

theorem nearbyBetheObjective_eq_logExpression
    {n : ℕ} {τ : ℚ} {Xq : Matrix (Fin n) (Fin n) ℚ}
    (R C : Fin n → ℚ)
    (hX : IsDoublyStochastic (fun i j ↦ ((Xq i j : ℚ) : ℝ)))
    (hXint : ∀ i, IsInteriorProbabilityVector
      (fun j ↦ ((Xq i j : ℚ) : ℝ))) :
    betheObjective
        (nearbyKKTMatrix (τ : ℝ)
          (fun i j ↦ ((Xq i j : ℚ) : ℝ))
          (fun i ↦ (R i : ℝ)) (fun j ↦ (C j : ℝ)))
        (fun i j ↦ ((Xq i j : ℚ) : ℝ)) =
      (∑ i, (R i : ℝ)) + (∑ j, (C j : ℝ)) +
        ∑ i, ∑ j,
          (Real.log ((1 - Xq i j : ℚ) : ℝ) +
            (τ : ℝ) * (Xq i j : ℝ) *
              Real.log (Xq i j : ℝ)) := by
  let X : Matrix (Fin n) (Fin n) ℝ :=
    fun i j ↦ ((Xq i j : ℚ) : ℝ)
  let Rr : Fin n → ℝ := fun i ↦ (R i : ℝ)
  let Cr : Fin n → ℝ := fun j ↦ (C j : ℝ)
  have hpos : ∀ i j, 0 < X i j := fun i j ↦ (hXint i).2 j |>.1
  have hlt : ∀ i j, X i j < 1 := fun i j ↦ (hXint i).2 j |>.2
  have hpot := weighted_potentials_eq_sum hX Rr Cr
  unfold betheObjective
  change (∑ i, betheRowObjective
    (nearbyKKTMatrix (τ : ℝ) X Rr Cr) X i) = _
  simp_rw [betheRowObjective, Real.negMulLog_def]
  simp_rw [log_nearbyKKTMatrix hpos hlt]
  change (∑ i, ∑ j,
      (X i j * (Rr i + Cr j + (1 + (τ : ℝ)) * Real.log (X i j) +
          Real.log (1 - X i j)) +
        (-X i j * Real.log (X i j)) +
        (1 - X i j) * Real.log (1 - X i j))) = _
  have hcoordinate : ∀ i j,
      X i j * (Rr i + Cr j + (1 + (τ : ℝ)) * Real.log (X i j) +
          Real.log (1 - X i j)) +
        (-X i j * Real.log (X i j)) +
        (1 - X i j) * Real.log (1 - X i j) =
      X i j * (Rr i + Cr j) +
        (Real.log (1 - X i j) +
          (τ : ℝ) * X i j * Real.log (X i j)) := by
    intro i j
    ring
  simp_rw [hcoordinate, Finset.sum_add_distrib]
  rw [hpot]
  simp only [X, Rr, Cr]
  push_cast
  ring

theorem scheduledLogLower_error {q : ℚ} (hq : 0 < q) (p : ℕ) :
    Real.log (q : ℝ) ≤
      (scheduledLogLower q p : ℝ) + ((1 / 2 : ℚ) ^ p : ℚ) := by
  have hupper := log_le_scheduledLogUpper hq p
  have hwidthQ := scheduledLog_width_le hq p
  have hwidth :
      (scheduledLogUpper q p : ℝ) -
          (scheduledLogLower q p : ℝ) ≤
        (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) := by
    exact_mod_cast hwidthQ
  linarith

theorem directedNearbyCoordinateLower_bounds
    {τ x : ℚ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hx0 : 0 < x) (hx1 : x < 1) (p : ℕ) :
    (directedNearbyCoordinateLower τ x p : ℝ) ≤
        Real.log ((1 - x : ℚ) : ℝ) +
          (τ : ℝ) * (x : ℝ) * Real.log (x : ℝ) ∧
      Real.log ((1 - x : ℚ) : ℝ) +
          (τ : ℝ) * (x : ℝ) * Real.log (x : ℝ) ≤
        (directedNearbyCoordinateLower τ x p : ℝ) +
          2 * (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) := by
  have hcx : 0 < 1 - x := sub_pos.mpr hx1
  have hloX := scheduledLogLower_le_log hx0 p
  have hloC := scheduledLogLower_le_log hcx p
  have herrX := scheduledLogLower_error hx0 p
  have herrC := scheduledLogLower_error hcx p
  norm_num only [Rat.cast_sub, Rat.cast_one] at hloC herrC
  have hcoef0 : 0 ≤ (τ : ℝ) * (x : ℝ) := by positivity
  have hcoef1 : (τ : ℝ) * (x : ℝ) ≤ 1 := by
    have hτr : (0 : ℝ) ≤ (τ : ℝ) := by exact_mod_cast hτ0
    have hτr1 : (τ : ℝ) ≤ 1 := by exact_mod_cast hτ1
    have hxr : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx0.le
    have hxr1 : (x : ℝ) ≤ 1 := by exact_mod_cast hx1.le
    nlinarith
  rw [directedNearbyCoordinateLower]
  push_cast
  constructor
  · exact add_le_add hloC (mul_le_mul_of_nonneg_left hloX hcoef0)
  · have hscaled := mul_le_mul_of_nonneg_left herrX hcoef0
    have he : 0 ≤ ((((1 / 2 : ℚ) ^ p : ℚ)) : ℝ) := by positivity
    have hcoefError :
        ((τ : ℝ) * (x : ℝ)) *
            ((((1 / 2 : ℚ) ^ p : ℚ)) : ℝ) ≤
          ((((1 / 2 : ℚ) ^ p : ℚ)) : ℝ) :=
      mul_le_of_le_one_left he hcoef1
    norm_num only [Rat.cast_pow, Rat.cast_div, Rat.cast_one,
      Rat.cast_ofNat] at herrX herrC hscaled he hcoefError ⊢
    nlinarith

theorem directedNearbyBetheLower_bounds
    {n : ℕ} {τ : ℚ} {Xq : Matrix (Fin n) (Fin n) ℚ}
    (R C : Fin n → ℚ)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hX : IsDoublyStochastic (fun i j ↦ ((Xq i j : ℚ) : ℝ)))
    (hXint : ∀ i, IsInteriorProbabilityVector
      (fun j ↦ ((Xq i j : ℚ) : ℝ))) (p : ℕ) :
    (directedNearbyBetheLower τ Xq R C p : ℝ) ≤
        betheObjective
          (nearbyKKTMatrix (τ : ℝ)
            (fun i j ↦ ((Xq i j : ℚ) : ℝ))
            (fun i ↦ (R i : ℝ)) (fun j ↦ (C j : ℝ)))
          (fun i j ↦ ((Xq i j : ℚ) : ℝ)) ∧
      betheObjective
          (nearbyKKTMatrix (τ : ℝ)
            (fun i j ↦ ((Xq i j : ℚ) : ℝ))
            (fun i ↦ (R i : ℝ)) (fun j ↦ (C j : ℝ)))
          (fun i j ↦ ((Xq i j : ℚ) : ℝ)) ≤
        (directedNearbyBetheLower τ Xq R C p : ℝ) +
          2 * (n : ℝ) ^ 2 * (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) := by
  let exactCoordinate : Fin n → Fin n → ℝ := fun i j ↦
    Real.log ((1 - Xq i j : ℚ) : ℝ) +
      (τ : ℝ) * (Xq i j : ℝ) * Real.log (Xq i j : ℝ)
  let lowerCoordinate : Fin n → Fin n → ℝ := fun i j ↦
    (directedNearbyCoordinateLower τ (Xq i j) p : ℝ)
  have hcoord : ∀ i j,
      lowerCoordinate i j ≤ exactCoordinate i j ∧
        exactCoordinate i j ≤ lowerCoordinate i j +
          2 * (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) := by
    intro i j
    have hx0 : 0 < Xq i j := by
      have h := (hXint i).2 j |>.1
      change 0 < ((Xq i j : ℚ) : ℝ) at h
      exact Rat.cast_pos.mp h
    have hx1 : Xq i j < 1 := by
      have h := (hXint i).2 j |>.2
      change ((Xq i j : ℚ) : ℝ) < 1 at h
      exact (Rat.cast_lt (K := ℝ)).mp (by simpa using! h)
    exact directedNearbyCoordinateLower_bounds hτ0 hτ1 hx0 hx1 p
  have hsumLower : (∑ i, ∑ j, lowerCoordinate i j) ≤
      ∑ i, ∑ j, exactCoordinate i j :=
    Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ (hcoord i j).1
  have hsumUpper : (∑ i, ∑ j, exactCoordinate i j) ≤
      (∑ i, ∑ j, lowerCoordinate i j) +
        2 * (n : ℝ) ^ 2 * (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) := by
    calc
      (∑ i, ∑ j, exactCoordinate i j) ≤
          ∑ i, ∑ j, (lowerCoordinate i j +
            2 * (((1 / 2 : ℚ) ^ p : ℚ) : ℝ)) :=
        Finset.sum_le_sum fun i _ ↦
          Finset.sum_le_sum fun j _ ↦ (hcoord i j).2
      _ = (∑ i, ∑ j, lowerCoordinate i j) +
          2 * (n : ℝ) ^ 2 * (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) := by
        simp [Finset.sum_add_distrib]
        ring
  rw [nearbyBetheObjective_eq_logExpression R C hX hXint]
  rw [directedNearbyBetheLower]
  push_cast
  have hsumLower' :
      (∑ i, ∑ j, (directedNearbyCoordinateLower τ (Xq i j) p : ℝ)) ≤
        ∑ i, ∑ j, (Real.log ((1 - Xq i j : ℚ) : ℝ) +
          (τ : ℝ) * (Xq i j : ℝ) * Real.log (Xq i j : ℝ)) := by
    simpa only [lowerCoordinate, exactCoordinate] using! hsumLower
  have hsumUpper' :
      (∑ i, ∑ j, (Real.log ((1 - Xq i j : ℚ) : ℝ) +
          (τ : ℝ) * (Xq i j : ℝ) * Real.log (Xq i j : ℝ))) ≤
        (∑ i, ∑ j,
          (directedNearbyCoordinateLower τ (Xq i j) p : ℝ)) +
          2 * (n : ℝ) ^ 2 * (((1 / 2 : ℚ) ^ p : ℚ) : ℝ) := by
    simpa only [lowerCoordinate, exactCoordinate] using! hsumUpper
  norm_num only [Rat.cast_sub, Rat.cast_one, Rat.cast_pow,
    Rat.cast_div, Rat.cast_ofNat] at hsumLower' hsumUpper' ⊢
  constructor <;> linarith

/-- Fixed precision used for evaluating the final logarithmic certificate.
The additive constant is deliberately generous; it is independent of the
input and absorbs the tiny hard-coded structural scale. -/
def directedCertificatePrecision (n : ℕ) : ℕ := n + 400

@[simp] theorem directedCertificatePrecision_eq_pairCostPrecision (n : ℕ) :
    directedCertificatePrecision n = directedPairCostPrecision n := by
  rfl

def explicitKKTError : ℚ := explicitCertifiedEpsilon / 32

def explicitLogEvaluationLoss : ℚ := explicitCertifiedEpsilon / 32

def explicitExpEvaluationLoss : ℚ := explicitCertifiedEpsilon / 32

theorem explicitKKTError_pos : 0 < explicitKKTError := by
  exact div_pos explicitCertifiedEpsilon_pos (by norm_num)

theorem explicitLogEvaluationLoss_pos : 0 < explicitLogEvaluationLoss := by
  exact div_pos explicitCertifiedEpsilon_pos (by norm_num)

theorem explicitExpEvaluationLoss_pos : 0 < explicitExpEvaluationLoss := by
  exact div_pos explicitCertifiedEpsilon_pos (by norm_num)

theorem dyadic_399_le_logEvaluationLoss :
    (1 / 2 : ℝ) ^ 399 ≤ (explicitLogEvaluationLoss : ℝ) := by
  have hq : (1 / 2 : ℚ) ^ 399 ≤ explicitLogEvaluationLoss := by
    rw [explicitLogEvaluationLoss, explicitCertifiedEpsilon,
      explicitCertifiedEpsilon_eq]
    norm_num [explicitXi, explicitDelta, explicitEta, explicitRowRatio]
    exact (pow_le_pow_of_le_one (by norm_num : 0 ≤ (1 / 2 : ℚ))
      (by norm_num : (1 / 2 : ℚ) ≤ 1) (show 240 ≤ 399 by omega)).trans (by norm_num)
  have hcast : (((1 / 2 : ℚ) ^ 399 : ℚ) : ℝ) ≤
      (explicitLogEvaluationLoss : ℝ) := Rat.cast_le.mpr hq
  norm_num only [Rat.cast_pow, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat] at hcast
  exact hcast

theorem directedCertificatePrecision_error
    {n : ℕ} (hn : 1 ≤ n) :
    2 * (n : ℝ) ^ 2 *
        (((1 / 2 : ℚ) ^ directedCertificatePrecision n : ℚ) : ℝ) ≤
      (explicitLogEvaluationLoss : ℝ) * n := by
  have hnat : n ≤ 2 ^ n := n.lt_two_pow_self.le
  have hnatR : (n : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hnat
  have hpowpos : 0 < (2 : ℝ) ^ n := by positivity
  have hratio : (n : ℝ) * (1 / 2 : ℝ) ^ n ≤ 1 := by
    simp only [one_div, inv_pow]
    rw [mul_inv_le_iff₀ hpowpos]
    simpa using! hnatR
  have hconst := dyadic_399_le_logEvaluationLoss
  rw [directedCertificatePrecision, pow_add]
  norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div,
    Rat.cast_one, Rat.cast_ofNat]
  have hnR : (0 : ℝ) ≤ n := by positivity
  have hshift : 2 * (1 / 2 : ℝ) ^ 400 = (1 / 2 : ℝ) ^ 399 := by
    rw [show 400 = 399 + 1 by omega, pow_succ]
    ring
  have hratioScaled :
      (n : ℝ) * ((n : ℝ) * (1 / 2 : ℝ) ^ n) *
          (1 / 2 : ℝ) ^ 399 ≤
        (n : ℝ) * 1 * (1 / 2 : ℝ) ^ 399 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hratio hnR)
      (pow_nonneg (by norm_num) _)
  calc
    2 * (n : ℝ) ^ 2 *
          ((1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ 400) =
        (n : ℝ) *
          ((n : ℝ) * (1 / 2 : ℝ) ^ n) *
            (1 / 2 : ℝ) ^ 399 := by
      rw [← hshift]
      ring
    _ ≤ (n : ℝ) * 1 * (1 / 2 : ℝ) ^ 399 := hratioScaled
    _ = (n : ℝ) * (1 / 2 : ℝ) ^ 399 := by ring
    _ ≤ (n : ℝ) * (explicitLogEvaluationLoss : ℝ) :=
      mul_le_mul_of_nonneg_left hconst hnR
    _ = (explicitLogEvaluationLoss : ℝ) * n := by ring

/-- Rational lower endpoint for the complete nearby certificate logarithm. -/
def explicitDirectedCertificateLog {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) : ℚ :=
  directedNearbyBetheLower (explicitRegularizationScale n) X R C
      (directedCertificatePrecision n) +
    explicitCertifiedMatchingGain X - explicitKKTError * n

/-- Fully rational positive certificate computed from rational approximate-KKT
data. -/
def explicitDirectedCertificateValue {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) : ℚ :=
  rationalExpLower (explicitDirectedCertificateLog X R C)
    (explicitExpEvaluationLoss * n)

theorem explicitDirectedCertificateLog_bounds
    {n : ℕ} (hn : 2 ≤ n)
    {X : Matrix (Fin n) (Fin n) ℚ} (R C : Fin n → ℚ)
    (hX : IsDoublyStochastic (fun i j ↦ ((X i j : ℚ) : ℝ)))
    (hXint : ∀ i, IsInteriorProbabilityVector
      (fun j ↦ ((X i j : ℚ) : ℝ))) :
    (explicitDirectedCertificateLog X R C : ℝ) ≤
        executableNearbyCertificateLog (explicitKKTError : ℝ) X
          (fun i ↦ (R i : ℝ)) (fun j ↦ (C j : ℝ)) ∧
      executableNearbyCertificateLog (explicitKKTError : ℝ) X
          (fun i ↦ (R i : ℝ)) (fun j ↦ (C j : ℝ)) ≤
        (explicitDirectedCertificateLog X R C : ℝ) +
          (explicitLogEvaluationLoss : ℝ) * n := by
  have hτ0 : 0 ≤ explicitRegularizationScale n :=
    (explicitRegularizationScale_pos (show 0 < n by omega)).le
  have hτ1 : explicitRegularizationScale n ≤ 1 :=
    explicitRegularizationScale_le_one (show 1 ≤ n by omega)
  have hb := directedNearbyBetheLower_bounds R C hτ0 hτ1 hX hXint
    (directedCertificatePrecision n)
  have herr := directedCertificatePrecision_error (show 1 ≤ n by omega)
  rw [explicitDirectedCertificateLog, executableNearbyCertificateLog]
  norm_num only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast]
  constructor <;> linarith

theorem explicitDirectedCertificateValue_pos
    {n : ℕ} (hn : 1 ≤ n)
    (X : Matrix (Fin n) (Fin n) ℚ) (R C : Fin n → ℚ) :
    0 < (explicitDirectedCertificateValue X R C : ℝ) := by
  have hlossQ : 0 < explicitExpEvaluationLoss * n :=
    mul_pos explicitExpEvaluationLoss_pos (by exact_mod_cast hn)
  have h := rationalExpLower_bounds
    (s := explicitDirectedCertificateLog X R C) hlossQ
  exact (Real.exp_pos _).trans_le h.1

/-- The fully rational certificate inherits the positive-matrix estimate.
All three numerical losses are explicit: approximate KKT transfer, directed
logarithms, and directed exponentiation. -/
theorem explicitDirectedCertificate_twoSided
    (stableCoefficient : AnariOveisGharanStableCoefficient.{0})
    {n : ℕ} (hn : 2 ≤ n)
    {A : Matrix (Fin n) (Fin n) ℝ}
    {X : Matrix (Fin n) (Fin n) ℚ} {R C : Fin n → ℚ}
    (hA : Matrix.Positive A)
    (hX : IsDoublyStochastic (fun i j ↦ ((X i j : ℚ) : ℝ)))
    (hXint : ∀ i, IsInteriorProbabilityVector
      (fun j ↦ ((X i j : ℚ) : ℝ)))
    (happrox : HasApproximateLogKKT (explicitKKTError : ℝ)
      (explicitRegularizationScale n : ℝ) A
      (fun i j ↦ ((X i j : ℚ) : ℝ))
      (fun i ↦ (R i : ℝ)) (fun j ↦ (C j : ℝ))) :
    (explicitDirectedCertificateValue X R C : ℝ) ≤
        Matrix.permanent A ∧
      Matrix.permanent A ≤
        (preSmoothingBase (explicitCertifiedEpsilon : ℝ)) ^ n *
          (explicitDirectedCertificateValue X R C : ℝ) := by
  let qlog : ℝ := (explicitDirectedCertificateLog X R C : ℝ)
  let exactLog : ℝ := executableNearbyCertificateLog
    (explicitKKTError : ℝ) X
      (fun i ↦ (R i : ℝ)) (fun j ↦ (C j : ℝ))
  let qvalue : ℝ := (explicitDirectedCertificateValue X R C : ℝ)
  let L : ℝ := executableNearbyCertificateValue
    (explicitKKTError : ℝ) X
      (fun i ↦ (R i : ℝ)) (fun j ↦ (C j : ℝ))
  have hlog := explicitDirectedCertificateLog_bounds hn R C hX hXint
  have hlog' : qlog ≤ exactLog ∧
      exactLog ≤ qlog + (explicitLogEvaluationLoss : ℝ) * n := by
    simpa only [qlog, exactLog] using! hlog
  have hlossQ : 0 < explicitExpEvaluationLoss * n :=
    mul_pos explicitExpEvaluationLoss_pos (by exact_mod_cast (show 0 < n by omega))
  have hexpQ := rationalExpLower_bounds
    (s := explicitDirectedCertificateLog X R C) hlossQ
  have hexp : Real.exp
        (qlog - (explicitExpEvaluationLoss : ℝ) * n) ≤ qvalue ∧
      qvalue ≤ Real.exp qlog := by
    simpa only [qlog, qvalue, explicitDirectedCertificateValue,
      Rat.cast_mul, Rat.cast_natCast] using! hexpQ
  have htransfer := executableNearbyCertificate_twoSided
    stableCoefficient hn hA hX hXint happrox
  have htransfer' : L ≤ Matrix.permanent A ∧
      Matrix.permanent A ≤
        (Real.sqrt 2 * Real.exp
          (-((explicitCertifiedEpsilon : ℝ) -
            2 * (explicitKKTError : ℝ)))) ^ n * L := by
    simpa only [L, explicitCertifiedEpsilon] using! htransfer
  have hL : L = Real.exp exactLog := by
    rfl
  constructor
  · have hqL : qvalue ≤ L := by
      rw [hL]
      exact hexp.2.trans (Real.exp_le_exp.mpr hlog'.1)
    exact hqL.trans htransfer'.1
  · have hLq : L ≤
        (Real.exp (explicitLogEvaluationLoss : ℝ) *
          Real.exp (explicitExpEvaluationLoss : ℝ)) ^ n * qvalue := by
      rw [hL]
      have hfirst : Real.exp exactLog ≤
          (Real.exp (explicitLogEvaluationLoss : ℝ)) ^ n *
            Real.exp qlog := by
        calc
          Real.exp exactLog ≤ Real.exp
              (qlog + (explicitLogEvaluationLoss : ℝ) * n) :=
            Real.exp_le_exp.mpr hlog'.2
          _ = (Real.exp (explicitLogEvaluationLoss : ℝ)) ^ n *
              Real.exp qlog := by
            rw [Real.exp_add]
            rw [show (explicitLogEvaluationLoss : ℝ) * (n : ℝ) =
              (n : ℝ) * (explicitLogEvaluationLoss : ℝ) by ring,
              Real.exp_nat_mul]
            ring
      have hsecond : Real.exp qlog ≤
          (Real.exp (explicitExpEvaluationLoss : ℝ)) ^ n * qvalue := by
        have hfactor0 : 0 ≤
            (Real.exp (explicitExpEvaluationLoss : ℝ)) ^ n :=
          pow_nonneg (Real.exp_pos _).le n
        have hscaled := mul_le_mul_of_nonneg_left hexp.1 hfactor0
        have hid : (Real.exp (explicitExpEvaluationLoss : ℝ)) ^ n *
              Real.exp (qlog - (explicitExpEvaluationLoss : ℝ) * n) =
            Real.exp qlog := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          congr 1
          ring
        rwa [hid] at hscaled
      calc
        Real.exp exactLog ≤
            (Real.exp (explicitLogEvaluationLoss : ℝ)) ^ n *
              Real.exp qlog := hfirst
        _ ≤ (Real.exp (explicitLogEvaluationLoss : ℝ)) ^ n *
            ((Real.exp (explicitExpEvaluationLoss : ℝ)) ^ n * qvalue) :=
          mul_le_mul_of_nonneg_left hsecond
            (pow_nonneg (Real.exp_pos _).le n)
        _ = (Real.exp (explicitLogEvaluationLoss : ℝ) *
              Real.exp (explicitExpEvaluationLoss : ℝ)) ^ n * qvalue := by
          rw [mul_pow]
          ring
    have hraw := htransfer'.2.trans
      (mul_le_mul_of_nonneg_left hLq
        (pow_nonneg (mul_nonneg (Real.sqrt_nonneg _)
          (Real.exp_pos _).le) n))
    have hbase :
        (Real.sqrt 2 * Real.exp
            (-((explicitCertifiedEpsilon : ℝ) -
              2 * (explicitKKTError : ℝ)))) *
          (Real.exp (explicitLogEvaluationLoss : ℝ) *
            Real.exp (explicitExpEvaluationLoss : ℝ)) ≤
          preSmoothingBase (explicitCertifiedEpsilon : ℝ) := by
      rw [preSmoothingBase]
      have hε0 : 0 < (explicitCertifiedEpsilon : ℝ) := by
        exact_mod_cast explicitCertifiedEpsilon_pos
      have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      have hexpMono :
          Real.exp
              (-((explicitCertifiedEpsilon : ℝ) -
                2 * (explicitKKTError : ℝ)) +
                (explicitLogEvaluationLoss : ℝ) +
                (explicitExpEvaluationLoss : ℝ)) ≤
            Real.exp (-(explicitCertifiedEpsilon : ℝ) +
              (explicitCertifiedEpsilon : ℝ) / 4) := by
        apply Real.exp_le_exp.mpr
        norm_num [explicitKKTError, explicitLogEvaluationLoss,
          explicitExpEvaluationLoss]
        nlinarith
      calc
        Real.sqrt 2 * Real.exp
              (-((explicitCertifiedEpsilon : ℝ) -
                2 * (explicitKKTError : ℝ))) *
            (Real.exp (explicitLogEvaluationLoss : ℝ) *
              Real.exp (explicitExpEvaluationLoss : ℝ)) =
            Real.sqrt 2 * Real.exp
              (-((explicitCertifiedEpsilon : ℝ) -
                2 * (explicitKKTError : ℝ)) +
                (explicitLogEvaluationLoss : ℝ) +
                (explicitExpEvaluationLoss : ℝ)) := by
          rw [← Real.exp_add
            (explicitLogEvaluationLoss : ℝ)
            (explicitExpEvaluationLoss : ℝ)]
          rw [show Real.sqrt 2 * Real.exp
              (-((explicitCertifiedEpsilon : ℝ) -
                2 * (explicitKKTError : ℝ))) *
                Real.exp ((explicitLogEvaluationLoss : ℝ) +
                  (explicitExpEvaluationLoss : ℝ)) =
              Real.sqrt 2 *
                (Real.exp (-((explicitCertifiedEpsilon : ℝ) -
                  2 * (explicitKKTError : ℝ))) *
                Real.exp ((explicitLogEvaluationLoss : ℝ) +
                  (explicitExpEvaluationLoss : ℝ))) by ring]
          rw [← Real.exp_add]
          congr 2
          ring
        _ ≤ Real.sqrt 2 * Real.exp
            (-(explicitCertifiedEpsilon : ℝ) +
              (explicitCertifiedEpsilon : ℝ) / 4) :=
          mul_le_mul_of_nonneg_left hexpMono hsqrt.le
    have hbasePow := pow_le_pow_left₀
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)) hbase n
    calc
      Matrix.permanent A ≤
          ((Real.sqrt 2 * Real.exp
              (-((explicitCertifiedEpsilon : ℝ) -
                2 * (explicitKKTError : ℝ)))) *
            (Real.exp (explicitLogEvaluationLoss : ℝ) *
              Real.exp (explicitExpEvaluationLoss : ℝ))) ^ n * qvalue := by
        simpa [mul_pow, mul_assoc] using! hraw
      _ ≤ (preSmoothingBase (explicitCertifiedEpsilon : ℝ)) ^ n * qvalue :=
        mul_le_mul_of_nonneg_right hbasePow
          (explicitDirectedCertificateValue_pos (show 1 ≤ n by omega) X R C).le

end BeyondBethe
