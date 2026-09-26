/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.NumericalInterior
public import LeanPool.BeyondBethe.BeyondBethe.NumericalScales
public import LeanPool.BeyondBethe.BeyondBethe.DirectedElementary
public import Mathlib.Tactic

/-! # Executable Interior -/

@[expose] public section

namespace BeyondBethe

/-!
# Executable interior floor from binary input size

The analytic interior estimate is converted here into a rational dyadic floor
whose exponent is computed directly from the matrix encoding, the dimension,
and the rational regularization parameter.
-/

/-- The interior-bound quantity `n*(n*B+2*n^2)/τ + n^3`. -/
def numericalInteriorK0 (n B : ℕ) (τ : ℚ) : ℚ :=
  n * (n * B + 2 * n ^ 2) / τ + n ^ 3

/-- The ceiling of twice the numerical interior-bound quantity. -/
def numericalInteriorExponent (n B : ℕ) (τ : ℚ) : ℕ :=
  rationalCeilNat (2 * numericalInteriorK0 n B τ)

/-- The dyadic interior floor with exponent given by the numerical interior bound. -/
def numericalInteriorFloor (n B : ℕ) (τ : ℚ) : ℚ :=
  (1 / 2 : ℚ) ^ numericalInteriorExponent n B τ

theorem numericalInteriorK0_nonneg
    {n B : ℕ} {τ : ℚ} (hτ : 0 < τ) :
    0 ≤ numericalInteriorK0 n B τ := by
  rw [numericalInteriorK0]
  positivity

theorem numericalInteriorFloor_pos (n B : ℕ) (τ : ℚ) :
    0 < numericalInteriorFloor n B τ := by
  rw [numericalInteriorFloor]
  positivity

theorem numericalInteriorExponent_dominates
    {n B : ℕ} {τ : ℚ} (hτ : 0 < τ) :
    2 * numericalInteriorK0 n B τ ≤
      numericalInteriorExponent n B τ := by
  exact le_rationalCeilNat (mul_nonneg (by norm_num)
    (numericalInteriorK0_nonneg hτ))

theorem log_inv_dyadic_cast (B : ℕ) :
    Real.log (1 / ((((1 / 2 : ℚ) ^ B : ℚ)) : ℝ)) =
      (B : ℝ) * Real.log 2 := by
  norm_num only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  rw [show (1 / ((1 / 2 : ℝ) ^ B)) = (2 : ℝ) ^ B by
    simp only [one_div, inv_pow, inv_inv]]
  rw [Real.log_pow]

theorem numericalObjectiveRange_dyadic_le
    {n B : ℕ} (hn : 1 ≤ n) :
    numericalObjectiveRange n
        ((((1 / 2 : ℚ) ^ B : ℚ)) : ℝ) ≤
      (n : ℝ) * B + 2 * (n : ℝ) ^ 2 := by
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at h
    exact h
  have hlogn0 := log_natCast_le_natCast_mul_log_two hn
  have hlogn : Real.log n ≤ (n : ℝ) := by
    have hnreal : 0 ≤ (n : ℝ) := by positivity
    nlinarith
  have hloginv := log_inv_dyadic_cast B
  rw [numericalObjectiveRange, hloginv]
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hBreal : 0 ≤ (B : ℝ) := by positivity
  have hBlog : (B : ℝ) * Real.log 2 ≤ B := by
    simpa using mul_le_mul_of_nonneg_left hlog2 hBreal
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have htermB := mul_le_mul_of_nonneg_left hBlog hn0
  have htermn := mul_le_mul_of_nonneg_left hlogn hn0
  have hnle : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  linarith

theorem numericalInteriorK0_bounds_analytic
    {n B : ℕ} (hn : 1 ≤ n) {τ : ℚ} (hτ : 0 < τ) :
    (n : ℝ) * numericalObjectiveRange n
          ((((1 / 2 : ℚ) ^ B : ℚ)) : ℝ) / (τ : ℝ) +
        (n : ℝ) ^ 2 * Real.log n ≤
      (numericalInteriorK0 n B τ : ℝ) := by
  have hrange := numericalObjectiveRange_dyadic_le (B := B) hn
  have hτr : 0 < (τ : ℝ) := by exact_mod_cast hτ
  have hnlog := log_natCast_le_natCast_mul_log_two hn
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at h
    exact h
  have hlogn : Real.log n ≤ (n : ℝ) := by
    have hnreal : 0 ≤ (n : ℝ) := by positivity
    nlinarith
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hscaled := (div_le_div_iff_of_pos_right hτr).2
    (mul_le_mul_of_nonneg_left hrange hn0)
  have hlogterm := mul_le_mul_of_nonneg_left hlogn
    (sq_nonneg (n : ℝ))
  rw [numericalInteriorK0]
  push_cast
  norm_num only [Rat.cast_pow, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat] at hscaled
  nlinarith

theorem numericalInteriorK0_le_exponent_mul_log_two
    {n B : ℕ} {τ : ℚ} (hτ : 0 < τ) :
    (numericalInteriorK0 n B τ : ℝ) ≤
      (numericalInteriorExponent n B τ : ℝ) * Real.log 2 := by
  have hq := numericalInteriorExponent_dominates (n := n) (B := B) hτ
  have hqR : 2 * (numericalInteriorK0 n B τ : ℝ) ≤
      (numericalInteriorExponent n B τ : ℝ) := by
    exact_mod_cast hq
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hK0 := numericalInteriorK0_nonneg (n := n) (B := B) hτ
  have hqnonneg : 0 ≤ (numericalInteriorExponent n B τ : ℝ) := by positivity
  nlinarith

theorem lower_bound_of_log_inv_le_exponent
    {x : ℝ} (hx : 0 < x) {q : ℕ}
    (hlog : Real.log (1 / x) ≤ (q : ℝ) * Real.log 2) :
    ((1 / 2 : ℚ) ^ q : ℚ) ≤ x := by
  have hinvpos : 0 < 1 / x := one_div_pos.mpr hx
  have hpowpos : 0 < (2 : ℝ) ^ q := pow_pos (by norm_num) q
  have hlogpow : Real.log ((2 : ℝ) ^ q) = (q : ℝ) * Real.log 2 := by
    rw [Real.log_pow]
  have hinv : 1 / x ≤ (2 : ℝ) ^ q := by
    rw [← Real.log_le_log_iff hinvpos hpowpos, hlogpow]
    exact hlog
  have hone : 1 ≤ (2 : ℝ) ^ q * x := by
    exact (div_le_iff₀ hx).mp hinv
  have hfloor : 1 / (2 : ℝ) ^ q ≤ x := by
    exact (div_le_iff₀ hpowpos).2 (by simpa [mul_comm] using hone)
  norm_num only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  simpa only [one_div, inv_pow] using hfloor

/-- The exact regularized optimizer lies in the executable dyadic floor
body. -/
theorem regularizedOptimizer_meets_executable_floor
    {n : ℕ} (hn : 1 < n) {τ : ℚ} (hτ : 0 < τ)
    {Aq : Matrix (Fin n) (Fin n) ℚ}
    (hAq : ∀ i j, 0 < Aq i j) (hAupper : ∀ i j, Aq i j ≤ 1)
    {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : IsDoublyStochastic X)
    (hmax : ∀ Y, IsDoublyStochastic Y →
      regularizedBetheObjective (τ : ℝ)
        (fun i j ↦ (Aq i j : ℝ)) Y ≤
      regularizedBetheObjective (τ : ℝ)
        (fun i j ↦ (Aq i j : ℝ)) X) :
    ∀ i j,
      (numericalInteriorFloor n (rationalMatrixEntryBitBound Aq) τ : ℝ) ≤
        X i j ∧
      (numericalInteriorFloor n (rationalMatrixEntryBitBound Aq) τ : ℝ) ≤
        1 - X i j := by
  let B := rationalMatrixEntryBitBound Aq
  let m : ℚ := (1 / 2 : ℚ) ^ B
  have hmQ : 0 < m := by positivity
  have hm : 0 < (m : ℝ) := by exact_mod_cast hmQ
  have hAlower : ∀ i j, (m : ℝ) ≤ (Aq i j : ℝ) := by
    intro i j
    exact_mod_cast (matrix_dyadic_bitBound_lt_entry hAq i j).le
  have hApos : Matrix.Positive (fun i j ↦ (Aq i j : ℝ)) := by
    intro i j
    change 0 < ((Aq i j : ℚ) : ℝ)
    exact Rat.cast_pos.mpr (hAq i j)
  have hAupR : ∀ i j, (Aq i j : ℝ) ≤ 1 := by
    intro i j
    exact_mod_cast hAupper i j
  have hτR : 0 < (τ : ℝ) := by exact_mod_cast hτ
  have hanalytic := numericalInteriorK0_bounds_analytic
    (B := B) (show 1 ≤ n by omega) hτ
  have hexponent := numericalInteriorK0_le_exponent_mul_log_two
    (n := n) (B := B) hτ
  intro i j
  have hentry := regularizedBetheMaximizer_log_inv_entry_le
    hn hτR hm hApos hAlower hAupR hX hmax i j
  have hcomp := regularizedBetheMaximizer_log_inv_one_sub_entry_le
    hn hτR hm hApos hAlower hAupR hX hmax i j
  have hXint := regularizedBetheMaximizer_interior hn hτR hApos hX hmax
  have hbudget :
      (n : ℝ) * numericalObjectiveRange n (m : ℝ) / (τ : ℝ) +
          (n : ℝ) ^ 2 * Real.log n ≤
        (numericalInteriorExponent n B τ : ℝ) * Real.log 2 :=
    hanalytic.trans hexponent
  have hfloorEntry := lower_bound_of_log_inv_le_exponent
    ((hXint i).2 j |>.1) (hentry.trans hbudget)
  have hfloorComp := lower_bound_of_log_inv_le_exponent
    (sub_pos.mpr ((hXint i).2 j |>.2)) (hcomp.trans hbudget)
  simpa only [m, B, numericalInteriorFloor] using
    And.intro hfloorEntry hfloorComp

end BeyondBethe
