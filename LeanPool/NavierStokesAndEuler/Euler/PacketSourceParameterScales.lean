/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketBaseGuardScales
import LeanPool.NavierStokesAndEuler.Euler.Foundations.Scale
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD

/-! Elementary bounds for the literal source parameters in (39).
Polynomial factors include the growing base core constant and inverse
time; no parameter depending on the base scale is treated as fixed. -/

@[expose] public section


noncomputable section

namespace EulerPacketSourceParameterScales

open Real EulerScale EulerPacketSourceScales EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketBaseGuardScales

/-- Predecessor exponent, given by `scaleSequence J X n/((J-1+n : ℕ) : ℝ)^3`. -/
def predecessorExponent (J : ℕ) (X : ℝ) (n : ℕ) : ℝ :=
  scaleSequence J X n/((J-1+n : ℕ) : ℝ)^3

/-- Polynomial factor, given by `((J+n : ℕ) : ℝ)^20*(scaleSequence J X n)^1000`. -/
def polynomialFactor (J : ℕ) (X : ℝ) (n : ℕ) : ℝ :=
  ((J+n : ℕ) : ℝ)^20*(scaleSequence J X n)^1000

theorem sequence_one_le (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 1 ≤ X) (n : ℕ) :
    1 ≤ scaleSequence J X n :=
  quadratic_growth_one_le J hJ (scaleSequence J X) hX (scaleSequence_succ J X) n

theorem sequence_initial_le (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 0 ≤ X) (n : ℕ) :
    X ≤ scaleSequence J X n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hj : (1 : ℝ) ≤ (J+n : ℕ) := by exact_mod_cast (show 1 ≤ J+n by omega)
    rw [scaleSequence_succ]
    exact ih.trans (le_mul_of_one_le_left (hX.trans ih) (one_le_pow₀ hj))

theorem predecessorExponent_nonneg (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 1 ≤ X) (n : ℕ) :
    0 ≤ predecessorExponent J X n := by
  have hx := zero_le_one.trans (sequence_one_le J hJ X hX n)
  unfold predecessorExponent
  positivity

theorem exponential_one_le (J : ℕ) (hJ : 1 ≤ J) (X c : ℝ) (hX : 1 ≤ X)
    (hc : 0 ≤ c) (n : ℕ) : 1 ≤ exp (c*predecessorExponent J X n) :=
  one_le_exp (mul_nonneg hc (predecessorExponent_nonneg J hJ X hX n))

theorem polynomialFactor_one (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 1 ≤ X) (n : ℕ) :
    1 ≤ polynomialFactor J X n := by
  have hj : (1 : ℝ) ≤ (J+n : ℕ) := by exact_mod_cast (show 1 ≤ J+n by omega)
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hj)
    (one_le_pow₀ (sequence_one_le J hJ X hX n))

theorem monomial_le_polynomialFactor (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 1 ≤ X)
    (n p q : ℕ) (hp : p ≤ 20) (hq : q ≤ 1000) :
    ((J+n : ℕ) : ℝ)^p*(scaleSequence J X n)^q ≤ polynomialFactor J X n := by
  have hj : (1 : ℝ) ≤ (J+n : ℕ) := by exact_mod_cast (show 1 ≤ J+n by omega)
  have hx := sequence_one_le J hJ X hX n
  exact mul_le_mul (pow_le_pow_right₀ hj hp) (pow_le_pow_right₀ hx hq)
    (pow_nonneg (zero_le_one.trans hx) q) (pow_nonneg (zero_le_one.trans hj) 20)

theorem predecessor_power_le (J : ℕ) (hJ : 2 ≤ J) (X : ℝ) (hX : 1 ≤ X)
    (n p : ℕ) (hp : 3 ≤ p) :
    scaleSequence J X n/((J-1+n : ℕ) : ℝ)^p ≤ predecessorExponent J X n := by
  have hj : (1 : ℝ) ≤ (J-1+n : ℕ) := by exact_mod_cast (show 1 ≤ J-1+n by omega)
  have hx := zero_le_one.trans (sequence_one_le J (by omega) X hX n)
  exact div_le_div_of_nonneg_left hx (by positivity) (pow_le_pow_right₀ hj hp)

theorem current_power_le (J : ℕ) (hJ : 2 ≤ J) (X : ℝ) (hX : 1 ≤ X)
    (n p : ℕ) (hp : 3 ≤ p) :
    scaleSequence J X n/((J+n : ℕ) : ℝ)^p ≤ predecessorExponent J X n := by
  have hj : (1 : ℝ) ≤ (J-1+n : ℕ) := by exact_mod_cast (show 1 ≤ J-1+n by omega)
  have hjn : ((J-1+n : ℕ) : ℝ) ≤ (J+n : ℕ) := by exact_mod_cast (show J-1+n ≤ J+n by omega)
  have hx := zero_le_one.trans (sequence_one_le J (by omega) X hX n)
  exact div_le_div_of_nonneg_left hx (by positivity)
    ((pow_le_pow_right₀ hj hp).trans (pow_le_pow_left₀ (zero_le_one.trans hj) hjn p))

theorem previousFrequency_power_le (J D : ℕ) (hJ : 2 ≤ J) (X c : ℝ)
    (hX : 1 ≤ X) (hc : 0 ≤ c)
    (hbase : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4)) (n : ℕ) :
    previousFrequency J D X n^c ≤ exp (c*predecessorExponent J X n) := by
  have hk := previousFrequency_le_normal J D (by omega) X hbase n
  have hx0 : 0 < X := zero_lt_one.trans_le hX
  calc
    _ ≤ (exp (scaleSequence J X n/((J-1+n : ℕ) : ℝ)^4))^c :=
      rpow_le_rpow (previousFrequency_pos J D hx0 n).le hk hc
    _ = exp (c*(scaleSequence J X n/((J-1+n : ℕ) : ℝ)^4)) := by
      rw [← exp_mul,mul_comm]
    _ ≤ _ := exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (predecessor_power_le J hJ X hX n 4 (by decide)) hc)

theorem previousShear_le_exponential (J : ℕ) (hJ : 2 ≤ J) (X : ℝ) (hX : 1 ≤ X)
    (hbase : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7)) (n : ℕ) :
    previousShear J X n ≤ exp (predecessorExponent J X n) :=
  (previousShear_le_normal J (by omega) X hbase n).trans
    (exp_le_exp.mpr (predecessor_power_le J hJ X hX n 7 (by decide)))

theorem shear_le_exponential (J : ℕ) (hJ : 2 ≤ J) (X : ℝ) (hX : 1 ≤ X) (n : ℕ) :
    shear J X n ≤ exp (predecessorExponent J X n) :=
  exp_le_exp.mpr (current_power_le J hJ X hX n 5 (by decide))

theorem spike_inverse_le_exponential (J : ℕ) (hJ : 2 ≤ J) (X : ℝ) (hX : 1 ≤ X) (n : ℕ) :
    (spike J X n)⁻¹ ≤ exp (predecessorExponent J X n) := by
  unfold spike
  rw [← exp_neg]
  have he : -(-scaleSequence J X n/((J+n : ℕ) : ℝ)^3) =
      scaleSequence J X n/((J+n : ℕ) : ℝ)^3 := by ring
  rw [he]
  exact exp_le_exp.mpr (current_power_le J hJ X hX n 3 le_rfl)

theorem base_inverse_time_le (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 1 ≤ X) :
    12/baseHorizon J X ≤ 2*X^1000 := by
  have hx0 : 0 < X := zero_lt_one.trans_le hX
  have hj : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hj0 : (0 : ℝ) < J := zero_lt_one.trans_le hj
  have he : 12/baseHorizon J X=2*X^498/(J : ℝ)^2 := by
    unfold baseHorizon
    rw [rpow_neg hx0.le]
    norm_num only [rpow_ofNat]
    field_simp
    ring
  rw [he]
  calc
    _ ≤ 2*X^498 := div_le_self (by positivity) (one_le_pow₀ hj)
    _ ≤ 2*X^1000 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX (by decide)) (by norm_num)

theorem inverse_time_le_factor (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 1 ≤ X) (n : ℕ) :
    12/baseHorizon J X ≤ 2*polynomialFactor J X n := by
  have hxn := sequence_initial_le J hJ X (zero_le_one.trans hX) n
  have hp := monomial_le_polynomialFactor J hJ X hX n 0 1000 (by decide) le_rfl
  simp only [pow_zero,one_mul] at hp
  exact (base_inverse_time_le J hJ X hX).trans
    (mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (zero_le_one.trans hX) hxn 1000).trans hp)
      (by norm_num))

end EulerPacketSourceParameterScales
