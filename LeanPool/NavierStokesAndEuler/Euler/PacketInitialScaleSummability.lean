/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketUniformFrequencyScales
import LeanPool.NavierStokesAndEuler.Euler.PacketSourceParameterScales
import Mathlib.Algebra.Order.Ring.Star

/-! The two literal initial-increment majorants are summable on the
source scale sequence. The mean retains its full inverse-frequency square. -/

@[expose] public section


noncomputable section

namespace EulerPacketInitialScale

open Real EulerPacketSourceScales EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketUniformFrequencyScales
  EulerPacketSourceParameterScales

/-- High majorant, given by `(supportScale J X n)⁻¹^m*(frequency J X n)^m *
(K*(parameterEnvelope J C c p q X n)^N)*exp (-scaleSequence J X n/8)`. -/
def highMajorant (J : ℕ) (C c K : ℝ) (p q N m : ℕ) (X : ℝ) (n : ℕ) : ℝ :=
  (supportScale J X n)⁻¹^m*(frequency J X n)^m *
    (K*(parameterEnvelope J C c p q X n)^N)*exp (-scaleSequence J X n/8)

/-- Mean majorant, given by `(supportScale J X n)⁻¹^m/(frequency J X n)^2 *
(K*(parameterEnvelope J C c p q X n)^N)`. -/
def meanMajorant (J : ℕ) (C c K : ℝ) (p q N m : ℕ) (X : ℝ) (n : ℕ) : ℝ :=
  (supportScale J X n)⁻¹^m/(frequency J X n)^2 *
    (K*(parameterEnvelope J C c p q X n)^N)

theorem high_expansion (J : ℕ) (C c K : ℝ) (p q N m : ℕ) (X : ℝ) (n : ℕ) :
    highMajorant J C c K p q N m X n =
      (K*C^N)*((J+n : ℕ) : ℝ)^(p*N)*(scaleSequence J X n)^(q*N) *
        exp (-(scaleSequence J X n/8) +
          (m : ℝ)*(scaleSequence J X n/((J+n : ℕ) : ℝ)^2) +
          (m : ℝ)*(scaleSequence J X n/((J+n : ℕ) : ℝ)^(7/2 : ℝ)) +
          (N : ℝ)*(c*(scaleSequence J X n/((J-1+n : ℕ) : ℝ)^3))) := by
  simp only [highMajorant,parameterEnvelope,supportScale,frequency,mul_pow,
    ← pow_mul,exp_add,exp_nat_mul,neg_div,exp_neg,inv_inv]
  ring

theorem mean_expansion (J : ℕ) (C c K : ℝ) (p q N m : ℕ) (X : ℝ) (n : ℕ) :
    meanMajorant J C c K p q N m X n =
      (K*C^N)*((J+n : ℕ) : ℝ)^(p*N)*(scaleSequence J X n)^(q*N) *
        exp (-2*(scaleSequence J X n/((J+n : ℕ) : ℝ)^2) +
          (m : ℝ)*(scaleSequence J X n/((J+n : ℕ) : ℝ)^(7/2 : ℝ)) +
          (N : ℝ)*(c*(scaleSequence J X n/((J-1+n : ℕ) : ℝ)^3))) := by
  have he (x : ℝ) : exp (-2*x)=((exp x)^2)⁻¹ := by
    rw [show -2*x=-(2*x) by ring,exp_neg,show (2 : ℝ)*x=(2 : ℕ)*x by norm_num,
      exp_nat_mul]
  simp only [meanMajorant,parameterEnvelope,supportScale,frequency,mul_pow,
    ← pow_mul,exp_add,exp_nat_mul,neg_div,exp_neg,inv_inv,he]
  ring

theorem current_real_power_le_previous (J : ℕ) (hJ : 2 ≤ J)
    (X : ℝ) (hX : 1 ≤ X) (n p : ℕ) (a : ℝ) (hpa : (p : ℝ) ≤ a) :
    scaleSequence J X n/((J+n : ℕ) : ℝ)^a ≤
      scaleSequence J X n/((J-1+n : ℕ) : ℝ)^p := by
  have hj : (1 : ℝ) ≤ (J+n : ℕ) := by exact_mod_cast (show 1 ≤ J+n by omega)
  have hp : (1 : ℝ) ≤ (J-1+n : ℕ) := by exact_mod_cast (show 1 ≤ J-1+n by omega)
  have hjp : ((J-1+n : ℕ) : ℝ) ≤ (J+n : ℕ) := by exact_mod_cast (show J-1+n ≤ J+n by omega)
  have hb : ((J-1+n : ℕ) : ℝ)^p ≤ ((J+n : ℕ) : ℝ)^a :=
    (pow_le_pow_left₀ (zero_le_one.trans hp) hjp p).trans
      (by simpa only [rpow_natCast] using rpow_le_rpow_of_exponent_le hj hpa)
  exact div_le_div_of_nonneg_left (zero_le_one.trans (sequence_one_le J (by omega) X hX n))
    (by positivity) hb

theorem high_summable (J : ℕ) (hJ : 2 ≤ J) (C c K : ℝ)
    (hC : 0 < C) (hc : 0 ≤ c) (hK : 0 < K)
    (p q N m : ℕ) (X : ℝ) (hX : 1 ≤ X) :
    Summable (highMajorant J C c K p q N m X) := by
  have hs := polynomial_source_scale_summable J 1 2 (by omega)
    (scaleSequence J X) (zero_lt_one.trans_le hX) (scaleSequence_succ J X)
    0 (1/8) (2*(m : ℝ)+(N : ℝ)*c) (K*C^N) (p*N) (q*N)
    (by norm_num) (by norm_num) (by norm_num) (by positivity)
  apply hs.of_nonneg_of_le
  · intro n
    unfold highMajorant parameterEnvelope supportScale frequency
    have hx := zero_le_one.trans (sequence_one_le J (by omega) X hX n)
    positivity
  · intro n
    rw [high_expansion]
    have hx := zero_le_one.trans (sequence_one_le J (by omega) X hX n)
    have hp : (1 : ℝ) ≤ (J-1+n : ℕ) := by exact_mod_cast (show 1 ≤ J-1+n by omega)
    have h1 := current_real_power_le_previous J hJ X hX n 2 2 (by norm_num)
    norm_num only [rpow_ofNat] at h1
    have h2 := current_real_power_le_previous J hJ X hX n 2 (7/2) (by norm_num)
    have h3 : scaleSequence J X n/((J-1+n : ℕ) : ℝ)^3 ≤
        scaleSequence J X n/((J-1+n : ℕ) : ℝ)^2 :=
      div_le_div_of_nonneg_left hx (by positivity) (pow_le_pow_right₀ hp (by decide))
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    apply exp_le_exp.mpr
    simp only [rpow_zero,div_one]
    nlinarith only [mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg m),
      mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg m),
      mul_le_mul_of_nonneg_left h3 (mul_nonneg (Nat.cast_nonneg N) hc)]

theorem mean_summable (J : ℕ) (hJ : 2 ≤ J) (C c K : ℝ)
    (hC : 0 < C) (hK : 0 < K)
    (p q N m : ℕ) (X : ℝ) (hX : 1 ≤ X) :
    Summable (meanMajorant J C c K p q N m X) := by
  have hs := polynomial_source_scale_summable J 1 3 (by omega)
    (scaleSequence J X) (zero_lt_one.trans_le hX) (scaleSequence_succ J X)
    2 2 ((m : ℝ)+(N : ℝ)*c) (K*C^N) (p*N) (q*N)
    (by norm_num) (by norm_num) (by norm_num) (by positivity)
  apply hs.of_nonneg_of_le
  · intro n
    unfold meanMajorant parameterEnvelope supportScale frequency
    have hx := zero_le_one.trans (sequence_one_le J (by omega) X hX n)
    positivity
  · intro n
    rw [mean_expansion]
    have hx := zero_le_one.trans (sequence_one_le J (by omega) X hX n)
    have h1 := current_real_power_le_previous J hJ X hX n 3 (7/2) (by norm_num)
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    apply exp_le_exp.mpr
    norm_num only [rpow_ofNat]
    nlinarith only [mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg m)]

end EulerPacketInitialScale
