/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Positivity.Finset
meta import Lean.Meta.Tactic.NormCast
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.NatFactorial

/-! Exact time-profile bookkeeping for the high, mean, and previous-corrector terms. -/

@[expose] public section


namespace EulerPacketTimeProfile

/-- Mean scale, given by `H^(2*p-2)`. -/
def meanScale (H : ℝ) (p : ℕ) : ℝ := H^(2*p-2)
/-- High scale, given by `γ*meanScale H p`. -/
def highScale (γ H : ℝ) (p : ℕ) : ℝ := γ*meanScale H p

theorem meanScale_pos (H : ℝ) (hH : 0 < H) (p : ℕ) : 0 < meanScale H p := pow_pos hH _
theorem highScale_pos (γ H : ℝ) (hγ : 0 < γ) (hH : 0 < H) (p : ℕ) :
    0 < highScale γ H p := mul_pos hγ (meanScale_pos H hH p)

theorem meanScale_mono (H : ℝ) (hH : 1 ≤ H) {i j : ℕ} (hij : i ≤ j) :
    meanScale H i ≤ meanScale H j :=
  pow_le_pow_right₀ hH (by omega : 2*i-2 ≤ 2*j-2)

theorem highScale_mono (γ H : ℝ) (hγ : 0 ≤ γ) (hH : 1 ≤ H) {i j : ℕ} (hij : i ≤ j) :
    highScale γ H i ≤ highScale γ H j :=
  mul_le_mul_of_nonneg_left (meanScale_mono H hH hij) hγ

theorem meanScale_slow_identity (H : ℝ) (i j p : ℕ)
    (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) :
    meanScale H i*meanScale H j*H^2 = meanScale H p := by
  simp only [meanScale,← pow_add]
  congr 1
  omega

theorem slow_mean_mean (H : ℝ) (hH : 1 ≤ H) (i j p : ℕ)
    (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) :
    meanScale H i*meanScale H j ≤ meanScale H p := by
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  have hs : (1 : ℝ) ≤ H^2 := by nlinarith
  calc
    _ ≤ (meanScale H i*meanScale H j)*H^2 :=
      le_mul_of_one_le_right (mul_nonneg (pow_nonneg hH0 _) (pow_nonneg hH0 _)) hs
    _ = _ := meanScale_slow_identity H i j p hi hj hp

theorem slow_high_high_mean (γ H : ℝ) (hγ : 0 ≤ γ) (hγH : γ ≤ H) (hH : 1 ≤ H)
    (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) :
    highScale γ H i*highScale γ H j ≤ meanScale H p := by
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  calc
    _ = γ^2*(meanScale H i*meanScale H j) := by unfold highScale; ring
    _ ≤ H^2*(meanScale H i*meanScale H j) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hγ hγH 2)
        (mul_nonneg (pow_nonneg hH0 _) (pow_nonneg hH0 _))
    _ = meanScale H i*meanScale H j*H^2 := by ring
    _ = _ := meanScale_slow_identity H i j p hi hj hp

theorem slow_high_high_high (γ H : ℝ) (hγ : 0 ≤ γ) (hγH : γ ≤ H) (hH : 1 ≤ H)
    (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) :
    highScale γ H i*highScale γ H j ≤ highScale γ H p := by
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  have hh : H ≤ H^2 := by nlinarith
  have hγ2 : γ^2 ≤ γ*H^2 := by nlinarith [mul_nonneg hγ (sub_nonneg.mpr (hγH.trans hh))]
  calc
    _ = γ^2*(meanScale H i*meanScale H j) := by unfold highScale; ring
    _ ≤ (γ*H^2)*(meanScale H i*meanScale H j) :=
      mul_le_mul_of_nonneg_right hγ2 (mul_nonneg (pow_nonneg hH0 _) (pow_nonneg hH0 _))
    _ = γ*(meanScale H i*meanScale H j*H^2) := by ring
    _ = _ := congrArg (γ * ·) (meanScale_slow_identity H i j p hi hj hp)

theorem slow_mean_high_high (γ H : ℝ) (hγ : 0 ≤ γ) (hH : 1 ≤ H)
    (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) :
    meanScale H i*highScale γ H j ≤ highScale γ H p := by
  have h := mul_le_mul_of_nonneg_left (slow_mean_mean H hH i j p hi hj hp) hγ
  simpa only [highScale,mul_left_comm] using h

theorem slow_mean_high_mean (γ H : ℝ) (hγ : 0 ≤ γ) (hγH : γ ≤ H) (hH : 1 ≤ H)
    (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) :
    meanScale H i*highScale γ H j ≤ meanScale H p := by
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  have hh : γ ≤ H^2 := by nlinarith
  calc
    _ = γ*(meanScale H i*meanScale H j) := by unfold highScale; ring
    _ ≤ H^2*(meanScale H i*meanScale H j) :=
      mul_le_mul_of_nonneg_right hh (mul_nonneg (pow_nonneg hH0 _) (pow_nonneg hH0 _))
    _ = meanScale H i*meanScale H j*H^2 := by ring
    _ = _ := meanScale_slow_identity H i j p hi hj hp

theorem fast_mean_high (γ H : ℝ) (i j p : ℕ)
    (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p + 1) :
    meanScale H i*highScale γ H j = highScale γ H p := by
  unfold highScale meanScale
  rw [mul_left_comm,← pow_add]
  congr 1
  congr 1
  omega

theorem fast_corrector_high_mean (γ H : ℝ) (hγ : 0 ≤ γ) (hγH : γ ≤ H) (hH : 1 ≤ H)
    (i j p : ℕ) (hi : 2 ≤ i) (hj : 1 ≤ j) (hp : i + j = p + 1) :
    highScale γ H (i-1)*highScale γ H j ≤ meanScale H p :=
  slow_high_high_mean γ H hγ hγH hH (i-1) j p (by omega) hj (by omega)

theorem fast_corrector_high_high (γ H : ℝ) (hγ : 0 ≤ γ) (hγH : γ ≤ H) (hH : 1 ≤ H)
    (i j p : ℕ) (hi : 2 ≤ i) (hj : 1 ≤ j) (hp : i + j = p + 1) :
    highScale γ H (i-1)*highScale γ H j ≤ highScale γ H p :=
  slow_high_high_high γ H hγ hγH hH (i-1) j p (by omega) hj (by omega)

theorem fast_corrector_corrector_mean (γ H : ℝ) (hγ : 0 ≤ γ) (hγH : γ ≤ H) (hH : 1 ≤ H)
    (i j p : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j) (hp : i + j = p + 1) :
    highScale γ H (i-1)*highScale γ H (j-1) ≤ meanScale H p :=
  (slow_high_high_mean γ H hγ hγH hH (i-1) (j-1) (p-1) (by omega) (by omega) (by omega)).trans
    (meanScale_mono H hH (Nat.sub_le p 1))

theorem fast_corrector_corrector_high (γ H : ℝ) (hγ : 0 ≤ γ) (hγH : γ ≤ H) (hH : 1 ≤ H)
    (i j p : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j) (hp : i + j = p + 1) :
    highScale γ H (i-1)*highScale γ H (j-1) ≤ highScale γ H p :=
  (slow_high_high_high γ H hγ hγH hH (i-1) (j-1) (p-1) (by omega) (by omega) (by omega)).trans
    (highScale_mono γ H hγ hH (Nat.sub_le p 1))

theorem previous_linear_mean (γ H : ℝ) (hγ : 0 ≤ γ) (hγH : γ ≤ H) (hH : 1 ≤ H)
    (p : ℕ) (hp : 2 ≤ p) : highScale γ H (p-1) ≤ meanScale H p := by
  have h := slow_mean_high_mean γ H hγ hγH hH 1 (p-1) p (by omega) (by omega) (by omega)
  simpa only [meanScale,show 2*1-2=0 by omega,pow_zero,one_mul] using h

end EulerPacketTimeProfile
