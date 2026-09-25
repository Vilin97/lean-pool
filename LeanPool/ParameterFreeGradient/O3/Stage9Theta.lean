/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.O3.Euclidean

/-!
# Source-exact OGM-G theta and kappa coefficients

This file isolates the scalar coefficient arithmetic in TeX Lemma `lem:ogmg`.
The representation is Nat-indexed because the certificate sums over
`i = 0, ..., n`; every theorem that uses a source index records the appropriate
boundary hypothesis explicitly.
-/

@[expose] public section

namespace O3

/-- The source OGM-G coefficient `theta_i` at horizon `n`.  Index zero uses
the special doubled radical, while positive indices use the ordinary backward
tail ending in `theta_n = 1`. -/
noncomputable def stage9Theta (n i : ℕ) : ℝ :=
  if i = 0 then ogmgThetaZero n else ogmgThetaTail (n - i)

@[simp] theorem stage9Theta_zero (n : ℕ) :
    stage9Theta n 0 = ogmgThetaZero n := by
  simp [stage9Theta]

theorem stage9Theta_of_pos {n i : ℕ} (hi : 0 < i) :
    stage9Theta n i = ogmgThetaTail (n - i) := by
  simp [stage9Theta, Nat.ne_of_gt hi]

@[simp] theorem stage9Theta_endpoint {n : ℕ} (hn : 1 ≤ n) :
    stage9Theta n n = 1 := by
  rw [stage9Theta_of_pos (lt_of_lt_of_le Nat.zero_lt_one hn)]
  simp [ogmgThetaTail]

theorem thetaZeroStep_pos (t : ℝ) : 0 < thetaZeroStep t := by
  unfold thetaZeroStep
  positivity

theorem thetaStep_gt_half (t : ℝ) : (1 : ℝ) / 2 < thetaStep t := by
  unfold thetaStep
  have := Real.sqrt_pos.2 (by positivity : (0 : ℝ) < 1 + 4 * t ^ 2)
  linarith

theorem thetaZeroStep_gt_half (t : ℝ) : (1 : ℝ) / 2 < thetaZeroStep t := by
  unfold thetaZeroStep
  have := Real.sqrt_pos.2 (by positivity : (0 : ℝ) < 1 + 8 * t ^ 2)
  linarith

theorem stage9Theta_pos (n i : ℕ) : 0 < stage9Theta n i := by
  by_cases hi : i = 0
  · subst i
    rw [stage9Theta_zero, ogmgThetaZero]
    exact thetaZeroStep_pos _
  · rw [stage9Theta, ite_eq_right hi]
    exact ogmgThetaTail_pos _

/-- In particular every denominator `theta_i` used by OGM-G is positive. -/
theorem stage9Theta_ne_zero (n i : ℕ) : stage9Theta n i ≠ 0 :=
  (stage9Theta_pos n i).ne'

/-- The other source denominator `2 theta_i - 1` is strictly positive. -/
theorem stage9_two_mul_theta_sub_one_pos (n i : ℕ) :
    0 < 2 * stage9Theta n i - 1 := by
  by_cases hi : i = 0
  · subst i
    rw [stage9Theta_zero, ogmgThetaZero]
    have h := thetaZeroStep_gt_half (ogmgThetaTail (n - 1))
    linarith
  · rw [stage9Theta, ite_eq_right hi]
    cases hdist : n - i with
    | zero =>
        simp [ogmgThetaTail]
    | succ k =>
        rw [ogmgThetaTail]
        have h := thetaStep_gt_half (ogmgThetaTail k)
        linarith

theorem stage9_two_mul_theta_sub_one_ne_zero (n i : ℕ) :
    2 * stage9Theta n i - 1 ≠ 0 :=
  (stage9_two_mul_theta_sub_one_pos n i).ne'

/-- The ordinary backward equation, valid exactly at `1 <= i < n`. -/
theorem stage9Theta_ordinary_equation {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    (stage9Theta n i) ^ 2 - stage9Theta n i =
      (stage9Theta n (i + 1)) ^ 2 := by
  have hip : 0 < i := lt_of_lt_of_le Nat.zero_lt_one hi
  have hisp : 0 < i + 1 := by omega
  rw [stage9Theta_of_pos hip, stage9Theta_of_pos hisp]
  have hsub : n - i = (n - (i + 1)) + 1 := by omega
  rw [hsub, ogmgThetaTail]
  exact thetaStep_equation _

/-- The source's special doubled first equation. -/
theorem stage9Theta_special_equation {n : ℕ} (_hn : 1 ≤ n) :
    (stage9Theta n 0) ^ 2 - stage9Theta n 0 =
      2 * (stage9Theta n 1) ^ 2 := by
  rw [stage9Theta_zero, ogmgThetaZero,
    stage9Theta_of_pos (by omega : 0 < (1 : ℕ))]
  have hsub : n - 1 = n - 1 := rfl
  exact thetaZeroStep_equation _

/-- Adjacent theta coefficients decrease with their source index. -/
theorem stage9Theta_succ_le {n i : ℕ} (hin : i < n) :
    stage9Theta n (i + 1) ≤ stage9Theta n i := by
  by_cases hi : i = 0
  · subst i
    rw [stage9Theta_zero, ogmgThetaZero,
      stage9Theta_of_pos (by omega : 0 < (0 + 1 : ℕ))]
    have hn : 1 ≤ n := by omega
    have hsqrt : 1 ≤ Real.sqrt 2 := by
      exact (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
    have htpos := ogmgThetaTail_pos (n - 1)
    have hz := thetaZeroStep_ge_sqrtTwo_mul htpos.le
    nlinarith
  · have hip : 0 < i := Nat.pos_of_ne_zero hi
    rw [stage9Theta_of_pos hip,
      stage9Theta_of_pos (by omega : 0 < i + 1)]
    have hsub : n - i = (n - (i + 1)) + 1 := by omega
    rw [hsub, ogmgThetaTail]
    have hstep := thetaStep_ge_add_half
      (le_of_lt (ogmgThetaTail_pos (n - (i + 1))))
    linarith

/-- Source definition of `kappa`: the zeroth coefficient is one and every
positive coefficient is `theta_0^2 / (2 theta_i^2)`. -/
noncomputable def stage9Kappa (n i : ℕ) : ℝ :=
  if i = 0 then 1 else (stage9Theta n 0) ^ 2 / (2 * (stage9Theta n i) ^ 2)

@[simp] theorem stage9Kappa_zero (n : ℕ) : stage9Kappa n 0 = 1 := by
  simp [stage9Kappa]

theorem stage9Kappa_of_pos {n i : ℕ} (hi : 0 < i) :
    stage9Kappa n i =
      (stage9Theta n 0) ^ 2 / (2 * (stage9Theta n i) ^ 2) := by
  simp [stage9Kappa, Nat.ne_of_gt hi]

theorem stage9Kappa_nonneg (n i : ℕ) : 0 ≤ stage9Kappa n i := by
  by_cases hi : i = 0
  · subst i
    simp
  · rw [stage9Kappa, ite_eq_right hi]
    positivity

/-- The constant product used at the quadratic telescoping endpoint. -/
theorem stage9Kappa_mul_theta_sq {n i : ℕ} (hi : 1 ≤ i) :
    stage9Kappa n i * (stage9Theta n i) ^ 2 =
      (stage9Theta n 0) ^ 2 / 2 := by
  rw [stage9Kappa_of_pos (lt_of_lt_of_le Nat.zero_lt_one hi)]
  have htheta := stage9Theta_pos n i
  field_simp [htheta.ne']

/-- The first increment is nonnegative; this is the step that uses the
special identity `theta_0^2 - theta_0 = 2 theta_1^2`. -/
theorem stage9Kappa_zero_le_one {n : ℕ} (hn : 1 ≤ n) :
    stage9Kappa n 0 ≤ stage9Kappa n 1 := by
  rw [stage9Kappa_zero, stage9Kappa_of_pos (by omega : 0 < (1 : ℕ))]
  have hs := stage9Theta_special_equation hn
  have ht0 := stage9Theta_pos n 0
  have ht1 := stage9Theta_pos n 1
  rw [le_div_iff₀ (by positivity : 0 < 2 * (stage9Theta n 1) ^ 2)]
  nlinarith

/-- `kappa_i` is nondecreasing on the entire source interval. -/
theorem stage9Kappa_mono_succ {n i : ℕ} (hin : i < n) :
    stage9Kappa n i ≤ stage9Kappa n (i + 1) := by
  by_cases hi : i = 0
  · subst i
    exact stage9Kappa_zero_le_one (by omega)
  · have hip : 0 < i := Nat.pos_of_ne_zero hi
    rw [stage9Kappa_of_pos hip,
      stage9Kappa_of_pos (by omega : 0 < i + 1)]
    have ht0sq : 0 ≤ (stage9Theta n 0) ^ 2 := sq_nonneg _
    have hti := stage9Theta_pos n i
    have htis := stage9Theta_pos n (i + 1)
    have hmono := stage9Theta_succ_le hin
    have hsq : (stage9Theta n (i + 1)) ^ 2 ≤ (stage9Theta n i) ^ 2 := by
      nlinarith
    exact div_le_div_of_nonneg_left ht0sq (by positivity) (by nlinarith)

/-- Interval form of monotonicity, convenient for finite certificate sums. -/
theorem stage9Kappa_mono {n i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) :
    stage9Kappa n i ≤ stage9Kappa n j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
      exact (ih (by omega)).trans (stage9Kappa_mono_succ (by omega))

/-- The source increment `delta_i = kappa_(i+1) - kappa_i`. -/
noncomputable def stage9Delta (n i : ℕ) : ℝ :=
  stage9Kappa n (i + 1) - stage9Kappa n i

theorem stage9Delta_nonneg {n i : ℕ} (hin : i < n) :
    0 ≤ stage9Delta n i := by
  unfold stage9Delta
  exact sub_nonneg.mpr (stage9Kappa_mono_succ hin)

/-- Exact coefficient increment used in the `p`-sequence induction.  The
`i=0` branch uses the special doubled theta equation, while positive indices
use the ordinary equation. -/
theorem stage9Delta_eq_kappa_div_theta {n i : ℕ} (hin : i < n) :
    stage9Delta n i = stage9Kappa n (i + 1) / stage9Theta n i := by
  unfold stage9Delta
  by_cases hi : i = 0
  · subst i
    rw [stage9Kappa_zero,
      stage9Kappa_of_pos (by omega : 0 < (0 + 1 : ℕ))]
    have hs := stage9Theta_special_equation (by omega : 1 ≤ n)
    have ht0 := stage9Theta_pos n 0
    have ht1 := stage9Theta_pos n 1
    field_simp [ht0.ne', ht1.ne']
    nlinarith
  · have hip : 0 < i := Nat.pos_of_ne_zero hi
    rw [stage9Kappa_of_pos hip,
      stage9Kappa_of_pos (by omega : 0 < i + 1)]
    have hs := stage9Theta_ordinary_equation (by omega : 1 ≤ i) hin
    have ht0 := stage9Theta_pos n 0
    have hti := stage9Theta_pos n i
    have htis := stage9Theta_pos n (i + 1)
    field_simp [ht0.ne', hti.ne', htis.ne']
    nlinarith

/-- Rearranged delta identity in precisely the form used to update the
weighted-gradient partial sum. -/
theorem stage9Kappa_eq_next_mul_one_sub_inv {n i : ℕ} (hin : i < n) :
    stage9Kappa n i =
      stage9Kappa n (i + 1) * (1 - 1 / stage9Theta n i) := by
  have hd := stage9Delta_eq_kappa_div_theta hin
  unfold stage9Delta at hd
  have ht := stage9Theta_ne_zero n i
  field_simp [ht] at hd ⊢
  nlinarith

/-- The source endpoint lower bound, now exposed through the Nat-indexed
coefficient representation used by Stage 9. -/
theorem stage9Theta_zero_lower {n : ℕ} (hn : 1 ≤ n) :
    (n + 1 : ℝ) / Real.sqrt 2 ≤ stage9Theta n 0 := by
  rw [stage9Theta_zero]
  exact ogmgThetaZero_ge hn

end O3
