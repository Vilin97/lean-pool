/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleChoice
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketBaseScales
import LeanPool.NavierStokesAndEuler.Euler.Foundations.Scale
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD

/-!
The literal sequences in (37), including the polynomial initial shear and
frequency.  Their first two exceptional stages are retained explicitly.
-/

@[expose] public section


noncomputable section


namespace EulerPacketSourceScaleSequence

open Real Filter EulerScale EulerPacketSourceScales EulerPacketSourceTime
  EulerPacketSourceScaleBounds EulerPacketSourceScaleChoice EulerPacketBaseScales

open scoped Topology

/-- Shear, given by `exp (scaleSequence J X n/((J+n : ℕ) : ℝ)^5)`. -/
def shear (J : ℕ) (X : ℝ) (n : ℕ) : ℝ :=
  exp (scaleSequence J X n/((J+n : ℕ) : ℝ)^5)

/-- Frequency, given by `exp (scaleSequence J X n/((J+n : ℕ) : ℝ)^2)`. -/
def frequency (J : ℕ) (X : ℝ) (n : ℕ) : ℝ :=
  exp (scaleSequence J X n/((J+n : ℕ) : ℝ)^2)

/-- Spike, given by `exp (-scaleSequence J X n/((J+n : ℕ) : ℝ)^3)`. -/
def spike (J : ℕ) (X : ℝ) (n : ℕ) : ℝ :=
  exp (-scaleSequence J X n/((J+n : ℕ) : ℝ)^3)

/-- Support scale, given by `exp (-scaleSequence J X n/((J+n : ℕ) : ℝ)^(7/2 : ℝ))`. -/
def supportScale (J : ℕ) (X : ℝ) (n : ℕ) : ℝ :=
  exp (-scaleSequence J X n/((J+n : ℕ) : ℝ)^(7/2 : ℝ))

/-- Previous shear as an element of `ℕ → ℝ | 0 => X^1000 | n+1 => shear J X n`. -/
def previousShear (J : ℕ) (X : ℝ) : ℕ → ℝ
  | 0 => X^1000
  | n+1 => shear J X n

/-- Previous frequency as an element of `ℕ → ℝ | 0 => X^D | n+1 => frequency J X n`. -/
def previousFrequency (J D : ℕ) (X : ℝ) : ℕ → ℝ
  | 0 => X^D
  | n+1 => frequency J X n

/-- Older shear as an element of `ℕ → ℝ | 0 => 1 | n+1 => previousShear J X n`. -/
def olderShear (J : ℕ) (X : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => previousShear J X n

/-- Time width, given by `3*scaleSequence J X (n+1)*scaleSequence J X n/sqrt (previousShear J X
n)`. -/
def timeWidth (J : ℕ) (X : ℝ) (n : ℕ) : ℝ :=
  3*scaleSequence J X (n+1)*scaleSequence J X n/sqrt (previousShear J X n)

theorem previousShear_pos (J : ℕ) {X : ℝ} (hX : 0 < X) (n : ℕ) :
    0 < previousShear J X n := by
  cases n with
  | zero => exact pow_pos hX 1000
  | succ n => exact exp_pos _

theorem previousFrequency_pos (J D : ℕ) {X : ℝ} (hX : 0 < X) (n : ℕ) :
    0 < previousFrequency J D X n := by
  cases n with
  | zero => exact pow_pos hX D
  | succ n => exact exp_pos _

theorem previousShear_succ_eq (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (n : ℕ) :
    previousShear J X (n+1) =
      exp (scaleSequence J X (n+1)/((J-1+(n+1) : ℕ) : ℝ)^7) := by
  have hj : (0 : ℝ) < (J+n : ℕ) := by exact_mod_cast (show 0 < J+n by omega)
  have he : J-1+(n+1) = J+n := by omega
  simp only [previousShear, shear, scaleSequence_succ, he]
  congr 1
  field_simp [hj.ne']

theorem previousFrequency_succ_eq (J D : ℕ) (hJ : 1 ≤ J) (X : ℝ) (n : ℕ) :
    previousFrequency J D X (n+1) =
      exp (scaleSequence J X (n+1)/((J-1+(n+1) : ℕ) : ℝ)^4) := by
  have hj : (0 : ℝ) < (J+n : ℕ) := by exact_mod_cast (show 0 < J+n by omega)
  have he : J-1+(n+1) = J+n := by omega
  simp only [previousFrequency, frequency, scaleSequence_succ, he]
  congr 1
  field_simp [hj.ne']

theorem olderShear_succ_succ_eq (J : ℕ) (hJ : 2 ≤ J) (X : ℝ) (n : ℕ) :
    olderShear J X (n+1+1) = exp (scaleSequence J X (n+1+1)/
      (((J-1+(n+1+1) : ℕ) : ℝ)^2*((J-2+(n+1+1) : ℕ) : ℝ)^7)) := by
  have hj : (0 : ℝ) < (J+n : ℕ) := by exact_mod_cast (show 0 < J+n by omega)
  have hj1 : (0 : ℝ) < (J+(n+1) : ℕ) := by exact_mod_cast (show 0 < J+(n+1) by omega)
  have he1 : J-1+(n+1+1) = J+(n+1) := by omega
  have he2 : J-2+(n+1+1) = J+n := by omega
  simp only [olderShear, previousShear, shear, scaleSequence_succ, he1, he2]
  congr 1
  field_simp [hj.ne', hj1.ne']

/-- A fixed positive linear exponential eventually dominates each actual
polynomial base shear or frequency. -/
theorem eventually_pow_le_exp (D : ℕ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ X : ℝ in atTop, X^D ≤ exp (X/r) := by
  have hh := base_exponential_decay 1 (D : ℝ) (1/r) 0 0 (by positivity)
  have hlim : Tendsto (fun X : ℝ => X^D*exp (-(X/r))) atTop (𝓝 0) := by
    convert! hh using 1
    ext X
    simp only [rpow_natCast, pow_zero, mul_one]
    congr 1
    ring_nf
  filter_upwards [hlim.eventually_le_const zero_lt_one] with X hX
  have hm := mul_le_mul_of_nonneg_right hX (exp_pos (X/r)).le
  simpa only [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one, one_mul] using hm

theorem previousShear_le_normal (J : ℕ) (hJ : 1 ≤ J) (X : ℝ)
    (hbase : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7)) (n : ℕ) :
    previousShear J X n ≤ exp (scaleSequence J X n/((J-1+n : ℕ) : ℝ)^7) := by
  cases n with
  | zero => simpa only [previousShear, scaleSequence_zero, Nat.add_zero] using hbase
  | succ n => exact (previousShear_succ_eq J hJ X n).le

theorem previousFrequency_le_normal (J D : ℕ) (hJ : 1 ≤ J) (X : ℝ)
    (hbase : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4)) (n : ℕ) :
    previousFrequency J D X n ≤ exp (scaleSequence J X n/((J-1+n : ℕ) : ℝ)^4) := by
  cases n with
  | zero => simpa only [previousFrequency, scaleSequence_zero, Nat.add_zero] using hbase
  | succ n => exact (previousFrequency_succ_eq J D hJ X n).le

theorem olderShear_le_normal (J : ℕ) (hJ : 3 ≤ J) (X : ℝ) (hX : 0 ≤ X)
    (hbase : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7)) (n : ℕ) :
    1+olderShear J X n ≤ sourceOlderGradient J (scaleSequence J X) n := by
  cases n with
  | zero =>
    change 1+1 ≤ 1+exp (X/(((J-1 : ℕ) : ℝ)^2*((J-2 : ℕ) : ℝ)^7))
    have hh : 1 ≤ exp (X/(((J-1 : ℕ) : ℝ)^2*((J-2 : ℕ) : ℝ)^7)) :=
      one_le_exp (by positivity)
    linarith only [hh]
  | succ n =>
    cases n with
    | zero =>
      have hJp : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
      have he1 : J-1+1 = J := by omega
      have he2 : J-2+1 = J-1 := by omega
      change 1+X^1000 ≤ 1+exp (scaleSequence J X 1/
        (((J-1+1 : ℕ) : ℝ)^2*((J-2+1 : ℕ) : ℝ)^7))
      rw [show scaleSequence J X 1 = (J : ℝ)^2*X by
          simp only [scaleSequence_succ, scaleSequence_zero, Nat.add_zero], he1, he2]
      have he : (J : ℝ)^2*X/((J : ℝ)^2*((J-1 : ℕ) : ℝ)^7) = X/((J-1 : ℕ) : ℝ)^7 := by
        field_simp [hJp.ne']
      rw [he]
      linarith only [hbase]
    | succ n =>
      rw [olderShear_succ_succ_eq J (by omega) X n]
      exact le_rfl

theorem timeWidth_pos (J : ℕ) (hJ : 1 ≤ J) {X : ℝ} (hX : 0 < X) (n : ℕ) :
    0 < timeWidth J X n := by
  have hxp := quadratic_growth_pos J hJ (scaleSequence J X) hX (scaleSequence_succ J X)
  exact div_pos (mul_pos (mul_pos (by norm_num) (hxp (n+1))) (hxp n))
    (sqrt_pos.mpr (previousShear_pos J hX n))

theorem timeWidth_succ_eq (J : ℕ) (X : ℝ) (n : ℕ) :
    timeWidth J X (n+1) = sourceNextTimeWidth J (scaleSequence J X) n := by
  simp only [timeWidth, previousShear, shear, scaleSequence_succ, ← exp_half]
  have hj : ((J+(n+1) : ℕ) : ℝ) = ((J+n : ℕ) : ℝ)+1 := by push_cast; ring
  rw [hj]
  unfold sourceNextTimeWidth
  rw [div_eq_mul_inv, ← exp_neg]
  have he : -(scaleSequence J X n/((J+n : ℕ) : ℝ)^5/2) =
      -scaleSequence J X n/(2*((J+n : ℕ) : ℝ)^5) := by ring
  rw [he]
  ring

theorem sourceTimeWidth_eq (J : ℕ) (X : ℝ) (n : ℕ) :
    sourceTimeWidth J (scaleSequence J X) n =
      3*scaleSequence J X (n+1)*scaleSequence J X n/
        sqrt (exp (scaleSequence J X n/((J-1+n : ℕ) : ℝ)^7)) := by
  rw [scaleSequence_succ, ← exp_half, div_eq_mul_inv, ← exp_neg]
  unfold sourceTimeWidth
  have he : -(scaleSequence J X n/((J-1+n : ℕ) : ℝ)^7/2) =
      -scaleSequence J X n/(2*((J-1+n : ℕ) : ℝ)^7) := by ring
  rw [he]
  ring

/-- The actual polynomial-base time width is no smaller than the normal-form
one, once the explicit polynomial/exponential comparison holds. -/
theorem sourceTimeWidth_le (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 0 < X)
    (hbase : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7)) (n : ℕ) :
    sourceTimeWidth J (scaleSequence J X) n ≤ timeWidth J X n := by
  rw [sourceTimeWidth_eq]
  have hxp := quadratic_growth_pos J hJ (scaleSequence J X) hX (scaleSequence_succ J X)
  exact div_le_div_of_nonneg_left
    (mul_nonneg (mul_nonneg (by norm_num) (hxp (n+1)).le) (hxp n).le)
    (sqrt_pos.mpr (previousShear_pos J hX n))
    (sqrt_le_sqrt (previousShear_le_normal J hJ X hbase n))

end EulerPacketSourceScaleSequence
