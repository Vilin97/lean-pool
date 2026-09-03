/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import LeanPool.ZetaZeros.Zeta.Basic
public import LeanPool.ZetaZeros.Zeta.Mass

/-!
# Properties of the extremal test function

`f_0` is even, vanishes off `[-1/2, 1/2]`, has total mass one, and is measurable, bounded and
continuous on its support. Every later step rests on these, and none mentions the functional.
-/

@[expose] public section

open MeasureTheory

namespace ZetaZeros

/-- `f₀` is even. Immediate from `cos` being even and `|-x| = |x|`. -/
lemma extremalTest_even (x : ℝ) : extremalTest (-x) = extremalTest x := by
  simp [extremalTest, abs_neg, mul_neg, Real.cos_neg]

/-- `f₀` is supported in `[-1/2, 1/2]`: it vanishes outside. -/
lemma extremalTest_eq_zero {x : ℝ} (hx : 1 / 2 < |x|) : extremalTest x = 0 := by
  rw [extremalTest, ite_eq_right (not_le.mpr hx)]


/-- On the closed interval `[-1/2,1/2]`, `extremalTest` agrees with the continuous
    `cos(√2 ·)/(√2 sin(1/√2))` (the jump of the indicator is strictly outside). -/
lemma extremalTest_eqOn_uIcc :
    Set.EqOn extremalTest
      (fun x => Real.cos (Real.sqrt 2 * x) / (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2)))
      (Set.uIcc (-(1:ℝ)/2) (1/2)) := by
  intro x hx
  rw [Set.uIcc_of_le (by norm_num : (-(1:ℝ)/2) ≤ 1/2), Set.mem_Icc] at hx
  have hxabs : |x| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  rw [extremalTest, ite_eq_left hxabs]

/-- `extremalTest` is continuous on `[-1/2,1/2]`. -/
lemma extremalTest_continuousOn :
    ContinuousOn extremalTest (Set.uIcc (-(1:ℝ)/2) (1/2)) := by
  have hc : Continuous
      (fun x => Real.cos (Real.sqrt 2 * x) / (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2))) := by
    fun_prop
  exact hc.continuousOn.congr extremalTest_eqOn_uIcc

/-- `extremalTest` is interval-integrable on `[-1/2,1/2]`. -/
lemma extremalTest_intervalIntegrable :
    IntervalIntegrable extremalTest MeasureTheory.volume (-(1:ℝ)/2) (1/2) :=
  extremalTest_continuousOn.intervalIntegrable

/-- `extremalTest` is measurable. -/
lemma extremalTest_measurable : Measurable extremalTest := by
  have hcont : Continuous
      (fun x => Real.cos (Real.sqrt 2 * x) / (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2))) := by
    fun_prop
  have hset : MeasurableSet {x : ℝ | |x| ≤ 1 / 2} := by
    have : {x : ℝ | |x| ≤ 1 / 2} = {x : ℝ | |x| ≤ 1 / 2} := rfl
    exact measurableSet_le (by fun_prop) measurable_const
  unfold extremalTest
  exact Measurable.ite hset hcont.measurable measurable_const

/-- `extremalTest` is bounded: `|extremalTest x| ≤ C` with
    `C = (√2 sin(1/√2))⁻¹`. -/
lemma extremalTest_abs_le (x : ℝ) :
    |extremalTest x| ≤ (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2))⁻¹ := by
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt2_lt : Real.sqrt 2 < 2 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (2:ℝ) < 4)
    rwa [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)] at h
  have hinv_pos : (0:ℝ) < 1 / Real.sqrt 2 := by positivity
  have hinv_lt_pi : 1 / Real.sqrt 2 < Real.pi := by
    have hlt1 : 1 / Real.sqrt 2 < 1 := by
      rw [div_lt_one h2]
      have : Real.sqrt 1 < Real.sqrt 2 := by apply Real.sqrt_lt_sqrt <;> norm_num
      simpa using this
    linarith [Real.pi_gt_three]
  have hsin_pos : 0 < Real.sin (1 / Real.sqrt 2) :=
    Real.sin_pos_of_pos_of_lt_pi hinv_pos hinv_lt_pi
  have hden : 0 < Real.sqrt 2 * Real.sin (1 / Real.sqrt 2) := mul_pos h2 hsin_pos
  unfold extremalTest
  by_cases hx : |x| ≤ 1 / 2
  · rw [ite_eq_left hx, abs_div, abs_of_pos hden, ← one_div, div_le_div_iff_of_pos_right hden]
    exact Real.abs_cos_le_one _
  · rw [ite_eq_right hx, abs_zero]
    positivity

/-- `extremalTest` is `IntegrableOn` any measurable set of finite measure. -/
lemma extremalTest_integrableOn {s : Set ℝ} (hs : volume s < ⊤) :
    IntegrableOn extremalTest s volume := by
  apply MeasureTheory.IntegrableOn.of_bound hs
    (extremalTest_measurable.aestronglyMeasurable)
    ((Real.sqrt 2 * Real.sin (1 / Real.sqrt 2))⁻¹)
  filter_upwards with x
  simpa [Real.norm_eq_abs] using extremalTest_abs_le x

end ZetaZeros
