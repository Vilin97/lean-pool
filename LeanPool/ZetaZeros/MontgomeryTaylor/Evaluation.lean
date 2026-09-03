/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import LeanPool.ZetaZeros.MontgomeryTaylor.AffineKernel

/-!
# The value of the constant

`G 0 = C_MT`. With `G` constant this single evaluation pins the functional:
`G 0 = f_0 0 + integral of |v| f_0 v`, elementary by parts, and the trigonometry collapses.
-/

@[expose] public section

open MeasureTheory

namespace ZetaZeros

/-- `G 0` is the Montgomery--Taylor constant. -/
lemma extremalG_zero : extremalG 0 = montgomeryTaylorConst := by
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h2ne : Real.sqrt 2 ≠ 0 := ne_of_gt h2
  have hmul : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  -- sin(1/√2) positivity
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
  have hsin_ne : Real.sin (1 / Real.sqrt 2) ≠ 0 := ne_of_gt hsin_pos
  -- key: √2 * (1/2) = 1/√2
  have hkey : Real.sqrt 2 * (1/2) = 1 / Real.sqrt 2 := by
    rw [eq_div_iff h2ne]; nlinarith [hmul]
  -- abbreviation for the antiderivative
  set F : ℝ → ℝ :=
    fun v => v * Real.sin (Real.sqrt 2 * v) / Real.sqrt 2 + Real.cos (Real.sqrt 2 * v) / 2 with hF
  -- integrability of v cos(√2 v)
  have hcont : Continuous (fun v => v * Real.cos (Real.sqrt 2 * v)) := by
    continuity
  unfold extremalG
  -- the kernel integral: replace extremalTest v by cos(√2 v)/(√2 sin(1/√2)) on the interval
  have hcongr : (∫ v in (-(1:ℝ)/2)..(1/2), |0 - v| * extremalTest v)
      = ∫ v in (-(1:ℝ)/2)..(1/2),
          |v| * (Real.cos (Real.sqrt 2 * v) / (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2))) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le (by norm_num : (-(1:ℝ)/2) ≤ 1/2), Set.mem_Icc] at hv
    have hvabs : |v| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hv.1, hv.2]
    simp only [zero_sub, abs_neg]
    rw [extremalTest, ite_eq_left hvabs]
  rw [hcongr]
  -- pull constant c out
  set c : ℝ := (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2))⁻¹ with hc
  have hcpos : 0 < Real.sqrt 2 * Real.sin (1 / Real.sqrt 2) := mul_pos h2 hsin_pos
  have hcne : Real.sqrt 2 * Real.sin (1 / Real.sqrt 2) ≠ 0 := ne_of_gt hcpos
  have hrw : (∫ v in (-(1:ℝ)/2)..(1/2),
        |v| * (Real.cos (Real.sqrt 2 * v) / (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2))))
      = c * ∫ v in (-(1:ℝ)/2)..(1/2), |v| * Real.cos (Real.sqrt 2 * v) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v _
    simp only [hc]
    field_simp
  rw [hrw]
  -- integrability of |v| cos(√2 v)
  have hcontabs : Continuous (fun v : ℝ => |v| * Real.cos (Real.sqrt 2 * v)) := by
    exact (continuous_abs.mul (by continuity))
  -- compute the elementary integral I := ∫ |v| cos(√2 v) = sin(1/√2)/√2 + cos(1/√2) - 1
  have hI : (∫ v in (-(1:ℝ)/2)..(1/2), |v| * Real.cos (Real.sqrt 2 * v))
      = Real.sin (1 / Real.sqrt 2) / Real.sqrt 2 + Real.cos (1 / Real.sqrt 2) - 1 := by
    -- split at 0
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (a := -(1:ℝ)/2) (b := 0) (c := 1/2)
      (hcontabs.intervalIntegrable _ _) (hcontabs.intervalIntegrable _ _)]
    -- left piece: on [-1/2,0], |v| = -v
    have hleft : (∫ v in (-(1:ℝ)/2)..(0:ℝ), |v| * Real.cos (Real.sqrt 2 * v))
        = ∫ v in (-(1:ℝ)/2)..(0:ℝ), (-v) * Real.cos (Real.sqrt 2 * v) := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le (by norm_num : (-(1:ℝ)/2) ≤ 0), Set.mem_Icc] at hv
      simp only
      rw [abs_of_nonpos (show v ≤ 0 by linarith [hv.2])]
    have hright : (∫ v in (0:ℝ)..(1/2), |v| * Real.cos (Real.sqrt 2 * v))
        = ∫ v in (0:ℝ)..(1/2), v * Real.cos (Real.sqrt 2 * v) := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2), Set.mem_Icc] at hv
      simp only
      rw [abs_of_nonneg (show (0:ℝ) ≤ v by linarith [hv.1])]
    rw [hleft, hright]
    -- ∫ v cos = F b - F a
    have hFderiv : ∀ x ∈ Set.uIcc (0:ℝ) (1/2), HasDerivAt F (x * Real.cos (Real.sqrt 2 * x)) x :=
      fun x _ => hasDerivAt_vcos x
    have hFderiv2 : ∀ x ∈ Set.uIcc (-(1:ℝ)/2) (0:ℝ),
        HasDerivAt F (x * Real.cos (Real.sqrt 2 * x)) x :=
      fun x _ => hasDerivAt_vcos x
    have hcont_vcos : Continuous (fun v : ℝ => v * Real.cos (Real.sqrt 2 * v)) := hcont
    have hint_right : (∫ v in (0:ℝ)..(1/2), v * Real.cos (Real.sqrt 2 * v)) = F (1/2) - F 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hFderiv (hcont_vcos.intervalIntegrable _ _)
    have hint_left0 : (∫ v in (-(1:ℝ)/2)..(0:ℝ), v * Real.cos (Real.sqrt 2 * v))
        = F 0 - F (-(1:ℝ)/2) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hFderiv2 (hcont_vcos.intervalIntegrable _ _)
    have hint_left : (∫ v in (-(1:ℝ)/2)..(0:ℝ), (-v) * Real.cos (Real.sqrt 2 * v))
        = -(F 0 - F (-(1:ℝ)/2)) := by
      rw [← hint_left0, ← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro v _; ring
    rw [hint_left, hint_right]
    -- now evaluate F at endpoints
    simp only [hF]
    rw [show Real.sqrt 2 * (1/2 : ℝ) = 1 / Real.sqrt 2 from hkey]
    rw [show Real.sqrt 2 * (-(1:ℝ)/2) = -(1 / Real.sqrt 2) by rw [← hkey]; ring]
    rw [show Real.sqrt 2 * (0:ℝ) = 0 by ring]
    rw [Real.sin_neg, Real.cos_neg, Real.sin_zero, Real.cos_zero]
    field_simp
    ring
  rw [hI]
  -- extremalTest 0 = 1 / (√2 sin(1/√2))
  rw [extremalTest, ite_eq_left (by norm_num : |(0:ℝ)| ≤ 1 / 2)]
  rw [show Real.sqrt 2 * (0:ℝ) = 0 by ring, Real.cos_zero]
  -- assemble
  rw [montgomeryTaylorConst, Real.cot_eq_cos_div_sin]
  simp only [hc]
  field_simp
  linear_combination (-Real.sin (1 / Real.sqrt 2)) * hmul

end ZetaZeros
