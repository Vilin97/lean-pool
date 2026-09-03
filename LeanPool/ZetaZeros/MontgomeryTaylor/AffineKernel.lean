/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import LeanPool.ZetaZeros.Zeta.Basic

/-!
# The auxiliary kernel `G`, and why it is constant

`G u = f_0 u + integral over [-1/2, 1/2] of |u - v| f_0 v`.

The heart of the computation: the modulus kernel differentiates twice to `2 f_0 u` while
`f_0'' = -2 f_0`, so `G'' = 0` and `G` is affine; being even, it is constant.
-/

@[expose] public section

open MeasureTheory

namespace ZetaZeros

/-- The auxiliary kernel `G(u) = f₀(u) + ∫_{-1/2}^{1/2} |u - v| f₀(v) dv`, which is constant on
`[-1/2, 1/2]`. -/
noncomputable def extremalG (u : ℝ) : ℝ :=
  extremalTest u + ∫ v in (-(1:ℝ)/2)..(1/2), |u - v| * extremalTest v

/-!
## Antiderivatives for the modulus kernel
-/

/-- Antiderivative fact: `d/dv [v sin(√2 v)/√2 + cos(√2 v)/2] = v cos(√2 v)`. -/
lemma hasDerivAt_vcos (v : ℝ) :
    HasDerivAt
      (fun v => v * Real.sin (Real.sqrt 2 * v) / Real.sqrt 2 + Real.cos (Real.sqrt 2 * v) / 2)
      (v * Real.cos (Real.sqrt 2 * v)) v := by
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h2ne : Real.sqrt 2 ≠ 0 := ne_of_gt h2
  have hmul : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  -- derivative of sin(√2 v)
  have hlin : HasDerivAt (fun v => Real.sqrt 2 * v) (Real.sqrt 2) v := by
    simpa using (hasDerivAt_id v).const_mul (Real.sqrt 2)
  have hsin : HasDerivAt (fun v => Real.sin (Real.sqrt 2 * v))
      (Real.sqrt 2 * Real.cos (Real.sqrt 2 * v)) v := by
    have := (Real.hasDerivAt_sin (Real.sqrt 2 * v)).comp v hlin
    simp only [Function.comp_def] at this
    rw [mul_comm] at this
    exact this
  have hcos : HasDerivAt (fun v => Real.cos (Real.sqrt 2 * v))
      (-(Real.sqrt 2 * Real.sin (Real.sqrt 2 * v))) v := by
    have := (Real.hasDerivAt_cos (Real.sqrt 2 * v)).comp v hlin
    simp only [Function.comp_def] at this
    rw [show -Real.sin (Real.sqrt 2 * v) * Real.sqrt 2
      = -(Real.sqrt 2 * Real.sin (Real.sqrt 2 * v)) by ring] at this
    exact this
  -- g1 = v * sin(√2 v) / √2
  have hg1 : HasDerivAt (fun v => v * Real.sin (Real.sqrt 2 * v) / Real.sqrt 2)
      ((Real.sin (Real.sqrt 2 * v) + v * (Real.sqrt 2 * Real.cos (Real.sqrt 2 * v))) / Real.sqrt 2)
      v := by
    have hp : HasDerivAt (fun v => v * Real.sin (Real.sqrt 2 * v))
        (1 * Real.sin (Real.sqrt 2 * v) + v * (Real.sqrt 2 * Real.cos (Real.sqrt 2 * v))) v :=
      (hasDerivAt_id v).mul hsin
    have := hp.div_const (Real.sqrt 2)
    simpa [one_mul] using this
  have hg2 : HasDerivAt (fun v => Real.cos (Real.sqrt 2 * v) / 2)
      (-(Real.sqrt 2 * Real.sin (Real.sqrt 2 * v)) / 2) v := hcos.div_const 2
  have hsum := hg1.add hg2
  have hval : (Real.sin (Real.sqrt 2 * v)
          + v * (Real.sqrt 2 * Real.cos (Real.sqrt 2 * v))) / Real.sqrt 2
        + -(Real.sqrt 2 * Real.sin (Real.sqrt 2 * v)) / 2
      = v * Real.cos (Real.sqrt 2 * v) := by
    rw [div_add_div _ _ h2ne (by norm_num : (2:ℝ) ≠ 0), div_eq_iff (by positivity)]
    linear_combination (-Real.sin (Real.sqrt 2 * v)) * hmul
  have hfun : (fun v => v * Real.sin (Real.sqrt 2 * v) / Real.sqrt 2
        + Real.cos (Real.sqrt 2 * v) / 2)
      = (fun v => v * Real.sin (Real.sqrt 2 * v) / Real.sqrt 2)
        + (fun v => Real.cos (Real.sqrt 2 * v) / 2) := rfl
  rw [hfun, ← hval]
  exact hsum

/-- Antiderivative for the shifted kernel: for fixed `u`,
    `d/dv [u·sin(√2 v)/√2 − (v·sin(√2 v)/√2 + cos(√2 v)/2)] = (u − v)·cos(√2 v)`. -/
lemma hasDerivAt_shift (u v : ℝ) :
    HasDerivAt (fun v => u * Real.sin (Real.sqrt 2 * v) / Real.sqrt 2
        - (v * Real.sin (Real.sqrt 2 * v) / Real.sqrt 2 + Real.cos (Real.sqrt 2 * v) / 2))
      ((u - v) * Real.cos (Real.sqrt 2 * v)) v := by
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h2ne : Real.sqrt 2 ≠ 0 := ne_of_gt h2
  have hmul : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hlin : HasDerivAt (fun v => Real.sqrt 2 * v) (Real.sqrt 2) v := by
    simpa using (hasDerivAt_id v).const_mul (Real.sqrt 2)
  have hsin : HasDerivAt (fun v => Real.sin (Real.sqrt 2 * v))
      (Real.sqrt 2 * Real.cos (Real.sqrt 2 * v)) v := by
    have := (Real.hasDerivAt_sin (Real.sqrt 2 * v)).comp v hlin
    simp only [Function.comp_def] at this
    rw [mul_comm] at this
    exact this
  -- derivative of u * sin(√2 v)/√2 is u cos(√2 v)
  have hA1 : HasDerivAt (fun v => u * Real.sin (Real.sqrt 2 * v) / Real.sqrt 2)
      (u * Real.cos (Real.sqrt 2 * v)) v := by
    have hd := (hsin.const_mul u).div_const (Real.sqrt 2)
    have hval1 : u * (Real.sqrt 2 * Real.cos (Real.sqrt 2 * v)) / Real.sqrt 2
        = u * Real.cos (Real.sqrt 2 * v) := by
      field_simp
    rw [hval1] at hd
    exact hd
  have hA2 := hasDerivAt_vcos v
  have hsub := hA1.sub hA2
  have hfun : (fun v => u * Real.sin (Real.sqrt 2 * v) / Real.sqrt 2
        - (v * Real.sin (Real.sqrt 2 * v) / Real.sqrt 2 + Real.cos (Real.sqrt 2 * v) / 2))
      = (fun v => u * Real.sin (Real.sqrt 2 * v) / Real.sqrt 2)
        - (fun v => v * Real.sin (Real.sqrt 2 * v) / Real.sqrt 2
            + Real.cos (Real.sqrt 2 * v) / 2) := rfl
  have hval2 : u * Real.cos (Real.sqrt 2 * v) - v * Real.cos (Real.sqrt 2 * v)
      = (u - v) * Real.cos (Real.sqrt 2 * v) := by ring
  rw [hfun, ← hval2]
  exact hsub

lemma extremalG_const {u : ℝ} (hu : |u| ≤ 1 / 2) : extremalG u = extremalG 0 := by
  -- Direct evaluation: for |u| ≤ 1/2, extremalG u = c·(sin(1/√2)/√2 + cos(1/√2)), independent of u.
  suffices h : ∀ w : ℝ, |w| ≤ 1/2 → extremalG w
      = (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2))⁻¹
        * (Real.sin (1 / Real.sqrt 2) / Real.sqrt 2 + Real.cos (1 / Real.sqrt 2)) by
    rw [h u hu, h 0 (by norm_num)]
  intro w hw
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h2ne : Real.sqrt 2 ≠ 0 := ne_of_gt h2
  have hmul : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hkey : Real.sqrt 2 * (1/2) = 1 / Real.sqrt 2 := by
    rw [eq_div_iff h2ne]; nlinarith [hmul]
  have hwabs : -(1:ℝ)/2 ≤ w ∧ w ≤ 1/2 := by
    rw [abs_le] at hw; constructor <;> linarith [hw.1, hw.2]
  unfold extremalG
  -- extremalTest w = c cos(√2 w)
  rw [extremalTest, ite_eq_left hw]
  -- replace extremalTest v by c cos(√2 v) in the kernel
  have hcongr : (∫ v in (-(1:ℝ)/2)..(1/2), |w - v| * extremalTest v)
      = ∫ v in (-(1:ℝ)/2)..(1/2),
          |w - v| * (Real.cos (Real.sqrt 2 * v) / (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2))) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le (by norm_num : (-(1:ℝ)/2) ≤ 1/2), Set.mem_Icc] at hv
    have hvabs : |v| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hv.1, hv.2]
    simp only
    rw [extremalTest, ite_eq_left hvabs]
  rw [hcongr]
  -- pull constant c out
  set c : ℝ := (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2))⁻¹ with hc
  have hcne : Real.sqrt 2 * Real.sin (1 / Real.sqrt 2) ≠ 0 := by
    -- shown nonzero from positivity below; here just need it for field_simp
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
    exact ne_of_gt (mul_pos h2 hsin_pos)
  have hrw : (∫ v in (-(1:ℝ)/2)..(1/2),
        |w - v| * (Real.cos (Real.sqrt 2 * v) / (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2))))
      = c * ∫ v in (-(1:ℝ)/2)..(1/2), |w - v| * Real.cos (Real.sqrt 2 * v) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v _
    simp only [hc]
    field_simp
  rw [hrw]
  -- compute the kernel integral K := ∫ |w-v| cos(√2 v)
  -- = -cos(√2 w) + sin(1/√2)/√2 + cos(1/√2)
  have hcontK : Continuous (fun v : ℝ => |w - v| * Real.cos (Real.sqrt 2 * v)) := by
    exact ((continuous_const.sub continuous_id').abs).mul (by continuity)
  have hcontvcos : Continuous (fun v : ℝ => (w - v) * Real.cos (Real.sqrt 2 * v)) := by
    continuity
  have hK : (∫ v in (-(1:ℝ)/2)..(1/2), |w - v| * Real.cos (Real.sqrt 2 * v))
      = -Real.cos (Real.sqrt 2 * w)
        + Real.sin (1 / Real.sqrt 2) / Real.sqrt 2 + Real.cos (1 / Real.sqrt 2) := by
    -- split at w
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (a := -(1:ℝ)/2) (b := w) (c := 1/2)
      (hcontK.intervalIntegrable _ _) (hcontK.intervalIntegrable _ _)]
    -- on [-1/2,w], w - v ≥ 0 so |w-v| = w - v
    have hleft : (∫ v in (-(1:ℝ)/2)..w, |w - v| * Real.cos (Real.sqrt 2 * v))
        = ∫ v in (-(1:ℝ)/2)..w, (w - v) * Real.cos (Real.sqrt 2 * v) := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le hwabs.1, Set.mem_Icc] at hv
      simp only
      rw [abs_of_nonneg (show (0:ℝ) ≤ w - v by linarith [hv.2])]
    -- on [w,1/2], w - v ≤ 0 so |w-v| = -(w-v) = v - w
    have hright : (∫ v in w..(1/2), |w - v| * Real.cos (Real.sqrt 2 * v))
        = ∫ v in w..(1/2), (-(w - v)) * Real.cos (Real.sqrt 2 * v) := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le hwabs.2, Set.mem_Icc] at hv
      simp only
      rw [abs_of_nonpos (show w - v ≤ 0 by linarith [hv.1])]
    rw [hleft, hright]
    -- antiderivative A v = w sin(√2 v)/√2 - (v sin(√2 v)/√2 + cos(√2 v)/2)
    set A : ℝ → ℝ := fun v => w * Real.sin (Real.sqrt 2 * v) / Real.sqrt 2
        - (v * Real.sin (Real.sqrt 2 * v) / Real.sqrt 2 + Real.cos (Real.sqrt 2 * v) / 2) with hA
    have hAderiv : ∀ x : ℝ, HasDerivAt A ((w - x) * Real.cos (Real.sqrt 2 * x)) x :=
      fun x => hasDerivAt_shift w x
    -- left integral = A w - A (-1/2)
    have hleftval : (∫ v in (-(1:ℝ)/2)..w, (w - v) * Real.cos (Real.sqrt 2 * v))
        = A w - A (-(1:ℝ)/2) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hAderiv x)
        (hcontvcos.intervalIntegrable _ _)]
    -- right integral of -(w-v)cos = A w - A(1/2)
    have hrightval : (∫ v in w..(1/2), (-(w - v)) * Real.cos (Real.sqrt 2 * v))
        = A w - A (1/2) := by
      have hneg : (∫ v in w..(1/2), (-(w - v)) * Real.cos (Real.sqrt 2 * v))
          = -(∫ v in w..(1/2), (w - v) * Real.cos (Real.sqrt 2 * v)) := by
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro v _; ring
      rw [hneg, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hAderiv x)
        (hcontvcos.intervalIntegrable _ _)]
      ring
    rw [hleftval, hrightval]
    -- A w = -cos(√2 w)/2
    have hAw : A w = -Real.cos (Real.sqrt 2 * w) / 2 := by
      simp only [hA]; ring
    -- A(1/2) : √2*(1/2) = 1/√2
    have hAhalf : A (1/2) = w * Real.sin (1 / Real.sqrt 2) / Real.sqrt 2
        - ((1/2) * Real.sin (1 / Real.sqrt 2) / Real.sqrt 2 + Real.cos (1 / Real.sqrt 2) / 2) := by
      simp only [hA]
      rw [hkey]
    -- A(-1/2) : √2*(-1/2) = -(1/√2)
    have hAmhalf : A (-(1:ℝ)/2) = -(w * Real.sin (1 / Real.sqrt 2)) / Real.sqrt 2
        - (-(1:ℝ)/2 * -Real.sin (1 / Real.sqrt 2) / Real.sqrt 2
            + Real.cos (1 / Real.sqrt 2) / 2) := by
      simp only [hA]
      have he : Real.sqrt 2 * (-(1:ℝ)/2) = -(1 / Real.sqrt 2) := by
        rw [show (-(1:ℝ)/2) = -(1/2) by ring, mul_neg, hkey]
      rw [he, Real.sin_neg, Real.cos_neg]
      ring
    rw [hAw, hAhalf, hAmhalf]
    ring
  rw [hK]
  simp only [hc]
  ring

end ZetaZeros
