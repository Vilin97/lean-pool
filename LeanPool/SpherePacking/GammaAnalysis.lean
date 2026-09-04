/-
Copyright (c) 2024 Sidharth Hariharan and 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Sidharth Hariharan, Gareth Ma, Dean Cureton
-/

module

import all LeanPool.SpherePacking.MellinAnalysis
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# GammaAnalysis

Gamma-kernel estimates and radial asymptotics.
-/

namespace CohnElkies

section

open Filter MeasureTheory Set
open scoped Topology

private theorem complexLaplaceKernel_integrable {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun x : ℝ => Complex.exp (-z * (x : ℂ))) (Ioi 0) := by
  have hneg : (-z).re < 0 := by
    simpa only [Complex.neg_re, Left.neg_neg_iff] using! hz
  simpa only [neg_mul] using!
    (integrableOn_exp_mul_complex_Ioi (a := -z) hneg 0)

private theorem integral_complexLaplaceKernel {z : ℂ} (hz : 0 < z.re) :
    (∫ x : ℝ in Ioi 0, Complex.exp (-z * (x : ℂ))) = z⁻¹ := by
  have hneg : (-z).re < 0 := by
    simpa only [Complex.neg_re, Left.neg_neg_iff] using! hz
  simpa only [neg_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_eq_mul_inv, inv_neg,
    mul_neg,
    one_mul, neg_neg] using!
    (integral_exp_mul_complex_Ioi (a := -z) hneg 0)

private noncomputable def complexFrullaniSegment (z w : ℂ) (s : ℝ) : ℂ :=
  z + (s : ℂ) * (w - z)

private theorem complexFrullaniSegment_re_pos {z w : ℂ}
    (hz : 0 < z.re) (hw : 0 < w.re)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    0 < (complexFrullaniSegment z w s).re := by
  simp only [complexFrullaniSegment, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, zero_mul, sub_zero]
  by_cases hzero : s = 0
  · simpa only [hzero, zero_mul, add_zero] using! hz
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hzero)
    have hfirst : 0 ≤ (1 - s) * z.re :=
      mul_nonneg (sub_nonneg.mpr hs.2) hz.le
    have hsecond : 0 < s * w.re := mul_pos hspos hw
    linarith

private noncomputable def complexFrullaniKernel (z w : ℂ) (x : ℝ) : ℂ :=
  (Complex.exp (-z * (x : ℂ)) -
    Complex.exp (-w * (x : ℂ))) / (x : ℂ)

private theorem complexFrullaniSegment_hasDerivAt
    (z w : ℂ) (s : ℝ) :
    HasDerivAt (complexFrullaniSegment z w) (w - z) s := by
  have hcomplex :
      HasDerivAt (fun q : ℂ => z + q * (w - z))
        (w - z) (s : ℂ) := by
    convert! (hasDerivAt_const (s : ℂ) z).add
      ((hasDerivAt_id (s : ℂ)).mul_const (w - z)) using 1
    all_goals simp only [one_mul, zero_add]
  change HasDerivAt
    (fun r : ℝ => z + (r : ℂ) * (w - z)) (w - z) s
  exact hcomplex.comp_ofReal

private theorem intervalIntegral_complexLaplaceSegment
    (z w : ℂ) {x : ℝ} (hx : x ≠ 0) :
    (∫ s in (0 : ℝ)..1,
      (w - z) *
        Complex.exp
          (-complexFrullaniSegment z w s * (x : ℂ))) =
      complexFrullaniKernel z w x := by
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  have hderiv (s : ℝ) :
      HasDerivAt
        (fun r : ℝ =>
          -Complex.exp
            (-complexFrullaniSegment z w r * (x : ℂ)) /
              (x : ℂ))
        ((w - z) *
          Complex.exp
            (-complexFrullaniSegment z w s * (x : ℂ))) s := by
    have hinner :=
      (complexFrullaniSegment_hasDerivAt z w s).neg.mul_const
        (x : ℂ)
    convert! hinner.cexp.neg.div_const (x : ℂ) using 1
    · simp only [Pi.neg_apply]
      field_simp [hxc]
  have hcontinuous :
      Continuous (fun s : ℝ =>
        (w - z) *
          Complex.exp
            (-complexFrullaniSegment z w s * (x : ℂ))) := by
    unfold complexFrullaniSegment
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hderiv s)
    (hcontinuous.intervalIntegrable 0 1)]
  unfold complexFrullaniSegment complexFrullaniKernel
  push_cast
  simp only [zero_mul, one_mul, add_zero]
  ring_nf

private theorem norm_complexLaplaceKernel (z : ℂ) (x : ℝ) :
    ‖Complex.exp (-z * (x : ℂ))‖ =
      Real.exp (-z.re * x) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

private theorem complexFrullaniSegment_min_re_le
    (z w : ℂ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    min z.re w.re ≤ (complexFrullaniSegment z w s).re := by
  simp only [complexFrullaniSegment, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, zero_mul, sub_zero]
  have hzmin := min_le_left z.re w.re
  have hwmin := min_le_right z.re w.re
  have hfirst :
      0 ≤ (1 - s) * (z.re - min z.re w.re) :=
    mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hzmin)
  have hsecond :
      0 ≤ s * (w.re - min z.re w.re) :=
    mul_nonneg hs.1 (sub_nonneg.mpr hwmin)
  linarith

private theorem complexFrullaniKernel_norm_le_exp
    (z w : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖complexFrullaniKernel z w x‖ ≤
      ‖w - z‖ *
        Real.exp (-(min z.re w.re) * x) := by
  rw [← intervalIntegral_complexLaplaceSegment z w hx.ne']
  have hbound :
      ‖∫ s in (0 : ℝ)..1,
          (w - z) *
            Complex.exp
              (-complexFrullaniSegment z w s * (x : ℂ))‖ ≤
        (‖w - z‖ *
          Real.exp (-(min z.re w.re) * x)) *
            |(1 : ℝ) - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
    have hclosed : s ∈ Icc (0 : ℝ) 1 :=
      ⟨hs.1.le, hs.2⟩
    rw [norm_mul, norm_complexLaplaceKernel]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    have hminimum :=
      complexFrullaniSegment_min_re_le z w hclosed
    nlinarith
  simpa only [neg_mul, intervalIntegral.integral_const_mul, Complex.norm_mul, ge_iff_le,
    sub_zero, abs_one,
    mul_one] using! hbound

private theorem integral_norm_complexFrullaniSegment
    {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ x : ℝ in Ioi 0,
      ‖(w - z) *
        Complex.exp
          (-complexFrullaniSegment z w s * (x : ℂ))‖) =
      ‖w - z‖ * (complexFrullaniSegment z w s).re⁻¹ := by
  have hpositive := complexFrullaniSegment_re_pos hz hw hs
  calc
    (∫ x : ℝ in Ioi 0,
      ‖(w - z) *
        Complex.exp
          (-complexFrullaniSegment z w s * (x : ℂ))‖) =
      ∫ x : ℝ in Ioi 0,
        ‖w - z‖ *
          Real.exp (-(complexFrullaniSegment z w s).re * x) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x _
            change
              ‖(w - z) *
                  Complex.exp
                    (-complexFrullaniSegment z w s * (x : ℂ))‖ =
                ‖w - z‖ *
                  Real.exp
                    (-(complexFrullaniSegment z w s).re * x)
            rw [norm_mul, norm_complexLaplaceKernel]
    _ = ‖w - z‖ *
        (∫ x : ℝ in Ioi 0,
          Real.exp (-(complexFrullaniSegment z w s).re * x)) := by
            rw [integral_const_mul]
    _ = ‖w - z‖ * (complexFrullaniSegment z w s).re⁻¹ := by
      rw [integral_laplaceKernel hpositive]

private theorem complexFrullaniParameter_integrable
    {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    Integrable
      (Function.uncurry (fun s x : ℝ =>
        (w - z) *
          Complex.exp
            (-complexFrullaniSegment z w s * (x : ℂ))))
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
        (volume.restrict (Ioi 0))) := by
  have hmeas :
      AEStronglyMeasurable
        (Function.uncurry (fun s x : ℝ =>
          (w - z) *
            Complex.exp
              (-complexFrullaniSegment z w s * (x : ℂ))))
        ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
          (volume.restrict (Ioi 0))) := by
    unfold complexFrullaniSegment
    fun_prop
  apply (integrable_prod_iff hmeas).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_uIoc]
      with s hs
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
    have hclosed : s ∈ Icc (0 : ℝ) 1 :=
      ⟨hs.1.le, hs.2⟩
    exact
      (complexLaplaceKernel_integrable
        (complexFrullaniSegment_re_pos hz hw hclosed)).const_mul
          (w - z)
  · have hsegment :
        Continuous (fun s : ℝ =>
          (complexFrullaniSegment z w s).re) := by
        unfold complexFrullaniSegment
        fun_prop
    have hnonzero :
        ∀ s ∈ Set.uIcc (0 : ℝ) 1,
          (complexFrullaniSegment z w s).re ≠ 0 := by
      intro s hs
      rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
      exact (complexFrullaniSegment_re_pos hz hw hs).ne'
    have hcontinuous :
        ContinuousOn
          (fun s : ℝ =>
            ‖w - z‖ *
              (complexFrullaniSegment z w s).re⁻¹)
          (Set.uIcc (0 : ℝ) 1) :=
      continuousOn_const.mul
        (hsegment.continuousOn.inv₀ hnonzero)
    have hintegrable :
        Integrable
          (fun s : ℝ =>
            ‖w - z‖ *
              (complexFrullaniSegment z w s).re⁻¹)
          (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
      intervalIntegrable_iff.mp
        (hcontinuous.intervalIntegrable)
    apply hintegrable.congr
    filter_upwards [ae_restrict_mem measurableSet_uIoc]
      with s hs
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
    have hclosed : s ∈ Icc (0 : ℝ) 1 :=
      ⟨hs.1.le, hs.2⟩
    exact (integral_norm_complexFrullaniSegment hz hw hclosed).symm

private theorem complexFrullaniKernel_integrable
    {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    IntegrableOn (complexFrullaniKernel z w) (Ioi 0) := by
  have hproduct :=
    (complexFrullaniParameter_integrable hz hw).integral_prod_right
  apply hproduct.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change
    (∫ s in Set.uIoc (0 : ℝ) 1,
      (w - z) *
        Complex.exp
          (-complexFrullaniSegment z w s * (x : ℂ))) =
      complexFrullaniKernel z w x
  rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    ← intervalIntegral.integral_of_le
      (show (0 : ℝ) ≤ 1 by norm_num)]
  exact intervalIntegral_complexLaplaceSegment z w (ne_of_gt hx)

private theorem intervalIntegral_complexFrullaniLogDerivative
    {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    (∫ s in (0 : ℝ)..1,
      (w - z) * (complexFrullaniSegment z w s)⁻¹) =
      Complex.log w - Complex.log z := by
  have hsegment :
      Continuous (fun s : ℝ => complexFrullaniSegment z w s) := by
    unfold complexFrullaniSegment
    fun_prop
  have hnonzero :
      ∀ s ∈ Set.uIcc (0 : ℝ) 1,
        complexFrullaniSegment z w s ≠ 0 := by
    intro s hs
    rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
    exact ne_of_apply_ne Complex.re
      (complexFrullaniSegment_re_pos hz hw hs).ne'
  have hcontinuous :
      ContinuousOn
        (fun s : ℝ =>
          (w - z) * (complexFrullaniSegment z w s)⁻¹)
        (Set.uIcc (0 : ℝ) 1) :=
    continuousOn_const.mul
      (hsegment.continuousOn.inv₀ hnonzero)
  have hderiv (s : ℝ) (hs : s ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt
        (fun r : ℝ => Complex.log (complexFrullaniSegment z w r))
        ((w - z) * (complexFrullaniSegment z w s)⁻¹) s := by
    rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
    have hslit :
        complexFrullaniSegment z w s ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr
        (Or.inl (complexFrullaniSegment_re_pos hz hw hs))
    simpa only [div_eq_mul_inv] using!
      (complexFrullaniSegment_hasDerivAt z w s).clog_real hslit
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcontinuous.intervalIntegrable]
  simp only [complexFrullaniSegment, Complex.ofReal_one, one_mul, add_sub_cancel,
    Complex.ofReal_zero, zero_mul,
    add_zero]

private theorem integral_complexFrullaniKernel
    {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    (∫ x : ℝ in Ioi 0, complexFrullaniKernel z w x) =
      Complex.log w - Complex.log z := by
  calc
    (∫ x : ℝ in Ioi 0, complexFrullaniKernel z w x) =
      ∫ x : ℝ in Ioi 0,
        ∫ s in (0 : ℝ)..1,
          (w - z) *
            Complex.exp
              (-complexFrullaniSegment z w s * (x : ℂ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact
        (intervalIntegral_complexLaplaceSegment z w
          (ne_of_gt hx)).symm
    _ = ∫ s in (0 : ℝ)..1,
          ∫ x : ℝ in Ioi 0,
            (w - z) *
              Complex.exp
                (-complexFrullaniSegment z w s * (x : ℂ)) :=
      (intervalIntegral_integral_swap
        (complexFrullaniParameter_integrable hz hw)).symm
    _ = ∫ s in (0 : ℝ)..1,
          (w - z) * (complexFrullaniSegment z w s)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
      change
        (∫ x : ℝ in Ioi 0,
          (w - z) *
            Complex.exp
              (-complexFrullaniSegment z w s * (x : ℂ))) =
          (w - z) * (complexFrullaniSegment z w s)⁻¹
      rw [integral_const_mul,
        integral_complexLaplaceKernel
          (complexFrullaniSegment_re_pos hz hw hs)]
    _ = Complex.log w - Complex.log z :=
      intervalIntegral_complexFrullaniLogDerivative hz hw

private theorem complexFrullaniShiftKernel_norm_le_exp
    (z : ℂ) {s x : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hx : 0 < x) :
    ‖complexFrullaniKernel (z + (s : ℂ)) 1 x‖ ≤
      (‖(1 : ℂ) - z‖ + 1) *
        Real.exp (-(min z.re 1) * x) := by
  have hnorm :
      ‖(1 : ℂ) - (z + (s : ℂ))‖ ≤
        ‖(1 : ℂ) - z‖ + 1 := by
    calc
      ‖(1 : ℂ) - (z + (s : ℂ))‖ =
          ‖((1 : ℂ) - z) - (s : ℂ)‖ := by
            congr 1
            ring
      _ ≤ ‖(1 : ℂ) - z‖ + ‖(s : ℂ)‖ :=
        norm_sub_le _ _
      _ ≤ ‖(1 : ℂ) - z‖ + 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hs.1]
        linarith [hs.2]
  have hmin :
      min z.re 1 ≤
        min (z + (s : ℂ)).re (1 : ℂ).re := by
    apply le_min
    · simp only [Complex.add_re, Complex.ofReal_re]
      linarith [min_le_left z.re (1 : ℝ), hs.1]
    · exact min_le_right z.re (1 : ℝ)
  calc
    ‖complexFrullaniKernel (z + (s : ℂ)) 1 x‖ ≤
      ‖(1 : ℂ) - (z + (s : ℂ))‖ *
        Real.exp
          (-(min (z + (s : ℂ)).re (1 : ℂ).re) * x) :=
      complexFrullaniKernel_norm_le_exp (z + (s : ℂ)) 1 hx
    _ ≤ (‖(1 : ℂ) - z‖ + 1) *
        Real.exp
          (-(min (z + (s : ℂ)).re (1 : ℂ).re) * x) :=
      mul_le_mul_of_nonneg_right hnorm (Real.exp_pos _).le
    _ ≤ (‖(1 : ℂ) - z‖ + 1) *
        Real.exp (-(min z.re 1) * x) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith

private theorem complexFrullaniShiftParameter_integrable
    {z : ℂ} (hz : 0 < z.re) :
    Integrable
      (Function.uncurry (fun s x : ℝ =>
        complexFrullaniKernel (z + (s : ℂ)) 1 x))
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
        (volume.restrict (Ioi 0))) := by
  have hm : 0 < min z.re 1 :=
    lt_min hz (by norm_num)
  let C : ℝ := ‖(1 : ℂ) - z‖ + 1
  have hC : 0 ≤ C := by
    try dsimp [C]
    positivity
  have hmeas :
      AEStronglyMeasurable
        (Function.uncurry (fun s x : ℝ =>
          complexFrullaniKernel (z + (s : ℂ)) 1 x))
        ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
          (volume.restrict (Ioi 0))) := by
    change
      AEStronglyMeasurable
        (fun p : ℝ × ℝ =>
          (Complex.exp (-(z + (p.1 : ℂ)) * (p.2 : ℂ)) -
            Complex.exp (-(1 : ℂ) * (p.2 : ℂ))) /
              (p.2 : ℂ))
        ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
          (volume.restrict (Ioi 0)))
    apply Measurable.aestronglyMeasurable
    fun_prop
  apply (integrable_prod_iff hmeas).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_uIoc]
      with s hs
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
    have hspositive : 0 < (z + (s : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith [hs.1]
    change
      IntegrableOn
        (complexFrullaniKernel (z + (s : ℂ)) 1)
        (Ioi 0)
    exact complexFrullaniKernel_integrable
      hspositive (by norm_num : 0 < (1 : ℂ).re)
  · have hconstant :
        Integrable (fun _ : ℝ => C * (min z.re 1)⁻¹)
          (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
      intervalIntegrable_iff.mp
        (continuous_const.intervalIntegrable (a := (0 : ℝ))
          (b := 1))
    apply hconstant.mono'
    · simpa only [Function.uncurry_apply_pair] using!
        hmeas.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_uIoc]
      with s hs
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
    have hclosed : s ∈ Icc (0 : ℝ) 1 :=
      ⟨hs.1.le, hs.2⟩
    have hspositive : 0 < (z + (s : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith [hs.1]
    have hkernel :=
      complexFrullaniKernel_integrable
        hspositive (by norm_num : 0 < (1 : ℂ).re)
    have hmajor :
        IntegrableOn
          (fun x : ℝ =>
            C * Real.exp (-(min z.re 1) * x))
          (Ioi 0) :=
      (laplaceKernel_integrable hm).const_mul C
    change
      ‖∫ x : ℝ in Ioi 0,
        ‖complexFrullaniKernel (z + (s : ℂ)) 1 x‖‖ ≤
          C * (min z.re 1)⁻¹
    rw [Real.norm_eq_abs, abs_of_nonneg
      (integral_nonneg fun x => norm_nonneg
        (complexFrullaniKernel (z + (s : ℂ)) 1 x))]
    calc
      (∫ x : ℝ in Ioi 0,
        ‖complexFrullaniKernel (z + (s : ℂ)) 1 x‖) ≤
          ∫ x : ℝ in Ioi 0,
            C * Real.exp (-(min z.re 1) * x) := by
        apply integral_mono_ae hkernel.norm hmajor
        filter_upwards [ae_restrict_mem measurableSet_Ioi]
          with x hx
        change
          ‖complexFrullaniKernel (z + (s : ℂ)) 1 x‖ ≤
            C * Real.exp (-(min z.re 1) * x)
        exact complexFrullaniShiftKernel_norm_le_exp z
          hclosed hx
      _ = C * (min z.re 1)⁻¹ := by
        rw [integral_const_mul, integral_laplaceKernel hm]

private noncomputable def complexWallisPhaseKernel (z : ℂ) (x : ℝ) : ℂ :=
  ((1 - Complex.exp (-(x : ℂ))) *
      Complex.exp (-z * (x : ℂ)) -
    (x : ℂ) * Complex.exp (-(x : ℂ))) /
      (x : ℂ) ^ 2

private theorem intervalIntegral_complexFrullaniShift
    (z : ℂ) {x : ℝ} (hx : x ≠ 0) :
    (∫ s in (0 : ℝ)..1,
      complexFrullaniKernel (z + (s : ℂ)) 1 x) =
      complexWallisPhaseKernel z x := by
  have hxc : (x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hx
  have hfirst :
      (∫ s in (0 : ℝ)..1,
        Complex.exp (-(z + (s : ℂ)) * (x : ℂ))) =
        complexFrullaniKernel z (z + 1) x := by
    convert!
      intervalIntegral_complexLaplaceSegment z (z + 1) hx
      using 1
    apply intervalIntegral.integral_congr
    intro s _
    unfold complexFrullaniSegment
    push_cast
    ring_nf
  have hfirstContinuous :
      Continuous
        (fun s : ℝ =>
          Complex.exp (-(z + (s : ℂ)) * (x : ℂ))) := by
    fun_prop
  have hconstantContinuous :
      Continuous
        (fun _ : ℝ => Complex.exp (-(x : ℂ))) :=
    continuous_const
  have hexponential :
      Complex.exp (-(z + 1) * (x : ℂ)) =
        Complex.exp (-z * (x : ℂ)) *
          Complex.exp (-(x : ℂ)) := by
    rw [show -(z + 1) * (x : ℂ) =
      -z * (x : ℂ) + -(x : ℂ) by ring,
      Complex.exp_add]
  unfold complexFrullaniKernel
  simp only [neg_one_mul]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_sub
      (hfirstContinuous.intervalIntegrable 0 1)
      (hconstantContinuous.intervalIntegrable 0 1),
    hfirst, intervalIntegral.integral_const]
  unfold complexFrullaniKernel complexWallisPhaseKernel
  simp only [sub_zero, one_smul]
  rw [hexponential]
  field_simp [hxc]

private theorem complexWallisPhaseKernel_integrable
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (complexWallisPhaseKernel z) (Ioi 0) := by
  have hproduct :=
    (complexFrullaniShiftParameter_integrable hz).integral_prod_right
  apply hproduct.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change
    (∫ s in Set.uIoc (0 : ℝ) 1,
      complexFrullaniKernel (z + (s : ℂ)) 1 x) =
      complexWallisPhaseKernel z x
  rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    ← intervalIntegral.integral_of_le
      (show (0 : ℝ) ≤ 1 by norm_num)]
  exact intervalIntegral_complexFrullaniShift z hx.ne'

private theorem complexWallisTranslatedSegment_hasDerivAt
    (z : ℂ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => z + (r : ℂ)) (1 : ℂ) s := by
  have hreal :
      HasDerivAt (fun r : ℝ => (r : ℂ)) (1 : ℂ) s := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using! Complex.ofRealCLM.hasDerivAt
  simpa only [hasDerivAt_const_add_iff] using! hreal.const_add z

private theorem complexWallisLogPrimitive_hasDerivAt
    {z : ℂ} (hz : 0 < z.re)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun r : ℝ =>
        (z + (r : ℂ)) * Complex.log (z + (r : ℂ)) -
          (z + (r : ℂ)))
      (Complex.log (z + (s : ℂ))) s := by
  have hline := complexWallisTranslatedSegment_hasDerivAt z s
  have hpositive : 0 < (z + (s : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith [hs.1]
  have hslit : z + (s : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl hpositive)
  have hnonzero : z + (s : ℂ) ≠ 0 :=
    Complex.slitPlane_ne_zero hslit
  have hlog := hline.clog_real hslit
  convert! (hline.mul hlog).sub hline using 1
  simp only [one_mul, div_eq_mul_inv, ne_eq, hnonzero, not_false_eq_true, mul_inv_cancel₀,
    add_sub_cancel_right]

private theorem intervalIntegral_complexWallisLog
    {z : ℂ} (hz : 0 < z.re) :
    (∫ s in (0 : ℝ)..1,
      Complex.log (z + (s : ℂ))) =
      (z + 1) * Complex.log (z + 1) -
        z * Complex.log z - 1 := by
  have hline : Continuous (fun s : ℝ => z + (s : ℂ)) := by
    fun_prop
  have hlog :
      ContinuousOn
        (fun s : ℝ => Complex.log (z + (s : ℂ)))
        (Set.uIcc (0 : ℝ) 1) := by
    apply hline.continuousOn.clog
    intro s hs
    rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith [hs.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => by
      rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
      exact complexWallisLogPrimitive_hasDerivAt hz s hs)
    hlog.intervalIntegrable]
  push_cast
  simp only [add_zero]
  ring

private theorem integral_complexWallisPhaseKernel
    {z : ℂ} (hz : 0 < z.re) :
    (∫ x : ℝ in Ioi 0, complexWallisPhaseKernel z x) =
      1 + z * Complex.log z -
        (z + 1) * Complex.log (z + 1) := by
  calc
    (∫ x : ℝ in Ioi 0, complexWallisPhaseKernel z x) =
      ∫ x : ℝ in Ioi 0,
        ∫ s in (0 : ℝ)..1,
          complexFrullaniKernel (z + (s : ℂ)) 1 x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact
        (intervalIntegral_complexFrullaniShift z hx.ne').symm
    _ = ∫ s in (0 : ℝ)..1,
          ∫ x : ℝ in Ioi 0,
            complexFrullaniKernel (z + (s : ℂ)) 1 x :=
      (intervalIntegral_integral_swap
        (complexFrullaniShiftParameter_integrable hz)).symm
    _ = ∫ s in (0 : ℝ)..1,
          -Complex.log (z + (s : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
      have hspositive : 0 < (z + (s : ℂ)).re := by
        simp only [Complex.add_re, Complex.ofReal_re]
        linarith [hs.1]
      change
        (∫ x : ℝ in Ioi 0,
          complexFrullaniKernel (z + (s : ℂ)) 1 x) =
          -Complex.log (z + (s : ℂ))
      rw [integral_complexFrullaniKernel
        hspositive (by norm_num : 0 < (1 : ℂ).re)]
      simp only [Complex.log_one, zero_sub]
    _ = -(∫ s in (0 : ℝ)..1,
          Complex.log (z + (s : ℂ))) := by
      rw [intervalIntegral.integral_neg]
    _ = 1 + z * Complex.log z -
        (z + 1) * Complex.log (z + 1) := by
      rw [intervalIntegral_complexWallisLog hz]
      ring

end

section

open Filter MeasureTheory Set
open scoped Interval Topology

private noncomputable def stripNormalizedPoissonKernel (σ T : ℝ) : ℝ :=
  stripPoissonKernel σ T / stripBottomMass σ

private noncomputable def stripNormalizedPoissonExtension (σ T : ℝ) : ℝ :=
  (Real.pi / 4) *
    Real.sinc (Real.pi * (1 - σ) / 2) /
      (Real.cosh (Real.pi * T / 2) +
        Real.cos (Real.pi * (1 - σ) / 2))

private noncomputable def limitingStripPoissonDensity (T : ℝ) : ℝ :=
  Real.pi /
    (4 * (Real.cosh (Real.pi * T / 2) + 1))

private theorem stripAngle_eq_pi_sub (σ : ℝ) :
    stripAngle σ =
      Real.pi - Real.pi * (1 - σ) / 2 := by
  unfold stripAngle
  ring

private theorem stripNormalizedPoissonKernel_eq_extension
    {σ : ℝ} (_hbelow : -1 < σ) (habove : σ < 1) (T : ℝ) :
    stripNormalizedPoissonKernel σ T =
      stripNormalizedPoissonExtension σ T := by
  have hsmall : Real.pi * (1 - σ) / 2 ≠ 0 := by
    exact ne_of_gt (div_pos (mul_pos Real.pi_pos (sub_pos.mpr habove))
      (by norm_num))
  have hmass : 1 - σ ≠ 0 := (sub_pos.mpr habove).ne'
  have hden :
      Real.cosh (Real.pi * T / 2) +
        Real.cos (Real.pi * (1 - σ) / 2) ≠ 0 := by
    have hangle := stripAngle_mem_Ioo _hbelow habove
    have horiginal :
        0 < Real.cosh (Real.pi * T / 2) -
          Real.cos (stripAngle σ) := by
      have hcos : Real.cos (stripAngle σ) < 1 := by
        have h := Real.cos_lt_cos_of_nonneg_of_le_pi
          (x := 0) (y := stripAngle σ)
          (by norm_num) hangle.2.le hangle.1
        simpa only [gt_iff_lt, Real.cos_zero] using! h
      linarith [Real.one_le_cosh (Real.pi * T / 2)]
    rw [stripAngle_eq_pi_sub, Real.cos_pi_sub] at horiginal
    have hpositive :
        0 < Real.cosh (Real.pi * T / 2) +
          Real.cos (Real.pi * (1 - σ) / 2) := by
      simpa only [sub_neg_eq_add] using! horiginal
    exact hpositive.ne'
  unfold stripNormalizedPoissonKernel stripPoissonKernel
    stripBottomMass stripNormalizedPoissonExtension
  rw [stripAngle_eq_pi_sub, Real.sin_pi_sub, Real.cos_pi_sub,
    Real.sinc_of_ne_zero hsmall]
  field_simp [hmass, hsmall, hden, Real.pi_ne_zero]; ring

private theorem stripNormalizedPoissonExtension_one (T : ℝ) :
    stripNormalizedPoissonExtension 1 T =
      limitingStripPoissonDensity T := by
  have hden : Real.cosh (Real.pi * T / 2) + 1 ≠ 0 := by
    linarith [Real.one_le_cosh (Real.pi * T / 2)]
  unfold stripNormalizedPoissonExtension limitingStripPoissonDensity
  simp only [sub_self, mul_zero, zero_div, Real.sinc_zero,
    Real.cos_zero, mul_one]
  field_simp [hden]

private theorem stripNormalizedPoissonExtension_continuousAt_one (T : ℝ) :
    ContinuousAt (fun σ : ℝ => stripNormalizedPoissonExtension σ T)
      1 := by
  unfold stripNormalizedPoissonExtension
  have hangle : Continuous
      (fun σ : ℝ => Real.pi * (1 - σ) / 2) := by
    fun_prop
  have hden :
      Real.cosh (Real.pi * T / 2) +
        Real.cos (Real.pi * (1 - (1 : ℝ)) / 2) ≠ 0 := by
    simp only [sub_self, mul_zero, zero_div, Real.cos_zero]
    have hcosh := Real.one_le_cosh (Real.pi * T / 2)
    linarith
  exact
    ((continuous_const.mul
      (Real.continuous_sinc.comp hangle)).continuousAt.div
        ((continuous_const.add
          (Real.continuous_cos.comp hangle)).continuousAt) hden)

private theorem tendsto_stripNormalizedPoissonKernel (T : ℝ) :
    Tendsto (fun σ : ℝ => stripNormalizedPoissonKernel σ T)
      (𝓝[<] 1) (𝓝 (limitingStripPoissonDensity T)) := by
  have hpos : ∀ᶠ σ : ℝ in 𝓝[<] (1 : ℝ), 0 < σ :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))
  have hlt : ∀ᶠ σ : ℝ in 𝓝[<] (1 : ℝ), σ < 1 :=
    self_mem_nhdsWithin
  have heq :
      (fun σ : ℝ => stripNormalizedPoissonKernel σ T) =ᶠ[𝓝[<] 1]
        (fun σ : ℝ => stripNormalizedPoissonExtension σ T) := by
    filter_upwards [hpos, hlt] with σ hσpos hσlt
    exact stripNormalizedPoissonKernel_eq_extension
      (by linarith) hσlt T
  have hext :
      Tendsto (fun σ : ℝ => stripNormalizedPoissonExtension σ T)
        (𝓝[<] 1) (𝓝 (limitingStripPoissonDensity T)) := by
    rw [← stripNormalizedPoissonExtension_one T]
    exact (stripNormalizedPoissonExtension_continuousAt_one T).tendsto.mono_left
      nhdsWithin_le_nhds
  exact hext.congr' heq.symm

private theorem stripNormalizedPoissonKernel_integrable
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    Integrable (stripNormalizedPoissonKernel σ) := by
  unfold stripNormalizedPoissonKernel
  exact (stripPoissonKernel_integrable hbelow habove).div_const _

private noncomputable def stripPoissonExponentialMajorant (T : ℝ) : ℝ :=
  (Real.pi / 2) *
    Real.exp (-(Real.pi / 2) * |T|)

private theorem inv_cosh_le_two_exp_neg_abs (u : ℝ) :
    (Real.cosh u)⁻¹ ≤ 2 * Real.exp (-|u|) := by
  have hhalf : Real.exp |u| / 2 ≤ Real.cosh u := by
    rw [← Real.cosh_abs, Real.cosh_eq]
    have hpositive := (Real.exp_pos (-|u|)).le
    linarith
  rw [← one_div, div_le_iff₀ (Real.cosh_pos u)]
  calc
    (1 : ℝ) =
        (2 * Real.exp (-|u|)) * (Real.exp |u| / 2) := by
      calc
        (1 : ℝ) = Real.exp (-|u|) * Real.exp |u| := by
          rw [← Real.exp_add]
          simp only [neg_add_cancel, Real.exp_zero]
        _ = (2 * Real.exp (-|u|)) * (Real.exp |u| / 2) := by
          ring
    _ ≤ (2 * Real.exp (-|u|)) * Real.cosh u :=
      mul_le_mul_of_nonneg_left hhalf (by positivity)

private theorem stripNormalizedPoissonExtension_le_majorant
    {σ : ℝ} (hzero : 0 ≤ σ) (hone : σ ≤ 1) (T : ℝ) :
    0 ≤ stripNormalizedPoissonExtension σ T ∧
      stripNormalizedPoissonExtension σ T ≤
        stripPoissonExponentialMajorant T := by
  let u : ℝ := Real.pi * T / 2
  let q : ℝ := Real.pi * (1 - σ) / 2
  have hqzero : 0 ≤ q := by
    try dsimp [q]
    exact div_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hone))
      (by norm_num)
  have hqlarge : q ≤ Real.pi / 2 := by
    try dsimp [q]
    linarith [mul_nonneg Real.pi_pos.le hzero]
  have hqpi : q ≤ Real.pi := by
    linarith [Real.pi_pos]
  have hcos : 0 ≤ Real.cos q :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos], hqlarge⟩
  have hsinc : 0 ≤ Real.sinc q := by
    by_cases hq : q = 0
    · simp only [hq, Real.sinc_zero, zero_le_one]
    · rw [Real.sinc_of_ne_zero hq]
      exact div_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi hqzero hqpi) hqzero
  have hden : 0 < Real.cosh u + Real.cos q :=
    add_pos_of_pos_of_nonneg (Real.cosh_pos u) hcos
  have hcoefficient : 0 < Real.pi / 4 :=
    div_pos Real.pi_pos (by norm_num)
  have habsu : |u| = (Real.pi / 2) * |T| := by
    try dsimp [u]
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
    norm_num
    ring
  constructor
  · unfold stripNormalizedPoissonExtension
    change 0 ≤ (Real.pi / 4) * Real.sinc q /
      (Real.cosh u + Real.cos q)
    exact div_nonneg (mul_nonneg hcoefficient.le hsinc) hden.le
  · unfold stripNormalizedPoissonExtension
      stripPoissonExponentialMajorant
    change
      (Real.pi / 4) * Real.sinc q /
        (Real.cosh u + Real.cos q) ≤
          (Real.pi / 2) *
            Real.exp (-(Real.pi / 2) * |T|)
    calc
      (Real.pi / 4) * Real.sinc q /
          (Real.cosh u + Real.cos q) ≤
        (Real.pi / 4) * 1 / Real.cosh u := by
          gcongr
          · exact Real.sinc_le_one q
          · exact le_add_of_nonneg_right hcos
      _ = (Real.pi / 4) * (Real.cosh u)⁻¹ := by
        simp only [div_eq_mul_inv, mul_one]
      _ ≤ (Real.pi / 4) * (2 * Real.exp (-|u|)) :=
        mul_le_mul_of_nonneg_left
          (inv_cosh_le_two_exp_neg_abs u) hcoefficient.le
      _ = (Real.pi / 2) *
          Real.exp (-(Real.pi / 2) * |T|) := by
        rw [habsu]
        ring_nf

private theorem integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun T : ℝ => Real.exp (-a * |T|)) := by
  have hright :
      IntegrableOn (fun T : ℝ => Real.exp (-a * |T|))
        (Ioi (0 : ℝ)) := by
    have h := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0
    apply h.congr_fun _ measurableSet_Ioi
    intro T hT
    change Real.exp (-a * T) = Real.exp (-a * |T|)
    rw [abs_of_pos hT]
  have hleft :
      IntegrableOn (fun T : ℝ => Real.exp (-a * |T|))
        (Iio (0 : ℝ)) := by
    have h := (integrableOn_exp_mul_Iic ha 0).mono_set
      (show Iio (0 : ℝ) ⊆ Iic (0 : ℝ) from
        fun _ hT => (mem_Iio.mp hT).le)
    apply h.congr_fun _ measurableSet_Iio
    intro T hT
    change Real.exp (a * T) = Real.exp (-a * |T|)
    rw [abs_of_neg hT]
    congr 1
    ring
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ),
    integrableOn_union, integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨hleft, hright⟩

private theorem stripPoissonExponentialMajorant_integrable :
    Integrable stripPoissonExponentialMajorant := by
  exact
    (integrable_exp_neg_mul_abs
      (half_pos Real.pi_pos)).const_mul (Real.pi / 2)

private theorem integrable_abs_pow_mul_exp_neg_mul_abs
    (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable
      (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) := by
  have hbase :
      IntegrableOn
        (fun T : ℝ => T ^ n * Real.exp (-a * T))
        (Ioi (0 : ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (n : ℝ)) (b := a)
      (by exact_mod_cast (show (-(1 : ℤ) < (n : ℤ)) by omega))
      (by norm_num) ha
    simpa only [neg_mul, Real.rpow_natCast, Real.rpow_one] using! h
  have hright :
      IntegrableOn
        (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|))
        (Ioi (0 : ℝ)) := by
    apply hbase.congr_fun _ measurableSet_Ioi
    intro T hT
    change T ^ n * Real.exp (-a * T) =
      |T| ^ n * Real.exp (-a * |T|)
    rw [abs_of_pos hT]
  have hreflected :
      IntegrableOn
        ((fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) ∘
          (fun T : ℝ => -T))
        ((fun T : ℝ => -T) ⁻¹' Iio (0 : ℝ)) := by
    simpa only [Function.comp_def, neg_preimage, neg_Iio, neg_zero,
      abs_neg] using! hright
  have hleft :
      IntegrableOn
        (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|))
        (Iio (0 : ℝ)) :=
    ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding).mp hreflected
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ),
    integrableOn_union, integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨hleft, hright⟩

private theorem limitingStripPoissonDensity_integrable :
    Integrable limitingStripPoissonDensity := by
  have hcontinuous : Continuous limitingStripPoissonDensity := by
    unfold limitingStripPoissonDensity
    apply Continuous.div continuous_const
    · fun_prop
    · intro T
      have hcosh := Real.one_le_cosh (Real.pi * T / 2)
      positivity
  apply stripPoissonExponentialMajorant_integrable.mono'
    hcontinuous.aestronglyMeasurable
  filter_upwards [] with T
  have h := stripNormalizedPoissonExtension_le_majorant
    (σ := (1 : ℝ)) (by norm_num) (by norm_num) T
  rw [stripNormalizedPoissonExtension_one] at h
  rw [Real.norm_eq_abs, abs_of_nonneg h.1]
  exact h.2

private noncomputable def poissonLogistic (u : ℝ) : ℝ :=
  Real.exp (Real.pi * u) /
    (1 + Real.exp (Real.pi * u))

private noncomputable def poissonLogisticDensity (u : ℝ) : ℝ :=
  Real.pi * Real.exp (Real.pi * u) /
    (1 + Real.exp (Real.pi * u)) ^ 2

private theorem poissonLogisticDensity_eq_limitingStripPoissonDensity
    (u : ℝ) :
    poissonLogisticDensity u =
      2 * limitingStripPoissonDensity (2 * u) := by
  have he : Real.exp (Real.pi * u) ≠ 0 :=
    (Real.exp_pos _).ne'
  unfold poissonLogisticDensity limitingStripPoissonDensity
  have harg : Real.pi * (2 * u) / 2 = Real.pi * u := by
    ring
  rw [harg, Real.cosh_eq, Real.exp_neg]
  field_simp [he]; ring

private theorem poissonLogistic_image_univ :
    poissonLogistic '' (Set.univ : Set ℝ) = Ioo (0 : ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨u, _, rfl⟩
    have he : 0 < Real.exp (Real.pi * u) := Real.exp_pos _
    unfold poissonLogistic
    constructor
    · positivity
    · apply (div_lt_one (by positivity)).2
      linarith
  · intro hx
    have hratio : 0 < x / (1 - x) :=
      div_pos hx.1 (sub_pos.mpr hx.2)
    refine ⟨Real.log (x / (1 - x)) / Real.pi,
      Set.mem_univ _, ?_⟩
    unfold poissonLogistic
    rw [mul_div_cancel₀ _ Real.pi_ne_zero,
      Real.exp_log hratio]
    field_simp [(sub_pos.mpr hx.2).ne']
    ring

private theorem poissonLogistic_hasDerivAt (u : ℝ) :
    HasDerivAt poissonLogistic (poissonLogisticDensity u) u := by
  have he :=
    (Real.hasDerivAt_exp (Real.pi * u)).comp u
      ((hasDerivAt_id u).const_mul Real.pi)
  have hden : 1 + Real.exp (Real.pi * u) ≠ 0 := by
    positivity
  have hquot := he.div ((hasDerivAt_const u 1).add he) hden
  convert! hquot using 1
  unfold poissonLogisticDensity
  simp only [Function.comp_apply, Pi.add_apply, mul_one, zero_add]
  field_simp [hden]
  ring

private theorem poissonLogistic_injective :
    Function.Injective poissonLogistic := by
  intro u v huv
  have heu : 1 + Real.exp (Real.pi * u) ≠ 0 := by positivity
  have hev : 1 + Real.exp (Real.pi * v) ≠ 0 := by positivity
  unfold poissonLogistic at huv
  have hexp :
      Real.exp (Real.pi * u) = Real.exp (Real.pi * v) := by
    apply (div_eq_div_iff heu hev).mp at huv
    linarith
  have harg : Real.pi * u = Real.pi * v :=
    Real.exp_injective hexp
  exact mul_left_cancel₀ Real.pi_ne_zero harg

private theorem poissonLogistic_mem_Ioo (u : ℝ) :
    poissonLogistic u ∈ Ioo (0 : ℝ) 1 := by
  rw [← poissonLogistic_image_univ]
  exact ⟨u, Set.mem_univ _, rfl⟩

private theorem poissonLogistic_odds (u : ℝ) :
    poissonLogistic u / (1 - poissonLogistic u) =
      Real.exp (Real.pi * u) := by
  have hden : 1 + Real.exp (Real.pi * u) ≠ 0 := by
    positivity
  unfold poissonLogistic
  field_simp [hden]
  ring

private theorem poissonLogistic_cpow_ratio (u : ℝ) (w : ℂ) :
    ((poissonLogistic u : ℝ) : ℂ) ^ w *
        (((1 - poissonLogistic u : ℝ) : ℂ) ^ (-w)) =
      Complex.exp (((Real.pi * u : ℝ) : ℂ) * w) := by
  have hx := poissonLogistic_mem_Ioo u
  have hfirst : (poissonLogistic u : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hx.1)
  have hsecond : ((1 - poissonLogistic u : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (sub_pos.mpr hx.2))
  have hlog :
      Real.log (poissonLogistic u) -
        Real.log (1 - poissonLogistic u) =
          Real.pi * u := by
    rw [← Real.log_div (ne_of_gt hx.1)
      (ne_of_gt (sub_pos.mpr hx.2)),
      poissonLogistic_odds, Real.log_exp]
  rw [Complex.cpow_def_of_ne_zero hfirst,
    Complex.cpow_def_of_ne_zero hsecond, ← Complex.exp_add,
    ← Complex.ofReal_log hx.1.le,
    ← Complex.ofReal_log (sub_pos.mpr hx.2).le]
  congr 1
  calc
    ((Real.log (poissonLogistic u) : ℝ) : ℂ) * w +
        ((Real.log (1 - poissonLogistic u) : ℝ) : ℂ) * (-w) =
      ((Real.log (poissonLogistic u) -
        Real.log (1 - poissonLogistic u) : ℝ) : ℂ) * w := by
          push_cast
          ring
    _ = ((Real.pi * u : ℝ) : ℂ) * w := by
      rw [hlog]

private theorem integral_poissonLogistic_change_Ioo {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :
    (∫ x : ℝ in Ioo 0 1, f x) =
      ∫ u : ℝ, poissonLogisticDensity u •
        f (poissonLogistic u) := by
  have hderiv :
      ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivWithinAt poissonLogistic
          (poissonLogisticDensity x) Set.univ x := by
    intro x _
    exact (poissonLogistic_hasDerivAt x).hasDerivWithinAt
  have hpositive (u : ℝ) : 0 < poissonLogisticDensity u := by
    unfold poissonLogisticDensity
    positivity
  have hrange :
      Set.range poissonLogistic = Ioo (0 : ℝ) 1 := by
    simpa only [Set.image_univ] using! poissonLogistic_image_univ
  have h := integral_image_eq_integral_abs_deriv_smul
    (f := poissonLogistic) (f' := poissonLogisticDensity)
    MeasurableSet.univ hderiv
    poissonLogistic_injective.injOn f
  simpa only [image_univ, hrange, Measure.restrict_univ, abs_of_pos (hpositive _)] using! h

private theorem poissonLogisticDensity_integrable :
    Integrable poissonLogisticDensity := by
  have hscaled :=
    limitingStripPoissonDensity_integrable.comp_mul_left'
      (by norm_num : (2 : ℝ) ≠ 0)
  apply (hscaled.const_mul (2 : ℝ)).congr
  filter_upwards [] with u
  exact (poissonLogisticDensity_eq_limitingStripPoissonDensity u).symm

private theorem integral_poissonLogisticDensity :
    (∫ u : ℝ, poissonLogisticDensity u) = 1 := by
  have h := integral_poissonLogistic_change_Ioo
    (fun _ : ℝ => (1 : ℝ))
  simpa only [smul_eq_mul, mul_one, integral_const, MeasurableSet.univ,
    measureReal_restrict_apply, univ_inter,
    Real.volume_real_Ioo, sub_zero, zero_le_one, sup_of_le_left] using! h.symm

private theorem poissonLogistic_betaIntegral (w : ℂ) :
    Complex.betaIntegral (1 + w) (1 - w) =
      ∫ u : ℝ,
        (poissonLogisticDensity u : ℂ) *
          Complex.exp (((Real.pi * u : ℝ) : ℂ) * w) := by
  calc
    Complex.betaIntegral (1 + w) (1 - w) =
        ∫ x : ℝ in Ioo 0 1,
          (x : ℂ) ^ w *
            (((1 - x : ℝ) : ℂ) ^ (-w)) := by
      unfold Complex.betaIntegral
      rw [intervalIntegral.integral_of_le
        (show (0 : ℝ) ≤ 1 by norm_num),
        integral_Ioc_eq_integral_Ioo]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x _
      push_cast
      congr 1 <;> ring_nf
    _ = ∫ u : ℝ,
        poissonLogisticDensity u •
          (((poissonLogistic u : ℝ) : ℂ) ^ w *
            (((1 - poissonLogistic u : ℝ) : ℂ) ^ (-w))) :=
      integral_poissonLogistic_change_Ioo
        (fun x : ℝ =>
          (x : ℂ) ^ w * (((1 - x : ℝ) : ℂ) ^ (-w)))
    _ = ∫ u : ℝ,
        (poissonLogisticDensity u : ℂ) *
          Complex.exp (((Real.pi * u : ℝ) : ℂ) * w) := by
      apply integral_congr_ae
      filter_upwards [] with u
      change
        (poissonLogisticDensity u : ℂ) *
            (((poissonLogistic u : ℝ) : ℂ) ^ w *
              (((1 - poissonLogistic u : ℝ) : ℂ) ^ (-w))) =
          (poissonLogisticDensity u : ℂ) *
            Complex.exp (((Real.pi * u : ℝ) : ℂ) * w)
      rw [poissonLogistic_cpow_ratio]

private theorem gamma_one_add_imaginary_mul_gamma_one_sub
    {x : ℝ} (hx : x ≠ 0) :
    Complex.Gamma (1 + Complex.I * (x : ℂ)) *
        Complex.Gamma (1 - Complex.I * (x : ℂ)) =
      ((Real.pi * x / Real.sinh (Real.pi * x) : ℝ) : ℂ) := by
  let z : ℂ := Complex.I * (x : ℂ)
  have hz : z ≠ 0 := by
    try dsimp [z]
    exact mul_ne_zero Complex.I_ne_zero
      (Complex.ofReal_ne_zero.mpr hx)
  have hnegz : -z ≠ 0 := neg_ne_zero.mpr hz
  have hplus :
      Complex.Gamma (1 + z) = z * Complex.Gamma z := by
    convert! Complex.Gamma_add_one z hz using 1; ring_nf
  have hminus :
      Complex.Gamma (1 - z) =
        (-z) * Complex.Gamma (-z) := by
    convert! Complex.Gamma_add_one (-z) hnegz using 1; ring_nf
  have hconjarg : -z = starRingEnd ℂ z := by
    try dsimp [z]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hgammaprod :
      Complex.Gamma z * Complex.Gamma (-z) =
        (‖Complex.Gamma z‖ ^ 2 : ℝ) := by
    rw [hconjarg, Complex.Gamma_conj, mul_comm,
      ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
  have hsinh : Real.sinh (Real.pi * x) ≠ 0 :=
    Real.sinh_ne_zero.mpr
      (mul_ne_zero Real.pi_ne_zero hx)
  change Complex.Gamma (1 + z) *
    Complex.Gamma (1 - z) = _
  rw [hplus, hminus]
  calc
    (z * Complex.Gamma z) *
        ((-z) * Complex.Gamma (-z)) =
      ((x ^ 2 : ℝ) : ℂ) *
        (Complex.Gamma z * Complex.Gamma (-z)) := by
          try dsimp [z]
          ring_nf
          simp only [Complex.I_sq, neg_mul, one_mul, neg_neg, Complex.ofReal_pow]
          ring
    _ = ((x ^ 2 * ‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) := by
      rw [hgammaprod]
      push_cast
      ring
    _ = ((Real.pi * x / Real.sinh (Real.pi * x) : ℝ) : ℂ) := by
      try dsimp [z]
      rw [norm_gamma_imaginary_sq hx]
      congr 1
      field_simp [hx, hsinh]

private theorem poissonLogistic_characteristic_of_ne_zero
    {t : ℝ} (ht : t ≠ 0) :
    (∫ u : ℝ,
      (poissonLogisticDensity u : ℂ) *
        Complex.exp
          (Complex.I * (t : ℂ) * (u : ℂ))) =
      ((t / Real.sinh t : ℝ) : ℂ) := by
  let x : ℝ := t / Real.pi
  have hx : x ≠ 0 := by
    try dsimp [x]
    exact div_ne_zero ht Real.pi_ne_zero
  let w : ℂ := Complex.I * (x : ℂ)
  have hwplus : 0 < (1 + w).re := by
    try dsimp [w]
    norm_num
  have hwminus : 0 < (1 - w).re := by
    try dsimp [w]
    norm_num
  have hphase (u : ℝ) :
      ((Real.pi * u : ℝ) : ℂ) * w =
        Complex.I * (t : ℂ) * (u : ℂ) := by
    try dsimp [w, x]
    push_cast
    field_simp [Real.pi_ne_zero]
  have hbeta :
      Complex.betaIntegral (1 + w) (1 - w) =
        Complex.Gamma (1 + w) *
          Complex.Gamma (1 - w) := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div
      (1 + w) (1 - w) hwplus hwminus]
    have hsum : (1 + w) + (1 - w) = (2 : ℂ) := by
      ring
    rw [hsum]
    norm_num
  have hscale : Real.pi * x = t := by
    try dsimp [x]
    field_simp [Real.pi_ne_zero]
  calc
    (∫ u : ℝ,
      (poissonLogisticDensity u : ℂ) *
        Complex.exp
          (Complex.I * (t : ℂ) * (u : ℂ))) =
        Complex.betaIntegral (1 + w) (1 - w) := by
      rw [poissonLogistic_betaIntegral w]
      apply integral_congr_ae
      filter_upwards [] with u
      rw [hphase]
    _ = Complex.Gamma (1 + w) *
          Complex.Gamma (1 - w) := hbeta
    _ = ((Real.pi * x / Real.sinh (Real.pi * x) : ℝ) : ℂ) := by
      exact gamma_one_add_imaginary_mul_gamma_one_sub hx
    _ = ((t / Real.sinh t : ℝ) : ℂ) := by
      rw [hscale]

private theorem poissonLogistic_characteristic (t : ℝ) :
    (∫ u : ℝ,
      (poissonLogisticDensity u : ℂ) *
        Complex.exp
          (Complex.I * (t : ℂ) * (u : ℂ))) =
      if t = 0 then 1 else
        ((t / Real.sinh t : ℝ) : ℂ) := by
  by_cases ht : t = 0
  · subst t
    simp only [Complex.ofReal_zero, mul_zero, zero_mul,
      Complex.exp_zero, mul_one, ↓reduceIte]
    let m : ℝ := ∫ u : ℝ, poissonLogisticDensity u
    have hm : m = 1 := integral_poissonLogisticDensity
    calc
      (∫ u : ℝ, (poissonLogisticDensity u : ℂ)) =
          (m : ℂ) := by
        try dsimp [m]
        exact integral_ofReal
      _ = 1 := by
        rw [hm]
        norm_num
  · simpa only [ht, ↓reduceIte, Complex.ofReal_div, Complex.ofReal_sinh] using!
      poissonLogistic_characteristic_of_ne_zero ht

private theorem poissonLogistic_characteristic_integrable (t : ℝ) :
    Integrable
      (fun u : ℝ =>
        (poissonLogisticDensity u : ℂ) *
          Complex.exp
            (Complex.I * (t : ℂ) * (u : ℂ))) := by
  have hcontinuous :
      Continuous (fun u : ℝ =>
        Complex.exp
          (Complex.I * (t : ℂ) * (u : ℂ))) := by
    fun_prop
  apply poissonLogisticDensity_integrable.mono'
    (poissonLogisticDensity_integrable.ofReal.aestronglyMeasurable.mul
      hcontinuous.aestronglyMeasurable)
  filter_upwards [] with u
  have hdensity : 0 < poissonLogisticDensity u := by
    unfold poissonLogisticDensity
    positivity
  change
    ‖(poissonLogisticDensity u : ℂ) *
      Complex.exp
        (Complex.I * (t : ℂ) * (u : ℂ))‖ ≤
      poissonLogisticDensity u
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hdensity]
  have hphase :
      Complex.I * (t : ℂ) * (u : ℂ) =
        Complex.I * ((t * u : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hphase, Complex.norm_exp_I_mul_ofReal]
  simp only [mul_one, Std.le_refl]

private theorem poissonLogistic_cosine_transform (t : ℝ) :
    (∫ u : ℝ,
      poissonLogisticDensity u * Real.cos (t * u)) =
      if t = 0 then 1 else t / Real.sinh t := by
  calc
    (∫ u : ℝ,
      poissonLogisticDensity u * Real.cos (t * u)) =
        ∫ u : ℝ,
          ((poissonLogisticDensity u : ℂ) *
            Complex.exp
              (Complex.I * (t : ℂ) * (u : ℂ))).re := by
      apply integral_congr_ae
      filter_upwards [] with u
      have hphase :
          Complex.I * (t : ℂ) * (u : ℂ) =
            ((t * u : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [hphase, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_re]
      ring
    _ =
      (∫ u : ℝ,
        (poissonLogisticDensity u : ℂ) *
          Complex.exp
            (Complex.I * (t : ℂ) * (u : ℂ))).re :=
      integral_re (poissonLogistic_characteristic_integrable t)
    _ = if t = 0 then 1 else t / Real.sinh t := by
      rw [poissonLogistic_characteristic t]
      split
      · simp only [Complex.one_re]
      · exact Complex.ofReal_re (t / Real.sinh t)

private theorem lowerEndpointPhase_continuous :
    Continuous lowerEndpointPhase := by
  have hargument : Continuous
      (fun T : ℝ => 1 + T ^ 2 / 4) := by
    fun_prop
  have hlog : Continuous
      (fun T : ℝ => Real.log (1 + T ^ 2 / 4)) :=
    hargument.log (fun T => by
      have hsq : 0 ≤ T ^ 2 := sq_nonneg T
      positivity)
  have hfirst : Continuous
      (fun T : ℝ => -Real.pi * |T| / 4) := by
    fun_prop
  have hsecond : Continuous
      (fun T : ℝ =>
        (1 / 2 : ℝ) * Real.log (1 + T ^ 2 / 4)) :=
    continuous_const.mul hlog
  have hthird : Continuous
      (fun T : ℝ =>
        |T| / 2 * Real.arctan (|T| / 2)) :=
    (continuous_abs.div_const 2).mul
      (Real.continuous_arctan.comp
        (continuous_abs.div_const 2))
  exact (hfirst.sub hsecond).add hthird

private theorem abs_lowerEndpointPhase_le (T : ℝ) :
    |lowerEndpointPhase T| ≤ Real.pi * |T| + T ^ 2 := by
  have hnonneg : 0 ≤ T ^ 2 / 4 := by positivity
  have hlogzero : 0 ≤ Real.log (1 + T ^ 2 / 4) :=
    Real.log_nonneg (by linarith)
  have hlogupper :
      Real.log (1 + T ^ 2 / 4) ≤ T ^ 2 / 4 := by
    have h := Real.log_le_sub_one_of_pos
      (show 0 < 1 + T ^ 2 / 4 by positivity)
    linarith
  have hatanzero : 0 ≤ Real.arctan (|T| / 2) :=
    Real.arctan_nonneg.mpr (by positivity)
  have hatanupper : Real.arctan (|T| / 2) ≤ Real.pi / 2 :=
    (Real.arctan_lt_pi_div_two _).le
  have hmulzero :
      0 ≤ |T| / 2 * Real.arctan (|T| / 2) :=
    mul_nonneg (by positivity) hatanzero
  have hmulupper :
      |T| / 2 * Real.arctan (|T| / 2) ≤
        |T| / 2 * (Real.pi / 2) :=
    mul_le_mul_of_nonneg_left hatanupper (by positivity)
  have hpimagnitude : 0 ≤ Real.pi * |T| :=
    mul_nonneg Real.pi_pos.le (abs_nonneg T)
  unfold lowerEndpointPhase
  apply (abs_le).2
  constructor
  · linarith [sq_nonneg T]
  · linarith [sq_nonneg T]

private theorem stripPoissonExponentialMajorant_mul_lowerEndpointPhase_integrable :
    Integrable
      (fun T : ℝ =>
        stripPoissonExponentialMajorant T *
          ‖lowerEndpointPhase T‖) := by
  have ha : 0 < Real.pi / 2 := half_pos Real.pi_pos
  have hfirst :
      Integrable
        (fun T : ℝ =>
          ((Real.pi / 2) * Real.pi) *
            (|T| ^ (1 : ℕ) *
              Real.exp (-(Real.pi / 2) * |T|))) :=
    (integrable_abs_pow_mul_exp_neg_mul_abs 1 ha).const_mul
      ((Real.pi / 2) * Real.pi)
  have hsecond :
      Integrable
        (fun T : ℝ =>
          (Real.pi / 2) *
            (|T| ^ (2 : ℕ) *
              Real.exp (-(Real.pi / 2) * |T|))) :=
    (integrable_abs_pow_mul_exp_neg_mul_abs 2 ha).const_mul
      (Real.pi / 2)
  apply (hfirst.add hsecond).mono'
    (by
      unfold stripPoissonExponentialMajorant
      exact
        ((continuous_const.mul
          (Real.continuous_exp.comp
            (continuous_const.mul continuous_abs))).mul
          lowerEndpointPhase_continuous.norm).aestronglyMeasurable)
  filter_upwards [] with T
  have hphase := abs_lowerEndpointPhase_le T
  have hfactor :
      0 ≤ (Real.pi / 2) *
        Real.exp (-(Real.pi / 2) * |T|) := by positivity
  change
    |((Real.pi / 2) * Real.exp (-(Real.pi / 2) * |T|)) *
        ‖lowerEndpointPhase T‖| ≤
      ((Real.pi / 2) * Real.pi) *
          (|T| ^ (1 : ℕ) *
            Real.exp (-(Real.pi / 2) * |T|)) +
        (Real.pi / 2) *
          (|T| ^ (2 : ℕ) *
            Real.exp (-(Real.pi / 2) * |T|))
  rw [abs_of_nonneg (mul_nonneg hfactor (norm_nonneg _))]
  calc
    (Real.pi / 2) * Real.exp (-(Real.pi / 2) * |T|) *
        ‖lowerEndpointPhase T‖ ≤
      ((Real.pi / 2) * Real.exp (-(Real.pi / 2) * |T|)) *
        (Real.pi * |T| + T ^ 2) := by
          rw [Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left hphase hfactor
    _ = ((Real.pi / 2) * Real.pi) *
          (|T| ^ (1 : ℕ) *
            Real.exp (-(Real.pi / 2) * |T|)) +
        (Real.pi / 2) *
          (|T| ^ (2 : ℕ) *
            Real.exp (-(Real.pi / 2) * |T|)) := by
          rw [pow_one, sq_abs]
          ring

private theorem tendsto_integral_stripNormalizedPoissonKernel_mul
    (f : ℝ → ℝ) (hf : AEStronglyMeasurable f volume)
    (hmajor : Integrable
      (fun T : ℝ => stripPoissonExponentialMajorant T * ‖f T‖)) :
    Tendsto
      (fun σ : ℝ =>
        ∫ T : ℝ, stripNormalizedPoissonKernel σ T * f T)
      (𝓝[<] 1)
      (𝓝 (∫ T : ℝ, limitingStripPoissonDensity T * f T)) := by
  have hpos : ∀ᶠ σ : ℝ in 𝓝[<] (1 : ℝ), 0 < σ :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))
  have hlt : ∀ᶠ σ : ℝ in 𝓝[<] (1 : ℝ), σ < 1 :=
    self_mem_nhdsWithin
  apply tendsto_integral_filter_of_dominated_convergence
    (fun T : ℝ => stripPoissonExponentialMajorant T * ‖f T‖)
  · filter_upwards [hpos, hlt] with σ hσpos hσlt
    exact
      (stripNormalizedPoissonKernel_integrable
        (by linarith) hσlt).aestronglyMeasurable.mul hf
  · filter_upwards [hpos, hlt] with σ hσpos hσlt
    filter_upwards [] with T
    have hext := stripNormalizedPoissonKernel_eq_extension
      (by linarith : -1 < σ) hσlt T
    have hbound := stripNormalizedPoissonExtension_le_majorant
      hσpos.le hσlt.le T
    rw [norm_mul, Real.norm_eq_abs, hext,
      abs_of_nonneg hbound.1]
    exact mul_le_mul_of_nonneg_right hbound.2 (norm_nonneg _)
  · exact hmajor
  · filter_upwards [] with T
    exact (tendsto_stripNormalizedPoissonKernel T).mul
      tendsto_const_nhds

private noncomputable def lowerPoissonEndpointExpectation (σ : ℝ) : ℝ :=
  ∫ T : ℝ,
    stripNormalizedPoissonKernel σ T * lowerEndpointPhase T

private noncomputable def limitingPoissonEndpointExpectation : ℝ :=
  ∫ T : ℝ,
    limitingStripPoissonDensity T * lowerEndpointPhase T

private theorem tendsto_lowerPoissonEndpointExpectation :
    Tendsto lowerPoissonEndpointExpectation (𝓝[<] 1)
      (𝓝 limitingPoissonEndpointExpectation) := by
  exact tendsto_integral_stripNormalizedPoissonKernel_mul
    lowerEndpointPhase
    lowerEndpointPhase_continuous.aestronglyMeasurable
    stripPoissonExponentialMajorant_mul_lowerEndpointPhase_integrable

private theorem poissonLogistic_cosine_integrable (t : ℝ) :
    Integrable
      (fun u : ℝ =>
        poissonLogisticDensity u * Real.cos (t * u)) := by
  have hcontinuous :
      Continuous (fun u : ℝ => Real.cos (t * u)) := by
    fun_prop
  apply poissonLogisticDensity_integrable.mono'
    (poissonLogisticDensity_integrable.aestronglyMeasurable.mul
      hcontinuous.aestronglyMeasurable)
  filter_upwards [] with u
  have hpositive : 0 < poissonLogisticDensity u := by
    unfold poissonLogisticDensity
    positivity
  change
    |poissonLogisticDensity u * Real.cos (t * u)| ≤
      poissonLogisticDensity u
  rw [abs_mul, abs_of_pos hpositive]
  exact mul_le_of_le_one_right hpositive.le
    (Real.abs_cos_le_one _)

private theorem poissonLogisticDensity_le_pi_exp (u : ℝ) :
    poissonLogisticDensity u ≤
      Real.pi * Real.exp (-Real.pi * |u|) := by
  have hbound :=
    stripNormalizedPoissonExtension_le_majorant
      (σ := (1 : ℝ)) (by norm_num) (by norm_num) (2 * u)
  rw [stripNormalizedPoissonExtension_one] at hbound
  calc
    poissonLogisticDensity u =
      2 * limitingStripPoissonDensity (2 * u) :=
      poissonLogisticDensity_eq_limitingStripPoissonDensity u
    _ ≤ 2 * stripPoissonExponentialMajorant (2 * u) :=
      mul_le_mul_of_nonneg_left hbound.2 (by norm_num)
    _ = Real.pi * Real.exp (-Real.pi * |u|) := by
      unfold stripPoissonExponentialMajorant
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring_nf

private theorem poissonLogisticDensity_abs_moment_integrable (n : ℕ) :
    Integrable
      (fun u : ℝ => poissonLogisticDensity u * |u| ^ n) := by
  have hmajor :=
    (integrable_abs_pow_mul_exp_neg_mul_abs n Real.pi_pos).const_mul
      Real.pi
  apply hmajor.mono'
    (poissonLogisticDensity_integrable.aestronglyMeasurable.mul
      ((continuous_abs.pow n).aestronglyMeasurable))
  filter_upwards [] with u
  have hdensity : 0 < poissonLogisticDensity u := by
    unfold poissonLogisticDensity
    positivity
  have hmoment : 0 ≤ |u| ^ n := pow_nonneg (abs_nonneg _) _
  change
    |poissonLogisticDensity u * |u| ^ n| ≤
      Real.pi * (|u| ^ n * Real.exp (-Real.pi * |u|))
  rw [abs_of_nonneg (mul_nonneg hdensity.le hmoment)]
  calc
    poissonLogisticDensity u * |u| ^ n ≤
      (Real.pi * Real.exp (-Real.pi * |u|)) * |u| ^ n :=
      mul_le_mul_of_nonneg_right
        (poissonLogisticDensity_le_pi_exp u) hmoment
    _ = Real.pi * (|u| ^ n * Real.exp (-Real.pi * |u|)) := by
      ring

private noncomputable def lowerWallisPhaseKernel (u t : ℝ) : ℝ :=
  ((1 - Real.exp (-t)) * Real.cos (u * t) -
    t * Real.exp (-t)) / t ^ 2

private theorem lowerWallisPhaseKernel_abs_le_moment
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    |lowerWallisPhaseKernel u t| ≤ |u| + 1 := by
  let q : ℝ := Real.exp (-t)
  have hqpos : 0 < q := by
    try dsimp [q]
    positivity
  have hqone : q ≤ 1 := by
    try dsimp [q]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hone : 0 ≤ 1 - q := by
    linarith
  have hone_le : 1 - q ≤ t := by
    try dsimp [q]
    linarith [Real.add_one_le_exp (-t)]
  have hcos :
      |Real.cos (u * t) - 1| ≤ |u| * t := by
    have h := Real.abs_cos_sub_cos_le (u * t) 0
    simpa only [ge_iff_le, Real.cos_zero, sub_zero, abs_mul, abs_of_pos ht] using! h
  have hqproduct : (1 + t) * q ≤ 1 := by
    calc
      (1 + t) * q ≤ Real.exp t * q := by
        apply mul_le_mul_of_nonneg_right _ hqpos.le
        simpa only [add_comm] using! Real.add_one_le_exp t
      _ = 1 := by
        try dsimp [q]
        rw [← Real.exp_add]
        simp only [add_neg_cancel, Real.exp_zero]
  have hcancel_nonneg : 0 ≤ 1 - q - t * q := by
    linarith
  have hcancel_upper : 1 - q - t * q ≤ t ^ 2 := by
    calc
      1 - q - t * q ≤ t * (1 - q) := by
        linarith [hone_le]
      _ ≤ t * t :=
        mul_le_mul_of_nonneg_left hone_le ht.le
      _ = t ^ 2 := by
        ring
  have hdecomp :
      (1 - q) * Real.cos (u * t) - t * q =
        (1 - q) * (Real.cos (u * t) - 1) +
          (1 - q - t * q) := by
    ring
  have hsq : 0 < t ^ 2 := sq_pos_of_pos ht
  unfold lowerWallisPhaseKernel
  change
    |((1 - q) * Real.cos (u * t) - t * q) / t ^ 2| ≤
      |u| + 1
  rw [hdecomp, abs_div, abs_of_pos hsq]
  apply (div_le_iff₀ hsq).2
  calc
    |(1 - q) * (Real.cos (u * t) - 1) +
        (1 - q - t * q)| ≤
      |(1 - q) * (Real.cos (u * t) - 1)| +
        |1 - q - t * q| :=
      abs_add_le _ _
    _ = (1 - q) * |Real.cos (u * t) - 1| +
        (1 - q - t * q) := by
      rw [abs_mul, abs_of_nonneg hone,
        abs_of_nonneg hcancel_nonneg]
    _ ≤ (1 - q) * (|u| * t) + t ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_left hcos hone)
        hcancel_upper
    _ ≤ t * (|u| * t) + t ^ 2 := by
      linarith [mul_le_mul_of_nonneg_right hone_le
        (mul_nonneg (abs_nonneg u) ht.le)]
    _ = (|u| + 1) * t ^ 2 := by
      ring

private theorem lowerWallisPhaseKernel_abs_le_tail
    (u : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    |lowerWallisPhaseKernel u t| ≤
      1 / t ^ 2 + Real.exp (-t) := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  let q : ℝ := Real.exp (-t)
  have hqpos : 0 < q := by
    try dsimp [q]
    positivity
  have hqone : q ≤ 1 := by
    try dsimp [q]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hone : 0 ≤ 1 - q := by
    linarith
  have hone_upper : 1 - q ≤ 1 := by
    linarith
  have ht_sq : t ≤ t ^ 2 := by
    nlinarith
  have hsq : 0 < t ^ 2 := sq_pos_of_pos htpos
  unfold lowerWallisPhaseKernel
  change
    |((1 - q) * Real.cos (u * t) - t * q) / t ^ 2| ≤
      1 / t ^ 2 + q
  rw [abs_div, abs_of_pos hsq]
  apply (div_le_iff₀ hsq).2
  calc
    |(1 - q) * Real.cos (u * t) - t * q| ≤
      |(1 - q) * Real.cos (u * t)| + |t * q| :=
      abs_sub _ _
    _ = (1 - q) * |Real.cos (u * t)| + t * q := by
      rw [abs_mul, abs_of_nonneg hone,
        abs_mul, abs_of_pos htpos, abs_of_pos hqpos]
    _ ≤ 1 + t * q := by
      have hcos : |Real.cos (u * t)| ≤ 1 :=
        Real.abs_cos_le_one _
      have hfactor :
          (1 - q) * |Real.cos (u * t)| ≤ 1 := by
        calc
          (1 - q) * |Real.cos (u * t)| ≤
            (1 - q) * 1 :=
            mul_le_mul_of_nonneg_left hcos hone
          _ ≤ 1 := by
            simpa only [mul_one, tsub_le_iff_right, le_add_iff_nonneg_right] using! hone_upper
      linarith
    _ ≤ 1 + q * t ^ 2 := by
      linarith [mul_nonneg hqpos.le
        (sub_nonneg.mpr ht_sq)]
    _ = (1 / t ^ 2 + q) * t ^ 2 := by
      field_simp [htpos.ne']

private theorem lowerWallisPhaseTail_integrable :
    IntegrableOn
      (fun t : ℝ => 1 / t ^ 2 + Real.exp (-t))
      (Ioi 1) := by
  have hpower :
      IntegrableOn (fun t : ℝ => t ^ (-(2 : ℝ))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt
      (by norm_num : (-(2 : ℝ)) < -1)
      (by norm_num : (0 : ℝ) < 1)
  have hinverse :
      IntegrableOn (fun t : ℝ => 1 / t ^ 2) (Ioi 1) := by
    apply hpower.congr_fun _ measurableSet_Ioi
    intro t ht
    have htpos : 0 < t :=
      lt_trans zero_lt_one (show 1 < t from ht)
    change t ^ (-(2 : ℝ)) = 1 / t ^ 2
    rw [Real.rpow_neg htpos.le, Real.rpow_ofNat]
    simp only [one_div]
  have hexponential :
      IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 1) := by
    have h := laplaceKernel_integrable
      (a := (1 : ℝ)) zero_lt_one
    have hrestrict := h.mono_set
      (show Ioi (1 : ℝ) ⊆ Ioi 0 from
        fun t ht => by
          change 0 < t
          exact lt_trans zero_lt_one (show 1 < t from ht))
    simpa only [neg_mul, one_mul] using! hrestrict
  exact hinverse.add hexponential

private theorem poissonLogistic_lowerWallisPhase_product_integrable :
    Integrable
      (fun p : ℝ × ℝ =>
        poissonLogisticDensity p.1 *
          lowerWallisPhaseKernel p.1 p.2)
      (volume.prod (volume.restrict (Ioi 0))) := by
  let F : ℝ × ℝ → ℝ := fun p =>
    poissonLogisticDensity p.1 *
      lowerWallisPhaseKernel p.1 p.2
  have hmeas : Measurable F := by
    try dsimp [F]
    unfold poissonLogisticDensity lowerWallisPhaseKernel
    fun_prop
  have hfrequency :
      Integrable
        (fun u : ℝ =>
          poissonLogisticDensity u * (|u| + 1)) := by
    have h :=
      (poissonLogisticDensity_abs_moment_integrable 1).add
        poissonLogisticDensity_integrable
    simpa only [mul_add, mul_one, pow_one] using! h
  have hnearConstant :
      Integrable (fun _ : ℝ => (1 : ℝ))
        (volume.restrict (Ioc (0 : ℝ) 1)) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hnearMajor := hfrequency.mul_prod hnearConstant
  have hnearMembership :
      ∀ᵐ p : ℝ × ℝ ∂volume.prod
          (volume.restrict (Ioc (0 : ℝ) 1)),
        p.2 ∈ Ioc (0 : ℝ) 1 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_Ioc.preimage measurable_snd)).2
    exact Filter.Eventually.of_forall
      (fun _ => ae_restrict_mem measurableSet_Ioc)
  have hnear :
      Integrable F
        (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    apply hnearMajor.mono' hmeas.aestronglyMeasurable
    filter_upwards [hnearMembership] with p hp
    have hdensity : 0 < poissonLogisticDensity p.1 := by
      unfold poissonLogisticDensity
      positivity
    change
      |poissonLogisticDensity p.1 *
          lowerWallisPhaseKernel p.1 p.2| ≤
        (poissonLogisticDensity p.1 * (|p.1| + 1)) * 1
    rw [abs_mul, abs_of_pos hdensity, mul_one]
    exact mul_le_mul_of_nonneg_left
      (lowerWallisPhaseKernel_abs_le_moment p.1 hp.1)
      hdensity.le
  have hfarMajor :=
    poissonLogisticDensity_integrable.mul_prod
      lowerWallisPhaseTail_integrable
  have hfarMembership :
      ∀ᵐ p : ℝ × ℝ ∂volume.prod
          (volume.restrict (Ioi (1 : ℝ))),
        p.2 ∈ Ioi (1 : ℝ) := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_Ioi.preimage measurable_snd)).2
    exact Filter.Eventually.of_forall
      (fun _ => ae_restrict_mem measurableSet_Ioi)
  have hfar :
      Integrable F
        (volume.prod (volume.restrict (Ioi (1 : ℝ)))) := by
    apply hfarMajor.mono' hmeas.aestronglyMeasurable
    filter_upwards [hfarMembership] with p hp
    have hdensity : 0 < poissonLogisticDensity p.1 := by
      unfold poissonLogisticDensity
      positivity
    change
      |poissonLogisticDensity p.1 *
          lowerWallisPhaseKernel p.1 p.2| ≤
        poissonLogisticDensity p.1 *
          (1 / p.2 ^ 2 + Real.exp (-p.2))
    rw [abs_mul, abs_of_pos hdensity]
    exact mul_le_mul_of_nonneg_left
      (lowerWallisPhaseKernel_abs_le_tail p.1 hp.le)
      hdensity.le
  have hnearOn :
      IntegrableOn F
        ((Set.univ : Set ℝ) ×ˢ Ioc (0 : ℝ) 1)
        (volume.prod volume) := by
    change
      Integrable F
        ((volume.prod volume).restrict
          ((Set.univ : Set ℝ) ×ˢ Ioc (0 : ℝ) 1))
    rw [← Measure.prod_restrict]
    simpa only [Measure.restrict_univ] using! hnear
  have hfarOn :
      IntegrableOn F
        ((Set.univ : Set ℝ) ×ˢ Ioi (1 : ℝ))
        (volume.prod volume) := by
    change
      Integrable F
        ((volume.prod volume).restrict
          ((Set.univ : Set ℝ) ×ˢ Ioi (1 : ℝ)))
    rw [← Measure.prod_restrict]
    simpa only [Measure.restrict_univ] using! hfar
  have hsets :
      (((Set.univ : Set ℝ) ×ˢ Ioc (0 : ℝ) 1) ∪
        ((Set.univ : Set ℝ) ×ˢ Ioi (1 : ℝ))) =
          (Set.univ : Set ℝ) ×ˢ Ioi (0 : ℝ) := by
    rw [← Set.prod_union,
      Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  have hfull :
      IntegrableOn F
        ((Set.univ : Set ℝ) ×ˢ Ioi (0 : ℝ))
        (volume.prod volume) := by
    rw [← hsets]
    exact hnearOn.union hfarOn
  change
    Integrable F
      (volume.prod (volume.restrict (Ioi 0)))
  have hproduct := hfull
  change
    Integrable F
      ((volume.prod volume).restrict
        ((Set.univ : Set ℝ) ×ˢ Ioi (0 : ℝ))) at hproduct
  rw [← Measure.prod_restrict] at hproduct
  simpa only [Measure.restrict_univ] using! hproduct

private theorem integral_poissonLogistic_mul_lowerWallisPhaseKernel
    {t : ℝ} (ht : 0 < t) :
    (∫ u : ℝ,
      poissonLogisticDensity u * lowerWallisPhaseKernel u t) =
      wallisLaplaceKernel t := by
  have htne : t ≠ 0 := ht.ne'
  have hcos := poissonLogistic_cosine_integrable t
  have hfirst :
      Integrable
        (fun u : ℝ =>
          (1 - Real.exp (-t)) *
            (poissonLogisticDensity u * Real.cos (t * u))) :=
    hcos.const_mul (1 - Real.exp (-t))
  have hsecond :
      Integrable
        (fun u : ℝ =>
          (t * Real.exp (-t)) * poissonLogisticDensity u) :=
    poissonLogisticDensity_integrable.const_mul
      (t * Real.exp (-t))
  calc
    (∫ u : ℝ,
      poissonLogisticDensity u * lowerWallisPhaseKernel u t) =
      ∫ u : ℝ,
        ((1 - Real.exp (-t)) *
            (poissonLogisticDensity u * Real.cos (t * u)) -
          (t * Real.exp (-t)) * poissonLogisticDensity u) /
            t ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with u
      unfold lowerWallisPhaseKernel
      rw [mul_comm u t]
      ring
    _ =
      ((1 - Real.exp (-t)) *
          (∫ u : ℝ,
            poissonLogisticDensity u * Real.cos (t * u)) -
        (t * Real.exp (-t)) *
          (∫ u : ℝ, poissonLogisticDensity u)) /
            t ^ 2 := by
      rw [integral_div,
        integral_sub hfirst hsecond,
        integral_const_mul, integral_const_mul]
    _ =
      ((1 - Real.exp (-t)) * (t / Real.sinh t) -
        t * Real.exp (-t)) / t ^ 2 := by
      rw [poissonLogistic_cosine_transform t,
        ite_eq_right htne, integral_poissonLogisticDensity]
      ring
    _ = wallisLaplaceKernel t := by
      have hsinh : Real.sinh t ≠ 0 :=
        Real.sinh_ne_zero.mpr htne
      have hpositive : Real.exp (-t) ≠ 0 :=
        (Real.exp_pos _).ne'
      have hdiff :
          Real.exp t - Real.exp (-t) ≠ 0 := by
        intro hzero
        apply hsinh
        rw [Real.sinh_eq, hzero]
        norm_num
      have hden : 1 + Real.exp (-t) ≠ 0 := by
        positivity
      rw [Real.sinh_eq]
      have hexp : Real.exp t * Real.exp (-t) = 1 := by
        rw [← Real.exp_add]
        simp only [add_neg_cancel, Real.exp_zero]
      unfold wallisLaplaceKernel
      field_simp [htne, hpositive, hdiff, hden]; linarith [hexp]

private noncomputable def lowerWallisRegularizedPhaseKernel (a u t : ℝ) : ℝ :=
  ((1 - Real.exp (-t)) * Real.exp (-a * t) *
      Real.cos (u * t) - t * Real.exp (-t)) / t ^ 2

private theorem complexWallisPhaseKernel_re (a u t : ℝ) :
    (complexWallisPhaseKernel
      ((a : ℂ) - Complex.I * (u : ℂ)) t).re =
        lowerWallisRegularizedPhaseKernel a u t := by
  unfold complexWallisPhaseKernel lowerWallisRegularizedPhaseKernel
  rw [← Complex.ofReal_pow]
  rw [Complex.div_ofReal_re]
  simp only [neg_sub, Complex.sub_re, Complex.mul_re, Complex.one_re, Complex.exp_re,
    Complex.neg_re,
    Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, neg_zero, Real.cos_zero, mul_one,
      Complex.I_re, zero_mul,
    Complex.I_im, mul_zero, sub_self, zero_sub, neg_mul, Complex.sub_im, Complex.mul_im,
      one_mul, zero_add, sub_zero,
    Complex.one_im, Complex.exp_im, Real.sin_zero]
  ring

private theorem lowerWallisRegularizedPhaseKernel_eq_add
    (a u t : ℝ) :
    lowerWallisRegularizedPhaseKernel a u t =
      lowerWallisPhaseKernel u t +
        ((1 - Real.exp (-t)) *
          (Real.exp (-a * t) - 1) * Real.cos (u * t)) /
            t ^ 2 := by
  unfold lowerWallisRegularizedPhaseKernel lowerWallisPhaseKernel
  ring

private theorem lowerWallisRegularizedPhaseKernel_abs_le_moment
    {a : ℝ} (hazero : 0 ≤ a) (haone : a ≤ 1)
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    |lowerWallisRegularizedPhaseKernel a u t| ≤ |u| + 2 := by
  let q : ℝ := Real.exp (-t)
  let r : ℝ := Real.exp (-a * t)
  have hqpos : 0 < q := by
    try dsimp [q]
    positivity
  have hqone : q ≤ 1 := by
    try dsimp [q]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hrpos : 0 < r := by
    try dsimp [r]
    positivity
  have hrone : r ≤ 1 := by
    try dsimp [r]
    apply Real.exp_le_one_iff.mpr
    linarith [mul_nonneg hazero ht.le]
  have hqnonneg : 0 ≤ 1 - q := by linarith
  have hrnonneg : 0 ≤ 1 - r := by linarith
  have hqbound : 1 - q ≤ t := by
    try dsimp [q]
    linarith [Real.add_one_le_exp (-t)]
  have hrbound : 1 - r ≤ t := by
    have hfirst : 1 - r ≤ a * t := by
      try dsimp [r]
      linarith [Real.add_one_le_exp (-a * t)]
    have hsecond : a * t ≤ t := by
      linarith [mul_nonneg (sub_nonneg.mpr haone) ht.le]
    exact hfirst.trans hsecond
  have hsq : 0 < t ^ 2 := sq_pos_of_pos ht
  have hcorrection :
      |((1 - q) * (r - 1) * Real.cos (u * t)) /
          t ^ 2| ≤ 1 := by
    rw [abs_div, abs_of_pos hsq, abs_mul, abs_mul,
      abs_of_nonneg hqnonneg,
      abs_of_nonpos (show r - 1 ≤ 0 by linarith)]
    apply (div_le_iff₀ hsq).2
    have hcos := Real.abs_cos_le_one (u * t)
    calc
      (1 - q) * (-(r - 1)) * |Real.cos (u * t)| ≤
          (1 - q) * (1 - r) := by
        have hfactor : 0 ≤ (1 - q) * (1 - r) :=
          mul_nonneg hqnonneg hrnonneg
        linarith [mul_le_mul_of_nonneg_left hcos hfactor]
      _ ≤ t * t :=
        mul_le_mul hqbound hrbound hrnonneg ht.le
      _ = 1 * t ^ 2 := by ring
  rw [lowerWallisRegularizedPhaseKernel_eq_add]
  change
    |lowerWallisPhaseKernel u t +
      ((1 - q) * (r - 1) * Real.cos (u * t)) / t ^ 2| ≤
        |u| + 2
  calc
    |lowerWallisPhaseKernel u t +
        ((1 - q) * (r - 1) * Real.cos (u * t)) / t ^ 2| ≤
      |lowerWallisPhaseKernel u t| +
        |((1 - q) * (r - 1) * Real.cos (u * t)) /
          t ^ 2| := abs_add_le _ _
    _ ≤ (|u| + 1) + 1 :=
      add_le_add (lowerWallisPhaseKernel_abs_le_moment u ht)
        hcorrection
    _ = |u| + 2 := by ring

private theorem lowerWallisRegularizedPhaseKernel_abs_le_tail
    {a : ℝ} (hazero : 0 ≤ a)
    (u : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    |lowerWallisRegularizedPhaseKernel a u t| ≤
      1 / t ^ 2 + Real.exp (-t) := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  let q : ℝ := Real.exp (-t)
  let r : ℝ := Real.exp (-a * t)
  have hqpos : 0 < q := by
    try dsimp [q]
    positivity
  have hqone : q ≤ 1 := by
    try dsimp [q]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hrpos : 0 < r := by
    try dsimp [r]
    positivity
  have hrone : r ≤ 1 := by
    try dsimp [r]
    apply Real.exp_le_one_iff.mpr
    linarith [mul_nonneg hazero htpos.le]
  have hqnonneg : 0 ≤ 1 - q := by linarith
  have hsq : 0 < t ^ 2 := sq_pos_of_pos htpos
  have htsq : t ≤ t ^ 2 := by nlinarith
  unfold lowerWallisRegularizedPhaseKernel
  change
    |((1 - q) * r * Real.cos (u * t) - t * q) /
      t ^ 2| ≤ 1 / t ^ 2 + q
  rw [abs_div, abs_of_pos hsq]
  apply (div_le_iff₀ hsq).2
  calc
    |(1 - q) * r * Real.cos (u * t) - t * q| ≤
        |(1 - q) * r * Real.cos (u * t)| + |t * q| :=
      abs_sub _ _
    _ = (1 - q) * r * |Real.cos (u * t)| + t * q := by
      rw [abs_mul, abs_mul, abs_of_nonneg hqnonneg,
        abs_of_pos hrpos, abs_mul, abs_of_pos htpos,
        abs_of_pos hqpos]
    _ ≤ 1 + t * q := by
      have hcos := Real.abs_cos_le_one (u * t)
      have hfirst : (1 - q) * r ≤ 1 := by
        calc
          (1 - q) * r ≤ (1 - q) * 1 :=
            mul_le_mul_of_nonneg_left hrone hqnonneg
          _ ≤ 1 := by linarith
      have hfactor : 0 ≤ (1 - q) * r :=
        mul_nonneg hqnonneg hrpos.le
      linarith [mul_le_mul_of_nonneg_left hcos hfactor]
    _ ≤ 1 + q * t ^ 2 := by
      linarith [mul_nonneg hqpos.le (sub_nonneg.mpr htsq)]
    _ = (1 / t ^ 2 + q) * t ^ 2 := by
      field_simp [htpos.ne']

private noncomputable def lowerWallisRegularizedPhaseMajorant (u t : ℝ) : ℝ :=
  if t ≤ 1 then |u| + 2 else 1 / t ^ 2 + Real.exp (-t)

private theorem lowerWallisRegularizedPhaseMajorant_integrable (u : ℝ) :
    IntegrableOn (lowerWallisRegularizedPhaseMajorant u) (Ioi 0) := by
  have hnear :
      IntegrableOn (lowerWallisRegularizedPhaseMajorant u)
        (Ioc (0 : ℝ) 1) := by
    have hconstant :
        IntegrableOn (fun _ : ℝ => |u| + 2)
          (Ioc (0 : ℝ) 1) :=
      integrableOn_const measure_Ioc_lt_top.ne
    apply hconstant.congr_fun _ measurableSet_Ioc
    intro t ht
    simp only [lowerWallisRegularizedPhaseMajorant, ht.2, ↓reduceIte]
  have hfar :
      IntegrableOn (lowerWallisRegularizedPhaseMajorant u)
        (Ioi (1 : ℝ)) := by
    apply lowerWallisPhaseTail_integrable.congr_fun _
      measurableSet_Ioi
    intro t ht
    simp only [one_div, lowerWallisRegularizedPhaseMajorant, not_le.mpr (show 1 < t from ht),
      ↓reduceIte]
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact hnear.union hfar

private theorem tendsto_integral_lowerWallisRegularizedPhaseKernel
    (u : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ t : ℝ in Ioi 0,
          lowerWallisRegularizedPhaseKernel
            (1 / ((n : ℝ) + 1)) u t)
      atTop
      (𝓝 (∫ t : ℝ in Ioi 0, lowerWallisPhaseKernel u t)) := by
  apply tendsto_integral_of_dominated_convergence
    (lowerWallisRegularizedPhaseMajorant u)
  · intro n
    exact
      (show Measurable
        (fun t : ℝ =>
          lowerWallisRegularizedPhaseKernel
            (1 / ((n : ℝ) + 1)) u t) by
        unfold lowerWallisRegularizedPhaseKernel
        fun_prop).aestronglyMeasurable
  · exact lowerWallisRegularizedPhaseMajorant_integrable u
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with t ht
    have hapos : 0 < 1 / ((n : ℝ) + 1) := by
      positivity
    have haone : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (show 0 < (n : ℝ) + 1 by positivity)).2
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    rw [Real.norm_eq_abs]
    by_cases htone : t ≤ 1
    · simp only [lowerWallisRegularizedPhaseMajorant,
        ite_eq_left htone]
      exact lowerWallisRegularizedPhaseKernel_abs_le_moment
        hapos.le haone u ht
    · simp only [lowerWallisRegularizedPhaseMajorant,
        ite_eq_right htone]
      exact lowerWallisRegularizedPhaseKernel_abs_le_tail
        hapos.le u (le_of_not_ge htone)
  · filter_upwards [] with t
    have hcontinuous :
        Continuous
          (fun a : ℝ => lowerWallisRegularizedPhaseKernel a u t) := by
      unfold lowerWallisRegularizedPhaseKernel
      fun_prop
    have hzero :
        lowerWallisRegularizedPhaseKernel 0 u t =
          lowerWallisPhaseKernel u t := by
      unfold lowerWallisRegularizedPhaseKernel
        lowerWallisPhaseKernel
      simp only [neg_zero, zero_mul, Real.exp_zero, mul_one]
    rw [← hzero]
    exact hcontinuous.continuousAt.tendsto.comp
      tendsto_one_div_add_atTop_nhds_zero_nat

private theorem integral_lowerWallisRegularizedPhaseKernel
    {a : ℝ} (ha : 0 < a) (u : ℝ) :
    (∫ t : ℝ in Ioi 0,
      lowerWallisRegularizedPhaseKernel a u t) =
      (1 + ((a : ℂ) - Complex.I * (u : ℂ)) *
        Complex.log ((a : ℂ) - Complex.I * (u : ℂ)) -
        (((a : ℂ) - Complex.I * (u : ℂ)) + 1) *
          Complex.log (((a : ℂ) - Complex.I * (u : ℂ)) + 1)).re := by
  let z : ℂ := (a : ℂ) - Complex.I * (u : ℂ)
  have hz : 0 < z.re := by
    try dsimp [z]
    simpa only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im,
      Complex.ofReal_im,
      mul_zero, sub_self, sub_zero] using! ha
  calc
    (∫ t : ℝ in Ioi 0,
      lowerWallisRegularizedPhaseKernel a u t) =
        ∫ t : ℝ in Ioi 0,
          (complexWallisPhaseKernel z t).re := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      exact (complexWallisPhaseKernel_re a u t).symm
    _ = (∫ t : ℝ in Ioi 0,
          complexWallisPhaseKernel z t).re := by
      exact integral_re (complexWallisPhaseKernel_integrable hz)
    _ = (1 + z * Complex.log z -
          (z + 1) * Complex.log (z + 1)).re := by
      rw [integral_complexWallisPhaseKernel hz]

private theorem lowerWallis_arg_one_sub_I_mul (u : ℝ) :
    Complex.arg (1 - Complex.I * (u : ℂ)) =
      -Real.arctan u := by
  let z : ℂ := 1 - Complex.I * (u : ℂ)
  have hre : 0 < z.re := by
    try dsimp [z]
    simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im,
      Complex.ofReal_im,
      mul_zero, sub_self, sub_zero, zero_lt_one]
  have hrange : |Complex.arg z| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have htan : Real.tan (Complex.arg z) = -u := by
    simp only [Complex.tan_arg, Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.I_re,
      Complex.ofReal_im,
      mul_zero, Complex.I_im, Complex.ofReal_re, one_mul, zero_add, zero_sub, Complex.sub_re,
        Complex.one_re,
      Complex.mul_re, zero_mul, sub_self, sub_zero, div_one, z]
  calc
    Complex.arg (1 - Complex.I * (u : ℂ)) =
        Real.arctan (Real.tan (Complex.arg z)) := by
      change Complex.arg z =
        Real.arctan (Real.tan (Complex.arg z))
      exact (Real.arctan_tan
        (abs_lt.mp hrange).1 (abs_lt.mp hrange).2).symm
    _ = Real.arctan (-u) := by rw [htan]
    _ = -Real.arctan u := Real.arctan_neg u

private theorem lowerWallis_imaginary_log_mul_re (u : ℝ) :
    ((-Complex.I * (u : ℂ)) *
      Complex.log (-Complex.I * (u : ℂ))).re =
        -Real.pi * |u| / 2 := by
  by_cases hzero : u = 0
  · subst u
    simp only [Complex.ofReal_zero, mul_zero, Complex.log_zero, Complex.zero_re, abs_zero, zero_div]
  rcases lt_or_gt_of_ne hzero with hnegative | hpositive
  · have harg :
        Complex.arg (-Complex.I * (u : ℂ)) =
          Real.pi / 2 := by
      apply Complex.arg_eq_pi_div_two_iff.mpr
      constructor
      · simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
        zero_mul, Complex.I_im,
          Complex.ofReal_im, mul_zero, sub_self, neg_zero]
      · simpa only [neg_mul, Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.ofReal_im,
        mul_zero, Complex.I_im,
          Complex.ofReal_re, one_mul, zero_add, Left.neg_pos_iff] using! (neg_pos.mpr hnegative)
    rw [Complex.mul_re, Complex.log_im, harg,
      abs_of_neg hnegative]
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
      zero_mul, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_self, neg_zero, Complex.neg_im, Complex.mul_im, one_mul,
        zero_add, sub_neg_eq_add,
      mul_neg, neg_neg]
    ring
  · have harg :
        Complex.arg (-Complex.I * (u : ℂ)) =
          -(Real.pi / 2) := by
      apply Complex.arg_eq_neg_pi_div_two_iff.mpr
      constructor
      · simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
        zero_mul, Complex.I_im,
          Complex.ofReal_im, mul_zero, sub_self, neg_zero]
      · simpa only [neg_mul, Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.ofReal_im,
        mul_zero, Complex.I_im,
          Complex.ofReal_re, one_mul, zero_add, Left.neg_neg_iff] using! (neg_neg_of_pos hpositive)
    rw [Complex.mul_re, Complex.log_im, harg,
      abs_of_pos hpositive]
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
      zero_mul, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_self, neg_zero, Complex.neg_im, Complex.mul_im, one_mul,
        zero_add, mul_neg,
      neg_neg, zero_sub]
    ring

private theorem lowerWallis_norm_one_sub_I_mul (u : ℝ) :
    ‖1 - Complex.I * (u : ℂ)‖ =
      Real.sqrt (1 + u ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
    zero_mul,
    Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, sub_zero, mul_one, Complex.sub_im,
      Complex.one_im,
    Complex.mul_im, one_mul, zero_add, zero_sub, mul_neg, neg_mul, neg_neg, add_right_inj]
  ring

private theorem lowerWallis_shifted_log_mul_re (u : ℝ) :
    ((1 - Complex.I * (u : ℂ)) *
      Complex.log (1 - Complex.I * (u : ℂ))).re =
        Real.log (1 + u ^ 2) / 2 -
          u * Real.arctan u := by
  rw [Complex.mul_re, Complex.log_re, Complex.log_im,
    lowerWallis_norm_one_sub_I_mul,
    lowerWallis_arg_one_sub_I_mul,
    Real.log_sqrt (show 0 ≤ 1 + u ^ 2 by positivity)]
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
    zero_mul,
    Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, sub_zero, one_mul, Complex.sub_im,
      Complex.one_im,
    Complex.mul_im, zero_add, zero_sub, mul_neg, neg_mul, neg_neg]

private theorem lowerWallis_abs_mul_arctan_abs (u : ℝ) :
    |u| * Real.arctan |u| = u * Real.arctan u := by
  by_cases hu : 0 ≤ u
  · simp only [abs_of_nonneg hu]
  · have hnegative : u < 0 := lt_of_not_ge hu
    rw [abs_of_neg hnegative, Real.arctan_neg]
    ring

private theorem lowerWallis_complexEndpointPhase_re (u : ℝ) :
    (1 + (-Complex.I * (u : ℂ)) *
      Complex.log (-Complex.I * (u : ℂ)) -
      ((-Complex.I * (u : ℂ)) + 1) *
        Complex.log ((-Complex.I * (u : ℂ)) + 1)).re =
          1 + lowerEndpointPhase (2 * u) := by
  have hshift :
      (-Complex.I * (u : ℂ)) + 1 =
        1 - Complex.I * (u : ℂ) := by
    ring
  rw [hshift, Complex.sub_re, Complex.add_re,
    lowerWallis_imaginary_log_mul_re,
    lowerWallis_shifted_log_mul_re]
  simp only [Complex.one_re]
  unfold lowerEndpointPhase
  have habs : |(2 : ℝ) * u| = 2 * |u| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [habs]
  have hquad : 1 + (2 * u) ^ 2 / 4 = 1 + u ^ 2 := by
    ring
  rw [hquad]
  have harg : 2 * |u| / 2 = |u| := by ring
  rw [harg, lowerWallis_abs_mul_arctan_abs]
  ring

private noncomputable def lowerWallisComplexLogPhase (z : ℂ) : ℝ :=
  (1 + z * Complex.log z -
    (z + 1) * Complex.log (z + 1)).re

private theorem lowerWallisComplexLogPhase_ofReal
    {a : ℝ} (ha : 0 ≤ a) :
    lowerWallisComplexLogPhase (a : ℂ) =
      1 + a * Real.log a -
        (a + 1) * Real.log (a + 1) := by
  have hcast : (a : ℂ) + 1 = ((a + 1 : ℝ) : ℂ) := by
    push_cast
    rfl
  have hnorm : ‖(a : ℂ) + 1‖ = a + 1 := by
    rw [hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ a + 1 by linarith)]
  unfold lowerWallisComplexLogPhase
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.log_re,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha, Complex.ofReal_im, zero_mul,
      sub_zero, hnorm, Complex.add_im,
    Complex.one_im, add_zero]

private theorem tendsto_lowerWallisComplexLogPhase_regularized (u : ℝ) :
    Tendsto
      (fun n : ℕ =>
        lowerWallisComplexLogPhase
          (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) -
            Complex.I * (u : ℂ)))
      atTop (𝓝 (1 + lowerEndpointPhase (2 * u))) := by
  have hparameter :
      Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ))
        atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  by_cases hzero : u = 0
  · subst u
    have hreal :
        Continuous
          (fun a : ℝ =>
            1 + a * Real.log a -
              (a + 1) * Real.log (a + 1)) := by
      have hshift : Continuous (fun a : ℝ => a + 1) := by
        fun_prop
      exact
        (continuous_const.add Real.continuous_mul_log).sub
          (Real.continuous_mul_log.comp hshift)
    have hlimit := hreal.continuousAt.tendsto.comp hparameter
    have hcomputed :
        Tendsto
          (fun n : ℕ =>
            lowerWallisComplexLogPhase
              (((1 / ((n : ℝ) + 1) : ℝ) : ℂ)))
          atTop (𝓝 (1 : ℝ)) := by
      have hrealLimit :
          Tendsto
            (fun n : ℕ =>
              1 + (1 / ((n : ℝ) + 1) : ℝ) *
                  Real.log (1 / ((n : ℝ) + 1)) -
                ((1 / ((n : ℝ) + 1) : ℝ) + 1) *
                  Real.log ((1 / ((n : ℝ) + 1) : ℝ) + 1))
            atTop (𝓝 (1 : ℝ)) := by
        simpa only [Function.comp_apply, zero_mul, mul_zero,
          zero_add, add_zero, one_mul, Real.log_one,
          sub_zero] using! hlimit
      apply hrealLimit.congr'
      filter_upwards [] with n
      exact
        (lowerWallisComplexLogPhase_ofReal
          (show 0 ≤ (1 / ((n : ℝ) + 1) : ℝ) by
            positivity)).symm
    simpa only [one_div, Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_one,
      Complex.ofReal_zero, mul_zero, sub_zero, lowerEndpointPhase, abs_zero, zero_div, ne_eq,
        OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, add_zero, Real.log_one, sub_self,
        Real.arctan_zero] using! hcomputed
  · let z : ℂ := -Complex.I * (u : ℂ)
    have hcast :
        Tendsto
          (fun n : ℕ =>
            ((1 / ((n : ℝ) + 1) : ℝ) : ℂ))
          atTop (𝓝 (0 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hparameter
    have hz :
        Tendsto
          (fun n : ℕ =>
            (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) -
              Complex.I * (u : ℂ)))
          atTop (𝓝 z) := by
      try dsimp [z]
      simpa only [one_div, Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast,
        Complex.ofReal_one,
        neg_mul, zero_sub] using!
        hcast.sub (tendsto_const_nhds
          (x := Complex.I * (u : ℂ)))
    have hslit : z ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      right
      try dsimp [z]
      simpa only [neg_mul, Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.ofReal_im,
        mul_zero, Complex.I_im,
        Complex.ofReal_re, one_mul, zero_add, neg_eq_zero] using! hzero
    have hshift : z + 1 ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      try dsimp [z]
      simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
        zero_mul, Complex.I_im,
        Complex.ofReal_im, mul_zero, sub_self, neg_zero, zero_add, zero_lt_one]
    let w : ℕ → ℂ := fun n =>
      (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) -
        Complex.I * (u : ℂ))
    have hw : Tendsto w atTop (𝓝 z) := by
      exact hz
    have hzlog := hw.clog hslit
    have htranslate := hw.add_const (1 : ℂ)
    have htranslatedLog := htranslate.clog hshift
    have hcomplex :
        Tendsto
          (fun n : ℕ =>
            (1 : ℂ) + w n * Complex.log (w n) -
              (w n + 1) * Complex.log (w n + 1))
          atTop
          (𝓝 ((1 : ℂ) + z * Complex.log z -
            (z + 1) * Complex.log (z + 1))) := by
      exact
        ((tendsto_const_nhds.add (hw.mul hzlog)).sub
          (htranslate.mul htranslatedLog))
    have hreal :
        Tendsto
          (fun n : ℕ => lowerWallisComplexLogPhase (w n))
          atTop (𝓝 (lowerWallisComplexLogPhase z)) := by
      simpa only [lowerWallisComplexLogPhase,
        Function.comp_apply] using!
        (Complex.continuous_re.continuousAt.tendsto.comp hcomplex)
    have hendpoint :
        lowerWallisComplexLogPhase z =
          1 + lowerEndpointPhase (2 * u) := by
      exact lowerWallis_complexEndpointPhase_re u
    rw [hendpoint] at hreal
    exact hreal

private theorem integral_lowerWallisPhaseKernel (u : ℝ) :
    (∫ t : ℝ in Ioi 0, lowerWallisPhaseKernel u t) =
      1 + lowerEndpointPhase (2 * u) := by
  have hdominated :=
    tendsto_integral_lowerWallisRegularizedPhaseKernel u
  have hcomputed :
      Tendsto
        (fun n : ℕ =>
          ∫ t : ℝ in Ioi 0,
            lowerWallisRegularizedPhaseKernel
              (1 / ((n : ℝ) + 1)) u t)
        atTop (𝓝 (1 + lowerEndpointPhase (2 * u))) := by
    have hidentity (n : ℕ) :
        (∫ t : ℝ in Ioi 0,
          lowerWallisRegularizedPhaseKernel
            (1 / ((n : ℝ) + 1)) u t) =
          lowerWallisComplexLogPhase
            (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) -
              Complex.I * (u : ℂ)) := by
      exact integral_lowerWallisRegularizedPhaseKernel
        (by positivity) u
    simp_rw [hidentity]
    exact tendsto_lowerWallisComplexLogPhase_regularized u
  exact tendsto_nhds_unique hdominated hcomputed

private theorem integral_poissonLogistic_one_add_lowerEndpointPhase :
    (∫ u : ℝ,
      poissonLogisticDensity u *
        (1 + lowerEndpointPhase (2 * u))) =
          Real.log (Real.pi / 2) := by
  calc
    (∫ u : ℝ,
      poissonLogisticDensity u *
        (1 + lowerEndpointPhase (2 * u))) =
        ∫ u : ℝ, ∫ t : ℝ in Ioi 0,
          poissonLogisticDensity u *
            lowerWallisPhaseKernel u t := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [integral_const_mul, integral_lowerWallisPhaseKernel]
    _ = ∫ t : ℝ in Ioi 0, ∫ u : ℝ,
          poissonLogisticDensity u *
            lowerWallisPhaseKernel u t := by
      exact integral_integral_swap
        poissonLogistic_lowerWallisPhase_product_integrable
    _ = ∫ t : ℝ in Ioi 0, wallisLaplaceKernel t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact integral_poissonLogistic_mul_lowerWallisPhaseKernel ht
    _ = Real.log (Real.pi / 2) :=
      integral_wallisLaplaceKernel

private theorem poissonLogistic_lowerEndpointPhase_integrable :
    Integrable
      (fun u : ℝ =>
        poissonLogisticDensity u *
          lowerEndpointPhase (2 * u)) := by
  have hproduct :=
    poissonLogistic_lowerWallisPhase_product_integrable.integral_prod_left
  have hone :
      Integrable
        (fun u : ℝ =>
          poissonLogisticDensity u *
            (1 + lowerEndpointPhase (2 * u))) := by
    apply hproduct.congr
    filter_upwards [] with u
    rw [integral_const_mul, integral_lowerWallisPhaseKernel]
  have hdifference := hone.sub poissonLogisticDensity_integrable
  apply hdifference.congr
  filter_upwards [] with u
  change
    poissonLogisticDensity u *
        (1 + lowerEndpointPhase (2 * u)) -
      poissonLogisticDensity u =
        poissonLogisticDensity u * lowerEndpointPhase (2 * u)
  ring

private theorem integral_poissonLogistic_lowerEndpointPhase :
    (∫ u : ℝ,
      poissonLogisticDensity u *
        lowerEndpointPhase (2 * u)) =
          Real.log (Real.pi / 2) - 1 := by
  have hsplit :
      (∫ u : ℝ,
        poissonLogisticDensity u *
          (1 + lowerEndpointPhase (2 * u))) =
        (∫ u : ℝ, poissonLogisticDensity u) +
          ∫ u : ℝ,
            poissonLogisticDensity u *
              lowerEndpointPhase (2 * u) := by
    calc
      (∫ u : ℝ,
        poissonLogisticDensity u *
          (1 + lowerEndpointPhase (2 * u))) =
          ∫ u : ℝ,
            poissonLogisticDensity u +
              poissonLogisticDensity u *
                lowerEndpointPhase (2 * u) := by
        apply integral_congr_ae
        filter_upwards [] with u
        ring
      _ = (∫ u : ℝ, poissonLogisticDensity u) +
            ∫ u : ℝ,
              poissonLogisticDensity u *
                lowerEndpointPhase (2 * u) :=
        integral_add poissonLogisticDensity_integrable
          poissonLogistic_lowerEndpointPhase_integrable
  have hwallis :=
    integral_poissonLogistic_one_add_lowerEndpointPhase
  rw [hsplit, integral_poissonLogisticDensity] at hwallis
  linarith

private theorem limitingPoissonEndpointExpectation_eq_log_pi_div_two_sub_one :
    limitingPoissonEndpointExpectation =
      Real.log (Real.pi / 2) - 1 := by
  have hscale :
      (∫ u : ℝ,
        limitingStripPoissonDensity (2 * u) *
          lowerEndpointPhase (2 * u)) =
        (1 / 2 : ℝ) * limitingPoissonEndpointExpectation := by
    unfold limitingPoissonEndpointExpectation
    have h := Measure.integral_comp_mul_left
      (fun T : ℝ =>
        limitingStripPoissonDensity T * lowerEndpointPhase T)
      (2 : ℝ)
    simpa only [one_div, abs_of_pos (show (0 : ℝ) < (2 : ℝ)⁻¹ by positivity), smul_eq_mul] using! h
  have hlogistic :
      (∫ u : ℝ,
        poissonLogisticDensity u *
          lowerEndpointPhase (2 * u)) =
        2 * (∫ u : ℝ,
          limitingStripPoissonDensity (2 * u) *
            lowerEndpointPhase (2 * u)) := by
    calc
      (∫ u : ℝ,
        poissonLogisticDensity u *
          lowerEndpointPhase (2 * u)) =
        ∫ u : ℝ,
          2 * (limitingStripPoissonDensity (2 * u) *
            lowerEndpointPhase (2 * u)) := by
        apply integral_congr_ae
        filter_upwards [] with u
        rw [poissonLogisticDensity_eq_limitingStripPoissonDensity]
        ring
      _ = 2 * (∫ u : ℝ,
          limitingStripPoissonDensity (2 * u) *
            lowerEndpointPhase (2 * u)) := by
        rw [integral_const_mul]
  have hphase := integral_poissonLogistic_lowerEndpointPhase
  linarith

private theorem lowerPoissonEndpointSharpCoefficient_eq
    {c : ℝ} (hc : 0 < c) :
    Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) +
        limitingPoissonEndpointExpectation =
      Real.log (Real.pi ^ 2 * c ^ 2) := by
  rw [limitingPoissonEndpointExpectation_eq_log_pi_div_two_sub_one]
  have hleft : 2 * Real.pi * Real.exp 1 * c ^ 2 ≠ 0 := by
    positivity
  have hright : Real.pi / 2 ≠ 0 := by
    positivity
  have hfactor :
      (2 * Real.pi * Real.exp 1 * c ^ 2) *
          (Real.pi / 2) =
        (Real.pi ^ 2 * c ^ 2) * Real.exp 1 := by
    ring
  calc
    Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) +
        (Real.log (Real.pi / 2) - 1) =
      Real.log
        ((2 * Real.pi * Real.exp 1 * c ^ 2) *
          (Real.pi / 2)) - 1 := by
        rw [Real.log_mul hleft hright]
        ring
    _ = Real.log (Real.pi ^ 2 * c ^ 2) := by
      rw [hfactor,
        Real.log_mul
          (show Real.pi ^ 2 * c ^ 2 ≠ 0 by positivity)
          (show Real.exp (1 : ℝ) ≠ 0 by positivity),
        Real.log_exp]
      ring

private theorem lowerPoissonEndpointSharpCoefficient_neg
    {c : ℝ} (hc : 0 < c)
    (hsharp : c < Real.pi⁻¹) :
    Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) +
      limitingPoissonEndpointExpectation < 0 := by
  rw [lowerPoissonEndpointSharpCoefficient_eq hc]
  have hproduct : Real.pi * c < 1 := by
    have hdiv : c < 1 / Real.pi := by
      simpa only [one_div] using! hsharp
    have h := (lt_div_iff₀ Real.pi_pos).mp hdiv
    linarith
  have hpositive : 0 < Real.pi * c :=
    mul_pos Real.pi_pos hc
  have hbelow : Real.pi ^ 2 * c ^ 2 < 1 := by
    have hfactor :
        0 < (1 - Real.pi * c) *
          (1 + Real.pi * c) :=
      mul_pos (sub_pos.mpr hproduct) (by linarith)
    linarith
  exact Real.log_neg (by positivity) hbelow

private theorem tendsto_lowerPoissonEndpointSharpCoefficient
    {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun σ : ℝ =>
        Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) +
          lowerPoissonEndpointExpectation σ)
      (𝓝[<] 1)
      (𝓝 (Real.log (Real.pi ^ 2 * c ^ 2))) := by
  rw [← lowerPoissonEndpointSharpCoefficient_eq hc]
  exact tendsto_const_nhds.add
    tendsto_lowerPoissonEndpointExpectation

private theorem eventually_lowerPoissonEndpointSharpCoefficient_neg
    {c : ℝ} (hc : 0 < c)
    (hsharp : c < Real.pi⁻¹) :
    ∀ᶠ σ : ℝ in 𝓝[<] 1,
      Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) +
        lowerPoissonEndpointExpectation σ < 0 := by
  have hlimit := tendsto_lowerPoissonEndpointSharpCoefficient hc
  have hnegative : Real.log (Real.pi ^ 2 * c ^ 2) < 0 := by
    rw [← lowerPoissonEndpointSharpCoefficient_eq hc]
    exact lowerPoissonEndpointSharpCoefficient_neg hc hsharp
  exact hlimit (Iio_mem_nhds hnegative)

end

section

open Filter MeasureTheory Set
open scoped Topology

private theorem saddle_one_add_abs_cube_le (T : ℝ) :
    (1 + |T|) ^ 3 ≤ 4 * (1 + |T| ^ 3) := by
  have hfactor : 0 ≤
      (|T| - 1) ^ 2 * (|T| + 1) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  linarith

private theorem plusPolynomial_imaginary_norm_ge_beta
    {ε u : ℝ} (hε : 0 < ε) (hu : -1 ≤ u) :
    (ε / 4) ≤ ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
  have hb : 0 < (ε / 4) := div_pos hε four_pos
  have hterm : 0 ≤ (1 - u) ^ 2 * (1 + u) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hvalue : 0 < (ε / 4) + (1 - u) ^ 2 * (1 + u) :=
    add_pos_of_pos_of_nonneg hb hterm
  rw [plusPolynomial_imaginary, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hvalue]
  linarith

private theorem plusPolynomial_imaginary_cubic_growth_le
    {ε u : ℝ} (hε : 0 < ε) (hu : -1 ≤ u) :
    (1 + |u|) ^ 3 ≤
      (27 / (ε / 4) + 9) *
        ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
  have hb : 0 < (ε / 4) := div_pos hε four_pos
  have hnorm :
      (ε / 4) ≤ ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ :=
    plusPolynomial_imaginary_norm_ge_beta hε hu
  by_cases hbounded : u ≤ 2
  · have habs : |u| ≤ 2 := by
      exact (abs_le).mpr ⟨by linarith, hbounded⟩
    have hcube : (1 + |u|) ^ 3 ≤ 27 := by
      have hbase : 1 + |u| ≤ (3 : ℝ) := by linarith
      have hpow := pow_le_pow_left₀
        (show 0 ≤ 1 + |u| by positivity) hbase 3
      norm_num at hpow ⊢
      exact hpow
    calc
      (1 + |u|) ^ 3 ≤ 27 := hcube
      _ = (27 / (ε / 4)) * (ε / 4) := by
        field_simp [hb.ne']
      _ ≤ (27 / (ε / 4)) *
          ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ ≤ (27 / (ε / 4) + 9) *
          ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
        have hnonnegative :=
          norm_nonneg (plusPolynomial ε (Complex.I * (u : ℂ)))
        linarith
  · have hlarge : 2 < u := lt_of_not_ge hbounded
    have habs : |u| = u := abs_of_pos (by linarith)
    have hvalue :
        ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ =
          (ε / 4) + (1 - u) ^ 2 * (1 + u) := by
      rw [plusPolynomial_imaginary, Complex.norm_real,
        Real.norm_eq_abs]
      apply abs_of_pos
      exact add_pos_of_pos_of_nonneg hb
        (mul_nonneg (sq_nonneg _) (by linarith))
    have hsq :
        (1 + u) ^ 2 ≤ 9 * (1 - u) ^ 2 := by
      have hfactor : 0 ≤ (2 * u - 1) * (u - 2) :=
        mul_nonneg (by linarith) (by linarith)
      linarith
    have hcube :
        (1 + u) ^ 3 ≤
          9 * ((1 - u) ^ 2 * (1 + u)) := by
      have hproduct := mul_le_mul_of_nonneg_right
        hsq (show 0 ≤ 1 + u by linarith)
      linarith
    rw [habs]
    calc
      (1 + u) ^ 3 ≤
          9 * ((1 - u) ^ 2 * (1 + u)) := hcube
      _ ≤ 9 * ‖plusPolynomial ε
          (Complex.I * (u : ℂ))‖ := by
        rw [hvalue]
        linarith
      _ ≤ (27 / (ε / 4) + 9) *
          ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
        have hnonnegative :=
          norm_nonneg (plusPolynomial ε (Complex.I * (u : ℂ)))
        have hcoefficient : 0 ≤ 27 / (ε / 4) := by
          positivity
        linarith [mul_nonneg hcoefficient hnonnegative]

private theorem minusPolynomial_imaginary_norm_ge_three_beta
    {ε u : ℝ} (hε : 0 < ε)
    (hu : 1 + ε / 4 ≤ u) :
    3 * (ε / 4) ≤
      ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
  have hb : 0 < (ε / 4) := div_pos hε four_pos
  have hone : 1 ≤ u := by linarith
  have hbeta : (ε / 4) ≤ u - 1 := by
    linarith
  have hsquare : (4 : ℝ) ≤ (1 + u) ^ 2 := by
    linarith [sq_nonneg (u - 1)]
  have hproduct :
      4 * (ε / 4) ≤ (u - 1) * (1 + u) ^ 2 := by
    calc
      4 * (ε / 4) = (ε / 4) * 4 := by ring
      _ ≤ (u - 1) * (1 + u) ^ 2 :=
        mul_le_mul hbeta hsquare (by norm_num) (by linarith)
  have hnegative := minusPolynomial_imaginary_re_neg hε hu
  rw [minusPolynomial_imaginary, Complex.norm_real,
    Real.norm_eq_abs]
  have harg : (ε / 4) + (1 - u) * (1 + u) ^ 2 < 0 := by
    rw [minusPolynomial_imaginary, Complex.ofReal_re]
      at hnegative
    exact hnegative
  rw [abs_of_neg harg]
  linarith

private theorem minusPolynomial_imaginary_cubic_growth_le
    {ε u : ℝ} (hε : 0 < ε)
    (hu : 1 + ε / 4 ≤ u) :
    (1 + |u|) ^ 3 ≤
      (9 / (ε / 4) + 6) *
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
  have hb : 0 < (ε / 4) := div_pos hε four_pos
  have hone : 1 ≤ u := by linarith
  have hbeta : (ε / 4) ≤ u - 1 := by
    linarith
  have habs : |u| = u := abs_of_pos (by linarith)
  have hnorm := minusPolynomial_imaginary_norm_ge_three_beta
    hε hu
  by_cases hbounded : u ≤ 2
  · have hcube : (1 + |u|) ^ 3 ≤ 27 := by
      have hbase : 1 + |u| ≤ (3 : ℝ) := by
        rw [habs]
        linarith
      have hpow := pow_le_pow_left₀
        (show 0 ≤ 1 + |u| by positivity) hbase 3
      norm_num at hpow ⊢
      exact hpow
    calc
      (1 + |u|) ^ 3 ≤ 27 := hcube
      _ = (9 / (ε / 4)) * (3 * (ε / 4)) := by
        field_simp [hb.ne']; norm_num
      _ ≤ (9 / (ε / 4)) *
          ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ ≤ (9 / (ε / 4) + 6) *
          ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
        have hnonnegative :=
          norm_nonneg (minusPolynomial ε
            (Complex.I * (u : ℂ)))
        linarith
  · have hlarge : 2 < u := lt_of_not_ge hbounded
    have hnegative := minusPolynomial_imaginary_re_neg hε hu
    have hvalue :
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ =
          (u - 1) * (1 + u) ^ 2 - (ε / 4) := by
      rw [minusPolynomial_imaginary, Complex.norm_real,
        Real.norm_eq_abs]
      have harg : (ε / 4) + (1 - u) * (1 + u) ^ 2 < 0 := by
        rw [minusPolynomial_imaginary, Complex.ofReal_re]
          at hnegative
        exact hnegative
      rw [abs_of_neg harg]
      ring
    have hsquare : (4 : ℝ) ≤ (1 + u) ^ 2 := by
      linarith [sq_nonneg (u - 1)]
    have hterm :
        2 * (ε / 4) ≤ (u - 1) * (1 + u) ^ 2 := by
      calc
        2 * (ε / 4) ≤ 4 * (ε / 4) := by linarith
        _ = (ε / 4) * 4 := by ring
        _ ≤ (u - 1) * (1 + u) ^ 2 :=
          mul_le_mul hbeta hsquare (by norm_num) (by linarith)
    have hlinear : 1 + u ≤ 3 * (u - 1) := by
      linarith
    have hcubic :
        (1 + u) ^ 3 ≤
          3 * ((u - 1) * (1 + u) ^ 2) := by
      have hproduct :=
        mul_le_mul_of_nonneg_right hlinear (sq_nonneg (1 + u))
      linarith
    rw [habs]
    calc
      (1 + u) ^ 3 ≤
          3 * ((u - 1) * (1 + u) ^ 2) := hcubic
      _ ≤ 6 * ‖minusPolynomial ε
          (Complex.I * (u : ℂ))‖ := by
        rw [hvalue]
        linarith
      _ ≤ (9 / (ε / 4) + 6) *
          ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
        have hnonnegative :=
          norm_nonneg (minusPolynomial ε
            (Complex.I * (u : ℂ)))
        have hcoefficient : 0 ≤ 9 / (ε / 4) := by
          positivity
        linarith [mul_nonneg hcoefficient hnonnegative]

private theorem saddle_complex_frequency_norm_le (T u : ℝ) :
    ‖(T : ℂ) + Complex.I * (u : ℂ)‖ ≤ |T| + |u| := by
  calc
    ‖(T : ℂ) + Complex.I * (u : ℂ)‖ ≤
        ‖(T : ℂ)‖ + ‖Complex.I * (u : ℂ)‖ :=
      norm_add_le _ _
    _ = |T| + |u| := by
      simp only [Complex.norm_real, Real.norm_eq_abs, Complex.norm_mul, Complex.norm_I, one_mul]

private theorem exists_plusPolynomial_uniform_norm_ratio
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : ℝ, -1 ≤ u → ∀ T : ℝ,
        ‖plusPolynomial ε
            ((T : ℂ) + Complex.I * (u : ℂ))‖ /
          ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
            C * (1 + |T| ^ 3) := by
  have hb : 0 < (ε / 4) := div_pos hε four_pos
  refine ⟨4 * (1 + (ε / 4)) * (27 / (ε / 4) + 9),
    by positivity, ?_⟩
  intro u hu T
  let z : ℂ := (T : ℂ) + Complex.I * (u : ℂ)
  let D : ℝ := ‖plusPolynomial ε (Complex.I * (u : ℂ))‖
  have hD : 0 < D :=
    lt_of_lt_of_le hb (plusPolynomial_imaginary_norm_ge_beta hε hu)
  have htriangle :
      1 + ‖z‖ ≤ (1 + |T|) * (1 + |u|) := by
    have hz := saddle_complex_frequency_norm_le T u
    change ‖z‖ ≤ |T| + |u| at hz
    linarith [mul_nonneg (abs_nonneg T) (abs_nonneg u)]
  have hpower :
      (1 + ‖z‖) ^ 3 ≤
        ((1 + |T|) * (1 + |u|)) ^ 3 :=
    pow_le_pow_left₀ (by positivity) htriangle 3
  have hbase := norm_plusPolynomial_le ε z
  rw [abs_of_pos hb] at hbase
  have hfrequency := saddle_one_add_abs_cube_le T
  have hheight := plusPolynomial_imaginary_cubic_growth_le
    hε hu
  change ‖plusPolynomial ε z‖ / D ≤
    (4 * (1 + (ε / 4)) * (27 / (ε / 4) + 9)) *
      (1 + |T| ^ 3)
  apply (div_le_iff₀ hD).2
  calc
    ‖plusPolynomial ε z‖ ≤
        (1 + (ε / 4)) * (1 + ‖z‖) ^ 3 := hbase
    _ ≤ (1 + (ε / 4)) *
        ((1 + |T|) * (1 + |u|)) ^ 3 := by
      gcongr
    _ = (1 + (ε / 4)) * (1 + |T|) ^ 3 *
        (1 + |u|) ^ 3 := by
      ring
    _ ≤ (1 + (ε / 4)) *
        (4 * (1 + |T| ^ 3)) *
          ((27 / (ε / 4) + 9) * D) := by
      gcongr
    _ = ((4 * (1 + (ε / 4)) * (27 / (ε / 4) + 9)) *
        (1 + |T| ^ 3)) * D := by
      ring

private theorem exists_minusPolynomial_uniform_norm_ratio
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : ℝ, 1 + ε / 4 ≤ u → ∀ T : ℝ,
        ‖minusPolynomial ε
            ((T : ℂ) + Complex.I * (u : ℂ))‖ /
          ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
            C * (1 + |T| ^ 3) := by
  have hb : 0 < (ε / 4) := div_pos hε four_pos
  refine ⟨4 * (1 + (ε / 4)) * (9 / (ε / 4) + 6),
    by positivity, ?_⟩
  intro u hu T
  let z : ℂ := (T : ℂ) + Complex.I * (u : ℂ)
  let D : ℝ := ‖minusPolynomial ε (Complex.I * (u : ℂ))‖
  have hD : 0 < D := by
    have h := minusPolynomial_imaginary_norm_ge_three_beta
      hε hu
    change 3 * (ε / 4) ≤ D at h
    linarith
  have htriangle :
      1 + ‖z‖ ≤ (1 + |T|) * (1 + |u|) := by
    have hz := saddle_complex_frequency_norm_le T u
    change ‖z‖ ≤ |T| + |u| at hz
    linarith [mul_nonneg (abs_nonneg T) (abs_nonneg u)]
  have hpower :
      (1 + ‖z‖) ^ 3 ≤
        ((1 + |T|) * (1 + |u|)) ^ 3 :=
    pow_le_pow_left₀ (by positivity) htriangle 3
  have hbase := norm_minusPolynomial_le ε z
  rw [abs_of_pos hb] at hbase
  have hfrequency := saddle_one_add_abs_cube_le T
  have hheight := minusPolynomial_imaginary_cubic_growth_le
    hε hu
  change ‖minusPolynomial ε z‖ / D ≤
    (4 * (1 + (ε / 4)) * (9 / (ε / 4) + 6)) *
      (1 + |T| ^ 3)
  apply (div_le_iff₀ hD).2
  calc
    ‖minusPolynomial ε z‖ ≤
        (1 + (ε / 4)) * (1 + ‖z‖) ^ 3 := hbase
    _ ≤ (1 + (ε / 4)) *
        ((1 + |T|) * (1 + |u|)) ^ 3 := by
      gcongr
    _ = (1 + (ε / 4)) * (1 + |T|) ^ 3 *
        (1 + |u|) ^ 3 := by
      ring
    _ ≤ (1 + (ε / 4)) *
        (4 * (1 + |T| ^ 3)) *
          ((9 / (ε / 4) + 6) * D) := by
      gcongr
    _ = ((4 * (1 + (ε / 4)) * (9 / (ε / 4) + 6)) *
        (1 + |T| ^ 3)) * D := by
      ring

private theorem plusPolynomial_add_sub (ε : ℝ) (z w : ℂ) :
    plusPolynomial ε (z + w) - plusPolynomial ε z =
      w * (2 * z + Complex.I * (1 + 3 * z ^ 2)) +
        w ^ 2 * (1 + 3 * Complex.I * z) +
          Complex.I * w ^ 3 := by
  unfold plusPolynomial
  ring

private theorem minusPolynomial_add_sub (ε : ℝ) (z w : ℂ) :
    minusPolynomial ε (z + w) - minusPolynomial ε z =
      w * (2 * z - Complex.I * (1 + 3 * z ^ 2)) +
        w ^ 2 * (1 - 3 * Complex.I * z) -
          Complex.I * w ^ 3 := by
  unfold minusPolynomial
  ring

private theorem plusSaddleLinearCoefficient_norm_le (z : ℂ) :
    ‖2 * z + Complex.I * (1 + 3 * z ^ 2)‖ ≤
      3 * (1 + ‖z‖) ^ 2 := by
  have hinner :
      ‖(1 : ℂ) + 3 * z ^ 2‖ ≤ 1 + 3 * ‖z‖ ^ 2 := by
    calc
      ‖(1 : ℂ) + 3 * z ^ 2‖ ≤
          ‖(1 : ℂ)‖ + ‖(3 : ℂ) * z ^ 2‖ :=
        norm_add_le _ _
      _ = 1 + 3 * ‖z‖ ^ 2 := by
        simp only [norm_one, Complex.norm_mul, Complex.norm_ofNat, norm_pow]
  calc
    ‖2 * z + Complex.I * (1 + 3 * z ^ 2)‖ ≤
        ‖(2 : ℂ) * z‖ +
          ‖Complex.I * (1 + 3 * z ^ 2)‖ :=
      norm_add_le _ _
    _ = 2 * ‖z‖ + ‖(1 : ℂ) + 3 * z ^ 2‖ := by
      simp only [Complex.norm_mul, Complex.norm_ofNat, Complex.norm_I, one_mul]
    _ ≤ 2 * ‖z‖ + (1 + 3 * ‖z‖ ^ 2) := by
      gcongr
    _ ≤ 3 * (1 + ‖z‖) ^ 2 := by
      linarith [norm_nonneg z]

private theorem minusSaddleLinearCoefficient_norm_le (z : ℂ) :
    ‖2 * z - Complex.I * (1 + 3 * z ^ 2)‖ ≤
      3 * (1 + ‖z‖) ^ 2 := by
  have hinner :
      ‖(1 : ℂ) + 3 * z ^ 2‖ ≤ 1 + 3 * ‖z‖ ^ 2 := by
    calc
      ‖(1 : ℂ) + 3 * z ^ 2‖ ≤
          ‖(1 : ℂ)‖ + ‖(3 : ℂ) * z ^ 2‖ :=
        norm_add_le _ _
      _ = 1 + 3 * ‖z‖ ^ 2 := by
        simp only [norm_one, Complex.norm_mul, Complex.norm_ofNat, norm_pow]
  calc
    ‖2 * z - Complex.I * (1 + 3 * z ^ 2)‖ ≤
        ‖(2 : ℂ) * z‖ +
          ‖Complex.I * (1 + 3 * z ^ 2)‖ :=
      norm_sub_le _ _
    _ = 2 * ‖z‖ + ‖(1 : ℂ) + 3 * z ^ 2‖ := by
      simp only [Complex.norm_mul, Complex.norm_ofNat, Complex.norm_I, one_mul]
    _ ≤ 2 * ‖z‖ + (1 + 3 * ‖z‖ ^ 2) := by
      gcongr
    _ ≤ 3 * (1 + ‖z‖) ^ 2 := by
      linarith [norm_nonneg z]

private theorem plusSaddleQuadraticCoefficient_norm_le (z : ℂ) :
    ‖1 + 3 * Complex.I * z‖ ≤
      3 * (1 + ‖z‖) ^ 2 := by
  calc
    ‖1 + 3 * Complex.I * z‖ ≤
        ‖(1 : ℂ)‖ + ‖(3 : ℂ) * Complex.I * z‖ :=
      norm_add_le _ _
    _ = 1 + 3 * ‖z‖ := by
      simp only [norm_one, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
    _ ≤ 3 * (1 + ‖z‖) ^ 2 := by
      linarith [norm_nonneg z, sq_nonneg ‖z‖]

private theorem minusSaddleQuadraticCoefficient_norm_le (z : ℂ) :
    ‖1 - 3 * Complex.I * z‖ ≤
      3 * (1 + ‖z‖) ^ 2 := by
  calc
    ‖1 - 3 * Complex.I * z‖ ≤
        ‖(1 : ℂ)‖ + ‖(3 : ℂ) * Complex.I * z‖ :=
      norm_sub_le _ _
    _ = 1 + 3 * ‖z‖ := by
      simp only [norm_one, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
    _ ≤ 3 * (1 + ‖z‖) ^ 2 := by
      linarith [norm_nonneg z, sq_nonneg ‖z‖]

private theorem saddle_abs_sq_le_add_cube (T : ℝ) :
    |T| ^ 2 ≤ |T| + |T| ^ 3 := by
  have hfactor :
      0 ≤ |T| * (|T| - (1 / 2 : ℝ)) ^ 2 :=
    mul_nonneg (abs_nonneg T) (sq_nonneg _)
  linarith [abs_nonneg T]

private theorem saddle_cubic_translation_norm_le
    (u T : ℝ) (A B C : ℂ)
    (hA : ‖A‖ ≤ 3 * (1 + |u|) ^ 2)
    (hB : ‖B‖ ≤ 3 * (1 + |u|) ^ 2)
    (hC : ‖C‖ ≤ 1) :
    ‖(T : ℂ) * A + (T : ℂ) ^ 2 * B +
        C * (T : ℂ) ^ 3‖ ≤
      9 * (1 + |u|) ^ 2 * (|T| + |T| ^ 3) := by
  let H : ℝ := (1 + |u|) ^ 2
  let S : ℝ := |T| + |T| ^ 3
  have hH : 1 ≤ H := by
    try dsimp [H]
    linarith [abs_nonneg u, sq_nonneg |u|]
  have hS : 0 ≤ S := by
    try dsimp [S]
    positivity
  have hT : |T| ≤ S := by
    try dsimp [S]
    linarith [pow_nonneg (abs_nonneg T) 3]
  have hT2 : |T| ^ 2 ≤ S := by
    exact saddle_abs_sq_le_add_cube T
  have hT3 : |T| ^ 3 ≤ S := by
    try dsimp [S]
    linarith [abs_nonneg T]
  have hfirst :
      ‖(T : ℂ) * A‖ ≤ |T| * (3 * H) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hA (abs_nonneg T)
  have hsecond :
      ‖(T : ℂ) ^ 2 * B‖ ≤ |T| ^ 2 * (3 * H) := by
    rw [norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hB
      (sq_nonneg |T|)
  have hthird :
      ‖C * (T : ℂ) ^ 3‖ ≤ |T| ^ 3 := by
    rw [norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs]
    linarith [mul_le_mul_of_nonneg_right hC
      (pow_nonneg (abs_nonneg T) 3)]
  have hfirst' : |T| * (3 * H) ≤ 3 * H * S := by
    linarith [mul_le_mul_of_nonneg_left hT
      (show 0 ≤ 3 * H by positivity)]
  have hsecond' : |T| ^ 2 * (3 * H) ≤ 3 * H * S := by
    linarith [mul_le_mul_of_nonneg_left hT2
      (show 0 ≤ 3 * H by positivity)]
  have hthird' : |T| ^ 3 ≤ H * S := by
    have hraise : S ≤ H * S := by
      linarith [mul_nonneg (sub_nonneg.mpr hH) hS]
    exact hT3.trans hraise
  calc
    ‖(T : ℂ) * A + (T : ℂ) ^ 2 * B +
        C * (T : ℂ) ^ 3‖ ≤
      ‖(T : ℂ) * A + (T : ℂ) ^ 2 * B‖ +
        ‖C * (T : ℂ) ^ 3‖ :=
      norm_add_le _ _
    _ ≤ (‖(T : ℂ) * A‖ + ‖(T : ℂ) ^ 2 * B‖) +
        ‖C * (T : ℂ) ^ 3‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (|T| * (3 * H) + |T| ^ 2 * (3 * H)) +
        |T| ^ 3 := by
      gcongr
    _ ≤ 9 * H * S := by
      linarith [mul_nonneg (show 0 ≤ H by positivity) hS]
    _ = 9 * (1 + |u|) ^ 2 * (|T| + |T| ^ 3) := by
      rfl

private theorem plusPolynomial_translation_norm_le
    (ε u T : ℝ) :
    ‖plusPolynomial ε ((T : ℂ) + Complex.I * (u : ℂ)) -
        plusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
      9 * (1 + |u|) ^ 2 * (|T| + |T| ^ 3) := by
  let z : ℂ := Complex.I * (u : ℂ)
  have hz : ‖z‖ = |u| := by
    try dsimp [z]
    simp only [Complex.norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
  have hA :
      ‖2 * z + Complex.I * (1 + 3 * z ^ 2)‖ ≤
        3 * (1 + |u|) ^ 2 := by
    simpa only [hz] using! plusSaddleLinearCoefficient_norm_le z
  have hB :
      ‖1 + 3 * Complex.I * z‖ ≤
        3 * (1 + |u|) ^ 2 := by
    simpa only [hz] using! plusSaddleQuadraticCoefficient_norm_le z
  have hidentity :
      plusPolynomial ε ((T : ℂ) + z) -
          plusPolynomial ε z =
        (T : ℂ) * (2 * z + Complex.I * (1 + 3 * z ^ 2)) +
          (T : ℂ) ^ 2 * (1 + 3 * Complex.I * z) +
            Complex.I * (T : ℂ) ^ 3 := by
    rw [add_comm (T : ℂ) z,
      plusPolynomial_add_sub]
  change
    ‖plusPolynomial ε ((T : ℂ) + z) -
        plusPolynomial ε z‖ ≤ _
  rw [hidentity]
  exact saddle_cubic_translation_norm_le u T
    (2 * z + Complex.I * (1 + 3 * z ^ 2))
    (1 + 3 * Complex.I * z) Complex.I
    hA hB (by simp only [Complex.norm_I, Std.le_refl])

private theorem minusPolynomial_translation_norm_le
    (ε u T : ℝ) :
    ‖minusPolynomial ε ((T : ℂ) + Complex.I * (u : ℂ)) -
        minusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
      9 * (1 + |u|) ^ 2 * (|T| + |T| ^ 3) := by
  let z : ℂ := Complex.I * (u : ℂ)
  have hz : ‖z‖ = |u| := by
    try dsimp [z]
    simp only [Complex.norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
  have hA :
      ‖2 * z - Complex.I * (1 + 3 * z ^ 2)‖ ≤
        3 * (1 + |u|) ^ 2 := by
    simpa only [hz] using! minusSaddleLinearCoefficient_norm_le z
  have hB :
      ‖1 - 3 * Complex.I * z‖ ≤
        3 * (1 + |u|) ^ 2 := by
    simpa only [hz] using! minusSaddleQuadraticCoefficient_norm_le z
  have hidentity :
      minusPolynomial ε ((T : ℂ) + z) -
          minusPolynomial ε z =
        (T : ℂ) * (2 * z - Complex.I * (1 + 3 * z ^ 2)) +
          (T : ℂ) ^ 2 * (1 - 3 * Complex.I * z) +
            (-Complex.I) * (T : ℂ) ^ 3 := by
    rw [add_comm (T : ℂ) z,
      minusPolynomial_add_sub]
    ring
  change
    ‖minusPolynomial ε ((T : ℂ) + z) -
        minusPolynomial ε z‖ ≤ _
  rw [hidentity]
  exact saddle_cubic_translation_norm_le u T
    (2 * z - Complex.I * (1 + 3 * z ^ 2))
    (1 - 3 * Complex.I * z) (-Complex.I)
    hA hB (by simp only [norm_neg, Complex.norm_I, Std.le_refl])

private theorem exists_plusPolynomial_uniform_difference_ratio
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : ℝ, -1 ≤ u → ∀ T : ℝ,
        ‖plusPolynomial ε
              ((T : ℂ) + Complex.I * (u : ℂ)) -
            plusPolynomial ε (Complex.I * (u : ℂ))‖ /
          ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
            C * (|T| + |T| ^ 3) := by
  have hb : 0 < (ε / 4) := div_pos hε four_pos
  refine ⟨9 * (27 / (ε / 4) + 9), by positivity, ?_⟩
  intro u hu T
  let D : ℝ := ‖plusPolynomial ε (Complex.I * (u : ℂ))‖
  let S : ℝ := |T| + |T| ^ 3
  have hD : 0 < D :=
    lt_of_lt_of_le hb (plusPolynomial_imaginary_norm_ge_beta hε hu)
  have hS : 0 ≤ S := by
    try dsimp [S]
    positivity
  have hsquare : (1 + |u|) ^ 2 ≤ (1 + |u|) ^ 3 := by
    have hfactor :
        0 ≤ |u| * (1 + |u|) ^ 2 :=
      mul_nonneg (abs_nonneg u) (sq_nonneg _)
    linarith
  have hgrowth := plusPolynomial_imaginary_cubic_growth_le
    hε hu
  have hquadratic :
      (1 + |u|) ^ 2 ≤ (27 / (ε / 4) + 9) * D :=
    hsquare.trans hgrowth
  change
    ‖plusPolynomial ε
          ((T : ℂ) + Complex.I * (u : ℂ)) -
        plusPolynomial ε (Complex.I * (u : ℂ))‖ / D ≤
      (9 * (27 / (ε / 4) + 9)) * S
  apply (div_le_iff₀ hD).2
  calc
    ‖plusPolynomial ε
          ((T : ℂ) + Complex.I * (u : ℂ)) -
        plusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
      9 * (1 + |u|) ^ 2 * S :=
        plusPolynomial_translation_norm_le ε u T
    _ ≤ 9 * ((27 / (ε / 4) + 9) * D) * S := by
      gcongr
    _ = ((9 * (27 / (ε / 4) + 9)) * S) * D := by
      ring

private theorem exists_minusPolynomial_uniform_difference_ratio
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : ℝ, 1 + ε / 4 ≤ u → ∀ T : ℝ,
        ‖minusPolynomial ε
              ((T : ℂ) + Complex.I * (u : ℂ)) -
            minusPolynomial ε (Complex.I * (u : ℂ))‖ /
          ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
            C * (|T| + |T| ^ 3) := by
  have hb : 0 < (ε / 4) := div_pos hε four_pos
  refine ⟨9 * (9 / (ε / 4) + 6), by positivity, ?_⟩
  intro u hu T
  let D : ℝ := ‖minusPolynomial ε (Complex.I * (u : ℂ))‖
  let S : ℝ := |T| + |T| ^ 3
  have hD : 0 < D := by
    have h := minusPolynomial_imaginary_norm_ge_three_beta
      hε hu
    change 3 * (ε / 4) ≤ D at h
    linarith
  have hS : 0 ≤ S := by
    try dsimp [S]
    positivity
  have hsquare : (1 + |u|) ^ 2 ≤ (1 + |u|) ^ 3 := by
    have hfactor :
        0 ≤ |u| * (1 + |u|) ^ 2 :=
      mul_nonneg (abs_nonneg u) (sq_nonneg _)
    linarith
  have hgrowth := minusPolynomial_imaginary_cubic_growth_le
    hε hu
  have hquadratic :
      (1 + |u|) ^ 2 ≤ (9 / (ε / 4) + 6) * D :=
    hsquare.trans hgrowth
  change
    ‖minusPolynomial ε
          ((T : ℂ) + Complex.I * (u : ℂ)) -
        minusPolynomial ε (Complex.I * (u : ℂ))‖ / D ≤
      (9 * (9 / (ε / 4) + 6)) * S
  apply (div_le_iff₀ hD).2
  calc
    ‖minusPolynomial ε
          ((T : ℂ) + Complex.I * (u : ℂ)) -
        minusPolynomial ε (Complex.I * (u : ℂ))‖ ≤
      9 * (1 + |u|) ^ 2 * S :=
        minusPolynomial_translation_norm_le ε u T
    _ ≤ 9 * ((9 / (ε / 4) + 6) * D) * S := by
      gcongr
    _ = ((9 * (9 / (ε / 4) + 6)) * S) * D := by
      ring

private noncomputable def upperNegativeHalfGammaArgument (N : ℕ) (s : ℝ) : ℂ :=
  -((N : ℂ) + (1 / 2 : ℂ)) -
    Complex.I * ((s / 2 : ℝ) : ℂ)

private theorem upperNegativeHalfGammaArgument_ne_zero
    (N : ℕ) (s : ℝ) :
    upperNegativeHalfGammaArgument N s ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  simp only [upperNegativeHalfGammaArgument, one_div, neg_add_rev, Complex.ofReal_div,
    Complex.ofReal_ofNat,
    Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.inv_re, Complex.re_ofNat,
      Complex.normSq_ofNat,
    div_self_mul_self', Complex.natCast_re, Complex.mul_re, Complex.I_re, Complex.div_ofNat_re,
      Complex.ofReal_re,
    zero_mul, Complex.I_im, Complex.div_ofNat_im, Complex.ofReal_im, zero_div, mul_zero,
      sub_self, sub_zero,
    Complex.zero_re] at hre
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  linarith

private theorem upperNegativeHalfGammaArgument_succ_add_one
    (N : ℕ) (s : ℝ) :
    upperNegativeHalfGammaArgument (N + 1) s + 1 =
      upperNegativeHalfGammaArgument N s := by
  unfold upperNegativeHalfGammaArgument
  simp only [Nat.cast_add, Nat.cast_one]
  ring

private theorem tendsto_upper_shortEndpoint_scaled :
    Tendsto (fun ε : ℝ => ε * (10 * Real.log (1 / ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hlog := tendsto_log_mul_rpow_nhdsGT_zero
    (by norm_num : (0 : ℝ) < 1)
  simp only [Real.rpow_one] at hlog
  have hscaled := hlog.const_mul (-10 : ℝ)
  convert! hscaled using 1
  · ext ε
    rw [one_div, Real.log_inv]
    ring
  · norm_num

private theorem tendsto_upper_one_add_shortEndpoint_scaled :
    Tendsto (fun ε : ℝ => ε * (1 + (10 * Real.log (1 / ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hid : Tendsto (fun ε : ℝ => ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  convert! hid.add tendsto_upper_shortEndpoint_scaled using 1
  · ext ε
    ring
  · norm_num

private theorem eventually_upper_shortMargin_positive :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ a ∈ Set.Icc (ε ^ 3) (10 * Real.log (1 / ε)),
        (1 / 2 : ℝ) ≤ (1 - 10 * ε * (1 + a)) := by
  have hscaled :
      Tendsto (fun ε : ℝ =>
        10 * (ε * (1 + (10 * Real.log (1 / ε)))))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    convert! tendsto_upper_one_add_shortEndpoint_scaled.const_mul
      (10 : ℝ) using 1; norm_num
  have hsmall := hscaled.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [self_mem_nhdsWithin, hsmall]
    with ε hε hbound a ha
  change 0 < ε at hε
  have hcompare :
      ε * (1 + a) ≤ ε * (1 + (10 * Real.log (1 / ε))) :=
    mul_le_mul_of_nonneg_left (by linarith [ha.2]) hε.le
  change 10 * (ε * (1 + (10 * Real.log (1 / ε)))) < 1 / 2
    at hbound
  linarith

private theorem eventually_upper_shellLocation_gt_shortEndpoint :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      (10 * Real.log (1 / ε)) + 1 < (ε⁻¹ ^ 3) := by
  have hid : Tendsto (fun ε : ℝ => ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hpow :
      Tendsto (fun ε : ℝ =>
        ε ^ 2 * (ε * (1 + (10 * Real.log (1 / ε)))))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero] using! (hid.pow 2).mul
      tendsto_upper_one_add_shortEndpoint_scaled
  have hsmall :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        ε ^ 3 * ((10 * Real.log (1 / ε)) + 1) < 1 := by
    have hevent := hpow.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hevent] with ε hε
    change ε ^ 2 * (ε * (1 + (10 * Real.log (1 / ε)))) < 1
      at hε
    linarith
  filter_upwards [self_mem_nhdsWithin, hsmall]
    with ε hε hbound
  change 0 < ε at hε
  have hcube : 0 < ε ^ 3 := pow_pos hε 3
  have hinv : ε ^ 3 * (ε⁻¹ ^ 3) = 1 := by
    field_simp [hε.ne']
  have hmul :
      ε ^ 3 * ((10 * Real.log (1 / ε)) + 1) <
        ε ^ 3 * (ε⁻¹ ^ 3) := by
    rw [hinv]
    exact hbound
  nlinarith [hmul]

private noncomputable def upperShellShortCoefficient (ε : ℝ) : ℝ :=
  (10 * Real.log (1 / ε)) + (ε ^ 3)⁻¹

private noncomputable def upperShellMarginRatio (ε : ℝ) : ℝ :=
  5000 * upperShellShortCoefficient ε *
      Real.exp ((ε / 2) * (10 * Real.log (1 / ε))) /
    (shellWeight ε *
      Real.exp ((ε / 2) * (ε⁻¹ ^ 3)))

private theorem upperShellMarginRatio_inv
    {x : ℝ} (hx : x ≠ 0) :
    upperShellMarginRatio x⁻¹ =
      5000 * (10 * Real.log x + x ^ 3) *
        Real.exp (-(x ^ 2) / 8) *
          Real.exp (5 * Real.log x / x) := by
  have hshort : (10 * Real.log (1 / x⁻¹)) = 10 * Real.log x := by
    simp only [div_inv_eq_mul, one_mul]
  have hcutoff : ((x⁻¹ ^ 3))⁻¹ = x ^ 3 := by
    simp only [inv_pow, inv_inv]
  have hlocation : (x⁻¹⁻¹ ^ 3) = x ^ 3 := by
    simp only [inv_inv]
  have hweight :
      shellWeight x⁻¹ = Real.exp (-(3 : ℝ) * x ^ 2 / 8) := by
    unfold shellWeight
    rw [hlocation]
    congr 1
    field_simp [hx]
  have hexp :
      Real.exp ((x⁻¹ / 2) * (10 * Real.log x)) /
          (Real.exp (-(3 : ℝ) * x ^ 2 / 8) *
            Real.exp ((x⁻¹ / 2) * x ^ 3)) =
        Real.exp (-(x ^ 2) / 8) *
          Real.exp (5 * Real.log x / x) := by
    rw [← Real.exp_add, ← Real.exp_sub, ← Real.exp_add]
    congr 1
    field_simp [hx]; ring
  unfold upperShellMarginRatio upperShellShortCoefficient
  rw [hshort, hcutoff, hlocation, hweight]
  calc
    5000 * (10 * Real.log x + x ^ 3) *
        Real.exp (x⁻¹ / 2 * (10 * Real.log x)) /
          (Real.exp (-(3 : ℝ) * x ^ 2 / 8) *
            Real.exp (x⁻¹ / 2 * x ^ 3)) =
      5000 * (10 * Real.log x + x ^ 3) *
        (Real.exp (x⁻¹ / 2 * (10 * Real.log x)) /
          (Real.exp (-(3 : ℝ) * x ^ 2 / 8) *
            Real.exp (x⁻¹ / 2 * x ^ 3))) := by ring
    _ = 5000 * (10 * Real.log x + x ^ 3) *
        (Real.exp (-(x ^ 2) / 8) *
          Real.exp (5 * Real.log x / x)) := by
      rw [hexp]
    _ = 5000 * (10 * Real.log x + x ^ 3) *
        Real.exp (-(x ^ 2) / 8) *
          Real.exp (5 * Real.log x / x) := by ring

private theorem tendsto_upper_log_cubic_gaussian_atTop :
    Tendsto (fun x : ℝ =>
      (10 * Real.log x + x ^ 3) *
        Real.exp (-(x ^ 2) / 8))
      atTop (𝓝 (0 : ℝ)) := by
  have hupper :
      Tendsto (fun x : ℝ =>
        11 * ((x ^ 3 + 1) *
          Real.exp (-(x ^ 2) / 8)))
        atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using! tendsto_cubic_gaussian_atTop.const_mul (11 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ))) hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
    have hcube : 0 ≤ x ^ 3 := by positivity
    exact mul_nonneg (by linarith) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hxpos : 0 < x := by linarith
    have hlog := Real.log_le_sub_one_of_pos hxpos
    have hsquare : 0 ≤ x ^ 2 - 1 := by
      linarith [sq_nonneg (x - 1)]
    have hcube : x ≤ x ^ 3 := by
      linarith [mul_nonneg hxpos.le hsquare]
    have hfactor :
        10 * Real.log x + x ^ 3 ≤
          11 * (x ^ 3 + 1) := by
      linarith
    calc
      (10 * Real.log x + x ^ 3) *
          Real.exp (-(x ^ 2) / 8) ≤
        (11 * (x ^ 3 + 1)) *
          Real.exp (-(x ^ 2) / 8) :=
        mul_le_mul_of_nonneg_right hfactor
          (Real.exp_pos _).le
      _ = 11 * ((x ^ 3 + 1) *
          Real.exp (-(x ^ 2) / 8)) := by ring

private theorem tendsto_upper_shell_log_correction_atTop :
    Tendsto (fun x : ℝ =>
      Real.exp (5 * Real.log x / x))
      atTop (𝓝 (1 : ℝ)) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [pow_one, one_mul, add_zero] using!
      Real.tendsto_pow_log_div_mul_add_atTop
        1 0 1 (by norm_num : (1 : ℝ) ≠ 0)
  have hscaled : Tendsto (fun x : ℝ =>
      5 * Real.log x / x)
      atTop (𝓝 (0 : ℝ)) := by
    convert! hlog.const_mul (5 : ℝ) using 1
    · ext x
      ring
    · norm_num
  simpa only [Real.exp_zero] using! hscaled.rexp

private theorem tendsto_upperShellMarginRatio :
    Tendsto upperShellMarginRatio
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  apply tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop
  have hproduct :
      Tendsto (fun x : ℝ =>
        (5000 * ((10 * Real.log x + x ^ 3) *
          Real.exp (-(x ^ 2) / 8))) *
            Real.exp (5 * Real.log x / x))
        atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, mul_one] using!
      (tendsto_upper_log_cubic_gaussian_atTop.const_mul
        (5000 : ℝ)).mul
          tendsto_upper_shell_log_correction_atTop
  refine hproduct.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
  rw [upperShellMarginRatio_inv hx]
  ring

private theorem eventually_upper_shell_parameter_margin :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      upperShellShortCoefficient ε *
          Real.exp ((ε / 2) * (10 * Real.log (1 / ε))) ≤
        (1 / 5000 : ℝ) * shellWeight ε *
          Real.exp ((ε / 2) * (ε⁻¹ ^ 3)) := by
  have hratio := tendsto_upperShellMarginRatio.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hratio] with ε hε
  unfold upperShellMarginRatio at hε
  have hden :
      0 < shellWeight ε *
        Real.exp ((ε / 2) * (ε⁻¹ ^ 3)) :=
    mul_pos (shellWeight_pos ε) (Real.exp_pos _)
  have hscaled :
      5000 * upperShellShortCoefficient ε *
        Real.exp ((ε / 2) * (10 * Real.log (1 / ε))) <
          shellWeight ε *
            Real.exp ((ε / 2) * (ε⁻¹ ^ 3)) := by
    exact (div_lt_one hden).mp hε
  linarith

private theorem upper_one_sub_cos_le_min (x : ℝ) :
    1 - Real.cos x ≤ min (x ^ 2 / 2) 2 := by
  apply le_min
  · linarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  · linarith [Real.neg_one_le_cos x]

private theorem upper_min_frequency_inverse_sq_le
    {a : ℝ} (ha : 0 < a) (T : ℝ) :
    min (T ^ 2) ((a ^ 2)⁻¹) ≤
      min (T ^ 2) 1 * (1 + (a ^ 2)⁻¹) := by
  have hinv : 0 ≤ (a ^ 2)⁻¹ := by positivity
  by_cases hsmall : T ^ 2 ≤ 1
  · rw [min_eq_left hsmall]
    have hmin := min_le_left (T ^ 2) ((a ^ 2)⁻¹)
    linarith [mul_nonneg (sq_nonneg T) hinv]
  · rw [min_eq_right (le_of_not_ge hsmall)]
    have hmin := min_le_right (T ^ 2) ((a ^ 2)⁻¹)
    linarith

private noncomputable def upperShortShellDamping (ε ℓ δ T : ℝ) : ℝ :=
  ℓ * ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
    (-shortShellDensity ε a) *
      Real.cosh ((1 + δ) * a) *
        (1 - Real.cos (a * T))

private theorem upper_shortShell_oscillation_div_sq_le
    {a : ℝ} (ha : 0 < a) (T : ℝ) :
    (1 - Real.cos (a * T)) / (2 * a ^ 2) ≤
      min (T ^ 2) ((a ^ 2)⁻¹) := by
  have hden : 0 < 2 * a ^ 2 := by positivity
  have hcos := upper_one_sub_cos_le_min (a * T)
  apply le_min
  · calc
      (1 - Real.cos (a * T)) / (2 * a ^ 2) ≤
          ((a * T) ^ 2 / 2) / (2 * a ^ 2) :=
        div_le_div_of_nonneg_right
          (hcos.trans (min_le_left _ _)) hden.le
      _ = T ^ 2 / 4 := by
        field_simp [ha.ne']; ring
      _ ≤ T ^ 2 := by
        linarith [sq_nonneg T]
  · calc
      (1 - Real.cos (a * T)) / (2 * a ^ 2) ≤
          2 / (2 * a ^ 2) :=
        div_le_div_of_nonneg_right
          (hcos.trans (min_le_right _ _)) hden.le
      _ = (a ^ 2)⁻¹ := by
        field_simp [ha.ne']

private theorem upper_shortShellDensity_damping_le
    {ε δ a A : ℝ}
    (hε : 0 < ε) (hδ : 0 ≤ δ)
    (ha : 0 < a) (haA : a ≤ A)
    (hmargin : 0 ≤ (1 - 10 * ε * (1 + a)))
    (T : ℝ) :
    (-shortShellDensity ε a) *
        Real.cosh ((1 + δ) * a) *
          (1 - Real.cos (a * T)) ≤
      Real.exp (δ * A) * min (T ^ 2) 1 *
        (1 + (a ^ 2)⁻¹) := by
  have hmarginone : (1 - 10 * ε * (1 + a)) ≤ 1 := by
    linarith [mul_nonneg hε.le (show 0 ≤ 1 + a by linarith)]
  have hnegativeexp : Real.exp (-2 * a) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hratio :
      Real.cosh ((1 + δ) * a) / Real.cosh a ≤
        Real.exp (δ * A) := by
    exact (cosh_ratio_upper ha.le hδ).trans
      (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left haA hδ))
  have hosc := upper_shortShell_oscillation_div_sq_le ha T
  have hosc_nonneg :
      0 ≤ (1 - Real.cos (a * T)) / (2 * a ^ 2) := by
    exact div_nonneg
      (sub_nonneg.mpr (Real.cos_le_one _))
      (by positivity)
  have hratio_scaled :
      (1 - 10 * ε * (1 + a)) * Real.exp (-2 * a) *
          (Real.cosh ((1 + δ) * a) / Real.cosh a) ≤
        (1 - 10 * ε * (1 + a)) * Real.exp (-2 * a) *
          Real.exp (δ * A) :=
    mul_le_mul_of_nonneg_left hratio
      (mul_nonneg hmargin (Real.exp_pos _).le)
  have hidentity :
      (-shortShellDensity ε a) *
          Real.cosh ((1 + δ) * a) *
            (1 - Real.cos (a * T)) =
        (1 - 10 * ε * (1 + a)) * Real.exp (-2 * a) *
          (Real.cosh ((1 + δ) * a) / Real.cosh a) *
            ((1 - Real.cos (a * T)) / (2 * a ^ 2)) := by
    unfold shortShellDensity
    field_simp [ha.ne', (Real.cosh_pos a).ne']
  rw [hidentity]
  calc
    (1 - 10 * ε * (1 + a)) * Real.exp (-2 * a) *
        (Real.cosh ((1 + δ) * a) / Real.cosh a) *
          ((1 - Real.cos (a * T)) / (2 * a ^ 2)) ≤
      ((1 - 10 * ε * (1 + a)) * Real.exp (-2 * a) *
        Real.exp (δ * A)) *
          ((1 - Real.cos (a * T)) / (2 * a ^ 2)) :=
      mul_le_mul_of_nonneg_right hratio_scaled hosc_nonneg
    _ ≤
      (1 : ℝ) * 1 * Real.exp (δ * A) *
        min (T ^ 2) ((a ^ 2)⁻¹) := by
      gcongr
    _ = Real.exp (δ * A) *
        min (T ^ 2) ((a ^ 2)⁻¹) := by ring
    _ ≤ Real.exp (δ * A) *
        (min (T ^ 2) 1 * (1 + (a ^ 2)⁻¹)) :=
      mul_le_mul_of_nonneg_left
        (upper_min_frequency_inverse_sq_le ha T)
        (Real.exp_pos _).le
    _ = Real.exp (δ * A) * min (T ^ 2) 1 *
        (1 + (a ^ 2)⁻¹) := by ring

private theorem upper_intervalIntegral_one_add_inv_sq
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, 1 + (x ^ 2)⁻¹) =
      b - a + a⁻¹ - b⁻¹ := by
  have hcont :
      ContinuousOn (fun x : ℝ => 1 + (x ^ 2)⁻¹)
        (Set.Icc a b) := by
    apply continuousOn_const.add
      ((continuous_id.pow 2).continuousOn.inv₀ ?_)
    intro x hx
    have hxpos : 0 < x := ha.trans_le hx.1
    exact (sq_pos_of_pos hxpos).ne'
  have hderiv (x : ℝ) (hx : x ∈ Set.Icc a b) :
      HasDerivAt (fun y : ℝ => y - y⁻¹)
        (1 + (x ^ 2)⁻¹) x := by
    have hxpos : 0 < x := ha.trans_le hx.1
    convert! (hasDerivAt_id x).sub
      (hasDerivAt_inv hxpos.ne') using 1; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hderiv x
      (by simpa only [mem_Icc, Set.uIcc_of_le hab] using! hx))
    (hcont.intervalIntegrable_of_Icc hab)]
  ring

private theorem upperShortShellDamping_global_bound
    {ε ℓ δ T : ℝ}
    (hε : 0 < ε) (hℓ : 0 ≤ ℓ) (hδ : 0 ≤ δ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Set.Icc (ε ^ 3)
      (10 * Real.log (1 / ε)), 0 ≤ (1 - 10 * ε * (1 + a))) :
    upperShortShellDamping ε ℓ δ T ≤
      ℓ * upperShellShortCoefficient ε *
        Real.exp (δ * (10 * Real.log (1 / ε))) *
          min (T ^ 2) 1 := by
  let a₀ : ℝ := (ε ^ 3)
  let A : ℝ := (10 * Real.log (1 / ε))
  let K : ℝ := Real.exp (δ * A) * min (T ^ 2) 1
  have ha₀ : 0 < a₀ := by
    try dsimp [a₀]
    positivity
  have hA : 0 < A := ha₀.trans_le horder
  have hK : 0 ≤ K := by
    try dsimp [K]
    exact mul_nonneg (Real.exp_pos _).le
      (le_min (sq_nonneg T) (by norm_num))
  have hshort :
      ContinuousOn (shortShellDensity ε) (Set.Icc a₀ A) := by
    have hn : Continuous (fun a : ℝ =>
      (1 - 10 * ε * (1 + a)) * Real.exp (-2 * a)) := by
      fun_prop
    have hd : Continuous (fun a : ℝ =>
      2 * a ^ 2 * Real.cosh a) := by
      fun_prop
    unfold shortShellDensity
    apply (hn.continuousOn.div hd.continuousOn ?_).neg
    intro a ha
    have hapos : 0 < a := ha₀.trans_le ha.1
    exact
      (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hapos))
        (Real.cosh_pos a)).ne'
  have hcosh : Continuous
      (fun a : ℝ => Real.cosh ((1 + δ) * a)) := by
    fun_prop
  have hosc : Continuous
      (fun a : ℝ => 1 - Real.cos (a * T)) := by
    fun_prop
  have hleft : ContinuousOn
      (fun a : ℝ =>
        (-shortShellDensity ε a) *
          Real.cosh ((1 + δ) * a) *
            (1 - Real.cos (a * T)))
        (Set.Icc a₀ A) :=
    (hshort.neg.mul hcosh.continuousOn).mul
      hosc.continuousOn
  have hinv : ContinuousOn
      (fun a : ℝ => (a ^ 2)⁻¹)
        (Set.Icc a₀ A) := by
    apply (continuous_id.pow 2).continuousOn.inv₀
    intro a ha
    have hapos : 0 < a := ha₀.trans_le ha.1
    exact (sq_pos_of_pos hapos).ne'
  have hright : ContinuousOn
      (fun a : ℝ => K * (1 + (a ^ 2)⁻¹))
        (Set.Icc a₀ A) :=
    continuousOn_const.mul
      (continuousOn_const.add hinv)
  have hpoint :
      ∀ a ∈ Set.Icc a₀ A,
        (-shortShellDensity ε a) *
            Real.cosh ((1 + δ) * a) *
              (1 - Real.cos (a * T)) ≤
          K * (1 + (a ^ 2)⁻¹) := by
    intro a ha
    have hapos : 0 < a := ha₀.trans_le ha.1
    exact upper_shortShellDensity_damping_le
      hε hδ hapos ha.2
      (hmargin a ha) T
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) horder
    (hleft.intervalIntegrable_of_Icc horder)
    (hright.intervalIntegrable_of_Icc horder)
    hpoint
  have hevaluate :
      (∫ a in a₀..A, K * (1 + (a ^ 2)⁻¹)) =
        K * (A - a₀ + a₀⁻¹ - A⁻¹) := by
    rw [intervalIntegral.integral_const_mul,
      upper_intervalIntegral_one_add_inv_sq ha₀ horder]
  rw [hevaluate] at hmono
  have hcoefficient :
      A - a₀ + a₀⁻¹ - A⁻¹ ≤ A + a₀⁻¹ := by
    have hAinv : 0 ≤ A⁻¹ := (inv_pos.mpr hA).le
    linarith
  change
    ℓ * (∫ a in a₀..A,
      (-shortShellDensity ε a) *
        Real.cosh ((1 + δ) * a) *
          (1 - Real.cos (a * T))) ≤
      ℓ * upperShellShortCoefficient ε *
        Real.exp (δ * A) * min (T ^ 2) 1
  calc
    ℓ * (∫ a in a₀..A,
        (-shortShellDensity ε a) *
          Real.cosh ((1 + δ) * a) *
            (1 - Real.cos (a * T))) ≤
        ℓ * (K * (A - a₀ + a₀⁻¹ - A⁻¹)) :=
      mul_le_mul_of_nonneg_left hmono hℓ
    _ ≤ ℓ * (K * (A + a₀⁻¹)) := by
      gcongr
    _ = ℓ * upperShellShortCoefficient ε *
        Real.exp (δ * A) * min (T ^ 2) 1 := by
      unfold upperShellShortCoefficient
      try dsimp [a₀, A, K]
      ring

private theorem eventually_upper_shortCutoff_le_shortEndpoint :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      (ε ^ 3) ≤ (10 * Real.log (1 / ε)) := by
  have hlower := tendsto_shortCutoff.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hupper := tendsto_shortEndpoint.eventually_ge_atTop
    (1 : ℝ)
  filter_upwards [hlower, hupper] with ε hl hu
  linarith

private theorem upper_shell_parameter_margin_propagate
    {ε δ : ℝ}
    (hδ : ε / 2 ≤ δ)
    (hseparation : (10 * Real.log (1 / ε)) ≤ (ε⁻¹ ^ 3))
    (hmargin :
      upperShellShortCoefficient ε *
          Real.exp ((ε / 2) * (10 * Real.log (1 / ε))) ≤
        (1 / 5000 : ℝ) * shellWeight ε *
          Real.exp ((ε / 2) * (ε⁻¹ ^ 3))) :
    upperShellShortCoefficient ε *
        Real.exp (δ * (10 * Real.log (1 / ε))) ≤
      (1 / 5000 : ℝ) * shellWeight ε *
        Real.exp (δ * (ε⁻¹ ^ 3)) := by
  let q : ℝ := δ - ε / 2
  have hq : 0 ≤ q := by
    try dsimp [q]
    linarith
  have hexp :
      Real.exp (q * (10 * Real.log (1 / ε))) ≤
        Real.exp (q * (ε⁻¹ ^ 3)) :=
    Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hseparation hq)
  have hfactor :
      0 ≤ (1 / 5000 : ℝ) * shellWeight ε *
        Real.exp ((ε / 2) * (ε⁻¹ ^ 3)) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (shellWeight_pos ε).le)
      (Real.exp_pos _).le
  calc
    upperShellShortCoefficient ε *
        Real.exp (δ * (10 * Real.log (1 / ε))) =
      (upperShellShortCoefficient ε *
        Real.exp ((ε / 2) * (10 * Real.log (1 / ε)))) *
          Real.exp (q * (10 * Real.log (1 / ε))) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      try dsimp [q]
      ring
    _ ≤ ((1 / 5000 : ℝ) * shellWeight ε *
        Real.exp ((ε / 2) * (ε⁻¹ ^ 3))) *
          Real.exp (q * (10 * Real.log (1 / ε))) :=
      mul_le_mul_of_nonneg_right hmargin
        (Real.exp_pos _).le
    _ ≤ ((1 / 5000 : ℝ) * shellWeight ε *
        Real.exp ((ε / 2) * (ε⁻¹ ^ 3))) *
          Real.exp (q * (ε⁻¹ ^ 3)) :=
      mul_le_mul_of_nonneg_left hexp hfactor
    _ = (1 / 5000 : ℝ) * shellWeight ε *
        Real.exp (δ * (ε⁻¹ ^ 3)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      try dsimp [q]
      ring

private theorem eventually_upper_shortShell_domination :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 0 ≤ ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          ∀ T : ℝ,
            upperShortShellDamping ε ℓ δ T ≤
              (1 / 100 : ℝ) *
                positiveShellDamping ε ℓ δ T := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_upper_shortMargin_positive,
      eventually_upper_shellLocation_gt_shortEndpoint,
      eventually_upper_shell_parameter_margin]
    with ε hε horder hshortmargin hseparation hmargin
  change 0 < ε at hε
  intro ℓ hℓ δ hδ T
  have hδnonneg : 0 ≤ δ := by
    linarith
  have hshort :
      upperShortShellDamping ε ℓ δ T ≤
        ℓ * upperShellShortCoefficient ε *
          Real.exp (δ * (10 * Real.log (1 / ε))) *
            min (T ^ 2) 1 :=
    upperShortShellDamping_global_bound
      hε hℓ hδnonneg horder
      (fun a ha => by
        have h := hshortmargin a ha
        linarith)
  have hpropagate :=
    upper_shell_parameter_margin_propagate hδ
      (le_of_lt (by linarith [hseparation])) hmargin
  have hpositive :=
    positiveShellDamping_lower_bound
      (ε := ε) (ℓ := ℓ) (δ := δ) (T := T)
      hε hℓ hδnonneg
  have hfreq : 0 ≤ min (T ^ 2) 1 :=
    le_min (sq_nonneg T) (by norm_num)
  calc
    upperShortShellDamping ε ℓ δ T ≤
        ℓ * upperShellShortCoefficient ε *
          Real.exp (δ * (10 * Real.log (1 / ε))) *
            min (T ^ 2) 1 := hshort
    _ ≤ ℓ * ((1 / 5000 : ℝ) * shellWeight ε *
          Real.exp (δ * (ε⁻¹ ^ 3))) *
            min (T ^ 2) 1 := by
      convert! mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpropagate hℓ)
          hfreq using 1; ring
    _ = (1 / 100 : ℝ) *
        (ℓ / 50 * shellWeight ε *
          Real.exp (δ * (ε⁻¹ ^ 3)) *
            min (T ^ 2) 1) := by
      ring
    _ ≤ (1 / 100 : ℝ) *
        positiveShellDamping ε ℓ δ T :=
      mul_le_mul_of_nonneg_left hpositive
        (by norm_num)

private noncomputable def upperPositiveShellVariance (ε δ : ℝ) : ℝ :=
  ∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
    positiveShellDensity ε a * a ^ 2 *
      Real.cosh ((1 + δ) * a)

private theorem upperPositiveShellVariance_bounds
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) :
    (1 / 2 : ℝ) * (ε⁻¹ ^ 3) ^ 2 *
        shellWeight ε *
          Real.exp (δ * (ε⁻¹ ^ 3)) ≤
      upperPositiveShellVariance ε δ ∧
    upperPositiveShellVariance ε δ ≤
      ((ε⁻¹ ^ 3) + 1) ^ 2 *
        shellWeight ε *
          Real.exp (δ * ((ε⁻¹ ^ 3) + 1)) := by
  let B : ℝ := (ε⁻¹ ^ 3)
  let lo : ℝ := (1 / 2 : ℝ) * B ^ 2 *
    shellWeight ε * Real.exp (δ * B)
  let hi : ℝ := (B + 1) ^ 2 *
    shellWeight ε * Real.exp (δ * (B + 1))
  have hB : 0 ≤ B := by
    try dsimp [B]
    positivity
  have hQ : 0 < shellWeight ε := shellWeight_pos ε
  have horder : B ≤ B + 1 := by linarith
  have hcont : Continuous (fun a : ℝ =>
      positiveShellDensity ε a * a ^ 2 *
        Real.cosh ((1 + δ) * a)) := by
    have hdensity := positiveShellDensity_continuous ε
    fun_prop
  have hlopoint :
      ∀ a ∈ Set.Icc B (B + 1),
        lo ≤ positiveShellDensity ε a * a ^ 2 *
          Real.cosh ((1 + δ) * a) := by
    intro a ha
    have ha0 : 0 ≤ a := hB.trans ha.1
    have hsquare : B ^ 2 ≤ a ^ 2 := by
      exact pow_le_pow_left₀ hB ha.1 2
    have hratio :
        Real.exp (δ * B) / 2 ≤
          Real.cosh ((1 + δ) * a) /
            Real.cosh a := by
      calc
        Real.exp (δ * B) / 2 ≤
          Real.exp (δ * a) / 2 := by
            apply div_le_div_of_nonneg_right
              (Real.exp_le_exp.mpr
                (mul_le_mul_of_nonneg_left ha.1 hδ))
              (by norm_num)
        _ ≤ Real.cosh ((1 + δ) * a) /
          Real.cosh a := cosh_ratio_lower ha0 hδ
    calc
      lo = shellWeight ε * B ^ 2 *
          (Real.exp (δ * B) / 2) := by
        try dsimp [lo]
        ring
      _ ≤ shellWeight ε * a ^ 2 *
          (Real.cosh ((1 + δ) * a) /
            Real.cosh a) := by
        gcongr
      _ = positiveShellDensity ε a * a ^ 2 *
          Real.cosh ((1 + δ) * a) := by
        unfold positiveShellDensity
        ring
  have hhipoint :
      ∀ a ∈ Set.Icc B (B + 1),
        positiveShellDensity ε a * a ^ 2 *
          Real.cosh ((1 + δ) * a) ≤ hi := by
    intro a ha
    have ha0 : 0 ≤ a := hB.trans ha.1
    have hsquare : a ^ 2 ≤ (B + 1) ^ 2 := by
      exact pow_le_pow_left₀ ha0 ha.2 2
    have hratio :
        Real.cosh ((1 + δ) * a) /
          Real.cosh a ≤
            Real.exp (δ * (B + 1)) :=
      (cosh_ratio_upper ha0 hδ).trans
        (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left ha.2 hδ))
    calc
      positiveShellDensity ε a * a ^ 2 *
          Real.cosh ((1 + δ) * a) =
        shellWeight ε * a ^ 2 *
          (Real.cosh ((1 + δ) * a) /
            Real.cosh a) := by
        unfold positiveShellDensity
        ring
      _ ≤ shellWeight ε * (B + 1) ^ 2 *
          Real.exp (δ * (B + 1)) := by
        gcongr
      _ = hi := by
        try dsimp [hi]
        ring
  have hlower := intervalIntegral.integral_mono_on
    (μ := volume) horder
    ((continuous_const : Continuous
      (fun _ : ℝ => lo)).intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _)
    hlopoint
  have hupper := intervalIntegral.integral_mono_on
    (μ := volume) horder
    (hcont.intervalIntegrable _ _)
    ((continuous_const : Continuous
      (fun _ : ℝ => hi)).intervalIntegrable _ _)
    hhipoint
  change lo ≤ upperPositiveShellVariance ε δ ∧
    upperPositiveShellVariance ε δ ≤ hi
  constructor
  · simpa only [upperPositiveShellVariance, intervalIntegral.integral_const,
    add_sub_cancel_left, smul_eq_mul,
      one_mul] using! hlower
  · simpa only [upperPositiveShellVariance, intervalIntegral.integral_const,
    add_sub_cancel_left, smul_eq_mul,
      one_mul] using! hupper

private noncomputable def upperShortShellVariance (ε δ : ℝ) : ℝ :=
  ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
    (-shortShellDensity ε a) * a ^ 2 *
      Real.cosh ((1 + δ) * a)

private theorem upper_shortShellDensity_variance_le
    {ε δ a A : ℝ}
    (hε : 0 < ε) (hδ : 0 ≤ δ)
    (ha : 0 < a) (haA : a ≤ A) :
    (-shortShellDensity ε a) * a ^ 2 *
        Real.cosh ((1 + δ) * a) ≤
      (1 / 2 : ℝ) * Real.exp (δ * A) := by
  have hmargin : (1 - 10 * ε * (1 + a)) ≤ 1 := by
    linarith [mul_nonneg hε.le
      (show 0 ≤ 1 + a by linarith)]
  have hexp : Real.exp (-2 * a) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hratio :
      Real.cosh ((1 + δ) * a) / Real.cosh a ≤
        Real.exp (δ * A) :=
    (cosh_ratio_upper ha.le hδ).trans
      (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left haA hδ))
  have hidentity :
      (-shortShellDensity ε a) * a ^ 2 *
        Real.cosh ((1 + δ) * a) =
          (1 / 2 : ℝ) * (1 - 10 * ε * (1 + a)) *
            Real.exp (-2 * a) *
              (Real.cosh ((1 + δ) * a) /
                Real.cosh a) := by
    unfold shortShellDensity
    field_simp [ha.ne', (Real.cosh_pos a).ne']
  rw [hidentity]
  calc
    (1 / 2 : ℝ) * (1 - 10 * ε * (1 + a)) *
        Real.exp (-2 * a) *
          (Real.cosh ((1 + δ) * a) /
            Real.cosh a) ≤
      (1 / 2 : ℝ) * 1 * 1 *
        Real.exp (δ * A) := by
      gcongr
    _ = (1 / 2 : ℝ) * Real.exp (δ * A) := by
      ring

private theorem upperShortShellVariance_global_bound
    {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 ≤ δ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    upperShortShellVariance ε δ ≤
      (1 / 2 : ℝ) * upperShellShortCoefficient ε *
        Real.exp (δ * (10 * Real.log (1 / ε))) := by
  let a₀ : ℝ := (ε ^ 3)
  let A : ℝ := (10 * Real.log (1 / ε))
  let K : ℝ := (1 / 2 : ℝ) * Real.exp (δ * A)
  have ha₀ : 0 < a₀ := by
    try dsimp [a₀]
    positivity
  have hA : 0 < A := ha₀.trans_le horder
  have hK : 0 ≤ K := by
    try dsimp [K]
    positivity
  have hshort :
      ContinuousOn (shortShellDensity ε) (Set.Icc a₀ A) := by
    have hn : Continuous (fun a : ℝ =>
      (1 - 10 * ε * (1 + a)) * Real.exp (-2 * a)) := by
      fun_prop
    have hd : Continuous (fun a : ℝ =>
      2 * a ^ 2 * Real.cosh a) := by
      fun_prop
    unfold shortShellDensity
    apply (hn.continuousOn.div hd.continuousOn ?_).neg
    intro a ha
    have hapos : 0 < a := ha₀.trans_le ha.1
    positivity
  have hcosh : Continuous
      (fun a : ℝ => Real.cosh ((1 + δ) * a)) := by
    fun_prop
  have hleft : ContinuousOn
      (fun a : ℝ =>
        (-shortShellDensity ε a) * a ^ 2 *
          Real.cosh ((1 + δ) * a))
        (Set.Icc a₀ A) :=
    (hshort.neg.mul
      (continuous_id.pow 2).continuousOn).mul
        hcosh.continuousOn
  have hpoint :
      ∀ a ∈ Set.Icc a₀ A,
        (-shortShellDensity ε a) * a ^ 2 *
          Real.cosh ((1 + δ) * a) ≤ K := by
    intro a ha
    exact upper_shortShellDensity_variance_le hε hδ
      (ha₀.trans_le ha.1) ha.2
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) horder
    (hleft.intervalIntegrable_of_Icc horder)
    ((continuous_const : Continuous
      (fun _ : ℝ => K)).intervalIntegrable _ _)
    hpoint
  have hinv : 0 ≤ a₀⁻¹ := (inv_pos.mpr ha₀).le
  change
    (∫ a in a₀..A,
      (-shortShellDensity ε a) * a ^ 2 *
        Real.cosh ((1 + δ) * a)) ≤
      (1 / 2 : ℝ) * upperShellShortCoefficient ε *
        Real.exp (δ * A)
  calc
    (∫ a in a₀..A,
      (-shortShellDensity ε a) * a ^ 2 *
        Real.cosh ((1 + δ) * a)) ≤
      (A - a₀) * K := by
        simpa only [neg_mul, intervalIntegral.integral_neg, intervalIntegral.integral_const,
          smul_eq_mul] using! hmono
    _ ≤ (A + a₀⁻¹) * K := by
      apply mul_le_mul_of_nonneg_right _ hK
      linarith
    _ = (1 / 2 : ℝ) * upperShellShortCoefficient ε *
        Real.exp (δ * A) := by
      unfold upperShellShortCoefficient
      try dsimp [A, a₀, K]
      ring

private theorem upperShortShellVariance_nonneg
    {ε δ : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Set.Icc (ε ^ 3)
      (10 * Real.log (1 / ε)), 0 ≤ (1 - 10 * ε * (1 + a))) :
    0 ≤ upperShortShellVariance ε δ := by
  unfold upperShortShellVariance
  apply intervalIntegral.integral_nonneg horder
  intro a ha
  have ha₀ : 0 < (ε ^ 3) := by
    positivity
  have hapos : 0 < a := ha₀.trans_le ha.1
  have hdensity : 0 ≤ -shortShellDensity ε a := by
    unfold shortShellDensity
    have hn : 0 ≤ (1 - 10 * ε * (1 + a)) * Real.exp (-2 * a) :=
      mul_nonneg (hmargin a ha) (Real.exp_pos _).le
    have hd : 0 < 2 * a ^ 2 * Real.cosh a := by
      positivity
    simpa only [neg_mul, neg_neg, ge_iff_le] using! div_nonneg hn hd.le
  exact mul_nonneg
    (mul_nonneg hdensity (sq_nonneg a))
    (Real.cosh_pos _).le

private theorem upper_shellLocation_one_le
    {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) :
    1 ≤ (ε⁻¹ ^ 3) := by
  have hinv : 1 ≤ ε⁻¹ :=
    (one_le_inv₀ hε).mpr hεone
  convert! pow_le_pow_left₀
    (show (0 : ℝ) ≤ 1 by norm_num) hinv 3 using 1; norm_num

private theorem eventually_upper_shortShellVariance_domination :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ δ : ℝ, ε / 2 ≤ δ →
        upperShortShellVariance ε δ ≤
          (1 / 100 : ℝ) *
            upperPositiveShellVariance ε δ := by
  have hsmall :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 1 :=
    (tendsto_id.mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards
    [self_mem_nhdsWithin, hsmall,
      eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_upper_shellLocation_gt_shortEndpoint,
      eventually_upper_shell_parameter_margin]
    with ε hε hεone horder hseparation hmargin
  change 0 < ε at hε
  intro δ hδ
  have hδnonneg : 0 ≤ δ := by
    linarith
  have hB : 1 ≤ (ε⁻¹ ^ 3) :=
    upper_shellLocation_one_le hε hεone.le
  have hBsq : 1 ≤ (ε⁻¹ ^ 3) ^ 2 := by
    linarith [sq_nonneg ((ε⁻¹ ^ 3) - 1)]
  have hpropagate :=
    upper_shell_parameter_margin_propagate
      hδ (by linarith [hseparation]) hmargin
  have hvariance :=
    upperShortShellVariance_global_bound
      hε hδnonneg horder
  have hpositive :=
    (upperPositiveShellVariance_bounds hε hδnonneg).1
  have hqexp :
      0 ≤ shellWeight ε *
        Real.exp (δ * (ε⁻¹ ^ 3)) :=
    mul_nonneg (shellWeight_pos ε).le
      (Real.exp_pos _).le
  calc
    upperShortShellVariance ε δ ≤
      (1 / 2 : ℝ) * upperShellShortCoefficient ε *
        Real.exp (δ * (10 * Real.log (1 / ε))) := hvariance
    _ ≤ (1 / 2 : ℝ) *
        ((1 / 5000 : ℝ) * shellWeight ε *
          Real.exp (δ * (ε⁻¹ ^ 3))) := by
      convert! mul_le_mul_of_nonneg_left
        hpropagate (by norm_num : (0 : ℝ) ≤ 1 / 2)
        using 1; ring
    _ ≤ (1 / 100 : ℝ) *
        ((1 / 2 : ℝ) * (ε⁻¹ ^ 3) ^ 2 *
          shellWeight ε *
            Real.exp (δ * (ε⁻¹ ^ 3))) := by
      have hscaled :=
        mul_le_mul_of_nonneg_right hBsq hqexp
      linarith
    _ ≤ (1 / 100 : ℝ) *
        upperPositiveShellVariance ε δ :=
      mul_le_mul_of_nonneg_left hpositive
        (by norm_num)

private noncomputable def upperNetShellVariance (ε δ : ℝ) : ℝ :=
  upperPositiveShellVariance ε δ -
    upperShortShellVariance ε δ

private theorem eventually_upper_netShellVariance_bounds :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ δ : ℝ, ε / 2 ≤ δ →
        (99 / 100 : ℝ) *
            upperPositiveShellVariance ε δ ≤
          upperNetShellVariance ε δ ∧
        upperNetShellVariance ε δ ≤
          upperPositiveShellVariance ε δ := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_upper_shortMargin_positive,
      eventually_upper_shortShellVariance_domination]
    with ε hε horder hmargin hdom
  change 0 < ε at hε
  intro δ hδ
  have hnonneg := upperShortShellVariance_nonneg
    (δ := δ) hε horder
    (fun a ha => by
      have h := hmargin a ha
      linarith)
  have hupper := hdom δ hδ
  unfold upperNetShellVariance
  constructor <;> linarith

private noncomputable def upperPositiveShellThirdMoment (ε δ : ℝ) : ℝ :=
  ∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
    positiveShellDensity ε a * a ^ 3 *
      Real.cosh ((1 + δ) * a)

private theorem upperPositiveShellThirdMoment_le
    {ε δ : ℝ} (hε : 0 < ε) :
    upperPositiveShellThirdMoment ε δ ≤
      ((ε⁻¹ ^ 3) + 1) *
        upperPositiveShellVariance ε δ := by
  let B : ℝ := (ε⁻¹ ^ 3)
  have hB : 0 ≤ B := by
    try dsimp [B]
    positivity
  have horder : B ≤ B + 1 := by
    linarith
  have hdensity := positiveShellDensity_continuous ε
  have hbase : Continuous (fun a : ℝ =>
      positiveShellDensity ε a * a ^ 2 *
        Real.cosh ((1 + δ) * a)) := by
    fun_prop
  have hthird : Continuous (fun a : ℝ =>
      positiveShellDensity ε a * a ^ 3 *
        Real.cosh ((1 + δ) * a)) := by
    fun_prop
  have hright : Continuous (fun a : ℝ =>
      (B + 1) *
        (positiveShellDensity ε a * a ^ 2 *
          Real.cosh ((1 + δ) * a))) :=
    continuous_const.mul hbase
  have hpoint :
      ∀ a ∈ Set.Icc B (B + 1),
        positiveShellDensity ε a * a ^ 3 *
            Real.cosh ((1 + δ) * a) ≤
          (B + 1) *
            (positiveShellDensity ε a * a ^ 2 *
              Real.cosh ((1 + δ) * a)) := by
    intro a ha
    have hdensitynonneg : 0 ≤ positiveShellDensity ε a := by
      unfold positiveShellDensity
      exact div_nonneg (shellWeight_pos ε).le
        (Real.cosh_pos a).le
    have hbasenonneg :
        0 ≤ positiveShellDensity ε a * a ^ 2 *
          Real.cosh ((1 + δ) * a) :=
      mul_nonneg
        (mul_nonneg hdensitynonneg (sq_nonneg a))
        (Real.cosh_pos _).le
    calc
      positiveShellDensity ε a * a ^ 3 *
          Real.cosh ((1 + δ) * a) =
        a * (positiveShellDensity ε a * a ^ 2 *
          Real.cosh ((1 + δ) * a)) := by
            ring
      _ ≤ (B + 1) *
          (positiveShellDensity ε a * a ^ 2 *
            Real.cosh ((1 + δ) * a)) :=
        mul_le_mul_of_nonneg_right ha.2 hbasenonneg
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) horder
    (hthird.intervalIntegrable _ _)
    (hright.intervalIntegrable _ _)
    hpoint
  simpa only [upperPositiveShellThirdMoment, upperPositiveShellVariance, ge_iff_le,
    intervalIntegral.integral_const_mul] using! hmono

private noncomputable def upperShortShellThirdMoment (ε δ : ℝ) : ℝ :=
  ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
    (-shortShellDensity ε a) * a ^ 3 *
      Real.cosh ((1 + δ) * a)

private theorem upperShortShellThirdMoment_le
    {ε δ : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Set.Icc (ε ^ 3)
      (10 * Real.log (1 / ε)), 0 ≤ (1 - 10 * ε * (1 + a))) :
    upperShortShellThirdMoment ε δ ≤
      (10 * Real.log (1 / ε)) * upperShortShellVariance ε δ := by
  let a₀ : ℝ := (ε ^ 3)
  let A : ℝ := (10 * Real.log (1 / ε))
  have ha₀ : 0 < a₀ := by
    try dsimp [a₀]
    positivity
  have hshort :
      ContinuousOn (shortShellDensity ε) (Set.Icc a₀ A) := by
    have hn : Continuous (fun a : ℝ =>
      (1 - 10 * ε * (1 + a)) * Real.exp (-2 * a)) := by
      fun_prop
    have hd : Continuous (fun a : ℝ =>
      2 * a ^ 2 * Real.cosh a) := by
      fun_prop
    unfold shortShellDensity
    apply (hn.continuousOn.div hd.continuousOn ?_).neg
    intro a ha
    have hapos : 0 < a := ha₀.trans_le ha.1
    positivity
  have hcosh : Continuous
      (fun a : ℝ => Real.cosh ((1 + δ) * a)) := by
    fun_prop
  have hbase : ContinuousOn (fun a : ℝ =>
      (-shortShellDensity ε a) * a ^ 2 *
        Real.cosh ((1 + δ) * a)) (Set.Icc a₀ A) :=
    (hshort.neg.mul
      (continuous_id.pow 2).continuousOn).mul
        hcosh.continuousOn
  have hthird : ContinuousOn (fun a : ℝ =>
      (-shortShellDensity ε a) * a ^ 3 *
        Real.cosh ((1 + δ) * a)) (Set.Icc a₀ A) :=
    (hshort.neg.mul
      (continuous_id.pow 3).continuousOn).mul
        hcosh.continuousOn
  have hright : ContinuousOn (fun a : ℝ =>
      A * ((-shortShellDensity ε a) * a ^ 2 *
        Real.cosh ((1 + δ) * a))) (Set.Icc a₀ A) :=
    continuousOn_const.mul hbase
  have hpoint :
      ∀ a ∈ Set.Icc a₀ A,
        (-shortShellDensity ε a) * a ^ 3 *
            Real.cosh ((1 + δ) * a) ≤
          A * ((-shortShellDensity ε a) * a ^ 2 *
            Real.cosh ((1 + δ) * a)) := by
    intro a ha
    have hapos : 0 < a := ha₀.trans_le ha.1
    have hmargin' : 0 ≤ (1 - 10 * ε * (1 + a)) := by
      apply hmargin
      exact ha
    have hdensity : 0 ≤ -shortShellDensity ε a := by
      unfold shortShellDensity
      have hn : 0 ≤ (1 - 10 * ε * (1 + a)) * Real.exp (-2 * a) :=
        mul_nonneg hmargin' (Real.exp_pos _).le
      have hd : 0 < 2 * a ^ 2 * Real.cosh a := by
        positivity
      simpa only [neg_mul, neg_neg, ge_iff_le] using! div_nonneg hn hd.le
    have hbasenonneg :
        0 ≤ (-shortShellDensity ε a) * a ^ 2 *
          Real.cosh ((1 + δ) * a) :=
      mul_nonneg
        (mul_nonneg hdensity (sq_nonneg a))
        (Real.cosh_pos _).le
    calc
      (-shortShellDensity ε a) * a ^ 3 *
          Real.cosh ((1 + δ) * a) =
        a * ((-shortShellDensity ε a) * a ^ 2 *
          Real.cosh ((1 + δ) * a)) := by
            ring
      _ ≤ A *
          ((-shortShellDensity ε a) * a ^ 2 *
            Real.cosh ((1 + δ) * a)) :=
        mul_le_mul_of_nonneg_right ha.2 hbasenonneg
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) horder
    (hthird.intervalIntegrable_of_Icc horder)
    (hright.intervalIntegrable_of_Icc horder)
    hpoint
  simpa only [upperShortShellThirdMoment, neg_mul, intervalIntegral.integral_neg,
    upperShortShellVariance,
    mul_neg, neg_le_neg_iff, ge_iff_le, intervalIntegral.integral_const_mul] using! hmono

private theorem eventually_upper_shortShellThirdMoment_domination :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ δ : ℝ, ε / 2 ≤ δ →
        upperShortShellThirdMoment ε δ ≤
          ((10 * Real.log (1 / ε)) / 100) *
            upperPositiveShellVariance ε δ := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_upper_shortMargin_positive,
      eventually_upper_shortShellVariance_domination]
    with ε hε horder hmargin hdom
  change 0 < ε at hε
  intro δ hδ
  have ha₀ : 0 < (ε ^ 3) := by
    positivity
  have hA : 0 ≤ (10 * Real.log (1 / ε)) :=
    (ha₀.trans_le horder).le
  have hthird := upperShortShellThirdMoment_le
    (δ := δ) hε horder
    (fun a ha => by
      have h := hmargin a ha
      linarith)
  calc
    upperShortShellThirdMoment ε δ ≤
      (10 * Real.log (1 / ε)) * upperShortShellVariance ε δ := hthird
    _ ≤ (10 * Real.log (1 / ε)) *
      ((1 / 100 : ℝ) *
        upperPositiveShellVariance ε δ) :=
      mul_le_mul_of_nonneg_left (hdom δ hδ) hA
    _ = ((10 * Real.log (1 / ε)) / 100) *
      upperPositiveShellVariance ε δ := by
        ring

private noncomputable def upperNetShellThirdMoment (ε δ : ℝ) : ℝ :=
  upperPositiveShellThirdMoment ε δ +
    upperShortShellThirdMoment ε δ

private theorem eventually_upper_netShellThirdMoment_bound :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ δ : ℝ, ε / 2 ≤ δ →
        upperNetShellThirdMoment ε δ ≤
          ((ε⁻¹ ^ 3) + 1 + (10 * Real.log (1 / ε)) / 100) *
            upperPositiveShellVariance ε δ := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_upper_shortShellThirdMoment_domination]
    with ε hε hshort
  change 0 < ε at hε
  intro δ hδ
  have hpositive := upperPositiveShellThirdMoment_le
    (δ := δ) hε
  have hnegative := hshort δ hδ
  unfold upperNetShellThirdMoment
  linarith

private theorem upper_inv_one_sub_exp_neg_bounds
    {x : ℝ} (hx : 0 < x) :
    x⁻¹ ≤ (1 - Real.exp (-x))⁻¹ ∧
      (1 - Real.exp (-x))⁻¹ ≤ 1 + x⁻¹ := by
  have hden : 0 < 1 - Real.exp (-x) := by
    have he : Real.exp (-x) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hlower : 1 - Real.exp (-x) ≤ x := by
    linarith [Real.add_one_le_exp (-x)]
  have hplus : 0 < 1 + x := by
    linarith
  have hexp : Real.exp (-x) ≤ (1 + x)⁻¹ := by
    rw [Real.exp_neg]
    apply (inv_le_inv₀ (Real.exp_pos x) hplus).2
    linarith [Real.add_one_le_exp x]
  constructor
  · exact (inv_le_inv₀ hx hden).2 hlower
  · have hgoal :
        1 / (1 - Real.exp (-x)) ≤ 1 + x⁻¹ := by
      apply (div_le_iff₀ hden).2
      have hfactor : 0 ≤ 1 + x⁻¹ := by
        positivity
      calc
        (1 : ℝ) =
            (1 + x⁻¹) * (1 - (1 + x)⁻¹) := by
              field_simp [hx.ne', hplus.ne']; ring
        _ ≤ (1 + x⁻¹) * (1 - Real.exp (-x)) :=
          mul_le_mul_of_nonneg_left
            (sub_le_sub_left hexp 1) hfactor
    simpa only [ge_iff_le, one_div] using! hgoal

private noncomputable def upperGammaMeasureDensity (ℓ η a : ℝ) : ℝ :=
  Real.exp (-η * a) /
    (a * (1 - Real.exp (-(2 * a / ℓ))))

private theorem upper_laplace_monomial_integrable
    {η : ℝ} (hη : 0 < η) (k : ℕ) :
    IntegrableOn
      (fun a : ℝ => a ^ k * Real.exp (-η * a))
      (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (k : ℝ)) (b := η)
    (by exact_mod_cast (show (-(1 : ℤ) < (k : ℤ)) by omega))
    (by norm_num) hη
  apply h.congr_fun _ measurableSet_Ioi
  intro a ha
  simp only [Real.rpow_natCast, Real.rpow_one, neg_mul]

/-- Evaluates a monomial against a positive exponential Laplace weight. -/
public
theorem upper_laplace_monomial_integral
    {η : ℝ} (hη : 0 < η) (k : ℕ) :
    (∫ a : ℝ in Set.Ioi 0,
      a ^ k * Real.exp (-η * a)) =
        (k.factorial : ℝ) / η ^ (k + 1) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by
    positivity
  calc
    (∫ a : ℝ in Set.Ioi 0,
      a ^ k * Real.exp (-η * a)) =
        ∫ a : ℝ in Set.Ioi 0,
          a ^ ((k : ℝ) + 1 - 1) *
            Real.exp (-(η * a)) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro a ha
              change a ^ k * Real.exp (-η * a) =
                a ^ ((k : ℝ) + 1 - 1) *
                  Real.exp (-(η * a))
              rw [show (k : ℝ) + 1 - 1 = (k : ℝ) by ring,
                Real.rpow_natCast]
              congr 1
              ring_nf
    _ = (1 / η) ^ ((k : ℝ) + 1) *
          Real.Gamma ((k : ℝ) + 1) :=
      Real.integral_rpow_mul_exp_neg_mul_Ioi hk hη
    _ = (k.factorial : ℝ) / η ^ (k + 1) := by
      rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by
        norm_num, Real.rpow_natCast]
      rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by
        push_cast; ring, Real.Gamma_nat_eq_factorial]
      simp only [div_eq_mul_inv, mul_comm, mul_one, inv_pow]

private theorem upperGammaVarianceDensity_pointwise_bounds
    {ℓ η a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) :
    (ℓ / 2) * Real.exp (-η * a) ≤
      a ^ 2 * upperGammaMeasureDensity ℓ η a ∧
    a ^ 2 * upperGammaMeasureDensity ℓ η a ≤
      (a + ℓ / 2) * Real.exp (-η * a) := by
  let x : ℝ := 2 * a / ℓ
  have hx : 0 < x := by
    try dsimp [x]
    positivity
  have hkernel := upper_inv_one_sub_exp_neg_bounds hx
  have hden : 0 < 1 - Real.exp (-x) := by
    have he : Real.exp (-x) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hfactor : 0 ≤ a * Real.exp (-η * a) := by
    positivity
  have hidentity :
      a ^ 2 * upperGammaMeasureDensity ℓ η a =
        a * Real.exp (-η * a) *
          (1 - Real.exp (-x))⁻¹ := by
    unfold upperGammaMeasureDensity
    try dsimp [x]
    field_simp [ha.ne', hℓ.ne', hden.ne']
  constructor
  · calc
      (ℓ / 2) * Real.exp (-η * a) =
          a * Real.exp (-η * a) * x⁻¹ := by
            try dsimp [x]
            field_simp [ha.ne', hℓ.ne']
      _ ≤ a * Real.exp (-η * a) *
          (1 - Real.exp (-x))⁻¹ :=
        mul_le_mul_of_nonneg_left hkernel.1 hfactor
      _ = a ^ 2 * upperGammaMeasureDensity ℓ η a :=
        hidentity.symm
  · calc
      a ^ 2 * upperGammaMeasureDensity ℓ η a =
          a * Real.exp (-η * a) *
            (1 - Real.exp (-x))⁻¹ := hidentity
      _ ≤ a * Real.exp (-η * a) * (1 + x⁻¹) :=
        mul_le_mul_of_nonneg_left hkernel.2 hfactor
      _ = (a + ℓ / 2) * Real.exp (-η * a) := by
        try dsimp [x]
        field_simp [ha.ne', hℓ.ne']

private theorem upperGammaThirdMomentDensity_pointwise_bounds
    {ℓ η a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) :
    (ℓ / 2) * a * Real.exp (-η * a) ≤
      a ^ 3 * upperGammaMeasureDensity ℓ η a ∧
    a ^ 3 * upperGammaMeasureDensity ℓ η a ≤
      (a ^ 2 + (ℓ / 2) * a) *
        Real.exp (-η * a) := by
  obtain ⟨hlower, hupper⟩ :=
    upperGammaVarianceDensity_pointwise_bounds
      (η := η) hℓ ha
  have hlow := mul_le_mul_of_nonneg_left hlower ha.le
  have hupp := mul_le_mul_of_nonneg_left hupper ha.le
  constructor <;> linarith

private theorem upperGammaVarianceDensity_integrable
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) :
    IntegrableOn
      (fun a : ℝ => a ^ 2 * upperGammaMeasureDensity ℓ η a)
      (Set.Ioi 0) := by
  have hzero := upper_laplace_monomial_integrable hη 0
  have hone := upper_laplace_monomial_integrable hη 1
  have hsum := hone.add (hzero.const_mul (ℓ / 2))
  have hmajor : IntegrableOn
      (fun a : ℝ => (a + ℓ / 2) * Real.exp (-η * a))
      (Set.Ioi 0) := by
    apply hsum.congr_fun _ measurableSet_Ioi
    intro a ha
    change a ^ 1 * Real.exp (-η * a) +
      (ℓ / 2) * (a ^ 0 * Real.exp (-η * a)) =
        (a + ℓ / 2) * Real.exp (-η * a)
    simp only [pow_one, neg_mul, pow_zero, one_mul]
    ring
  have hmeas : Measurable
      (fun a : ℝ => a ^ 2 * upperGammaMeasureDensity ℓ η a) := by
    unfold upperGammaMeasureDensity
    fun_prop
  apply hmajor.mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi]
    with a ha
  have hbounds := upperGammaVarianceDensity_pointwise_bounds
    (η := η) hℓ ha
  have hpositive :
      0 ≤ a ^ 2 * upperGammaMeasureDensity ℓ η a :=
    (show 0 ≤ (ℓ / 2) * Real.exp (-η * a) by positivity).trans
      hbounds.1
  rw [Real.norm_eq_abs, abs_of_nonneg hpositive]
  exact hbounds.2

private theorem upperGammaThirdMomentDensity_integrable
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) :
    IntegrableOn
      (fun a : ℝ => a ^ 3 * upperGammaMeasureDensity ℓ η a)
      (Set.Ioi 0) := by
  have hone := upper_laplace_monomial_integrable hη 1
  have htwo := upper_laplace_monomial_integrable hη 2
  have hsum := htwo.add (hone.const_mul (ℓ / 2))
  have hmajor : IntegrableOn
      (fun a : ℝ =>
        (a ^ 2 + (ℓ / 2) * a) * Real.exp (-η * a))
      (Set.Ioi 0) := by
    apply hsum.congr_fun _ measurableSet_Ioi
    intro a ha
    change a ^ 2 * Real.exp (-η * a) +
      (ℓ / 2) * (a ^ 1 * Real.exp (-η * a)) =
        (a ^ 2 + (ℓ / 2) * a) * Real.exp (-η * a)
    simp only [neg_mul, pow_one]
    ring
  have hmeas : Measurable
      (fun a : ℝ => a ^ 3 * upperGammaMeasureDensity ℓ η a) := by
    unfold upperGammaMeasureDensity
    fun_prop
  apply hmajor.mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi]
    with a ha
  have hapos : 0 < a := ha
  have hbounds := upperGammaThirdMomentDensity_pointwise_bounds
    (η := η) hℓ hapos
  have hpositive :
      0 ≤ a ^ 3 * upperGammaMeasureDensity ℓ η a :=
    (show 0 ≤ (ℓ / 2) * a * Real.exp (-η * a) by
      positivity).trans hbounds.1
  rw [Real.norm_eq_abs, abs_of_nonneg hpositive]
  exact hbounds.2

private noncomputable def upperGammaVariance (ℓ η : ℝ) : ℝ :=
  ℓ⁻¹ * ∫ a : ℝ in Set.Ioi 0,
    a ^ 2 * upperGammaMeasureDensity ℓ η a

private noncomputable def upperGammaThirdMoment (ℓ η : ℝ) : ℝ :=
  ℓ⁻¹ * ∫ a : ℝ in Set.Ioi 0,
    a ^ 3 * upperGammaMeasureDensity ℓ η a

private theorem upperGammaVariance_bounds
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) :
    1 / (2 * η) ≤ upperGammaVariance ℓ η ∧
      upperGammaVariance ℓ η ≤
        1 / (2 * η) + 1 / (ℓ * η ^ 2) := by
  have hzero : IntegrableOn
      (fun a : ℝ => Real.exp (-η * a))
      (Set.Ioi 0) := by
    simpa only [neg_mul, pow_zero, one_mul] using! upper_laplace_monomial_integrable hη 0
  have hline : IntegrableOn
      (fun a : ℝ => a * Real.exp (-η * a))
      (Set.Ioi 0) := by
    simpa only [neg_mul, pow_one] using! upper_laplace_monomial_integrable hη 1
  have hconst : IntegrableOn
      (fun a : ℝ => (ℓ / 2) * Real.exp (-η * a))
      (Set.Ioi 0) :=
    hzero.const_mul (ℓ / 2)
  have hactual := upperGammaVarianceDensity_integrable hℓ hη
  have hmajor : IntegrableOn
      (fun a : ℝ => (a + ℓ / 2) * Real.exp (-η * a))
      (Set.Ioi 0) := by
    apply (hline.add hconst).congr_fun _ measurableSet_Ioi
    intro a ha
    change a * Real.exp (-η * a) +
      (ℓ / 2) * Real.exp (-η * a) =
        (a + ℓ / 2) * Real.exp (-η * a)
    ring
  have hlowerIntegral :
      (∫ a : ℝ in Set.Ioi 0,
        (ℓ / 2) * Real.exp (-η * a)) ≤
        ∫ a : ℝ in Set.Ioi 0,
          a ^ 2 * upperGammaMeasureDensity ℓ η a := by
    apply integral_mono_ae hconst hactual
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    exact (upperGammaVarianceDensity_pointwise_bounds
      (η := η) hℓ ha).1
  have hupperIntegral :
      (∫ a : ℝ in Set.Ioi 0,
        a ^ 2 * upperGammaMeasureDensity ℓ η a) ≤
        ∫ a : ℝ in Set.Ioi 0,
          (a + ℓ / 2) * Real.exp (-η * a) := by
    apply integral_mono_ae hactual hmajor
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    exact (upperGammaVarianceDensity_pointwise_bounds
      (η := η) hℓ ha).2
  have hzerovalue :
      (∫ a : ℝ in Set.Ioi 0,
        Real.exp (-η * a)) = η⁻¹ :=
    integral_laplaceKernel hη
  have hlinevalue :
      (∫ a : ℝ in Set.Ioi 0,
        a * Real.exp (-η * a)) = 1 / η ^ 2 := by
    simpa only [neg_mul, one_div, pow_one, Nat.factorial_one, Nat.cast_one,
      Nat.reduceAdd] using! upper_laplace_monomial_integral hη 1
  have hconstvalue :
      (∫ a : ℝ in Set.Ioi 0,
        (ℓ / 2) * Real.exp (-η * a)) =
          (ℓ / 2) * η⁻¹ := by
    rw [integral_const_mul, hzerovalue]
  have hmajorvalue :
      (∫ a : ℝ in Set.Ioi 0,
        (a + ℓ / 2) * Real.exp (-η * a)) =
          1 / η ^ 2 + (ℓ / 2) * η⁻¹ := by
    calc
      (∫ a : ℝ in Set.Ioi 0,
        (a + ℓ / 2) * Real.exp (-η * a)) =
          ∫ a : ℝ in Set.Ioi 0,
            (a * Real.exp (-η * a) +
              (ℓ / 2) * Real.exp (-η * a)) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro a ha
              ring
      _ = (∫ a : ℝ in Set.Ioi 0,
            a * Real.exp (-η * a)) +
          ∫ a : ℝ in Set.Ioi 0,
            (ℓ / 2) * Real.exp (-η * a) :=
        integral_add hline hconst
      _ = 1 / η ^ 2 + (ℓ / 2) * η⁻¹ := by
        rw [hlinevalue, hconstvalue]
  have hℓinv : 0 ≤ ℓ⁻¹ := (inv_pos.mpr hℓ).le
  unfold upperGammaVariance
  constructor
  · calc
      1 / (2 * η) =
          ℓ⁻¹ * ((ℓ / 2) * η⁻¹) := by
            field_simp [hℓ.ne', hη.ne']
      _ = ℓ⁻¹ *
          (∫ a : ℝ in Set.Ioi 0,
            (ℓ / 2) * Real.exp (-η * a)) := by
            rw [hconstvalue]
      _ ≤ ℓ⁻¹ *
          (∫ a : ℝ in Set.Ioi 0,
            a ^ 2 * upperGammaMeasureDensity ℓ η a) :=
        mul_le_mul_of_nonneg_left hlowerIntegral hℓinv
  · calc
      ℓ⁻¹ *
          (∫ a : ℝ in Set.Ioi 0,
            a ^ 2 * upperGammaMeasureDensity ℓ η a) ≤
        ℓ⁻¹ *
          (∫ a : ℝ in Set.Ioi 0,
            (a + ℓ / 2) * Real.exp (-η * a)) :=
        mul_le_mul_of_nonneg_left hupperIntegral hℓinv
      _ = ℓ⁻¹ *
          (1 / η ^ 2 + (ℓ / 2) * η⁻¹) := by
            rw [hmajorvalue]
      _ = 1 / (2 * η) + 1 / (ℓ * η ^ 2) := by
            field_simp [hℓ.ne', hη.ne']; ring

private theorem upperGammaThirdMoment_bounds
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) :
    1 / (2 * η ^ 2) ≤ upperGammaThirdMoment ℓ η ∧
      upperGammaThirdMoment ℓ η ≤
        1 / (2 * η ^ 2) + 2 / (ℓ * η ^ 3) := by
  have hline : IntegrableOn
      (fun a : ℝ => a * Real.exp (-η * a))
      (Set.Ioi 0) := by
    simpa only [neg_mul, pow_one] using! upper_laplace_monomial_integrable hη 1
  have hquadratic : IntegrableOn
      (fun a : ℝ => a ^ 2 * Real.exp (-η * a))
      (Set.Ioi 0) :=
    upper_laplace_monomial_integrable hη 2
  have hconst : IntegrableOn
      (fun a : ℝ => (ℓ / 2) * a * Real.exp (-η * a))
      (Set.Ioi 0) := by
    have h : IntegrableOn
        (fun a : ℝ =>
          (ℓ / 2) * (a * Real.exp (-η * a)))
        (Set.Ioi 0) :=
      hline.const_mul (ℓ / 2)
    apply h.congr_fun _ measurableSet_Ioi
    intro a ha
    change (ℓ / 2) *
      (a * Real.exp (-η * a)) =
        (ℓ / 2) * a * Real.exp (-η * a)
    ring
  have hactual := upperGammaThirdMomentDensity_integrable hℓ hη
  have hmajor : IntegrableOn
      (fun a : ℝ =>
        (a ^ 2 + (ℓ / 2) * a) * Real.exp (-η * a))
      (Set.Ioi 0) := by
    apply (hquadratic.add hconst).congr_fun _ measurableSet_Ioi
    intro a ha
    change a ^ 2 * Real.exp (-η * a) +
      (ℓ / 2) * a * Real.exp (-η * a) =
        (a ^ 2 + (ℓ / 2) * a) * Real.exp (-η * a)
    ring
  have hlowerIntegral :
      (∫ a : ℝ in Set.Ioi 0,
        (ℓ / 2) * a * Real.exp (-η * a)) ≤
        ∫ a : ℝ in Set.Ioi 0,
          a ^ 3 * upperGammaMeasureDensity ℓ η a := by
    apply integral_mono_ae hconst hactual
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    exact (upperGammaThirdMomentDensity_pointwise_bounds
      (η := η) hℓ ha).1
  have hupperIntegral :
      (∫ a : ℝ in Set.Ioi 0,
        a ^ 3 * upperGammaMeasureDensity ℓ η a) ≤
        ∫ a : ℝ in Set.Ioi 0,
          (a ^ 2 + (ℓ / 2) * a) *
            Real.exp (-η * a) := by
    apply integral_mono_ae hactual hmajor
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    exact (upperGammaThirdMomentDensity_pointwise_bounds
      (η := η) hℓ ha).2
  have hlinevalue :
      (∫ a : ℝ in Set.Ioi 0,
        a * Real.exp (-η * a)) = 1 / η ^ 2 := by
    simpa only [neg_mul, one_div, pow_one, Nat.factorial_one, Nat.cast_one,
      Nat.reduceAdd] using! upper_laplace_monomial_integral hη 1
  have hquadraticvalue :
      (∫ a : ℝ in Set.Ioi 0,
        a ^ 2 * Real.exp (-η * a)) = 2 / η ^ 3 := by
    simpa only [neg_mul, Nat.factorial_two, Nat.cast_ofNat,
      Nat.reduceAdd] using! upper_laplace_monomial_integral hη 2
  have hconstvalue :
      (∫ a : ℝ in Set.Ioi 0,
        (ℓ / 2) * a * Real.exp (-η * a)) =
          (ℓ / 2) * (1 / η ^ 2) := by
    calc
      (∫ a : ℝ in Set.Ioi 0,
        (ℓ / 2) * a * Real.exp (-η * a)) =
          ∫ a : ℝ in Set.Ioi 0,
            (ℓ / 2) *
              (a * Real.exp (-η * a)) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro a ha
              ring
      _ = (ℓ / 2) *
          (∫ a : ℝ in Set.Ioi 0,
            a * Real.exp (-η * a)) := by
        rw [integral_const_mul]
      _ = (ℓ / 2) * (1 / η ^ 2) := by
        rw [hlinevalue]
  have hmajorvalue :
      (∫ a : ℝ in Set.Ioi 0,
        (a ^ 2 + (ℓ / 2) * a) * Real.exp (-η * a)) =
          2 / η ^ 3 + (ℓ / 2) * (1 / η ^ 2) := by
    calc
      (∫ a : ℝ in Set.Ioi 0,
        (a ^ 2 + (ℓ / 2) * a) * Real.exp (-η * a)) =
          ∫ a : ℝ in Set.Ioi 0,
            (a ^ 2 * Real.exp (-η * a) +
              (ℓ / 2) * a * Real.exp (-η * a)) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro a ha
              ring
      _ = (∫ a : ℝ in Set.Ioi 0,
            a ^ 2 * Real.exp (-η * a)) +
          ∫ a : ℝ in Set.Ioi 0,
            (ℓ / 2) * a * Real.exp (-η * a) :=
        integral_add hquadratic hconst
      _ = 2 / η ^ 3 + (ℓ / 2) * (1 / η ^ 2) := by
        rw [hquadraticvalue, hconstvalue]
  have hℓinv : 0 ≤ ℓ⁻¹ := (inv_pos.mpr hℓ).le
  unfold upperGammaThirdMoment
  constructor
  · calc
      1 / (2 * η ^ 2) =
          ℓ⁻¹ * ((ℓ / 2) * (1 / η ^ 2)) := by
            field_simp [hℓ.ne', hη.ne']
      _ = ℓ⁻¹ *
          (∫ a : ℝ in Set.Ioi 0,
            (ℓ / 2) * a * Real.exp (-η * a)) := by
            rw [hconstvalue]
      _ ≤ ℓ⁻¹ *
          (∫ a : ℝ in Set.Ioi 0,
            a ^ 3 * upperGammaMeasureDensity ℓ η a) :=
        mul_le_mul_of_nonneg_left hlowerIntegral hℓinv
  · calc
      ℓ⁻¹ *
          (∫ a : ℝ in Set.Ioi 0,
            a ^ 3 * upperGammaMeasureDensity ℓ η a) ≤
        ℓ⁻¹ *
          (∫ a : ℝ in Set.Ioi 0,
            (a ^ 2 + (ℓ / 2) * a) *
              Real.exp (-η * a)) :=
        mul_le_mul_of_nonneg_left hupperIntegral hℓinv
      _ = ℓ⁻¹ *
          (2 / η ^ 3 + (ℓ / 2) * (1 / η ^ 2)) := by
            rw [hmajorvalue]
      _ = 1 / (2 * η ^ 2) + 2 / (ℓ * η ^ 3) := by
            field_simp [hℓ.ne', hη.ne']; ring

private theorem plusPolynomial_negative_imaginary_residue
    (ε s : ℝ) :
    plusPolynomial ε
        (Complex.I * ((-(1 + s) : ℝ) : ℂ)) =
      (((ε / 4) - s * (2 + s) ^ 2 : ℝ) : ℂ) := by
  rw [plusPolynomial_imaginary]
  push_cast
  ring

private noncomputable def saddleShellDerivativeOne (ε : ℝ) : ℝ :=
  (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
    shortShellDensity ε a * a * Real.sinh a) +
  (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
    positiveShellDensity ε a * a * Real.sinh a)

private noncomputable def saddleSmallRadiusVariable (ε r : ℝ) : ℝ :=
  Real.pi * Real.exp (2 * saddleShellDerivativeOne ε) * r ^ 2

private noncomputable def plusSaddleSmallRadiusCoefficient
    (ε ℓ : ℝ) (n : ℕ) : ℝ :=
  Real.exp
      (ℓ *
        (realHyperbolicShellPhase ε
          (1 + 2 * (n : ℝ) / ℓ) -
            realHyperbolicShellPhase ε 1) -
        2 * (n : ℝ) * saddleShellDerivativeOne ε) *
    (((ε / 4) - (2 * (n : ℝ) / ℓ) *
        (2 + 2 * (n : ℝ) / ℓ) ^ 2) /
      (ε / 4))

private theorem plusSaddlePoleResidue_explicit_real
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) :
    plusSaddlePoleResidue ε ℓ n =
      ((2 * (-1 : ℝ) ^ n / (n.factorial : ℝ) *
        (Real.pi ^ (ℓ / 2 + (n : ℝ)) *
          Real.exp
            (ℓ * realHyperbolicShellPhase ε
              (1 + 2 * (n : ℝ) / ℓ))) *
        ((ε / 4) - (2 * (n : ℝ) / ℓ) *
          (2 + 2 * (n : ℝ) / ℓ) ^ 2) : ℝ) : ℂ) := by
  unfold plusSaddlePoleResidue
  rw [plusSaddleRegularMellinFactor_neg_even hℓ n,
    plusPolynomial_negative_imaginary_residue]
  push_cast
  ring

private theorem saddleSmallRadiusVariable_nonneg (ε r : ℝ) :
    0 ≤ saddleSmallRadiusVariable ε r := by
  unfold saddleSmallRadiusVariable
  positivity

private theorem saddleSmallRadiusVariable_neg_pow
    (ε r : ℝ) (n : ℕ) :
    (-saddleSmallRadiusVariable ε r) ^ n =
      (-1 : ℝ) ^ n * Real.pi ^ n *
        Real.exp (2 * saddleShellDerivativeOne ε) ^ n *
          r ^ (2 * n) := by
  calc
    (-saddleSmallRadiusVariable ε r) ^ n =
        ((-1 : ℝ) * Real.pi *
          Real.exp (2 * saddleShellDerivativeOne ε) *
            r ^ 2) ^ n := by
              congr 1
              unfold saddleSmallRadiusVariable
              ring
    _ = (-1 : ℝ) ^ n * Real.pi ^ n *
          Real.exp (2 * saddleShellDerivativeOne ε) ^ n *
            (r ^ 2) ^ n := by
              simp only [mul_pow]
    _ = (-1 : ℝ) ^ n * Real.pi ^ n *
          Real.exp (2 * saddleShellDerivativeOne ε) ^ n *
            r ^ (2 * n) := by
              rw [← pow_mul]

private theorem saddleSmallRadiusPhase_pole_factorization
    (ε ℓ : ℝ) (n : ℕ) :
    Real.exp
        (ℓ * realHyperbolicShellPhase ε
          (1 + 2 * (n : ℝ) / ℓ)) =
      Real.exp (ℓ * realHyperbolicShellPhase ε 1) *
        Real.exp (2 * saddleShellDerivativeOne ε) ^ n *
        Real.exp
          (ℓ *
            (realHyperbolicShellPhase ε
              (1 + 2 * (n : ℝ) / ℓ) -
                realHyperbolicShellPhase ε 1) -
            2 * (n : ℝ) * saddleShellDerivativeOne ε) := by
  let H : ℝ := saddleShellDerivativeOne ε
  let p : ℝ :=
    realHyperbolicShellPhase ε (1 + 2 * (n : ℝ) / ℓ)
  let p₀ : ℝ := realHyperbolicShellPhase ε 1
  have harg :
      ℓ * p =
        ℓ * p₀ + (n : ℝ) * (2 * H) +
          (ℓ * (p - p₀) - 2 * (n : ℝ) * H) := by
    ring
  change Real.exp (ℓ * p) =
    Real.exp (ℓ * p₀) * Real.exp (2 * H) ^ n *
      Real.exp (ℓ * (p - p₀) - 2 * (n : ℝ) * H)
  rw [harg, Real.exp_add, Real.exp_add,
    Real.exp_nat_mul]

private theorem plusSaddlePoleResidue_mul_pow_eq_smallCoefficient
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (n : ℕ) (r : ℝ) :
    plusSaddlePoleResidue ε ℓ n *
        ((r ^ (2 * n) : ℝ) : ℂ) =
      ((saddleOriginValue ε ℓ *
        ((-saddleSmallRadiusVariable ε r) ^ n /
          (n.factorial : ℝ)) *
        plusSaddleSmallRadiusCoefficient ε ℓ n : ℝ) : ℂ) := by
  have hb : (ε / 4) ≠ 0 := (div_pos hε four_pos).ne'
  have hfac : (n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero n)
  have hpi :
      Real.pi ^ (ℓ / 2 + (n : ℝ)) =
        Real.pi ^ (ℓ / 2) * Real.pi ^ n :=
    Real.rpow_add_natCast Real.pi_ne_zero (ℓ / 2) n
  have hphase := saddleSmallRadiusPhase_pole_factorization
    ε ℓ n
  have hy := saddleSmallRadiusVariable_neg_pow ε r n
  rw [plusSaddlePoleResidue_explicit_real hℓ n,
    ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  unfold saddleOriginValue plusSaddleSmallRadiusCoefficient
  rw [hpi, hphase, hy]
  field_simp [hb, hfac]

private theorem plusSaddleProfile_eq_small_radius_residue_series
    {ε ℓ r : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r) (N : ℕ) :
    plusSaddleProfile ε ℓ r =
      (saddleOriginValue ε ℓ : ℂ) *
        ((∑ n ∈ Finset.range (N + 1),
          (-saddleSmallRadiusVariable ε r) ^ n /
            (n.factorial : ℝ) *
              plusSaddleSmallRadiusCoefficient ε ℓ n : ℝ) : ℂ) +
      plusSaddleTaylorRemainder ε ℓ N r := by
  rw [plusSaddleProfile_eq_residue_sum_add_remainder
    hε hℓ horder hr N]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hterm :=
    plusSaddlePoleResidue_mul_pow_eq_smallCoefficient
      hε hℓ n r
  push_cast at hterm
  simpa only [mul_assoc] using! hterm

private theorem plusSaddleProfile_div_origin_eq_small_radius_residue_series
    {ε ℓ r : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r) (N : ℕ) :
    plusSaddleProfile ε ℓ r /
        (saddleOriginValue ε ℓ : ℂ) =
      ((∑ n ∈ Finset.range (N + 1),
        (-saddleSmallRadiusVariable ε r) ^ n /
          (n.factorial : ℝ) *
            plusSaddleSmallRadiusCoefficient ε ℓ n : ℝ) : ℂ) +
      plusSaddleTaylorRemainder ε ℓ N r /
        (saddleOriginValue ε ℓ : ℂ) := by
  have hzero : (saddleOriginValue ε ℓ : ℂ) ≠ 0 := by
    exact_mod_cast (saddleOriginValue_pos hε ℓ).ne'
  rw [plusSaddleProfile_eq_small_radius_residue_series
    hε hℓ horder hr N]
  field_simp [hzero]

private theorem realHyperbolicShellPhase_contDiff
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (n : WithTop ℕ∞) :
    ContDiff ℝ n (realHyperbolicShellPhase ε) := by
  have hcomplex : ContDiff ℝ n (mellinShellPhase ε) :=
    ((mellinShellPhase_analyticOnNhd hε horder).restrictScalars
      (𝕜 := ℝ)).contDiff
  have harg : ContDiff ℝ n
      (fun u : ℝ => Complex.I * (u : ℂ)) := by
    exact contDiff_const.mul Complex.ofRealCLM.contDiff
  have hphase : ContDiff ℝ n
      (fun u : ℝ =>
        mellinShellPhase ε (Complex.I * (u : ℂ))) := by
    simpa only [Function.comp_apply] using! hcomplex.comp harg
  have hre : ContDiff ℝ n
      (fun u : ℝ =>
        (mellinShellPhase ε (Complex.I * (u : ℂ))).re) := by
    simpa only [Function.comp_apply] using!
      Complex.reCLM.contDiff.comp hphase
  simpa only [mellinShellPhase_imaginary, Complex.ofReal_re] using! hre

private theorem realHyperbolicShellInterval_hasDerivAt
    (w : ℝ → ℝ) (hw : Continuous w)
    {a b : ℝ} (hab : a ≤ b) (u : ℝ) :
    HasDerivAt
      (fun v : ℝ => ∫ x in a..b,
        w x * (Real.cosh (x * v) - 1))
      (∫ x in a..b,
        w x * x * Real.sinh (x * u)) u := by
  let F : ℝ → ℝ → ℝ := fun v x =>
    w x * (Real.cosh (x * v) - 1)
  let F' : ℝ → ℝ → ℝ := fun v x =>
    w x * x * Real.sinh (x * v)
  have hF (v : ℝ) : Continuous (F v) := by
    try dsimp [F]
    exact hw.mul
      ((Real.continuous_cosh.comp
        (continuous_id.mul continuous_const)).sub continuous_const)
  have hF' (v : ℝ) : Continuous (F' v) := by
    try dsimp [F']
    exact (hw.mul continuous_id).mul
      (Real.continuous_sinh.comp
        (continuous_id.mul continuous_const))
  have hF'joint : Continuous (Function.uncurry F') := by
    try dsimp [F', Function.uncurry]
    exact ((hw.comp continuous_snd).mul continuous_snd).mul
      (Real.continuous_sinh.comp
        (continuous_snd.mul continuous_fst))
  have hderiv (x v : ℝ) :
      HasDerivAt (fun z : ℝ => F z x) (F' v x) v := by
    have hlinear : HasDerivAt
        (fun z : ℝ => x * z) x v := by
      simpa only [id_eq, mul_one] using! (hasDerivAt_id v).const_mul x
    have hcosh := (Real.hasDerivAt_cosh
      (x * v)).comp v hlinear
    simpa [F, F', mul_assoc, mul_left_comm,
      mul_comm] using! (hcosh.sub_const (1 : ℝ)).const_mul (w x)
  have hrewrite :
      (fun v : ℝ => ∫ x in a..b,
        w x * (Real.cosh (x * v) - 1)) =
      (fun v : ℝ => ∫ x in Set.Icc a b, F v x) := by
    funext v
    rw [intervalIntegral.integral_of_le hab,
      ← integral_Icc_eq_integral_Ioc]
  have hderivrewrite :
      (∫ x in a..b, w x * x * Real.sinh (x * u)) =
      (∫ x in Set.Icc a b, F' u x) := by
    rw [intervalIntegral.integral_of_le hab,
      ← integral_Icc_eq_integral_Ioc]
  rw [hrewrite, hderivrewrite]
  have hcompact :
      IsCompact (Metric.closedBall u 1 ×ˢ Set.Icc a b) :=
    (isCompact_closedBall u 1).prod isCompact_Icc
  obtain ⟨C, hC⟩ :=
    hcompact.bddAbove_image hF'joint.norm.continuousOn
  have hbound : ∀ᵐ x ∂volume.restrict (Set.Icc a b),
      ∀ v ∈ Metric.ball u 1, ‖F' v x‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    intro v hv
    have hpair :
        (v, x) ∈ Metric.closedBall u 1 ×ˢ Set.Icc a b :=
      ⟨Metric.ball_subset_closedBall hv, hx⟩
    exact hC (Set.mem_image_of_mem
      (fun p : ℝ × ℝ => ‖F' p.1 p.2‖) hpair)
  have hmeas : ∀ᶠ v in 𝓝 u,
      AEStronglyMeasurable (F v)
        (volume.restrict (Set.Icc a b)) :=
    Eventually.of_forall (fun v => (hF v).aestronglyMeasurable)
  have hint : Integrable (F u)
      (volume.restrict (Set.Icc a b)) :=
    (hF u).integrableOn_Icc
  have hderivmeas : AEStronglyMeasurable (F' u)
      (volume.restrict (Set.Icc a b)) :=
    (hF' u).aestronglyMeasurable
  have hconstant : Integrable (fun _ : ℝ => C)
      (volume.restrict (Set.Icc a b)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hdifferentiable :
      ∀ᵐ x ∂volume.restrict (Set.Icc a b),
        ∀ v ∈ Metric.ball u 1,
          HasDerivAt (fun z : ℝ => F z x) (F' v x) v :=
    Eventually.of_forall (fun x v _ => hderiv x v)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Icc a b))
    (s := Metric.ball u 1) (bound := fun _ : ℝ => C)
    (Metric.ball_mem_nhds u zero_lt_one)
    hmeas hint hderivmeas hbound hconstant
    hdifferentiable).2

private theorem realHyperbolicShellPhase_hasDerivAt
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (u : ℝ) :
    HasDerivAt (realHyperbolicShellPhase ε)
      ((∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
          shortShellDensity ε a * a * Real.sinh (a * u)) +
       (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
          positiveShellDensity ε a * a * Real.sinh (a * u))) u := by
  have hcutoff : 0 < (ε ^ 3) := by
    positivity
  let w : ℝ → ℝ := fun a =>
    shortShellDensity ε (max a (ε ^ 3))
  have hmax (a : ℝ) : 0 < max a (ε ^ 3) :=
    hcutoff.trans_le (le_max_right _ _)
  have hw : Continuous w := by
    have hn : Continuous (fun a : ℝ =>
        (1 - 10 * ε * (1 + (max a (ε ^ 3)))) *
          Real.exp (-2 * max a (ε ^ 3))) := by
      fun_prop
    have hd : Continuous (fun a : ℝ =>
        2 * (max a (ε ^ 3)) ^ 2 *
          Real.cosh (max a (ε ^ 3))) := by
      fun_prop
    try dsimp [w]
    unfold shortShellDensity
    exact (hn.div hd (fun a => by positivity [hmax a])).neg
  have hshortfun :
      (fun v : ℝ => ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
        shortShellDensity ε a *
          (Real.cosh (a * v) - 1)) =
      (fun v : ℝ => ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
        w a * (Real.cosh (a * v) - 1)) := by
    funext v
    apply intervalIntegral.integral_congr
    intro a ha
    rw [uIcc_of_le horder] at ha
    try dsimp [w]
    rw [max_eq_left ha.1]
  have hshortderiv :
      (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
        shortShellDensity ε a * a * Real.sinh (a * u)) =
      (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
        w a * a * Real.sinh (a * u)) := by
    apply intervalIntegral.integral_congr
    intro a ha
    rw [uIcc_of_le horder] at ha
    try dsimp [w]
    rw [max_eq_left ha.1]
  have hshort :
      HasDerivAt
        (fun v : ℝ => ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
          shortShellDensity ε a *
            (Real.cosh (a * v) - 1))
        (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
          shortShellDensity ε a * a * Real.sinh (a * u)) u := by
    rw [hshortfun, hshortderiv]
    exact realHyperbolicShellInterval_hasDerivAt
      w hw horder u
  have hremote : (ε⁻¹ ^ 3) ≤ (ε⁻¹ ^ 3) + 1 := by
    linarith
  have hpositive := realHyperbolicShellInterval_hasDerivAt
    (positiveShellDensity ε)
    (positiveShellDensity_continuous ε) hremote u
  exact hshort.add hpositive

private theorem realHyperbolicShellPhase_hasDerivAt_one
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    HasDerivAt (realHyperbolicShellPhase ε)
      (saddleShellDerivativeOne ε) 1 := by
  simpa only [saddleShellDerivativeOne, mul_one] using!
    realHyperbolicShellPhase_hasDerivAt hε horder 1

private theorem exists_realHyperbolicShellPhase_quadratic_remainder
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc (1 : ℝ) 2,
      |realHyperbolicShellPhase ε x -
          realHyperbolicShellPhase ε 1 -
            (x - 1) * saddleShellDerivativeOne ε| ≤
        C * (x - 1) ^ 2 := by
  have hcont : ContDiffOn ℝ (2 : WithTop ℕ∞)
      (realHyperbolicShellPhase ε) (Set.Icc 1 2) :=
    (realHyperbolicShellPhase_contDiff
      hε horder (2 : WithTop ℕ∞)).contDiffOn
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound
    (f := realHyperbolicShellPhase ε)
    (n := 1) (by norm_num : (1 : ℝ) ≤ 2) hcont
  have hwithin :
      derivWithin (realHyperbolicShellPhase ε)
        (Set.Icc (1 : ℝ) 2) 1 =
          saddleShellDerivativeOne ε := by
    have hdwithin :
        HasDerivWithinAt (realHyperbolicShellPhase ε)
          (saddleShellDerivativeOne ε)
          (Set.Icc (1 : ℝ) 2) 1 :=
      HasDerivAt.hasDerivWithinAt
        (realHyperbolicShellPhase_hasDerivAt_one hε horder)
    exact HasDerivWithinAt.derivWithin hdwithin
      ((uniqueDiffOn_Icc (by norm_num : (1 : ℝ) < 2))
        1 (by constructor <;> norm_num))
  have htaylor (x : ℝ) :
      taylorWithinEval (realHyperbolicShellPhase ε)
          1 (Set.Icc (1 : ℝ) 2) 1 x =
        realHyperbolicShellPhase ε 1 +
          (x - 1) * saddleShellDerivativeOne ε := by
    simp only [taylorWithinEval_succ, taylor_within_zero_eval, CharP.cast_eq_zero, zero_add,
      Nat.factorial_zero,
      Nat.cast_one, mul_one, inv_one, pow_one, one_mul, iteratedDerivWithin_one, hwithin,
        smul_eq_mul]
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  have hxbound := hC x hx
  rw [htaylor x, Real.norm_eq_abs] at hxbound
  calc
    |realHyperbolicShellPhase ε x -
        realHyperbolicShellPhase ε 1 -
          (x - 1) * saddleShellDerivativeOne ε| =
      |realHyperbolicShellPhase ε x -
        (realHyperbolicShellPhase ε 1 +
          (x - 1) * saddleShellDerivativeOne ε)| := by
        congr 1
        ring
    _ ≤ C * (x - 1) ^ 2 := hxbound
    _ ≤ max C 0 * (x - 1) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (le_max_left _ _) (sq_nonneg _)

private theorem exists_plusSaddleSmallRadiusPhase_error
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ℓ : ℝ), 0 < ℓ →
        ∀ n : ℕ, 2 * (n : ℝ) ≤ ℓ →
          |ℓ *
              (realHyperbolicShellPhase ε
                (1 + 2 * (n : ℝ) / ℓ) -
                  realHyperbolicShellPhase ε 1) -
              2 * (n : ℝ) * saddleShellDerivativeOne ε| ≤
            C * (n : ℝ) ^ 2 / ℓ := by
  obtain ⟨C, hCnonneg, hC⟩ :=
    exists_realHyperbolicShellPhase_quadratic_remainder
      hε horder
  refine ⟨4 * C, by positivity, ?_⟩
  intro ℓ hℓ n hn
  let x : ℝ := 1 + 2 * (n : ℝ) / ℓ
  have hratio : 0 ≤ 2 * (n : ℝ) / ℓ := by
    positivity
  have hratioupper : 2 * (n : ℝ) / ℓ ≤ 1 :=
    (div_le_iff₀ hℓ).mpr (by simpa only [one_mul] using! hn)
  have hx : x ∈ Set.Icc (1 : ℝ) 2 := by
    constructor <;> dsimp [x] <;> linarith
  have hscale : ℓ * (x - 1) = 2 * (n : ℝ) := by
    try dsimp [x]
    field_simp; ring
  have hidentity :
      ℓ * (realHyperbolicShellPhase ε x -
        realHyperbolicShellPhase ε 1) -
          2 * (n : ℝ) * saddleShellDerivativeOne ε =
      ℓ * (realHyperbolicShellPhase ε x -
        realHyperbolicShellPhase ε 1 -
          (x - 1) * saddleShellDerivativeOne ε) := by
    rw [← hscale]
    ring
  change
    |ℓ * (realHyperbolicShellPhase ε x -
      realHyperbolicShellPhase ε 1) -
        2 * (n : ℝ) * saddleShellDerivativeOne ε| ≤
      (4 * C) * (n : ℝ) ^ 2 / ℓ
  calc
    |ℓ * (realHyperbolicShellPhase ε x -
        realHyperbolicShellPhase ε 1) -
          2 * (n : ℝ) * saddleShellDerivativeOne ε| =
      ℓ * |realHyperbolicShellPhase ε x -
        realHyperbolicShellPhase ε 1 -
          (x - 1) * saddleShellDerivativeOne ε| := by
        rw [hidentity, abs_mul, abs_of_pos hℓ]
    _ ≤ ℓ * (C * (x - 1) ^ 2) :=
      mul_le_mul_of_nonneg_left (hC x hx) hℓ.le
    _ = (4 * C) * (n : ℝ) ^ 2 / ℓ := by
      try dsimp [x]
      field_simp; ring

private theorem plusSaddleSmallRadiusPolynomial_error
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (n : ℕ) (hn : 2 * (n : ℝ) ≤ ℓ) :
    |(((ε / 4) - (2 * (n : ℝ) / ℓ) *
          (2 + 2 * (n : ℝ) / ℓ) ^ 2) /
        (ε / 4)) - 1| ≤
      (18 / (ε / 4)) * ((n : ℝ) / ℓ) := by
  have hb : 0 < (ε / 4) := div_pos hε four_pos
  let s : ℝ := 2 * (n : ℝ) / ℓ
  have hs : 0 ≤ s := by
    try dsimp [s]
    positivity
  have hsone : s ≤ 1 := by
    try dsimp [s]
    exact (div_le_iff₀ hℓ).mpr (by simpa only [one_mul] using! hn)
  have hsquare : (2 + s) ^ 2 ≤ 9 := by
    linarith [mul_nonneg
      (show 0 ≤ 3 - (2 + s) by linarith)
      (show 0 ≤ 3 + (2 + s) by linarith)]
  have hnumerator : 0 ≤ s * (2 + s) ^ 2 :=
    mul_nonneg hs (sq_nonneg _)
  change |((ε / 4) - s * (2 + s) ^ 2) /
      (ε / 4) - 1| ≤ (18 / (ε / 4)) *
        ((n : ℝ) / ℓ)
  have hid :
      ((ε / 4) - s * (2 + s) ^ 2) / (ε / 4) - 1 =
        -(s * (2 + s) ^ 2) / (ε / 4) := by
    field_simp; ring
  rw [hid, abs_div, abs_neg,
    abs_of_nonneg hnumerator, abs_of_pos hb]
  calc
    s * (2 + s) ^ 2 / (ε / 4) ≤
        s * 9 / (ε / 4) := by
          gcongr
    _ = (18 / (ε / 4)) * ((n : ℝ) / ℓ) := by
      try dsimp [s]
      field_simp; ring

private theorem abs_exp_sub_one_le_abs_mul_exp_abs (t : ℝ) :
    |Real.exp t - 1| ≤ |t| * Real.exp |t| := by
  rcases le_total 0 t with ht | ht
  · have hexp : 1 ≤ Real.exp t := by
      simpa only [Real.one_le_exp_iff, Real.exp_zero] using! Real.exp_le_exp.mpr ht
    rw [abs_of_nonneg (sub_nonneg.mpr hexp),
      abs_of_nonneg ht]
    have hsupport := Real.add_one_le_exp (-t)
    have hmul := mul_le_mul_of_nonneg_left hsupport
      (Real.exp_pos t).le
    have hcancel : Real.exp t * Real.exp (-t) = 1 := by
      rw [← Real.exp_add]
      simp only [add_neg_cancel, Real.exp_zero]
    rw [hcancel] at hmul
    linarith
  · have hexp : Real.exp t ≤ 1 := by
      simpa only [Real.exp_le_one_iff, Real.exp_zero] using! Real.exp_le_exp.mpr ht
    have hnegt : 0 ≤ -t := neg_nonneg.mpr ht
    have hexpneg : 1 ≤ Real.exp (-t) := by
      simpa only [Real.one_le_exp_iff, Left.nonneg_neg_iff,
        Real.exp_zero] using! Real.exp_le_exp.mpr hnegt
    rw [abs_of_nonpos (sub_nonpos.mpr hexp),
      abs_of_nonpos ht]
    have hsupport := Real.add_one_le_exp t
    have hlinear : 1 - Real.exp t ≤ -t := by
      linarith
    calc
      -(Real.exp t - 1) = 1 - Real.exp t := by ring
      _ ≤ -t := hlinear
      _ ≤ -t * Real.exp (-t) := by
        linarith [mul_nonneg hnegt
          (sub_nonneg.mpr hexpneg)]

private theorem plusSaddleSmallRadiusCoefficient_error_of_phase
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (n : ℕ) (hn : 2 * (n : ℝ) ≤ ℓ)
    (C : ℝ) (hC : 0 ≤ C)
    (hphase :
      |ℓ *
          (realHyperbolicShellPhase ε
            (1 + 2 * (n : ℝ) / ℓ) -
              realHyperbolicShellPhase ε 1) -
          2 * (n : ℝ) * saddleShellDerivativeOne ε| ≤
        C * (n : ℝ) ^ 2 / ℓ) :
    |plusSaddleSmallRadiusCoefficient ε ℓ n - 1| ≤
      (C * (n : ℝ) ^ 2 / ℓ +
        (18 / (ε / 4)) * ((n : ℝ) / ℓ)) *
          Real.exp (C * (n : ℝ) ^ 2 / ℓ) := by
  let E : ℝ :=
    ℓ * (realHyperbolicShellPhase ε
      (1 + 2 * (n : ℝ) / ℓ) -
        realHyperbolicShellPhase ε 1) -
      2 * (n : ℝ) * saddleShellDerivativeOne ε
  let P : ℝ :=
    ((ε / 4) - (2 * (n : ℝ) / ℓ) *
      (2 + 2 * (n : ℝ) / ℓ) ^ 2) / (ε / 4)
  let q : ℝ := C * (n : ℝ) ^ 2 / ℓ
  let k : ℝ := (18 / (ε / 4)) * ((n : ℝ) / ℓ)
  have hq : 0 ≤ q := by
    try dsimp [q]
    positivity
  have hk : 0 ≤ k := by
    try dsimp [k]
    positivity [div_pos hε four_pos]
  have hE : |E| ≤ q := by
    simpa only  using! hphase
  have hP : |P - 1| ≤ k := by
    simpa only  using!
      plusSaddleSmallRadiusPolynomial_error hε hℓ n hn
  have hexp : Real.exp E ≤ Real.exp q :=
    Real.exp_le_exp.mpr ((le_abs_self E).trans hE)
  have hexpabs : Real.exp |E| ≤ Real.exp q :=
    Real.exp_le_exp.mpr hE
  have htermP :
      |Real.exp E * (P - 1)| ≤ Real.exp q * k := by
    rw [abs_mul, abs_of_pos (Real.exp_pos E)]
    exact mul_le_mul hexp hP
      (abs_nonneg _) (Real.exp_pos q).le
  have htermE : |Real.exp E - 1| ≤ q * Real.exp q :=
    (abs_exp_sub_one_le_abs_mul_exp_abs E).trans
      (mul_le_mul hE hexpabs
        (Real.exp_pos |E|).le hq)
  change |Real.exp E * P - 1| ≤
    (q + k) * Real.exp q
  calc
    |Real.exp E * P - 1| =
        |Real.exp E * (P - 1) +
          (Real.exp E - 1)| := by
            congr 1
            ring
    _ ≤ |Real.exp E * (P - 1)| +
          |Real.exp E - 1| := abs_add_le _ _
    _ ≤ Real.exp q * k + q * Real.exp q :=
      add_le_add htermP htermE
    _ = (q + k) * Real.exp q := by ring

private theorem exists_plusSaddleSmallRadiusCoefficient_error
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ℓ : ℝ), 0 < ℓ →
        ∀ n : ℕ, 2 * (n : ℝ) ≤ ℓ →
          |plusSaddleSmallRadiusCoefficient ε ℓ n - 1| ≤
            (C * ((n : ℝ) + (n : ℝ) ^ 2) / ℓ) *
              Real.exp (C * (n : ℝ) ^ 2 / ℓ) := by
  obtain ⟨C, hC, hphase⟩ :=
    exists_plusSaddleSmallRadiusPhase_error hε horder
  let K : ℝ := 18 / (ε / 4)
  have hK : 0 ≤ K := by
    try dsimp [K]
    positivity [div_pos hε four_pos]
  refine ⟨C + K, add_nonneg hC hK, ?_⟩
  intro ℓ hℓ n hn
  have hsource := plusSaddleSmallRadiusCoefficient_error_of_phase
    hε hℓ n hn C hC (hphase ℓ hℓ n hn)
  have hnreal : 0 ≤ (n : ℝ) := by positivity
  have hpoly :
      C * (n : ℝ) ^ 2 / ℓ + K * ((n : ℝ) / ℓ) ≤
        (C + K) * ((n : ℝ) + (n : ℝ) ^ 2) / ℓ := by
    rw [show C * (n : ℝ) ^ 2 / ℓ +
          K * ((n : ℝ) / ℓ) =
        (C * (n : ℝ) ^ 2 + K * (n : ℝ)) / ℓ by
          ring]
    apply (div_le_div_iff_of_pos_right hℓ).mpr
    linarith [mul_nonneg hC hnreal,
      mul_nonneg hK (sq_nonneg (n : ℝ))]
  have hq :
      C * (n : ℝ) ^ 2 / ℓ ≤
        (C + K) * (n : ℝ) ^ 2 / ℓ := by
    gcongr
    exact le_add_of_nonneg_right hK
  have hright :
      0 ≤ (C + K) * ((n : ℝ) + (n : ℝ) ^ 2) / ℓ := by
    positivity
  calc
    |plusSaddleSmallRadiusCoefficient ε ℓ n - 1| ≤
      (C * (n : ℝ) ^ 2 / ℓ +
        K * ((n : ℝ) / ℓ)) *
          Real.exp (C * (n : ℝ) ^ 2 / ℓ) := by
            simpa only [K] using! hsource
    _ ≤ ((C + K) * ((n : ℝ) + (n : ℝ) ^ 2) / ℓ) *
          Real.exp ((C + K) * (n : ℝ) ^ 2 / ℓ) :=
        mul_le_mul hpoly (Real.exp_le_exp.mpr hq)
          (Real.exp_pos _).le hright

private theorem saddleExpSeries_hasSum (y : ℝ) :
    HasSum (fun n : ℕ => y ^ n / (n.factorial : ℝ))
      (Real.exp y) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp y

private theorem saddleExpSeries_firstMoment_hasSum (y : ℝ) :
    HasSum
      (fun n : ℕ => (n : ℝ) *
        (y ^ n / (n.factorial : ℝ)))
      (y * Real.exp y) := by
  let f : ℕ → ℝ := fun n =>
    (n : ℝ) * (y ^ n / (n.factorial : ℝ))
  have hshift :
      (fun n : ℕ => f (n + 1)) =
      (fun n : ℕ => y *
        (y ^ n / (n.factorial : ℝ))) := by
    funext n
    try dsimp [f]
    rw [Nat.factorial_succ, pow_succ]
    push_cast
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hfact : (n.factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    field_simp
  have htail : HasSum (fun n : ℕ => f (n + 1))
      (y * Real.exp y) := by
    rw [hshift]
    exact (saddleExpSeries_hasSum y).mul_left y
  simpa [f] using! htail.zero_add

private theorem saddleExpSeries_secondFallingMoment_hasSum (y : ℝ) :
    HasSum
      (fun n : ℕ =>
        (n : ℝ) * ((n : ℝ) - 1) *
          (y ^ n / (n.factorial : ℝ)))
      (y ^ 2 * Real.exp y) := by
  let f : ℕ → ℝ := fun n =>
    (n : ℝ) * ((n : ℝ) - 1) *
      (y ^ n / (n.factorial : ℝ))
  have hshift :
      (fun n : ℕ => f (n + 2)) =
      (fun n : ℕ => y ^ 2 *
        (y ^ n / (n.factorial : ℝ))) := by
    funext n
    try dsimp [f]
    rw [show n + 2 = (n + 1) + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ,
      pow_succ, pow_succ]
    push_cast
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hn' : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
    have hfact : (n.factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    field_simp; ring
  have htail : HasSum (fun n : ℕ => f (n + 2))
      (y ^ 2 * Real.exp y) := by
    rw [hshift]
    exact (saddleExpSeries_hasSum y).mul_left (y ^ 2)
  have hfull := htail.sum_range_add
  simpa [f, Finset.sum_range_succ] using! hfull

private theorem saddleExpSeries_polynomialMoment_hasSum (y : ℝ) :
    HasSum
      (fun n : ℕ =>
        ((n : ℝ) + (n : ℝ) ^ 2) *
          (y ^ n / (n.factorial : ℝ)))
      ((2 * y + y ^ 2) * Real.exp y) := by
  have hfirst :=
    (saddleExpSeries_firstMoment_hasSum y).mul_left 2
  have hsecond :=
    saddleExpSeries_secondFallingMoment_hasSum y
  have hcombined := hfirst.add hsecond
  convert! hcombined using 1
  · funext n
    ring
  · ring

private theorem saddleExpSeries_polynomialMoment_sum_range_le
    {y : ℝ} (hy : 0 ≤ y) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      ((n : ℝ) + (n : ℝ) ^ 2) *
        (y ^ n / (n.factorial : ℝ))) ≤
      (2 * y + y ^ 2) * Real.exp y := by
  exact sum_le_hasSum (Finset.range N)
    (fun n _ => by positivity)
    (saddleExpSeries_polynomialMoment_hasSum y)

private theorem exists_plusSaddleSmallRadius_weightedCoefficient_error
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ℓ : ℝ), 0 < ℓ →
        ∀ N : ℕ, 2 * (N : ℝ) ≤ ℓ →
          ∀ y : ℝ, 0 ≤ y →
            (∑ n ∈ Finset.range (N + 1),
              (y ^ n / (n.factorial : ℝ)) *
                |plusSaddleSmallRadiusCoefficient ε ℓ n - 1|) ≤
              (C / ℓ) *
                Real.exp (C * (N : ℝ) ^ 2 / ℓ) *
                  (2 * y + y ^ 2) * Real.exp y := by
  obtain ⟨C, hC, hcoeff⟩ :=
    exists_plusSaddleSmallRadiusCoefficient_error hε horder
  refine ⟨C, hC, ?_⟩
  intro ℓ hℓ N hN y hy
  have hnonneg : 0 ≤ (C / ℓ) *
      Real.exp (C * (N : ℝ) ^ 2 / ℓ) := by
    positivity
  calc
    (∑ n ∈ Finset.range (N + 1),
        (y ^ n / (n.factorial : ℝ)) *
          |plusSaddleSmallRadiusCoefficient ε ℓ n - 1|) ≤
      ∑ n ∈ Finset.range (N + 1),
        ((C / ℓ) * Real.exp (C * (N : ℝ) ^ 2 / ℓ)) *
          (((n : ℝ) + (n : ℝ) ^ 2) *
            (y ^ n / (n.factorial : ℝ))) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnN : n ≤ N :=
          Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
        have hnNreal : (n : ℝ) ≤ (N : ℝ) := by
          exact_mod_cast hnN
        have hnpole : 2 * (n : ℝ) ≤ ℓ :=
          (mul_le_mul_of_nonneg_left hnNreal (by norm_num)).trans hN
        have hbound := hcoeff ℓ hℓ n hnpole
        have hterm : 0 ≤ y ^ n / (n.factorial : ℝ) := by
          positivity
        have hq :
            C * (n : ℝ) ^ 2 / ℓ ≤
              C * (N : ℝ) ^ 2 / ℓ := by
          gcongr
        have hbase :
            0 ≤ C * ((n : ℝ) + (n : ℝ) ^ 2) / ℓ := by
          positivity
        calc
          (y ^ n / (n.factorial : ℝ)) *
              |plusSaddleSmallRadiusCoefficient ε ℓ n - 1| ≤
            (y ^ n / (n.factorial : ℝ)) *
              ((C * ((n : ℝ) + (n : ℝ) ^ 2) / ℓ) *
                Real.exp (C * (n : ℝ) ^ 2 / ℓ)) :=
              mul_le_mul_of_nonneg_left hbound hterm
          _ ≤ (y ^ n / (n.factorial : ℝ)) *
              ((C * ((n : ℝ) + (n : ℝ) ^ 2) / ℓ) *
                Real.exp (C * (N : ℝ) ^ 2 / ℓ)) := by
              gcongr
          _ = ((C / ℓ) * Real.exp (C * (N : ℝ) ^ 2 / ℓ)) *
              (((n : ℝ) + (n : ℝ) ^ 2) *
                (y ^ n / (n.factorial : ℝ))) := by
              ring
    _ = ((C / ℓ) * Real.exp (C * (N : ℝ) ^ 2 / ℓ)) *
        (∑ n ∈ Finset.range (N + 1),
          ((n : ℝ) + (n : ℝ) ^ 2) *
            (y ^ n / (n.factorial : ℝ))) := by
          rw [Finset.mul_sum]
    _ ≤ ((C / ℓ) * Real.exp (C * (N : ℝ) ^ 2 / ℓ)) *
        ((2 * y + y ^ 2) * Real.exp y) :=
          mul_le_mul_of_nonneg_left
            (saddleExpSeries_polynomialMoment_sum_range_le
              hy (N + 1)) hnonneg
    _ = (C / ℓ) *
          Real.exp (C * (N : ℝ) ^ 2 / ℓ) *
            (2 * y + y ^ 2) * Real.exp y := by ring

private theorem saddleExpSeries_tail_term_le_geometric
    {y : ℝ} (hy : 0 ≤ y)
    (m : ℕ) (hym : 2 * y ≤ (m : ℝ) + 1)
    (k : ℕ) :
    y ^ (m + k) / ((m + k).factorial : ℝ) ≤
      (y ^ m / (m.factorial : ℝ)) *
        ((1 / 2 : ℝ) ^ k) := by
  induction k with
  | zero => simp only [add_zero, one_div, pow_zero, mul_one, Std.le_refl]
  | succ k ih =>
    have hden : 0 < ((m + k + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < m + k + 1 by omega)
    have hdenlarge :
        (m : ℝ) + 1 ≤ ((m + k + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show m + 1 ≤ m + k + 1 by omega)
    have hratio :
        y / ((m + k + 1 : ℕ) : ℝ) ≤ (1 / 2 : ℝ) := by
      apply (div_le_iff₀ hden).mpr
      linarith
    have hstep :
        y ^ (m + (k + 1)) /
            ((m + (k + 1)).factorial : ℝ) =
          (y ^ (m + k) / ((m + k).factorial : ℝ)) *
            (y / ((m + k + 1 : ℕ) : ℝ)) := by
      rw [show m + (k + 1) = (m + k) + 1 by omega,
        Nat.factorial_succ, pow_succ]
      push_cast
      have hfact : ((m + k).factorial : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (m + k)
      field_simp
    calc
      y ^ (m + (k + 1)) /
          ((m + (k + 1)).factorial : ℝ) =
        (y ^ (m + k) / ((m + k).factorial : ℝ)) *
          (y / ((m + k + 1 : ℕ) : ℝ)) := hstep
      _ ≤ ((y ^ m / (m.factorial : ℝ)) *
            ((1 / 2 : ℝ) ^ k)) * (1 / 2 : ℝ) := by
          exact mul_le_mul ih hratio
            (by positivity) (by positivity)
      _ = (y ^ m / (m.factorial : ℝ)) *
          ((1 / 2 : ℝ) ^ (k + 1)) := by
            rw [pow_succ]
            ring

private theorem saddleExpSeries_alternating_tail_bound
    {y : ℝ} (hy : 0 ≤ y)
    (m : ℕ) (hym : 2 * y ≤ (m : ℝ) + 1) :
    |Real.exp (-y) -
        (∑ n ∈ Finset.range m,
          (-y) ^ n / (n.factorial : ℝ))| ≤
      2 * (y ^ m / (m.factorial : ℝ)) := by
  let f : ℕ → ℝ := fun n =>
    (-y) ^ n / (n.factorial : ℝ)
  have hwhole : HasSum f (Real.exp (-y)) :=
    saddleExpSeries_hasSum (-y)
  have htail : Summable (fun n : ℕ => f (n + m)) :=
    (summable_nat_add_iff m).mpr hwhole.summable
  have hnorm : Summable
      (fun n : ℕ => ‖f (n + m)‖) := htail.norm
  have hgeometric :
      Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) := by
    apply summable_geometric_of_norm_lt_one
    norm_num
  have hmajor : Summable
      (fun n : ℕ =>
        (y ^ m / (m.factorial : ℝ)) *
          ((1 / 2 : ℝ) ^ n)) :=
    hgeometric.mul_left (y ^ m / (m.factorial : ℝ))
  have hdecomp :
      (∑ n ∈ Finset.range m, f n) +
        (∑' n : ℕ, f (n + m)) = Real.exp (-y) :=
    HasSum.unique htail.hasSum.sum_range_add hwhole
  have htermnorm (n : ℕ) :
      ‖f (n + m)‖ =
        y ^ (m + n) / ((m + n).factorial : ℝ) := by
    try dsimp [f]
    rw [abs_div, abs_pow,
      abs_neg, abs_of_nonneg hy]
    have hfact : 0 < ((n + m).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos (n + m)
    rw [abs_of_pos hfact]
    simp only [Nat.add_comm]
  have hterms (n : ℕ) :
      ‖f (n + m)‖ ≤
        (y ^ m / (m.factorial : ℝ)) *
          ((1 / 2 : ℝ) ^ n) := by
    rw [htermnorm n]
    exact saddleExpSeries_tail_term_le_geometric
      hy m hym n
  change |Real.exp (-y) -
    (∑ n ∈ Finset.range m, f n)| ≤
      2 * (y ^ m / (m.factorial : ℝ))
  have hidentity : Real.exp (-y) -
      (∑ n ∈ Finset.range m, f n) =
        ∑' n : ℕ, f (n + m) := by
    linarith
  calc
    |Real.exp (-y) -
        (∑ n ∈ Finset.range m, f n)| =
      ‖∑' n : ℕ, f (n + m)‖ := by
        rw [Real.norm_eq_abs, hidentity]
    _ ≤ ∑' n : ℕ, ‖f (n + m)‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ,
        (y ^ m / (m.factorial : ℝ)) *
          ((1 / 2 : ℝ) ^ n) :=
        Summable.tsum_le_tsum hterms hnorm hmajor
    _ = (y ^ m / (m.factorial : ℝ)) *
          (∑' n : ℕ, (1 / 2 : ℝ) ^ n) :=
        tsum_mul_left
    _ = 2 * (y ^ m / (m.factorial : ℝ)) := by
        rw [tsum_geometric_of_lt_one
          (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)]
        norm_num; ring

private theorem exists_plusSaddleSmallRadius_finiteResidue_error
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ℓ : ℝ), 0 < ℓ →
        ∀ N : ℕ, 2 * (N : ℝ) ≤ ℓ →
          ∀ y : ℝ, 0 ≤ y →
            2 * y ≤ (N : ℝ) + 2 →
              |(∑ n ∈ Finset.range (N + 1),
                  ((-y) ^ n / (n.factorial : ℝ)) *
                    plusSaddleSmallRadiusCoefficient ε ℓ n) -
                Real.exp (-y)| ≤
              (C / ℓ) *
                Real.exp (C * (N : ℝ) ^ 2 / ℓ) *
                  (2 * y + y ^ 2) * Real.exp y +
                2 * (y ^ (N + 1) /
                  ((N + 1).factorial : ℝ)) := by
  obtain ⟨C, hC, hweight⟩ :=
    exists_plusSaddleSmallRadius_weightedCoefficient_error
      hε horder
  refine ⟨C, hC, ?_⟩
  intro ℓ hℓ N hN y hy hyratio
  have hmoment := hweight ℓ hℓ N hN y hy
  have htail := saddleExpSeries_alternating_tail_bound
    hy (N + 1) (by
      push_cast
      linarith)
  have hsplit :
      (∑ n ∈ Finset.range (N + 1),
        ((-y) ^ n / (n.factorial : ℝ)) *
          plusSaddleSmallRadiusCoefficient ε ℓ n) =
        (∑ n ∈ Finset.range (N + 1),
          ((-y) ^ n / (n.factorial : ℝ)) *
            (plusSaddleSmallRadiusCoefficient ε ℓ n - 1)) +
        (∑ n ∈ Finset.range (N + 1),
          (-y) ^ n / (n.factorial : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hcoefficient :
      |∑ n ∈ Finset.range (N + 1),
        ((-y) ^ n / (n.factorial : ℝ)) *
          (plusSaddleSmallRadiusCoefficient ε ℓ n - 1)| ≤
      ∑ n ∈ Finset.range (N + 1),
        (y ^ n / (n.factorial : ℝ)) *
          |plusSaddleSmallRadiusCoefficient ε ℓ n - 1| := by
    calc
      |∑ n ∈ Finset.range (N + 1),
          ((-y) ^ n / (n.factorial : ℝ)) *
            (plusSaddleSmallRadiusCoefficient ε ℓ n - 1)| ≤
        ∑ n ∈ Finset.range (N + 1),
          |((-y) ^ n / (n.factorial : ℝ)) *
            (plusSaddleSmallRadiusCoefficient ε ℓ n - 1)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ n ∈ Finset.range (N + 1),
          (y ^ n / (n.factorial : ℝ)) *
            |plusSaddleSmallRadiusCoefficient ε ℓ n - 1| := by
          apply Finset.sum_congr rfl
          intro n hn
          have hfact : 0 < (n.factorial : ℝ) := by
            exact_mod_cast Nat.factorial_pos n
          rw [abs_mul, abs_div, abs_pow,
            abs_neg, abs_of_nonneg hy,
            abs_of_pos hfact]
  rw [hsplit]
  calc
    |(∑ n ∈ Finset.range (N + 1),
          ((-y) ^ n / (n.factorial : ℝ)) *
            (plusSaddleSmallRadiusCoefficient ε ℓ n - 1)) +
        (∑ n ∈ Finset.range (N + 1),
          (-y) ^ n / (n.factorial : ℝ)) -
        Real.exp (-y)| =
      |(∑ n ∈ Finset.range (N + 1),
          ((-y) ^ n / (n.factorial : ℝ)) *
            (plusSaddleSmallRadiusCoefficient ε ℓ n - 1)) +
        ((∑ n ∈ Finset.range (N + 1),
          (-y) ^ n / (n.factorial : ℝ)) -
          Real.exp (-y))| := by
        congr 1
        ring
    _ ≤ |∑ n ∈ Finset.range (N + 1),
          ((-y) ^ n / (n.factorial : ℝ)) *
            (plusSaddleSmallRadiusCoefficient ε ℓ n - 1)| +
        |(∑ n ∈ Finset.range (N + 1),
          (-y) ^ n / (n.factorial : ℝ)) -
          Real.exp (-y)| := abs_add_le _ _
    _ ≤ (∑ n ∈ Finset.range (N + 1),
          (y ^ n / (n.factorial : ℝ)) *
            |plusSaddleSmallRadiusCoefficient ε ℓ n - 1|) +
        2 * (y ^ (N + 1) /
          ((N + 1).factorial : ℝ)) := by
        apply add_le_add hcoefficient
        rw [abs_sub_comm]
        exact htail
    _ ≤ (C / ℓ) *
          Real.exp (C * (N : ℝ) ^ 2 / ℓ) *
            (2 * y + y ^ 2) * Real.exp y +
          2 * (y ^ (N + 1) /
            ((N + 1).factorial : ℝ)) :=
        add_le_add hmoment (le_refl _)

private theorem exists_plusSaddleSmallRadius_relativeFiniteResidue_error
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ℓ : ℝ), 0 < ℓ →
        ∀ N : ℕ, 2 * (N : ℝ) ≤ ℓ →
          ∀ y : ℝ, 0 ≤ y →
            2 * y ≤ (N : ℝ) + 2 →
              Real.exp y *
                |(∑ n ∈ Finset.range (N + 1),
                    ((-y) ^ n / (n.factorial : ℝ)) *
                      plusSaddleSmallRadiusCoefficient ε ℓ n) -
                  Real.exp (-y)| ≤
                (C / ℓ) *
                  Real.exp (C * (N : ℝ) ^ 2 / ℓ) *
                    (2 * y + y ^ 2) * Real.exp (2 * y) +
                2 * Real.exp y *
                  (y ^ (N + 1) /
                    ((N + 1).factorial : ℝ)) := by
  obtain ⟨C, hC, hfinite⟩ :=
    exists_plusSaddleSmallRadius_finiteResidue_error
      hε horder
  refine ⟨C, hC, ?_⟩
  intro ℓ hℓ N hN y hy hyratio
  have hbound := hfinite ℓ hℓ N hN y hy hyratio
  have hexp : 0 ≤ Real.exp y := (Real.exp_pos y).le
  calc
    Real.exp y *
        |(∑ n ∈ Finset.range (N + 1),
            ((-y) ^ n / (n.factorial : ℝ)) *
              plusSaddleSmallRadiusCoefficient ε ℓ n) -
          Real.exp (-y)| ≤
      Real.exp y *
        ((C / ℓ) *
          Real.exp (C * (N : ℝ) ^ 2 / ℓ) *
            (2 * y + y ^ 2) * Real.exp y +
          2 * (y ^ (N + 1) /
            ((N + 1).factorial : ℝ))) :=
          mul_le_mul_of_nonneg_left hbound hexp
    _ = (C / ℓ) *
          Real.exp (C * (N : ℝ) ^ 2 / ℓ) *
            (2 * y + y ^ 2) * Real.exp (2 * y) +
          2 * Real.exp y *
            (y ^ (N + 1) /
              ((N + 1).factorial : ℝ)) := by
          rw [show Real.exp (2 * y) =
            Real.exp y * Real.exp y by
              rw [show 2 * y = y + y by ring,
                Real.exp_add]]
          ring

private theorem upperGammaMeasureDensity_pos
    {ℓ η a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) :
    0 < upperGammaMeasureDensity ℓ η a := by
  have hx : 0 < 2 * a / ℓ := by positivity
  have hden : 0 < 1 - Real.exp (-(2 * a / ℓ)) := by
    have he := Real.exp_lt_one_iff.mpr (show -(2 * a / ℓ) < 0 by linarith)
    linarith
  unfold upperGammaMeasureDensity
  exact div_pos (Real.exp_pos _) (mul_pos ha hden)

private theorem upper_one_sub_cos_quadratic_lower
    {x : ℝ} (hx : |x| ≤ 1) :
    x ^ 2 / 4 ≤ 1 - Real.cos x := by
  have hnonnegative : 0 ≤ |x| := abs_nonneg x
  have hquartic := cos_le_quartic hnonnegative hx
  rw [Real.cos_abs] at hquartic
  have hsquare : |x| ^ 2 = x ^ 2 := by
    exact sq_abs x
  have hfourth : |x| ^ 4 = x ^ 4 := by
    calc
      |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
      _ = (x ^ 2) ^ 2 := by rw [hsquare]
      _ = x ^ 4 := by ring
  rw [hsquare, hfourth] at hquartic
  have hx2 : x ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ hnonnegative hx 2
    simpa only [sq_le_one_iff_abs_le_one, ge_iff_le, hsquare, one_pow] using! h
  have hx4 : x ^ 4 ≤ x ^ 2 := by
    linarith [mul_nonneg (sq_nonneg x)
      (sub_nonneg.mpr hx2)]
  nlinarith

private noncomputable def upperGammaDampingIntegrand (ℓ η T a : ℝ) : ℝ :=
  (1 - Real.cos (a * T)) *
    upperGammaMeasureDensity ℓ η a

private noncomputable def upperGammaDamping (ℓ η T : ℝ) : ℝ :=
  ∫ a : ℝ in Ioi 0,
    upperGammaDampingIntegrand ℓ η T a

private theorem upperGammaDampingIntegrand_integrable
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) :
    IntegrableOn
      (upperGammaDampingIntegrand ℓ η T) (Ioi 0) := by
  have hvariance := upperGammaVarianceDensity_integrable
    hℓ hη
  have hmajor : IntegrableOn
      (fun a : ℝ => (T ^ 2 / 2) *
        (a ^ 2 * upperGammaMeasureDensity ℓ η a))
      (Ioi 0) :=
    hvariance.const_mul (T ^ 2 / 2)
  have hmeas : Measurable
      (upperGammaDampingIntegrand ℓ η T) := by
    unfold upperGammaDampingIntegrand
      upperGammaMeasureDensity
    fun_prop
  apply hmajor.mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi]
    with a ha
  have hdensity := upperGammaMeasureDensity_pos
    (η := η) hℓ ha
  have hcos :
      0 ≤ 1 - Real.cos (a * T) :=
    sub_nonneg.mpr (Real.cos_le_one _)
  have hquad :
      1 - Real.cos (a * T) ≤ (a * T) ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos
      (x := a * T)]
  unfold upperGammaDampingIntegrand
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hcos hdensity.le)]
  calc
    (1 - Real.cos (a * T)) *
        upperGammaMeasureDensity ℓ η a ≤
      ((a * T) ^ 2 / 2) *
        upperGammaMeasureDensity ℓ η a :=
      mul_le_mul_of_nonneg_right hquad hdensity.le
    _ = (T ^ 2 / 2) *
        (a ^ 2 * upperGammaMeasureDensity ℓ η a) := by
      ring

private theorem upperGammaDamping_nonneg
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (T : ℝ) :
    0 ≤ upperGammaDamping ℓ η T := by
  unfold upperGammaDamping
  apply setIntegral_nonneg measurableSet_Ioi
  intro a ha
  unfold upperGammaDampingIntegrand
  exact mul_nonneg
    (sub_nonneg.mpr (Real.cos_le_one _))
    (upperGammaMeasureDensity_pos
      (η := η) hℓ ha).le

private theorem upperGammaDampingIntegrand_lower_on_window
    {ℓ η T a : ℝ}
    (hℓ : 0 < ℓ) (hη : 0 < η)
    (ha : 0 < a)
    (haη : a ≤ η⁻¹)
    (haT : a ≤ |T|⁻¹)
    (hT : T ≠ 0) :
    (ℓ / (8 * Real.exp 1)) * T ^ 2 ≤
      upperGammaDampingIntegrand ℓ η T a := by
  have hTa : |a * T| ≤ 1 := by
    rw [abs_mul, abs_of_pos ha]
    calc
      a * |T| ≤ |T|⁻¹ * |T| :=
        mul_le_mul_of_nonneg_right haT
          (abs_nonneg T)
      _ = 1 := inv_mul_cancel₀ (abs_ne_zero.mpr hT)
  have heta : η * a ≤ 1 := by
    calc
      η * a ≤ η * η⁻¹ :=
        mul_le_mul_of_nonneg_left haη hη.le
      _ = 1 := mul_inv_cancel₀ hη.ne'
  have hexp : (Real.exp 1)⁻¹ ≤
      Real.exp (-η * a) := by
    rw [← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith)
  have hvariance :=
    (upperGammaVarianceDensity_pointwise_bounds
      (η := η) hℓ ha).1
  have hcos := upper_one_sub_cos_quadratic_lower hTa
  have hdensity := upperGammaMeasureDensity_pos
    (η := η) hℓ ha
  have hquarter : 0 ≤ T ^ 2 / 4 := by positivity
  calc
    (ℓ / (8 * Real.exp 1)) * T ^ 2 =
        (T ^ 2 / 4) *
          ((ℓ / 2) * (Real.exp 1)⁻¹) := by
      field_simp [(Real.exp_pos 1).ne']
      ring
    _ ≤ (T ^ 2 / 4) *
          ((ℓ / 2) * Real.exp (-η * a)) := by
      gcongr
    _ ≤ (T ^ 2 / 4) *
          (a ^ 2 * upperGammaMeasureDensity ℓ η a) :=
      mul_le_mul_of_nonneg_left hvariance hquarter
    _ = ((a * T) ^ 2 / 4) *
          upperGammaMeasureDensity ℓ η a := by
      ring
    _ ≤ (1 - Real.cos (a * T)) *
          upperGammaMeasureDensity ℓ η a :=
      mul_le_mul_of_nonneg_right hcos hdensity.le
    _ = upperGammaDampingIntegrand ℓ η T a := rfl

private theorem upperGammaDamping_lower_bound
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) :
    (ℓ / (8 * Real.exp 1)) *
        min (T ^ 2 / η) |T| ≤
      upperGammaDamping ℓ η T := by
  by_cases hT : T = 0
  · subst T
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, abs_zero,
      min_self, mul_zero,
      upperGammaDamping, upperGammaDampingIntegrand, Real.cos_zero, sub_self, zero_mul,
        integral_zero, Std.le_refl]
  · let q : ℝ := min η⁻¹ |T|⁻¹
    let c : ℝ :=
      (ℓ / (8 * Real.exp 1)) * T ^ 2
    have hq : 0 < q := by
      try dsimp [q]
      exact lt_min (inv_pos.mpr hη)
        (inv_pos.mpr (abs_pos.mpr hT))
    have hsubset : Ioc (0 : ℝ) q ⊆ Ioi 0 := by
      intro a ha
      exact ha.1
    have hfull :=
      upperGammaDampingIntegrand_integrable
        hℓ hη T
    have hsmall := hfull.mono_set hsubset
    have hconstant : IntegrableOn
        (fun _ : ℝ => c) (Ioc 0 q) :=
      integrableOn_const (by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top)
    have hpoint : ∀ a ∈ Ioc (0 : ℝ) q,
        c ≤ upperGammaDampingIntegrand ℓ η T a := by
      intro a ha
      apply upperGammaDampingIntegrand_lower_on_window
        hℓ hη ha.1
      · exact ha.2.trans (min_le_left _ _)
      · exact ha.2.trans (min_le_right _ _)
      · exact hT
    have hmono :=
      setIntegral_mono_on hconstant hsmall
        measurableSet_Ioc hpoint
    have hnonnegative :
        0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
          upperGammaDampingIntegrand ℓ η T := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi]
        with a ha
      unfold upperGammaDampingIntegrand
      exact mul_nonneg
        (sub_nonneg.mpr (Real.cos_le_one _))
        (upperGammaMeasureDensity_pos
          (η := η) hℓ ha).le
    have haesubset :
        Ioc (0 : ℝ) q ≤ᶠ[ae (volume : Measure ℝ)]
          Ioi 0 :=
      Filter.Eventually.of_forall fun a ha => hsubset ha
    have hrestrict :=
      setIntegral_mono_set hfull hnonnegative haesubset
    have hmeasure :
        (volume : Measure ℝ).real (Ioc (0 : ℝ) q) = q := by
      change ((volume : Measure ℝ)
        (Ioc (0 : ℝ) q)).toReal = q
      rw [Real.volume_Ioc,
        ENNReal.toReal_ofReal (by linarith)]
      simp only [sub_zero]
    have hconstintegral :
        (∫ a : ℝ in Ioc (0 : ℝ) q, c) = q * c := by
      rw [setIntegral_const, hmeasure]
      rfl
    have hmin :
        q * T ^ 2 = min (T ^ 2 / η) |T| := by
      try dsimp [q]
      rw [min_mul_of_nonneg η⁻¹ |T|⁻¹
        (sq_nonneg T)]
      congr 1
      · simp only [div_eq_mul_inv, mul_comm]
      · have hTabs : |T| ≠ 0 := abs_ne_zero.mpr hT
        calc
          |T|⁻¹ * T ^ 2 = |T|⁻¹ * |T| ^ 2 := by
            rw [sq_abs]
          _ = |T| := by
            field_simp [hTabs]
    calc
      (ℓ / (8 * Real.exp 1)) *
          min (T ^ 2 / η) |T| = q * c := by
        try dsimp [c]
        rw [← hmin]
        ring
      _ = ∫ a : ℝ in Ioc (0 : ℝ) q, c :=
        hconstintegral.symm
      _ ≤ ∫ a : ℝ in Ioc (0 : ℝ) q,
          upperGammaDampingIntegrand ℓ η T a :=
        hmono
      _ ≤ ∫ a : ℝ in Ioi 0,
          upperGammaDampingIntegrand ℓ η T a :=
        hrestrict
      _ = upperGammaDamping ℓ η T := rfl

private noncomputable def upperSaddleDamping (ε ℓ δ T : ℝ) : ℝ :=
  upperGammaDamping ℓ (2 + δ) T +
    positiveShellDamping ε ℓ δ T -
      upperShortShellDamping ε ℓ δ T

private noncomputable def upperSaddleVariance (ε ℓ δ : ℝ) : ℝ :=
  upperGammaVariance ℓ (2 + δ) +
    upperNetShellVariance ε δ

private noncomputable def upperSaddleThirdMoment (ε ℓ δ : ℝ) : ℝ :=
  upperGammaThirdMoment ℓ (2 + δ) +
    upperNetShellThirdMoment ε δ

private theorem eventually_upperSaddleDamping_gamma_add_shell
    : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        ∀ ℓ : ℝ, 0 < ℓ →
          ∀ δ : ℝ, ε / 2 ≤ δ →
            ∀ T : ℝ,
              upperGammaDamping ℓ (2 + δ) T +
                (99 / 100 : ℝ) *
                  positiveShellDamping ε ℓ δ T ≤
                upperSaddleDamping ε ℓ δ T := by
  filter_upwards [eventually_upper_shortShell_domination]
    with ε hdom
  intro ℓ hℓ δ hδ T
  have hshort := hdom ℓ hℓ.le δ hδ T
  unfold upperSaddleDamping
  linarith

private theorem eventually_upperSaddleVariance_bounds
    : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        ∀ ℓ : ℝ, 0 < ℓ →
          ∀ δ : ℝ, ε / 2 ≤ δ →
            1 / (2 * (2 + δ)) +
                (99 / 100 : ℝ) *
                  upperPositiveShellVariance ε δ ≤
              upperSaddleVariance ε ℓ δ ∧
            upperSaddleVariance ε ℓ δ ≤
              (1 / (2 * (2 + δ)) +
                1 / (ℓ * (2 + δ) ^ 2)) +
                  upperPositiveShellVariance ε δ := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upper_netShellVariance_bounds]
    with ε hε hnet
  change 0 < ε at hε
  intro ℓ hℓ δ hδ
  have hη : 0 < 2 + δ := by
    linarith
  obtain ⟨hγlow, hγhigh⟩ :=
    upperGammaVariance_bounds hℓ hη
  obtain ⟨hslow, hshigh⟩ :=
    hnet δ hδ
  unfold upperSaddleVariance
  exact ⟨add_le_add hγlow hslow,
    add_le_add hγhigh hshigh⟩

private theorem upperPositiveShellVariance_pos
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) :
    0 < upperPositiveShellVariance ε δ := by
  have hB : 0 < (ε⁻¹ ^ 3) := by
    positivity
  have hlower :=
    (upperPositiveShellVariance_bounds hε hδ).1
  have hpositive :
      0 < (1 / 2 : ℝ) *
        (ε⁻¹ ^ 3) ^ 2 *
          shellWeight ε *
            Real.exp (δ * (ε⁻¹ ^ 3)) := by
    exact mul_pos
      (mul_pos
        (mul_pos (by norm_num)
          (sq_pos_of_pos hB))
        (shellWeight_pos ε))
      (Real.exp_pos _)
  exact hpositive.trans_le hlower

private theorem eventually_upperSaddleVariance_pos
    : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        ∀ ℓ : ℝ, 0 < ℓ →
          ∀ δ : ℝ, ε / 2 ≤ δ →
            0 < upperSaddleVariance ε ℓ δ := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upperSaddleVariance_bounds]
    with ε hε hbound
  change 0 < ε at hε
  intro ℓ hℓ δ hδ
  have hδnonnegative : 0 ≤ δ := by
    linarith
  have hη : 0 < 2 + δ := by
    linarith
  have hshell :=
    upperPositiveShellVariance_pos hε hδnonnegative
  have hpositive :
      0 < 1 / (2 * (2 + δ)) +
        (99 / 100 : ℝ) *
          upperPositiveShellVariance ε δ := by
    positivity
  exact hpositive.trans_le
    (hbound ℓ hℓ δ hδ).1

private theorem upperGammaThirdMoment_le_two_mul_variance
    {ℓ η : ℝ} (hℓ : 1 ≤ ℓ) (hη : 2 ≤ η) :
    upperGammaThirdMoment ℓ η ≤
      2 * upperGammaVariance ℓ η := by
  have hℓpositive : 0 < ℓ := by linarith
  have hηpositive : 0 < η := by linarith
  have hγthird :=
    (upperGammaThirdMoment_bounds hℓpositive hηpositive).2
  have hγvariance :=
    (upperGammaVariance_bounds hℓpositive hηpositive).1
  have hfirst :
      1 / (2 * η ^ 2) ≤ 1 / (2 * η) := by
    apply (div_le_div_iff₀
      (show 0 < 2 * η ^ 2 by positivity)
      (show 0 < 2 * η by positivity)).2
    linarith [mul_nonneg hηpositive.le
      (show 0 ≤ η - 1 by linarith)]
  have hηsquare : 4 ≤ η ^ 2 := by
    linarith [sq_nonneg (η - 2)]
  have hsquare : 4 ≤ ℓ * η ^ 2 := by
    calc
      (4 : ℝ) ≤ η ^ 2 := hηsquare
      _ ≤ ℓ * η ^ 2 := by
        linarith [mul_nonneg
          (show 0 ≤ ℓ - 1 by linarith)
          (sq_nonneg η)]
  have hsecond :
      2 / (ℓ * η ^ 3) ≤ 1 / (2 * η) := by
    apply (div_le_div_iff₀
      (show 0 < ℓ * η ^ 3 by positivity)
      (show 0 < 2 * η by positivity)).2
    have hscaled :=
      mul_le_mul_of_nonneg_right hsquare hηpositive.le
    linarith
  calc
    upperGammaThirdMoment ℓ η ≤
        1 / (2 * η ^ 2) +
          2 / (ℓ * η ^ 3) := hγthird
    _ ≤ 2 * (1 / (2 * η)) := by
      linarith
    _ ≤ 2 * upperGammaVariance ℓ η := by
      linarith

private noncomputable def upperSaddleShellThirdCoefficient (ε : ℝ) : ℝ :=
  (ε⁻¹ ^ 3) + 1 + (10 * Real.log (1 / ε)) / 100

private theorem eventually_upperSaddleThirdMoment_le_variance
    : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        ∀ ℓ : ℝ, 1 ≤ ℓ →
          ∀ δ : ℝ, ε / 2 ≤ δ →
            upperSaddleThirdMoment ε ℓ δ ≤
              (2 + (100 / 99 : ℝ) *
                upperSaddleShellThirdCoefficient ε) *
                  upperSaddleVariance ε ℓ δ := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_upper_netShellVariance_bounds,
    eventually_upper_netShellThirdMoment_bound]
    with ε hε horder hnet hthird
  change 0 < ε at hε
  intro ℓ hℓ δ hδ
  have hℓpositive : 0 < ℓ := by linarith
  have hδnonnegative : 0 ≤ δ := by
    linarith
  have hη : 2 ≤ 2 + δ := by
    linarith
  have hηpositive : 0 < 2 + δ := by
    linarith
  have hgamma :=
    upperGammaThirdMoment_le_two_mul_variance
      hℓ hη
  obtain ⟨hnetlower, hnetupper⟩ :=
    hnet δ hδ
  have hpositiveShell :=
    upperPositiveShellVariance_pos hε hδnonnegative
  have hnetnonnegative :
      0 ≤ upperNetShellVariance ε δ := by
    linarith
  have hgammavariance :
      0 ≤ upperGammaVariance ℓ (2 + δ) := by
    have h := (upperGammaVariance_bounds
      hℓpositive hηpositive).1
    have hpositive : 0 < 1 / (2 * (2 + δ)) := by
      positivity
    exact hpositive.le.trans h
  have hshortEndpoint : 0 ≤ (10 * Real.log (1 / ε)) := by
    have hcutoff : 0 < (ε ^ 3) := by
      positivity
    exact (hcutoff.trans_le horder).le
  have hB : 0 ≤ (ε⁻¹ ^ 3) := by
    positivity
  have hC : 0 ≤ upperSaddleShellThirdCoefficient ε := by
    unfold upperSaddleShellThirdCoefficient
    positivity
  have htransfer :
      upperPositiveShellVariance ε δ ≤
        (100 / 99 : ℝ) *
          upperNetShellVariance ε δ := by
    linarith
  have hthirdshell :
      upperNetShellThirdMoment ε δ ≤
        (100 / 99 : ℝ) *
          upperSaddleShellThirdCoefficient ε *
            upperNetShellVariance ε δ := by
    calc
      upperNetShellThirdMoment ε δ ≤
          upperSaddleShellThirdCoefficient ε *
            upperPositiveShellVariance ε δ := by
        simpa only [upperSaddleShellThirdCoefficient] using! hthird δ hδ
      _ ≤ upperSaddleShellThirdCoefficient ε *
            ((100 / 99 : ℝ) *
              upperNetShellVariance ε δ) :=
        mul_le_mul_of_nonneg_left htransfer hC
      _ = (100 / 99 : ℝ) *
          upperSaddleShellThirdCoefficient ε *
            upperNetShellVariance ε δ := by
        ring
  unfold upperSaddleThirdMoment upperSaddleVariance
  linarith [mul_nonneg hC hgammavariance,
    mul_nonneg hC hnetnonnegative]

private theorem upperShortMargin_mul_exp_antitone
    {ε : ℝ} (hε : 0 < ε) :
    AntitoneOn
      (fun a : ℝ =>
        (1 - 10 * ε * (1 + a)) * Real.exp (ε * a))
      (Ici (0 : ℝ)) := by
  let f : ℝ → ℝ := fun a =>
    (1 - 10 * ε * (1 + a)) * Real.exp (ε * a)
  have hderiv (a : ℝ) :
      HasDerivAt f
        (ε * Real.exp (ε * a) *
          ((1 - 10 * ε * (1 + a)) - 10)) a := by
    have hmargin : HasDerivAt
        (fun x : ℝ => (1 - 10 * ε * (1 + x)))
        (-(10 * ε)) a := by
      have h :=
        (hasDerivAt_const a (1 : ℝ)).sub
          ((hasDerivAt_const a (10 * ε)).mul
            ((hasDerivAt_const a (1 : ℝ)).add
              (hasDerivAt_id a)))
      convert! h using 1; simp only [Pi.add_apply, id, zero_mul, zero_add, mul_one, zero_sub]
    have hexp : HasDerivAt
        (fun x : ℝ => Real.exp (ε * x))
        (Real.exp (ε * a) * ε) a := by
      convert! ((hasDerivAt_id a).const_mul ε).exp
        using 1; simp only [id, mul_one]
    have h := hmargin.mul hexp
    convert! h using 1; simp only [neg_mul]; ring
  apply antitoneOn_of_deriv_nonpos
    (convex_Ici (0 : ℝ))
  · have hc : Continuous f := by
      try dsimp [f]
      fun_prop
    exact hc.continuousOn
  · intro a ha
    exact (hderiv a).differentiableAt.differentiableWithinAt
  · intro a ha
    rw [(hderiv a).deriv]
    have ha0 : 0 ≤ a := by
      have h := interior_subset ha
      exact h
    have hmargin : (1 - 10 * ε * (1 + a)) ≤ 1 := by
      linarith [mul_nonneg hε.le
        (show 0 ≤ 1 + a by linarith)]
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg hε.le (Real.exp_pos _).le)
      (by linarith)

private theorem upperShortMargin_mul_exp_le_zero_value
    {ε a : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) :
    (1 - 10 * ε * (1 + a)) * Real.exp (ε * a) ≤
      1 - 10 * ε := by
  have h := upperShortMargin_mul_exp_antitone hε
    (show (0 : ℝ) ∈ Ici 0 by simp only [mem_Ici, Std.le_refl])
    (show a ∈ Ici 0 from ha) ha
  simpa only [ge_iff_le, add_zero, mul_one, mul_zero, Real.exp_zero] using! h

private theorem upperFirstBranch_shortRatio_le
    {ε u a : ℝ}
    (hε : 0 < ε) (ha : 0 ≤ a)
    (hulower : -1 ≤ u)
    (huupper : u ≤ 1 + ε / 2)
    (hmargin : 0 ≤ (1 - 10 * ε * (1 + a))) :
    (1 - 10 * ε * (1 + a)) *
        Real.exp ((u - 1) * a) *
          (Real.cosh (u * a) / Real.cosh a) ≤
      1 - 4 * ε := by
  have hmarginupper :
      (1 - 10 * ε * (1 + a)) ≤ 1 - 10 * ε := by
    linarith [mul_nonneg hε.le ha]
  by_cases hubounded : u ≤ 1
  · have huexp :
        Real.exp ((u - 1) * a) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr hubounded) ha
    have huabs : |u| ≤ 1 :=
      (abs_le).mpr ⟨hulower, hubounded⟩
    have hcosh : Real.cosh (u * a) ≤ Real.cosh a := by
      apply Real.cosh_le_cosh.mpr
      rw [abs_mul, abs_of_nonneg ha]
      exact (mul_le_mul_of_nonneg_right huabs ha).trans
        (by simp only [one_mul, Std.le_refl])
    have hratio :
        Real.cosh (u * a) / Real.cosh a ≤ 1 := by
      exact (div_le_one (Real.cosh_pos a)).mpr hcosh
    calc
      (1 - 10 * ε * (1 + a)) *
          Real.exp ((u - 1) * a) *
            (Real.cosh (u * a) / Real.cosh a) ≤
        (1 - 10 * ε * (1 + a)) * 1 * 1 := by
          gcongr
      _ = (1 - 10 * ε * (1 + a)) := by ring
      _ ≤ 1 - 10 * ε := hmarginupper
      _ ≤ 1 - 4 * ε := by linarith
  · have hugreater : 1 ≤ u :=
      (le_of_not_ge hubounded)
    have hδ : 0 ≤ u - 1 := by linarith
    have hratio :
        Real.cosh (u * a) / Real.cosh a ≤
          Real.exp ((u - 1) * a) := by
      convert! cosh_ratio_upper ha hδ using 1; ring_nf
    have hdouble :
        Real.exp (2 * (u - 1) * a) ≤
          Real.exp (ε * a) := by
      apply Real.exp_le_exp.mpr
      linarith [mul_nonneg
        (show 0 ≤ ε - 2 * (u - 1) by linarith)
        ha]
    calc
      (1 - 10 * ε * (1 + a)) *
          Real.exp ((u - 1) * a) *
            (Real.cosh (u * a) / Real.cosh a) ≤
        (1 - 10 * ε * (1 + a)) *
          Real.exp ((u - 1) * a) *
            Real.exp ((u - 1) * a) := by
          gcongr
      _ = (1 - 10 * ε * (1 + a)) *
          Real.exp (2 * (u - 1) * a) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        ring_nf
      _ ≤ (1 - 10 * ε * (1 + a)) *
          Real.exp (ε * a) :=
        mul_le_mul_of_nonneg_left hdouble hmargin
      _ ≤ 1 - 10 * ε :=
        upperShortMargin_mul_exp_le_zero_value
          hε ha
      _ ≤ 1 - 4 * ε := by linarith

private theorem upperFirstBranch_shortMeasure_pointwise
    {ε ℓ u a : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (ha : 0 < a)
    (hulower : -1 ≤ u)
    (huupper : u ≤ 1 + ε / 2)
    (hmargin : 0 ≤ (1 - 10 * ε * (1 + a))) :
    ℓ * (-shortShellDensity ε a) * Real.cosh (u * a) ≤
      (1 - 4 * ε) *
        upperGammaMeasureDensity ℓ (1 + u) a := by
  have hfactor : 0 ≤ 1 - 4 * ε := by
    linarith
  have hratio := upperFirstBranch_shortRatio_le
    hε ha.le hulower huupper hmargin
  have hvariance :=
    (upperGammaVarianceDensity_pointwise_bounds
      (η := 1 + u) hℓ ha).1
  have hbase :
      (ℓ / 2) * Real.exp (-(1 + u) * a) /
          a ^ 2 ≤
        upperGammaMeasureDensity ℓ (1 + u) a := by
    apply (div_le_iff₀
      (sq_pos_of_pos ha)).2
    linarith
  have hbasepositive :
      0 ≤ (ℓ / 2) *
        Real.exp (-(1 + u) * a) / a ^ 2 := by
    positivity
  have hidentity :
      ℓ * (-shortShellDensity ε a) *
          Real.cosh (u * a) =
        ((1 - 10 * ε * (1 + a)) *
          Real.exp ((u - 1) * a) *
            (Real.cosh (u * a) / Real.cosh a)) *
          ((ℓ / 2) * Real.exp (-(1 + u) * a) /
            a ^ 2) := by
    have hexp :
        Real.exp (a * (u - 1)) *
          Real.exp (-(a * (1 + u))) =
            Real.exp (-(a * 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    unfold shortShellDensity
    field_simp [ha.ne', (Real.cosh_pos a).ne']
    rw [← hexp]
    ring
  rw [hidentity]
  calc
    ((1 - 10 * ε * (1 + a)) *
        Real.exp ((u - 1) * a) *
          (Real.cosh (u * a) / Real.cosh a)) *
        ((ℓ / 2) * Real.exp (-(1 + u) * a) /
          a ^ 2) ≤
      (1 - 4 * ε) *
        ((ℓ / 2) * Real.exp (-(1 + u) * a) /
          a ^ 2) :=
      mul_le_mul_of_nonneg_right hratio hbasepositive
    _ ≤ (1 - 4 * ε) *
          upperGammaMeasureDensity ℓ (1 + u) a :=
      mul_le_mul_of_nonneg_left hbase hfactor

private theorem upperFirstBranch_shortDamping_le_gamma
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3) (10 * Real.log (1 / ε)),
      0 ≤ (1 - 10 * ε * (1 + a)))
    (T : ℝ) :
    upperShortShellDamping ε ℓ (u - 1) T ≤
      (1 - 4 * ε) * upperGammaDamping ℓ (1 + u) T := by
  let a₀ : ℝ := (ε ^ 3)
  let A : ℝ := (10 * Real.log (1 / ε))
  let η : ℝ := 1 + u
  have hη : 0 < η := by
    try dsimp [η]
    linarith
  have ha₀ : 0 < a₀ := by
    try dsimp [a₀]
    positivity
  have hfactor : 0 ≤ 1 - 4 * ε := by
    linarith
  have hsubset : Ioc a₀ A ⊆ Ioi (0 : ℝ) := by
    intro a ha
    exact ha₀.trans ha.1
  have hgamma :=
    upperGammaDampingIntegrand_integrable hℓ hη T
  have hgammaOn : IntegrableOn
      (upperGammaDampingIntegrand ℓ η T)
      (Ioc a₀ A) :=
    hgamma.mono_set hsubset
  have hscaledOn : IntegrableOn
      (fun a : ℝ => (1 - 4 * ε) *
        upperGammaDampingIntegrand ℓ η T a)
      (Ioc a₀ A) :=
    hgammaOn.const_mul (1 - 4 * ε)
  have hs := shortShellDensity_intervalIntegrable hε horder
  have hcosh : Continuous
      (fun a : ℝ => Real.cosh (u * a)) := by
    fun_prop
  have hosc : Continuous
      (fun a : ℝ => 1 - Real.cos (a * T)) := by
    fun_prop
  have hshortInterval : IntervalIntegrable
      (fun a : ℝ =>
        ℓ * (-shortShellDensity ε a) *
          Real.cosh (u * a) *
            (1 - Real.cos (a * T)))
      volume a₀ A := by
    have hneg : IntervalIntegrable
        (fun a : ℝ => -shortShellDensity ε a)
        volume a₀ A := by
      simpa only  using! hs.neg
    have hconst := hneg.const_mul ℓ
    have hwithCosh :=
      hconst.mul_continuousOn hcosh.continuousOn
    exact hwithCosh.mul_continuousOn hosc.continuousOn
  have hshortOn : IntegrableOn
      (fun a : ℝ =>
        ℓ * (-shortShellDensity ε a) *
          Real.cosh (u * a) *
            (1 - Real.cos (a * T)))
      (Ioc a₀ A) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (show a₀ ≤ A by exact horder)).mp hshortInterval
  have hpoint (a : ℝ) (ha : a ∈ Ioc a₀ A) :
      ℓ * (-shortShellDensity ε a) *
          Real.cosh (u * a) *
            (1 - Real.cos (a * T)) ≤
        (1 - 4 * ε) *
          upperGammaDampingIntegrand ℓ η T a := by
    have hcomparison :=
      upperFirstBranch_shortMeasure_pointwise
        hε hεsmall hℓ (ha₀.trans ha.1)
        hulower.le huupper
        (hmargin a ⟨ha.1.le, ha.2⟩)
    have hoscNonneg : 0 ≤ 1 - Real.cos (a * T) :=
      sub_nonneg.mpr (Real.cos_le_one _)
    have hmul :=
      mul_le_mul_of_nonneg_right hcomparison hoscNonneg
    simpa only [mul_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, upperGammaDampingIntegrand,
      ge_iff_le] using! hmul
  have hmono := setIntegral_mono_on
    hshortOn hscaledOn measurableSet_Ioc hpoint
  have hnonnegative :
      0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        upperGammaDampingIntegrand ℓ η T := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    unfold upperGammaDampingIntegrand
    exact mul_nonneg
      (sub_nonneg.mpr (Real.cos_le_one _))
      (upperGammaMeasureDensity_pos hℓ ha).le
  have haesubset :
      Ioc a₀ A ≤ᶠ[ae (volume : Measure ℝ)] Ioi 0 :=
    Filter.Eventually.of_forall fun a ha => hsubset ha
  have hrestrict :=
    setIntegral_mono_set hgamma hnonnegative haesubset
  have hscaleRestrict :=
    mul_le_mul_of_nonneg_left hrestrict hfactor
  have hshortEq :
      upperShortShellDamping ε ℓ (u - 1) T =
        ∫ a : ℝ in Ioc a₀ A,
          ℓ * (-shortShellDensity ε a) *
            Real.cosh (u * a) *
              (1 - Real.cos (a * T)) := by
    unfold upperShortShellDamping
    have hu : 1 + (u - 1) = u := by ring
    rw [hu, ← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le horder]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro a ha
    ring
  calc
    upperShortShellDamping ε ℓ (u - 1) T =
        ∫ a : ℝ in Ioc a₀ A,
          ℓ * (-shortShellDensity ε a) *
            Real.cosh (u * a) *
              (1 - Real.cos (a * T)) := hshortEq
    _ ≤ ∫ a : ℝ in Ioc a₀ A,
          (1 - 4 * ε) *
            upperGammaDampingIntegrand ℓ η T a := hmono
    _ = (1 - 4 * ε) *
          ∫ a : ℝ in Ioc a₀ A,
            upperGammaDampingIntegrand ℓ η T a := by
      rw [integral_const_mul]
    _ ≤ (1 - 4 * ε) *
          ∫ a : ℝ in Ioi 0,
            upperGammaDampingIntegrand ℓ η T a :=
      hscaleRestrict
    _ = (1 - 4 * ε) *
          upperGammaDamping ℓ (1 + u) T := by
      rfl

private theorem positiveShellDamping_nonneg
    {ε ℓ δ T : ℝ}
    (hℓ : 0 ≤ ℓ) :
    0 ≤ positiveShellDamping ε ℓ δ T := by
  unfold positiveShellDamping
  apply mul_nonneg hℓ
  apply intervalIntegral.integral_nonneg
    (show (ε⁻¹ ^ 3) ≤ (ε⁻¹ ^ 3) + 1 by linarith)
  intro a ha
  unfold positiveShellDensity
  exact mul_nonneg
    (mul_nonneg
      (div_nonneg (shellWeight_pos ε).le
        (Real.cosh_pos a).le)
      (Real.cosh_pos _).le)
    (sub_nonneg.mpr (Real.cos_le_one _))

private noncomputable def upperFirstBranchSaddleDamping
    (ε ℓ u T : ℝ) : ℝ :=
  upperGammaDamping ℓ (1 + u) T +
    positiveShellDamping ε ℓ (u - 1) T -
      upperShortShellDamping ε ℓ (u - 1) T

private theorem upperFirstBranchSaddleDamping_lower_bound
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3) (10 * Real.log (1 / ε)),
      0 ≤ (1 - 10 * ε * (1 + a)))
    (T : ℝ) :
    4 * ε * upperGammaDamping ℓ (1 + u) T ≤
      upperFirstBranchSaddleDamping ε ℓ u T := by
  have hshort := upperFirstBranch_shortDamping_le_gamma
    hε hεsmall hℓ hulower huupper horder hmargin T
  have hpositive := positiveShellDamping_nonneg
    (ε := ε) (δ := u - 1) (T := T) hℓ.le
  unfold upperFirstBranchSaddleDamping
  linarith

private theorem saddle_shifted_complexCos_re
    (a T u : ℝ) :
    (Complex.cos
      ((a : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ)))).re =
      Real.cos (a * T) * Real.cosh (a * u) := by
  have harg :
      (a : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ)) =
        ((a * T : ℝ) : ℂ) +
          ((a * u : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.cos_add, Complex.cos_mul_I,
    Complex.sin_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sin,
    ← Complex.ofReal_sinh]
  simp only [Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, mul_one]

private theorem saddle_complexShellInterval_re
    (w : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b)
    (hw : ContinuousOn w (Icc a b))
    (T u : ℝ) :
    (∫ x in a..b,
      (w x : ℂ) *
        (Complex.cos
          ((x : ℂ) *
            ((T : ℂ) + Complex.I * (u : ℂ))) - 1)).re =
      ∫ x in a..b,
        w x *
          (Real.cos (x * T) * Real.cosh (x * u) - 1) := by
  let F : ℝ → ℂ := fun x =>
    (w x : ℂ) *
      (Complex.cos
        ((x : ℂ) *
          ((T : ℂ) + Complex.I * (u : ℂ))) - 1)
  have hwcomplex : ContinuousOn
      (fun x : ℝ => (w x : ℂ))
      (Icc a b) :=
    Complex.ofRealCLM.continuous.comp_continuousOn hw
  have hkernel : Continuous
      (fun x : ℝ =>
        Complex.cos
          ((x : ℂ) *
            ((T : ℂ) + Complex.I * (u : ℂ))) - 1) := by
    fun_prop
  have hF : IntervalIntegrable F volume a b := by
    exact (hwcomplex.mul hkernel.continuousOn).intervalIntegrable_of_Icc
      hab
  calc
    (∫ x in a..b,
      (w x : ℂ) *
        (Complex.cos
          ((x : ℂ) *
            ((T : ℂ) + Complex.I * (u : ℂ))) - 1)).re =
      ∫ x in a..b, (F x).re := by
        exact (Complex.reCLM.intervalIntegral_comp_comm hF).symm
    _ = ∫ x in a..b,
        w x *
          (Real.cos (x * T) * Real.cosh (x * u) - 1) := by
      apply intervalIntegral.integral_congr
      intro x hx
      try dsimp [F]
      rw [Complex.mul_re, Complex.sub_re,
        saddle_shifted_complexCos_re]
      simp only [Complex.ofReal_re, Complex.one_re, Complex.ofReal_im, Complex.sub_im,
        Complex.one_im, sub_zero,
        zero_mul]

private theorem shortShellDensity_continuousOn_support
    {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (shortShellDensity ε)
      (Icc (ε ^ 3) (10 * Real.log (1 / ε))) := by
  have hn : Continuous
      (fun a : ℝ =>
        (1 - 10 * ε * (1 + a)) * Real.exp (-2 * a)) := by
    fun_prop
  have hd : Continuous
      (fun a : ℝ =>
        2 * a ^ 2 * Real.cosh a) := by
    fun_prop
  unfold shortShellDensity
  exact (hn.continuousOn.div hd.continuousOn
    (fun a ha => by
      have hcutoff : 0 < (ε ^ 3) := by
        positivity
      have ha0 : 0 < a := hcutoff.trans_le ha.1
      positivity)).neg

private theorem mellinShellPhase_shifted_re
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (T u : ℝ) :
    (mellinShellPhase ε
      ((T : ℂ) + Complex.I * (u : ℂ))).re =
      (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
        shortShellDensity ε a *
          (Real.cos (a * T) * Real.cosh (a * u) - 1)) +
      (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
        positiveShellDensity ε a *
          (Real.cos (a * T) * Real.cosh (a * u) - 1)) := by
  unfold mellinShellPhase
  rw [Complex.add_re]
  congr 1
  · exact saddle_complexShellInterval_re
      (shortShellDensity ε) horder
      (shortShellDensity_continuousOn_support hε) T u
  · exact saddle_complexShellInterval_re
      (positiveShellDensity ε)
      (show (ε⁻¹ ^ 3) ≤ (ε⁻¹ ^ 3) + 1 by
        linarith)
      (positiveShellDensity_continuous ε).continuousOn T u

private theorem saddle_shellInterval_hyperbolic_sub_oscillatory
    (w : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b)
    (hw : ContinuousOn w (Icc a b))
    (T u : ℝ) :
    (∫ x in a..b,
        w x * (Real.cosh (x * u) - 1)) -
      (∫ x in a..b,
        w x *
          (Real.cos (x * T) * Real.cosh (x * u) - 1)) =
      ∫ x in a..b,
        w x * Real.cosh (x * u) *
          (1 - Real.cos (x * T)) := by
  have hhyper : ContinuousOn
      (fun x : ℝ =>
        w x * (Real.cosh (x * u) - 1))
      (Icc a b) := by
    apply hw.mul
    exact (by fun_prop :
      Continuous (fun x : ℝ =>
        Real.cosh (x * u) - 1)).continuousOn
  have hosc : ContinuousOn
      (fun x : ℝ =>
        w x *
          (Real.cos (x * T) * Real.cosh (x * u) - 1))
      (Icc a b) := by
    apply hw.mul
    exact (by fun_prop :
      Continuous (fun x : ℝ =>
        Real.cos (x * T) * Real.cosh (x * u) - 1)).continuousOn
  rw [← intervalIntegral.integral_sub
    (hhyper.intervalIntegrable_of_Icc hab)
    (hosc.intervalIntegrable_of_Icc hab)]
  apply intervalIntegral.integral_congr
  intro x hx
  ring

private theorem saddleShellPhase_damping_identity
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ T u : ℝ) :
    ℓ *
      (realHyperbolicShellPhase ε u -
        (mellinShellPhase ε
          ((T : ℂ) + Complex.I * (u : ℂ))).re) =
      positiveShellDamping ε ℓ (u - 1) T -
        upperShortShellDamping ε ℓ (u - 1) T := by
  have hshort :=
    saddle_shellInterval_hyperbolic_sub_oscillatory
      (shortShellDensity ε) horder
      (shortShellDensity_continuousOn_support hε) T u
  have hpositive :=
    saddle_shellInterval_hyperbolic_sub_oscillatory
      (positiveShellDensity ε)
      (show (ε⁻¹ ^ 3) ≤ (ε⁻¹ ^ 3) + 1 by
        linarith)
      (positiveShellDensity_continuous ε).continuousOn T u
  rw [mellinShellPhase_shifted_re hε horder T u]
  unfold realHyperbolicShellPhase
    positiveShellDamping upperShortShellDamping
  have hu : 1 + (u - 1) = u := by ring
  simp only [hu]
  have hshortNormalized :
      (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
        (-shortShellDensity ε a) *
          Real.cosh (u * a) *
            (1 - Real.cos (a * T))) =
        -(∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
          shortShellDensity ε a *
            Real.cosh (a * u) *
              (1 - Real.cos (a * T))) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro a ha
    change
      -shortShellDensity ε a * Real.cosh (u * a) *
          (1 - Real.cos (a * T)) =
        -(shortShellDensity ε a * Real.cosh (a * u) *
          (1 - Real.cos (a * T)))
    rw [mul_comm u a]
    ring
  have hpositiveNormalized :
      (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
        positiveShellDensity ε a *
          Real.cosh (u * a) *
            (1 - Real.cos (a * T))) =
        ∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
          positiveShellDensity ε a *
            Real.cosh (a * u) *
              (1 - Real.cos (a * T)) := by
    apply intervalIntegral.integral_congr
    intro a ha
    change
      positiveShellDensity ε a * Real.cosh (u * a) *
          (1 - Real.cos (a * T)) =
        positiveShellDensity ε a * Real.cosh (a * u) *
          (1 - Real.cos (a * T))
    rw [mul_comm u a]
  rw [hshortNormalized, hpositiveNormalized]
  linear_combination ℓ * hshort + ℓ * hpositive

end

section

open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology

private noncomputable def radialCriticalLogProfile {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) (u : ℝ) : ℂ :=
  Real.exp (-((d : ℝ) / 2) * u) •
    radialProfile hd f (Real.exp (-u))

private theorem radialCriticalLogProfile_eq_reflected_tilt {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (u : ℝ) :
    radialCriticalLogProfile hd f u =
      schwartzExponentialTilt (radialSchwartzProfile hd f)
        ((d : ℝ) / 2) 1 (-u) := by
  simp only [radialCriticalLogProfile, neg_mul, Complex.real_smul, Complex.ofReal_exp,
    Complex.ofReal_neg,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat,
      schwartzExponentialTilt,
    mul_neg, one_mul, radialSchwartzProfile_apply]

private theorem radialCriticalLogProfile_integrable {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) :
    Integrable (radialCriticalLogProfile hd f) := by
  have hdimension : 0 < (d : ℝ) / 2 :=
    div_pos (by exact_mod_cast hd) (by norm_num)
  have h := (schwartzExponentialTilt_integrable
    (radialSchwartzProfile hd f) hdimension
    (show (0 : ℝ) < 1 by norm_num)).comp_neg
  apply h.congr
  filter_upwards [] with u
  exact (radialCriticalLogProfile_eq_reflected_tilt hd f u).symm

private theorem radialCriticalLogProfile_continuous {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) :
    Continuous (radialCriticalLogProfile hd f) := by
  unfold radialCriticalLogProfile
  exact (by fun_prop :
    Continuous (fun u : ℝ => Real.exp (-((d : ℝ) / 2) * u))).smul
      ((radialProfile_continuous hd f).comp
        (by fun_prop : Continuous (fun u : ℝ => Real.exp (-u))))

private theorem radialCriticalLogProfile_fourier_integrable {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) :
    Integrable (𝓕 (radialCriticalLogProfile hd f) : ℝ → ℂ) := by
  have hdimension : 0 < (d : ℝ) / 2 :=
    div_pos (by exact_mod_cast hd) (by norm_num)
  let G : ℝ → ℂ :=
    schwartzExponentialTilt (radialSchwartzProfile hd f)
      ((d : ℝ) / 2) 1
  have hG : Integrable (𝓕 G : ℝ → ℂ) :=
    schwartzExponentialTilt_fourier_integrable
      (radialSchwartzProfile hd f) hdimension
      (show (0 : ℝ) < 1 by norm_num)
  have hneg := hG.comp_neg
  apply hneg.congr
  filter_upwards [] with u
  have hprofile :
      radialCriticalLogProfile hd f =
        (fun v : ℝ => G (-v)) := by
    funext v
    exact radialCriticalLogProfile_eq_reflected_tilt hd f v
  rw [hprofile]
  simpa only [LinearIsometryEquiv.coe_neg, Function.comp_def] using!
    (Real.fourier_comp_linearIsometry
      (LinearIsometryEquiv.neg ℝ) G u).symm

private theorem radialMellinFrequency_eq_criticalLogFourier {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (t : ℝ) :
    radialMellinFrequency hd f t =
      (𝓕 (radialCriticalLogProfile hd f) : ℝ → ℂ)
        (-t / (2 * Real.pi)) := by
  exact radialMellinFrequency_eq_fourier hd f t

private theorem plusSaddleFourierData_continuous {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    Continuous (plusSaddleFourierData ε ℓ) := by
  unfold plusSaddleFourierData
  exact (plusSaddleSpectrum_continuous hε hℓ horder).comp
    (by fun_prop)

private theorem minusSaddleFourierData_continuous {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    Continuous (minusSaddleFourierData ε ℓ) := by
  unfold minusSaddleFourierData
  exact (minusSaddleSpectrum_continuous hε hℓ horder).comp
    (by fun_prop)

private theorem plusSaddleFourierData_integrable {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    Integrable (plusSaddleFourierData ε ℓ) := by
  have hnorm : Integrable
      (fun y : ℝ => ‖plusSaddleFourierData ε ℓ y‖) := by
    simpa only [Real.norm_eq_abs, pow_zero, one_mul] using!
      plusSaddleFourierData_norm_moment_integrable hε hℓ horder 0
  exact (integrable_norm_iff
    (plusSaddleFourierData_continuous
      hε hℓ horder).aestronglyMeasurable).mp hnorm

private theorem minusSaddleFourierData_integrable {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    Integrable (minusSaddleFourierData ε ℓ) := by
  have hnorm : Integrable
      (fun y : ℝ => ‖minusSaddleFourierData ε ℓ y‖) := by
    simpa only [Real.norm_eq_abs, pow_zero, one_mul] using!
      minusSaddleFourierData_norm_moment_integrable hε hℓ horder 0
  exact (integrable_norm_iff
    (minusSaddleFourierData_continuous
      hε hℓ horder).aestronglyMeasurable).mp hnorm

private theorem radialProfile_eq_plusSaddleProfile_of_source
    {ε : ℝ} {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = plusSaddleFunction ε d x)
    {r : ℝ} (hr : 0 ≤ r) :
    radialProfile hd f r = plusSaddleProfile ε ((d : ℝ) / 2) r := by
  unfold radialProfile
  rw [hf]
  simp only [plusSaddleFunction, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr,
    norm_radialUnitDirection hd,
    mul_one]

private theorem radialProfile_eq_minusSaddleProfile_of_source
    {ε : ℝ} {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = minusSaddleFunction ε d x)
    {r : ℝ} (hr : 0 ≤ r) :
    radialProfile hd f r = minusSaddleProfile ε ((d : ℝ) / 2) r := by
  unfold radialProfile
  rw [hf]
  simp only [minusSaddleFunction, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr,
    norm_radialUnitDirection hd,
    mul_one]

private theorem exp_neg_rpow_neg_half_dimension {d : ℕ} (u : ℝ) :
    (Real.exp (-u)) ^ (-((d : ℝ) / 2)) =
      Real.exp (((d : ℝ) / 2) * u) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos (-u)), Real.log_exp]
  congr 1
  ring

private theorem plusSaddleCriticalLogProfile_eq_fourierInv
    {ε : ℝ} {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = plusSaddleFunction ε d x) :
    radialCriticalLogProfile hd f =
      (𝓕⁻ (plusSaddleFourierData ε ((d : ℝ) / 2)) : ℝ → ℂ) := by
  funext u
  unfold radialCriticalLogProfile
  rw [radialProfile_eq_plusSaddleProfile_of_source
    hd f hf (Real.exp_pos (-u)).le]
  rw [plusSaddleProfile_eq_fourier ε ((d : ℝ) / 2)
    (Real.exp_pos (-u))]
  rw [exp_neg_rpow_neg_half_dimension,
    Real.log_exp, Real.fourierInv_eq_fourier_neg]
  simp only [Complex.real_smul]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  simp only [neg_mul, neg_add_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]

private theorem minusSaddleCriticalLogProfile_eq_fourierInv
    {ε : ℝ} {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = minusSaddleFunction ε d x) :
    radialCriticalLogProfile hd f =
      (𝓕⁻ (minusSaddleFourierData ε ((d : ℝ) / 2)) : ℝ → ℂ) := by
  funext u
  unfold radialCriticalLogProfile
  rw [radialProfile_eq_minusSaddleProfile_of_source
    hd f hf (Real.exp_pos (-u)).le]
  rw [minusSaddleProfile_eq_fourier ε ((d : ℝ) / 2)
    (Real.exp_pos (-u))]
  rw [exp_neg_rpow_neg_half_dimension,
    Real.log_exp, Real.fourierInv_eq_fourier_neg]
  simp only [Complex.real_smul]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  simp only [neg_mul, neg_add_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]

private theorem plusSaddleFourierData_fourier_integrable_of_source
    {ε : ℝ} {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = plusSaddleFunction ε d x) :
    Integrable
      (𝓕 (plusSaddleFourierData ε ((d : ℝ) / 2)) : ℝ → ℂ) := by
  have hlog := (radialCriticalLogProfile_integrable hd f).comp_neg
  apply hlog.congr
  filter_upwards [] with u
  have h := congrFun
    (plusSaddleCriticalLogProfile_eq_fourierInv hd f hf) (-u)
  simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using! h

private theorem minusSaddleFourierData_fourier_integrable_of_source
    {ε : ℝ} {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = minusSaddleFunction ε d x) :
    Integrable
      (𝓕 (minusSaddleFourierData ε ((d : ℝ) / 2)) : ℝ → ℂ) := by
  have hlog := (radialCriticalLogProfile_integrable hd f).comp_neg
  apply hlog.congr
  filter_upwards [] with u
  have h := congrFun
    (minusSaddleCriticalLogProfile_eq_fourierInv hd f hf) (-u)
  simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using! h

private theorem plusSaddle_radialMellinFrequency_of_source
    {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = plusSaddleFunction ε d x)
    (t : ℝ) :
    radialMellinFrequency hd f t =
      plusSaddleSpectrum ε ((d : ℝ) / 2) t := by
  have hdimension : 0 < (d : ℝ) / 2 :=
    div_pos (by exact_mod_cast hd) (by norm_num)
  have hdata := plusSaddleFourierData_integrable
    hε hdimension horder
  have hfourier := plusSaddleFourierData_fourier_integrable_of_source
    hd f hf
  have hcontinuous := plusSaddleFourierData_continuous
    hε hdimension horder
  rw [radialMellinFrequency_eq_criticalLogFourier,
    plusSaddleCriticalLogProfile_eq_fourierInv hd f hf]
  rw [hdata.fourier_fourierInv_eq hfourier
    hcontinuous.continuousAt]
  unfold plusSaddleFourierData
  congr 1
  field_simp [Real.pi_ne_zero]

private theorem minusSaddle_radialMellinFrequency_of_source
    {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = minusSaddleFunction ε d x)
    (t : ℝ) :
    radialMellinFrequency hd f t =
      minusSaddleSpectrum ε ((d : ℝ) / 2) t := by
  have hdimension : 0 < (d : ℝ) / 2 :=
    div_pos (by exact_mod_cast hd) (by norm_num)
  have hdata := minusSaddleFourierData_integrable
    hε hdimension horder
  have hfourier := minusSaddleFourierData_fourier_integrable_of_source
    hd f hf
  have hcontinuous := minusSaddleFourierData_continuous
    hε hdimension horder
  rw [radialMellinFrequency_eq_criticalLogFourier,
    minusSaddleCriticalLogProfile_eq_fourierInv hd f hf]
  rw [hdata.fourier_fourierInv_eq hfourier
    hcontinuous.continuousAt]
  unfold minusSaddleFourierData
  congr 1
  field_simp [Real.pi_ne_zero]

private theorem radialMellinFrequency_injective {d : ℕ}
    (hd : 0 < d) {f g : TestFunction d}
    (hf : IsRadial f) (hg : IsRadial g)
    (hfrequency : ∀ t : ℝ,
      radialMellinFrequency hd f t =
        radialMellinFrequency hd g t) :
    f = g := by
  have hfourier :
      (𝓕 (radialCriticalLogProfile hd f) : ℝ → ℂ) =
        (𝓕 (radialCriticalLogProfile hd g) : ℝ → ℂ) := by
    funext ξ
    have h := hfrequency (-(2 * Real.pi * ξ))
    rw [radialMellinFrequency_eq_criticalLogFourier,
      radialMellinFrequency_eq_criticalLogFourier] at h
    convert! h using 1 <;> field_simp [Real.pi_ne_zero]
  have hlog : radialCriticalLogProfile hd f =
      radialCriticalLogProfile hd g := by
    funext u
    calc
      radialCriticalLogProfile hd f u =
          (𝓕⁻ (𝓕 (radialCriticalLogProfile hd f) : ℝ → ℂ) :
            ℝ → ℂ) u :=
        ((radialCriticalLogProfile_integrable hd f).fourierInv_fourier_eq
          (radialCriticalLogProfile_fourier_integrable hd f)
          (radialCriticalLogProfile_continuous hd f).continuousAt).symm
      _ = (𝓕⁻ (𝓕 (radialCriticalLogProfile hd g) : ℝ → ℂ) :
            ℝ → ℂ) u := by rw [hfourier]
      _ = radialCriticalLogProfile hd g u :=
        (radialCriticalLogProfile_integrable hd g).fourierInv_fourier_eq
          (radialCriticalLogProfile_fourier_integrable hd g)
          (radialCriticalLogProfile_continuous hd g).continuousAt
  have hpositive (r : ℝ) (hr : 0 < r) :
      radialProfile hd f r = radialProfile hd g r := by
    have h := congrFun hlog (-Real.log r)
    simp only [radialCriticalLogProfile, neg_neg,
      Real.exp_log hr, Complex.real_smul] at h
    apply mul_left_cancel₀
      (Complex.ofReal_ne_zero.mpr
        (Real.exp_ne_zero (-((d : ℝ) / 2) * -Real.log r)))
    exact h
  have heventually :
      radialProfile hd f =ᶠ[𝓝[>] (0 : ℝ)]
        radialProfile hd g := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hpositive r hr
  have hleft :
      Tendsto (radialProfile hd f)
        (𝓝[>] (0 : ℝ)) (𝓝 (radialProfile hd f 0)) :=
    (radialProfile_continuous hd f).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hright :
      Tendsto (radialProfile hd f)
        (𝓝[>] (0 : ℝ)) (𝓝 (radialProfile hd g 0)) :=
    ((radialProfile_continuous hd g).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).congr' heventually.symm
  have hzero : radialProfile hd f 0 = radialProfile hd g 0 :=
    tendsto_nhds_unique hleft hright
  apply SchwartzMap.ext
  intro x
  by_cases hx : x = 0
  · subst x
    simpa only [radialProfile_zero] using! hzero
  · have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    calc
      f x = radialProfile hd f ‖x‖ :=
        (radialProfile_norm hd f hf x).symm
      _ = radialProfile hd g ‖x‖ := hpositive ‖x‖ hr
      _ = g x := radialProfile_norm hd g hg x

private theorem plusSaddle_radial_of_source {ε : ℝ} {d : ℕ}
    (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = plusSaddleFunction ε d x) :
    IsRadial f := by
  intro x y hxy
  rw [hf x, hf y]
  exact plusSaddleFunction_radial ε d x y hxy

private theorem minusSaddle_radial_of_source {ε : ℝ} {d : ℕ}
    (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = minusSaddleFunction ε d x) :
    IsRadial f := by
  intro x y hxy
  rw [hf x, hf y]
  exact minusSaddleFunction_radial ε d x y hxy

private theorem plusSaddle_real_of_source {ε : ℝ} {d : ℕ}
    (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = plusSaddleFunction ε d x) :
    IsRealValued f := by
  intro x
  rw [hf x]
  exact plusSaddleFunction_real ε d x

private theorem minusSaddle_real_of_source {ε : ℝ} {d : ℕ}
    (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = minusSaddleFunction ε d x) :
    IsRealValued f := by
  intro x
  rw [hf x]
  exact minusSaddleFunction_real ε d x

private theorem saddleSource_fourier_minus_eq_plus
    {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (fminus fplus : TestFunction d)
    (hminus : ∀ x : Euclidean d,
      fminus x = minusSaddleFunction ε d x)
    (hplus : ∀ x : Euclidean d,
      fplus x = plusSaddleFunction ε d x) :
    (𝓕 fminus : TestFunction d) = fplus := by
  have hdimension : 0 < (d : ℝ) / 2 :=
    div_pos (by exact_mod_cast hd) (by norm_num)
  have hrminus : IsRadial fminus :=
    minusSaddle_radial_of_source fminus hminus
  have hrplus : IsRadial fplus :=
    plusSaddle_radial_of_source fplus hplus
  apply radialMellinFrequency_injective hd
    (gaussianMellin_fourier_radial hrminus) hrplus
  intro t
  calc
    radialMellinFrequency hd
        (𝓕 fminus : TestFunction d) t =
      mellinMultiplier ((d : ℝ) / 2) t *
        radialMellinFrequency hd fminus (-t) :=
      radialMellinMultiplier hd fminus hrminus t
    _ = mellinMultiplier ((d : ℝ) / 2) t *
        minusSaddleSpectrum ε ((d : ℝ) / 2) (-t) := by
      rw [minusSaddle_radialMellinFrequency_of_source
        hε hd horder fminus hminus]
    _ = plusSaddleSpectrum ε ((d : ℝ) / 2) t :=
      mellinMultiplier_mul_minusSaddleSpectrum_neg hdimension t
    _ = radialMellinFrequency hd fplus t :=
      (plusSaddle_radialMellinFrequency_of_source
        hε hd horder fplus hplus t).symm

private theorem saddleSource_zero_pos
    {ε : ℝ} (hε : 0 < ε) {d : ℕ}
    (fminus fplus : TestFunction d)
    (hminus : ∀ x : Euclidean d,
      fminus x = minusSaddleFunction ε d x)
    (hplus : ∀ x : Euclidean d,
      fplus x = plusSaddleFunction ε d x) :
    0 < (fminus (0 : Euclidean d)).re ∧
      0 < (fplus (0 : Euclidean d)).re := by
  rw [hminus, hplus]
  exact (saddleFunction_zero_pos hε d).symm

private theorem saddleSource_zero_eq {ε : ℝ} {d : ℕ}
    (fminus fplus : TestFunction d)
    (hminus : ∀ x : Euclidean d,
      fminus x = minusSaddleFunction ε d x)
    (hplus : ∀ x : Euclidean d,
      fplus x = plusSaddleFunction ε d x) :
    fminus (0 : Euclidean d) = fplus (0 : Euclidean d) := by
  rw [hminus, hplus, minusSaddleFunction_zero,
    plusSaddleFunction_zero]

private noncomputable def saddleSourceAdmissible
    {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    {R : ℝ} (hR : 0 < R)
    (fminus fplus : TestFunction d)
    (hminus : ∀ x : Euclidean d,
      fminus x = minusSaddleFunction ε d x)
    (hplus : ∀ x : Euclidean d,
      fplus x = plusSaddleFunction ε d x)
    (hplusnonneg : ∀ x : Euclidean d,
      0 ≤ (plusSaddleFunction ε d x).re)
    (hminusoutside : ∀ x : Euclidean d,
      R ≤ ‖x‖ → (minusSaddleFunction ε d x).re ≤ 0) :
    Admissible d := by
  have hfourier : (𝓕 fminus : TestFunction d) = fplus :=
    saddleSource_fourier_minus_eq_plus
      hε hd horder fminus fplus hminus hplus
  have hrealplus : IsRealValued fplus :=
    plusSaddle_real_of_source fplus hplus
  have hnonneg (ξ : Euclidean d) : 0 ≤ (fplus ξ).re := by
    rw [hplus ξ]
    exact hplusnonneg ξ
  have hzero : 0 < (fplus (0 : Euclidean d)).re :=
    (saddleSource_zero_pos hε fminus fplus hminus hplus).2
  refine
    { function := dilate fminus R hR
      real := (minusSaddle_real_of_source fminus hminus).dilate R hR
      radial := (minusSaddle_radial_of_source fminus hminus).dilate R hR
      fourier_real := ?_
      fourier_nonneg := ?_
      fourier_zero_pos := ?_
      outside_nonpos := ?_ }
  · intro ξ
    rw [fourier_dilate_apply, hfourier, Complex.smul_im,
      hrealplus (R⁻¹ • ξ)]
    simp only [smul_eq_mul, mul_zero]
  · intro ξ
    rw [fourier_dilate_apply, hfourier, Complex.smul_re]
    simpa only [smul_eq_mul] using!
      mul_nonneg
        (inv_nonneg.mpr (pow_nonneg hR.le d))
        (hnonneg (R⁻¹ • ξ))
  · rw [fourier_dilate_zero, hfourier, Complex.smul_re]
    simpa only [smul_eq_mul] using!
      mul_pos (inv_pos.mpr (pow_pos hR d)) hzero
  · intro x hx
    change (fminus (R • x)).re ≤ 0
    rw [hminus]
    apply hminusoutside
    have hscaled := mul_le_mul_of_nonneg_left hx hR.le
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hR, ge_iff_le, mul_one] using! hscaled

@[simp] private theorem saddleSourceAdmissible_function
    {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    {R : ℝ} (hR : 0 < R)
    (fminus fplus : TestFunction d)
    (hminus : ∀ x : Euclidean d,
      fminus x = minusSaddleFunction ε d x)
    (hplus : ∀ x : Euclidean d,
      fplus x = plusSaddleFunction ε d x)
    (hplusnonneg : ∀ x : Euclidean d,
      0 ≤ (plusSaddleFunction ε d x).re)
    (hminusoutside : ∀ x : Euclidean d,
      R ≤ ‖x‖ → (minusSaddleFunction ε d x).re ≤ 0) :
    (saddleSourceAdmissible hε hd horder hR
      fminus fplus hminus hplus hplusnonneg
      hminusoutside).function = dilate fminus R hR := by
  rfl

private theorem saddleSourceAdmissible_quotient
    {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    {R : ℝ} (hR : 0 < R)
    (fminus fplus : TestFunction d)
    (hminus : ∀ x : Euclidean d,
      fminus x = minusSaddleFunction ε d x)
    (hplus : ∀ x : Euclidean d,
      fplus x = plusSaddleFunction ε d x)
    (hplusnonneg : ∀ x : Euclidean d,
      0 ≤ (plusSaddleFunction ε d x).re)
    (hminusoutside : ∀ x : Euclidean d,
      R ≤ ‖x‖ → (minusSaddleFunction ε d x).re ≤ 0) :
    quotient (saddleSourceAdmissible hε hd horder hR
      fminus fplus hminus hplus hplusnonneg
      hminusoutside) = R ^ d := by
  have hfourier : (𝓕 fminus : TestFunction d) = fplus :=
    saddleSource_fourier_minus_eq_plus
      hε hd horder fminus fplus hminus hplus
  have hzero : 0 < (fplus (0 : Euclidean d)).re :=
    (saddleSource_zero_pos hε fminus fplus hminus hplus).2
  have hpow : R ^ d ≠ 0 := pow_ne_zero d hR.ne'
  unfold quotient
  rw [saddleSourceAdmissible_function
    hε hd horder hR fminus fplus hminus hplus
    hplusnonneg hminusoutside]
  rw [dilate_zero]
  change (fminus (0 : Euclidean d)).re /
    ((𝓕 (dilate fminus R hR) : TestFunction d)
      (0 : Euclidean d)).re = R ^ d
  rw [fourier_dilate_zero, hfourier,
    saddleSource_zero_eq fminus fplus hminus hplus,
    Complex.smul_re]
  simp only [smul_eq_mul]
  field_simp [hpow, hzero.ne']

private theorem saddleSourceAdmissible_normalizedCost
    {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    {R : ℝ} (hR : 0 < R)
    (fminus fplus : TestFunction d)
    (hminus : ∀ x : Euclidean d,
      fminus x = minusSaddleFunction ε d x)
    (hplus : ∀ x : Euclidean d,
      fplus x = plusSaddleFunction ε d x)
    (hplusnonneg : ∀ x : Euclidean d,
      0 ≤ (plusSaddleFunction ε d x).re)
    (hminusoutside : ∀ x : Euclidean d,
      R ≤ ‖x‖ → (minusSaddleFunction ε d x).re ≤ 0) :
    normalizedCost (saddleSourceAdmissible hε hd horder hR
      fminus fplus hminus hplus hplusnonneg
      hminusoutside) = R / Real.sqrt (d : ℝ) := by
  calc
    normalizedCost (saddleSourceAdmissible hε hd horder hR
        fminus fplus hminus hplus hplusnonneg
        hminusoutside) =
      (R ^ d : ℝ) ^ ((d : ℝ)⁻¹) /
        Real.sqrt (d : ℝ) := by
      unfold normalizedCost
      rw [saddleSourceAdmissible_quotient
        hε hd horder hR fminus fplus hminus hplus
        hplusnonneg hminusoutside]
    _ = R / Real.sqrt (d : ℝ) := by
      congr 1
      rw [← Real.rpow_natCast_mul hR.le]
      rw [mul_inv_cancel₀ (by exact_mod_cast hd.ne'),
        Real.rpow_one]

private noncomputable def saddleDigamma (x : ℝ) : ℝ :=
  deriv (Real.log ∘ Real.Gamma) x

private noncomputable def saddleLogRadius (ε : ℝ) (d : ℕ) (u : ℝ) : ℝ :=
  -(Real.log Real.pi) / 2 +
    saddleDigamma (((d : ℝ) / 2) * (1 + u) / 2) / 2 +
    (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
      shortShellDensity ε a * a * Real.sinh (u * a)) +
    (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
      positiveShellDensity ε a * a * Real.sinh (u * a))

private noncomputable def saddleSourceRadius (ε : ℝ) (d : ℕ) : ℝ :=
  Real.exp (saddleLogRadius ε d (1 + ε / 4))

private theorem saddleSourceRadius_pos (ε : ℝ) (d : ℕ) :
    0 < saddleSourceRadius ε d := by
  exact Real.exp_pos _

private theorem saddleLogGamma_add_one {x : ℝ} (hx : 0 < x) :
    (Real.log ∘ Real.Gamma) (x + 1) =
      (Real.log ∘ Real.Gamma) x + Real.log x := by
  simp only [Function.comp_apply, Real.Gamma_add_one hx.ne',
    Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']
  ring

private theorem saddleLogGamma_differentiableAt {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (Real.log ∘ Real.Gamma) x := by
  exact (Real.differentiableAt_Gamma
    (fun n => ne_of_gt (by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith))).log (Real.Gamma_pos_of_pos hx).ne'

private theorem saddleDigamma_bounds {x : ℝ} (hx : 1 < x) :
    Real.log (x - 1) ≤ saddleDigamma x ∧
      saddleDigamma x ≤ Real.log x := by
  have hxpositive : 0 < x := by linarith
  have hxprevious : 0 < x - 1 := by linarith
  have hnext : 0 < x + 1 := by linarith
  have hdiff := saddleLogGamma_differentiableAt hxpositive
  constructor
  · have hconv := Real.convexOn_log_Gamma.slope_le_deriv
      (show x - 1 ∈ Ioi (0 : ℝ) from hxprevious)
      (show x ∈ Ioi (0 : ℝ) from hxpositive)
      (show x - 1 < x by linarith) hdiff
    have hrec := saddleLogGamma_add_one hxprevious
    have hshift : (x - 1) + 1 = x := by ring
    rw [hshift] at hrec
    unfold saddleDigamma
    rw [slope_def_field] at hconv
    have hden : x - (x - 1) = (1 : ℝ) := by ring
    rw [hden, div_one, hrec] at hconv
    simpa only [ge_iff_le, Function.comp_apply, add_sub_cancel_left] using! hconv
  · have hconv := Real.convexOn_log_Gamma.deriv_le_slope
      (show x ∈ Ioi (0 : ℝ) from hxpositive)
      (show x + 1 ∈ Ioi (0 : ℝ) from hnext)
      (show x < x + 1 by linarith) hdiff
    have hrec := saddleLogGamma_add_one hxpositive
    unfold saddleDigamma
    rw [slope_def_field] at hconv
    have hden : (x + 1) - x = (1 : ℝ) := by ring
    rw [hden, div_one, hrec] at hconv
    simpa only [ge_iff_le, Function.comp_apply, add_sub_cancel_left] using! hconv

private theorem tendsto_saddleDigamma_sub_log :
    Tendsto (fun x : ℝ => saddleDigamma x - Real.log x)
      atTop (𝓝 (0 : ℝ)) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹)
      atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
  have hargument : Tendsto (fun x : ℝ => 1 - x⁻¹)
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using! (tendsto_const_nhds.sub hinv)
  have hlog : Tendsto (fun x : ℝ =>
      Real.log (1 - x⁻¹)) atTop (𝓝 (0 : ℝ)) := by
    convert! (Real.continuousAt_log
      (show (1 : ℝ) ≠ 0 by norm_num)).tendsto.comp
        hargument using 1
    all_goals simp only [Real.log_one]
  have hlower : Tendsto (fun x : ℝ =>
      Real.log (x - 1) - Real.log x)
      atTop (𝓝 (0 : ℝ)) := by
    refine hlog.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hxzero : x ≠ 0 := by linarith
    have hxprevious : x - 1 ≠ 0 := by linarith
    rw [← Real.log_div hxprevious hxzero]
    congr 1
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower (tendsto_const_nhds (x := (0 : ℝ))) ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact sub_le_sub_right (saddleDigamma_bounds hx).1 _
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact sub_nonpos.mpr (saddleDigamma_bounds hx).2

private theorem saddle_exp_half_log_eq_sqrt {x : ℝ} (hx : 0 < x) :
    Real.exp (Real.log x / 2) = Real.sqrt x := by
  rw [← Real.log_sqrt hx.le,
    Real.exp_log (Real.sqrt_pos.2 hx)]

private noncomputable def saddleCriticalGammaArgument (ε : ℝ) (d : ℕ) : ℝ :=
  ((d : ℝ) / 2) * (2 + ε / 4) / 2

private theorem saddleCriticalGammaArgument_pos {ε : ℝ}
    (hε : 0 < ε) {d : ℕ} (hd : 0 < d) :
    0 < saddleCriticalGammaArgument ε d := by
  unfold saddleCriticalGammaArgument
  positivity

private theorem tendsto_saddleCriticalGammaArgument_atTop
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (saddleCriticalGammaArgument ε)
      atTop atTop := by
  have hc : 0 < (2 + ε / 4) / 4 := by positivity
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hc
  refine h.congr' ?_
  filter_upwards [] with d
  unfold saddleCriticalGammaArgument
  ring

private theorem saddleLogRadius_critical_eq (ε : ℝ) (d : ℕ) :
    saddleLogRadius ε d (1 + ε / 4) =
      -(Real.log Real.pi) / 2 +
        saddleDigamma (saddleCriticalGammaArgument ε d) / 2 +
        shortShellRadiusContribution ε +
        positiveShellRadiusContribution ε := by
  unfold saddleLogRadius saddleCriticalGammaArgument
    shortShellRadiusContribution shortShellRadiusIntegrand
    positiveShellRadiusContribution
  congr 2
  ring_nf

private theorem saddleSourceRadius_div_sqrt_eq
    {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d) :
    saddleSourceRadius ε d / Real.sqrt (d : ℝ) =
      Real.exp ((saddleDigamma (saddleCriticalGammaArgument ε d) -
          Real.log (saddleCriticalGammaArgument ε d)) / 2) *
        limitingSaddleRadius ε := by
  let a : ℝ := 2 + ε / 4
  let m : ℝ := saddleCriticalGammaArgument ε d
  let S : ℝ := shortShellRadiusContribution ε +
    positiveShellRadiusContribution ε
  have ha : 0 < a := by
    try dsimp [a]
    positivity
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hm : 0 < m := saddleCriticalGammaArgument_pos hε hd
  have hquotient : 0 < a / (4 * Real.pi) := by positivity
  have hmformula : m = (d : ℝ) * a / 4 := by
    try dsimp [m, a, saddleCriticalGammaArgument]
    ring
  have hlogm : Real.log m =
      Real.log (d : ℝ) + Real.log a - Real.log (4 : ℝ) := by
    rw [hmformula,
      Real.log_div (mul_ne_zero hdreal.ne' ha.ne')
        (by norm_num : (4 : ℝ) ≠ 0),
      Real.log_mul hdreal.ne' ha.ne']
  have hlogquotient :
      Real.log (a / (4 * Real.pi)) =
        Real.log a - Real.log (4 : ℝ) - Real.log Real.pi := by
    rw [Real.log_div ha.ne'
      (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0)
        Real.pi_ne_zero),
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
        Real.pi_ne_zero]
    ring
  have hv : saddleLogRadius ε d (1 + ε / 4) =
      -(Real.log Real.pi) / 2 +
        saddleDigamma m / 2 + S := by
    rw [saddleLogRadius_critical_eq]
    try dsimp [m, S]
    ring
  calc
    saddleSourceRadius ε d / Real.sqrt (d : ℝ) =
      Real.exp
        (-(Real.log Real.pi) / 2 +
          saddleDigamma m / 2 + S -
          Real.log (d : ℝ) / 2) := by
      unfold saddleSourceRadius
      rw [hv, ← saddle_exp_half_log_eq_sqrt hdreal,
        ← Real.exp_sub]
    _ = Real.exp
        ((saddleDigamma m - Real.log m) / 2 +
          Real.log (a / (4 * Real.pi)) / 2 + S) := by
      congr 1
      rw [hlogm, hlogquotient]
      ring
    _ = Real.exp ((saddleDigamma m - Real.log m) / 2) *
          Real.sqrt (a / (4 * Real.pi)) * Real.exp S := by
      rw [Real.exp_add, Real.exp_add,
        saddle_exp_half_log_eq_sqrt hquotient]
    _ = Real.exp
          ((saddleDigamma (saddleCriticalGammaArgument ε d) -
            Real.log (saddleCriticalGammaArgument ε d)) / 2) *
          limitingSaddleRadius ε := by
      unfold limitingSaddleRadius
      try dsimp [m, a, S]
      ring

private theorem tendsto_saddleSourceRadius_normalized
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun d : ℕ =>
        saddleSourceRadius ε d / Real.sqrt (d : ℝ))
      atTop (𝓝 (limitingSaddleRadius ε)) := by
  have hargument := tendsto_saddleDigamma_sub_log.comp
    (tendsto_saddleCriticalGammaArgument_atTop hε)
  have hhalf : Tendsto
      (fun d : ℕ =>
        (saddleDigamma (saddleCriticalGammaArgument ε d) -
          Real.log (saddleCriticalGammaArgument ε d)) / 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_apply, zero_div] using! hargument.div_const (2 : ℝ)
  have hcorrection : Tendsto
      (fun d : ℕ =>
        Real.exp
          ((saddleDigamma (saddleCriticalGammaArgument ε d) -
            Real.log (saddleCriticalGammaArgument ε d)) / 2))
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [Real.exp_zero] using! hhalf.rexp
  have htarget : Tendsto
      (fun d : ℕ =>
        Real.exp
          ((saddleDigamma (saddleCriticalGammaArgument ε d) -
            Real.log (saddleCriticalGammaArgument ε d)) / 2) *
          limitingSaddleRadius ε)
      atTop (𝓝 (limitingSaddleRadius ε)) := by
    simpa only [one_mul] using! hcorrection.mul_const (limitingSaddleRadius ε)
  refine htarget.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
  exact (saddleSourceRadius_div_sqrt_eq hε hd).symm

end
end CohnElkies
