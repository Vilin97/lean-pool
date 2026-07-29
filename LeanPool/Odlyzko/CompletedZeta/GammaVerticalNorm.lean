/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.GammaFactor
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Gamma Vertical Norm

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex

namespace NumberField.Odlyzko

theorem Gamma_one_add_mul_I_mul_Gamma_one_sub_mul_I
    {t : ℝ} (ht : t ≠ 0) :
    Complex.Gamma (1 + t * I) * Complex.Gamma (1 - t * I) =
      (Real.pi * t / Real.sinh (Real.pi * t) : ℝ) := by
  have htI : (t : ℂ) * I ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr ht) I_ne_zero
  have hreflect :=
    Complex.Gamma_mul_Gamma_one_sub ((t : ℂ) * I)
  have hrec :
      Complex.Gamma (1 + t * I) =
        ((t : ℂ) * I) * Complex.Gamma ((t : ℂ) * I) := by
    rw [show (1 : ℂ) + t * I = (t : ℂ) * I + 1 by ring]
    exact Complex.Gamma_add_one ((t : ℂ) * I) htI
  rw [hrec, mul_assoc, hreflect]
  rw [show (Real.pi : ℂ) * ((t : ℂ) * I) =
      ((Real.pi * t : ℝ) : ℂ) * I by
        push_cast
        ring]
  rw [Complex.sin_mul_I]
  push_cast
  grind

theorem sq_norm_Gamma_one_add_mul_I
    {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gamma (1 + t * I)‖ ^ 2 =
      Real.pi * |t| / Real.sinh (Real.pi * |t|) := by
  have hconj :
      star (Complex.Gamma (1 + t * I)) =
        Complex.Gamma (1 - t * I) := by
    rw [Complex.star_def, ← Complex.Gamma_conj]
    congr 1
    apply Complex.ext <;> simp
  have hprod :=
    Gamma_one_add_mul_I_mul_Gamma_one_sub_mul_I ht
  have hnorm :
      ‖Complex.Gamma (1 + t * I)‖ ^ 2 =
        (Complex.Gamma (1 + t * I) *
          Complex.Gamma (1 - t * I)).re := by
    rw [← hconj, Complex.star_def, Complex.mul_conj, Complex.sq_norm]
    simp
  rw [hnorm, hprod]
  simp only [ofReal_re]
  by_cases htpos : 0 < t
  · grind
  · have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt htpos) ht
    rw [abs_of_neg htneg, mul_neg, Real.sinh_neg, neg_div_neg_eq]

theorem sq_norm_Gamma_two_add_mul_I
    {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gamma (2 + t * I)‖ ^ 2 =
      (1 + t ^ 2) *
        (Real.pi * |t| / Real.sinh (Real.pi * |t|)) := by
  have harg : (1 : ℂ) + t * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hrec :
      Complex.Gamma (2 + t * I) =
        (1 + t * I) * Complex.Gamma (1 + t * I) := by
    rw [show (2 : ℂ) + t * I = (1 + t * I) + 1 by ring]
    exact Complex.Gamma_add_one (1 + t * I) harg
  rw [hrec, norm_mul, mul_pow, sq_norm_Gamma_one_add_mul_I ht]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [add_re, one_re, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
    zero_mul, mul_one, sub_zero, add_im, one_im, zero_add]
  ring

theorem two_mul_pi_mul_abs_mul_exp_neg_le_sq_norm_Gamma_one_add_mul_I
    {t : ℝ} (ht : t ≠ 0) :
    2 * Real.pi * |t| * Real.exp (-(Real.pi * |t|)) ≤
      ‖Complex.Gamma (1 + t * I)‖ ^ 2 := by
  rw [sq_norm_Gamma_one_add_mul_I ht]
  let x := Real.pi * |t|
  have hx : 0 < x := mul_pos Real.pi_pos (abs_pos.mpr ht)
  have hsinh : Real.sinh x ≤ Real.exp x / 2 := by
    rw [Real.sinh_eq]
    have hpos := Real.exp_pos (-x)
    linarith
  have hsinhpos : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hratio :
      2 * x * Real.exp (-x) ≤ x / Real.sinh x := by
    rw [le_div_iff₀ hsinhpos]
    have hexp : Real.exp (-x) * Real.exp x = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      2 * x * Real.exp (-x) * Real.sinh x ≤
          2 * x * Real.exp (-x) * (Real.exp x / 2) := by
        gcongr
      _ = x := by grind
  grind

theorem sq_norm_complexPlaceGammaFactor_two_add_mul_I
    {t : ℝ} (ht : t ≠ 0) :
    ‖CompletedZeta.complexPlaceGammaFactor (2 + t * I)‖ ^ 2 =
      (2 * Real.pi) ^ (-4 : ℝ) * (1 + t ^ 2) *
        (Real.pi * |t| / Real.sinh (Real.pi * |t|)) := by
  rw [complexPlaceGammaFactor_eq, norm_mul, mul_pow,
    sq_norm_Gamma_two_add_mul_I ht]
  have hbase : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hnorm :
      ‖((2 * (Real.pi : ℂ)) ^ (-(2 + t * I)))‖ =
        (2 * Real.pi) ^ (-2 : ℝ) := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by
      simp]
    (convert norm_cpow_eq_rpow_re_of_pos hbase (-(2 + t * I)) using 1; norm_num)
  rw [hnorm, ← Real.rpow_natCast]
  rw [← Real.rpow_mul hbase.le]
  grind

theorem complexPlaceGammaFactor_two_vertical_sq_lowerBound
    {t : ℝ} (ht : t ≠ 0) :
    (2 * Real.pi) ^ (-4 : ℝ) * (1 + t ^ 2) *
        (2 * Real.pi * |t| * Real.exp (-(Real.pi * |t|))) ≤
      ‖CompletedZeta.complexPlaceGammaFactor (2 + t * I)‖ ^ 2 := by
  rw [sq_norm_complexPlaceGammaFactor_two_add_mul_I ht]
  gcongr
  have h :=
    two_mul_pi_mul_abs_mul_exp_neg_le_sq_norm_Gamma_one_add_mul_I ht
  rw [sq_norm_Gamma_one_add_mul_I ht] at h
  grind

/-- A complex place gamma vertical lower constant used in the Odlyzko-bound argument. -/
noncomputable def complexPlaceGammaVerticalLowerConstant : ℝ :=
  (2 * Real.pi) ^ (-3 : ℝ)

theorem complexPlaceGammaVerticalLowerConstant_pos :
    0 < complexPlaceGammaVerticalLowerConstant := by
  exact Real.rpow_pos_of_pos (mul_pos (by norm_num) Real.pi_pos) _

theorem complexPlaceGammaVerticalLowerConstant_mul_exp_le_sq_norm
    {t : ℝ} (ht : 1 ≤ |t|) :
    complexPlaceGammaVerticalLowerConstant *
        Real.exp (-(Real.pi * |t|)) ≤
      ‖CompletedZeta.complexPlaceGammaFactor (2 + t * I)‖ ^ 2 := by
  have ht0 : t ≠ 0 := by grind
  apply le_trans ?_ (complexPlaceGammaFactor_two_vertical_sq_lowerBound ht0)
  have hbase : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hpow :
      complexPlaceGammaVerticalLowerConstant =
        (2 * Real.pi) ^ (-4 : ℝ) * (2 * Real.pi) := by
    calc
      complexPlaceGammaVerticalLowerConstant =
          (2 * Real.pi) ^ ((-4 : ℝ) + 1) := by
        rw [complexPlaceGammaVerticalLowerConstant]
        norm_num
      _ = (2 * Real.pi) ^ (-4 : ℝ) * (2 * Real.pi) ^ (1 : ℝ) :=
        Real.rpow_add hbase (-4 : ℝ) 1
      _ = (2 * Real.pi) ^ (-4 : ℝ) * (2 * Real.pi) := by simp
  rw [hpow]
  have hquad : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  calc
    (2 * Real.pi) ^ (-4 : ℝ) * (2 * Real.pi) *
          Real.exp (-(Real.pi * |t|))
        ≤ (2 * Real.pi) ^ (-4 : ℝ) * (1 + t ^ 2) *
            ((2 * Real.pi) * Real.exp (-(Real.pi * |t|))) := by
      calc
        (2 * Real.pi) ^ (-4 : ℝ) * (2 * Real.pi) *
              Real.exp (-(Real.pi * |t|)) =
            ((2 * Real.pi) ^ (-4 : ℝ) * (2 * Real.pi) *
              Real.exp (-(Real.pi * |t|))) * 1 := by ring
        _ ≤ ((2 * Real.pi) ^ (-4 : ℝ) * (2 * Real.pi) *
              Real.exp (-(Real.pi * |t|))) * (1 + t ^ 2) := by
          exact mul_le_mul_of_nonneg_left hquad (by positivity)
        _ = (2 * Real.pi) ^ (-4 : ℝ) * (1 + t ^ 2) *
              ((2 * Real.pi) * Real.exp (-(Real.pi * |t|))) := by ring
    _ ≤ (2 * Real.pi) ^ (-4 : ℝ) * (1 + t ^ 2) *
          (2 * Real.pi * |t| * Real.exp (-(Real.pi * |t|))) := by
      calc
        (2 * Real.pi) ^ (-4 : ℝ) * (1 + t ^ 2) *
              ((2 * Real.pi) * Real.exp (-(Real.pi * |t|))) =
            ((2 * Real.pi) ^ (-4 : ℝ) * (1 + t ^ 2) *
              (2 * Real.pi) * Real.exp (-(Real.pi * |t|))) * 1 := by ring
        _ ≤ ((2 * Real.pi) ^ (-4 : ℝ) * (1 + t ^ 2) *
              (2 * Real.pi) * Real.exp (-(Real.pi * |t|))) * |t| := by
          exact mul_le_mul_of_nonneg_left ht (by positivity)
        _ = (2 * Real.pi) ^ (-4 : ℝ) * (1 + t ^ 2) *
              (2 * Real.pi * |t| * Real.exp (-(Real.pi * |t|))) := by ring

end NumberField.Odlyzko
