/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.WindingWeights.Common
import LeanPool.LeanModularForms.ContourIntegral.WindingNumber
import LeanPool.LeanModularForms.ContourIntegral.CrossingLimit

/-!
# Winding Number Weight at i

PV integral computation and generalized winding number of `fdBoundaryH`
around the point i.

## Main Results

* `pv_integral_at_i_tendsto` — PV integral converges to -iπ
* `gWN_fdBoundary_H_at_i` — gWN = -1/2 at i
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Half-angle factorization of `sin(δπ/6)` used across the i-point trig proofs. -/
private lemma sin_delta_pi_six_factor (δ : ℝ) :
    Real.sin (δ * Real.pi / 6) =
      2 * Real.sin (δ * Real.pi / 12) * Real.cos (δ * Real.pi / 12) := by
  rw [show δ * Real.pi / 6 = 2 * (δ * Real.pi / 12) from by ring, Real.sin_two_mul]

/-- Half-angle factorization of `cos(δπ/6) - 1` used across the i-point trig proofs. -/
private lemma cos_delta_pi_six_sub_one_factor (δ : ℝ) :
    Real.cos (δ * Real.pi / 6) - 1 =
      -(2 * Real.sin (δ * Real.pi / 12) * Real.sin (δ * Real.pi / 12)) := by
  rw [show δ * Real.pi / 6 = 2 * (δ * Real.pi / 12) from by ring, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq (δ * Real.pi / 12)]

private lemma arg_approach_i_left (hδ : 0 < δ) (hδ_small : δ < 1) :
    (fdBoundaryH H (2 - δ) - I).arg = -(δ * Real.pi / 12) := by
  have h1 : 1 < 2 - δ := by linarith
  have h3 : 2 - δ < 3 := by linarith
  rw [fdBoundary_H_eq_arc h1 h3]
  set θ := Real.pi / 2 - δ * Real.pi / 6 with hθ_def
  rw [show Real.pi * (1 + (2 - δ)) / 6 = θ from by simp only [hθ_def]; ring]
  rw [show (↑θ : ℂ) * I = ↑θ * I from rfl, exp_real_angle_I]
  have h_cos : Real.cos θ = Real.sin (δ * Real.pi / 6) := by rw [hθ_def, Real.cos_pi_div_two_sub]
  have h_sin : Real.sin θ = Real.cos (δ * Real.pi / 6) := by rw [hθ_def, Real.sin_pi_div_two_sub]
  have h_re_factor : Real.sin (δ * Real.pi / 6) =
      2 * Real.sin (δ * Real.pi / 12) * Real.cos (δ * Real.pi / 12) := sin_delta_pi_six_factor δ
  have h_im_factor : Real.cos (δ * Real.pi / 6) - 1 =
      -(2 * Real.sin (δ * Real.pi / 12) * Real.sin (δ * Real.pi / 12)) :=
    cos_delta_pi_six_sub_one_factor δ
  have h_sin_pos : 0 < Real.sin (δ * Real.pi / 12) :=
    ArcCalculus.sin_pos_of_mem_Ioo_zero_pi (by constructor <;> nlinarith [Real.pi_pos])
  have h_eq : ↑(Real.cos θ) + ↑(Real.sin θ) * I - I =
      ↑(2 * Real.sin (δ * Real.pi / 12)) *
        (↑(Real.cos (δ * Real.pi / 12)) + ↑(-(Real.sin (δ * Real.pi / 12))) * I) := by
    rw [h_cos, h_sin]
    apply Complex.ext
    · simp only [add_re, sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero, mul_one]; linarith [h_re_factor]
    · simp only [add_im, sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, add_zero, mul_one, zero_add]; linarith [h_im_factor]
  rw [h_eq]
  have h_trig : (↑(Real.cos (δ * Real.pi / 12)) : ℂ) +
      ↑(-(Real.sin (δ * Real.pi / 12))) * I =
      Complex.cos ↑(-(δ * Real.pi / 12)) + Complex.sin ↑(-(δ * Real.pi / 12)) * I := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, ofReal_neg]
  rw [h_trig]
  exact Complex.arg_mul_cos_add_sin_mul_I (mul_pos (by norm_num : (0 : ℝ) < 2) h_sin_pos)
    ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩

private lemma arg_approach_i_right (hδ : 0 < δ) (hδ_small : δ < 1) :
    (fdBoundaryH H (2 + δ) - I).arg = δ * Real.pi / 12 - Real.pi := by
  have h1 : 1 < 2 + δ := by linarith
  have h3 : 2 + δ < 3 := by linarith
  rw [fdBoundary_H_eq_arc h1 h3]
  set θ := Real.pi / 2 + δ * Real.pi / 6 with hθ_def
  rw [show Real.pi * (1 + (2 + δ)) / 6 = θ from by simp only [hθ_def]; ring]
  rw [show (↑θ : ℂ) * I = ↑θ * I from rfl, exp_real_angle_I]
  have h_cos : Real.cos θ = -Real.sin (δ * Real.pi / 6) := by
    rw [hθ_def, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have h_sin : Real.sin θ = Real.cos (δ * Real.pi / 6) := by
    rw [hθ_def, Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  have h_re_factor : -Real.sin (δ * Real.pi / 6) =
      -(2 * Real.sin (δ * Real.pi / 12) * Real.cos (δ * Real.pi / 12)) := by
    rw [sin_delta_pi_six_factor]
  have h_im_factor : Real.cos (δ * Real.pi / 6) - 1 =
      -(2 * Real.sin (δ * Real.pi / 12) * Real.sin (δ * Real.pi / 12)) :=
    cos_delta_pi_six_sub_one_factor δ
  have h_sin_pos : 0 < Real.sin (δ * Real.pi / 12) :=
    ArcCalculus.sin_pos_of_mem_Ioo_zero_pi (by constructor <;> nlinarith [Real.pi_pos])
  set w := (↑(Real.cos (δ * Real.pi / 12)) : ℂ) +
    ↑(Real.sin (δ * Real.pi / 12)) * I with hw_def
  have h_eq : ↑(Real.cos θ) + ↑(Real.sin θ) * I - I =
      -(↑(2 * Real.sin (δ * Real.pi / 12)) * w) := by
    rw [h_cos, h_sin]
    apply Complex.ext
    · simp only [hw_def, add_re, sub_re, neg_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero, mul_one]; linarith [h_re_factor]
    · simp only [hw_def, add_im, sub_im, neg_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, add_zero, mul_one, zero_add]; linarith [h_im_factor]
  rw [h_eq]
  have hw_im_pos : 0 < w.im := by
    simp only [hw_def, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
      mul_zero, add_zero, mul_one]
    linarith
  have hw_arg : w.arg = δ * Real.pi / 12 := by
    have hw_eq : w = ↑(1 : ℝ) * (Complex.cos ↑(δ * Real.pi / 12) +
        Complex.sin ↑(δ * Real.pi / 12) * I) := by
      simp only [hw_def, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Complex.ofReal_one, one_mul]
    rw [hw_eq]
    exact Complex.arg_mul_cos_add_sin_mul_I (by norm_num : (0 : ℝ) < 1)
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  have hrw_im_pos : 0 < (↑(2 * Real.sin (δ * Real.pi / 12)) * w).im := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    simp only [zero_mul, add_zero]
    exact mul_pos (mul_pos (by norm_num) h_sin_pos) hw_im_pos
  rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos hrw_im_pos,
      Complex.arg_real_mul w (mul_pos (by norm_num : (0 : ℝ) < 2) h_sin_pos),
      hw_arg]

private lemma g_i_norm_left {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ‖fdBoundaryH H (2 - δ) - I‖ = 2 * Real.sin (δ * Real.pi / 12) := by
  have h1 : 1 < 2 - δ := by linarith
  have h3 : 2 - δ < 3 := by linarith
  rw [fdBoundary_H_eq_arc h1 h3, exp_real_angle_I]
  set θ := Real.pi / 2 - δ * Real.pi / 6 with hθ_def
  rw [show Real.pi * (1 + (2 - δ)) / 6 = θ from by simp only [hθ_def]; ring]
  have h_cos : Real.cos θ = Real.sin (δ * Real.pi / 6) := by rw [hθ_def, Real.cos_pi_div_two_sub]
  have h_sin : Real.sin θ = Real.cos (δ * Real.pi / 6) := by rw [hθ_def, Real.sin_pi_div_two_sub]
  have h_re_factor : Real.sin (δ * Real.pi / 6) =
      2 * Real.sin (δ * Real.pi / 12) * Real.cos (δ * Real.pi / 12) := sin_delta_pi_six_factor δ
  have h_im_factor : Real.cos (δ * Real.pi / 6) - 1 =
      -(2 * Real.sin (δ * Real.pi / 12) * Real.sin (δ * Real.pi / 12)) :=
    cos_delta_pi_six_sub_one_factor δ
  have h_sin_pos : 0 < Real.sin (δ * Real.pi / 12) :=
    ArcCalculus.sin_pos_of_mem_Ioo_zero_pi (by constructor <;> nlinarith [Real.pi_pos])
  have h_eq : ↑(Real.cos θ) + ↑(Real.sin θ) * I - I =
      (2 * Real.sin (δ * Real.pi / 12)) • Complex.exp (↑(-(δ * Real.pi / 12)) * I) := by
    rw [Complex.real_smul, exp_real_angle_I, Real.cos_neg, Real.sin_neg, h_cos, h_sin]
    apply Complex.ext
    · simp only [add_re, sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero, mul_one]; linarith [h_re_factor]
    · simp only [add_im, sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, add_zero, mul_one, zero_add]; linarith [h_im_factor]
  rw [h_eq, norm_smul, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_of_nonneg (by linarith)]

private lemma g_i_norm_right {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ‖fdBoundaryH H (2 + δ) - I‖ = 2 * Real.sin (δ * Real.pi / 12) := by
  have h1 : 1 < 2 + δ := by linarith
  have h3 : 2 + δ < 3 := by linarith
  rw [fdBoundary_H_eq_arc h1 h3, exp_real_angle_I]
  set θ := Real.pi / 2 + δ * Real.pi / 6 with hθ_def
  rw [show Real.pi * (1 + (2 + δ)) / 6 = θ from by simp only [hθ_def]; ring]
  have h_cos : Real.cos θ = -Real.sin (δ * Real.pi / 6) := by
    rw [hθ_def, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have h_sin : Real.sin θ = Real.cos (δ * Real.pi / 6) := by
    rw [hθ_def, Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  have h_re_factor : -Real.sin (δ * Real.pi / 6) =
      -(2 * Real.sin (δ * Real.pi / 12) * Real.cos (δ * Real.pi / 12)) := by
    rw [sin_delta_pi_six_factor]
  have h_im_factor : Real.cos (δ * Real.pi / 6) - 1 =
      -(2 * Real.sin (δ * Real.pi / 12) * Real.sin (δ * Real.pi / 12)) :=
    cos_delta_pi_six_sub_one_factor δ
  have h_sin_pos : 0 < Real.sin (δ * Real.pi / 12) :=
    ArcCalculus.sin_pos_of_mem_Ioo_zero_pi (by constructor <;> nlinarith [Real.pi_pos])
  have h_eq : ↑(Real.cos θ) + ↑(Real.sin θ) * I - I =
      (-(2 * Real.sin (δ * Real.pi / 12))) • Complex.exp (↑(δ * Real.pi / 12) * I) := by
    rw [Complex.real_smul, exp_real_angle_I, h_cos, h_sin]
    apply Complex.ext
    · simp only [add_re, sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero, mul_one]; linarith [h_re_factor]
    · simp only [add_im, sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, add_zero, mul_one, zero_add]; linarith [h_im_factor]
  rw [h_eq, norm_smul, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (by linarith)]

private lemma g_i_norm_ge_seg0 {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 / 2 ≤ ‖fdBoundaryH H t - I‖ := by
  have hre : (fdBoundaryH H t - I).re = 1 / 2 := by
    rw [fdBoundary_H_seg0 H ht1]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.div_ofNat_re,
      mul_zero, sub_zero, zero_mul, mul_one]
    norm_num
  calc (1 : ℝ) / 2 = |1 / 2| := (abs_of_pos (by norm_num)).symm
    _ = |(fdBoundaryH H t - I).re| := by rw [hre]
    _ ≤ ‖fdBoundaryH H t - I‖ := Complex.abs_re_le_norm _

private lemma g_i_norm_ge_seg4 (H : ℝ) (hH : 1 < H) {t : ℝ} (ht4 : 4 ≤ t) (ht5 : t ≤ 5) :
    H - 1 ≤ ‖fdBoundaryH H t - I‖ := by
  have him : (fdBoundaryH H t - I).im = H - 1 := by
    rcases eq_or_lt_of_le ht4 with rfl | ht4'
    · rw [fdBoundary_H_at_four H]
      simp only [Complex.neg_im, Complex.div_ofNat_im, Complex.one_im, Complex.add_im,
        Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.sub_im,
        Complex.ofReal_re]
      ring
    · rw [fdBoundary_H_seg4 H (by linarith) (by linarith) (by linarith) (by linarith)]
      simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.div_ofNat_im, Complex.im_ofNat]
      ring
  calc H - 1 = |H - 1| := (abs_of_pos (by linarith)).symm
    _ = |(fdBoundaryH H t - I).im| := by rw [him]
    _ ≤ ‖fdBoundaryH H t - I‖ := Complex.abs_im_le_norm _

private lemma g_i_slitPlane_left {t : ℝ} (_ht0 : 0 ≤ t) (ht2 : t < 2) :
    fdBoundaryH H t - I ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  rcases le_or_gt t 1 with ht1 | ht1
  · rw [fdBoundary_H_seg0 H ht1]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.div_ofNat_re,
      mul_zero, sub_zero, zero_mul, mul_one]
    norm_num
  · rw [fdBoundary_H_seg1 H (by linarith) (by linarith)]
    set θ := Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3) with hθ_def
    rw [show (↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
      (↑θ : ℂ) * I from by simp only [hθ_def]; push_cast; ring, exp_real_angle_I]
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero,
      mul_one]
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · simp only [hθ_def]; nlinarith [Real.pi_pos]
    · simp only [hθ_def]; nlinarith [Real.pi_pos]

private lemma g_i_seg3_value {t : ℝ} (ht3 : 3 < t) (ht4 : t ≤ 4) :
    fdBoundaryH H t - I =
      -1/2 + ↑(Real.sqrt 3 / 2 - 1 + (t - 3) * (H - Real.sqrt 3 / 2)) * I := by
  rw [fdBoundary_H_seg3 H (by linarith) (by linarith) (by linarith) ht4]
  push_cast; ring

private lemma g_i_seg4_value {t : ℝ} (ht4 : 4 < t) :
    fdBoundaryH H t - I = ↑(t - 9/2) + ↑(H - 1) * I := by
  rw [fdBoundary_H_seg4 H (by linarith) (by linarith) (by linarith) (by linarith)]
  push_cast; ring

private lemma g_i_norm_ge_seg3 {t : ℝ} (ht3 : 3 ≤ t) (ht4 : t ≤ 4) :
    1 / 2 ≤ ‖fdBoundaryH H t - I‖ := by
  have hre : (fdBoundaryH H t - I).re = -1 / 2 := by
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · rw [fdBoundary_H_at_three_eq_rho]
      simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk,
        Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.div_ofNat_re,
        Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero]
      norm_num
    · rw [g_i_seg3_value ht3' ht4]
      simp only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re, Complex.one_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, sub_zero, add_zero, zero_mul]
  calc 1 / 2 = |(-1 : ℝ) / 2| := by norm_num
    _ = |(fdBoundaryH H t - I).re| := by rw [hre]
    _ ≤ ‖fdBoundaryH H t - I‖ := Complex.abs_re_le_norm _

private lemma g_i_slitPlane_arc_right {t : ℝ} (ht2 : 2 < t) (ht3 : t ≤ 3) :
    fdBoundaryH H t - I ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]; right
  rcases eq_or_lt_of_le ht3 with rfl | ht3'
  · rw [fdBoundary_H_at_three_eq_rho]
    simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk,
      Complex.add_im, Complex.sub_im, Complex.neg_im, Complex.div_ofNat_im, Complex.div_ofNat_re,
      Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one, zero_div]
    nlinarith [Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), sq_nonneg (2 - Real.sqrt 3)]
  · rw [fdBoundary_H_eq_arc (by linarith) ht3', exp_real_angle_I]
    simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one, zero_add]
    have hθ_bound : Real.pi / 2 < Real.pi * (1 + t) / 6 := by nlinarith [Real.pi_pos]
    have hθ_bound2 : Real.pi * (1 + t) / 6 < Real.pi + Real.pi / 2 := by nlinarith [Real.pi_pos]
    have h_cos_neg := Real.cos_neg_of_pi_div_two_lt_of_lt hθ_bound hθ_bound2
    have h_sin_lt : Real.sin (Real.pi * (1 + t) / 6) < 1 := by
      by_contra h_ge; push Not at h_ge
      have h_eq := le_antisymm (Real.sin_le_one _) h_ge
      have : Real.cos (Real.pi * (1 + t) / 6) = 0 := by
        nlinarith [Real.sin_sq_add_cos_sq (Real.pi * (1 + t) / 6)]
      linarith
    linarith

private lemma g_i_norm_arc_right {t : ℝ} (ht2 : 2 < t) (ht3 : t < 3) :
    ‖fdBoundaryH H t - I‖ = 2 * Real.sin ((t - 2) * Real.pi / 12) := by
  have h := g_i_norm_right (H := H) (δ := t - 2) (by linarith) (by linarith)
  rwa [show 2 + (t - 2) = t from by ring] at h

private lemma g_i_norm_arc_left {t : ℝ} (ht1 : 1 < t) (ht2 : t < 2) :
    ‖fdBoundaryH H t - I‖ = 2 * Real.sin ((2 - t) * Real.pi / 12) := by
  have h := g_i_norm_left (H := H) (δ := 2 - t) (by linarith) (by linarith)
  rwa [show 2 - (2 - t) = t from by ring] at h

private noncomputable def t₀_i (H : ℝ) : ℝ :=
  3 + (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2)

private lemma H_sub_sqrt3_div2_pos (hH : 1 < H) : 0 < H - Real.sqrt 3 / 2 :=
  have := Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)
  by nlinarith [sq_nonneg (2 - Real.sqrt 3)]

private lemma t₀_i_gt_three (hH : 1 < H) : 3 < t₀_i H := by
  unfold t₀_i
  have h_num_pos : 0 < 1 - Real.sqrt 3 / 2 :=
    by nlinarith [Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), sq_nonneg (2 - Real.sqrt 3)]
  linarith [div_pos h_num_pos (H_sub_sqrt3_div2_pos hH)]

private lemma t₀_i_lt_four (hH : 1 < H) : t₀_i H < 4 := by
  unfold t₀_i
  have h_den_pos := H_sub_sqrt3_div2_pos hH
  rw [show (4 : ℝ) = 3 + 1 from by ring]
  have : (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) < 1 := by rw [div_lt_one h_den_pos]; linarith
  linarith

private lemma t₀_i_im_eq_zero (hH : 1 < H) :
    Real.sqrt 3 / 2 - 1 + (t₀_i H - 3) * (H - Real.sqrt 3 / 2) = 0 := by
  have h_den_pos := H_sub_sqrt3_div2_pos hH
  unfold t₀_i
  rw [show 3 + (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) - 3 =
    (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) from by ring,
    div_mul_cancel₀ _ (ne_of_gt h_den_pos)]; ring

private lemma g_i_at_t₀ (hH : 1 < H) :
    fdBoundaryH H (t₀_i H) - I = -1/2 := by
  have ht₀3 := t₀_i_gt_three hH
  have ht₀4 := t₀_i_lt_four hH
  rw [g_i_seg3_value (by linarith) (by linarith), t₀_i_im_eq_zero hH]
  simp only [ofReal_zero, zero_mul, add_zero]

private lemma g_i_seg3_im_neg {t : ℝ} (ht3 : 3 < t) (ht_t0 : t < t₀_i H)
    (hH : 1 < H) : (fdBoundaryH H t - I).im < 0 := by
  rw [g_i_seg3_value ht3 (by linarith [t₀_i_lt_four hH])]
  simp only [Complex.add_im, Complex.neg_im, Complex.div_ofNat_im, Complex.one_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, add_zero, mul_one]
  norm_num
  nlinarith [H_sub_sqrt3_div2_pos hH, t₀_i_im_eq_zero hH]

private lemma g_i_seg3_im_pos {t : ℝ} (ht_t0 : t₀_i H < t) (ht4 : t ≤ 4)
    (hH : 1 < H) : 0 < (fdBoundaryH H t - I).im := by
  rw [g_i_seg3_value (by linarith [t₀_i_gt_three hH]) ht4]
  simp only [Complex.add_im, Complex.neg_im, Complex.div_ofNat_im, Complex.one_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, add_zero, mul_one]
  norm_num
  nlinarith [H_sub_sqrt3_div2_pos hH, t₀_i_im_eq_zero hH]

private lemma g_i_ne_zero_seg3 {t : ℝ} (ht3 : 3 ≤ t) (ht4 : t ≤ 4) :
    fdBoundaryH H t - I ≠ 0 := by
  intro h; have := congr_arg Complex.re h
  simp only [Complex.zero_re] at this
  rcases eq_or_lt_of_le ht3 with rfl | ht3'
  · rw [fdBoundary_H_at_three_eq_rho] at this
    simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk,
      Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.div_ofNat_re,
      Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero] at this
    norm_num at this
  · rw [g_i_seg3_value ht3' ht4] at this
    simp only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, sub_zero, add_zero, zero_mul] at this
    norm_num at this

private lemma log_neg_eq_add_pi_I {z : ℂ} (_hz_ne : z ≠ 0) (hz_im : z.im < 0) :
    Complex.log (-z) = Complex.log z + ↑Real.pi * I := by
  change ↑(Real.log ‖-z‖) + ↑((-z).arg) * I =
    ↑(Real.log ‖z‖) + ↑z.arg * I + ↑Real.pi * I
  simp only [norm_neg]
  rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg hz_im]
  push_cast; ring

private lemma log_neg_half_branch :
    Complex.log (-((-1 : ℂ) / 2)) - Complex.log ((-1 : ℂ) / 2) = -(↑Real.pi * I) := by
  have h1 : -(-1 / 2 : ℂ) = (1 / 2 : ℂ) := by ring
  rw [h1]
  have hm : (-1 : ℂ) / 2 = ↑((1 : ℝ)/2) * (-1 : ℂ) := by push_cast; ring
  rw [hm, Complex.log_ofReal_mul (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (-1 : ℂ) ≠ 0),
      Complex.log_neg_one]
  rw [show (1 : ℂ)/2 = ↑((1 : ℝ)/2) from by push_cast; ring,
      ← Complex.ofReal_log (show (0 : ℝ) ≤ 1/2 from by norm_num)]
  ring

private lemma fdBoundary_sub_I_at_one (H : ℝ) :
    fdBoundaryH H 1 - I = exp (↑(Real.pi * (1 + (1 : ℝ)) / 6) * I) - I := by
  rw [fdBoundary_H_at_one_eq_rho_plus_one]
  simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk]
  rw [show Real.pi * (1 + 1) / 6 = Real.pi / 3 from by ring,
      show (↑(Real.pi / 3) : ℂ) * I = ↑(Real.pi / 3) * I from rfl,
      exp_real_angle_I, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast; ring

private lemma fdBoundary_sub_I_at_three (H : ℝ) :
    fdBoundaryH H 3 - I = exp (↑(Real.pi * (1 + (3 : ℝ)) / 6) * I) - I := by
  rw [fdBoundary_H_at_three_eq_rho]
  simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
  rw [show Real.pi * (1 + 3) / 6 = 2 * Real.pi / 3 from by ring]
  rw [show (↑(2 * Real.pi / 3) : ℂ) * I = ↑(2 * Real.pi / 3) * I from rfl,
      exp_real_angle_I, cos_two_pi_div_three, sin_two_pi_div_three]
  push_cast; ring

private lemma h2_at_three_im_neg (H : ℝ) :
    ((-1/2 + ↑(Real.sqrt 3 / 2 - 1 + ((3 : ℝ) - 3) * (H - Real.sqrt 3 / 2)) * I : ℂ)).im < 0 := by
  simp only [Complex.add_im, Complex.neg_im, Complex.div_ofNat_im,
    Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one]
  nlinarith [Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), sq_nonneg (2 - Real.sqrt 3)]

/-- On an open interval where `g` and `h` agree, both the values and the derivatives match. -/
private lemma eq_and_deriv_eq_on_Ioo {g h : ℝ → ℂ} {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hgh : ∀ s ∈ Ioo a b, g s = h s) : g t = h t ∧ deriv g t = deriv h t :=
  ⟨hgh t ht, Filter.EventuallyEq.deriv_eq
    (Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) hgh)⟩

private lemma hasDerivAt_i_seg0 (H : ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => 1/2 + (↑H - ↑s * (↑H - ↑(Real.sqrt 3) / 2) - 1) * I)
      (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
  have ht := (hasDerivAt_id t).ofReal_comp.mul_const (↑H - ↑(Real.sqrt 3) / 2 : ℂ)
  have hinner := ((hasDerivAt_const t (↑H : ℂ)).sub ht).sub (hasDerivAt_const t (1 : ℂ))
  exact ((hasDerivAt_const t ((1 : ℂ)/2)).add (hinner.mul_const I)).congr_deriv
    (by push_cast; ring)

private lemma hasDerivAt_i_arc (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (↑(Real.pi * (1 + s) / 6) * I) - I)
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I)) t := by
  have hf : HasDerivAt (fun s : ℝ => Real.pi * (1 + s) / 6) (Real.pi / 6) t :=
    ((hasDerivAt_id t).add_const (1 : ℝ) |>.const_mul (Real.pi / 6)).congr_of_eventuallyEq
      (Eventually.of_forall fun s => show _ from by simp [id]; ring)
      |>.congr_deriv (by ring)
  have hci : HasDerivAt (fun s : ℝ => (↑(Real.pi * (1 + s) / 6) : ℂ) * I)
      ((↑(Real.pi / 6) : ℂ) * I) t :=
    (hf.ofReal_comp.mul_const I).congr_deriv (by norm_num [smul_eq_mul])
  exact (hci.cexp.sub (hasDerivAt_const t I)).congr_deriv (by simp only [sub_zero]; ring)

private lemma hasDerivAt_i_seg3 (H : ℝ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => -1/2 + ↑(Real.sqrt 3 / 2 - 1 + (s - 3) * (H - Real.sqrt 3 / 2)) * I)
      ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
  have hf : HasDerivAt (fun s : ℝ => Real.sqrt 3 / 2 - 1 + (s - 3) * (H - Real.sqrt 3 / 2))
      (H - Real.sqrt 3 / 2) t :=
    ((hasDerivAt_id t).sub_const (3 : ℝ) |>.mul_const (H - Real.sqrt 3 / 2)
      |>.add_const (Real.sqrt 3 / 2 - 1)).congr_of_eventuallyEq
      (Eventually.of_forall fun s => show _ from by simp [id]; ring)
      |>.congr_deriv (by ring)
  exact ((hasDerivAt_const t ((-1 : ℂ)/2)).add
    (hf.ofReal_comp.mul_const I)).congr_deriv (by push_cast; ring)

private lemma hasDerivAt_i_seg4 (H : ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ↑(s - 9/2) + ↑(H - 1) * I) (1 : ℂ) t := by
  have h1 : HasDerivAt (fun s : ℝ => s - 9/2) (1 : ℝ) t := by
    have := (hasDerivAt_id t).sub (hasDerivAt_const t (9/2 : ℝ))
    exact this.congr_deriv (by ring)
  have h2 := h1.ofReal_comp.add (hasDerivAt_const t (↑(H - 1) * I))
  exact h2.congr_deriv (by simp only [Complex.ofReal_one, add_zero])

private lemma ftc_logDeriv_telescope_i (H : ℝ) (hH : 1 < H) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    let g := fun t => fdBoundaryH H t - I
    IntervalIntegrable (fun t => deriv g t / g t) volume 0 (2 - δ) ∧
    IntervalIntegrable (fun t => deriv g t / g t) volume (2 + δ) 5 ∧
    ((∫ t in (0 : ℝ)..(2 - δ), deriv g t / g t) + (∫ t in (2 + δ)..(5 : ℝ), deriv g t / g t) =
    Complex.log (g (2 - δ)) - Complex.log (g (2 + δ)) - 2 * ↑Real.pi * I) := by
  intro g
  have hH_sqrt : Real.sqrt 3 / 2 < H := by linarith [H_sub_sqrt3_div2_pos hH]
  set t₀ := t₀_i H with ht₀_def
  have ht₀3 := t₀_i_gt_three hH
  have ht₀4 := t₀_i_lt_four hH
  set h₀ : ℝ → ℂ := fun t => 1/2 + (↑H - ↑t * (↑H - ↑(Real.sqrt 3) / 2) - 1) * I
  set h₁ : ℝ → ℂ := fun t => exp (↑(Real.pi * (1 + t) / 6) * I) - I
  set h₂ : ℝ → ℂ :=
    fun t => -1/2 + ↑(Real.sqrt 3 / 2 - 1 + (t - 3) * (H - Real.sqrt 3 / 2)) * I
  set h₃ : ℝ → ℂ := fun t => ↑(t - 9/2) + ↑(H - 1) * I
  have hg_eq_h₀ : ∀ t, t ≤ 1 → g t = h₀ t := by
    intro t ht; change fdBoundaryH H t - I = h₀ t
    rw [fdBoundary_H_seg0 H ht]; simp only [h₀]; ring
  have hg_eq_h₁ : ∀ t, 1 < t → t < 3 → g t = h₁ t := by
    intro t ht1 ht3; change fdBoundaryH H t - I = h₁ t
    rw [fdBoundary_H_eq_arc ht1 ht3]
  have hg_eq_h₂ : ∀ t, 3 < t → t ≤ 4 → g t = h₂ t := fun t ht3 ht4 => g_i_seg3_value ht3 ht4
  have hg_eq_h₃ : ∀ t, 4 < t → g t = h₃ t := fun t ht4 => g_i_seg4_value ht4
  have hg0 : g 0 = h₀ 0 := hg_eq_h₀ 0 (by norm_num)
  have hg1_0 : g 1 = h₀ 1 := hg_eq_h₀ 1 (le_refl 1)
  have hg1_1 : g 1 = h₁ 1 := fdBoundary_sub_I_at_one H
  have hg2mδ : g (2 - δ) = h₁ (2 - δ) := hg_eq_h₁ (2 - δ) (by linarith) (by linarith)
  have hg2pδ : g (2 + δ) = h₁ (2 + δ) := hg_eq_h₁ (2 + δ) (by linarith) (by linarith)
  have hg3_1 : g 3 = h₁ 3 := fdBoundary_sub_I_at_three H
  have hg3_2 : g 3 = h₂ 3 := by
    change fdBoundaryH H 3 - I = h₂ 3
    rw [fdBoundary_H_at_three_eq_rho]
    simp only [h₂, ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
    push_cast; ring
  have hgt₀_2 : g t₀ = h₂ t₀ := hg_eq_h₂ t₀ ht₀3 (le_of_lt ht₀4)
  have hgt₀_val : g t₀ = (-1 : ℂ) / 2 := g_i_at_t₀ hH
  have hg4_2 : g 4 = h₂ 4 := hg_eq_h₂ 4 (by linarith) (le_refl 4)
  have hg4_3 : g 4 = h₃ 4 := by
    change fdBoundaryH H 4 - I = h₃ 4
    rw [fdBoundary_H_at_four H]; simp only [h₃]; push_cast; ring
  have hg5 : g 5 = h₃ 5 := hg_eq_h₃ 5 (by norm_num)
  have hd_h₀ : ∀ t : ℝ, HasDerivAt h₀ (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) t :=
    hasDerivAt_i_seg0 H
  have hd_h₁ : ∀ t : ℝ, HasDerivAt h₁
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I)) t :=
    hasDerivAt_i_arc
  have hd_h₂ : ∀ t : ℝ, HasDerivAt h₂ ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) t :=
    hasDerivAt_i_seg3 H
  have hd_h₃ : ∀ t : ℝ, HasDerivAt h₃ 1 t :=
    hasDerivAt_i_seg4 H
  have heq_01 : ∀ t ∈ Ioo (0 : ℝ) 1, g t = h₀ t ∧ deriv g t = deriv h₀ t := fun t ht =>
    eq_and_deriv_eq_on_Ioo ht (fun s hs => hg_eq_h₀ s (le_of_lt hs.2))
  have heq_1_2mδ : ∀ t ∈ Ioo (1 : ℝ) (2 - δ), g t = h₁ t ∧ deriv g t = deriv h₁ t := fun t ht =>
    eq_and_deriv_eq_on_Ioo ht (fun s hs => hg_eq_h₁ s hs.1 (by linarith [hs.2]))
  have heq_2pδ_3 : ∀ t ∈ Ioo (2 + δ) (3 : ℝ), g t = h₁ t ∧ deriv g t = deriv h₁ t := fun t ht =>
    eq_and_deriv_eq_on_Ioo ht (fun s hs => hg_eq_h₁ s (by linarith [hs.1]) hs.2)
  have heq_3_t₀ : ∀ t ∈ Ioo (3 : ℝ) t₀, g t = h₂ t ∧ deriv g t = deriv h₂ t := fun t ht =>
    eq_and_deriv_eq_on_Ioo ht (fun s hs => hg_eq_h₂ s hs.1 (by linarith [hs.2, ht₀4]))
  have heq_t₀_4 : ∀ t ∈ Ioo t₀ (4 : ℝ), g t = h₂ t ∧ deriv g t = deriv h₂ t := fun t ht =>
    eq_and_deriv_eq_on_Ioo ht (fun s hs => hg_eq_h₂ s (by linarith [hs.1, ht₀3]) (le_of_lt hs.2))
  have heq_45 : ∀ t ∈ Ioo (4 : ℝ) 5, g t = h₃ t ∧ deriv g t = deriv h₃ t := fun t ht =>
    eq_and_deriv_eq_on_Ioo ht (fun s hs => hg_eq_h₃ s hs.1)
  have hh₀_cont : ContinuousOn h₀ (Icc 0 1) :=
    fun t _ => (hd_h₀ t).continuousAt.continuousWithinAt
  have hh₃_cont : ContinuousOn h₃ (Icc 4 5) :=
    fun t _ => (hd_h₃ t).continuousAt.continuousWithinAt
  have hh₀_diff : ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ h₀ t :=
    fun t _ => (hd_h₀ t).differentiableAt
  have hh₃_diff : ∀ t ∈ Ioo (4 : ℝ) 5, DifferentiableAt ℝ h₃ t :=
    fun t _ => (hd_h₃ t).differentiableAt
  have hh₁_cont : ∀ a b : ℝ, ContinuousOn h₁ (Icc a b) :=
    fun _ _ t _ => (hd_h₁ t).continuousAt.continuousWithinAt
  have hh₂_cont : ∀ a b : ℝ, ContinuousOn h₂ (Icc a b) :=
    fun _ _ t _ => (hd_h₂ t).continuousAt.continuousWithinAt
  have hh₁_diff : ∀ a b : ℝ, ∀ t ∈ Ioo a b, DifferentiableAt ℝ h₁ t :=
    fun _ _ t _ => (hd_h₁ t).differentiableAt
  have hh₂_diff : ∀ a b : ℝ, ∀ t ∈ Ioo a b, DifferentiableAt ℝ h₂ t :=
    fun _ _ t _ => (hd_h₂ t).differentiableAt
  have hh₀_deriv_cont : ContinuousOn (deriv h₀) (Icc 0 1) := by
    rw [show deriv h₀ = fun _ => -(↑(H - Real.sqrt 3 / 2) : ℂ) * I from
      funext fun t => (hd_h₀ t).deriv]; exact continuousOn_const
  have hh₁_deriv_cont : ∀ (a b : ℝ), ContinuousOn (deriv h₁) (Icc a b) := by
    intro a b
    rw [show deriv h₁ = fun t => ↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I) from
      funext fun t => (hd_h₁ t).deriv]
    exact (Continuous.mul continuous_const (Continuous.cexp (Continuous.mul
      (continuous_ofReal.comp (by fun_prop : Continuous fun s => Real.pi * (1 + s) / 6))
      continuous_const))).continuousOn
  have hh₂_deriv_cont : ∀ (a b : ℝ), ContinuousOn (deriv h₂) (Icc a b) := by
    intro a b
    rw [show deriv h₂ = fun _ => (↑(H - Real.sqrt 3 / 2) : ℂ) * I from
      funext fun t => (hd_h₂ t).deriv]; exact continuousOn_const
  have hh₃_deriv_cont : ContinuousOn (deriv h₃) (Icc 4 5) := by
    rw [show deriv h₃ = fun _ => (1 : ℂ) from
      funext fun t => (hd_h₃ t).deriv]; exact continuousOn_const
  have hh₀_slit : ∀ t ∈ Icc (0 : ℝ) 1, h₀ t ∈ slitPlane := by
    intro t ⟨ht0, ht1⟩; rw [← hg_eq_h₀ t ht1]
    exact g_i_slitPlane_left ht0 (by linarith)
  have piece₀ := ftc_log_piece (by norm_num : (0 : ℝ) ≤ 1) hh₀_cont hh₀_diff
    hh₀_deriv_cont hh₀_slit heq_01 hg0 hg1_0
  have hh₁_slit_12 : ∀ t ∈ Icc (1 : ℝ) (2 - δ), h₁ t ∈ slitPlane := by
    intro t ⟨ht1, ht2⟩
    rcases eq_or_lt_of_le ht1 with rfl | ht1'
    · rw [← hg1_1]; exact g_i_slitPlane_left (by norm_num) (by linarith)
    · rw [← hg_eq_h₁ t ht1' (by linarith)]
      exact g_i_slitPlane_left (by linarith) (by linarith)
  have piece₁ := ftc_log_piece (by linarith : (1 : ℝ) ≤ 2 - δ) (hh₁_cont 1 (2-δ))
    (hh₁_diff 1 (2-δ)) (hh₁_deriv_cont 1 (2-δ)) hh₁_slit_12 heq_1_2mδ hg1_1 hg2mδ
  have hh₁_slit_23 : ∀ t ∈ Icc (2 + δ) (3 : ℝ), h₁ t ∈ slitPlane := by
    intro t ⟨ht2, ht3⟩
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · rw [← hg3_1]; exact g_i_slitPlane_arc_right (by linarith) (le_refl 3)
    · rw [← hg_eq_h₁ t (by linarith) ht3']
      exact g_i_slitPlane_arc_right (by linarith) (le_of_lt ht3')
  have piece₂ := ftc_log_piece (by linarith : (2 + δ) ≤ 3) (hh₁_cont (2+δ) 3)
    (hh₁_diff (2+δ) 3) (hh₁_deriv_cont (2+δ) 3) hh₁_slit_23 heq_2pδ_3 hg2pδ hg3_1
  have hh₂_im_np_3t₀ : ∀ t ∈ Icc (3 : ℝ) t₀, (h₂ t).im ≤ 0 := by
    intro t ⟨ht3, ht_t0⟩
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · exact le_of_lt (h2_at_three_im_neg H)
    · rcases eq_or_lt_of_le ht_t0 with rfl | ht_t0'
      · change (h₂ t₀).im ≤ 0
        rw [← hg_eq_h₂ t₀ (by linarith [t₀_i_gt_three hH]) (by linarith [t₀_i_lt_four hH]),
          hgt₀_val]
        norm_num
      · change (h₂ t).im ≤ 0
        rw [← hg_eq_h₂ t ht3' (by linarith)]
        exact le_of_lt (g_i_seg3_im_neg ht3' ht_t0' hH)
  have hh₂_ne_3t₀ : ∀ t ∈ Icc (3 : ℝ) t₀, h₂ t ≠ 0 := by
    intro t ⟨ht3, ht_t0⟩
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · rw [← hg3_2]; exact g_i_ne_zero_seg3 (le_refl 3) (by linarith)
    · rw [← hg_eq_h₂ t ht3' (by linarith)]
      exact g_i_ne_zero_seg3 (by linarith) (by linarith)
  have hh₂_im_neg_int_3t₀ : ∀ t ∈ Ioo (3 : ℝ) t₀, (h₂ t).im < 0 := by
    intro t ⟨ht3, ht_t0⟩
    rw [← hg_eq_h₂ t ht3 (by linarith)]
    exact g_i_seg3_im_neg ht3 ht_t0 hH
  have piece₃ := ftc_log_piece_lower (by linarith : (3 : ℝ) ≤ t₀)
    (hh₂_cont 3 t₀) (hh₂_diff 3 t₀) (hh₂_deriv_cont 3 t₀) hh₂_im_np_3t₀ hh₂_ne_3t₀
    hh₂_im_neg_int_3t₀ heq_3_t₀ hg3_2 hgt₀_2
  have hh₂_im_nn_t₀4 : ∀ t ∈ Icc t₀ (4 : ℝ), 0 ≤ (h₂ t).im := by
    intro t ⟨ht_t0, ht4⟩
    rcases eq_or_lt_of_le ht_t0 with rfl | ht_t0'
    · rw [← hgt₀_2, hgt₀_val]; norm_num
    · rw [← hg_eq_h₂ t (by linarith) ht4]
      exact le_of_lt (g_i_seg3_im_pos ht_t0' ht4 hH)
  have hh₂_ne_t₀4 : ∀ t ∈ Icc t₀ (4 : ℝ), h₂ t ≠ 0 := by
    intro t ⟨ht_t0, ht4⟩
    rcases eq_or_lt_of_le ht_t0 with rfl | ht_t0'
    · rw [← hgt₀_2]; exact g_i_ne_zero_seg3 (by linarith) (by linarith)
    · rw [← hg_eq_h₂ t (by linarith) ht4]
      exact g_i_ne_zero_seg3 (by linarith) ht4
  have hh₂_slit_int_t₀4 : ∀ t ∈ Ioo t₀ (4 : ℝ), h₂ t ∈ slitPlane := by
    intro t ⟨ht_t0, ht4⟩
    rw [← hg_eq_h₂ t (by linarith) (le_of_lt ht4)]
    rw [Complex.mem_slitPlane_iff]; right
    exact ne_of_gt (g_i_seg3_im_pos ht_t0 (le_of_lt ht4) hH)
  have piece₄ := ftc_log_piece_upper (by linarith : t₀ ≤ 4)
    (hh₂_cont t₀ 4) (hh₂_diff t₀ 4) (hh₂_deriv_cont t₀ 4)
    hh₂_im_nn_t₀4 hh₂_ne_t₀4 hh₂_slit_int_t₀4 heq_t₀_4 hgt₀_2 hg4_2
  have hh₃_slit : ∀ t ∈ Icc (4 : ℝ) 5, h₃ t ∈ slitPlane := by
    intro t ⟨ht4, ht5⟩
    rcases eq_or_lt_of_le ht4 with rfl | ht4'
    · rw [Complex.mem_slitPlane_iff]; right
      simp only [h₃, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
      linarith
    · rw [show h₃ t = g t from (hg_eq_h₃ t ht4').symm, Complex.mem_slitPlane_iff]; right
      show (g t).im ≠ 0
      simp only [show g t = h₃ t from hg_eq_h₃ t ht4', h₃, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
      linarith
  have piece₅ := ftc_log_piece (by norm_num : (4 : ℝ) ≤ 5) hh₃_cont hh₃_diff
    hh₃_deriv_cont hh₃_slit heq_45 hg4_3 hg5
  have hint_left : IntervalIntegrable (fun t => deriv g t / g t) volume 0 (2 - δ) :=
    piece₀.1.trans piece₁.1
  have hint_right : IntervalIntegrable (fun t => deriv g t / g t) volume (2 + δ) 5 :=
    piece₂.1.trans (piece₃.1.trans (piece₄.1.trans piece₅.1))
  refine ⟨hint_left, hint_right, ?_⟩
  rw [(intervalIntegral.integral_add_adjacent_intervals piece₀.1 piece₁.1).symm,
    (intervalIntegral.integral_add_adjacent_intervals piece₂.1
      (piece₃.1.trans (piece₄.1.trans piece₅.1))).symm,
    (intervalIntegral.integral_add_adjacent_intervals piece₃.1
      (piece₄.1.trans piece₅.1)).symm,
    (intervalIntegral.integral_add_adjacent_intervals piece₄.1 piece₅.1).symm,
    piece₀.2, piece₁.2, piece₂.2, piece₃.2, piece₄.2, piece₅.2]
  have hg3_im_neg : (g 3).im < 0 := by rw [hg3_2]; exact h2_at_three_im_neg H
  have hg3_ne : g 3 ≠ 0 := g_i_ne_zero_seg3 (le_refl 3) (by norm_num)
  have h_branch_3 : Complex.log (-(g 3)) = Complex.log (g 3) + ↑Real.pi * I :=
    log_neg_eq_add_pi_I hg3_ne hg3_im_neg
  have h_branch_t₀ : Complex.log (-(g t₀)) - Complex.log (g t₀) = -(↑Real.pi * I) := by
    rw [hgt₀_val]; exact log_neg_half_branch
  have hg_closed : g 0 = g 5 := by
    change fdBoundaryH H 0 - I = fdBoundaryH H 5 - I; rw [fdBoundary_H_closed H]
  have h_branch_t₀' : Complex.log (-(g t₀)) = Complex.log (g t₀) - ↑Real.pi * I := by
    linear_combination h_branch_t₀
  rw [hg_closed, h_branch_3, h_branch_t₀']; ring

-- Helper: for ε < threshold where threshold ≤ min(2sin(π/12), 1),
-- the map δ(ε) = 12/π · arcsin(ε/2) satisfies δ < 1.
private lemma i_delta_lt_one {ε : ℝ} (hε_pos : 0 < ε)
    (hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12)) :
    12 / Real.pi * Real.arcsin (ε / 2) < 1 := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have harcsin_lt := arcsin_eps_div_two_lt_pi_12 hε_pos hε_lt_2sin
  calc 12 / Real.pi * Real.arcsin (ε / 2)
      < 12 / Real.pi * (Real.pi / 12) :=
        mul_lt_mul_of_pos_left harcsin_lt (div_pos (by norm_num) hpi_pos)
    _ = 1 := by field_simp

private lemma i_h_far (H : ℝ) (hH : 1 < H) :
    let threshold := min (min (min (1/2 : ℝ) (H - 1)) (2 * Real.sin (Real.pi / 12))) 1
    ∀ ε, 0 < ε → ε < threshold →
      ∀ t ∈ Icc (0 : ℝ) 5,
        (12 / Real.pi * Real.arcsin (ε / 2)) < |t - 2| →
        ε < ‖fdBoundaryH H t - I‖ := by
  intro threshold ε hε_pos hε_lt t ht_mem h_abs
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hH1_pos : 0 < H - 1 := by linarith
  have hsin_pos : 0 < Real.sin (Real.pi / 12) := sin_pi_12_pos
  have h2sin_pos : 0 < 2 * Real.sin (Real.pi / 12) := by positivity
  have hε_lt_half : ε < 1/2 := lt_of_lt_of_le hε_lt
    (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hε_lt_gap : ε < H - 1 := lt_of_lt_of_le hε_lt
    (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) := lt_of_lt_of_le hε_lt
    (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε_lt_one : ε < 1 := lt_of_lt_of_le hε_lt (min_le_right _ _)
  have hε_half_pos : 0 < ε / 2 := by linarith
  have hε_half_le : ε / 2 ≤ 1 := by linarith
  have hε_half_neg : -1 ≤ ε / 2 := by linarith
  have harcsin_pos : 0 < Real.arcsin (ε / 2) := Real.arcsin_pos.mpr hε_half_pos
  set δ := 12 / Real.pi * Real.arcsin (ε / 2) with hδ_def
  have hδ_pos : 0 < δ := by rw [hδ_def]; positivity
  have hδ_lt_one : δ < 1 := i_delta_lt_one hε_pos hε_lt_2sin
  have hδ_angle : δ * Real.pi / 12 = Real.arcsin (ε / 2) := by rw [hδ_def]; field_simp
  have h_norm_L : ‖fdBoundaryH H (2 - δ) - I‖ = ε := by
    rw [g_i_norm_left hδ_pos hδ_lt_one, hδ_angle,
        Real.sin_arcsin hε_half_neg hε_half_le]; linarith
  have h_norm_R : ‖fdBoundaryH H (2 + δ) - I‖ = ε := by
    rw [g_i_norm_right hδ_pos hδ_lt_one, hδ_angle,
        Real.sin_arcsin hε_half_neg hε_half_le]; linarith
  -- h_abs : δ < |t - 2|, so t < 2 - δ or t > 2 + δ
  rcases lt_or_ge t (2 - δ) with h_left | h_right
  · -- t < 2 - δ: use left norm bounds
    rcases le_or_gt t 1 with ht1 | ht1
    · calc ε < 1 / 2 := hε_lt_half
        _ ≤ ‖fdBoundaryH H t - I‖ := g_i_norm_ge_seg0 ht_mem.1 ht1
    · change ε < ‖fdBoundaryH H t - I‖
      rw [g_i_norm_arc_left ht1 (by linarith)]
      rw [← h_norm_L, g_i_norm_left hδ_pos hδ_lt_one]
      apply mul_lt_mul_of_pos_left _ (by norm_num : (0 : ℝ) < 2)
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos])
  · -- t ≥ 2 - δ and δ < |t - 2|, so t > 2 + δ
    have h_gt : 2 + δ < t := by
      rcases le_or_gt (2 : ℝ) t with h2 | h2
      · -- t ≥ 2: |t - 2| = t - 2 > δ
        rw [abs_of_nonneg (by linarith)] at h_abs
        linarith
      · -- t < 2: |t - 2| = 2 - t, but 2 - t < δ from h_right, contradiction
        rw [abs_of_neg (by linarith)] at h_abs
        linarith
    rcases lt_or_ge t 3 with ht3 | ht3
    · change ε < ‖fdBoundaryH H t - I‖
      rw [g_i_norm_arc_right (by linarith) ht3]
      rw [← h_norm_R, g_i_norm_right hδ_pos hδ_lt_one]
      apply mul_lt_mul_of_pos_left _ (by norm_num : (0 : ℝ) < 2)
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos])
    · rcases le_or_gt t 4 with ht4 | ht4
      · calc ε < 1 / 2 := hε_lt_half
          _ ≤ ‖fdBoundaryH H t - I‖ := g_i_norm_ge_seg3 ht3 ht4
      · calc ε < H - 1 := hε_lt_gap
          _ ≤ ‖fdBoundaryH H t - I‖ :=
              g_i_norm_ge_seg4 H hH (le_of_lt ht4) ht_mem.2

private lemma i_h_near (H : ℝ) :
    let threshold := min (min (min (1/2 : ℝ) (H - 1)) (2 * Real.sin (Real.pi / 12))) 1
    ∀ ε, 0 < ε → ε < threshold →
      ∀ t, |t - 2| ≤ (12 / Real.pi * Real.arcsin (ε / 2)) →
        ‖fdBoundaryH H t - I‖ ≤ ε := by
  intro threshold ε hε_pos hε_lt t h_abs
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hε_half_pos : 0 < ε / 2 := by linarith
  have hε_lt_one : ε < 1 := lt_of_lt_of_le hε_lt (min_le_right _ _)
  have hε_half_le : ε / 2 ≤ 1 := by linarith
  have hε_half_neg : -1 ≤ ε / 2 := by linarith
  have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) := lt_of_lt_of_le hε_lt
    (le_trans (min_le_left _ _) (min_le_right _ _))
  have harcsin_pos : 0 < Real.arcsin (ε / 2) := Real.arcsin_pos.mpr hε_half_pos
  set δ := 12 / Real.pi * Real.arcsin (ε / 2) with hδ_def
  have hδ_pos : 0 < δ := by rw [hδ_def]; positivity
  have hδ_lt_one : δ < 1 := i_delta_lt_one hε_pos hε_lt_2sin
  have hδ_angle : δ * Real.pi / 12 = Real.arcsin (ε / 2) := by rw [hδ_def]; field_simp
  have hδpi12_le : δ * Real.pi / 12 ≤ Real.pi / 2 := by
    rw [hδ_angle]; exact le_of_lt (Real.arcsin_lt_pi_div_two.mpr (by linarith))
  -- From h_abs : |t - 2| ≤ δ
  rw [abs_le] at h_abs
  -- t ∈ [2-δ, 2+δ] ⊂ (1, 3) for δ < 1
  rcases le_or_gt t 2 with ht2 | ht2
  · rcases eq_or_lt_of_le ht2 with rfl | ht2'
    · rw [fdBoundary_H_at_two_eq_I, sub_self, norm_zero]; exact le_of_lt hε_pos
    · have ht1 : 1 < t := by linarith [h_abs.1]
      rw [g_i_norm_arc_left ht1 ht2']
      have h2t_le : 2 - t ≤ δ := by linarith [h_abs.1]
      have h2t_nonneg : 0 ≤ (2 - t) * Real.pi / 12 := by nlinarith [Real.pi_pos]
      have h2t_le_pi2 : (2 - t) * Real.pi / 12 ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
      calc 2 * Real.sin ((2 - t) * Real.pi / 12)
          ≤ 2 * Real.sin (δ * Real.pi / 12) :=
            mul_le_mul_of_nonneg_left
              (Real.sin_le_sin_of_le_of_le_pi_div_two
                (by nlinarith [Real.pi_pos])
                hδpi12_le
                (by nlinarith))
              (by norm_num)
        _ = ε := by rw [hδ_angle, Real.sin_arcsin hε_half_neg hε_half_le]; linarith
  · have ht3 : t < 3 := by linarith [h_abs.2]
    rw [g_i_norm_arc_right ht2 ht3]
    have ht2_le : t - 2 ≤ δ := by linarith [h_abs.2]
    have ht2_nonneg : 0 ≤ (t - 2) * Real.pi / 12 := by nlinarith [Real.pi_pos]
    have ht2_le_pi2 : (t - 2) * Real.pi / 12 ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
    calc 2 * Real.sin ((t - 2) * Real.pi / 12)
        ≤ 2 * Real.sin (δ * Real.pi / 12) :=
          mul_le_mul_of_nonneg_left
            (Real.sin_le_sin_of_le_of_le_pi_div_two
              (by nlinarith [Real.pi_pos])
              hδpi12_le
              (by nlinarith))
            (by norm_num)
      _ = ε := by rw [hδ_angle, Real.sin_arcsin hε_half_neg hε_half_le]; linarith

private lemma i_angle_bound {δ ε : ℝ} (H : ℝ)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (h_norm_L : ‖fdBoundaryH H (2 - δ) - I‖ = ε) :
    δ * Real.pi / 12 < ε := by
  set x := δ * Real.pi / 12 with hx_def
  have hx_pos : 0 < x := by positivity
  have hx_le_one : x ≤ 1 := by nlinarith [Real.pi_le_four]
  have h_sin_lb := Real.sin_gt_sub_cube hx_pos hx_le_one
  have h_lb : x - x ^ 3 / 4 > x / 2 := by nlinarith [sq_nonneg x, sq_nonneg (1 - x)]
  have h_norm_is_2sin : 2 * Real.sin x = ε := by
    rw [hx_def]
    linarith [g_i_norm_left (H := H) hδ_pos hδ_lt_one]
  linarith

-- Helper: integrability and FTC for the i-crossing, with integrand already in the
-- form expected by pv_tendsto_of_crossing_limit (i.e. (γ t - I)⁻¹ * deriv γ t).
private lemma i_ftc_integrability (H : ℝ) (hH : 1 < H) {ε : ℝ}
    (hε_pos : 0 < ε) (hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12)) :
    let δ := 12 / Real.pi * Real.arcsin (ε / 2)
    IntervalIntegrable (fun t => (fdBoundaryH H t - I)⁻¹ * deriv (fdBoundaryH H) t)
        volume 0 (2 - δ) ∧
    IntervalIntegrable (fun t => (fdBoundaryH H t - I)⁻¹ * deriv (fdBoundaryH H) t)
        volume (2 + δ) 5 ∧
    ((∫ t in (0 : ℝ)..(2 - δ), (fdBoundaryH H t - I)⁻¹ * deriv (fdBoundaryH H) t) +
     (∫ t in (2 + δ)..(5 : ℝ), (fdBoundaryH H t - I)⁻¹ * deriv (fdBoundaryH H) t) =
     Complex.log (fdBoundaryH H (2 - δ) - I) -
     Complex.log (fdBoundaryH H (2 + δ) - I) - 2 * ↑Real.pi * I) := by
  intro δ
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hε_half_pos : 0 < ε / 2 := by linarith
  have harcsin_pos : 0 < Real.arcsin (ε / 2) := Real.arcsin_pos.mpr hε_half_pos
  have hδ_pos : 0 < δ := mul_pos (div_pos (by norm_num) hpi_pos) harcsin_pos
  have hδ_lt_one : δ < 1 := i_delta_lt_one hε_pos hε_lt_2sin
  obtain ⟨hL, hR, hsum⟩ := ftc_logDeriv_telescope_i H hH hδ_pos hδ_lt_one
  have h_congr : ∀ t, (fdBoundaryH H t - I)⁻¹ * deriv (fdBoundaryH H) t =
      deriv (fun s => fdBoundaryH H s - I) t / (fdBoundaryH H t - I) := fun t => by
    have hd : deriv (fun s => fdBoundaryH H s - I) t = deriv (fdBoundaryH H) t :=
      deriv_sub_const (f := fdBoundaryH H) _
    rw [hd, div_eq_mul_inv, mul_comm]
  refine ⟨(intervalIntegrable_congr (fun t _ => h_congr t)).mpr hL,
          (intervalIntegrable_congr (fun t _ => h_congr t)).mpr hR, ?_⟩
  simp_rw [h_congr]; exact hsum

-- Helper: the log-difference E(ε) tends to -(I·π).
private lemma i_E_tendsto (H : ℝ) (_ : 1 < H) (threshold : ℝ) (hthresh_pos : 0 < threshold)
    (hthresh_le_2sin : threshold ≤ 2 * Real.sin (Real.pi / 12))
    (hthresh_le_one : threshold ≤ 1) :
    Tendsto (fun ε =>
        Complex.log (fdBoundaryH H (2 - 12 / Real.pi * Real.arcsin (ε / 2)) - I) -
        Complex.log (fdBoundaryH H (2 + 12 / Real.pi * Real.arcsin (ε / 2)) - I) -
        2 * ↑Real.pi * I)
      (𝓝[>] 0) (𝓝 (-(I * ↑Real.pi))) := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro r hr
  refine ⟨min threshold (r/2), lt_min hthresh_pos (by linarith), ?_⟩
  intro ε hε_mem hε_dist
  simp only [Set.mem_Ioi] at hε_mem
  rw [Real.dist_eq, sub_zero, abs_of_pos hε_mem] at hε_dist
  have hε_pos : 0 < ε := hε_mem
  have hε_lt : ε < threshold := hε_dist.trans_le (min_le_left _ _)
  have hε_lt_r2 : ε < r / 2 := hε_dist.trans_le (min_le_right _ _)
  have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) := lt_of_lt_of_le hε_lt hthresh_le_2sin
  have hε_half_neg : -1 ≤ ε / 2 := by linarith
  have hε_half_le : ε / 2 ≤ 1 := by linarith [lt_of_lt_of_le hε_lt hthresh_le_one]
  have hε_half_pos : 0 < ε / 2 := by linarith
  have harcsin_pos : 0 < Real.arcsin (ε / 2) := Real.arcsin_pos.mpr hε_half_pos
  have hδ_pos : 0 < 12 / Real.pi * Real.arcsin (ε / 2) :=
    mul_pos (div_pos (by norm_num) hpi_pos) harcsin_pos
  have hδ_lt_one : 12 / Real.pi * Real.arcsin (ε / 2) < 1 :=
    i_delta_lt_one hε_pos hε_lt_2sin
  -- sin((δ·π/12)) = ε/2
  have hsin_eq : Real.sin ((12 / Real.pi * Real.arcsin (ε / 2)) * Real.pi / 12) = ε / 2 := by
    have : (12 / Real.pi * Real.arcsin (ε / 2)) * Real.pi / 12 = Real.arcsin (ε / 2) := by
      field_simp
    rw [this, Real.sin_arcsin hε_half_neg hε_half_le]
  -- Angle bound: δπ/12 < ε
  have h_angle_bnd : (12 / Real.pi * Real.arcsin (ε / 2)) * Real.pi / 12 < ε :=
    i_angle_bound H hδ_pos hδ_lt_one (by rw [g_i_norm_left hδ_pos hδ_lt_one]; linarith)
  -- norms at crossing points equal ε
  have h_nL : ‖fdBoundaryH H (2 - 12 / Real.pi * Real.arcsin (ε / 2)) - I‖ = ε := by
    rw [g_i_norm_left hδ_pos hδ_lt_one]; linarith
  have h_nR : ‖fdBoundaryH H (2 + 12 / Real.pi * Real.arcsin (ε / 2)) - I‖ = ε := by
    rw [g_i_norm_right hδ_pos hδ_lt_one]
    linarith [h_nL, g_i_norm_left (H := H) hδ_pos hδ_lt_one]
  -- E(ε) - (-(I·π)) = -(δπ/6)·I
  have h_E_eq :
      Complex.log (fdBoundaryH H (2 - 12 / Real.pi * Real.arcsin (ε / 2)) - I) -
      Complex.log (fdBoundaryH H (2 + 12 / Real.pi * Real.arcsin (ε / 2)) - I) -
      2 * ↑Real.pi * I - -(I * ↑Real.pi) =
      -(↑((12 / Real.pi * Real.arcsin (ε / 2)) * Real.pi / 6) * I) := by
    rw [← Complex.re_add_im
          (Complex.log (fdBoundaryH H (2 - 12 / Real.pi * Real.arcsin (ε / 2)) - I)),
        ← Complex.re_add_im
          (Complex.log (fdBoundaryH H (2 + 12 / Real.pi * Real.arcsin (ε / 2)) - I)),
        Complex.log_re, Complex.log_re, Complex.log_im, Complex.log_im,
        arg_approach_i_left (H := H) hδ_pos hδ_lt_one,
        arg_approach_i_right (H := H) hδ_pos hδ_lt_one, h_nL, h_nR]
    push_cast; ring
  rw [Complex.dist_eq, h_E_eq, norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  linarith

/-- The PV integral of `(γ-I)⁻¹ γ'` over `[0,5]` with ε-ball cutoff tends to `-iπ`.

Proof wires through `pv_tendsto_of_crossing_limit` with:
- `t₀ = 2` (arc crossing at `i`)
- `δ(ε) = 12/π · arcsin(ε/2)` (arc-length inverse of the norm formula)
- `E(ε) = log(g(2-δ)) - log(g(2+δ)) - 2πi` (FTC telescope with branch correction)
- `h_limit : E(ε) → -(I·π)` (arg computation shows the difference is constantly `-iπ`) -/
theorem pv_integral_at_i_tendsto (H : ℝ) (hH : 1 < H) :
    Tendsto (fun ε => ∫ t in (0 : ℝ)..5, if ‖fdBoundaryH H t - I‖ > ε
      then (fdBoundaryH H t - I)⁻¹ *
           deriv (fun s => fdBoundaryH H s - I) t
      else 0) (𝓝[>] 0) (𝓝 (-(I * ↑Real.pi))) := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hH1_pos : 0 < H - 1 := by linarith
  have hsin_pos : 0 < Real.sin (Real.pi / 12) := sin_pi_12_pos
  have h2sin_pos : 0 < 2 * Real.sin (Real.pi / 12) := by positivity
  set threshold := min (min (min (1/2 : ℝ) (H - 1)) (2 * Real.sin (Real.pi / 12))) 1
    with hthreshold_def
  have hthresh_pos : 0 < threshold :=
    lt_min (lt_min (lt_min (by norm_num) hH1_pos) h2sin_pos) one_pos
  have hthresh_le_2sin : threshold ≤ 2 * Real.sin (Real.pi / 12) :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hthresh_le_one : threshold ≤ 1 := min_le_right _ _
  -- δ(ε) = 12/π * arcsin(ε/2)
  have hδ_pos : ∀ ε, 0 < ε → ε < threshold → 0 < 12 / Real.pi * Real.arcsin (ε / 2) :=
    fun ε hε _ => mul_pos (div_pos (by norm_num) hpi_pos)
      (Real.arcsin_pos.mpr (by linarith))
  have hδ_small : ∀ ε, 0 < ε → ε < threshold →
      12 / Real.pi * Real.arcsin (ε / 2) < min (2 - 0) (5 - 2) := by
    intro ε hε_pos hε_lt
    have hδ1 := i_delta_lt_one hε_pos (lt_of_lt_of_le hε_lt hthresh_le_2sin)
    simp only [sub_zero]; exact lt_min (by linarith) (by linarith)
  -- reduce to the form without deriv (fun s => ...)
  suffices h : Tendsto (fun ε => ∫ t in (0 : ℝ)..5,
        if ‖fdBoundaryH H t - I‖ > ε
        then (fdBoundaryH H t - I)⁻¹ * deriv (fdBoundaryH H) t
        else 0)
      (𝓝[>] 0) (𝓝 (-(I * ↑Real.pi))) by
    have heq : ∀ ε, (∫ t in (0 : ℝ)..5,
          if ‖fdBoundaryH H t - I‖ > ε
          then (fdBoundaryH H t - I)⁻¹ * deriv (fun s => fdBoundaryH H s - I) t
          else 0) =
        (∫ t in (0 : ℝ)..5,
          if ‖fdBoundaryH H t - I‖ > ε
          then (fdBoundaryH H t - I)⁻¹ * deriv (fdBoundaryH H) t
          else 0) := fun ε =>
      intervalIntegral.integral_congr fun t _ => by
        split_ifs with h
        · congr 1; exact deriv_sub_const (f := fdBoundaryH H) _
        · rfl
    simp_rw [heq]; exact h
  apply ContourIntegral.pv_tendsto_of_crossing_limit
    (t₀ := 2) (ht₀ := by norm_num)
    (threshold := threshold) (hthresh := hthresh_pos)
    (δ := fun ε => 12 / Real.pi * Real.arcsin (ε / 2))
    (E := fun ε =>
      Complex.log (fdBoundaryH H (2 - 12 / Real.pi * Real.arcsin (ε / 2)) - I) -
      Complex.log (fdBoundaryH H (2 + 12 / Real.pi * Real.arcsin (ε / 2)) - I) -
      2 * ↑Real.pi * I)
  · exact hδ_pos
  · exact hδ_small
  · intro ε hε_pos hε_lt; exact i_h_far H hH ε hε_pos hε_lt
  · intro ε hε_pos hε_lt; exact i_h_near H ε hε_pos hε_lt
  · -- h_ftc
    intro ε hε_pos hε_lt
    exact (i_ftc_integrability H hH hε_pos (lt_of_lt_of_le hε_lt hthresh_le_2sin)).2.2
  · -- hint_left
    intro ε hε_pos hε_lt
    exact (i_ftc_integrability H hH hε_pos (lt_of_lt_of_le hε_lt hthresh_le_2sin)).1
  · -- hint_right
    intro ε hε_pos hε_lt
    exact (i_ftc_integrability H hH hε_pos (lt_of_lt_of_le hε_lt hthresh_le_2sin)).2.1
  · -- h_limit
    exact i_E_tendsto H hH threshold hthresh_pos hthresh_le_2sin hthresh_le_one

/-- `generalizedWindingNumber' (fdBoundaryH H) 0 5 I = -1/2`.

Note: requires `1 < H` (not just `√3/2 < H`) because for `H > 1`, the point `I` is
strictly inside the contour and the branch cut correction on seg 3 contributes `-2πi`.
For `√3/2 < H < 1`, `I` would be outside the contour and the result would be `+1/2`. -/
theorem gWN_fdBoundary_H_at_i (H : ℝ) (hH : 1 < H) :
    generalizedWindingNumber' (fdBoundaryH H) 0 5 I = -1/2 := by
  apply ContourIntegral.gWN_eq_neg_half_of_pv_tendsto
  convert pv_integral_at_i_tendsto H hH using 2
  · simp [sub_zero, gt_iff_lt]
  · ring

end
