/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.Boundary.Basic
import LeanPool.LeanModularForms.GeneralizedResidueTheory.PiecewiseCurveAPI
import LeanPool.LeanModularForms.GeneralizedResidueTheory.CurveAvoidance
import LeanPool.LeanModularForms.GeneralizedResidueTheory.ArcCalculus

/-!
# Fundamental Domain Boundary – Bounds

Segment selectors, trigonometric helpers, and geometric bounds for the
fundamental domain boundary.

## Main Results

* `fdBoundary_H_im_pos` — positive imaginary part
* `fdBoundary_H_im_ge_sqrt3_div_2` — imaginary part ≥ √3/2
* `fdBoundary_H_re_abs_le_half` — |real part| ≤ 1/2
* `fdBoundary_continuous` — continuity of fixed-height boundary
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

lemma fdBoundary_H_eq_seg1_H {H t : ℝ} (ht : t ≤ 1) :
    fdBoundaryH H t = fdBoundarySeg1H H t := by
  simp only [fdBoundaryH, ht, ite_true, fdBoundarySeg1H]

lemma fdBoundary_H_eq_seg2_H {t : ℝ} (H : ℝ)
    (ht1 : 1 < t) (ht2 : t ≤ 2) :
    fdBoundaryH H t = fdBoundarySeg2H t := by
  simp only [fdBoundaryH, show ¬t ≤ 1 from not_le.mpr ht1, ht2, ite_true, ite_false,
    fdBoundarySeg2H, fdBoundarySeg2]

lemma fdBoundary_H_eq_seg3_H {t : ℝ} (H : ℝ)
    (ht2 : 2 < t) (ht3 : t ≤ 3) :
    fdBoundaryH H t = fdBoundarySeg3H t := by
  simp only [fdBoundaryH, show ¬t ≤ 1 from not_le.mpr (by linarith),
    show ¬t ≤ 2 from not_le.mpr ht2, ht3, ite_true, ite_false,
    fdBoundarySeg3H, fdBoundarySeg3]

lemma fdBoundary_H_eq_seg4_H {H t : ℝ}
    (ht3 : 3 < t) (ht4 : t ≤ 4) :
    fdBoundaryH H t = fdBoundarySeg4H H t := by
  simp only [fdBoundaryH, show ¬t ≤ 1 from not_le.mpr (by linarith),
    show ¬t ≤ 2 from not_le.mpr (by linarith), show ¬t ≤ 3 from not_le.mpr ht3,
    ht4, ite_true, ite_false, fdBoundarySeg4H]

lemma fdBoundary_H_eq_seg5_H {H t : ℝ} (ht4 : 4 < t) :
    fdBoundaryH H t = fdBoundarySeg5H H t := by
  simp only [fdBoundaryH, show ¬t ≤ 1 from not_le.mpr (by linarith),
    show ¬t ≤ 2 from not_le.mpr (by linarith), show ¬t ≤ 3 from not_le.mpr (by linarith),
    show ¬t ≤ 4 from not_le.mpr ht4, ite_false, fdBoundarySeg5H]

private lemma seg2_angle_in_range {t : ℝ} (ht1 : 1 ≤ t) (ht2 : t ≤ 2) :
    Real.pi / 3 ≤ Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3) ∧
    Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3) ≤ 2 * Real.pi / 3 := by
  have hpi := Real.pi_pos; constructor
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ t - 1 by linarith)
      (show (0 : ℝ) ≤ Real.pi / 6 by linarith)]
  · nlinarith [mul_le_mul_of_nonneg_right (show t - 1 ≤ 1 by linarith)
      (show (0 : ℝ) ≤ Real.pi / 6 by linarith)]

private lemma seg3_angle_in_range {t : ℝ} (ht2 : 2 ≤ t) (ht3 : t ≤ 3) :
    Real.pi / 3 ≤ Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2) ∧
    Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2) ≤ 2 * Real.pi / 3 := by
  have hpi := Real.pi_pos
  have h_nonneg : 0 ≤ (t - 2) * (2 * Real.pi / 3 - Real.pi / 2) := by nlinarith
  constructor
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_right (show t - 2 ≤ 1 by linarith)
      (show (0 : ℝ) ≤ Real.pi / 6 by linarith)]

private lemma sin_pos_of_angle_in_range {θ : ℝ} (h1 : Real.pi / 3 ≤ θ)
    (h2 : θ ≤ 2 * Real.pi / 3) : 0 < Real.sin θ :=
  ArcCalculus.sin_pos_of_mem_Ioo_zero_pi ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

private lemma sin_ge_sqrt3_div_2_of_angle_in_range {θ : ℝ} (h1 : Real.pi / 3 ≤ θ)
    (h2 : θ ≤ 2 * Real.pi / 3) : Real.sqrt 3 / 2 ≤ Real.sin θ := by
  have hpi := Real.pi_pos
  rw [show Real.sqrt 3 / 2 = Real.sin (Real.pi / 3) from Real.sin_pi_div_three.symm]
  by_cases h : θ ≤ Real.pi / 2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h h1
  · push Not at h; rw [show Real.sin θ = Real.sin (Real.pi - θ) from (Real.sin_pi_sub θ).symm]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)

private lemma abs_cos_le_half_of_angle_in_range {θ : ℝ} (h1 : Real.pi / 3 ≤ θ)
    (h2 : θ ≤ 2 * Real.pi / 3) : |Real.cos θ| ≤ 1 / 2 :=
  ArcCalculus.abs_cos_le_half_of_mem_Icc ⟨h1, h2⟩

private lemma seg1_H_im {H t : ℝ} (_ht0 : 0 ≤ t) (_ht1 : t ≤ 1) :
    (fdBoundarySeg1H H t).im = H - t * (H - Real.sqrt 3 / 2) := by
  simp [fdBoundarySeg1H, add_im, ofReal_im, mul_im, I_re, I_im]

private lemma seg4_H_im {H t : ℝ} :
    (fdBoundarySeg4H H t).im =
      Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2) := by
  simp [fdBoundarySeg4H, add_im, ofReal_im, mul_im, I_re, I_im]

private lemma seg5_H_im {H t : ℝ} : (fdBoundarySeg5H H t).im = H := by
  simp [fdBoundarySeg5H, add_im, ofReal_im, mul_im, I_re, I_im]

private lemma seg2_as_trig (t : ℝ) :
    fdBoundarySeg2 t = ↑(Real.cos (Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3))) +
      ↑(Real.sin (Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3))) * I := by
  unfold fdBoundarySeg2
  conv_lhs => rw [show (↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3) : ℂ) * I =
    ↑(Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I from by push_cast; ring]
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]

private lemma seg3_as_trig (t : ℝ) :
    fdBoundarySeg3 t = ↑(Real.cos (Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2))) +
      ↑(Real.sin (Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2))) * I := by
  unfold fdBoundarySeg3
  conv_lhs =>
    rw [show (↑Real.pi / 2 + (↑t - 2) *
      (2 * ↑Real.pi / 3 - ↑Real.pi / 2) : ℂ) * I =
    ↑(Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I from by push_cast; ring]
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]

private lemma seg2_im {t : ℝ} :
    (fdBoundarySeg2 t).im = Real.sin (Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) := by
  rw [seg2_as_trig, add_im, ofReal_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]; ring

private lemma seg3_im {t : ℝ} :
    (fdBoundarySeg3 t).im =
      Real.sin (Real.pi / 2 +
        (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) := by
  rw [seg3_as_trig, add_im, ofReal_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]; ring

private lemma seg2_re {t : ℝ} :
    (fdBoundarySeg2 t).re = Real.cos (Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) := by
  rw [seg2_as_trig, add_re, ofReal_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]; ring

private lemma seg3_re {t : ℝ} :
    (fdBoundarySeg3 t).re =
      Real.cos (Real.pi / 2 +
        (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) := by
  rw [seg3_as_trig, add_re, ofReal_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]; ring

lemma fdBoundary_H_im_pos (H : ℝ)
    (hH : Real.sqrt 3 / 2 < H) :
    ∀ t ∈ Icc (0 : ℝ) 5,
      0 < (fdBoundaryH H t).im := by
  intro t ⟨ht0, ht5⟩
  have hsqrt : 0 < Real.sqrt 3 / 2 := by positivity
  by_cases h1 : t ≤ 1
  · rw [fdBoundary_H_eq_seg1_H h1, seg1_H_im ht0 h1]
    nlinarith
  · push Not at h1
    by_cases h2 : t ≤ 2
    · rw [fdBoundary_H_eq_seg2_H H h1 h2, fdBoundarySeg2H, seg2_im]
      exact sin_pos_of_angle_in_range (seg2_angle_in_range (le_of_lt h1) h2).1
        (seg2_angle_in_range (le_of_lt h1) h2).2
    · push Not at h2
      by_cases h3 : t ≤ 3
      · rw [fdBoundary_H_eq_seg3_H H h2 h3, fdBoundarySeg3H, seg3_im]
        exact sin_pos_of_angle_in_range (seg3_angle_in_range (le_of_lt h2) h3).1
          (seg3_angle_in_range (le_of_lt h2) h3).2
      · push Not at h3
        by_cases h4 : t ≤ 4
        · rw [fdBoundary_H_eq_seg4_H h3 h4, seg4_H_im]; nlinarith
        · push Not at h4
          rw [fdBoundary_H_eq_seg5_H h4, seg5_H_im]; linarith

lemma fdBoundary_H_im_ge_sqrt3_div_2 (H : ℝ)
    (hH : Real.sqrt 3 / 2 ≤ H) :
    ∀ t ∈ Icc (0 : ℝ) 5,
      Real.sqrt 3 / 2 ≤ (fdBoundaryH H t).im := by
  intro t ⟨ht0, ht5⟩
  by_cases h1 : t ≤ 1
  · rw [fdBoundary_H_eq_seg1_H h1, seg1_H_im ht0 h1]
    nlinarith
  · push Not at h1
    by_cases h2 : t ≤ 2
    · rw [fdBoundary_H_eq_seg2_H H h1 h2, fdBoundarySeg2H, seg2_im]
      exact sin_ge_sqrt3_div_2_of_angle_in_range
        (seg2_angle_in_range (le_of_lt h1) h2).1 (seg2_angle_in_range (le_of_lt h1) h2).2
    · push Not at h2
      by_cases h3 : t ≤ 3
      · rw [fdBoundary_H_eq_seg3_H H h2 h3, fdBoundarySeg3H, seg3_im]
        exact sin_ge_sqrt3_div_2_of_angle_in_range
          (seg3_angle_in_range (le_of_lt h2) h3).1 (seg3_angle_in_range (le_of_lt h2) h3).2
      · push Not at h3
        by_cases h4 : t ≤ 4
        · rw [fdBoundary_H_eq_seg4_H h3 h4, seg4_H_im]
          nlinarith
        · push Not at h4
          rw [fdBoundary_H_eq_seg5_H h4, seg5_H_im]; exact hH

private lemma seg1_H_re {H t : ℝ} : (fdBoundarySeg1H H t).re = 1 / 2 := by
  simp [fdBoundarySeg1H, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]

private lemma seg4_H_re {H t : ℝ} : (fdBoundarySeg4H H t).re = -1 / 2 := by
  simp [fdBoundarySeg4H, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]

private lemma seg5_H_re {H t : ℝ} : (fdBoundarySeg5H H t).re = t - 9 / 2 := by
  simp [fdBoundarySeg5H, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]

lemma fdBoundary_H_re_abs_le_half (H : ℝ) :
    ∀ t ∈ Icc (0 : ℝ) 5,
      |Complex.re (fdBoundaryH H t)| ≤ 1 / 2 := by
  intro t ⟨ht0, ht5⟩
  by_cases h1 : t ≤ 1
  · rw [fdBoundary_H_eq_seg1_H h1, seg1_H_re]; norm_num
  · push Not at h1
    by_cases h2 : t ≤ 2
    · rw [fdBoundary_H_eq_seg2_H H h1 h2, fdBoundarySeg2H, seg2_re]
      exact abs_cos_le_half_of_angle_in_range
        (seg2_angle_in_range (le_of_lt h1) h2).1 (seg2_angle_in_range (le_of_lt h1) h2).2
    · push Not at h2
      by_cases h3 : t ≤ 3
      · rw [fdBoundary_H_eq_seg3_H H h2 h3, fdBoundarySeg3H, seg3_re]
        exact abs_cos_le_half_of_angle_in_range
          (seg3_angle_in_range (le_of_lt h2) h3).1 (seg3_angle_in_range (le_of_lt h2) h3).2
      · push Not at h3
        by_cases h4 : t ≤ 4
        · rw [fdBoundary_H_eq_seg4_H h3 h4, seg4_H_re]; norm_num
        · push Not at h4
          rw [fdBoundary_H_eq_seg5_H h4, seg5_H_re]; rw [abs_le]; constructor <;> linarith

lemma fdBoundary_eq_seg1 {t : ℝ} (ht : t ≤ 1) :
    fdBoundary t = fdBoundarySeg1 t := by simp only [fdBoundary, ht, ite_true, fdBoundarySeg1]

lemma fdBoundary_eq_seg2 {t : ℝ} (ht1 : 1 < t) (ht2 : t ≤ 2) :
    fdBoundary t = fdBoundarySeg2 t := by
  simp only [fdBoundary, show ¬t ≤ 1 from not_le.mpr ht1, ht2, ite_true, ite_false,
    fdBoundarySeg2]

lemma fdBoundary_eq_seg3 {t : ℝ} (ht2 : 2 < t) (ht3 : t ≤ 3) :
    fdBoundary t = fdBoundarySeg3 t := by
  simp only [fdBoundary, show ¬t ≤ 1 from not_le.mpr (by linarith),
    show ¬t ≤ 2 from not_le.mpr ht2, ht3, ite_true, ite_false,
    fdBoundarySeg3]

lemma fdBoundary_eq_seg4 {t : ℝ} (ht3 : 3 < t) (ht4 : t ≤ 4) :
    fdBoundary t = fdBoundarySeg4 t := by
  simp only [fdBoundary, show ¬t ≤ 1 from not_le.mpr (by linarith),
    show ¬t ≤ 2 from not_le.mpr (by linarith), show ¬t ≤ 3 from not_le.mpr ht3,
    ht4, ite_true, ite_false, fdBoundarySeg4]

lemma fdBoundary_eq_seg5 {t : ℝ} (ht4 : 4 < t) :
    fdBoundary t = fdBoundarySeg5 t := by
  simp only [fdBoundary, show ¬t ≤ 1 from not_le.mpr (by linarith),
    show ¬t ≤ 2 from not_le.mpr (by linarith), show ¬t ≤ 3 from not_le.mpr (by linarith),
    show ¬t ≤ 4 from not_le.mpr ht4, ite_false, fdBoundarySeg5]

theorem fdBoundary_continuous : Continuous fdBoundary := by
  rw [fdBoundary_eq_fdBoundary_H]
  exact fdBoundary_H_continuous heightCutoff

lemma fdBoundary_im_pos :
    ∀ t ∈ Icc (0 : ℝ) 5,
      0 < (fdBoundary t).im := by
  rw [fdBoundary_eq_fdBoundary_H]
  exact fdBoundary_H_im_pos heightCutoff sqrt3_div2_lt_heightCutoff

lemma fdBoundary_H_im_le_H {H : ℝ} (hH : 1 ≤ H) :
    ∀ t ∈ Icc (0 : ℝ) 5, (fdBoundaryH H t).im ≤ H := by
  intro t ⟨ht0, ht5⟩
  have hH_sqrt3 : Real.sqrt 3 / 2 < H := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  by_cases h1 : t ≤ 1
  · rw [fdBoundary_H_eq_seg1_H h1, seg1_H_im ht0 h1]; nlinarith
  · push Not at h1
    by_cases h2 : t ≤ 2
    · rw [fdBoundary_H_eq_seg2_H H h1 h2, fdBoundarySeg2H, seg2_im]
      linarith [Real.sin_le_one (Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3))]
    · push Not at h2
      by_cases h3 : t ≤ 3
      · rw [fdBoundary_H_eq_seg3_H H h2 h3, fdBoundarySeg3H, seg3_im]
        linarith [Real.sin_le_one
          (Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2))]
      · push Not at h3
        by_cases h4 : t ≤ 4
        · rw [fdBoundary_H_eq_seg4_H h3 h4, seg4_H_im]; nlinarith
        · push Not at h4
          rw [fdBoundary_H_eq_seg5_H h4, seg5_H_im]

lemma fdBoundary_im_le_heightCutoff :
    ∀ t ∈ Icc (0 : ℝ) 5, (fdBoundary t).im ≤ heightCutoff := by
  rw [fdBoundary_eq_fdBoundary_H]
  exact fdBoundary_H_im_le_H (le_of_lt one_lt_heightCutoff)

lemma fdBoundary_re_abs_le_half :
    ∀ t ∈ Icc (0 : ℝ) 5,
      |Complex.re (fdBoundary t)| ≤ 1 / 2 := by
  rw [fdBoundary_eq_fdBoundary_H]
  exact fdBoundary_H_re_abs_le_half heightCutoff

lemma fdBoundary_im_ge_sqrt3_div_2 :
    ∀ t ∈ Icc (0 : ℝ) 5,
      Real.sqrt 3 / 2 ≤ (fdBoundary t).im := by
  rw [fdBoundary_eq_fdBoundary_H]
  exact fdBoundary_H_im_ge_sqrt3_div_2 heightCutoff (le_of_lt sqrt3_div2_lt_heightCutoff)

lemma fdBoundary_passes_through_i :
    ∃ t ∈ Icc (0 : ℝ) 5,
      fdBoundary t = ellipticPointI := ⟨2, by norm_num, fdBoundary_at_two⟩

lemma fdBoundary_passes_through_rho :
    ∃ t ∈ Icc (0 : ℝ) 5,
      fdBoundary t = ellipticPointRho := ⟨3, by norm_num, fdBoundary_at_three⟩

lemma fdBoundary_passes_through_rho_plus_one :
    ∃ t ∈ Icc (0 : ℝ) 5,
      fdBoundary t = ellipticPointRhoPlusOne := ⟨1, by norm_num, fdBoundary_at_one⟩

end
