/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.WindingWeights.Common
import LeanPool.LeanModularForms.ContourIntegral.WindingNumber
import LeanPool.LeanModularForms.ContourIntegral.CrossingLimit

/-!
# Winding Number Weight at ρ+1

PV integral computation and generalized winding number of `fdBoundaryH`
around the elliptic point ρ+1 = e^{πi/3}.

## Main Results

* `pv_integral_at_rho_plus_one_tendsto` — PV integral converges to -iπ/3
* `gWN_fdBoundary_H_at_rho_plus_one` — gWN = -1/6 at ρ+1
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

private lemma g_rho'_seg0_value {t : ℝ} (ht : t ≤ 1) :
    fdBoundaryH H t - ellipticPointRhoPlusOne =
    ↑((1 - t) * (H - Real.sqrt 3 / 2)) * I := by
  rw [fdBoundary_H_seg0 H ht]
  simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk]
  push_cast; ring

private lemma g_rho'_norm_seg0 (hH : Real.sqrt 3 / 2 < H) {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t < 1) :
    ‖fdBoundaryH H t - ellipticPointRhoPlusOne‖ = (1 - t) * (H - Real.sqrt 3 / 2) := by
  rw [g_rho'_seg0_value (le_of_lt ht1), norm_mul, Complex.norm_real,
    Complex.norm_I, mul_one, Real.norm_of_nonneg (mul_nonneg (by linarith) (by linarith))]

private lemma g_rho'_arc_value {t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) :
    fdBoundaryH H t - ellipticPointRhoPlusOne =
    Complex.exp (↑(Real.pi * (1 + t) / 6) * I) - (↑(1/2 : ℝ) + ↑(Real.sqrt 3 / 2) * I) := by
  rw [fdBoundary_H_eq_arc ht1 ht3]
  simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk]
  push_cast; ring

private lemma g_rho'_seg3_value {t : ℝ} (ht3 : 3 < t) (ht4 : t ≤ 4) :
    fdBoundaryH H t - ellipticPointRhoPlusOne =
    -1 + ↑((t - 3) * (H - Real.sqrt 3 / 2)) * I := by
  rw [fdBoundary_H_seg3 H (by linarith) (by linarith) (by linarith) ht4]
  simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk]
  push_cast; ring

private lemma g_rho'_seg4_value {t : ℝ} (ht4 : 4 < t) :
    fdBoundaryH H t - ellipticPointRhoPlusOne =
    ↑(t - 5) + ↑(H - Real.sqrt 3 / 2) * I := by
  rw [fdBoundary_H_seg4 H (by linarith) (by linarith) (by linarith) (by linarith)]
  simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk]
  push_cast; ring

private lemma sin_ge_sqrt3_div_2_of_mem {θ : ℝ}
    (hlo : Real.pi / 3 ≤ θ) (hhi : θ ≤ 2 * Real.pi / 3) :
    Real.sqrt 3 / 2 ≤ Real.sin θ := by
  rw [← Real.sin_pi_div_three]
  by_cases h : θ ≤ Real.pi / 2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [Real.pi_pos]) h hlo
  · push Not at h
    rw [show θ = Real.pi - (Real.pi - θ) from by ring, Real.sin_pi_sub]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two
      (by nlinarith [Real.pi_pos]) (by nlinarith) (by nlinarith)

private lemma sin_gt_sqrt3_div_2_of_mem {θ : ℝ}
    (hlo : Real.pi / 3 < θ) (hhi : θ < 2 * Real.pi / 3) :
    Real.sqrt 3 / 2 < Real.sin θ := by
  rw [← Real.sin_pi_div_three]
  by_cases h : θ ≤ Real.pi / 2
  · exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by nlinarith [Real.pi_pos]) h hlo
  · push Not at h
    rw [show θ = Real.pi - (Real.pi - θ) from by ring, Real.sin_pi_sub]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (by nlinarith [Real.pi_pos]) (by nlinarith) (by nlinarith)

private lemma g_rho'_im_nonneg (hH : Real.sqrt 3 / 2 < H)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 5) (hne : t ≠ 1) :
    0 ≤ (fdBoundaryH H t - ellipticPointRhoPlusOne).im := by
  rcases le_or_gt t 1 with h1 | h1
  · have ht1 : t < 1 := lt_of_le_of_ne h1 hne
    rw [g_rho'_seg0_value h1, mul_comm, Complex.I_mul_im, Complex.ofReal_re]
    exact mul_nonneg (by linarith) (by linarith)
  · rcases lt_or_ge t 3 with h3 | h3
    · rw [g_rho'_arc_value h1 h3]
      have hre_zero : (↑(Real.pi * (1 + t) / 6) * I : ℂ).re = 0 := by
        simp [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
      simp only [sub_im, Complex.exp_im, hre_zero, Real.exp_zero, one_mul,
        add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, mul_zero, add_zero, mul_one]
      have h_sin_ge : Real.sqrt 3 / 2 ≤ Real.sin (Real.pi * (1 + t) / 6) :=
        sin_ge_sqrt3_div_2_of_mem (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
      linarith
    · rcases eq_or_lt_of_le h3 with rfl | h3'
      · rw [fdBoundary_H_at_three_eq_rho]
        simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne',
          ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk,
          sub_im, add_im, neg_im, one_im, div_ofNat_im, mul_im, ofReal_im, I_re,
          I_im, mul_zero, add_zero, mul_one, zero_div]
        ring_nf; norm_num
      · rcases le_or_gt t 4 with h4 | h4
        · rw [g_rho'_seg3_value h3' h4]
          have : (-1 + ↑((t - 3) * (H - Real.sqrt 3 / 2)) * I : ℂ).im =
              (t - 3) * (H - Real.sqrt 3 / 2) := by
            simp [Complex.add_im, Complex.neg_im, Complex.one_im, Complex.mul_im,
              Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]
          rw [this]; exact mul_nonneg (by linarith) (by linarith)
        · rw [g_rho'_seg4_value h4]
          have : (↑(t - 5) + ↑(H - Real.sqrt 3 / 2) * I : ℂ).im =
              H - Real.sqrt 3 / 2 := by
            simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
              Complex.I_re, Complex.I_im, Complex.ofReal_re]
          rw [this]; linarith

private lemma g_rho'_ne_zero (hH : Real.sqrt 3 / 2 < H)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 5) (hne : t ≠ 1) :
    fdBoundaryH H t - ellipticPointRhoPlusOne ≠ 0 := by
  intro h_eq
  rcases le_or_gt t 1 with h1 | h1
  · have ht1 : t < 1 := lt_of_le_of_ne h1 hne
    have h_val := g_rho'_seg0_value (H := H) h1
    rw [h_eq] at h_val
    have : ((1 - t) * (H - Real.sqrt 3 / 2)) ≠ 0 := mul_ne_zero (by linarith) (by linarith)
    exact this (by simpa [Complex.ext_iff, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] using h_val)
  · rcases lt_or_ge t 3 with h3 | h3
    · have hre_zero : (↑(Real.pi * (1 + t) / 6) * I : ℂ).re = 0 := by
        simp [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
      have him_pos : 0 < (fdBoundaryH H t - ellipticPointRhoPlusOne).im := by
        rw [g_rho'_arc_value h1 h3]
        simp only [sub_im, Complex.exp_im, hre_zero, Real.exp_zero, one_mul,
          add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, mul_zero, add_zero, mul_one]
        have : Real.sqrt 3 / 2 < Real.sin (Real.pi * (1 + t) / 6) :=
          sin_gt_sqrt3_div_2_of_mem (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
        linarith
      rw [h_eq] at him_pos; simp only [Complex.zero_im, lt_irrefl] at him_pos
    · rcases eq_or_lt_of_le h3 with rfl | h3'
      · rw [fdBoundary_H_at_three_eq_rho] at h_eq
        simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne',
          ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk] at h_eq
        have : (-1/2 + ↑(Real.sqrt 3) / 2 * I - (1/2 + ↑(Real.sqrt 3) / 2 * I) : ℂ) = -1 := by
          ring
        rw [this] at h_eq; exact absurd h_eq (by norm_num)
      · rcases le_or_gt t 4 with h4 | h4
        · rw [g_rho'_seg3_value h3' h4] at h_eq
          have hre : (-1 + ↑((t - 3) * (H - Real.sqrt 3 / 2)) * I : ℂ).re = -1 := by
            simp [Complex.add_re, Complex.neg_re, Complex.one_re, Complex.mul_re,
              Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
          rw [h_eq] at hre
          simp only [Complex.zero_re] at hre
          norm_num at hre
        · rw [g_rho'_seg4_value h4] at h_eq
          have him : (↑(t - 5) + ↑(H - Real.sqrt 3 / 2) * I : ℂ).im =
              H - Real.sqrt 3 / 2 := by
            simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
              Complex.I_im, Complex.ofReal_re]
          rw [h_eq] at him; simp only [Complex.zero_im] at him; linarith

private lemma g_rho'_slitPlane (hH : Real.sqrt 3 / 2 < H)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 5) (hne1 : t ≠ 1) (hne3 : t ≠ 3) :
    fdBoundaryH H t - ellipticPointRhoPlusOne ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]; right
  rcases le_or_gt t 1 with h1 | h1
  · have ht1 : t < 1 := lt_of_le_of_ne h1 hne1
    rw [g_rho'_seg0_value h1, mul_comm, Complex.I_mul_im, Complex.ofReal_re]
    exact ne_of_gt (mul_pos (by linarith) (by linarith))
  · rcases lt_or_ge t 3 with h3 | h3
    · rw [g_rho'_arc_value h1 h3]
      have hre_zero : (↑(Real.pi * (1 + t) / 6) * I : ℂ).re = 0 := by
        simp [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
      simp only [sub_im, Complex.exp_im, hre_zero, Real.exp_zero, one_mul,
        add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, mul_zero, add_zero, mul_one]
      have h_sin_gt : Real.sqrt 3 / 2 < Real.sin (Real.pi * (1 + t) / 6) :=
        sin_gt_sqrt3_div_2_of_mem (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
      exact ne_of_gt (by linarith)
    · rcases eq_or_lt_of_le h3 with rfl | h3'
      · exact absurd rfl hne3
      · rcases le_or_gt t 4 with h4 | h4
        · rw [g_rho'_seg3_value h3' h4]
          have : (-1 + ↑((t - 3) * (H - Real.sqrt 3 / 2)) * I : ℂ).im =
              (t - 3) * (H - Real.sqrt 3 / 2) := by
            simp [Complex.add_im, Complex.neg_im, Complex.one_im, Complex.mul_im,
              Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]
          rw [this]; exact ne_of_gt (mul_pos (by linarith) (by linarith))
        · rw [g_rho'_seg4_value h4]
          have : (↑(t - 5) + ↑(H - Real.sqrt 3 / 2) * I : ℂ).im = H - Real.sqrt 3 / 2 := by
            simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
              Complex.I_re, Complex.I_im, Complex.ofReal_re]
          rw [this]; exact ne_of_gt (by linarith)

private theorem arg_approach_rho'_left (hH : Real.sqrt 3 / 2 < H)
    {δ : ℝ} (hδ : 0 < δ) (_hδ1 : δ ≤ 1) :
    (fdBoundaryH H (1 - δ) - ellipticPointRhoPlusOne).arg = Real.pi / 2 := by
  rw [g_rho'_seg0_value (by linarith : 1 - δ ≤ 1), show (1 - (1 - δ)) = δ from by ring,
    Complex.arg_eq_pi_div_two_iff]
  constructor
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
    ring
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re]
    nlinarith

private lemma g_rho'_norm_seg0_at (hH : Real.sqrt 3 / 2 < H)
    {δ : ℝ} (hδ : 0 < δ) (_hδ1 : δ ≤ 1) :
    ‖fdBoundaryH H (1 - δ) - ellipticPointRhoPlusOne‖ = δ * (H - Real.sqrt 3 / 2) := by
  rw [g_rho'_seg0_value (by linarith : 1 - δ ≤ 1), show (1 - (1 - δ)) = δ from by ring,
    norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_of_nonneg (mul_nonneg (le_of_lt hδ) (by linarith))]

private lemma arg_approach_rho'_right_helper (hδ : 0 < δ) (hδ_small : δ < 2) :
    (fdBoundaryH H (1 + δ) - ellipticPointRhoPlusOne).arg =
      5 * Real.pi / 6 + δ * Real.pi / 12 := by
  have h1 : 1 < 1 + δ := by linarith
  have h3 : 1 + δ < 3 := by linarith
  rw [g_rho'_arc_value h1 h3]
  set θ : ℝ := Real.pi * (1 + (1 + δ)) / 6 with hθ_def
  have hθ_eq : θ = Real.pi / 3 + δ * Real.pi / 6 := by simp only [hθ_def]; ring
  rw [show (↑(Real.pi * (1 + (1 + δ)) / 6) : ℂ) * I = (↑θ : ℂ) * I from rfl,
    exp_real_angle_I]
  have h_cos_sub : Real.cos θ - 1 / 2 =
      -2 * Real.sin (δ * Real.pi / 12) * Real.sin (Real.pi / 3 + δ * Real.pi / 12) := by
    have h := Real.cos_sub_cos θ (Real.pi / 3)
    rw [show (θ + Real.pi / 3) / 2 = Real.pi / 3 + δ * Real.pi / 12 from by rw [hθ_eq]; ring,
        show (θ - Real.pi / 3) / 2 = δ * Real.pi / 12 from by rw [hθ_eq]; ring] at h
    linarith [Real.cos_pi_div_three]
  have h_sin_sub : Real.sin θ - Real.sqrt 3 / 2 =
      2 * Real.sin (δ * Real.pi / 12) * Real.cos (Real.pi / 3 + δ * Real.pi / 12) := by
    have h := Real.sin_sub_sin θ (Real.pi / 3)
    rw [show (θ - Real.pi / 3) / 2 = δ * Real.pi / 12 from by rw [hθ_eq]; ring,
        show (θ + Real.pi / 3) / 2 =
          Real.pi / 3 + δ * Real.pi / 12 from by rw [hθ_eq]; ring] at h
    linarith [Real.sin_pi_div_three]
  set φ := Real.pi / 3 + δ * Real.pi / 12 with hφ_def
  have h_neg_sin_eq : -Real.sin φ = Real.cos (5 * Real.pi / 6 + δ * Real.pi / 12) := by
    rw [show 5 * Real.pi / 6 + δ * Real.pi / 12 = Real.pi / 2 + φ from by rw [hφ_def]; ring,
      Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have h_cos_eq : Real.cos φ = Real.sin (5 * Real.pi / 6 + δ * Real.pi / 12) := by
    rw [show 5 * Real.pi / 6 + δ * Real.pi / 12 = Real.pi / 2 + φ from by rw [hφ_def]; ring,
      Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  have h_eq : ↑(Real.cos θ) + ↑(Real.sin θ) * I - (↑(1/2 : ℝ) + ↑(Real.sqrt 3 / 2) * I) =
      ↑(2 * Real.sin (δ * Real.pi / 12)) * (↑(Real.cos (5 * Real.pi / 6 + δ * Real.pi / 12)) +
         ↑(Real.sin (5 * Real.pi / 6 + δ * Real.pi / 12)) * I) := by
    rw [← h_neg_sin_eq, ← h_cos_eq]
    apply Complex.ext
    · simp only [add_re, sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero, mul_one]; linarith [h_cos_sub]
    · simp only [add_im, sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, add_zero, mul_one]; linarith [h_sin_sub]
  rw [h_eq]
  have h_sin_pos : 0 < Real.sin (δ * Real.pi / 12) :=
    ArcCalculus.sin_pos_of_mem_Ioo_zero_pi (by constructor <;> nlinarith [Real.pi_pos])
  have h_angle_lt_pi : 5 * Real.pi / 6 + δ * Real.pi / 12 < Real.pi := by
    nlinarith [Real.pi_pos, mul_pos (show (0 : ℝ) < 2 - δ by linarith) Real.pi_pos]
  simp only [Complex.ofReal_cos, Complex.ofReal_sin]
  exact Complex.arg_mul_cos_add_sin_mul_I (mul_pos (by norm_num : (0 : ℝ) < 2) h_sin_pos)
    ⟨by linarith [show (0 : ℝ) < 5 * Real.pi / 6 + δ * Real.pi / 12 from by positivity],
     le_of_lt h_angle_lt_pi⟩

private lemma g_rho'_norm_arc {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ < 2) :
    ‖fdBoundaryH H (1 + δ) - ellipticPointRhoPlusOne‖ = 2 * Real.sin (δ * Real.pi / 12) := by
  have h1 : 1 < 1 + δ := by linarith
  have h3 : 1 + δ < 3 := by linarith
  rw [g_rho'_arc_value h1 h3]
  set θ : ℝ := Real.pi * (1 + (1 + δ)) / 6
  set φ := Real.pi / 3 + δ * Real.pi / 12
  have hθ_eq : θ = Real.pi / 3 + δ * Real.pi / 6 := by simp only [θ]; ring
  have h_cos_sub : Real.cos θ - 1 / 2 =
      -2 * Real.sin (δ * Real.pi / 12) * Real.sin φ := by
    have h := Real.cos_sub_cos θ (Real.pi / 3)
    rw [show (θ + Real.pi / 3) / 2 = φ from by simp only [φ, hθ_eq]; ring,
        show (θ - Real.pi / 3) / 2 = δ * Real.pi / 12 from by rw [hθ_eq]; ring] at h
    linarith [Real.cos_pi_div_three]
  have h_sin_sub : Real.sin θ - Real.sqrt 3 / 2 =
      2 * Real.sin (δ * Real.pi / 12) * Real.cos φ := by
    have h := Real.sin_sub_sin θ (Real.pi / 3)
    rw [show (θ - Real.pi / 3) / 2 = δ * Real.pi / 12 from by rw [hθ_eq]; ring,
        show (θ + Real.pi / 3) / 2 = φ from by simp only [φ, hθ_eq]; ring] at h
    linarith [Real.sin_pi_div_three]
  have h_neg_sin_eq : -Real.sin φ = Real.cos (5 * Real.pi / 6 + δ * Real.pi / 12) := by
    rw [show 5 * Real.pi / 6 + δ * Real.pi / 12 = Real.pi / 2 + φ from by simp only [φ]; ring,
      Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have h_cos_eq : Real.cos φ = Real.sin (5 * Real.pi / 6 + δ * Real.pi / 12) := by
    rw [show 5 * Real.pi / 6 + δ * Real.pi / 12 = Real.pi / 2 + φ from by simp only [φ]; ring,
      Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  have h_eq : ↑(Real.cos θ) + ↑(Real.sin θ) * I - (↑(1/2 : ℝ) + ↑(Real.sqrt 3 / 2) * I) =
      ↑(2 * Real.sin (δ * Real.pi / 12)) * (↑(Real.cos (5 * Real.pi / 6 + δ * Real.pi / 12)) +
         ↑(Real.sin (5 * Real.pi / 6 + δ * Real.pi / 12)) * I) := by
    rw [← h_neg_sin_eq, ← h_cos_eq]
    apply Complex.ext
    · simp only [add_re, sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero, mul_one]; linarith [h_cos_sub]
    · simp only [add_im, sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, add_zero, mul_one]; linarith [h_sin_sub]
  rw [exp_real_angle_I, h_eq]
  have h_sin_nn : 0 ≤ Real.sin (δ * Real.pi / 12) :=
    le_of_lt (ArcCalculus.sin_pos_of_mem_Ioo_zero_pi (by constructor <;> nlinarith [Real.pi_pos]))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (by norm_num) h_sin_nn),
    show (↑(Real.cos (5 * Real.pi / 6 + δ * Real.pi / 12)) +
      ↑(Real.sin (5 * Real.pi / 6 + δ * Real.pi / 12)) * I) =
      Complex.exp (↑(5 * Real.pi / 6 + δ * Real.pi / 12) * I) from by rw [exp_real_angle_I],
    Complex.norm_exp_ofReal_mul_I, mul_one]

private lemma g_rho'_norm_arc_full {t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) :
    ‖fdBoundaryH H t - ellipticPointRhoPlusOne‖ = 2 * Real.sin ((t - 1) * Real.pi / 12) := by
  have hδ : 0 < t - 1 := by linarith
  have hδ2 : t - 1 < 2 := by linarith
  convert g_rho'_norm_arc (δ := t - 1) hδ hδ2 using 2 <;> ring_nf

private lemma g_rho'_norm_ge_seg4 (hH : Real.sqrt 3 / 2 < H)
    {t : ℝ} (ht4 : 4 ≤ t) (ht5 : t ≤ 5) :
    H - Real.sqrt 3 / 2 ≤ ‖fdBoundaryH H t - ellipticPointRhoPlusOne‖ := by
  have him : (fdBoundaryH H t - (ellipticPointRhoPlusOne : ℂ)).im = H - Real.sqrt 3 / 2 := by
    rcases eq_or_lt_of_le ht4 with rfl | ht4'
    · have : fdBoundaryH H 4 - (ellipticPointRhoPlusOne : ℂ) =
          -1 + ↑(H - Real.sqrt 3 / 2) * I := by
        rw [fdBoundary_H_at_four]
        simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk]
        push_cast; ring
      rw [this, Complex.add_im, Complex.neg_im, Complex.one_im, mul_comm,
        Complex.I_mul_im, Complex.ofReal_re]; ring
    · rw [g_rho'_seg4_value ht4']
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, mul_zero, zero_add, add_zero, mul_one]
  calc H - Real.sqrt 3 / 2 = |(H - Real.sqrt 3 / 2 : ℝ)| := (abs_of_pos (by linarith)).symm
    _ = |(fdBoundaryH H t - (ellipticPointRhoPlusOne : ℂ)).im| := by rw [him]
    _ ≤ ‖fdBoundaryH H t - (ellipticPointRhoPlusOne : ℂ)‖ := Complex.abs_im_le_norm _

private lemma g_rho'_norm_ge_one_seg3 {t : ℝ} (ht3 : 3 ≤ t) (ht4 : t ≤ 4) :
    1 ≤ ‖fdBoundaryH H t - ellipticPointRhoPlusOne‖ := by
  rcases eq_or_lt_of_le ht3 with rfl | ht3'
  · rw [fdBoundary_H_at_three_eq_rho]
    simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne',
      ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
    have : (-1/2 + ↑(Real.sqrt 3) / 2 * I - (1/2 + ↑(Real.sqrt 3) / 2 * I) : ℂ) = -1 := by
      ring
    rw [this, norm_neg, norm_one]
  · have hre : (fdBoundaryH H t - (ellipticPointRhoPlusOne : ℂ)).re = -1 := by
      rw [g_rho'_seg3_value (H := H) ht3' ht4]
      simp [Complex.add_re, Complex.neg_re, Complex.one_re, Complex.mul_re,
        Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
    calc 1 = |(-1 : ℝ)| := by norm_num
      _ = |(fdBoundaryH H t - (ellipticPointRhoPlusOne : ℂ)).re| := by rw [hre]
      _ ≤ ‖fdBoundaryH H t - (ellipticPointRhoPlusOne : ℂ)‖ := Complex.abs_re_le_norm _

private lemma hasDerivAt_rho'_seg0 (H : ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (↑((1 - s) * (H - Real.sqrt 3 / 2)) : ℂ) * I)
      (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
  have := ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul_const
    (H - Real.sqrt 3 / 2) |>.ofReal_comp.mul_const I
  exact this.congr_deriv (by push_cast; ring)

private lemma hasDerivAt_rho'_arc (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (↑(Real.pi * (1 + s) / 6) * I) - ellipticPointRhoPlusOne)
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I)) t := by
  have hf : HasDerivAt (fun s : ℝ => Real.pi * (1 + s) / 6) (Real.pi / 6) t :=
    ((hasDerivAt_id t).add_const (1 : ℝ) |>.const_mul (Real.pi / 6)).congr_of_eventuallyEq
      (Eventually.of_forall fun s => show _ from by simp [id]; ring)
      |>.congr_deriv (by ring)
  have hci : HasDerivAt (fun s : ℝ => (↑(Real.pi * (1 + s) / 6) : ℂ) * I)
      ((↑(Real.pi / 6) : ℂ) * I) t :=
    (hf.ofReal_comp.mul_const I).congr_deriv (by norm_num [smul_eq_mul])
  exact (hci.cexp.sub (hasDerivAt_const t (ellipticPointRhoPlusOne : ℂ))).congr_deriv
    (by simp only [sub_zero]; ring)

private lemma hasDerivAt_rho'_seg3 (H : ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => -1 + ↑((s - 3) * (H - Real.sqrt 3 / 2)) * I)
      ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) t :=
  ((hasDerivAt_const t (-1 : ℂ)).add
    ((((hasDerivAt_id t).sub (hasDerivAt_const t 3)).mul_const
    (H - Real.sqrt 3 / 2)).ofReal_comp.mul_const I)).congr_deriv (by simp [zero_add])

private lemma hasDerivAt_rho'_seg4 (H : ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ↑(s - 5) + ↑(H - Real.sqrt 3 / 2) * I) (1 : ℂ) t := by
  have key := (((hasDerivAt_id t).sub (hasDerivAt_const t (5 : ℝ))).ofReal_comp.add
    (hasDerivAt_const t (↑(H - Real.sqrt 3 / 2) * I)))
  exact key.congr_deriv (by simp [sub_zero])

private lemma ftc_logDeriv_telescope_rho_plus_one (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {δ_L δ_R : ℝ} (hδ_L : 0 < δ_L) (hδ_L1 : δ_L < 1) (hδ_R : 0 < δ_R) (hδ_R1 : δ_R < 1) :
    let g := fun t => fdBoundaryH H t - (ellipticPointRhoPlusOne : ℂ)
    IntervalIntegrable (fun t => deriv g t / g t) volume 0 (1 - δ_L) ∧
    IntervalIntegrable (fun t => deriv g t / g t) volume (1 + δ_R) 5 ∧
    ((∫ t in (0 : ℝ)..(1 - δ_L), deriv g t / g t) + (∫ t in (1 + δ_R)..(5 : ℝ), deriv g t / g t) =
    Complex.log (g (1 - δ_L)) - Complex.log (g (1 + δ_R))) := by
  intro g
  set ρ' : ℂ := ellipticPointRhoPlusOne with hρ'_def
  set h₀ : ℝ → ℂ := fun t => ↑((1 - t) * (H - Real.sqrt 3 / 2)) * I
  set h₁ : ℝ → ℂ := fun t => exp (↑(Real.pi * (1 + t) / 6) * I) - ρ'
  set h₂ : ℝ → ℂ := fun t => -1 + ↑((t - 3) * (H - Real.sqrt 3 / 2)) * I
  set h₃ : ℝ → ℂ := fun t => ↑(t - 5) + ↑(H - Real.sqrt 3 / 2) * I
  have hg_eq_h₀ : ∀ t, t ≤ 1 → g t = h₀ t := by
    intro t ht; change fdBoundaryH H t - ρ' = h₀ t
    rw [g_rho'_seg0_value ht]
  have hg_eq_h₁ : ∀ t, 1 < t → t < 3 → g t = h₁ t := by
    intro t ht1 ht3; change fdBoundaryH H t - ρ' = h₁ t
    rw [g_rho'_arc_value ht1 ht3]
    simp only [h₁, hρ'_def, ellipticPointRhoPlusOne, ellipticPointRhoPlusOne',
      UpperHalfPlane.coe_mk]
    push_cast; ring
  have hg_eq_h₂ : ∀ t, 3 < t → t ≤ 4 → g t = h₂ t := by
    intro t ht3 ht4; change fdBoundaryH H t - ρ' = h₂ t
    rw [g_rho'_seg3_value ht3 ht4]
  have hg_eq_h₃ : ∀ t, 4 < t → g t = h₃ t := by
    intro t ht4; change fdBoundaryH H t - ρ' = h₃ t
    rw [g_rho'_seg4_value ht4]
  have hg0 : g 0 = h₀ 0 := hg_eq_h₀ 0 (by norm_num)
  have hg1mδ : g (1 - δ_L) = h₀ (1 - δ_L) := hg_eq_h₀ (1 - δ_L) (by linarith)
  have hg1pδ : g (1 + δ_R) = h₁ (1 + δ_R) := hg_eq_h₁ (1 + δ_R) (by linarith) (by linarith)
  have hg3_1 : g 3 = h₁ 3 := by
    change fdBoundaryH H 3 - ρ' = h₁ 3
    rw [fdBoundary_H_at_three_eq_rho]
    simp only [h₁, hρ'_def, ellipticPointRhoPlusOne, ellipticPointRhoPlusOne',
      ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
    rw [show Real.pi * (1 + 3) / 6 = 2 * Real.pi / 3 from by ring]
    rw [exp_real_angle_I, cos_two_pi_div_three, sin_two_pi_div_three]
    push_cast; ring
  have hg3_2 : g 3 = h₂ 3 := by
    change fdBoundaryH H 3 - ρ' = h₂ 3
    rw [fdBoundary_H_at_three_eq_rho]
    simp only [h₂, hρ'_def, ellipticPointRhoPlusOne, ellipticPointRhoPlusOne',
      ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
    push_cast; ring
  have hg4_2 : g 4 = h₂ 4 := hg_eq_h₂ 4 (by linarith) (le_refl 4)
  have hg4_3 : g 4 = h₃ 4 := by
    change fdBoundaryH H 4 - ρ' = h₃ 4
    rw [fdBoundary_H_at_four H]
    simp only [hρ'_def, ellipticPointRhoPlusOne, ellipticPointRhoPlusOne',
      UpperHalfPlane.coe_mk, h₃]
    push_cast; ring
  have hg5 : g 5 = h₃ 5 := hg_eq_h₃ 5 (by norm_num)
  have hd_h₀ : ∀ t : ℝ, HasDerivAt h₀ (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) t :=
    hasDerivAt_rho'_seg0 H
  have hd_h₁ : ∀ t : ℝ, HasDerivAt h₁
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I)) t :=
    hasDerivAt_rho'_arc
  have hd_h₂ : ∀ t : ℝ, HasDerivAt h₂ ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) t :=
    hasDerivAt_rho'_seg3 H
  have hd_h₃ : ∀ t : ℝ, HasDerivAt h₃ 1 t :=
    hasDerivAt_rho'_seg4 H
  have heq_0_1mδ : ∀ t ∈ Ioo (0 : ℝ) (1 - δ_L),
      g t = h₀ t ∧ deriv g t = deriv h₀ t := by
    intro t ⟨_, ht1⟩
    refine ⟨hg_eq_h₀ t (by linarith), ?_⟩
    have heq : g =ᶠ[𝓝 t] h₀ :=
      Filter.eventually_of_mem (Iio_mem_nhds (show t < 1 by linarith))
        (fun s hs => hg_eq_h₀ s (le_of_lt hs))
    exact heq.deriv_eq
  have heq_1pδ_3 : ∀ t ∈ Ioo (1 + δ_R) (3 : ℝ),
      g t = h₁ t ∧ deriv g t = deriv h₁ t := by
    intro t ⟨ht1, ht3⟩
    refine ⟨hg_eq_h₁ t (by linarith) ht3, ?_⟩
    have heq : g =ᶠ[𝓝 t] h₁ :=
      Filter.eventually_of_mem (Ioo_mem_nhds (by linarith : 1 < t) ht3)
        (fun s hs => hg_eq_h₁ s hs.1 hs.2)
    exact heq.deriv_eq
  have heq_34 : ∀ t ∈ Ioo (3 : ℝ) 4, g t = h₂ t ∧ deriv g t = deriv h₂ t := by
    intro t ⟨ht3, ht4⟩
    refine ⟨hg_eq_h₂ t ht3 (le_of_lt ht4), ?_⟩
    have heq : g =ᶠ[𝓝 t] h₂ :=
      Filter.eventually_of_mem (Ioo_mem_nhds ht3 ht4) (fun s hs => hg_eq_h₂ s hs.1 (le_of_lt hs.2))
    exact heq.deriv_eq
  have heq_45 : ∀ t ∈ Ioo (4 : ℝ) 5, g t = h₃ t ∧ deriv g t = deriv h₃ t := by
    intro t ⟨ht4, _⟩
    refine ⟨hg_eq_h₃ t ht4, ?_⟩
    have heq : g =ᶠ[𝓝 t] h₃ :=
      Filter.eventually_of_mem (Ioi_mem_nhds ht4) (fun s hs => hg_eq_h₃ s hs)
    exact heq.deriv_eq
  have hh₀_cont : ContinuousOn h₀ (Icc 0 (1 - δ_L)) :=
    fun t _ => (hd_h₀ t).continuousAt.continuousWithinAt
  have hh₁_cont : ContinuousOn h₁ (Icc (1 + δ_R) 3) :=
    fun t _ => (hd_h₁ t).continuousAt.continuousWithinAt
  have hh₂_cont : ContinuousOn h₂ (Icc 3 4) :=
    fun t _ => (hd_h₂ t).continuousAt.continuousWithinAt
  have hh₃_cont : ContinuousOn h₃ (Icc 4 5) :=
    fun t _ => (hd_h₃ t).continuousAt.continuousWithinAt
  have hh₀_diff : ∀ t ∈ Ioo (0 : ℝ) (1 - δ_L), DifferentiableAt ℝ h₀ t :=
    fun t _ => (hd_h₀ t).differentiableAt
  have hh₁_diff : ∀ t ∈ Ioo (1 + δ_R) (3 : ℝ), DifferentiableAt ℝ h₁ t :=
    fun t _ => (hd_h₁ t).differentiableAt
  have hh₂_diff : ∀ t ∈ Ioo (3 : ℝ) 4, DifferentiableAt ℝ h₂ t :=
    fun t _ => (hd_h₂ t).differentiableAt
  have hh₃_diff : ∀ t ∈ Ioo (4 : ℝ) 5, DifferentiableAt ℝ h₃ t :=
    fun t _ => (hd_h₃ t).differentiableAt
  have hh₀_deriv_cont : ContinuousOn (deriv h₀) (Icc 0 (1 - δ_L)) := by
    rw [show deriv h₀ = fun _ => -(↑(H - Real.sqrt 3 / 2) : ℂ) * I from
      funext fun t => (hd_h₀ t).deriv]; exact continuousOn_const
  have hh₁_deriv_cont : ContinuousOn (deriv h₁) (Icc (1 + δ_R) 3) := by
    rw [show deriv h₁ = fun t => ↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I) from
      funext fun t => (hd_h₁ t).deriv]
    exact (Continuous.mul continuous_const (Continuous.cexp (Continuous.mul
      (continuous_ofReal.comp (by fun_prop : Continuous fun s => Real.pi * (1 + s) / 6))
      continuous_const))).continuousOn
  have hh₂_deriv_cont : ContinuousOn (deriv h₂) (Icc 3 4) := by
    rw [show deriv h₂ = fun _ => (↑(H - Real.sqrt 3 / 2) : ℂ) * I from
      funext fun t => (hd_h₂ t).deriv]; exact continuousOn_const
  have hh₃_deriv_cont : ContinuousOn (deriv h₃) (Icc 4 5) := by
    rw [show deriv h₃ = fun _ => (1 : ℂ) from
      funext fun t => (hd_h₃ t).deriv]; exact continuousOn_const
  have hh₀_slit : ∀ t ∈ Icc (0 : ℝ) (1 - δ_L), h₀ t ∈ slitPlane := by
    intro t ⟨ht0, ht1⟩
    rw [← hg_eq_h₀ t (by linarith)]
    exact g_rho'_slitPlane hH ⟨ht0, by linarith⟩ (by linarith) (by linarith)
  have piece₀ := ftc_log_piece (by linarith : (0 : ℝ) ≤ 1 - δ_L) hh₀_cont hh₀_diff
    hh₀_deriv_cont hh₀_slit heq_0_1mδ hg0 hg1mδ
  have hh₁_im_nn : ∀ t ∈ Icc (1 + δ_R) (3 : ℝ), 0 ≤ (h₁ t).im := by
    intro t ⟨ht1, ht3⟩
    rw [← show g t = h₁ t from by
      rcases eq_or_lt_of_le ht3 with rfl | ht3'
      · exact hg3_1
      · exact hg_eq_h₁ t (by linarith) ht3']
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · exact g_rho'_im_nonneg hH ⟨by norm_num, by norm_num⟩ (by norm_num)
    · exact g_rho'_im_nonneg hH ⟨by linarith, by linarith⟩ (by linarith)
  have hh₁_ne : ∀ t ∈ Icc (1 + δ_R) (3 : ℝ), h₁ t ≠ 0 := by
    intro t ⟨ht1, ht3⟩
    rw [← show g t = h₁ t from by
      rcases eq_or_lt_of_le ht3 with rfl | ht3'
      · exact hg3_1
      · exact hg_eq_h₁ t (by linarith) ht3']
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · exact g_rho'_ne_zero hH ⟨by norm_num, by norm_num⟩ (by norm_num)
    · exact g_rho'_ne_zero hH ⟨by linarith, by linarith⟩ (by linarith)
  have hh₁_slit_interior : ∀ t ∈ Ioo (1 + δ_R) (3 : ℝ), h₁ t ∈ slitPlane := by
    intro t ⟨ht1, ht3⟩
    rw [← hg_eq_h₁ t (by linarith) ht3]
    exact g_rho'_slitPlane hH ⟨by linarith, by linarith⟩ (by linarith) (by linarith)
  have piece₁ := ftc_log_piece_upper (by linarith : (1 + δ_R) ≤ 3) hh₁_cont hh₁_diff
    hh₁_deriv_cont hh₁_im_nn hh₁_ne hh₁_slit_interior
    heq_1pδ_3 hg1pδ (hg3_2.symm ▸ hg3_1)
  have hh₂_im_nn : ∀ t ∈ Icc (3 : ℝ) 4, 0 ≤ (h₂ t).im := by
    intro t ⟨ht3, ht4⟩
    rw [← show g t = h₂ t from by
      rcases eq_or_lt_of_le ht3 with rfl | ht3'
      · exact hg3_2
      · exact hg_eq_h₂ t ht3' ht4]
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · exact g_rho'_im_nonneg hH ⟨by norm_num, by norm_num⟩ (by norm_num)
    · exact g_rho'_im_nonneg hH ⟨by linarith, by linarith⟩ (by linarith)
  have hh₂_ne : ∀ t ∈ Icc (3 : ℝ) 4, h₂ t ≠ 0 := by
    intro t ⟨ht3, ht4⟩
    rw [← show g t = h₂ t from by
      rcases eq_or_lt_of_le ht3 with rfl | ht3'
      · exact hg3_2
      · exact hg_eq_h₂ t ht3' ht4]
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · exact g_rho'_ne_zero hH ⟨by norm_num, by norm_num⟩ (by norm_num)
    · exact g_rho'_ne_zero hH ⟨by linarith, by linarith⟩ (by linarith)
  have hh₂_slit_interior : ∀ t ∈ Ioo (3 : ℝ) 4, h₂ t ∈ slitPlane := by
    intro t ⟨ht3, ht4⟩
    rw [← hg_eq_h₂ t ht3 (le_of_lt ht4)]
    exact g_rho'_slitPlane hH ⟨by linarith, by linarith⟩ (by linarith) (by linarith)
  have piece₂ := ftc_log_piece_upper (by norm_num : (3 : ℝ) ≤ 4) hh₂_cont hh₂_diff
    hh₂_deriv_cont hh₂_im_nn hh₂_ne hh₂_slit_interior heq_34 hg3_2 (hg4_3.symm ▸ hg4_2)
  have hh₃_slit : ∀ t ∈ Icc (4 : ℝ) 5, h₃ t ∈ slitPlane := by
    intro t ⟨ht4, ht5⟩
    rcases eq_or_lt_of_le ht4 with rfl | ht4'
    · rw [← hg4_3]
      exact g_rho'_slitPlane hH ⟨by norm_num, by norm_num⟩ (by norm_num) (by norm_num)
    · rw [← hg_eq_h₃ t ht4']
      exact g_rho'_slitPlane hH ⟨by linarith, ht5⟩ (by linarith) (by linarith)
  have piece₃ := ftc_log_piece (by norm_num : (4 : ℝ) ≤ 5)
    hh₃_cont hh₃_diff hh₃_deriv_cont hh₃_slit heq_45 hg4_3 hg5
  refine ⟨piece₀.1, piece₁.1.trans (piece₂.1.trans piece₃.1), ?_⟩
  rw [(intervalIntegral.integral_add_adjacent_intervals piece₁.1
      (piece₂.1.trans piece₃.1)).symm,
    (intervalIntegral.integral_add_adjacent_intervals piece₂.1 piece₃.1).symm,
    piece₀.2, piece₁.2, piece₂.2, piece₃.2]
  have hg_closed : g 0 = g 5 := by
    change fdBoundaryH H 0 - ρ' = fdBoundaryH H 5 - ρ'
    rw [fdBoundary_H_closed H]
  rw [hg_closed]
  ring

private lemma norm_le_middle_rho_plus_one (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {ε δ_L δ_R : ℝ} (hε : 0 < ε)
    (hδ_L_pos : 0 < δ_L) (hδ_L_lt_one : δ_L < 1)
    (hδ_R_pos : 0 < δ_R) (hδ_R_lt_one : δ_R < 1)
    (h_norm_L : ‖fdBoundaryH H (1 - δ_L) - ellipticPointRhoPlusOne‖ = ε)
    (h_norm_R : ‖fdBoundaryH H (1 + δ_R) - ellipticPointRhoPlusOne‖ = ε)
    (hH_gap : 0 < H - Real.sqrt 3 / 2) :
    ∀ t, 1 - δ_L ≤ t → t ≤ 1 + δ_R →
      ¬(‖fdBoundaryH H t - (ellipticPointRhoPlusOne : ℂ)‖ > ε) := by
  intro t ht_lo ht_hi
  push Not
  have hpi_pos := Real.pi_pos
  rcases le_or_gt t 1 with ht1 | ht1
  · rcases eq_or_lt_of_le ht1 with rfl | ht1'
    · simp only [fdBoundary_H_at_one_eq_rho_plus_one, sub_self, norm_zero]
      exact le_of_lt hε
    · rw [g_rho'_norm_seg0 hH (by linarith) ht1',
          ← h_norm_L, g_rho'_norm_seg0_at hH hδ_L_pos (le_of_lt hδ_L_lt_one)]
      exact mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hH_gap)
  · rw [g_rho'_norm_arc_full ht1 (by linarith : t < 3),
        ← h_norm_R, g_rho'_norm_arc hδ_R_pos (by linarith : δ_R < 2)]
    exact mul_le_mul_of_nonneg_left (Real.sin_le_sin_of_le_of_le_pi_div_two
        (by nlinarith) (by nlinarith) (by nlinarith [show t - 1 ≤ δ_R from by linarith]))
      (by norm_num)

private lemma rho'_norm_gt_right_of_arc (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {ε δ_R : ℝ} (hε_lt_one : ε < 1) (hε_lt_gap : ε < H - Real.sqrt 3 / 2)
    (hδ_R_pos : 0 < δ_R) (hδ_R_lt_one : δ_R < 1)
    (h_norm_R : ‖fdBoundaryH H (1 + δ_R) - ellipticPointRhoPlusOne‖ = ε) :
    ∀ t ∈ Ioo (1 + δ_R) (5 : ℝ),
      ‖fdBoundaryH H t - (ellipticPointRhoPlusOne : ℂ)‖ > ε := by
  intro t ⟨ht1, ht5⟩
  rcases le_or_gt t 3 with ht3 | ht3
  · rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · calc ε < 1 := hε_lt_one
        _ ≤ _ := g_rho'_norm_ge_one_seg3 (le_refl 3) (by norm_num)
    · rw [g_rho'_norm_arc_full (by linarith : 1 < t) ht3',
          ← h_norm_R, g_rho'_norm_arc hδ_R_pos (by linarith : δ_R < 2)]
      have hpi_pos := Real.pi_pos
      apply mul_lt_mul_of_pos_left _ (by norm_num : (0 : ℝ) < 2)
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (by nlinarith) (by nlinarith)
        (by nlinarith [show δ_R < t - 1 from by linarith])
  · rcases le_or_gt t 4 with ht4 | ht4
    · calc ε < 1 := hε_lt_one
        _ ≤ _ := g_rho'_norm_ge_one_seg3 (le_of_lt ht3) ht4
    · calc ε < H - Real.sqrt 3 / 2 := hε_lt_gap
        _ ≤ _ := g_rho'_norm_ge_seg4 hH (le_of_lt ht4) (le_of_lt ht5)

private lemma arc_angle_lt_epsilon {δ_R ε : ℝ} (hδ_R_pos : 0 < δ_R)
    (hδ_R_lt_one : δ_R < 1)
    (h_norm_R : ‖fdBoundaryH H (1 + δ_R) - (ellipticPointRhoPlusOne : ℂ)‖ = ε) :
    δ_R * Real.pi / 12 < ε := by
  have h_sin_eq : Real.sin (δ_R * Real.pi / 12) = ε / 2 := by
    linarith [h_norm_R ▸ g_rho'_norm_arc (H := H) hδ_R_pos (show δ_R < 2 by linarith)]
  set x := δ_R * Real.pi / 12 with hx_def
  have hx_pos : 0 < x := by positivity
  have hx_le_one : x ≤ 1 := by
    linarith [Real.pi_le_four, show x < Real.pi / 12 by rw [hx_def]; nlinarith]
  nlinarith [Real.sin_gt_sub_cube hx_pos hx_le_one, sq_nonneg x, sq_nonneg (1 - x)]

private lemma δ_right_lt_one_aux {ε : ℝ}
    (hε_half_neg : (-1 : ℝ) ≤ ε / 2)
    (hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12)) :
    12 / Real.pi * Real.arcsin (ε / 2) < 1 := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hε_lt_sin : ε / 2 < Real.sin (Real.pi / 12) := by linarith
  have harcsin_lt : Real.arcsin (ε / 2) < Real.pi / 12 :=
    calc Real.arcsin (ε / 2) < Real.arcsin (Real.sin (Real.pi / 12)) :=
            Real.arcsin_lt_arcsin hε_half_neg hε_lt_sin (Real.sin_le_one _)
        _ = Real.pi / 12 :=
            Real.arcsin_sin (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  calc 12 / Real.pi * Real.arcsin (ε / 2)
      < 12 / Real.pi * (Real.pi / 12) :=
        mul_lt_mul_of_pos_left harcsin_lt (div_pos (by norm_num) hpi_pos)
    _ = 1 := by field_simp [hpi_pos.ne']

/-- Bundles the recurring `δ_left`/`δ_right` positivity-and-smallness facts used throughout
the PV-integral proof at `ρ'`, given `0 < ε` below both gap thresholds. -/
private lemma rho'_delta_bounds {H ε : ℝ} (hH_gap : 0 < H - Real.sqrt 3 / 2)
    (hε_pos : 0 < ε) (hε_lt_gap : ε < H - Real.sqrt 3 / 2)
    (hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12)) :
    (-1 : ℝ) ≤ ε / 2 ∧ ε / 2 ≤ 1 ∧
    0 < ε / (H - Real.sqrt 3 / 2) ∧ ε / (H - Real.sqrt 3 / 2) < 1 ∧
    0 < 12 / Real.pi * Real.arcsin (ε / 2) ∧
    12 / Real.pi * Real.arcsin (ε / 2) < 1 := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hε_half_neg : (-1 : ℝ) ≤ ε / 2 := by linarith
  have hε_half_le : ε / 2 ≤ 1 := by linarith [Real.sin_le_one (Real.pi / 12)]
  refine ⟨hε_half_neg, hε_half_le, div_pos hε_pos hH_gap, ?_,
    mul_pos (div_pos (by norm_num) hpi_pos) (Real.arcsin_pos.mpr (by linarith)),
    δ_right_lt_one_aux hε_half_neg hε_lt_2sin⟩
  rw [div_lt_one hH_gap]; exact hε_lt_gap

private lemma inv_mul_deriv_eq_logDeriv_sub (H : ℝ) (c : ℂ) :
    (fun t => (fdBoundaryH H t - c)⁻¹ * deriv (fdBoundaryH H) t) =
    (fun t => deriv (fun s => fdBoundaryH H s - c) t / (fdBoundaryH H t - c)) := by
  funext t
  have : deriv (fun s => fdBoundaryH H s - c) t = deriv (fdBoundaryH H) t :=
    deriv_sub_const (f := fdBoundaryH H) c
  rw [this, div_eq_mul_inv, mul_comm]

/-- The PV integral of `(γ-ρ')⁻¹ γ'` over `[0,5]` with ε-ball cutoff tends to `-iπ/3`. -/
theorem pv_integral_at_rho_plus_one_tendsto (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    Tendsto (fun ε => ∫ t in (0 : ℝ)..5, if ‖fdBoundaryH H t - ellipticPointRhoPlusOne‖ > ε
      then (fdBoundaryH H t - ellipticPointRhoPlusOne)⁻¹ *
           deriv (fun s => fdBoundaryH H s - ellipticPointRhoPlusOne) t
      else 0) (𝓝[>] 0) (𝓝 (-(I * ↑Real.pi / 3))) := by
  have hH_gap : 0 < H - Real.sqrt 3 / 2 := by linarith
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hsin_pos : 0 < Real.sin (Real.pi / 12) :=
    ArcCalculus.sin_pos_of_mem_Ioo_zero_pi (by constructor <;> nlinarith [Real.pi_pos])
  have h2sin_pos : 0 < 2 * Real.sin (Real.pi / 12) := by positivity
  have hderiv_eq : ∀ t : ℝ, deriv (fun s => fdBoundaryH H s - (ellipticPointRhoPlusOne : ℂ)) t =
      deriv (fdBoundaryH H) t := fun t =>
    deriv_sub_const (f := fdBoundaryH H) _
  simp_rw [hderiv_eq]
  set threshold := min (H - Real.sqrt 3 / 2) (2 * Real.sin (Real.pi / 12)) with hthresh_def
  have hthresh_pos : 0 < threshold := lt_min hH_gap h2sin_pos
  set δ_left : ℝ → ℝ := fun ε => ε / (H - Real.sqrt 3 / 2) with hδL_def
  set δ_right : ℝ → ℝ := fun ε => 12 / Real.pi * Real.arcsin (ε / 2) with hδR_def
  set E : ℝ → ℂ := fun ε =>
    Complex.log (fdBoundaryH H (1 - δ_left ε) - ellipticPointRhoPlusOne) -
    Complex.log (fdBoundaryH H (1 + δ_right ε) - ellipticPointRhoPlusOne) with hE_def
  apply ContourIntegral.pv_tendsto_of_crossing_limit_asymmetric
      (γ := fdBoundaryH H) (s := ellipticPointRhoPlusOne) (a := 0) (b := 5) (t₀ := 1)
      (δ_left := δ_left) (δ_right := δ_right) (threshold := threshold) (E := E)
  · -- ht₀: (1 : ℝ) ∈ Ioo 0 5
    norm_num
  · -- hthresh
    exact hthresh_pos
  · -- hδL_pos: δ_left ε > 0 for 0 < ε < threshold
    intro ε hε_pos _; exact div_pos hε_pos hH_gap
  · -- hδR_pos: δ_right ε > 0 for 0 < ε < threshold
    intro ε hε_pos _
    simp only [hδR_def]
    exact mul_pos (div_pos (by norm_num) hpi_pos)
      (Real.arcsin_pos.mpr (by linarith))
  · -- hδL_small: δ_left ε < 1 - 0 = 1
    intro ε hε_pos hε_lt
    simp only [hδL_def]
    norm_num
    rw [div_lt_one hH_gap]
    exact lt_of_lt_of_le hε_lt (min_le_left _ _)
  · -- hδR_small: δ_right ε < 5 - 1 = 4
    intro ε hε_pos hε_lt
    simp only [hδR_def]
    have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) :=
      lt_of_lt_of_le hε_lt (min_le_right _ _)
    have hε_half_neg : (-1 : ℝ) ≤ ε / 2 := by linarith
    linarith [δ_right_lt_one_aux hε_half_neg hε_lt_2sin]
  · -- h_far_left: ε < ‖γ t - s‖ for t ∈ Ico 0 (1 - δ_left ε)
    intro ε hε_pos hε_lt t ht_mem
    simp only [hδL_def] at ht_mem
    have ht0 : (0 : ℝ) ≤ t := ht_mem.1
    have ht1 : t < 1 - ε / (H - Real.sqrt 3 / 2) := ht_mem.2
    have ht_lt_one : t < 1 := by linarith [div_pos hε_pos hH_gap]
    rw [g_rho'_norm_seg0 hH ht0 ht_lt_one]
    have h_key : ε / (H - Real.sqrt 3 / 2) < 1 - t := by linarith
    calc ε = ε / (H - Real.sqrt 3 / 2) * (H - Real.sqrt 3 / 2) :=
              (div_mul_cancel₀ ε (ne_of_gt hH_gap)).symm
        _ < (1 - t) * (H - Real.sqrt 3 / 2) := mul_lt_mul_of_pos_right h_key hH_gap
  · -- h_far_right: ε < ‖γ t - s‖ for t ∈ Ioc (1 + δ_right ε) 5
    intro ε hε_pos hε_lt t ht_mem
    have hε_lt_gap : ε < H - Real.sqrt 3 / 2 := lt_of_lt_of_le hε_lt (min_le_left _ _)
    have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) :=
      lt_of_lt_of_le hε_lt (min_le_right _ _)
    have hε_half_neg : (-1 : ℝ) ≤ ε / 2 := by linarith
    have hε_half_le : ε / 2 ≤ 1 := by linarith [Real.sin_le_one (Real.pi / 12)]
    have hε_lt_one : ε < 1 := by
      have hsin_bound : Real.sin (Real.pi / 12) < 1 / 2 :=
        calc Real.sin (Real.pi / 12) < Real.sin (Real.pi / 6) :=
              Real.sin_lt_sin_of_lt_of_le_pi_div_two (by nlinarith [Real.pi_pos])
                (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
          _ = 1 / 2 := by rw [Real.sin_pi_div_six]
      linarith
    simp only [hδR_def] at ht_mem
    have hδR_pos : 0 < δ_right ε := by
      simp only [hδR_def]
      exact mul_pos (div_pos (by norm_num) hpi_pos)
        (Real.arcsin_pos.mpr (by linarith))
    have hδR_lt_one : δ_right ε < 1 := by
      simp only [hδR_def]; exact δ_right_lt_one_aux hε_half_neg hε_lt_2sin
    have hδR_angle : δ_right ε * Real.pi / 12 = Real.arcsin (ε / 2) := by
      simp only [hδR_def]; field_simp
    have h_norm_R : ‖fdBoundaryH H (1 + δ_right ε) - ellipticPointRhoPlusOne‖ = ε := by
      rw [g_rho'_norm_arc hδR_pos (by linarith : δ_right ε < 2), hδR_angle,
          Real.sin_arcsin hε_half_neg hε_half_le]
      linarith
    have h_ioo := rho'_norm_gt_right_of_arc H hH hε_lt_one hε_lt_gap
      hδR_pos hδR_lt_one h_norm_R
    rcases eq_or_lt_of_le ht_mem.2 with rfl | ht_lt5
    · calc ε < H - Real.sqrt 3 / 2 := hε_lt_gap
        _ ≤ ‖fdBoundaryH H 5 - ellipticPointRhoPlusOne‖ :=
            g_rho'_norm_ge_seg4 hH (by norm_num) (le_refl 5)
    · exact h_ioo t ⟨ht_mem.1, ht_lt5⟩
  · -- h_near: ‖γ t - s‖ ≤ ε for t ∈ Icc (1 - δ_left ε) (1 + δ_right ε)
    intro ε hε_pos hε_lt t ht_mem
    have hε_lt_gap : ε < H - Real.sqrt 3 / 2 := lt_of_lt_of_le hε_lt (min_le_left _ _)
    have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) :=
      lt_of_lt_of_le hε_lt (min_le_right _ _)
    obtain ⟨hε_half_neg, hε_half_le, hδL_pos, hδL_lt_one, hδR_pos, hδR_lt_one⟩ :=
      rho'_delta_bounds hH_gap hε_pos hε_lt_gap hε_lt_2sin
    have hδR_angle : δ_right ε * Real.pi / 12 = Real.arcsin (ε / 2) := by
      simp only [hδR_def]; field_simp
    have h_norm_L : ‖fdBoundaryH H (1 - δ_left ε) - ellipticPointRhoPlusOne‖ = ε := by
      rw [g_rho'_norm_seg0_at hH hδL_pos (le_of_lt hδL_lt_one)]
      field_simp
      have : H * 2 - Real.sqrt 3 > 0 := by nlinarith
      exact div_self (ne_of_gt this)
    have h_norm_R : ‖fdBoundaryH H (1 + δ_right ε) - ellipticPointRhoPlusOne‖ = ε := by
      rw [g_rho'_norm_arc hδR_pos (by linarith : δ_right ε < 2), hδR_angle,
          Real.sin_arcsin hε_half_neg hε_half_le]
      linarith
    exact not_lt.mp (norm_le_middle_rho_plus_one H hH hε_pos hδL_pos hδL_lt_one
      hδR_pos hδR_lt_one h_norm_L h_norm_R hH_gap t ht_mem.1 ht_mem.2)
  · -- h_ftc: FTC gives the two-piece integral equals E ε
    intro ε hε_pos hε_lt
    have hε_lt_gap : ε < H - Real.sqrt 3 / 2 := lt_of_lt_of_le hε_lt (min_le_left _ _)
    have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) :=
      lt_of_lt_of_le hε_lt (min_le_right _ _)
    obtain ⟨_, _, hδL_pos, hδL_lt_one, hδR_pos, hδR_lt_one⟩ :=
      rho'_delta_bounds hH_gap hε_pos hε_lt_gap hε_lt_2sin
    obtain ⟨_, _, h_telescope⟩ := ftc_logDeriv_telescope_rho_plus_one H hH hδL_pos hδL_lt_one
      hδR_pos hδR_lt_one
    simp only [hE_def, hδL_def, hδR_def]
    simp_rw [inv_mul_deriv_eq_logDeriv_sub H ellipticPointRhoPlusOne]
    exact h_telescope
  · -- hint_left: integrable on [0, 1 - δ_left ε]
    intro ε hε_pos hε_lt
    have hε_lt_gap : ε < H - Real.sqrt 3 / 2 := lt_of_lt_of_le hε_lt (min_le_left _ _)
    have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) :=
      lt_of_lt_of_le hε_lt (min_le_right _ _)
    obtain ⟨_, _, hδL_pos, hδL_lt_one, hδR_pos, hδR_lt_one⟩ :=
      rho'_delta_bounds hH_gap hε_pos hε_lt_gap hε_lt_2sin
    obtain ⟨hint_L, _, _⟩ := ftc_logDeriv_telescope_rho_plus_one H hH hδL_pos hδL_lt_one
      hδR_pos hδR_lt_one
    rw [inv_mul_deriv_eq_logDeriv_sub H ellipticPointRhoPlusOne]
    exact hint_L
  · -- hint_right: integrable on [1 + δ_right ε, 5]
    intro ε hε_pos hε_lt
    have hε_lt_gap : ε < H - Real.sqrt 3 / 2 := lt_of_lt_of_le hε_lt (min_le_left _ _)
    have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) :=
      lt_of_lt_of_le hε_lt (min_le_right _ _)
    obtain ⟨_, _, hδL_pos, hδL_lt_one, hδR_pos, hδR_lt_one⟩ :=
      rho'_delta_bounds hH_gap hε_pos hε_lt_gap hε_lt_2sin
    obtain ⟨_, hint_R, _⟩ := ftc_logDeriv_telescope_rho_plus_one H hH hδL_pos hδL_lt_one
      hδR_pos hδR_lt_one
    rw [inv_mul_deriv_eq_logDeriv_sub H ellipticPointRhoPlusOne]
    exact hint_R
  · -- h_limit: E(ε) → -(I * π/3) as ε → 0⁺
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro r hr
    refine ⟨min threshold r, lt_min hthresh_pos hr, ?_⟩
    intro ε hε_mem hε_dist
    simp only [Set.mem_Ioi] at hε_mem
    rw [Real.dist_eq, sub_zero, abs_of_pos hε_mem] at hε_dist
    have hε_pos : 0 < ε := hε_mem
    have hε_lt : ε < threshold := lt_of_lt_of_le hε_dist (min_le_left _ _)
    have hε_lt_gap : ε < H - Real.sqrt 3 / 2 := lt_of_lt_of_le hε_lt (min_le_left _ _)
    have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) :=
      lt_of_lt_of_le hε_lt (min_le_right _ _)
    obtain ⟨hε_half_neg, hε_half_le, hδL_pos, hδL_lt_one, hδR_pos, hδR_lt_one⟩ :=
      rho'_delta_bounds hH_gap hε_pos hε_lt_gap hε_lt_2sin
    have hδR_angle : δ_right ε * Real.pi / 12 = Real.arcsin (ε / 2) := by
      simp only [hδR_def]; field_simp
    have h_norm_L : ‖fdBoundaryH H (1 - δ_left ε) - ellipticPointRhoPlusOne‖ = ε := by
      rw [g_rho'_norm_seg0_at hH hδL_pos (le_of_lt hδL_lt_one)]
      field_simp
      have : H * 2 - Real.sqrt 3 > 0 := by nlinarith
      exact div_self (ne_of_gt this)
    have h_norm_R : ‖fdBoundaryH H (1 + δ_right ε) - ellipticPointRhoPlusOne‖ = ε := by
      rw [g_rho'_norm_arc hδR_pos (by linarith : δ_right ε < 2), hδR_angle,
          Real.sin_arcsin hε_half_neg hε_half_le]
      linarith
    simp only [hE_def]
    rw [show dist (Complex.log (fdBoundaryH H (1 - δ_left ε) - ↑ellipticPointRhoPlusOne) -
          Complex.log (fdBoundaryH H (1 + δ_right ε) - ↑ellipticPointRhoPlusOne))
          (-(I * ↑Real.pi / 3)) =
        ‖Complex.log (fdBoundaryH H (1 - δ_left ε) - ↑ellipticPointRhoPlusOne) -
          Complex.log (fdBoundaryH H (1 + δ_right ε) - ↑ellipticPointRhoPlusOne) -
          (-(I * ↑Real.pi / 3))‖ from Complex.dist_eq _ _]
    set zL := fdBoundaryH H (1 - δ_left ε) - (ellipticPointRhoPlusOne : ℂ) with hzL_def
    set zR := fdBoundaryH H (1 + δ_right ε) - (ellipticPointRhoPlusOne : ℂ) with hzR_def
    have hzL_norm : ‖zL‖ = ε := by rw [hzL_def]; exact h_norm_L
    have hzR_norm : ‖zR‖ = ε := by rw [hzR_def]; exact h_norm_R
    have hzL_arg : zL.arg = Real.pi / 2 := by
      rw [hzL_def]
      exact arg_approach_rho'_left hH hδL_pos (le_of_lt hδL_lt_one)
    have hzR_arg : zR.arg = 5 * Real.pi / 6 + δ_right ε * Real.pi / 12 := by
      rw [hzR_def]
      exact arg_approach_rho'_right_helper hδR_pos (by linarith : δ_right ε < 2)
    have hlogL : Complex.log zL = ↑(Real.log ‖zL‖) + ↑(zL.arg) * I := by
      rw [← Complex.log_re zL, ← Complex.log_im zL]; exact (Complex.re_add_im _).symm
    have hlogR : Complex.log zR = ↑(Real.log ‖zR‖) + ↑(zR.arg) * I := by
      rw [← Complex.log_re zR, ← Complex.log_im zR]; exact (Complex.re_add_im _).symm
    rw [hlogL, hlogR, hzL_norm, hzR_norm, hzL_arg, hzR_arg]
    have h_simp : ↑(Real.log ε) + ↑(Real.pi / 2) * I -
        (↑(Real.log ε) + ↑(5 * Real.pi / 6 + δ_right ε * Real.pi / 12) * I) -
        -(I * ↑Real.pi / 3) =
        ↑(-(δ_right ε * Real.pi / 12)) * I := by push_cast; ring
    rw [h_simp, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
    exact lt_trans (arc_angle_lt_epsilon hδR_pos hδR_lt_one h_norm_R)
      (lt_of_lt_of_le hε_dist (min_le_right _ _))

/-- `generalizedWindingNumber' (fdBoundaryH H) 0 5 ρ' = -1/6`. -/
theorem gWN_fdBoundary_H_at_rho_plus_one (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    generalizedWindingNumber' (fdBoundaryH H) 0 5 ellipticPointRhoPlusOne = -1/6 := by
  apply ContourIntegral.gWN_eq_neg_sixth_of_pv_tendsto
  convert pv_integral_at_rho_plus_one_tendsto H hH using 2
  · simp [sub_zero, gt_iff_lt]
  · ring

end
