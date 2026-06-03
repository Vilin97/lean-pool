/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.WindingWeights.Common
import LeanPool.LeanModularForms.ContourIntegral.WindingNumber
import LeanPool.LeanModularForms.ContourIntegral.CrossingLimit

/-!
# Winding Number Weight at ρ

PV integral computation and generalized winding number of `fdBoundaryH`
around the elliptic point ρ = e^{2πi/3}.

## Main Results

* `pv_integral_at_rho_tendsto` — PV integral converges to -iπ/3
* `gWN_fdBoundary_H_at_rho` — gWN = -1/6 at ρ
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

theorem fdBoundary_H_sub_rho_seg0_re (H : ℝ) {t : ℝ} (ht : t ≤ 1) :
    (fdBoundaryH H t - ellipticPointRho).re = 1 := by
  rw [fdBoundary_H_seg0 H ht]
  simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.neg_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
    Complex.sub_im, Complex.mul_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im]
  ring

theorem fdBoundary_H_sub_rho_seg0_slitPlane (H : ℝ) {t : ℝ} (ht : t ≤ 1) :
    fdBoundaryH H t - ellipticPointRho ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left; rw [fdBoundary_H_sub_rho_seg0_re H ht]; norm_num

/-- On seg 1: `γ(t) - ρ` has `re = cos(θ(t)) + 1/2` where `θ ∈ [π/3, π/2]`,
    so `cos(θ) ∈ [0, 1/2]` and `re ∈ [1/2, 1] > 0`. -/
theorem fdBoundary_H_sub_rho_seg1_re (H : ℝ) {t : ℝ} (ht1 : 1 < t) (ht2 : t ≤ 2) :
    (fdBoundaryH H t - ellipticPointRho).re > 0 := by
  rw [fdBoundary_H_seg1 H (not_le.mpr ht1) ht2]
  simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
  set θ : ℝ := Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3) with hθ_def
  rw [show (↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
    (↑θ : ℂ) * I from by simp only [hθ_def]; push_cast; ring, exp_real_angle_I]
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.neg_re, Complex.one_re,
    Complex.div_ofNat_re, Complex.div_ofNat_im, zero_div]
  have hθ_upper : θ ≤ Real.pi / 2 := by simp only [hθ_def]; nlinarith [Real.pi_pos]
  have hcos : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by simp only [hθ_def]; nlinarith [Real.pi_pos], hθ_upper⟩
  linarith

/-- On seg 2 (t ∈ (2, 3)): `γ(t) - ρ` has `re = cos(θ(t)) + 1/2 > 0` since
    `θ ∈ (π/2, 2π/3)` gives `cos ∈ (-1/2, 0)` hence `re ∈ (0, 1/2)`. -/
theorem fdBoundary_H_sub_rho_seg2_re (H : ℝ) {t : ℝ} (ht2 : 2 < t) (ht3 : t < 3) :
    (fdBoundaryH H t - ellipticPointRho).re > 0 := by
  have h1 : ¬(t ≤ 1) := by linarith
  have h2 : ¬(t ≤ 2) := by linarith
  rw [fdBoundary_H_seg2 H h1 h2 (le_of_lt ht3)]
  simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
  set θ : ℝ := Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2) with hθ_def
  rw [show (↑Real.pi / 2 + (↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
    (↑θ : ℂ) * I from by simp only [hθ_def]; push_cast; ring, exp_real_angle_I]
  have hre : (↑(Real.cos θ) + ↑(Real.sin θ) * I -
      (-1 / 2 + ↑(Real.sqrt 3) / 2 * I)).re = Real.cos θ + 1 / 2 := by
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.neg_re, Complex.one_re,
      Complex.div_ofNat_re, Complex.div_ofNat_im, zero_div]
    ring
  rw [hre]
  have hθ_upper : θ < 2 * Real.pi / 3 := by simp only [hθ_def]; nlinarith [Real.pi_pos]
  have hcos_gt : Real.cos θ > -1 / 2 := by
    have := cos_two_pi_div_three
    rw [show (-1 : ℝ) / 2 = Real.cos (2 * Real.pi / 3) from by linarith]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (by simp only [hθ_def]; nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos]) hθ_upper
  linarith

/-- On seg 3 (t ∈ (3, 4]): `γ(t) - ρ = (y(t) - √3/2)I` with `y > √3/2`, so `im > 0`. -/
theorem fdBoundary_H_sub_rho_seg3_slitPlane (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {t : ℝ} (ht3 : 3 < t) (ht4 : t ≤ 4) :
    fdBoundaryH H t - ellipticPointRho ∈ slitPlane := by
  have h1 : ¬(t ≤ 1) := by linarith
  have h2 : ¬(t ≤ 2) := by linarith
  have h3 : ¬(t ≤ 3) := by linarith
  have h_diff : fdBoundaryH H t - (ellipticPointRho : ℂ) =
    ↑((t - 3) * (H - Real.sqrt 3 / 2)) * I := by
    rw [fdBoundary_H_seg3 H h1 h2 h3 ht4]
    simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
    push_cast; ring
  rw [h_diff, Complex.mem_slitPlane_iff]; right
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  nlinarith

/-- On seg 4: `γ(t) - ρ` has `im = H - √3/2 > 0` for `H > √3/2`. -/
theorem fdBoundary_H_sub_rho_seg4_slitPlane (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {t : ℝ} (ht4 : 4 < t) (_ht5 : t ≤ 5) :
    fdBoundaryH H t - ellipticPointRho ∈ slitPlane := by
  have h1 : ¬(t ≤ 1) := by linarith
  have h2 : ¬(t ≤ 2) := by linarith
  have h3 : ¬(t ≤ 3) := by linarith
  have h4 : ¬(t ≤ 4) := by linarith
  have h_diff : fdBoundaryH H t - (ellipticPointRho : ℂ) =
    ↑(t - 4) + ↑(H - Real.sqrt 3 / 2) * I := by
    rw [fdBoundary_H_seg4 H h1 h2 h3 h4]
    simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
    push_cast; ring
  rw [h_diff, Complex.mem_slitPlane_iff]; right
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re]
  linarith

/-- Combined: `γ(t) - ρ ∈ slitPlane` for all `t ∈ [0, 5]` with `t ≠ 3`. -/
theorem fdBoundary_H_sub_rho_slitPlane (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 5) (hne : t ≠ 3) :
    fdBoundaryH H t - ellipticPointRho ∈ slitPlane := by
  rcases le_or_gt t 1 with h1 | h1
  · exact fdBoundary_H_sub_rho_seg0_slitPlane H h1
  · rcases le_or_gt t 2 with h2 | h2
    · exact Complex.mem_slitPlane_iff.mpr (Or.inl (fdBoundary_H_sub_rho_seg1_re H h1 h2))
    · rcases lt_or_ge t 3 with h3 | h3
      · exact Complex.mem_slitPlane_iff.mpr (Or.inl (fdBoundary_H_sub_rho_seg2_re H h2 h3))
      · rcases eq_or_lt_of_le h3 with h3eq | h3lt
        · exact absurd h3eq.symm hne
        · rcases le_or_gt t 4 with h4 | h4
          · exact fdBoundary_H_sub_rho_seg3_slitPlane H hH h3lt h4
          · exact fdBoundary_H_sub_rho_seg4_slitPlane H hH h4 ht.2

/-- `ρ` is only hit at `t = 3`. -/
theorem fdBoundary_H_eq_rho_iff (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 5) :
    fdBoundaryH H t = ellipticPointRho ↔ t = 3 := by
  constructor
  · intro heq; by_contra hne
    have := fdBoundary_H_sub_rho_slitPlane H hH ht hne
    rw [heq, sub_self] at this
    exact Complex.zero_notMem_slitPlane this
  · intro heq
    rw [heq, fdBoundary_H_at_three_eq_rho]

private lemma arg_approach_rho_left_helper (hδ : 0 < δ) (hδ_small : δ < 1) :
    (fdBoundaryH H (3 - δ) - ellipticPointRho).arg = Real.pi / 6 - δ * Real.pi / 12 := by
  have h1 : ¬(3 - δ ≤ 1) := by linarith
  have h2 : ¬(3 - δ ≤ 2) := by linarith
  rw [fdBoundary_H_seg2 H h1 h2 (by linarith : 3 - δ ≤ 3)]
  simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
  have h_angle : (↑(Real.pi : ℝ) / 2 + (↑(3 - δ : ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
    (↑(2 * Real.pi / 3 - δ * Real.pi / 6) : ℂ) * I := by congr 1; push_cast; ring
  rw [h_angle, exp_real_angle_I]
  have h_cos_shift : Real.cos (2 * Real.pi / 3 - δ * Real.pi / 6) =
      -Real.sin (Real.pi / 6 - δ * Real.pi / 6) := by
    rw [show 2 * Real.pi / 3 - δ * Real.pi / 6 =
      Real.pi / 2 + (Real.pi / 6 - δ * Real.pi / 6) from by ring,
      Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have h_sin_shift : Real.sin (2 * Real.pi / 3 - δ * Real.pi / 6) =
      Real.cos (Real.pi / 6 - δ * Real.pi / 6) := by
    rw [show 2 * Real.pi / 3 - δ * Real.pi / 6 =
      Real.pi / 2 + (Real.pi / 6 - δ * Real.pi / 6) from by ring,
      Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  have h_re : -Real.sin (Real.pi / 6 - δ * Real.pi / 6) + 1 / 2 =
      2 * Real.sin (δ * Real.pi / 12) * Real.cos (Real.pi / 6 - δ * Real.pi / 12) := by
    have h := Real.sin_sub_sin (Real.pi / 6) (Real.pi / 6 - δ * Real.pi / 6)
    rw [show (Real.pi / 6 - (Real.pi / 6 - δ * Real.pi / 6)) / 2 = δ * Real.pi / 12 from by ring,
        show (Real.pi / 6 + (Real.pi / 6 - δ * Real.pi / 6)) / 2 = Real.pi / 6 - δ * Real.pi / 12
        from by ring] at h
    linarith [Real.sin_pi_div_six]
  have h_im : Real.cos (Real.pi / 6 - δ * Real.pi / 6) - Real.sqrt 3 / 2 =
      2 * Real.sin (δ * Real.pi / 12) * Real.sin (Real.pi / 6 - δ * Real.pi / 12) := by
    have h := Real.cos_sub_cos (Real.pi / 6 - δ * Real.pi / 6) (Real.pi / 6)
    rw [show (Real.pi / 6 - δ * Real.pi / 6 + Real.pi / 6) / 2 = Real.pi / 6 - δ * Real.pi / 12
        from by ring,
        show (Real.pi / 6 - δ * Real.pi / 6 - Real.pi / 6) / 2 = -(δ * Real.pi / 12) from by ring,
        Real.sin_neg] at h
    nlinarith [Real.cos_pi_div_six,
      mul_comm (Real.sin (Real.pi / 6 - δ * Real.pi / 12)) (Real.sin (δ * Real.pi / 12))]
  have h_eq : ↑(Real.cos (2 * Real.pi / 3 - δ * Real.pi / 6)) +
      ↑(Real.sin (2 * Real.pi / 3 - δ * Real.pi / 6)) * I - (-1 / 2 + ↑(Real.sqrt 3) / 2 * I) =
      ↑(2 * Real.sin (δ * Real.pi / 12)) * (↑(Real.cos (Real.pi / 6 - δ * Real.pi / 12)) +
         ↑(Real.sin (Real.pi / 6 - δ * Real.pi / 12)) * I) := by
    rw [h_cos_shift, h_sin_shift]
    apply Complex.ext
    · simp only [add_re, sub_re, mul_re, neg_re, ofReal_re, ofReal_im, I_re, I_im,
        one_re, div_ofNat_re, div_ofNat_im, mul_zero, zero_mul, sub_zero, add_zero,
        mul_one, zero_div]
      linarith [h_re]
    · simp only [add_im, sub_im, mul_im, neg_im, ofReal_re, ofReal_im, I_re, I_im,
        one_im, div_ofNat_re, div_ofNat_im, mul_zero, zero_mul, add_zero,
        mul_one, zero_div]
      linarith [h_im]
  rw [h_eq, show (↑(Real.cos (Real.pi / 6 - δ * Real.pi / 12)) : ℂ) =
    Complex.cos ↑(Real.pi / 6 - δ * Real.pi / 12) from Complex.ofReal_cos _,
    show (↑(Real.sin (Real.pi / 6 - δ * Real.pi / 12)) : ℂ) =
    Complex.sin ↑(Real.pi / 6 - δ * Real.pi / 12) from Complex.ofReal_sin _]
  exact Complex.arg_mul_cos_add_sin_mul_I (mul_pos (by norm_num : (0 : ℝ) < 2)
      (ArcCalculus.sin_pos_of_mem_Ioo_zero_pi (by constructor <;> nlinarith [Real.pi_pos])))
    ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩

/-- The `arg` of the approach direction from the left (seg 2 side) at `ρ`.
    `γ(3-δ) - ρ ≈ δ·(π/6)·exp(iπ/6)`, so `arg → π/6`. -/
theorem arg_approach_rho_left :
    Tendsto (fun δ => (fdBoundaryH H (3 - δ) - ellipticPointRho).arg)
      (𝓝[>] 0) (𝓝 (Real.pi / 6)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min 1 ε, by positivity, ?_⟩
  intro x hx_mem hx_dist
  simp only [Real.dist_eq, Set.mem_Ioi] at hx_mem hx_dist ⊢
  have hx_small : x < 1 := by
    rw [sub_zero, abs_of_pos hx_mem] at hx_dist; linarith [min_le_left 1 ε]
  rw [arg_approach_rho_left_helper (H := H) hx_mem hx_small,
      show Real.pi / 6 - x * Real.pi / 12 - Real.pi / 6 = -(x * Real.pi / 12) from by ring,
      abs_neg, abs_of_pos (by positivity)]
  have hx_lt_eps : x < ε := by
    rw [sub_zero, abs_of_pos hx_mem] at hx_dist; linarith [min_le_right 1 ε]
  nlinarith [Real.pi_le_four]

/-- The `arg` of the approach direction from the right (seg 3 side) at `ρ`.
    `γ(3+δ) - ρ = δ(H-√3/2)I`, so `arg = π/2` (exact, not just limit). -/
theorem arg_approach_rho_right (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1) :
    (fdBoundaryH H (3 + δ) - ellipticPointRho).arg = Real.pi / 2 := by
  have h1 : ¬(3 + δ ≤ 1) := by linarith
  have h2 : ¬(3 + δ ≤ 2) := by linarith
  have h3 : ¬(3 + δ ≤ 3) := by linarith
  have h4 : 3 + δ ≤ 4 := by linarith
  have h_diff : fdBoundaryH H (3 + δ) - (ellipticPointRho : ℂ) =
    ↑(δ * (H - Real.sqrt 3 / 2)) * I := by
    rw [fdBoundary_H_seg3 H h1 h2 h3 h4]
    simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
    push_cast; ring
  rw [h_diff, Complex.arg_eq_pi_div_two_iff]
  constructor
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
    ring
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re]
    nlinarith

private lemma g_seg3_value (H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    fdBoundaryH H (3 + δ) - ellipticPointRho = ↑(δ * (H - Real.sqrt 3 / 2)) * I := by
  have h1 : ¬(3 + δ ≤ 1) := by linarith
  have h2 : ¬(3 + δ ≤ 2) := by linarith
  have h3 : ¬(3 + δ ≤ 3) := by linarith
  rw [fdBoundary_H_seg3 H h1 h2 h3 (by linarith : 3 + δ ≤ 4)]
  simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
  push_cast; ring

private lemma g_norm_seg3 (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ‖fdBoundaryH H (3 + δ) - ellipticPointRho‖ = δ * (H - Real.sqrt 3 / 2) := by
  rw [g_seg3_value H hδ hδ1, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by nlinarith : 0 ≤ δ * (H - Real.sqrt 3 / 2))]

private lemma g_norm_seg2 {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ‖fdBoundaryH H (3 - δ) - ellipticPointRho‖ = 2 * Real.sin (δ * Real.pi / 12) := by
  have h1 : ¬(3 - δ ≤ 1) := by linarith
  have h2 : ¬(3 - δ ≤ 2) := by linarith
  rw [fdBoundary_H_seg2 H h1 h2 (by linarith : 3 - δ ≤ 3)]
  simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
  set θ := 2 * Real.pi / 3 - δ * Real.pi / 6
  have h_cos_shift : Real.cos θ = -Real.sin (Real.pi / 6 - δ * Real.pi / 6) := by
    rw [show θ = Real.pi / 2 + (Real.pi / 6 - δ * Real.pi / 6) from by simp only [θ]; ring,
        Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have h_sin_shift : Real.sin θ = Real.cos (Real.pi / 6 - δ * Real.pi / 6) := by
    rw [show θ = Real.pi / 2 + (Real.pi / 6 - δ * Real.pi / 6) from by simp only [θ]; ring,
        Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  have h_re : -Real.sin (Real.pi / 6 - δ * Real.pi / 6) + 1 / 2 =
      2 * Real.sin (δ * Real.pi / 12) * Real.cos (Real.pi / 6 - δ * Real.pi / 12) := by
    have h := Real.sin_sub_sin (Real.pi / 6) (Real.pi / 6 - δ * Real.pi / 6)
    rw [show (Real.pi / 6 - (Real.pi / 6 - δ * Real.pi / 6)) / 2 = δ * Real.pi / 12 from by ring,
        show (Real.pi / 6 + (Real.pi / 6 - δ * Real.pi / 6)) / 2 = Real.pi / 6 - δ * Real.pi / 12
        from by ring] at h
    linarith [Real.sin_pi_div_six]
  have h_im : Real.cos (Real.pi / 6 - δ * Real.pi / 6) - Real.sqrt 3 / 2 =
      2 * Real.sin (δ * Real.pi / 12) * Real.sin (Real.pi / 6 - δ * Real.pi / 12) := by
    have h := Real.cos_sub_cos (Real.pi / 6 - δ * Real.pi / 6) (Real.pi / 6)
    rw [show (Real.pi / 6 - δ * Real.pi / 6 + Real.pi / 6) / 2 = Real.pi / 6 - δ * Real.pi / 12
        from by ring,
        show (Real.pi / 6 - δ * Real.pi / 6 - Real.pi / 6) / 2 = -(δ * Real.pi / 12) from by ring,
        Real.sin_neg] at h
    nlinarith [Real.cos_pi_div_six,
      mul_comm (Real.sin (Real.pi / 6 - δ * Real.pi / 12)) (Real.sin (δ * Real.pi / 12))]
  have h_eq : (↑(Real.cos θ) + ↑(Real.sin θ) * I - (-1/2 + ↑(Real.sqrt 3) / 2 * I)) =
      ↑(2 * Real.sin (δ * Real.pi / 12)) * (↑(Real.cos (Real.pi / 6 - δ * Real.pi / 12)) +
         ↑(Real.sin (Real.pi / 6 - δ * Real.pi / 12)) * I) := by
    rw [h_cos_shift, h_sin_shift]
    apply Complex.ext
    · simp only [add_re, sub_re, mul_re, neg_re, ofReal_re, ofReal_im, I_re, I_im,
        one_re, div_ofNat_re, div_ofNat_im, mul_zero, zero_mul, sub_zero, add_zero,
        mul_one, zero_div]; linarith [h_re]
    · simp only [add_im, sub_im, mul_im, neg_im, ofReal_re, ofReal_im, I_re, I_im,
        one_im, div_ofNat_re, div_ofNat_im, mul_zero, zero_mul, add_zero,
        mul_one, zero_div]; linarith [h_im]
  rw [show (↑Real.pi / 2 + (↑(3 - δ : ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
    (↑θ : ℂ) * I from by simp only [θ]; push_cast; ring, exp_real_angle_I, h_eq]
  have h_sin_nn : 0 ≤ Real.sin (δ * Real.pi / 12) :=
    le_of_lt (ArcCalculus.sin_pos_of_mem_Ioo_zero_pi (by constructor <;> nlinarith [Real.pi_pos]))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (by norm_num) h_sin_nn),
    show (↑(Real.cos (Real.pi / 6 - δ * Real.pi / 12)) +
      ↑(Real.sin (Real.pi / 6 - δ * Real.pi / 12)) * I) =
      Complex.exp (↑(Real.pi / 6 - δ * Real.pi / 12) * I) from by rw [exp_real_angle_I],
    Complex.norm_exp_ofReal_mul_I, mul_one]

private lemma g_norm_arc {t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) :
    ‖fdBoundaryH H t - ellipticPointRho‖ = 2 * Real.sin ((3 - t) * Real.pi / 12) := by
  rw [fdBoundary_H_eq_arc ht1 ht3]
  simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
  set δ := 3 - t with hδ_def
  have hδ : 0 < δ := by linarith
  have hδ2 : δ < 2 := by linarith
  set θ := 2 * Real.pi / 3 - δ * Real.pi / 6
  rw [show Real.pi * (1 + t) / 6 = θ from by simp only [θ, hδ_def]; ring]
  have h_cos_shift : Real.cos θ = -Real.sin (Real.pi / 6 - δ * Real.pi / 6) := by
    rw [show θ = Real.pi / 2 + (Real.pi / 6 - δ * Real.pi / 6) from by simp only [θ]; ring,
        Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have h_sin_shift : Real.sin θ = Real.cos (Real.pi / 6 - δ * Real.pi / 6) := by
    rw [show θ = Real.pi / 2 + (Real.pi / 6 - δ * Real.pi / 6) from by simp only [θ]; ring,
        Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  have h_re : -Real.sin (Real.pi / 6 - δ * Real.pi / 6) + 1 / 2 =
      2 * Real.sin (δ * Real.pi / 12) * Real.cos (Real.pi / 6 - δ * Real.pi / 12) := by
    have h := Real.sin_sub_sin (Real.pi / 6) (Real.pi / 6 - δ * Real.pi / 6)
    rw [show (Real.pi / 6 - (Real.pi / 6 - δ * Real.pi / 6)) / 2 = δ * Real.pi / 12 from by ring,
        show (Real.pi / 6 + (Real.pi / 6 - δ * Real.pi / 6)) / 2 = Real.pi / 6 - δ * Real.pi / 12
        from by ring] at h
    linarith [Real.sin_pi_div_six]
  have h_im : Real.cos (Real.pi / 6 - δ * Real.pi / 6) - Real.sqrt 3 / 2 =
      2 * Real.sin (δ * Real.pi / 12) * Real.sin (Real.pi / 6 - δ * Real.pi / 12) := by
    have h := Real.cos_sub_cos (Real.pi / 6 - δ * Real.pi / 6) (Real.pi / 6)
    rw [show (Real.pi / 6 - δ * Real.pi / 6 + Real.pi / 6) / 2 = Real.pi / 6 - δ * Real.pi / 12
        from by ring,
        show (Real.pi / 6 - δ * Real.pi / 6 - Real.pi / 6) / 2 = -(δ * Real.pi / 12) from by ring,
        Real.sin_neg] at h
    nlinarith [Real.cos_pi_div_six,
      mul_comm (Real.sin (Real.pi / 6 - δ * Real.pi / 12)) (Real.sin (δ * Real.pi / 12))]
  have h_eq : (↑(Real.cos θ) + ↑(Real.sin θ) * I - (-1/2 + ↑(Real.sqrt 3) / 2 * I)) =
      ↑(2 * Real.sin (δ * Real.pi / 12)) * (↑(Real.cos (Real.pi / 6 - δ * Real.pi / 12)) +
         ↑(Real.sin (Real.pi / 6 - δ * Real.pi / 12)) * I) := by
    rw [h_cos_shift, h_sin_shift]
    apply Complex.ext
    · simp only [add_re, sub_re, mul_re, neg_re, ofReal_re, ofReal_im, I_re, I_im,
        one_re, div_ofNat_re, div_ofNat_im, mul_zero, zero_mul, sub_zero, add_zero,
        mul_one, zero_div]; linarith [h_re]
    · simp only [add_im, sub_im, mul_im, neg_im, ofReal_re, ofReal_im, I_re, I_im,
        one_im, div_ofNat_re, div_ofNat_im, mul_zero, zero_mul, add_zero,
        mul_one, zero_div]; linarith [h_im]
  rw [show (↑(θ : ℝ) : ℂ) * I = (↑θ : ℂ) * I from rfl, exp_real_angle_I, h_eq]
  have h_sin_nn : 0 ≤ Real.sin (δ * Real.pi / 12) :=
    le_of_lt (ArcCalculus.sin_pos_of_mem_Ioo_zero_pi (by constructor <;> nlinarith [Real.pi_pos]))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (by norm_num) h_sin_nn),
    show (↑(Real.cos (Real.pi / 6 - δ * Real.pi / 12)) +
      ↑(Real.sin (Real.pi / 6 - δ * Real.pi / 12)) * I) =
      Complex.exp (↑(Real.pi / 6 - δ * Real.pi / 12) * I) from by rw [exp_real_angle_I],
    Complex.norm_exp_ofReal_mul_I, mul_one]

private lemma g_norm_ge_one_seg0 {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 ≤ ‖fdBoundaryH H t - ellipticPointRho‖ := by
  calc 1 = |1| := (abs_of_pos one_pos).symm
    _ = |(fdBoundaryH H t - ellipticPointRho).re| := by rw [fdBoundary_H_sub_rho_seg0_re H ht1]
    _ ≤ ‖fdBoundaryH H t - ellipticPointRho‖ := Complex.abs_re_le_norm _

private lemma g_norm_ge_seg4 (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {t : ℝ} (ht4 : 4 ≤ t) (ht5 : t ≤ 5) :
    H - Real.sqrt 3 / 2 ≤ ‖fdBoundaryH H t - ellipticPointRho‖ := by
  have him : (fdBoundaryH H t - (ellipticPointRho : ℂ)).im = H - Real.sqrt 3 / 2 := by
    rcases eq_or_lt_of_le ht4 with rfl | ht4'
    · have hd : fdBoundaryH H 4 - (ellipticPointRho : ℂ) = ↑(H - Real.sqrt 3 / 2) * I := by
        rw [fdBoundary_H_at_four H]
        simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
        push_cast; ring
      rw [hd, mul_comm, Complex.I_mul_im, Complex.ofReal_re]
    · have hd : fdBoundaryH H t - (ellipticPointRho : ℂ) =
          ↑(t - 4) + ↑(H - Real.sqrt 3 / 2) * I := by
        rw [fdBoundary_H_seg4 H (by linarith) (by linarith) (by linarith) (by linarith)]
        simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
        push_cast; ring
      rw [hd, Complex.add_im, Complex.ofReal_im, zero_add,
        mul_comm, Complex.I_mul_im, Complex.ofReal_re]
  calc H - Real.sqrt 3 / 2 = |(H - Real.sqrt 3 / 2 : ℝ)| := (abs_of_pos (by linarith)).symm
    _ = |(fdBoundaryH H t - (ellipticPointRho : ℂ)).im| := by rw [him]
    _ ≤ ‖fdBoundaryH H t - (ellipticPointRho : ℂ)‖ := Complex.abs_im_le_norm _

private lemma ftc_logDeriv_telescope_rho (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {δ_L δ_R : ℝ} (hδ_L : 0 < δ_L) (hδ_L1 : δ_L < 1) (hδ_R : 0 < δ_R) (hδ_R1 : δ_R < 1) :
    let g := fun t => fdBoundaryH H t - (ellipticPointRho : ℂ)
    IntervalIntegrable (fun t => deriv g t / g t) volume 0 (3 - δ_L) ∧
    IntervalIntegrable (fun t => deriv g t / g t) volume (3 + δ_R) 5 ∧
    ((∫ t in (0 : ℝ)..(3 - δ_L), deriv g t / g t) + (∫ t in (3 + δ_R)..(5 : ℝ), deriv g t / g t) =
    Complex.log (g (3 - δ_L)) - Complex.log (g (3 + δ_R))) := by
  intro g
  set ρ : ℂ := ellipticPointRho with hρ_def
  set h₀ : ℝ → ℂ :=
    fun t => 1 + (↑H - ↑t * (↑H - ↑(Real.sqrt 3) / 2) - ↑(Real.sqrt 3) / 2) * I
  set h₁ : ℝ → ℂ := fun t => exp (↑(Real.pi * (1 + t) / 6) * I) - ρ
  set h₂ : ℝ → ℂ := fun t => ↑((t - 3) * (H - Real.sqrt 3 / 2)) * I
  set h₃ : ℝ → ℂ := fun t => ↑(t - 4) + ↑(H - Real.sqrt 3 / 2) * I
  have hg_eq_h₀ : ∀ t, t ≤ 1 → g t = h₀ t := by
    intro t ht; change fdBoundaryH H t - ρ = h₀ t
    rw [fdBoundary_H_seg0 H ht]
    simp only [hρ_def, ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk, h₀]
    ring
  have hg_eq_h₁ : ∀ t, 1 < t → t < 3 → g t = h₁ t := by
    intro t ht1 ht3; change fdBoundaryH H t - ρ = h₁ t
    rw [fdBoundary_H_eq_arc ht1 ht3]
  have hg_eq_h₂ : ∀ t, 3 < t → t ≤ 4 → g t = h₂ t := by
    intro t ht3 ht4; change fdBoundaryH H t - ρ = h₂ t
    rw [fdBoundary_H_seg3 H (by linarith) (by linarith) (by linarith) ht4]
    simp only [hρ_def, ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk, h₂]
    push_cast; ring
  have hg_eq_h₃ : ∀ t, 4 < t → g t = h₃ t := by
    intro t ht4; change fdBoundaryH H t - ρ = h₃ t
    rw [fdBoundary_H_seg4 H (by linarith) (by linarith) (by linarith) (by linarith)]
    simp only [hρ_def, ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk, h₃]
    push_cast; ring
  have hg0 : g 0 = h₀ 0 := hg_eq_h₀ 0 (by norm_num)
  have hg1_0 : g 1 = h₀ 1 := hg_eq_h₀ 1 (le_refl 1)
  have hg1_1 : g 1 = h₁ 1 := by
    change fdBoundaryH H 1 - ρ = h₁ 1
    rw [fdBoundary_H_at_one_eq_rho_plus_one]
    simp only [h₁, hρ_def, ellipticPointRhoPlusOne, ellipticPointRhoPlusOne',
      ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
    rw [show Real.pi * (1 + 1) / 6 = Real.pi / 3 from by ring]
    rw [exp_real_angle_I, Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast; ring
  have hg3mδ : g (3 - δ_L) = h₁ (3 - δ_L) := hg_eq_h₁ (3 - δ_L) (by linarith) (by linarith)
  have hg3pδ : g (3 + δ_R) = h₂ (3 + δ_R) := hg_eq_h₂ (3 + δ_R) (by linarith) (by linarith)
  have hg4_2 : g 4 = h₂ 4 := hg_eq_h₂ 4 (by linarith) (le_refl 4)
  have hg4_3 : g 4 = h₃ 4 := by
    change fdBoundaryH H 4 - ρ = h₃ 4
    rw [fdBoundary_H_at_four H]
    simp only [hρ_def, ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk, h₃]
    push_cast; ring
  have hg5 : g 5 = h₃ 5 := hg_eq_h₃ 5 (by norm_num)
  have hd_h₀ : ∀ t : ℝ, HasDerivAt h₀ (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
    intro t
    set c : ℂ := ↑(H - Real.sqrt 3 / 2) * I
    have h_eq : h₀ = fun (s : ℝ) => (1 + c) + (-c) * ↑s := by
      ext s; simp only [h₀, c]; push_cast; ring
    rw [h_eq, show -(↑(H - Real.sqrt 3 / 2) : ℂ) * I = -c from by simp [c]; ring]
    exact ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-c)).const_add (1 + c)
      |>.congr_deriv (by simp [mul_one])
  have hd_h₁ : ∀ t : ℝ, HasDerivAt h₁
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I)) t := by
    intro t
    have hf : HasDerivAt (fun s : ℝ => Real.pi * (1 + s) / 6) (Real.pi / 6) t :=
      ((hasDerivAt_id t).add_const (1 : ℝ) |>.const_mul (Real.pi / 6)).congr_of_eventuallyEq
        (Eventually.of_forall fun s => show _ from by simp [id]; ring)
        |>.congr_deriv (by ring)
    have hci : HasDerivAt (fun s : ℝ => (↑(Real.pi * (1 + s) / 6) : ℂ) * I)
        ((↑(Real.pi / 6) : ℂ) * I) t :=
      (hf.ofReal_comp.mul_const I).congr_deriv (by norm_num [smul_eq_mul])
    exact (hci.cexp.sub (hasDerivAt_const t ρ)).congr_deriv (by simp only [sub_zero]; ring)
  have hd_h₂ : ∀ t : ℝ, HasDerivAt h₂ ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
    intro t
    exact ((((hasDerivAt_id t).sub (hasDerivAt_const t 3)).mul_const
      (H - Real.sqrt 3 / 2)).ofReal_comp.mul_const I).congr_deriv (by norm_num [smul_eq_mul])
  have hd_h₃ : ∀ t : ℝ, HasDerivAt h₃ 1 t := by
    intro t
    have key := (((hasDerivAt_id t).sub (hasDerivAt_const t (4 : ℝ))).ofReal_comp.add
      (hasDerivAt_const t (↑(H - Real.sqrt 3 / 2) * I)))
    convert key using 1; simp [sub_zero]
  have heq_01 : ∀ t ∈ Ioo (0 : ℝ) 1, g t = h₀ t ∧ deriv g t = deriv h₀ t := by
    intro t ⟨_, ht1⟩
    refine ⟨hg_eq_h₀ t (le_of_lt ht1), ?_⟩
    have heq : g =ᶠ[𝓝 t] h₀ :=
      Filter.eventually_of_mem (Iio_mem_nhds ht1) (fun s hs => hg_eq_h₀ s (le_of_lt hs))
    exact heq.deriv_eq
  have heq_1_3mδ : ∀ t ∈ Ioo (1 : ℝ) (3 - δ_L),
      g t = h₁ t ∧ deriv g t = deriv h₁ t := by
    intro t ⟨ht1, ht3mδ⟩
    have ht3 : t < 3 := by linarith
    refine ⟨hg_eq_h₁ t ht1 ht3, ?_⟩
    have heq : g =ᶠ[𝓝 t] h₁ :=
      Filter.eventually_of_mem (Ioo_mem_nhds ht1 ht3) (fun s hs => hg_eq_h₁ s hs.1 hs.2)
    exact heq.deriv_eq
  have heq_3pδ_4 : ∀ t ∈ Ioo (3 + δ_R) (4 : ℝ),
      g t = h₂ t ∧ deriv g t = deriv h₂ t := by
    intro t ⟨ht3, ht4⟩
    refine ⟨hg_eq_h₂ t (by linarith) (le_of_lt ht4), ?_⟩
    have heq : g =ᶠ[𝓝 t] h₂ :=
      Filter.eventually_of_mem (Ioo_mem_nhds (by linarith : 3 < t) ht4)
        (fun s hs => hg_eq_h₂ s (by linarith [hs.1]) (le_of_lt hs.2))
    exact heq.deriv_eq
  have heq_45 : ∀ t ∈ Ioo (4 : ℝ) 5, g t = h₃ t ∧ deriv g t = deriv h₃ t := by
    intro t ⟨ht4, _⟩
    refine ⟨hg_eq_h₃ t ht4, ?_⟩
    have heq : g =ᶠ[𝓝 t] h₃ :=
      Filter.eventually_of_mem (Ioi_mem_nhds ht4) (fun s hs => hg_eq_h₃ s hs)
    exact heq.deriv_eq
  have hh₀_cont : ContinuousOn h₀ (Icc 0 1) :=
    fun t _ => (hd_h₀ t).continuousAt.continuousWithinAt
  have hh₁_cont : ContinuousOn h₁ (Icc 1 (3 - δ_L)) :=
    fun t _ => (hd_h₁ t).continuousAt.continuousWithinAt
  have hh₂_cont : ContinuousOn h₂ (Icc (3 + δ_R) 4) :=
    fun t _ => (hd_h₂ t).continuousAt.continuousWithinAt
  have hh₃_cont : ContinuousOn h₃ (Icc 4 5) :=
    fun t _ => (hd_h₃ t).continuousAt.continuousWithinAt
  have hh₀_diff : ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ h₀ t :=
    fun t _ => (hd_h₀ t).differentiableAt
  have hh₁_diff : ∀ t ∈ Ioo (1 : ℝ) (3 - δ_L), DifferentiableAt ℝ h₁ t :=
    fun t _ => (hd_h₁ t).differentiableAt
  have hh₂_diff : ∀ t ∈ Ioo (3 + δ_R) (4 : ℝ), DifferentiableAt ℝ h₂ t :=
    fun t _ => (hd_h₂ t).differentiableAt
  have hh₃_diff : ∀ t ∈ Ioo (4 : ℝ) 5, DifferentiableAt ℝ h₃ t :=
    fun t _ => (hd_h₃ t).differentiableAt
  have hh₀_deriv_cont : ContinuousOn (deriv h₀) (Icc 0 1) := by
    rw [show deriv h₀ = fun _ => -(↑(H - Real.sqrt 3 / 2) : ℂ) * I from
      funext fun t => (hd_h₀ t).deriv]; exact continuousOn_const
  have hh₁_deriv_cont : ContinuousOn (deriv h₁) (Icc 1 (3 - δ_L)) := by
    rw [show deriv h₁ = fun t => ↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I) from
      funext fun t => (hd_h₁ t).deriv]
    exact (Continuous.mul continuous_const (Continuous.cexp (Continuous.mul
      (continuous_ofReal.comp (by fun_prop : Continuous fun s => Real.pi * (1 + s) / 6))
      continuous_const))).continuousOn
  have hh₂_deriv_cont : ContinuousOn (deriv h₂) (Icc (3 + δ_R) 4) := by
    rw [show deriv h₂ = fun _ => (↑(H - Real.sqrt 3 / 2) : ℂ) * I from
      funext fun t => (hd_h₂ t).deriv]; exact continuousOn_const
  have hh₃_deriv_cont : ContinuousOn (deriv h₃) (Icc 4 5) := by
    rw [show deriv h₃ = fun _ => (1 : ℂ) from
      funext fun t => (hd_h₃ t).deriv]; exact continuousOn_const
  have hh₀_slit : ∀ t ∈ Icc (0 : ℝ) 1, h₀ t ∈ slitPlane := by
    intro t ht; rw [← hg_eq_h₀ t ht.2]
    exact fdBoundary_H_sub_rho_seg0_slitPlane H ht.2
  have hh₁_slit : ∀ t ∈ Icc (1 : ℝ) (3 - δ_L), h₁ t ∈ slitPlane := by
    intro t ⟨ht1, ht3⟩
    rcases eq_or_lt_of_le ht1 with rfl | ht1'
    · rw [← hg1_1]
      exact fdBoundary_H_sub_rho_slitPlane H hH ⟨by norm_num, by linarith⟩ (by linarith)
    · rw [← hg_eq_h₁ t ht1' (by linarith)]
      exact fdBoundary_H_sub_rho_slitPlane H hH ⟨by linarith, by linarith⟩ (by linarith)
  have hh₂_slit : ∀ t ∈ Icc (3 + δ_R) (4 : ℝ), h₂ t ∈ slitPlane := by
    intro t ⟨ht3, ht4⟩
    rw [← hg_eq_h₂ t (by linarith) ht4]
    exact fdBoundary_H_sub_rho_slitPlane H hH ⟨by linarith, by linarith⟩ (by linarith)
  have hh₃_slit : ∀ t ∈ Icc (4 : ℝ) 5, h₃ t ∈ slitPlane := by
    intro t ⟨ht4, ht5⟩
    rcases eq_or_lt_of_le ht4 with rfl | ht4'
    · rw [← hg4_3]
      exact fdBoundary_H_sub_rho_slitPlane H hH ⟨by norm_num, by norm_num⟩ (by norm_num)
    · rw [← hg_eq_h₃ t ht4']
      exact fdBoundary_H_sub_rho_slitPlane H hH ⟨by linarith, ht5⟩ (by linarith)
  have piece₀ := ftc_log_piece (by norm_num : (0 : ℝ) ≤ 1)
    hh₀_cont hh₀_diff hh₀_deriv_cont hh₀_slit heq_01 hg0 hg1_0
  have piece₁ := ftc_log_piece (by linarith : (1 : ℝ) ≤ 3 - δ_L)
    hh₁_cont hh₁_diff hh₁_deriv_cont
    hh₁_slit heq_1_3mδ (hg1_0.symm ▸ hg1_1) hg3mδ
  have piece₂ := ftc_log_piece (by linarith : (3 + δ_R) ≤ 4)
    hh₂_cont hh₂_diff hh₂_deriv_cont
    hh₂_slit heq_3pδ_4 hg3pδ (hg4_3.symm ▸ hg4_2)
  have piece₃ := ftc_log_piece (by norm_num : (4 : ℝ) ≤ 5)
    hh₃_cont hh₃_diff hh₃_deriv_cont hh₃_slit heq_45 hg4_3 hg5
  refine ⟨piece₀.1.trans piece₁.1, piece₂.1.trans piece₃.1, ?_⟩
  rw [(intervalIntegral.integral_add_adjacent_intervals piece₀.1 piece₁.1).symm,
      (intervalIntegral.integral_add_adjacent_intervals piece₂.1 piece₃.1).symm,
      piece₀.2, piece₁.2, piece₂.2, piece₃.2]
  have hg_closed : g 0 = g 5 := by
    change fdBoundaryH H 0 - ρ = fdBoundaryH H 5 - ρ
    rw [fdBoundary_H_closed H]
  rw [hg_closed]
  ring

private lemma norm_le_middle_rho (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {ε δ_L δ_R : ℝ} (hε : 0 < ε) (hδ_L_pos : 0 < δ_L) (hδ_L_lt_one : δ_L < 1)
    (hδ_R_pos : 0 < δ_R) (hδ_R_lt_one : δ_R < 1)
    (h_norm_L : ‖fdBoundaryH H (3 - δ_L) - ellipticPointRho‖ = ε)
    (h_norm_R : ‖fdBoundaryH H (3 + δ_R) - ellipticPointRho‖ = ε)
    (hH_gap : 0 < H - Real.sqrt 3 / 2) :
    ∀ t, 3 - δ_L ≤ t → t ≤ 3 + δ_R →
      ¬(‖fdBoundaryH H t - (ellipticPointRho : ℂ)‖ > ε) := by
  intro t ht_lo ht_hi
  push Not
  rcases le_or_gt t 3 with ht3 | ht3
  · rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · simp only [fdBoundary_H_at_three_eq_rho, sub_self, norm_zero]
      exact le_of_lt hε
    · have ht1 : 1 < t := by nlinarith
      rw [g_norm_arc ht1 ht3']
      rw [← h_norm_L, g_norm_seg2 hδ_L_pos hδ_L_lt_one]
      have h_3mt_le : 3 - t ≤ δ_L := by linarith
      have h_angle_le : (3 - t) * Real.pi / 12 ≤ δ_L * Real.pi / 12 := by
        nlinarith [Real.pi_pos]
      exact mul_le_mul_of_nonneg_left
        (Real.sin_le_sin_of_le_of_le_pi_div_two
          (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]) h_angle_le)
        (by norm_num : (0 : ℝ) ≤ 2)
  · have ht_le_4 : t ≤ 4 := by linarith
    have h_t_as_3pδ : t = 3 + (t - 3) := by ring
    rw [h_t_as_3pδ, g_norm_seg3 H hH (by linarith) (by linarith : t - 3 ≤ 1)]
    rw [← h_norm_R, g_norm_seg3 H hH hδ_R_pos (le_of_lt hδ_R_lt_one)]
    exact mul_le_mul_of_nonneg_right (by linarith : t - 3 ≤ δ_R) (le_of_lt hH_gap)

private lemma cutoff_integral_eq_ftc (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {ε : ℝ} (hε : 0 < ε) (hε_small : ε < H - Real.sqrt 3 / 2)
    (hε_small2 : ε < 2 * Real.sin (Real.pi / 12)) :
    let g := fun t => fdBoundaryH H t - (ellipticPointRho : ℂ)
    (∃ δ_L ∈ Set.Ioo (0 : ℝ) 1, ∃ δ_R ∈ Set.Ioo (0 : ℝ) 1,
      ‖g (3 - δ_L)‖ = ε ∧ ‖g (3 + δ_R)‖ = ε ∧
      (∫ t in (0 : ℝ)..5, if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0) =
      (∫ t in (0 : ℝ)..(3 - δ_L),
        deriv g t / g t) + (∫ t in (3 + δ_R)..(5 : ℝ), deriv g t / g t)) := by
  intro g
  set δ_R := ε / (H - Real.sqrt 3 / 2) with hδ_R_def
  set δ_L := 12 / Real.pi * Real.arcsin (ε / 2) with hδ_L_def
  have hH_gap : 0 < H - Real.sqrt 3 / 2 := by linarith
  have hε_half_le : ε / 2 ≤ 1 := by linarith [hε_small2, Real.sin_le_one (Real.pi / 12)]
  have hε_half_neg : -1 ≤ ε / 2 := by linarith
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hδ_R_pos : 0 < δ_R := div_pos hε hH_gap
  have hδ_R_lt_one : δ_R < 1 := by
    rw [hδ_R_def, div_lt_one hH_gap]; linarith
  have hδ_L_pos : 0 < δ_L := by
    rw [hδ_L_def]; exact mul_pos (div_pos (by norm_num) hpi_pos)
      (Real.arcsin_pos.mpr (by linarith))
  have hδ_L_lt_one : δ_L < 1 := by
    rw [hδ_L_def]
    have harcsin_lt : Real.arcsin (ε / 2) < Real.pi / 12 :=
      calc Real.arcsin (ε / 2)
          < Real.arcsin (Real.sin (Real.pi / 12)) :=
            Real.arcsin_lt_arcsin hε_half_neg (by linarith) (Real.sin_le_one _)
        _ = Real.pi / 12 :=
            Real.arcsin_sin (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    calc 12 / Real.pi * Real.arcsin (ε / 2)
        < 12 / Real.pi * (Real.pi / 12) :=
          mul_lt_mul_of_pos_left harcsin_lt (div_pos (by norm_num) hpi_pos)
      _ = 1 := by field_simp
  have hδ_L_angle : δ_L * Real.pi / 12 = Real.arcsin (ε / 2) := by
    rw [hδ_L_def]; field_simp
  have h_norm_L : ‖g (3 - δ_L)‖ = ε := by
    change ‖fdBoundaryH H (3 - δ_L) - ellipticPointRho‖ = ε
    rw [g_norm_seg2 hδ_L_pos hδ_L_lt_one, hδ_L_angle,
        Real.sin_arcsin hε_half_neg hε_half_le]
    linarith
  have h_norm_R : ‖g (3 + δ_R)‖ = ε := by
    change ‖fdBoundaryH H (3 + δ_R) - ellipticPointRho‖ = ε
    rw [g_norm_seg3 H hH hδ_R_pos (le_of_lt hδ_R_lt_one), hδ_R_def]
    field_simp
    have : H * 2 - Real.sqrt 3 > 0 := by nlinarith
    exact div_self (ne_of_gt this)
  obtain ⟨hint_L, hint_R, _⟩ :=
    ftc_logDeriv_telescope_rho H hH hδ_L_pos hδ_L_lt_one hδ_R_pos hδ_R_lt_one
  have hε_lt_one : ε < 1 := by
    have hsin_bound : Real.sin (Real.pi / 12) < 1 / 2 := by
      calc Real.sin (Real.pi / 12) < Real.sin (Real.pi / 6) :=
            Real.sin_lt_sin_of_lt_of_le_pi_div_two (by nlinarith [Real.pi_pos])
              (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
        _ = 1 / 2 := by rw [Real.sin_pi_div_six]
    linarith
  set F := fun t => if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else (0 : ℂ) with hF_def
  have hg_eq : g = fun t => fdBoundaryH H t - (ellipticPointRho : ℂ) := rfl
  have h_norm_gt_left : ∀ t ∈ Ioo (0 : ℝ) (3 - δ_L), ‖g t‖ > ε := by
    intro t ⟨ht0, ht3⟩
    rcases le_or_gt t 1 with ht1 | ht1
    · calc ε < 1 := hε_lt_one
        _ ≤ ‖g t‖ := g_norm_ge_one_seg0 (le_of_lt ht0) ht1
    · have ht3' : t < 3 := by linarith
      rw [hg_eq, g_norm_arc ht1 ht3', ← h_norm_L, hg_eq, g_norm_seg2 hδ_L_pos hδ_L_lt_one]
      apply mul_lt_mul_of_pos_left _ (by norm_num : (0 : ℝ) < 2)
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
        (by nlinarith : δ_L * Real.pi / 12 < (3 - t) * Real.pi / 12)
  have h_norm_gt_right : ∀ t ∈ Ioo (3 + δ_R) (5 : ℝ), ‖g t‖ > ε := by
    intro t ⟨ht3, ht5⟩
    rcases le_or_gt t 4 with ht4 | ht4
    · have h_t_eq : t = 3 + (t - 3) := by ring
      rw [hg_eq, h_t_eq, g_norm_seg3 H hH (by linarith : 0 < t - 3) (by linarith : t - 3 ≤ 1),
          ← h_norm_R, hg_eq, g_norm_seg3 H hH hδ_R_pos (le_of_lt hδ_R_lt_one)]
      exact mul_lt_mul_of_pos_right (by linarith : δ_R < t - 3) hH_gap
    · calc ε < H - Real.sqrt 3 / 2 := hε_small
        _ ≤ ‖g t‖ := by rw [hg_eq]; exact g_norm_ge_seg4 H hH (le_of_lt ht4) (le_of_lt ht5)
  have h_norm_le_middle : ∀ t, 3 - δ_L ≤ t → t ≤ 3 + δ_R → ¬(‖g t‖ > ε) :=
    norm_le_middle_rho H hH hε hδ_L_pos hδ_L_lt_one hδ_R_pos hδ_R_lt_one h_norm_L h_norm_R hH_gap
  have hF_when_gt (t : ℝ) (h_gt : ‖g t‖ > ε) : F t = deriv g t / g t := by
    simp only [hF_def, if_pos h_gt, mul_comm (g t)⁻¹, div_eq_mul_inv]
  have hF_when_le (t : ℝ) (h_le : ¬(‖g t‖ > ε)) : F t = 0 := by
    simp only [hF_def, if_neg h_le]
  have hF_eq_left_ae :
      ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) (3 - δ_L) → F t = deriv g t / g t := by
    have : ({3 - δ_L} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact measure_singleton _)
    filter_upwards [this] with t ht_ne ht_mem
    rw [uIoc_of_le (by linarith : (0 : ℝ) ≤ 3 - δ_L)] at ht_mem
    have ht_lt : t < 3 - δ_L := lt_of_le_of_ne ht_mem.2 (fun h => ht_ne (mem_singleton_iff.mpr h))
    exact hF_when_gt t (h_norm_gt_left t ⟨ht_mem.1, ht_lt⟩)
  have hF_int_left : IntervalIntegrable F volume 0 (3 - δ_L) :=
    hint_L.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hF_eq_left_ae.mono (fun t ht hm => (ht hm).symm)))
  have hF_eq_mid : ∀ t ∈ Ι (3 - δ_L) (3 + δ_R), F t = 0 := by
    intro t ht
    rw [uIoc_of_le (by linarith : 3 - δ_L ≤ 3 + δ_R)] at ht
    exact hF_when_le t (h_norm_le_middle t (le_of_lt ht.1) ht.2)
  have hF_int_mid : IntervalIntegrable F volume (3 - δ_L) (3 + δ_R) :=
    (IntervalIntegrable.zero (μ := volume) (a := 3 - δ_L) (b := 3 + δ_R)).congr
      (fun t ht => (hF_eq_mid t ht).symm)
  have hF_eq_right_ae :
      ∀ᵐ t ∂volume, t ∈ Ι (3 + δ_R) (5 : ℝ) → F t = deriv g t / g t := by
    have : ({5} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact measure_singleton _)
    filter_upwards [this] with t ht_ne ht_mem
    rw [uIoc_of_le (by linarith : 3 + δ_R ≤ 5)] at ht_mem
    have ht_lt : t < 5 := lt_of_le_of_ne ht_mem.2 (fun h => ht_ne (mem_singleton_iff.mpr h))
    exact hF_when_gt t (h_norm_gt_right t ⟨ht_mem.1, ht_lt⟩)
  have hF_int_right : IntervalIntegrable F volume (3 + δ_R) 5 :=
    hint_R.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hF_eq_right_ae.mono (fun t ht hm => (ht hm).symm)))
  have h_adj1 := intervalIntegral.integral_add_adjacent_intervals hF_int_left hF_int_mid
  have h_adj2 := intervalIntegral.integral_add_adjacent_intervals
    (hF_int_left.trans hF_int_mid) hF_int_right
  have h_split : ∫ t in (0 : ℝ)..5, F t =
      (∫ t in (0 : ℝ)..(3 - δ_L), F t) + (∫ t in (3 - δ_L)..(3 + δ_R), F t) +
      (∫ t in (3 + δ_R)..(5 : ℝ), F t) := by
    rw [← h_adj2, ← h_adj1]
  have h_mid_zero : ∫ t in (3 - δ_L)..(3 + δ_R), F t = 0 := by
    rw [intervalIntegral.integral_congr_ae (ae_of_all _ (fun t ht => hF_eq_mid t ht))]
    simp [intervalIntegral.integral_zero]
  have h_left_eq : ∫ t in (0 : ℝ)..(3 - δ_L), F t =
      ∫ t in (0 : ℝ)..(3 - δ_L), deriv g t / g t :=
    intervalIntegral.integral_congr_ae hF_eq_left_ae
  have h_right_eq : ∫ t in (3 + δ_R)..(5 : ℝ), F t =
      ∫ t in (3 + δ_R)..(5 : ℝ), deriv g t / g t :=
    intervalIntegral.integral_congr_ae hF_eq_right_ae
  refine ⟨δ_L, ⟨hδ_L_pos, hδ_L_lt_one⟩, δ_R, ⟨hδ_R_pos, hδ_R_lt_one⟩,
    h_norm_L, h_norm_R, ?_⟩
  calc (∫ t in (0 : ℝ)..5, if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0)
      = ∫ t in (0 : ℝ)..5, F t := rfl
    _ = ((∫ t in (0 : ℝ)..(3 - δ_L), F t) + (∫ t in (3 - δ_L)..(3 + δ_R), F t)) +
        (∫ t in (3 + δ_R)..(5 : ℝ), F t) := h_split
    _ = ((∫ t in (0 : ℝ)..(3 - δ_L), F t) + 0) + (∫ t in (3 + δ_R)..(5 : ℝ), F t) := by
        rw [h_mid_zero]
    _ = (∫ t in (0 : ℝ)..(3 - δ_L), deriv g t / g t) +
        (∫ t in (3 + δ_R)..(5 : ℝ), deriv g t / g t) := by rw [h_left_eq, h_right_eq, add_zero]

-- Left cutoff: angle-based distance to ρ from arc side
private def δ_L_rho : ℝ → ℝ := fun ε => 12 / Real.pi * Real.arcsin (ε / 2)

-- Right cutoff: linear distance to ρ from vertical segment side
private def δ_R_rho (H : ℝ) : ℝ → ℝ := fun ε => ε / (H - Real.sqrt 3 / 2)

/-- Norm bounds: the curve is far from ρ outside the cutoff interval, and close inside. -/
private lemma pv_norm_bounds_rho (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    let g := fun t => fdBoundaryH H t - (ellipticPointRho : ℂ)
    let threshold := min (H - Real.sqrt 3 / 2) (2 * Real.sin (Real.pi / 12))
    (∀ ε : ℝ, 0 < ε → ε < threshold → ∀ t ∈ Ico (0 : ℝ) (3 - δ_L_rho ε), ε < ‖g t - 0‖) ∧
    (∀ ε : ℝ, 0 < ε → ε < threshold → ∀ t ∈ Ioc (3 + δ_R_rho H ε) (5 : ℝ), ε < ‖g t - 0‖) ∧
    (∀ ε : ℝ, 0 < ε → ε < threshold → ∀ t ∈ Icc (3 - δ_L_rho ε) (3 + δ_R_rho H ε),
      ‖g t - 0‖ ≤ ε) := by
  intro g threshold
  have hH_gap : 0 < H - Real.sqrt 3 / 2 := by linarith
  have hsin_pos : 0 < Real.sin (Real.pi / 12) :=
    ArcCalculus.sin_pos_of_mem_Ioo_zero_pi (by constructor <;> nlinarith [Real.pi_pos])
  have h2sin_pos : 0 < 2 * Real.sin (Real.pi / 12) := by positivity
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hthresh : 0 < threshold := lt_min hH_gap h2sin_pos
  have hε_aux : ∀ ε : ℝ, 0 < ε → ε < threshold →
      0 < ε / 2 ∧ ε / 2 ≤ 1 ∧ -1 ≤ ε / 2 ∧ 0 < Real.arcsin (ε / 2) ∧
      Real.arcsin (ε / 2) < Real.pi / 12 := by
    intro ε hε_pos hε_lt
    have hε_lt_gap : ε < H - Real.sqrt 3 / 2 := lt_of_lt_of_le hε_lt (min_le_left _ _)
    have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) := lt_of_lt_of_le hε_lt (min_le_right _ _)
    refine ⟨by linarith, ?_, by linarith, Real.arcsin_pos.mpr (by linarith), ?_⟩
    · have hsin_le : Real.sin (Real.pi / 12) ≤ 1 := Real.sin_le_one _; linarith
    · have hε_lt_sin : ε / 2 < Real.sin (Real.pi / 12) := by linarith
      calc Real.arcsin (ε / 2)
          < Real.arcsin (Real.sin (Real.pi / 12)) :=
            Real.arcsin_lt_arcsin (by linarith) hε_lt_sin (Real.sin_le_one _)
        _ = Real.pi / 12 := Real.arcsin_sin (by nlinarith) (by nlinarith)
  -- δ_L_rho positivity and bound
  have hδL_pos : ∀ ε : ℝ, 0 < ε → ε < threshold → 0 < δ_L_rho ε := by
    intro ε hε_pos hε_lt
    obtain ⟨_, _, _, harcsin_pos, _⟩ := hε_aux ε hε_pos hε_lt
    exact mul_pos (div_pos (by norm_num) hpi_pos) harcsin_pos
  have hδL_lt_one : ∀ ε : ℝ, 0 < ε → ε < threshold → δ_L_rho ε < 1 := by
    intro ε hε_pos hε_lt
    obtain ⟨_, _, _, _, harcsin_lt⟩ := hε_aux ε hε_pos hε_lt
    change 12 / Real.pi * Real.arcsin (ε / 2) < 1
    calc 12 / Real.pi * Real.arcsin (ε / 2)
        < 12 / Real.pi * (Real.pi / 12) :=
          mul_lt_mul_of_pos_left harcsin_lt (div_pos (by norm_num) hpi_pos)
      _ = 1 := by field_simp
  -- δ_R_rho positivity and bound
  have hδR_pos : ∀ ε : ℝ, 0 < ε → ε < threshold → 0 < δ_R_rho H ε := by
    intro ε hε_pos hε_lt; exact div_pos hε_pos hH_gap
  have hδR_lt_one : ∀ ε : ℝ, 0 < ε → ε < threshold → δ_R_rho H ε < 1 := by
    intro ε hε_pos hε_lt
    change ε / (H - Real.sqrt 3 / 2) < 1
    rw [div_lt_one hH_gap]; exact lt_of_lt_of_le hε_lt (min_le_left _ _)
  -- Angle bookkeeping
  have hδL_angle : ∀ ε : ℝ, 0 < ε → ε < threshold →
      δ_L_rho ε * Real.pi / 12 = Real.arcsin (ε / 2) := by
    intro ε hε_pos hε_lt
    change 12 / Real.pi * Real.arcsin (ε / 2) * Real.pi / 12 = Real.arcsin (ε / 2); field_simp
  -- Norm at left cutoff
  have h_norm_L : ∀ ε : ℝ, 0 < ε → ε < threshold →
      ‖fdBoundaryH H (3 - δ_L_rho ε) - ellipticPointRho‖ = ε := by
    intro ε hε_pos hε_lt
    obtain ⟨_, hε2_le, hε2_neg, _, _⟩ := hε_aux ε hε_pos hε_lt
    rw [g_norm_seg2 (hδL_pos ε hε_pos hε_lt) (hδL_lt_one ε hε_pos hε_lt),
        hδL_angle ε hε_pos hε_lt, Real.sin_arcsin hε2_neg hε2_le]; linarith
  -- Norm at right cutoff
  have h_norm_R : ∀ ε : ℝ, 0 < ε → ε < threshold →
      ‖fdBoundaryH H (3 + δ_R_rho H ε) - ellipticPointRho‖ = ε := by
    intro ε hε_pos hε_lt
    rw [g_norm_seg3 H hH (hδR_pos ε hε_pos hε_lt) (le_of_lt (hδR_lt_one ε hε_pos hε_lt))]
    exact div_mul_cancel₀ ε (ne_of_gt hH_gap)
  refine ⟨?_, ?_, ?_⟩
  -- h_far_left
  · intro ε hε_pos hε_lt t ⟨ht0, ht3⟩
    simp only [sub_zero]
    have hδL_p := hδL_pos ε hε_pos hε_lt
    have hδL_lt := hδL_lt_one ε hε_pos hε_lt
    have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) := lt_of_lt_of_le hε_lt (min_le_right _ _)
    have hε_lt_one : ε < 1 := by
      have hsin_bound : Real.sin (Real.pi / 12) < 1 / 2 := by
        calc Real.sin (Real.pi / 12) < Real.sin (Real.pi / 6) :=
              Real.sin_lt_sin_of_lt_of_le_pi_div_two (by nlinarith) (by nlinarith) (by nlinarith)
          _ = 1 / 2 := Real.sin_pi_div_six
      linarith
    have h_nL := h_norm_L ε hε_pos hε_lt
    rcases le_or_gt t 1 with ht1 | ht1
    · calc ε < 1 := hε_lt_one
          _ ≤ ‖g t‖ := g_norm_ge_one_seg0 ht0 ht1
    · have ht3' : t < 3 := by linarith
      rw [show g = fun t => fdBoundaryH H t - ellipticPointRho from rfl, g_norm_arc ht1 ht3']
      rw [← h_nL, g_norm_seg2 hδL_p hδL_lt]
      apply mul_lt_mul_of_pos_left _ (by norm_num : (0 : ℝ) < 2)
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (by nlinarith) (by nlinarith)
        (by nlinarith : δ_L_rho ε * Real.pi / 12 < (3 - t) * Real.pi / 12)
  -- h_far_right
  · intro ε hε_pos hε_lt t ⟨ht3, ht5⟩
    simp only [sub_zero]
    have hε_lt_gap : ε < H - Real.sqrt 3 / 2 := lt_of_lt_of_le hε_lt (min_le_left _ _)
    have hδR_p := hδR_pos ε hε_pos hε_lt
    have hδR_lt := hδR_lt_one ε hε_pos hε_lt
    have h_nR := h_norm_R ε hε_pos hε_lt
    rcases le_or_gt t 4 with ht4 | ht4
    · have h_t_eq : t = 3 + (t - 3) := by ring
      rw [show g = fun t => fdBoundaryH H t - ellipticPointRho from rfl, h_t_eq,
          g_norm_seg3 H hH (by linarith : 0 < t - 3) (by linarith : t - 3 ≤ 1)]
      rw [← h_nR, g_norm_seg3 H hH hδR_p (le_of_lt hδR_lt)]
      exact mul_lt_mul_of_pos_right (by linarith : δ_R_rho H ε < t - 3) hH_gap
    · calc ε < H - Real.sqrt 3 / 2 := hε_lt_gap
          _ ≤ ‖g t‖ := by
              rw [show g = fun t => fdBoundaryH H t - ellipticPointRho from rfl]
              exact g_norm_ge_seg4 H hH (le_of_lt ht4) ht5
  -- h_near
  · intro ε hε_pos hε_lt t ⟨ht_lo, ht_hi⟩
    simp only [sub_zero]
    exact not_lt.mp (norm_le_middle_rho H hH hε_pos
      (hδL_pos ε hε_pos hε_lt) (hδL_lt_one ε hε_pos hε_lt)
      (hδR_pos ε hε_pos hε_lt) (hδR_lt_one ε hε_pos hε_lt)
      (h_norm_L ε hε_pos hε_lt) (h_norm_R ε hε_pos hε_lt) hH_gap t ht_lo ht_hi)

/-- FTC API: far-segment integrals equal log difference; integrability. -/
private lemma pv_integrals_rho (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    let g := fun t => fdBoundaryH H t - (ellipticPointRho : ℂ)
    let threshold := min (H - Real.sqrt 3 / 2) (2 * Real.sin (Real.pi / 12))
    (∀ ε : ℝ, 0 < ε → ε < threshold →
      (∫ t in (0 : ℝ)..(3 - δ_L_rho ε), (g t - 0)⁻¹ * deriv g t) +
      (∫ t in (3 + δ_R_rho H ε)..(5 : ℝ), (g t - 0)⁻¹ * deriv g t) =
      Complex.log (g (3 - δ_L_rho ε)) - Complex.log (g (3 + δ_R_rho H ε))) ∧
    (∀ ε : ℝ, 0 < ε → ε < threshold →
      IntervalIntegrable (fun t => (g t - 0)⁻¹ * deriv g t) volume 0 (3 - δ_L_rho ε)) ∧
    (∀ ε : ℝ, 0 < ε → ε < threshold →
      IntervalIntegrable (fun t => (g t - 0)⁻¹ * deriv g t) volume (3 + δ_R_rho H ε) 5) := by
  intro g threshold
  have hH_gap : 0 < H - Real.sqrt 3 / 2 := by linarith
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hε_aux : ∀ ε : ℝ, 0 < ε → ε < threshold →
      Real.arcsin (ε / 2) < Real.pi / 12 := by
    intro ε hε_pos hε_lt
    have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) := lt_of_lt_of_le hε_lt (min_le_right _ _)
    have hε_lt_sin : ε / 2 < Real.sin (Real.pi / 12) := by linarith
    calc Real.arcsin (ε / 2)
        < Real.arcsin (Real.sin (Real.pi / 12)) :=
          Real.arcsin_lt_arcsin (by linarith) hε_lt_sin (Real.sin_le_one _)
      _ = Real.pi / 12 := Real.arcsin_sin (by nlinarith) (by nlinarith)
  have hδL_pos : ∀ ε : ℝ, 0 < ε → ε < threshold → 0 < δ_L_rho ε := by
    intro ε hε_pos hε_lt
    have harcsin_pos : 0 < Real.arcsin (ε / 2) :=
      Real.arcsin_pos.mpr (by linarith)
    exact mul_pos (div_pos (by norm_num) hpi_pos) harcsin_pos
  have hδL_lt_one : ∀ ε : ℝ, 0 < ε → ε < threshold → δ_L_rho ε < 1 := by
    intro ε hε_pos hε_lt
    change 12 / Real.pi * Real.arcsin (ε / 2) < 1
    calc 12 / Real.pi * Real.arcsin (ε / 2)
        < 12 / Real.pi * (Real.pi / 12) :=
          mul_lt_mul_of_pos_left (hε_aux ε hε_pos hε_lt) (div_pos (by norm_num) hpi_pos)
      _ = 1 := by field_simp
  have hδR_pos : ∀ ε : ℝ, 0 < ε → ε < threshold → 0 < δ_R_rho H ε := by
    intro ε hε_pos hε_lt; exact div_pos hε_pos hH_gap
  have hδR_lt_one : ∀ ε : ℝ, 0 < ε → ε < threshold → δ_R_rho H ε < 1 := by
    intro ε hε_pos hε_lt
    change ε / (H - Real.sqrt 3 / 2) < 1
    rw [div_lt_one hH_gap]; exact lt_of_lt_of_le hε_lt (min_le_left _ _)
  have key : ∀ t : ℝ, (g t - 0)⁻¹ * deriv g t = deriv g t / g t := by
    intro t; simp only [sub_zero, div_eq_mul_inv, mul_comm]
  refine ⟨?_, ?_, ?_⟩
  -- h_ftc_api
  · intro ε hε_pos hε_lt
    have h_ftc := ftc_logDeriv_telescope_rho H hH
      (hδL_pos ε hε_pos hε_lt) (hδL_lt_one ε hε_pos hε_lt)
      (hδR_pos ε hε_pos hε_lt) (hδR_lt_one ε hε_pos hε_lt)
    obtain ⟨_, _, h_telescope⟩ := h_ftc
    simp_rw [key]; exact h_telescope
  -- hint_left
  · intro ε hε_pos hε_lt
    have h_ftc := ftc_logDeriv_telescope_rho H hH
      (hδL_pos ε hε_pos hε_lt) (hδL_lt_one ε hε_pos hε_lt)
      (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1)
    simp_rw [key]; exact h_ftc.1
  -- hint_right
  · intro ε hε_pos hε_lt
    have h_ftc := ftc_logDeriv_telescope_rho H hH
      (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1)
      (hδR_pos ε hε_pos hε_lt) (hδR_lt_one ε hε_pos hε_lt)
    simp_rw [key]; exact h_ftc.2.1

/-- Helper: `log(g(3 - δ_L ε)) - log(g(3 + δ_R ε)) → -(I * π / 3)` as `ε → 0⁺`. -/
private lemma pv_log_limit_at_rho (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    let g := fun t => fdBoundaryH H t - (ellipticPointRho : ℂ)
    let δ_L : ℝ → ℝ := δ_L_rho
    let δ_R : ℝ → ℝ := δ_R_rho H
    Tendsto (fun ε => Complex.log (g (3 - δ_L ε)) - Complex.log (g (3 + δ_R ε)))
      (nhdsWithin 0 (Ioi 0)) (nhds (-(I * ↑Real.pi / 3))) := by
  intro g δ_L δ_R
  have hH_gap : 0 < H - Real.sqrt 3 / 2 := by linarith
  have hsin_pos : 0 < Real.sin (Real.pi / 12) :=
    ArcCalculus.sin_pos_of_mem_Ioo_zero_pi (by constructor <;> nlinarith [Real.pi_pos])
  have h2sin_pos : 0 < 2 * Real.sin (Real.pi / 12) := by positivity
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  set threshold := min (H - Real.sqrt 3 / 2) (2 * Real.sin (Real.pi / 12))
  have hthresh : 0 < threshold := lt_min hH_gap h2sin_pos
  have hε_aux : ∀ ε : ℝ, 0 < ε → ε < threshold →
      0 < ε / 2 ∧ ε / 2 ≤ 1 ∧ -1 ≤ ε / 2 ∧ 0 < Real.arcsin (ε / 2) ∧
      Real.arcsin (ε / 2) < Real.pi / 12 := by
    intro ε hε_pos hε_lt
    have hε_lt_gap : ε < H - Real.sqrt 3 / 2 := lt_of_lt_of_le hε_lt (min_le_left _ _)
    have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) := lt_of_lt_of_le hε_lt (min_le_right _ _)
    refine ⟨by linarith, ?_, by linarith, Real.arcsin_pos.mpr (by linarith), ?_⟩
    · have hsin_le : Real.sin (Real.pi / 12) ≤ 1 := Real.sin_le_one _; linarith
    · have hε_lt_sin : ε / 2 < Real.sin (Real.pi / 12) := by linarith
      calc Real.arcsin (ε / 2)
          < Real.arcsin (Real.sin (Real.pi / 12)) :=
            Real.arcsin_lt_arcsin (by linarith) hε_lt_sin (Real.sin_le_one _)
        _ = Real.pi / 12 := Real.arcsin_sin (by nlinarith) (by nlinarith)
  have hδL_pos : ∀ ε : ℝ, 0 < ε → ε < threshold → 0 < δ_L ε := by
    intro ε hε_pos hε_lt
    obtain ⟨_, _, _, harcsin_pos, _⟩ := hε_aux ε hε_pos hε_lt
    exact mul_pos (div_pos (by norm_num) hpi_pos) harcsin_pos
  have hδR_pos : ∀ ε : ℝ, 0 < ε → ε < threshold → 0 < δ_R ε := by
    intro ε hε_pos hε_lt; exact div_pos hε_pos hH_gap
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro r hr
  set ε₀ := min threshold r
  have hε₀_pos : 0 < ε₀ := lt_min hthresh hr
  refine ⟨ε₀, hε₀_pos, ?_⟩
  intro ε hε_mem hε_dist
  simp only [Set.mem_Ioi] at hε_mem
  rw [Real.dist_eq, sub_zero, abs_of_pos hε_mem] at hε_dist
  have hε_pos : 0 < ε := hε_mem
  have hε_lt : ε < threshold := lt_of_lt_of_le hε_dist (min_le_left _ _)
  have hε_lt_r : ε < r := lt_of_lt_of_le hε_dist (min_le_right _ _)
  have hδL_p := hδL_pos ε hε_pos hε_lt
  have hδR_p := hδR_pos ε hε_pos hε_lt
  obtain ⟨_, hε2_le, hε2_neg, _, harcsin_lt⟩ := hε_aux ε hε_pos hε_lt
  have hδL_lt_one : δ_L ε < 1 := by
    change 12 / Real.pi * Real.arcsin (ε / 2) < 1
    calc 12 / Real.pi * Real.arcsin (ε / 2)
        < 12 / Real.pi * (Real.pi / 12) :=
          mul_lt_mul_of_pos_left harcsin_lt (div_pos (by norm_num) hpi_pos)
      _ = 1 := by field_simp
  have hδR_lt_one : δ_R ε < 1 := by
    change ε / (H - Real.sqrt 3 / 2) < 1
    rw [div_lt_one hH_gap]; exact lt_of_lt_of_le hε_lt (min_le_left _ _)
  have hδL_angle : δ_L ε * Real.pi / 12 = Real.arcsin (ε / 2) := by
    change 12 / Real.pi * Real.arcsin (ε / 2) * Real.pi / 12 = Real.arcsin (ε / 2)
    field_simp
  have h_norm_L : ‖g (3 - δ_L ε)‖ = ε := by
    change ‖fdBoundaryH H (3 - δ_L ε) - ellipticPointRho‖ = ε
    rw [g_norm_seg2 hδL_p hδL_lt_one, hδL_angle, Real.sin_arcsin hε2_neg hε2_le]; linarith
  have h_norm_R : ‖g (3 + δ_R ε)‖ = ε := by
    change ‖fdBoundaryH H (3 + δ_R ε) - ellipticPointRho‖ = ε
    rw [g_norm_seg3 H hH hδR_p (le_of_lt hδR_lt_one)]
    exact div_mul_cancel₀ ε (ne_of_gt hH_gap)
  set zL := g (3 - δ_L ε)
  set zR := g (3 + δ_R ε)
  rw [show dist (Complex.log zL - Complex.log zR) (-(I * ↑Real.pi / 3)) =
      ‖Complex.log zL - Complex.log zR - (-(I * ↑Real.pi / 3))‖ from Complex.dist_eq _ _,
    ← Complex.re_add_im (Complex.log zL), ← Complex.re_add_im (Complex.log zR),
    Complex.log_re, Complex.log_re, Complex.log_im, Complex.log_im]
  change ‖zL‖ = ε at h_norm_L
  change ‖zR‖ = ε at h_norm_R
  rw [h_norm_L, h_norm_R]
  rw [arg_approach_rho_left_helper hδL_p hδL_lt_one,
      arg_approach_rho_right H hH hδR_p (le_of_lt hδR_lt_one)]
  have h_simp : ↑(Real.log ε) + ↑(Real.pi / 6 - δ_L ε * Real.pi / 12) * I -
      (↑(Real.log ε) + ↑(Real.pi / 2) * I) - -(I * ↑Real.pi / 3) =
      ↑(-(δ_L ε * Real.pi / 12)) * I := by push_cast; ring
  rw [h_simp, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
  have h_angle_bound : δ_L ε * Real.pi / 12 < ε := by
    have h_sin_eq : Real.sin (δ_L ε * Real.pi / 12) = ε / 2 := by
      linarith [h_norm_L ▸ g_norm_seg2 (H := H) hδL_p hδL_lt_one]
    set x := δ_L ε * Real.pi / 12 with hx_def
    have hx_pos : 0 < x := by positivity
    have hx_le_one : x ≤ 1 := by
      have : x < Real.pi / 12 := by nlinarith
      linarith [Real.pi_le_four]
    nlinarith [Real.sin_gt_sub_cube hx_pos hx_le_one, sq_nonneg x, sq_nonneg (1 - x)]
  linarith

/-- The PV integral of `(γ-ρ)⁻¹ γ'` over `[0,5]` with ε-ball cutoff tends to `-iπ/3`. -/
theorem pv_integral_at_rho_tendsto (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    Tendsto (fun ε => ∫ t in (0 : ℝ)..5, if ‖fdBoundaryH H t - ellipticPointRho‖ > ε
      then (fdBoundaryH H t - ellipticPointRho)⁻¹ *
           deriv (fun s => fdBoundaryH H s - ellipticPointRho) t
      else 0) (𝓝[>] 0) (𝓝 (-(I * ↑Real.pi / 3))) := by
  set g := fun t => fdBoundaryH H t - (ellipticPointRho : ℂ) with hg_def
  have hH_gap : 0 < H - Real.sqrt 3 / 2 := by linarith
  have hsin_pos : 0 < Real.sin (Real.pi / 12) :=
    ArcCalculus.sin_pos_of_mem_Ioo_zero_pi (by constructor <;> nlinarith [Real.pi_pos])
  have h2sin_pos : 0 < 2 * Real.sin (Real.pi / 12) := by positivity
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  -- Cutoff functions (using module-level defs for transparency)
  let δ_L : ℝ → ℝ := δ_L_rho
  let δ_R : ℝ → ℝ := δ_R_rho H
  set threshold := min (H - Real.sqrt 3 / 2) (2 * Real.sin (Real.pi / 12))
  have hthresh : 0 < threshold := lt_min hH_gap h2sin_pos
  -- δ_L positivity and smallness
  have hδL_pos : ∀ ε : ℝ, 0 < ε → ε < threshold → 0 < δ_L ε := by
    intro ε hε_pos hε_lt
    exact mul_pos (div_pos (by norm_num) hpi_pos)
      (Real.arcsin_pos.mpr (by linarith [lt_of_lt_of_le hε_lt (min_le_right _ _)]))
  have hδL_small : ∀ ε : ℝ, 0 < ε → ε < threshold → δ_L ε < (3 : ℝ) - 0 := by
    intro ε hε_pos hε_lt
    have harcsin_lt : Real.arcsin (ε / 2) < Real.pi / 12 := by
      have hε_lt_2sin := lt_of_lt_of_le hε_lt (min_le_right _ _)
      calc Real.arcsin (ε / 2) < Real.arcsin (Real.sin (Real.pi / 12)) :=
            Real.arcsin_lt_arcsin (by linarith) (by linarith) (Real.sin_le_one _)
        _ = Real.pi / 12 := Real.arcsin_sin (by nlinarith) (by nlinarith)
    simp only [sub_zero, δ_L, δ_L_rho]
    calc 12 / Real.pi * Real.arcsin (ε / 2)
        < 12 / Real.pi * (Real.pi / 12) :=
          mul_lt_mul_of_pos_left harcsin_lt (div_pos (by norm_num) hpi_pos)
      _ = 1 := by field_simp
      _ < 3 := by norm_num
  -- δ_R positivity and smallness
  have hδR_pos : ∀ ε : ℝ, 0 < ε → ε < threshold → 0 < δ_R ε :=
    fun ε hε_pos _ => div_pos hε_pos hH_gap
  have hδR_small : ∀ ε : ℝ, 0 < ε → ε < threshold → δ_R ε < (5 : ℝ) - 3 := by
    intro ε hε_pos hε_lt
    have hε_lt_gap : ε < H - Real.sqrt 3 / 2 := lt_of_lt_of_le hε_lt (min_le_left _ _)
    simp only [show (5 : ℝ) - 3 = 2 from by norm_num, δ_R, δ_R_rho]
    calc ε / (H - Real.sqrt 3 / 2) < 1 := by rw [div_lt_one hH_gap]; linarith
      _ < 2 := by norm_num
  -- Norm bounds and FTC from private lemmas
  obtain ⟨h_far_left, h_far_right, h_near⟩ := pv_norm_bounds_rho H hH
  obtain ⟨h_ftc_api, hint_left, hint_right⟩ := pv_integrals_rho H hH
  -- The limit
  have h_limit : Tendsto
      (fun ε => Complex.log (g (3 - δ_L ε)) - Complex.log (g (3 + δ_R ε)))
      (nhdsWithin 0 (Ioi 0)) (nhds (-(I * ↑Real.pi / 3))) :=
    pv_log_limit_at_rho H hH
  -- Apply the master asymmetric crossing limit theorem
  have h_tendsto := ContourIntegral.pv_tendsto_of_crossing_limit_asymmetric
    (γ := g) (a := 0) (b := 5) (s := 0) (L := -(I * ↑Real.pi / 3))
    (t₀ := 3) (by constructor <;> norm_num : (3 : ℝ) ∈ Ioo 0 5)
    (δ_left := δ_L) (δ_right := δ_R)
    hthresh hδL_pos hδR_pos hδL_small hδR_small
    h_far_left h_far_right h_near
    (E := fun ε => Complex.log (g (3 - δ_L ε)) - Complex.log (g (3 + δ_R ε)))
    h_ftc_api hint_left hint_right h_limit
  have h_eq : (fun ε => ∫ t in (0 : ℝ)..5,
      if ‖fdBoundaryH H t - ellipticPointRho‖ > ε
      then (fdBoundaryH H t - ellipticPointRho)⁻¹ *
           deriv (fun s => fdBoundaryH H s - ellipticPointRho) t
      else 0) = (fun ε => ∫ t in (0 : ℝ)..5,
      if ‖g t - 0‖ > ε then (g t - 0)⁻¹ * deriv g t else 0) := by
    funext ε; congr 1; funext t; simp only [hg_def, sub_zero]
  rw [h_eq]
  exact h_tendsto

/-- `generalizedWindingNumber' (fdBoundaryH H) 0 5 ρ = -1/6`. -/
theorem gWN_fdBoundary_H_at_rho (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    generalizedWindingNumber' (fdBoundaryH H) 0 5 ellipticPointRho = -1/6 := by
  apply ContourIntegral.gWN_eq_neg_sixth_of_pv_tendsto
  convert pv_integral_at_rho_tendsto H hH using 2
  · simp [sub_zero, gt_iff_lt]
  · ring

end
