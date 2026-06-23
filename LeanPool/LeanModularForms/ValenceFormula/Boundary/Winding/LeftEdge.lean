/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.Boundary.Winding.RightEdge
import LeanPool.LeanModularForms.ContourIntegral.WindingNumber
import LeanPool.LeanModularForms.ContourIntegral.CrossingLimit

/-!
# Generalized Winding Number at Left Edge Points

Proves `generalizedWindingNumber' (fdBoundaryH H) 0 5 s = -1/2` for points `s`
on the left vertical edge of the fundamental domain (`s.re = -1/2`, `√3/2 < s.im < H`).
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

attribute [local instance] Classical.propDecidable

noncomputable section

private lemma leftEdge_t₀_mem_Ioo (H : ℝ) (_hH_sqrt : Real.sqrt 3 / 2 < H) (s : ℂ)
    (hs_im_lower : Real.sqrt 3 / 2 < s.im) (hs_im : s.im < H) :
    3 + (s.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) ∈ Ioo (3 : ℝ) 4 := by
  have hα_pos : 0 < H - Real.sqrt 3 / 2 := by linarith
  constructor
  · linarith [div_pos (by linarith : (0 : ℝ) < s.im - Real.sqrt 3 / 2) hα_pos]
  · have : (s.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) < 1 :=
      (div_lt_one hα_pos).mpr (by linarith)
    linarith

private lemma leftEdge_h₃_eq {H : ℝ} {s : ℂ} (hs_re : s.re = -1 / 2) (t : ℝ) :
    fdBoundarySeg4H H t - s =
      ↑(Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2) - s.im) * I := by
  simp only [fdBoundarySeg4H]
  apply Complex.ext <;>
    simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, hs_re]

private lemma leftEdge_dist_from_rightVertical (s : ℂ) (hs_re : s.re = -1 / 2)
    (z : ℂ) (hz_re : z.re = 1 / 2) : 1 ≤ ‖z - s‖ := by
  have hre : (z - s).re = 1 := by simp [Complex.sub_re, hz_re, hs_re]; ring
  calc 1 = |(z - s).re| := by rw [hre]; norm_num
    _ ≤ ‖z - s‖ := abs_re_le_norm (z - s)

private lemma leftEdge_min_dist_pos (s : ℂ) (hs_norm : ‖s‖ > 1) (hs_im : s.im < H) :
    0 < min (min (‖s‖ - 1) 1) (H - s.im) :=
  lt_min (lt_min (by linarith) one_pos) (by linarith)

private lemma leftEdge_min_dist_from_non_seg4 (H : ℝ) (s : ℂ) (hs_re : s.re = -1 / 2)
    (_hs_norm : ‖s‖ > 1) (_hs_im : s.im < H) (t : ℝ) (ht_seg4_left : t ≤ 3)
    (_ht_upper : t ≤ 5) :
    min (min (‖s‖ - 1) 1) (H - s.im) ≤ ‖fdBoundaryH H t - s‖ := by
  set d := min (min (‖s‖ - 1) 1) (H - s.im)
  by_cases h1 : t ≤ 1
  · rw [fdBoundary_H_eq_seg1_H h1]
    calc d ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
      _ ≤ _ := leftEdge_dist_from_rightVertical s hs_re _
              (by simp [fdBoundarySeg1H, Complex.add_re, Complex.mul_re,
                Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im])
  · push Not at h1
    by_cases h3 : t ≤ 3
    · have h_on_arc : ‖fdBoundaryH H t‖ = 1 := by
        by_cases h2 : t ≤ 2
        · rw [fdBoundary_H_eq_seg2_H H h1 h2]
          simp only [fdBoundarySeg2H, fdBoundarySeg2]
          rw [show (↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
              ↑(Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I from by push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I _
        · push Not at h2
          rw [fdBoundary_H_eq_seg3_H H h2 h3]
          simp only [fdBoundarySeg3H, fdBoundarySeg3]
          rw [show (↑Real.pi / 2 + (↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
              ↑(Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I
              from by push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I _
      calc d ≤ ‖s‖ - 1 := le_trans (min_le_left _ _) (min_le_left _ _)
        _ ≤ _ := rightEdge_dist_from_arc s _ h_on_arc
    · exact absurd ht_seg4_left h3

private lemma leftEdge_min_dist_from_non_seg4_right (H : ℝ) (s : ℂ) (_hs_re : s.re = -1 / 2)
    (_hs_norm : ‖s‖ > 1) (hs_im : s.im < H) (t : ℝ) (ht4 : 4 < t) (_ht5 : t ≤ 5) :
    min (min (‖s‖ - 1) 1) (H - s.im) ≤ ‖fdBoundaryH H t - s‖ := by
  rw [fdBoundary_H_eq_seg5_H ht4]
  have him : (fdBoundarySeg5H H t - s).im = H - s.im := by
    simp [fdBoundarySeg5H, Complex.sub_im, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  calc min (min (‖s‖ - 1) 1) (H - s.im)
      ≤ H - s.im := min_le_right _ _
    _ = |(fdBoundarySeg5H H t - s).im| := by rw [him]; exact (abs_of_pos (by linarith)).symm
    _ ≤ ‖fdBoundarySeg5H H t - s‖ := Complex.abs_im_le_norm _

private lemma leftEdge_final_log (H : ℝ) (s : ℂ)
    (hs_re : s.re = -1 / 2) (α : ℝ) (hα_def : α = H - Real.sqrt 3 / 2)
    (δ : ℝ) (hδ_pos : 0 < δ) (hα_pos : 0 < α)
    (t₀ : ℝ) (ht₀_mul : (t₀ - 3) * α = s.im - Real.sqrt 3 / 2) :
    Complex.log (fdBoundarySeg4H H (t₀ - δ) - s) -
    Complex.log (fdBoundarySeg4H H (t₀ + δ) - s) = -(↑Real.pi * I) := by
  have hval_minus : fdBoundarySeg4H H (t₀ - δ) - s = ↑(-(δ * α)) * I := by
    rw [leftEdge_h₃_eq hs_re]
    have h_expand : (t₀ - δ - 3) * (H - Real.sqrt 3 / 2) = (t₀ - 3) * α - δ * α := by
      rw [hα_def]; ring
    have h_eq' : Real.sqrt 3 / 2 + (t₀ - δ - 3) * (H - Real.sqrt 3 / 2) - s.im = -(δ * α) := by
      rw [h_expand]; linarith [ht₀_mul]
    rw [h_eq']
  have hval_plus : fdBoundarySeg4H H (t₀ + δ) - s = ↑(δ * α) * I := by
    rw [leftEdge_h₃_eq hs_re]
    have h_expand : (t₀ + δ - 3) * (H - Real.sqrt 3 / 2) = (t₀ - 3) * α + δ * α := by
      rw [hα_def]; ring
    have h_eq' : Real.sqrt 3 / 2 + (t₀ + δ - 3) * (H - Real.sqrt 3 / 2) - s.im = δ * α := by
      rw [h_expand]; linarith [ht₀_mul]
    rw [h_eq']
  rw [hval_minus, hval_plus]
  rw [show (↑(-(δ * α)) * I : ℂ) = -(↑(δ * α) * I) from by push_cast; ring]
  exact log_neg_rI_sub_log_rI (mul_pos hδ_pos hα_pos)

private lemma leftEdge_slit_seg1 (s : ℂ) (hs_re : s.re = -1 / 2)
    (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1) :
    fdBoundarySeg1H H t - s ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  simp only [fdBoundarySeg1H, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero]
  rw [hs_re]; norm_num

private lemma leftEdge_slit_arc (s : ℂ) (hs_re : s.re = -1 / 2)
    (hs_im_lower : Real.sqrt 3 / 2 < s.im) (t : ℝ) (ht1 : 1 ≤ t) (ht3 : t ≤ 3) :
    exp (↑(Real.pi * (1 + t) / 6) * I) - s ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  set θ := Real.pi * (1 + t) / 6 with hθ_def
  have hθ_lower : Real.pi / 3 ≤ θ := by simp only [hθ_def]; nlinarith [Real.pi_pos]
  have hθ_upper : θ ≤ 2 * Real.pi / 3 := by simp only [hθ_def]; nlinarith [Real.pi_pos]
  by_cases h3_eq : t = 3
  · right
    subst h3_eq
    change (cexp (↑(Real.pi * (1 + 3) / 6) * I) - s).im ≠ 0
    rw [show Real.pi * (1 + 3) / 6 = 2 * Real.pi / 3 from by ring,
        exp_real_angle_I, cos_two_pi_div_three, sin_two_pi_div_three]
    simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
    linarith [hs_im_lower]
  · left
    have ht3_strict : t < 3 := lt_of_le_of_ne ht3 h3_eq
    have hθ_strict : θ < 2 * Real.pi / 3 := by simp only [hθ_def]; nlinarith [Real.pi_pos]
    change 0 < (cexp (↑θ * I) - s).re
    simp only [Complex.sub_re, exp_ofReal_mul_I_re]
    rw [hs_re]
    have hcos_gt : Real.cos θ > -(1 / 2) := by
      have h := Real.cos_lt_cos_of_nonneg_of_le_pi
        (le_of_lt (by nlinarith [Real.pi_pos])) (by nlinarith [Real.pi_pos]) hθ_strict
      rw [cos_two_pi_div_three] at h; linarith
    linarith

private lemma leftEdge_slit_seg4_left (H : ℝ) (s : ℂ) (hs_re : s.re = -1 / 2)
    (α : ℝ) (hα_def : α = H - Real.sqrt 3 / 2) (hα_pos : 0 < α)
    (t₀ : ℝ) (ht₀_mul : (t₀ - 3) * α = s.im - Real.sqrt 3 / 2)
    (δ' : ℝ) (hδ' : 0 < δ') (_hδ't₀ : δ' < t₀ - 3)
    (t : ℝ) (_ht3 : 3 ≤ t) (htd : t ≤ t₀ - δ') :
    fdBoundarySeg4H H t - s ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; right
  show (fdBoundarySeg4H H t - s).im ≠ 0
  rw [leftEdge_h₃_eq hs_re]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
  have : (t - 3) * α < s.im - Real.sqrt 3 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right (show t - 3 ≤ t₀ - δ' - 3 from by linarith)
               (le_of_lt hα_pos), mul_pos hδ' hα_pos, ht₀_mul]
  rw [hα_def] at this; intro h; linarith

private lemma leftEdge_slit_seg4_right (H : ℝ) (s : ℂ) (hs_re : s.re = -1 / 2)
    (α : ℝ) (hα_def : α = H - Real.sqrt 3 / 2) (hα_pos : 0 < α)
    (t₀ : ℝ) (ht₀_mul : (t₀ - 3) * α = s.im - Real.sqrt 3 / 2)
    (δ' : ℝ) (hδ' : 0 < δ') (_hδ'4 : δ' < 4 - t₀)
    (t : ℝ) (htd : t₀ + δ' ≤ t) (_ht4 : t ≤ 4) :
    fdBoundarySeg4H H t - s ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; right
  show (fdBoundarySeg4H H t - s).im ≠ 0
  rw [leftEdge_h₃_eq hs_re]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
  have : (t - 3) * α > s.im - Real.sqrt 3 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right (show t₀ + δ' - 3 ≤ t - 3 from by linarith)
               (le_of_lt hα_pos), mul_pos hδ' hα_pos, ht₀_mul]
  rw [hα_def] at this; intro h; linarith

private lemma leftEdge_slit_seg5 (H : ℝ) (s : ℂ) (hs_re : s.re = -1 / 2)
    (hs_im : s.im < H) (t : ℝ) (ht4 : 4 ≤ t) (ht5 : t ≤ 5) :
    fdBoundarySeg5H H t - s ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  simp only [fdBoundarySeg5H]
  by_cases ht4_eq : t = 4
  · right
    subst ht4_eq
    simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    linarith
  · left
    have : 4 < t := lt_of_le_of_ne ht4 (Ne.symm ht4_eq)
    simp only [sub_re, add_re, ofReal_re, div_ofNat_re, re_ofNat, mul_re, I_re, mul_zero, ofReal_im,
      I_im, mul_one, sub_self, add_zero, sub_pos, gt_iff_lt]
    rw [hs_re]; linarith

private lemma leftEdge_norm_gt_of_seg4_left (H : ℝ) (s : ℂ) (hs_re : s.re = -1 / 2)
    (α : ℝ) (hα_pos : 0 < α) (hα_def : α = H - Real.sqrt 3 / 2)
    (t₀ : ℝ) (ht₀_mul : (t₀ - 3) * α = s.im - Real.sqrt 3 / 2)
    (ε : ℝ) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_def : δ = ε / α)
    (t : ℝ) (ht3 : 3 < t) (ht4 : t ≤ 4) (ht_lt_t₀mδ : t < t₀ - δ) :
    ‖fdBoundaryH H t - s‖ > ε := by
  rw [fdBoundary_H_eq_seg4_H ht3 ht4, leftEdge_h₃_eq hs_re]
  rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  have h_im_neg : Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2) - s.im < 0 := by
    have : (t - 3) * α < (t₀ - δ - 3) * α := mul_lt_mul_of_pos_right (by linarith) hα_pos
    have : (t₀ - δ - 3) * α = (t₀ - 3) * α - δ * α := by ring
    have := mul_pos hδ_pos hα_pos; rw [hα_def] at *; linarith [ht₀_mul]
  rw [abs_of_neg h_im_neg]
  have hε_eq : ε = δ * α := by rw [hδ_def]; field_simp
  have : (t - 3) * α < (t₀ - δ - 3) * α := mul_lt_mul_of_pos_right (by linarith) hα_pos
  have : (t₀ - δ - 3) * α = (t₀ - 3) * α - δ * α := by ring
  rw [hα_def] at *; linarith [ht₀_mul]

private lemma leftEdge_norm_gt_of_seg4_right (H : ℝ) (s : ℂ) (hs_re : s.re = -1 / 2)
    (α : ℝ) (hα_pos : 0 < α) (hα_def : α = H - Real.sqrt 3 / 2)
    (t₀ : ℝ) (ht₀_mul : (t₀ - 3) * α = s.im - Real.sqrt 3 / 2)
    (ε : ℝ) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_def : δ = ε / α)
    (t : ℝ) (ht3 : 3 < t) (ht4 : t ≤ 4) (ht_gt_t₀pδ : t₀ + δ < t) :
    ‖fdBoundaryH H t - s‖ > ε := by
  rw [fdBoundary_H_eq_seg4_H ht3 ht4, leftEdge_h₃_eq hs_re]
  rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
    show H - Real.sqrt 3 / 2 = α from hα_def.symm]
  have hε_eq : ε = δ * α := by rw [hδ_def]; exact (div_mul_cancel₀ ε (ne_of_gt hα_pos)).symm
  have h_im_pos : Real.sqrt 3 / 2 + (t - 3) * α - s.im > 0 := by nlinarith [ht₀_mul]
  rw [abs_of_pos h_im_pos]; nlinarith [ht₀_mul]

private lemma leftEdge_norm_le_of_near_crossing (H : ℝ) (s : ℂ) (hs_re : s.re = -1 / 2)
    (α : ℝ) (hα_pos : 0 < α) (hα_def : α = H - Real.sqrt 3 / 2)
    (t₀ : ℝ) (_ht₀_gt3 : 3 < t₀) (ht₀_mul : (t₀ - 3) * α = s.im - Real.sqrt 3 / 2)
    (ε : ℝ) (δ : ℝ) (hδ_def : δ = ε / α)
    (hδ_lt_t₀m3 : δ < t₀ - 3) (hεα_lt_4mt₀ : δ < 4 - t₀)
    (t : ℝ) (ht_mem : t ∈ Ioc (t₀ - δ) (t₀ + δ)) :
    ‖fdBoundaryH H t - s‖ ≤ ε := by
  rw [fdBoundary_H_eq_seg4_H (by linarith [ht_mem.1]) (by linarith [ht_mem.2])]
  rw [leftEdge_h₃_eq hs_re]
  rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_le,
    show H - Real.sqrt 3 / 2 = α from hα_def.symm]
  have hε_eq : ε = δ * α := by rw [hδ_def]; exact (div_mul_cancel₀ ε (ne_of_gt hα_pos)).symm
  have h_tα_upper : (t - 3) * α ≤ (t₀ + δ - 3) * α :=
    mul_le_mul_of_nonneg_right (by linarith [ht_mem.2]) (le_of_lt hα_pos)
  have h_tα_lower : (t₀ - δ - 3) * α < (t - 3) * α :=
    mul_lt_mul_of_pos_right (by linarith [ht_mem.1]) hα_pos
  constructor <;> nlinarith [ht₀_mul]

/-- From `t` in the open-interval `uIoc a b` minus its endpoints, get strict bounds. -/
private lemma mem_Ioo_of_uIoc_sdiff_endpoints {a b t : ℝ} (hab : a ≤ b)
    (ht_ne : t ∈ ({a, b} : Set ℝ)ᶜ) (ht_mem : t ∈ Set.uIoc a b) : a < t ∧ t < b := by
  rw [Set.uIoc_of_le hab] at ht_mem
  refine ⟨?_, ?_⟩
  · rcases eq_or_lt_of_le (le_of_lt ht_mem.1) with h | h
    · exact absurd (by simp only [mem_insert_iff, mem_singleton_iff]; left; linarith) ht_ne
    · exact h
  · rcases eq_or_lt_of_le ht_mem.2 with h | h
    · exact absurd (by simp only [mem_insert_iff, mem_singleton_iff]; right; linarith) ht_ne
    · exact h

private lemma ae_endpoints_compl (a b : ℝ) : ({a, b} : Set ℝ)ᶜ ∈ ae volume :=
  mem_ae_iff.mpr (by rw [compl_compl]; exact (Set.toFinite ({a, b} : Set ℝ)).measure_zero volume)

private lemma leftEdge_ae_seg_eq (g h₀ h_arc h₃ h₅ : ℝ → ℂ)
    (hg_h₀ : ∀ t, t ≤ 1 → g t = h₀ t)
    (hg_arc : ∀ t, 1 < t → t < 3 → g t = h_arc t)
    (hg_h₃ : ∀ t, 3 < t → t ≤ 4 → g t = h₃ t)
    (hg_h₅ : ∀ t, 4 < t → g t = h₅ t)
    (hderiv_01 : ∀ t ∈ Ioo (0 : ℝ) 1, deriv g t = deriv h₀ t)
    (hderiv_arc : ∀ t ∈ Ioo (1 : ℝ) 3, deriv g t = deriv h_arc t)
    (hderiv_3 : ∀ t ∈ Ioo (3 : ℝ) 4, deriv g t = deriv h₃ t)
    (hderiv_5 : ∀ t ∈ Ioo (4 : ℝ) 5, deriv g t = deriv h₅ t) :
    (∀ᵐ t ∂volume, t ∈ Set.uIoc 0 1 → deriv h₀ t / h₀ t = deriv g t / g t) ∧
    (∀ᵐ t ∂volume, t ∈ Set.uIoc 1 3 → deriv h_arc t / h_arc t = deriv g t / g t) ∧
    (∀ a b : ℝ, 3 ≤ a → a < b → b ≤ 4 →
      ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → deriv h₃ t / h₃ t = deriv g t / g t) ∧
    (∀ᵐ t ∂volume, t ∈ Set.uIoc 4 5 → deriv h₅ t / h₅ t = deriv g t / g t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [ae_endpoints_compl 0 1] with t ht_ne ht_mem
    obtain ⟨ht0, ht1⟩ := mem_Ioo_of_uIoc_sdiff_endpoints (by norm_num) ht_ne ht_mem
    rw [hg_h₀ t (le_of_lt ht1), hderiv_01 t ⟨ht0, ht1⟩]
  · filter_upwards [ae_endpoints_compl 1 3] with t ht_ne ht_mem
    obtain ⟨ht1, ht3⟩ := mem_Ioo_of_uIoc_sdiff_endpoints (by norm_num) ht_ne ht_mem
    rw [hg_arc t ht1 ht3, hderiv_arc t ⟨ht1, ht3⟩]
  · intro a b ha_ge hab hb4
    filter_upwards [ae_endpoints_compl a b] with t ht_ne ht_mem
    obtain ⟨ht_gt_a, ht_lt_b⟩ := mem_Ioo_of_uIoc_sdiff_endpoints (le_of_lt hab) ht_ne ht_mem
    rw [hg_h₃ t (by linarith) (by linarith), hderiv_3 t ⟨by linarith, by linarith⟩]
  · filter_upwards [ae_endpoints_compl 4 5] with t ht_ne ht_mem
    obtain ⟨ht4, ht5⟩ := mem_Ioo_of_uIoc_sdiff_endpoints (by norm_num) ht_ne ht_mem
    rw [hg_h₅ t ht4, hderiv_5 t ⟨ht4, ht5⟩]

private lemma leftEdge_norm_gt_left (H : ℝ) (s : ℂ) (hs_re : s.re = -1 / 2)
    (hs_norm : ‖s‖ > 1) (hs_im : s.im < H)
    (α : ℝ) (hα_pos : 0 < α) (hα_def : α = H - Real.sqrt 3 / 2)
    (t₀ : ℝ) (ht₀_lt4 : t₀ < 4) (ht₀_mul : (t₀ - 3) * α = s.im - Real.sqrt 3 / 2)
    (ε : ℝ) (_hε_pos : 0 < ε) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_def : δ = ε / α)
    (hεα_lt_t₀m3 : δ < t₀ - 3)
    (hε_lt_d : ε < min (min (‖s‖ - 1) 1) (H - s.im))
    (t : ℝ) (ht_mem : t ∈ Ioc (0 : ℝ) (t₀ - δ)) (ht_ne_right : t ≠ t₀ - δ) :
    ‖fdBoundaryH H t - s‖ > ε := by
  set d := min (min (‖s‖ - 1) 1) (H - s.im)
  by_cases ht3 : t ≤ 3
  · have : d ≤ ‖fdBoundaryH H t - s‖ :=
      leftEdge_min_dist_from_non_seg4 H s hs_re hs_norm hs_im t ht3 (by linarith)
    linarith [hε_lt_d]
  · push Not at ht3
    have ht_lt_t₀mδ : t < t₀ - δ :=
      lt_of_le_of_ne ht_mem.2 ht_ne_right
    exact leftEdge_norm_gt_of_seg4_left H s hs_re α hα_pos hα_def t₀ ht₀_mul ε δ hδ_pos
      hδ_def t ht3 (by linarith [ht_mem.2]) ht_lt_t₀mδ

private lemma leftEdge_norm_gt_right (H : ℝ) (s : ℂ) (hs_re : s.re = -1 / 2)
    (hs_norm : ‖s‖ > 1) (hs_im : s.im < H)
    (α : ℝ) (hα_pos : 0 < α) (hα_def : α = H - Real.sqrt 3 / 2)
    (t₀ : ℝ) (ht₀_gt3 : 3 < t₀) (_ht₀_lt4 : t₀ < 4)
    (ht₀_mul : (t₀ - 3) * α = s.im - Real.sqrt 3 / 2)
    (ε : ℝ) (_hε_pos : 0 < ε) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_def : δ = ε / α)
    (_hεα_lt_4mt₀ : δ < 4 - t₀)
    (hε_lt_d : ε < min (min (‖s‖ - 1) 1) (H - s.im))
    (t : ℝ) (ht_mem : t ∈ Ioc (t₀ + δ) 5) :
    ‖fdBoundaryH H t - s‖ > ε := by
  set d := min (min (‖s‖ - 1) 1) (H - s.im)
  by_cases ht4 : t ≤ 4
  · exact leftEdge_norm_gt_of_seg4_right H s hs_re α hα_pos hα_def t₀ ht₀_mul ε δ hδ_pos
      hδ_def t (by linarith [ht_mem.1]) ht4 ht_mem.1
  · push Not at ht4
    have : d ≤ ‖fdBoundaryH H t - s‖ :=
      leftEdge_min_dist_from_non_seg4_right H s hs_re hs_norm hs_im t ht4 ht_mem.2
    linarith [hε_lt_d]

private lemma leftEdge_h_far (H : ℝ) (_hH_sqrt : Real.sqrt 3 / 2 < H)
    (s : ℂ) (hs_re : s.re = -1 / 2) (hs_norm : ‖s‖ > 1) (hs_im : s.im < H)
    (α : ℝ) (hα_pos : 0 < α) (hα_def : α = H - Real.sqrt 3 / 2)
    (t₀ : ℝ) (ht₀_gt3 : 3 < t₀) (ht₀_lt4 : t₀ < 4)
    (ht₀_mul : (t₀ - 3) * α = s.im - Real.sqrt 3 / 2)
    (threshold : ℝ) (_hthresh : 0 < threshold)
    (hthresh_le_d : threshold ≤ min (min (‖s‖ - 1) 1) (H - s.im))
    (hthresh_le_t₀m3α : threshold ≤ (t₀ - 3) * α)
    (hthresh_le_4mt₀α : threshold ≤ (4 - t₀) * α) :
    ∀ ε, 0 < ε → ε < threshold → ∀ t ∈ Icc (0 : ℝ) 5, ε / α < |t - t₀| →
      ε < ‖fdBoundaryH H t - s‖ := by
  intro ε hε_pos hε_lt t ht_mem h_abs
  have hδ_pos : 0 < ε / α := div_pos hε_pos hα_pos
  have hεα_lt_t₀m3 : ε / α < t₀ - 3 :=
    (div_lt_iff₀ hα_pos).mpr (hε_lt.trans_le hthresh_le_t₀m3α)
  have hεα_lt_4mt₀ : ε / α < 4 - t₀ :=
    (div_lt_iff₀ hα_pos).mpr (hε_lt.trans_le hthresh_le_4mt₀α)
  have hε_lt_d : ε < min (min (‖s‖ - 1) 1) (H - s.im) := hε_lt.trans_le hthresh_le_d
  -- Since h_abs : ε/α < |t - t₀|, t is strictly to the left or right of the window
  rw [abs_sub_comm] at h_abs
  rcases lt_or_ge t (t₀ - ε / α) with h_left | h_right
  · -- t < t₀ - δ
    rcases eq_or_lt_of_le ht_mem.1 with h_t0 | h_t0
    · -- t = 0: use min_dist bound directly (seg1 case)
      have : min (min (‖s‖ - 1) 1) (H - s.im) ≤ ‖fdBoundaryH H t - s‖ :=
        leftEdge_min_dist_from_non_seg4 H s hs_re hs_norm hs_im t (by linarith [h_left,
          hεα_lt_t₀m3]) (by linarith [h_left, hεα_lt_4mt₀])
      linarith [hε_lt_d]
    · apply leftEdge_norm_gt_left H s hs_re hs_norm hs_im α hα_pos hα_def t₀ ht₀_lt4 ht₀_mul ε
        hε_pos (ε / α) hδ_pos rfl hεα_lt_t₀m3 hε_lt_d t ⟨h_t0, le_of_lt h_left⟩
      exact ne_of_lt h_left
  · -- h_right : t₀ - ε/α ≤ t, h_abs : ε/α < |t₀ - t|
    -- Derive t > t₀ + ε/α (strict): since t ≥ t₀ - ε/α and |t₀ - t| > ε/α
    have ht_gt : t₀ + ε / α < t := by
      rcases le_or_gt t₀ t with h | h
      · -- t ≥ t₀, so |t₀ - t| = t - t₀ > ε/α
        rw [abs_of_nonpos (by linarith)] at h_abs; linarith
      · -- t < t₀, so |t₀ - t| = t₀ - t ≤ ε/α (from h_right), but h_abs says > ε/α
        rw [abs_of_pos (by linarith)] at h_abs; linarith
    apply leftEdge_norm_gt_right H s hs_re hs_norm hs_im α hα_pos hα_def t₀ ht₀_gt3 ht₀_lt4
      ht₀_mul ε hε_pos (ε / α) hδ_pos rfl hεα_lt_4mt₀ hε_lt_d t ⟨ht_gt, ht_mem.2⟩

private lemma leftEdge_h_near (H : ℝ) (_hH_sqrt : Real.sqrt 3 / 2 < H)
    (s : ℂ) (hs_re : s.re = -1 / 2)
    (α : ℝ) (hα_pos : 0 < α) (hα_def : α = H - Real.sqrt 3 / 2)
    (t₀ : ℝ) (ht₀_gt3 : 3 < t₀) (_ht₀_lt4 : t₀ < 4)
    (ht₀_mul : (t₀ - 3) * α = s.im - Real.sqrt 3 / 2)
    (threshold : ℝ)
    (hthresh_le_t₀m3α : threshold ≤ (t₀ - 3) * α)
    (hthresh_le_4mt₀α : threshold ≤ (4 - t₀) * α) :
    ∀ ε, 0 < ε → ε < threshold → ∀ t, |t - t₀| ≤ ε / α → ‖fdBoundaryH H t - s‖ ≤ ε := by
  intro ε hε_pos _hε_lt t h_abs
  have hδ_pos : 0 < ε / α := div_pos hε_pos hα_pos
  have hδ_def : ε / α = ε / α := rfl
  have hεα_lt_t₀m3 : ε / α < t₀ - 3 :=
    (div_lt_iff₀ hα_pos).mpr (_hε_lt.trans_le hthresh_le_t₀m3α)
  have hεα_lt_4mt₀ : ε / α < 4 - t₀ :=
    (div_lt_iff₀ hα_pos).mpr (_hε_lt.trans_le hthresh_le_4mt₀α)
  rw [abs_le] at h_abs
  have ht_lower : t₀ - ε / α ≤ t := by linarith [h_abs.1]
  have ht_upper : t ≤ t₀ + ε / α := by linarith [h_abs.2]
  rcases eq_or_lt_of_le ht_lower with h_eq | h_lt
  · -- t = t₀ - δ: boundary case
    rw [← h_eq]
    rw [fdBoundary_H_eq_seg4_H (by linarith [hεα_lt_t₀m3]) (by linarith [hεα_lt_4mt₀]),
        leftEdge_h₃_eq hs_re]
    simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    have hea : ε / α * α = ε := div_mul_cancel₀ ε (ne_of_gt hα_pos)
    have hα_eq : H - Real.sqrt 3 / 2 = α := hα_def.symm
    have key : Real.sqrt 3 / 2 + (t₀ - ε / α - 3) * α - s.im = -(ε / α) * α := by
      have expand : (t₀ - ε / α - 3) * α = (t₀ - 3) * α - ε / α * α := by ring
      linarith [ht₀_mul]
    have : Real.sqrt 3 / 2 + (t₀ - ε / α - 3) * (H - Real.sqrt 3 / 2) - s.im = -(ε / α) * α := by
      rw [hα_eq]; exact key
    rw [this, show (-(ε / α) * α) = -ε from by linarith [neg_mul (ε / α) α, hea],
      abs_neg, abs_of_pos hε_pos]
  · exact leftEdge_norm_le_of_near_crossing H s hs_re α hα_pos hα_def t₀ ht₀_gt3 ht₀_mul ε
      (ε / α) hδ_def hεα_lt_t₀m3 hεα_lt_4mt₀ t ⟨h_lt, ht_upper⟩

/-- FTC telescope for the left edge: the sum of far-segment integrals equals
the log difference at the crossing point. Also returns integrability. -/
private lemma leftEdge_ftc_telescope (H : ℝ) (_hH_sqrt : Real.sqrt 3 / 2 < H)
    (s : ℂ) (hs_re : s.re = -1 / 2) (_hs_norm : ‖s‖ > 1)
    (hs_im_lower : Real.sqrt 3 / 2 < s.im) (hs_im : s.im < H)
    (α : ℝ) (hα_pos : 0 < α) (hα_def : α = H - Real.sqrt 3 / 2)
    (t₀ : ℝ) (_ht₀_gt3 : 3 < t₀) (_ht₀_lt4 : t₀ < 4)
    (ht₀_mul : (t₀ - 3) * α = s.im - Real.sqrt 3 / 2)
    (threshold : ℝ) (_hthresh : 0 < threshold)
    (hthresh_le_t₀m3α : threshold ≤ (t₀ - 3) * α)
    (hthresh_le_4mt₀α : threshold ≤ (4 - t₀) * α) :
    ∀ ε, 0 < ε → ε < threshold →
      IntervalIntegrable (fun t => (fdBoundaryH H t - s)⁻¹ *
          deriv (fun u => fdBoundaryH H u - s) t) volume 0 (t₀ - ε / α) ∧
      IntervalIntegrable (fun t => (fdBoundaryH H t - s)⁻¹ *
          deriv (fun u => fdBoundaryH H u - s) t) volume (t₀ + ε / α) 5 ∧
      (∫ t in (0 : ℝ)..(t₀ - ε / α), (fdBoundaryH H t - s)⁻¹ *
          deriv (fun u => fdBoundaryH H u - s) t) +
      (∫ t in (t₀ + ε / α)..(5 : ℝ), (fdBoundaryH H t - s)⁻¹ *
          deriv (fun u => fdBoundaryH H u - s) t) =
      Complex.log (fdBoundarySeg4H H (t₀ - ε / α) - s) -
      Complex.log (fdBoundarySeg4H H (t₀ + ε / α) - s) := by
  intro ε hε_pos hε_lt
  set g : ℝ → ℂ := fun t => fdBoundaryH H t - s with hg_def
  set δ := ε / α with hδ_def
  have hδ_pos : 0 < δ := div_pos hε_pos hα_pos
  have hεα_lt_t₀m3 : δ < t₀ - 3 :=
    hδ_def ▸ (div_lt_iff₀ hα_pos).mpr (hε_lt.trans_le hthresh_le_t₀m3α)
  have hεα_lt_4mt₀ : δ < 4 - t₀ :=
    hδ_def ▸ (div_lt_iff₀ hα_pos).mpr (hε_lt.trans_le hthresh_le_4mt₀α)
  set h₀ : ℝ → ℂ := fun t => fdBoundarySeg1H H t - s
  set h_arc : ℝ → ℂ := fun t => exp (↑(Real.pi * (1 + t) / 6) * I) - s
  set h₃ : ℝ → ℂ := fun t => fdBoundarySeg4H H t - s
  set h₅ : ℝ → ℂ := fun t => fdBoundarySeg5H H t - s
  have hd₀ : ∀ t : ℝ, HasDerivAt h₀ (-(↑α : ℂ) * I) t := fun t =>
    (hasDerivAt_fdBoundary_seg1_H H t).sub (hasDerivAt_const t s)
      |>.congr_deriv (by simp [hα_def])
  have hd_arc : ∀ t : ℝ, HasDerivAt h_arc
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I)) t :=
    hasDerivAt_arc_rep s
  have hd₃ : ∀ t : ℝ, HasDerivAt h₃ ((↑α : ℂ) * I) t := fun t =>
    (hasDerivAt_fdBoundary_seg4_H H t).sub (hasDerivAt_const t s)
      |>.congr_deriv (by simp [hα_def])
  have hd₅ : ∀ t : ℝ, HasDerivAt h₅ 1 t := fun t =>
    (hasDerivAt_fdBoundary_seg5_H H t).sub (hasDerivAt_const t s)
      |>.congr_deriv (by simp only [sub_zero])
  have hg_h₀ : ∀ t, t ≤ 1 → g t = h₀ t := fun t ht => by
    simp only [hg_def, h₀]; rw [fdBoundary_H_eq_seg1_H ht]
  have hg_arc : ∀ t, 1 < t → t < 3 → g t = h_arc t := fun t ht1 ht3 => by
    simp only [hg_def, h_arc]; rw [fdBoundary_H_eq_arc ht1 ht3]
  have hg_h₃ : ∀ t, 3 < t → t ≤ 4 → g t = h₃ t := fun t ht3 ht4 => by
    simp only [hg_def, h₃]; rw [fdBoundary_H_eq_seg4_H ht3 ht4]
  have hg_h₅ : ∀ t, 4 < t → g t = h₅ t := fun t ht4 => by
    simp only [hg_def, h₅]; rw [fdBoundary_H_eq_seg5_H ht4]
  have hep_01 : h₀ 0 = h₅ 5 := by
    simp only [h₀, h₅, fdBoundarySeg1H, fdBoundarySeg5H]; push_cast; ring
  have hep_1 : h₀ 1 = h_arc 1 := by
    simp only [h₀, h_arc, fdBoundarySeg1H]
    rw [show Real.pi * (1 + 1) / 6 = Real.pi / 3 from by ring,
        exp_real_angle_I, Real.cos_pi_div_three, Real.sin_pi_div_three]; push_cast; ring
  have hep_3 : h_arc 3 = h₃ 3 := by
    simp only [h_arc, h₃, fdBoundarySeg4H]
    rw [show Real.pi * (1 + 3) / 6 = 2 * Real.pi / 3 from by ring,
        exp_real_angle_I, cos_two_pi_div_three, sin_two_pi_div_three]; push_cast; ring
  have hep_4 : h₃ 4 = h₅ 4 := by
    simp only [h₃, h₅, fdBoundarySeg4H, fdBoundarySeg5H]; push_cast; ring
  have hderiv_01 : ∀ t ∈ Ioo (0 : ℝ) 1, deriv g t = deriv h₀ t := fun t ⟨_, ht1⟩ =>
    Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Iio_mem_nhds ht1) (fun s hs => hg_h₀ s (le_of_lt hs)))
  have hderiv_arc : ∀ t ∈ Ioo (1 : ℝ) 3, deriv g t = deriv h_arc t :=
    fun t ⟨ht1, ht3⟩ => Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioo_mem_nhds ht1 ht3) (fun s hs => hg_arc s hs.1 hs.2))
  have hderiv_3 : ∀ t ∈ Ioo (3 : ℝ) 4, deriv g t = deriv h₃ t :=
    fun t ⟨ht3, ht4⟩ => Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioo_mem_nhds ht3 ht4)
        (fun s hs => hg_h₃ s hs.1 (le_of_lt hs.2)))
  have hderiv_5 : ∀ t ∈ Ioo (4 : ℝ) 5, deriv g t = deriv h₅ t :=
    fun t ⟨ht4, _⟩ => Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioi_mem_nhds ht4) (fun s hs => hg_h₅ s hs))
  have piece₀ := ftc_log (by norm_num : (0 : ℝ) ≤ 1)
    ((continuous_fdBoundary_seg1_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₀ t).differentiableAt)
    (by rw [show deriv h₀ = fun _ => -(↑α : ℂ) * I from funext fun t => (hd₀ t).deriv]
        exact continuousOn_const)
    (fun t ht => leftEdge_slit_seg1 s hs_re t ht)
  have h_arc_cont : Continuous h_arc :=
    (Continuous.cexp (by fun_prop)).sub continuous_const
  have piece₁ := ftc_log (by norm_num : (1 : ℝ) ≤ 3)
    h_arc_cont.continuousOn (fun t _ => (hd_arc t).differentiableAt)
    (by rw [show deriv h_arc = fun t => ↑(Real.pi / 6) * I *
          exp (↑(Real.pi * (1 + t) / 6) * I) from funext fun t => (hd_arc t).deriv]
        exact (Continuous.mul continuous_const (Continuous.cexp (by fun_prop))).continuousOn)
    (fun t ⟨ht1, ht3⟩ => leftEdge_slit_arc s hs_re hs_im_lower t ht1 ht3)
  have piece₂ := ftc_log (by linarith : (3 : ℝ) ≤ t₀ - δ)
    ((continuous_fdBoundary_seg4_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₃ t).differentiableAt)
    (by rw [show deriv h₃ = fun _ => (↑α : ℂ) * I from funext fun t => (hd₃ t).deriv]
        exact continuousOn_const)
    (fun t ⟨ht3, htd⟩ => leftEdge_slit_seg4_left H s hs_re α hα_def hα_pos t₀ ht₀_mul
      δ hδ_pos hεα_lt_t₀m3 t ht3 htd)
  have piece₃ := ftc_log (by linarith : t₀ + δ ≤ 4)
    ((continuous_fdBoundary_seg4_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₃ t).differentiableAt)
    (by rw [show deriv h₃ = fun _ => (↑α : ℂ) * I from funext fun t => (hd₃ t).deriv]
        exact continuousOn_const)
    (fun t ⟨htd, ht4⟩ => leftEdge_slit_seg4_right H s hs_re α hα_def hα_pos t₀ ht₀_mul
      δ hδ_pos hεα_lt_4mt₀ t htd ht4)
  have piece₄ := ftc_log (by norm_num : (4 : ℝ) ≤ 5)
    ((continuous_fdBoundary_seg5_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₅ t).differentiableAt)
    (by rw [show deriv h₅ = fun _ => (1 : ℂ) from funext fun t => (hd₅ t).deriv]
        exact continuousOn_const)
    (fun t ⟨ht4, ht5⟩ => leftEdge_slit_seg5 H s hs_re hs_im t ht4 ht5)
  obtain ⟨h_ae₀, h_ae_arc, h_ae₃, h_ae₅⟩ := leftEdge_ae_seg_eq g h₀ h_arc h₃ h₅
    hg_h₀ hg_arc hg_h₃ hg_h₅ hderiv_01 hderiv_arc hderiv_3 hderiv_5
  have hint₀ : IntervalIntegrable (fun t => deriv g t / g t) volume 0 1 :=
    piece₀.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae₀.mono (fun t ht hm => ht hm)))
  have hint_arc : IntervalIntegrable (fun t => deriv g t / g t) volume 1 3 :=
    piece₁.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae_arc.mono (fun t ht hm => ht hm)))
  have hint₃_left : IntervalIntegrable (fun t => deriv g t / g t) volume 3 (t₀ - δ) :=
    piece₂.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((h_ae₃ 3 (t₀ - δ) le_rfl (by linarith) (by linarith)).mono
        (fun t ht hm => ht hm)))
  have hint₃_right : IntervalIntegrable (fun t => deriv g t / g t) volume (t₀ + δ) 4 :=
    piece₃.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((h_ae₃ (t₀ + δ) 4 (by linarith) (by linarith) le_rfl).mono
        (fun t ht hm => ht hm)))
  have hint₅ : IntervalIntegrable (fun t => deriv g t / g t) volume 4 5 :=
    piece₄.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae₅.mono (fun t ht hm => ht hm)))
  -- Convert deriv g / g to the inverse-times-deriv form for the statement
  have h_congr : ∀ t, deriv g t / g t =
      (fdBoundaryH H t - s)⁻¹ * deriv (fun u => fdBoundaryH H u - s) t := fun t => by
    simp only [hg_def, div_eq_mul_inv, mul_comm]
  have hint_left : IntervalIntegrable (fun t =>
      (fdBoundaryH H t - s)⁻¹ * deriv (fun u => fdBoundaryH H u - s) t) volume 0 (t₀ - δ) :=
    (intervalIntegrable_congr (fun t _ => h_congr t)).mp (hint₀.trans hint_arc |>.trans hint₃_left)
  have hint_right : IntervalIntegrable (fun t =>
      (fdBoundaryH H t - s)⁻¹ * deriv (fun u => fdBoundaryH H u - s) t) volume (t₀ + δ) 5 :=
    (intervalIntegrable_congr (fun t _ => h_congr t)).mp (hint₃_right.trans hint₅)
  -- FTC for each segment
  have h_ftc₀ : ∫ t in (0 : ℝ)..(1 : ℝ), deriv g t / g t =
      Complex.log (h₀ 1) - Complex.log (h₀ 0) := by
    rw [← piece₀.2, intervalIntegral.integral_congr_ae (h_ae₀.mono (fun t ht hm => ht hm))]
  have h_ftc_arc : ∫ t in (1 : ℝ)..(3 : ℝ), deriv g t / g t =
      Complex.log (h_arc 3) - Complex.log (h_arc 1) := by
    rw [← piece₁.2, intervalIntegral.integral_congr_ae
      (h_ae_arc.mono (fun t ht hm => ht hm))]
  have h_ftc₃_left : ∫ t in (3 : ℝ)..(t₀ - δ), deriv g t / g t =
      Complex.log (h₃ (t₀ - δ)) - Complex.log (h₃ 3) := by
    rw [← piece₂.2, intervalIntegral.integral_congr_ae
      ((h_ae₃ 3 (t₀ - δ) le_rfl (by linarith) (by linarith)).mono
        (fun t ht hm => ht hm))]
  have h_ftc₃_right : ∫ t in (t₀ + δ)..(4 : ℝ), deriv g t / g t =
      Complex.log (h₃ 4) - Complex.log (h₃ (t₀ + δ)) := by
    rw [← piece₃.2, intervalIntegral.integral_congr_ae
      ((h_ae₃ (t₀ + δ) 4 (by linarith) (by linarith) le_rfl).mono
        (fun t ht hm => ht hm))]
  have h_ftc₅ : ∫ t in (4 : ℝ)..(5 : ℝ), deriv g t / g t =
      Complex.log (h₅ 5) - Complex.log (h₅ 4) := by
    rw [← piece₄.2, intervalIntegral.integral_congr_ae
      (h_ae₅.mono (fun t ht hm => ht hm))]
  -- Assemble the telescoping sum
  have h_left_sum : (∫ t in (0 : ℝ)..(t₀ - δ), deriv g t / g t) =
      Complex.log (h₀ 1) - Complex.log (h₀ 0) +
        (Complex.log (h_arc 3) - Complex.log (h_arc 1)) +
      (Complex.log (h₃ (t₀ - δ)) - Complex.log (h₃ 3)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
        (hint₀.trans hint_arc) hint₃_left,
      ← intervalIntegral.integral_add_adjacent_intervals hint₀ hint_arc,
      h_ftc₀, h_ftc_arc, h_ftc₃_left]
  have h_right_sum : (∫ t in (t₀ + δ)..(5 : ℝ), deriv g t / g t) =
      Complex.log (h₃ 4) - Complex.log (h₃ (t₀ + δ)) +
      (Complex.log (h₅ 5) - Complex.log (h₅ 4)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hint₃_right hint₅,
        h_ftc₃_right, h_ftc₅]
  -- Telescope: endpoint equalities cancel interior logs
  have h_telescope :
      Complex.log (h₀ 1) - Complex.log (h₀ 0) +
      (Complex.log (h_arc 3) - Complex.log (h_arc 1)) +
      (Complex.log (h₃ (t₀ - δ)) - Complex.log (h₃ 3)) +
      (Complex.log (h₃ 4) - Complex.log (h₃ (t₀ + δ)) +
        (Complex.log (h₅ 5) - Complex.log (h₅ 4))) =
      Complex.log (h₃ (t₀ - δ)) - Complex.log (h₃ (t₀ + δ)) := by
    rw [hep_1, hep_3, hep_4, hep_01]; ring
  -- Convert to the desired form and telescope
  have h_int_eq_left : (∫ t in (0 : ℝ)..(t₀ - δ), (fdBoundaryH H t - s)⁻¹ *
        deriv (fun u => fdBoundaryH H u - s) t) =
      ∫ t in (0 : ℝ)..(t₀ - δ), deriv g t / g t :=
    intervalIntegral.integral_congr_ae (ae_of_all _ (fun t _ => (h_congr t).symm))
  have h_int_eq_right : (∫ t in (t₀ + δ)..(5 : ℝ), (fdBoundaryH H t - s)⁻¹ *
        deriv (fun u => fdBoundaryH H u - s) t) =
      ∫ t in (t₀ + δ)..(5 : ℝ), deriv g t / g t :=
    intervalIntegral.integral_congr_ae (ae_of_all _ (fun t _ => (h_congr t).symm))
  -- Return the triple: (hint_left, hint_right, ftc_eq)
  exact ⟨hint_left, hint_right, by
    rw [h_int_eq_left, h_int_eq_right, h_left_sum, h_right_sum]
    linear_combination h_telescope⟩

private lemma leftEdge_winding_aux (H : ℝ) (hH_sqrt : Real.sqrt 3 / 2 < H)
    (s : ℂ) (hs_re : s.re = -1 / 2) (hs_norm : ‖s‖ > 1)
    (hs_im_lower : Real.sqrt 3 / 2 < s.im) (hs_im : s.im < H) :
    Tendsto (fun ε => ∫ t in (0 : ℝ)..5,
        if ‖fdBoundaryH H t - s‖ > ε then
          (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0)
      (𝓝[>] 0) (𝓝 (-(↑Real.pi * I))) := by
  set α := H - Real.sqrt 3 / 2 with hα_def
  have hα_pos : 0 < α := by rw [hα_def]; linarith
  set t₀ := 3 + (s.im - Real.sqrt 3 / 2) / α with ht₀_def
  have ht₀_Ioo := leftEdge_t₀_mem_Ioo H hH_sqrt s hs_im_lower hs_im
  have ht₀_gt3 : 3 < t₀ := ht₀_Ioo.1
  have ht₀_lt4 : t₀ < 4 := ht₀_Ioo.2
  have ht₀_mul : (t₀ - 3) * α = s.im - Real.sqrt 3 / 2 := by
    simp only [ht₀_def, add_sub_cancel_left]; exact div_mul_cancel₀ _ (ne_of_gt hα_pos)
  set d := min (min (‖s‖ - 1) 1) (H - s.im)
  have hd_pos : 0 < d := leftEdge_min_dist_pos s hs_norm hs_im
  -- Choose threshold small enough for all bounds
  set threshold := min d (min ((t₀ - 3) * α) ((4 - t₀) * α))
  have hthresh_pos : 0 < threshold := lt_min hd_pos
    (lt_min (mul_pos (by linarith) hα_pos) (mul_pos (by linarith) hα_pos))
  have hthresh_le_d : threshold ≤ d := min_le_left _ _
  have hthresh_le_t₀m3α : threshold ≤ (t₀ - 3) * α :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hthresh_le_4mt₀α : threshold ≤ (4 - t₀) * α :=
    (min_le_right _ _).trans (min_le_right _ _)
  -- Define δ(ε) = ε/α
  have hδ_fn : ∀ ε, 0 < ε → ε < threshold → 0 < ε / α :=
    fun ε hε _ => div_pos hε hα_pos
  have hδ_small : ∀ ε, 0 < ε → ε < threshold →
      ε / α < min (t₀ - 0) (5 - t₀) := by
    intro ε hε_pos hε_lt
    simp only [sub_zero]
    exact lt_min
      (by rw [div_lt_iff₀ hα_pos]; nlinarith [hε_lt.trans_le hthresh_le_t₀m3α])
      (by rw [div_lt_iff₀ hα_pos]; nlinarith [hε_lt.trans_le hthresh_le_4mt₀α])
  have hd : ∀ t, deriv (fun u => fdBoundaryH H u - s) t = deriv (fdBoundaryH H) t :=
    fun t => deriv_sub_const (f := fdBoundaryH H) _
  have hftc := fun ε (hε_pos : 0 < ε) (hε_lt : ε < threshold) =>
    leftEdge_ftc_telescope H hH_sqrt s hs_re hs_norm hs_im_lower hs_im α hα_pos hα_def
      t₀ ht₀_gt3 ht₀_lt4 ht₀_mul threshold hthresh_pos hthresh_le_t₀m3α hthresh_le_4mt₀α
      ε hε_pos hε_lt
  -- Apply pv_tendsto_of_crossing_limit
  refine ContourIntegral.pv_tendsto_of_crossing_limit
      (t₀ := t₀) (ht₀ := ⟨by linarith, by linarith⟩)
      (threshold := threshold) (hthresh := hthresh_pos)
      (δ := fun ε => ε / α)
      (E := fun ε => Complex.log (fdBoundarySeg4H H (t₀ - ε / α) - s) -
                     Complex.log (fdBoundarySeg4H H (t₀ + ε / α) - s))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- hδ_pos
    exact hδ_fn
  · -- hδ_small
    exact hδ_small
  · -- h_far
    intro ε hε_pos hε_lt
    exact leftEdge_h_far H hH_sqrt s hs_re hs_norm hs_im α hα_pos hα_def t₀ ht₀_gt3 ht₀_lt4
      ht₀_mul threshold hthresh_pos hthresh_le_d hthresh_le_t₀m3α hthresh_le_4mt₀α
      ε hε_pos hε_lt
  · -- h_near
    intro ε hε_pos hε_lt
    exact leftEdge_h_near H hH_sqrt s hs_re α hα_pos hα_def t₀ ht₀_gt3 ht₀_lt4 ht₀_mul
      threshold hthresh_le_t₀m3α hthresh_le_4mt₀α ε hε_pos hε_lt
  · -- h_ftc: far integrals = E(ε)
    intro ε hε_pos hε_lt
    have h := (hftc ε hε_pos hε_lt).2.2
    simp_rw [hd] at h
    exact h
  · -- hint_left
    intro ε hε_pos hε_lt
    have h := (hftc ε hε_pos hε_lt).1
    simp_rw [hd] at h
    exact h
  · -- hint_right
    intro ε hε_pos hε_lt
    have h := (hftc ε hε_pos hε_lt).2.1
    simp_rw [hd] at h
    exact h
  · -- h_limit: E(ε) → L
    -- E(ε) = log(h₃(t₀ - ε/α)) - log(h₃(t₀ + ε/α)) = -(π*I) constantly
    have hE_const : ∀ ε, 0 < ε → ε < threshold →
        Complex.log (fdBoundarySeg4H H (t₀ - ε / α) - s) -
        Complex.log (fdBoundarySeg4H H (t₀ + ε / α) - s) = -(↑Real.pi * I) := by
      intro ε hε_pos hε_lt
      have hδ_pos : 0 < ε / α := div_pos hε_pos hα_pos
      exact leftEdge_final_log H s hs_re α hα_def (ε / α) hδ_pos hα_pos t₀ ht₀_mul
    exact tendsto_const_nhds.congr' (by
      filter_upwards [Ioo_mem_nhdsGT hthresh_pos] with ε hε
      exact (hE_const ε hε.1 hε.2).symm)

theorem gWN_fdBoundary_H_eq_neg_half_of_leftEdge (H : ℝ) (hH_sqrt : Real.sqrt 3 / 2 < H)
    (s : ℂ) (hs_re : s.re = -1 / 2) (hs_norm : ‖s‖ > 1)
    (hs_im_lower : Real.sqrt 3 / 2 < s.im) (hs_im : s.im < H) :
    generalizedWindingNumber' (fdBoundaryH H) 0 5 s = -1/2 := by
  apply ContourIntegral.gWN_eq_neg_half_of_pv_tendsto
  have h_tendsto := leftEdge_winding_aux H hH_sqrt s hs_re hs_norm hs_im_lower hs_im
  have hd : ∀ t, deriv (fun u => fdBoundaryH H u - s) t = deriv (fdBoundaryH H) t :=
    fun t => deriv_sub_const (f := fdBoundaryH H) _
  simp_rw [hd]
  convert h_tendsto using 3
  simp [sub_zero, gt_iff_lt]

end
