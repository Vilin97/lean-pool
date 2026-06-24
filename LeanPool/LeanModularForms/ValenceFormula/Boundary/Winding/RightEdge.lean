/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.Boundary.Smooth
import LeanPool.LeanModularForms.GeneralizedResidueTheory.PrincipalValue
import LeanPool.LeanModularForms.ValenceFormula.WindingWeights.Common
import LeanPool.LeanModularForms.ContourIntegral.WindingNumber
import LeanPool.LeanModularForms.ContourIntegral.CrossingLimit
import LeanPool.LeanModularForms.ValenceFormula.Boundary.Winding.Framework

/-!
# Generalized Winding Number at Right Edge Points

Proves `generalizedWindingNumber' (fdBoundaryH H) 0 5 s = -1/2` for points `s`
on the right vertical edge of the fundamental domain (`s.re = 1/2`, `√3/2 < s.im < H`).
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

attribute [local instance] Classical.propDecidable

noncomputable section

/-- For a point on the right edge, `t₀ = (H - s.im) / (H - √3/2)` is the unique
parameter in `(0, 1)` with `fdBoundaryH H t₀ = s`. -/
lemma rightEdge_t₀_mem_Ioo (H : ℝ) (_hH : heightCutoff ≤ H) (s : ℂ)
    (hs_im_lower : Real.sqrt 3 / 2 < s.im) (hs_im : s.im < H) :
    (H - s.im) / (H - Real.sqrt 3 / 2) ∈ Ioo (0 : ℝ) 1 := by
  have hH_sqrt : Real.sqrt 3 / 2 < H := by
    have : heightCutoff = Real.sqrt 3 / 2 + 1 := rfl; linarith
  have hα_pos : 0 < H - Real.sqrt 3 / 2 := by linarith
  exact ⟨div_pos (by linarith) hα_pos, by rw [div_lt_one hα_pos]; linarith⟩

/-- `fdBoundaryH H` passes through `s` at parameter `t₀`. -/
lemma rightEdge_fdBoundary_eq (H : ℝ) (s : ℂ)
    (hs_re : s.re = 1 / 2) (hs_im_lower : Real.sqrt 3 / 2 < s.im) (hs_im : s.im < H) :
    let t₀ := (H - s.im) / (H - Real.sqrt 3 / 2)
    fdBoundaryH H t₀ = s := by
  intro t₀
  have hH_sqrt : Real.sqrt 3 / 2 < H := by linarith
  have hden_pos : 0 < H - Real.sqrt 3 / 2 := by linarith
  have ht₀_le : t₀ ≤ 1 := by rw [div_le_one hden_pos]; linarith
  simp only [fdBoundaryH, ht₀_le, ↓reduceIte]
  apply Complex.ext
  · simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im]
    linarith [hs_re]
  · simp only [one_div, add_im, inv_im, im_ofNat, neg_zero, normSq_ofNat, zero_div, mul_im, sub_re,
    ofReal_re, mul_re, div_ofNat_re, ofReal_im, sub_im, div_ofNat_im, sub_self, mul_zero, sub_zero,
    I_im, mul_one, zero_mul, add_zero, I_re, zero_add]
    have h_cancel : (H - s.im) / (H - Real.sqrt 3 / 2) * (H - Real.sqrt 3 / 2) = H - s.im :=
      div_mul_cancel₀ (H - s.im) (ne_of_gt hden_pos)
    linarith

/-- The right edge parameter `t₀` is the UNIQUE crossing point on `[0, 5]`. -/
lemma rightEdge_unique_crossing (H : ℝ) (_hH : heightCutoff ≤ H) (s : ℂ)
    (hs_re : s.re = 1 / 2) (hs_norm : ‖s‖ > 1) (hs_im_lower : Real.sqrt 3 / 2 < s.im)
    (hs_im : s.im < H) :
    let t₀ := (H - s.im) / (H - Real.sqrt 3 / 2)
    ∀ t ∈ Icc (0 : ℝ) 5, fdBoundaryH H t = s → t = t₀ := by
  intro t₀ t ht hs_eq
  have hH_sqrt : Real.sqrt 3 / 2 < H := by
    have : heightCutoff = Real.sqrt 3 / 2 + 1 := rfl; linarith
  have hden_pos : 0 < H - Real.sqrt 3 / 2 := by linarith
  by_cases h1 : t ≤ 1
  · simp only [fdBoundaryH, h1, ↓reduceIte] at hs_eq
    have him := congr_arg Complex.im hs_eq
    simp only [one_div, add_im, inv_im, im_ofNat, neg_zero, normSq_ofNat, zero_div, mul_im, sub_re,
      ofReal_re, mul_re, div_ofNat_re, ofReal_im, sub_im, div_ofNat_im, sub_self, mul_zero,
      sub_zero, I_im, mul_one, zero_mul, add_zero, I_re, zero_add] at him
    change t = (H - s.im) / (H - Real.sqrt 3 / 2)
    have h_eq : t * (H - Real.sqrt 3 / 2) = H - s.im := by linarith
    rw [eq_div_iff (ne_of_gt hden_pos)]
    linarith
  · push Not at h1
    by_cases h2 : t ≤ 2
    · simp only [fdBoundaryH, show ¬(t ≤ 1) from not_le.mpr h1, ↓reduceIte, h2] at hs_eq
      have : ‖s‖ = 1 := by
        rw [← hs_eq]
        rw [show (↑π / 3 + (↑t - 1) * (↑π / 2 - ↑π / 3)) * I =
          ↑(π / 3 + (t - 1) * (π / 2 - π / 3)) * I from by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      linarith
    · push Not at h2
      by_cases h3 : t ≤ 3
      · simp only [fdBoundaryH, show ¬(t ≤ 1) from not_le.mpr h1, ↓reduceIte,
                    show ¬(t ≤ 2) from not_le.mpr h2, h3] at hs_eq
        have : ‖s‖ = 1 := by
          rw [← hs_eq]
          rw [show (↑π / 2 + (↑t - 2) * (2 * ↑π / 3 - ↑π / 2)) * I =
            ↑(π / 2 + (t - 2) * (2 * π / 3 - π / 2)) * I from by push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I _
        linarith
      · push Not at h3
        by_cases h4 : t ≤ 4
        · simp only [fdBoundaryH, show ¬(t ≤ 1) from not_le.mpr h1, ↓reduceIte,
                      show ¬(t ≤ 2) from not_le.mpr h2,
                      show ¬(t ≤ 3) from not_le.mpr h3, h4] at hs_eq
          have hre := congr_arg Complex.re hs_eq
          simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
                Complex.I_re, Complex.I_im] at hre
          linarith [hs_re]
        · push Not at h4
          simp only [fdBoundaryH, show ¬(t ≤ 1) from not_le.mpr h1, ↓reduceIte,
                      show ¬(t ≤ 2) from not_le.mpr h2,
                      show ¬(t ≤ 3) from not_le.mpr h3,
                      show ¬(t ≤ 4) from not_le.mpr h4] at hs_eq
          have him := congr_arg Complex.im hs_eq
          simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
                Complex.I_re, Complex.I_im] at him
          linarith

/-- Points on seg2/seg3 (unit circle) are at distance ≥ ‖s‖ - 1 from s. -/
lemma rightEdge_dist_from_arc (s : ℂ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖s‖ - 1 ≤ ‖z - s‖ := by
  calc ‖s‖ - 1 = ‖s‖ - ‖z‖ := by rw [hz]
    _ ≤ |‖s‖ - ‖z‖| := le_abs_self _
    _ = |‖z‖ - ‖s‖| := abs_sub_comm _ _
    _ ≤ ‖z - s‖ := abs_norm_sub_norm_le z s

/-- Points on seg4 (left vertical, re = -1/2) are at distance ≥ 1 from s with re = 1/2. -/
lemma rightEdge_dist_from_leftVertical (s : ℂ) (hs_re : s.re = 1 / 2) (z : ℂ)
    (hz_re : z.re = -1 / 2) :
    1 ≤ ‖z - s‖ := by
  have hre : (z - s).re = -1 := by simp [Complex.sub_re, hz_re, hs_re]; ring
  calc 1 = |(z - s).re| := by rw [hre]; norm_num
    _ ≤ ‖z - s‖ := abs_re_le_norm (z - s)

/-- Points on seg5 (horizontal at height H) are at distance ≥ H - s.im from s with s.im < H. -/
lemma rightEdge_dist_from_horizontal (s : ℂ) (hs_im : s.im < H) (z : ℂ) (hz_im : z.im = H) :
    H - s.im ≤ ‖z - s‖ := by
  have him : (z - s).im = H - s.im := by simp [Complex.sub_im, hz_im]
  calc H - s.im = |(z - s).im| := by rw [him]; rw [abs_of_pos (by linarith)]
    _ ≤ ‖z - s‖ := abs_im_le_norm (z - s)

/-- Minimum distance from s (on right edge) to the non-seg1 parts of the boundary. -/
lemma rightEdge_min_dist_pos (s : ℂ) (hs_norm : ‖s‖ > 1) (hs_im : s.im < H) :
    0 < min (min (‖s‖ - 1) 1) (H - s.im) := by
  simpa only [lt_min_iff] using ⟨⟨by linarith, by norm_num⟩, by linarith⟩

/-- FTC on a smooth segment: `∫ f'/f = log(−f(b)) − log(−f(a))`
when `−f` stays in `slitPlane`. Delegates to `LogDerivFTC.ftc_log_neg_on_segment`. -/
lemma ftc_log_neg {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hf_cont : ContinuousOn f (Icc a b))
    (hf_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hf_deriv_cont : ContinuousOn (deriv f) (Icc a b))
    (hf_slit : ∀ t ∈ Icc a b, -(f t) ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t => deriv f t / f t) volume a b ∧
    ∫ t in a..b, deriv f t / f t =
      Complex.log (-(f b)) - Complex.log (-(f a)) :=
  LogDerivFTC.ftc_log_neg_on_segment hab hf_cont hf_diff hf_deriv_cont hf_slit

/-- FTC for `log ∘ f` when `f` stays in slitPlane (no negation).
Delegates to `LogDerivFTC.ftc_log_on_segment`. -/
lemma ftc_log {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hf_cont : ContinuousOn f (Icc a b))
    (hf_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hf_deriv_cont : ContinuousOn (deriv f) (Icc a b))
    (hf_slit : ∀ t ∈ Icc a b, f t ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t => deriv f t / f t) volume a b ∧
    ∫ t in a..b, deriv f t / f t = Complex.log (f b) - Complex.log (f a) :=
  LogDerivFTC.ftc_log_on_segment hab hf_cont hf_diff hf_deriv_cont hf_slit

/-- log(-(r*I)) - log(r*I) = -π*I for r > 0 -/
lemma log_neg_rI_sub_log_rI {r : ℝ} (hr : 0 < r) :
    Complex.log (-(↑r * I)) - Complex.log (↑r * I) = -(↑Real.pi * I) := by
  rw [show -(↑r * I : ℂ) = ↑r * (-I) from by ring]
  rw [Complex.log_ofReal_mul hr I_ne_zero, Complex.log_ofReal_mul hr (neg_ne_zero.mpr I_ne_zero)]
  rw [Complex.log_I, Complex.log_neg_I]; ring

/-- For elements with positive real part, `log(a/b) = log a - log b`. -/
lemma log_div_of_re_pos {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    Complex.log (a / b) = Complex.log a - Complex.log b := by
  have ha_ne : a ≠ 0 := by intro h; simp [h] at ha
  have hb_ne : b ≠ 0 := by intro h; simp [h] at hb
  have hb_inv_ne : b⁻¹ ≠ 0 := inv_ne_zero hb_ne
  rw [div_eq_mul_inv]
  have hb_arg_ne_pi : b.arg ≠ Real.pi := by
    intro h; have := Complex.arg_eq_pi_iff.mp h; linarith [this.1]
  have hb_inv_arg : b⁻¹.arg = -b.arg := by rw [Complex.arg_inv]; simp [hb_arg_ne_pi]
  have ha_abs_arg : |a.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha)
  have hb_abs_arg : |b.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb)
  have hbi_abs_arg : |b⁻¹.arg| < Real.pi / 2 := by rw [hb_inv_arg, abs_neg]; exact hb_abs_arg
  have h_sum : a.arg + b⁻¹.arg ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨by linarith [abs_lt.mp ha_abs_arg, abs_lt.mp hbi_abs_arg],
      by linarith [abs_lt.mp ha_abs_arg, abs_lt.mp hbi_abs_arg]⟩
  rw [Complex.log_mul ha_ne hb_inv_ne h_sum, Complex.log_inv b hb_arg_ne_pi]; ring

private lemma rightEdge_h₀_eq {H : ℝ} {s : ℂ} (hs_re : s.re = 1 / 2) (t : ℝ) :
    fdBoundarySeg1H H t - s = (↑(H - t * (H - Real.sqrt 3 / 2) - s.im) : ℂ) * I := by
  simp only [fdBoundarySeg1H]
  rw [show s = (↑(1/2 : ℝ) : ℂ) + ↑s.im * I from by
    rw [show (1/2 : ℝ) = s.re from hs_re.symm]; exact (Complex.re_add_im s).symm]
  apply Complex.ext
  · simp [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im]
  · simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]

/-- HasDerivAt for the arc smooth representative minus s. -/
lemma hasDerivAt_arc_rep (s : ℂ) (t : ℝ) :
    HasDerivAt (fun t => exp (↑(Real.pi * (1 + t) / 6) * I) - s)
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I)) t := by
  have hf : HasDerivAt (fun s : ℝ => Real.pi * (1 + s) / 6) (Real.pi / 6) t :=
    ((hasDerivAt_id t).add_const (1 : ℝ) |>.const_mul (Real.pi / 6)).congr_of_eventuallyEq
      (Eventually.of_forall fun s => show _ from by simp [id]; ring)
      |>.congr_deriv (by ring)
  have hci : HasDerivAt (fun s : ℝ => (↑(Real.pi * (1 + s) / 6) : ℂ) * I)
      ((↑(Real.pi / 6) : ℂ) * I) t :=
    (hf.ofReal_comp.mul_const I).congr_deriv (by norm_num [smul_eq_mul])
  exact (hci.cexp.sub (hasDerivAt_const t s)).congr_deriv (by simp only [sub_zero]; ring)

private lemma norm_fdBoundary_H_arc (H : ℝ) (t : ℝ) (ht1 : 1 < t) (ht3 : t < 3) :
    ‖fdBoundaryH H t‖ = 1 := by
  rw [fdBoundary_H_eq_arc ht1 ht3]; exact Complex.norm_exp_ofReal_mul_I _

lemma re_fdBoundary_H_seg4 (H : ℝ) (t : ℝ) (_ht1 : 1 < t) (_ht2 : 2 < t)
    (ht3 : 3 < t) (ht4 : t ≤ 4) : (fdBoundaryH H t).re = -1/2 := by
  rw [fdBoundary_H_eq_seg4_H ht3 ht4]
  simp [fdBoundarySeg4H, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]

lemma im_fdBoundary_H_seg5 (H : ℝ) (t : ℝ) (_ht1 : 1 < t) (_ht2 : 2 < t)
    (_ht3 : 3 < t) (ht4 : 4 < t) : (fdBoundaryH H t).im = H := by
  rw [fdBoundary_H_eq_seg5_H ht4]
  simp [fdBoundarySeg5H, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]

private lemma rightEdge_min_dist_from_non_seg1_arc (s : ℂ) (_hs_norm : ‖s‖ > 1) (z : ℂ)
    (hz : ‖z‖ = 1) : min (min (‖s‖ - 1) 1) (H - s.im) ≤ ‖s - z‖ := by
  rw [norm_sub_rev]
  exact ((min_le_left _ _).trans (min_le_left _ _)).trans (rightEdge_dist_from_arc s z hz)

private lemma rightEdge_min_dist_from_non_seg1_seg4 (s : ℂ) (hs_re : s.re = 1 / 2) (z : ℂ)
    (hz_re : z.re = -1 / 2) : min (min (‖s‖ - 1) 1) (H - s.im) ≤ ‖s - z‖ := by
  rw [norm_sub_rev]
  exact ((min_le_left _ _).trans (min_le_right _ _)).trans
    (rightEdge_dist_from_leftVertical s hs_re z hz_re)

private lemma rightEdge_min_dist_from_non_seg1_seg5 (s : ℂ) (hs_im : s.im < H) (z : ℂ)
    (hz_im : z.im = H) : min (min (‖s‖ - 1) 1) (H - s.im) ≤ ‖s - z‖ := by
  rw [norm_sub_rev]
  exact (min_le_right _ _).trans (rightEdge_dist_from_horizontal s hs_im z hz_im)

private lemma rightEdge_min_dist_from_non_seg1 (H : ℝ) (s : ℂ)
    (hs_re : s.re = 1 / 2) (hs_norm : ‖s‖ > 1) (hs_im : s.im < H)
    (t : ℝ) (ht1 : 1 < t) (ht5 : t ≤ 5) :
    min (min (‖s‖ - 1) 1) (H - s.im) ≤ ‖fdBoundaryH H t - s‖ := by
  have neg_sub_norm : ‖fdBoundaryH H t - s‖ = ‖s - fdBoundaryH H t‖ := by rw [norm_sub_rev]
  rw [neg_sub_norm]
  by_cases h2 : t ≤ 2
  · exact rightEdge_min_dist_from_non_seg1_arc s hs_norm _
      (norm_fdBoundary_H_arc H t ht1 (by linarith))
  · push Not at h2
    by_cases h3 : t < 3
    · exact rightEdge_min_dist_from_non_seg1_arc s hs_norm _
        (norm_fdBoundary_H_arc H t ht1 h3)
    · push Not at h3
      rcases eq_or_lt_of_le h3 with h3_eq | h3_lt
      · subst h3_eq
        have : ‖fdBoundaryH H 3‖ = 1 := by
          simp only [fdBoundaryH, show ¬((3 : ℝ) ≤ 1) from by norm_num, ↓reduceIte,
            show ¬((3 : ℝ) ≤ 2) from by norm_num, show (3 : ℝ) ≤ 3 from le_refl _]
          convert Complex.norm_exp_ofReal_mul_I (2 * Real.pi / 3) using 2
          push_cast; ring
        exact rightEdge_min_dist_from_non_seg1_arc s hs_norm _ this
      · by_cases h4 : t ≤ 4
        · exact rightEdge_min_dist_from_non_seg1_seg4 s hs_re _
            (re_fdBoundary_H_seg4 H t ht1 h2 h3_lt h4)
        · push Not at h4
          exact rightEdge_min_dist_from_non_seg1_seg5 s hs_im _
            (im_fdBoundary_H_seg5 H t ht1 h2 h3_lt h4)

/-- AE seg equalities for the right edge: each segment representative agrees with `g`
on its interior, so `deriv h / h = deriv g / g` a.e. on the corresponding interval. -/
private lemma rightEdge_ae_seg_eq (g h₀ h_arc h₃ h₅ : ℝ → ℂ)
    (hg_h₀ : ∀ t, t ≤ 1 → g t = h₀ t)
    (hg_arc : ∀ t, 1 < t → t < 3 → g t = h_arc t)
    (hg_h₃ : ∀ t, 3 < t → t ≤ 4 → g t = h₃ t)
    (hg_h₅ : ∀ t, 4 < t → g t = h₅ t)
    (hderiv_01 : ∀ t ∈ Ioo (0 : ℝ) 1, deriv g t = deriv h₀ t)
    (hderiv_arc : ∀ t ∈ Ioo (1 : ℝ) 3, deriv g t = deriv h_arc t)
    (hderiv_3 : ∀ t ∈ Ioo (3 : ℝ) 4, deriv g t = deriv h₃ t)
    (hderiv_5 : ∀ t ∈ Ioo (4 : ℝ) 5, deriv g t = deriv h₅ t) :
    (∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
      ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → deriv h₀ t / h₀ t = deriv g t / g t) ∧
    (∀ᵐ t ∂volume, t ∈ Set.uIoc 1 3 →
      deriv h_arc t / h_arc t = deriv g t / g t) ∧
    (∀ᵐ t ∂volume, t ∈ Set.uIoc 3 4 →
      deriv h₃ t / h₃ t = deriv g t / g t) ∧
    (∀ᵐ t ∂volume, t ∈ Set.uIoc 4 5 →
      deriv h₅ t / h₅ t = deriv g t / g t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b _ha_nn hab hb1
    have h_excl : ({b} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact (Set.toFinite ({b} : Set ℝ)).measure_zero volume)
    filter_upwards [h_excl] with t ht_ne ht
    rw [Set.uIoc_of_le (le_of_lt hab)] at ht
    have ht_lt_b : t < b := lt_of_le_of_ne ht.2 (fun h => ht_ne (Set.mem_singleton_iff.mpr h))
    have ht_lt1 : t < 1 := lt_of_lt_of_le ht_lt_b hb1
    rw [hg_h₀ t (le_of_lt ht_lt1), hderiv_01 t ⟨by linarith [ht.1], ht_lt1⟩]
  · have : ({1, 3} : Set ℝ)ᶜ ∈ ae volume := mem_ae_iff.mpr (by
        rw [compl_compl]; exact (Set.toFinite ({1, 3} : Set ℝ)).measure_zero volume)
    filter_upwards [this] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at ht_mem
    have ht1 : 1 < t := by
      rcases eq_or_lt_of_le (le_of_lt ht_mem.1) with h | h
      · exfalso; exact ht_ne (Set.mem_insert_iff.mpr (Or.inl (by linarith)))
      · exact h
    have ht3 : t < 3 := by
      rcases eq_or_lt_of_le ht_mem.2 with h | h
      · exfalso
        exact ht_ne (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr (by linarith))))
      · exact h
    rw [hg_arc t ht1 ht3, hderiv_arc t ⟨ht1, ht3⟩]
  · have : ({3, 4} : Set ℝ)ᶜ ∈ ae volume := mem_ae_iff.mpr (by
        rw [compl_compl]; exact (Set.toFinite ({3, 4} : Set ℝ)).measure_zero volume)
    filter_upwards [this] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by norm_num : (3 : ℝ) ≤ 4)] at ht_mem
    have ht3 : 3 < t := by
      rcases eq_or_lt_of_le (le_of_lt ht_mem.1) with h | h
      · exfalso; exact ht_ne (Set.mem_insert_iff.mpr (Or.inl (by linarith)))
      · exact h
    have ht4 : t < 4 := by
      rcases eq_or_lt_of_le ht_mem.2 with h | h
      · exfalso
        exact ht_ne (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr (by linarith))))
      · exact h
    rw [hg_h₃ t ht3 (le_of_lt ht4), hderiv_3 t ⟨ht3, ht4⟩]
  · have : ({4, 5} : Set ℝ)ᶜ ∈ ae volume := mem_ae_iff.mpr (by
        rw [compl_compl]; exact (Set.toFinite ({4, 5} : Set ℝ)).measure_zero volume)
    filter_upwards [this] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by norm_num : (4 : ℝ) ≤ 5)] at ht_mem
    have ht4 : 4 < t := by
      rcases eq_or_lt_of_le (le_of_lt ht_mem.1) with h | h
      · exfalso; exact ht_ne (Set.mem_insert_iff.mpr (Or.inl (by linarith)))
      · exact h
    have ht5 : t < 5 := by
      rcases eq_or_lt_of_le ht_mem.2 with h | h
      · exfalso
        exact ht_ne (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr (by linarith))))
      · exact h
    rw [hg_h₅ t ht4, hderiv_5 t ⟨ht4, ht5⟩]

/-- `-(fdBoundarySeg4H H t - s) ∈ slitPlane` when `s.re = 1/2`:
`(s - seg4).re = 1 > 0`. -/
private lemma rightEdge_neg_seg4_slitPlane (s : ℂ) (hs_re : s.re = 1 / 2)
    (t : ℝ) (_ht3 : 3 ≤ t) (_ht4 : t ≤ 4) :
    -(fdBoundarySeg4H H t - s) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  simp only [fdBoundarySeg4H, neg_sub, Complex.sub_re,
    Complex.add_re, Complex.neg_re, Complex.div_ofNat_re,
    Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_zero]
  rw [hs_re]; norm_num

/-- `-(fdBoundarySeg5H H t - s) ∈ slitPlane` when `s.re = 1/2, s.im < H`:
either `(s-seg5).re > 0` (when `t < 5`) or `(s-seg5).im ≠ 0` (when `t = 5`). -/
private lemma rightEdge_neg_seg5_slitPlane (s : ℂ) (hs_re : s.re = 1 / 2)
    (hs_im : s.im < H)
    (t : ℝ) (_ht4 : 4 ≤ t) (ht5 : t ≤ 5) :
    -(fdBoundarySeg5H H t - s) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  simp only [fdBoundarySeg5H, neg_sub]
  by_cases ht5_eq : t = 5
  · right; subst ht5_eq
    simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    linarith
  · left; have : t < 5 := lt_of_le_of_ne ht5 ht5_eq
    simp only [sub_re, add_re, ofReal_re, div_ofNat_re, re_ofNat, mul_re, I_re, mul_zero, ofReal_im,
      I_im, mul_one, sub_self, add_zero, sub_pos, gt_iff_lt]
    rw [hs_re]; linarith

private lemma rightEdge_neg_seg1_slitPlane_left (H : ℝ) (s : ℂ) (hs_re : s.re = 1 / 2)
    (_hs_im : s.im < H) (hH_sqrt : Real.sqrt 3 / 2 < H)
    (δ' : ℝ) (hδ' : 0 < δ') (t₀ : ℝ) (_hδ't₀ : δ' < t₀)
    (ht₀_mul : t₀ * (H - Real.sqrt 3 / 2) = H - s.im)
    (t : ℝ) (_ht0 : 0 ≤ t) (htd : t ≤ t₀ - δ') :
    -(fdBoundarySeg1H H t - s) ∈ Complex.slitPlane := by
  have hα_pos : 0 < H - Real.sqrt 3 / 2 := by linarith
  rw [Complex.mem_slitPlane_iff]; right
  rw [rightEdge_h₀_eq hs_re]
  simp only [Complex.neg_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, add_zero]
  have : t * (H - Real.sqrt 3 / 2) < H - s.im := by
    nlinarith [mul_le_mul_of_nonneg_right htd (le_of_lt hα_pos), mul_pos hδ' hα_pos]
  intro h; linarith

private lemma rightEdge_neg_seg1_slitPlane_right (H : ℝ) (s : ℂ) (hs_re : s.re = 1 / 2)
    (_hs_im : s.im < H) (hH_sqrt : Real.sqrt 3 / 2 < H)
    (δ' : ℝ) (hδ' : 0 < δ') (t₀ : ℝ) (_hδ'1t₀ : δ' < 1 - t₀)
    (ht₀_mul : t₀ * (H - Real.sqrt 3 / 2) = H - s.im)
    (t : ℝ) (htd : t₀ + δ' ≤ t) (_ht1 : t ≤ 1) :
    -(fdBoundarySeg1H H t - s) ∈ Complex.slitPlane := by
  have hα_pos : 0 < H - Real.sqrt 3 / 2 := by linarith
  rw [Complex.mem_slitPlane_iff]; right
  rw [rightEdge_h₀_eq hs_re]
  simp only [Complex.neg_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, add_zero]
  have : t * (H - Real.sqrt 3 / 2) > H - s.im := by
    nlinarith [mul_le_mul_of_nonneg_right htd (le_of_lt hα_pos), mul_pos hδ' hα_pos]
  intro h; linarith

private lemma rightEdge_neg_arc_slitPlane (s : ℂ) (hs_re : s.re = 1 / 2)
    (hs_im_lower : Real.sqrt 3 / 2 < s.im)
    (t : ℝ) (ht1 : 1 ≤ t) (ht3 : t ≤ 3) :
    -(exp (↑(Real.pi * (1 + t) / 6) * I) - s) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  simp only [neg_sub]
  set θ := Real.pi * (1 + t) / 6 with hθ_def
  have hθ_lower : Real.pi / 3 ≤ θ := by simp only [hθ_def]; nlinarith [Real.pi_pos]
  have hθ_upper : θ ≤ 2 * Real.pi / 3 := by simp only [hθ_def]; nlinarith [Real.pi_pos]
  by_cases ht1_eq : t = 1
  · right
    subst ht1_eq
    change (s - cexp (↑(Real.pi * (1 + 1) / 6) * I)).im ≠ 0
    rw [show Real.pi * (1 + 1) / 6 = Real.pi / 3 from by ring,
        exp_real_angle_I, Real.cos_pi_div_three, Real.sin_pi_div_three]
    simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
    linarith [hs_im_lower]
  · left
    have ht1_strict : 1 < t := lt_of_le_of_ne ht1 (Ne.symm ht1_eq)
    have hθ_strict : Real.pi / 3 < θ := by simp only [hθ_def]; nlinarith [Real.pi_pos]
    simp only [Complex.sub_re, exp_ofReal_mul_I_re]
    rw [hs_re]
    have hcos_lt : Real.cos θ < 1 / 2 := by
      have h_pi_div_three : Real.pi / 3 > 0 := by nlinarith [Real.pi_pos]
      rw [← Real.cos_pi_div_three]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi (le_of_lt h_pi_div_three)
        (hθ_upper.trans (by nlinarith [Real.pi_pos])) hθ_strict
    linarith

private lemma rightEdge_final_log (H : ℝ) (s : ℂ)
    (hs_re : s.re = 1 / 2) (α : ℝ) (hα_def : α = H - Real.sqrt 3 / 2)
    (δ : ℝ) (hδ_pos : 0 < δ) (hα_pos : 0 < α)
    (t₀ : ℝ) (ht₀_mul : t₀ * α = H - s.im) :
    Complex.log (-(fdBoundarySeg1H H (t₀ - δ) - s)) -
    Complex.log (-(fdBoundarySeg1H H (t₀ + δ) - s)) = -(↑Real.pi * I) := by
  have hval_minus : fdBoundarySeg1H H (t₀ - δ) - s = ↑(δ * α) * I := by
    rw [rightEdge_h₀_eq hs_re]
    have h_sub : (t₀ - δ) * α = t₀ * α - δ * α := sub_mul t₀ δ α
    have hval : H - (t₀ - δ) * (H - Real.sqrt 3 / 2) - s.im = δ * α := by
      rw [hα_def] at h_sub ht₀_mul ⊢; linarith
    rw [hval]
  have hval_plus : fdBoundarySeg1H H (t₀ + δ) - s = ↑(-(δ * α)) * I := by
    rw [rightEdge_h₀_eq hs_re]
    have h_add : (t₀ + δ) * α = t₀ * α + δ * α := add_mul t₀ δ α
    have hval : H - (t₀ + δ) * (H - Real.sqrt 3 / 2) - s.im = -(δ * α) := by
      rw [hα_def] at h_add ht₀_mul ⊢; linarith
    rw [hval]
  rw [hval_minus, hval_plus]
  rw [show -(↑(δ * α) * I : ℂ) = ↑(δ * α) * (-I) from by ring,
      show -(↑(-(δ * α)) * I : ℂ) = ↑(δ * α) * I from by push_cast; ring]
  have hdα_pos : 0 < δ * α := mul_pos hδ_pos hα_pos
  rw [Complex.log_ofReal_mul hdα_pos (show (-I : ℂ) ≠ 0 from neg_ne_zero.mpr I_ne_zero),
      Complex.log_ofReal_mul hdα_pos I_ne_zero,
      Complex.log_neg_I, Complex.log_I]; ring

/-- The crossing-correction `E ε` is eventually constant `-(π·I)` near `0⁺`, hence tends to it. -/
private lemma rightEdge_E_tendsto (H : ℝ) (s : ℂ) (hs_re : s.re = 1 / 2)
    (α : ℝ) (hα_def : α = H - Real.sqrt 3 / 2) (hα_pos : 0 < α)
    (t₀ : ℝ) (ht₀_mul : t₀ * α = H - s.im)
    (threshold : ℝ) (hthresh_pos : 0 < threshold) :
    Tendsto (fun ε => Complex.log (-(fdBoundarySeg1H H (t₀ - ε / α) - s)) -
        Complex.log (-(fdBoundarySeg1H H (t₀ + ε / α) - s)))
      (𝓝[>] 0) (𝓝 (-(↑Real.pi * I))) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [Ioo_mem_nhdsGT hthresh_pos] with ε hε
    exact (rightEdge_final_log H s hs_re α hα_def (ε / α)
      (div_pos hε.1 hα_pos) hα_pos t₀ ht₀_mul).symm)

private lemma rightEdge_seg1_eq_arc_at_one (H : ℝ) (s : ℂ) :
    fdBoundarySeg1H H 1 - s = exp (↑(Real.pi * (1 + (1 : ℝ)) / 6) * I) - s := by
  simp only [fdBoundarySeg1H]
  rw [show Real.pi * (1 + 1) / 6 = Real.pi / 3 from by ring,
      exp_real_angle_I, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast; ring

private lemma rightEdge_arc_eq_seg4_at_three (H : ℝ) (s : ℂ) :
    exp (↑(Real.pi * (1 + (3 : ℝ)) / 6) * I) - s = fdBoundarySeg4H H 3 - s := by
  simp only [fdBoundarySeg4H]
  rw [show Real.pi * (1 + 3) / 6 = 2 * Real.pi / 3 from by ring,
      exp_real_angle_I, cos_two_pi_div_three, sin_two_pi_div_three]
  push_cast; ring

/-- If `g` and `h` agree on the open interval `(a, b)`, their derivatives agree there too. -/
private lemma rightEdge_deriv_eq_on_Ioo {g h : ℝ → ℂ} {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hgh : ∀ s ∈ Ioo a b, g s = h s) : deriv g t = deriv h t :=
  Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) hgh)

/-- FTC telescope: the left + right logDeriv integrals of `fdBoundaryH H - s` (skipping the
crossing interval `[t₀ - δ, t₀ + δ]`) equal `log(-(h₀(t₀ - δ))) - log(-(h₀(t₀ + δ)))`.
Here `h₀ t = fdBoundarySeg1H H t - s`, `α = H - √3/2`, `t₀ = (H - s.im)/α`, `δ > 0`.
Also returns integrability of `(fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t`. -/
lemma rightEdge_ftc_telescope (H : ℝ) (_hH_sqrt : Real.sqrt 3 / 2 < H)
    (s : ℂ) (hs_re : s.re = 1 / 2)
    (hs_im_lower : Real.sqrt 3 / 2 < s.im) (hs_im : s.im < H)
    (δ : ℝ) (hδ_pos : 0 < δ)
    (hδ_lt_t₀ : δ < (H - s.im) / (H - Real.sqrt 3 / 2))
    (hδ_lt_1mt₀ : δ < 1 - (H - s.im) / (H - Real.sqrt 3 / 2)) :
    let h₀ : ℝ → ℂ := fun t => fdBoundarySeg1H H t - s
    let t₀ := (H - s.im) / (H - Real.sqrt 3 / 2)
    IntervalIntegrable (fun t => (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t)
        volume 0 (t₀ - δ) ∧
    IntervalIntegrable (fun t => (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t)
        volume (t₀ + δ) 5 ∧
    (∫ t in (0 : ℝ)..(t₀ - δ), (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t) +
    (∫ t in (t₀ + δ)..(5 : ℝ), (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t) =
    Complex.log (-(h₀ (t₀ - δ))) - Complex.log (-(h₀ (t₀ + δ))) := by
  intro h₀ t₀
  set g : ℝ → ℂ := fun t => fdBoundaryH H t - s with hg_def
  set α := H - Real.sqrt 3 / 2 with hα_def
  have hα_pos : 0 < α := by rw [hα_def]; linarith
  have ht₀_def : t₀ = (H - s.im) / α := rfl
  have ht₀_pos : 0 < t₀ := div_pos (by linarith) hα_pos
  have ht₀_lt : t₀ < 1 := by rw [ht₀_def, div_lt_one hα_pos]; linarith [hα_def]
  have ht₀_mul : t₀ * α = H - s.im := div_mul_cancel₀ _ (ne_of_gt hα_pos)
  set h_arc : ℝ → ℂ := fun t => exp (↑(Real.pi * (1 + t) / 6) * I) - s
  set h₃ : ℝ → ℂ := fun t => fdBoundarySeg4H H t - s
  set h₅ : ℝ → ℂ := fun t => fdBoundarySeg5H H t - s
  have hd₀ : ∀ t : ℝ, HasDerivAt h₀ (-(↑α : ℂ) * I) t := by
    intro t; exact (hasDerivAt_fdBoundary_seg1_H H t).sub (hasDerivAt_const t s)
      |>.congr_deriv (by simp [hα_def])
  have hd_arc : ∀ t : ℝ, HasDerivAt h_arc
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I)) t :=
    hasDerivAt_arc_rep s
  have hd₃ : ∀ t : ℝ, HasDerivAt h₃ ((↑α : ℂ) * I) t := by
    intro t; exact (hasDerivAt_fdBoundary_seg4_H H t).sub (hasDerivAt_const t s)
      |>.congr_deriv (by simp [hα_def])
  have hd₅ : ∀ t : ℝ, HasDerivAt h₅ 1 t := by
    intro t; exact (hasDerivAt_fdBoundary_seg5_H H t).sub (hasDerivAt_const t s)
      |>.congr_deriv (by simp only [sub_zero])
  have hg_h₀ : ∀ t, t ≤ 1 → g t = h₀ t := by
    intro t ht; simp only [g, h₀]; rw [fdBoundary_H_eq_seg1_H ht]
  have hg_arc : ∀ t, 1 < t → t < 3 → g t = h_arc t := by
    intro t ht1 ht3; simp only [g, h_arc]; rw [fdBoundary_H_eq_arc ht1 ht3]
  have hg_h₃ : ∀ t, 3 < t → t ≤ 4 → g t = h₃ t := by
    intro t ht3 ht4; simp only [g, h₃]; rw [fdBoundary_H_eq_seg4_H ht3 ht4]
  have hg_h₅ : ∀ t, 4 < t → g t = h₅ t := by
    intro t ht4; simp only [g, h₅]; rw [fdBoundary_H_eq_seg5_H ht4]
  have hep_01 : h₀ 0 = h₅ 5 := by
    simp only [h₀, h₅, fdBoundarySeg1H, fdBoundarySeg5H]; push_cast; ring
  have hep_1 : h₀ 1 = h_arc 1 := rightEdge_seg1_eq_arc_at_one H s
  have hep_3 : h_arc 3 = h₃ 3 := rightEdge_arc_eq_seg4_at_three H s
  have hep_4 : h₃ 4 = h₅ 4 := by
    simp only [h₃, h₅, fdBoundarySeg4H, fdBoundarySeg5H]; push_cast; ring
  have hderiv_01 : ∀ t ∈ Ioo (0 : ℝ) 1, deriv g t = deriv h₀ t := fun t ht =>
    rightEdge_deriv_eq_on_Ioo ht (fun s hs => hg_h₀ s (le_of_lt hs.2))
  have hderiv_arc : ∀ t ∈ Ioo (1 : ℝ) 3, deriv g t = deriv h_arc t := fun t ht =>
    rightEdge_deriv_eq_on_Ioo ht (fun s hs => hg_arc s hs.1 hs.2)
  have hderiv_3 : ∀ t ∈ Ioo (3 : ℝ) 4, deriv g t = deriv h₃ t := fun t ht =>
    rightEdge_deriv_eq_on_Ioo ht (fun s hs => hg_h₃ s hs.1 (le_of_lt hs.2))
  have hderiv_5 : ∀ t ∈ Ioo (4 : ℝ) 5, deriv g t = deriv h₅ t := fun t ht =>
    rightEdge_deriv_eq_on_Ioo ht (fun s hs => hg_h₅ s hs.1)
  have hslit₀_left : ∀ δ', 0 < δ' → δ' < t₀ →
      ∀ t ∈ Icc (0 : ℝ) (t₀ - δ'), -(h₀ t) ∈ Complex.slitPlane := by
    intro δ' hδ' hδ't₀ t ⟨ht0, htd⟩
    exact rightEdge_neg_seg1_slitPlane_left H s hs_re hs_im _hH_sqrt δ' hδ' t₀ hδ't₀
      ht₀_mul t ht0 htd
  have hslit₀_right : ∀ δ', 0 < δ' → δ' < 1 - t₀ →
      ∀ t ∈ Icc (t₀ + δ') 1, -(h₀ t) ∈ Complex.slitPlane := by
    intro δ' hδ' hδ'1t₀ t ⟨htd, ht1⟩
    exact rightEdge_neg_seg1_slitPlane_right H s hs_re hs_im _hH_sqrt δ' hδ' t₀ hδ'1t₀
      ht₀_mul t htd ht1
  have hslit_arc : ∀ t ∈ Icc (1 : ℝ) 3, -(h_arc t) ∈ Complex.slitPlane := by
    intro t ⟨ht1, ht3⟩; exact rightEdge_neg_arc_slitPlane s hs_re hs_im_lower t ht1 ht3
  have hslit₃ : ∀ t ∈ Icc (3 : ℝ) 4, -(h₃ t) ∈ Complex.slitPlane :=
    fun t ⟨ht3, ht4⟩ => rightEdge_neg_seg4_slitPlane s hs_re t ht3 ht4
  have hslit₅ : ∀ t ∈ Icc (4 : ℝ) 5, -(h₅ t) ∈ Complex.slitPlane :=
    fun t ⟨ht4, ht5⟩ => rightEdge_neg_seg5_slitPlane s hs_re hs_im t ht4 ht5
  have piece₀ := ftc_log_neg (by linarith : (0 : ℝ) ≤ t₀ - δ)
    ((continuous_fdBoundary_seg1_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₀ t).differentiableAt)
    (by rw [show deriv h₀ = fun _ => -(↑α : ℂ) * I from funext fun t => (hd₀ t).deriv]
        exact continuousOn_const)
    (hslit₀_left δ hδ_pos hδ_lt_t₀)
  have piece₁ := ftc_log_neg (by linarith : t₀ + δ ≤ 1)
    ((continuous_fdBoundary_seg1_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₀ t).differentiableAt)
    (by rw [show deriv h₀ = fun _ => -(↑α : ℂ) * I from funext fun t => (hd₀ t).deriv]
        exact continuousOn_const)
    (hslit₀_right δ hδ_pos hδ_lt_1mt₀)
  have h_arc_cont : Continuous h_arc := by
    simp only [h_arc]; exact (Continuous.cexp (by fun_prop)).sub continuous_const
  have piece₂ := ftc_log_neg (by norm_num : (1 : ℝ) ≤ 3)
    h_arc_cont.continuousOn (fun t _ => (hd_arc t).differentiableAt)
    (by rw [show deriv h_arc = fun t => ↑(Real.pi / 6) * I *
          exp (↑(Real.pi * (1 + t) / 6) * I) from funext fun t => (hd_arc t).deriv]
        exact (Continuous.mul continuous_const (Continuous.cexp (by fun_prop))).continuousOn)
    hslit_arc
  have piece₃ := ftc_log_neg (by norm_num : (3 : ℝ) ≤ 4)
    ((continuous_fdBoundary_seg4_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₃ t).differentiableAt)
    (by rw [show deriv h₃ = fun _ => (↑α : ℂ) * I from funext fun t => (hd₃ t).deriv]
        exact continuousOn_const)
    hslit₃
  have piece₄ := ftc_log_neg (by norm_num : (4 : ℝ) ≤ 5)
    ((continuous_fdBoundary_seg5_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₅ t).differentiableAt)
    (by rw [show deriv h₅ = fun _ => (1 : ℂ) from funext fun t => (hd₅ t).deriv]
        exact continuousOn_const)
    hslit₅
  obtain ⟨h_ae₀, h_ae_arc, h_ae₃, h_ae₅⟩ := rightEdge_ae_seg_eq g h₀ h_arc h₃ h₅
    hg_h₀ hg_arc hg_h₃ hg_h₅ hderiv_01 hderiv_arc hderiv_3 hderiv_5
  have hint₀ : IntervalIntegrable (fun t => deriv g t / g t) volume 0 (t₀ - δ) :=
    piece₀.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((h_ae₀ 0 (t₀ - δ) le_rfl (by linarith) (by linarith)).mono
        (fun t ht hm => ht hm)))
  have hint₁ : IntervalIntegrable (fun t => deriv g t / g t) volume (t₀ + δ) 1 :=
    piece₁.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((h_ae₀ (t₀ + δ) 1 (by linarith) (by linarith) le_rfl).mono
        (fun t ht hm => ht hm)))
  have hint_arc : IntervalIntegrable (fun t => deriv g t / g t) volume 1 3 :=
    piece₂.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae_arc.mono (fun t ht hm => ht hm)))
  have hint₃ : IntervalIntegrable (fun t => deriv g t / g t) volume 3 4 :=
    piece₃.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae₃.mono (fun t ht hm => ht hm)))
  have hint₅ : IntervalIntegrable (fun t => deriv g t / g t) volume 4 5 :=
    piece₄.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae₅.mono (fun t ht hm => ht hm)))
  have hint_right : IntervalIntegrable (fun t => deriv g t / g t) volume (t₀ + δ) 5 :=
    hint₁.trans hint_arc |>.trans hint₃ |>.trans hint₅
  have h_ftc₀ : ∫ t in (0 : ℝ)..(t₀ - δ), deriv g t / g t =
      Complex.log (-(h₀ (t₀ - δ))) - Complex.log (-(h₀ 0)) := by
    rw [← piece₀.2, intervalIntegral.integral_congr_ae
      ((h_ae₀ 0 (t₀ - δ) le_rfl (by linarith) (by linarith)).mono
        (fun t ht hm => ht hm))]
  have h_ftc₁ : ∫ t in (t₀ + δ)..(1 : ℝ), deriv g t / g t =
      Complex.log (-(h₀ 1)) - Complex.log (-(h₀ (t₀ + δ))) := by
    rw [← piece₁.2, intervalIntegral.integral_congr_ae
      ((h_ae₀ (t₀ + δ) 1 (by linarith) (by linarith) le_rfl).mono
        (fun t ht hm => ht hm))]
  have h_ftc_arc : ∫ t in (1 : ℝ)..(3 : ℝ), deriv g t / g t =
      Complex.log (-(h_arc 3)) - Complex.log (-(h_arc 1)) := by
    rw [← piece₂.2, intervalIntegral.integral_congr_ae (h_ae_arc.mono (fun t ht hm => ht hm))]
  have h_ftc₃ : ∫ t in (3 : ℝ)..(4 : ℝ), deriv g t / g t =
      Complex.log (-(h₃ 4)) - Complex.log (-(h₃ 3)) := by
    rw [← piece₃.2, intervalIntegral.integral_congr_ae (h_ae₃.mono (fun t ht hm => ht hm))]
  have h_ftc₅ : ∫ t in (4 : ℝ)..(5 : ℝ), deriv g t / g t =
      Complex.log (-(h₅ 5)) - Complex.log (-(h₅ 4)) := by
    rw [← piece₄.2, intervalIntegral.integral_congr_ae (h_ae₅.mono (fun t ht hm => ht hm))]
  have h_right_total : ∫ t in (t₀ + δ)..(5 : ℝ), deriv g t / g t =
      Complex.log (-(h₀ 1)) - Complex.log (-(h₀ (t₀ + δ))) +
      (Complex.log (-(h_arc 3)) - Complex.log (-(h_arc 1))) +
      (Complex.log (-(h₃ 4)) - Complex.log (-(h₃ 3))) +
      (Complex.log (-(h₅ 5)) - Complex.log (-(h₅ 4))) := by
    have h_split_right : (∫ t in (t₀ + δ)..(5 : ℝ), deriv g t / g t) =
      (∫ t in (t₀ + δ)..(1 : ℝ), deriv g t / g t) + (∫ t in (1 : ℝ)..(3 : ℝ), deriv g t / g t) +
      (∫ t in (3 : ℝ)..(4 : ℝ), deriv g t / g t) + (∫ t in (4 : ℝ)..(5 : ℝ), deriv g t / g t) := by
        have h1 : (∫ t in (t₀ + δ)..(1 : ℝ), deriv g t / g t) +
            (∫ t in (1 : ℝ)..(3 : ℝ), deriv g t / g t) =
            ∫ t in (t₀ + δ)..(3 : ℝ), deriv g t / g t := by
          rw [← intervalIntegral.integral_add_adjacent_intervals hint₁ hint_arc]
        have h2 : (∫ t in (t₀ + δ)..(3 : ℝ), deriv g t / g t) +
            (∫ t in (3 : ℝ)..(4 : ℝ), deriv g t / g t) =
            ∫ t in (t₀ + δ)..(4 : ℝ), deriv g t / g t := by
          rw [← intervalIntegral.integral_add_adjacent_intervals
            (hint₁.trans hint_arc) hint₃]
        have h3 : (∫ t in (t₀ + δ)..(4 : ℝ), deriv g t / g t) +
            (∫ t in (4 : ℝ)..(5 : ℝ), deriv g t / g t) =
            ∫ t in (t₀ + δ)..(5 : ℝ), deriv g t / g t := by
          rw [← intervalIntegral.integral_add_adjacent_intervals
            ((hint₁.trans hint_arc).trans hint₃) hint₅]
        rw [← h3, ← h2, ← h1]
    rw [h_split_right, h_ftc₁, h_ftc_arc, h_ftc₃, h_ftc₅]
  have h_telescope : Complex.log (-(h₀ (t₀ - δ))) - Complex.log (-(h₀ 0)) +
      (Complex.log (-(h₀ 1)) - Complex.log (-(h₀ (t₀ + δ))) +
        (Complex.log (-(h_arc 3)) - Complex.log (-(h_arc 1))) +
        (Complex.log (-(h₃ 4)) - Complex.log (-(h₃ 3))) +
        (Complex.log (-(h₅ 5)) - Complex.log (-(h₅ 4)))) =
      Complex.log (-(h₀ (t₀ - δ))) - Complex.log (-(h₀ (t₀ + δ))) := by
    rw [hep_1, hep_3, hep_4, hep_01]; ring
  -- Convert from deriv g / g to (γ t - s)⁻¹ * deriv γ t form
  have h_congr : ∀ t, deriv g t / g t =
      (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t := fun t => by
    simp only [hg_def]
    have hd : deriv (fun t => fdBoundaryH H t - s) t = deriv (fdBoundaryH H) t :=
      deriv_sub_const (f := fdBoundaryH H) _
    rw [hd, div_eq_mul_inv, mul_comm]
  have hint_left_g : IntervalIntegrable
      (fun t => (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t)
      volume 0 (t₀ - δ) := hint₀.congr_ae (ae_of_all _ h_congr)
  have hint_right_g : IntervalIntegrable
      (fun t => (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t)
      volume (t₀ + δ) 5 := hint_right.congr_ae (ae_of_all _ h_congr)
  have h_int_eq_left :
      (∫ t in (0 : ℝ)..(t₀ - δ), (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t) =
      ∫ t in (0 : ℝ)..(t₀ - δ), deriv g t / g t :=
    intervalIntegral.integral_congr_ae (ae_of_all _ (fun t _ => (h_congr t).symm))
  have h_int_eq_right :
      (∫ t in (t₀ + δ)..(5 : ℝ), (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t) =
      ∫ t in (t₀ + δ)..(5 : ℝ), deriv g t / g t :=
    intervalIntegral.integral_congr_ae (ae_of_all _ (fun t _ => (h_congr t).symm))
  refine ⟨hint_left_g, hint_right_g, ?_⟩
  rw [h_int_eq_left, h_int_eq_right, h_ftc₀, h_right_total, h_telescope]

private lemma rightEdge_h_far (H : ℝ) (_hH_sqrt : Real.sqrt 3 / 2 < H)
    (s : ℂ) (hs_re : s.re = 1 / 2) (hs_norm : ‖s‖ > 1) (hs_im : s.im < H)
    (α : ℝ) (hα_pos : 0 < α) (hα_def : α = H - Real.sqrt 3 / 2)
    (t₀ : ℝ) (_ht₀_pos : 0 < t₀) (_ht₀_lt : t₀ < 1)
    (ht₀_mul : t₀ * α = H - s.im)
    (threshold : ℝ) (_hthresh : 0 < threshold)
    (hthresh_le_d : threshold ≤ min (min (‖s‖ - 1) 1) (H - s.im))
    (hthresh_le_t₀α : threshold ≤ t₀ * α)
    (hthresh_le_1mt₀α : threshold ≤ (1 - t₀) * α) :
    ∀ ε, 0 < ε → ε < threshold → ∀ t ∈ Icc (0 : ℝ) 5, ε / α < |t - t₀| →
      ε < ‖fdBoundaryH H t - s‖ := by
  intro ε hε_pos hε_lt t ht_mem h_abs
  set d := min (min (‖s‖ - 1) 1) (H - s.im)
  have hδ_pos : 0 < ε / α := div_pos hε_pos hα_pos
  have hεα_lt_t₀ : ε / α < t₀ :=
    (div_lt_iff₀ hα_pos).mpr (hε_lt.trans_le hthresh_le_t₀α)
  have hεα_lt_1mt₀ : ε / α < 1 - t₀ :=
    (div_lt_iff₀ hα_pos).mpr (hε_lt.trans_le hthresh_le_1mt₀α)
  have hε_lt_d : ε < d := hε_lt.trans_le hthresh_le_d
  rw [abs_sub_comm] at h_abs
  rcases lt_or_ge t (t₀ - ε / α) with h_left | h_right
  · -- t < t₀ - δ: t is on seg1 (t < 1), norm > ε
    have ht1 : t ≤ 1 := by linarith [hεα_lt_t₀]
    rw [fdBoundary_H_eq_seg1_H ht1, rightEdge_h₀_eq hs_re]
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
        show H - Real.sqrt 3 / 2 = α from hα_def.symm]
    have h_im_pos : H - t * α - s.im > 0 := by
      have : t * α < (t₀ - ε / α) * α := mul_lt_mul_of_pos_right h_left hα_pos
      have : (t₀ - ε / α) * α = t₀ * α - ε / α * α := by ring
      nlinarith [div_mul_cancel₀ ε (ne_of_gt hα_pos), ht₀_mul]
    rw [abs_of_pos h_im_pos]
    have hε_eq : ε = ε / α * α := (div_mul_cancel₀ ε (ne_of_gt hα_pos)).symm
    have h_tα : t * α < (t₀ - ε / α) * α := mul_lt_mul_of_pos_right h_left hα_pos
    nlinarith [ht₀_mul, div_mul_cancel₀ ε (ne_of_gt hα_pos)]
  · -- h_right : t₀ - ε/α ≤ t, h_abs : ε/α < |t₀ - t|
    -- Derive t > t₀ + ε/α
    have ht_gt : t₀ + ε / α < t := by
      rcases le_or_gt t₀ t with h | h
      · rw [abs_of_nonpos (by linarith)] at h_abs; linarith
      · rw [abs_of_pos (by linarith)] at h_abs; linarith
    by_cases ht1 : t ≤ 1
    · -- t on seg1, t > t₀ + ε/α
      rw [fdBoundary_H_eq_seg1_H ht1, rightEdge_h₀_eq hs_re]
      rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
          show H - Real.sqrt 3 / 2 = α from hα_def.symm]
      have h_tα : (t₀ + ε / α) * α < t * α := mul_lt_mul_of_pos_right ht_gt hα_pos
      have h_expand : (t₀ + ε / α) * α = t₀ * α + ε / α * α := by ring
      have h_im_neg : H - t * α - s.im < 0 := by
        nlinarith [ht₀_mul, div_mul_cancel₀ ε (ne_of_gt hα_pos)]
      rw [abs_of_neg h_im_neg]
      nlinarith [ht₀_mul, div_mul_cancel₀ ε (ne_of_gt hα_pos)]
    · -- t > 1: non-seg1 part, use min dist bound
      push Not at ht1
      have : d ≤ ‖fdBoundaryH H t - s‖ :=
        rightEdge_min_dist_from_non_seg1 H s hs_re hs_norm hs_im t ht1 ht_mem.2
      linarith [hε_lt_d]

private lemma rightEdge_h_near (H : ℝ) (_hH_sqrt : Real.sqrt 3 / 2 < H)
    (s : ℂ) (hs_re : s.re = 1 / 2)
    (α : ℝ) (hα_pos : 0 < α) (hα_def : α = H - Real.sqrt 3 / 2)
    (t₀ : ℝ) (_ht₀_pos : 0 < t₀) (_ht₀_lt : t₀ < 1)
    (ht₀_mul : t₀ * α = H - s.im)
    (threshold : ℝ)
    (hthresh_le_t₀α : threshold ≤ t₀ * α)
    (hthresh_le_1mt₀α : threshold ≤ (1 - t₀) * α) :
    ∀ ε, 0 < ε → ε < threshold → ∀ t, |t - t₀| ≤ ε / α → ‖fdBoundaryH H t - s‖ ≤ ε := by
  intro ε hε_pos _hε_lt t h_abs
  have hδ_pos : 0 < ε / α := div_pos hε_pos hα_pos
  have hεα_lt_t₀ : ε / α < t₀ :=
    (div_lt_iff₀ hα_pos).mpr (_hε_lt.trans_le hthresh_le_t₀α)
  have hεα_lt_1mt₀ : ε / α < 1 - t₀ :=
    (div_lt_iff₀ hα_pos).mpr (_hε_lt.trans_le hthresh_le_1mt₀α)
  rw [abs_le] at h_abs
  have ht_lower : t₀ - ε / α ≤ t := by linarith [h_abs.1]
  have ht_upper : t ≤ t₀ + ε / α := by linarith [h_abs.2]
  have ht1 : t ≤ 1 := by linarith
  rw [fdBoundary_H_eq_seg1_H ht1, rightEdge_h₀_eq hs_re]
  rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      show H - Real.sqrt 3 / 2 = α from hα_def.symm]
  rw [abs_le]
  have hε_eq : ε = ε / α * α := (div_mul_cancel₀ ε (ne_of_gt hα_pos)).symm
  have h_tα_upper : t * α ≤ (t₀ + ε / α) * α :=
    mul_le_mul_of_nonneg_right ht_upper (le_of_lt hα_pos)
  have h_tα_lower : (t₀ - ε / α) * α ≤ t * α :=
    mul_le_mul_of_nonneg_right ht_lower (le_of_lt hα_pos)
  constructor <;> nlinarith [ht₀_mul, div_mul_cancel₀ ε (ne_of_gt hα_pos)]

/-- From `ε < threshold ≤ min (t₀·α) ((1-t₀)·α)` derive `0 < ε/α`, `ε/α < t₀`, `ε/α < 1-t₀`. -/
private lemma rightEdge_eps_bounds {α t₀ threshold ε : ℝ} (hα_pos : 0 < α)
    (hthresh_le_t₀α : threshold ≤ t₀ * α) (hthresh_le_1mt₀α : threshold ≤ (1 - t₀) * α)
    (hε_pos : 0 < ε) (hε_lt : ε < threshold) :
    0 < ε / α ∧ ε / α < t₀ ∧ ε / α < 1 - t₀ :=
  ⟨div_pos hε_pos hα_pos,
    (div_lt_iff₀ hα_pos).mpr (hε_lt.trans_le hthresh_le_t₀α),
    (div_lt_iff₀ hα_pos).mpr (hε_lt.trans_le hthresh_le_1mt₀α)⟩

private lemma rightEdge_winding_aux (H : ℝ) (hH_sqrt : Real.sqrt 3 / 2 < H)
    (s : ℂ) (hs_re : s.re = 1 / 2) (hs_norm : ‖s‖ > 1)
    (hs_im_lower : Real.sqrt 3 / 2 < s.im) (hs_im : s.im < H) :
    Tendsto (fun ε => ∫ t in (0 : ℝ)..5,
        if ‖fdBoundaryH H t - s‖ > ε then
          (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0)
      (𝓝[>] 0) (𝓝 (-(↑Real.pi * I))) := by
  set α := H - Real.sqrt 3 / 2 with hα_def
  have hα_pos : 0 < α := by rw [hα_def]; linarith
  set t₀ := (H - s.im) / α with ht₀_def
  have ht₀_pos : 0 < t₀ := div_pos (by linarith) hα_pos
  have ht₀_lt : t₀ < 1 := by rw [ht₀_def, div_lt_one hα_pos]; linarith [hα_def]
  have ht₀_mul : t₀ * α = H - s.im := div_mul_cancel₀ _ (ne_of_gt hα_pos)
  set d := min (min (‖s‖ - 1) 1) (H - s.im)
  have hd_pos : 0 < d := rightEdge_min_dist_pos s hs_norm hs_im
  -- Choose threshold small enough for all bounds
  set threshold := min d (min (t₀ * α) ((1 - t₀) * α))
  have hthresh_pos : 0 < threshold := lt_min hd_pos
    (lt_min (mul_pos ht₀_pos hα_pos) (mul_pos (by linarith) hα_pos))
  have hthresh_le_d : threshold ≤ d := min_le_left _ _
  have hthresh_le_t₀α : threshold ≤ t₀ * α :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hthresh_le_1mt₀α : threshold ≤ (1 - t₀) * α :=
    (min_le_right _ _).trans (min_le_right _ _)
  -- Define δ(ε) = ε/α
  have hδ_fn : ∀ ε, 0 < ε → ε < threshold → 0 < ε / α :=
    fun ε hε _ => div_pos hε hα_pos
  have hδ_small : ∀ ε, 0 < ε → ε < threshold →
      ε / α < min (t₀ - 0) (5 - t₀) := by
    intro ε hε_pos hε_lt
    obtain ⟨_, h1, h2⟩ :=
      rightEdge_eps_bounds hα_pos hthresh_le_t₀α hthresh_le_1mt₀α hε_pos hε_lt
    simpa only [sub_zero] using lt_min h1 (h2.trans (by linarith))
  -- Apply pv_tendsto_of_crossing_limit
  refine ContourIntegral.pv_tendsto_of_crossing_limit
      (t₀ := t₀) (ht₀ := ⟨by linarith, by linarith⟩)
      (threshold := threshold) (hthresh := hthresh_pos)
      (δ := fun ε => ε / α)
      (E := fun ε => Complex.log (-(fdBoundarySeg1H H (t₀ - ε / α) - s)) -
                     Complex.log (-(fdBoundarySeg1H H (t₀ + ε / α) - s)))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- hδ_pos
    exact hδ_fn
  · -- hδ_small
    exact hδ_small
  · -- h_far
    intro ε hε_pos hε_lt
    exact rightEdge_h_far H hH_sqrt s hs_re hs_norm hs_im α hα_pos hα_def t₀ ht₀_pos ht₀_lt
      ht₀_mul threshold hthresh_pos hthresh_le_d hthresh_le_t₀α hthresh_le_1mt₀α
      ε hε_pos hε_lt
  · -- h_near
    intro ε hε_pos hε_lt
    exact rightEdge_h_near H hH_sqrt s hs_re α hα_pos hα_def t₀ ht₀_pos ht₀_lt ht₀_mul
      threshold hthresh_le_t₀α hthresh_le_1mt₀α ε hε_pos hε_lt
  · -- h_ftc: far integrals = E(ε)
    intro ε hε_pos hε_lt
    obtain ⟨hδ_pos, hεα_lt_t₀, hεα_lt_1mt₀⟩ :=
      rightEdge_eps_bounds hα_pos hthresh_le_t₀α hthresh_le_1mt₀α hε_pos hε_lt
    exact (rightEdge_ftc_telescope H hH_sqrt s hs_re hs_im_lower hs_im (ε / α)
      hδ_pos hεα_lt_t₀ hεα_lt_1mt₀).2.2
  · -- hint_left
    intro ε hε_pos hε_lt
    obtain ⟨hδ_pos, hεα_lt_t₀, hεα_lt_1mt₀⟩ :=
      rightEdge_eps_bounds hα_pos hthresh_le_t₀α hthresh_le_1mt₀α hε_pos hε_lt
    exact (rightEdge_ftc_telescope H hH_sqrt s hs_re hs_im_lower hs_im (ε / α)
      hδ_pos hεα_lt_t₀ hεα_lt_1mt₀).1
  · -- hint_right
    intro ε hε_pos hε_lt
    obtain ⟨hδ_pos, hεα_lt_t₀, hεα_lt_1mt₀⟩ :=
      rightEdge_eps_bounds hα_pos hthresh_le_t₀α hthresh_le_1mt₀α hε_pos hε_lt
    exact (rightEdge_ftc_telescope H hH_sqrt s hs_re hs_im_lower hs_im (ε / α)
      hδ_pos hεα_lt_t₀ hεα_lt_1mt₀).2.1
  · -- h_limit: E(ε) → L
    exact rightEdge_E_tendsto H s hs_re α hα_def hα_pos t₀ ht₀_mul threshold hthresh_pos

theorem gWN_fdBoundary_H_eq_neg_half_of_rightEdge (H : ℝ) (hH_sqrt : Real.sqrt 3 / 2 < H)
    (s : ℂ) (hs_re : s.re = 1 / 2) (hs_norm : ‖s‖ > 1)
    (hs_im_lower : Real.sqrt 3 / 2 < s.im) (hs_im : s.im < H) :
    generalizedWindingNumber' (fdBoundaryH H) 0 5 s = -1/2 := by
  apply ContourIntegral.gWN_eq_neg_half_of_pv_tendsto
  have h_tendsto := rightEdge_winding_aux H hH_sqrt s hs_re hs_norm hs_im_lower hs_im
  have hd : ∀ t, deriv (fun t => fdBoundaryH H t - s) t = deriv (fdBoundaryH H) t :=
    fun t => deriv_sub_const (f := fdBoundaryH H) _
  convert h_tendsto using 1
  ext ε; congr 1; ext t; simp only [sub_zero, gt_iff_lt, hd]

/-! ### SingleCrossingData construction for right edge

Demonstrates how the `SingleCrossingData` framework can be used to prove
the right edge winding number result. -/

/-- Construct `SingleCrossingData` for a right edge point.

Bundles all the geometric ingredients (crossing parameter, cutoff function,
far/near bounds, FTC telescope, limit) into a single data structure. -/
def rightEdgeCrossingData (H : ℝ) (hH_sqrt : Real.sqrt 3 / 2 < H)
    (s : ℂ) (hs_re : s.re = 1 / 2) (hs_norm : ‖s‖ > 1)
    (hs_im_lower : Real.sqrt 3 / 2 < s.im) (hs_im : s.im < H) :
    SingleCrossingData (fdBoundaryH H) 0 5 s where
  L := -(↑Real.pi * I)
  t₀ := (H - s.im) / (H - Real.sqrt 3 / 2)
  ht₀ := by
    set α := H - Real.sqrt 3 / 2
    have hα_pos : 0 < α := by change 0 < H - Real.sqrt 3 / 2; linarith
    constructor
    · exact div_pos (by linarith) hα_pos
    · have : (H - s.im) / α < 1 := by
        rw [div_lt_one hα_pos]; change H - s.im < H - Real.sqrt 3 / 2; linarith
      linarith
  δ := fun ε => ε / (H - Real.sqrt 3 / 2)
  threshold :=
    let α := H - Real.sqrt 3 / 2
    let t₀ := (H - s.im) / α
    let d := min (min (‖s‖ - 1) 1) (H - s.im)
    min d (min (t₀ * α) ((1 - t₀) * α))
  hthresh := by
    set α := H - Real.sqrt 3 / 2 with hα_def
    have hα_pos : 0 < α := by change 0 < H - Real.sqrt 3 / 2; linarith
    set t₀ := (H - s.im) / α
    have ht₀_pos : 0 < t₀ := div_pos (by linarith) hα_pos
    have ht₀_lt : t₀ < 1 := by
      rw [div_lt_one hα_pos]; change H - s.im < H - Real.sqrt 3 / 2; linarith
    exact lt_min (rightEdge_min_dist_pos s hs_norm hs_im)
      (lt_min (mul_pos ht₀_pos hα_pos) (mul_pos (by linarith) hα_pos))
  hδ_pos := fun ε hε _ => div_pos hε (by change 0 < H - Real.sqrt 3 / 2; linarith)
  hδ_small := by
    set α := H - Real.sqrt 3 / 2 with hα_def
    have hα_pos : 0 < α := by change 0 < H - Real.sqrt 3 / 2; linarith
    set t₀ := (H - s.im) / α
    have ht₀_lt : t₀ < 1 := by
      rw [div_lt_one hα_pos]; change H - s.im < H - Real.sqrt 3 / 2; linarith
    intro ε hε_pos hε_lt
    obtain ⟨_, h1, h2⟩ := rightEdge_eps_bounds hα_pos
      (le_trans (min_le_right _ _) (min_le_left _ _))
      (le_trans (min_le_right _ _) (min_le_right _ _)) hε_pos hε_lt
    simpa only [sub_zero] using lt_min h1 (h2.trans (by linarith))
  h_far := by
    set α := H - Real.sqrt 3 / 2 with hα_def
    have hα_pos : 0 < α := by change 0 < H - Real.sqrt 3 / 2; linarith
    set t₀ := (H - s.im) / α
    have ht₀_pos : 0 < t₀ := div_pos (by linarith) hα_pos
    have ht₀_lt : t₀ < 1 := by
      rw [div_lt_one hα_pos]; change H - s.im < H - Real.sqrt 3 / 2; linarith
    have ht₀_mul : t₀ * α = H - s.im := div_mul_cancel₀ _ (ne_of_gt hα_pos)
    set threshold := min (min (min (‖s‖ - 1) 1) (H - s.im)) (min (t₀ * α) ((1 - t₀) * α))
    have hthresh_pos : 0 < threshold := lt_min (rightEdge_min_dist_pos s hs_norm hs_im)
      (lt_min (mul_pos ht₀_pos hα_pos) (mul_pos (by linarith) hα_pos))
    intro ε hε_pos hε_lt
    exact rightEdge_h_far H hH_sqrt s hs_re hs_norm hs_im α hα_pos hα_def t₀ ht₀_pos ht₀_lt
      ht₀_mul threshold hthresh_pos (min_le_left _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))
      (le_trans (min_le_right _ _) (min_le_right _ _))
      ε hε_pos hε_lt
  h_near := by
    set α := H - Real.sqrt 3 / 2 with hα_def
    have hα_pos : 0 < α := by change 0 < H - Real.sqrt 3 / 2; linarith
    set t₀ := (H - s.im) / α
    have ht₀_pos : 0 < t₀ := div_pos (by linarith) hα_pos
    have ht₀_lt : t₀ < 1 := by
      rw [div_lt_one hα_pos]; change H - s.im < H - Real.sqrt 3 / 2; linarith
    have ht₀_mul : t₀ * α = H - s.im := div_mul_cancel₀ _ (ne_of_gt hα_pos)
    intro ε hε_pos hε_lt
    exact rightEdge_h_near H hH_sqrt s hs_re α hα_pos hα_def t₀ ht₀_pos ht₀_lt ht₀_mul
      _ (le_trans (min_le_right _ _) (min_le_left _ _))
      (le_trans (min_le_right _ _) (min_le_right _ _))
      ε hε_pos hε_lt
  E := fun ε =>
    let α := H - Real.sqrt 3 / 2
    let t₀ := (H - s.im) / α
    Complex.log (-(fdBoundarySeg1H H (t₀ - ε / α) - s)) -
    Complex.log (-(fdBoundarySeg1H H (t₀ + ε / α) - s))
  h_ftc := by
    set α := H - Real.sqrt 3 / 2 with hα_def
    have hα_pos : 0 < α := by change 0 < H - Real.sqrt 3 / 2; linarith
    set t₀ := (H - s.im) / α
    intro ε hε_pos hε_lt
    obtain ⟨hδ_pos, hεα_lt_t₀, hεα_lt_1mt₀⟩ := rightEdge_eps_bounds hα_pos
      (le_trans (min_le_right _ _) (min_le_left _ _))
      (le_trans (min_le_right _ _) (min_le_right _ _)) hε_pos hε_lt
    exact (rightEdge_ftc_telescope H hH_sqrt s hs_re hs_im_lower hs_im (ε / α)
      hδ_pos hεα_lt_t₀ hεα_lt_1mt₀).2.2
  hint_left := by
    set α := H - Real.sqrt 3 / 2 with hα_def
    have hα_pos : 0 < α := by change 0 < H - Real.sqrt 3 / 2; linarith
    set t₀ := (H - s.im) / α
    intro ε hε_pos hε_lt
    obtain ⟨hδ_pos, hεα_lt_t₀, hεα_lt_1mt₀⟩ := rightEdge_eps_bounds hα_pos
      (le_trans (min_le_right _ _) (min_le_left _ _))
      (le_trans (min_le_right _ _) (min_le_right _ _)) hε_pos hε_lt
    exact (rightEdge_ftc_telescope H hH_sqrt s hs_re hs_im_lower hs_im (ε / α)
      hδ_pos hεα_lt_t₀ hεα_lt_1mt₀).1
  hint_right := by
    set α := H - Real.sqrt 3 / 2 with hα_def
    have hα_pos : 0 < α := by change 0 < H - Real.sqrt 3 / 2; linarith
    set t₀ := (H - s.im) / α
    intro ε hε_pos hε_lt
    obtain ⟨hδ_pos, hεα_lt_t₀, hεα_lt_1mt₀⟩ := rightEdge_eps_bounds hα_pos
      (le_trans (min_le_right _ _) (min_le_left _ _))
      (le_trans (min_le_right _ _) (min_le_right _ _)) hε_pos hε_lt
    exact (rightEdge_ftc_telescope H hH_sqrt s hs_re hs_im_lower hs_im (ε / α)
      hδ_pos hεα_lt_t₀ hεα_lt_1mt₀).2.1
  h_limit := by
    set α := H - Real.sqrt 3 / 2 with hα_def
    have hα_pos : 0 < α := by change 0 < H - Real.sqrt 3 / 2; linarith
    set t₀ := (H - s.im) / α
    have ht₀_pos : 0 < t₀ := div_pos (by linarith) hα_pos
    have ht₀_lt : t₀ < 1 := by
      rw [div_lt_one hα_pos]; change H - s.im < H - Real.sqrt 3 / 2; linarith
    have ht₀_mul : t₀ * α = H - s.im := div_mul_cancel₀ _ (ne_of_gt hα_pos)
    set threshold := min (min (min (‖s‖ - 1) 1) (H - s.im)) (min (t₀ * α) ((1 - t₀) * α))
    have hthresh_pos : 0 < threshold := lt_min (rightEdge_min_dist_pos s hs_norm hs_im)
      (lt_min (mul_pos ht₀_pos hα_pos) (mul_pos (by linarith) hα_pos))
    exact rightEdge_E_tendsto H s hs_re α hα_def hα_pos t₀ ht₀_mul threshold hthresh_pos

/-- Alternative proof of the right edge gWN via the `SingleCrossingData` framework.

Demonstrates that the main theorem can be derived from the framework by
constructing `rightEdgeCrossingData` and applying `gWN_eq_neg_half_of_singleCrossing`. -/
theorem gWN_fdBoundary_H_eq_neg_half_of_rightEdge' (H : ℝ) (hH_sqrt : Real.sqrt 3 / 2 < H)
    (s : ℂ) (hs_re : s.re = 1 / 2) (hs_norm : ‖s‖ > 1)
    (hs_im_lower : Real.sqrt 3 / 2 < s.im) (hs_im : s.im < H) :
    generalizedWindingNumber' (fdBoundaryH H) 0 5 s = -1/2 :=
  gWN_eq_neg_half_of_singleCrossing
    (rightEdgeCrossingData H hH_sqrt s hs_re hs_norm hs_im_lower hs_im)
    rfl

end
