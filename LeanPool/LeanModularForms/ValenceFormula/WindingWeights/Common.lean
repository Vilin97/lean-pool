/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.Boundary.Smooth
import LeanPool.LeanModularForms.GeneralizedResidueTheory.LogDerivFTC
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import LeanPool.LeanModularForms.ValenceFormula.TrigLemmas

/-!
# Shared Infrastructure for Winding Weight Computations

Common helpers used across the ρ, ρ+1, and i winding weight proofs:
trigonometric identities, old-style segment selectors, the unified arc
formula, and FTC lemmas for log-derivative integrals.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

/-- Work around mathlib 4.29-rc8 instance synthesis issue for `ℝ`-scalar-on-`ℂ`. -/
private noncomputable instance instNormSMulClassRealComplex' : NormSMulClass ℝ ℂ :=
  @NormedSpace.toNormSMulClass ℝ ℂ _ _ _

noncomputable section

theorem fdBoundary_H_at_one_eq_rho_plus_one (H : ℝ) :
    fdBoundaryH H 1 = ellipticPointRhoPlusOne := by
  simp only [fdBoundaryH, show (1 : ℝ) ≤ 1 from le_refl 1, ↓reduceIte,
    ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk,
    Complex.ofReal_one, one_mul]
  ring

theorem fdBoundary_H_at_two_eq_I (H : ℝ) :
    fdBoundaryH H 2 = I := by
  simp only [fdBoundaryH, show ¬((2 : ℝ) ≤ 1) from by norm_num,
             show (2 : ℝ) ≤ 2 from le_refl 2, ↓reduceIte]
  rw [show (↑(Real.pi : ℝ) / 3 + (↑(2 : ℝ) - 1) * (↑(Real.pi : ℝ) / 2 - ↑(Real.pi : ℝ) / 3)) * I =
    ↑(Real.pi / 2) * I from by push_cast; ring,
    exp_real_angle_I, Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast; ring

theorem fdBoundary_H_at_three_eq_rho (H : ℝ) :
    fdBoundaryH H 3 = ellipticPointRho := by
  simp only [fdBoundaryH, show ¬((3 : ℝ) ≤ 1) from by norm_num,
             show ¬((3 : ℝ) ≤ 2) from by norm_num,
             show (3 : ℝ) ≤ 3 from le_refl 3, ↓reduceIte]
  rw [show (↑(Real.pi : ℝ) / 2
        + (↑(3 : ℝ) - 2) * (2 * ↑(Real.pi : ℝ) / 3 - ↑(Real.pi : ℝ) / 2)) * I =
    ↑(2 * Real.pi / 3) * I from by push_cast; ring,
    exp_real_angle_I, cos_two_pi_div_three, sin_two_pi_div_three]
  simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
  push_cast; ring

theorem fdBoundary_H_seg0 (H : ℝ) {t : ℝ} (ht : t ≤ 1) :
    fdBoundaryH H t = 1/2 + (↑H - ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I := by
  simp only [fdBoundaryH, ht, ↓reduceIte]

theorem fdBoundary_H_seg1 (H : ℝ) {t : ℝ} (ht1 : ¬(t ≤ 1)) (ht2 : t ≤ 2) :
    fdBoundaryH H t = exp ((↑(Real.pi : ℝ) / 3 + (↑t - 1) *
      (↑(Real.pi : ℝ) / 2 - ↑(Real.pi : ℝ) / 3)) * I) := by
  simp only [fdBoundaryH, ht1, ht2, ↓reduceIte]

theorem fdBoundary_H_seg2 (H : ℝ) {t : ℝ} (ht1 : ¬(t ≤ 1)) (ht2 : ¬(t ≤ 2))
    (ht3 : t ≤ 3) :
    fdBoundaryH H t = exp ((↑(Real.pi : ℝ) / 2 + (↑t - 2) *
      (2 * ↑(Real.pi : ℝ) / 3 - ↑(Real.pi : ℝ) / 2)) * I) := by
  simp only [fdBoundaryH, ht1, ht2, ht3, ↓reduceIte]

theorem fdBoundary_H_seg3 (H : ℝ) {t : ℝ} (ht1 : ¬(t ≤ 1)) (ht2 : ¬(t ≤ 2))
    (ht3 : ¬(t ≤ 3)) (ht4 : t ≤ 4) :
    fdBoundaryH H t = -1/2 + (↑(Real.sqrt 3) / 2 + (↑t - 3) *
      (↑H - ↑(Real.sqrt 3) / 2)) * I := by simp only [fdBoundaryH, ht1, ht2, ht3, ht4, ↓reduceIte]

theorem fdBoundary_H_seg4 (H : ℝ) {t : ℝ} (ht1 : ¬(t ≤ 1)) (ht2 : ¬(t ≤ 2))
    (ht3 : ¬(t ≤ 3)) (ht4 : ¬(t ≤ 4)) :
    fdBoundaryH H t = (↑t - 9/2) + ↑H * I := by
  simp only [fdBoundaryH, ht1, ht2, ht3, ht4, ↓reduceIte]

theorem fdBoundary_H_eq_arc {H : ℝ} {t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) :
    fdBoundaryH H t = Complex.exp (↑(Real.pi * (1 + t) / 6) * I) := by
  simp only [fdBoundaryH, show ¬(t ≤ 1) from by linarith, ↓reduceIte]
  by_cases h2 : t ≤ 2
  · simp only [h2, ↓reduceIte]; congr 1; push_cast; ring
  · simp only [h2, ↓reduceIte, show t ≤ 3 from le_of_lt ht3]; congr 1; push_cast; ring

lemma ftc_log_piece {g h : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hh_cont : ContinuousOn h (Icc a b))
    (hh_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ h t)
    (hh_deriv_cont : ContinuousOn (deriv h) (Icc a b))
    (hh_slit : ∀ t ∈ Icc a b, h t ∈ Complex.slitPlane)
    (heq : ∀ t ∈ Ioo a b, g t = h t ∧ deriv g t = deriv h t)
    (heq_a : g a = h a) (heq_b : g b = h b) :
    IntervalIntegrable (fun t => deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) :=
  LogDerivFTC.ftc_log_piece hab hh_cont hh_diff hh_deriv_cont hh_slit heq heq_a heq_b

lemma continuousOn_arg_im_nonneg :
    ContinuousOn Complex.arg {z : ℂ | 0 ≤ z.im ∧ z ≠ 0} := by
  intro z ⟨hz_im, hz_ne⟩
  exact ContinuousWithinAt.congr
    ((continuous_re.continuousWithinAt.div continuous_norm.continuousWithinAt
      (norm_ne_zero_iff.mpr hz_ne)).arccos)
    (fun w ⟨hw_im, hw_ne⟩ => Complex.arg_of_im_nonneg_of_ne_zero hw_im hw_ne)
    (Complex.arg_of_im_nonneg_of_ne_zero hz_im hz_ne)

lemma continuousOn_clog_im_nonneg :
    ContinuousOn Complex.log {z : ℂ | 0 ≤ z.im ∧ z ≠ 0} := by
  intro z ⟨hz_im, hz_ne⟩
  have h_fun_eq : Complex.log = fun w => ↑(Real.log ‖w‖) + ↑(Complex.arg w) * I :=
    funext fun _ => rfl
  rw [h_fun_eq]
  apply ContinuousWithinAt.add
  · exact (continuous_ofReal.continuousAt.comp
      ((Real.continuousAt_log (norm_ne_zero_iff.mpr hz_ne)).comp
        continuous_norm.continuousAt)).continuousWithinAt
  · exact (continuous_ofReal.continuousAt.comp_continuousWithinAt
      (continuousOn_arg_im_nonneg z ⟨hz_im, hz_ne⟩)).mul continuousWithinAt_const

/-- Shared integrability/congruence scaffolding for the upper/lower FTC log pieces:
    integrability of `deriv h / h`, ae-agreement of the `g` and `h` log-derivatives on `Ι a b`,
    and the resulting integrability of `deriv g / g`. -/
private lemma logDeriv_integrable_congr {g h : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hh_cont : ContinuousOn h (Icc a b)) (hh_deriv_cont : ContinuousOn (deriv h) (Icc a b))
    (hh_ne : ∀ t ∈ Icc a b, h t ≠ 0)
    (heq : ∀ t ∈ Ioo a b, g t = h t ∧ deriv g t = deriv h t) :
    IntervalIntegrable (fun t => deriv h t / h t) volume a b ∧
    (∀ᵐ t ∂volume, t ∈ Ι a b → deriv g t / g t = deriv h t / h t) ∧
    IntervalIntegrable (fun t => deriv g t / g t) volume a b := by
  have hh_div_cont : ContinuousOn (fun t => deriv h t / h t) (Icc a b) :=
    hh_deriv_cont.div hh_cont hh_ne
  have hint_h : IntervalIntegrable (fun t => deriv h t / h t) volume a b :=
    (hh_div_cont.mono (uIcc_of_le hab ▸ Subset.rfl)).intervalIntegrable
  have hb_ae : ({b} : Set ℝ)ᶜ ∈ ae volume :=
    mem_ae_iff.mpr (by rw [compl_compl]; exact measure_singleton b)
  have h_congr : ∀ᵐ t ∂volume, t ∈ Ι a b → deriv g t / g t = deriv h t / h t := by
    filter_upwards [hb_ae] with t ht_ne_b ht_mem
    have ht_ne : t ≠ b := fun h => ht_ne_b (mem_singleton_iff.mpr h)
    rw [uIoc_of_le hab] at ht_mem
    obtain ⟨hval, hderiv⟩ := heq t ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 ht_ne⟩
    rw [hval, hderiv]
  refine ⟨hint_h, h_congr, ?_⟩
  constructor
  · exact MeasureTheory.Integrable.congr
      (show Integrable _ (volume.restrict (Ioc a b)) from hint_h.1)
      ((MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
        (h_congr.mono (fun t ht hm => (ht (uIoc_of_le hab ▸ hm)).symm)))
  · rw [show Ioc b a = ∅ from Set.Ioc_eq_empty (not_lt.mpr hab)]
    exact MeasureTheory.integrableOn_empty

lemma ftc_log_piece_upper {g h : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hh_cont : ContinuousOn h (Icc a b)) (hh_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ h t)
    (hh_deriv_cont : ContinuousOn (deriv h) (Icc a b)) (hh_im_nn : ∀ t ∈ Icc a b, 0 ≤ (h t).im)
    (hh_ne : ∀ t ∈ Icc a b, h t ≠ 0) (hh_slit_interior : ∀ t ∈ Ioo a b, h t ∈ slitPlane)
    (heq : ∀ t ∈ Ioo a b, g t = h t ∧ deriv g t = deriv h t)
    (heq_a : g a = h a) (heq_b : g b = h b) :
    IntervalIntegrable (fun t => deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) := by
  have hh_log_cont : ContinuousOn (fun t => Complex.log (h t)) (Icc a b) := by
    apply ContinuousOn.comp continuousOn_clog_im_nonneg hh_cont
    intro t ht; exact ⟨hh_im_nn t ht, hh_ne t ht⟩
  obtain ⟨hint_h, h_congr, hint_g⟩ :=
    logDeriv_integrable_congr hab hh_cont hh_deriv_cont hh_ne heq
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    hh_log_cont (fun t ht => (hh_diff t ht).hasDerivAt.clog_real
      (hh_slit_interior t ht)) hint_h
  exact ⟨hint_g, by
    calc ∫ t in a..b, deriv g t / g t
        = ∫ t in a..b, deriv h t / h t := intervalIntegral.integral_congr_ae h_congr
      _ = Complex.log (h b) - Complex.log (h a) := h_ftc
      _ = Complex.log (g b) - Complex.log (g a) := by rw [heq_a, heq_b]⟩

lemma ftc_log_piece_lower {g h : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hh_cont : ContinuousOn h (Icc a b)) (hh_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ h t)
    (hh_deriv_cont : ContinuousOn (deriv h) (Icc a b)) (hh_im_np : ∀ t ∈ Icc a b, (h t).im ≤ 0)
    (hh_ne : ∀ t ∈ Icc a b, h t ≠ 0) (hh_im_neg_interior : ∀ t ∈ Ioo a b, (h t).im < 0)
    (heq : ∀ t ∈ Ioo a b, g t = h t ∧ deriv g t = deriv h t)
    (heq_a : g a = h a) (heq_b : g b = h b) :
    IntervalIntegrable (fun t => deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t =
      Complex.log (-(g b)) - Complex.log (-(g a)) := by
  have hnh_log_cont : ContinuousOn (fun t => Complex.log (-(h t))) (Icc a b) := by
    apply ContinuousOn.comp continuousOn_clog_im_nonneg hh_cont.neg
    intro t ht; constructor
    · simp only [Complex.neg_im, Left.nonneg_neg_iff]; exact hh_im_np t ht
    · exact neg_ne_zero.mpr (hh_ne t ht)
  obtain ⟨hint_h, h_congr, hint_g⟩ :=
    logDeriv_integrable_congr hab hh_cont hh_deriv_cont hh_ne heq
  have hnh_slit : ∀ t ∈ Ioo a b, (-(h t)) ∈ slitPlane := by
    intro t ht; rw [Complex.mem_slitPlane_iff]; right
    simpa only [Complex.neg_im, ne_eq, neg_eq_zero] using ne_of_lt (hh_im_neg_interior t ht)
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    hnh_log_cont (fun t ht => by
      have hda := (hh_diff t ht).hasDerivAt.neg
      have := hda.clog_real (hnh_slit t ht)
      have goal_eq : -deriv h t / -h t = deriv h t / h t := by simp only [neg_div_neg_eq]
      exact goal_eq ▸ this) hint_h
  exact ⟨hint_g, by
    calc ∫ t in a..b, deriv g t / g t
        = ∫ t in a..b, deriv h t / h t := intervalIntegral.integral_congr_ae h_congr
      _ = Complex.log (-(h b)) - Complex.log (-(h a)) := h_ftc
      _ = Complex.log (-(g b)) - Complex.log (-(g a)) := by rw [heq_a, heq_b]⟩

/-- FTC piece helper: given `HasDerivAt h d t` for all `t`, `g = h` on `[a,b]`,
    and `h t ∈ slitPlane`, get integrability + `∫ g'/g = log(g(b)) - log(g(a))`. -/
lemma ftc_piece_of_hasDerivAt {g h : ℝ → ℂ} {a b : ℝ} {d : ℝ → ℂ}
    (hab : a ≤ b) (hd : ∀ t : ℝ, HasDerivAt h (d t) t) (hd_cont : Continuous d)
    (hg_eq : ∀ t, a ≤ t → t ≤ b → g t = h t)
    (hg_eq_nhds : ∀ t ∈ Ioo a b, g =ᶠ[𝓝 t] h)
    (hh_slit : ∀ t ∈ Icc a b, h t ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t => deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) :=
  ftc_log_piece hab (fun t _ => (hd t).continuousAt.continuousWithinAt)
    (fun t _ => (hd t).differentiableAt)
    (by rw [show deriv h = d from funext fun t => (hd t).deriv]; exact hd_cont.continuousOn)
    hh_slit (fun t ht => ⟨hg_eq t (le_of_lt ht.1) (le_of_lt ht.2), (hg_eq_nhds t ht).deriv_eq⟩)
    (hg_eq a (le_refl a) hab) (hg_eq b hab (le_refl b))

/-- FTC piece variant for upper half-plane (`im ≥ 0`). -/
lemma ftc_piece_upper_of_hasDerivAt {g h : ℝ → ℂ} {a b : ℝ} {d : ℝ → ℂ}
    (hab : a ≤ b) (hd : ∀ t : ℝ, HasDerivAt h (d t) t) (hd_cont : Continuous d)
    (hg_eq : ∀ t, a ≤ t → t ≤ b → g t = h t)
    (hg_eq_nhds : ∀ t ∈ Ioo a b, g =ᶠ[𝓝 t] h)
    (hh_im_nn : ∀ t ∈ Icc a b, 0 ≤ (h t).im)
    (hh_ne : ∀ t ∈ Icc a b, h t ≠ 0)
    (hh_slit_int : ∀ t ∈ Ioo a b, h t ∈ slitPlane) :
    IntervalIntegrable (fun t => deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) :=
  ftc_log_piece_upper hab (fun t _ => (hd t).continuousAt.continuousWithinAt)
    (fun t _ => (hd t).differentiableAt)
    (by rw [show deriv h = d from funext fun t => (hd t).deriv]; exact hd_cont.continuousOn)
    hh_im_nn hh_ne hh_slit_int
    (fun t ht => ⟨hg_eq t (le_of_lt ht.1) (le_of_lt ht.2), (hg_eq_nhds t ht).deriv_eq⟩)
    (hg_eq a (le_refl a) hab) (hg_eq b hab (le_refl b))

/-- HasDerivAt for arc parameterization `exp(i*pi*(1+t)/6) - s`. -/
lemma hasDerivAt_arc (s : ℂ) :
    ∀ t : ℝ, HasDerivAt (fun t => exp (↑(Real.pi * (1 + t) / 6) * I) - s)
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I)) t := by
  intro t
  have hf : HasDerivAt (fun s : ℝ => Real.pi * (1 + s) / 6) (Real.pi / 6) t :=
    ((hasDerivAt_id t).add_const (1 : ℝ) |>.const_mul (Real.pi / 6)).congr_of_eventuallyEq
      (Eventually.of_forall fun s => show _ from by simp [id]; ring) |>.congr_deriv (by ring)
  have hci : HasDerivAt (fun s : ℝ => (↑(Real.pi * (1 + s) / 6) : ℂ) * I)
      ((↑(Real.pi / 6) : ℂ) * I) t :=
    (hf.ofReal_comp.mul_const I).congr_deriv (by norm_num [smul_eq_mul])
  exact (hci.cexp.sub (hasDerivAt_const t s)).congr_deriv (by simp only [sub_zero]; ring)

/-- Continuity of the arc derivative. -/
lemma continuous_arc_deriv (_ : ℂ) :
    Continuous (fun t : ℝ => ↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I)) :=
  Continuous.mul continuous_const (Continuous.cexp (Continuous.mul
    (continuous_ofReal.comp (by fun_prop : Continuous fun s => Real.pi * (1 + s) / 6))
    continuous_const))

/-- nhds equality from Ioo agreement. -/
lemma eventuallyEq_of_Ioo_subset {g h : ℝ → ℂ} {a b : ℝ}
    (hg_eq : ∀ t, a < t → t < b → g t = h t) (t : ℝ) (ht : t ∈ Ioo a b) : g =ᶠ[𝓝 t] h :=
  Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) (fun s hs => hg_eq s hs.1 hs.2)

/-- nhds equality from Iio agreement. -/
lemma eventuallyEq_of_Iio {g h : ℝ → ℂ} {b : ℝ}
    (hg_eq : ∀ t, t < b → g t = h t) (t : ℝ) (ht : t < b) : g =ᶠ[𝓝 t] h :=
  Filter.eventually_of_mem (Iio_mem_nhds ht) (fun s hs => hg_eq s hs)

/-- nhds equality from Ioi agreement. -/
lemma eventuallyEq_of_Ioi {g h : ℝ → ℂ} {a : ℝ}
    (hg_eq : ∀ t, a < t → g t = h t) (t : ℝ) (ht : a < t) : g =ᶠ[𝓝 t] h :=
  Filter.eventually_of_mem (Ioi_mem_nhds ht) (fun s hs => hg_eq s hs)

/-- `sin(π/12) < 1/2`, used to bound ε from 2·sin(π/12) bounds. -/
lemma sin_pi_12_lt_half : Real.sin (Real.pi / 12) < 1 / 2 :=
  calc Real.sin (Real.pi / 12) < Real.sin (Real.pi / 6) :=
        Real.sin_lt_sin_of_lt_of_le_pi_div_two (by nlinarith [Real.pi_pos])
          (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    _ = 1 / 2 := Real.sin_pi_div_six

/-- `sin(π/12) > 0`. -/
lemma sin_pi_12_pos : 0 < Real.sin (Real.pi / 12) :=
  ArcCalculus.sin_pos_of_mem_Ioo_zero_pi (by constructor <;> nlinarith [Real.pi_pos])

/-- `arcsin(ε/2) < π/12` whenever `0 < ε < 2·sin(π/12)`. -/
lemma arcsin_eps_div_two_lt_pi_12 {ε : ℝ} (hε_pos : 0 < ε)
    (hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12)) :
    Real.arcsin (ε / 2) < Real.pi / 12 :=
  calc Real.arcsin (ε / 2) < Real.arcsin (Real.sin (Real.pi / 12)) :=
        Real.arcsin_lt_arcsin (by linarith) (by linarith) (Real.sin_le_one _)
    _ = Real.pi / 12 := Real.arcsin_sin (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

end
