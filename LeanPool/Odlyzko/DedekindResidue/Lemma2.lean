/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib
public import LeanPool.Odlyzko.DedekindResidue.AuxiliaryFunction
public import LeanPool.Odlyzko.DedekindResidue.CompletedZeta.Normalisation

/-!
# Lemma 2: the Fourier transform of the auxiliary function  (T003)

Belabas–Friedman Lemma 2 (eq. 8): the paper-convention Fourier transform (eq. 2,
`F̂(γ) = ∫ F(t)e^{itγ}dt`) of the test function `F_{s,X}` in closed form. This file builds
it bottom-up: the evenness reduction to a cosine transform, the plateau contribution
`2 sin(γT)/γ`, the exponential-tail integration by parts (paper eq. 7), and the assembly.

The main statement is for `γ ≠ 0`; the `sin(γT)/γ` term forces a separate `γ = 0`
companion (the pointwise limit), faithful to the paper's implicit convention.
-/

namespace DedekindResidue

@[expose] public section

open MeasureTheory
open scoped Real


/-- The paper Fourier transform of an even function reduces to a cosine transform on the
positive ray. -/
theorem paperFourierIntegral_even (F : ℝ → ℂ) (hF : ∀ t, F (-t) = F t) (γ : ℝ)
    (hInt : Integrable (fun t : ℝ => F t * Complex.exp (Complex.I * t * γ))) :
    paperFourierIntegral F γ
      = 2 * ∫ t in Set.Ioi (0:ℝ), F t * ((Real.cos (t * γ) : ℝ) : ℂ) := by
  rw [paperFourierIntegral]
  rw [← integral_add_compl (measurableSet_Iic (a := (0:ℝ))) hInt, Set.compl_Iic]
  have hneg : (∫ t in Set.Iic (0:ℝ), F t * Complex.exp (Complex.I * t * γ))
      = ∫ t in Set.Ioi (0:ℝ), F t * Complex.exp (-(Complex.I * t * γ)) := by
    rw [show Set.Iic (0:ℝ) = Set.Iic (-(0:ℝ)) by norm_num]
    rw [← integral_comp_neg_Ioi (f := fun t : ℝ => F t * Complex.exp (Complex.I * t * γ))]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [hF]
    push_cast
    ring_nf
  have hInt' : Integrable (fun t : ℝ => F t * Complex.exp (-(Complex.I * t * γ))) := by
    have h1 := hInt.comp_neg
    refine h1.congr (Filter.Eventually.of_forall (fun t => ?_))
    show F (-t) * Complex.exp (Complex.I * (-t : ℝ) * γ)
      = F t * Complex.exp (-(Complex.I * t * γ))
    rw [hF]
    push_cast
    ring_nf
  rw [hneg, ← integral_add hInt'.integrableOn hInt.integrableOn]
  · rw [show (2 : ℂ) * (∫ t in Set.Ioi (0:ℝ), F t * ((Real.cos (t * γ) : ℝ) : ℂ))
      = ∫ t in Set.Ioi (0:ℝ), 2 * (F t * ((Real.cos (t * γ) : ℝ) : ℂ)) from
      (integral_const_mul 2 _).symm]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [Complex.ofReal_cos, Complex.cos]
    push_cast
    ring_nf

open scoped Real in
/-- The plateau contribution: `∫_0^T cos(tγ) dt = sin(Tγ)/γ` (`γ ≠ 0`, `T ≥ 0`). -/
theorem integral_plateau_cos {T γ : ℝ} (hT : 0 ≤ T) (hγ : γ ≠ 0) :
    (∫ t in Set.Ioc (0:ℝ) T, ((Real.cos (t * γ) : ℝ) : ℂ))
      = ((Real.sin (T * γ) / γ : ℝ) : ℂ) := by
  rw [← intervalIntegral.integral_of_le hT, intervalIntegral.integral_ofReal]
  congr 1
  rw [intervalIntegral.integral_comp_mul_right (fun t => Real.cos t) hγ]
  rw [integral_cos]
  simp [div_eq_inv_mul]

/-- The global exponential bound on the auxiliary function:
`‖F_{s,X}(t)‖ ≤ e^{h_r T}·e^{-h_r|t|}` with `h_r = Re s − 1/2 ≥ 0`, `T = log X ≥ 0`. -/
theorem norm_auxF_le (s : ℂ) {X : ℝ} (hX : 1 ≤ X) (hs : 1/2 ≤ s.re) (t : ℝ) :
    ‖auxF s X t‖ ≤ Real.exp ((s.re - 1/2) * Real.log X)
      * Real.exp (-(s.re - 1/2) * |t|) := by
  have hT : 0 ≤ Real.log X := Real.log_nonneg hX
  have hr : 0 ≤ s.re - 1/2 := by linarith
  rw [auxF]
  split_ifs with h
  · -- plateau: ‖1‖ = 1 ≤ e^{h_r(T − |t|)}
    rw [norm_one, ← Real.exp_add]
    refine Real.one_le_exp ?_
    have : (s.re - 1/2) * Real.log X + -(s.re - 1/2) * |t|
        = (s.re - 1/2) * (Real.log X - |t|) := by ring
    rw [this]
    exact mul_nonneg hr (by linarith)
  · -- tail: (T/|t|)·e^{-h_r(|t|−T)} ≤ e^{h_r T}e^{-h_r|t|}
    push Not at h
    have ht0 : (0:ℝ) < |t| := lt_of_le_of_lt hT h
    rw [norm_mul, Complex.norm_real, Complex.norm_exp]
    have hre : (-(s - 1/2) * Complex.ofReal (|t| - Real.log X)).re
        = -(s.re - 1/2) * (|t| - Real.log X) := by
      simp [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [hre]
    have habs : |Real.log X / (abs t)| = Real.log X / (abs t) :=
      abs_of_nonneg (div_nonneg hT ht0.le)
    rw [Real.norm_eq_abs, habs, ← Real.exp_add]
    have hdivle : Real.log X / |t| ≤ 1 := by
      rw [div_le_one ht0]
      exact h.le
    calc Real.log X / |t| * Real.exp (-(s.re - 1/2) * (|t| - Real.log X))
        ≤ 1 * Real.exp (-(s.re - 1/2) * (|t| - Real.log X)) :=
          mul_le_mul_of_nonneg_right hdivle (Real.exp_pos _).le
      _ = Real.exp (-(s.re - 1/2) * (|t| - Real.log X)) := one_mul _
      _ = Real.exp ((s.re - 1/2) * Real.log X + -(s.re - 1/2) * |t|) := by
          congr 1
          ring

/-- Two-sided exponential decay is integrable on the line. -/
theorem integrable_exp_neg_mul_abs {b : ℝ} (hb : 0 < b) :
    Integrable (fun t : ℝ => Real.exp (-b * |t|)) := by
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-b * |t|)) (Set.Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi 0 hb).congr_fun (fun t ht => ?_) measurableSet_Ioi
    rw [abs_of_pos ht]
  have h1' : IntegrableOn (fun t : ℝ => Real.exp (-b * |t|)) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr h1
  have hmap : Measure.map (MeasurableEquiv.neg ℝ) (volume.restrict (Set.Ici (0:ℝ)))
      = volume.restrict (Set.Iic 0) := by
    rw [show Set.Ici (0:ℝ) = (MeasurableEquiv.neg ℝ) ⁻¹' (Set.Iic 0) by
      ext t
      simp [MeasurableEquiv.neg_apply]]
    rw [← Measure.restrict_map (MeasurableEquiv.neg ℝ).measurable measurableSet_Iic]
    congr 1
    exact Measure.map_neg_eq_self (volume : Measure ℝ)
  have h2 : IntegrableOn (fun t : ℝ => Real.exp (-b * |t|)) (Set.Iic 0) := by
    rw [IntegrableOn, ← hmap, integrable_map_equiv]
    refine h1'.congr (Filter.Eventually.of_forall (fun t => ?_))
    show Real.exp (-b * |t|) = Real.exp (-b * |(-t : ℝ)|)
    rw [abs_neg]
  have hunion := h2.union h1
  rw [Set.Iic_union_Ioi] at hunion
  rwa [← integrableOn_univ]

/-- The paper Fourier kernel against `F_{s,X}` is integrable on the line
(`Re s > 1/2`, `X ≥ 1`). -/
theorem integrable_auxF_kernel (s : ℂ) {X : ℝ} (hX : 1 ≤ X) (hs : 1/2 < s.re) (γ : ℝ) :
    Integrable (fun t : ℝ => auxF s X t * Complex.exp (Complex.I * t * γ)) := by
  refine Integrable.mono'
    ((integrable_exp_neg_mul_abs (b := s.re - 1/2) (by linarith)).const_mul
      (Real.exp ((s.re - 1/2) * Real.log X)))
    (((measurable_auxF s X).mul (by fun_prop)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun t => ?_))
  rw [norm_mul]
  have hker : ‖Complex.exp (Complex.I * t * γ)‖ = 1 := by
    rw [Complex.norm_exp]
    have : (Complex.I * t * γ).re = 0 := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]
    rw [this, Real.exp_zero]
  rw [hker, mul_one]
  exact norm_auxF_le s hX (le_of_lt hs) t

/-- Belabas–Friedman eq. (7), first derivative: on `t > 0`,
`d/dt [e^{-ht}/t] = -(h + 1/t)·e^{-ht}/t`. -/
theorem hasDerivAt_gAux_core (h : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => Complex.exp (-h * u) / u)
      (-(h + 1/t) * (Complex.exp (-h * t) / t)) t := by
  have hden_ne : ((t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ht.ne'
  have hnum : HasDerivAt (fun w : ℂ => Complex.exp (-h * w))
      (Complex.exp (-h * (t : ℂ)) * (-h)) (t : ℂ) := by
    have hlin : HasDerivAt (fun w : ℂ => -h * w) (-h) (t : ℂ) := by
      simpa using (hasDerivAt_id ((t : ℝ) : ℂ)).const_mul (-h)
    exact hlin.cexp
  have hdiv := hnum.div (hasDerivAt_id ((t : ℝ) : ℂ)) hden_ne
  have hcomp := hdiv.comp_ofReal
  refine hcomp.congr_deriv ?_
  simp only [id_eq]
  field_simp
  ring

/-- Belabas–Friedman eq. (7), second derivative: on `t > 0`, the derivative of
`-(h+1/t)·e^{-ht}/t` is `(h² + (2ht+2)/t²)·e^{-ht}/t`. -/
theorem hasDerivAt_gAux_deriv (h : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => -(h + 1/u) * (Complex.exp (-h * u) / u))
      ((h^2 + (2*h*t + 2)/t^2) * (Complex.exp (-h * t) / t)) t := by
  have hden_ne : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  -- all-ℂ computation, then compose with ofReal
  have hfac : HasDerivAt (fun w : ℂ => -(h + 1/w)) (1/(t:ℂ)^2) (t : ℂ) := by
    have hinv : HasDerivAt (fun w : ℂ => w⁻¹) (-((t:ℂ)^2)⁻¹) (t : ℂ) :=
      hasDerivAt_inv hden_ne
    have h2 := (hinv.const_add h).neg
    rw [show (-fun w : ℂ => h + w⁻¹) = (fun w : ℂ => -(h + 1/w)) from
      funext (fun w => by simp [one_div])] at h2
    simpa [neg_neg] using h2
  have hnum : HasDerivAt (fun w : ℂ => Complex.exp (-h * w))
      (Complex.exp (-h * (t : ℂ)) * (-h)) (t : ℂ) := by
    have hlin : HasDerivAt (fun w : ℂ => -h * w) (-h) (t : ℂ) := by
      simpa using (hasDerivAt_id ((t : ℝ) : ℂ)).const_mul (-h)
    exact hlin.cexp
  have hg := hnum.div (hasDerivAt_id ((t : ℝ) : ℂ)) hden_ne
  have hprod := hfac.mul hg
  have hcomp := hprod.comp_ofReal
  refine hcomp.congr_deriv ?_
  simp only [Pi.div_apply, id_eq]
  field_simp
  ring

/-- Master decay bound: a continuous multiplier `φ` bounded on `(T, ∞)` times the
kernel `e^{-ht}/t` (with `Re h > 0`, `T > 0`) is integrable on `(T, ∞)`, by comparison
with `(C/T)·e^{-Re h · t}`. -/
theorem integrableOn_bounded_mul_exp_div {h : ℂ} (hh : 0 < h.re) {T : ℝ} (hT : 0 < T)
    {φ : ℝ → ℂ} (hφc : ContinuousOn φ (Set.Ioi T)) {C : ℝ}
    (hφb : ∀ t ∈ Set.Ioi T, ‖φ t‖ ≤ C) :
    IntegrableOn (fun t : ℝ => φ t * (Complex.exp (-h * t) / t)) (Set.Ioi T) := by
  have hg : ContinuousOn (fun t : ℝ => Complex.exp (-h * t) / (t : ℂ)) (Set.Ioi T) := by
    refine ContinuousOn.div ?_ Complex.continuous_ofReal.continuousOn ?_
    · exact (Complex.continuous_exp.comp (by fun_prop)).continuousOn
    · intro t ht
      exact_mod_cast (hT.trans ht).ne'
  refine Integrable.mono' (g := fun t : ℝ => C / T * Real.exp (-h.re * t))
    ((exp_neg_integrableOn_Ioi T hh).const_mul _)
    ((hφc.mul hg).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : 0 < t := hT.trans ht
  have hnorm : ‖φ t * (Complex.exp (-h * t) / t)‖
      = ‖φ t‖ * (Real.exp (-h.re * t) / t) := by
    rw [norm_mul, norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos htpos]
    congr 2
    simp [Complex.mul_re]
  rw [hnorm]
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hφb t ht)
  have hle : Real.exp (-h.re * t) / t ≤ Real.exp (-h.re * t) / T :=
    div_le_div_of_nonneg_left (Real.exp_pos _).le hT (le_of_lt ht)
  calc ‖φ t‖ * (Real.exp (-h.re * t) / t)
      ≤ C * (Real.exp (-h.re * t) / T) :=
        mul_le_mul (hφb t ht) hle (by positivity) hC0
    _ = C / T * Real.exp (-h.re * t) := by ring

/-- The kernel `e^{-ht}/t` times an eventually-bounded multiplier tends to `0` at `∞`. -/
theorem tendsto_exp_div_mul_atTop {h : ℂ} (hh : 0 < h.re) {v : ℝ → ℂ} {C : ℝ}
    (hv : ∀ᶠ t : ℝ in Filter.atTop, ‖v t‖ ≤ C) :
    Filter.Tendsto (fun t : ℝ => Complex.exp (-h * t) / t * v t) Filter.atTop (nhds 0) := by
  have hexp : Filter.Tendsto (fun t : ℝ => C * Real.exp (-(h.re * t))) Filter.atTop
      (nhds (C * 0)) := by
    refine Filter.Tendsto.const_mul C (Real.tendsto_exp_atBot.comp ?_)
    exact Filter.tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop hh Filter.tendsto_id)
  rw [mul_zero] at hexp
  refine squeeze_zero_norm' ?_ hexp
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ), hv] with t ht hvt
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht
  have hnorm : ‖Complex.exp (-h * t) / t * v t‖
      = Real.exp (-h.re * t) / t * ‖v t‖ := by
    rw [norm_mul, norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos htpos]
    congr 2
    simp [Complex.mul_re]
  rw [hnorm, neg_mul]
  have h1 : Real.exp (-(h.re * t)) / t ≤ Real.exp (-(h.re * t)) :=
    div_le_self (Real.exp_pos _).le ht
  have hv0 : 0 ≤ ‖v t‖ := norm_nonneg _
  calc Real.exp (-(h.re * t)) / t * ‖v t‖
      ≤ Real.exp (-(h.re * t)) * C := by
        exact mul_le_mul h1 hvt hv0 (Real.exp_pos _).le
    _ = C * Real.exp (-(h.re * t)) := by ring

/-- The affine-plus-inverse norm bound `‖h + 1/t‖ ≤ ‖h‖ + 1/T` for `T > 0` and `t ≥ T`,
used throughout the exponential-tail integrations by parts. -/
theorem norm_affine_inv_le (h : ℂ) {t T : ℝ} (hT : 0 < T) (ht : T ≤ t) :
    ‖h + 1 / (t : ℂ)‖ ≤ ‖h‖ + 1 / T := by
  refine le_trans (norm_add_le _ _) ?_
  have : ‖(1 : ℂ) / (t : ℂ)‖ ≤ 1 / T := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (lt_of_lt_of_le hT ht)]
    gcongr
  linarith

/-- The bound `‖(h·t + 1)/t²‖ ≤ ‖h‖/T + 1/T²` for `T > 0` and `t ≥ T`, the second-order
counterpart of `norm_affine_inv_le` for the remainder integrand. -/
theorem norm_affine_div_sq_le (h : ℂ) {t T : ℝ} (hT : 0 < T) (ht : T ≤ t) :
    ‖(h * (t : ℂ) + 1) / (t : ℂ) ^ 2‖ ≤ ‖h‖ / T + 1 / T ^ 2 := by
  have htpos : 0 < t := lt_of_lt_of_le hT ht
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
  have hnum : ‖h * (t : ℂ) + 1‖ ≤ ‖h‖ * t + 1 := by
    have hht : ‖h * (t : ℂ)‖ = ‖h‖ * t := by simp [Complex.norm_real, abs_of_pos htpos]
    calc ‖h * (t : ℂ) + 1‖ ≤ ‖h * (t : ℂ)‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖h‖ * t + 1 := by rw [hht, norm_one]
  calc ‖h * (t : ℂ) + 1‖ / t ^ 2 ≤ (‖h‖ * t + 1) / t ^ 2 := by gcongr
    _ = ‖h‖ / t + 1 / t ^ 2 := by field_simp
    _ ≤ ‖h‖ / T + 1 / T ^ 2 := by gcongr

/-- First integration by parts for the Fourier tail (Belabas–Friedman, proof of Lemma 2):
with `g(t) = e^{-ht}/t`, `∫_T^∞ (g′(t)·sin(tγ)/γ + g(t)·cos(tγ)) dt = -g(T)·sin(Tγ)/γ`. -/
theorem integral_Ioi_gAux_ibp₁ (h : ℂ) (hh : 0 < h.re) {T γ : ℝ} (hT : 0 < T) (hγ : γ ≠ 0) :
    (∫ t in Set.Ioi T,
        (-(h + 1/t) * (Complex.exp (-h * t) / t) * ((Real.sin (t * γ) / γ : ℝ) : ℂ)
          + Complex.exp (-h * t) / t * ((Real.cos (t * γ) : ℝ) : ℂ)))
      = -(Complex.exp (-h * T) / T * ((Real.sin (T * γ) / γ : ℝ) : ℂ)) := by
  have key := integral_Ioi_deriv_mul_eq_sub
    (u := fun t : ℝ => Complex.exp (-h * t) / t)
    (u' := fun t : ℝ => -(h + 1/t) * (Complex.exp (-h * t) / t))
    (v := fun t : ℝ => ((Real.sin (t * γ) / γ : ℝ) : ℂ))
    (v' := fun t : ℝ => ((Real.cos (t * γ) : ℝ) : ℂ))
    (a := T) (a' := Complex.exp (-h * T) / T * ((Real.sin (T * γ) / γ : ℝ) : ℂ)) (b' := 0)
    (fun t ht => hasDerivAt_gAux_core h (hT.trans ht))
    (fun t _ => by
      have hs : HasDerivAt (fun t : ℝ => Real.sin (t * γ) / γ) (Real.cos (t * γ)) t := by
        have := (((hasDerivAt_id t).mul_const γ).sin).div_const γ
        simpa [mul_div_assoc, mul_div_cancel_right₀ _ hγ] using this
      exact hs.ofReal_comp)
    ?_ ?_ ?_
  · rw [key, zero_sub]
  · -- integrability of u'·v + u·v'
    have h₁ : IntegrableOn
        (fun t : ℝ => (-(h + 1/t) * ((Real.sin (t * γ) / γ : ℝ) : ℂ))
          * (Complex.exp (-h * t) / t)) (Set.Ioi T) := by
      refine integrableOn_bounded_mul_exp_div hh hT ?_
        (C := (‖h‖ + 1/T) * (1/|γ|)) ?_
      · refine ContinuousOn.mul (ContinuousOn.neg ?_)
          (Complex.continuous_ofReal.comp
            (by fun_prop : Continuous fun t : ℝ => Real.sin (t * γ) / γ)).continuousOn
        exact continuousOn_const.add (continuousOn_const.div
          Complex.continuous_ofReal.continuousOn
          (fun t ht => by exact_mod_cast (hT.trans ht).ne'))
      · intro t ht
        rw [norm_mul, norm_neg]
        refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
        · exact norm_affine_inv_le h hT (le_of_lt ht)
        · rw [Complex.norm_real, Real.norm_eq_abs, abs_div]
          gcongr
          exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    have h₂ : IntegrableOn
        (fun t : ℝ => ((Real.cos (t * γ) : ℝ) : ℂ) * (Complex.exp (-h * t) / t))
        (Set.Ioi T) := by
      refine integrableOn_bounded_mul_exp_div hh hT
        (Complex.continuous_ofReal.comp
          (by fun_prop : Continuous fun t : ℝ => Real.cos (t * γ))).continuousOn
        (C := 1) ?_
      intro t _
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    have h₁' : IntegrableOn (fun t : ℝ =>
        -(h + 1/t) * (Complex.exp (-h * t) / t) * ((Real.sin (t * γ) / γ : ℝ) : ℂ))
        (Set.Ioi T) := h₁.congr_fun (fun t _ => by ring) measurableSet_Ioi
    have h₂' : IntegrableOn (fun t : ℝ =>
        Complex.exp (-h * t) / t * ((Real.cos (t * γ) : ℝ) : ℂ)) (Set.Ioi T) :=
      h₂.congr_fun (fun t _ => by ring) measurableSet_Ioi
    exact h₁'.add h₂'
  · -- boundary at T
    have hc : ContinuousAt (fun t : ℝ =>
        Complex.exp (-h * t) / t * ((Real.sin (t * γ) / γ : ℝ) : ℂ)) T := by
      have hT0 : ((T : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
      fun_prop (disch := intros; exact hT0)
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  · -- vanishing at ∞
    refine tendsto_exp_div_mul_atTop hh (C := 1/|γ|) ?_
    filter_upwards with t
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div]
    gcongr
    exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩

/-- Integrability of the kernel against a bounded continuous real multiplier. -/
theorem integrableOn_exp_div_mul_real {h : ℂ} (hh : 0 < h.re) {T : ℝ} (hT : 0 < T)
    {ψ : ℝ → ℝ} (hψc : Continuous ψ) {C : ℝ} (hψb : ∀ t, |ψ t| ≤ C) :
    IntegrableOn (fun t : ℝ => Complex.exp (-h * t) / t * ((ψ t : ℝ) : ℂ))
      (Set.Ioi T) := by
  have := integrableOn_bounded_mul_exp_div hh hT
    (φ := fun t : ℝ => ((ψ t : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp hψc).continuousOn (C := C)
    (fun t _ => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hψb t)
  exact this.congr_fun (fun t _ => by ring) measurableSet_Ioi

/-- Integrability of the first-derivative term `-(h+1/t)·e^{-ht}/t` against a bounded
continuous real multiplier. -/
theorem integrableOn_gAux_deriv_mul_real {h : ℂ} (hh : 0 < h.re) {T : ℝ} (hT : 0 < T)
    {ψ : ℝ → ℝ} (hψc : Continuous ψ) {C : ℝ} (hψb : ∀ t, |ψ t| ≤ C) :
    IntegrableOn (fun t : ℝ =>
      -(h + 1/t) * (Complex.exp (-h * t) / t) * ((ψ t : ℝ) : ℂ)) (Set.Ioi T) := by
  have := integrableOn_bounded_mul_exp_div hh hT
    (φ := fun t : ℝ => -(h + 1/t) * ((ψ t : ℝ) : ℂ))
    (C := (‖h‖ + 1/T) * C) ?_ ?_
  · exact this.congr_fun (fun t _ => by ring) measurableSet_Ioi
  · refine ContinuousOn.mul (ContinuousOn.neg ?_)
      (Complex.continuous_ofReal.comp hψc).continuousOn
    exact continuousOn_const.add (continuousOn_const.div
      Complex.continuous_ofReal.continuousOn
      (fun t ht => by exact_mod_cast (hT.trans ht).ne'))
  · intro t ht
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hψb t)
    refine mul_le_mul ?_ (hψb t) (abs_nonneg _) (by positivity)
    exact norm_affine_inv_le h hT (le_of_lt ht)

/-- Integrability of the second-derivative term `(h²+(2ht+2)/t²)·e^{-ht}/t` against a
bounded continuous real multiplier. -/
theorem integrableOn_gAux_deriv2_mul_real {h : ℂ} (hh : 0 < h.re) {T : ℝ} (hT : 0 < T)
    {ψ : ℝ → ℝ} (hψc : Continuous ψ) {C : ℝ} (hψb : ∀ t, |ψ t| ≤ C) :
    IntegrableOn (fun t : ℝ =>
      (h^2 + (2*h*t + 2)/t^2) * (Complex.exp (-h * t) / t) * ((ψ t : ℝ) : ℂ))
      (Set.Ioi T) := by
  have := integrableOn_bounded_mul_exp_div hh hT
    (φ := fun t : ℝ => (h^2 + (2*h*t + 2)/t^2) * ((ψ t : ℝ) : ℂ))
    (C := (‖h‖^2 + (2*‖h‖/T + 2/T^2)) * C) ?_ ?_
  · exact this.congr_fun (fun t _ => by ring) measurableSet_Ioi
  · refine ContinuousOn.mul ?_ (Complex.continuous_ofReal.comp hψc).continuousOn
    refine continuousOn_const.add (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
    intro t ht
    have : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hT.trans ht).ne'
    exact pow_ne_zero 2 this
  · intro t ht
    have htpos : 0 < t := hT.trans ht
    have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hψb t)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul ?_ (hψb t) (abs_nonneg _) (by positivity)
    refine le_trans (norm_add_le _ _) ?_
    have h2 : ‖(2*h*(t:ℂ) + 2)/((t:ℂ))^2‖ ≤ 2*‖h‖/T + 2/T^2 := by
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
      have hnum : ‖2*h*(t:ℂ) + 2‖ ≤ 2*‖h‖*t + 2 := by
        have h2h : ‖2*h*(t:ℂ)‖ = 2*‖h‖*t := by
          simp [Complex.norm_real, abs_of_pos htpos]
        have h22 : ‖(2 : ℂ)‖ = 2 := by norm_num
        calc ‖2*h*(t:ℂ) + 2‖ ≤ ‖2*h*(t:ℂ)‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
          _ = 2*‖h‖*t + 2 := by rw [h2h, h22]
      calc ‖2*h*(t:ℂ) + 2‖ / t^2 ≤ (2*‖h‖*t + 2) / t^2 := by gcongr
        _ = 2*‖h‖/t + 2/t^2 := by field_simp
        _ ≤ 2*‖h‖/T + 2/T^2 := by
            gcongr <;> exact le_of_lt ht
    rw [norm_pow]
    linarith

/-- Second integration by parts for the Fourier tail: with `g(t) = e^{-ht}/t`,
`∫_T^∞ (g″(t)·(-cos(tγ)/γ²) + g′(t)·sin(tγ)/γ) dt = (h+1/T)·g(T)·cos(Tγ)/γ²`,
stated with the boundary value in raw `-(u(T)·v(T))` form. -/
theorem integral_Ioi_gAux_ibp₂ (h : ℂ) (hh : 0 < h.re) {T γ : ℝ} (hT : 0 < T) (hγ : γ ≠ 0) :
    (∫ t in Set.Ioi T,
        ((h^2 + (2*h*t + 2)/t^2) * (Complex.exp (-h * t) / t)
            * ((-Real.cos (t * γ) / γ^2 : ℝ) : ℂ)
          + -(h + 1/t) * (Complex.exp (-h * t) / t) * ((Real.sin (t * γ) / γ : ℝ) : ℂ)))
      = -(-(h + 1/T) * (Complex.exp (-h * T) / T)
          * ((-Real.cos (T * γ) / γ^2 : ℝ) : ℂ)) := by
  have key := integral_Ioi_deriv_mul_eq_sub
    (u := fun t : ℝ => -(h + 1/t) * (Complex.exp (-h * t) / t))
    (u' := fun t : ℝ => (h^2 + (2*h*t + 2)/t^2) * (Complex.exp (-h * t) / t))
    (v := fun t : ℝ => ((-Real.cos (t * γ) / γ^2 : ℝ) : ℂ))
    (v' := fun t : ℝ => ((Real.sin (t * γ) / γ : ℝ) : ℂ))
    (a := T)
    (a' := -(h + 1/T) * (Complex.exp (-h * T) / T) * ((-Real.cos (T * γ) / γ^2 : ℝ) : ℂ))
    (b' := 0)
    (fun t ht => hasDerivAt_gAux_deriv h (hT.trans ht))
    (fun t _ => by
      have h0 : HasDerivAt (fun u : ℝ => Real.cos (u * γ)) (-Real.sin (t * γ) * γ) t := by
        simpa using ((hasDerivAt_id t).mul_const γ).cos
      have hc : HasDerivAt (fun u : ℝ => -Real.cos (u * γ) / γ^2)
          (Real.sin (t * γ) / γ) t := by
        refine ((h0.neg).div_const (γ^2)).congr_deriv ?_
        field_simp
      exact hc.ofReal_comp)
    ?_ ?_ ?_
  · rw [key, zero_sub]
  · -- integrability of u'·v + u·v'
    have h₁ := integrableOn_gAux_deriv2_mul_real hh hT
      (ψ := fun t : ℝ => -Real.cos (t * γ) / γ^2) (by fun_prop) (C := 1/γ^2)
      (fun t => by
        rw [abs_div, abs_neg, abs_pow, sq_abs]
        gcongr
        exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
    have h₂ := integrableOn_gAux_deriv_mul_real hh hT
      (ψ := fun t : ℝ => Real.sin (t * γ) / γ) (by fun_prop) (C := 1/|γ|)
      (fun t => by
        rw [abs_div]
        gcongr
        exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩)
    exact h₁.add h₂
  · -- boundary at T
    have hc : ContinuousAt (fun t : ℝ =>
        -(h + 1/t) * (Complex.exp (-h * t) / t)
          * ((-Real.cos (t * γ) / γ^2 : ℝ) : ℂ)) T := by
      have hT0 : ((T : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
      fun_prop (disch := intros; exact hT0)
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  · -- vanishing at ∞: rewrite into kernel-times-multiplier shape
    have hmain := tendsto_exp_div_mul_atTop (v := fun t : ℝ =>
        -(h + 1/t) * ((-Real.cos (t * γ) / γ^2 : ℝ) : ℂ)) hh
      (C := (‖h‖ + 1/T) * (1/γ^2)) ?_
    · exact hmain.congr (fun t => by simp only [Pi.mul_apply]; ring)
    · filter_upwards [Filter.eventually_ge_atTop (max T 1)] with t ht
      have htT : T ≤ t := le_trans (le_max_left _ _) ht
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      have hb1 : ‖h + 1/(t:ℂ)‖ ≤ ‖h‖ + 1/T := norm_affine_inv_le h hT htT
      have hb2 : |(-Real.cos (t * γ) / γ^2 : ℝ)| ≤ 1/γ^2 := by
        rw [abs_div, abs_neg, abs_pow, sq_abs]
        gcongr
        exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
      exact mul_le_mul hb1 hb2 (abs_nonneg _) (by positivity)

/-- **The Fourier tail identity** (Belabas–Friedman, proof of Lemma 2, eq. (8) tail):
with `g(t) = e^{-ht}/t` and `Re h > 0`, for `T > 0` and `γ ≠ 0`,
`(h²+γ²)·∫_T^∞ g(t)cos(tγ) dt
  = -γ·g(T)·sin(Tγ) + (h+1/T)·g(T)·cos(Tγ) - 2∫_T^∞ cos(tγ)·g(t)·(ht+1)/t² dt`. -/
theorem tail_integral_identity (h : ℂ) (hh : 0 < h.re) {T γ : ℝ} (hT : 0 < T)
    (hγ : γ ≠ 0) :
    (h^2 + γ^2) * ∫ t in Set.Ioi T,
        Complex.exp (-h * t) / t * ((Real.cos (t * γ) : ℝ) : ℂ)
      = -γ * (Complex.exp (-h * T) / T) * ((Real.sin (T * γ) : ℝ) : ℂ)
        + (h + 1/T) * (Complex.exp (-h * T) / T) * ((Real.cos (T * γ) : ℝ) : ℂ)
        - 2 * ∫ t in Set.Ioi T,
            ((Real.cos (t * γ) : ℝ) : ℂ) * (Complex.exp (-h * t) / t)
              * ((h*t + 1)/t^2) := by
  have hγc : ((γ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hγ
  -- the four integrands and their integrability
  have hsin : ∀ t : ℝ, |Real.sin (t * γ) / γ| ≤ 1/|γ| := fun t => by
    rw [abs_div]
    gcongr
    exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have hcos1 : ∀ t : ℝ, |Real.cos (t * γ)| ≤ 1 := fun t =>
    abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hcos2 : ∀ t : ℝ, |(-Real.cos (t * γ) / γ^2 : ℝ)| ≤ 1/γ^2 := fun t => by
    rw [abs_div, abs_neg, abs_pow, sq_abs]
    gcongr
    exact hcos1 t
  have hIB := integrableOn_exp_div_mul_real hh hT
    (ψ := fun t : ℝ => Real.cos (t * γ)) (by fun_prop) hcos1
  have hIA := integrableOn_gAux_deriv_mul_real hh hT
    (ψ := fun t : ℝ => Real.sin (t * γ) / γ) (by fun_prop) hsin
  have hID := integrableOn_gAux_deriv2_mul_real hh hT
    (ψ := fun t : ℝ => -Real.cos (t * γ) / γ^2) (by fun_prop) hcos2
  have hIDcos := integrableOn_gAux_deriv2_mul_real hh hT
    (ψ := fun t : ℝ => Real.cos (t * γ)) (by fun_prop) hcos1
  -- split the two IBP identities
  have h1 := integral_Ioi_gAux_ibp₁ h hh hT hγ
  rw [integral_add hIA hIB] at h1
  have h2 := integral_Ioi_gAux_ibp₂ h hh hT hγ
  rw [integral_add hID hIA] at h2
  -- express the D-integral through the cosine version
  have hDsplit : (∫ t in Set.Ioi T,
      (h^2 + (2*h*t + 2)/t^2) * (Complex.exp (-h * t) / t)
        * ((-Real.cos (t * γ) / γ^2 : ℝ) : ℂ))
      = -(1/(γ:ℂ)^2) * ∫ t in Set.Ioi T,
          (h^2 + (2*h*t + 2)/t^2) * (Complex.exp (-h * t) / t)
            * ((Real.cos (t * γ) : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    push_cast
    ring
  -- and the cosine version through B and the remainder R
  have hRint : IntegrableOn (fun t : ℝ =>
      ((Real.cos (t * γ) : ℝ) : ℂ) * (Complex.exp (-h * t) / t) * ((h*t + 1)/t^2))
      (Set.Ioi T) := by
    have := integrableOn_bounded_mul_exp_div hh hT
      (φ := fun t : ℝ => ((Real.cos (t * γ) : ℝ) : ℂ) * ((h*t + 1)/(t:ℂ)^2))
      (C := 1 * (‖h‖/T + 1/T^2)) ?_ ?_
    · exact this.congr_fun (fun t _ => by ring) measurableSet_Ioi
    · refine ContinuousOn.mul
        (Complex.continuous_ofReal.comp (by fun_prop)).continuousOn
        (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
      intro t ht
      have : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hT.trans ht).ne'
      exact pow_ne_zero 2 this
    · intro t ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hcos1 t) (norm_affine_div_sq_le h hT (le_of_lt ht))
        (norm_nonneg _) (by norm_num)
  have hDcos : (∫ t in Set.Ioi T,
      (h^2 + (2*h*t + 2)/t^2) * (Complex.exp (-h * t) / t)
        * ((Real.cos (t * γ) : ℝ) : ℂ))
      = h^2 * (∫ t in Set.Ioi T,
          Complex.exp (-h * t) / t * ((Real.cos (t * γ) : ℝ) : ℂ))
        + 2 * ∫ t in Set.Ioi T,
            ((Real.cos (t * γ) : ℝ) : ℂ) * (Complex.exp (-h * t) / t)
              * ((h*t + 1)/t^2) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hIB.const_mul _) (hRint.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have htne : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hT.trans ht).ne'
    field_simp
  -- assemble: linear algebra over ℂ
  rw [hDsplit, hDcos] at h2
  push_cast at h1 h2 ⊢
  -- h1 : A + B = -(g(T)·sin(Tγ)/γ), h2 : -(1/γ²)(h²B + 2R) + A = (h+1/T)g(T)cos(Tγ)/γ²-form
  have hA := eq_sub_of_add_eq h1
  rw [hA] at h2
  field_simp at h2 ⊢
  linear_combination (-1 : ℂ) * h2

/-- **Belabas–Friedman Lemma 2, eq. (8)** (the `γ ≠ 0` case): the paper-convention
Fourier transform of the auxiliary function `F_{s,X}` in closed form. With `h = s - 1/2`
and `T = log X`,
`F̂(γ) = 2h²·sin(Tγ)/((h²+γ²)γ) + 2(h+1/T)·cos(Tγ)/(h²+γ²)
        - 4/(h²+γ²)·∫_T^∞ cos(tγ)·F_{s,X}(t)·(ht+1)/t² dt`. -/
theorem fourier_auxF (s : ℂ) {X : ℝ} (hX : 1 < X) (hs : 1/2 < s.re) {γ : ℝ}
    (hγ : γ ≠ 0) :
    paperFourierIntegral (auxF s X) γ
      = 2 * (s - 1/2)^2 / (((s - 1/2)^2 + (γ:ℂ)^2) * γ)
          * ((Real.sin (Real.log X * γ) : ℝ) : ℂ)
        + 2 * ((s - 1/2) + 1/(Real.log X : ℂ)) / ((s - 1/2)^2 + (γ:ℂ)^2)
          * ((Real.cos (Real.log X * γ) : ℝ) : ℂ)
        - 4 / ((s - 1/2)^2 + (γ:ℂ)^2) * ∫ t in Set.Ioi (Real.log X),
            ((Real.cos (t * γ) : ℝ) : ℂ) * auxF s X t * (((s - 1/2)*t + 1)/t^2) := by
  have hT0 : 0 < Real.log X := Real.log_pos hX
  have hTc0 : ((Real.log X : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
  have hγc : ((γ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hγ
  have hh : 0 < (s - 1/2 : ℂ).re := by
    have hre : (s - 1/2 : ℂ).re = s.re - 1/2 := by
      simp [Complex.sub_re]
    rw [hre]
    linarith
  -- the denominator h² + γ² is nonzero when Re h > 0 and γ ≠ 0
  have hne : (s - 1/2)^2 + ((γ:ℝ):ℂ)^2 ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h0
    have h2 := congrArg Complex.im h0
    simp only [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im] at h1 h2
    have hb : (s - 1/2 : ℂ).im = 0 := by nlinarith [hh]
    rw [hb] at h1
    nlinarith [hh, abs_pos.mpr hγ, sq_abs γ]
  -- the tail branch of auxF is the exponential kernel times a constant
  have htail_eq : ∀ t ∈ Set.Ioi (Real.log X), auxF s X t
      = (Real.log X : ℂ) * Complex.exp ((s - 1/2) * (Real.log X : ℂ))
          * (Complex.exp (-(s - 1/2) * t) / t) := by
    intro t ht
    have htpos : 0 < t := hT0.trans ht
    have hnot : ¬ |t| ≤ Real.log X := by
      rw [abs_of_pos htpos]
      exact not_le.mpr ht
    have htc : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast htpos.ne'
    rw [auxF, if_neg hnot, abs_of_pos htpos]
    push_cast
    rw [show -(s - 1/2) * ((t:ℂ) - (Real.log X : ℂ))
        = -(s - 1/2) * (t:ℂ) + (s - 1/2) * (Real.log X : ℂ) by ring, Complex.exp_add]
    field_simp
  -- evenness reduction: F̂ = 2·∫_{(0,∞)} F·cos
  rw [paperFourierIntegral_even (auxF s X) (auxF_neg s X) γ
    (integrable_auxF_kernel s hX.le hs γ)]
  -- split (0,∞) = (0,T] ∪ (T,∞)
  have hIocInt : IntegrableOn
      (fun t : ℝ => auxF s X t * ((Real.cos (t * γ) : ℝ) : ℂ))
      (Set.Ioc 0 (Real.log X)) := by
    have hbase : IntegrableOn (fun t : ℝ => ((Real.cos (t * γ) : ℝ) : ℂ))
        (Set.Ioc 0 (Real.log X)) := Continuous.integrableOn_Ioc (by fun_prop)
    refine hbase.congr_fun (fun t ht => ?_) measurableSet_Ioc
    rw [auxF_of_le s X (by rw [abs_of_pos ht.1]; exact ht.2), one_mul]
  have hIoiInt : IntegrableOn
      (fun t : ℝ => auxF s X t * ((Real.cos (t * γ) : ℝ) : ℂ))
      (Set.Ioi (Real.log X)) := by
    have hbase : IntegrableOn (fun t : ℝ =>
        (Real.log X : ℂ) * Complex.exp ((s - 1/2) * (Real.log X : ℂ))
          * (Complex.exp (-(s - 1/2) * t) / t * ((Real.cos (t * γ) : ℝ) : ℂ)))
        (Set.Ioi (Real.log X)) :=
      (integrableOn_exp_div_mul_real (h := s - 1/2) hh hT0
        (ψ := fun t : ℝ => Real.cos (t * γ)) (by fun_prop)
        (fun t => abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)).const_mul _
    refine hbase.congr_fun (fun t ht => ?_) measurableSet_Ioi
    rw [htail_eq t ht]
    ring
  rw [show Set.Ioi (0:ℝ) = Set.Ioc 0 (Real.log X) ∪ Set.Ioi (Real.log X) from
    (Set.Ioc_union_Ioi_eq_Ioi hT0.le).symm]
  rw [setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hIocInt hIoiInt]
  -- plateau piece
  have hplat : (∫ t in Set.Ioc (0:ℝ) (Real.log X),
      auxF s X t * ((Real.cos (t * γ) : ℝ) : ℂ))
      = ((Real.sin (Real.log X * γ) / γ : ℝ) : ℂ) := by
    rw [← integral_plateau_cos hT0.le hγ]
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    rw [auxF_of_le s X (by rw [abs_of_pos ht.1]; exact ht.2), one_mul]
  -- tail piece: pull out the constant
  have htint : (∫ t in Set.Ioi (Real.log X),
      auxF s X t * ((Real.cos (t * γ) : ℝ) : ℂ))
      = (Real.log X : ℂ) * Complex.exp ((s - 1/2) * (Real.log X : ℂ))
        * ∫ t in Set.Ioi (Real.log X),
            Complex.exp (-(s - 1/2) * t) / t * ((Real.cos (t * γ) : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [htail_eq t ht]
    ring
  -- remainder integral: same constant relation
  have hrint : (∫ t in Set.Ioi (Real.log X),
      ((Real.cos (t * γ) : ℝ) : ℂ) * auxF s X t * (((s - 1/2)*t + 1)/t^2))
      = (Real.log X : ℂ) * Complex.exp ((s - 1/2) * (Real.log X : ℂ))
        * ∫ t in Set.Ioi (Real.log X),
            ((Real.cos (t * γ) : ℝ) : ℂ) * (Complex.exp (-(s - 1/2) * t) / t)
              * (((s - 1/2)*t + 1)/t^2) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [htail_eq t ht]
    ring
  have hEE : Complex.exp ((s - 1/2) * (Real.log X : ℂ))
      * Complex.exp (-(s - 1/2) * (Real.log X : ℂ)) = 1 := by
    rw [← Complex.exp_add,
      show (s - 1/2) * (Real.log X : ℂ) + -(s - 1/2) * (Real.log X : ℂ) = 0 by ring]
    exact Complex.exp_zero
  have hkey := tail_integral_identity (s - 1/2) hh hT0 hγ
  have hI : (∫ t in Set.Ioi (Real.log X),
      Complex.exp (-(s - 1/2) * t) / t * ((Real.cos (t * γ) : ℝ) : ℂ))
      = (-γ * (Complex.exp (-(s - 1/2) * (Real.log X : ℂ)) / (Real.log X : ℂ))
            * ((Real.sin (Real.log X * γ) : ℝ) : ℂ)
          + (s - 1/2 + 1/(Real.log X : ℂ))
            * (Complex.exp (-(s - 1/2) * (Real.log X : ℂ)) / (Real.log X : ℂ))
            * ((Real.cos (Real.log X * γ) : ℝ) : ℂ)
          - 2 * ∫ t in Set.Ioi (Real.log X),
              ((Real.cos (t * γ) : ℝ) : ℂ) * (Complex.exp (-(s - 1/2) * t) / t)
                * (((s - 1/2)*t + 1)/t^2))
        / ((s - 1/2)^2 + (γ:ℂ)^2) := by
    rw [eq_div_iff hne]
    linear_combination hkey
  rw [hplat, htint, hrint, hI]
  push_cast
  field_simp
  have hw0 : ((1:ℂ) + (γ:ℂ)^2*4 - s*4 + s^2*4) ≠ 0 := by
    intro h0
    apply hne
    linear_combination (1/4 : ℂ) * h0
  have hW : ((1:ℂ) + (γ:ℂ)^2*4 - s*4 + s^2*4)
      * ((1:ℂ) + (γ:ℂ)^2*4 - s*4 + s^2*4)⁻¹ = 1 := mul_inv_cancel₀ hw0
  have hEE' : Complex.exp ((Real.log X : ℂ) * (2 * s - 1) / 2)
      * Complex.exp (-((Real.log X : ℂ) * (2 * s - 1) / 2)) = 1 := by
    rw [← Complex.exp_add,
      show (Real.log X : ℂ) * (2 * s - 1) / 2 + -((Real.log X : ℂ) * (2 * s - 1) / 2)
        = 0 by ring]
    exact Complex.exp_zero
  linear_combination
    (-((Real.log X : ℂ)) * Complex.sin ((Real.log X : ℂ) * (γ : ℂ))) * hW
    + (((1:ℂ) + (γ:ℂ)^2*4 - s*4 + s^2*4)⁻¹
        * (-(4:ℂ)*(γ:ℂ)^2*(Real.log X : ℂ)*Complex.sin ((Real.log X : ℂ)*(γ:ℂ))
           + (4*s - 2)*(Real.log X : ℂ)*(γ:ℂ)*Complex.cos ((Real.log X : ℂ)*(γ:ℂ))
           + 4*(γ:ℂ)*Complex.cos ((Real.log X : ℂ)*(γ:ℂ)))) * hEE'

/-- **Belabas–Friedman Lemma 2, the `γ = 0` evaluation**: the paper's eq. (8) at `γ = 0`
(the `sin(γT)/((h²+γ²)γ)`-term becomes its limit `T/h²`, giving
`F̂(0) = 2T + 2(h+1/T)/h² - 4/h²·∫_T^∞ F_{s,X}(t)(ht+1)/t² dt`). Lean's total-function
semantics of `sin(γT)/γ` at `γ = 0` stores junk, so the paper's single display is
faithfully rendered as this separate companion. -/
theorem fourier_auxF_zero (s : ℂ) {X : ℝ} (hX : 1 < X) (hs : 1/2 < s.re) :
    paperFourierIntegral (auxF s X) 0
      = 2 * (Real.log X : ℂ)
        + 2 * ((s - 1/2) + 1/(Real.log X : ℂ)) / (s - 1/2)^2
        - 4 / (s - 1/2)^2 * ∫ t in Set.Ioi (Real.log X),
            auxF s X t * (((s - 1/2)*t + 1)/t^2) := by
  have hT0 : 0 < Real.log X := Real.log_pos hX
  have hTc0 : ((Real.log X : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
  have hh : 0 < (s - 1/2 : ℂ).re := by
    have hre : (s - 1/2 : ℂ).re = s.re - 1/2 := by
      simp [Complex.sub_re]
    rw [hre]
    linarith
  have hhne : (s - 1/2 : ℂ) ≠ 0 := by
    intro h0
    rw [h0] at hh
    simp at hh
  have hh2 : ((s - 1/2 : ℂ))^2 ≠ 0 := pow_ne_zero 2 hhne
  -- the tail branch of auxF is the exponential kernel times a constant
  have htail_eq : ∀ t ∈ Set.Ioi (Real.log X), auxF s X t
      = (Real.log X : ℂ) * Complex.exp ((s - 1/2) * (Real.log X : ℂ))
          * (Complex.exp (-(s - 1/2) * t) / t) := by
    intro t ht
    have htpos : 0 < t := hT0.trans ht
    have hnot : ¬ |t| ≤ Real.log X := by
      rw [abs_of_pos htpos]
      exact not_le.mpr ht
    have htc : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast htpos.ne'
    rw [auxF, if_neg hnot, abs_of_pos htpos]
    push_cast
    rw [show -(s - 1/2) * ((t:ℂ) - (Real.log X : ℂ))
        = -(s - 1/2) * (t:ℂ) + (s - 1/2) * (Real.log X : ℂ) by ring, Complex.exp_add]
    field_simp
  -- evenness reduction at γ = 0
  rw [paperFourierIntegral_even (auxF s X) (auxF_neg s X) 0
    (integrable_auxF_kernel s hX.le hs 0)]
  -- the cosine factor is 1
  have hcos0 : ∀ t : ℝ, ((Real.cos (t * 0) : ℝ) : ℂ) = 1 := fun t => by
    rw [mul_zero, Real.cos_zero, Complex.ofReal_one]
  -- integrability of auxF on the two pieces
  have hIocInt : IntegrableOn (fun t : ℝ => auxF s X t * ((Real.cos (t * 0) : ℝ) : ℂ))
      (Set.Ioc 0 (Real.log X)) := by
    have hbase : IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Set.Ioc 0 (Real.log X)) :=
      Continuous.integrableOn_Ioc (by fun_prop)
    refine hbase.congr_fun (fun t ht => ?_) measurableSet_Ioc
    rw [auxF_of_le s X (by rw [abs_of_pos ht.1]; exact ht.2), hcos0, one_mul]
  have hkerInt : IntegrableOn
      (fun t : ℝ => Complex.exp (-(s - 1/2) * t) / t) (Set.Ioi (Real.log X)) := by
    have := integrableOn_exp_div_mul_real (h := s - 1/2) hh hT0
      (ψ := fun _ : ℝ => 1) continuous_const (C := 1) (fun t => by norm_num)
    refine this.congr_fun (fun t _ => by push_cast; ring) measurableSet_Ioi
  have hIoiInt : IntegrableOn (fun t : ℝ => auxF s X t * ((Real.cos (t * 0) : ℝ) : ℂ))
      (Set.Ioi (Real.log X)) := by
    have hbase : IntegrableOn (fun t : ℝ =>
        (Real.log X : ℂ) * Complex.exp ((s - 1/2) * (Real.log X : ℂ))
          * (Complex.exp (-(s - 1/2) * t) / t)) (Set.Ioi (Real.log X)) :=
      hkerInt.const_mul _
    refine hbase.congr_fun (fun t ht => ?_) measurableSet_Ioi
    rw [htail_eq t ht, hcos0, mul_one]
  rw [show Set.Ioi (0:ℝ) = Set.Ioc 0 (Real.log X) ∪ Set.Ioi (Real.log X) from
    (Set.Ioc_union_Ioi_eq_Ioi hT0.le).symm]
  rw [setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hIocInt hIoiInt]
  -- plateau piece: ∫ 1 over (0, T] is T
  have hplat : (∫ t in Set.Ioc (0:ℝ) (Real.log X),
      auxF s X t * ((Real.cos (t * 0) : ℝ) : ℂ)) = ((Real.log X : ℝ) : ℂ) := by
    rw [show (∫ t in Set.Ioc (0:ℝ) (Real.log X),
        auxF s X t * ((Real.cos (t * 0) : ℝ) : ℂ))
        = ∫ _ in Set.Ioc (0:ℝ) (Real.log X), (1 : ℂ) from
      setIntegral_congr_fun measurableSet_Ioc (fun t ht => by
        rw [auxF_of_le s X (by rw [abs_of_pos ht.1]; exact ht.2), hcos0, one_mul])]
    rw [setIntegral_const, Complex.real_smul, mul_one]
    norm_num [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal hT0.le]
  -- tail piece: pull out the constant
  have htint : (∫ t in Set.Ioi (Real.log X),
      auxF s X t * ((Real.cos (t * 0) : ℝ) : ℂ))
      = (Real.log X : ℂ) * Complex.exp ((s - 1/2) * (Real.log X : ℂ))
        * ∫ t in Set.Ioi (Real.log X), Complex.exp (-(s - 1/2) * t) / t := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [htail_eq t ht, hcos0, mul_one]
  -- remainder integral: same constant relation
  have hrint : (∫ t in Set.Ioi (Real.log X),
      auxF s X t * (((s - 1/2)*t + 1)/t^2))
      = (Real.log X : ℂ) * Complex.exp ((s - 1/2) * (Real.log X : ℂ))
        * ∫ t in Set.Ioi (Real.log X),
            (Complex.exp (-(s - 1/2) * t) / t) * (((s - 1/2)*t + 1)/t^2) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [htail_eq t ht]
    ring
  -- FTC on (T, ∞): the integrand (h²+(2ht+2)/t²)·g has antiderivative -(h+1/t)·g
  have hI2 : IntegrableOn (fun t : ℝ =>
      ((s - 1/2)^2 + (2*(s - 1/2)*t + 2)/t^2) * (Complex.exp (-(s - 1/2) * t) / t))
      (Set.Ioi (Real.log X)) := by
    have := integrableOn_gAux_deriv2_mul_real (h := s - 1/2) hh hT0
      (ψ := fun _ : ℝ => 1) continuous_const (C := 1) (fun t => by norm_num)
    refine this.congr_fun (fun t _ => by push_cast; ring) measurableSet_Ioi
  have hFTC : (∫ t in Set.Ioi (Real.log X),
      ((s - 1/2)^2 + (2*(s - 1/2)*t + 2)/t^2) * (Complex.exp (-(s - 1/2) * t) / t))
      = ((s - 1/2) + 1/(Real.log X : ℂ))
        * (Complex.exp (-(s - 1/2) * (Real.log X : ℂ)) / (Real.log X : ℂ)) := by
    have := integral_Ioi_of_hasDerivAt_of_tendsto'
      (f := fun t : ℝ => -((s - 1/2) + 1/t) * (Complex.exp (-(s - 1/2) * t) / t))
      (f' := fun t : ℝ =>
        ((s - 1/2)^2 + (2*(s - 1/2)*t + 2)/t^2) * (Complex.exp (-(s - 1/2) * t) / t))
      (a := Real.log X) (m := 0)
      (fun t ht => hasDerivAt_gAux_deriv (s - 1/2) (lt_of_lt_of_le hT0 ht))
      hI2 ?_
    · rw [this, zero_sub]
      ring
    · have hmain := tendsto_exp_div_mul_atTop (h := s - 1/2) hh
        (v := fun t : ℝ => -((s - 1/2) + 1/(t:ℂ)))
        (C := ‖(s - 1/2 : ℂ)‖ + 1/Real.log X) ?_
      · exact hmain.congr (fun t => by ring)
      · filter_upwards [Filter.eventually_ge_atTop (max (Real.log X) 1)] with t ht
        have htT : Real.log X ≤ t := le_trans (le_max_left _ _) ht
        rw [norm_neg]
        exact norm_affine_inv_le (s - 1/2) hT0 htT
  -- split the FTC identity into the plain and remainder kernel integrals
  have hRk : IntegrableOn (fun t : ℝ =>
      (Complex.exp (-(s - 1/2) * t) / t) * (((s - 1/2)*t + 1)/t^2))
      (Set.Ioi (Real.log X)) := by
    have := integrableOn_bounded_mul_exp_div (h := s - 1/2) hh hT0
      (φ := fun t : ℝ => ((s - 1/2)*(t:ℂ) + 1)/(t:ℂ)^2)
      (C := ‖(s - 1/2 : ℂ)‖/Real.log X + 1/(Real.log X)^2) ?_ ?_
    · exact this.congr_fun (fun t _ => by ring) measurableSet_Ioi
    · refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
      intro t ht
      have : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hT0.trans ht).ne'
      exact pow_ne_zero 2 this
    · intro t ht
      exact norm_affine_div_sq_le (s - 1/2) hT0 (le_of_lt ht)
  have hsplit : (∫ t in Set.Ioi (Real.log X),
      ((s - 1/2)^2 + (2*(s - 1/2)*t + 2)/t^2) * (Complex.exp (-(s - 1/2) * t) / t))
      = (s - 1/2)^2 * (∫ t in Set.Ioi (Real.log X), Complex.exp (-(s - 1/2) * t) / t)
        + 2 * ∫ t in Set.Ioi (Real.log X),
            (Complex.exp (-(s - 1/2) * t) / t) * (((s - 1/2)*t + 1)/t^2) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hkerInt.const_mul _) (hRk.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have htne : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hT0.trans ht).ne'
    field_simp
  -- assemble
  rw [hplat, htint, hrint]
  have hIval : (∫ t in Set.Ioi (Real.log X), Complex.exp (-(s - 1/2) * t) / t)
      = (((s - 1/2) + 1/(Real.log X : ℂ))
          * (Complex.exp (-(s - 1/2) * (Real.log X : ℂ)) / (Real.log X : ℂ))
        - 2 * ∫ t in Set.Ioi (Real.log X),
            (Complex.exp (-(s - 1/2) * t) / t) * (((s - 1/2)*t + 1)/t^2))
        / (s - 1/2)^2 := by
    rw [eq_div_iff hh2]
    linear_combination hFTC - hsplit
  rw [hIval]
  field_simp
  ring_nf
  have hEE₀ : Complex.exp ((Real.log X : ℂ) * (-1/2) + (Real.log X : ℂ) * s)
      * Complex.exp ((Real.log X : ℂ) * (1/2) - (Real.log X : ℂ) * s) = 1 := by
    rw [← Complex.exp_add,
      show (Real.log X : ℂ) * (-1/2) + (Real.log X : ℂ) * s
          + ((Real.log X : ℂ) * (1/2) - (Real.log X : ℂ) * s) = 0 by ring]
    exact Complex.exp_zero
  linear_combination (((1 : ℂ) - s*4 + s^2*4)⁻¹
    * (4*(Real.log X : ℂ)*s - 2*(Real.log X : ℂ) + 4)) * hEE₀

end

end DedekindResidue
