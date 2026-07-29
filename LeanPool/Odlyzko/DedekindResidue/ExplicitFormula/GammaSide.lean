/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import LeanPool.Odlyzko.DedekindResidue.Lemma2
public import LeanPool.Odlyzko.DedekindResidue.ExplicitFormula.FourierJordan
public import LeanPool.Odlyzko.DedekindResidue.ExplicitFormula.RectangleContour

/-!
# The archimedean side: digamma integrals (SP2-Γψ)

Poitou's computation of the archimedean part of the explicit formula (Poitou, *Sur les
petits discriminants*, exposé 6, pp. 6-03–6-06) rests on **Gauss's integral formula**
(his eq. (5))

`ψ(z) = -∫₀^∞ (e^{-xz}/(1-e^{-x}) - e^{-x}/x) dx`,   `Re z > 0`,

and its consequences for `Re ψ` on vertical lines. Mathlib defines `Complex.digamma`
(as `logDeriv Gamma`) but has no integral representation (explicit TODO in
`Mathlib.Analysis.SpecialFunctions.Gamma.Digamma`), so this file builds it from the
Euler integral: `Γ'(z) = ∫₀^∞ t^{z-1}e^{-t} log t dt` (mathlib's
`hasDerivAt_GammaIntegral`), the Frullani representation of `log`, and Fubini — the
classical Gauss derivation.

## Main results

- `integral_frullani_log` : `∫₀^∞ (e^{-x} - e^{-tx})/x dx = log t` for `t > 0`.
- `integrableOn_rpow_mul_exp_neg_mul_abs_log` : the log-weighted Euler integrand is
  integrable.
- `abs_frullani_kernel_le` : exponential domination of the Frullani kernel.
- `integral_gauss_inner` : the inner evaluation
  `∫₀^∞ t^{z-1}e^{-t}(e^{-x}-e^{-tx})/x dt = Γ(z)(e^{-x} - (1+x)^{-z})/x`.
- `digamma_eq_integral_gauss_one` : **Gauss's first form**
  `ψ(z) = ∫₀^∞ (e^{-x} - (1+x)^{-z})/x dx` for `Re z > 0`.
- `integrableOn_gauss_one_integrand` : integrability of that integrand.
- `digamma_sub_digamma_eq_integral` : **Poitou's difference form**
  `ψ(w) - ψ(σ) = ∫₀^∞ (e^{-σu} - e^{-wu})/(1-e^{-u}) du` (`x = e^u - 1`), the form his
  eq. (5) is used in — both counterterms cancel in the difference.
-/

@[expose] public section


namespace DedekindResidue

open MeasureTheory Complex intervalIntegral Real Filter SchwartzMap
open scoped FourierTransform ContDiff ComplexConjugate InnerProductSpace ENNReal

/-- The Frullani kernel is a parameter integral of the exponential: for `x > 0`,
`(e^{-x} - e^{-tx})/x = ∫_1^t e^{-sx} ds` (the primitive is `s ↦ -e^{-sx}/x`). -/
theorem frullani_kernel_eq_intervalIntegral (t : ℝ) {x : ℝ} (hx : 0 < x) :
    (Real.exp (-x) - Real.exp (-(t*x))) / x = ∫ s in (1:ℝ)..t, Real.exp (-(s*x)) := by
  have hprim : ∀ s : ℝ, HasDerivAt (fun s' : ℝ => -Real.exp (-(s'*x)) / x)
      (Real.exp (-(s*x))) s := by
    intro s
    have h0 : HasDerivAt (fun s' : ℝ => s' * x) x s := by
      simpa using (hasDerivAt_id s).mul_const x
    have h1 : HasDerivAt (fun s' : ℝ => -(s' * x)) (-x) s := h0.neg
    have h2 := h1.exp
    have h3 : HasDerivAt (fun s' : ℝ => -Real.exp (-(s'*x)))
        (-(Real.exp (-(s*x)) * -x)) s := h2.neg
    have h4 := h3.div_const x
    have hval : -(Real.exp (-(s*x)) * -x) / x = Real.exp (-(s*x)) := by
      rw [div_eq_iff hx.ne']
      ring
    rw [hval] at h4
    exact h4
  have hint : IntervalIntegrable (fun s : ℝ => Real.exp (-(s*x))) volume 1 t := by
    refine ContinuousOn.intervalIntegrable ?_
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hprim s) hint]
  field_simp
  ring

/-- **Frullani integral for the logarithm** (Γψ-c1): for `t > 0`,
`∫₀^∞ (e^{-x} - e^{-tx})/x dx = log t`. The kernel is `∫_1^t e^{-sx} ds`; Fubini and
`∫₀^∞ e^{-sx} dx = 1/s` reduce it to `∫_1^t ds/s`. -/
theorem integral_frullani_log {t : ℝ} (ht : 0 < t) :
    ∫ x in Set.Ioi (0:ℝ), (Real.exp (-x) - Real.exp (-(t*x))) / x = Real.log t := by
  have hker : ∀ x : ℝ, 0 < x →
      (Real.exp (-x) - Real.exp (-(t*x))) / x = ∫ s in (1:ℝ)..t, Real.exp (-(s*x)) :=
    fun x hx => frullani_kernel_eq_intervalIntegral t hx
  -- Fubini on a positive window: ∫_x ∫_{s ∈ Ioc a b} e^{-sx} = ∫_{Ioc a b} 1/s
  have haux : ∀ a b : ℝ, 0 < a → a ≤ b →
      (∫ x in Set.Ioi (0:ℝ), ∫ s in Set.Ioc a b, Real.exp (-(s*x)))
        = ∫ s in Set.Ioc a b, 1/s := by
    intro a b ha hab
    have hmeasp : AEStronglyMeasurable (Function.uncurry fun x s : ℝ => Real.exp (-(s*x)))
        ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioc a b))) := by
      refine Continuous.aestronglyMeasurable ?_
      have : (Function.uncurry fun x s : ℝ => Real.exp (-(s*x)))
          = fun p : ℝ × ℝ => Real.exp (-(p.2 * p.1)) := by
        funext p
        rw [Function.uncurry]
      rw [this]
      fun_prop
    have hprod : Integrable (Function.uncurry fun x s : ℝ => Real.exp (-(s*x)))
        ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioc a b))) := by
      have hdom : Integrable (fun p : ℝ × ℝ => Real.exp (-(a * p.1)) * 1)
          ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioc a b))) := by
        refine MeasureTheory.Integrable.mul_prod
          (f := fun x : ℝ => Real.exp (-(a*x))) (g := fun _ : ℝ => (1:ℝ)) ?_ ?_
        · have := exp_neg_integrableOn_Ioi (0:ℝ) ha
          refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
          show Real.exp (-a * x) = Real.exp (-(a*x))
          rw [show -a * x = -(a*x) by ring]
        · exact MeasureTheory.integrableOn_const (by
            rw [Real.volume_Ioc]
            exact ENNReal.ofReal_ne_top)
      refine hdom.mono' hmeasp ?_
      rw [Measure.prod_restrict]
      refine (MeasureTheory.ae_restrict_iff'
        (measurableSet_Ioi.prod measurableSet_Ioc)).mpr ?_
      refine Filter.Eventually.of_forall (fun p hp => ?_)
      have hx : 0 < p.1 := hp.1
      have hs : a ≤ p.2 := hp.2.1.le
      show ‖Real.exp (-(p.2 * p.1))‖ ≤ Real.exp (-(a * p.1)) * 1
      rw [Real.norm_eq_abs, Real.abs_exp, mul_one]
      refine Real.exp_le_exp.mpr ?_
      rw [neg_le_neg_iff]
      exact mul_le_mul_of_nonneg_right hs hx.le
    have hswap := MeasureTheory.integral_integral_swap hprod
    rw [hswap]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
    have hspos : 0 < s := lt_trans ha hs.1
    exact integral_exp_neg_mul_Ioi hspos
  rcases le_or_gt 1 t with h1t | h1t
  · have h0 : (∫ x in Set.Ioi (0:ℝ), (Real.exp (-x) - Real.exp (-(t*x))) / x)
        = ∫ x in Set.Ioi (0:ℝ), ∫ s in Set.Ioc (1:ℝ) t, Real.exp (-(s*x)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [Set.mem_Ioi] at hx
      rw [hker x hx, intervalIntegral.integral_of_le h1t]
    rw [h0, haux 1 t one_pos h1t]
    have h2 : (∫ s in Set.Ioc (1:ℝ) t, 1/s) = ∫ s in (1:ℝ)..t, 1/s := by
      rw [intervalIntegral.integral_of_le h1t]
    rw [h2, integral_one_div (by
      intro h
      rw [Set.mem_uIcc] at h
      rcases h with ⟨h', _⟩ | ⟨_, h'⟩ <;> linarith), div_one]
  · have h0 : (∫ x in Set.Ioi (0:ℝ), (Real.exp (-x) - Real.exp (-(t*x))) / x)
        = ∫ x in Set.Ioi (0:ℝ), -∫ s in Set.Ioc t 1, Real.exp (-(s*x)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [Set.mem_Ioi] at hx
      rw [hker x hx, intervalIntegral.integral_symm,
        intervalIntegral.integral_of_le h1t.le]
    rw [h0, MeasureTheory.integral_neg, haux t 1 ht h1t.le]
    have h2 : (∫ s in Set.Ioc t (1:ℝ), 1/s) = ∫ s in t..(1:ℝ), 1/s := by
      rw [intervalIntegral.integral_of_le h1t.le]
    rw [h2, integral_one_div (by
      intro h
      rw [Set.mem_uIcc] at h
      rcases h with ⟨h', _⟩ | ⟨_, h'⟩ <;> linarith)]
    rw [one_div, Real.log_inv, neg_neg]

/-- The log-weighted Gamma integrand is integrable: `∫₀^∞ t^{a-1} e^{-t} |log t| dt < ∞`
for `a > 0` (Γψ-c2b). Near `0` the log loses to `t^{a/2}`; at infinity `log t ≤ t`. -/
theorem integrableOn_rpow_mul_exp_neg_mul_abs_log {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (a-1) * Real.exp (-t) * |Real.log t|)
      (Set.Ioi 0) := by
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => t ^ (a-1) * Real.exp (-t) * |Real.log t|)
      (volume.restrict (Set.Ioi 0)) := by
    refine Measurable.aestronglyMeasurable ?_ |>.restrict
    fun_prop
  refine MeasureTheory.Integrable.mono'
    (g := fun t => (2/a) * (Real.exp (-t) * t ^ (a/2 - 1))
      + Real.exp (-t) * t ^ ((a+1) - 1))
    (((Real.GammaIntegral_convergent (by positivity : (0:ℝ) < a/2)).const_mul
        (2/a)).add
      (Real.GammaIntegral_convergent (by positivity : (0:ℝ) < a+1)))
    hmeas ?_
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
  refine Filter.Eventually.of_forall (fun t ht => ?_)
  rw [Set.mem_Ioi] at ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rcases le_or_gt t 1 with h1 | h1
  · -- near 0: |log t| = -log t ≤ (2/a) t^{-a/2}
    have hlog : |Real.log t| ≤ (2/a) * t ^ (-(a/2)) := by
      rw [abs_of_nonpos (Real.log_nonpos ht.le h1)]
      have h2 : Real.log (t ^ (-(a/2))) ≤ t ^ (-(a/2)) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_rpow ht] at h2
      have h3 : -Real.log t = (2/a) * (-(a/2) * Real.log t) := by
        field_simp
      rw [h3]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      nlinarith [Real.rpow_nonneg ht.le (-(a/2))]
    calc t ^ (a-1) * Real.exp (-t) * |Real.log t|
        ≤ t ^ (a-1) * Real.exp (-t) * ((2/a) * t ^ (-(a/2))) := by
          refine mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = (2/a) * (Real.exp (-t) * (t ^ (a-1) * t ^ (-(a/2)))) := by ring
      _ = (2/a) * (Real.exp (-t) * t ^ (a/2 - 1)) := by
          rw [← Real.rpow_add ht]
          ring_nf
      _ ≤ (2/a) * (Real.exp (-t) * t ^ (a/2 - 1))
          + Real.exp (-t) * t ^ ((a+1) - 1) := by
          have : (0:ℝ) ≤ Real.exp (-t) * t ^ ((a+1) - 1) := by positivity
          linarith
  · -- tail: |log t| = log t ≤ t
    have hlog : |Real.log t| ≤ t := by
      rw [abs_of_nonneg (Real.log_nonneg h1.le)]
      have := Real.log_le_sub_one_of_pos ht
      linarith
    calc t ^ (a-1) * Real.exp (-t) * |Real.log t|
        ≤ t ^ (a-1) * Real.exp (-t) * t := by
          refine mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = Real.exp (-t) * (t ^ (a-1) * t ^ (1:ℝ)) := by
          rw [Real.rpow_one]
          ring
      _ = Real.exp (-t) * t ^ ((a+1) - 1) := by
          rw [← Real.rpow_add ht]
          ring_nf
      _ ≤ (2/a) * (Real.exp (-t) * t ^ (a/2 - 1))
          + Real.exp (-t) * t ^ ((a+1) - 1) := by
          have : (0:ℝ) ≤ (2/a) * (Real.exp (-t) * t ^ (a/2 - 1)) := by positivity
          linarith

/-- The Frullani kernel is dominated exponentially: `|(e^{-x} - e^{-tx})/x| ≤ |t-1| e^{-mx}`
with `m = min 1 t`, hence integrable on `(0, ∞)` for each `t > 0` (Γψ-c2 slice bound). -/
theorem abs_frullani_kernel_le (t : ℝ) {x : ℝ} (hx : 0 < x) :
    |(Real.exp (-x) - Real.exp (-(t*x))) / x| ≤ |t - 1| * Real.exp (-(min 1 t * x)) := by
  rw [frullani_kernel_eq_intervalIntegral t hx]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := Real.exp (-(min 1 t * x))) (a := (1:ℝ)) (b := t)
    (f := fun s : ℝ => Real.exp (-(s*x)))
    (fun s hs => by
      rw [Real.norm_eq_abs, Real.abs_exp]
      refine Real.exp_le_exp.mpr ?_
      rw [neg_le_neg_iff]
      refine mul_le_mul_of_nonneg_right ?_ hx.le
      rw [Set.mem_uIoc] at hs
      rcases hs with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact le_trans (min_le_left _ _) h1.le
      · exact le_trans (min_le_right _ _) h1.le)
  rw [Real.norm_eq_abs] at hbound
  calc |∫ s in (1:ℝ)..t, Real.exp (-(s*x))|
      ≤ Real.exp (-(min 1 t * x)) * |t - 1| := hbound
    _ = |t - 1| * Real.exp (-(min 1 t * x)) := mul_comm _ _

/-- Inner evaluation of the Gauss double integral (Γψ-c2, fixed `x > 0`):
`∫₀^∞ t^{z-1} e^{-t} (e^{-x} - e^{-tx})/x dt = Γ(z)·(e^{-x} - (1+x)^{-z})/x`. -/
theorem integral_gauss_inner {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ in Set.Ioi 0, (t:ℂ) ^ (z-1)
        * ((Real.exp (-t) * ((Real.exp (-x) - Real.exp (-(t*x))) / x) : ℝ) : ℂ))
      = Complex.Gamma z * ((((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)) / (x:ℂ)) := by
  -- the two Gamma-type integrals
  have hint1 : IntegrableOn (fun t : ℝ => (t:ℂ) ^ (z-1) * ((Real.exp (-t) : ℝ) : ℂ))
      (Set.Ioi 0) := by
    have h0 := Complex.GammaIntegral_convergent hz
    refine h0.congr_fun (fun t _ => ?_) measurableSet_Ioi
    rw [mul_comm]
  have hcont_cpow : ContinuousOn (fun t : ℝ => (t:ℂ) ^ (z-1)) (Set.Ioi 0) := by
    refine continuousOn_of_forall_continuousAt (fun t ht => ?_)
    have h0 : ContinuousAt (fun w : ℂ => w ^ (z - 1)) (t:ℂ) :=
      continuousAt_cpow_const <| Complex.ofReal_mem_slitPlane.2 ht
    exact ContinuousAt.comp h0 Complex.continuous_ofReal.continuousAt
  have hint2 : IntegrableOn
      (fun t : ℝ => (t:ℂ) ^ (z-1) * ((Real.exp (-((1+x)*t)) : ℝ) : ℂ)) (Set.Ioi 0) := by
    have h0 := Complex.GammaIntegral_convergent hz
    refine MeasureTheory.Integrable.mono' (h0.norm) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine ContinuousOn.mul hcont_cpow ?_
      exact (Complex.continuous_ofReal.comp (by fun_prop)).continuousOn
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      rw [Set.mem_Ioi] at ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
      calc ‖(t:ℂ) ^ (z-1)‖ * Real.exp (-((1+x)*t))
          ≤ ‖(t:ℂ) ^ (z-1)‖ * Real.exp (-t) := by
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            refine Real.exp_le_exp.mpr ?_
            nlinarith
        _ = Real.exp (-t) * ‖(t:ℂ) ^ (z-1)‖ := mul_comm _ _
  -- expand the kernel and split
  have hsplit : (∫ t : ℝ in Set.Ioi 0, (t:ℂ) ^ (z-1)
      * ((Real.exp (-t) * ((Real.exp (-x) - Real.exp (-(t*x))) / x) : ℝ) : ℂ))
      = (((Real.exp (-x) : ℝ) : ℂ) / (x:ℂ))
          * (∫ t : ℝ in Set.Ioi 0, (t:ℂ) ^ (z-1) * ((Real.exp (-t) : ℝ) : ℂ))
        - ((1:ℂ) / (x:ℂ))
          * ∫ t : ℝ in Set.Ioi 0, (t:ℂ) ^ (z-1) * ((Real.exp (-((1+x)*t)) : ℝ) : ℂ) := by
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_sub ((hint1.const_mul _)) ((hint2.const_mul _))]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [Set.mem_Ioi] at ht
    have hxne : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    push_cast
    rw [show -((1+(x:ℂ))*(t:ℂ)) = -(t:ℂ) + -((t:ℂ)*(x:ℂ)) by ring, Complex.exp_add]
    field_simp
  rw [hsplit]
  -- evaluate both integrals
  have hval1 : (∫ t : ℝ in Set.Ioi 0, (t:ℂ) ^ (z-1) * ((Real.exp (-t) : ℝ) : ℂ))
      = Complex.Gamma z := by
    rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [mul_comm]
  have hval2 : (∫ t : ℝ in Set.Ioi 0, (t:ℂ) ^ (z-1) * ((Real.exp (-((1+x)*t)) : ℝ) : ℂ))
      = ((1+x : ℝ) : ℂ) ^ (-z) * Complex.Gamma z := by
    have h0 := Complex.integral_cpow_mul_exp_neg_mul_Ioi hz (by linarith : (0:ℝ) < 1+x)
    have h1 : (∫ t : ℝ in Set.Ioi 0, (t:ℂ) ^ (z-1) * ((Real.exp (-((1+x)*t)) : ℝ) : ℂ))
        = ∫ t : ℝ in Set.Ioi 0, (t:ℂ) ^ (z-1) * Complex.exp (-(((1+x:ℝ):ℂ) * (t:ℂ))) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
      congr 1
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [h1, h0]
    have harg : ((1+x : ℝ) : ℂ).arg ≠ π := by
      rw [Complex.arg_ofReal_of_nonneg (by linarith)]
      exact Real.pi_ne_zero.symm
    rw [one_div, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
  rw [hval1, hval2]
  ring

/-- **Gauss's first integral for the digamma function** (Γψ-c2): for `Re z > 0`,
`ψ(z) = ∫₀^∞ (e^{-x} - (1+x)^{-z})/x dx`. Obtained from `Γ'(z) = ∫ t^{z-1}e^{-t} log t dt`
by writing `log t` as a Frullani integral and applying Fubini. -/
theorem digamma_eq_integral_gauss_one {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma z = ∫ x in Set.Ioi (0:ℝ),
      (((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)) / (x:ℂ) := by
  -- Γ' as the log-weighted Euler integral
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : Complex.Gamma =ᶠ[nhds z] Complex.GammaIntegral := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact Complex.Gamma_eq_integral hw
  have hd : HasDerivAt Complex.Gamma
      (∫ t : ℝ in Set.Ioi 0, (t:ℂ) ^ (z - 1)
        * (((Real.log t : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ))) z :=
    (Complex.hasDerivAt_GammaIntegral hz).congr_of_eventuallyEq hev
  -- continuity of the double integrand on the open quadrant
  have hcont_cpow : ContinuousOn (fun t : ℝ => (t:ℂ) ^ (z-1)) (Set.Ioi 0) := by
    refine continuousOn_of_forall_continuousAt (fun t ht => ?_)
    have h0 : ContinuousAt (fun w : ℂ => w ^ (z - 1)) (t:ℂ) :=
      continuousAt_cpow_const <| Complex.ofReal_mem_slitPlane.2 ht
    exact ContinuousAt.comp h0 Complex.continuous_ofReal.continuousAt
  set F : ℝ × ℝ → ℂ := fun p => (p.1:ℂ) ^ (z-1)
      * ((Real.exp (-p.1) * ((Real.exp (-p.2) - Real.exp (-(p.1*p.2))) / p.2) : ℝ) : ℂ)
    with hF
  have hcontF : ContinuousOn F ((Set.Ioi 0) ×ˢ (Set.Ioi 0)) := by
    refine ContinuousOn.mul ?_ ?_
    · exact hcont_cpow.comp continuous_fst.continuousOn (fun p hp => hp.1)
    · refine Complex.continuous_ofReal.comp_continuousOn ?_
      refine ContinuousOn.mul (by fun_prop) ?_
      refine ContinuousOn.div (by fun_prop) continuous_snd.continuousOn ?_
      exact fun p hp => (hp.2 : (0:ℝ) < p.2).ne'
  have hmeasF : AEStronglyMeasurable (Function.uncurry fun t x : ℝ => F (t, x))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    rw [Measure.prod_restrict]
    have huncurry : (Function.uncurry fun t x : ℝ => F (t, x)) = F := by
      funext p
      rw [Function.uncurry]
    rw [huncurry]
    exact hcontF.aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ioi)
  -- pointwise |K|-integral: exactly |log t|
  have hKabs : ∀ t : ℝ, 0 < t →
      (∫ x in Set.Ioi (0:ℝ), |(Real.exp (-x) - Real.exp (-(t*x))) / x|)
        = |Real.log t| := by
    intro t ht
    rcases le_or_gt 1 t with h1t | h1t
    · have hpos : ∀ x ∈ Set.Ioi (0:ℝ),
          |(Real.exp (-x) - Real.exp (-(t*x))) / x|
            = (Real.exp (-x) - Real.exp (-(t*x))) / x := by
        intro x hx
        rw [Set.mem_Ioi] at hx
        refine abs_of_nonneg ?_
        refine div_nonneg ?_ hx.le
        have : t * x ≥ x := by nlinarith
        have := Real.exp_le_exp.mpr (neg_le_neg this)
        linarith
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpos,
        integral_frullani_log ht, abs_of_nonneg (Real.log_nonneg h1t)]
    · have hneg : ∀ x ∈ Set.Ioi (0:ℝ),
          |(Real.exp (-x) - Real.exp (-(t*x))) / x|
            = -((Real.exp (-x) - Real.exp (-(t*x))) / x) := by
        intro x hx
        rw [Set.mem_Ioi] at hx
        refine abs_of_nonpos ?_
        refine div_nonpos_of_nonpos_of_nonneg ?_ hx.le
        have : t * x ≤ x := by nlinarith
        have := Real.exp_le_exp.mpr (neg_le_neg this)
        linarith
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hneg,
        MeasureTheory.integral_neg, integral_frullani_log ht,
        abs_of_nonpos (Real.log_nonpos ht.le h1t.le)]
  -- product integrability
  have hprodF : Integrable (Function.uncurry fun t x : ℝ => F (t, x))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    refine (MeasureTheory.integrable_prod_iff hmeasF).mpr ⟨?_, ?_⟩
    · -- slices in x, for a.e. t
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      rw [Set.mem_Ioi] at ht
      simp only [Function.uncurry_apply_pair]
      have hm : 0 < min 1 t := lt_min one_pos ht
      refine MeasureTheory.Integrable.mono'
        (g := fun x => ‖(t:ℂ) ^ (z-1)‖ * Real.exp (-t)
          * (|t - 1| * Real.exp (-(min 1 t * x)))) ?_ ?_ ?_
      · have h0 : IntegrableOn (fun x : ℝ => Real.exp (-(min 1 t * x))) (Set.Ioi 0) := by
          have := exp_neg_integrableOn_Ioi (0:ℝ) hm
          refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
          show Real.exp (-(min 1 t) * x) = Real.exp (-(min 1 t * x))
          rw [show -(min 1 t) * x = -(min 1 t * x) by ring]
        have h1 := (h0.const_mul (|t - 1|)).const_mul (‖(t:ℂ) ^ (z-1)‖ * Real.exp (-t))
        refine h1.congr (Filter.Eventually.of_forall (fun x => ?_))
        ring
      · have hFy : (fun y => F (t, y))
            = fun y => ((t:ℂ)^(z-1))
              * ((Real.exp (-t) * ((Real.exp (-y) - Real.exp (-(t*y))) / y) : ℝ) : ℂ) := by
          funext y
          rw [hF]
        rw [hFy]
        refine (Measurable.aestronglyMeasurable ?_).restrict
        exact (Complex.measurable_ofReal.comp (by fun_prop)).const_mul _
      · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
        refine Filter.Eventually.of_forall (fun x hx => ?_)
        rw [Set.mem_Ioi] at hx
        rw [hF]
        simp only
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, Real.abs_exp]
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact abs_frullani_kernel_le t hx
    · -- the norm-outer function equals t^{a-1} e^{-t} |log t|
      have hcongr : ∀ t ∈ Set.Ioi (0:ℝ),
          (∫ x, ‖(Function.uncurry fun t x : ℝ => F (t, x)) (t, x)‖
            ∂(volume.restrict (Set.Ioi 0)))
          = t ^ (z.re - 1) * Real.exp (-t) * |Real.log t| := by
        intro t ht
        rw [Set.mem_Ioi] at ht
        have h0 : ∀ x ∈ Set.Ioi (0:ℝ),
            ‖(Function.uncurry fun t x : ℝ => F (t, x)) (t, x)‖
              = (t ^ (z.re - 1) * Real.exp (-t))
                * |(Real.exp (-x) - Real.exp (-(t*x))) / x| := by
          intro x hx
          simp only [Function.uncurry_apply_pair]
          rw [hF]
          simp only
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, Real.abs_exp,
            Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
          ring
        rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h0,
          MeasureTheory.integral_const_mul, hKabs t ht]
      have hbase := integrableOn_rpow_mul_exp_neg_mul_abs_log (a := z.re) hz
      refine hbase.congr ?_
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      exact (hcongr t ht).symm
  -- Γ' as the double integral
  have hlog_inner : ∀ t ∈ Set.Ioi (0:ℝ),
      (t:ℂ) ^ (z - 1) * (((Real.log t : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ))
        = ∫ x in Set.Ioi (0:ℝ), F (t, x) := by
    intro t ht
    rw [Set.mem_Ioi] at ht
    rw [← integral_frullani_log ht]
    rw [show ((∫ x in Set.Ioi (0:ℝ), (Real.exp (-x) - Real.exp (-(t*x))) / x : ℝ) : ℂ)
        = ∫ x in Set.Ioi (0:ℝ), (((Real.exp (-x) - Real.exp (-(t*x))) / x : ℝ) : ℂ) from
      integral_complex_ofReal.symm]
    rw [show (t:ℂ) ^ (z - 1)
        * ((∫ x in Set.Ioi (0:ℝ), (((Real.exp (-x) - Real.exp (-(t*x))) / x : ℝ) : ℂ))
          * ((Real.exp (-t) : ℝ) : ℂ))
        = ((t:ℂ) ^ (z - 1) * ((Real.exp (-t) : ℝ) : ℂ))
          * ∫ x in Set.Ioi (0:ℝ), (((Real.exp (-x) - Real.exp (-(t*x))) / x : ℝ) : ℂ)
      from by ring]
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [hF]
    simp only
    push_cast
    ring
  have hΓ' : (∫ t : ℝ in Set.Ioi 0, (t:ℂ) ^ (z - 1)
      * (((Real.log t : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ)))
      = ∫ t in Set.Ioi (0:ℝ), ∫ x in Set.Ioi (0:ℝ), F (t, x) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hlog_inner
  have hswap := MeasureTheory.integral_integral_swap hprodF
  have hswap' : (∫ t in Set.Ioi (0:ℝ), ∫ x in Set.Ioi (0:ℝ), F (t, x))
      = ∫ x in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ), F (t, x) := hswap
  -- inner evaluation
  have hinner_eval : ∀ x ∈ Set.Ioi (0:ℝ), (∫ t in Set.Ioi (0:ℝ), F (t, x))
      = Complex.Gamma z
        * ((((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)) / (x:ℂ)) := by
    intro x hx
    rw [Set.mem_Ioi] at hx
    rw [← integral_gauss_inner hz hx]
  have hΓne : Complex.Gamma z ≠ 0 := by
    refine Complex.Gamma_ne_zero (fun m => ?_)
    intro h
    rw [h] at hz
    simp only [Complex.neg_re, Complex.natCast_re] at hz
    have h2 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  rw [Complex.digamma_def, logDeriv_apply, hd.deriv, hΓ', hswap',
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hinner_eval,
    MeasureTheory.integral_const_mul, mul_comm, mul_div_assoc, div_self hΓne, mul_one]

/-- The Gauss integrand `(e^{-x} - (1+x)^{-z})/x` is integrable on `(0, ∞)` for
`Re z > 0`: bounded near `0` (the singularities cancel to first order) and dominated by
`e^{-x}/x₀ + x^{-(1+Re z)}` in the tail. -/
theorem integrableOn_gauss_one_integrand {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn
      (fun x : ℝ => (((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)) / (x:ℂ))
      (Set.Ioi 0) := by
  set x₀ : ℝ := min 1 (1/(‖z‖+1)) with hx₀
  have hx₀pos : 0 < x₀ := lt_min one_pos (by positivity)
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => (((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)) / (x:ℂ))
      (volume.restrict (Set.Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.div ?_ (Complex.continuous_ofReal.continuousOn) ?_
    · refine ContinuousOn.sub ?_ ?_
      · exact (Complex.continuous_ofReal.comp (by fun_prop)).continuousOn
      · refine continuousOn_of_forall_continuousAt (fun x hx => ?_)
        rw [Set.mem_Ioi] at hx
        have h0 : ContinuousAt (fun w : ℂ => w ^ (-z)) ((1+x : ℝ):ℂ) :=
          continuousAt_cpow_const <| Complex.ofReal_mem_slitPlane.2 (by linarith)
        have hinner : ContinuousAt (fun x : ℝ => ((1+x : ℝ) : ℂ)) x := by fun_prop
        exact ContinuousAt.comp (x := x) h0 hinner
    · intro x hx
      rw [Set.mem_Ioi] at hx
      exact_mod_cast hx.ne'
  rw [show Set.Ioi (0:ℝ) = Set.Ioc 0 x₀ ∪ Set.Ioi x₀ by
    rw [Set.Ioc_union_Ioi_eq_Ioi hx₀pos.le], MeasureTheory.integrableOn_union]
  constructor
  · -- near 0: bounded by 1 + 2‖z‖
    refine MeasureTheory.Integrable.mono'
      (g := fun _ => 1 + 2*‖z‖)
      (MeasureTheory.integrableOn_const (by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top))
      (hmeas.mono_measure (Measure.restrict_mono Set.Ioc_subset_Ioi_self le_rfl)) ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    obtain ⟨hx0, hxle⟩ := hx
    have hlog_le : Real.log (1+x) ≤ x := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1+x)
      linarith
    have hlog_nonneg : 0 ≤ Real.log (1+x) := Real.log_nonneg (by linarith)
    have hznorm : ‖-z * (Real.log (1+x) : ℂ)‖ ≤ 1 := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hlog_nonneg]
      have h1 : Real.log (1+x) ≤ 1/(‖z‖+1) := by
        calc Real.log (1+x) ≤ x := hlog_le
          _ ≤ x₀ := hxle
          _ ≤ 1/(‖z‖+1) := min_le_right _ _
      calc ‖z‖ * Real.log (1+x) ≤ ‖z‖ * (1/(‖z‖+1)) :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ ≤ 1 := by
            rw [mul_one_div, div_le_one (by positivity)]
            linarith
    have hcpow_exp : ((1+x : ℝ) : ℂ) ^ (-z)
        = Complex.exp (-z * (Real.log (1+x) : ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero (by
        exact_mod_cast (by linarith : (0:ℝ) < 1+x).ne'),
        ← Complex.ofReal_log (by linarith : (0:ℝ) ≤ 1+x)]
      ring_nf
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    rw [div_le_iff₀ hx0]
    have htri : ‖((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)‖
        ≤ ‖((Real.exp (-x) : ℝ) : ℂ) - 1‖ + ‖(1:ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)‖ := by
      calc ‖((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)‖
          = ‖(((Real.exp (-x) : ℝ) : ℂ) - 1) + ((1:ℂ) - ((1+x : ℝ) : ℂ) ^ (-z))‖ := by
            ring_nf
        _ ≤ _ := norm_add_le _ _
    have h1 : ‖((Real.exp (-x) : ℝ) : ℂ) - 1‖ ≤ x := by
      rw [show ((Real.exp (-x) : ℝ) : ℂ) - 1 = ((Real.exp (-x) - 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by
          have := Real.exp_le_one_iff.mpr (by linarith : -x ≤ 0)
          linarith)]
      have := Real.add_one_le_exp (-x)
      linarith
    have h2 : ‖(1:ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)‖ ≤ 2*‖z‖*x := by
      rw [hcpow_exp, ← norm_neg]
      have h3 := Complex.norm_exp_sub_one_le hznorm
      calc ‖-(1 - Complex.exp (-z * (Real.log (1+x) : ℂ)))‖
          = ‖Complex.exp (-z * (Real.log (1+x) : ℂ)) - 1‖ := by
            rw [neg_sub]
        _ ≤ 2 * ‖-z * (Real.log (1+x) : ℂ)‖ := h3
        _ = 2 * (‖z‖ * Real.log (1+x)) := by
            rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hlog_nonneg]
        _ ≤ 2*‖z‖*x := by
            have := mul_le_mul_of_nonneg_left hlog_le (norm_nonneg z)
            nlinarith [norm_nonneg z]
    calc ‖((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)‖
        ≤ x + 2*‖z‖*x := by
          have := htri
          linarith
      _ = (1 + 2*‖z‖) * x := by ring
  · -- tail: dominated by e^{-x}/x₀ + x^{-(1+Re z)}
    refine MeasureTheory.Integrable.mono'
      (g := fun x => (1/x₀) * Real.exp (-x) + x ^ (-(1 + z.re)))
      (MeasureTheory.Integrable.add ?_ ?_)
      (hmeas.mono_measure (Measure.restrict_mono (Set.Ioi_subset_Ioi hx₀pos.le) le_rfl)) ?_
    · have h0 := exp_neg_integrableOn_Ioi x₀ (one_pos)
      have h1 : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi x₀) := by
        refine h0.congr_fun (fun x _ => ?_) measurableSet_Ioi
        show Real.exp (-1 * x) = Real.exp (-x)
        rw [neg_one_mul]
      exact h1.const_mul _
    · refine integrableOn_Ioi_rpow_of_lt (by linarith) hx₀pos
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Set.mem_Ioi] at hx
      have hx0 : 0 < x := lt_trans hx₀pos hx
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
      rw [div_le_iff₀ hx0]
      have hnorm_sub : ‖((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)‖
          ≤ Real.exp (-x) + (1+x) ^ (-z.re) := by
        calc ‖((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)‖
            ≤ ‖((Real.exp (-x) : ℝ) : ℂ)‖ + ‖((1+x : ℝ) : ℂ) ^ (-z)‖ := norm_sub_le _ _
          _ = Real.exp (-x) + (1+x) ^ (-z.re) := by
              rw [Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
                Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0:ℝ) < 1+x),
                Complex.neg_re]
      calc ‖((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)‖
          ≤ Real.exp (-x) + (1+x) ^ (-z.re) := hnorm_sub
        _ ≤ (1/x₀) * Real.exp (-x) * x + x ^ (-(1 + z.re)) * x := by
            have hp1 : Real.exp (-x) ≤ (1/x₀) * Real.exp (-x) * x := by
              have h5 : (1:ℝ) ≤ x/x₀ := (one_le_div hx₀pos).mpr hx.le
              calc Real.exp (-x) = Real.exp (-x) * 1 := (mul_one _).symm
                _ ≤ Real.exp (-x) * (x/x₀) :=
                    mul_le_mul_of_nonneg_left h5 (Real.exp_pos _).le
                _ = (1/x₀) * Real.exp (-x) * x := by ring
            have hp2 : (1+x) ^ (-z.re) ≤ x ^ (-(1 + z.re)) * x := by
              have h4 : (1+x) ^ (-z.re) ≤ x ^ (-z.re) := by
                refine Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by linarith)
              calc (1+x) ^ (-z.re) ≤ x ^ (-z.re) := h4
                _ = x ^ (-(1 + z.re)) * x := by
                    rw [show x ^ (-(1 + z.re)) * x
                        = x ^ (-(1 + z.re)) * x ^ (1:ℝ) by rw [Real.rpow_one],
                      ← Real.rpow_add hx0]
                    ring_nf
            linarith
        _ = ((1/x₀) * Real.exp (-x) + x ^ (-(1 + z.re))) * x := by ring

/-- **Poitou's difference form of Gauss's formula** (p. 6-03, eq. (5), applied to a
difference so that both counterterms cancel): for `σ > 0` real and `Re w > 0`,

`ψ(w) - ψ(σ) = ∫₀^∞ (e^{-σu} - e^{-wu})/(1 - e^{-u}) du`.

Change of variables `x = e^u - 1` in the difference of two Gauss first-form integrals. -/
theorem digamma_sub_digamma_eq_integral {σ : ℝ} (hσ : 0 < σ) {w : ℂ} (hw : 0 < w.re) :
    Complex.digamma w - Complex.digamma (σ:ℂ)
      = ∫ u in Set.Ioi (0:ℝ),
          (Complex.exp (-(σ:ℂ) * (u:ℂ)) - Complex.exp (-w * (u:ℂ)))
            / (1 - Complex.exp (-(u:ℂ))) := by
  have hσ' : 0 < ((σ:ℂ)).re := by simpa using hσ
  rw [digamma_eq_integral_gauss_one hw, digamma_eq_integral_gauss_one hσ',
    ← MeasureTheory.integral_sub (integrableOn_gauss_one_integrand hw)
      (integrableOn_gauss_one_integrand hσ')]
  -- the e^{-x}/x counterterms cancel
  have hstep1 : (∫ x in Set.Ioi (0:ℝ),
      ((((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-w)) / (x:ℂ)
        - (((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-(σ:ℂ))) / (x:ℂ)))
      = ∫ x in Set.Ioi (0:ℝ),
          (((1+x : ℝ) : ℂ) ^ (-(σ:ℂ)) - ((1+x : ℝ) : ℂ) ^ (-w)) / (x:ℂ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    ring
  rw [hstep1]
  -- change of variables x = e^u - 1
  set g : ℝ → ℝ := fun u => Real.exp u - 1 with hg
  have himg : g '' Set.Ioi 0 = Set.Ioi (0:ℝ) := by
    ext x
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [hg]
      simp only
      have := Real.exp_lt_exp.mpr hu
      rw [Real.exp_zero] at this
      linarith
    · intro hx
      refine ⟨Real.log (1+x), ?_, ?_⟩
      · refine Real.log_pos ?_
        linarith
      · rw [hg]
        simp only
        rw [Real.exp_log (by linarith)]
        ring
  have hderiv : ∀ u ∈ Set.Ioi (0:ℝ), HasDerivWithinAt g (Real.exp u) (Set.Ioi 0) u := by
    intro u _
    exact ((Real.hasDerivAt_exp u).sub_const 1).hasDerivWithinAt
  have hinj : Set.InjOn g (Set.Ioi 0) := by
    have hmono : StrictMono g := by
      intro a b hab
      rw [hg]
      simp only
      have := Real.exp_lt_exp.mpr hab
      linarith
    exact (hmono.injective).injOn
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hderiv hinj
    (fun x : ℝ => (((1+x : ℝ) : ℂ) ^ (-(σ:ℂ)) - ((1+x : ℝ) : ℂ) ^ (-w)) / (x:ℂ))
  rw [himg] at hcov
  rw [hcov]
  -- pointwise identification with the exponential kernel
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
  rw [Set.mem_Ioi] at hu
  have hexp1 : (0:ℝ) < Real.exp u - 1 := by
    have := Real.exp_lt_exp.mpr hu
    rw [Real.exp_zero] at this
    linarith
  have hbase : (1 + (g u) : ℝ) = Real.exp u := by
    rw [hg]
    ring
  -- (e^u)^{-z} = exp(-zu) for both exponents
  have hcpow : ∀ z : ℂ, ((1 + (g u) : ℝ) : ℂ) ^ (-z) = Complex.exp (-z * (u:ℂ)) := by
    intro z
    rw [hbase, Complex.cpow_def_of_ne_zero (by
      exact_mod_cast (Real.exp_pos u).ne'),
      ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
    ring_nf
  rw [show |Real.exp u| = Real.exp u from abs_of_pos (Real.exp_pos u)]
  rw [Complex.real_smul, hcpow, hcpow]
  have hgu : ((g u : ℝ) : ℂ) = ((Real.exp u - 1 : ℝ) : ℂ) := by
    rw [hg]
  rw [hgu]
  have hne1 : ((Real.exp u - 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hexp1.ne'
  have hne2 : (1 : ℂ) - Complex.exp (-(u:ℂ)) ≠ 0 := by
    have h2 : Complex.exp (-(u:ℂ)) = ((Real.exp (-u) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]
      push_cast
      ring_nf
    rw [h2]
    have h3 : Real.exp (-u) < 1 := by
      have := Real.exp_lt_exp.mpr (show -u < 0 by linarith)
      rwa [Real.exp_zero] at this
    intro h
    have h4 := sub_eq_zero.mp h
    have h5 : (1:ℝ) = Real.exp (-u) := by exact_mod_cast h4
    linarith
  rw [← mul_div_assoc, div_eq_div_iff hne1 hne2]
  have hkey : ((Real.exp u : ℝ) : ℂ) * (1 - Complex.exp (-(u:ℂ)))
      = ((Real.exp u - 1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    push_cast
    rw [mul_sub, mul_one, ← Complex.exp_add]
    simp
  linear_combination (Complex.exp (-(σ:ℂ) * (u:ℂ)) - Complex.exp (-w * (u:ℂ))) * hkey

/-- The exponential difference kernel of `digamma_sub_digamma_eq_integral` is integrable
on `(0, ∞)`: near `0` the numerator vanishes to first order, and the tail decays
exponentially. -/
theorem integrableOn_digamma_diff_kernel {σ : ℝ} (hσ : 0 < σ) {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun u : ℝ =>
      (Complex.exp (-(σ:ℂ) * (u:ℂ)) - Complex.exp (-w * (u:ℂ)))
        / (1 - Complex.exp (-(u:ℂ)))) (Set.Ioi 0) := by
  set u₀ : ℝ := min 1 (1/(‖w - (σ:ℂ)‖+1)) with hu₀
  have hu₀pos : 0 < u₀ := lt_min one_pos (by positivity)
  have hu₀le1 : u₀ ≤ 1 := min_le_left _ _
  have hden_pos : ∀ u : ℝ, 0 < u → 0 < 1 - Real.exp (-u) := by
    intro u hu
    have := Real.exp_lt_exp.mpr (show -u < 0 by linarith)
    rw [Real.exp_zero] at this
    linarith
  have hden_real : ∀ u : ℝ, (1:ℂ) - Complex.exp (-(u:ℂ))
      = ((1 - Real.exp (-u) : ℝ) : ℂ) := by
    intro u
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_exp]
    push_cast
    ring_nf
  have hne : ∀ u : ℝ, 0 < u → (1:ℂ) - Complex.exp (-(u:ℂ)) ≠ 0 := by
    intro u hu
    rw [hden_real u]
    exact_mod_cast (hden_pos u hu).ne'
  have hmeas : AEStronglyMeasurable (fun u : ℝ =>
      (Complex.exp (-(σ:ℂ) * (u:ℂ)) - Complex.exp (-w * (u:ℂ)))
        / (1 - Complex.exp (-(u:ℂ)))) (volume.restrict (Set.Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro u hu
    rw [Set.mem_Ioi] at hu
    exact hne u hu
  have hden_lower : ∀ u : ℝ, 0 < u → u / Real.exp u ≤ 1 - Real.exp (-u) := by
    intro u hu
    have h1 := Real.add_one_le_exp u
    rw [Real.exp_neg u, div_le_iff₀ (Real.exp_pos u), sub_mul, one_mul,
      inv_mul_cancel₀ (Real.exp_pos u).ne']
    linarith
  have hnum_re : ∀ u : ℝ, (-(σ:ℂ) * (u:ℂ)).re = -(σ * u) := by
    intro u
    simp [Complex.mul_re]
  rw [show Set.Ioi (0:ℝ) = Set.Ioc 0 u₀ ∪ Set.Ioi u₀ by
    rw [Set.Ioc_union_Ioi_eq_Ioi hu₀pos.le], MeasureTheory.integrableOn_union]
  constructor
  · -- near 0: bounded
    refine MeasureTheory.Integrable.mono'
      (g := fun _ => 2 * ‖w - (σ:ℂ)‖ * Real.exp 1)
      (MeasureTheory.integrableOn_const (by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top))
      (hmeas.mono_measure (Measure.restrict_mono Set.Ioc_subset_Ioi_self le_rfl)) ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    obtain ⟨hu0, huu₀⟩ := hu
    have hu1 : u ≤ 1 := le_trans huu₀ hu₀le1
    have hnum : Complex.exp (-(σ:ℂ) * (u:ℂ)) - Complex.exp (-w * (u:ℂ))
        = Complex.exp (-(σ:ℂ) * (u:ℂ)) * (1 - Complex.exp (-(w - (σ:ℂ)) * (u:ℂ))) := by
      rw [mul_sub, mul_one, ← Complex.exp_add]
      ring_nf
    have hv : ‖(-(w - (σ:ℂ)) * (u:ℂ))‖ = ‖w - (σ:ℂ)‖ * u := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0]
    have hsmall : ‖(-(w - (σ:ℂ)) * (u:ℂ))‖ ≤ 1 := by
      rw [hv]
      have h1 : u ≤ 1/(‖w - (σ:ℂ)‖+1) := le_trans huu₀ (min_le_right _ _)
      calc ‖w - (σ:ℂ)‖ * u ≤ ‖w - (σ:ℂ)‖ * (1/(‖w - (σ:ℂ)‖+1)) :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ ≤ 1 := by
            rw [mul_one_div, div_le_one (by positivity)]
            linarith
    rw [hnum, norm_div, norm_mul]
    have h1 : ‖Complex.exp (-(σ:ℂ) * (u:ℂ))‖ ≤ 1 := by
      rw [Complex.norm_exp, hnum_re u]
      refine Real.exp_le_one_iff.mpr ?_
      have := mul_pos hσ hu0
      linarith
    have h3 : ‖(1:ℂ) - Complex.exp (-(w - (σ:ℂ)) * (u:ℂ))‖ ≤ 2 * (‖w - (σ:ℂ)‖ * u) := by
      rw [← norm_neg, neg_sub]
      calc ‖Complex.exp (-(w - (σ:ℂ)) * (u:ℂ)) - 1‖
          ≤ 2 * ‖(-(w - (σ:ℂ)) * (u:ℂ))‖ := Complex.norm_exp_sub_one_le hsmall
        _ = 2 * (‖w - (σ:ℂ)‖ * u) := by rw [hv]
    rw [hden_real u, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hden_pos u hu0), div_le_iff₀ (hden_pos u hu0)]
    have h5 := hden_lower u hu0
    calc ‖Complex.exp (-(σ:ℂ) * (u:ℂ))‖
          * ‖(1:ℂ) - Complex.exp (-(w - (σ:ℂ)) * (u:ℂ))‖
        ≤ 1 * (2 * (‖w - (σ:ℂ)‖ * u)) :=
          mul_le_mul h1 h3 (norm_nonneg _) zero_le_one
      _ = 2 * ‖w - (σ:ℂ)‖ * u := by ring
      _ ≤ 2 * ‖w - (σ:ℂ)‖ * Real.exp 1 * (u / Real.exp u) := by
          rw [show 2 * ‖w - (σ:ℂ)‖ * Real.exp 1 * (u / Real.exp u)
              = 2 * ‖w - (σ:ℂ)‖ * u * (Real.exp 1 / Real.exp u) by ring]
          have h7 : (1:ℝ) ≤ Real.exp 1 / Real.exp u := by
            rw [le_div_iff₀ (Real.exp_pos u), one_mul]
            exact Real.exp_le_exp.mpr hu1
          have hc : (0:ℝ) ≤ 2 * ‖w - (σ:ℂ)‖ * u := by positivity
          nlinarith [mul_nonneg hc (by linarith : (0:ℝ) ≤ Real.exp 1 / Real.exp u - 1)]
      _ ≤ 2 * ‖w - (σ:ℂ)‖ * Real.exp 1 * (1 - Real.exp (-u)) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
  · -- tail: exponential decay over a bounded-below denominator
    set a := min σ w.re with ha
    have hapos : 0 < a := lt_min hσ hw
    refine MeasureTheory.Integrable.mono'
      (g := fun u => (2 / (1 - Real.exp (-u₀))) * Real.exp (-(a * u)))
      (Integrable.const_mul ?_ _)
      (hmeas.mono_measure (Measure.restrict_mono (Set.Ioi_subset_Ioi hu₀pos.le) le_rfl)) ?_
    · have h0 := exp_neg_integrableOn_Ioi u₀ hapos
      refine h0.congr_fun (fun u _ => ?_) measurableSet_Ioi
      show Real.exp (-a * u) = Real.exp (-(a * u))
      rw [neg_mul]
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
      refine Filter.Eventually.of_forall (fun u hu => ?_)
      rw [Set.mem_Ioi] at hu
      have hu0 : 0 < u := lt_trans hu₀pos hu
      rw [norm_div, hden_real u, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hden_pos u hu0), div_le_iff₀ (hden_pos u hu0)]
      have hmono : 1 - Real.exp (-u₀) ≤ 1 - Real.exp (-u) := by
        have := Real.exp_le_exp.mpr (show -u ≤ -u₀ by linarith)
        linarith
      have hnum_bound : ‖Complex.exp (-(σ:ℂ) * (u:ℂ)) - Complex.exp (-w * (u:ℂ))‖
          ≤ 2 * Real.exp (-(a * u)) := by
        calc ‖Complex.exp (-(σ:ℂ) * (u:ℂ)) - Complex.exp (-w * (u:ℂ))‖
            ≤ ‖Complex.exp (-(σ:ℂ) * (u:ℂ))‖ + ‖Complex.exp (-w * (u:ℂ))‖ :=
              norm_sub_le _ _
          _ = Real.exp (-(σ * u)) + Real.exp (-(w.re * u)) := by
              rw [Complex.norm_exp, Complex.norm_exp, hnum_re u]
              congr 2
              simp [Complex.mul_re]
          _ ≤ Real.exp (-(a * u)) + Real.exp (-(a * u)) := by
              have h1 : a ≤ σ := min_le_left _ _
              have h2 : a ≤ w.re := min_le_right _ _
              have h3 : Real.exp (-(σ * u)) ≤ Real.exp (-(a * u)) := by
                refine Real.exp_le_exp.mpr ?_
                nlinarith
              have h4 : Real.exp (-(w.re * u)) ≤ Real.exp (-(a * u)) := by
                refine Real.exp_le_exp.mpr ?_
                nlinarith
              linarith
          _ = 2 * Real.exp (-(a * u)) := by ring
      calc ‖Complex.exp (-(σ:ℂ) * (u:ℂ)) - Complex.exp (-w * (u:ℂ))‖
          ≤ 2 * Real.exp (-(a * u)) := hnum_bound
        _ = (2 / (1 - Real.exp (-u₀))) * Real.exp (-(a * u)) * (1 - Real.exp (-u₀)) := by
            field_simp
            exact (div_self (hden_pos u₀ hu₀pos).ne').symm
        _ ≤ (2 / (1 - Real.exp (-u₀))) * Real.exp (-(a * u)) * (1 - Real.exp (-u)) := by
            refine mul_le_mul_of_nonneg_left hmono ?_
            have := hden_pos u₀ hu₀pos
            positivity

/-- Pointwise real part of Poitou's difference kernel: for `u > 0`,
`Re((e^{-σu} - e^{-(σ+it)u})/(1-e^{-u})) = e^{-σu}(1 - cos(tu))/(1-e^{-u})`. -/
theorem re_digamma_diff_kernel_apply {σ : ℝ} (t : ℝ) {u : ℝ} (hu : 0 < u) :
    ((Complex.exp (-(σ:ℂ) * (u:ℂ)) - Complex.exp (-((σ:ℂ) + (t:ℂ)*Complex.I) * (u:ℂ)))
        / (1 - Complex.exp (-(u:ℂ)))).re
      = Real.exp (-(σ*u)) * (1 - Real.cos (t*u)) / (1 - Real.exp (-u)) := by
  have hden_pos : 0 < 1 - Real.exp (-u) := by
    have := Real.exp_lt_exp.mpr (show -u < 0 by linarith)
    rw [Real.exp_zero] at this
    linarith
  have hden_real : (1:ℂ) - Complex.exp (-(u:ℂ)) = ((1 - Real.exp (-u) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_exp]
    push_cast
    ring_nf
  rw [hden_real, div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hre1 : (Complex.exp (-(σ:ℂ) * (u:ℂ))).re = Real.exp (-(σ*u)) := by
    rw [Complex.exp_re]
    have h1 : (-(σ:ℂ) * (u:ℂ)).re = -(σ*u) := by simp [Complex.mul_re]
    have h2 : (-(σ:ℂ) * (u:ℂ)).im = 0 := by simp [Complex.mul_im]
    rw [h1, h2, Real.cos_zero, mul_one]
  have hre2 : (Complex.exp (-((σ:ℂ) + (t:ℂ)*Complex.I) * (u:ℂ))).re
      = Real.exp (-(σ*u)) * Real.cos (t*u) := by
    rw [Complex.exp_re]
    have h1 : (-((σ:ℂ) + (t:ℂ)*Complex.I) * (u:ℂ)).re = -(σ*u) := by
      simp [Complex.mul_re, Complex.add_re, Complex.add_im]
    have h2 : (-((σ:ℂ) + (t:ℂ)*Complex.I) * (u:ℂ)).im = -(t*u) := by
      simp [Complex.mul_im, Complex.add_re, Complex.add_im]
    rw [h1, h2, Real.cos_neg]
  rw [Complex.sub_re, hre1, hre2]
  field_simp

/-- **Poitou's cosine-kernel identity** (p. 6-04): for `σ > 0`,
`Re(ψ(σ+it) - ψ(σ)) = ∫₀^∞ e^{-σu}(1 - cos(tu))/(1-e^{-u}) du`. -/
theorem re_digamma_sub_eq_integral {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    (Complex.digamma ((σ:ℂ) + (t:ℂ)*Complex.I) - Complex.digamma (σ:ℂ)).re
      = ∫ u in Set.Ioi (0:ℝ),
          Real.exp (-(σ*u)) * (1 - Real.cos (t*u)) / (1 - Real.exp (-u)) := by
  have hw : 0 < ((σ:ℂ) + (t:ℂ)*Complex.I).re := by simp [hσ]
  rw [digamma_sub_digamma_eq_integral hσ hw]
  have hint := integrableOn_digamma_diff_kernel hσ hw
  have h0 := integral_re hint
  simp only [RCLike.re_to_complex] at h0
  rw [← h0]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
  rw [Set.mem_Ioi] at hu
  exact re_digamma_diff_kernel_apply t hu

/-- The `σ = 1/2` kernel is the hyperbolic-sine kernel (Poitou p. 6-04, first display):
`e^{-u/2}/(1 - e^{-u}) = 1/(2 sinh(u/2))`. -/
theorem exp_half_div_one_sub_exp_neg {u : ℝ} (hu : 0 < u) :
    Real.exp (-(u/2)) / (1 - Real.exp (-u)) = 1/(2 * Real.sinh (u/2)) := by
  have hsh : 2 * Real.sinh (u/2) = Real.exp (u/2) - Real.exp (-(u/2)) := by
    rw [Real.sinh_eq]
    ring
  have hden_pos : 0 < 1 - Real.exp (-u) := by
    have := Real.exp_lt_exp.mpr (show -u < 0 by linarith)
    rw [Real.exp_zero] at this
    linarith
  have hsh_pos : 0 < Real.exp (u/2) - Real.exp (-(u/2)) := by
    have := Real.exp_lt_exp.mpr (show -(u/2) < u/2 by linarith)
    linarith
  rw [hsh, div_eq_div_iff hden_pos.ne' (by linarith)]
  rw [mul_sub, ← Real.exp_add, ← Real.exp_add]
  ring_nf
  rw [Real.exp_zero]

/-- **The elementary cosh integral** (Poitou p. 6-04): `∫₀^∞ du/(2 cosh(u/2)) = π/2`.
Substituting `v = e^{u/2}` gives `2∫₁^∞ dv/(1+v²) = 2(π/2 - π/4)`. -/
theorem integral_inv_two_cosh_half :
    ∫ u in Set.Ioi (0:ℝ), 1/(2 * Real.cosh (u/2)) = π/2 := by
  set g : ℝ → ℝ := fun u => Real.exp (u/2) with hg
  have himg : g '' Set.Ioi 0 = Set.Ioi (1:ℝ) := by
    ext v
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [hg]
      simp only
      have := Real.exp_lt_exp.mpr (show (0:ℝ) < u/2 by linarith)
      rwa [Real.exp_zero] at this
    · intro hv
      refine ⟨2 * Real.log v, ?_, ?_⟩
      · have := Real.log_pos hv
        linarith
      · rw [hg]
        simp only
        rw [show 2 * Real.log v / 2 = Real.log v by ring, Real.exp_log (by linarith)]
  have hderiv : ∀ u ∈ Set.Ioi (0:ℝ),
      HasDerivWithinAt g (Real.exp (u/2) * (1/2)) (Set.Ioi 0) u := by
    intro u _
    have h0 : HasDerivAt (fun u : ℝ => u/2) (1/2) u := by
      simpa using (hasDerivAt_id u).div_const 2
    exact (h0.exp).hasDerivWithinAt
  have hinj : Set.InjOn g (Set.Ioi 0) := by
    have hmono : StrictMono g := by
      intro a b hab
      rw [hg]
      simp only
      exact Real.exp_lt_exp.mpr (by linarith)
    exact hmono.injective.injOn
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hderiv hinj (fun v : ℝ => 2/(1+v^2))
  rw [himg] at hcov
  -- evaluate the v-side
  have hval : (∫ v in Set.Ioi (1:ℝ), 2/(1+v^2)) = π/2 := by
    have h0 : (∫ v in Set.Ioi (1:ℝ), 2/(1+v^2))
        = 2 * ∫ v in Set.Ioi (1:ℝ), (1+v^2)⁻¹ := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
      rw [div_eq_mul_inv]
    rw [h0, integral_Ioi_inv_one_add_sq, Real.arctan_one]
    ring
  have hpt : (∫ u in Set.Ioi (0:ℝ), 1/(2 * Real.cosh (u/2)))
      = ∫ u in Set.Ioi (0:ℝ), |Real.exp (u/2) * (1/2)| • (2/(1 + (g u)^2)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    rw [Set.mem_Ioi] at hu
    rw [hg]
    simp only
    rw [abs_of_pos (by positivity : (0:ℝ) < Real.exp (u/2) * (1/2)), smul_eq_mul]
    have hcosh : 2 * Real.cosh (u/2) = Real.exp (u/2) + Real.exp (-(u/2)) := by
      rw [Real.cosh_eq]
      ring
    rw [hcosh]
    have h2 : Real.exp (u/2) + Real.exp (-(u/2)) > 0 := by positivity
    have h3 : Real.exp (-(u/2)) * Real.exp (u/2) = 1 := by
      rw [← Real.exp_add]
      simp
    have h4 : (0:ℝ) < 1 + Real.exp (u/2)^2 := by positivity
    field_simp
    nlinarith [h3, Real.exp_pos (u/2)]
  rw [hpt, ← hcov, hval]

/-- The real cosine kernel of `re_digamma_sub_eq_integral` is integrable on `(0, ∞)`. -/
theorem integrableOn_re_diff_kernel {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    IntegrableOn
      (fun u : ℝ => Real.exp (-(σ*u)) * (1 - Real.cos (t*u)) / (1 - Real.exp (-u)))
      (Set.Ioi 0) := by
  have hw : 0 < ((σ:ℂ) + (t:ℂ)*Complex.I).re := by simp [hσ]
  have h0 := (integrableOn_digamma_diff_kernel hσ hw).re
  simp only [RCLike.re_to_complex] at h0
  refine h0.congr ?_
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
  refine Filter.Eventually.of_forall (fun u hu => ?_)
  rw [Set.mem_Ioi] at hu
  exact re_digamma_diff_kernel_apply t hu

/-- The sine-integral tail `∫_t^∞ sin u/u du`, defined through the Dirichlet integral as
`π/2 - ∫_0^t sin u/u du` (Poitou p. 6-05, the `γ₁ + γ₃` term). -/
noncomputable def sincTail (t : ℝ) : ℝ := π/2 - ∫ u in (0:ℝ)..t, Real.sin u / u

/-- The truncated tail integrals converge to `sincTail`. -/
theorem tendsto_integral_sinc_window (t : ℝ) :
    Tendsto (fun X : ℝ => ∫ u in t..X, Real.sin u / u) atTop (nhds (sincTail t)) := by
  have h0 : ∀ X : ℝ, (∫ u in t..X, Real.sin u / u)
      = (∫ u in (0:ℝ)..X, Real.sin u / u) - ∫ u in (0:ℝ)..t, Real.sin u / u := by
    intro X
    rw [eq_sub_iff_add_eq]
    rw [add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_sinc 0 t) (intervalIntegrable_sinc t X)
  simp only [h0]
  rw [sincTail]
  exact (tendsto_integral_sinc_atTop).sub_const _

/-- `sincTail` vanishes at infinity. -/
theorem tendsto_sincTail_atTop : Tendsto sincTail atTop (nhds 0) := by
  have h0 := tendsto_integral_sinc_atTop.const_sub (π/2)
  simp only [sub_self] at h0
  exact h0

/-- `sincTail` is differentiable away from `0`, with derivative `-sin t/t`. -/
theorem hasDerivAt_sincTail {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt sincTail (-(Real.sin t / t)) t := by
  have h0 : HasDerivAt (fun t : ℝ => ∫ u in (0:ℝ)..t, Real.sin u / u)
      (Real.sin t / t) t := by
    refine intervalIntegral.integral_hasDerivAt_right
      (intervalIntegrable_sinc 0 t) ?_ ?_
    · refine (Measurable.stronglyMeasurable ?_).stronglyMeasurableAtFilter
      fun_prop
    · have : ContinuousAt (fun u : ℝ => Real.sin u / u) t := by
        refine ContinuousAt.div (by fun_prop) (by fun_prop) ht
      exact this
  have h1 : HasDerivAt (fun t : ℝ => π/2 - ∫ u in (0:ℝ)..t, Real.sin u / u)
      (0 - Real.sin t / t) t := (hasDerivAt_const t (π/2)).sub h0
  have h2 : sincTail = fun t : ℝ => π/2 - ∫ u in (0:ℝ)..t, Real.sin u / u := rfl
  rw [h2]
  simpa using h1

/-- The symmetric exponential tails equal the sinc tail: for `t > 0`,
`∫_1^X (e^{itx} - e^{-itx})/x dx → 2i·sincTail t` (Poitou p. 6-05, `γ₁ + γ₃`). -/
theorem tendsto_integral_cexp_sub_div_window {t : ℝ} (ht : 0 < t) :
    Tendsto (fun X : ℝ => ∫ x in (1:ℝ)..X,
        (Complex.exp ((t*x : ℝ) * Complex.I) - Complex.exp (-((t*x : ℝ)) * Complex.I))
          / (x:ℂ))
      atTop (nhds (2 * Complex.I * ((sincTail t : ℝ) : ℂ))) := by
  -- pointwise: the integrand is 2i·sin(tx)/x
  have hpt : ∀ x : ℝ,
      (Complex.exp ((t*x : ℝ) * Complex.I) - Complex.exp (-((t*x : ℝ)) * Complex.I))
        / (x:ℂ)
      = 2 * Complex.I * ((Real.sin (t*x) / x : ℝ) : ℂ) := by
    intro x
    rcases eq_or_ne x 0 with hx | hx
    · simp [hx]
    · rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
      have hxne : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
      push_cast
      field_simp
      ring
  have h0 : ∀ X : ℝ, (∫ x in (1:ℝ)..X,
      (Complex.exp ((t*x : ℝ) * Complex.I) - Complex.exp (-((t*x : ℝ)) * Complex.I))
        / (x:ℂ))
      = 2 * Complex.I * ((∫ x in (1:ℝ)..X, Real.sin (t*x) / x : ℝ) : ℂ) := by
    intro X
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun x _ => hpt x)
  simp only [h0]
  -- ∫_1^X sin(tx)/x = ∫_t^{tX} sinc → sincTail t
  have h1 : ∀ X : ℝ, (∫ x in (1:ℝ)..X, Real.sin (t*x) / x)
      = ∫ u in t..(t*X), Real.sin u / u := by
    intro X
    have := integral_sin_mul_div_eq t 1 X ht
    rw [mul_one] at this
    exact this
  simp only [h1]
  have h2 : Tendsto (fun X : ℝ => t * X) atTop atTop :=
    Filter.Tendsto.const_mul_atTop ht Filter.tendsto_id
  have h3 := (tendsto_integral_sinc_window t).comp h2
  have h4 : Tendsto (fun X : ℝ => ((∫ u in t..(t*X), Real.sin u / u : ℝ) : ℂ))
      atTop (nhds ((sincTail t : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp h3
  exact h4.const_mul _

/-- **Differentiation of a Fourier-type set integral** (Lemme 1 engine, Poitou p. 6-05):
if `G` and `x·G(x)` are integrable on `s`, then `t ↦ ∫_s G(x) e^{itx} dx` is
differentiable with derivative `∫_s i·x·G(x) e^{itx} dx`. -/
theorem hasDerivAt_integral_mul_cexp {G : ℝ → ℂ} {s : Set ℝ}
    (hG : IntegrableOn G s) (hxG : IntegrableOn (fun x : ℝ => (x:ℂ) * G x) s) (t : ℝ) :
    HasDerivAt (fun τ : ℝ => ∫ x in s, G x * Complex.exp ((τ * x : ℝ) * Complex.I))
      (∫ x in s, Complex.I * (x:ℂ) * G x * Complex.exp ((t * x : ℝ) * Complex.I)) t := by
  have hexp_meas : ∀ τ : ℝ, AEStronglyMeasurable
      (fun x : ℝ => Complex.exp ((τ * x : ℝ) * Complex.I)) (volume.restrict s) := by
    intro τ
    refine (Continuous.aestronglyMeasurable ?_).restrict
    fun_prop
  have hexp_norm : ∀ τ x : ℝ, ‖Complex.exp ((τ * x : ℝ) * Complex.I)‖ = 1 := by
    intro τ x
    rw [Complex.norm_exp]
    simp
  have h := _root_.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun τ : ℝ => fun x : ℝ => G x * Complex.exp ((τ * x : ℝ) * Complex.I))
    (F' := fun τ : ℝ => fun x : ℝ =>
      Complex.I * (x:ℂ) * G x * Complex.exp ((τ * x : ℝ) * Complex.I))
    (bound := fun x => ‖(x:ℂ) * G x‖)
    (μ := volume.restrict s) (x₀ := t) (s := Metric.ball t 1)
    (Metric.ball_mem_nhds t one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact h.2
  · refine Filter.Eventually.of_forall (fun τ => ?_)
    exact (hG.aestronglyMeasurable.mul (hexp_meas τ))
  · refine hG.mul_bdd (c := 1) (hexp_meas t) ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [hexp_norm t x]
  · have h5 : AEStronglyMeasurable (fun x : ℝ => Complex.I * (x:ℂ))
        (volume.restrict s) := (Continuous.aestronglyMeasurable (by fun_prop)).restrict
    exact (h5.mul hG.aestronglyMeasurable).mul (hexp_meas t)
  · refine Filter.Eventually.of_forall (fun x => ?_)
    intro τ _
    rw [norm_mul, hexp_norm τ x, mul_one, norm_mul]
    rw [show ‖Complex.I * (x:ℂ)‖ = ‖(x:ℂ)‖ by
      rw [norm_mul, Complex.norm_I, one_mul]]
    rw [← norm_mul]
  · exact hxG.norm
  · refine Filter.Eventually.of_forall (fun x => ?_)
    intro τ _
    have h0 : HasDerivAt (fun τ : ℝ => τ * x) x τ := by
      simpa using (hasDerivAt_id τ).mul_const x
    have h1 : HasDerivAt (fun τ : ℝ => ((τ * x : ℝ) : ℂ)) ((x:ℝ):ℂ) τ :=
      h0.ofReal_comp
    have h2 : HasDerivAt (fun τ : ℝ => ((τ * x : ℝ) : ℂ) * Complex.I)
        ((x:ℂ) * Complex.I) τ := h1.mul_const Complex.I
    have h3 := h2.cexp
    have h4 := h3.const_mul (G x)
    have hval : G x * (Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I) * ((x:ℂ) * Complex.I))
        = Complex.I * (x:ℂ) * G x * Complex.exp ((τ * x : ℝ) * Complex.I) := by
      ring
    rw [hval] at h4
    exact h4

/-- **Poitou's `γ`** (p. 6-05): the Fourier transform of `(F(0) - F(x))/x`, the
non-summable `F(0)`-tails taken as improper sinc-tail limits. Defined for all `t`
(the value at `t = 0` is junk). -/
noncomputable def gammaFT (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  (∫ x in Set.Ioc (-1:ℝ) 1, (F 0 - F x)/(x:ℂ) * Complex.exp ((t*x : ℝ) * Complex.I))
  + F 0 * (2 * Complex.I * ((Real.sign t * sincTail |t| : ℝ) : ℂ))
  - ∫ x in (Set.Ioc (-1:ℝ) 1)ᶜ, F x/(x:ℂ) * Complex.exp ((t*x : ℝ) * Complex.I)

/-- Dividing an integrable `F` by `x` stays integrable on the complement of the unit
window `{x | |x| ≥ 1}`, since `‖F x / x‖ ≤ ‖F x‖` there. -/
theorem integrableOn_div_ofReal_compl_Ioc {F : ℝ → ℂ} (hF : Integrable F) :
    IntegrableOn (fun x : ℝ => F x/(x:ℂ)) (Set.Ioc (-1:ℝ) 1)ᶜ := by
  refine MeasureTheory.Integrable.mono' (hF.integrableOn.norm) ?_ ?_
  · refine ((hF.aestronglyMeasurable.restrict.mul
      ((Complex.measurable_ofReal.inv).aestronglyMeasurable.restrict)).congr ?_)
    exact Filter.Eventually.of_forall (fun x => (div_eq_mul_inv (F x) _).symm)
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc.compl).mpr ?_
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Set.mem_compl_iff, Set.mem_Ioc] at hx
    push Not at hx
    have hx1 : 1 ≤ |x| := by
      rcases le_or_gt x (-1) with h | h
      · rw [abs_of_nonpos (by linarith)]
        linarith
      · have := hx h
        rw [abs_of_pos (by linarith)]
        linarith
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    exact div_le_self (norm_nonneg _) hx1

/-- **Lemme 1** (Poitou p. 6-04/6-05): away from `t = 0`, Poitou's `γ` is differentiable
with `γ'(t) = -i·φ(t)`, `φ` the Fourier transform of `F`. -/
theorem hasDerivAt_gammaFT {F : ℝ → ℂ} (hF : Integrable F)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (gammaFT F)
      (-Complex.I * ∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)) t := by
  -- P1: the near-zero piece
  have hxG₀ : IntegrableOn (fun x : ℝ => (x:ℂ) * ((F 0 - F x)/(x:ℂ)))
      (Set.Ioc (-1) 1) := by
    have h0 : IntegrableOn (fun x : ℝ => F 0 - F x) (Set.Ioc (-1:ℝ) 1) := by
      refine (MeasureTheory.integrableOn_const (by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top)).sub hF.integrableOn
    refine h0.congr ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
    filter_upwards [MeasureTheory.ae_iff.mpr (by
      simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
      exact MeasureTheory.measure_singleton (0:ℝ) : volume {x : ℝ | ¬ x ≠ 0} = 0)]
      with x hx _
    have hxne : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    exact (mul_div_cancel₀ _ hxne).symm
  have hP1 := hasDerivAt_integral_mul_cexp hFdiv hxG₀ t
  -- P3: the tail piece
  have hGtail : IntegrableOn (fun x : ℝ => F x/(x:ℂ)) (Set.Ioc (-1:ℝ) 1)ᶜ :=
    integrableOn_div_ofReal_compl_Ioc hF
  have hxGtail : IntegrableOn (fun x : ℝ => (x:ℂ) * (F x/(x:ℂ)))
      (Set.Ioc (-1:ℝ) 1)ᶜ := by
    refine hF.integrableOn.congr ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc.compl).mpr ?_
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Set.mem_compl_iff, Set.mem_Ioc] at hx
    push Not at hx
    have hxne : x ≠ 0 := by
      rcases le_or_gt x (-1) with h | h
      · linarith
      · have := hx h
        nlinarith
    have hxne' : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxne
    field_simp
  have hP3 := hasDerivAt_integral_mul_cexp hGtail hxGtail t
  -- P2: the sinc-tail piece, locally sign-constant
  have hP2 : HasDerivAt (fun τ : ℝ =>
      F 0 * (2 * Complex.I * ((Real.sign τ * sincTail |τ| : ℝ) : ℂ)))
      (F 0 * (2 * Complex.I * ((-(Real.sin t / t) : ℝ) : ℂ))) t := by
    rcases lt_or_gt_of_ne ht with hneg | hpos
    · -- t < 0 : locally sign = -1, |τ| = -τ
      have hev : (fun τ : ℝ => F 0 * (2 * Complex.I
          * ((Real.sign τ * sincTail |τ| : ℝ) : ℂ)))
          =ᶠ[nhds t] (fun τ : ℝ => F 0 * (2 * Complex.I
          * ((-(sincTail (-τ)) : ℝ) : ℂ))) := by
        filter_upwards [eventually_lt_nhds hneg] with τ hτ
        rw [Real.sign_of_neg hτ, abs_of_neg hτ]
        norm_num
      have h0 : HasDerivAt (fun τ : ℝ => sincTail (-τ)) (Real.sin t / t) t := by
        have h1 := (hasDerivAt_sincTail (show -t ≠ 0 by simpa using ht)).comp t
          ((hasDerivAt_id t).neg)
        have h2 : -(Real.sin (-t) / (-t)) * -1 = Real.sin t / t := by
          rw [Real.sin_neg]
          field_simp
        rw [h2] at h1
        exact h1
      have h3 : HasDerivAt (fun τ : ℝ => F 0 * (2 * Complex.I
          * ((-(sincTail (-τ)) : ℝ) : ℂ)))
          (F 0 * (2 * Complex.I * ((-(Real.sin t / t) : ℝ) : ℂ))) t := by
        have h4 : HasDerivAt (fun τ : ℝ => ((-(sincTail (-τ)) : ℝ) : ℂ))
            ((-(Real.sin t / t) : ℝ) : ℂ) t := by
          have h5 : HasDerivAt (fun τ : ℝ => -(sincTail (-τ))) (-(Real.sin t / t)) t :=
            h0.neg
          exact h5.ofReal_comp
        have h6 := h4.const_mul (F 0 * (2 * Complex.I))
        have h7 : (fun τ : ℝ => F 0 * (2 * Complex.I) * ((-(sincTail (-τ)) : ℝ) : ℂ))
            = fun τ : ℝ => F 0 * (2 * Complex.I * ((-(sincTail (-τ)) : ℝ) : ℂ)) := by
          funext τ
          ring
        rw [h7] at h6
        have h8 : F 0 * (2 * Complex.I) * ((-(Real.sin t / t) : ℝ) : ℂ)
            = F 0 * (2 * Complex.I * ((-(Real.sin t / t) : ℝ) : ℂ)) := by ring
        rw [h8] at h6
        exact h6
      exact h3.congr_of_eventuallyEq hev
    · -- t > 0 : locally sign = 1, |τ| = τ
      have hev : (fun τ : ℝ => F 0 * (2 * Complex.I
          * ((Real.sign τ * sincTail |τ| : ℝ) : ℂ)))
          =ᶠ[nhds t] (fun τ : ℝ => F 0 * (2 * Complex.I
          * ((sincTail τ : ℝ) : ℂ))) := by
        filter_upwards [eventually_gt_nhds hpos] with τ hτ
        rw [Real.sign_of_pos hτ, abs_of_pos hτ, one_mul]
      have h3 : HasDerivAt (fun τ : ℝ => F 0 * (2 * Complex.I
          * ((sincTail τ : ℝ) : ℂ)))
          (F 0 * (2 * Complex.I * ((-(Real.sin t / t) : ℝ) : ℂ))) t := by
        have h4 : HasDerivAt (fun τ : ℝ => ((sincTail τ : ℝ) : ℂ))
            ((-(Real.sin t / t) : ℝ) : ℂ) t :=
          (hasDerivAt_sincTail ht).ofReal_comp
        have h6 := h4.const_mul (F 0 * (2 * Complex.I))
        have h7 : (fun τ : ℝ => F 0 * (2 * Complex.I) * ((sincTail τ : ℝ) : ℂ))
            = fun τ : ℝ => F 0 * (2 * Complex.I * ((sincTail τ : ℝ) : ℂ)) := by
          funext τ
          ring
        rw [h7] at h6
        have h8 : F 0 * (2 * Complex.I) * ((-(Real.sin t / t) : ℝ) : ℂ)
            = F 0 * (2 * Complex.I * ((-(Real.sin t / t) : ℝ) : ℂ)) := by ring
        rw [h8] at h6
        exact h6
      exact h3.congr_of_eventuallyEq hev
  -- assemble
  have hsum := (hP1.add hP2).sub hP3
  have hfun : (((fun τ : ℝ => ∫ x in Set.Ioc (-1:ℝ) 1, (F 0 - F x)/(x:ℂ)
          * Complex.exp ((τ*x : ℝ) * Complex.I))
        + fun τ : ℝ => F 0 * (2 * Complex.I * ((Real.sign τ * sincTail |τ| : ℝ) : ℂ)))
      - fun τ : ℝ => ∫ x in (Set.Ioc (-1:ℝ) 1)ᶜ, F x/(x:ℂ)
          * Complex.exp ((τ*x : ℝ) * Complex.I))
      = gammaFT F := by
    funext τ
    rfl
  rw [hfun] at hsum
  -- integrable building blocks on the window
  have hexp_meas : AEStronglyMeasurable
      (fun x : ℝ => Complex.exp ((t * x : ℝ) * Complex.I))
      (volume.restrict (Set.Ioc (-1:ℝ) 1)) := by
    refine (Continuous.aestronglyMeasurable ?_).restrict
    fun_prop
  have hexp_int : IntegrableOn (fun x : ℝ => Complex.exp ((t*x : ℝ) * Complex.I))
      (Set.Ioc (-1:ℝ) 1) := by
    refine MeasureTheory.Integrable.mono'
      (g := fun _ => (1:ℝ))
      (MeasureTheory.integrableOn_const (by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top)) hexp_meas ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Complex.norm_exp]
    simp
  have hFe_Ioc : IntegrableOn
      (fun x : ℝ => F x * Complex.exp ((t*x : ℝ) * Complex.I)) (Set.Ioc (-1:ℝ) 1) := by
    refine hF.integrableOn.mul_bdd (c := 1) hexp_meas ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Complex.norm_exp]
    simp
  have hFe_compl : IntegrableOn
      (fun x : ℝ => F x * Complex.exp ((t*x : ℝ) * Complex.I)) (Set.Ioc (-1:ℝ) 1)ᶜ := by
    refine hF.integrableOn.mul_bdd (c := 1) ?_ ?_
    · refine (Continuous.aestronglyMeasurable ?_).restrict
      fun_prop
    · refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Complex.norm_exp]
      simp
  -- V2: the window value
  have hV2 : (∫ x in Set.Ioc (-1:ℝ) 1, Complex.exp ((t*x : ℝ) * Complex.I))
      = ((2 * Real.sin t / t : ℝ) : ℂ) := by
    have h0 := integral_cexp_window ht (1:ℝ)
    rw [intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)] at h0
    rw [one_mul] at h0
    rw [← h0]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
    congr 1
    push_cast
    ring
  -- V1: split the near-zero derivative integral
  have hV1 : (∫ x in Set.Ioc (-1:ℝ) 1, Complex.I * (x:ℂ) * ((F 0 - F x)/(x:ℂ))
      * Complex.exp ((t*x : ℝ) * Complex.I))
      = Complex.I * F 0 * ((2 * Real.sin t / t : ℝ) : ℂ)
        - Complex.I * ∫ x in Set.Ioc (-1:ℝ) 1,
            F x * Complex.exp ((t*x : ℝ) * Complex.I) := by
    have h0 : (∫ x in Set.Ioc (-1:ℝ) 1, Complex.I * (x:ℂ) * ((F 0 - F x)/(x:ℂ))
        * Complex.exp ((t*x : ℝ) * Complex.I))
        = ∫ x in Set.Ioc (-1:ℝ) 1,
            (Complex.I * F 0 * Complex.exp ((t*x : ℝ) * Complex.I)
              - Complex.I * (F x * Complex.exp ((t*x : ℝ) * Complex.I))) := by
      refine MeasureTheory.integral_congr_ae ?_
      refine ((MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_)
      filter_upwards [MeasureTheory.ae_iff.mpr (by
        simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
        exact MeasureTheory.measure_singleton (0:ℝ) : volume {x : ℝ | ¬ x ≠ 0} = 0)]
        with x hx _
      have hxne : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
      field_simp
    rw [h0, MeasureTheory.integral_sub ((hexp_int.const_mul _)) (hFe_Ioc.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hV2]
  -- V3: the tail derivative integral
  have hV3 : (∫ x in (Set.Ioc (-1:ℝ) 1)ᶜ, Complex.I * (x:ℂ) * (F x/(x:ℂ))
      * Complex.exp ((t*x : ℝ) * Complex.I))
      = Complex.I * ∫ x in (Set.Ioc (-1:ℝ) 1)ᶜ,
          F x * Complex.exp ((t*x : ℝ) * Complex.I) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc.compl (fun x hx => ?_)
    rw [Set.mem_compl_iff, Set.mem_Ioc] at hx
    push Not at hx
    have hxne : x ≠ 0 := by
      rcases le_or_gt x (-1) with h | h
      · linarith
      · have := hx h
        nlinarith
    have hxne' : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxne
    field_simp
  -- V5: recombine the full line
  have hV5 : (∫ x in Set.Ioc (-1:ℝ) 1, F x * Complex.exp ((t*x : ℝ) * Complex.I))
      + ∫ x in (Set.Ioc (-1:ℝ) 1)ᶜ, F x * Complex.exp ((t*x : ℝ) * Complex.I)
      = ∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I) :=
    MeasureTheory.integral_add_compl measurableSet_Ioc (by
      refine hF.mul_bdd (c := 1) ?_ ?_
      · refine Continuous.aestronglyMeasurable ?_
        fun_prop
      · refine Filter.Eventually.of_forall (fun x => ?_)
        rw [Complex.norm_exp]
        simp)
  have hval : ((∫ x in Set.Ioc (-1:ℝ) 1, Complex.I * (x:ℂ) * ((F 0 - F x)/(x:ℂ))
        * Complex.exp ((t*x : ℝ) * Complex.I))
      + F 0 * (2 * Complex.I * ((-(Real.sin t / t) : ℝ) : ℂ)))
      - ∫ x in (Set.Ioc (-1:ℝ) 1)ᶜ, Complex.I * (x:ℂ) * (F x/(x:ℂ))
          * Complex.exp ((t*x : ℝ) * Complex.I)
      = -Complex.I * ∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I) := by
    rw [hV1, hV3, ← hV5]
    push_cast
    ring
  rw [hval] at hsum
  exact hsum

/-- Chord bound: `‖e^{iθ} - 1‖ ≤ |θ|` (via `‖e^{iθ}-1‖ = 2|sin(θ/2)|`). -/
theorem norm_cexp_mul_I_sub_one_le (θ : ℝ) :
    ‖Complex.exp ((θ:ℂ) * Complex.I) - 1‖ ≤ |θ| := by
  have h0 : Complex.exp ((θ:ℂ) * Complex.I) - 1
      = ⟨Real.cos θ - 1, Real.sin θ⟩ := by
    rw [Complex.exp_mul_I]
    apply Complex.ext
    · simp [Complex.add_re, Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    · simp [Complex.add_im, Complex.mul_im, Complex.sin_ofReal_re]
  rw [h0]
  rw [Complex.norm_def, Complex.normSq_mk]
  have h1 : (Real.cos θ - 1) * (Real.cos θ - 1) + Real.sin θ * Real.sin θ
      = 4 * Real.sin (θ/2)^2 := by
    have h2 : Real.cos θ = 1 - 2 * Real.sin (θ/2)^2 := by
      have h5 := Real.cos_two_mul (θ/2)
      have h6 : 2 * (θ/2) = θ := by ring
      rw [h6] at h5
      have h7 := Real.sin_sq_add_cos_sq (θ/2)
      nlinarith
    have h3 := Real.sin_sq_add_cos_sq θ
    nlinarith
  rw [h1]
  have h4 : Real.sqrt (4 * Real.sin (θ/2)^2) = 2 * |Real.sin (θ/2)| := by
    rw [show (4 : ℝ) * Real.sin (θ/2)^2 = (2 * |Real.sin (θ/2)|)^2 by
      rw [mul_pow, sq_abs]
      ring]
    exact Real.sqrt_sq (by positivity)
  rw [h4]
  calc 2 * |Real.sin (θ/2)| ≤ 2 * |θ/2| := by
        have := Real.abs_sin_le_abs (x := θ/2)
        linarith
    _ = |θ| := by
        rw [abs_div, abs_two]
        ring

/-- **Poitou's `ρ`** (Lemme 2, p. 6-05): `ρ(t) = ∫ k(x)(1 - e^{itx})/x dx`. -/
noncomputable def rhoFT (k : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, k x * ((1 - Complex.exp ((t*x : ℝ) * Complex.I))/(x:ℂ))

@[simp]
theorem rhoFT_zero (k : ℝ → ℂ) : rhoFT k 0 = 0 := by
  rw [rhoFT]
  simp

/-- The `ρ` integrand is integrable for integrable `k` (chord bound `≤ |t|·‖k‖`). -/
theorem integrable_rhoFT_integrand {k : ℝ → ℂ} (hk : Integrable k) (t : ℝ) :
    Integrable (fun x : ℝ => k x * ((1 - Complex.exp ((t*x : ℝ) * Complex.I))/(x:ℂ))) := by
  refine MeasureTheory.Integrable.mono' (g := fun x => |t| * ‖k x‖)
    (hk.norm.const_mul _) ?_ ?_
  · refine hk.aestronglyMeasurable.mul ?_
    refine AEStronglyMeasurable.mul ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      fun_prop
    · exact ((Complex.measurable_ofReal.inv).aestronglyMeasurable)
  · refine Filter.Eventually.of_forall (fun x => ?_)
    rcases eq_or_ne x 0 with hx | hx
    · simp [hx]
      positivity
    · rw [norm_mul, mul_comm (|t|) _]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      rw [div_le_iff₀ (abs_pos.mpr hx)]
      have h0 : ‖(1:ℂ) - Complex.exp ((t*x : ℝ) * Complex.I)‖
          = ‖Complex.exp ((t*x : ℝ) * Complex.I) - 1‖ := by
        rw [← norm_neg, neg_sub]
      rw [h0]
      calc ‖Complex.exp ((t*x : ℝ) * Complex.I) - 1‖ ≤ |t*x| :=
            norm_cexp_mul_I_sub_one_le (t*x)
        _ = |t| * |x| := abs_mul t x

/-- **Lemme 2, derivative of `ρ`** (Poitou p. 6-06): `ρ'(t) = -i·μ(t)` with
`μ(t) = ∫ k(x) e^{itx} dx`. -/
theorem hasDerivAt_rhoFT {k : ℝ → ℂ} (hk : Integrable k) (t : ℝ) :
    HasDerivAt (rhoFT k)
      (-Complex.I * ∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) t := by
  have hexp_meas : ∀ τ : ℝ, AEStronglyMeasurable
      (fun x : ℝ => Complex.exp ((τ * x : ℝ) * Complex.I)) volume := by
    intro τ
    refine Continuous.aestronglyMeasurable ?_
    fun_prop
  have h := _root_.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun τ : ℝ => fun x : ℝ =>
      k x * ((1 - Complex.exp ((τ * x : ℝ) * Complex.I))/(x:ℂ)))
    (F' := fun τ : ℝ => fun x : ℝ =>
      -Complex.I * (k x * Complex.exp ((τ * x : ℝ) * Complex.I)))
    (bound := fun x => ‖k x‖)
    (μ := volume) (x₀ := t) (s := Metric.ball t 1)
    (Metric.ball_mem_nhds t one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · have h2 := h.2
    have h3 : (fun τ : ℝ => ∫ x : ℝ,
        k x * ((1 - Complex.exp ((τ * x : ℝ) * Complex.I))/(x:ℂ))) = rhoFT k := by
      funext τ
      rw [rhoFT]
    rw [h3] at h2
    rw [← MeasureTheory.integral_const_mul]
    exact h2
  · refine Filter.Eventually.of_forall (fun τ => ?_)
    exact (integrable_rhoFT_integrand hk τ).aestronglyMeasurable
  · exact integrable_rhoFT_integrand hk t
  · refine AEStronglyMeasurable.const_mul ?_ _
    exact hk.aestronglyMeasurable.mul (hexp_meas t)
  · refine Filter.Eventually.of_forall (fun x => ?_)
    intro τ _
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, norm_mul, Complex.norm_exp]
    have h0 : (((τ * x : ℝ) : ℂ) * Complex.I).re = 0 := by
      simp
    rw [h0, Real.exp_zero, mul_one]
  · exact hk.norm
  · filter_upwards [MeasureTheory.ae_iff.mpr (by
      simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
      exact MeasureTheory.measure_singleton (0:ℝ) : volume {x : ℝ | ¬ x ≠ 0} = 0)]
      with x hx
    intro τ _
    · have h0 : HasDerivAt (fun τ : ℝ => τ * x) x τ := by
        simpa using (hasDerivAt_id τ).mul_const x
      have h1 : HasDerivAt (fun τ : ℝ => ((τ * x : ℝ) : ℂ)) ((x:ℝ):ℂ) τ :=
        h0.ofReal_comp
      have h2 : HasDerivAt (fun τ : ℝ => ((τ * x : ℝ) : ℂ) * Complex.I)
          ((x:ℂ) * Complex.I) τ := h1.mul_const Complex.I
      have h3 := h2.cexp
      have h4' : HasDerivAt (fun τ : ℝ => (1 : ℂ)
          - Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I))
          (0 - Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I) * ((x:ℂ) * Complex.I)) τ :=
        (hasDerivAt_const τ (1:ℂ)).sub h3
      have h4 : HasDerivAt (fun τ : ℝ => (1 : ℂ)
          - Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I))
          (-(Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I) * ((x:ℂ) * Complex.I))) τ := by
        have h9 : (0 : ℂ) - Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I) * ((x:ℂ) * Complex.I)
            = -(Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I) * ((x:ℂ) * Complex.I)) := by
          ring
        rw [h9] at h4'
        exact h4'
      have h5 := (h4.div_const ((x:ℂ))).const_mul (k x)
      have hval : k x * (-(Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I)
          * ((x:ℂ) * Complex.I)) / (x:ℂ))
          = -Complex.I * (k x * Complex.exp ((τ * x : ℝ) * Complex.I)) := by
        have hxne : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
        field_simp
      rw [hval] at h5
      exact h5

/-- `μ` is continuous (dominated convergence). -/
theorem continuous_muFT {k : ℝ → ℂ} (hk : Integrable k) :
    Continuous (fun t : ℝ => ∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) := by
  refine continuous_iff_continuousAt.mpr (fun t => ?_)
  refine MeasureTheory.continuousAt_of_dominated ?_ ?_ hk.norm ?_
  · refine Filter.Eventually.of_forall (fun τ => ?_)
    refine hk.aestronglyMeasurable.mul ?_
    refine Continuous.aestronglyMeasurable ?_
    fun_prop
  · refine Filter.Eventually.of_forall (fun τ => ?_)
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [norm_mul, Complex.norm_exp]
    have h0 : (((τ * x : ℝ) : ℂ) * Complex.I).re = 0 := by simp
    rw [h0, Real.exp_zero, mul_one]
  · refine Filter.Eventually.of_forall (fun x => ?_)
    refine Continuous.continuousAt ?_
    have h1 : Continuous (fun τ : ℝ => Complex.exp ((τ * x : ℝ) * Complex.I)) := by
      fun_prop
    exact h1.const_mul _

/-- `ρ` is continuous (it is differentiable everywhere). -/
theorem continuous_rhoFT {k : ℝ → ℂ} (hk : Integrable k) :
    Continuous (rhoFT k) := by
  refine continuous_iff_continuousAt.mpr (fun t => ?_)
  exact (hasDerivAt_rhoFT hk t).continuousAt

/-- The sinc tail is globally bounded. -/
theorem exists_bound_sincTail : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, |sincTail t| ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := exists_bound_primitive_sinc
  refine ⟨π/2 + C, by positivity, fun t => ?_⟩
  rw [sincTail]
  have h0 : |∫ u in (0:ℝ)..t, Real.sin u / u| ≤ C := by
    rcases le_or_gt 0 t with h | h
    · exact hC t h
    · have h2 := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := -t)
        (f := fun u : ℝ => Real.sin u / u)
      have h3 : (∫ x in (0:ℝ)..(-t), Real.sin (-x) / (-x))
          = ∫ x in (0:ℝ)..(-t), Real.sin x / x := by
        refine intervalIntegral.integral_congr (fun x _ => ?_)
        rw [Real.sin_neg, neg_div_neg_eq]
      rw [h3] at h2
      simp only [neg_neg, neg_zero] at h2
      -- h2 : ∫ x in 0..(-t), sin x/x = ∫ x in t..0, sin x/x
      have h4 : (∫ u in (0:ℝ)..t, Real.sin u / u)
          = -∫ x in (0:ℝ)..(-t), Real.sin x / x := by
        rw [h2, intervalIntegral.integral_symm]
      rw [h4, abs_neg]
      exact hC (-t) (by linarith)
  calc |π/2 - ∫ u in (0:ℝ)..t, Real.sin u / u|
      ≤ |π/2| + |∫ u in (0:ℝ)..t, Real.sin u / u| := abs_sub _ _
    _ ≤ π/2 + C := by
        rw [abs_of_pos (by positivity : (0:ℝ) < π/2)]
        linarith

/-- Continuity in `t` of Fourier-type set integrals (dominated convergence). -/
theorem continuous_integral_mul_cexp {G : ℝ → ℂ} {s : Set ℝ} (hG : IntegrableOn G s) :
    Continuous (fun t : ℝ => ∫ x in s, G x * Complex.exp ((t*x : ℝ) * Complex.I)) := by
  refine continuous_iff_continuousAt.mpr (fun t => ?_)
  refine MeasureTheory.continuousAt_of_dominated ?_ ?_ hG.norm ?_
  · refine Filter.Eventually.of_forall (fun τ => ?_)
    refine hG.aestronglyMeasurable.mul ?_
    refine (Continuous.aestronglyMeasurable ?_).restrict
    fun_prop
  · refine Filter.Eventually.of_forall (fun τ => ?_)
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [norm_mul, Complex.norm_exp]
    have h0 : (((τ * x : ℝ) : ℂ) * Complex.I).re = 0 := by simp
    rw [h0, Real.exp_zero, mul_one]
  · refine Filter.Eventually.of_forall (fun x => ?_)
    refine Continuous.continuousAt ?_
    have h1 : Continuous (fun τ : ℝ => Complex.exp ((τ * x : ℝ) * Complex.I)) := by
      fun_prop
    exact h1.const_mul _

/-- `γ` is globally bounded on any compact window: the continuous pieces are bounded on
compacts and the sinc-tail jump term is globally bounded. -/
theorem exists_bound_gammaFT {F : ℝ → ℂ} (hF : Integrable F)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    (a b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Set.Icc a b, ‖gammaFT F t‖ ≤ C := by
  have hGtail : IntegrableOn (fun x : ℝ => F x/(x:ℂ)) (Set.Ioc (-1:ℝ) 1)ᶜ :=
    integrableOn_div_ofReal_compl_Ioc hF
  obtain ⟨Cs, hCspos, hCs⟩ := exists_bound_sincTail
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    ((continuous_integral_mul_cexp hFdiv).continuousOn)
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    ((continuous_integral_mul_cexp hGtail).continuousOn)
  refine ⟨(|C₀| + 1) + ‖F 0‖ * (2 * Cs) + (|C₁| + 1), by positivity, fun t htmem => ?_⟩
  rw [gammaFT]
  set A : ℂ := ∫ x in Set.Ioc (-1:ℝ) 1, (F 0 - F x)/(x:ℂ)
      * Complex.exp ((t*x : ℝ) * Complex.I) with hA
  set B : ℂ := F 0 * (2 * Complex.I * ((Real.sign t * sincTail |t| : ℝ) : ℂ)) with hB
  set D : ℂ := ∫ x in (Set.Ioc (-1:ℝ) 1)ᶜ, F x/(x:ℂ)
      * Complex.exp ((t*x : ℝ) * Complex.I) with hD
  have h1 : ‖A + B - D‖ ≤ ‖A‖ + ‖B‖ + ‖D‖ := by
    have t1 : ‖A + B - D‖ ≤ ‖A + B‖ + ‖D‖ := norm_sub_le _ _
    have t2 : ‖A + B‖ ≤ ‖A‖ + ‖B‖ := norm_add_le _ _
    linarith
  refine le_trans h1 ?_
  have h2 : ‖B‖ ≤ ‖F 0‖ * (2 * Cs) := by
    rw [hB, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_mul]
    have hsign : |Real.sign t| ≤ 1 := by
      rcases lt_trichotomy t 0 with h | h | h
      · rw [Real.sign_of_neg h]
        norm_num
      · rw [h, Real.sign_zero]
        norm_num
      · rw [Real.sign_of_pos h]
        norm_num
    calc ‖(2:ℂ)‖ * (|Real.sign t| * abs (sincTail |t|))
        ≤ ‖(2:ℂ)‖ * (1 * Cs) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          refine mul_le_mul hsign (hCs (|t|)) (abs_nonneg _) zero_le_one
      _ = 2 * Cs := by
          rw [Complex.norm_ofNat]
          ring
  have h3 : ‖A‖ ≤ |C₀| + 1 := by
    rw [hA]
    refine le_trans (hC₀ t htmem) ?_
    calc C₀ ≤ |C₀| := le_abs_self _
      _ ≤ |C₀| + 1 := by linarith
  have h4 : ‖D‖ ≤ |C₁| + 1 := by
    rw [hD]
    refine le_trans (hC₁ t htmem) ?_
    calc C₁ ≤ |C₁| := le_abs_self _
      _ ≤ |C₁| + 1 := by linarith
  linarith

/-- **Integration by parts off zero** (Lemme 2, p. 6-06): on an interval avoiding `0`,
`∫_c^d ρφ = i(ρ(d)γ(d) - ρ(c)γ(c)) - ∫_c^d μγ`. -/
theorem integral_rhoFT_mul_phi_eq {k F : ℝ → ℂ} (hk : Integrable k) (hF : Integrable F)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    {c d : ℝ} (h0 : (0:ℝ) ∉ Set.uIcc c d) :
    (∫ t in c..d, rhoFT k t * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)))
      = Complex.I * (rhoFT k d * gammaFT F d - rhoFT k c * gammaFT F c)
        - ∫ t in c..d, (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t := by
  have hu : ∀ t ∈ Set.uIcc c d, HasDerivAt (rhoFT k)
      (-Complex.I * ∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) t :=
    fun t _ => hasDerivAt_rhoFT hk t
  have hv : ∀ t ∈ Set.uIcc c d, HasDerivAt (gammaFT F)
      (-Complex.I * ∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)) t := by
    intro t ht
    refine hasDerivAt_gammaFT hF hFdiv ?_
    intro heq
    rw [heq] at ht
    exact h0 ht
  have hu' : IntervalIntegrable (fun t : ℝ =>
      -Complex.I * ∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) volume c d := by
    refine Continuous.intervalIntegrable ?_ c d
    exact (continuous_muFT hk).const_mul _
  have hv' : IntervalIntegrable (fun t : ℝ =>
      -Complex.I * ∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)) volume c d := by
    refine Continuous.intervalIntegrable ?_ c d
    exact (continuous_muFT hF).const_mul _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  -- hibp : ∫ ρ·(-iφ) = ρ d γ d - ρ c γ c - ∫ (-iμ)·γ
  have h1 : (∫ t in c..d, rhoFT k t
      * (-Complex.I * ∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)))
      = -Complex.I * ∫ t in c..d,
          rhoFT k t * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    ring
  have h2 : (∫ t in c..d,
      (-Complex.I * ∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t)
      = -Complex.I * ∫ t in c..d,
          (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    ring
  rw [h1, h2] at hibp
  -- solve for ∫ρφ
  have hA : ∀ A : ℂ, Complex.I * (-Complex.I * A) = A := fun A => by
    rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
  have h3 := congrArg (fun z => Complex.I * z) hibp
  rw [hA] at h3
  rw [mul_sub, hA] at h3
  exact h3

/-- **The fixed-`T` boundary identity** (Lemme 2, p. 6-06): letting `ε → 0` in the
integration by parts on `[-T, -ε]` and `[ε, T]`, the `ρ(±ε)γ(±ε)` boundary terms vanish
(`ρ(0) = 0`, `γ` bounded near `0`), leaving
`∫_{-T}^T ρφ = i(ρ(T)γ(T) - ρ(-T)γ(-T)) - ∫_{-T}^T μγ`. -/
theorem integral_rhoFT_mul_phi_symm {k F : ℝ → ℂ} (hk : Integrable k) (hF : Integrable F)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    (hμγ : Integrable (fun t : ℝ =>
      (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t))
    {T : ℝ} (hT : 0 < T) :
    (∫ t in (-T)..T, rhoFT k t * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)))
      = Complex.I * (rhoFT k T * gammaFT F T - rhoFT k (-T) * gammaFT F (-T))
        - ∫ t in (-T)..T,
            (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t := by
  set ρ := rhoFT k with hρ
  set γ := gammaFT F with hγ
  set μ : ℝ → ℂ := fun t => ∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I) with hμ
  set φ : ℝ → ℂ := fun t => ∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I) with hφ
  have hρφ_cont : Continuous (fun t => ρ t * φ t) :=
    (continuous_rhoFT hk).mul (continuous_muFT hF)
  have hμγ_ii : ∀ a b : ℝ, IntervalIntegrable (fun t => μ t * γ t) volume a b :=
    fun a b => hμγ.intervalIntegrable
  obtain ⟨Cγ, hCγpos, hCγ⟩ := exists_bound_gammaFT hF hFdiv (-1) 1
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1:ℝ)) (b := 1)).exists_bound_of_continuousOn
    (hρφ_cont.continuousOn)
  -- the ε-parameterized decomposition
  have hEq : ∀ ε : ℝ, 0 < ε → ε < T →
      (∫ t in (-T)..T, ρ t * φ t)
      = (Complex.I * (ρ (-ε) * γ (-ε) - ρ (-T) * γ (-T)) - ∫ t in (-T)..(-ε), μ t * γ t)
        + (∫ t in (-ε)..ε, ρ t * φ t)
        + (Complex.I * (ρ T * γ T - ρ ε * γ ε) - ∫ t in ε..T, μ t * γ t) := by
    intro ε hε hεT
    have hsplit : (∫ t in (-T)..T, ρ t * φ t)
        = (∫ t in (-T)..(-ε), ρ t * φ t) + (∫ t in (-ε)..ε, ρ t * φ t)
          + ∫ t in ε..T, ρ t * φ t := by
      rw [intervalIntegral.integral_add_adjacent_intervals
        (hρφ_cont.intervalIntegrable _ _) (hρφ_cont.intervalIntegrable _ _),
        intervalIntegral.integral_add_adjacent_intervals
        (hρφ_cont.intervalIntegrable _ _) (hρφ_cont.intervalIntegrable _ _)]
    rw [hsplit]
    rw [integral_rhoFT_mul_phi_eq hk hF hFdiv (c := -T) (d := -ε) (by
      rw [Set.uIcc_of_le (by linarith), Set.mem_Icc]
      push Not
      intro h
      linarith)]
    rw [integral_rhoFT_mul_phi_eq hk hF hFdiv (c := ε) (d := T) (by
      rw [Set.uIcc_of_le (by linarith), Set.mem_Icc]
      push Not
      intro h
      linarith)]
  -- limits of each ε-piece along 𝓝[>] 0
  have hρ0 : Tendsto (fun ε : ℝ => ρ ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h0 := (continuous_rhoFT hk).tendsto 0
    rw [show rhoFT k 0 = 0 from rhoFT_zero k] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hρ0' : Tendsto (fun ε : ℝ => ρ (-ε)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h0 := (continuous_rhoFT hk).tendsto 0
    rw [show rhoFT k 0 = 0 from rhoFT_zero k] at h0
    have h1 : Tendsto (fun ε : ℝ => -ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have := (continuous_neg.tendsto (0:ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa using this
    exact h0.comp h1
  have hbd1 : Tendsto (fun ε : ℝ => ρ ε * γ ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hb : Tendsto (fun ε : ℝ => Cγ * ‖ρ ε‖) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa using (hρ0.norm.const_mul Cγ)
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hε
    rw [norm_mul]
    calc ‖ρ ε‖ * ‖γ ε‖ ≤ ‖ρ ε‖ * Cγ := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact hCγ ε ⟨by linarith [hε.1], hε.2.le⟩
      _ = Cγ * ‖ρ ε‖ := mul_comm _ _
  have hbd2 : Tendsto (fun ε : ℝ => ρ (-ε) * γ (-ε)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hb : Tendsto (fun ε : ℝ => Cγ * ‖ρ (-ε)‖) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa using (hρ0'.norm.const_mul Cγ)
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hε
    rw [norm_mul]
    calc ‖ρ (-ε)‖ * ‖γ (-ε)‖ ≤ ‖ρ (-ε)‖ * Cγ := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          refine hCγ (-ε) ⟨by linarith [hε.2], by linarith [hε.1]⟩
      _ = Cγ * ‖ρ (-ε)‖ := mul_comm _ _
  have hmid : Tendsto (fun ε : ℝ => ∫ t in (-ε)..ε, ρ t * φ t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hb : Tendsto (fun ε : ℝ => (2 * (|M| + 1)) * ε)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h0 : Tendsto (fun ε : ℝ => (2 * (|M| + 1)) * ε) (nhds 0) (nhds 0) := by
        have h1 : Tendsto (fun ε : ℝ => ε) (nhds (0:ℝ)) (nhds 0) := tendsto_id
        simpa using h1.const_mul (2 * (|M| + 1))
      exact h0.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hb
    · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hε
      have h0 := intervalIntegral.norm_integral_le_of_norm_le_const
        (C := |M| + 1) (a := -ε) (b := ε) (f := fun t => ρ t * φ t) (fun t htmem => by
          rw [Set.uIoc_of_le (by linarith [hε.1] : -ε ≤ ε), Set.mem_Ioc] at htmem
          calc ‖ρ t * φ t‖ ≤ M := hM t ⟨by linarith [htmem.1, hε.2], by
                linarith [htmem.2, hε.2]⟩
            _ ≤ |M| + 1 := by
                have := le_abs_self M
                linarith)
      calc ‖∫ t in (-ε)..ε, ρ t * φ t‖ ≤ (|M| + 1) * |ε - (-ε)| := h0
        _ = (2 * (|M| + 1)) * ε := by
            rw [abs_of_pos (by linarith [hε.1] : (0:ℝ) < ε - (-ε))]
            ring
  have htail_pos : Tendsto (fun ε : ℝ => ∫ t in ε..T, μ t * γ t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ t in (0:ℝ)..T, μ t * γ t)) := by
    have h0 : ∀ ε : ℝ, (∫ t in ε..T, μ t * γ t)
        = (∫ t in (0:ℝ)..T, μ t * γ t) - ∫ t in (0:ℝ)..ε, μ t * γ t := by
      intro ε
      rw [eq_sub_iff_add_eq, add_comm]
      exact intervalIntegral.integral_add_adjacent_intervals
        (hμγ_ii 0 ε) (hμγ_ii ε T)
    refine Tendsto.congr (fun ε => (h0 ε).symm) ?_
    have h1 : Tendsto (fun ε : ℝ => ∫ t in (0:ℝ)..ε, μ t * γ t)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h2 : Tendsto (fun ε : ℝ => ∫ t in Set.Ioc (0:ℝ) ε, μ t * γ t)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        refine hμγ.tendsto_setIntegral_nhds_zero ?_
        have h3 : Tendsto (fun ε : ℝ => ENNReal.ofReal ε)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
          rw [show (0 : ENNReal) = ENNReal.ofReal 0 by simp]
          exact (ENNReal.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
        refine h3.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with ε hε
        rw [Function.comp_apply, Real.volume_Ioc, sub_zero]
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [Set.mem_Ioi] at hε
      rw [intervalIntegral.integral_of_le hε.le]
    have h4 : Tendsto (fun ε : ℝ => (∫ t in (0:ℝ)..T, μ t * γ t)
        - ∫ t in (0:ℝ)..ε, μ t * γ t) (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((∫ t in (0:ℝ)..T, μ t * γ t) - 0)) := tendsto_const_nhds.sub h1
    simpa using h4
  have htail_neg : Tendsto (fun ε : ℝ => ∫ t in (-T)..(-ε), μ t * γ t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ t in (-T)..(0:ℝ), μ t * γ t)) := by
    have h0 : ∀ ε : ℝ, (∫ t in (-T)..(-ε), μ t * γ t)
        = (∫ t in (-T)..(0:ℝ), μ t * γ t) - ∫ t in (-ε)..(0:ℝ), μ t * γ t := by
      intro ε
      rw [eq_sub_iff_add_eq]
      exact intervalIntegral.integral_add_adjacent_intervals
        (hμγ_ii (-T) (-ε)) (hμγ_ii (-ε) 0)
    refine Tendsto.congr (fun ε => (h0 ε).symm) ?_
    have h1 : Tendsto (fun ε : ℝ => ∫ t in (-ε)..(0:ℝ), μ t * γ t)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h2 : Tendsto (fun ε : ℝ => ∫ t in Set.Ioc (-ε) (0:ℝ), μ t * γ t)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        refine hμγ.tendsto_setIntegral_nhds_zero ?_
        have h3 : Tendsto (fun ε : ℝ => ENNReal.ofReal ε)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
          rw [show (0 : ENNReal) = ENNReal.ofReal 0 by simp]
          exact (ENNReal.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
        refine h3.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with ε hε
        rw [Function.comp_apply, Real.volume_Ioc, sub_neg_eq_add, zero_add]
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [Set.mem_Ioi] at hε
      rw [intervalIntegral.integral_of_le (by linarith : -ε ≤ 0)]
    have h4 : Tendsto (fun ε : ℝ => (∫ t in (-T)..(0:ℝ), μ t * γ t)
        - ∫ t in (-ε)..(0:ℝ), μ t * γ t) (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((∫ t in (-T)..(0:ℝ), μ t * γ t) - 0)) := tendsto_const_nhds.sub h1
    simpa using h4
  -- assemble the ε-limit of the right-hand side
  have hRHS : Tendsto (fun ε : ℝ =>
      (Complex.I * (ρ (-ε) * γ (-ε) - ρ (-T) * γ (-T)) - ∫ t in (-T)..(-ε), μ t * γ t)
        + (∫ t in (-ε)..ε, ρ t * φ t)
        + (Complex.I * (ρ T * γ T - ρ ε * γ ε) - ∫ t in ε..T, μ t * γ t))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((Complex.I * ((0:ℂ) - ρ (-T) * γ (-T)) - ∫ t in (-T)..(0:ℝ), μ t * γ t)
        + (0:ℂ)
        + (Complex.I * (ρ T * γ T - 0) - ∫ t in (0:ℝ)..T, μ t * γ t))) := by
    refine Filter.Tendsto.add (Filter.Tendsto.add ?_ hmid) ?_
    · refine Filter.Tendsto.sub ?_ htail_neg
      refine Filter.Tendsto.const_mul _ ?_
      exact (hbd2.sub_const _)
    · refine Filter.Tendsto.sub ?_ htail_pos
      refine Filter.Tendsto.const_mul _ ?_
      exact (tendsto_const_nhds.sub hbd1)
  -- the left side is constant; conclude by uniqueness of limits
  have hLHS : Tendsto (fun _ : ℝ => ∫ t in (-T)..T, ρ t * φ t)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((Complex.I * ((0:ℂ) - ρ (-T) * γ (-T)) - ∫ t in (-T)..(0:ℝ), μ t * γ t)
        + (0:ℂ)
        + (Complex.I * (ρ T * γ T - 0) - ∫ t in (0:ℝ)..T, μ t * γ t))) := by
    refine hRHS.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hT] with ε hε
    exact (hEq ε hε.1 hε.2).symm
  have huniq := tendsto_nhds_unique tendsto_const_nhds hLHS
  have hadj : (∫ t in (-T)..(0:ℝ), μ t * γ t) + ∫ t in (0:ℝ)..T, μ t * γ t
      = ∫ t in (-T)..T, μ t * γ t :=
    intervalIntegral.integral_add_adjacent_intervals (hμγ_ii (-T) 0) (hμγ_ii 0 T)
  linear_combination huniq - hadj

/-- **Lemme 2** (Poitou p. 6-06): with the boundary decay `ργ → 0` at `±∞` and `μγ`
integrable, the symmetric truncations `∫_{-T}^{T} ρ(t)φ(t) dt` converge as `T → ∞`,
with value `-∫_ℝ μ(t)γ(t) dt`. -/
theorem tendsto_integral_rhoFT_mul_phi {k F : ℝ → ℂ}
    (hk : Integrable k) (hF : Integrable F)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    (hμγ : Integrable (fun t : ℝ =>
      (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t))
    (htop : Tendsto (fun t : ℝ => rhoFT k t * gammaFT F t) atTop (nhds 0))
    (hbot : Tendsto (fun t : ℝ => rhoFT k t * gammaFT F t) atBot (nhds 0)) :
    Tendsto (fun T : ℝ => ∫ t in (-T)..T,
        rhoFT k t * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)))
      atTop (nhds (-∫ t : ℝ,
        (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t)) := by
  have hev : (fun T : ℝ => ∫ t in (-T)..T,
      rhoFT k t * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)))
      =ᶠ[atTop] (fun T : ℝ =>
        Complex.I * (rhoFT k T * gammaFT F T - rhoFT k (-T) * gammaFT F (-T))
        - ∫ t in (-T)..T,
            (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with T hT
    exact integral_rhoFT_mul_phi_symm hk hF hFdiv hμγ hT
  rw [Filter.tendsto_congr' hev]
  have hneg : Tendsto (fun T : ℝ => -T) atTop atBot :=
    Filter.tendsto_neg_atBot_iff.mpr Filter.tendsto_id
  have hb1 : Tendsto (fun T : ℝ => rhoFT k T * gammaFT F T) atTop (nhds 0) := htop
  have hb2 : Tendsto (fun T : ℝ => rhoFT k (-T) * gammaFT F (-T)) atTop (nhds 0) :=
    hbot.comp hneg
  have hboundary : Tendsto (fun T : ℝ =>
      Complex.I * (rhoFT k T * gammaFT F T - rhoFT k (-T) * gammaFT F (-T)))
      atTop (nhds 0) := by
    have h0 := (hb1.sub hb2).const_mul Complex.I
    simpa using h0
  have hint : Tendsto (fun T : ℝ => ∫ t in (-T)..T,
      (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t)
      atTop (nhds (∫ t : ℝ,
        (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral hμγ hneg Filter.tendsto_id
  have h1 := hboundary.sub hint
  simpa using h1

/-- **Convention bridge** (P-b): the kernel transform `μ(t) = ∫ k(x)e^{itx} dx` is the
mathlib Fourier integral at `-t/(2π)`. -/
theorem muFT_eq_fourierIntegral (k : ℝ → ℂ) (t : ℝ) :
    (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I))
      = 𝓕 k (-t/(2*π)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  show k x * Complex.exp ((t*x : ℝ) * Complex.I)
      = Complex.exp (((-2 * π * x * (-t/(2*π)) : ℝ) : ℂ) * Complex.I) • k x
  rw [smul_eq_mul]
  rw [show (-2 * π * x * (-t/(2*π)) : ℝ) = t * x by
    field_simp]
  ring

/-- **Multiplication formula against Schwartz functions** (Pa-1): for integrable `f`,
`∫ 𝓕Φ(x) • f(x) dx = ∫ Φ(ξ) • 𝓕f(ξ) dξ`. -/
theorem integral_fourier_schwartz_smul {f : ℝ → ℂ} (hf : Integrable f)
    (Φ : SchwartzMap ℝ ℂ) :
    ∫ x : ℝ, (𝓕 (Φ : ℝ → ℂ)) x • f x = ∫ ξ : ℝ, (Φ : ℝ → ℂ) ξ • (𝓕 f) ξ := by
  have h0 := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (L := innerₗ ℝ) (f := (Φ : ℝ → ℂ)) (g := f)
    (by fun_prop) (by fun_prop) (Φ.integrable) hf
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    exact real_inner_comm a b
  rw [hflip] at h0
  exact h0

/-- **The `L¹ ∩ L²` compatibility of the Fourier transform** (Pa-2): for `f` both
integrable and square-integrable, the abstract `L²` Fourier transform (extended from
Schwartz functions) agrees a.e. with the pointwise Fourier integral. Both sides define
the same tempered distribution, and locally integrable functions are a.e.-determined by
their distributional action. -/
theorem coeFn_fourier_toLp_two {f : ℝ → ℂ} (hf1 : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    ((𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 f := by
  set A : ℝ → ℂ := ((𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) with hA
  have hB_cont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous (by fun_prop) (by fun_prop) hf1
  have hsub_li : LocallyIntegrable (fun x => A x - 𝓕 f x) volume := by
    refine LocallyIntegrable.sub ?_ ?_
    · exact (Lp.memLp _).locallyIntegrable (by norm_num)
    · exact hB_cont.locallyIntegrable
  have h0 : ∀ᵐ x ∂(volume : Measure ℝ), A x - 𝓕 f x = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hsub_li ?_
    intro g g_smooth g_cpt
    have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_cpt.comp_left rfl
    have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
    set Φg := hg₁.toSchwartzMap hg₂ with hΦg
    have hΦg_coe : ∀ x : ℝ, Φg x = ((g x : ℝ) : ℂ) := fun x => rfl
    have hΦg_cont : Continuous (fun x : ℝ => Φg x) := Φg.continuous
    have hΦg_supp : HasCompactSupport (fun x : ℝ => Φg x) := hg₁
    have hΦg2 : MemLp (fun x : ℝ => Φg x) 2 (volume : Measure ℝ) :=
      hΦg_cont.memLp_of_hasCompactSupport (p := 2) hΦg_supp
    -- integrability of the two test pairings
    have hgA : Integrable (fun x => g x • A x) volume := by
      have h1 : Integrable ((fun x : ℝ => Φg x) * A) volume :=
        MemLp.integrable_mul hΦg2 (Lp.memLp _)
      refine h1.congr (Filter.Eventually.of_forall (fun x => ?_))
      show Φg x * A x = g x • A x
      rw [hΦg_coe x]
      exact Complex.real_smul.symm
    have hgB : Integrable (fun x => g x • 𝓕 f x) volume := by
      have h1 : Integrable (fun x : ℝ => Φg x * 𝓕 f x) volume := by
        refine Integrable.mul_bdd (c := ∫ y : ℝ, ‖f y‖)
          (hΦg_cont.integrable_of_hasCompactSupport hΦg_supp) ?_ ?_
        · exact hB_cont.aestronglyMeasurable
        · refine Filter.Eventually.of_forall (fun ξ => ?_)
          exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
      refine h1.congr (Filter.Eventually.of_forall (fun x => ?_))
      show Φg x * 𝓕 f x = g x • 𝓕 f x
      rw [hΦg_coe x]
      exact Complex.real_smul.symm
    -- the distributional chain
    have hchain : (∫ x, g x • A x) = ∫ x, g x • 𝓕 f x := by
      have c1 : (∫ x, g x • A x) = Lp.toTemperedDistribution (𝓕 (hf2.toLp f)) Φg := by
        rw [Lp.toTemperedDistribution_apply]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        show g x • A x = Φg x • A x
        rw [hΦg_coe x, Complex.real_smul, smul_eq_mul]
      have c2 : Lp.toTemperedDistribution (𝓕 (hf2.toLp f)) Φg
          = 𝓕 (Lp.toTemperedDistribution (hf2.toLp f)) Φg := by
        rw [Lp.fourier_toTemperedDistribution_eq]
      have c3 : 𝓕 (Lp.toTemperedDistribution (hf2.toLp f)) Φg
          = Lp.toTemperedDistribution (hf2.toLp f) (𝓕 Φg) := rfl
      have c4 : Lp.toTemperedDistribution (hf2.toLp f) (𝓕 Φg)
          = ∫ x, (𝓕 Φg) x • ((hf2.toLp f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x :=
        Lp.toTemperedDistribution_apply _ _
      have c5 : (∫ x, (𝓕 Φg) x • ((hf2.toLp f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x)
          = ∫ x, (𝓕 (fun y : ℝ => Φg y)) x • f x := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hf2.coeFn_toLp] with x hx
        rw [hx]
        congr 1
      have c6 : (∫ x, (𝓕 (fun y : ℝ => Φg y)) x • f x)
          = ∫ ξ, (fun y : ℝ => Φg y) ξ • 𝓕 f ξ :=
        integral_fourier_schwartz_smul hf1 Φg
      have c7 : (∫ ξ, (fun y : ℝ => Φg y) ξ • 𝓕 f ξ) = ∫ ξ, g ξ • 𝓕 f ξ := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
        show Φg ξ • 𝓕 f ξ = g ξ • 𝓕 f ξ
        rw [hΦg_coe ξ, Complex.real_smul, smul_eq_mul]
      rw [c1, c2, c3, c4, c5, c6, c7]
    calc (∫ x, g x • (A x - 𝓕 f x))
        = (∫ x, g x • A x) - ∫ x, g x • 𝓕 f x := by
          rw [← MeasureTheory.integral_sub hgA hgB]
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          show g x • (A x - 𝓕 f x) = g x • A x - g x • 𝓕 f x
          exact smul_sub _ _ _
      _ = 0 := by rw [hchain, sub_self]
  filter_upwards [h0] with x hx
  exact sub_eq_zero.mp hx

/-- The Fourier transform of the conjugate reflection is the conjugate transform:
`𝓕(conj ∘ k ∘ neg) = conj ∘ 𝓕k`. -/
theorem fourier_conj_neg (k : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => conj (k (-x))) ξ = conj (𝓕 k ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  rw [← integral_conj]
  have h0 : (fun v : ℝ => conj (Complex.exp ((-2 * π * v * ξ : ℝ) * Complex.I) • k v))
      = fun v : ℝ => Complex.exp ((-2 * π * (-v) * ξ : ℝ) * Complex.I) • conj (k v) := by
    funext v
    rw [smul_eq_mul, smul_eq_mul, map_mul, ← Complex.exp_conj]
    congr 2
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [h0]
  have h1 := integral_comp_neg_real
    (fun v : ℝ => Complex.exp ((-2 * π * (-v) * ξ : ℝ) * Complex.I) • conj (k v))
  rw [← h1]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  show Complex.exp ((-2 * π * v * ξ : ℝ) * Complex.I) • conj (k (-v))
      = Complex.exp ((-2 * π * (-(-v)) * ξ : ℝ) * Complex.I) • conj (k (-v))
  rw [neg_neg]

/-- **The mixed Plancherel pairing**: for `k ∈ L¹ ∩ L²` and `h ∈ L²` (not necessarily
integrable), `∫ 𝓕k(ξ)·(𝓕₂h)(ξ) dξ = ∫ k(-x)·h(x) dx`, where `𝓕₂h` is (a representative
of) the `L²` Fourier transform. -/
theorem integral_fourier_mul_fourierL2 {k h : ℝ → ℂ}
    (hk1 : Integrable k) (hk2 : MemLp k 2 (volume : Measure ℝ))
    (hh2 : MemLp h 2 (volume : Measure ℝ)) :
    (∫ ξ : ℝ, 𝓕 k ξ * ((𝓕 (hh2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ)
      = ∫ x : ℝ, k (-x) * h x := by
  classical
  set kstar : ℝ → ℂ := fun x => conj (k (-x)) with hkstar
  have hMP : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg _
  have hks1 : Integrable kstar := by
    have h0 : Integrable (fun x : ℝ => k (-x)) :=
      hMP.integrable_comp_of_integrable hk1
    exact memLp_one_iff_integrable.mp ((memLp_one_iff_integrable.mpr h0).star)
  have hks2 : MemLp kstar 2 (volume : Measure ℝ) := by
    have h0 : MemLp (fun x : ℝ => k (-x)) 2 (volume : Measure ℝ) :=
      hk2.comp_measurePreserving hMP
    exact h0.star
  have hpair := MeasureTheory.Lp.inner_fourier_eq
    (hks2.toLp kstar) (hh2.toLp h)
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def] at hpair
  have hL : (∫ a : ℝ, ⟪(𝓕 (hks2.toLp kstar) : Lp ℂ 2 (volume : Measure ℝ)) a,
        (𝓕 (hh2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) a⟫_ℂ)
      = ∫ ξ : ℝ, 𝓕 k ξ * ((𝓕 (hh2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [coeFn_fourier_toLp_two hks1 hks2] with ξ h1
    rw [RCLike.inner_apply, h1, fourier_conj_neg, starRingEnd_self_apply]
    exact mul_comm _ _
  have hR : (∫ a : ℝ, ⟪(hks2.toLp kstar : Lp ℂ 2 (volume : Measure ℝ)) a,
        (hh2.toLp h : Lp ℂ 2 (volume : Measure ℝ)) a⟫_ℂ)
      = ∫ x : ℝ, k (-x) * h x := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hks2.coeFn_toLp, hh2.coeFn_toLp] with x h1 h2
    rw [RCLike.inner_apply, h1, h2]
    rw [hkstar]
    simp only [starRingEnd_self_apply]
    exact mul_comm _ _
  rw [hL, hR] at hpair
  exact hpair

/-- Two-sided version of the symmetric-tail limit: for `t ≠ 0`,
`∫_1^X (e^{itx} - e^{-itx})/x dx → 2i·sign(t)·sincTail|t|`. -/
theorem tendsto_integral_cexp_sub_div_window' {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun X : ℝ => ∫ x in (1:ℝ)..X,
        (Complex.exp ((t*x : ℝ) * Complex.I) - Complex.exp (-((t*x : ℝ)) * Complex.I))
          / (x:ℂ))
      atTop (nhds (2 * Complex.I * ((Real.sign t * sincTail |t| : ℝ) : ℂ))) := by
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · -- t < 0: flip signs and use the positive case at |t| = -t
    have h0 := tendsto_integral_cexp_sub_div_window (t := -t) (by linarith)
    have h1 : (fun X : ℝ => ∫ x in (1:ℝ)..X,
        (Complex.exp ((t*x : ℝ) * Complex.I) - Complex.exp (-((t*x : ℝ)) * Complex.I))
          / (x:ℂ))
        = fun X : ℝ => -∫ x in (1:ℝ)..X,
          (Complex.exp ((-t*x : ℝ) * Complex.I) - Complex.exp (-((-t*x : ℝ)) * Complex.I))
            / (x:ℂ) := by
      funext X
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      rw [show ((-t*x : ℝ) : ℂ) = -((t*x : ℝ) : ℂ) by push_cast; ring]
      rw [show (-(-((t*x : ℝ) : ℂ))) = ((t*x : ℝ) : ℂ) by ring]
      ring
    rw [h1]
    have h2 := h0.neg
    have h3 : -(2 * Complex.I * ((sincTail (-t) : ℝ) : ℂ))
        = 2 * Complex.I * ((Real.sign t * sincTail |t| : ℝ) : ℂ) := by
      rw [Real.sign_of_neg hneg, abs_of_neg hneg]
      push_cast
      ring
    rw [h3] at h2
    exact h2
  · have h0 := tendsto_integral_cexp_sub_div_window hpos
    have h3 : 2 * Complex.I * ((sincTail t : ℝ) : ℂ)
        = 2 * Complex.I * ((Real.sign t * sincTail |t| : ℝ) : ℂ) := by
      rw [Real.sign_of_pos hpos, abs_of_pos hpos, one_mul]
    rw [h3] at h0
    exact h0

/-- **Pointwise convergence of truncated Fourier integrals to Poitou's `γ`** (P-c, step 1):
for `t ≠ 0`, `∫_{-n}^{n} (F(0)-F(x))/x · e^{itx} dx → gammaFT F t`. -/
theorem tendsto_truncated_fourier_gammaFT {F : ℝ → ℂ} (hF : Integrable F)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun n : ℕ => ∫ x in Set.Ioc (-(n:ℝ)) (n:ℝ),
        ((F 0 - F x)/(x:ℂ)) * Complex.exp ((t*x : ℝ) * Complex.I))
      atTop (nhds (gammaFT F t)) := by
  set h : ℝ → ℂ := fun x => (F 0 - F x)/(x:ℂ) with hh
  set e : ℝ → ℂ := fun x => Complex.exp ((t*x : ℝ) * Complex.I) with he
  have he_bd : ∀ x : ℝ, ‖e x‖ = 1 := by
    intro x
    rw [he]
    simp only
    rw [Complex.norm_exp]
    simp
  have he_meas : AEStronglyMeasurable e volume := by
    refine Continuous.aestronglyMeasurable ?_
    rw [he]
    fun_prop
  -- integrabilities
  have hFe_int : Integrable (fun x : ℝ => (F x/(x:ℂ)) * e x) volume → True := fun _ => trivial
  have hFx_tail : IntegrableOn (fun x : ℝ => F x/(x:ℂ)) (Set.Ioc (-1:ℝ) 1)ᶜ :=
    integrableOn_div_ofReal_compl_Ioc hF
  -- eventually-n decomposition
  have hEq : ∀ n : ℕ, 1 ≤ n →
      (∫ x in Set.Ioc (-(n:ℝ)) (n:ℝ), h x * e x)
      = (∫ x in Set.Ioc (-1:ℝ) 1, h x * e x)
        + (F 0 * ∫ x in (1:ℝ)..(n:ℝ),
            (Complex.exp ((t*x : ℝ) * Complex.I)
              - Complex.exp (-((t*x : ℝ)) * Complex.I)) / (x:ℂ))
        - ∫ x in (Set.Ioc (-(n:ℝ)) (-1:ℝ) ∪ Set.Ioc (1:ℝ) (n:ℝ)), (F x/(x:ℂ)) * e x := by
    intro n hn
    have hn' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hsplit : Set.Ioc (-(n:ℝ)) (n:ℝ)
        = Set.Ioc (-(n:ℝ)) (-1:ℝ) ∪ Set.Ioc (-1:ℝ) 1 ∪ Set.Ioc (1:ℝ) (n:ℝ) := by
      rw [Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith),
        Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)]
    -- integrability of h·e on the three pieces
    have hmid : IntegrableOn (fun x => h x * e x) (Set.Ioc (-1:ℝ) 1) := by
      refine hFdiv.mul_bdd (c := 1) (he_meas.restrict) ?_
      exact Filter.Eventually.of_forall (fun x => by rw [he_bd x])
    have hF0_int : ∀ a b : ℝ, Set.Ioc a b ⊆ (Set.Ioc (-1:ℝ) 1)ᶜ →
        IntegrableOn (fun x : ℝ => F 0/(x:ℂ) * e x) (Set.Ioc a b) := by
      intro a b hsub
      refine MeasureTheory.Integrable.mono'
        (g := fun _ => ‖F 0‖)
        (MeasureTheory.integrableOn_const (by
          rw [Real.volume_Ioc]
          exact ENNReal.ofReal_ne_top)) ?_ ?_
      · refine AEStronglyMeasurable.mul ?_ (he_meas.restrict)
        exact ((Complex.measurable_ofReal.inv).aestronglyMeasurable.const_mul
          (F 0)).congr (Filter.Eventually.of_forall (fun x =>
            (div_eq_mul_inv (F 0) ((x:ℝ):ℂ)).symm)) |>.restrict
      · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
        refine Filter.Eventually.of_forall (fun x hx => ?_)
        have hx1 : 1 ≤ |x| := by
          have := hsub hx
          rw [Set.mem_compl_iff, Set.mem_Ioc] at this
          push Not at this
          rcases le_or_gt x (-1) with h' | h'
          · rw [abs_of_nonpos (by linarith)]
            linarith
          · have := this h'
            rw [abs_of_pos (by linarith)]
            linarith
        rw [norm_mul, he_bd x, mul_one, norm_div, Complex.norm_real,
          Real.norm_eq_abs]
        exact div_le_self (norm_nonneg _) hx1
    have hFx_int : ∀ a b : ℝ, Set.Ioc a b ⊆ (Set.Ioc (-1:ℝ) 1)ᶜ →
        IntegrableOn (fun x => (F x/(x:ℂ)) * e x) (Set.Ioc a b) := by
      intro a b hsub
      refine ((hFx_tail.mono_set hsub).mul_bdd (c := 1) (he_meas.restrict) ?_)
      exact Filter.Eventually.of_forall (fun x => by rw [he_bd x])
    have htail_int : ∀ a b : ℝ, Set.Ioc a b ⊆ (Set.Ioc (-1:ℝ) 1)ᶜ →
        IntegrableOn (fun x => h x * e x) (Set.Ioc a b) := by
      intro a b hsub
      refine ((hF0_int a b hsub).sub (hFx_int a b hsub)).congr ?_
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
      refine Filter.Eventually.of_forall (fun x _ => ?_)
      show F 0/(x:ℂ) * e x - (F x/(x:ℂ)) * e x = h x * e x
      rw [hh]
      simp only
      ring
    have hneg_sub : Set.Ioc (-(n:ℝ)) (-1:ℝ) ⊆ (Set.Ioc (-1:ℝ) 1)ᶜ := by
      intro x hx
      rw [Set.mem_Ioc] at hx
      rw [Set.mem_compl_iff, Set.mem_Ioc]
      push Not
      intro h'
      linarith [hx.2]
    have hpos_sub : Set.Ioc (1:ℝ) (n:ℝ) ⊆ (Set.Ioc (-1:ℝ) 1)ᶜ := by
      intro x hx
      rw [Set.mem_Ioc] at hx
      rw [Set.mem_compl_iff, Set.mem_Ioc]
      push Not
      intro h'
      linarith [hx.1]
    -- split the integral
    have hdisj1 : Disjoint (Set.Ioc (-(n:ℝ)) (-1:ℝ)) (Set.Ioc (-1:ℝ) 1) := by
      refine Set.disjoint_left.mpr (fun x hx hx' => ?_)
      rw [Set.mem_Ioc] at hx hx'
      linarith [hx.2, hx'.1]
    have hdisj2 : Disjoint (Set.Ioc (-(n:ℝ)) (-1:ℝ) ∪ Set.Ioc (-1:ℝ) 1)
        (Set.Ioc (1:ℝ) (n:ℝ)) := by
      refine Set.disjoint_left.mpr (fun x hx hx' => ?_)
      rw [Set.mem_Ioc] at hx'
      rcases hx with hx | hx <;> rw [Set.mem_Ioc] at hx
      · linarith [hx.2, hx'.1]
      · linarith [hx.2, hx'.1]
    rw [hsplit, MeasureTheory.setIntegral_union hdisj2 measurableSet_Ioc
      (MeasureTheory.IntegrableOn.union (htail_int _ _ hneg_sub) hmid)
      (htail_int _ _ hpos_sub),
      MeasureTheory.setIntegral_union hdisj1 measurableSet_Ioc
      (htail_int _ _ hneg_sub) hmid]
    -- tail algebra
    have htail_eq : ∀ a b : ℝ, Set.Ioc a b ⊆ (Set.Ioc (-1:ℝ) 1)ᶜ →
        (∫ x in Set.Ioc a b, h x * e x)
        = (∫ x : ℝ in Set.Ioc a b, F 0/(x:ℂ) * e x)
          - ∫ x in Set.Ioc a b, (F x/(x:ℂ)) * e x := by
      intro a b hsub
      rw [← MeasureTheory.integral_sub (hF0_int a b hsub) (hFx_int a b hsub)]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
      show h x * e x = F 0/(x:ℂ) * e x - (F x/(x:ℂ)) * e x
      rw [hh]
      simp only
      ring
    rw [htail_eq _ _ hneg_sub, htail_eq _ _ hpos_sub]
    -- pull out F 0 and reflect the negative window
    have hF0pull : ∀ a b : ℝ, (∫ x : ℝ in Set.Ioc a b, F 0/(x:ℂ) * e x)
        = F 0 * ∫ x in Set.Ioc a b, e x / (x:ℂ) := by
      intro a b
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
      ring
    rw [hF0pull, hF0pull]
    have hIoc_int : ∀ a b : ℝ, IntervalIntegrable (fun x : ℝ => e x / (x:ℂ)) volume a b
        → True := fun _ _ _ => trivial
    have hnegint : (∫ x in Set.Ioc (-(n:ℝ)) (-1:ℝ), e x / (x:ℂ))
        = -∫ x in (1:ℝ)..(n:ℝ), Complex.exp (-((t*x : ℝ)) * Complex.I) / (x:ℂ) := by
      rw [← intervalIntegral.integral_of_le (by linarith : -(n:ℝ) ≤ -1)]
      have h0 := intervalIntegral.integral_comp_neg (a := (1:ℝ)) (b := (n:ℝ))
        (f := fun y : ℝ => e y / (y:ℂ))
      -- h0 : ∫ x in 1..n, e(-x)/(-x) = ∫ x in -n..-1, e x/x
      rw [← h0, ← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      show e (-x) / ((-x : ℝ):ℂ) = -(Complex.exp (-((t*x : ℝ)) * Complex.I) / (x:ℂ))
      rw [he]
      simp only
      rw [show ((t*(-x) : ℝ) : ℂ) = -((t*x : ℝ) : ℂ) by push_cast; ring]
      push_cast
      rw [div_neg]
    have hposint : (∫ x in Set.Ioc (1:ℝ) (n:ℝ), e x / (x:ℂ))
        = ∫ x in (1:ℝ)..(n:ℝ), Complex.exp ((t*x : ℝ) * Complex.I) / (x:ℂ) := by
      rw [← intervalIntegral.integral_of_le hn']
    rw [hnegint, hposint]
    -- recombine the interval integrals
    have hcont1 : IntervalIntegrable
        (fun x : ℝ => Complex.exp ((t*x : ℝ) * Complex.I) / (x:ℂ)) volume 1 (n:ℝ) := by
      refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
      intro x hx
      rw [Set.uIcc_of_le hn', Set.mem_Icc] at hx
      exact_mod_cast (by linarith : x ≠ 0)
    have hcont2 : IntervalIntegrable
        (fun x : ℝ => Complex.exp (-((t*x : ℝ)) * Complex.I) / (x:ℂ)) volume 1 (n:ℝ) := by
      refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
      intro x hx
      rw [Set.uIcc_of_le hn', Set.mem_Icc] at hx
      exact_mod_cast (by linarith : x ≠ 0)
    have hwindow : (F 0 * ∫ x in (1:ℝ)..(n:ℝ),
          Complex.exp ((t*x : ℝ) * Complex.I) / (x:ℂ))
        + F 0 * -∫ x in (1:ℝ)..(n:ℝ), Complex.exp (-((t*x : ℝ)) * Complex.I) / (x:ℂ)
        = F 0 * ∫ x in (1:ℝ)..(n:ℝ),
            (Complex.exp ((t*x : ℝ) * Complex.I)
              - Complex.exp (-((t*x : ℝ)) * Complex.I)) / (x:ℂ) := by
      have hcont2' : IntervalIntegrable
          (fun x : ℝ => -(Complex.exp (-((t*x : ℝ)) * Complex.I) / (x:ℂ)))
          volume 1 (n:ℝ) := hcont2.neg
      rw [← mul_add, ← intervalIntegral.integral_neg,
        ← intervalIntegral.integral_add hcont1 hcont2']
      congr 1
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      ring
    -- recombine the F-tail set integrals
    have hFtails : (∫ x in Set.Ioc (-(n:ℝ)) (-1:ℝ), (F x/(x:ℂ)) * e x)
        + ∫ x in Set.Ioc (1:ℝ) (n:ℝ), (F x/(x:ℂ)) * e x
        = ∫ x in (Set.Ioc (-(n:ℝ)) (-1:ℝ) ∪ Set.Ioc (1:ℝ) (n:ℝ)), (F x/(x:ℂ)) * e x := by
      rw [MeasureTheory.setIntegral_union ?_ measurableSet_Ioc
        (hFx_int _ _ hneg_sub) (hFx_int _ _ hpos_sub)]
      refine Set.disjoint_left.mpr (fun x hx hx' => ?_)
      rw [Set.mem_Ioc] at hx hx'
      linarith [hx.2, hx'.1]
    linear_combination hwindow - hFtails
  -- assemble the limit
  have hlim : Tendsto (fun n : ℕ =>
      (∫ x in Set.Ioc (-1:ℝ) 1, h x * e x)
        + (F 0 * ∫ x in (1:ℝ)..((n:ℕ):ℝ),
            (Complex.exp ((t*x : ℝ) * Complex.I)
              - Complex.exp (-((t*x : ℝ)) * Complex.I)) / (x:ℂ))
        - ∫ x in (Set.Ioc (-((n:ℕ):ℝ)) (-1:ℝ) ∪ Set.Ioc (1:ℝ) ((n:ℕ):ℝ)),
            (F x/(x:ℂ)) * e x)
      atTop (nhds (gammaFT F t)) := by
    -- window limit
    have hT2 : Tendsto (fun n : ℕ => F 0 * ∫ x in (1:ℝ)..((n:ℕ):ℝ),
        (Complex.exp ((t*x : ℝ) * Complex.I)
          - Complex.exp (-((t*x : ℝ)) * Complex.I)) / (x:ℂ))
        atTop (nhds (F 0 * (2 * Complex.I * ((Real.sign t * sincTail |t| : ℝ) : ℂ)))) := by
      refine Filter.Tendsto.const_mul _ ?_
      exact (tendsto_integral_cexp_sub_div_window' ht).comp
        tendsto_natCast_atTop_atTop
    -- tail limit: the union is exactly the complement
    have hUnion : (⋃ n : ℕ, (Set.Ioc (-((n:ℕ):ℝ)) (-1:ℝ) ∪ Set.Ioc (1:ℝ) ((n:ℕ):ℝ)))
        = (Set.Ioc (-1:ℝ) 1)ᶜ := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_union, Set.mem_Ioc, Set.mem_compl_iff]
      constructor
      · rintro ⟨n, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
        · push Not
          intro h'
          linarith
        · push Not
          intro h'
          linarith
      · intro hx
        push Not at hx
        rcases le_or_gt x (-1) with h' | h'
        · obtain ⟨n, hn⟩ := exists_nat_gt (-x)
          exact ⟨n, Or.inl ⟨by linarith, h'⟩⟩
        · have h'' := hx h'
          obtain ⟨n, hn⟩ := exists_nat_gt x
          exact ⟨n, Or.inr ⟨h'', hn.le⟩⟩
    have hmono : Monotone (fun n : ℕ =>
        Set.Ioc (-((n:ℕ):ℝ)) (-1:ℝ) ∪ Set.Ioc (1:ℝ) ((n:ℕ):ℝ)) := by
      intro m n hmn
      have hmn' : ((m:ℕ):ℝ) ≤ ((n:ℕ):ℝ) := by exact_mod_cast hmn
      refine Set.union_subset_union ?_ ?_
      · exact Set.Ioc_subset_Ioc_left (by linarith)
      · exact Set.Ioc_subset_Ioc_right hmn'
    have hint_union : IntegrableOn (fun x => (F x/(x:ℂ)) * e x)
        (⋃ n : ℕ, (Set.Ioc (-((n:ℕ):ℝ)) (-1:ℝ) ∪ Set.Ioc (1:ℝ) ((n:ℕ):ℝ))) := by
      rw [hUnion]
      refine hFx_tail.mul_bdd (c := 1) (he_meas.restrict) ?_
      exact Filter.Eventually.of_forall (fun x => by rw [he_bd x])
    have hT3 : Tendsto (fun n : ℕ =>
        ∫ x in (Set.Ioc (-((n:ℕ):ℝ)) (-1:ℝ) ∪ Set.Ioc (1:ℝ) ((n:ℕ):ℝ)),
          (F x/(x:ℂ)) * e x)
        atTop (nhds (∫ x in (Set.Ioc (-1:ℝ) 1)ᶜ, (F x/(x:ℂ)) * e x)) := by
      have h0 := MeasureTheory.tendsto_setIntegral_of_monotone₀
        (s := fun n : ℕ => Set.Ioc (-((n:ℕ):ℝ)) (-1:ℝ) ∪ Set.Ioc (1:ℝ) ((n:ℕ):ℝ))
        (fun n => (measurableSet_Ioc.union measurableSet_Ioc).nullMeasurableSet)
        hmono hint_union
      rw [hUnion] at h0
      exact h0
    have hT1 : Tendsto (fun _ : ℕ => ∫ x in Set.Ioc (-1:ℝ) 1, h x * e x)
        atTop (nhds (∫ x in Set.Ioc (-1:ℝ) 1, h x * e x)) := tendsto_const_nhds
    have hfinal := (hT1.add hT2).sub hT3
    have hval : (∫ x in Set.Ioc (-1:ℝ) 1, h x * e x)
        + F 0 * (2 * Complex.I * ((Real.sign t * sincTail |t| : ℝ) : ℂ))
        - ∫ x in (Set.Ioc (-1:ℝ) 1)ᶜ, (F x/(x:ℂ)) * e x = gammaFT F t := by
      rw [gammaFT]
    rw [hval] at hfinal
    exact hfinal
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact (hEq n hn).symm

/-- **L² convergence of truncations**: for `g ∈ L²`,
`eLpNorm (1_{(-n,n]}·g - g) 2 → 0`. -/
theorem tendsto_eLpNorm_indicator_truncation {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) :
    Tendsto (fun n : ℕ => eLpNorm
        ((Set.Ioc (-(n:ℝ)) (n:ℝ)).indicator g - g) 2 (volume : Measure ℝ))
      atTop (nhds 0) := by
  have hkey : ∀ n : ℕ, eLpNorm ((Set.Ioc (-(n:ℝ)) (n:ℝ)).indicator g - g) 2 volume
      = (∫⁻ x, ((Set.Ioc (-(n:ℝ)) (n:ℝ))ᶜ.indicator (fun y => ‖g y‖ₑ ^ (2:ℝ)) x))
        ^ (1/(2:ℝ)) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    rw [show ((2:ℝ≥0∞).toReal) = (2:ℝ) by norm_num]
    congr 1
    refine lintegral_congr (fun x => ?_)
    rw [Pi.sub_apply]
    rcases (em (x ∈ Set.Ioc (-(n:ℝ)) (n:ℝ))) with hx | hx
    · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem (by simpa using hx)]
      simp
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem (by simpa using hx)]
      simp [enorm_neg]
  simp only [hkey]
  -- dominated convergence for the inner lintegral
  have hdom : Tendsto (fun n : ℕ => ∫⁻ x,
      ((Set.Ioc (-(n:ℝ)) (n:ℝ))ᶜ.indicator (fun y => ‖g y‖ₑ ^ (2:ℝ)) x))
      atTop (nhds 0) := by
    have h0 : (0 : ℝ≥0∞) = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) ∂(volume : Measure ℝ) := by simp
    rw [h0]
    refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
      (bound := fun x => ‖g x‖ₑ ^ (2:ℝ)) ?_ ?_ ?_ ?_
    · intro n
      refine AEMeasurable.indicator ?_ (measurableSet_Ioc.compl)
      exact (hg.aestronglyMeasurable.enorm.pow_const _)
    · intro n
      refine Filter.Eventually.of_forall (fun x => ?_)
      rcases (em (x ∈ (Set.Ioc (-(n:ℝ)) (n:ℝ))ᶜ)) with hx | hx
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        exact bot_le
    · have := hg.eLpNorm_lt_top
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
        show ((2:ℝ≥0∞).toReal) = (2:ℝ) by norm_num] at this
      have h1 : (∫⁻ x, ‖g x‖ₑ ^ (2:ℝ)) < ⊤ := by
        by_contra hcon
        push Not at hcon
        rw [top_le_iff.mp hcon] at this
        simp at this
      exact h1.ne
    · refine Filter.Eventually.of_forall (fun x => ?_)
      obtain ⟨N, hN⟩ := exists_nat_gt |x|
      refine tendsto_nhds_of_eventually_eq ?_
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have hx : x ∈ Set.Ioc (-(n:ℝ)) (n:ℝ) := by
        rw [Set.mem_Ioc]
        have h2 : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
        constructor
        · nlinarith [abs_nonneg x, neg_abs_le x]
        · nlinarith [le_abs_self x]
      rw [Set.indicator_of_notMem (by simpa using hx)]
  -- continuity of `· ^ (1/2)` at 0
  have hcont : Tendsto (fun z : ℝ≥0∞ => z ^ (1/(2:ℝ))) (nhds 0) (nhds 0) := by
    have h0 := (ENNReal.continuous_rpow_const (y := 1/(2:ℝ))).tendsto 0
    rw [show (0:ℝ≥0∞) ^ (1/(2:ℝ)) = 0 by
      rw [ENNReal.zero_rpow_of_pos (by norm_num)]] at h0
    exact h0
  exact hcont.comp hdom

/-- **Poitou's `γ` is the `L²` Fourier transform** (P-c): for `F` integrable with
`(F(0)-F(x))/x` locally integrable at `0` and square-integrable, `gammaFT F` agrees a.e.
with a representative of the `L²` Fourier transform of `(F(0)-F(x))/x`, reflected and
rescaled to the `e^{itx}` convention. -/
theorem gammaFT_ae_eq_fourierL2 {F : ℝ → ℂ} (hF : Integrable F)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    (hFdiv2 : MemLp (fun x : ℝ => (F 0 - F x)/(x:ℂ)) 2 (volume : Measure ℝ)) :
    (fun t : ℝ => gammaFT F t) =ᵐ[volume]
      (fun t : ℝ => ((𝓕 (hFdiv2.toLp _) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
        (-t/(2*π))) := by
  classical
  set h : ℝ → ℂ := fun x => (F 0 - F x)/(x:ℂ) with hh
  set hn : ℕ → ℝ → ℂ := fun n => (Set.Ioc (-(n:ℝ)) (n:ℝ)).indicator h with hhn
  -- truncations are L¹ ∩ L²
  have hIntOn : ∀ n : ℕ, IntegrableOn h (Set.Ioc (-(n:ℝ)) (n:ℝ)) := by
    intro n
    have : IsFiniteMeasure (volume.restrict (Set.Ioc (-(n:ℝ)) (n:ℝ))) := by
      constructor
      rw [Measure.restrict_apply_univ, Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    have h1 : MemLp h 2 (volume.restrict (Set.Ioc (-(n:ℝ)) (n:ℝ))) :=
      hFdiv2.restrict _
    have h2 : MemLp (fun _ : ℝ => (1:ℂ)) 2
        (volume.restrict (Set.Ioc (-(n:ℝ)) (n:ℝ))) := memLp_const _
    have h3 := MemLp.integrable_mul h1 h2
    refine h3.congr (Filter.Eventually.of_forall (fun x => ?_))
    show h x * 1 = h x
    rw [mul_one]
  have hn1 : ∀ n : ℕ, Integrable (hn n) := by
    intro n
    rw [hhn]
    exact (integrable_indicator_iff measurableSet_Ioc).mpr (hIntOn n)
  have hn2 : ∀ n : ℕ, MemLp (hn n) 2 (volume : Measure ℝ) := by
    intro n
    rw [hhn]
    exact hFdiv2.indicator measurableSet_Ioc
  -- the eLpNorm of the transform difference equals the eLpNorm of the truncation error
  have hbr : ∀ u : Lp ℂ 2 (volume : Measure ℝ),
      (𝓕 u : Lp ℂ 2 (volume : Measure ℝ))
        = MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ u := fun _ => rfl
  have hLp_eLp : ∀ c : Lp ℂ 2 (volume : Measure ℝ),
      eLpNorm (⇑(𝓕 c : Lp ℂ 2 (volume : Measure ℝ))) 2 volume = eLpNorm (⇑c) 2 volume := by
    intro c
    have e1 : eLpNorm (⇑(𝓕 c : Lp ℂ 2 (volume : Measure ℝ))) 2 volume
        = ENNReal.ofReal ‖(𝓕 c : Lp ℂ 2 (volume : Measure ℝ))‖ := by
      rw [MeasureTheory.Lp.norm_def,
        ENNReal.ofReal_toReal (MeasureTheory.Lp.eLpNorm_ne_top _)]
    have e2 : eLpNorm (⇑c) 2 volume = ENNReal.ofReal ‖c‖ := by
      rw [MeasureTheory.Lp.norm_def,
        ENNReal.ofReal_toReal (MeasureTheory.Lp.eLpNorm_ne_top _)]
    rw [e1, e2, MeasureTheory.Lp.norm_fourier_eq]
  have hstep : ∀ n : ℕ,
      eLpNorm ((𝓕 (fun x : ℝ => hn n x))
        - ((𝓕 (hFdiv2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) 2 volume
      = eLpNorm (hn n - h) 2 volume := by
    intro n
    have h1 : (𝓕 (fun x : ℝ => hn n x))
        =ᵐ[volume] ((𝓕 ((hn2 n).toLp (hn n)) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) :=
      (coeFn_fourier_toLp_two (hn1 n) (hn2 n)).symm
    rw [eLpNorm_congr_ae (Filter.EventuallyEq.sub h1 (Filter.EventuallyEq.refl _ _))]
    have h2 : (((𝓕 ((hn2 n).toLp (hn n)) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
        - ((𝓕 (hFdiv2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
        =ᵐ[volume] ((𝓕 ((hn2 n).toLp (hn n)) - 𝓕 (hFdiv2.toLp h)
          : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) :=
      (MeasureTheory.Lp.coeFn_sub _ _).symm
    rw [eLpNorm_congr_ae h2]
    have h3 : (𝓕 ((hn2 n).toLp (hn n)) - 𝓕 (hFdiv2.toLp h)
        : Lp ℂ 2 (volume : Measure ℝ))
        = (𝓕 ((hn2 n).toLp (hn n) - hFdiv2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) := by
      rw [hbr, hbr, hbr, ← map_sub]
    rw [h3, hLp_eLp]
    refine eLpNorm_congr_ae ?_
    filter_upwards [MeasureTheory.Lp.coeFn_sub ((hn2 n).toLp (hn n)) (hFdiv2.toLp h),
      (hn2 n).coeFn_toLp, hFdiv2.coeFn_toLp] with x hx1 hx2 hx3
    rw [hx1, Pi.sub_apply, hx2, hx3]
    rfl
  have heLp : Tendsto (fun n : ℕ =>
      eLpNorm ((𝓕 (fun x : ℝ => hn n x))
        - ((𝓕 (hFdiv2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) 2 volume)
      atTop (nhds 0) := by
    simp only [hstep]
    exact tendsto_eLpNorm_indicator_truncation hFdiv2
  -- convergence in measure and an a.e.-convergent subsequence
  have hmeas : TendstoInMeasure volume (fun n : ℕ => 𝓕 (fun x : ℝ => hn n x)) atTop
      ((𝓕 (hFdiv2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_ ?_ heLp
    · intro n
      refine Continuous.aestronglyMeasurable ?_
      exact VectorFourier.fourierIntegral_continuous (by fun_prop) (by fun_prop) (hn1 n)
    · exact (MeasureTheory.Lp.memLp _).aestronglyMeasurable
  obtain ⟨ns, hns_mono, hns_ae⟩ := hmeas.exists_seq_tendsto_ae
  -- pull the a.e. statement back through ξ = -t/(2π)
  have hqmp : Measure.QuasiMeasurePreserving (fun t : ℝ => -t/(2*π))
      volume volume := by
    have h0 : (fun t : ℝ => -t/(2*π)) = fun t : ℝ => (-(2*π))⁻¹ * t := by
      funext t
      field_simp
    rw [h0]
    refine ⟨by fun_prop, ?_⟩
    have hne0 : ((-(2*π))⁻¹ : ℝ) ≠ 0 := by
      refine inv_ne_zero ?_
      refine neg_ne_zero.mpr ?_
      positivity
    rw [Real.map_volume_mul_left hne0]
    exact Measure.smul_absolutelyContinuous
  have hae_t := hqmp.ae hns_ae
  -- combine with the pointwise truncated convergence
  have hne : ∀ᵐ t : ℝ, t ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
    exact MeasureTheory.measure_singleton 0
  filter_upwards [hae_t, hne] with t hlim ht
  have hpt : Tendsto (fun i : ℕ => 𝓕 (fun x : ℝ => hn (ns i) x) (-t/(2*π)))
      atTop (nhds (gammaFT F t)) := by
    have h0 : ∀ n : ℕ, 𝓕 (fun x : ℝ => hn n x) (-t/(2*π))
        = ∫ x in Set.Ioc (-(n:ℝ)) (n:ℝ), h x * Complex.exp ((t*x : ℝ) * Complex.I) := by
      intro n
      rw [← muFT_eq_fourierIntegral (fun x : ℝ => hn n x) t]
      rw [hhn]
      rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      show (Set.Ioc (-(n:ℝ)) (n:ℝ)).indicator h x * Complex.exp ((t*x : ℝ) * Complex.I)
          = (Set.Ioc (-(n:ℝ)) (n:ℝ)).indicator
              (fun y => h y * Complex.exp ((t*y : ℝ) * Complex.I)) x
      simp only [Set.indicator_apply]
      split_ifs with hx
      · rfl
      · rw [zero_mul]
    simp only [h0]
    exact (tendsto_truncated_fourier_gammaFT hF hFdiv ht).comp
      (hns_mono.tendsto_atTop)
  exact tendsto_nhds_unique hpt hlim

/-- **`μγ` is integrable** (P-d prerequisite): the product of the two transforms is
integrable, being a.e. a product of two `L²` representatives after rescaling. -/
theorem integrable_muFT_mul_gammaFT {k F : ℝ → ℂ}
    (hk1 : Integrable k) (hk2 : MemLp k 2 (volume : Measure ℝ))
    (hF : Integrable F)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    (hFdiv2 : MemLp (fun x : ℝ => (F 0 - F x)/(x:ℂ)) 2 (volume : Measure ℝ)) :
    Integrable (fun t : ℝ =>
      (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t) := by
  set repk : ℝ → ℂ := ((𝓕 (hk2.toLp k) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) with hrepk
  set reph : ℝ → ℂ := ((𝓕 (hFdiv2.toLp _) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
    with hreph
  -- integrable product of the scaled reps
  have hprod : Integrable (fun t : ℝ => repk (-t/(2*π)) * reph (-t/(2*π))) := by
    have h0 : Integrable (fun s : ℝ => repk s * reph s) :=
      MemLp.integrable_mul (MeasureTheory.Lp.memLp _) (MeasureTheory.Lp.memLp _)
    have h1 : Integrable (fun t : ℝ => (fun s : ℝ => repk s * reph s) ((-(2*π))⁻¹ * t)) := by
      rw [MeasureTheory.integrable_comp_mul_left_iff
        (fun s : ℝ => repk s * reph s)
        (inv_ne_zero (neg_ne_zero.mpr (by positivity : (2*π : ℝ) ≠ 0)))]
      exact h0
    refine h1.congr (Filter.Eventually.of_forall (fun t => ?_))
    field_simp
  -- transfer along a.e. equality
  have hμeq : ∀ t : ℝ, (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I))
      = 𝓕 k (-t/(2*π)) := fun t => muFT_eq_fourierIntegral k t
  have hkae : (fun t : ℝ => 𝓕 k (-t/(2*π))) =ᵐ[volume]
      (fun t : ℝ => repk (-t/(2*π))) := by
    have h0 : (𝓕 k) =ᵐ[volume] repk := (coeFn_fourier_toLp_two hk1 hk2).symm
    have hqmp : Measure.QuasiMeasurePreserving (fun t : ℝ => -t/(2*π))
        (volume : Measure ℝ) (volume : Measure ℝ) := by
      have h1 : (fun t : ℝ => -t/(2*π)) = fun t : ℝ => (-(2*π))⁻¹ * t := by
        funext t
        field_simp
      rw [h1]
      refine ⟨by fun_prop, ?_⟩
      rw [Real.map_volume_mul_left (inv_ne_zero (neg_ne_zero.mpr
        (by positivity : (2*π : ℝ) ≠ 0)))]
      exact Measure.smul_absolutelyContinuous
    exact hqmp.ae h0
  have hγae : (fun t : ℝ => gammaFT F t) =ᵐ[volume]
      (fun t : ℝ => reph (-t/(2*π))) := gammaFT_ae_eq_fourierL2 hF hFdiv hFdiv2
  refine hprod.congr ?_
  filter_upwards [hkae, hγae] with t h1 h2
  rw [hμeq t, h1, h2]

/-- **The Plancherel evaluation of `∫μγ`** (P-d, Poitou p. 6-06): for `k ∈ L¹∩L²` and
admissible `F`,
`∫ μ(t)γ(t) dt = 2π ∫ k(-x)·(F(0)-F(x))/x dx`. -/
theorem integral_muFT_mul_gammaFT {k F : ℝ → ℂ}
    (hk1 : Integrable k) (hk2 : MemLp k 2 (volume : Measure ℝ))
    (hF : Integrable F)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    (hFdiv2 : MemLp (fun x : ℝ => (F 0 - F x)/(x:ℂ)) 2 (volume : Measure ℝ)) :
    (∫ t : ℝ, (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t)
      = ((2*π : ℝ) : ℂ) * ∫ x : ℝ, k (-x) * ((F 0 - F x)/(x:ℂ)) := by
  set repk : ℝ → ℂ := ((𝓕 (hk2.toLp k) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) with hrepk
  set reph : ℝ → ℂ := ((𝓕 (hFdiv2.toLp _) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
    with hreph
  have hμeq : ∀ t : ℝ, (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I))
      = 𝓕 k (-t/(2*π)) := fun t => muFT_eq_fourierIntegral k t
  have hkae : (fun t : ℝ => 𝓕 k (-t/(2*π))) =ᵐ[volume]
      (fun t : ℝ => repk (-t/(2*π))) := by
    have h0 : (𝓕 k) =ᵐ[volume] repk := (coeFn_fourier_toLp_two hk1 hk2).symm
    have hqmp : Measure.QuasiMeasurePreserving (fun t : ℝ => -t/(2*π))
        (volume : Measure ℝ) (volume : Measure ℝ) := by
      have h1 : (fun t : ℝ => -t/(2*π)) = fun t : ℝ => (-(2*π))⁻¹ * t := by
        funext t
        field_simp
      rw [h1]
      refine ⟨by fun_prop, ?_⟩
      rw [Real.map_volume_mul_left (inv_ne_zero (neg_ne_zero.mpr
        (by positivity : (2*π : ℝ) ≠ 0)))]
      exact Measure.smul_absolutelyContinuous
    exact hqmp.ae h0
  have hγae : (fun t : ℝ => gammaFT F t) =ᵐ[volume]
      (fun t : ℝ => reph (-t/(2*π))) := gammaFT_ae_eq_fourierL2 hF hFdiv hFdiv2
  -- replace by the scaled representatives
  have h1 : (∫ t : ℝ, (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t)
      = ∫ t : ℝ, repk (-t/(2*π)) * reph (-t/(2*π)) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hkae, hγae] with t hk' hγ'
    rw [hμeq t, hk', hγ']
  rw [h1]
  -- rescale
  have h2 : (∫ t : ℝ, repk (-t/(2*π)) * reph (-t/(2*π)))
      = |((-(2*π))⁻¹)⁻¹| • ∫ s : ℝ, repk s * reph s := by
    rw [← MeasureTheory.Measure.integral_comp_mul_left
      (fun s : ℝ => repk s * reph s) ((-(2*π))⁻¹)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    field_simp
  rw [h2]
  have h3 : |((-(2*π))⁻¹)⁻¹| = (2*π : ℝ) := by
    rw [inv_inv, abs_neg, abs_of_pos (by positivity)]
  rw [h3]
  -- evaluate via the mixed Plancherel pairing
  have h4 : (∫ s : ℝ, repk s * reph s)
      = ∫ x : ℝ, k (-x) * ((F 0 - F x)/(x:ℂ)) := by
    have h5 : (∫ s : ℝ, repk s * reph s) = ∫ s : ℝ, 𝓕 k s * reph s := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [(coeFn_fourier_toLp_two hk1 hk2)] with s hs
      rw [hrepk]
      show ((𝓕 (hk2.toLp k) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) s * reph s
          = 𝓕 k s * reph s
      rw [hs]
    rw [h5, hreph]
    exact integral_fourier_mul_fourierL2 hk1 hk2 hFdiv2
  rw [h4, Complex.real_smul]

/-- **Proposition 3, abstract form** (Poitou p. 6-04/6-06): for `k ∈ L¹∩L²` and
admissible `F` with the boundary decay `ρ(t)γ(t) → 0`, the symmetric truncations of
`∫ρφ` converge:

`lim_{T→∞} ∫_{-T}^T ρ(t)·φ(t) dt = -2π ∫ k(-x)·(F(0)-F(x))/x dx`.

For odd `k` the right side is `+2π ∫ k(x)·(F(0)-F(x))/x dx`. -/
theorem tendsto_integral_rhoFT_mul_phi_eq_plancherel {k F : ℝ → ℂ}
    (hk1 : Integrable k) (hk2 : MemLp k 2 (volume : Measure ℝ))
    (hF : Integrable F)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    (hFdiv2 : MemLp (fun x : ℝ => (F 0 - F x)/(x:ℂ)) 2 (volume : Measure ℝ))
    (htop : Tendsto (fun t : ℝ => rhoFT k t * gammaFT F t) atTop (nhds 0))
    (hbot : Tendsto (fun t : ℝ => rhoFT k t * gammaFT F t) atBot (nhds 0)) :
    Tendsto (fun T : ℝ => ∫ t in (-T)..T,
        rhoFT k t * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)))
      atTop (nhds (-(((2*π : ℝ) : ℂ) * ∫ x : ℝ, k (-x) * ((F 0 - F x)/(x:ℂ))))) := by
  have h0 := tendsto_integral_rhoFT_mul_phi hk1 hF hFdiv
    (integrable_muFT_mul_gammaFT hk1 hk2 hF hFdiv hFdiv2) htop hbot
  rw [integral_muFT_mul_gammaFT hk1 hk2 hF hFdiv hFdiv2] at h0
  exact h0

/-- **Poitou's odd kernel** (p. 6-06): the odd extension of
`x ↦ x e^{-σx}/(1-e^{-x})` from `x > 0`. -/
noncomputable def poitouKernel (σ : ℝ) (x : ℝ) : ℝ :=
  Real.sign x * (|x| * Real.exp (-(σ*|x|)) / (1 - Real.exp (-|x|)))

theorem poitouKernel_neg (σ x : ℝ) : poitouKernel σ (-x) = -poitouKernel σ x := by
  rw [poitouKernel, poitouKernel, Real.sign_neg, abs_neg]
  ring

theorem poitouKernel_of_pos {σ x : ℝ} (hx : 0 < x) :
    poitouKernel σ x = x * Real.exp (-(σ*x)) / (1 - Real.exp (-x)) := by
  rw [poitouKernel, Real.sign_of_pos hx, abs_of_pos hx, one_mul]

/-- The kernel profile bound: `|poitouKernel σ x| ≤ (1+|x|)e^{-σ|x|}` (from
`y/(1-e^{-y}) ≤ 1+y`, i.e. `(1+y)e^{-y} ≤ 1`). -/
theorem abs_poitouKernel_le (σ : ℝ) (x : ℝ) :
    |poitouKernel σ x| ≤ (1 + |x|) * Real.exp (-(σ*|x|)) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [poitouKernel, Real.sign_of_neg hx, abs_mul, abs_neg, abs_one, one_mul]
    have hax : 0 < |x| := abs_pos.mpr hx.ne
    have hden : 0 < 1 - Real.exp (-|x|) := by
      have := Real.exp_lt_exp.mpr (show -|x| < 0 by linarith)
      rw [Real.exp_zero] at this
      linarith
    rw [abs_div, abs_mul, abs_abs, Real.abs_exp, abs_of_pos hden,
      div_le_iff₀ hden]
    have hkey : (1 + |x|) * Real.exp (-|x|) ≤ 1 := by
      have h0 := Real.add_one_le_exp |x|
      rw [Real.exp_neg]
      rw [mul_inv_le_iff₀ (Real.exp_pos _)]
      linarith
    nlinarith [Real.exp_pos (-(σ*|x|)), Real.exp_pos (-|x|), abs_nonneg x,
      mul_pos (Real.exp_pos (-(σ*|x|))) hden]
  · rw [hx]
    simp [poitouKernel]
  · rw [poitouKernel, Real.sign_of_pos hx, one_mul]
    have hax : 0 < |x| := abs_pos.mpr hx.ne'
    have hden : 0 < 1 - Real.exp (-|x|) := by
      have := Real.exp_lt_exp.mpr (show -|x| < 0 by linarith)
      rw [Real.exp_zero] at this
      linarith
    rw [abs_div, abs_mul, abs_abs, Real.abs_exp, abs_of_pos hden,
      div_le_iff₀ hden]
    have hkey : (1 + |x|) * Real.exp (-|x|) ≤ 1 := by
      have h0 := Real.add_one_le_exp |x|
      rw [Real.exp_neg]
      rw [mul_inv_le_iff₀ (Real.exp_pos _)]
      linarith
    nlinarith [Real.exp_pos (-(σ*|x|)), Real.exp_pos (-|x|), abs_nonneg x,
      mul_pos (Real.exp_pos (-(σ*|x|))) hden]

/-- The two-sided exponential `e^{-a|x|}` is integrable. -/
theorem integrable_exp_neg_mul_abs' {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-(a*|x|))) :=
  (integrable_exp_neg_mul_abs ha).congr
    (Filter.Eventually.of_forall (fun x => by
      show Real.exp (-a * |x|) = Real.exp (-(a * |x|))
      rw [neg_mul]))

/-- The exponential-polynomial majorant bound: `(1+|x|)e^{-a|x|} ≤ (1+2/a)e^{-a|x|/2}`. -/
theorem one_add_abs_mul_exp_le {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (1 + |x|) * Real.exp (-(a*|x|)) ≤ (1 + 2/a) * Real.exp (-(a*|x|/2)) := by
  have h1 : |x| * Real.exp (-(a*|x|)) ≤ (2/a) * Real.exp (-(a*|x|/2)) := by
    have h2 : a*|x|/2 + 1 ≤ Real.exp (a*|x|/2) := Real.add_one_le_exp _
    have h3 : |x| ≤ (2/a) * Real.exp (a*|x|/2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ ha]
      nlinarith [abs_nonneg x]
    calc |x| * Real.exp (-(a*|x|))
        ≤ ((2/a) * Real.exp (a*|x|/2)) * Real.exp (-(a*|x|)) := by
          refine mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = (2/a) * Real.exp (-(a*|x|/2)) := by
          rw [mul_assoc, ← Real.exp_add]
          ring_nf
  have h4 : Real.exp (-(a*|x|)) ≤ Real.exp (-(a*|x|/2)) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [abs_nonneg x]
  nlinarith [Real.exp_pos (-(a*|x|/2))]

/-- The exponential-polynomial majorant is integrable on the whole line. -/
theorem integrable_one_add_abs_mul_exp {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => (1 + |x|) * Real.exp (-(a*|x|))) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (1 + |x|) * Real.exp (-(a*|x|)))
      (volume : Measure ℝ) := by
    refine Continuous.aestronglyMeasurable ?_
    fun_prop
  refine MeasureTheory.Integrable.mono'
    (g := fun x => (1 + 2/a) * Real.exp (-(a*|x|/2)))
    (((integrable_exp_neg_mul_abs' (show (0:ℝ) < a/2 by positivity)).congr
      (Filter.Eventually.of_forall (fun x => by
        show Real.exp (-(a/2*|x|)) = Real.exp (-(a*|x|/2))
        ring_nf))).const_mul _) hmeas ?_
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact one_add_abs_mul_exp_le ha x)

/-- Total form of the Poitou kernel: `sign x·|x| = x` collapses the piecewise
definition. -/
theorem poitouKernel_eq (σ x : ℝ) :
    poitouKernel σ x = x * Real.exp (-(σ*|x|)) / (1 - Real.exp (-|x|)) := by
  have hs : Real.sign x * |x| = x := by
    rcases lt_trichotomy x 0 with h | h | h
    · rw [Real.sign_of_neg h, abs_of_neg h]
      ring
    · rw [h, Real.sign_zero, abs_zero, mul_zero]
    · rw [Real.sign_of_pos h, abs_of_pos h, one_mul]
  rw [poitouKernel, show Real.sign x * (|x| * Real.exp (-(σ*|x|)) / (1 - Real.exp (-|x|)))
      = (Real.sign x * |x|) * Real.exp (-(σ*|x|)) / (1 - Real.exp (-|x|)) from by ring,
    hs]

/-- The Poitou kernel is measurable. -/
theorem measurable_poitouKernel (σ : ℝ) : Measurable (poitouKernel σ) := by
  have h0 : poitouKernel σ = fun x => x * Real.exp (-(σ*|x|)) / (1 - Real.exp (-|x|)) :=
    funext (poitouKernel_eq σ)
  rw [h0]
  fun_prop

/-- The (complexified) Poitou kernel is integrable (K3). -/
theorem integrable_poitouKernel {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun x : ℝ => ((poitouKernel σ x : ℝ) : ℂ)) := by
  refine MeasureTheory.Integrable.mono' (integrable_one_add_abs_mul_exp hσ) ?_ ?_
  · exact (Complex.measurable_ofReal.comp (measurable_poitouKernel σ)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_poitouKernel_le σ x

/-- The (complexified) Poitou kernel is square-integrable (K4). -/
theorem memLp_two_poitouKernel {σ : ℝ} (hσ : 0 < σ) :
    MemLp (fun x : ℝ => ((poitouKernel σ x : ℝ) : ℂ)) 2 (volume : Measure ℝ) := by
  have hmaj : MemLp (fun x : ℝ => (1 + |x|) * Real.exp (-(σ*|x|))) 2
      (volume : Measure ℝ) := by
    rw [memLp_two_iff_integrable_sq (by
      refine Continuous.aestronglyMeasurable ?_
      fun_prop)]
    have h0 : ∀ x : ℝ, ((1 + |x|) * Real.exp (-(σ*|x|)))^2
        ≤ (1 + 2/σ)^2 * Real.exp (-(σ*|x|)) := by
      intro x
      have h1 := one_add_abs_mul_exp_le hσ x
      have h2 : ((1 + |x|) * Real.exp (-(σ*|x|)))^2
          ≤ ((1 + 2/σ) * Real.exp (-(σ*|x|/2)))^2 := by
        refine pow_le_pow_left₀ (by positivity) h1 2
      refine le_trans h2 (le_of_eq ?_)
      rw [mul_pow]
      congr 1
      rw [sq, ← Real.exp_add]
      ring_nf
    refine MeasureTheory.Integrable.mono'
      (((integrable_exp_neg_mul_abs' hσ).const_mul ((1 + 2/σ)^2))) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      fun_prop
    · refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact h0 x
  refine MemLp.of_le hmaj ?_ ?_
  · exact (Complex.measurable_ofReal.comp (measurable_poitouKernel σ)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    refine le_trans (abs_poitouKernel_le σ x) (le_abs_self _)

/-- **The ρ-fold identity** (K5, Poitou p. 6-06): for the odd Poitou kernel,
`ρ(t) = 2(Re ψ(σ+it) - ψ(σ))` — in particular `ρ` is real-valued. This is the bridge
between the abstract Proposition 3 and the digamma kernel identities. -/
theorem rhoFT_poitouKernel {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    rhoFT (fun x => ((poitouKernel σ x : ℝ) : ℂ)) t
      = (((2 * ((Complex.digamma ((σ:ℂ) + (t:ℂ)*Complex.I)
          - Complex.digamma (σ:ℂ)).re) : ℝ)) : ℂ) := by
  set k : ℝ → ℂ := fun x => ((poitouKernel σ x : ℝ) : ℂ) with hk
  have hint := integrable_rhoFT_integrand (integrable_poitouKernel hσ) t
  rw [rhoFT]
  -- split at 0
  have hsplit := MeasureTheory.integral_add_compl (measurableSet_Iio (a := (0:ℝ)))
    hint
  rw [← hsplit]
  have hcomplIio : (Set.Iio (0:ℝ))ᶜ = Set.Ici (0:ℝ) := by
    ext x
    simp
  rw [hcomplIio]
  -- Ici → Ioi (null point)
  have hIci : (∫ x in Set.Ici (0:ℝ), k x * ((1 - Complex.exp ((t*x : ℝ) * Complex.I))/(x:ℂ)))
      = ∫ x in Set.Ioi (0:ℝ), k x * ((1 - Complex.exp ((t*x : ℝ) * Complex.I))/(x:ℂ)) :=
    (MeasureTheory.setIntegral_congr_set (Ioi_ae_eq_Ici (a := (0:ℝ)))).symm
  rw [hIci]
  -- reflect the negative half-line
  have A : MeasurableEmbedding fun x : ℝ => -x :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have hmap : (volume : Measure ℝ).restrict (Set.Iio (0:ℝ))
      = Measure.map (fun x : ℝ => -x) ((volume : Measure ℝ).restrict (Set.Ioi (0:ℝ))) := by
    rw [show Set.Ioi (0:ℝ) = (fun x : ℝ => -x) ⁻¹' (Set.Iio 0) by ext x; simp,
      ← Measure.restrict_map A.measurable measurableSet_Iio,
      Measure.map_neg_eq_self (volume : Measure ℝ)]
  have hIio : (∫ x in Set.Iio (0:ℝ), k x * ((1 - Complex.exp ((t*x : ℝ) * Complex.I))/(x:ℂ)))
      = ∫ y in Set.Ioi (0:ℝ),
          k y * ((1 - Complex.exp (-((t*y : ℝ)) * Complex.I))/(y:ℂ)) := by
    rw [show (∫ x in Set.Iio (0:ℝ),
        k x * ((1 - Complex.exp ((t*x : ℝ) * Complex.I))/(x:ℂ)))
        = ∫ x, k x * ((1 - Complex.exp ((t*x : ℝ) * Complex.I))/(x:ℂ))
            ∂((volume : Measure ℝ).restrict (Set.Iio 0)) from rfl,
      hmap, A.integral_map]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    rw [Set.mem_Ioi] at hy
    show k (-y) * ((1 - Complex.exp ((t*(-y) : ℝ) * Complex.I))/((-y : ℝ):ℂ))
        = k y * ((1 - Complex.exp (-((t*y : ℝ)) * Complex.I))/(y:ℂ))
    have hkneg : k (-y) = -k y := by
      rw [hk]
      simp only
      rw [poitouKernel_neg]
      push_cast
      ring
    rw [hkneg, show ((t*(-y) : ℝ) : ℂ) = -((t*y : ℝ) : ℂ) by push_cast; ring]
    push_cast
    have hyne : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    field_simp
  rw [hIio]
  -- combine the two half-line integrals
  have hcomb : (∫ y in Set.Ioi (0:ℝ),
        k y * ((1 - Complex.exp (-((t*y : ℝ)) * Complex.I))/(y:ℂ)))
      + (∫ y in Set.Ioi (0:ℝ),
          k y * ((1 - Complex.exp ((t*y : ℝ) * Complex.I))/(y:ℂ)))
      = ∫ y in Set.Ioi (0:ℝ),
          ((2 * (Real.exp (-(σ*y)) * (1 - Real.cos (t*y)) / (1 - Real.exp (-y))) : ℝ) : ℂ) := by
    rw [← MeasureTheory.integral_add ?_ ?_]
    · refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
      rw [Set.mem_Ioi] at hy
      have hyne : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
      have hkpos : k y = ((y * Real.exp (-(σ*y)) / (1 - Real.exp (-y)) : ℝ) : ℂ) := by
        rw [hk]
        simp only
        rw [poitouKernel_of_pos hy]
      have hcos : Complex.exp (-((t*y : ℝ)) * Complex.I)
          + Complex.exp ((t*y : ℝ) * Complex.I) = ((2 * Real.cos (t*y) : ℝ) : ℂ) := by
        rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
        push_cast
        ring
      have hden : (0:ℝ) < 1 - Real.exp (-y) := by
        have := Real.exp_lt_exp.mpr (show -y < 0 by linarith)
        rw [Real.exp_zero] at this
        linarith
      have he1 : Complex.exp ((t*y : ℝ) * Complex.I)
          = ((Real.cos (t*y) : ℝ) : ℂ) + ((Real.sin (t*y) : ℝ) : ℂ) * Complex.I := by
        rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
      have he2 : Complex.exp (-((t*y : ℝ)) * Complex.I)
          = ((Real.cos (t*y) : ℝ) : ℂ) - ((Real.sin (t*y) : ℝ) : ℂ) * Complex.I := by
        rw [show (-((t*y : ℝ)) : ℂ) * Complex.I = (((-(t*y)) : ℝ) : ℂ) * Complex.I by
          push_cast; ring, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
        push_cast
        rw [Complex.cos_neg, Complex.sin_neg]
        ring
      rw [hkpos, he1, he2]
      have hdneC : ((1 - Real.exp (-y) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast hden.ne'
      push_cast at hdneC ⊢
      field_simp
      ring
    · have h0 : Integrable (fun x => k x * ((1 - Complex.exp ((t*x : ℝ) * Complex.I))/(x:ℂ)))
          ((volume : Measure ℝ).restrict (Set.Iio 0)) := hint.integrableOn
      rw [hmap, A.integrable_map_iff] at h0
      refine h0.congr ?_
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      rw [Set.mem_Ioi] at hy
      show k (-y) * ((1 - Complex.exp ((t*(-y) : ℝ) * Complex.I))/((-y : ℝ):ℂ))
          = k y * ((1 - Complex.exp (-((t*y : ℝ)) * Complex.I))/(y:ℂ))
      have hkneg : k (-y) = -k y := by
        rw [hk]
        simp only
        rw [poitouKernel_neg]
        push_cast
        ring
      rw [hkneg, show ((t*(-y) : ℝ) : ℂ) = -((t*y : ℝ) : ℂ) by push_cast; ring]
      push_cast
      have hyne : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
      field_simp
    · exact hint.integrableOn
  rw [hcomb]
  -- evaluate against the digamma kernel identity
  rw [integral_complex_ofReal]
  congr 1
  rw [MeasureTheory.integral_const_mul, re_digamma_sub_eq_integral hσ t]

/-- The even-`F` fold of the kernel pairing: for even `F`,
`∫_ℝ k_σ(-x)·(F(0)-F(x))/x dx = -2∫₀^∞ e^{-σy}(F(0)-F(y))/(1-e^{-y}) dy`. -/
theorem integral_poitouKernel_neg_mul {σ : ℝ} (hσ : 0 < σ) {F : ℝ → ℂ}
    (hFeven : ∀ x : ℝ, F (-x) = F x)
    (hFdiv2 : MemLp (fun x : ℝ => (F 0 - F x)/(x:ℂ)) 2 (volume : Measure ℝ)) :
    (∫ x : ℝ, ((poitouKernel σ (-x) : ℝ) : ℂ) * ((F 0 - F x)/(x:ℂ)))
      = -(2 * ∫ y in Set.Ioi (0:ℝ),
          ((Real.exp (-(σ*y)) / (1 - Real.exp (-y)) : ℝ) : ℂ) * (F 0 - F y)) := by
  classical
  set h : ℝ → ℂ := fun x => (F 0 - F x)/(x:ℂ) with hh
  set k : ℝ → ℂ := fun x => ((poitouKernel σ x : ℝ) : ℂ) with hk
  -- integrability of the pairing
  have hpair_int : Integrable (fun x : ℝ => k (-x) * h x) := by
    have h0 : Integrable (fun x : ℝ => k (-x)) :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable
        (integrable_poitouKernel hσ)
    have h1 : MemLp (fun x : ℝ => k (-x)) 2 (volume : Measure ℝ) :=
      (memLp_two_poitouKernel hσ).comp_measurePreserving
        (Measure.measurePreserving_neg _)
    have h2 := MemLp.integrable_mul h1 hFdiv2
    exact h2
  -- k(-x) = -k(x)
  have hodd : ∀ x : ℝ, k (-x) = -k x := by
    intro x
    rw [hk]
    simp only
    rw [poitouKernel_neg]
    push_cast
    ring
  -- fold to the positive half-line: h is odd for even F
  have hhodd : ∀ x : ℝ, x ≠ 0 → h (-x) = -h x := by
    intro x hx
    rw [hh]
    simp only
    rw [hFeven x]
    push_cast
    have hxne : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    field_simp
  -- split and reflect
  have hsplit := MeasureTheory.integral_add_compl (measurableSet_Iio (a := (0:ℝ)))
    hpair_int
  rw [← hsplit]
  have hcomplIio : (Set.Iio (0:ℝ))ᶜ = Set.Ici (0:ℝ) := by
    ext x
    simp
  rw [hcomplIio]
  have hIci : (∫ x in Set.Ici (0:ℝ), k (-x) * h x)
      = ∫ x in Set.Ioi (0:ℝ), k (-x) * h x :=
    (MeasureTheory.setIntegral_congr_set (Ioi_ae_eq_Ici (a := (0:ℝ)))).symm
  rw [hIci]
  have A : MeasurableEmbedding fun x : ℝ => -x :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have hmap : (volume : Measure ℝ).restrict (Set.Iio (0:ℝ))
      = Measure.map (fun x : ℝ => -x) ((volume : Measure ℝ).restrict (Set.Ioi (0:ℝ))) := by
    rw [show Set.Ioi (0:ℝ) = (fun x : ℝ => -x) ⁻¹' (Set.Iio 0) by ext x; simp,
      ← Measure.restrict_map A.measurable measurableSet_Iio,
      Measure.map_neg_eq_self (volume : Measure ℝ)]
  have hIio : (∫ x in Set.Iio (0:ℝ), k (-x) * h x)
      = ∫ y in Set.Ioi (0:ℝ), k (-y) * h y := by
    rw [show (∫ x in Set.Iio (0:ℝ), k (-x) * h x)
        = ∫ x, k (-x) * h x ∂((volume : Measure ℝ).restrict (Set.Iio 0)) from rfl,
      hmap, A.integral_map]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    rw [Set.mem_Ioi] at hy
    show k (-(-y)) * h (-y) = k (-y) * h y
    rw [neg_neg, hodd y, hhodd y hy.ne']
    ring
  rw [hIio]
  -- both halves agree; evaluate on the positive side
  have hval : (∫ y in Set.Ioi (0:ℝ), k (-y) * h y)
      = -∫ y in Set.Ioi (0:ℝ),
          ((Real.exp (-(σ*y)) / (1 - Real.exp (-y)) : ℝ) : ℂ) * (F 0 - F y) := by
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    rw [Set.mem_Ioi] at hy
    rw [hodd y]
    have hkpos : k y = ((y * Real.exp (-(σ*y)) / (1 - Real.exp (-y)) : ℝ) : ℂ) := by
      rw [hk]
      simp only
      rw [poitouKernel_of_pos hy]
    rw [hkpos, hh]
    simp only
    have hyne : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    push_cast
    field_simp
  rw [hval]
  ring

/-- **Poitou's Proposition 3** (p. 6-04, for the Dedekind kernel): for `σ > 0` and an
even admissible `F` with the boundary decay `ργ → 0`,

`lim_{T→∞} ∫_{-T}^T 2(Re ψ(σ+it) - ψ(σ))·φ(t) dt
   = 4π ∫₀^∞ e^{-σy}(F(0)-F(y))/(1-e^{-y}) dy`,

equivalently `(1/2π)∫(Re ψ(σ+it) - ψ(σ))φ(t)dt = ∫₀^∞ e^{-σx}(F(0)-F(x))/(1-e^{-x})dx`
— exactly Poitou's display. -/
theorem prop3_poitou {σ : ℝ} (hσ : 0 < σ) {F : ℝ → ℂ} (hF : Integrable F)
    (hFeven : ∀ x : ℝ, F (-x) = F x)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    (hFdiv2 : MemLp (fun x : ℝ => (F 0 - F x)/(x:ℂ)) 2 (volume : Measure ℝ))
    (htop : Tendsto (fun t : ℝ =>
      rhoFT (fun x => ((poitouKernel σ x : ℝ) : ℂ)) t * gammaFT F t) atTop (nhds 0))
    (hbot : Tendsto (fun t : ℝ =>
      rhoFT (fun x => ((poitouKernel σ x : ℝ) : ℂ)) t * gammaFT F t) atBot (nhds 0)) :
    Tendsto (fun T : ℝ => ∫ t in (-T)..T,
        (((2 * ((Complex.digamma ((σ:ℂ) + (t:ℂ)*Complex.I)
            - Complex.digamma (σ:ℂ)).re) : ℝ)) : ℂ)
          * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)))
      atTop (nhds (((4*π : ℝ) : ℂ) * ∫ y in Set.Ioi (0:ℝ),
        ((Real.exp (-(σ*y)) / (1 - Real.exp (-y)) : ℝ) : ℂ) * (F 0 - F y))) := by
  have h0 := tendsto_integral_rhoFT_mul_phi_eq_plancherel
    (integrable_poitouKernel hσ) (memLp_two_poitouKernel hσ) hF hFdiv hFdiv2 htop hbot
  -- rewrite the integrand via the ρ-fold identity
  have hfun : (fun T : ℝ => ∫ t in (-T)..T,
      rhoFT (fun x => ((poitouKernel σ x : ℝ) : ℂ)) t
        * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)))
      = fun T : ℝ => ∫ t in (-T)..T,
        (((2 * ((Complex.digamma ((σ:ℂ) + (t:ℂ)*Complex.I)
            - Complex.digamma (σ:ℂ)).re) : ℝ)) : ℂ)
          * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)) := by
    funext T
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [rhoFT_poitouKernel hσ t]
  rw [hfun] at h0
  -- rewrite the limit via the even fold
  have hval : -(((2*π : ℝ) : ℂ)
      * ∫ x : ℝ, ((poitouKernel σ (-x) : ℝ) : ℂ) * ((F 0 - F x)/(x:ℂ)))
      = ((4*π : ℝ) : ℂ) * ∫ y in Set.Ioi (0:ℝ),
        ((Real.exp (-(σ*y)) / (1 - Real.exp (-y)) : ℝ) : ℂ) * (F 0 - F y) := by
    rw [integral_poitouKernel_neg_mul hσ hFeven hFdiv2]
    push_cast
    ring
  rw [hval] at h0
  exact h0

/-- `logDeriv` of a natural power. -/
theorem logDeriv_pow' {f : ℂ → ℂ} {x : ℂ} (n : ℕ) (hf : f x ≠ 0)
    (hd : DifferentiableAt ℂ f x) :
    logDeriv (fun y => f y ^ n) x = n * logDeriv f x := by
  induction n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    exact congrFun (logDeriv_const 1) x
  | succ n ih =>
    have h0 : (fun y => f y ^ (n+1)) = fun y => (f y ^ n) * f y := by
      funext y
      rw [pow_succ]
    rw [h0, logDeriv_mul (f := fun y => f y ^ n) (g := f) x (pow_ne_zero n hf) hf
      (hd.pow n) hd, ih]
    push_cast
    ring

/-- `Complex.Gamma` is differentiable at every `s` in the right half-plane: on `0 < s.re`
the nonvanishing side-condition `∀ m, s ≠ -m` of `Complex.differentiableAt_Gamma` is
automatic. -/
theorem differentiableAt_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gamma s := by
  refine Complex.differentiableAt_Gamma _ (fun m => ?_)
  intro heq
  have := congrArg Complex.re heq
  simp only [Complex.neg_re, Complex.natCast_re] at this
  rw [this] at hs
  have h2 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  linarith

/-- **`d log Γℝ`** (Γψ-b, Poitou p. 6-03): `(Γℝ'/Γℝ)(s) = -½ log π + ½ ψ(s/2)`. -/
theorem logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s
      = -(1/2) * Complex.log π + (1/2) * Complex.digamma (s/2) := by
  have hs2 : 0 < (s/2).re := by
    have h0 : (s/2 : ℂ).re = s.re / 2 := by
      simp
    rw [h0]
    linarith
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hfun : Complex.Gammaℝ = fun s : ℂ => (π:ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) :=
    funext Complex.Gammaℝ_def
  rw [hfun]
  -- split the product
  have hpow_ne : (π:ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl hπ
  have hΓ_ne : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs2
  have hd1 : DifferentiableAt ℂ (fun w : ℂ => (π:ℂ) ^ (-w / 2)) s := by
    have h0 : HasDerivAt (fun w : ℂ => -w / 2) (-(1/2)) s := by
      have h1 : HasDerivAt (fun w : ℂ => w) 1 s := hasDerivAt_id s
      have h2 := (h1.neg).div_const 2
      have h3 : -(1:ℂ)/2 = -(1/2) := by ring
      rw [h3] at h2
      exact h2
    exact ((h0.const_cpow (Or.inl hπ)).differentiableAt)
  have hd2 : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2)) s :=
    (differentiableAt_Gamma_of_re_pos hs2).comp s (differentiableAt_id.div_const 2)
  rw [logDeriv_mul s hpow_ne hΓ_ne hd1 hd2]
  -- the power part
  have hlog1 : logDeriv (fun w : ℂ => (π:ℂ) ^ (-w / 2)) s = -(1/2) * Complex.log π := by
    rw [logDeriv_apply]
    have h0 : HasDerivAt (fun w : ℂ => -w / 2) (-(1/2)) s := by
      have h1 := (hasDerivAt_id s).neg.div_const (2:ℂ)
      have h3 : -(1:ℂ)/2 = -(1/2) := by ring
      rw [h3] at h1
      exact h1
    have h1 := h0.const_cpow (c := (π:ℂ)) (Or.inl hπ)
    rw [h1.deriv]
    field_simp
  -- the Gamma part via the chain rule
  have hlog2 : logDeriv (fun w : ℂ => Complex.Gamma (w / 2)) s
      = (1/2) * Complex.digamma (s/2) := by
    have h0 : (fun w : ℂ => Complex.Gamma (w / 2))
        = Complex.Gamma ∘ (fun w : ℂ => w / 2) := rfl
    rw [h0, logDeriv_comp ?_ ?_]
    · rw [show deriv (fun w : ℂ => w / 2) s = 1/2 from by
        rw [deriv_div_const, deriv_id'']
      ]
      rw [Complex.digamma_def]
      ring
    · exact differentiableAt_Gamma_of_re_pos hs2
    · exact differentiableAt_id.div_const 2
  rw [hlog1, hlog2]

/-- Differentiability of `Γℝ` on the right half-plane. -/
theorem differentiableAt_Gammaℝ_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  have hs2 : 0 < (s/2).re := by
    have h0 : (s/2 : ℂ).re = s.re / 2 := by simp
    rw [h0]
    linarith
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hfun : Complex.Gammaℝ = fun s : ℂ => (π:ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) :=
    funext Complex.Gammaℝ_def
  rw [hfun]
  refine DifferentiableAt.mul ?_ ?_
  · have h0 : HasDerivAt (fun w : ℂ => -w / 2) (-(1/2)) s := by
      have h1 := (hasDerivAt_id s).neg.div_const (2:ℂ)
      have h3 : -(1:ℂ)/2 = -(1/2) := by ring
      rw [h3] at h1
      exact h1
    exact (h0.const_cpow (Or.inl hπ)).differentiableAt
  · exact (differentiableAt_Gamma_of_re_pos hs2).comp s (differentiableAt_id.div_const 2)

/-- `Γℂ` is nonvanishing on the right half-plane. -/
theorem Gammaℂ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    Complex.Gammaℂ s ≠ 0 := by
  have hbase : (2 * (π : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [Complex.Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos hs)
  rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
  exact Or.inl hbase

/-- Differentiability of `Γℂ` on the right half-plane. -/
theorem differentiableAt_Gammaℂ_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gammaℂ s := by
  have hbase : (2 * (π : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hfun : Complex.Gammaℂ
      = fun s : ℂ => 2 * (2 * (π:ℂ)) ^ (-s) * Complex.Gamma s :=
    funext Complex.Gammaℂ_def
  rw [hfun]
  refine DifferentiableAt.mul (DifferentiableAt.const_mul ?_ 2) ?_
  · exact ((hasDerivAt_id s).neg.const_cpow (Or.inl hbase)).differentiableAt
  · exact differentiableAt_Gamma_of_re_pos hs

/-- **`d log Γℂ`** (Γψ-b): `(Γℂ'/Γℂ)(s) = -log(2π) + ψ(s)` on the right half-plane. -/
theorem logDeriv_Gammaℂ {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℂ s
      = -Complex.log (2*π) + Complex.digamma s := by
  have hbase : (2 * (π : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hfun : Complex.Gammaℂ
      = fun s : ℂ => 2 * (2 * (π:ℂ)) ^ (-s) * Complex.Gamma s :=
    funext Complex.Gammaℂ_def
  rw [hfun]
  have hpow_ne : (2 * (π:ℂ)) ^ (-s) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl hbase
  have hΓ_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have hd1 : DifferentiableAt ℂ (fun w : ℂ => 2 * (2 * (π:ℂ)) ^ (-w)) s :=
    DifferentiableAt.const_mul
      (((hasDerivAt_id s).neg.const_cpow (Or.inl hbase)).differentiableAt) 2
  have hdΓ : DifferentiableAt ℂ Complex.Gamma s := differentiableAt_Gamma_of_re_pos hs
  rw [logDeriv_mul (f := fun w : ℂ => 2 * (2 * (π:ℂ)) ^ (-w)) (g := Complex.Gamma) s
    (mul_ne_zero two_ne_zero hpow_ne) hΓ_ne hd1 hdΓ]
  have h1 : logDeriv (fun w : ℂ => 2 * (2 * (π:ℂ)) ^ (-w)) s = -Complex.log (2*π) := by
    rw [logDeriv_const_mul s 2 two_ne_zero]
    rw [logDeriv_apply]
    have h0 : HasDerivAt (fun w : ℂ => -w) (-1) s := (hasDerivAt_id s).neg
    have h1 := h0.const_cpow (c := 2 * (π:ℂ)) (Or.inl hbase)
    rw [h1.deriv]
    field_simp
  rw [h1, Complex.digamma_def]

/-- **`d log γ_K`** (Γψ-b, Poitou p. 6-03): on the right half-plane,
`(γ_K'/γ_K)(s) = r₁(-½ log π + ½ ψ(s/2)) + r₂(-log 2π + ψ(s))`. -/
theorem logDeriv_gammaFactor (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : 0 < s.re) :
    logDeriv (gammaFactor K) s
      = (NumberField.InfinitePlace.nrRealPlaces K)
          * (-(1/2) * Complex.log π + (1/2) * Complex.digamma (s/2))
        + (NumberField.InfinitePlace.nrComplexPlaces K)
          * (-Complex.log (2*π) + Complex.digamma s) := by
  have hfun : gammaFactor K = fun s : ℂ =>
      (Complex.Gammaℝ s) ^ NumberField.InfinitePlace.nrRealPlaces K
        * (Complex.Gammaℂ s) ^ NumberField.InfinitePlace.nrComplexPlaces K := rfl
  rw [hfun]
  rw [logDeriv_mul
    (f := fun s : ℂ => (Complex.Gammaℝ s) ^ NumberField.InfinitePlace.nrRealPlaces K)
    (g := fun s : ℂ => (Complex.Gammaℂ s) ^ NumberField.InfinitePlace.nrComplexPlaces K)
    s (pow_ne_zero _ (Complex.Gammaℝ_ne_zero_of_re_pos hs))
    (pow_ne_zero _ (Gammaℂ_ne_zero_of_re_pos hs))
    ((differentiableAt_Gammaℝ_of_re_pos hs).pow _)
    ((differentiableAt_Gammaℂ_of_re_pos hs).pow _)]
  rw [logDeriv_pow' _ (Complex.Gammaℝ_ne_zero_of_re_pos hs)
    (differentiableAt_Gammaℝ_of_re_pos hs)]
  rw [logDeriv_pow' _ (Gammaℂ_ne_zero_of_re_pos hs)
    (differentiableAt_Gammaℂ_of_re_pos hs)]
  rw [logDeriv_Gammaℝ hs, logDeriv_Gammaℂ hs]

/-- `logDeriv` of a `c^{s/2}`-prefactor: `(c^{s/2}·f)'/(c^{s/2}·f) = ½ log c + f'/f`. -/
theorem logDeriv_cpow_half_mul {c : ℂ} (hc : c ≠ 0) {f : ℂ → ℂ} {s : ℂ}
    (hf : f s ≠ 0) (hd : DifferentiableAt ℂ f s) :
    logDeriv (fun w : ℂ => c ^ (w/2) * f w) s
      = (1/2) * Complex.log c + logDeriv f s := by
  have hpow_ne : c ^ (s/2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl hc
  have h0 : HasDerivAt (fun w : ℂ => w / 2) (1/2) s := by
    have h1 := (hasDerivAt_id s).div_const (2:ℂ)
    have h3 : (1:ℂ)/2 = 1/2 := by norm_num
    rw [h3] at h1
    exact h1
  have hd1 : DifferentiableAt ℂ (fun w : ℂ => c ^ (w/2)) s :=
    (h0.const_cpow (Or.inl hc)).differentiableAt
  rw [logDeriv_mul (f := fun w : ℂ => c ^ (w/2)) (g := f) s hpow_ne hf hd1 hd]
  congr 1
  rw [logDeriv_apply, (h0.const_cpow (Or.inl hc)).deriv]
  field_simp

variable (K : Type*) [Field K] [NumberField K]

/-- **The Γ-side logarithmic derivative is `O(log|t|)` in the critical band**
(Γψ-a prerequisite; Poitou p. 6-03 "\|G'/G(s)\| est O(log|t|) dans une bande
verticale"): from the `d log γ_K` expansion and the digamma window bound A6. -/
theorem exists_norm_logDeriv_gammaFactor_le :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1/4 ≤ σ → σ ≤ 5/4 → 4 ≤ |t| →
      ‖logDeriv (gammaFactor K) ((σ:ℂ) + (t:ℂ) * Complex.I)‖
        ≤ C * Real.log (2 + |t|) := by
  obtain ⟨C₆, hC₆pos, hC₆⟩ := exists_norm_digamma_le
  set r₁ := NumberField.InfinitePlace.nrRealPlaces K
  set r₂ := NumberField.InfinitePlace.nrComplexPlaces K
  refine ⟨(r₁ : ℝ) * ((1/2) * ‖Complex.log (π:ℂ)‖ + (1/2) * C₆)
      + (r₂ : ℝ) * (‖Complex.log (2*(π:ℂ))‖ + C₆) + 1, by positivity,
    fun σ t hσl hσr ht => ?_⟩
  set s : ℂ := (σ:ℂ) + (t:ℂ) * Complex.I with hs
  have hsre : s.re = σ := by
    rw [hs]
    simp
  have hsim : s.im = t := by
    rw [hs]
    simp
  have hspos : 0 < s.re := by
    rw [hsre]
    linarith
  have hlog1 : (1:ℝ) ≤ Real.log (2 + |t|) := by
    rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    refine Real.log_le_log (Real.exp_pos 1) ?_
    have := Real.exp_one_lt_d9
    linarith
  rw [logDeriv_gammaFactor K hspos]
  -- half-point coordinates
  have hs2 : s/2 = ((σ/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * Complex.I := by
    rw [hs]
    push_cast
    ring
  have hψ2 : ‖Complex.digamma (s/2)‖ ≤ C₆ * Real.log (2 + |t|) := by
    rw [hs2]
    have h0 := hC₆ (σ/2) (t/2) (by linarith) (by linarith) (by
      rw [abs_div, abs_two]
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      linarith)
    refine le_trans h0 ?_
    refine mul_le_mul_of_nonneg_left ?_ hC₆pos.le
    refine Real.log_le_log (by positivity) ?_
    rw [abs_div, abs_two]
    nlinarith [abs_nonneg t]
  have hψ1 : ‖Complex.digamma s‖ ≤ C₆ * Real.log (2 + |t|) := by
    have h0 := hC₆ σ t (by linarith) (by linarith) (by linarith)
    rw [← hs] at h0
    exact h0
  -- assemble
  have htri : ‖(r₁ : ℂ) * (-(1/2) * Complex.log π + (1/2) * Complex.digamma (s/2))
      + (r₂ : ℂ) * (-Complex.log (2*π) + Complex.digamma s)‖
      ≤ (r₁ : ℝ) * ((1/2) * ‖Complex.log (π:ℂ)‖ + (1/2) * ‖Complex.digamma (s/2)‖)
        + (r₂ : ℝ) * (‖Complex.log (2*(π:ℂ))‖ + ‖Complex.digamma s‖) := by
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add ?_ ?_
    · rw [norm_mul, Complex.norm_natCast]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul, norm_neg]
      refine add_le_add (le_of_eq ?_) (le_of_eq ?_)
      · norm_num
      · norm_num
    · rw [norm_mul, Complex.norm_natCast]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_neg]
  refine le_trans htri ?_
  have h1 : (r₁ : ℝ) * ((1/2) * ‖Complex.log (π:ℂ)‖ + (1/2) * ‖Complex.digamma (s/2)‖)
      ≤ (r₁ : ℝ) * ((1/2) * ‖Complex.log (π:ℂ)‖ + (1/2) * C₆) * Real.log (2 + |t|) := by
    have h2 : (1/2 : ℝ) * ‖Complex.log (π:ℂ)‖ + (1/2) * ‖Complex.digamma (s/2)‖
        ≤ ((1/2) * ‖Complex.log (π:ℂ)‖ + (1/2) * C₆) * Real.log (2 + |t|) := by
      rw [add_mul]
      refine add_le_add ?_ ?_
      · nlinarith [norm_nonneg (Complex.log (π:ℂ))]
      · rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left hψ2 (by norm_num)
    calc (r₁ : ℝ) * ((1/2) * ‖Complex.log (π:ℂ)‖ + (1/2) * ‖Complex.digamma (s/2)‖)
        ≤ (r₁ : ℝ) * (((1/2) * ‖Complex.log (π:ℂ)‖ + (1/2) * C₆) * Real.log (2 + |t|)) :=
          mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
      _ = (r₁ : ℝ) * ((1/2) * ‖Complex.log (π:ℂ)‖ + (1/2) * C₆) * Real.log (2 + |t|) := by
          ring
  have h2 : (r₂ : ℝ) * (‖Complex.log (2*(π:ℂ))‖ + ‖Complex.digamma s‖)
      ≤ (r₂ : ℝ) * (‖Complex.log (2*(π:ℂ))‖ + C₆) * Real.log (2 + |t|) := by
    have h3 : ‖Complex.log (2*(π:ℂ))‖ + ‖Complex.digamma s‖
        ≤ (‖Complex.log (2*(π:ℂ))‖ + C₆) * Real.log (2 + |t|) := by
      rw [add_mul]
      refine add_le_add ?_ ?_
      · nlinarith [norm_nonneg (Complex.log (2*(π:ℂ)))]
      · exact hψ1
    calc (r₂ : ℝ) * (‖Complex.log (2*(π:ℂ))‖ + ‖Complex.digamma s‖)
        ≤ (r₂ : ℝ) * ((‖Complex.log (2*(π:ℂ))‖ + C₆) * Real.log (2 + |t|)) :=
          mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
      _ = (r₂ : ℝ) * (‖Complex.log (2*(π:ℂ))‖ + C₆) * Real.log (2 + |t|) := by ring
  have hfin := add_le_add h1 h2
  refine le_trans hfin ?_
  rw [show ((r₁ : ℝ) * ((1/2) * ‖Complex.log (π:ℂ)‖ + (1/2) * C₆)
      + (r₂ : ℝ) * (‖Complex.log (2*(π:ℂ))‖ + C₆) + 1) * Real.log (2 + |t|)
      = (r₁ : ℝ) * ((1/2) * ‖Complex.log (π:ℂ)‖ + (1/2) * C₆) * Real.log (2 + |t|)
        + (r₂ : ℝ) * (‖Complex.log (2*(π:ℂ))‖ + C₆) * Real.log (2 + |t|)
        + Real.log (2 + |t|) by ring]
  linarith

/-- `ψ(3/4) - ψ(1/4) = π`, derived from the Gauss-difference integral and the
`∫ 1/(2 cosh(x/2)) = π/2` evaluation (Poitou p. 6-04; no reflection formula needed). -/
theorem digamma_three_quarter_sub_quarter :
    Complex.digamma ((3/4 : ℝ) : ℂ) - Complex.digamma ((1/4 : ℝ) : ℂ) = ((π : ℝ) : ℂ) := by
  have hw : (0:ℝ) < (((3/4 : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]
    norm_num
  rw [digamma_sub_digamma_eq_integral (show (0:ℝ) < 1/4 by norm_num) hw]
  -- the integrand is a real cast
  have hcast : ∀ u ∈ Set.Ioi (0:ℝ),
      (Complex.exp (-((1/4 : ℝ):ℂ) * (u:ℂ)) - Complex.exp (-((3/4 : ℝ):ℂ) * (u:ℂ)))
          / (1 - Complex.exp (-(u:ℂ)))
        = (((Real.exp (-(u/4)) - Real.exp (-(3*u/4))) / (1 - Real.exp (-u)) : ℝ) : ℂ) := by
    intro u _
    rw [show (-((1/4 : ℝ):ℂ) * (u:ℂ)) = ((-(u/4) : ℝ) : ℂ) by push_cast; ring,
      show (-((3/4 : ℝ):ℂ) * (u:ℂ)) = ((-(3*u/4) : ℝ) : ℂ) by push_cast; ring,
      show (-(u:ℂ)) = ((-u : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
    push_cast
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcast, integral_complex_ofReal]
  congr 1
  -- substitute u = 2x and identify the cosh kernel
  set g : ℝ → ℝ := fun u => (Real.exp (-(u/4)) - Real.exp (-(3*u/4))) / (1 - Real.exp (-u))
    with hg
  have hsub := MeasureTheory.integral_comp_mul_left_Ioi g 0 (show (0:ℝ) < 2 by norm_num)
  rw [mul_zero] at hsub
  have hker : ∀ x ∈ Set.Ioi (0:ℝ), g (2*x) = 1/(2 * Real.cosh (x/2)) := by
    intro x hx
    rw [Set.mem_Ioi] at hx
    rw [hg]
    simp only
    set y : ℝ := Real.exp (-(x/2)) with hy
    have hy0 : 0 < y := Real.exp_pos _
    have hy1 : y < 1 := by
      rw [hy, show (1:ℝ) = Real.exp 0 by rw [Real.exp_zero]]
      exact Real.exp_lt_exp.mpr (by linarith)
    have he1 : Real.exp (-(2*x/4)) = y := by
      rw [hy]
      congr 1
      ring
    have he3 : Real.exp (-(3*(2*x)/4)) = y^3 := by
      rw [hy, show -(3*(2*x)/4) = (-(x/2)) + ((-(x/2)) + (-(x/2))) by ring,
        Real.exp_add, Real.exp_add]
      ring
    have he4 : Real.exp (-(2*x)) = y^4 := by
      rw [hy, show -(2*x) = (-(x/2)) + ((-(x/2)) + ((-(x/2)) + (-(x/2)))) by ring,
        Real.exp_add, Real.exp_add, Real.exp_add]
      ring
    have hcosh : Real.cosh (x/2) = (y⁻¹ + y)/2 := by
      rw [Real.cosh_eq, hy, ← Real.exp_neg, neg_neg]
    rw [show Real.exp (-(2*x/4)) = y from he1, he3, he4, hcosh]
    have hy4lt : y^4 < 1 := pow_lt_one₀ hy0.le hy1 (by norm_num)
    have hy4 : (1:ℝ) - y^4 ≠ 0 := (by linarith : (0:ℝ) < 1 - y^4).ne'
    have hyne : y ≠ 0 := hy0.ne'
    field_simp
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hker,
    integral_inv_two_cosh_half] at hsub
  have h2 : ∫ u in Set.Ioi (0:ℝ), g u = 2 * (π/2) := by
    have h3 := hsub.symm
    rw [smul_eq_mul] at h3
    linarith
  rw [h2]
  ring

/-- Log-derivative of the Legendre duplication formula at `s = 1/4`:
`ψ(1/4) + ψ(3/4) = 2 ψ(1/2) - 2 log 2`. -/
theorem digamma_quarter_add_three_quarter :
    Complex.digamma ((1/4 : ℝ) : ℂ) + Complex.digamma ((3/4 : ℝ) : ℂ)
      = 2 * Complex.digamma ((1/2 : ℝ) : ℂ) - 2 * Complex.log 2 := by
  have hdiff : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ Complex.Gamma z :=
    fun z hz => differentiableAt_Gamma_of_re_pos hz
  set s₀ : ℂ := ((1/4 : ℝ) : ℂ) with hs₀
  have hre₀ : s₀.re = 1/4 := Complex.ofReal_re _
  have hshift : s₀ + 1/2 = ((3/4 : ℝ) : ℂ) := by
    rw [hs₀]
    push_cast
    norm_num
  have hdouble : 2 * s₀ = ((1/2 : ℝ) : ℂ) := by
    rw [hs₀]
    push_cast
    norm_num
  -- logDeriv of both sides of the duplication identity
  have hfg : logDeriv (fun s : ℂ => Complex.Gamma s * Complex.Gamma (s + 1/2)) s₀
      = logDeriv (fun s : ℂ =>
          Complex.Gamma (2*s) * (2:ℂ) ^ (1 - 2*s) * (Real.sqrt π : ℂ)) s₀ := by
    congr 1
    funext s
    exact Complex.Gamma_mul_Gamma_add_half s
  -- LHS = ψ(1/4) + ψ(3/4)
  have hΓq : Complex.Gamma s₀ ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by rw [hre₀]; norm_num)
  have hΓ3q : Complex.Gamma (s₀ + 1/2) ≠ 0 := by
    rw [hshift]
    exact Complex.Gamma_ne_zero_of_re_pos (by rw [Complex.ofReal_re]; norm_num)
  have hd3q : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s + 1/2)) s₀ := by
    have h0 : (fun s : ℂ => Complex.Gamma (s + 1/2))
        = Complex.Gamma ∘ (fun s : ℂ => s + 1/2) := rfl
    rw [h0]
    refine DifferentiableAt.comp s₀ ?_ (differentiableAt_id.add_const _)
    rw [hshift]
    exact hdiff _ (by rw [Complex.ofReal_re]; norm_num)
  have hLHS : logDeriv (fun s : ℂ => Complex.Gamma s * Complex.Gamma (s + 1/2)) s₀
      = Complex.digamma ((1/4 : ℝ) : ℂ) + Complex.digamma ((3/4 : ℝ) : ℂ) := by
    rw [logDeriv_mul s₀ hΓq hΓ3q (hdiff s₀ (by rw [hre₀]; norm_num)) hd3q]
    congr 1
    have h0 : (fun s : ℂ => Complex.Gamma (s + 1/2))
        = Complex.Gamma ∘ (fun s : ℂ => s + 1/2) := rfl
    rw [h0, logDeriv_comp ?_ ?_]
    · rw [show deriv (fun s : ℂ => s + 1/2) s₀ = 1 from by
        rw [deriv_add_const, deriv_id'']]
      rw [hshift, Complex.digamma_def]
      ring
    · rw [hshift]
      exact hdiff _ (by rw [Complex.ofReal_re]; norm_num)
    · exact differentiableAt_id.add_const _
  -- RHS = 2 ψ(1/2) - 2 log 2
  have hΓh : Complex.Gamma (2 * s₀) ≠ 0 := by
    rw [hdouble]
    exact Complex.Gamma_ne_zero_of_re_pos (by rw [Complex.ofReal_re]; norm_num)
  have hpow_ne : (2:ℂ) ^ (1 - 2*s₀) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl two_ne_zero
  have hderiv_lin : HasDerivAt (fun s : ℂ => 1 - 2*s) (-2) s₀ := by
    have h1 := ((hasDerivAt_id s₀).const_mul (2:ℂ)).const_sub (1:ℂ)
    have h2 : -((2:ℂ) * 1) = -2 := by ring
    rw [h2] at h1
    exact h1
  have hdpow : HasDerivAt (fun s : ℂ => (2:ℂ) ^ (1 - 2*s))
      ((2:ℂ) ^ (1 - 2*s₀) * Complex.log 2 * (-2)) s₀ :=
    hderiv_lin.const_cpow (Or.inl two_ne_zero)
  have hdΓ2 : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (2*s)) s₀ := by
    have h0 : (fun s : ℂ => Complex.Gamma (2*s))
        = Complex.Gamma ∘ (fun s : ℂ => 2*s) := rfl
    rw [h0]
    refine DifferentiableAt.comp s₀ ?_ (differentiableAt_id.const_mul _)
    rw [hdouble]
    exact hdiff _ (by rw [Complex.ofReal_re]; norm_num)
  have hRHS : logDeriv (fun s : ℂ =>
        Complex.Gamma (2*s) * (2:ℂ) ^ (1 - 2*s) * (Real.sqrt π : ℂ)) s₀
      = 2 * Complex.digamma ((1/2 : ℝ) : ℂ) - 2 * Complex.log 2 := by
    have hprod_ne : Complex.Gamma (2*s₀) * (2:ℂ) ^ (1 - 2*s₀) ≠ 0 :=
      mul_ne_zero hΓh hpow_ne
    have hsqrt_ne : ((Real.sqrt π : ℝ) : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]
      exact (Real.sqrt_pos.mpr Real.pi_pos).ne'
    rw [logDeriv_mul (f := fun s : ℂ => Complex.Gamma (2*s) * (2:ℂ) ^ (1 - 2*s))
        (g := fun _ : ℂ => ((Real.sqrt π : ℝ) : ℂ)) s₀ hprod_ne hsqrt_ne
        (hdΓ2.mul hdpow.differentiableAt) (differentiableAt_const _),
      logDeriv_mul (f := fun s : ℂ => Complex.Gamma (2*s))
        (g := fun s : ℂ => (2:ℂ) ^ (1 - 2*s)) s₀ hΓh hpow_ne hdΓ2
        hdpow.differentiableAt]
    have hconst : logDeriv (fun _ : ℂ => ((Real.sqrt π : ℝ) : ℂ)) s₀ = 0 :=
      congrFun (logDeriv_const _) s₀
    have hgamma2 : logDeriv (fun s : ℂ => Complex.Gamma (2*s)) s₀
        = 2 * Complex.digamma ((1/2 : ℝ) : ℂ) := by
      have h0 : (fun s : ℂ => Complex.Gamma (2*s))
          = Complex.Gamma ∘ (fun s : ℂ => 2*s) := rfl
      rw [h0, logDeriv_comp ?_ ?_]
      · rw [show deriv (fun s : ℂ => 2*s) s₀ = 2 from by
          rw [deriv_const_mul_field, deriv_id'']
          ring]
        rw [hdouble, Complex.digamma_def]
        ring
      · rw [hdouble]
        exact hdiff _ (by rw [Complex.ofReal_re]; norm_num)
      · exact differentiableAt_id.const_mul _
    have hcpow : logDeriv (fun s : ℂ => (2:ℂ) ^ (1 - 2*s)) s₀
        = Complex.log 2 * (-2) := by
      rw [logDeriv_apply, hdpow.deriv]
      field_simp
    rw [hconst, hgamma2, hcpow]
    ring
  rw [hLHS, hRHS] at hfg
  exact hfg

/-- **`ψ(1/2) - ψ(1/4) = π/2 + log 2`** (Poitou p. 6-04, the value
`∫₀^∞ dx/(2 ch(x/2)) = -ψ(1/4) + ψ(1/2) - log 2 = π/2` rearranged). -/
theorem digamma_half_sub_quarter :
    Complex.digamma ((1/2 : ℝ) : ℂ) - Complex.digamma ((1/4 : ℝ) : ℂ)
      = ((π/2 + Real.log 2 : ℝ) : ℂ) := by
  have h1 := digamma_three_quarter_sub_quarter
  have h2 := digamma_quarter_add_three_quarter
  have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [hlog] at h2
  push_cast at h1 h2 ⊢
  linear_combination h1/2 - h2/2

/-- Pushforward of Lebesgue measure under `x ↦ x/2` is `2 • volume`. -/
theorem map_volume_half_mul :
    Measure.map (fun x : ℝ => (2:ℝ)⁻¹ * x) (volume : Measure ℝ)
      = (2 : ℝ≥0∞) • (volume : Measure ℝ) := by
  rw [Real.map_volume_mul_left (by norm_num : ((2:ℝ)⁻¹) ≠ 0)]
  rw [show |((2:ℝ)⁻¹)⁻¹| = (2:ℝ) by norm_num]
  rw [show ((2:ℝ) : ℝ) = ((2:ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
  norm_num

/-- Integrability of the half-scaled test function `x ↦ F(x/2)/2`. -/
theorem integrable_halfScale {F : ℝ → ℂ} (hF : Integrable F) :
    Integrable (fun x : ℝ => F (x/2) / 2) := by
  have h0 : Integrable (fun x : ℝ => F ((2:ℝ)⁻¹ * x)) :=
    (MeasureTheory.integrable_comp_mul_left_iff F (by norm_num : ((2:ℝ)⁻¹) ≠ 0)).mpr hF
  refine (h0.div_const 2).congr (Filter.Eventually.of_forall (fun x => ?_))
  show F ((2:ℝ)⁻¹ * x) / 2 = F (x/2) / 2
  rw [show (2:ℝ)⁻¹ * x = x/2 by ring]

/-- The near-zero local integrability hypothesis transfers to the half-scaled
test function. -/
theorem integrableOn_halfScale_div {F : ℝ → ℂ}
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1)) :
    IntegrableOn (fun x : ℝ => (F 0/2 - F (x/2)/2)/(x:ℂ)) (Set.Ioc (-1) 1) := by
  set q : ℝ → ℂ := fun w => (F 0 - F w)/(w:ℂ) with hq
  have h1 : IntegrableOn q (Set.Ioc (-(1/2)) (1/2)) :=
    hFdiv.mono_set (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have he : MeasurableEmbedding (fun x : ℝ => (2:ℝ)⁻¹ * x) :=
    (Homeomorph.mulLeft₀ ((2:ℝ)⁻¹) (by norm_num)).isClosedEmbedding.measurableEmbedding
  have hpre : (fun x : ℝ => (2:ℝ)⁻¹ * x) ⁻¹' (Set.Ioc (-(1/2)) (1/2)) = Set.Ioc (-1) 1 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor
    · rintro ⟨ha, hb⟩
      constructor <;> linarith
    · rintro ⟨ha, hb⟩
      constructor <;> linarith
  have hrestr : Measure.map (fun x : ℝ => (2:ℝ)⁻¹ * x)
        ((volume : Measure ℝ).restrict (Set.Ioc (-1) 1))
      = ((2 : ℝ≥0∞) • (volume : Measure ℝ)).restrict (Set.Ioc (-(1/2)) (1/2)) := by
    rw [← hpre, ← Measure.restrict_map he.measurable measurableSet_Ioc, map_volume_half_mul]
  have h2 : Integrable (fun x : ℝ => q ((2:ℝ)⁻¹ * x))
      ((volume : Measure ℝ).restrict (Set.Ioc (-1) 1)) := by
    have h3 : Integrable q (Measure.map (fun x : ℝ => (2:ℝ)⁻¹ * x)
        ((volume : Measure ℝ).restrict (Set.Ioc (-1) 1))) := by
      rw [hrestr, Measure.restrict_smul]
      exact (integrable_smul_measure (by norm_num) (by norm_num)).mpr h1
    exact he.integrable_map_iff.mp h3
  refine (h2.const_mul ((1/4 : ℂ))).congr (Filter.Eventually.of_forall (fun x => ?_))
  show (1/4 : ℂ) * q ((2:ℝ)⁻¹ * x) = (F 0/2 - F (x/2)/2)/(x:ℂ)
  rw [show (2:ℝ)⁻¹ * x = x/2 by ring]
  show (1/4 : ℂ) * ((F 0 - F (x/2))/((x/2 : ℝ):ℂ)) = (F 0/2 - F (x/2)/2)/(x:ℂ)
  rw [show ((x/2 : ℝ) : ℂ) = (x:ℂ)/2 by push_cast; ring]
  rw [div_div_eq_mul_div]
  rw [show (F 0/2 - F (x/2)/2) = (F 0 - F (x/2))/2 by ring]
  rw [mul_div_assoc']
  congr 1
  ring

/-- The global square-integrability hypothesis transfers to the half-scaled
test function. -/
theorem memLp_two_halfScale_div {F : ℝ → ℂ}
    (hFdiv2 : MemLp (fun x : ℝ => (F 0 - F x)/(x:ℂ)) 2 (volume : Measure ℝ)) :
    MemLp (fun x : ℝ => (F 0/2 - F (x/2)/2)/(x:ℂ)) 2 (volume : Measure ℝ) := by
  set q : ℝ → ℂ := fun w => (F 0 - F w)/(w:ℂ) with hq
  have he : Measurable (fun x : ℝ => (2:ℝ)⁻¹ * x) := measurable_id.const_mul _
  have hq2 : MemLp q 2 ((2 : ℝ≥0∞) • (volume : Measure ℝ)) :=
    hFdiv2.smul_measure (by norm_num)
  rw [← map_volume_half_mul] at hq2
  have h3 : MemLp (q ∘ (fun x : ℝ => (2:ℝ)⁻¹ * x)) 2 (volume : Measure ℝ) :=
    (memLp_map_measure_iff hq2.aestronglyMeasurable he.aemeasurable).mp hq2
  refine (memLp_congr_ae (Filter.Eventually.of_forall (fun x => ?_))).mp
    (h3.const_mul ((1/4 : ℂ)))
  show (1/4 : ℂ) * q ((2:ℝ)⁻¹ * x) = (F 0/2 - F (x/2)/2)/(x:ℂ)
  rw [show (2:ℝ)⁻¹ * x = x/2 by ring]
  show (1/4 : ℂ) * ((F 0 - F (x/2))/((x/2 : ℝ):ℂ)) = (F 0/2 - F (x/2)/2)/(x:ℂ)
  rw [show ((x/2 : ℝ) : ℂ) = (x:ℂ)/2 by push_cast; ring]
  rw [div_div_eq_mul_div]
  rw [show (F 0/2 - F (x/2)/2) = (F 0 - F (x/2))/2 by ring]
  rw [mul_div_assoc']
  congr 1
  ring

/-- **Proposition 3 at the quarter point with half-scaled frequency** (the
`Re ψ(1/4 + it/2)` term of Poitou p. 6-03/6-04): for `F` integrable, even, with
the local and global divided-difference hypotheses and the boundary decay for the
half-scaled data,

`lim_{T→∞} ∫_{-T}^T 2(Re ψ(1/4 + it/2) - ψ(1/4))·φ(t) dt
   = 8π ∫₀^∞ e^{-x/2}(F(0) - F(x))/(1 - e^{-2x}) dx`. -/
theorem prop3_poitou_quarter {F : ℝ → ℂ} (hF : Integrable F)
    (hFeven : ∀ x : ℝ, F (-x) = F x)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    (hFdiv2 : MemLp (fun x : ℝ => (F 0 - F x)/(x:ℂ)) 2 (volume : Measure ℝ))
    (htop : Tendsto (fun t : ℝ =>
      rhoFT (fun x => ((poitouKernel (1/4) x : ℝ) : ℂ)) t
        * gammaFT (fun x : ℝ => F (x/2) / 2) t) atTop (nhds 0))
    (hbot : Tendsto (fun t : ℝ =>
      rhoFT (fun x => ((poitouKernel (1/4) x : ℝ) : ℂ)) t
        * gammaFT (fun x : ℝ => F (x/2) / 2) t) atBot (nhds 0)) :
    Tendsto (fun T : ℝ => ∫ t in (-T)..T,
        (((2 * ((Complex.digamma (((1/4 : ℝ):ℂ) + ((t/2 : ℝ):ℂ)*Complex.I)
            - Complex.digamma ((1/4 : ℝ):ℂ)).re) : ℝ)) : ℂ)
          * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)))
      atTop (nhds (((8*π : ℝ) : ℂ) * ∫ y in Set.Ioi (0:ℝ),
        ((Real.exp (-(y/2)) / (1 - Real.exp (-(2*y))) : ℝ) : ℂ) * (F 0 - F y))) := by
  set Fh : ℝ → ℂ := fun x => F (x/2) / 2 with hFh_def
  have hFh0 : Fh 0 = F 0 / 2 := by
    show F (0/2) / 2 = F 0 / 2
    norm_num
  -- transferred hypotheses
  have hFh : Integrable Fh := integrable_halfScale hF
  have hFh_even : ∀ x : ℝ, Fh (-x) = Fh x := by
    intro x
    show F ((-x)/2) / 2 = F (x/2) / 2
    rw [show (-x)/2 = -(x/2) by ring, hFeven]
  have hFhx : ∀ x : ℝ, Fh x = F (x/2) / 2 := fun _ => rfl
  have hFhdiv : IntegrableOn (fun x : ℝ => (Fh 0 - Fh x)/(x:ℂ)) (Set.Ioc (-1) 1) := by
    refine (integrableOn_halfScale_div hFdiv).congr
      (Filter.Eventually.of_forall (fun x => ?_))
    show (F 0/2 - F (x/2)/2)/(x:ℂ) = (Fh 0 - Fh x)/(x:ℂ)
    rw [hFh0, hFhx]
  have hFhdiv2 : MemLp (fun x : ℝ => (Fh 0 - Fh x)/(x:ℂ)) 2 (volume : Measure ℝ) := by
    refine (memLp_congr_ae (Filter.Eventually.of_forall (fun x => ?_))).mp
      (memLp_two_halfScale_div hFdiv2)
    show (F 0/2 - F (x/2)/2)/(x:ℂ) = (Fh 0 - Fh x)/(x:ℂ)
    rw [hFh0, hFhx]
  have h0 := prop3_poitou (show (0:ℝ) < 1/4 by norm_num) hFh hFh_even hFhdiv hFhdiv2
    htop hbot
  -- the Fourier transform of the half-scaled function is φ(2u)
  have hFour : ∀ u : ℝ, (∫ x : ℝ, Fh x * Complex.exp ((u*x : ℝ) * Complex.I))
      = ∫ x : ℝ, F x * Complex.exp (((2*u)*x : ℝ) * Complex.I) := by
    intro u
    set g : ℝ → ℂ := fun w => F w * Complex.exp (((2*u)*w : ℝ) * Complex.I) with hg
    have h1 : (∫ x : ℝ, g ((2:ℝ)⁻¹ * x)) = |(((2:ℝ)⁻¹))⁻¹| • ∫ x : ℝ, g x :=
      MeasureTheory.Measure.integral_comp_mul_left g ((2:ℝ)⁻¹)
    have h2 : (fun x : ℝ => Fh x * Complex.exp ((u*x : ℝ) * Complex.I))
        = fun x : ℝ => (1/2 : ℂ) * g ((2:ℝ)⁻¹ * x) := by
      funext x
      show F (x/2) / 2 * Complex.exp ((u*x : ℝ) * Complex.I)
          = (1/2 : ℂ) * g ((2:ℝ)⁻¹ * x)
      rw [show (2:ℝ)⁻¹ * x = x/2 by ring]
      show F (x/2) / 2 * Complex.exp ((u*x : ℝ) * Complex.I)
          = (1/2 : ℂ) * (F (x/2) * Complex.exp (((2*u)*(x/2) : ℝ) * Complex.I))
      rw [show ((2*u)*(x/2) : ℝ) = (u*x : ℝ) by ring]
      ring
    rw [h2, MeasureTheory.integral_const_mul, h1,
      show |(((2:ℝ)⁻¹))⁻¹| = (2:ℝ) by norm_num, Complex.real_smul]
    push_cast
    ring
  -- fixed-T change of variables t = 2u
  have hint : ∀ T : ℝ, (∫ t in (-T)..T,
      (((2 * ((Complex.digamma (((1/4 : ℝ):ℂ) + ((t/2 : ℝ):ℂ)*Complex.I)
          - Complex.digamma ((1/4 : ℝ):ℂ)).re) : ℝ)) : ℂ)
        * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)))
      = 2 * ∫ u in (-(T/2))..(T/2),
          (((2 * ((Complex.digamma (((1/4 : ℝ):ℂ) + (u:ℂ)*Complex.I)
              - Complex.digamma ((1/4 : ℝ):ℂ)).re) : ℝ)) : ℂ)
            * (∫ x : ℝ, Fh x * Complex.exp ((u*x : ℝ) * Complex.I)) := by
    intro T
    have h1 := intervalIntegral.integral_comp_mul_left
      (f := fun t : ℝ =>
        (((2 * ((Complex.digamma (((1/4 : ℝ):ℂ) + ((t/2 : ℝ):ℂ)*Complex.I)
            - Complex.digamma ((1/4 : ℝ):ℂ)).re) : ℝ)) : ℂ)
          * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)))
      (a := -(T/2)) (b := T/2) (show (2:ℝ) ≠ 0 by norm_num)
    rw [show (2:ℝ) * -(T/2) = -T by ring, show (2:ℝ) * (T/2) = T by ring] at h1
    have h2 : (∫ t in (-T)..T,
        (((2 * ((Complex.digamma (((1/4 : ℝ):ℂ) + ((t/2 : ℝ):ℂ)*Complex.I)
            - Complex.digamma ((1/4 : ℝ):ℂ)).re) : ℝ)) : ℂ)
          * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)))
        = (2:ℝ) • ∫ u in (-(T/2))..(T/2),
            (((2 * ((Complex.digamma (((1/4 : ℝ):ℂ) + (((2*u)/2 : ℝ):ℂ)*Complex.I)
                - Complex.digamma ((1/4 : ℝ):ℂ)).re) : ℝ)) : ℂ)
              * (∫ x : ℝ, F x * Complex.exp (((2*u)*x : ℝ) * Complex.I)) := by
      rw [h1, smul_smul]
      norm_num
    rw [h2, Complex.real_smul, Complex.ofReal_ofNat]
    congr 1
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    rw [show (((2*u)/2 : ℝ) : ℂ) = (u:ℂ) from Complex.ofReal_inj.mpr (by ring)]
    rw [hFour u]
  -- the limit value under the y = 2x substitution
  have hlim : (2:ℂ) * ((((4*π : ℝ)) : ℂ) * ∫ y in Set.Ioi (0:ℝ),
      ((Real.exp (-(1/4*y)) / (1 - Real.exp (-y)) : ℝ) : ℂ) * (Fh 0 - Fh y))
      = ((8*π : ℝ) : ℂ) * ∫ y in Set.Ioi (0:ℝ),
        ((Real.exp (-(y/2)) / (1 - Real.exp (-(2*y))) : ℝ) : ℂ) * (F 0 - F y) := by
    set m : ℝ → ℂ := fun y =>
      ((Real.exp (-(1/4*y)) / (1 - Real.exp (-y)) : ℝ) : ℂ) * (Fh 0 - Fh y) with hm
    have h1 := MeasureTheory.integral_comp_mul_left_Ioi m 0
      (show (0:ℝ) < 2 by norm_num)
    rw [mul_zero] at h1
    have h2 : ∀ x ∈ Set.Ioi (0:ℝ), m (2*x)
        = ((Real.exp (-(x/2)) / (1 - Real.exp (-(2*x))) : ℝ) : ℂ)
            * ((F 0 - F x)/2) := by
      intro x _
      show ((Real.exp (-(1/4*(2*x))) / (1 - Real.exp (-(2*x))) : ℝ) : ℂ)
          * (Fh 0 - Fh (2*x))
        = ((Real.exp (-(x/2)) / (1 - Real.exp (-(2*x))) : ℝ) : ℂ) * ((F 0 - F x)/2)
      rw [hFh0, show Fh (2*x) = F x / 2 from by
        show F ((2*x)/2) / 2 = F x / 2
        rw [show (2*x)/2 = x by ring]]
      rw [show -(1/4*(2*x)) = -(x/2) by ring]
      push_cast
      ring
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h2] at h1
    -- h1 : ∫ (kernel'·(F0−Fx)/2) = 2⁻¹ • ∫ m
    have h3 : (∫ y in Set.Ioi (0:ℝ), m y)
        = 2 * ∫ x in Set.Ioi (0:ℝ),
            ((Real.exp (-(x/2)) / (1 - Real.exp (-(2*x))) : ℝ) : ℂ)
              * ((F 0 - F x)/2) := by
      rw [h1, Complex.real_smul]
      push_cast
      ring
    rw [h3]
    rw [show (∫ x in Set.Ioi (0:ℝ),
        ((Real.exp (-(x/2)) / (1 - Real.exp (-(2*x))) : ℝ) : ℂ) * ((F 0 - F x)/2))
        = (1/2 : ℂ) * ∫ x in Set.Ioi (0:ℝ),
          ((Real.exp (-(x/2)) / (1 - Real.exp (-(2*x))) : ℝ) : ℂ) * (F 0 - F x) from by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
      ring]
    push_cast
    ring
  -- assemble
  refine Tendsto.congr (fun T => (hint T).symm) ?_
  have hhalf : Tendsto (fun T : ℝ => T/2) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨2*b, fun a ha => by linarith⟩)
  have h9 := (h0.comp hhalf).const_mul (2:ℂ)
  rw [hlim] at h9
  exact h9
/-- The sinh limit kernel `(F(0) - F(x))/(2 sinh(x/2))` is integrable on `(0,∞)`:
it is the product of the square-integrable Poitou kernel at `σ = 1/2` and the
square-integrable divided difference. -/
theorem integrableOn_sinh_kernel_mul {F : ℝ → ℂ}
    (hFdiv2 : MemLp (fun x : ℝ => (F 0 - F x)/(x:ℂ)) 2 (volume : Measure ℝ)) :
    IntegrableOn (fun y : ℝ => ((1/(2 * Real.sinh (y/2)) : ℝ) : ℂ) * (F 0 - F y))
      (Set.Ioi (0:ℝ)) := by
  have h1 : MemLp (fun y : ℝ => ((poitouKernel (1/2) y : ℝ) : ℂ)) 2
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
    (memLp_two_poitouKernel (by norm_num : (0:ℝ) < 1/2)).restrict _
  have h2 : MemLp (fun x : ℝ => (F 0 - F x)/(x:ℂ)) 2
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) := hFdiv2.restrict _
  have h3 := MemLp.integrable_mul h1 h2
  refine h3.congr ?_
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
    (Filter.Eventually.of_forall (fun y hy => ?_))
  rw [Set.mem_Ioi] at hy
  show ((poitouKernel (1/2) y : ℝ) : ℂ) * ((F 0 - F y)/(y:ℂ))
      = ((1/(2 * Real.sinh (y/2)) : ℝ) : ℂ) * (F 0 - F y)
  rw [poitouKernel_of_pos hy, ← exp_half_div_one_sub_exp_neg hy]
  have hyne : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hden : (0:ℝ) < 1 - Real.exp (-y) := by
    have h := Real.exp_lt_exp.mpr (show -y < 0 by linarith)
    rw [Real.exp_zero] at h
    linarith
  have hdenC : ((1 - Real.exp (-y) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hden.ne'
  rw [show -((1/2:ℝ)*y) = -(y/2) by ring]
  push_cast at hdenC ⊢
  field_simp

/-- The cosh limit kernel `(F(0) - F(x))/(2 cosh(x/2))` is integrable on `(0,∞)`:
dominated by the sinh kernel. -/
theorem integrableOn_cosh_kernel_mul {F : ℝ → ℂ} (hF : Integrable F)
    (hFdiv2 : MemLp (fun x : ℝ => (F 0 - F x)/(x:ℂ)) 2 (volume : Measure ℝ)) :
    IntegrableOn (fun y : ℝ => ((1/(2 * Real.cosh (y/2)) : ℝ) : ℂ) * (F 0 - F y))
      (Set.Ioi (0:ℝ)) := by
  refine Integrable.mono' (integrableOn_sinh_kernel_mul hFdiv2).norm ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ ((aestronglyMeasurable_const.sub
      hF.aestronglyMeasurable).restrict)
    refine Continuous.aestronglyMeasurable ?_
    exact Complex.continuous_ofReal.comp
      (continuous_const.div ((continuous_const.mul
        ((Real.continuous_cosh).comp (continuous_id.div_const 2))))
        (fun y => by positivity))
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall (fun y hy => ?_))
    rw [Set.mem_Ioi] at hy
    show ‖((1/(2 * Real.cosh (y/2)) : ℝ) : ℂ) * (F 0 - F y)‖
        ≤ ‖((1/(2 * Real.sinh (y/2)) : ℝ) : ℂ) * (F 0 - F y)‖
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real]
    have hsh : 0 < Real.sinh (y/2) := Real.sinh_pos_iff.mpr (by linarith)
    have hch : Real.sinh (y/2) ≤ Real.cosh (y/2) := by
      have h0 : Real.cosh (y/2) - Real.sinh (y/2) = Real.exp (-(y/2)) := by
        rw [Real.cosh_eq, Real.sinh_eq]
        ring
      have h1 := Real.exp_pos (-(y/2))
      linarith
    have h1 : |(1/(2 * Real.cosh (y/2)) : ℝ)| ≤ |(1/(2 * Real.sinh (y/2)) : ℝ)| := by
      rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
      gcongr
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)


/-- Kernel conversion for the `σ = 1/2` Proposition-3 limit: the Gauss kernel is
the sinh kernel. -/
theorem integral_gauss_half_eq_sinh {F : ℝ → ℂ} :
    (∫ y in Set.Ioi (0:ℝ),
        ((Real.exp (-(1/2*y)) / (1 - Real.exp (-y)) : ℝ) : ℂ) * (F 0 - F y))
      = ∫ y in Set.Ioi (0:ℝ),
          ((1/(2 * Real.sinh (y/2)) : ℝ) : ℂ) * (F 0 - F y) := by
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
  rw [Set.mem_Ioi] at hy
  rw [show -(1/2*y) = -(y/2) by ring,
    exp_half_div_one_sub_exp_neg hy]

/-- Kernel conversion for the quarter-point limit: the `e^{-y/2}/(1-e^{-2y})`
kernel is the average of the sinh and cosh kernels, so its integral splits. -/
theorem integral_gauss_quarter_eq_sinh_add_cosh {F : ℝ → ℂ} (hF : Integrable F)
    (hFdiv2 : MemLp (fun x : ℝ => (F 0 - F x)/(x:ℂ)) 2 (volume : Measure ℝ)) :
    (∫ y in Set.Ioi (0:ℝ),
        ((Real.exp (-(y/2)) / (1 - Real.exp (-(2*y))) : ℝ) : ℂ) * (F 0 - F y))
      = (1/2 : ℂ) * ((∫ y in Set.Ioi (0:ℝ),
            ((1/(2 * Real.sinh (y/2)) : ℝ) : ℂ) * (F 0 - F y))
          + ∫ y in Set.Ioi (0:ℝ),
            ((1/(2 * Real.cosh (y/2)) : ℝ) : ℂ) * (F 0 - F y)) := by
  rw [← MeasureTheory.integral_add (integrableOn_sinh_kernel_mul hFdiv2)
    (integrableOn_cosh_kernel_mul hF hFdiv2)]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
  rw [Set.mem_Ioi] at hy
  -- pointwise: e^{-y/2}/(1-e^{-2y}) = (1/2)(1/(2sh(y/2)) + 1/(2ch(y/2)))
  have hexp : 0 < Real.exp (-y) := Real.exp_pos _
  have hlt : Real.exp (-y) < 1 := by
    rw [show (1:ℝ) = Real.exp 0 by rw [Real.exp_zero]]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hsh : Real.exp (-(y/2)) / (1 - Real.exp (-y)) = 1/(2 * Real.sinh (y/2)) :=
    exp_half_div_one_sub_exp_neg hy
  have hch : Real.exp (-(y/2)) / (1 + Real.exp (-y)) = 1/(2 * Real.cosh (y/2)) := by
    have hcosh : 2 * Real.cosh (y/2) = Real.exp (y/2) + Real.exp (-(y/2)) := by
      rw [Real.cosh_eq]
      ring
    rw [hcosh, div_eq_div_iff (by positivity) (by positivity), one_mul, mul_add,
      ← Real.exp_add, ← Real.exp_add]
    ring_nf
    rw [Real.exp_zero]
  have hker : Real.exp (-(y/2)) / (1 - Real.exp (-(2*y)))
      = (1/2) * (1/(2 * Real.sinh (y/2)) + 1/(2 * Real.cosh (y/2))) := by
    rw [← hsh, ← hch, show -(2*y) = (-y) + (-y) by ring, Real.exp_add]
    have h1 : (1:ℝ) - Real.exp (-y) ≠ 0 := by linarith
    have h2 : (1:ℝ) + Real.exp (-y) ≠ 0 := by positivity
    have h3 : (1:ℝ) - Real.exp (-y)^2 ≠ 0 := by nlinarith
    field_simp
    ring
  rw [hker]
  push_cast
  ring

/-- **The pointwise split of `2 Re (γ_K'/γ_K)(1/2 + it)`** (Poitou p. 6-03, the
`I_G(T)` integrand): constants plus the two digamma difference kernels. -/
theorem two_re_logDeriv_gammaFactor_half (K : Type*) [Field K] [NumberField K] (t : ℝ) :
    2 * (logDeriv (gammaFactor K) (((1/2:ℝ):ℂ) + (t:ℂ)*Complex.I)).re
      = -((((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
            + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ))
              * (Real.eulerMascheroniConstant + Real.log (8*π))
          + (NumberField.InfinitePlace.nrRealPlaces K : ℝ) * (π/2)))
        + ((NumberField.InfinitePlace.nrRealPlaces K : ℝ)/2)
            * (2 * ((Complex.digamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*Complex.I)
                - Complex.digamma ((1/4:ℝ):ℂ)).re))
        + (NumberField.InfinitePlace.nrComplexPlaces K : ℝ)
            * (2 * ((Complex.digamma (((1/2:ℝ):ℂ) + (t:ℂ)*Complex.I)
                - Complex.digamma ((1/2:ℝ):ℂ)).re)) := by
  set r₁ := NumberField.InfinitePlace.nrRealPlaces K
  set r₂ := NumberField.InfinitePlace.nrComplexPlaces K
  have hs : 0 < ((((1/2:ℝ):ℂ) + (t:ℂ)*Complex.I)).re := by
    simp
  rw [logDeriv_gammaFactor K hs]
  rw [show (((1/2:ℝ):ℂ) + (t:ℂ)*Complex.I)/2
      = ((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*Complex.I by push_cast; ring]
  -- normalise the coefficients and logs to real casts
  rw [show Complex.log (π:ℂ) = ((Real.log π : ℝ):ℂ) from
    (Complex.ofReal_log Real.pi_pos.le).symm]
  rw [show Complex.log (2*(π:ℂ)) = ((Real.log (2*π) : ℝ):ℂ) from by
    rw [show (2*(π:ℂ)) = ((2*π : ℝ):ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity)]]
  rw [show ((r₁:ℕ):ℂ) = ((r₁:ℝ):ℂ) by norm_cast, show ((r₂:ℕ):ℂ) = ((r₂:ℝ):ℂ) by norm_cast]
  rw [show (-(1/2) : ℂ) = ((-(1/2) : ℝ):ℂ) by norm_num,
    show ((1/2) : ℂ) = (((1/2) : ℝ):ℂ) by norm_num]
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re, Complex.neg_re,
    Complex.sub_re]
  -- digamma values
  have hψhalf : (Complex.digamma ((1/2:ℝ):ℂ)).re
      = -2*Real.log 2 - Real.eulerMascheroniConstant := by
    rw [show ((1/2:ℝ):ℂ) = (1/2:ℂ) by norm_num, Complex.digamma_one_half,
      Complex.sub_re, Complex.ofReal_re,
      show (-2 * Complex.log 2 : ℂ) = ((-2:ℝ):ℂ) * Complex.log ((2:ℝ):ℂ) by norm_num,
      Complex.re_ofReal_mul, Complex.log_ofReal_re]
  have hψdiff : (Complex.digamma ((1/2:ℝ):ℂ)).re - (Complex.digamma ((1/4:ℝ):ℂ)).re
      = π/2 + Real.log 2 := by
    have h := congrArg Complex.re digamma_half_sub_quarter
    rw [Complex.sub_re, Complex.ofReal_re] at h
    exact h
  have hψquarter : (Complex.digamma ((1/4:ℝ):ℂ)).re
      = -Real.eulerMascheroniConstant - 3*Real.log 2 - π/2 := by
    rw [hψhalf] at hψdiff
    linarith
  have hlogA : Real.log (8*π) = Real.log π + 3*Real.log 2 := by
    rw [show (8*π : ℝ) = 2^3*π by ring, Real.log_mul (by norm_num) Real.pi_pos.ne',
      Real.log_pow]
    push_cast
    ring
  have hlogB : Real.log (2*π) = Real.log 2 + Real.log π :=
    Real.log_mul (by norm_num) Real.pi_pos.ne'
  rw [hψhalf, hψquarter]
  linear_combination ((r₁:ℝ) + 2*(r₂:ℝ)) * hlogA - 2*(r₂:ℝ) * hlogB

/-- **The Γ-side of the explicit formula on the critical line** (Poitou pp. 6-03/6-04,
`I_G(T)` for the pure Γ-factor): for an even admissible test function `F` with the
boundary decay hypotheses at both digamma points,

`lim_{T→∞} ∫_{-T}^T 2 Re(γ_K'/γ_K)(1/2+it)·φ(t) dt
   = 2π·{ -(n(γ_E + log 8π) + r₁ π/2)·F(0)
          + n ∫₀^∞ (F(0)-F(x))/(2 sinh(x/2)) dx
          + r₁ ∫₀^∞ (F(0)-F(x))/(2 cosh(x/2)) dx }`,

where `n = [K:ℚ]`, `r₁` is the number of real places and `γ_E` Euler's constant. -/
theorem tendsto_IG_gammaFactor (K : Type*) [Field K] [NumberField K]
    {F : ℝ → ℂ} (hF : Integrable F)
    (hre : LocallyBoundedVariationOn (fun u : ℝ => (F u).re) Set.univ)
    (him : LocallyBoundedVariationOn (fun u : ℝ => (F u).im) Set.univ)
    (hF0 : Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds (F 0)))
    (hFeven : ∀ x : ℝ, F (-x) = F x)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    (hFdiv2 : MemLp (fun x : ℝ => (F 0 - F x)/(x:ℂ)) 2 (volume : Measure ℝ))
    (htop2 : Tendsto (fun t : ℝ =>
      rhoFT (fun x => ((poitouKernel (1/2) x : ℝ) : ℂ)) t * gammaFT F t) atTop (nhds 0))
    (hbot2 : Tendsto (fun t : ℝ =>
      rhoFT (fun x => ((poitouKernel (1/2) x : ℝ) : ℂ)) t * gammaFT F t) atBot (nhds 0))
    (htop4 : Tendsto (fun t : ℝ =>
      rhoFT (fun x => ((poitouKernel (1/4) x : ℝ) : ℂ)) t
        * gammaFT (fun x : ℝ => F (x/2) / 2) t) atTop (nhds 0))
    (hbot4 : Tendsto (fun t : ℝ =>
      rhoFT (fun x => ((poitouKernel (1/4) x : ℝ) : ℂ)) t
        * gammaFT (fun x : ℝ => F (x/2) / 2) t) atBot (nhds 0)) :
    Tendsto (fun T : ℝ => ∫ t in (-T)..T,
        ((2 * (logDeriv (gammaFactor K) (((1/2:ℝ):ℂ) + (t:ℂ)*Complex.I)).re : ℝ) : ℂ)
          * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)))
      atTop (nhds (((2*π : ℝ) : ℂ) *
        ((((-(((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
              + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ))
                * (Real.eulerMascheroniConstant + Real.log (8*π))
              + (NumberField.InfinitePlace.nrRealPlaces K : ℝ) * (π/2)) : ℝ)) : ℂ) * F 0
          + (((NumberField.InfinitePlace.nrRealPlaces K
              + 2*NumberField.InfinitePlace.nrComplexPlaces K : ℕ)) : ℂ)
              * (∫ y in Set.Ioi (0:ℝ),
                ((1/(2 * Real.sinh (y/2)) : ℝ) : ℂ) * (F 0 - F y))
          + ((NumberField.InfinitePlace.nrRealPlaces K : ℕ) : ℂ)
              * ∫ y in Set.Ioi (0:ℝ),
                ((1/(2 * Real.cosh (y/2)) : ℝ) : ℂ) * (F 0 - F y)))) := by
  set r₁ := NumberField.InfinitePlace.nrRealPlaces K
  set r₂ := NumberField.InfinitePlace.nrComplexPlaces K
  -- the left one-sided limit at 0 from evenness
  have hmneg : Tendsto (fun x : ℝ => -x) (nhdsWithin 0 (Set.Iio 0))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h2 := (continuous_neg.tendsto (0:ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Iio 0))
      rw [neg_zero] at h2
      exact h2
    · filter_upwards [self_mem_nhdsWithin] with x hx
      rw [Set.mem_Iio] at hx
      exact Set.mem_Ioi.mpr (by linarith)
  have hFm : Tendsto F (nhdsWithin 0 (Set.Iio 0)) (nhds (F 0)) := by
    have h2 := hF0.comp hmneg
    exact h2.congr (fun x => hFeven x)
  -- the Fourier window at 0
  have hW := tendsto_fourier_window_jordan hF hre him hF0 hFm
  have hWfun : (fun T : ℝ => ∫ t in (-T)..T,
      ∫ u : ℝ, F u * Complex.exp ((t:ℂ)*(u:ℂ)*Complex.I))
      = fun T : ℝ => ∫ t in (-T)..T,
          ∫ x : ℝ, F x * Complex.exp ((t*x : ℝ)*Complex.I) := by
    funext T
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    show F u * Complex.exp ((t:ℂ)*(u:ℂ)*Complex.I)
        = F u * Complex.exp (((t*u : ℝ):ℂ)*Complex.I)
    rw [Complex.ofReal_mul]
  rw [hWfun] at hW
  -- the two Proposition-3 inputs
  have hQ := prop3_poitou (show (0:ℝ) < 1/2 by norm_num) hF hFeven hFdiv hFdiv2
    htop2 hbot2
  have hP := prop3_poitou_quarter hF hFeven hFdiv hFdiv2 htop4 hbot4
  -- continuity for interval integrability
  have hφc : Continuous (fun t : ℝ => ∫ x : ℝ, F x * Complex.exp ((t*x : ℝ)*Complex.I)) :=
    continuous_muFT hF
  have hk2eq : (fun t : ℝ => (((2 * ((Complex.digamma (((1/2:ℝ):ℂ) + (t:ℂ)*Complex.I)
      - Complex.digamma ((1/2:ℝ):ℂ)).re) : ℝ)) : ℂ))
      = rhoFT (fun x => ((poitouKernel (1/2) x : ℝ) : ℂ)) :=
    funext (fun t => (rhoFT_poitouKernel (by norm_num : (0:ℝ) < 1/2) t).symm)
  have hk2c : Continuous (fun t : ℝ =>
      (((2 * ((Complex.digamma (((1/2:ℝ):ℂ) + (t:ℂ)*Complex.I)
        - Complex.digamma ((1/2:ℝ):ℂ)).re) : ℝ)) : ℂ)) := by
    rw [hk2eq]
    exact continuous_rhoFT (integrable_poitouKernel (by norm_num))
  have hk4eq : (fun t : ℝ => (((2 * ((Complex.digamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*Complex.I)
      - Complex.digamma ((1/4:ℝ):ℂ)).re) : ℝ)) : ℂ))
      = (rhoFT (fun x => ((poitouKernel (1/4) x : ℝ) : ℂ))) ∘ (fun t : ℝ => t/2) :=
    funext (fun t => (rhoFT_poitouKernel (by norm_num : (0:ℝ) < 1/4) (t/2)).symm)
  have hk4c : Continuous (fun t : ℝ =>
      (((2 * ((Complex.digamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*Complex.I)
        - Complex.digamma ((1/4:ℝ):ℂ)).re) : ℝ)) : ℂ)) := by
    rw [hk4eq]
    exact (continuous_rhoFT (integrable_poitouKernel (by norm_num))).comp
      (continuous_id.div_const 2)
  -- the pointwise split, cast to ℂ
  have hpt : ∀ t : ℝ,
      ((2 * (logDeriv (gammaFactor K) (((1/2:ℝ):ℂ) + (t:ℂ)*Complex.I)).re : ℝ) : ℂ)
        * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ)*Complex.I))
      = ((-(((r₁:ℝ) + 2*(r₂:ℝ)) * (Real.eulerMascheroniConstant + Real.log (8*π))
            + (r₁:ℝ) * (π/2)) : ℝ) : ℂ)
          * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ)*Complex.I))
        + (((r₁:ℕ):ℂ)/2 * ((((2 * ((Complex.digamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*Complex.I)
              - Complex.digamma ((1/4:ℝ):ℂ)).re) : ℝ)) : ℂ)
            * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ)*Complex.I)))
          + ((r₂:ℕ):ℂ) * ((((2 * ((Complex.digamma (((1/2:ℝ):ℂ) + (t:ℂ)*Complex.I)
              - Complex.digamma ((1/2:ℝ):ℂ)).re) : ℝ)) : ℂ)
            * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ)*Complex.I)))) := by
    intro t
    rw [two_re_logDeriv_gammaFactor_half K t]
    push_cast
    ring
  -- fixed-T splitting of the interval integral
  have hfun : ∀ T : ℝ, (∫ t in (-T)..T,
      ((2 * (logDeriv (gammaFactor K) (((1/2:ℝ):ℂ) + (t:ℂ)*Complex.I)).re : ℝ) : ℂ)
        * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ)*Complex.I)))
      = ((-(((r₁:ℝ) + 2*(r₂:ℝ)) * (Real.eulerMascheroniConstant + Real.log (8*π))
            + (r₁:ℝ) * (π/2)) : ℝ) : ℂ)
          * (∫ t in (-T)..T, ∫ x : ℝ, F x * Complex.exp ((t*x : ℝ)*Complex.I))
        + (((r₁:ℕ):ℂ)/2 * (∫ t in (-T)..T,
            (((2 * ((Complex.digamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*Complex.I)
              - Complex.digamma ((1/4:ℝ):ℂ)).re) : ℝ)) : ℂ)
              * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ)*Complex.I)))
          + ((r₂:ℕ):ℂ) * (∫ t in (-T)..T,
            (((2 * ((Complex.digamma (((1/2:ℝ):ℂ) + (t:ℂ)*Complex.I)
              - Complex.digamma ((1/2:ℝ):ℂ)).re) : ℝ)) : ℂ)
              * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ)*Complex.I)))) := by
    intro T
    have ii1 : IntervalIntegrable (fun t : ℝ =>
        ((-(((r₁:ℝ) + 2*(r₂:ℝ)) * (Real.eulerMascheroniConstant + Real.log (8*π))
            + (r₁:ℝ) * (π/2)) : ℝ) : ℂ)
          * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ)*Complex.I)))
        MeasureTheory.volume (-T) T :=
      (continuous_const.mul hφc).intervalIntegrable _ _
    have ii2 : IntervalIntegrable (fun t : ℝ =>
        ((r₁:ℕ):ℂ)/2 * ((((2 * ((Complex.digamma (((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ)*Complex.I)
            - Complex.digamma ((1/4:ℝ):ℂ)).re) : ℝ)) : ℂ)
          * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ)*Complex.I))))
        MeasureTheory.volume (-T) T :=
      (continuous_const.mul (hk4c.mul hφc)).intervalIntegrable _ _
    have ii3 : IntervalIntegrable (fun t : ℝ =>
        ((r₂:ℕ):ℂ) * ((((2 * ((Complex.digamma (((1/2:ℝ):ℂ) + (t:ℂ)*Complex.I)
            - Complex.digamma ((1/2:ℝ):ℂ)).re) : ℝ)) : ℂ)
          * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ)*Complex.I))))
        MeasureTheory.volume (-T) T :=
      (continuous_const.mul (hk2c.mul hφc)).intervalIntegrable _ _
    rw [intervalIntegral.integral_congr (fun t _ => hpt t),
      intervalIntegral.integral_add ii1 (ii2.add ii3),
      intervalIntegral.integral_add ii2 ii3,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  refine Tendsto.congr (fun T => (hfun T).symm) ?_
  -- assemble the three limits
  have hsum := (hW.const_mul
      ((((-(((r₁:ℝ) + 2*(r₂:ℝ)) * (Real.eulerMascheroniConstant + Real.log (8*π))
        + (r₁:ℝ) * (π/2)) : ℝ)) : ℂ))).add
    ((hP.const_mul (((r₁:ℕ):ℂ)/2)).add (hQ.const_mul ((r₂:ℕ):ℂ)))
  -- identify the limit value
  have hlim : ((((-(((r₁:ℝ) + 2*(r₂:ℝ)) * (Real.eulerMascheroniConstant + Real.log (8*π))
        + (r₁:ℝ) * (π/2)) : ℝ)) : ℂ)) * (((π : ℝ) : ℂ) * (F 0 + F 0))
      + ((((r₁:ℕ):ℂ)/2) * (((8*π : ℝ) : ℂ) * ∫ y in Set.Ioi (0:ℝ),
          ((Real.exp (-(y/2)) / (1 - Real.exp (-(2*y))) : ℝ) : ℂ) * (F 0 - F y))
        + ((r₂:ℕ):ℂ) * (((4*π : ℝ) : ℂ) * ∫ y in Set.Ioi (0:ℝ),
          ((Real.exp (-(1/2*y)) / (1 - Real.exp (-y)) : ℝ) : ℂ) * (F 0 - F y)))
      = ((2*π : ℝ) : ℂ) *
        ((((-(((r₁:ℝ) + 2*(r₂:ℝ)) * (Real.eulerMascheroniConstant + Real.log (8*π))
              + (r₁:ℝ) * (π/2)) : ℝ)) : ℂ) * F 0
          + (((r₁ + 2*r₂ : ℕ)) : ℂ) * (∫ y in Set.Ioi (0:ℝ),
              ((1/(2 * Real.sinh (y/2)) : ℝ) : ℂ) * (F 0 - F y))
          + ((r₁ : ℕ) : ℂ) * ∫ y in Set.Ioi (0:ℝ),
              ((1/(2 * Real.cosh (y/2)) : ℝ) : ℂ) * (F 0 - F y)) := by
    rw [integral_gauss_quarter_eq_sinh_add_cosh hF hFdiv2, integral_gauss_half_eq_sinh,
      show ((8*π : ℝ) : ℂ) = 4*((2*π : ℝ) : ℂ) by push_cast; ring,
      show ((4*π : ℝ) : ℂ) = 2*((2*π : ℝ) : ℂ) by push_cast; ring,
      show ((π : ℝ) : ℂ) * (F 0 + F 0) = ((2*π : ℝ) : ℂ) * F 0 by push_cast; ring,
      show (((r₁ + 2*r₂ : ℕ)) : ℂ) = ((r₁:ℕ):ℂ) + 2*((r₂:ℕ):ℂ) by push_cast; ring]
    ring
  rw [← hlim]
  exact hsum

/-- **Schwarz reflection for the digamma function** on the right half-plane:
`ψ(z̄) = conj ψ(z)`, from the Gauss integral representation. (Not yet in mathlib.) -/
theorem digamma_conj {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma (starRingEnd ℂ z) = starRingEnd ℂ (Complex.digamma z) := by
  have hzc : 0 < ((starRingEnd ℂ) z).re := by
    rw [Complex.conj_re]
    exact hz
  rw [digamma_eq_integral_gauss_one hzc, digamma_eq_integral_gauss_one hz,
    ← integral_conj]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [Set.mem_Ioi] at hx
  rw [map_div₀, map_sub, Complex.conj_ofReal, Complex.conj_ofReal]
  congr 1
  congr 1
  -- conj((1+x)^(-z)) = (1+x)^(-z̄)
  rw [show (-(starRingEnd ℂ) z) = (starRingEnd ℂ) (-z) by rw [map_neg],
    Complex.cpow_conj _ _ (by
      rw [Complex.arg_ofReal_of_nonneg (by linarith : (0:ℝ) ≤ 1+x)]
      exact Real.pi_ne_zero.symm),
    Complex.conj_ofReal]

/-- **Schwarz reflection for `γ_K'/γ_K`** on the right half-plane. -/
theorem logDeriv_gammaFactor_conj (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 0 < s.re) :
    logDeriv (gammaFactor K) (starRingEnd ℂ s)
      = starRingEnd ℂ (logDeriv (gammaFactor K) s) := by
  have hsc : 0 < ((starRingEnd ℂ) s).re := by
    rw [Complex.conj_re]
    exact hs
  have hs2 : 0 < (s/2).re := by
    rw [show (s/2).re = s.re/2 by simp]
    linarith
  rw [logDeriv_gammaFactor K hsc, logDeriv_gammaFactor K hs]
  rw [show (starRingEnd ℂ) s / 2 = (starRingEnd ℂ) (s/2) by
    rw [map_div₀, map_ofNat]]
  rw [digamma_conj hs2, digamma_conj hs]
  rw [show Complex.log (π:ℂ) = ((Real.log π : ℝ):ℂ) from
    (Complex.ofReal_log Real.pi_pos.le).symm]
  rw [show Complex.log (2*(π:ℂ)) = ((Real.log (2*π) : ℝ):ℂ) from by
    rw [show (2*(π:ℂ)) = ((2*π : ℝ):ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity)]]
  simp only [map_add, map_mul, map_neg, map_natCast, map_div₀, map_one, map_ofNat,
    Complex.conj_ofReal]

/-- `γ_K'/γ_K` is differentiable on the right half-plane (the derivative of an
analytic nonvanishing function divided by it). -/
theorem differentiableAt_logDeriv_gammaFactor (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (logDeriv (gammaFactor K)) s := by
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ (gammaFactor K) {w : ℂ | 0 < w.re} := by
    intro w hw
    rw [Set.mem_setOf_eq] at hw
    exact (((differentiableAt_Gammaℝ_of_re_pos hw).pow _).mul
      ((differentiableAt_Gammaℂ_of_re_pos hw).pow _)).differentiableWithinAt
  have han : AnalyticOnNhd ℂ (gammaFactor K) {w : ℂ | 0 < w.re} :=
    hdiff.analyticOnNhd hU
  have hd : DifferentiableAt ℂ (deriv (gammaFactor K)) s :=
    ((han s hs).deriv).differentiableAt
  have hval : DifferentiableAt ℂ (gammaFactor K) s := (han s hs).differentiableAt
  have hne : gammaFactor K s ≠ 0 := gammaFactor_ne_zero_of_re_pos K hs
  exact hd.div hval hne

/-- **The generic contour shift `Re = 1+a → Re = 1/2`** (Poitou p. 6-03: "on peut
remplacer `I_G^a(T)` par `I_G(T)`"): for entire `Φ` bounded on the band by `B|t|`,
and `g` analytic on the right half-plane with `‖g‖ ≤ C|t|` on the sub-band, the
difference of the two symmetric vertical integrals of `(Φ(s) + Φ(1-s))·g(s)`
vanishes as `T → ∞` provided `B·C → 0`. -/
theorem tendsto_shift_vertical_sub {a : ℝ} (ha : 0 < a) {Φ g : ℂ → ℂ}
    (hΦ : ∀ ζ : ℂ, -a ≤ ζ.re → ζ.re ≤ 1+a → DifferentiableAt ℂ Φ ζ)
    (hg : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ g s)
    {B C : ℝ → ℝ}
    (hB : ∀ σ t : ℝ, -a ≤ σ → σ ≤ 1+a → ‖Φ ((σ:ℂ) + (t:ℂ)*Complex.I)‖ ≤ B |t|)
    (hgb : ∀ σ t : ℝ, 1/2 ≤ σ → σ ≤ 1+a → 4 ≤ |t| →
      ‖g ((σ:ℂ) + (t:ℂ)*Complex.I)‖ ≤ C |t|)
    (hlim : Tendsto (fun T : ℝ => B T * C T) atTop (nhds 0)) :
    Tendsto (fun T : ℝ =>
      (∫ y in (-T)..T, (Φ (((1+a:ℝ):ℂ) + (y:ℂ)*Complex.I)
          + Φ (1 - (((1+a:ℝ):ℂ) + (y:ℂ)*Complex.I)))
          * g (((1+a:ℝ):ℂ) + (y:ℂ)*Complex.I))
      - ∫ y in (-T)..T, (Φ (((1/2:ℝ):ℂ) + (y:ℂ)*Complex.I)
          + Φ (1 - (((1/2:ℝ):ℂ) + (y:ℂ)*Complex.I)))
          * g (((1/2:ℝ):ℂ) + (y:ℂ)*Complex.I)) atTop (nhds 0) := by
  set f : ℂ → ℂ := fun s => (Φ s + Φ (1 - s)) * g s with hf
  have hfdiff : ∀ ζ : ℂ, 1/2 ≤ ζ.re → ζ.re ≤ 1+a → DifferentiableAt ℂ f ζ := by
    intro ζ hζ1 hζ2
    refine DifferentiableAt.mul ?_ (hg ζ (by linarith))
    refine (hΦ ζ (by linarith) hζ2).add ?_
    have h0 : (fun s : ℂ => Φ (1 - s)) = Φ ∘ (fun s : ℂ => 1 - s) := rfl
    rw [h0]
    refine DifferentiableAt.comp ζ (hΦ (1 - ζ) ?_ ?_)
      ((differentiableAt_const 1).sub differentiableAt_id)
    · rw [Complex.sub_re, Complex.one_re]
      linarith
    · rw [Complex.sub_re, Complex.one_re]
      linarith
  -- the fixed-T horizontal bound
  have hkey : ∀ T : ℝ, 4 ≤ T →
      ‖(∫ y in (-T)..T, f (((1+a:ℝ):ℂ) + (y:ℂ)*Complex.I))
        - ∫ y in (-T)..T, f (((1/2:ℝ):ℂ) + (y:ℂ)*Complex.I)‖
      ≤ (2 + 4*a) * (B T * C T) := by
    intro T hT
    have hT0 : 0 < T := by linarith
    set z : ℂ := ((1/2:ℝ):ℂ) + ((-T:ℝ):ℂ)*Complex.I with hz
    set w : ℂ := ((1+a:ℝ):ℂ) + ((T:ℝ):ℂ)*Complex.I with hw
    have hzre : z.re = 1/2 := by
      rw [hz]
      simp
    have hzim : z.im = -T := by
      rw [hz]
      simp
    have hwre : w.re = 1+a := by
      rw [hw]
      simp
    have hwim : w.im = T := by
      rw [hw]
      simp
    have hrele : (1/2 : ℝ) ≤ 1+a := by linarith
    have himle : (-T : ℝ) ≤ T := by linarith
    -- Goursat on the rectangle
    have h0 : rectangleIntegral f z w = 0 := by
      refine rectangleIntegral_eq_zero (s := ∅) Set.countable_empty ?_ ?_
      · intro ζ hζ
        rw [Complex.mem_reProdIm, hzre, hwre, hzim, hwim,
          Set.uIcc_of_le hrele, Set.uIcc_of_le himle] at hζ
        exact ((hfdiff ζ hζ.1.1 hζ.1.2).continuousAt).continuousWithinAt
      · intro ζ hζ
        rw [Set.mem_sdiff, Complex.mem_reProdIm, hzre, hwre, hzim, hwim] at hζ
        refine hfdiff ζ ?_ ?_
        · have h1 := hζ.1.1.1
          rw [min_eq_left hrele] at h1
          linarith
        · have h2 := hζ.1.1.2
          rw [max_eq_right hrele] at h2
          linarith
    rw [rectangleIntegral, hzre, hzim, hwre, hwim] at h0
    -- solve for the vertical difference
    have h1 : Complex.I * ((∫ y in (-T)..T, f (((1+a:ℝ):ℂ) + (y:ℂ)*Complex.I))
        - ∫ y in (-T)..T, f (((1/2:ℝ):ℂ) + (y:ℂ)*Complex.I))
        = (∫ x in (1/2)..(1+a), f ((x:ℂ) + ((T:ℝ):ℂ)*Complex.I))
          - ∫ x in (1/2)..(1+a), f ((x:ℂ) + ((-T:ℝ):ℂ)*Complex.I) := by
      have h2 := h0
      rw [smul_eq_mul, smul_eq_mul] at h2
      linear_combination h2
    have h2 : (∫ y in (-T)..T, f (((1+a:ℝ):ℂ) + (y:ℂ)*Complex.I))
        - ∫ y in (-T)..T, f (((1/2:ℝ):ℂ) + (y:ℂ)*Complex.I)
        = -Complex.I * ((∫ x in (1/2)..(1+a), f ((x:ℂ) + ((T:ℝ):ℂ)*Complex.I))
          - ∫ x in (1/2)..(1+a), f ((x:ℂ) + ((-T:ℝ):ℂ)*Complex.I)) := by
      have h3 : -Complex.I * (Complex.I * ((∫ y in (-T)..T, f (((1+a:ℝ):ℂ) + (y:ℂ)*Complex.I))
          - ∫ y in (-T)..T, f (((1/2:ℝ):ℂ) + (y:ℂ)*Complex.I)))
          = -Complex.I * ((∫ x in (1/2)..(1+a), f ((x:ℂ) + ((T:ℝ):ℂ)*Complex.I))
            - ∫ x in (1/2)..(1+a), f ((x:ℂ) + ((-T:ℝ):ℂ)*Complex.I)) := by
        rw [h1]
      rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul] at h3
      exact h3
    rw [h2, norm_mul, norm_neg, Complex.norm_I, one_mul]
    -- bound the two horizontal integrals
    have hBnn : 0 ≤ B T := by
      have h4 := hB (1/2) T (by linarith) (by linarith)
      rw [abs_of_pos hT0] at h4
      exact le_trans (norm_nonneg _) h4
    have hCnn : 0 ≤ C T := by
      have h4 := hgb (1/2) T (le_refl _) (by linarith) (by rw [abs_of_pos hT0]; exact hT)
      rw [abs_of_pos hT0] at h4
      exact le_trans (norm_nonneg _) h4
    have hbound : ∀ t : ℝ, |t| = T → ∀ x ∈ Set.uIoc (1/2 : ℝ) (1+a),
        ‖f ((x:ℂ) + (t:ℝ)*Complex.I)‖ ≤ 2*B T*C T := by
      intro t ht x hx
      rw [Set.uIoc_of_le hrele, Set.mem_Ioc] at hx
      rw [hf]
      show ‖(Φ ((x:ℂ) + (t:ℂ)*Complex.I) + Φ (1 - ((x:ℂ) + (t:ℂ)*Complex.I)))
        * g ((x:ℂ) + (t:ℂ)*Complex.I)‖ ≤ 2*B T*C T
      rw [norm_mul]
      have hb1 : ‖Φ ((x:ℂ) + (t:ℂ)*Complex.I)‖ ≤ B T := by
        have h5 := hB x t (by linarith [hx.1]) hx.2
        rw [ht] at h5
        exact h5
      have hb2 : ‖Φ (1 - ((x:ℂ) + (t:ℂ)*Complex.I))‖ ≤ B T := by
        have h6 : (1 : ℂ) - ((x:ℂ) + (t:ℂ)*Complex.I)
            = (((1-x : ℝ)):ℂ) + ((-t : ℝ):ℂ)*Complex.I := by
          push_cast
          ring
        rw [h6]
        have h5 := hB (1-x) (-t) (by linarith [hx.2]) (by linarith [hx.1])
        rw [abs_neg, ht] at h5
        exact h5
      have hb3 : ‖g ((x:ℂ) + (t:ℂ)*Complex.I)‖ ≤ C T := by
        have h5 := hgb x t (le_of_lt hx.1) hx.2 (by rw [ht]; exact hT)
        rw [ht] at h5
        exact h5
      calc ‖Φ ((x:ℂ) + (t:ℂ)*Complex.I) + Φ (1 - ((x:ℂ) + (t:ℂ)*Complex.I))‖
            * ‖g ((x:ℂ) + (t:ℂ)*Complex.I)‖
          ≤ (B T + B T) * C T := by
            refine mul_le_mul (le_trans (norm_add_le _ _) (add_le_add hb1 hb2)) hb3
              (norm_nonneg _) (by linarith)
        _ = 2*B T*C T := by ring
    have htop : ‖∫ x in (1/2)..(1+a), f ((x:ℂ) + ((T:ℝ):ℂ)*Complex.I)‖
        ≤ 2*B T*C T * |1+a - 1/2| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (hbound T (abs_of_pos hT0) )
    have hbot : ‖∫ x in (1/2)..(1+a), f ((x:ℂ) + ((-T:ℝ):ℂ)*Complex.I)‖
        ≤ 2*B T*C T * |1+a - 1/2| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (hbound (-T) (by rw [abs_neg, abs_of_pos hT0]))
    have habs : |1+a - (1/2 : ℝ)| = 1/2 + a := by
      rw [abs_of_pos (by linarith)]
      ring
    rw [habs] at htop hbot
    calc ‖(∫ x in (1/2)..(1+a), f ((x:ℂ) + ((T:ℝ):ℂ)*Complex.I))
          - ∫ x in (1/2)..(1+a), f ((x:ℂ) + ((-T:ℝ):ℂ)*Complex.I)‖
        ≤ ‖∫ x in (1/2)..(1+a), f ((x:ℂ) + ((T:ℝ):ℂ)*Complex.I)‖
          + ‖∫ x in (1/2)..(1+a), f ((x:ℂ) + ((-T:ℝ):ℂ)*Complex.I)‖ := norm_sub_le _ _
      _ ≤ 2*B T*C T * (1/2 + a) + 2*B T*C T * (1/2 + a) := add_le_add htop hbot
      _ = (2 + 4*a) * (B T * C T) := by ring
  -- squeeze
  have h9 := hlim.const_mul (2 + 4*a)
  rw [mul_zero] at h9
  refine squeeze_zero_norm' ?_ h9
  filter_upwards [Filter.eventually_ge_atTop (4:ℝ)] with T hT
  exact hkey T hT

/-- Continuity of `y ↦ γ_K'/γ_K(1/2 + iy)`. -/
theorem continuous_logDeriv_gammaFactor_half (K : Type*) [Field K] [NumberField K] :
    Continuous (fun y : ℝ =>
      logDeriv (gammaFactor K) (((1/2:ℝ):ℂ) + (y:ℂ)*Complex.I)) := by
  refine continuous_iff_continuousAt.mpr (fun y => ?_)
  refine ContinuousAt.comp ?_ ?_
  · refine (differentiableAt_logDeriv_gammaFactor K ?_).continuousAt
    simp
  · exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt

/-- **The critical-line fold** (Poitou p. 6-03, the passage from
`{Φ(s) + Φ(1-s)} d log G` to `φ(t)·2 Re(G'/G)`): for an even integrable `F` whose
`Φ` restricts on the critical line to the Fourier integral `φ`, the shifted vertical
integral coincides with the `I_G` integrand at every height `T`. The reflection
`t ↦ -t` together with Schwarz reflection for `γ_K` produces the real part; no
reality assumption on `F` is needed. -/
theorem integral_half_line_fold (K : Type*) [Field K] [NumberField K]
    {F : ℝ → ℂ} (hF : Integrable F) (hFeven : ∀ x : ℝ, F (-x) = F x)
    {Φ : ℂ → ℂ}
    (hΦval : ∀ y : ℝ, Φ (((1/2:ℝ):ℂ) + (y:ℂ)*Complex.I)
      = ∫ x : ℝ, F x * Complex.exp ((y*x : ℝ) * Complex.I))
    (T : ℝ) :
    (∫ y in (-T)..T, (Φ (((1/2:ℝ):ℂ) + (y:ℂ)*Complex.I)
        + Φ (1 - (((1/2:ℝ):ℂ) + (y:ℂ)*Complex.I)))
        * logDeriv (gammaFactor K) (((1/2:ℝ):ℂ) + (y:ℂ)*Complex.I))
      = ∫ y in (-T)..T,
          ((2 * (logDeriv (gammaFactor K) (((1/2:ℝ):ℂ) + (y:ℂ)*Complex.I)).re : ℝ) : ℂ)
            * (∫ x : ℝ, F x * Complex.exp ((y*x : ℝ) * Complex.I)) := by
  set φ : ℝ → ℂ := fun y => ∫ x : ℝ, F x * Complex.exp ((y*x : ℝ) * Complex.I) with hφ
  set L : ℝ → ℂ := fun y =>
    logDeriv (gammaFactor K) (((1/2:ℝ):ℂ) + (y:ℂ)*Complex.I) with hL
  -- φ is even
  have hφeven : ∀ y : ℝ, φ (-y) = φ y := by
    intro y
    rw [hφ]
    simp only
    rw [← integral_comp_neg_real (fun x => F x * Complex.exp ((y*x : ℝ) * Complex.I))]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show F x * Complex.exp (((-y)*x : ℝ) * Complex.I)
        = F (-x) * Complex.exp ((y*(-x) : ℝ) * Complex.I)
    rw [hFeven x, show (y*(-x) : ℝ) = ((-y)*x : ℝ) by ring]
  -- L reflects by conjugation
  have hLconj : ∀ y : ℝ, L (-y) = (starRingEnd ℂ) (L y) := by
    intro y
    rw [hL]
    simp only
    rw [show (((1/2:ℝ):ℂ) + ((-y : ℝ):ℂ)*Complex.I)
        = (starRingEnd ℂ) (((1/2:ℝ):ℂ) + (y:ℂ)*Complex.I) by
      rw [map_add, Complex.conj_ofReal, map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring]
    exact logDeriv_gammaFactor_conj K (by simp)
  -- the left-hand integrand is 2·φ·L
  have hpt : ∀ y : ℝ, (Φ (((1/2:ℝ):ℂ) + (y:ℂ)*Complex.I)
      + Φ (1 - (((1/2:ℝ):ℂ) + (y:ℂ)*Complex.I)))
      * logDeriv (gammaFactor K) (((1/2:ℝ):ℂ) + (y:ℂ)*Complex.I)
      = 2 * φ y * L y := by
    intro y
    have h1 : (1:ℂ) - (((1/2:ℝ):ℂ) + (y:ℂ)*Complex.I)
        = ((1/2:ℝ):ℂ) + ((-y : ℝ):ℂ)*Complex.I := by
      push_cast
      ring
    rw [h1, hΦval y, hΦval (-y)]
    have h2 : (∫ x : ℝ, F x * Complex.exp (((-y)*x : ℝ) * Complex.I)) = φ (-y) := rfl
    rw [h2, hφeven y]
    show (φ y + φ y) * L y = 2 * φ y * L y
    ring
  rw [intervalIntegral.integral_congr (fun y _ => hpt y)]
  -- continuity for integrability
  have hφc : Continuous φ := continuous_muFT hF
  have hLc : Continuous L := continuous_logDeriv_gammaFactor_half K
  have hLcc : Continuous (fun y : ℝ => (starRingEnd ℂ) (L y)) :=
    Complex.continuous_conj.comp hLc
  -- reflect: ∫ 2φL = ∫ 2φ·conj L
  have hrefl : (∫ y in (-T)..T, 2 * φ y * L y)
      = ∫ y in (-T)..T, 2 * φ y * (starRingEnd ℂ) (L y) := by
    have h0 := intervalIntegral.integral_comp_neg (a := -T) (b := T)
      (fun y => 2 * φ y * L y)
    rw [neg_neg] at h0
    rw [← h0]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    rw [hφeven y, hLconj y]
  -- average and take the real part of L
  have hii1 : IntervalIntegrable (fun y => 2 * φ y * L y) MeasureTheory.volume (-T) T :=
    ((continuous_const.mul hφc).mul hLc).intervalIntegrable _ _
  have hii2 : IntervalIntegrable (fun y => 2 * φ y * (starRingEnd ℂ) (L y))
      MeasureTheory.volume (-T) T :=
    ((continuous_const.mul hφc).mul hLcc).intervalIntegrable _ _
  have havg : (∫ y in (-T)..T, 2 * φ y * L y)
      = ∫ y in (-T)..T, φ y * (L y + (starRingEnd ℂ) (L y)) := by
    have h1 : (∫ y in (-T)..T, 2 * φ y * L y)
        = ((∫ y in (-T)..T, 2 * φ y * L y)
          + ∫ y in (-T)..T, 2 * φ y * (starRingEnd ℂ) (L y)) / 2 := by
      rw [← hrefl]
      ring
    rw [h1, ← intervalIntegral.integral_add hii1 hii2]
    rw [show ((∫ y in (-T)..T, (2 * φ y * L y + 2 * φ y * (starRingEnd ℂ) (L y))) / 2)
        = (1/2 : ℂ) * ∫ y in (-T)..T, (2 * φ y * L y + 2 * φ y * (starRingEnd ℂ) (L y))
        from by ring]
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    ring
  rw [havg]
  refine intervalIntegral.integral_congr (fun y _ => ?_)
  rw [Complex.add_conj]
  rw [hφ, hL]
  simp only
  push_cast
  ring

/-- **The `ρ`-kernel is `O(log|t|)`** (Poitou p. 6-06: "ce qu'on sait être de
l'ordre de log t pour t grand"): the boundary-decay input for Lemme 2, discharged
from the digamma window bound A6. -/
theorem exists_norm_rhoFT_poitouKernel_le {σ : ℝ} (hσ : 0 < σ) (hσl : -1 ≤ σ)
    (hσr : σ ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ |t| →
      ‖rhoFT (fun x => ((poitouKernel σ x : ℝ) : ℂ)) t‖ ≤ C * Real.log (2 + |t|) := by
  obtain ⟨C₆, hC₆pos, hC₆⟩ := exists_norm_digamma_le
  refine ⟨2 * (C₆ + ‖Complex.digamma (σ:ℂ)‖) + 1, by positivity, fun t ht => ?_⟩
  have hlog1 : (1:ℝ) ≤ Real.log (2 + |t|) := by
    rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    refine Real.log_le_log (Real.exp_pos 1) ?_
    have := Real.exp_one_lt_d9
    linarith
  rw [rhoFT_poitouKernel hσ t, Complex.norm_real, Real.norm_eq_abs]
  have h1 : |2 * ((Complex.digamma ((σ:ℂ) + (t:ℂ)*Complex.I)
      - Complex.digamma (σ:ℂ)).re)|
      ≤ 2 * (‖Complex.digamma ((σ:ℂ) + (t:ℂ)*Complex.I)‖ + ‖Complex.digamma (σ:ℂ)‖) := by
    rw [abs_mul, abs_two]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    calc |(Complex.digamma ((σ:ℂ) + (t:ℂ)*Complex.I) - Complex.digamma (σ:ℂ)).re|
        ≤ ‖Complex.digamma ((σ:ℂ) + (t:ℂ)*Complex.I) - Complex.digamma (σ:ℂ)‖ :=
          Complex.abs_re_le_norm _
      _ ≤ ‖Complex.digamma ((σ:ℂ) + (t:ℂ)*Complex.I)‖ + ‖Complex.digamma (σ:ℂ)‖ :=
          norm_sub_le _ _
  refine le_trans h1 ?_
  have h2 := hC₆ σ t hσl hσr ht
  have h3 : ‖Complex.digamma (σ:ℂ)‖ ≤ ‖Complex.digamma (σ:ℂ)‖ * Real.log (2 + |t|) := by
    nlinarith [norm_nonneg (Complex.digamma (σ:ℂ))]
  calc 2 * (‖Complex.digamma ((σ:ℂ) + (t:ℂ)*Complex.I)‖ + ‖Complex.digamma (σ:ℂ)‖)
      ≤ 2 * (C₆ * Real.log (2 + |t|) + ‖Complex.digamma (σ:ℂ)‖ * Real.log (2 + |t|)) := by
        nlinarith
    _ ≤ (2 * (C₆ + ‖Complex.digamma (σ:ℂ)‖) + 1) * Real.log (2 + |t|) := by
        nlinarith [norm_nonneg (Complex.digamma (σ:ℂ))]

end DedekindResidue
