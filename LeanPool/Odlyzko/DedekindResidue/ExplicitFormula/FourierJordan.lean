/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import LeanPool.Odlyzko.DedekindResidue.ExplicitFormula.PrimeSide
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import LeanPool.Odlyzko.DedekindResidue.ExplicitFormula.PhiTransform

/-!
# Fourier–Jordan inversion: the Dirichlet integral (SP2-FJ-c)

The classical Dirichlet integral `∫₀^∞ (sin x)/x dx = π/2`, phrased as convergence of the
truncated integrals `∫₀^b (sin x)/x dx → π/2` as `b → ∞`. This is the analytic engine of
Jordan's pointwise Fourier-inversion criterion for functions of bounded variation, used in
Poitou's proof of the explicit formula (Poitou, *Sur les petits discriminants*, Séminaire
DPP 1976/77, exposé 6, p. 6-03) to invert the transform `Φ` on the prime side.

Not available in mathlib. We follow the Frullani/Fubini route:
`1/x = ∫₀^∞ e^{-xy} dy`, so
`∫₀^b (sin x)/x dx = ∫₀^∞ (1 - e^{-yb}(cos y + y sin b))/(1+y²) dy`
by Fubini and the closed form of the damped sine integral; dominated convergence then gives
the limit `∫₀^∞ dy/(1+y²) = π/2`.

## Main results

- `hasDerivAt_exp_sin_primitive`, `integral_exp_neg_mul_sin`: closed form of
  `∫₀^b e^{-yx} sin x dx`.
- `integral_exp_neg_mul_Ioi`: `∫₀^∞ e^{-xy} dy = 1/x`.
- `integral_sinc_eq`: the Fubini identity for the truncated Dirichlet integral.
- `tendsto_integral_sinc_atTop`: `∫₀^b (sin x)/x dx → π/2`.
-/

@[expose] public section


namespace DedekindResidue

open MeasureTheory Complex intervalIntegral Real Filter

/-- Antiderivative for the damped sine: `d/dt [-e^{-yt}(cos t + y sin t)/(1+y²)]
= e^{-yt} sin t`. -/
theorem hasDerivAt_exp_sin_primitive (y x : ℝ) :
    HasDerivAt (fun t : ℝ =>
      -(Real.exp (-(y*t)) * (Real.cos t + y * Real.sin t)) / (1 + y^2))
      (Real.exp (-(y*x)) * Real.sin x) x := by
  have h0 : HasDerivAt (fun t : ℝ => y*t) y x := by
    simpa using (hasDerivAt_id x).const_mul y
  have h1 : HasDerivAt (fun t : ℝ => -(y*t)) (-y) x := h0.neg
  have hexp := h1.exp
  have htrig : HasDerivAt (fun t : ℝ => Real.cos t + y * Real.sin t)
      (-Real.sin x + y * Real.cos x) x :=
    (Real.hasDerivAt_cos x).add ((Real.hasDerivAt_sin x).const_mul y)
  have hmul := hexp.mul htrig
  have hfull := (hmul.neg).div_const (1 + y^2)
  have hy2 : (1 + y^2) ≠ 0 := by positivity
  have hval : -(Real.exp (-(y*x)) * -y * (Real.cos x + y * Real.sin x)
      + Real.exp (-(y*x)) * (-Real.sin x + y * Real.cos x)) / (1 + y^2)
      = Real.exp (-(y*x)) * Real.sin x := by
    rw [div_eq_iff hy2]
    ring
  rwa [hval] at hfull

/-- Closed form of the damped sine integral. -/
theorem integral_exp_neg_mul_sin (y b : ℝ) :
    ∫ x in (0:ℝ)..b, Real.exp (-(y*x)) * Real.sin x
      = (1 - Real.exp (-(y*b)) * (Real.cos b + y * Real.sin b)) / (1 + y^2) := by
  have hint : IntervalIntegrable (fun x : ℝ => Real.exp (-(y*x)) * Real.sin x)
      volume 0 b := by
    refine ContinuousOn.intervalIntegrable ?_
    fun_prop
  have := integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => -(Real.exp (-(y*t)) * (Real.cos t + y * Real.sin t)) / (1 + y^2))
    (fun x _ => hasDerivAt_exp_sin_primitive y x) hint
  rw [this]
  simp only [mul_zero, neg_zero, Real.exp_zero, Real.cos_zero, Real.sin_zero,
    add_zero, mul_one]
  ring

/-- The inner exponential integral: `∫_{y>0} e^{-xy} dy = 1/x` for `x > 0`. -/
theorem integral_exp_neg_mul_Ioi {x : ℝ} (hx : 0 < x) :
    ∫ y in Set.Ioi (0:ℝ), Real.exp (-(x*y)) = 1/x := by
  have hderiv : ∀ t ∈ Set.Ici (0:ℝ),
      HasDerivAt (fun y : ℝ => -Real.exp (-(x*y)) / x) (Real.exp (-(x*t))) t := by
    intro t _
    have h0 : HasDerivAt (fun y : ℝ => x*y) x t := by
      simpa using (hasDerivAt_id t).const_mul x
    have h1 : HasDerivAt (fun y : ℝ => -(x*y)) (-x) t := h0.neg
    have h2 := (h1.exp.neg).div_const x
    have hval : -(Real.exp (-(x*t)) * -x) / x = Real.exp (-(x*t)) := by
      rw [div_eq_iff hx.ne']
      ring
    rwa [hval] at h2
  have hint : IntegrableOn (fun y : ℝ => Real.exp (-(x*y))) (Set.Ioi 0) := by
    have := exp_neg_integrableOn_Ioi (0:ℝ) hx
    refine this.congr_fun (fun y _ => ?_) measurableSet_Ioi
    ring_nf
  have htend : Tendsto (fun y : ℝ => -Real.exp (-(x*y)) / x) atTop (nhds 0) := by
    have h1 : Tendsto (fun y : ℝ => -(x*y)) atTop atBot := by
      refine Filter.tendsto_neg_atBot_iff.mpr ?_
      exact Tendsto.const_mul_atTop hx tendsto_id
    have h2 := (Real.tendsto_exp_atBot.comp h1).neg
    have h3 := h2.div_const x
    simpa using h3
  have := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  rw [this, mul_zero, neg_zero, Real.exp_zero]
  rw [zero_sub, neg_div, neg_neg, one_div]



/-- **The Fubini step of the Dirichlet integral**: for `b > 0`,
`∫₀^b sin x/x dx = ∫_{y>0} (1 − e^{-yb}(cos b + y sin b))/(1+y²) dy`. -/
theorem integral_sinc_eq {b : ℝ} (hb : 0 < b) :
    (∫ x in (0:ℝ)..b, Real.sin x / x)
      = ∫ y in Set.Ioi (0:ℝ),
          (1 - Real.exp (-(y*b)) * (Real.cos b + y * Real.sin b)) / (1 + y^2) := by
  -- joint integrability on Ioc 0 b × Ioi 0
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun x y => Real.sin x * Real.exp (-(x*y)))
      ((volume.restrict (Set.Ioc (0:ℝ) b)).prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    refine Continuous.aestronglyMeasurable ?_
    fun_prop
  have hint_slice : ∀ x ∈ Set.Ioc (0:ℝ) b,
      Integrable (fun y => Real.sin x * Real.exp (-(x*y)))
        (volume.restrict (Set.Ioi (0:ℝ))) := by
    intro x hx
    refine Integrable.const_mul ?_ _
    have := exp_neg_integrableOn_Ioi (0:ℝ) hx.1
    refine (this.congr_fun (fun y _ => ?_) measurableSet_Ioi)
    simp only
    rw [show -x * y = -(x*y) by ring]
  have hnorm_int : ∀ x ∈ Set.Ioc (0:ℝ) b,
      (∫ y in Set.Ioi (0:ℝ), ‖Real.sin x * Real.exp (-(x*y))‖) ≤ 1 := by
    intro x hx
    have hval : (∫ y in Set.Ioi (0:ℝ), ‖Real.sin x * Real.exp (-(x*y))‖)
        = |Real.sin x| * (1/x) := by
      rw [show (fun y => ‖Real.sin x * Real.exp (-(x*y))‖)
          = fun y => |Real.sin x| * Real.exp (-(x*y)) from funext (fun y => by
            rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.abs_exp])]
      rw [MeasureTheory.integral_const_mul, integral_exp_neg_mul_Ioi hx.1]
    rw [hval]
    have h1 : |Real.sin x| ≤ |x| := Real.abs_sin_le_abs
    rw [abs_of_pos hx.1] at h1
    rw [mul_one_div]
    rw [div_le_one hx.1]
    exact h1
  have hprod : Integrable (Function.uncurry fun x y => Real.sin x * Real.exp (-(x*y)))
      ((volume.restrict (Set.Ioc (0:ℝ) b)).prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    rw [MeasureTheory.integrable_prod_iff hmeas]
    constructor
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
      exact Filter.Eventually.of_forall (fun x hx => hint_slice x hx)
    · refine MeasureTheory.Integrable.mono'
        (g := fun _ => (1:ℝ))
        (MeasureTheory.integrableOn_const (C := (1:ℝ)) (by
          rw [Real.volume_Ioc]
          exact ENNReal.ofReal_ne_top))
        ((hmeas.norm).integral_prod_right') ?_
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hnorm_int x hx
  -- pointwise kernel identity and the swap
  have hswap := MeasureTheory.integral_integral_swap hprod
  rw [intervalIntegral.integral_of_le hb.le]
  calc (∫ x in Set.Ioc (0:ℝ) b, Real.sin x / x)
      = ∫ x in Set.Ioc (0:ℝ) b,
          (∫ y in Set.Ioi (0:ℝ), Real.sin x * Real.exp (-(x*y))) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
        rw [MeasureTheory.integral_const_mul, integral_exp_neg_mul_Ioi hx.1, mul_one_div]
    _ = ∫ y in Set.Ioi (0:ℝ),
          (∫ x in Set.Ioc (0:ℝ) b, Real.sin x * Real.exp (-(x*y))) := hswap
    _ = ∫ y in Set.Ioi (0:ℝ),
          (1 - Real.exp (-(y*b)) * (Real.cos b + y * Real.sin b)) / (1 + y^2) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
        rw [← intervalIntegral.integral_of_le hb.le]
        rw [show (fun x => Real.sin x * Real.exp (-(x*y)))
            = fun x => Real.exp (-(y*x)) * Real.sin x from funext (fun x => by
              rw [mul_comm x y]; ring)]
        exact integral_exp_neg_mul_sin y b

/-- **The Dirichlet integral** (SP2-FJ-c): `∫₀^∞ sin x/x dx = π/2`, as a limit of the
truncated integrals. Fubini against `1/x = ∫ e^{-xy} dy` plus dominated convergence. -/
theorem tendsto_integral_sinc_atTop :
    Filter.Tendsto (fun b : ℝ => ∫ x in (0:ℝ)..b, Real.sin x / x)
      atTop (nhds (π/2)) := by
  have hval : (π/2 : ℝ) = ∫ y in Set.Ioi (0:ℝ), (1 + y^2)⁻¹ := by
    rw [integral_Ioi_inv_one_add_sq]
    simp
  rw [hval]
  have hev : (fun b : ℝ => ∫ x in (0:ℝ)..b, Real.sin x / x)
      =ᶠ[atTop] (fun b => ∫ y in Set.Ioi (0:ℝ),
        (1 - Real.exp (-(y*b)) * (Real.cos b + y * Real.sin b)) / (1 + y^2)) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with b hb
    exact integral_sinc_eq hb
  rw [Filter.tendsto_congr' hev]
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun y => (1 + (1+y) * Real.exp (-y)) / (1 + y^2)) ?_ ?_ ?_ ?_
  · refine Filter.Eventually.of_forall (fun b => ?_)
    refine Continuous.aestronglyMeasurable ?_
    have h2 : ∀ y : ℝ, (1 + y^2) ≠ 0 := fun y => by positivity
    fun_prop (disch := exact h2)
  · filter_upwards [Filter.eventually_ge_atTop 1] with b hb
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    rw [Set.mem_Ioi] at hy
    have hy2 : (0:ℝ) < 1 + y^2 := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hy2]
    refine div_le_div_of_nonneg_right ?_ hy2.le
    have htrig : |Real.cos b + y * Real.sin b| ≤ 1 + y := by
      calc |Real.cos b + y * Real.sin b|
          ≤ |Real.cos b| + |y * Real.sin b| := abs_add_le _ _
        _ ≤ 1 + y := by
            have h1 := Real.abs_cos_le_one b
            have h2 := Real.abs_sin_le_one b
            rw [abs_mul, abs_of_pos hy]
            nlinarith [abs_nonneg (Real.sin b)]
    have hexp : Real.exp (-(y*b)) ≤ Real.exp (-y) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    calc |1 - Real.exp (-(y*b)) * (Real.cos b + y * Real.sin b)|
        ≤ 1 + Real.exp (-(y*b)) * |Real.cos b + y * Real.sin b| := by
          have h0 := norm_sub_le (1:ℝ)
            (Real.exp (-(y*b)) * (Real.cos b + y * Real.sin b))
          simp only [Real.norm_eq_abs, abs_one] at h0
          rw [abs_mul, Real.abs_exp] at h0
          exact h0
      _ ≤ 1 + (1+y) * Real.exp (-y) := by
          have h1 : Real.exp (-(y*b)) * |Real.cos b + y * Real.sin b|
              ≤ Real.exp (-y) * (1+y) := by
            refine mul_le_mul hexp htrig (abs_nonneg _) (Real.exp_pos _).le
          linarith
  · -- the dominating function is integrable
    have hint1 : IntegrableOn (fun y : ℝ => (1+y^2)⁻¹) (Set.Ioi 0) :=
      integrable_inv_one_add_sq.integrableOn
    have hint2 : IntegrableOn (fun y : ℝ => Real.exp (-y)) (Set.Ioi 0) := by
      have := exp_neg_integrableOn_Ioi (0:ℝ) (by norm_num : (0:ℝ) < 1)
      refine this.congr_fun (fun y _ => ?_) measurableSet_Ioi
      show Real.exp (-1 * y) = Real.exp (-y)
      rw [neg_one_mul]
    have hint3 : IntegrableOn (fun y : ℝ => 2 * Real.exp (-(y/2))) (Set.Ioi 0) := by
      have h0 := exp_neg_integrableOn_Ioi (0:ℝ) (by norm_num : (0:ℝ) < 1/2)
      have h1 : IntegrableOn (fun y : ℝ => Real.exp (-(y/2))) (Set.Ioi 0) := by
        refine h0.congr_fun (fun y _ => ?_) measurableSet_Ioi
        show Real.exp (-(1/2) * y) = Real.exp (-(y/2))
        rw [show (-(1/2) * y : ℝ) = -(y/2) by ring]
      exact h1.const_mul 2
    refine MeasureTheory.Integrable.mono' ((hint1.add hint2).add hint3) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      have h2 : ∀ y : ℝ, (1 + y^2) ≠ 0 := fun y => by positivity
      fun_prop (disch := exact h2)
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      rw [Set.mem_Ioi] at hy
      have hy2 : (0:ℝ) < 1 + y^2 := by positivity
      have hy21 : (1:ℝ) ≤ 1 + y^2 := by nlinarith
      have hnn : (0:ℝ) ≤ (1 + (1+y) * Real.exp (-y)) / (1 + y^2) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have hsplit : (1 + (1+y) * Real.exp (-y)) / (1 + y^2)
          = (1+y^2)⁻¹ + ((1+y) * Real.exp (-y)) / (1+y^2) := by
        rw [add_div, one_div]
      rw [hsplit]
      have hexp_bd : ((1+y) * Real.exp (-y)) / (1+y^2) ≤ (1+y) * Real.exp (-y) := by
        rw [div_le_iff₀ hy2]
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1+y) (Real.exp_pos (-y)).le]
      have hy_exp : y * Real.exp (-y) ≤ 2 * Real.exp (-(y/2)) := by
        have h1 : y/2 + 1 ≤ Real.exp (y/2) := Real.add_one_le_exp (y/2)
        have h2 : y ≤ 2 * Real.exp (y/2) := by linarith
        calc y * Real.exp (-y) ≤ (2 * Real.exp (y/2)) * Real.exp (-y) :=
              mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
          _ = 2 * Real.exp (-(y/2)) := by
              rw [mul_assoc, ← Real.exp_add]
              ring_nf
      have hfinal : (1+y) * Real.exp (-y) ≤ Real.exp (-y) + 2 * Real.exp (-(y/2)) := by
        have : (1+y) * Real.exp (-y) = Real.exp (-y) + y * Real.exp (-y) := by ring
        rw [this]
        linarith
      calc (1+y^2)⁻¹ + ((1+y) * Real.exp (-y)) / (1+y^2)
          ≤ (1+y^2)⁻¹ + (1+y) * Real.exp (-y) := by linarith
        _ ≤ (1+y^2)⁻¹ + (Real.exp (-y) + 2 * Real.exp (-(y/2))) := by linarith
        _ = (fun y : ℝ => (1+y^2)⁻¹) y + (fun y : ℝ => Real.exp (-y)) y
            + (fun y : ℝ => 2 * Real.exp (-(y/2))) y := by
            simp only
            ring
  · -- pointwise limits
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    rw [Set.mem_Ioi] at hy
    have h0 : Filter.Tendsto
        (fun b : ℝ => Real.exp (-(y*b)) * (Real.cos b + y * Real.sin b))
        atTop (nhds 0) := by
      refine squeeze_zero_norm (a := fun b => (1+y) * Real.exp (-(y*b))) (fun b => ?_) ?_
      · rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
        have htrig : |Real.cos b + y * Real.sin b| ≤ 1 + y := by
          calc |Real.cos b + y * Real.sin b|
              ≤ |Real.cos b| + |y * Real.sin b| := abs_add_le _ _
            _ ≤ 1 + y := by
                have h1 := Real.abs_cos_le_one b
                have h2 := Real.abs_sin_le_one b
                rw [abs_mul, abs_of_pos hy]
                nlinarith [abs_nonneg (Real.sin b)]
        calc Real.exp (-(y*b)) * |Real.cos b + y * Real.sin b|
            ≤ Real.exp (-(y*b)) * (1+y) :=
              mul_le_mul_of_nonneg_left htrig (Real.exp_pos _).le
          _ = (1+y) * Real.exp (-(y*b)) := by ring
      · have h1 : Filter.Tendsto (fun b : ℝ => -(y*b)) atTop atBot := by
          refine Filter.tendsto_neg_atBot_iff.mpr ?_
          exact Filter.Tendsto.const_mul_atTop hy Filter.tendsto_id
        have h2 := Real.tendsto_exp_atBot.comp h1
        have h3 := h2.const_mul (1+y)
        simpa using h3
    have h1 : Filter.Tendsto
        (fun b : ℝ => (1 - Real.exp (-(y*b)) * (Real.cos b + y * Real.sin b)) / (1 + y^2))
        atTop (nhds ((1 - 0) / (1 + y^2))) :=
      (Filter.Tendsto.const_sub 1 h0).div_const _
    simpa using h1

/-- The sinc function is interval integrable on every interval (it is measurable and
bounded by `1`). -/
theorem intervalIntegrable_sinc (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.sin x / x) volume a b := by
  refine intervalIntegrable_iff.mpr ?_
  have hmeas : AEStronglyMeasurable (fun x : ℝ => Real.sin x / x)
      (volume.restrict (Set.uIoc a b)) :=
    (Real.measurable_sin.div measurable_id).aestronglyMeasurable
  refine MeasureTheory.Integrable.mono'
    (g := fun _ => (1:ℝ))
    (MeasureTheory.integrableOn_const (C := (1:ℝ)) (by
      rw [Real.volume_uIoc]
      exact ENNReal.ofReal_ne_top))
    hmeas ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [Real.norm_eq_abs]
  rcases eq_or_ne x 0 with hx | hx
  · simp [hx]
  · rw [abs_div]
    exact div_le_one_of_le₀ Real.abs_sin_le_abs (abs_nonneg _)

/-- The sinc primitive is uniformly bounded on `[0, ∞)`: continuity on compacts plus
the limit `π/2` at infinity. This is the constant `C_sinc` of Poitou's Fourier–Jordan
argument (p. 6-03). -/
theorem exists_bound_primitive_sinc :
    ∃ C : ℝ, 0 < C ∧ ∀ b : ℝ, 0 ≤ b → |∫ x in (0:ℝ)..b, Real.sin x / x| ≤ C := by
  set g : ℝ → ℝ := fun b => ∫ x in (0:ℝ)..b, Real.sin x / x with hg
  have hgc : Continuous g :=
    intervalIntegral.continuous_primitive (fun a b => intervalIntegrable_sinc a b) 0
  -- eventually within 1 of π/2
  have htail := tendsto_integral_sinc_atTop.eventually
    (Metric.closedBall_mem_nhds (π/2) one_pos)
  rw [Filter.eventually_atTop] at htail
  obtain ⟨b₀, hb₀⟩ := htail
  -- bound on the compact initial segment [0, max b₀ 0]
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := (0:ℝ)) (b := max b₀ 0)).exists_bound_of_continuousOn
    hgc.continuousOn
  refine ⟨max C₀ (|π/2| + 1) + 1, by positivity, fun b hb => ?_⟩
  rcases le_or_gt b (max b₀ 0) with hble | hbgt
  · have := hC₀ b ⟨hb, hble⟩
    rw [Real.norm_eq_abs] at this
    calc |g b| ≤ C₀ := this
      _ ≤ max C₀ (|π/2| + 1) := le_max_left _ _
      _ ≤ max C₀ (|π/2| + 1) + 1 := le_add_of_nonneg_right zero_le_one
  · have hb' : b₀ ≤ b := le_trans (le_max_left _ _) hbgt.le
    have := hb₀ b hb'
    rw [Real.dist_eq] at this
    calc |g b| = |(g b - π/2) + π/2| := by ring_nf
      _ ≤ |g b - π/2| + |π/2| := abs_add_le _ _
      _ ≤ 1 + |π/2| := by gcongr
      _ = |π/2| + 1 := add_comm _ _
      _ ≤ max C₀ (|π/2| + 1) := le_max_right _ _
      _ ≤ max C₀ (|π/2| + 1) + 1 := le_add_of_nonneg_right zero_le_one

/-- **Uniform sinc-window bound `C_sinc`** (FJ-c tail corollary): a single constant
bounds `|∫_A^B sin x/x dx|` over all nonnegative windows. Used to control the
variation part of the Fourier–Jordan near-zero estimate. -/
theorem exists_bound_integral_sinc :
    ∃ C : ℝ, 0 < C ∧ ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      |∫ x in A..B, Real.sin x / x| ≤ C := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := exists_bound_primitive_sinc
  refine ⟨2 * C₀, by positivity, fun A B hA hB => ?_⟩
  have hsub : (∫ x in (0:ℝ)..B, Real.sin x / x) - ∫ x in (0:ℝ)..A, Real.sin x / x
      = ∫ x in A..B, Real.sin x / x :=
    intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_sinc 0 B) (intervalIntegrable_sinc 0 A)
  rw [← hsub]
  calc |(∫ x in (0:ℝ)..B, Real.sin x / x) - ∫ x in (0:ℝ)..A, Real.sin x / x|
      ≤ |∫ x in (0:ℝ)..B, Real.sin x / x| + |∫ x in (0:ℝ)..A, Real.sin x / x| :=
        abs_sub _ _
    _ ≤ C₀ + C₀ := add_le_add (hC₀ B hB) (hC₀ A hA)
    _ = 2 * C₀ := by ring

/-- **Sinc scaling**: `∫_v^δ sin(Tu)/u du = ∫_{Tv}^{Tδ} sin x/x dx` for `T > 0`. -/
theorem integral_sin_mul_div_eq (T v δ : ℝ) (hT : 0 < T) :
    ∫ u in v..δ, Real.sin (T * u) / u = ∫ x in (T*v)..(T*δ), Real.sin x / x := by
  have h1 : (fun u : ℝ => Real.sin (T * u) / u)
      = fun u : ℝ => T • ((fun x : ℝ => Real.sin x / x) (T * u)) := by
    funext u
    rcases eq_or_ne u 0 with hu | hu
    · simp [hu]
    · rw [smul_eq_mul]
      show Real.sin (T * u) / u = T * (Real.sin (T * u) / (T * u))
      field_simp
  rw [h1, intervalIntegral.integral_smul]
  have h2 := intervalIntegral.integral_comp_mul_left (a := v) (b := δ) (c := T)
    (fun x => Real.sin x / x) hT.ne'
  rw [h2, smul_smul, mul_inv_cancel₀ hT.ne', one_smul]

/-- The scaled sinc window is uniformly bounded: with `C_sinc` from
`exists_bound_integral_sinc`, `|∫_v^δ sin(Tu)/u du| ≤ C` for all `0 ≤ v, δ` and `T > 0`. -/
theorem exists_bound_integral_sin_mul_div :
    ∃ C : ℝ, 0 < C ∧ ∀ T v δ : ℝ, 0 < T → 0 ≤ v → 0 ≤ δ →
      |∫ u in v..δ, Real.sin (T * u) / u| ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := exists_bound_integral_sinc
  refine ⟨C, hCpos, fun T v δ hT hv hδ => ?_⟩
  rw [integral_sin_mul_div_eq T v δ hT]
  exact hC (T*v) (T*δ) (by positivity) (by positivity)

/-- **FJ-e, plateau limit**: `∫_0^δ sin(Tu)/u du → π/2` as `T → ∞`, for fixed `δ > 0`. -/
theorem tendsto_integral_sin_mul_div_atTop {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun T : ℝ => ∫ u in (0:ℝ)..δ, Real.sin (T * u) / u)
      atTop (nhds (π/2)) := by
  have hev : (fun T : ℝ => ∫ u in (0:ℝ)..δ, Real.sin (T * u) / u)
      =ᶠ[atTop] fun T : ℝ => ∫ x in (0:ℝ)..(T*δ), Real.sin x / x := by
    filter_upwards [Filter.eventually_gt_atTop 0] with T hT
    rw [integral_sin_mul_div_eq T 0 δ hT, mul_zero]
  rw [Filter.tendsto_congr' hev]
  have hcomp : Tendsto (fun T : ℝ => T * δ) atTop atTop :=
    Filter.Tendsto.atTop_mul_const hδ Filter.tendsto_id
  exact tendsto_integral_sinc_atTop.comp hcomp

/-- The symmetric complex-exponential window integral: for `u ≠ 0`,
`∫_{-T}^{T} e^{itu} dt = 2 sin(Tu)/u`. -/
theorem integral_cexp_window {u : ℝ} (hu : u ≠ 0) (T : ℝ) :
    ∫ t : ℝ in (-T)..T, Complex.exp ((t : ℂ) * (u : ℂ) * Complex.I)
      = ((2 * Real.sin (T * u) / u : ℝ) : ℂ) := by
  have hu' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu
  have hc : ((u : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero hu' Complex.I_ne_zero
  have h1 : (fun t : ℝ => Complex.exp ((t : ℂ) * (u : ℂ) * Complex.I))
      = fun t : ℝ => Complex.exp (((u : ℂ) * Complex.I) * (t : ℝ)) := by
    funext t
    ring_nf
  rw [h1, integral_exp_mul_complex hc]
  rw [div_eq_iff hc]
  have hz : (u:ℂ) * Complex.I * (T:ℂ) = ((T:ℂ) * (u:ℂ)) * Complex.I := by ring
  have hz' : (u:ℂ) * Complex.I * ((-T : ℝ):ℂ) = (-((T:ℂ) * (u:ℂ))) * Complex.I := by
    push_cast
    ring
  rw [hz, hz', Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  push_cast
  field_simp
  ring

/-- **FJ-b, kernel collapse** (Poitou p. 6-03): for integrable `H`, Fubini collapses the
symmetric Fourier window onto the Dirichlet kernel:
`∫_{-T}^{T} (∫ H(u) e^{itu} du) dt = ∫ H(u) · 2sin(Tu)/u du`. -/
theorem integral_fourier_window_collapse {H : ℝ → ℂ} (hH : Integrable H) {T : ℝ}
    (hT : 0 < T) :
    (∫ t : ℝ in (-T)..T, ∫ u : ℝ, H u * Complex.exp ((t : ℂ) * (u : ℂ) * Complex.I))
      = ∫ u : ℝ, H u * ((2 * Real.sin (T * u) / u : ℝ) : ℂ) := by
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  -- joint integrability on Ioc(-T,T) × ℝ
  have hHsnd : Integrable (fun p : ℝ × ℝ => H p.2)
      ((volume.restrict (Set.Ioc (-T) T)).prod volume) := by
    have h1 : Integrable (fun _ : ℝ => (1:ℂ)) (volume.restrict (Set.Ioc (-T) T)) :=
      MeasureTheory.integrableOn_const (by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top)
    have := h1.mul_prod hH
    simpa using this
  have hexp_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Complex.exp ((p.1 : ℂ) * (p.2 : ℂ) * Complex.I))
      ((volume.restrict (Set.Ioc (-T) T)).prod volume) := by
    refine Continuous.aestronglyMeasurable ?_
    fun_prop
  have hprod : Integrable
      (Function.uncurry fun t u : ℝ => H u * Complex.exp ((t : ℂ) * (u : ℂ) * Complex.I))
      ((volume.restrict (Set.Ioc (-T) T)).prod volume) := by
    have := hHsnd.bdd_mul (c := 1) hexp_meas ?_
    · refine this.congr (Filter.Eventually.of_forall (fun p => ?_))
      simp only [Function.uncurry]
      exact mul_comm _ _
    · refine Filter.Eventually.of_forall (fun p => ?_)
      rw [Complex.norm_exp]
      simp
  have hswap := MeasureTheory.integral_integral_swap hprod
  rw [hswap]
  -- inner integral: pull out H u, evaluate the window
  refine MeasureTheory.integral_congr_ae ?_
  have h0 : ∀ᵐ (u : ℝ), u ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
    exact MeasureTheory.measure_singleton 0
  filter_upwards [h0] with u hu
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [← intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  exact integral_cexp_window hu T

/-- Riemann–Lebesgue for the kernel `e^{-iuT}`: for (any) `G`,
`∫ G(u) e^{-iuT} du → 0` as `T → ∞`. -/
theorem tendsto_integral_mul_cexp_neg_atTop (G : ℝ → ℂ) :
    Tendsto (fun T : ℝ => ∫ u : ℝ, G u * Complex.exp (-((u:ℂ) * (T:ℂ)) * Complex.I))
      atTop (nhds 0) := by
  have hRL := Real.tendsto_integral_exp_smul_cocompact G
  have hmap : Tendsto (fun T : ℝ => T / (2*π)) atTop (Filter.cocompact ℝ) := by
    rw [cocompact_eq_atBot_atTop]
    refine Filter.Tendsto.mono_right ?_ le_sup_right
    exact Filter.tendsto_id.atTop_div_const (by positivity)
  have hcomp := hRL.comp hmap
  refine hcomp.congr (fun T => ?_)
  simp only [Function.comp_apply]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  show Real.fourierChar (-(u * (T / (2*π)))) • G u = G u * Complex.exp (-((u:ℂ) * (T:ℂ)) * Complex.I)
  rw [Circle.smul_def, Real.fourierChar_apply]
  have hreal : 2 * π * -(u * (T / (2 * π))) = -(u * T) := by
    have hpi : (2:ℝ) * π ≠ 0 := by positivity
    field_simp
  rw [hreal]
  push_cast
  exact mul_comm _ _

/-- Riemann–Lebesgue for the kernel `e^{+iuT}`: the sign-reflected companion of
`tendsto_integral_mul_cexp_neg_atTop`, via the change of variables `u ↦ -u`. -/
theorem tendsto_integral_mul_cexp_pos_atTop (G : ℝ → ℂ) :
    Tendsto (fun T : ℝ => ∫ u : ℝ, G u * Complex.exp ((u:ℂ) * (T:ℂ) * Complex.I))
      atTop (nhds 0) := by
  refine (tendsto_integral_mul_cexp_neg_atTop (fun u => G (-u))).congr (fun T => ?_)
  rw [← integral_comp_neg_real (fun u => G u * Complex.exp ((u:ℂ) * (T:ℂ) * Complex.I))]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  show G (-u) * Complex.exp (-((u:ℂ) * (T:ℂ)) * Complex.I)
      = G (-u) * Complex.exp (((-u : ℝ) : ℂ) * (T:ℂ) * Complex.I)
  rw [show (((-u : ℝ) : ℂ) * (T:ℂ) * Complex.I) = -((u:ℂ) * (T:ℂ)) * Complex.I by
    push_cast; ring]

/-- **FJ-d, Riemann–Lebesgue with the sine kernel**: for integrable `G`,
`∫ G(u)·sin(Tu) du → 0` as `T → ∞`. Applied away from `u = 0` (to `G = H(u)/u` on
`|u| ≥ δ`) in the Fourier–Jordan argument. -/
theorem tendsto_integral_mul_sin_atTop {G : ℝ → ℂ} (hG : Integrable G) :
    Tendsto (fun T : ℝ => ∫ u : ℝ, G u * ((Real.sin (T * u) : ℝ) : ℂ))
      atTop (nhds 0) := by
  have hplus := tendsto_integral_mul_cexp_pos_atTop G
  have hminus := tendsto_integral_mul_cexp_neg_atTop G
  have hdiff := (hplus.sub hminus).div_const (2 * Complex.I)
  rw [sub_zero, zero_div] at hdiff
  refine hdiff.congr (fun T => ?_)
  have hexp_p : AEStronglyMeasurable
      (fun u : ℝ => Complex.exp ((u:ℂ) * (T:ℂ) * Complex.I)) volume := by
    refine Continuous.aestronglyMeasurable ?_
    fun_prop
  have hexp_m : AEStronglyMeasurable
      (fun u : ℝ => Complex.exp (-((u:ℂ) * (T:ℂ)) * Complex.I)) volume := by
    refine Continuous.aestronglyMeasurable ?_
    fun_prop
  have hint_p : Integrable (fun u : ℝ => G u * Complex.exp ((u:ℂ) * (T:ℂ) * Complex.I)) := by
    have h1 := hG.bdd_mul (c := 1) hexp_p (Filter.Eventually.of_forall (fun u => by
      simp [Complex.norm_exp]))
    refine h1.congr (Filter.Eventually.of_forall (fun u => ?_))
    exact mul_comm _ _
  have hint_m : Integrable
      (fun u : ℝ => G u * Complex.exp (-((u:ℂ) * (T:ℂ)) * Complex.I)) := by
    have h1 := hG.bdd_mul (c := 1) hexp_m (Filter.Eventually.of_forall (fun u => by
      simp [Complex.norm_exp]))
    refine h1.congr (Filter.Eventually.of_forall (fun u => ?_))
    exact mul_comm _ _
  rw [← MeasureTheory.integral_sub hint_p hint_m, ← MeasureTheory.integral_div]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  show (G u * Complex.exp ((u:ℂ) * (T:ℂ) * Complex.I)
        - G u * Complex.exp (-((u:ℂ) * (T:ℂ)) * Complex.I)) / (2 * Complex.I)
      = G u * ((Real.sin (T * u) : ℝ) : ℂ)
  rw [show ((Real.sin (T * u) : ℝ) : ℂ) = Complex.sin ((u:ℂ) * (T:ℂ)) by
    push_cast
    rw [mul_comm]]
  rw [show Complex.sin ((u:ℂ) * (T:ℂ))
      = ((Complex.exp (-((u:ℂ) * (T:ℂ)) * Complex.I)
          - Complex.exp (((u:ℂ) * (T:ℂ)) * Complex.I)) * Complex.I) / 2 from rfl]
  have hIne : (2 : ℂ) * Complex.I ≠ 0 := by
    simp [Complex.I_ne_zero]
  field_simp
  rw [Complex.I_sq]
  ring

/-- **FJ-f core, Stieltjes–Fubini kernel bound**: for `g` monotone and a kernel `K`
whose windows `∫_v^δ K` are uniformly bounded by `C`, the right-continuous modification
`ḡ = rightLim g` satisfies
`|∫_0^δ (ḡ(u) - ḡ(0))·K(u) du| ≤ C·(ḡ(δ) - ḡ(0))`.

Proof: `ḡ(u) - ḡ(0) = μ((0,u])` for the Lebesgue–Stieltjes measure `μ` of `g`; Fubini on
the triangle `{0 < v ≤ u ≤ δ}` turns the left side into `∫_{(0,δ]} (∫_v^δ K) dμ(v)`,
bounded by `C·μ((0,δ])`. This is the engine of Jordan's near-zero variation estimate
(Poitou p. 6-03). -/
theorem abs_integral_stieltjes_kernel_le {g K : ℝ → ℝ} (hg : Monotone g) {δ C : ℝ}
    (hδ : 0 < δ) (hKmeas : Measurable K)
    (hK : IntervalIntegrable K volume 0 δ)
    (hwin : ∀ v ∈ Set.Icc (0:ℝ) δ, |∫ u in v..δ, K u| ≤ C) :
    |∫ u in (0:ℝ)..δ, (Function.rightLim g u - Function.rightLim g 0) * K u|
      ≤ C * (Function.rightLim g δ - Function.rightLim g 0) := by
  classical
  set F := hg.stieltjesFunction with hF
  have hFeq : ∀ x, F x = Function.rightLim g x := fun x => hg.stieltjesFunction_eq x
  set μ := F.measure with hμ
  set μ' := μ.restrict (Set.Ioc 0 δ) with hμ'
  -- the window measure is finite, with total mass ḡ(δ) - ḡ(0)
  have hmass : μ (Set.Ioc 0 δ) = ENNReal.ofReal (Function.rightLim g δ - Function.rightLim g 0) := by
    rw [hμ, F.measure_Ioc, hFeq, hFeq]
  have hmono : Function.rightLim g 0 ≤ Function.rightLim g δ := hg.rightLim hδ.le
  have : IsFiniteMeasure μ' := by
    constructor
    rw [hμ', Measure.restrict_apply_univ, hmass]
    exact ENNReal.ofReal_lt_top
  have hmass' : μ'.real Set.univ = Function.rightLim g δ - Function.rightLim g 0 := by
    rw [measureReal_def, hμ', Measure.restrict_apply_univ, hmass,
      ENNReal.toReal_ofReal (by linarith)]
  -- the mass representation on (0, δ]
  have hrep : ∀ u ∈ Set.Ioc (0:ℝ) δ,
      Function.rightLim g u - Function.rightLim g 0 = (μ (Set.Ioc 0 u)).toReal := by
    intro u hu
    rw [hμ, F.measure_Ioc, hFeq, hFeq,
      ENNReal.toReal_ofReal (by
        have := hg.rightLim hu.1.le
        linarith)]
  -- the triangle integrand
  set ψ : ℝ × ℝ → ℝ := fun p => if p.2 ≤ p.1 then K p.1 else 0 with hψ
  have hψmeas : Measurable ψ := by
    refine Measurable.ite ?_ (hKmeas.comp measurable_fst) measurable_const
    exact measurableSet_le measurable_snd measurable_fst
  -- inner evaluation in v (u fixed): mass of Ioc 0 u times K u
  have hinner : ∀ u ∈ Set.Ioc (0:ℝ) δ,
      (∫ v, ψ (u, v) ∂μ') = (μ (Set.Ioc 0 u)).toReal * K u := by
    intro u hu
    have h1 : (fun v => ψ (u, v)) = Set.indicator (Set.Iic u) (fun _ => K u) := by
      funext v
      rw [hψ]
      simp only [Set.indicator_apply, Set.mem_Iic]
    rw [h1, MeasureTheory.integral_indicator measurableSet_Iic,
      MeasureTheory.setIntegral_const, smul_eq_mul]
    have h2 : μ' (Set.Iic u) = μ (Set.Ioc 0 u) := by
      rw [hμ', Measure.restrict_apply measurableSet_Iic, Set.inter_comm,
        Set.Ioc_inter_Iic, min_eq_right hu.2]
    rw [measureReal_def, h2]
  -- outer evaluation in u (v fixed): the K-window from v to δ
  have houter : ∀ v ∈ Set.Ioc (0:ℝ) δ,
      (∫ u in Set.Ioc (0:ℝ) δ, ψ (u, v)) = ∫ u in v..δ, K u := by
    intro v hv
    have h1 : (fun u => ψ (u, v)) = Set.indicator (Set.Ici v) K := by
      funext u
      rw [hψ]
      simp only [Set.indicator_apply, Set.mem_Ici]
    rw [h1, MeasureTheory.integral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici]
    have h2 : Set.Ici v ∩ Set.Ioc (0:ℝ) δ = Set.Icc v δ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc, Set.mem_Icc]
      constructor
      · rintro ⟨h1', _, h3'⟩
        exact ⟨h1', h3'⟩
      · rintro ⟨h1', h2'⟩
        exact ⟨h1', lt_of_lt_of_le hv.1 h1', h2'⟩
    rw [h2, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hv.2]
  -- product integrability for the swap
  have hKint : IntegrableOn K (Set.Ioc 0 δ) := by
    have := intervalIntegrable_iff.mp hK
    rwa [Set.uIoc_of_le hδ.le] at this
  have hprod : Integrable (Function.uncurry fun u v : ℝ => ψ (u, v))
      ((volume.restrict (Set.Ioc 0 δ)).prod μ') := by
    have hmeasp : AEStronglyMeasurable (Function.uncurry fun u v : ℝ => ψ (u, v))
        ((volume.restrict (Set.Ioc 0 δ)).prod μ') := by
      have : (Function.uncurry fun u v : ℝ => ψ (u, v)) = ψ := by
        funext p
        rw [Function.uncurry]
      rw [this]
      exact hψmeas.aestronglyMeasurable
    refine (MeasureTheory.integrable_prod_iff hmeasp).mpr ⟨?_, ?_⟩
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
      refine Filter.Eventually.of_forall (fun u _ => ?_)
      simp only [Function.uncurry_apply_pair]
      have h1 : (fun v => ψ (u, v)) = Set.indicator (Set.Iic u) (fun _ => K u) := by
        funext v
        rw [hψ]
        simp only [Set.indicator_apply, Set.mem_Iic]
      rw [h1]
      exact (MeasureTheory.integrable_const (K u)).indicator measurableSet_Iic
    · -- the norm-outer function is dominated by |K|·mass
      refine MeasureTheory.Integrable.mono'
        (g := fun u => |K u| * μ'.real Set.univ)
        (hKint.norm.mul_const _) ?_ ?_
      · exact (hmeasp.norm).integral_prod_right'
      · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
        refine Filter.Eventually.of_forall (fun u _ => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        simp only [Function.uncurry_apply_pair]
        calc ∫ v, ‖ψ (u, v)‖ ∂μ'
            ≤ ∫ _, |K u| ∂μ' := by
              refine MeasureTheory.integral_mono_of_nonneg
                (Filter.Eventually.of_forall (fun v => norm_nonneg _))
                (MeasureTheory.integrable_const _)
                (Filter.Eventually.of_forall (fun v => ?_))
              show ‖if v ≤ u then K u else 0‖ ≤ |K u|
              rw [Real.norm_eq_abs]
              split
              · exact le_refl _
              · simp
          _ = |K u| * μ'.real Set.univ := by
              rw [MeasureTheory.integral_const, smul_eq_mul, mul_comm]
  -- Fubini
  have hswap := MeasureTheory.integral_integral_swap hprod
  -- assemble: LHS as the double integral
  rw [intervalIntegral.integral_of_le hδ.le]
  have hLHS : (∫ u in Set.Ioc (0:ℝ) δ,
      (Function.rightLim g u - Function.rightLim g 0) * K u)
      = ∫ u in Set.Ioc (0:ℝ) δ, ∫ v, ψ (u, v) ∂μ' := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
    rw [hinner u hu, hrep u hu]
  rw [hLHS, hswap]
  -- bound the outer Stieltjes integral
  have hbound : ∀ᵐ v ∂μ', ‖∫ u in Set.Ioc (0:ℝ) δ, ψ (u, v)‖ ≤ C := by
    rw [hμ']
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
    refine Filter.Eventually.of_forall (fun v hv => ?_)
    rw [houter v hv, Real.norm_eq_abs]
    exact hwin v ⟨hv.1.le, hv.2⟩
  calc |∫ v, (∫ u in Set.Ioc (0:ℝ) δ, ψ (u, v)) ∂μ'|
      ≤ C * μ'.real Set.univ := by
        rw [← Real.norm_eq_abs]
        exact MeasureTheory.norm_integral_le_of_norm_le_const hbound
    _ = C * (Function.rightLim g δ - Function.rightLim g 0) := by rw [hmass']

/-- Transfer of the Stieltjes kernel bound from the right-continuous modification to `g`
itself: monotone functions agree with `rightLim g` off a countable (hence null) set. -/
theorem abs_integral_monotone_kernel_le {g K : ℝ → ℝ} (hg : Monotone g) {δ C : ℝ}
    (hδ : 0 < δ) (hKmeas : Measurable K)
    (hK : IntervalIntegrable K volume 0 δ)
    (hwin : ∀ v ∈ Set.Icc (0:ℝ) δ, |∫ u in v..δ, K u| ≤ C) :
    |∫ u in (0:ℝ)..δ, (g u - Function.rightLim g 0) * K u|
      ≤ C * (Function.rightLim g δ - Function.rightLim g 0) := by
  have hcount : Set.Countable {x : ℝ | g x ≠ Function.rightLim g x} := by
    refine Set.Countable.mono ?_ hg.countable_not_continuousAt
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    intro hcont
    exact hx (hcont.continuousWithinAt.rightLim_eq).symm
  have hnull : volume {x : ℝ | g x ≠ Function.rightLim g x} = 0 :=
    hcount.measure_zero _
  have hae : ∀ᵐ x : ℝ, g x = Function.rightLim g x := by
    rw [MeasureTheory.ae_iff]
    simpa using hnull
  have heq : (∫ u in (0:ℝ)..δ, (g u - Function.rightLim g 0) * K u)
      = ∫ u in (0:ℝ)..δ, (Function.rightLim g u - Function.rightLim g 0) * K u := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with x hx _
    rw [hx]
  rw [heq]
  exact abs_integral_stieltjes_kernel_le hg hδ hKmeas hK hwin

/-- Pointwise bound for a monotone function on a window: `|p u - c| ≤ max |p a - c| |p b - c|`
for `u ∈ [a, b]`. -/
theorem abs_monotone_sub_le {p : ℝ → ℝ} (hp : Monotone p) {a b u c : ℝ}
    (hu : u ∈ Set.Icc a b) : |p u - c| ≤ max (|p a - c|) (|p b - c|) := by
  rcases le_or_gt c (p u) with h | h
  · rw [abs_of_nonneg (by linarith)]
    refine le_max_of_le_right ?_
    have h2 : p u ≤ p b := hp hu.2
    calc p u - c ≤ p b - c := by linarith
      _ ≤ |p b - c| := le_abs_self _
  · rw [abs_of_neg (by linarith)]
    refine le_max_of_le_left ?_
    have h2 : p a ≤ p u := hp hu.1
    calc -(p u - c) = c - p u := by ring
      _ ≤ c - p a := by linarith
      _ ≤ |p a - c| := by
          rw [abs_sub_comm]
          exact le_abs_self _

/-- The product of a monotone-difference factor and an interval-integrable kernel is
interval integrable. -/
theorem intervalIntegrable_monotone_sub_mul {p K : ℝ → ℝ} (hp : Monotone p) {δ c : ℝ}
    (hδ : 0 < δ) (hK : IntervalIntegrable K volume 0 δ) :
    IntervalIntegrable (fun u => (p u - c) * K u) volume 0 δ := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hδ.le] at hK ⊢
  refine MeasureTheory.Integrable.bdd_mul (c := max (|p 0 - c|) (|p δ - c|)) hK ?_ ?_
  · exact ((hp.measurable.sub measurable_const).aestronglyMeasurable).restrict
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    rw [Real.norm_eq_abs]
    exact abs_monotone_sub_le hp ⟨hu.1.le, hu.2⟩

/-- **FJ-f, difference-of-monotone form**: the near-zero kernel bound for a function of
bounded variation presented as a difference `p - q` of monotone functions, right limits
taken at `0`. The bound is `C` times the sum of the two monotone increments — the
variation bound of Jordan's argument (Poitou p. 6-03). -/
theorem abs_integral_monotone_sub_kernel_le {p q K : ℝ → ℝ}
    (hp : Monotone p) (hq : Monotone q) {δ C : ℝ}
    (hδ : 0 < δ) (hKmeas : Measurable K)
    (hK : IntervalIntegrable K volume 0 δ)
    (hwin : ∀ v ∈ Set.Icc (0:ℝ) δ, |∫ u in v..δ, K u| ≤ C) :
    |∫ u in (0:ℝ)..δ,
        ((p u - q u) - (Function.rightLim p 0 - Function.rightLim q 0)) * K u|
      ≤ C * ((Function.rightLim p δ - Function.rightLim p 0)
          + (Function.rightLim q δ - Function.rightLim q 0)) := by
  have hsplit : (∫ u in (0:ℝ)..δ,
      ((p u - q u) - (Function.rightLim p 0 - Function.rightLim q 0)) * K u)
      = (∫ u in (0:ℝ)..δ, (p u - Function.rightLim p 0) * K u)
        - ∫ u in (0:ℝ)..δ, (q u - Function.rightLim q 0) * K u := by
    rw [← intervalIntegral.integral_sub
      (intervalIntegrable_monotone_sub_mul hp hδ hK)
      (intervalIntegrable_monotone_sub_mul hq hδ hK)]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    ring
  rw [hsplit]
  calc |(∫ u in (0:ℝ)..δ, (p u - Function.rightLim p 0) * K u)
        - ∫ u in (0:ℝ)..δ, (q u - Function.rightLim q 0) * K u|
      ≤ |∫ u in (0:ℝ)..δ, (p u - Function.rightLim p 0) * K u|
        + |∫ u in (0:ℝ)..δ, (q u - Function.rightLim q 0) * K u| := abs_sub _ _
    _ ≤ C * (Function.rightLim p δ - Function.rightLim p 0)
        + C * (Function.rightLim q δ - Function.rightLim q 0) :=
        add_le_add (abs_integral_monotone_kernel_le hp hδ hKmeas hK hwin)
          (abs_integral_monotone_kernel_le hq hδ hKmeas hK hwin)
    _ = C * ((Function.rightLim p δ - Function.rightLim p 0)
        + (Function.rightLim q δ - Function.rightLim q 0)) := by ring

/-- **FJ-g3**: the right increment of the right-continuous modification of a monotone
function vanishes as the window shrinks: `rightLim g δ - rightLim g 0 → 0` as `δ → 0+`. -/
theorem tendsto_rightLim_sub_rightLim {g : ℝ → ℝ} (hg : Monotone g) :
    Tendsto (fun δ : ℝ => Function.rightLim g δ - Function.rightLim g 0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hcont : ContinuousWithinAt hg.stieltjesFunction (Set.Ici 0) 0 :=
    hg.stieltjesFunction.right_continuous 0
  have h1 : Tendsto (fun δ : ℝ => Function.rightLim g δ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Function.rightLim g 0)) := by
    have h2 := hcont.tendsto
    have h3 : Tendsto (fun δ : ℝ => hg.stieltjesFunction δ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (hg.stieltjesFunction 0)) :=
      h2.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)
    have h4 : (fun δ : ℝ => hg.stieltjesFunction δ)
        = fun δ : ℝ => Function.rightLim g δ := by
      funext δ
      exact hg.stieltjesFunction_eq δ
    rwa [h4, hg.stieltjesFunction_eq] at h3
  have := h1.sub_const (Function.rightLim g 0)
  simpa using this

/-- The scaled Dirichlet kernel `u ↦ 2·sin(Tu)/u` is measurable. -/
theorem measurable_dirichlet_kernel (T : ℝ) :
    Measurable (fun u : ℝ => 2 * Real.sin (T * u) / u) := by
  fun_prop

/-- The scaled Dirichlet kernel is bounded by `2|T|` (since `|sin x| ≤ |x|`). -/
theorem abs_dirichlet_kernel_le (T u : ℝ) :
    |2 * Real.sin (T * u) / u| ≤ 2 * |T| := by
  rcases eq_or_ne u 0 with hu | hu
  · simp [hu]
  · rw [abs_div, abs_mul, abs_two]
    rw [div_le_iff₀ (abs_pos.mpr hu)]
    have h1 : |Real.sin (T * u)| ≤ |T * u| := Real.abs_sin_le_abs
    calc 2 * |Real.sin (T * u)| ≤ 2 * |T * u| := by linarith
      _ = 2 * |T| * |u| := by rw [abs_mul]; ring

/-- The scaled Dirichlet kernel is interval integrable on `[0, δ]`. -/
theorem intervalIntegrable_dirichlet_kernel (T δ : ℝ) :
    IntervalIntegrable (fun u : ℝ => 2 * Real.sin (T * u) / u) volume 0 δ := by
  refine intervalIntegrable_iff.mpr ?_
  refine MeasureTheory.Integrable.mono'
    (g := fun _ => 2 * |T|)
    (MeasureTheory.integrableOn_const (C := 2 * |T|) (by
      rw [Real.volume_uIoc]
      exact ENNReal.ofReal_ne_top))
    ((measurable_dirichlet_kernel T).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun u => ?_)
  rw [Real.norm_eq_abs]
  exact abs_dirichlet_kernel_le T u

/-- Windows of the scaled Dirichlet kernel are uniformly bounded (twice the sinc-window
constant), independently of `T > 0` and of the window `[v, δ] ⊆ [0, ∞)`. -/
theorem exists_bound_dirichlet_window :
    ∃ C : ℝ, 0 < C ∧ ∀ T v δ : ℝ, 0 < T → 0 ≤ v → 0 ≤ δ →
      |∫ u in v..δ, 2 * Real.sin (T * u) / u| ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := exists_bound_integral_sin_mul_div
  refine ⟨2 * C, by positivity, fun T v δ hT hv hδ => ?_⟩
  have h1 : (∫ u in v..δ, 2 * Real.sin (T * u) / u)
      = 2 * ∫ u in v..δ, Real.sin (T * u) / u := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    ring
  rw [h1, abs_mul, abs_two]
  have := hC T v δ hT hv hδ
  linarith

/-- **FJ-g2, near-zero remainder bound**: for `H` with monotone-decomposed real and
imaginary parts and `Hp` the right-limit value at `0`, the remainder integral against the
Dirichlet kernel is bounded by the window constant times the four monotone increments —
uniformly in `T`. -/
theorem norm_integral_sub_rightLim_kernel_le
    {p q r s : ℝ → ℝ} (hp : Monotone p) (hq : Monotone q)
    (hr : Monotone r) (hs : Monotone s) {H : ℝ → ℂ}
    (hre : ∀ u, (H u).re = p u - q u) (him : ∀ u, (H u).im = r u - s u)
    {Hp : ℂ} (hHpre : Hp.re = Function.rightLim p 0 - Function.rightLim q 0)
    (hHpim : Hp.im = Function.rightLim r 0 - Function.rightLim s 0)
    {C T δ : ℝ} (hδ : 0 < δ)
    (hHint : IntegrableOn H (Set.Ioc 0 δ))
    (hwin : ∀ v ∈ Set.Icc (0:ℝ) δ, |∫ u in v..δ, 2 * Real.sin (T * u) / u| ≤ C) :
    ‖∫ u in (0:ℝ)..δ, (H u - Hp) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ)‖
      ≤ C * ((Function.rightLim p δ - Function.rightLim p 0)
            + (Function.rightLim q δ - Function.rightLim q 0))
        + C * ((Function.rightLim r δ - Function.rightLim r 0)
            + (Function.rightLim s δ - Function.rightLim s 0)) := by
  -- integrability of the full integrand on the window
  have hint : IntegrableOn (fun u => (H u - Hp) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ))
      (Set.Ioc 0 δ) := by
    refine MeasureTheory.Integrable.mul_bdd (c := 2 * |T|)
      (hHint.sub (MeasureTheory.integrableOn_const (by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top))) ?_ ?_
    · exact ((Complex.measurable_ofReal.comp
        (measurable_dirichlet_kernel T)).aestronglyMeasurable).restrict
    · refine Filter.Eventually.of_forall (fun u => ?_)
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_dirichlet_kernel_le T u
  have h0 := integral_re hint
  have h0' := integral_im hint
  simp only [RCLike.re_to_complex] at h0
  simp only [RCLike.im_to_complex] at h0'
  -- the real part is the (p, q) monotone-difference integral
  have hre_val : (∫ u in (0:ℝ)..δ, (H u - Hp) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ)).re
      = ∫ u in (0:ℝ)..δ, ((p u - q u) - (Function.rightLim p 0 - Function.rightLim q 0))
          * (2 * Real.sin (T * u) / u) := by
    rw [intervalIntegral.integral_of_le hδ.le, intervalIntegral.integral_of_le hδ.le,
      ← h0]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun u _ => ?_)
    show ((H u - Hp) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ)).re = _
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.sub_re, hre u, hHpre]
  -- the imaginary part is the (r, s) monotone-difference integral
  have him_val : (∫ u in (0:ℝ)..δ, (H u - Hp) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ)).im
      = ∫ u in (0:ℝ)..δ, ((r u - s u) - (Function.rightLim r 0 - Function.rightLim s 0))
          * (2 * Real.sin (T * u) / u) := by
    rw [intervalIntegral.integral_of_le hδ.le, intervalIntegral.integral_of_le hδ.le,
      ← h0']
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun u _ => ?_)
    show ((H u - Hp) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ)).im = _
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
      Complex.sub_im, him u, hHpim]
  -- combine via ‖z‖ ≤ |re z| + |im z|
  calc ‖∫ u in (0:ℝ)..δ, (H u - Hp) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ)‖
      ≤ |(∫ u in (0:ℝ)..δ, (H u - Hp) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ)).re|
        + |(∫ u in (0:ℝ)..δ, (H u - Hp) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ C * ((Function.rightLim p δ - Function.rightLim p 0)
            + (Function.rightLim q δ - Function.rightLim q 0))
        + C * ((Function.rightLim r δ - Function.rightLim r 0)
            + (Function.rightLim s δ - Function.rightLim s 0)) := by
        rw [hre_val, him_val]
        exact add_le_add
          (abs_integral_monotone_sub_kernel_le hp hq hδ
            (measurable_dirichlet_kernel T) (intervalIntegrable_dirichlet_kernel T δ) hwin)
          (abs_integral_monotone_sub_kernel_le hr hs hδ
            (measurable_dirichlet_kernel T) (intervalIntegrable_dirichlet_kernel T δ) hwin)

/-- The Dirichlet kernel is even. -/
theorem dirichlet_kernel_neg (T u : ℝ) :
    2 * Real.sin (T * -u) / -u = 2 * Real.sin (T * u) / u := by
  rw [mul_neg, Real.sin_neg]
  rcases eq_or_ne u 0 with hu | hu
  · simp [hu]
  · rw [mul_neg, neg_div_neg_eq]

/-- Multiplying an integrable function by the Dirichlet kernel keeps it interval
integrable on the window. -/
theorem intervalIntegrable_mul_dirichlet {H : ℝ → ℂ} {δ : ℝ} (hδ : 0 < δ) (T : ℝ)
    (hHint : IntegrableOn H (Set.Ioc 0 δ)) :
    IntervalIntegrable (fun u => H u * ((2 * Real.sin (T * u) / u : ℝ) : ℂ))
      volume 0 δ := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hδ.le]
  refine MeasureTheory.Integrable.mul_bdd (c := 2 * |T|) hHint ?_ ?_
  · exact ((Complex.measurable_ofReal.comp
      (measurable_dirichlet_kernel T)).aestronglyMeasurable).restrict
  · refine Filter.Eventually.of_forall (fun u => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_dirichlet_kernel_le T u

/-- **FJ-g1, window split**: the full-line Dirichlet-kernel integral decomposes into a
far part (`|u| > δ`, plus the null point `0`) and two reflected near windows. -/
theorem integral_dirichlet_split {H : ℝ → ℂ} (hH : Integrable H) {δ : ℝ}
    (hδ : 0 < δ) (T : ℝ) :
    ∫ u : ℝ, H u * ((2 * Real.sin (T * u) / u : ℝ) : ℂ)
      = (∫ u in (Set.Ioc 0 δ ∪ Set.Ico (-δ) 0)ᶜ,
            H u * ((2 * Real.sin (T * u) / u : ℝ) : ℂ))
        + (∫ u in (0:ℝ)..δ, H u * ((2 * Real.sin (T * u) / u : ℝ) : ℂ))
        + ∫ u in (0:ℝ)..δ, H (-u) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ) := by
  set f : ℝ → ℂ := fun u => H u * ((2 * Real.sin (T * u) / u : ℝ) : ℂ) with hf
  have hfint : Integrable f := by
    refine MeasureTheory.Integrable.mul_bdd (c := 2 * |T|) hH ?_ ?_
    · exact (Complex.measurable_ofReal.comp
        (measurable_dirichlet_kernel T)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun u => ?_)
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_dirichlet_kernel_le T u
  have hmeas_union : MeasurableSet (Set.Ioc 0 δ ∪ Set.Ico (-δ) 0) :=
    measurableSet_Ioc.union measurableSet_Ico
  have hsplit1 : (∫ u in Set.Ioc 0 δ ∪ Set.Ico (-δ) 0, f u)
      + ∫ u in (Set.Ioc 0 δ ∪ Set.Ico (-δ) 0)ᶜ, f u = ∫ u : ℝ, f u :=
    MeasureTheory.integral_add_compl hmeas_union hfint
  have hdisj : Disjoint (Set.Ioc 0 δ) (Set.Ico (-δ) 0) := by
    refine Set.disjoint_left.mpr (fun u hu hu' => ?_)
    exact absurd hu.1 (not_lt.mpr hu'.2.le)
  have hsplit2 : (∫ u in Set.Ioc 0 δ ∪ Set.Ico (-δ) 0, f u)
      = (∫ u in Set.Ioc 0 δ, f u) + ∫ u in Set.Ico (-δ) 0, f u :=
    MeasureTheory.setIntegral_union hdisj measurableSet_Ico
      (hfint.integrableOn) (hfint.integrableOn)
  -- reflect the negative window
  have hreflect : (∫ u in Set.Ico (-δ) 0, f u) = ∫ u in Set.Ioc 0 δ, f (-u) := by
    have h1 : (∫ u in Set.Ico (-δ) 0, f u)
        = ∫ u : ℝ, (Set.Ico (-δ) 0).indicator f u := by
      rw [MeasureTheory.integral_indicator measurableSet_Ico]
    have h2 : (∫ u : ℝ, (Set.Ico (-δ) 0).indicator f u)
        = ∫ u : ℝ, (Set.Ico (-δ) 0).indicator f (-u) :=
      (integral_comp_neg_real ((Set.Ico (-δ) 0).indicator f)).symm
    have h3 : (fun u : ℝ => (Set.Ico (-δ) 0).indicator f (-u))
        = (Set.Ioc 0 δ).indicator (fun u => f (-u)) := by
      funext u
      simp only [Set.indicator_apply, Set.mem_Ico, Set.mem_Ioc]
      by_cases hu : -δ ≤ -u ∧ -u < 0
      · rw [if_pos hu, if_pos ⟨by linarith [hu.2], by linarith [hu.1]⟩]
      · rw [if_neg hu, if_neg (fun h => hu ⟨by linarith [h.2], by linarith [h.1]⟩)]
    rw [h1, h2, h3, MeasureTheory.integral_indicator measurableSet_Ioc]
  have hK_even : ∀ u : ℝ, f (-u) = H (-u) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ) := by
    intro u
    rw [hf]
    simp only
    rw [dirichlet_kernel_neg]
  have h4 : (∫ u in Set.Ioc (0:ℝ) δ, f (-u))
      = ∫ u in Set.Ioc (0:ℝ) δ, H (-u) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun u _ => hK_even u)
  rw [← hsplit1, hsplit2, hreflect]
  rw [intervalIntegral.integral_of_le hδ.le, intervalIntegral.integral_of_le hδ.le]
  rw [h4]
  abel

/-- **FJ-g far limit**: for fixed `δ > 0` the far part of the Dirichlet-kernel integral
vanishes as `T → ∞` (Riemann–Lebesgue applied to `H(u)·2/u` off `(-δ, δ)`). -/
theorem tendsto_integral_dirichlet_far {H : ℝ → ℂ} (hH : Integrable H) {δ : ℝ}
    (hδ : 0 < δ) :
    Tendsto (fun T : ℝ => ∫ u in (Set.Ioc 0 δ ∪ Set.Ico (-δ) 0)ᶜ,
        H u * ((2 * Real.sin (T * u) / u : ℝ) : ℂ)) atTop (nhds 0) := by
  set far := (Set.Ioc 0 δ ∪ Set.Ico (-δ) 0)ᶜ with hfar
  have hfarmeas : MeasurableSet far :=
    (measurableSet_Ioc.union measurableSet_Ico).compl
  set G : ℝ → ℂ := far.indicator (fun u => H u * ((2 / u : ℝ) : ℂ)) with hG
  -- |2/u| ≤ 2/δ on the far set
  have hfar_bound : ∀ u ∈ far, |2 / u| ≤ 2 / δ := by
    intro u hu
    rw [hfar, Set.mem_compl_iff, Set.mem_union, Set.mem_Ioc, Set.mem_Ico] at hu
    push Not at hu
    rcases lt_trichotomy u 0 with h | h | h
    · have h1 : u < -δ := by
        by_contra h2
        push Not at h2
        exact absurd h (not_lt.mpr (hu.2 h2))
      rw [abs_div, abs_two, abs_of_neg h]
      rw [div_le_div_iff₀ (by linarith) hδ]
      linarith
    · simp [h]
      positivity
    · have h1 : δ < u := by
        by_contra h2
        push Not at h2
        exact absurd (hu.1 h) (not_lt.mpr h2)
      rw [abs_div, abs_two, abs_of_pos h]
      rw [div_le_div_iff₀ (by linarith) hδ]
      linarith
  have hGint : Integrable G := by
    refine MeasureTheory.Integrable.mono' (g := fun u => (2/δ) * ‖H u‖)
      (hH.norm.const_mul _) ?_ ?_
    · refine AEStronglyMeasurable.indicator ?_ hfarmeas
      refine hH.aestronglyMeasurable.mul ?_
      exact (Complex.measurable_ofReal.comp (by fun_prop)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun u => ?_)
      rw [hG]
      rcases Set.indicator_eq_zero_or_self far (fun u => H u * ((2 / u : ℝ) : ℂ)) u
        with h | h
      · rw [h]
        simp only [norm_zero]
        positivity
      · rcases (em (u ∈ far)) with hmem | hmem
        · rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
          refine mul_le_mul (hfar_bound u hmem) (le_refl _) (norm_nonneg _)
            (by positivity)
        · rw [Set.indicator_of_notMem hmem]
          simp only [norm_zero]
          positivity
  have hRL := tendsto_integral_mul_sin_atTop hGint
  refine hRL.congr (fun T => ?_)
  rw [← MeasureTheory.integral_indicator hfarmeas]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  show G u * ((Real.sin (T * u) : ℝ) : ℂ)
      = far.indicator (fun w => H w * ((2 * Real.sin (T * w) / w : ℝ) : ℂ)) u
  rw [hG]
  rcases (em (u ∈ far)) with hmem | hmem
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    push_cast
    ring
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, zero_mul]

/-- **FJ-g plateau limit**: `∫_0^δ 2·sin(Tu)/u du → π` as `T → ∞`. -/
theorem tendsto_integral_dirichlet_plateau {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun T : ℝ => ∫ u in (0:ℝ)..δ, ((2 * Real.sin (T * u) / u : ℝ) : ℂ))
      atTop (nhds ((π : ℝ) : ℂ)) := by
  have h1 := tendsto_integral_sin_mul_div_atTop hδ
  have h2 := h1.const_mul (2:ℝ)
  have h3 : Tendsto (fun T : ℝ =>
      ((2 * ∫ u in (0:ℝ)..δ, Real.sin (T*u)/u : ℝ) : ℂ)) atTop (nhds ((π : ℝ) : ℂ)) := by
    have h4 := (Complex.continuous_ofReal.tendsto (2 * (π/2))).comp h2
    have h5 : (2 : ℝ) * (π/2) = π := by ring
    rw [h5] at h4
    exact h4
  refine h3.congr (fun T => ?_)
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  push_cast
  ring

/-- **Jordan's Fourier inversion criterion, Dirichlet-kernel form** (SP2-FJ-a/g; Poitou
p. 6-03): for integrable `H` whose real and imaginary parts have bounded variation, with
one-sided limits `Hp` (from the right) and `Hm` (from the left) at `0`,

`∫_ℝ H(u) · 2sin(Tu)/u du  →  π(Hp + Hm)`  as `T → ∞`.

The proof splits the line at `±δ`: the far part vanishes by Riemann–Lebesgue, the plateau
contributes `π·(Hp + Hm)`, and the near-zero remainders are bounded — uniformly in `T` —
by the Stieltjes window constant times the monotone increments, which vanish as `δ → 0+`. -/
theorem tendsto_integral_dirichlet_jordan {H : ℝ → ℂ} (hH : Integrable H)
    (hre : LocallyBoundedVariationOn (fun u => (H u).re) Set.univ)
    (him : LocallyBoundedVariationOn (fun u => (H u).im) Set.univ)
    {Hp Hm : ℂ}
    (hp : Tendsto H (nhdsWithin 0 (Set.Ioi 0)) (nhds Hp))
    (hm : Tendsto H (nhdsWithin 0 (Set.Iio 0)) (nhds Hm)) :
    Tendsto (fun T : ℝ => ∫ u : ℝ, H u * ((2 * Real.sin (T * u) / u : ℝ) : ℂ))
      atTop (nhds (((π : ℝ) : ℂ) * (Hp + Hm))) := by
  classical
  -- monotone decompositions of the real and imaginary parts
  obtain ⟨p, q, hpm', hqm', hpq⟩ := hre.exists_monotoneOn_sub_monotoneOn
  obtain ⟨r, s, hrm', hsm', hrs⟩ := him.exists_monotoneOn_sub_monotoneOn
  rw [monotoneOn_univ] at hpm' hqm' hrm' hsm'
  have hre_pt : ∀ u, (H u).re = p u - q u := fun u => by
    have := congrFun hpq u
    simpa using this
  have him_pt : ∀ u, (H u).im = r u - s u := fun u => by
    have := congrFun hrs u
    simpa using this
  -- reflected decompositions for the left side
  set p' : ℝ → ℝ := fun u => -(q (-u)) with hp'def
  set q' : ℝ → ℝ := fun u => -(p (-u)) with hq'def
  set r' : ℝ → ℝ := fun u => -(s (-u)) with hr'def
  set s' : ℝ → ℝ := fun u => -(r (-u)) with hs'def
  have hp'm : Monotone p' := fun a b hab => by
    simp only [hp'def, neg_le_neg_iff]
    exact hqm' (neg_le_neg hab)
  have hq'm : Monotone q' := fun a b hab => by
    simp only [hq'def, neg_le_neg_iff]
    exact hpm' (neg_le_neg hab)
  have hr'm : Monotone r' := fun a b hab => by
    simp only [hr'def, neg_le_neg_iff]
    exact hsm' (neg_le_neg hab)
  have hs'm : Monotone s' := fun a b hab => by
    simp only [hs'def, neg_le_neg_iff]
    exact hrm' (neg_le_neg hab)
  have hre'_pt : ∀ u, (H (-u)).re = p' u - q' u := fun u => by
    rw [hre_pt (-u), hp'def, hq'def]
    ring
  have him'_pt : ∀ u, (H (-u)).im = r' u - s' u := fun u => by
    rw [him_pt (-u), hr'def, hs'def]
    ring
  -- one-sided limit identities via right limits of the monotone parts
  have hHp_re : Hp.re = Function.rightLim p 0 - Function.rightLim q 0 := by
    have h1 : Tendsto (fun u => (H u).re) (nhdsWithin 0 (Set.Ioi 0)) (nhds Hp.re) :=
      (Complex.continuous_re.tendsto Hp).comp hp
    have h2 : Tendsto (fun u => p u - q u) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Function.rightLim p 0 - Function.rightLim q 0)) :=
      (hpm'.tendsto_rightLim 0).sub (hqm'.tendsto_rightLim 0)
    have h3 : (fun u => (H u).re) = fun u => p u - q u := funext hre_pt
    rw [h3] at h1
    exact tendsto_nhds_unique h1 h2
  have hHp_im : Hp.im = Function.rightLim r 0 - Function.rightLim s 0 := by
    have h1 : Tendsto (fun u => (H u).im) (nhdsWithin 0 (Set.Ioi 0)) (nhds Hp.im) :=
      (Complex.continuous_im.tendsto Hp).comp hp
    have h2 : Tendsto (fun u => r u - s u) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Function.rightLim r 0 - Function.rightLim s 0)) :=
      (hrm'.tendsto_rightLim 0).sub (hsm'.tendsto_rightLim 0)
    have h3 : (fun u => (H u).im) = fun u => r u - s u := funext him_pt
    rw [h3] at h1
    exact tendsto_nhds_unique h1 h2
  -- the reflected function tends to Hm from the right
  have hneg_tendsto : Tendsto (fun u : ℝ => -u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Iio 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h0 := continuous_neg.tendsto (0:ℝ)
      simp only [neg_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      simpa using hu
  have hm' : Tendsto (fun u => H (-u)) (nhdsWithin 0 (Set.Ioi 0)) (nhds Hm) :=
    hm.comp hneg_tendsto
  have hHm_re : Hm.re = Function.rightLim p' 0 - Function.rightLim q' 0 := by
    have h1 : Tendsto (fun u => (H (-u)).re) (nhdsWithin 0 (Set.Ioi 0)) (nhds Hm.re) :=
      (Complex.continuous_re.tendsto Hm).comp hm'
    have h2 : Tendsto (fun u => p' u - q' u) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Function.rightLim p' 0 - Function.rightLim q' 0)) :=
      (hp'm.tendsto_rightLim 0).sub (hq'm.tendsto_rightLim 0)
    have h3 : (fun u => (H (-u)).re) = fun u => p' u - q' u := funext hre'_pt
    rw [h3] at h1
    exact tendsto_nhds_unique h1 h2
  have hHm_im : Hm.im = Function.rightLim r' 0 - Function.rightLim s' 0 := by
    have h1 : Tendsto (fun u => (H (-u)).im) (nhdsWithin 0 (Set.Ioi 0)) (nhds Hm.im) :=
      (Complex.continuous_im.tendsto Hm).comp hm'
    have h2 : Tendsto (fun u => r' u - s' u) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Function.rightLim r' 0 - Function.rightLim s' 0)) :=
      (hr'm.tendsto_rightLim 0).sub (hs'm.tendsto_rightLim 0)
    have h3 : (fun u => (H (-u)).im) = fun u => r' u - s' u := funext him'_pt
    rw [h3] at h1
    exact tendsto_nhds_unique h1 h2
  -- window constant
  obtain ⟨Cw, hCwpos, hCw⟩ := exists_bound_dirichlet_window
  -- reflected function integrability
  have hHneg : Integrable (fun u : ℝ => H (-u)) := by
    have := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hH
    exact this
  -- the ε-argument
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose δ with all eight increments small
  have hVR : Tendsto (fun δ : ℝ =>
      Cw * ((Function.rightLim p δ - Function.rightLim p 0)
          + (Function.rightLim q δ - Function.rightLim q 0))
        + Cw * ((Function.rightLim r δ - Function.rightLim r 0)
          + (Function.rightLim s δ - Function.rightLim s 0)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h0 := (((tendsto_rightLim_sub_rightLim hpm').add
      (tendsto_rightLim_sub_rightLim hqm')).const_mul Cw).add
      (((tendsto_rightLim_sub_rightLim hrm').add
        (tendsto_rightLim_sub_rightLim hsm')).const_mul Cw)
    simpa using h0
  have hVL : Tendsto (fun δ : ℝ =>
      Cw * ((Function.rightLim p' δ - Function.rightLim p' 0)
          + (Function.rightLim q' δ - Function.rightLim q' 0))
        + Cw * ((Function.rightLim r' δ - Function.rightLim r' 0)
          + (Function.rightLim s' δ - Function.rightLim s' 0)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h0 := (((tendsto_rightLim_sub_rightLim hp'm).add
      (tendsto_rightLim_sub_rightLim hq'm)).const_mul Cw).add
      (((tendsto_rightLim_sub_rightLim hr'm).add
        (tendsto_rightLim_sub_rightLim hs'm)).const_mul Cw)
    simpa using h0
  have hδex : ∃ δ : ℝ, δ ∈ Set.Ioi (0:ℝ)
      ∧ (Cw * ((Function.rightLim p δ - Function.rightLim p 0)
          + (Function.rightLim q δ - Function.rightLim q 0))
        + Cw * ((Function.rightLim r δ - Function.rightLim r 0)
          + (Function.rightLim s δ - Function.rightLim s 0)) < ε/4)
      ∧ (Cw * ((Function.rightLim p' δ - Function.rightLim p' 0)
          + (Function.rightLim q' δ - Function.rightLim q' 0))
        + Cw * ((Function.rightLim r' δ - Function.rightLim r' 0)
          + (Function.rightLim s' δ - Function.rightLim s' 0)) < ε/4) := by
    have h1 := hVR.eventually (eventually_lt_nhds (show (0:ℝ) < ε/4 by linarith))
    have h2 := hVL.eventually (eventually_lt_nhds (show (0:ℝ) < ε/4 by linarith))
    exact (eventually_mem_nhdsWithin.and (h1.and h2)).exists.imp
      (fun δ h => ⟨h.1, h.2.1, h.2.2⟩)
  obtain ⟨δ, hδpos, hδR, hδL⟩ := hδex
  rw [Set.mem_Ioi] at hδpos
  -- T-eventualities: far part and plateau
  have hfar := tendsto_integral_dirichlet_far hH hδpos
  have hplat := tendsto_integral_dirichlet_plateau hδpos
  have hfar_ev : ∀ᶠ T in atTop, ‖∫ u in (Set.Ioc 0 δ ∪ Set.Ico (-δ) 0)ᶜ,
      H u * ((2 * Real.sin (T * u) / u : ℝ) : ℂ)‖ < ε/4 := by
    have h1 := hfar.norm
    simp only [norm_zero] at h1
    exact h1.eventually (eventually_lt_nhds (show (0:ℝ) < ε/4 by linarith))
  have hplat_ev : ∀ᶠ T in atTop,
      ‖(∫ u in (0:ℝ)..δ, ((2 * Real.sin (T * u) / u : ℝ) : ℂ)) - ((π : ℝ) : ℂ)‖
        < ε / (4 * (‖Hp + Hm‖ + 1)) := by
    have h1 := (hplat.sub_const ((π : ℝ) : ℂ)).norm
    simp only [sub_self, norm_zero] at h1
    refine h1.eventually (eventually_lt_nhds ?_)
    have : (0:ℝ) < ‖Hp + Hm‖ + 1 := by positivity
    positivity
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp
    ((hfar_ev.and hplat_ev).and (Filter.eventually_gt_atTop 0))
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨⟨hfarT, hplatT⟩, hTpos⟩ := hT₀ T hT
  -- window bound at this T
  have hwinT : ∀ v ∈ Set.Icc (0:ℝ) δ, |∫ u in v..δ, 2 * Real.sin (T * u) / u| ≤ Cw :=
    fun v hv => hCw T v δ hTpos hv.1 hδpos.le
  -- near-window integrabilities
  have hHIoc : IntegrableOn H (Set.Ioc 0 δ) := hH.integrableOn
  have hHnegIoc : IntegrableOn (fun u : ℝ => H (-u)) (Set.Ioc 0 δ) := hHneg.integrableOn
  have hconstIoc : ∀ c : ℂ, IntegrableOn (fun _ : ℝ => c) (Set.Ioc 0 δ) := fun c =>
    MeasureTheory.integrableOn_const (by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top)
  -- split off the constants on both near windows
  have hIright : (∫ u in (0:ℝ)..δ, H u * ((2 * Real.sin (T * u) / u : ℝ) : ℂ))
      = Hp * (∫ u in (0:ℝ)..δ, ((2 * Real.sin (T * u) / u : ℝ) : ℂ))
        + ∫ u in (0:ℝ)..δ, (H u - Hp) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ) := by
    have h1 : (∫ u in (0:ℝ)..δ, H u * ((2 * Real.sin (T * u) / u : ℝ) : ℂ))
        = (∫ u in (0:ℝ)..δ, Hp * ((2 * Real.sin (T * u) / u : ℝ) : ℂ))
          + ∫ u in (0:ℝ)..δ, (H u - Hp) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ) := by
      have hsubR : IntegrableOn (fun u : ℝ => H u - Hp) (Set.Ioc 0 δ) :=
        hHIoc.sub (hconstIoc Hp)
      rw [← intervalIntegral.integral_add
        (intervalIntegrable_mul_dirichlet hδpos T (hconstIoc Hp))
        (intervalIntegrable_mul_dirichlet hδpos T hsubR)]
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      ring
    rw [h1, intervalIntegral.integral_const_mul]
  have hIleft : (∫ u in (0:ℝ)..δ, H (-u) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ))
      = Hm * (∫ u in (0:ℝ)..δ, ((2 * Real.sin (T * u) / u : ℝ) : ℂ))
        + ∫ u in (0:ℝ)..δ, (H (-u) - Hm) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ) := by
    have h1 : (∫ u in (0:ℝ)..δ, H (-u) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ))
        = (∫ u in (0:ℝ)..δ, Hm * ((2 * Real.sin (T * u) / u : ℝ) : ℂ))
          + ∫ u in (0:ℝ)..δ, (H (-u) - Hm) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ) := by
      have hsubL : IntegrableOn (fun u : ℝ => H (-u) - Hm) (Set.Ioc 0 δ) :=
        hHnegIoc.sub (hconstIoc Hm)
      rw [← intervalIntegral.integral_add
        (intervalIntegrable_mul_dirichlet hδpos T (hconstIoc Hm))
        (intervalIntegrable_mul_dirichlet hδpos T hsubL)]
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      ring
    rw [h1, intervalIntegral.integral_const_mul]
  -- the two remainder bounds (uniform in T)
  have hRright : ‖∫ u in (0:ℝ)..δ, (H u - Hp) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ)‖
      ≤ Cw * ((Function.rightLim p δ - Function.rightLim p 0)
            + (Function.rightLim q δ - Function.rightLim q 0))
        + Cw * ((Function.rightLim r δ - Function.rightLim r 0)
            + (Function.rightLim s δ - Function.rightLim s 0)) :=
    norm_integral_sub_rightLim_kernel_le hpm' hqm' hrm' hsm' hre_pt him_pt
      hHp_re hHp_im hδpos hHIoc hwinT
  have hRleft : ‖∫ u in (0:ℝ)..δ, (H (-u) - Hm) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ)‖
      ≤ Cw * ((Function.rightLim p' δ - Function.rightLim p' 0)
            + (Function.rightLim q' δ - Function.rightLim q' 0))
        + Cw * ((Function.rightLim r' δ - Function.rightLim r' 0)
            + (Function.rightLim s' δ - Function.rightLim s' 0)) :=
    norm_integral_sub_rightLim_kernel_le hp'm hq'm hr'm hs'm hre'_pt him'_pt
      hHm_re hHm_im hδpos hHnegIoc hwinT
  -- the exact decomposition of the difference
  have hXY : (∫ u : ℝ, H u * ((2 * Real.sin (T * u) / u : ℝ) : ℂ))
        - ((π : ℝ) : ℂ) * (Hp + Hm)
      = (∫ u in (Set.Ioc 0 δ ∪ Set.Ico (-δ) 0)ᶜ,
            H u * ((2 * Real.sin (T * u) / u : ℝ) : ℂ))
        + (Hp + Hm) * ((∫ u in (0:ℝ)..δ, ((2 * Real.sin (T * u) / u : ℝ) : ℂ))
            - ((π : ℝ) : ℂ))
        + (∫ u in (0:ℝ)..δ, (H u - Hp) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ))
        + ∫ u in (0:ℝ)..δ, (H (-u) - Hm) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ) := by
    rw [integral_dirichlet_split hH hδpos T, hIright, hIleft]
    ring
  rw [dist_eq_norm, hXY]
  -- bound the four pieces
  have hplat_piece : ‖(Hp + Hm) * ((∫ u in (0:ℝ)..δ, ((2 * Real.sin (T * u) / u : ℝ) : ℂ))
      - ((π : ℝ) : ℂ))‖ < ε/4 := by
    rw [norm_mul]
    have h1 : ‖Hp + Hm‖ * ‖(∫ u in (0:ℝ)..δ, ((2 * Real.sin (T * u) / u : ℝ) : ℂ))
        - ((π : ℝ) : ℂ)‖ ≤ ‖Hp + Hm‖ * (ε / (4 * (‖Hp + Hm‖ + 1))) :=
      mul_le_mul_of_nonneg_left hplatT.le (norm_nonneg _)
    refine lt_of_le_of_lt h1 ?_
    have hN1 : (0:ℝ) < ‖Hp + Hm‖ + 1 := by positivity
    rw [show ‖Hp + Hm‖ * (ε / (4 * (‖Hp + Hm‖ + 1)))
        = (‖Hp + Hm‖ / (‖Hp + Hm‖ + 1)) * (ε / 4) by
      field_simp]
    have h2 : ‖Hp + Hm‖ / (‖Hp + Hm‖ + 1) < 1 := by
      rw [div_lt_one hN1]
      linarith
    exact mul_lt_of_lt_one_left (by linarith) h2
  have tri : ∀ a b c d : ℂ, ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    intro a b c d
    have h1 : ‖a + b + c + d‖ ≤ ‖a + b + c‖ + ‖d‖ := norm_add_le _ _
    have h2 : ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
    have h3 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
    linarith
  calc ‖(∫ u in (Set.Ioc 0 δ ∪ Set.Ico (-δ) 0)ᶜ,
            H u * ((2 * Real.sin (T * u) / u : ℝ) : ℂ))
        + (Hp + Hm) * ((∫ u in (0:ℝ)..δ, ((2 * Real.sin (T * u) / u : ℝ) : ℂ))
            - ((π : ℝ) : ℂ))
        + (∫ u in (0:ℝ)..δ, (H u - Hp) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ))
        + ∫ u in (0:ℝ)..δ, (H (-u) - Hm) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ)‖
      ≤ ‖∫ u in (Set.Ioc 0 δ ∪ Set.Ico (-δ) 0)ᶜ,
            H u * ((2 * Real.sin (T * u) / u : ℝ) : ℂ)‖
        + ‖(Hp + Hm) * ((∫ u in (0:ℝ)..δ, ((2 * Real.sin (T * u) / u : ℝ) : ℂ))
            - ((π : ℝ) : ℂ))‖
        + ‖∫ u in (0:ℝ)..δ, (H u - Hp) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ)‖
        + ‖∫ u in (0:ℝ)..δ, (H (-u) - Hm) * ((2 * Real.sin (T * u) / u : ℝ) : ℂ)‖ :=
        tri _ _ _ _
    _ < ε/4 + ε/4 + ε/4 + ε/4 := by
        refine add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le
          (add_lt_add_of_lt_of_lt hfarT hplat_piece) (hRright.trans hδR.le)) (hRleft.trans hδL.le)
    _ = ε := by ring

/-- **Jordan's Fourier inversion, symmetric-window form** (SP2-FJ-a; Poitou p. 6-03): for
integrable `H` of bounded variation with one-sided limits `Hp`, `Hm` at `0`,

`∫_{-T}^{T} (∫_ℝ H(u) e^{itu} du) dt  →  π(Hp + Hm)`  as `T → ∞`.

With the jump-mean normalisation `H(0) = (Hp + Hm)/2` the right side is `2π·H(0)` —
Poitou's form of the réciprocité de Fourier "sous la forme de Jordan". -/
theorem tendsto_fourier_window_jordan {H : ℝ → ℂ} (hH : Integrable H)
    (hre : LocallyBoundedVariationOn (fun u => (H u).re) Set.univ)
    (him : LocallyBoundedVariationOn (fun u => (H u).im) Set.univ)
    {Hp Hm : ℂ}
    (hp : Tendsto H (nhdsWithin 0 (Set.Ioi 0)) (nhds Hp))
    (hm : Tendsto H (nhdsWithin 0 (Set.Iio 0)) (nhds Hm)) :
    Tendsto (fun T : ℝ => ∫ t : ℝ in (-T)..T,
        ∫ u : ℝ, H u * Complex.exp ((t : ℂ) * (u : ℂ) * Complex.I))
      atTop (nhds (((π : ℝ) : ℂ) * (Hp + Hm))) := by
  have h1 := tendsto_integral_dirichlet_jordan hH hre him hp hm
  refine h1.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with T hT
  exact (integral_fourier_window_collapse hH hT).symm

/-- **Proposition 2 — the prime side** (Poitou p. 6-03, display (4)): for even `F`
with the weighted integrability making `F_a ∈ L¹` and with Jordan-type hypotheses
on Poitou's `H`, the prime-side edge integral converges:

`lim_{T→∞} ∫_{-T}^T {Φ(1+a+it) + Φ(-a-it)}·(−ζ_K'/ζ_K(1+a+it)) dt = 2π(H(0+) + H(0-))`.

(For the concrete admissible test functions `H` is continuous at `0` with
`H(0) = ∑ log(N𝔭)/N𝔭^{m/2}·F(m log N𝔭)`, recovering Poitou's `−2∑…` after the
sign bookkeeping of the surrounding contour.) -/
theorem tendsto_prime_side (K : Type*) [Field K] [NumberField K]
    {a : ℝ} (ha : 0 < a) {F : ℝ → ℂ}
    (hFeven : ∀ x : ℝ, F (-x) = F x)
    (hFa : Integrable (fun x : ℝ => F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)))
    (hHre : LocallyBoundedVariationOn (fun u => (primeSideH K a F u).re) Set.univ)
    (hHim : LocallyBoundedVariationOn (fun u => (primeSideH K a F u).im) Set.univ)
    {Hp Hm : ℂ}
    (hHp : Tendsto (primeSideH K a F) (nhdsWithin 0 (Set.Ioi 0)) (nhds Hp))
    (hHm : Tendsto (primeSideH K a F) (nhdsWithin 0 (Set.Iio 0)) (nhds Hm)) :
    Tendsto (fun T : ℝ => ∫ t in (-T)..T,
        (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
          + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
          * (-(logDeriv (NumberField.dedekindZeta K) (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I))))
      atTop (nhds (2 * ((π : ℝ) : ℂ) * (Hp + Hm))) := by
  have hW := tendsto_fourier_window_jordan (integrable_primeSideH K ha hFa)
    hHre hHim hHp hHm
  have hW2 := hW.const_mul (2:ℂ)
  have hfun : ∀ T : ℝ, (∫ t in (-T)..T,
      (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
        + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
        * (-(logDeriv (NumberField.dedekindZeta K) (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I))))
      = 2 * ∫ t in (-T)..T,
          ∫ u : ℝ, primeSideH K a F u * Complex.exp ((t:ℂ)*(u:ℂ)*Complex.I) := by
    intro T
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [paperPhi_one_sub hFeven]
    have h1 : (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
        + paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I))
        * (-(logDeriv (NumberField.dedekindZeta K) (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
        = 2 * (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
          * (-(logDeriv (NumberField.dedekindZeta K) (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))) := by
      ring
    rw [h1, paperPhi_mul_neg_logDeriv_eq K ha hFa t]
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    show primeSideH K a F u * Complex.exp ((t*u : ℝ) * Complex.I)
        = primeSideH K a F u * Complex.exp ((t:ℂ)*(u:ℂ)*Complex.I)
    rw [Complex.ofReal_mul]
  refine Tendsto.congr (fun T => (hfun T).symm) ?_
  have hlim : (2:ℂ) * (((π : ℝ) : ℂ) * (Hp + Hm)) = 2 * ((π : ℝ) : ℂ) * (Hp + Hm) := by
    ring
  rw [← hlim]
  exact hW2

end DedekindResidue
