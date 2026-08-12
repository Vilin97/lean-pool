/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.FunctionalEquationLogDeriv
public import LeanPool.Odlyzko.CompletedZeta.RightHalfPlane
public import LeanPool.Odlyzko.ExplicitFormula.GaussDigammaEqDigamma
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouQuadraticDecay
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPrimePowerSeriesIntegral
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedTartarTransform
public import LeanPool.Odlyzko.ExplicitFormula.TartarPoitouTransform
public import LeanPool.Odlyzko.ExplicitFormula.WeightedRectangleArgumentPrinciple
public import LeanPool.Odlyzko.ExplicitFormula.ZeroFreeRectangles
public import LeanPool.Odlyzko.FromPrimeNumberTheoremAnd.RectangleIntegral
public import LeanPool.Odlyzko.Numerics.Degree
public import LeanPool.Odlyzko.Numerics.Integrability
public import LeanPool.Odlyzko.Numerics.IntegralTail
public import LeanPool.Odlyzko.Reduction
public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Regularized Poitou Contour Limit

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

section

open Complex intervalIntegral

namespace NumberField.Odlyzko

theorem verticalSegmentIntegral_one_sub_of_antiInvariant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} (hf : ∀ z, f (1 - z) = -f z)
    (b T : ℝ) :
    verticalSegmentIntegral f (1 - b) (-T) T =
      -verticalSegmentIntegral f b (-T) T := by
  have hpoint (y : ℝ) :
      f (((1 - b : ℝ) : ℂ) + y * I) =
        -f ((b : ℂ) + (-y) * I) := by
    have harg :
        (((1 - b : ℝ) : ℂ) + y * I) =
          1 - ((b : ℂ) + (-y) * I) := by
      apply Complex.ext <;> simp
    simp_all
  simp only [verticalSegmentIntegral]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_neg]
  have heq :
      (fun x : ℝ ↦ f ((b : ℂ) + -(x : ℂ) * I)) =
        fun x : ℝ ↦ (fun y : ℝ ↦ f ((b : ℂ) + y * I)) (-x) := by simp
  rw [heq]
  have hcomp :
      (∫ x in -T..T, (fun y : ℝ ↦ f ((b : ℂ) + y * I)) (-x)) =
        ∫ x in -T..T, f ((b : ℂ) + x * I) := by
    simpa using
      (intervalIntegral.integral_comp_neg
        (f := fun y : ℝ ↦ f ((b : ℂ) + y * I))
        (a := -T) (b := T))
  simp_all

theorem rectangleIntegral_eq_horizontal_sub_add_two_vertical_of_antiInvariant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} (hf : ∀ z, f (1 - z) = -f z)
    (b T : ℝ) :
    rectangleIntegral f ((1 - b : ℝ) + (-T) * I) (b + T * I) =
      horizontalIntegral f (1 - b) b (-T) -
        horizontalIntegral f (1 - b) b T +
          (2 : ℂ) • verticalSegmentIntegral f b (-T) T := by
  rw [rectangleIntegral]
  simp only [add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im,
    I_re, I_im, neg_re, neg_im, mul_zero, mul_one, zero_add,
    neg_zero, sub_self, add_zero]
  rw [verticalSegmentIntegral_one_sub_of_antiInvariant hf]
  simp only [two_smul]
  grind

theorem mul_antiInvariant_of_invariant_of_antiInvariant
    {h g : ℂ → ℂ}
    (hh : ∀ z, h (1 - z) = h z)
    (hg : ∀ z, g (1 - z) = -g z) :
    ∀ z, h (1 - z) * g (1 - z) = -(h z * g z) := by simp_all

end NumberField.Odlyzko

end

section

open Filter MeasureTheory Real Set
open scoped Topology

namespace NumberField.Odlyzko

/-- A fermi dirac kernel used in the Odlyzko-bound argument. -/
noncomputable def fermiDiracKernel (x : ℝ) : ℝ :=
  1 / (Real.exp x + 1)

/-- An inverse gauss kernel used in the Odlyzko-bound argument. -/
noncomputable def inverseGaussKernel (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (Real.exp (-x) - 2 * f x / (Real.exp x + 1)) /
    (1 - Real.exp (-x))

theorem inverseGaussKernel_eq
    {f : ℝ → ℝ} {x : ℝ} (hx : 0 < x) :
    inverseGaussKernel f x =
      (1 - f x) / Real.sinh x - fermiDiracKernel x := by
  have hexp : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  have hexpm1 : Real.exp x - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr hx))
  have hexpp1 : Real.exp x + 1 ≠ 0 := by positivity
  have hsinh_formula :
      Real.sinh x =
        (Real.exp x ^ 2 - 1) / (2 * Real.exp x) := by
    rw [Real.sinh_eq, Real.exp_neg]
    grind
  unfold inverseGaussKernel fermiDiracKernel
  rw [hsinh_formula, Real.exp_neg]
  grind

private theorem fermiDiracKernel_nonneg (x : ℝ) :
    0 ≤ fermiDiracKernel x := by
  unfold fermiDiracKernel
  positivity

private theorem fermiDiracKernel_le_exp_neg (x : ℝ) :
    fermiDiracKernel x ≤ Real.exp (-x) := by
  unfold fermiDiracKernel
  rw [one_div, Real.exp_neg]
  exact inv_anti₀ (Real.exp_pos x)
    (le_add_of_nonneg_right zero_le_one)

theorem integrableOn_fermiDiracKernel_Ioi :
    IntegrableOn fermiDiracKernel (Ioi 0) := by
  apply (integrableOn_exp_neg_Ioi 0).mono'
  · exact
      (by
        unfold fermiDiracKernel
        have hden :
            ∀ x : ℝ, Real.exp x + 1 ≠ 0 :=
          fun x ↦ ne_of_gt (by positivity)
        exact
          (continuous_const :
            Continuous (fun _ : ℝ ↦ (1 : ℝ))).div
            (Real.continuous_exp.add continuous_const) hden :
          Continuous fermiDiracKernel)
        |>.aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs,
      abs_of_nonneg (fermiDiracKernel_nonneg x)]
    exact fermiDiracKernel_le_exp_neg x

theorem integral_fermiDiracKernel :
    (∫ x : ℝ in Ioi 0, fermiDiracKernel x) =
      Real.log 2 := by
  let F : ℝ → ℝ :=
    fun x ↦ (-1 : ℝ) * Real.log (1 + Real.exp (-x))
  have hderiv :
      ∀ x ∈ Ici (0 : ℝ),
        HasDerivAt F (fermiDiracKernel x) x := by
    intro x hx
    have he :=
      (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    have hsum :=
      (hasDerivAt_const x (1 : ℝ)).add he
    have hpos : 0 < 1 + Real.exp (-x) := by positivity
    have hlog :=
      (hsum.log hpos.ne').const_mul (-1 : ℝ)
    have hvalue :
        fermiDiracKernel x =
          -(-Real.exp (-x) / (1 + Real.exp (-x))) := by
      unfold fermiDiracKernel
      rw [Real.exp_neg]
      field_simp [Real.exp_ne_zero]
    rw [hvalue]
    simpa only [F, Pi.add_apply, Function.comp_apply,
      zero_add, mul_neg, mul_one, neg_one_mul] using hlog
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hexp : Tendsto (fun x : ℝ ↦ Real.exp (-x))
        atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
    have hone :
        Tendsto (fun x : ℝ ↦ 1 + Real.exp (-x))
          atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hexp
    simpa [F] using
      ((Real.continuousAt_log one_ne_zero).tendsto.comp hone).neg
  have h :=
    integral_Ioi_of_hasDerivAt_of_tendsto'
      hderiv integrableOn_fermiDiracKernel_Ioi hlim
  (convert h using 1; norm_num [F])

end NumberField.Odlyzko

end

section

open Real

namespace NumberField.Odlyzko

theorem exp_sub_poitouKernel_mul_exp_neg_half_div_eq_inverseGaussKernel
    (f : ℝ → ℝ) {x : ℝ} (_hx : 0 < x) :
    (Real.exp (-x) -
        poitouKernel f x * Real.exp (-x / 2)) /
        (1 - Real.exp (-x)) =
      inverseGaussKernel f x := by
  have hexphalf : Real.exp (x / 2) ≠ 0 := Real.exp_ne_zero _
  have hcosh :
      Real.cosh (x / 2) =
        (Real.exp x + 1) / (2 * Real.exp (x / 2)) := by
    rw [Real.cosh_eq, Real.exp_neg]
    have hsquare : Real.exp (x / 2) ^ 2 = Real.exp x := by
      calc
        Real.exp (x / 2) ^ 2 =
            Real.exp (x / 2) * Real.exp (x / 2) := pow_two _
        _ = Real.exp (x / 2 + x / 2) := (Real.exp_add _ _).symm
        _ = Real.exp x := by simp
    grind
  unfold poitouKernel inverseGaussKernel
  rw [hcosh]
  have hexpneghalf :
      Real.exp (-x / 2) = (Real.exp (x / 2))⁻¹ := by
    rw [show -x / 2 = -(x / 2) by ring, Real.exp_neg]
  grind

theorem exp_sub_regularizedPoitouKernel_mul_exp_neg_half_div
    (y δ : ℝ) {x : ℝ} (hx : 0 < x) :
    (Real.exp (-x) -
        poitouKernel (regularizedScaledTartar y δ) x *
          Real.exp (-x / 2)) /
        (1 - Real.exp (-x)) =
      inverseGaussKernel (regularizedScaledTartar y δ) x :=
  exp_sub_poitouKernel_mul_exp_neg_half_div_eq_inverseGaussKernel
    (regularizedScaledTartar y δ) hx

end NumberField.Odlyzko

end

section

open Complex MeasureTheory Real Set

namespace NumberField.Odlyzko

theorem norm_gaussDigammaIntegrand_vertical_le
    (σ t : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖gaussDigammaIntegrand (σ + t * I) x‖ ≤
      (Real.exp (-x) + Real.exp (-σ * x)) /
        (1 - Real.exp (-x)) := by
  have hdenPos : 0 < 1 - Real.exp (-x) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx))
  have hden :
      ‖(1 : ℂ) - Complex.exp (-x)‖ =
        1 - Real.exp (-x) := by
    rw [show Complex.exp (-x) = (Real.exp (-x) : ℝ) by
      simp]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdenPos]
  have hnum :
      ‖Complex.exp (-x) -
          Complex.exp (-(σ + t * I) * x)‖ ≤
        Real.exp (-x) + Real.exp (-σ * x) := by
    calc
      _ ≤ ‖Complex.exp (-x)‖ +
          ‖Complex.exp (-(σ + t * I) * x)‖ :=
        norm_sub_le _ _
      _ = _ := by
        rw [Complex.norm_exp, Complex.norm_exp]
        simp
  rw [gaussDigammaIntegrand, norm_div, hden]
  exact div_le_div_of_nonneg_right hnum hdenPos.le

theorem integrable_poitouTransform_regularized_mul_cexp_neg
    {δ : ℝ} (hδ : 0 < δ) (y σ x : ℝ) :
    Integrable (fun t : ℝ ↦
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        Complex.exp (-(σ + t * I) * x)) := by
  have hΦ :=
    poitouTransform_regularizedScaledTartar_vertical_integrable hδ y σ
  apply hΦ.mul_bdd
  · fun_prop
  · filter_upwards [] with t
    rw [Complex.norm_exp]
    have hre : (-(σ + t * I) * (x : ℂ)).re = -σ * x := by
      simp
    rw [hre]

theorem integral_poitouTransform_regularized_mul_gaussDigammaIntegrand
    {δ : ℝ} (hδ : 0 < δ) (y σ : ℝ) {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ,
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        gaussDigammaIntegrand (σ + t * I) x) =
      ((2 * Real.pi *
        inverseGaussKernel (regularizedScaledTartar y δ) x : ℝ) : ℂ) := by
  let Φ : ℝ → ℂ := fun t ↦
    poitouTransform (regularizedScaledTartar y δ) (σ + t * I)
  let d : ℂ := 1 - Complex.exp (-x)
  have hΦ : Integrable Φ :=
    poitouTransform_regularizedScaledTartar_vertical_integrable hδ y σ
  have hfirst : Integrable (fun t : ℝ ↦
      Φ t * Complex.exp (-x)) :=
    hΦ.mul_const _
  have hsecond : Integrable (fun t : ℝ ↦
      Φ t * Complex.exp (-(σ + t * I) * x)) :=
    integrable_poitouTransform_regularized_mul_cexp_neg
      hδ y σ x
  have hintegrand :
      (fun t : ℝ ↦
        poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
          gaussDigammaIntegrand (σ + t * I) x) =
        fun t : ℝ ↦
          (Φ t * Complex.exp (-x) -
            Φ t * Complex.exp (-(σ + t * I) * x)) / d := by
    funext t
    unfold gaussDigammaIntegrand
    grind
  have hsecondValue :
      (∫ t : ℝ,
        Φ t * Complex.exp (-(σ + t * I) * x)) =
        2 * Real.pi *
          (poitouKernel (regularizedScaledTartar y δ) x : ℂ) *
            Complex.exp (-x / 2) := by
    rw [show
        (fun t : ℝ ↦
          Φ t * Complex.exp (-(σ + t * I) * x)) =
          fun t : ℝ ↦
            poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
              Complex.exp (-x * (σ + t * I)) by
      grind]
    exact integral_poitouTransform_regularized_mul_exp_neg
      hδ y σ x
  rw [hintegrand, integral_div, integral_sub hfirst hsecond,
    integral_mul_const,
    integral_poitouTransform_regularized_vertical hδ y σ,
    hsecondValue]
  have hkernel :=
    exp_sub_regularizedPoitouKernel_mul_exp_neg_half_div y δ hx
  have hkernelC := congrArg (fun r : ℝ ↦ (r : ℂ)) hkernel
  simp only [Complex.ofReal_div, Complex.ofReal_sub,
    Complex.ofReal_exp, Complex.ofReal_mul] at hkernelC
  norm_num at hkernelC
  dsimp only [d]
  push_cast
  grind

end NumberField.Odlyzko

end

section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace NumberField.Odlyzko

theorem regularizedScaledTartar_integrable
    {y δ : ℝ} (hy : y ≠ 0) (hδ : 0 ≤ δ) :
    Integrable (regularizedScaledTartar y δ) := by
  apply (scaledTartarTestFunction_integrable hy).mono'
  · exact (continuous_regularizedScaledTartar y δ).aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_eq_abs,
      abs_of_nonneg (regularizedScaledTartar_nonneg y δ x)]
    exact regularizedScaledTartar_le_scaledTartar hδ

theorem poitouTransformIntegrand_regularizedScaledTartar_eq
    (y δ : ℝ) (s : ℂ) (x : ℝ) :
    poitouTransformIntegrand (regularizedScaledTartar y δ) s x =
      Real.exp (-δ * x ^ 2) *
        poitouTransformIntegrand (scaledTartarTestFunction y) s x := by
  rw [poitouTransformIntegrand, poitouTransformIntegrand,
    poitouKernel, poitouKernel, regularizedScaledTartar]
  push_cast
  ring

theorem norm_poitouTransformIntegrand_regularized_le_scaled
    {y δ : ℝ} (hδ : 0 ≤ δ) (s : ℂ) (x : ℝ) :
    ‖poitouTransformIntegrand (regularizedScaledTartar y δ) s x‖ ≤
      ‖poitouTransformIntegrand (scaledTartarTestFunction y) s x‖ := by
  rw [poitouTransformIntegrand_regularizedScaledTartar_eq,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (-δ * x ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    simpa only [neg_mul] using
      neg_nonpos.mpr (mul_nonneg hδ (sq_nonneg x))
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hexp (norm_nonneg _)

theorem tendsto_poitouTransform_regularizedScaledTartar_nhdsGT_zero
    {y : ℝ} (hy : y ≠ 0) {s : ℂ} (hs : s.re ∈ Icc 0 1) :
    Tendsto
      (fun δ : ℝ ↦
        poitouTransform (regularizedScaledTartar y δ) s)
      (𝓝[>] 0)
      (𝓝 (poitouTransform (scaledTartarTestFunction y) s)) := by
  unfold poitouTransform
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun x : ℝ ↦ 2 * scaledTartarTestFunction y x)
  · filter_upwards [] with δ
    exact
      (continuous_poitouTransformIntegrand_regularizedScaledTartar
        y δ s).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [] with x
    exact (norm_poitouTransformIntegrand_regularized_le_scaled
      hδ.le s x).trans
        (norm_poitouTransformIntegrand_scaledTartar_le hs x)
  · exact (scaledTartarTestFunction_integrable hy).const_mul 2
  · filter_upwards [] with x
    simp_rw [poitouTransformIntegrand_regularizedScaledTartar_eq]
    have hexp :
        Tendsto (fun δ : ℝ ↦ (Real.exp (-δ * x ^ 2) : ℂ))
          (𝓝[>] 0) (𝓝 1) := by
      have harg :
          Tendsto (fun δ : ℝ ↦ -δ * x ^ 2)
            (𝓝[>] 0) (𝓝 0) := by
        have hid :
            Tendsto (id : ℝ → ℝ) (𝓝[>] 0) (𝓝 0) :=
          tendsto_id.mono_left inf_le_left
        have hneg :
            Tendsto (fun δ : ℝ ↦ -δ) (𝓝[>] 0) (𝓝 0) := by
          simpa only [id_eq, neg_zero] using hid.neg
        simpa using hneg.mul_const (x ^ 2)
      simpa using
        (Real.continuous_exp.continuousAt.tendsto.comp harg).ofReal
    simpa only [one_mul] using
      hexp.mul tendsto_const_nhds

end NumberField.Odlyzko

end

section

open Complex Filter Set
open scoped Topology

namespace NumberField.Odlyzko

/-- A completed zeta pole factor used in the Odlyzko-bound argument. -/
noncomputable def completedZetaPoleFactor (s : ℂ) : ℂ :=
  s * (s - 1)

/-- A completed zeta pole log deriv used in the Odlyzko-bound argument. -/
noncomputable def completedZetaPoleLogDeriv (s : ℂ) : ℂ :=
  1 / s + 1 / (s - 1)

theorem completedZetaPoleLogDeriv_one_sub (s : ℂ) :
    completedZetaPoleLogDeriv (1 - s) =
      -completedZetaPoleLogDeriv s := by
  unfold completedZetaPoleLogDeriv
  grind

theorem meromorphicOrderAt_completedZetaPoleFactor_zero :
    meromorphicOrderAt completedZetaPoleFactor 0 = 1 := by
  have hg : meromorphicOrderAt (fun s : ℂ ↦ s - 1) 0 = 0 := by
    have ha : AnalyticAt ℂ (fun s : ℂ ↦ s - 1) 0 := by fun_prop
    rw [ha.meromorphicOrderAt_eq,
      ha.analyticOrderAt_eq_zero.mpr (by norm_num)]
    simp
  change meromorphicOrderAt
    ((fun s : ℂ ↦ s) * (fun s : ℂ ↦ s - 1)) 0 = 1
  rw [meromorphicOrderAt_mul (by fun_prop) (by fun_prop), hg]
  rw [add_zero, show (fun s : ℂ ↦ s) = id by grind]
  simp

theorem meromorphicOrderAt_completedZetaPoleFactor_one :
    meromorphicOrderAt completedZetaPoleFactor 1 = 1 := by
  have hf : meromorphicOrderAt (fun s : ℂ ↦ s) 1 = 0 := by
    have ha : AnalyticAt ℂ (fun s : ℂ ↦ s) 1 := by fun_prop
    rw [ha.meromorphicOrderAt_eq,
      ha.analyticOrderAt_eq_zero.mpr (by norm_num)]
    simp
  change meromorphicOrderAt
    ((fun s : ℂ ↦ s) * (fun s : ℂ ↦ s - 1)) 1 = 1
  rw [meromorphicOrderAt_mul (by fun_prop) (by fun_prop), hf]
  simp

theorem logDeriv_completedZetaPoleFactor_eq
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv completedZetaPoleFactor s =
      completedZetaPoleLogDeriv s := by
  unfold completedZetaPoleFactor completedZetaPoleLogDeriv
  rw [logDeriv_mul]
  · simp only [logDeriv_apply, deriv_sub_const,
      deriv_id'', one_div]
  · simp_all
  · grind
  · simp
  · simp

theorem rectangleIntegral_mul_completedZetaPoleLogDeriv
    {h : ℂ → ℂ} {a b u v : ℝ}
    (ha : a < 0) (hb : 1 < b) (hu : u < 0) (hv : 0 < v)
    (hh : ∀ z ∈ Icc a b ×ℂ Icc u v, AnalyticAt ℂ h z) :
    rectangleIntegral
        (fun s ↦ h s * completedZetaPoleLogDeriv s)
        (a + u * I) (b + v * I) =
      2 * Real.pi * I * (h 0 + h 1) := by
  classical
  have hab : a ≤ b := by linarith
  have huv : u ≤ v := by linarith
  have harg :=
    rectangleIntegral_mul_logDeriv_eq_two_pi_I_mul_sum
      (f := completedZetaPoleFactor) (h := h)
      (S := {0, 1}) (order := fun _ ↦ 1)
      hab huv
      (by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl
        · exact ⟨ha, by norm_num; linarith, hu, hv⟩
        · exact ⟨by norm_num; linarith, hb, hu, hv⟩)
      (by
        unfold completedZetaPoleFactor
        fun_prop)
      hh
      (by
        intro z _ hz
        rw [completedZetaPoleFactor, mul_eq_zero, sub_eq_zero] at hz
        simp_all)
      (by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl
        · exact meromorphicOrderAt_completedZetaPoleFactor_zero
        · exact meromorphicOrderAt_completedZetaPoleFactor_one)
  have hboundary :
      rectangleIntegral
          (fun s ↦ h s * logDeriv completedZetaPoleFactor s)
          (a + u * I) (b + v * I) =
        rectangleIntegral
          (fun s ↦ h s * completedZetaPoleLogDeriv s)
          (a + u * I) (b + v * I) := by
    apply rectangleIntegral_congr
    · intro t ht
      congr 1
      apply logDeriv_completedZetaPoleFactor_eq
      · intro hz
        have him := congrArg Complex.im hz
        norm_num at him
        linarith
      · intro hz
        have him := congrArg Complex.im hz
        norm_num at him
        linarith
    · intro t ht
      congr 1
      apply logDeriv_completedZetaPoleFactor_eq
      · intro hz
        have him := congrArg Complex.im hz
        norm_num at him
        linarith
      · intro hz
        have him := congrArg Complex.im hz
        norm_num at him
        linarith
    · intro t ht
      congr 1
      apply logDeriv_completedZetaPoleFactor_eq
      · intro hz
        have hre := congrArg Complex.re hz
        norm_num at hre
        linarith
      · intro hz
        have hre := congrArg Complex.re hz
        norm_num at hre
        linarith
    · intro t ht
      congr 1
      apply logDeriv_completedZetaPoleFactor_eq
      · intro hz
        have hre := congrArg Complex.re hz
        norm_num at hre
        linarith
      · intro hz
        have hre := congrArg Complex.re hz
        norm_num at hre
        linarith
  simp_all

end NumberField.Odlyzko

end

section

open Asymptotics Complex Filter MeasureTheory Set
open scoped Topology

namespace NumberField.Odlyzko

/-- A poitou critical strip used in the Odlyzko-bound argument. -/
def poitouCriticalStrip : Set ℂ := re ⁻¹' Ioo 0 1

/-- A poitou closed critical strip used in the Odlyzko-bound argument. -/
def poitouClosedCriticalStrip : Set ℂ := re ⁻¹' Icc 0 1

end NumberField.Odlyzko

end

section

open Complex intervalIntegral MeasureTheory Real Set

namespace NumberField.Odlyzko

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
theorem rectangleBorderIntegrable_of_continuousAt_boundary
    {f : ℂ → E} {a b u v : ℝ} (hab : a ≤ b) (huv : u ≤ v)
    (hf : ∀ z ∈ Icc a b ×ℂ Icc u v,
      (z.re = a ∨ z.re = b ∨ z.im = u ∨ z.im = v) →
        ContinuousAt f z) :
    RectangleBorderIntegrable f (a + u * I) (b + v * I) := by
  simp only [RectangleBorderIntegrable, add_re, ofReal_re, mul_re,
    I_re, mul_zero, sub_self, add_zero, add_im, ofReal_im,
    mul_im, I_im, mul_one, zero_add]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le hab] at hx
    apply ContinuousAt.continuousWithinAt
    have hout := hf (x + u * I) (by
        simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re,
          mul_zero, sub_self, add_zero, add_im, ofReal_im, mul_im,
          I_im, mul_one, zero_add]
        simp_all) (by simp)
    have hin : ContinuousAt (fun q : ℝ ↦ (q : ℂ) + u * I) x := by fun_prop
    simpa only [ContinuousAt, Function.comp_def] using
      Filter.Tendsto.comp hout hin
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le hab] at hx
    apply ContinuousAt.continuousWithinAt
    have hout := hf (x + v * I) (by
        simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re,
          mul_zero, sub_self, add_zero, add_im, ofReal_im, mul_im,
          I_im, mul_one, zero_add]
        simp_all) (by simp)
    have hin : ContinuousAt (fun q : ℝ ↦ (q : ℂ) + v * I) x := by fun_prop
    simpa only [ContinuousAt, Function.comp_def] using
      Filter.Tendsto.comp hout hin
  · apply ContinuousOn.intervalIntegrable
    intro y hy
    rw [uIcc_of_le huv] at hy
    apply ContinuousAt.continuousWithinAt
    have hout := hf (b + y * I) (by
        simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re,
          mul_zero, sub_self, add_zero, add_im, ofReal_im, mul_im,
          I_im, mul_one, zero_add]
        simp_all) (by simp)
    have hin : ContinuousAt (fun q : ℝ ↦ (b : ℂ) + q * I) y := by fun_prop
    simpa only [ContinuousAt, Function.comp_def] using
      Filter.Tendsto.comp hout hin
  · apply ContinuousOn.intervalIntegrable
    intro y hy
    rw [uIcc_of_le huv] at hy
    apply ContinuousAt.continuousWithinAt
    have hout := hf (a + y * I) (by
        simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re,
          mul_zero, sub_self, add_zero, add_im, ofReal_im, mul_im,
          I_im, mul_one, zero_add]
        simp_all) (by simp)
    have hin : ContinuousAt (fun q : ℝ ↦ (a : ℂ) + q * I) y := by fun_prop
    simpa only [ContinuousAt, Function.comp_def] using
      Filter.Tendsto.comp hout hin

theorem rectangleIntegral_sub
    {f g : ℂ → E} {z w : ℂ}
    (hf : RectangleBorderIntegrable f z w)
    (hg : RectangleBorderIntegrable g z w) :
    rectangleIntegral (fun s ↦ f s - g s) z w =
      rectangleIntegral f z w - rectangleIntegral g z w := by
  rcases hf with ⟨hf₁, hf₂, hf₃, hf₄⟩
  rcases hg with ⟨hg₁, hg₂, hg₃, hg₄⟩
  unfold rectangleIntegral horizontalIntegral verticalSegmentIntegral
  rw [integral_sub hf₁ hg₁, integral_sub hf₂ hg₂,
    integral_sub hf₃ hg₃, integral_sub hf₄ hg₄]
  simp only [smul_sub]
  grind

end NumberField.Odlyzko

end

section

open Complex MeasureTheory Real
open scoped Convolution FourierTransform RealInnerProductSpace

namespace NumberField.Odlyzko

private theorem tartarWeightConvolution_integrable :
    Integrable tartarWeightConvolution := by
  have h := complexTartarWeight_convolution_integrable
  apply h.norm.congr
  filter_upwards [] with x
  rw [complexTartarWeight_convolution_eq, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tartarWeightConvolution_nonneg x)]

theorem scaledTartarTestFunction_eq_integral_weightConvolution_cos
    (y x : ℝ) :
    scaledTartarTestFunction y x =
      (9 / 16 : ℝ) *
        ∫ v : ℝ, tartarWeightConvolution v * Real.cos (v * y * x) := by
  let Wℂ : ℝ → ℂ :=
    complexTartarWeight ⋆[ContinuousLinearMap.mul ℂ ℂ] complexTartarWeight
  let ξ : ℝ := y * x / (2 * Real.pi)
  have hint :
      Integrable (fun v : ℝ ↦
        Complex.exp (↑(-2 * Real.pi * v * ξ) * I) • Wℂ v) := by
    constructor
    · exact (by fun_prop : Continuous (fun v : ℝ ↦
        Complex.exp (↑(-2 * Real.pi * v * ξ) * I))).aestronglyMeasurable.smul
          complexTartarWeight_convolution_integrable.aestronglyMeasurable
    · apply complexTartarWeight_convolution_integrable.2.congr'
      filter_upwards [] with v
      rw [norm_smul, Complex.norm_exp]
      simp [Wℂ, Complex.mul_re]
  dsimp [Wℂ] at hint
  have hfour := fourier_complexTartarWeight_convolution ξ
  rw [Real.fourier_real_eq_integral_exp_smul] at hfour
  simp only [smul_eq_mul] at hfour
  have hre := congrArg Complex.re hfour
  rw [← RCLike.re_eq_complex_re, ← integral_re hint] at hre
  simp_rw [complexTartarWeight_convolution_eq] at hre
  simp only [RCLike.re_eq_complex_re, Complex.exp_mul_I,
    Complex.mul_re, Complex.add_re, Complex.cos_ofReal_re,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, mul_one, sub_zero] at hre
  dsimp [ξ] at hre
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold scaledTartarTestFunction
  rw [show (16 / 9 : ℝ) * Tartar.testFunction (2 * Real.pi *
      (y * x / (2 * Real.pi))) =
      (16 / 9 : ℝ) * Tartar.testFunction (y * x) by
        grind] at hre
  have hcos :
      (fun v : ℝ ↦
        Real.cos (-2 * Real.pi * v * (y * x / (2 * Real.pi))) *
          tartarWeightConvolution v) =
      (fun v : ℝ ↦
        tartarWeightConvolution v * Real.cos (v * y * x)) := by
    funext v
    rw [show -2 * Real.pi * v * (y * x / (2 * Real.pi)) =
        -(v * y * x) by grind, Real.cos_neg]
    ring
  simp only [add_zero] at hre
  grind

theorem integral_exp_neg_mul_sq_mul_cos_nonneg
    {δ : ℝ} (hδ : 0 < δ) (a : ℝ) :
    0 ≤ ∫ x : ℝ, Real.exp (-δ * x ^ 2) * Real.cos (a * x) := by
  have hint :
      Integrable (fun x : ℝ ↦
        Complex.exp (I * (a : ℂ) * x) *
          Complex.exp (-(δ : ℂ) * x ^ 2)) :=
    integrable_cexp_quadratic (b := (δ : ℂ)) (by simp_all) (I * a) 0 |>.congr (by
      filter_upwards [] with x
      rw [add_zero, Complex.exp_add, mul_comm])
  have hgauss :=
    fourierIntegral_gaussian (b := (δ : ℂ)) (by simp_all) (a : ℂ)
  have hIa (x : ℝ) :
      I * (a : ℂ) * x = ((a * x : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hrealExp (x : ℝ) :
      Complex.exp (-(δ : ℂ) * x ^ 2) =
        (Real.exp (-δ * x ^ 2) : ℂ) := by simp
  have hq : 0 ≤ Real.pi / δ := (div_pos Real.pi_pos hδ).le
  have hpow :
      ((Real.pi / δ : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
        (((Real.pi / δ : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using
        (Complex.ofReal_cpow hq (1 / 2)).symm
  have hexp :
      Complex.exp (-(a : ℂ) ^ 2 / (4 * (δ : ℂ))) =
        (Real.exp (-(a ^ 2) / (4 * δ)) : ℂ) := by
    simp
  have hquot :
      (Real.pi : ℂ) / (δ : ℂ) =
        ((Real.pi / δ : ℝ) : ℂ) := by simp
  rw [hquot, hpow, hexp] at hgauss
  have hre := congrArg Complex.re hgauss
  rw [← RCLike.re_eq_complex_re, ← integral_re hint] at hre
  simp_rw [hIa, hrealExp] at hre
  simp only [RCLike.re_eq_complex_re, Complex.exp_mul_I,
    Complex.mul_re, Complex.add_re, Complex.cos_ofReal_re,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    mul_one, add_zero, sub_zero] at hre
  rw [show (fun x : ℝ ↦
      Real.cos (a * x) * Real.exp (-δ * x ^ 2)) =
      (fun x : ℝ ↦
        Real.exp (-δ * x ^ 2) * Real.cos (a * x)) by
          funext x
          ring] at hre
  rw [hre]
  positivity

theorem cosineTransform_regularizedScaledTartar_nonneg
    {δ : ℝ} (hδ : 0 < δ) (y t : ℝ) :
    0 ≤ Poitou.cosineTransform (regularizedScaledTartar y δ) t := by
  let F : ℝ → ℝ → ℝ := fun x v ↦
    tartarWeightConvolution v * Real.exp (-δ * x ^ 2) *
      Real.cos (v * y * x) * Real.cos (t * x)
  have hgauss : Integrable (fun x : ℝ ↦ Real.exp (-δ * x ^ 2)) :=
    integrable_exp_neg_mul_sq hδ
  have hmajor :
      Integrable (fun z : ℝ × ℝ ↦
        Real.exp (-δ * z.1 ^ 2) * tartarWeightConvolution z.2) :=
    hgauss.mul_prod tartarWeightConvolution_integrable
  have hWcont : Continuous tartarWeightConvolution := by
    have hc :=
      Complex.continuous_re.comp
        complexTartarWeight_convolution_continuous
    convert hc using 1
    funext x
    change tartarWeightConvolution x =
      ((complexTartarWeight ⋆[ContinuousLinearMap.mul ℂ ℂ]
        complexTartarWeight) x).re
    rw [complexTartarWeight_convolution_eq]
    simp
  have hdouble : Integrable (Function.uncurry F) := by
    apply hmajor.mono'
    · exact (by fun_prop : Continuous (Function.uncurry F))
        |>.aestronglyMeasurable
    · filter_upwards [] with z
      change |F z.1 z.2| ≤
        Real.exp (-δ * z.1 ^ 2) * tartarWeightConvolution z.2
      dsimp [F]
      rw [abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (tartarWeightConvolution_nonneg z.2),
        abs_of_pos (Real.exp_pos _)]
      calc
        tartarWeightConvolution z.2 * Real.exp (-δ * z.1 ^ 2) *
              |Real.cos (z.2 * y * z.1)| * |Real.cos (t * z.1)| ≤
            tartarWeightConvolution z.2 * Real.exp (-δ * z.1 ^ 2) *
              1 * 1 := by
          have hA :
              0 ≤ tartarWeightConvolution z.2 *
                Real.exp (-δ * z.1 ^ 2) :=
            mul_nonneg (tartarWeightConvolution_nonneg z.2)
              (Real.exp_pos _).le
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_left
              (mul_le_mul
                (Real.abs_cos_le_one (z.2 * y * z.1))
                (Real.abs_cos_le_one (t * z.1))
                (abs_nonneg (Real.cos (t * z.1))) zero_le_one) hA
        _ = Real.exp (-δ * z.1 ^ 2) *
              tartarWeightConvolution z.2 := by ring
  have hinner (v : ℝ) :
      0 ≤ ∫ x : ℝ, F x v := by
    have hminus :=
      integral_exp_neg_mul_sq_mul_cos_nonneg hδ (v * y - t)
    have hplus :=
      integral_exp_neg_mul_sq_mul_cos_nonneg hδ (v * y + t)
    have hidentity :
        (fun x : ℝ ↦ F x v) =
          (fun x : ℝ ↦ tartarWeightConvolution v *
            ((Real.exp (-δ * x ^ 2) * Real.cos ((v * y - t) * x) +
              Real.exp (-δ * x ^ 2) * Real.cos ((v * y + t) * x)) / 2)) := by
      funext x
      dsimp [F]
      rw [show (v * y - t) * x = v * y * x - t * x by ring,
        show (v * y + t) * x = v * y * x + t * x by ring]
      rw [Real.cos_sub, Real.cos_add]
      ring
    have hminusInt :
        Integrable (fun x : ℝ ↦
          Real.exp (-δ * x ^ 2) * Real.cos ((v * y - t) * x)) :=
      (integrable_exp_neg_mul_sq hδ).mul_bdd
        (by fun_prop)
        (Filter.Eventually.of_forall fun x ↦ by
          simpa [Real.norm_eq_abs] using
            Real.abs_cos_le_one ((v * y - t) * x))
    have hplusInt :
        Integrable (fun x : ℝ ↦
          Real.exp (-δ * x ^ 2) * Real.cos ((v * y + t) * x)) :=
      (integrable_exp_neg_mul_sq hδ).mul_bdd
        (by fun_prop)
        (Filter.Eventually.of_forall fun x ↦ by
          simpa [Real.norm_eq_abs] using
            Real.abs_cos_le_one ((v * y + t) * x))
    rw [hidentity, integral_const_mul, integral_div,
      integral_add hminusInt hplusInt]
    exact mul_nonneg (tartarWeightConvolution_nonneg v)
      (div_nonneg (add_nonneg hminus hplus) (by norm_num))
  have hswap := integral_integral_swap hdouble
  calc
    Poitou.cosineTransform (regularizedScaledTartar y δ) t =
        (9 / 16 : ℝ) * ∫ x : ℝ, ∫ v : ℝ, F x v := by
      unfold Poitou.cosineTransform regularizedScaledTartar
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [scaledTartarTestFunction_eq_integral_weightConvolution_cos]
      rw [show (∫ v : ℝ, F x v) =
          (∫ v : ℝ, tartarWeightConvolution v *
            Real.cos (v * y * x)) *
              (Real.exp (-δ * x ^ 2) * Real.cos (t * x)) by
            rw [← integral_mul_const]
            apply integral_congr_ae
            filter_upwards [] with v
            dsimp [F]
            ring]
      ring
    _ = (9 / 16 : ℝ) * ∫ v : ℝ, ∫ x : ℝ, F x v := by simp_all
    _ ≥ 0 := mul_nonneg (by norm_num) (integral_nonneg hinner)

theorem regularizedScaledTartar_poitouAdmissible
    {y δ : ℝ} (hy : y ≠ 0) (hδ : 0 < δ) :
    Poitou.Admissible (regularizedScaledTartar y δ) where
  continuous := continuous_regularizedScaledTartar y δ
  even := regularizedScaledTartar_even y δ
  value_zero := regularizedScaledTartar_zero y δ
  nonnegative := regularizedScaledTartar_nonneg y δ
  integrable := regularizedScaledTartar_integrable hy hδ.le
  cosineTransform_nonnegative :=
    cosineTransform_regularizedScaledTartar_nonneg hδ y

end NumberField.Odlyzko

end

section

open Asymptotics Complex Filter MeasureTheory Real Set
open scoped Topology

namespace NumberField.Odlyzko

/-- A regularized poitou critical strip majorant used in the Odlyzko-bound argument. -/
noncomputable def regularizedPoitouCriticalStripMajorant
    (δ x : ℝ) : ℝ :=
  Real.exp ((1 / 2 : ℝ) ^ 2 / (2 * δ)) *
    Real.exp (-(δ / 2) * x ^ 2)

private theorem regularizedPoitouCriticalStripMajorant_integrable
    {δ : ℝ} (hδ : 0 < δ) :
    Integrable (regularizedPoitouCriticalStripMajorant δ) := by
  exact (integrable_exp_neg_mul_sq (half_pos hδ)).const_mul _

theorem norm_poitouTransformIntegrand_regularized_le_criticalStripMajorant
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {s : ℂ}
    (hs : s ∈ poitouClosedCriticalStrip) (x : ℝ) :
    ‖poitouTransformIntegrand (regularizedScaledTartar y δ) s x‖ ≤
      regularizedPoitouCriticalStripMajorant δ x := by
  refine (norm_poitouTransformIntegrand_regularizedScaledTartar_le
    hδ s x).trans ?_
  unfold regularizedPoitouCriticalStripMajorant
  apply mul_le_mul_of_nonneg_right
  · apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right
    · have habs : |s.re - 1 / 2| ≤ 1 / 2 := by
        rw [abs_le]
        constructor <;> linarith [hs.1, hs.2]
      exact (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 habs
    · positivity
  · exact (Real.exp_pos _).le

theorem norm_poitouTransform_regularized_le_criticalStripIntegral
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {s : ℂ}
    (hs : s ∈ poitouClosedCriticalStrip) :
    ‖poitouTransform (regularizedScaledTartar y δ) s‖ ≤
      ∫ x : ℝ, regularizedPoitouCriticalStripMajorant δ x := by
  rw [poitouTransform]
  apply norm_integral_le_of_norm_le
    (regularizedPoitouCriticalStripMajorant_integrable hδ)
  filter_upwards [] with x
  exact norm_poitouTransformIntegrand_regularized_le_criticalStripMajorant
    hδ y hs x

theorem diffContOnCl_poitouTransform_regularized
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    DiffContOnCl ℂ (poitouTransform (regularizedScaledTartar y δ))
      poitouCriticalStrip := by
  have han :=
    analyticOnNhd_poitouTransform_regularizedScaledTartar
      (y := y) hδ
  constructor
  · intro s hs
    exact (han s (mem_univ s)).differentiableAt.differentiableWithinAt
  · exact han.continuousOn.mono (subset_univ _)

/-- A negative exp regularized poitou transform used in the Odlyzko-bound argument. -/
noncomputable def negativeExpRegularizedPoitouTransform
    (y δ : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (-poitouTransform (regularizedScaledTartar y δ) s)

theorem diffContOnCl_negativeExpRegularizedPoitouTransform
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    DiffContOnCl ℂ (negativeExpRegularizedPoitouTransform y δ)
      poitouCriticalStrip := by
  let h := (diffContOnCl_poitouTransform_regularized hδ y).neg
  constructor
  · intro s hs
    exact (h.differentiableOn s hs).cexp
  · exact Complex.continuous_exp.continuousOn.comp h.continuousOn
      (fun _ _ ↦ mem_univ _)

theorem norm_negativeExpRegularizedPoitouTransform_le
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {s : ℂ}
    (hs : s ∈ poitouClosedCriticalStrip) :
    ‖negativeExpRegularizedPoitouTransform y δ s‖ ≤
      Real.exp
        (∫ x : ℝ, regularizedPoitouCriticalStripMajorant δ x) := by
  rw [negativeExpRegularizedPoitouTransform, Complex.norm_exp, neg_re]
  apply Real.exp_le_exp.mpr
  calc
    -(poitouTransform (regularizedScaledTartar y δ) s).re ≤
        |(poitouTransform (regularizedScaledTartar y δ) s).re| :=
      neg_le_abs _
    _ ≤ ‖poitouTransform (regularizedScaledTartar y δ) s‖ :=
      Complex.abs_re_le_norm _
    _ ≤ _ :=
      norm_poitouTransform_regularized_le_criticalStripIntegral hδ y hs

theorem negativeExpRegularizedPoitouTransform_growth
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    ∃ c < Real.pi / (1 - 0), ∃ B,
      negativeExpRegularizedPoitouTransform y δ
        =O[comap (_root_.abs ∘ im) atTop ⊓
          𝓟 (re ⁻¹' Ioo (0 : ℝ) 1)]
        fun z ↦ Real.exp (B * Real.exp (c * |z.im|)) := by
  refine ⟨0, by positivity, 0, ?_⟩
  apply IsBigO.of_bound
    (Real.exp
      (∫ x : ℝ, regularizedPoitouCriticalStripMajorant δ x))
  apply eventually_inf_principal.2
  filter_upwards [] with s hs
  have hs' : s ∈ poitouClosedCriticalStrip := ⟨hs.1.le, hs.2.le⟩
  simpa using
    norm_negativeExpRegularizedPoitouTransform_le hδ y hs'

theorem norm_negativeExpRegularizedPoitouTransform_le_one_of_re_zero
    {y δ : ℝ} (hy : y ≠ 0) (hδ : 0 < δ) {s : ℂ}
    (hs : s.re = 0) :
    ‖negativeExpRegularizedPoitouTransform y δ s‖ ≤ 1 := by
  have heq : s = (s.im : ℂ) * I := by
    apply Complex.ext
    · simp [hs]
    · simp
  rw [negativeExpRegularizedPoitouTransform, Complex.norm_exp,
    neg_re, Real.exp_le_one_iff, heq]
  exact neg_nonpos.mpr (re_poitouTransform_mul_I_nonneg
    (regularizedScaledTartar_poitouAdmissible hy hδ) s.im
    (poitouTransformIntegrand_regularizedScaledTartar_integrable
      hδ (s.im * I)))

theorem norm_negativeExpRegularizedPoitouTransform_le_one_of_re_one
    {y δ : ℝ} (hy : y ≠ 0) (hδ : 0 < δ) {s : ℂ}
    (hs : s.re = 1) :
    ‖negativeExpRegularizedPoitouTransform y δ s‖ ≤ 1 := by
  have heq : s = 1 + (s.im : ℂ) * I := by
    apply Complex.ext
    · simp [hs]
    · simp
  rw [negativeExpRegularizedPoitouTransform, Complex.norm_exp,
    neg_re, Real.exp_le_one_iff, heq]
  exact neg_nonpos.mpr (re_poitouTransform_one_add_mul_I_nonneg
    (regularizedScaledTartar_poitouAdmissible hy hδ) s.im
    (poitouTransformIntegrand_regularizedScaledTartar_integrable
      hδ (((-s.im : ℝ) : ℂ) * I)))

theorem re_poitouTransform_regularizedScaledTartar_nonneg
    {y δ : ℝ} (hy : y ≠ 0) (hδ : 0 < δ) {s : ℂ}
    (hs : s ∈ poitouClosedCriticalStrip) :
    0 ≤ (poitouTransform (regularizedScaledTartar y δ) s).re := by
  have hnorm :
      ‖negativeExpRegularizedPoitouTransform y δ s‖ ≤ 1 :=
    PhragmenLindelof.vertical_strip
      (a := 0) (b := 1) (C := 1)
      (diffContOnCl_negativeExpRegularizedPoitouTransform hδ y)
      (negativeExpRegularizedPoitouTransform_growth hδ y)
      (fun z hz ↦
        norm_negativeExpRegularizedPoitouTransform_le_one_of_re_zero
          hy hδ hz)
      (fun z hz ↦
        norm_negativeExpRegularizedPoitouTransform_le_one_of_re_one
          hy hδ hz)
      hs.1 hs.2
  rw [negativeExpRegularizedPoitouTransform, Complex.norm_exp,
    Real.exp_le_one_iff] at hnorm
  simp_all

end NumberField.Odlyzko

end

section

open Complex NumberField Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

theorem completedDedekindZetaZeroDivisor_support_re_mem_Icc
    {s : ℂ} (hs : s ∈ (completedDedekindZetaZeroDivisor K).support) :
    s.re ∈ Icc 0 1 := by
  have hs0 :
      poleClearedCompletedDedekindZetaContinuation K s = 0 :=
    poleClearedCompletedDedekindZetaContinuation_eq_zero_of_mem_support K hs
  constructor
  · by_contra h
    exact poleClearedCompletedDedekindZetaContinuation_ne_zero_of_re_lt_zero K
      (lt_of_not_ge h) hs0
  · by_contra h
    exact poleClearedCompletedDedekindZetaContinuation_ne_zero_of_one_lt_re K
      (lt_of_not_ge h) hs0

private theorem completedDedekindZetaZeroDivisor_apply_nonneg (s : ℂ) :
    0 ≤ (completedDedekindZetaZeroDivisor K s : ℤ) := by
  have h :=
    meromorphicOrderAt_poleClearedCompletedDedekindZetaContinuation_nonneg K s
  rw [meromorphicOrderAt_poleClearedCompletedDedekindZetaContinuation_eq_divisor K s] at h
  simp_all

private theorem re_mul_completedDedekindZetaZeroDivisor_nonneg_of_re_nonneg
    (Φ : ℂ → ℂ) {s : ℂ} (hΦ : 0 ≤ (Φ s).re) :
    0 ≤ (Φ s * (completedDedekindZetaZeroDivisor K s : ℂ)).re := by
  norm_num [mul_re]
  exact mul_nonneg hΦ
    (by exact_mod_cast completedDedekindZetaZeroDivisor_apply_nonneg K s)

theorem re_sum_mul_completedDedekindZetaZeroDivisor_nonneg_of_re_nonneg
    (Φ : ℂ → ℂ) {S : Finset ℂ}
    (hΦ : ∀ s ∈ S, 0 ≤ (Φ s).re) :
    0 ≤ (∑ s ∈ S, Φ s *
      (completedDedekindZetaZeroDivisor K s : ℂ)).re := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | @insert s S hsnot ih =>
      rw [Finset.sum_insert hsnot, add_re]
      exact add_nonneg
        (re_mul_completedDedekindZetaZeroDivisor_nonneg_of_re_nonneg
          K Φ (hΦ s (Finset.mem_insert_self s S)))
        (ih fun z hz ↦ hΦ z (Finset.mem_insert_of_mem hz))

end NumberField.Odlyzko

end

section

open Complex NumberField Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

theorem re_poitouTransform_regularized_nonneg_of_completedZetaZero
    {y δ : ℝ} (hy : y ≠ 0) (hδ : 0 < δ) {s : ℂ}
    (hs : s ∈ (completedDedekindZetaZeroDivisor K).support) :
    0 ≤ (poitouTransform (regularizedScaledTartar y δ) s).re :=
  re_poitouTransform_regularizedScaledTartar_nonneg hy hδ
    (completedDedekindZetaZeroDivisor_support_re_mem_Icc K hs)

theorem re_sum_poitouTransform_regularized_mul_completedZetaZeroDivisor_nonneg
    {y δ : ℝ} (hy : y ≠ 0) (hδ : 0 < δ) {S : Finset ℂ}
    (hS : ∀ s ∈ S, s ∈ (completedDedekindZetaZeroDivisor K).support) :
    0 ≤ (∑ s ∈ S, poitouTransform (regularizedScaledTartar y δ) s *
      (completedDedekindZetaZeroDivisor K s : ℂ)).re := by
  apply re_sum_mul_completedDedekindZetaZeroDivisor_nonneg_of_re_nonneg
  intro s hs
  exact re_poitouTransform_regularized_nonneg_of_completedZetaZero
    K hy hδ (hS s hs)

theorem re_sum_poitouTransform_regularized_completedZetaZerosInClosedRectangle_nonneg
    {y δ : ℝ} (hy : y ≠ 0) (hδ : 0 < δ)
    (a b u v : ℝ) :
    0 ≤
      (∑ s ∈ completedDedekindZetaZerosInClosedRectangle K a b u v,
        poitouTransform (regularizedScaledTartar y δ) s *
          (completedDedekindZetaZeroDivisor K s : ℂ)).re := by
  apply
    re_sum_poitouTransform_regularized_mul_completedZetaZeroDivisor_nonneg
      K hy hδ
  intro s hs
  exact
    (mem_completedDedekindZetaZerosInClosedRectangle_iff K).mp hs |>.2

end NumberField.Odlyzko

end

section

open Complex NumberField Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

theorem regularizedPoitou_mul_completedZetaLogDeriv_one_sub
    (y δ : ℝ) (s : ℂ) :
    poitouTransform (regularizedScaledTartar y δ) (1 - s) *
        logDeriv (poleClearedCompletedDedekindZetaContinuation K) (1 - s) =
      -(poitouTransform (regularizedScaledTartar y δ) s *
        logDeriv (poleClearedCompletedDedekindZetaContinuation K) s) := by
  apply mul_antiInvariant_of_invariant_of_antiInvariant
  · intro z
    exact poitouTransform_one_sub (regularizedScaledTartar_even y δ) z
  · intro z
    exact
      logDeriv_poleClearedCompletedDedekindZetaContinuation_one_sub_all K z

theorem regularizedPoitou_centeredRectangle_identity
    {y δ b T : ℝ} (hδ : 0 < δ) (hb : 1 / 2 ≤ b) (hT : 0 ≤ T)
    (hboundary : ∀ z ∈ Icc (1 - b) b ×ℂ Icc (-T) T,
      (z.re = 1 - b ∨ z.re = b ∨ z.im = -T ∨ z.im = T) →
        poleClearedCompletedDedekindZetaContinuation K z ≠ 0) :
    horizontalIntegral
        (fun s ↦
          poitouTransform (regularizedScaledTartar y δ) s *
            logDeriv
              (poleClearedCompletedDedekindZetaContinuation K) s)
        (1 - b) b (-T) -
      horizontalIntegral
        (fun s ↦
          poitouTransform (regularizedScaledTartar y δ) s *
            logDeriv
              (poleClearedCompletedDedekindZetaContinuation K) s)
        (1 - b) b T +
      (2 : ℂ) • verticalSegmentIntegral
        (fun s ↦
          poitouTransform (regularizedScaledTartar y δ) s *
            logDeriv
              (poleClearedCompletedDedekindZetaContinuation K) s)
        b (-T) T =
      (2 * Real.pi * I) *
        ∑ p ∈ completedDedekindZetaZerosInClosedRectangle
            K (1 - b) b (-T) T,
          poitouTransform (regularizedScaledTartar y δ) p *
            (completedDedekindZetaZeroDivisor K p : ℂ) := by
  let q : ℂ → ℂ := fun s ↦
    poitouTransform (regularizedScaledTartar y δ) s *
      logDeriv (poleClearedCompletedDedekindZetaContinuation K) s
  change
    horizontalIntegral q (1 - b) b (-T) -
        horizontalIntegral q (1 - b) b T +
        (2 : ℂ) • verticalSegmentIntegral q b (-T) T = _
  rw [← rectangleIntegral_eq_horizontal_sub_add_two_vertical_of_antiInvariant
    (f := q)
    (regularizedPoitou_mul_completedZetaLogDeriv_one_sub K y δ) b T]
  have hab : 1 - b ≤ b := by linarith
  have huv : -T ≤ T := by linarith
  have hanalytic :
      ∀ z ∈ Icc (1 - b) b ×ℂ Icc (-T) T,
        AnalyticAt ℂ
          (poitouTransform (regularizedScaledTartar y δ)) z := by
    intro z _
    exact
      analyticOnNhd_poitouTransform_regularizedScaledTartar hδ z
        (mem_univ z)
  have hrect :=
    rectangleIntegral_mul_logDeriv_poleClearedCompletedDedekindZetaContinuation
      K
      (h := poitouTransform (regularizedScaledTartar y δ))
      (a := 1 - b) (b := b) (u := -T) (v := T)
      hab huv hanalytic hboundary
  simpa only [q, ofReal_neg] using hrect

theorem regularizedPoitou_zeroFreeRectangle_identity
    {y δ ε T : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hT : 0 ≤ T)
    (hboundary : ∀ z ∈ Icc (-ε) (1 + ε) ×ℂ Icc (-T) T,
      (z.re = -ε ∨ z.re = 1 + ε ∨ z.im = -T ∨ z.im = T) →
        poleClearedCompletedDedekindZetaContinuation K z ≠ 0) :
    horizontalIntegral
        (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
          logDeriv (poleClearedCompletedDedekindZetaContinuation K) s)
        (-ε) (1 + ε) (-T) -
      horizontalIntegral
        (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
          logDeriv (poleClearedCompletedDedekindZetaContinuation K) s)
        (-ε) (1 + ε) T +
      (2 : ℂ) • verticalSegmentIntegral
        (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
          logDeriv (poleClearedCompletedDedekindZetaContinuation K) s)
        (1 + ε) (-T) T =
      (2 * Real.pi * I) *
        ∑ p ∈ completedDedekindZetaZerosInClosedRectangle
            K (-ε) (1 + ε) (-T) T,
          poitouTransform (regularizedScaledTartar y δ) p *
            (completedDedekindZetaZeroDivisor K p : ℂ) := by
  have hb : 1 / 2 ≤ 1 + ε := by linarith
  have h :=
    regularizedPoitou_centeredRectangle_identity K hδ hb hT
      (y := y) (b := 1 + ε) (by simp_all)
  simp_all

theorem regularizedPoitou_zeroFreeRectangle_im_nonneg
    {y δ ε T : ℝ} (hy : y ≠ 0) (hδ : 0 < δ)
    (hε : 0 < ε) (hT : 0 ≤ T)
    (hboundary : ∀ z ∈ Icc (-ε) (1 + ε) ×ℂ Icc (-T) T,
      (z.re = -ε ∨ z.re = 1 + ε ∨ z.im = -T ∨ z.im = T) →
        poleClearedCompletedDedekindZetaContinuation K z ≠ 0) :
    0 ≤
      (horizontalIntegral
          (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
            logDeriv (poleClearedCompletedDedekindZetaContinuation K) s)
          (-ε) (1 + ε) (-T) -
        horizontalIntegral
          (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
            logDeriv (poleClearedCompletedDedekindZetaContinuation K) s)
          (-ε) (1 + ε) T +
        (2 : ℂ) • verticalSegmentIntegral
          (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
            logDeriv (poleClearedCompletedDedekindZetaContinuation K) s)
          (1 + ε) (-T) T).im := by
  rw [regularizedPoitou_zeroFreeRectangle_identity K hδ hε hT hboundary]
  let S :=
    ∑ p ∈ completedDedekindZetaZerosInClosedRectangle
        K (-ε) (1 + ε) (-T) T,
      poitouTransform (regularizedScaledTartar y δ) p *
        (completedDedekindZetaZeroDivisor K p : ℂ)
  have hS : 0 ≤ S.re := by
    dsimp [S]
    exact
      re_sum_poitouTransform_regularized_completedZetaZerosInClosedRectangle_nonneg
        K hy hδ (-ε) (1 + ε) (-T) T
  change 0 ≤ ((2 * Real.pi : ℂ) * Complex.I * S).im
  simp only [mul_im, mul_re, ofReal_re, ofReal_im, I_re,
    I_im, mul_zero, mul_one, sub_zero, add_zero]
  norm_num
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  have hp : 0 ≤ (2 : ℝ) * Real.pi :=
    mul_nonneg htwo Real.pi_pos.le
  exact mul_nonneg hp hS

end NumberField.Odlyzko

end

section

open Complex NumberField Set

namespace NumberField.Odlyzko

theorem regularizedPoitou_completedZetaPole_centeredRectangle_identity
    {y δ b T : ℝ} (hδ : 0 < δ) (hb : 1 < b) (hT : 0 < T) :
    horizontalIntegral
        (fun s ↦
          poitouTransform (regularizedScaledTartar y δ) s *
            completedZetaPoleLogDeriv s)
        (1 - b) b (-T) -
      horizontalIntegral
        (fun s ↦
          poitouTransform (regularizedScaledTartar y δ) s *
            completedZetaPoleLogDeriv s)
        (1 - b) b T +
      (2 : ℂ) • verticalSegmentIntegral
        (fun s ↦
          poitouTransform (regularizedScaledTartar y δ) s *
            completedZetaPoleLogDeriv s)
        b (-T) T =
      4 * Real.pi * I *
        poitouTransform (regularizedScaledTartar y δ) 1 := by
  let q : ℂ → ℂ := fun s ↦
    poitouTransform (regularizedScaledTartar y δ) s *
      completedZetaPoleLogDeriv s
  have hanti : ∀ s, q (1 - s) = -q s :=
    mul_antiInvariant_of_invariant_of_antiInvariant
      (fun s ↦ poitouTransform_one_sub
        (regularizedScaledTartar_even y δ) s)
      completedZetaPoleLogDeriv_one_sub
  change
    horizontalIntegral q (1 - b) b (-T) -
        horizontalIntegral q (1 - b) b T +
        (2 : ℂ) • verticalSegmentIntegral q b (-T) T = _
  rw [← rectangleIntegral_eq_horizontal_sub_add_two_vertical_of_antiInvariant
    hanti]
  have hpole :=
    rectangleIntegral_mul_completedZetaPoleLogDeriv
      (a := 1 - b) (b := b) (u := -T) (v := T)
      (h := poitouTransform (regularizedScaledTartar y δ))
      (by linarith) hb (by linarith) hT
      (by
        intro z _
        exact analyticOnNhd_poitouTransform_regularizedScaledTartar
          hδ z (mem_univ z))
  have h01 :
      poitouTransform (regularizedScaledTartar y δ) 0 =
        poitouTransform (regularizedScaledTartar y δ) 1 := by
    simpa using
      (poitouTransform_one_sub
        (regularizedScaledTartar_even y δ) (1 : ℂ))
  rw [h01] at hpole
  have hrhs :
      2 * (Real.pi : ℂ) * I *
          (poitouTransform (regularizedScaledTartar y δ) 1 +
            poitouTransform (regularizedScaledTartar y δ) 1) =
        4 * (Real.pi : ℂ) * I *
          poitouTransform (regularizedScaledTartar y δ) 1 := by
    ring
  rw [hrhs] at hpole
  simpa only [q, ofReal_neg] using hpole

end NumberField.Odlyzko

end

section

open Complex NumberField Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

theorem regularizedPoitou_subtracted_centeredRectangle_im_lowerBound
    {y δ b T : ℝ} (hy : y ≠ 0) (hδ : 0 < δ)
    (hb : 1 < b) (hT : 0 < T)
    (hboundary : ∀ z ∈ Icc (1 - b) b ×ℂ Icc (-T) T,
      (z.re = 1 - b ∨ z.re = b ∨ z.im = -T ∨ z.im = T) →
        poleClearedCompletedDedekindZetaContinuation K z ≠ 0) :
    -4 * Real.pi *
        (poitouTransform (regularizedScaledTartar y δ) 1).re ≤
      (horizontalIntegral
          (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
            (logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
              completedZetaPoleLogDeriv s))
          (1 - b) b (-T) -
        horizontalIntegral
          (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
            (logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
              completedZetaPoleLogDeriv s))
          (1 - b) b T +
        (2 : ℂ) • verticalSegmentIntegral
          (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
            (logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
              completedZetaPoleLogDeriv s))
          b (-T) T).im := by
  let Φ : ℂ → ℂ :=
    poitouTransform (regularizedScaledTartar y δ)
  let qFull : ℂ → ℂ := fun s ↦
    Φ s * logDeriv (poleClearedCompletedDedekindZetaContinuation K) s
  let qPole : ℂ → ℂ := fun s ↦
    Φ s * completedZetaPoleLogDeriv s
  let qSub : ℂ → ℂ := fun s ↦
    Φ s * (logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
      completedZetaPoleLogDeriv s)
  let z : ℂ := ((1 - b : ℝ) : ℂ) + -(T : ℂ) * I
  let w : ℂ := (b : ℂ) + (T : ℂ) * I
  have hab : 1 - b ≤ b := by linarith
  have huv : -T ≤ T := by linarith
  have hΦanalytic : AnalyticOnNhd ℂ Φ univ :=
    analyticOnNhd_poitouTransform_regularizedScaledTartar hδ
  have hfullInt : RectangleBorderIntegrable qFull z w := by
    simpa only [z, w, ofReal_neg] using
      (rectangleBorderIntegrable_of_continuousAt_boundary
        (f := qFull) hab huv (by
          intro s hs hside
          unfold qFull logDeriv
          exact (hΦanalytic s (mem_univ s)).continuousAt.mul
            ((analyticOnNhd_poleClearedCompletedDedekindZetaContinuation
                K s (mem_univ s)).deriv.continuousAt.div
              (analyticOnNhd_poleClearedCompletedDedekindZetaContinuation
                K s (mem_univ s)).continuousAt
              (hboundary s hs hside))))
  have hpoleInt : RectangleBorderIntegrable qPole z w := by
    simpa only [z, w, ofReal_neg] using
      (rectangleBorderIntegrable_of_continuousAt_boundary
        (f := qPole) hab huv (by
          intro s hs hside
          have hs0 : s ≠ 0 := by
            intro heq
            subst s
            simp only [zero_re, zero_im] at hside
            grind
          have hs1 : s ≠ 1 := by
            intro heq
            subst s
            simp only [one_re, one_im] at hside
            grind
          unfold qPole completedZetaPoleLogDeriv
          apply (hΦanalytic s (mem_univ s)).continuousAt.mul
          apply ContinuousAt.add
          · exact continuousAt_const.div continuousAt_id hs0
          · exact continuousAt_const.div
              (continuousAt_id.sub continuousAt_const)
              (sub_ne_zero.mpr hs1)))
  have hsubPointwise :
      qSub = fun s ↦ qFull s - qPole s := by grind
  have hrectSub :
      rectangleIntegral qSub z w =
        rectangleIntegral qFull z w - rectangleIntegral qPole z w := by
    rw [hsubPointwise]
    exact rectangleIntegral_sub hfullInt hpoleInt
  let EFull : ℂ :=
    horizontalIntegral qFull (1 - b) b (-T) -
      horizontalIntegral qFull (1 - b) b T +
      (2 : ℂ) • verticalSegmentIntegral qFull b (-T) T
  let EPole : ℂ :=
    horizontalIntegral qPole (1 - b) b (-T) -
      horizontalIntegral qPole (1 - b) b T +
      (2 : ℂ) • verticalSegmentIntegral qPole b (-T) T
  let ESub : ℂ :=
    horizontalIntegral qSub (1 - b) b (-T) -
      horizontalIntegral qSub (1 - b) b T +
      (2 : ℂ) • verticalSegmentIntegral qSub b (-T) T
  have hfullRect : EFull = rectangleIntegral qFull z w := by
    simpa only [EFull, z, w, ofReal_neg] using
      (rectangleIntegral_eq_horizontal_sub_add_two_vertical_of_antiInvariant
        (b := b) (T := T) (f := qFull)
        (fun s ↦
          regularizedPoitou_mul_completedZetaLogDeriv_one_sub K y δ s)).symm
  have hpoleRect : EPole = rectangleIntegral qPole z w := by
    simpa only [EPole, z, w, ofReal_neg] using
      (rectangleIntegral_eq_horizontal_sub_add_two_vertical_of_antiInvariant
        (b := b) (T := T) (f := qPole)
        (fun s ↦ mul_antiInvariant_of_invariant_of_antiInvariant
          (fun u ↦ poitouTransform_one_sub
            (regularizedScaledTartar_even y δ) u)
          completedZetaPoleLogDeriv_one_sub s)).symm
  have hsubAnti : ∀ s, qSub (1 - s) = -qSub s := by
    intro s
    dsimp only [qSub, Φ]
    rw [poitouTransform_one_sub (regularizedScaledTartar_even y δ),
      logDeriv_poleClearedCompletedDedekindZetaContinuation_one_sub_all K,
      completedZetaPoleLogDeriv_one_sub]
    ring
  have hsubRect : ESub = rectangleIntegral qSub z w := by
    simpa only [ESub, z, w, ofReal_neg] using
      (rectangleIntegral_eq_horizontal_sub_add_two_vertical_of_antiInvariant
        (b := b) (T := T) (f := qSub) hsubAnti).symm
  have hESub : ESub = EFull - EPole := by simp_all
  have hfullNonneg : 0 ≤ EFull.im := by
    have hε : 0 < b - 1 := by linarith
    have h :=
      regularizedPoitou_zeroFreeRectangle_im_nonneg
        K hy hδ hε hT.le
        (by
          simp_all)
    have hleft : -(b - 1) = 1 - b := by ring
    grind
  have hpole :
      EPole =
        4 * Real.pi * I *
          poitouTransform (regularizedScaledTartar y δ) 1 := by
    simpa only [EPole, qPole, Φ] using
      regularizedPoitou_completedZetaPole_centeredRectangle_identity
        hδ hb hT
  have hpoleIm :
      EPole.im =
        4 * Real.pi *
          (poitouTransform (regularizedScaledTartar y δ) 1).re := by
    rw [hpole]
    simp
  change -4 * Real.pi * (Φ 1).re ≤ ESub.im
  rw [hESub, sub_im, hpoleIm]
  nlinarith

end NumberField.Odlyzko

end

namespace NumberField.Odlyzko

theorem numericalCertificate_of_integral_le {J : ℝ} (hJ : J ≤ 2 / 5) :
    Real.log (33 / 4) ≤
      Real.eulerMascheroniConstant + Real.log (4 * Real.pi) - J - 20 * Real.pi / 123 := by
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hx : 0 ≤ (16 * Real.pi / 33 - 1) := by
    nlinarith
  have hlog :
      2 * (16 * Real.pi / 33 - 1) / ((16 * Real.pi / 33 - 1) + 2) ≤
        Real.log (16 * Real.pi / 33) := by
    simpa only [add_sub_cancel] using Real.le_log_one_add_of_nonneg hx
  have hrat :
      (862 : ℝ) / 2081 <
        2 * (16 * Real.pi / 33 - 1) / ((16 * Real.pi / 33 - 1) + 2) := by
    have hden' : 0 < (16 * Real.pi / 33 - 1) + 2 := by positivity
    rw [lt_div_iff₀ hden']
    norm_num [div_eq_mul_inv] at *
    nlinarith
  have hlogTarget :
      (862 : ℝ) / 2081 < Real.log (4 * Real.pi) - Real.log (33 / 4) := by
    rw [← Real.log_div (by positivity) (by norm_num), show
      (4 * Real.pi) / (33 / 4) = 16 * Real.pi / 33 by ring]
    grind
  have hγ : (1 / 2 : ℝ) < Real.eulerMascheroniConstant :=
    Real.one_half_lt_eulerMascheroniConstant
  have hbudget :
      (2 / 5 : ℝ) < 1 / 2 + 862 / 2081 - 21 / 41 := by
    norm_num
  nlinarith [Real.pi_lt_d2]

end NumberField.Odlyzko

section

open Complex MeasureTheory Real Set

namespace NumberField.Odlyzko

/-- A gauss digamma vertical majorant used in the Odlyzko-bound argument. -/
noncomputable def gaussDigammaVerticalMajorant (σ x : ℝ) : ℝ :=
  (Real.exp (-x) + Real.exp (-σ * x)) /
    (1 - Real.exp (-x))

end NumberField.Odlyzko

end

section

open MeasureTheory Real Set

namespace NumberField.Odlyzko

/-- A regularized archimedean integrand used in the Odlyzko-bound argument. -/
noncomputable def regularizedArchimedeanIntegrand
    (y δ x : ℝ) : ℝ :=
  (1 - regularizedScaledTartar y δ x) / Real.sinh x

theorem one_sub_regularizedScaledTartar_le_sq
    {δ : ℝ} (hδ : 0 ≤ δ) (y x : ℝ) :
    1 - regularizedScaledTartar y δ x ≤
      (y ^ 2 / 5 + δ) * x ^ 2 := by
  let f := scaledTartarTestFunction y x
  let q := δ * x ^ 2
  have hf1 : f ≤ 1 := tartarTestFunction_le_one _
  have hq0 : 0 ≤ q := mul_nonneg hδ (sq_nonneg x)
  have hexp0 : 0 ≤ 1 - Real.exp (-q) := by simp_all
  have hexp : 1 - Real.exp (-q) ≤ q := by
    have h := Real.add_one_le_exp (-q)
    nlinarith
  have hfexp : f * (1 - Real.exp (-q)) ≤ q := by
    calc
      f * (1 - Real.exp (-q)) ≤ 1 * (1 - Real.exp (-q)) := by
        exact mul_le_mul_of_nonneg_right hf1 hexp0
      _ ≤ q := by grind
  have htartar :
      1 - f ≤ y ^ 2 / 5 * x ^ 2 := by
    dsimp only [f, scaledTartarTestFunction]
    have h := one_sub_tartarTestFunction_le_sq_div_five (y * x)
    nlinarith
  unfold regularizedScaledTartar
  grind

theorem regularizedArchimedeanIntegrand_nonneg
    {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 < x) (y : ℝ) :
    0 ≤ regularizedArchimedeanIntegrand y δ x := by
  unfold regularizedArchimedeanIntegrand
  exact div_nonneg
    (sub_nonneg.mpr (regularizedScaledTartar_le_one hδ))
    (Real.sinh_pos_iff.mpr hx).le

theorem regularizedArchimedeanIntegrand_le_linear
    {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 < x) (y : ℝ) :
    regularizedArchimedeanIntegrand y δ x ≤
      (y ^ 2 / 5 + δ) * x := by
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hxs : x ≤ Real.sinh x := Real.self_le_sinh_iff.mpr hx.le
  rw [regularizedArchimedeanIntegrand, div_le_iff₀ hs]
  calc
    1 - regularizedScaledTartar y δ x ≤
        (y ^ 2 / 5 + δ) * x ^ 2 :=
      one_sub_regularizedScaledTartar_le_sq hδ y x
    _ = ((y ^ 2 / 5 + δ) * x) * x := by ring
    _ ≤ ((y ^ 2 / 5 + δ) * x) * Real.sinh x := by
      gcongr

theorem integrableOn_regularizedArchimedeanIntegrand_Ioc_zero_one
    {δ : ℝ} (hδ : 0 ≤ δ) (y : ℝ) :
    IntegrableOn (regularizedArchimedeanIntegrand y δ) (Ioc 0 1) := by
  have hmajor :
      IntegrableOn (fun x : ℝ ↦ (y ^ 2 / 5 + δ) * x) (Ioc 0 1) :=
    (by fun_prop : Continuous (fun x : ℝ ↦
      (y ^ 2 / 5 + δ) * x)).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
  apply Integrable.mono' hmajor
  · unfold regularizedArchimedeanIntegrand
    exact (((measurable_const.sub
      (continuous_regularizedScaledTartar y δ).measurable).div
        Real.continuous_sinh.measurable).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (regularizedArchimedeanIntegrand_nonneg hδ hx.1 y)]
    exact regularizedArchimedeanIntegrand_le_linear hδ hx.1 y

theorem integrableOn_regularizedArchimedeanIntegrand_Ioi_one
    {δ : ℝ} (hδ : 0 ≤ δ) (y : ℝ) :
    IntegrableOn (regularizedArchimedeanIntegrand y δ) (Ioi 1) := by
  have hmajor :
      IntegrableOn (fun x : ℝ ↦ (8 / 3 : ℝ) * Real.exp (-x)) (Ioi 1) :=
    (integrableOn_exp_neg_Ioi 1).const_mul _
  apply Integrable.mono' hmajor
  · unfold regularizedArchimedeanIntegrand
    exact (((measurable_const.sub
      (continuous_regularizedScaledTartar y δ).measurable).div
        Real.continuous_sinh.measurable).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (regularizedArchimedeanIntegrand_nonneg hδ hx0 y)]
    calc
      regularizedArchimedeanIntegrand y δ x ≤
          1 / Real.sinh x := by
        unfold regularizedArchimedeanIntegrand
        exact div_le_div_of_nonneg_right
          (sub_le_self _ (regularizedScaledTartar_nonneg y δ x))
          (Real.sinh_pos_iff.mpr hx0).le
      _ ≤ (8 / 3 : ℝ) * Real.exp (-x) :=
        one_div_sinh_le_exp_tail hx.le

theorem integrableOn_regularizedArchimedeanIntegrand_Ioi
    {δ : ℝ} (hδ : 0 ≤ δ) (y : ℝ) :
    IntegrableOn (regularizedArchimedeanIntegrand y δ) (Ioi 0) := by
  have hunion : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by simp
  rw [← hunion]
  exact
    (integrableOn_regularizedArchimedeanIntegrand_Ioc_zero_one hδ y).union
      (integrableOn_regularizedArchimedeanIntegrand_Ioi_one hδ y)

end NumberField.Odlyzko

end

section

open Filter MeasureTheory Real Set
open scoped Topology

namespace NumberField.Odlyzko

/-- A regularized archimedean majorant used in the Odlyzko-bound argument. -/
noncomputable def regularizedArchimedeanMajorant
    (y x : ℝ) : ℝ :=
  if x ≤ 1 then (y ^ 2 / 5 + 1) * x
  else (8 / 3 : ℝ) * Real.exp (-x)

theorem integrableOn_regularizedArchimedeanMajorant_Ioi
    (y : ℝ) :
    IntegrableOn (regularizedArchimedeanMajorant y) (Ioi 0) := by
  have hnear :
      IntegrableOn (regularizedArchimedeanMajorant y) (Ioc 0 1) := by
    have hlin :
        IntegrableOn (fun x : ℝ ↦ (y ^ 2 / 5 + 1) * x) (Ioc 0 1) :=
      (by fun_prop : Continuous (fun x : ℝ ↦
        (y ^ 2 / 5 + 1) * x)).integrableOn_Icc.mono_set
          Ioc_subset_Icc_self
    apply hlin.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    simp [regularizedArchimedeanMajorant, hx.2]
  have htail :
      IntegrableOn (regularizedArchimedeanMajorant y) (Ioi 1) := by
    have hexp :
        IntegrableOn
          (fun x : ℝ ↦ (8 / 3 : ℝ) * Real.exp (-x)) (Ioi 1) :=
      (integrableOn_exp_neg_Ioi 1).const_mul _
    apply hexp.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change 1 < x at hx
    simp [regularizedArchimedeanMajorant, not_le_of_gt hx]
  have hunion : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by simp
  rw [← hunion]
  exact hnear.union htail

theorem norm_regularizedArchimedeanIntegrand_le_majorant
    {δ x : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hx : 0 < x) (y : ℝ) :
    ‖regularizedArchimedeanIntegrand y δ x‖ ≤
      regularizedArchimedeanMajorant y x := by
  rw [Real.norm_eq_abs,
    abs_of_nonneg (regularizedArchimedeanIntegrand_nonneg hδ hx y)]
  by_cases hx1 : x ≤ 1
  · rw [regularizedArchimedeanMajorant, ite_eq_left hx1]
    exact
      (regularizedArchimedeanIntegrand_le_linear hδ hx y).trans
        (mul_le_mul_of_nonneg_right
          (by linarith : y ^ 2 / 5 + δ ≤ y ^ 2 / 5 + 1) hx.le)
  · rw [regularizedArchimedeanMajorant, ite_eq_right hx1]
    have hxone : 1 ≤ x := le_of_not_ge hx1
    calc
      regularizedArchimedeanIntegrand y δ x ≤
          1 / Real.sinh x := by
        unfold regularizedArchimedeanIntegrand
        exact div_le_div_of_nonneg_right
          (sub_le_self _ (regularizedScaledTartar_nonneg y δ x))
          (Real.sinh_pos_iff.mpr hx).le
      _ ≤ (8 / 3 : ℝ) * Real.exp (-x) :=
        one_div_sinh_le_exp_tail hxone

theorem tendsto_integral_regularizedArchimedeanIntegrand_nhdsGT_zero
    (y : ℝ) :
    Tendsto
      (fun δ : ℝ ↦
        ∫ x : ℝ in Ioi 0,
          regularizedArchimedeanIntegrand y δ x)
      (𝓝[>] 0)
      (𝓝 (archimedeanIntegral y)) := by
  unfold archimedeanIntegral
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := regularizedArchimedeanMajorant y)
  · filter_upwards [] with δ
    unfold regularizedArchimedeanIntegrand
    exact (((measurable_const.sub
      (continuous_regularizedScaledTartar y δ).measurable).div
        Real.continuous_sinh.measurable).aestronglyMeasurable)
  · have hlt :
        ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < 1 :=
      Filter.Eventually.filter_mono inf_le_left
        (Iio_mem_nhds zero_lt_one)
    filter_upwards [self_mem_nhdsWithin, hlt] with δ hδ hδ1
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_regularizedArchimedeanIntegrand_le_majorant
      hδ.le hδ1.le hx y
  · exact integrableOn_regularizedArchimedeanMajorant_Ioi y
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    unfold regularizedArchimedeanIntegrand archimedeanIntegrand
    simpa [scaledTartarTestFunction] using
      tendsto_nhdsWithin_of_tendsto_nhds
        ((tendsto_const_nhds.sub
          (tendsto_regularizedScaledTartar_nhds_zero y x))
        |>.div_const (Real.sinh x))

theorem tendsto_integral_inverseGaussKernel_regularizedScaledTartar_nhdsGT_zero
    (y : ℝ) :
    Tendsto
      (fun δ : ℝ ↦
        ∫ x : ℝ in Ioi 0,
          inverseGaussKernel (regularizedScaledTartar y δ) x)
      (𝓝[>] 0)
      (𝓝 (archimedeanIntegral y - Real.log 2)) := by
  have harch :=
    tendsto_integral_regularizedArchimedeanIntegrand_nhdsGT_zero y
  apply harch.sub_const (Real.log 2) |>.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [← integral_fermiDiracKernel,
    ← integral_sub
      (integrableOn_regularizedArchimedeanIntegrand_Ioi hδ.le y)
      integrableOn_fermiDiracKernel_Ioi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (inverseGaussKernel_eq hx).symm

end NumberField.Odlyzko

end

section

open Complex Real Set

namespace NumberField.Odlyzko

theorem norm_gaussDigammaIntegrand_vertical_le_four_div
    {σ t x : ℝ} (hσ : 0 ≤ σ) (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖gaussDigammaIntegrand (σ + t * I) x‖ ≤ 4 / x := by
  have hden : x / 2 ≤ 1 - Real.exp (-x) :=
    half_mul_le_one_sub_exp_neg hx.le hx1
  have hnum :
      Real.exp (-x) + Real.exp (-σ * x) ≤ 2 := by
    have hsecond : Real.exp (-σ * x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        simp_all)
    linarith
  calc
    ‖gaussDigammaIntegrand (σ + t * I) x‖ ≤
        (Real.exp (-x) + Real.exp (-σ * x)) /
          (1 - Real.exp (-x)) :=
      norm_gaussDigammaIntegrand_vertical_le σ t hx
    _ ≤ 2 / (x / 2) := by
      exact div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 4 / x := by grind

theorem norm_gaussDigammaIntegrand_vertical_le_sqrt
    {σ t x : ℝ} (hσ : 0 ≤ σ) (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖gaussDigammaIntegrand (σ + t * I) x‖ ≤
      4 * Real.sqrt (‖(σ : ℂ) + t * I - 1‖ / x) := by
  let N : ℝ := ‖(σ : ℂ) + t * I - 1‖
  have hN : 0 ≤ N := norm_nonneg _
  by_cases hsmall : N * x ≤ 1
  · have hlocal :
        ‖gaussDigammaIntegrand (σ + t * I) x‖ ≤ 4 * N := by
      apply norm_gaussDigammaIntegrand_le_local
        (s := (σ : ℂ) + t * I) hx hx1
      grind
    have hNsqrt : N ≤ Real.sqrt (N / x) := by
      rw [Real.le_sqrt hN (div_nonneg hN hx.le)]
      apply (le_div_iff₀ hx).mpr
      nlinarith
    grind
  · have hlarge : 1 ≤ N * x := le_of_not_ge hsmall
    have hinvSqrt : 1 / x ≤ Real.sqrt (N / x) := by
      rw [Real.le_sqrt (by positivity) (div_nonneg hN hx.le)]
      rw [div_pow]
      rw [div_le_div_iff₀ (sq_pos_of_pos hx) hx]
      nlinarith
    change
      ‖gaussDigammaIntegrand (σ + t * I) x‖ ≤
        4 * Real.sqrt (N / x)
    exact
      (norm_gaussDigammaIntegrand_vertical_le_four_div hσ hx hx1).trans
        (by
          grind)

end NumberField.Odlyzko

end

section

open Complex MeasureTheory Real Set

namespace NumberField.Odlyzko

private theorem sqrt_add_abs_mul_norm_poitouTransform_le_rpow
    {δ : ℝ} (hδ : 0 < δ) (y σ : ℝ) {t : ℝ} (ht : 1 ≤ |t|) :
    Real.sqrt (|σ - 1| + |t|) *
        ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖ ≤
      Real.sqrt (|σ - 1| + 1) *
        (∫ x : ℝ,
          ‖poitouVerticalProfileSecondDerivative
            (regularizedScaledTartar y δ)
            (regularizedScaledTartarDerivative y δ)
            (regularizedScaledTartarSecondDerivative y δ) σ x‖) *
        |t| ^ (-(3 : ℝ) / 2) := by
  let A : ℝ :=
    ∫ x : ℝ,
      ‖poitouVerticalProfileSecondDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ)
        (regularizedScaledTartarSecondDerivative y δ) σ x‖
  have htpos : 0 < |t| := zero_lt_one.trans_le ht
  have hsqrt :
      Real.sqrt (|σ - 1| + |t|) ≤
        Real.sqrt (|σ - 1| + 1) * Real.sqrt |t| := by
    rw [← Real.sqrt_mul (by positivity)]
    gcongr
    nlinarith [abs_nonneg (σ - 1)]
  have hquad :
      |t| ^ 2 *
          ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖ ≤ A :=
    sq_abs_mul_norm_poitouTransform_regularized_le hδ y σ t
  have hnorm :
      ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖ ≤
        A / |t| ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos htpos)).2 (by
      grind)
  calc
    Real.sqrt (|σ - 1| + |t|) *
        ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖ ≤
      (Real.sqrt (|σ - 1| + 1) * Real.sqrt |t|) *
        (A / |t| ^ 2) := by gcongr
    _ = Real.sqrt (|σ - 1| + 1) * A *
        (Real.sqrt |t| / |t| ^ 2) := by ring
    _ = _ := by
      rw [show Real.sqrt |t| / |t| ^ 2 = |t| ^ (-(3 : ℝ) / 2) by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast]
        rw [← Real.rpow_sub htpos]
        grind]

theorem integrable_sqrt_add_abs_mul_norm_poitouTransform_regularized
    {δ : ℝ} (hδ : 0 < δ) (y σ : ℝ) :
    Integrable (fun t : ℝ ↦
      Real.sqrt (|σ - 1| + |t|) *
        ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖) := by
  let Φ : ℝ → ℂ := fun t ↦
    poitouTransform (regularizedScaledTartar y δ) (σ + t * I)
  let A : ℝ :=
    ∫ x : ℝ,
      ‖poitouVerticalProfileSecondDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ)
        (regularizedScaledTartarSecondDerivative y δ) σ x‖
  let C : ℝ := Real.sqrt (|σ - 1| + 1) * A
  have hΦ : Integrable Φ :=
    poitouTransform_regularizedScaledTartar_vertical_integrable hδ y σ
  have hcont : Continuous (fun t : ℝ ↦
      Real.sqrt (|σ - 1| + |t|) * ‖Φ t‖) := by
    have hΦcont : Continuous Φ := by
      rw [continuous_iff_continuousAt]
      intro t
      have hin : ContinuousAt
          (fun u : ℝ ↦ (σ : ℂ) + u * I) t := by
        fun_prop
      have hout :
          ContinuousAt
            (poitouTransform (regularizedScaledTartar y δ))
            (σ + t * I) :=
        (analyticOnNhd_poitouTransform_regularizedScaledTartar
          hδ (σ + t * I) (mem_univ _)).continuousAt
      simpa only [Φ, ContinuousAt, Function.comp_def] using
        Filter.Tendsto.comp hout hin
    fun_prop
  have hpow :
      IntegrableOn (fun u : ℝ ↦ u ^ (-(3 : ℝ) / 2)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hpos :
      IntegrableOn (fun t : ℝ ↦
        Real.sqrt (|σ - 1| + |t|) * ‖Φ t‖) (Ioi 1) := by
    apply (hpow.const_mul C).mono'
    · exact hcont.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change 1 < t at ht
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
      change
        Real.sqrt (|σ - 1| + |t|) * ‖Φ t‖ ≤
          C * t ^ (-(3 : ℝ) / 2)
      simpa only [abs_of_pos (zero_lt_one.trans ht)] using
        sqrt_add_abs_mul_norm_poitouTransform_le_rpow
          hδ y σ (t := t) (by
            grind)
  have hnegMajor :
      IntegrableOn (fun t : ℝ ↦ C * (-t) ^ (-(3 : ℝ) / 2))
        (Iio (-1)) := by
    have hpowC :
        IntegrableOn (fun u : ℝ ↦ C * u ^ (-(3 : ℝ) / 2))
          (Ioi 1) :=
      (show Integrable (fun u : ℝ ↦ u ^ (-(3 : ℝ) / 2))
          (volume.restrict (Ioi 1)) from hpow).const_mul C
    have hpowC' :
        IntegrableOn (fun u : ℝ ↦ C * u ^ (-(3 : ℝ) / 2))
          (Ioi (-(-1 : ℝ))) := by simp_all
    exact hpowC'.comp_neg_Iio
  have hneg :
      IntegrableOn (fun t : ℝ ↦
        Real.sqrt (|σ - 1| + |t|) * ‖Φ t‖) (Iio (-1)) := by
    apply hnegMajor.mono'
    · exact hcont.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
      change t < -1 at ht
      have htneg : t < 0 := ht.trans (by norm_num)
      have habs : |t| = -t := abs_of_neg htneg
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
      change
        Real.sqrt (|σ - 1| + |t|) * ‖Φ t‖ ≤
          C * (-t) ^ (-(3 : ℝ) / 2)
      simpa only [habs] using
        sqrt_add_abs_mul_norm_poitouTransform_le_rpow
          hδ y σ (t := t) (by grind)
  have hmid :
      IntegrableOn (fun t : ℝ ↦
        Real.sqrt (|σ - 1| + |t|) * ‖Φ t‖) (Icc (-1) 1) := by
    apply ((hΦ.norm.const_mul (Real.sqrt (|σ - 1| + 1))).integrableOn).mono'
    · exact hcont.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
      gcongr
      grind
  have huniv : Iio (-1 : ℝ) ∪ Icc (-1) 1 ∪ Ioi 1 = univ := by simp
  rw [← integrableOn_univ]
  change IntegrableOn
    (fun t : ℝ ↦ Real.sqrt (|σ - 1| + |t|) * ‖Φ t‖) univ
  rw [← huniv]
  exact (hneg.union hmid).union hpos

end NumberField.Odlyzko

end

section

open Complex MeasureTheory Real Set

namespace NumberField.Odlyzko

private theorem integrableOn_four_div_sqrt_Ioc :
    IntegrableOn (fun x : ℝ ↦ 4 / Real.sqrt x) (Ioc 0 1) := by
  have hp :
      IntegrableOn (fun x : ℝ ↦ 4 * x ^ (-(1 : ℝ) / 2)) (Ioo 0 1) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2
      (by norm_num)).const_mul 4
  have hp' :
      IntegrableOn (fun x : ℝ ↦ 4 * x ^ (-(1 : ℝ) / 2)) (Ioc 0 1) :=
    hp.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm
  apply hp'.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have he : (-(1 : ℝ) / 2) = -(1 / 2) := by ring
  rw [Real.sqrt_eq_rpow, he, Real.rpow_neg hx.1.le]
  ring

private theorem norm_regularizedPoitou_mul_gauss_le_sqrt_product
    {δ : ℝ} (y σ t : ℝ) {x : ℝ}
    (hσ : 0 ≤ σ) (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        gaussDigammaIntegrand (σ + t * I) x‖ ≤
      (Real.sqrt (|σ - 1| + |t|) *
        ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖) *
      (4 / Real.sqrt x) := by
  have hnorm :
      ‖(σ : ℂ) + t * I - 1‖ ≤ |σ - 1| + |t| := by
    rw [show (σ : ℂ) + t * I - 1 =
        ((σ - 1 : ℝ) : ℂ) + (t : ℂ) * I by
      push_cast
      ring]
    calc
      ‖((σ - 1 : ℝ) : ℂ) + (t : ℂ) * I‖ ≤
          ‖((σ - 1 : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ :=
        norm_add_le _ _
      _ = |σ - 1| + |t| := by
        rw [Complex.norm_real, Real.norm_eq_abs, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  have hsqrt :
      Real.sqrt (‖(σ : ℂ) + t * I - 1‖ / x) ≤
        Real.sqrt (|σ - 1| + |t|) / Real.sqrt x := by
    rw [Real.sqrt_div (norm_nonneg _)]
    exact div_le_div_of_nonneg_right
      (Real.sqrt_le_sqrt hnorm) (Real.sqrt_nonneg _)
  rw [norm_mul]
  calc
    ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖ *
        ‖gaussDigammaIntegrand (σ + t * I) x‖ ≤
      ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖ *
        (4 * Real.sqrt (‖(σ : ℂ) + t * I - 1‖ / x)) := by
      gcongr
      exact norm_gaussDigammaIntegrand_vertical_le_sqrt hσ hx hx1
    _ ≤
      ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖ *
        (4 * (Real.sqrt (|σ - 1| + |t|) / Real.sqrt x)) := by
      gcongr
    _ = _ := by ring

private theorem integrableOn_gaussDigammaVerticalTailMajorant
    {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (gaussDigammaVerticalMajorant σ) (Ioi 1) := by
  let C : ℝ := (1 - Real.exp (-1))⁻¹
  have hfirst :
      IntegrableOn (fun x : ℝ ↦ Real.exp (-x)) (Ioi 1) := by
    simpa only [neg_mul, one_mul] using
      (integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 1)
  have hsecond :
      IntegrableOn (fun x : ℝ ↦ Real.exp (-σ * x)) (Ioi 1) :=
    integrableOn_exp_mul_Ioi (by linarith) 1
  have hmajor :
      IntegrableOn
        (fun x : ℝ ↦ C * (Real.exp (-x) + Real.exp (-σ * x)))
        (Ioi 1) :=
    (hfirst.add hsecond).const_mul C
  apply hmajor.mono'
  · change AEStronglyMeasurable
      (fun x : ℝ ↦
        (Real.exp (-x) + Real.exp (-σ * x)) /
          (1 - Real.exp (-x)))
      (volume.restrict (Ioi 1))
    exact (by measurability : Measurable (fun x : ℝ ↦
      (Real.exp (-x) + Real.exp (-σ * x)) /
        (1 - Real.exp (-x)))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change 1 < x at hx
    change
      ‖(Real.exp (-x) + Real.exp (-σ * x)) /
          (1 - Real.exp (-x))‖ ≤
        C * (Real.exp (-x) + Real.exp (-σ * x))
    rw [Real.norm_eq_abs]
    have hxpos : 0 < x := zero_lt_one.trans hx
    have hdenPos : 0 < 1 - Real.exp (-x) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hxpos))
    have hnumNonneg :
        0 ≤ Real.exp (-x) + Real.exp (-σ * x) := by positivity
    rw [abs_of_nonneg (div_nonneg hnumNonneg hdenPos.le)]
    change
      (Real.exp (-x) + Real.exp (-σ * x)) /
          (1 - Real.exp (-x)) ≤
      C * (Real.exp (-x) + Real.exp (-σ * x))
    dsimp only [C]
    rw [← div_eq_inv_mul]
    exact div_le_div_of_nonneg_left hnumNonneg
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))
      (by
        gcongr)

theorem integrableOn_uncurry_poitouTransform_regularized_mul_gaussDigammaIntegrand_Ioi
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Integrable
      (Function.uncurry fun t x : ℝ ↦
        poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
          gaussDigammaIntegrand (σ + t * I) x)
      (volume.prod (volume.restrict (Ioi 0))) := by
  let F : ℝ × ℝ → ℂ := Function.uncurry fun t x : ℝ ↦
    poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
      gaussDigammaIntegrand (σ + t * I) x
  have hΦcont : Continuous (fun t : ℝ ↦
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hin : ContinuousAt
        (fun u : ℝ ↦ (σ : ℂ) + u * I) t := by fun_prop
    have hout :
        ContinuousAt
          (poitouTransform (regularizedScaledTartar y δ))
          (σ + t * I) :=
      (analyticOnNhd_poitouTransform_regularizedScaledTartar
        hδ (σ + t * I) (mem_univ _)).continuousAt
    simpa only [ContinuousAt, Function.comp_def] using
      Filter.Tendsto.comp hout hin
  have hmeas : Measurable F := by
    unfold F Function.uncurry gaussDigammaIntegrand
    apply Measurable.mul
    · exact hΦcont.measurable.comp measurable_fst
    · measurability
  have hnear :
      Integrable F
        (volume.prod (volume.restrict (Ioc 0 1))) := by
    have ht :=
      integrable_sqrt_add_abs_mul_norm_poitouTransform_regularized
        hδ y σ
    have hx := integrableOn_four_div_sqrt_Ioc
    have hmajor :=
      ht.mul_prod hx
    apply hmajor.mono' hmeas.aestronglyMeasurable
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le hmeas.norm (by
        apply Measurable.mul
        · apply Measurable.mul
          · measurability
          · exact (hΦcont.measurable.comp measurable_fst).norm
        · measurability))).2
    filter_upwards [] with t
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact norm_regularizedPoitou_mul_gauss_le_sqrt_product
      y σ t hσ.le hx.1 hx.2
  have htail :
      Integrable F
        (volume.prod (volume.restrict (Ioi 1))) := by
    have ht :=
      (poitouTransform_regularizedScaledTartar_vertical_integrable
        hδ y σ).norm
    have hx := integrableOn_gaussDigammaVerticalTailMajorant hσ
    have hmajor := ht.mul_prod hx
    apply hmajor.mono' hmeas.aestronglyMeasurable
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le hmeas.norm (by
        apply Measurable.mul
        · exact (hΦcont.measurable.comp measurable_fst).norm
        · unfold gaussDigammaVerticalMajorant
          measurability))).2
    filter_upwards [] with t
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change
      ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
          gaussDigammaIntegrand (σ + t * I) x‖ ≤
        ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖ *
          gaussDigammaVerticalMajorant σ x
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact norm_gaussDigammaIntegrand_vertical_le
      σ t (zero_lt_one.trans hx)
  have hunion : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by simp
  have hdisjoint : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) :=
    Set.disjoint_left.2 fun _ hx hy ↦ (not_lt_of_ge hx.2) hy
  have hmeasure :
      volume.restrict (Ioi (0 : ℝ)) =
        volume.restrict (Ioc 0 1) + volume.restrict (Ioi 1) := by
    rw [← hunion, Measure.restrict_union hdisjoint measurableSet_Ioi]
  rw [hmeasure, Measure.prod_add]
  exact hnear.add_measure htail

theorem integral_poitouTransform_regularized_mul_integral_gaussDigammaIntegrand_Ioi
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    (∫ t : ℝ,
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        ∫ x : ℝ in Ioi 0,
          gaussDigammaIntegrand (σ + t * I) x) =
      ∫ x : ℝ in Ioi 0,
        ((2 * Real.pi *
          inverseGaussKernel (regularizedScaledTartar y δ) x : ℝ) : ℂ) := by
  let F : ℝ → ℝ → ℂ := fun t x ↦
    poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
      gaussDigammaIntegrand (σ + t * I) x
  have hdouble :=
    integrableOn_uncurry_poitouTransform_regularized_mul_gaussDigammaIntegrand_Ioi
      hδ y hσ
  calc
    _ = ∫ t : ℝ, ∫ x : ℝ in Ioi 0, F t x := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [integral_const_mul]
    _ = ∫ x : ℝ in Ioi 0, ∫ t : ℝ, F t x := by
      exact integral_integral_swap hdouble
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact
        integral_poitouTransform_regularized_mul_gaussDigammaIntegrand
          hδ y σ hx

end NumberField.Odlyzko

end

section

open Complex MeasureTheory Real Set

namespace NumberField.Odlyzko

theorem integral_gaussDigammaIntegrand_eq_digamma_add_euler
    {s : ℂ} (hs : 0 < s.re) :
    (∫ x : ℝ in Ioi 0, gaussDigammaIntegrand s x) =
      Complex.digamma s + Real.eulerMascheroniConstant := by
  have hgauss := gaussDigamma_eq_digamma hs
  unfold gaussDigamma at hgauss
  grind

theorem integrable_poitouTransform_regularized_mul_digamma_add_euler
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun t : ℝ ↦
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        (Complex.digamma (σ + t * I) +
          Real.eulerMascheroniConstant)) := by
  have hdouble :=
    integrableOn_uncurry_poitouTransform_regularized_mul_gaussDigammaIntegrand_Ioi
      hδ y hσ
  have hinter := hdouble.integral_prod_left
  apply hinter.congr
  filter_upwards [] with t
  change
    (∫ x : ℝ in Ioi 0,
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        gaussDigammaIntegrand (σ + t * I) x) =
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        (Complex.digamma (σ + t * I) +
          Real.eulerMascheroniConstant)
  rw [integral_const_mul,
    integral_gaussDigammaIntegrand_eq_digamma_add_euler
      (by simpa using hσ)]

theorem integral_poitouTransform_regularized_mul_digamma_add_euler
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    (∫ t : ℝ,
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        (Complex.digamma (σ + t * I) +
          Real.eulerMascheroniConstant)) =
      ∫ x : ℝ in Ioi 0,
        ((2 * Real.pi *
          inverseGaussKernel (regularizedScaledTartar y δ) x : ℝ) : ℂ) := by
  rw [←
    integral_poitouTransform_regularized_mul_integral_gaussDigammaIntegrand_Ioi
      hδ y hσ]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [integral_gaussDigammaIntegrand_eq_digamma_add_euler
    (by simpa using hσ)]

end NumberField.Odlyzko

end

section

open Complex Ideal IsDedekindDomain NumberField NumberField.InfinitePlace

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

theorem logDeriv_poleClearedContinuation_sub_poles
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
        completedZetaPoleLogDeriv s =
      (Real.log |(discr K : ℝ)| : ℂ) / 2 +
        nrComplexPlaces K *
          (Complex.digamma s -
            Complex.log (2 * (Real.pi : ℂ))) -
        ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
          primePowerLogTerm K pe.1 pe.2 s := by
  have hD : 0 ≤ |(discr K : ℝ)| := abs_nonneg _
  rw [logDeriv_poleClearedCompletedDedekindZetaContinuation_eq_primePower
    K hs]
  unfold completedZetaPoleLogDeriv
  rw [Complex.ofReal_log hD]
  ring

theorem logDeriv_poleClearedContinuation_sub_poles_eq_logDeriv_dedekindZeta
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
        completedZetaPoleLogDeriv s =
      (Real.log |(discr K : ℝ)| : ℂ) / 2 +
        nrComplexPlaces K *
          (Complex.digamma s -
            Complex.log (2 * (Real.pi : ℂ))) +
        logDeriv (dedekindZeta K) s := by
  rw [logDeriv_poleClearedContinuation_sub_poles K hs]
  have hprime :=
    neg_logDeriv_dedekindZeta_eq_tsum_primePower K hs
  grind

end NumberField.Odlyzko

end

section

open Complex Ideal IsDedekindDomain MeasureTheory Real Set
open NumberField.InfinitePlace

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem integrable_poitouTransform_regularized_mul_neg_logDeriv_dedekindZeta
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    Integrable (fun t : ℝ ↦
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        (-logDeriv (dedekindZeta K) (σ + t * I))) := by
  let Φ : ℝ → ℂ := fun t ↦
    poitouTransform (regularizedScaledTartar y δ) (σ + t * I)
  let G : ℝ → ℂ := fun t ↦
    ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
      primePowerLogTerm K pe.1 pe.2 (σ + t * I)
  let b : HeightOneSpectrum (𝓞 K) × ℕ → ℝ := fun pe ↦
    ‖primePowerLogTerm K pe.1 pe.2 (σ : ℂ)‖
  have hΦ : Integrable Φ :=
    poitouTransform_regularizedScaledTartar_vertical_integrable hδ y σ
  have hGmeas : Measurable G := by
    dsimp only [G]
    apply Measurable.tsum
    intro pe
    rw [show
        (fun t : ℝ ↦ primePowerLogTerm K pe.1 pe.2 (σ + t * I)) =
          fun t : ℝ ↦
            (Real.log (primeIdealNorm K pe.1) : ℂ) *
              Complex.exp
                (-(((pe.2 + 1 : ℕ) : ℝ) *
                  Real.log (primeIdealNorm K pe.1)) * (σ + t * I)) by
      funext t
      exact primePowerLogTerm_eq_log_mul_cexp_neg K pe.1 pe.2 _]
    fun_prop
  have hGbound : ∀ t : ℝ, ‖G t‖ ≤ ∑' pe, b pe := by
    intro t
    apply (norm_tsum_le_tsum_norm
      (summable_norm_primePowerLogTerm K
        (s := (σ + t * I : ℂ)) (by simpa using hσ))).trans_eq
    congr 1
    funext pe
    dsimp only [b]
    rw [norm_primePowerLogTerm, norm_primePowerLogTerm]
    simp
  have hprod : Integrable (fun t ↦ Φ t * G t) :=
    hΦ.mul_bdd hGmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hGbound)
  apply hprod.congr
  filter_upwards [] with t
  have hst : 1 < (σ + t * I : ℂ).re := by simpa using hσ
  rw [neg_logDeriv_dedekindZeta_eq_tsum_primePower K hst]

variable [IsTotallyComplex K]

theorem integrable_poitouTransform_regularized_mul_logDeriv_sub_poles
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    Integrable (fun t : ℝ ↦
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        (logDeriv (poleClearedCompletedDedekindZetaContinuation K) (σ + t * I) -
          completedZetaPoleLogDeriv (σ + t * I))) := by
  let Φ : ℝ → ℂ := fun t ↦
    poitouTransform (regularizedScaledTartar y δ) (σ + t * I)
  have hΦ : Integrable Φ :=
    poitouTransform_regularizedScaledTartar_vertical_integrable hδ y σ
  have hEuler :
      Integrable (fun t : ℝ ↦
        Φ t * (Complex.digamma (σ + t * I) +
          Real.eulerMascheroniConstant)) :=
    integrable_poitouTransform_regularized_mul_digamma_add_euler
      hδ y (zero_lt_one.trans hσ)
  have hDig :
      Integrable (fun t : ℝ ↦
        Φ t * (Complex.digamma (σ + t * I) -
          Complex.log (2 * (Real.pi : ℂ)))) := by
    have hconst :=
      hΦ.mul_const
        (Real.eulerMascheroniConstant +
          Complex.log (2 * (Real.pi : ℂ)))
    apply (hEuler.sub hconst).congr
    filter_upwards [] with t
    change
      Φ t * (Complex.digamma (σ + t * I) +
          Real.eulerMascheroniConstant) -
        Φ t * (Real.eulerMascheroniConstant +
          Complex.log (2 * (Real.pi : ℂ))) =
        Φ t * (Complex.digamma (σ + t * I) -
          Complex.log (2 * (Real.pi : ℂ)))
    ring
  have hdisc :
      Integrable (fun t : ℝ ↦
        Φ t * ((Real.log |(discr K : ℝ)| : ℂ) / 2)) :=
    hΦ.mul_const _
  have harch :
      Integrable (fun t : ℝ ↦
        Φ t * (nrComplexPlaces K *
          (Complex.digamma (σ + t * I) -
            Complex.log (2 * (Real.pi : ℂ))))) := by
    apply hDig.const_mul (nrComplexPlaces K) |>.congr
    filter_upwards [] with t
    ring
  have hneg :=
    integrable_poitouTransform_regularized_mul_neg_logDeriv_dedekindZeta
      K hδ y hσ
  have hzeta :
      Integrable (fun t : ℝ ↦
        Φ t * logDeriv (dedekindZeta K) (σ + t * I)) := by
    apply hneg.neg.congr
    filter_upwards [] with t
    change
      -(Φ t * (-logDeriv (dedekindZeta K) (σ + t * I))) =
        Φ t * logDeriv (dedekindZeta K) (σ + t * I)
    ring
  apply (hdisc.add harch |>.add hzeta).congr
  filter_upwards [] with t
  rw [logDeriv_poleClearedContinuation_sub_poles_eq_logDeriv_dedekindZeta
    K (by simpa using hσ)]
  change
    (Φ t * ((Real.log |(discr K : ℝ)| : ℂ) / 2) +
      Φ t * (nrComplexPlaces K *
        (Complex.digamma (σ + t * I) -
          Complex.log (2 * (Real.pi : ℂ))))) +
      Φ t * logDeriv (dedekindZeta K) (σ + t * I) = _
  grind

theorem integral_poitouTransform_regularized_mul_logDeriv_sub_poles
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    (∫ t : ℝ,
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        (logDeriv (poleClearedCompletedDedekindZetaContinuation K) (σ + t * I) -
          completedZetaPoleLogDeriv (σ + t * I))) =
      (2 * Real.pi : ℂ) *
          ((Real.log |(discr K : ℝ)| : ℂ) / 2) +
        nrComplexPlaces K *
          ((∫ x : ℝ in Ioi 0,
              ((2 * Real.pi *
                inverseGaussKernel (regularizedScaledTartar y δ) x : ℝ) : ℂ)) -
            (2 * Real.pi : ℂ) *
              (Real.eulerMascheroniConstant +
                Complex.log (2 * (Real.pi : ℂ)))) -
        ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
          ((2 * Real.pi *
            regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2 : ℝ) : ℂ) := by
  let Φ : ℝ → ℂ := fun t ↦
    poitouTransform (regularizedScaledTartar y δ) (σ + t * I)
  let A : ℝ → ℂ := fun t ↦
    Φ t * ((Real.log |(discr K : ℝ)| : ℂ) / 2)
  let B : ℝ → ℂ := fun t ↦
    Φ t * (nrComplexPlaces K *
      (Complex.digamma (σ + t * I) -
        Complex.log (2 * (Real.pi : ℂ))))
  let C : ℝ → ℂ := fun t ↦
    Φ t * logDeriv (dedekindZeta K) (σ + t * I)
  have hΦ : Integrable Φ :=
    poitouTransform_regularizedScaledTartar_vertical_integrable hδ y σ
  have hEuler :
      Integrable (fun t : ℝ ↦
        Φ t * (Complex.digamma (σ + t * I) +
          Real.eulerMascheroniConstant)) :=
    integrable_poitouTransform_regularized_mul_digamma_add_euler
      hδ y (zero_lt_one.trans hσ)
  have hDig :
      Integrable (fun t : ℝ ↦
        Φ t * (Complex.digamma (σ + t * I) -
          Complex.log (2 * (Real.pi : ℂ)))) := by
    have hconst :=
      hΦ.mul_const
        (Real.eulerMascheroniConstant +
          Complex.log (2 * (Real.pi : ℂ)))
    apply (hEuler.sub hconst).congr
    filter_upwards [] with t
    change
      Φ t * (Complex.digamma (σ + t * I) +
          Real.eulerMascheroniConstant) -
        Φ t * (Real.eulerMascheroniConstant +
          Complex.log (2 * (Real.pi : ℂ))) =
        Φ t * (Complex.digamma (σ + t * I) -
          Complex.log (2 * (Real.pi : ℂ)))
    ring
  have hA : Integrable A := hΦ.mul_const _
  have hB : Integrable B := by
    apply hDig.const_mul (nrComplexPlaces K)
      |>.congr
    filter_upwards [] with t
    grind
  have hneg :=
    integrable_poitouTransform_regularized_mul_neg_logDeriv_dedekindZeta
      K hδ y hσ
  have hC : Integrable C := by
    apply hneg.neg.congr
    filter_upwards [] with t
    change
      -(Φ t * (-logDeriv (dedekindZeta K) (σ + t * I))) =
        C t
    grind
  have hdecomp :
      (fun t : ℝ ↦
        Φ t *
          (logDeriv (poleClearedCompletedDedekindZetaContinuation K) (σ + t * I) -
            completedZetaPoleLogDeriv (σ + t * I))) =
        fun t ↦ A t + B t + C t := by
    funext t
    rw [logDeriv_poleClearedContinuation_sub_poles_eq_logDeriv_dedekindZeta
      K (by simpa using hσ)]
    grind
  have hDigValue :
      (∫ t : ℝ,
        Φ t * (Complex.digamma (σ + t * I) -
          Complex.log (2 * (Real.pi : ℂ)))) =
        (∫ x : ℝ in Ioi 0,
          ((2 * Real.pi *
            inverseGaussKernel (regularizedScaledTartar y δ) x : ℝ) : ℂ)) -
        (2 * Real.pi : ℂ) *
          (Real.eulerMascheroniConstant +
            Complex.log (2 * (Real.pi : ℂ))) := by
    have harch :=
      integral_poitouTransform_regularized_mul_digamma_add_euler
        hδ y (zero_lt_one.trans hσ)
    have hmass :=
      integral_poitouTransform_regularized_vertical hδ y σ
    have hconstValue :
        (∫ t : ℝ,
          Φ t * (Real.eulerMascheroniConstant +
            Complex.log (2 * (Real.pi : ℂ)))) =
          (2 * Real.pi : ℂ) *
            (Real.eulerMascheroniConstant +
              Complex.log (2 * (Real.pi : ℂ))) := by
      rw [integral_mul_const, hmass]
    rw [← harch, ← hconstValue, ← integral_sub hEuler
      (hΦ.mul_const
        (Real.eulerMascheroniConstant +
          Complex.log (2 * (Real.pi : ℂ))))]
    apply integral_congr_ae
    filter_upwards [] with t
    ring
  rw [show
      (fun t : ℝ ↦
        poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
          (logDeriv (poleClearedCompletedDedekindZetaContinuation K) (σ + t * I) -
            completedZetaPoleLogDeriv (σ + t * I))) =
        fun t ↦ A t + B t + C t by
      grind]
  change
    (∫ t : ℝ, (A + B) t + C t) =
      (2 * Real.pi : ℂ) *
          ((Real.log |(discr K : ℝ)| : ℂ) / 2) +
        nrComplexPlaces K *
          ((∫ x : ℝ in Ioi 0,
              ((2 * Real.pi *
                inverseGaussKernel (regularizedScaledTartar y δ) x : ℝ) : ℂ)) -
            (2 * Real.pi : ℂ) *
              (Real.eulerMascheroniConstant +
                Complex.log (2 * (Real.pi : ℂ)))) -
        ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
          ((2 * Real.pi *
            regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2 : ℝ) : ℂ)
  rw [integral_add (hA.add hB) hC]
  change
    ((∫ t : ℝ, A t + B t) + ∫ t : ℝ, C t) = _
  rw [integral_add hA hB]
  have hmass :=
    integral_poitouTransform_regularized_vertical hδ y σ
  have hprime :=
    integral_poitouTransform_regularized_mul_neg_logDeriv_dedekindZeta_eq_tsum
      K hδ y hσ
  dsimp only [A, B, C]
  rw [integral_mul_const, hmass]
  rw [show
      (fun t : ℝ ↦
        Φ t * (nrComplexPlaces K *
          (Complex.digamma (σ + t * I) -
            Complex.log (2 * (Real.pi : ℂ))))) =
        fun t ↦ (nrComplexPlaces K : ℂ) *
          (Φ t * (Complex.digamma (σ + t * I) -
            Complex.log (2 * (Real.pi : ℂ)))) by
      grind,
    integral_const_mul, hDigValue]
  have hCvalue :
      (∫ t : ℝ,
        Φ t * logDeriv (dedekindZeta K) (σ + t * I)) =
        -(∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
          ((2 * Real.pi *
            regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2 : ℝ) : ℂ)) := by
    rw [← hprime, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with t
    ring
  grind

theorem re_integral_poitouTransform_regularized_mul_logDeriv_sub_poles
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    (∫ t : ℝ,
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        (logDeriv (poleClearedCompletedDedekindZetaContinuation K) (σ + t * I) -
          completedZetaPoleLogDeriv (σ + t * I))).re =
      2 * Real.pi *
        (Real.log |(discr K : ℝ)| / 2 +
          nrComplexPlaces K *
            ((∫ x : ℝ in Ioi 0,
                inverseGaussKernel (regularizedScaledTartar y δ) x) -
              Real.eulerMascheroniConstant -
              Real.log (2 * Real.pi)) -
          ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
            regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2) := by
  have h :=
    integral_poitouTransform_regularized_mul_logDeriv_sub_poles
      K hδ y hσ
  have hlog :
      Complex.log (2 * (Real.pi : ℂ)) =
        (Real.log (2 * Real.pi) : ℂ) := by
    rw [show 2 * (Real.pi : ℂ) =
        ((2 * Real.pi : ℝ) : ℂ) by
      simp]
    exact (Complex.ofReal_log (by positivity)).symm
  have hintegral :
      (∫ x : ℝ in Ioi 0,
        ((2 * Real.pi *
          inverseGaussKernel (regularizedScaledTartar y δ) x : ℝ) : ℂ)) =
        ((∫ x : ℝ in Ioi 0,
          2 * Real.pi *
            inverseGaussKernel (regularizedScaledTartar y δ) x : ℝ) : ℂ) :=
    integral_ofReal
  rw [hlog] at h
  rw [hintegral] at h
  rw [← Complex.ofReal_tsum
    (fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
      2 * Real.pi *
        regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2)] at h
  have hscale :
      (∫ x : ℝ in Ioi 0,
        2 * Real.pi *
          inverseGaussKernel (regularizedScaledTartar y δ) x) =
        2 * Real.pi *
          ∫ x : ℝ in Ioi 0,
            inverseGaussKernel (regularizedScaledTartar y δ) x := by
    rw [integral_const_mul]
  rw [hscale, tsum_mul_left] at h
  push_cast at h
  have hre := congrArg Complex.re h
  have hweights :
      Summable (fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
        regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2) :=
    summable_regularizedPrimePowerPoitouWeight K hδ y hσ
  have hweightsC :
      Summable (fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
        ((regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2 : ℝ) : ℂ)) :=
    Complex.summable_ofReal.mpr hweights
  simp only [mul_re, mul_im, add_re, add_im, sub_re, sub_im, div_re, ofReal_re, ofReal_im,
    mul_zero, zero_mul, sub_zero, add_zero, natCast_re, natCast_im] at hre
  rw [Complex.re_tsum hweightsC] at hre
  rw [Complex.im_tsum hweightsC] at hre
  simp only [ofReal_re, ofReal_im] at hre
  have htwoRe : (2 : ℂ).re = 2 := by norm_num
  have htwoIm : (2 : ℂ).im = 0 := by norm_num
  have htwoNormSq : Complex.normSq (2 : ℂ) = 4 := by norm_num [Complex.normSq]
  grind

end NumberField.Odlyzko

end

section

open NumberField Module

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem le_rootDiscr_of_log_le_logDiscr_div_finrank {c : ℝ} (hc : 0 < c)
    (h :
      Real.log c ≤ Real.log |(discr K : ℝ)| / finrank ℚ K) :
    c ≤ rootDiscr K := by
  have hD : 0 < |(discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  rw [rootDiscr_def, Int.cast_abs]
  calc
    c = Real.exp (Real.log c) := (Real.exp_log hc).symm
    _ ≤ Real.exp (Real.log |(discr K : ℝ)| / finrank ℚ K) :=
      Real.exp_le_exp.mpr h
    _ = |(discr K : ℝ)| ^ ((finrank ℚ K : ℝ)⁻¹) := by
      rw [Real.rpow_def_of_pos hD]
      grind

/-- A totally complex poitou estimate used in the Odlyzko-bound argument. -/
def TotallyComplexPoitouEstimate : Prop :=
  Real.log |(discr K : ℝ)| / finrank ℚ K ≥
    Real.eulerMascheroniConstant + Real.log (4 * Real.pi) -
      archimedeanIntegral odlyzkoScale -
      12 * Real.pi / (5 * finrank ℚ K * odlyzkoScale)

theorem target_le_rootDiscr_of_poitouEstimate
    (hdim : 18 ≤ finrank ℚ K) (hP : TotallyComplexPoitouEstimate K) :
    (8.25 : ℝ) ≤ rootDiscr K := by
  have hJ := NumericalCertificate.archimedeanIntegral_le
  have hnum := numericalCertificate_of_integral_le hJ
  have hdegree := degreeCorrection_le_degreeEighteen hdim
  have hlog :
      Real.log (33 / 4) ≤ Real.log |(discr K : ℝ)| / finrank ℚ K := by
    unfold TotallyComplexPoitouEstimate at hP
    linarith
  norm_num [show (8.25 : ℝ) = 33 / 4 by norm_num]
  exact le_rootDiscr_of_log_le_logDiscr_div_finrank K (by norm_num) hlog

theorem odlyzkoBound_of_poitouEstimate (hdim : 18 ≤ finrank ℚ K)
    (hP : TotallyComplexPoitouEstimate K) :
    |(discr K : ℝ)| ≥ (8.25 : ℝ) ^ finrank ℚ K :=
  target_pow_finrank_le_abs_discr K
    (target_le_rootDiscr_of_poitouEstimate K hdim hP)

end NumberField.Odlyzko

end

section

open Complex Filter Ideal IsDedekindDomain MeasureTheory Real Set
open NumberField.InfinitePlace
open Module
open scoped Topology

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

/-- A regularized right vertical lower bound used in the Odlyzko-bound argument. -/
def RegularizedRightVerticalLowerBound (y σ : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    -(2 * Real.pi) *
        (poitouTransform (regularizedScaledTartar y δ) 1).re ≤
      (∫ t : ℝ,
        poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
          (logDeriv (poleClearedCompletedDedekindZetaContinuation K) (σ + t * I) -
            completedZetaPoleLogDeriv (σ + t * I))).re

theorem poitouEstimate_of_regularizedRightVerticalLowerBound
    {y σ : ℝ} (hy : 0 < y) (hσ : 1 < σ)
    (hbound : RegularizedRightVerticalLowerBound K y σ) :
    Real.log |(discr K : ℝ)| / finrank ℚ K ≥
      Real.eulerMascheroniConstant + Real.log (4 * Real.pi) -
        archimedeanIntegral y -
        12 * Real.pi / (5 * finrank ℚ K * y) := by
  let m : ℝ := nrComplexPlaces K
  let n : ℝ := finrank ℚ K
  have hmn : 2 * m = n := by
    dsimp only [m, n]
    exact_mod_cast two_mul_nrComplexPlaces_eq_finrank K
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (finrank_pos : 0 < finrank ℚ K)
  have hm : 0 < m := by nlinarith
  let L : ℝ → ℝ := fun δ ↦
    Real.eulerMascheroniConstant + Real.log (2 * Real.pi) -
      (∫ x : ℝ in Ioi 0,
        inverseGaussKernel (regularizedScaledTartar y δ) x) -
      (poitouTransform (regularizedScaledTartar y δ) 1).re / m
  have hLle :
      ∀ δ : ℝ, 0 < δ →
        L δ ≤ Real.log |(discr K : ℝ)| / n := by
    intro δ hδ
    have hformula :=
      re_integral_poitouTransform_regularized_mul_logDeriv_sub_poles
        K hδ y hσ
    have hcontour := hbound δ hδ
    rw [hformula] at hcontour
    have hprime :
        0 ≤ ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
          regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2 :=
      tsum_regularizedPrimePowerPoitouWeight_nonneg K y δ
    dsimp only [L]
    change
      Real.eulerMascheroniConstant + Real.log (2 * Real.pi) -
          (∫ x : ℝ in Ioi 0,
            inverseGaussKernel (regularizedScaledTartar y δ) x) -
          (poitouTransform (regularizedScaledTartar y δ) 1).re / m ≤
        Real.log |(discr K : ℝ)| / n
    have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
    rw [← hmn]
    field_simp [hm.ne']
    nlinarith
  have htransform :
      Tendsto
        (fun δ : ℝ ↦
          (poitouTransform (regularizedScaledTartar y δ) 1).re)
        (𝓝[>] 0)
        (𝓝 (6 * Real.pi / (5 * y))) := by
    have hcomplex :=
      tendsto_poitouTransform_regularizedScaledTartar_nhdsGT_zero
        hy.ne' (s := (1 : ℂ)) (by simp)
    have h := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
    rw [poitouTransform_scaledTartar_one hy] at h
    change
      Tendsto
        (fun δ : ℝ ↦
          (poitouTransform (regularizedScaledTartar y δ) 1).re)
        (𝓝[>] 0)
        (𝓝 (((6 * Real.pi / (5 * y) : ℝ) : ℂ).re)) at h
    simpa only [ofReal_re] using h
  have hinverse :=
    tendsto_integral_inverseGaussKernel_regularizedScaledTartar_nhdsGT_zero y
  have hL :
      Tendsto L (𝓝[>] 0)
        (𝓝
          (Real.eulerMascheroniConstant + Real.log (2 * Real.pi) -
            (archimedeanIntegral y - Real.log 2) -
            (6 * Real.pi / (5 * y)) / m)) := by
    dsimp only [L]
    exact
      ((tendsto_const_nhds.add tendsto_const_nhds).sub hinverse).sub
        (htransform.div_const m)
  have hlimit :
      Real.eulerMascheroniConstant + Real.log (2 * Real.pi) -
          (archimedeanIntegral y - Real.log 2) -
          (6 * Real.pi / (5 * y)) / m ≤
        Real.log |(discr K : ℝ)| / n :=
    le_of_tendsto hL (by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      simp_all)
  have hlog :
      Real.log (2 * Real.pi) + Real.log 2 =
        Real.log (4 * Real.pi) := by
    rw [← Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0)]
    grind
  change
    Real.eulerMascheroniConstant + Real.log (2 * Real.pi) -
          (archimedeanIntegral y - Real.log 2) -
          (6 * Real.pi / (5 * y)) / m ≤
        Real.log |(discr K : ℝ)| / n at hlimit
  change
    Real.eulerMascheroniConstant + Real.log (4 * Real.pi) -
          archimedeanIntegral y -
          12 * Real.pi / (5 * n * y) ≤
        Real.log |(discr K : ℝ)| / n
  rw [← hmn] at hlimit
  have hlimit' :
      Real.eulerMascheroniConstant +
          (Real.log (2 * Real.pi) + Real.log 2) -
          archimedeanIntegral y -
          (6 * Real.pi / (5 * y)) / m ≤
        Real.log |(discr K : ℝ)| / (2 * m) := by
    linarith
  rw [hlog] at hlimit'
  rw [← hmn]
  (convert hlimit' using 1; grind)

theorem totallyComplexPoitouEstimate_of_regularizedRightVerticalLowerBound
    {σ : ℝ} (hσ : 1 < σ)
    (hbound : RegularizedRightVerticalLowerBound K odlyzkoScale σ) :
    TotallyComplexPoitouEstimate K := by
  unfold TotallyComplexPoitouEstimate
  exact poitouEstimate_of_regularizedRightVerticalLowerBound
    K odlyzkoScale_pos hσ hbound

end NumberField.Odlyzko

end

section

open Complex Filter MeasureTheory Real Set
open scoped Topology

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

/-- A regularized subtracted horizontal vanishing used in the Odlyzko-bound argument. -/
def RegularizedSubtractedHorizontalVanishing
    (y δ b : ℝ) : Prop :=
  ∃ T : ℕ → ℝ,
    Tendsto T atTop atTop ∧
    (∀ n, 0 < T n ∧
      ∀ z ∈ Icc (1 - b) b ×ℂ Icc (-(T n)) (T n),
        (z.re = 1 - b ∨ z.re = b ∨
          z.im = -(T n) ∨ z.im = T n) →
          poleClearedCompletedDedekindZetaContinuation K z ≠ 0) ∧
    Tendsto
      (fun n ↦
        horizontalIntegral
            (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
              (logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
                completedZetaPoleLogDeriv s))
            (1 - b) b (-(T n)) -
          horizontalIntegral
            (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
              (logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
                completedZetaPoleLogDeriv s))
            (1 - b) b (T n))
      atTop (𝓝 0)

theorem regularizedRightVerticalLowerBound_of_horizontalVanishing
    {y δ b : ℝ} (hy : y ≠ 0) (hδ : 0 < δ) (hb : 1 < b)
    (hvanish : RegularizedSubtractedHorizontalVanishing K y δ b) :
    -(2 * Real.pi) *
        (poitouTransform (regularizedScaledTartar y δ) 1).re ≤
      (∫ t : ℝ,
        poitouTransform (regularizedScaledTartar y δ) (b + t * I) *
          (logDeriv (poleClearedCompletedDedekindZetaContinuation K) (b + t * I) -
            completedZetaPoleLogDeriv (b + t * I))).re := by
  obtain ⟨T, hT, hboundary, hhorizontal⟩ := hvanish
  let q : ℝ → ℂ := fun t ↦
    poitouTransform (regularizedScaledTartar y δ) (b + t * I) *
      (logDeriv (poleClearedCompletedDedekindZetaContinuation K) (b + t * I) -
        completedZetaPoleLogDeriv (b + t * I))
  let H : ℕ → ℂ := fun n ↦
    horizontalIntegral
        (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
          (logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
            completedZetaPoleLogDeriv s))
        (1 - b) b (-(T n)) -
      horizontalIntegral
        (fun s ↦ poitouTransform (regularizedScaledTartar y δ) s *
          (logDeriv (poleClearedCompletedDedekindZetaContinuation K) s -
            completedZetaPoleLogDeriv s))
        (1 - b) b (T n)
  let V : ℕ → ℂ := fun n ↦ ∫ t : ℝ in -(T n)..T n, q t
  let R : ℂ := ∫ t : ℝ, q t
  have hq : Integrable q :=
    integrable_poitouTransform_regularized_mul_logDeriv_sub_poles
      K hδ y hb
  have hV : Tendsto V atTop (𝓝 R) := by
    exact intervalIntegral_tendsto_integral hq
      ((tendsto_neg_atBot_iff).2 hT) hT
  have hH : Tendsto H atTop (𝓝 0) := hhorizontal
  have hfinite :
      ∀ n, -4 * Real.pi *
          (poitouTransform (regularizedScaledTartar y δ) 1).re ≤
        (H n + 2 * (I * V n)).im := by
    intro n
    have h :=
      regularizedPoitou_subtracted_centeredRectangle_im_lowerBound
        K hy hδ hb (hboundary n).1 (hboundary n).2
    simpa only [H, V, q, verticalSegmentIntegral, smul_eq_mul,
      ofReal_ofNat, mul_assoc] using h
  have hcomplex :
      Tendsto (fun n ↦ H n + 2 * (I * V n))
        atTop (𝓝 (2 * (I * R))) := by
    simpa only [zero_add] using
      hH.add (tendsto_const_nhds.mul (tendsto_const_nhds.mul hV))
  have him :
      Tendsto (fun n ↦ (H n + 2 * (I * V n)).im)
        atTop (𝓝 ((2 * (I * R)).im)) :=
    Complex.continuous_im.continuousAt.tendsto.comp hcomplex
  have hlim :
      -4 * Real.pi *
          (poitouTransform (regularizedScaledTartar y δ) 1).re ≤
        (2 * (I * R)).im :=
    ge_of_tendsto him (Filter.Eventually.of_forall hfinite)
  change
    -(2 * Real.pi) *
        (poitouTransform (regularizedScaledTartar y δ) 1).re ≤ R.re
  have hvalue : (2 * (I * R)).im = 2 * R.re := by simp
  grind

theorem regularizedRightVerticalLowerBound_of_forall_horizontalVanishing
    {y b : ℝ} (hy : y ≠ 0) (hb : 1 < b)
    (hvanish : ∀ δ : ℝ, 0 < δ →
      RegularizedSubtractedHorizontalVanishing K y δ b) :
    RegularizedRightVerticalLowerBound K y b := by
  intro δ hδ
  exact regularizedRightVerticalLowerBound_of_horizontalVanishing
    K hy hδ hb (hvanish δ hδ)

end NumberField.Odlyzko

end
