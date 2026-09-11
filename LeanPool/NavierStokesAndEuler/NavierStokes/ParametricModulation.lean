/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricRephase
import LeanPool.NavierStokesAndEuler.NavierStokes.UniformCone
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import LeanPool.NavierStokesAndEuler.NavierStokes.ConeAlgebra
import Mathlib.Analysis.SpecialFunctions.Sqrt
public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothLoop
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Joint periodic primitives and realization of the constructed true-cone loops

The primitives in this file are actual normalized interval integrals. Their
joint smoothness is derived through compact-interval parameter integration.
-/

section

/-!
# Construction of the true-cone loop

This file assembles the actual exponential moment inverse, a smooth speed
correction, compact uniform cone margins, and the smooth phase change.
-/

section

/-!
# The actual exponential tilt variance

This file studies the integral normalizer and variance used by Lemma 6.1.
All moments below are Lebesgue integrals of the actual cosine exponential
family, not postulated properties of an abstract variance map.
-/

@[expose] public section

namespace NavierStokes.LoopVariance

noncomputable section

open MeasureTheory ProbabilityTheory Set
open SmoothLoop
open scoped Interval ContDiff Topology

/-- Angle measure, given by `volume.restrict (Ioc 0 (2 * Real.pi))`. -/
def angleMeasure : Measure ℝ := volume.restrict (Ioc 0 (2 * Real.pi))

theorem integrable_exp_cos (s : ℝ) :
    Integrable (fun θ => Real.exp (s * Real.cos θ)) angleMeasure :=
  ((Real.continuous_exp.comp (continuous_const.mul Real.continuous_cos)).intervalIntegrable
    0 (2 * Real.pi)).1

theorem integrableExpSet_cos : integrableExpSet Real.cos angleMeasure = univ := by
  ext s
  simp only [mem_univ, iff_true]
  exact integrable_exp_cos s

theorem mem_interior_integrableExpSet (s : ℝ) :
    s ∈ interior (integrableExpSet Real.cos angleMeasure) := by
  rw [integrableExpSet_cos, interior_univ]
  exact mem_univ s

/-- The angular exponential moments, including the normalizer at order zero. -/
def moment (n : ℕ) (s : ℝ) : ℝ :=
  (∫ θ, Real.cos θ ^ n * Real.exp (s * Real.cos θ) ∂angleMeasure) / (2 * Real.pi)

theorem moment_eq_angularMean (n : ℕ) (s : ℝ) :
    moment n s = angularMean (fun θ => Real.cos θ ^ n * Real.exp (s * Real.cos θ)) := by
  simp only [moment, angularMean, angleMeasure,
    intervalIntegral.integral_of_le (le_of_lt period_pos)]

theorem normalizer_eq_moment (s : ℝ) : expNormalizer s = moment 0 s := by
  rw [moment_eq_angularMean]
  simp only [pow_zero, one_mul, expNormalizer]

theorem moment_zero_pos (s : ℝ) : 0 < moment 0 s := by
  rw [← normalizer_eq_moment]
  exact expNormalizer_pos s

theorem moment_hasDerivAt (n : ℕ) (s : ℝ) :
    HasDerivAt (moment n) (moment (n + 1) s) s := by
  exact (hasDerivAt_integral_pow_mul_exp_real (mem_interior_integrableExpSet s) n).div_const _

theorem moment_analyticAt (n : ℕ) (s : ℝ) : AnalyticAt ℝ (moment n) s := by
  have heq : moment n = fun t => iteratedDeriv n (mgf Real.cos angleMeasure) t / (2 * Real.pi) := by
    funext t
    rw [iteratedDeriv_mgf (mem_interior_integrableExpSet t) n]
    rfl
  rw [heq]
  exact (analyticAt_iteratedDeriv_mgf (mem_interior_integrableExpSet s) n).div
    analyticAt_const period_ne_zero

theorem moment_contDiff (n : ℕ) : ContDiff ℝ (∞ : WithTop ℕ∞) (moment n) :=
  contDiff_iff_contDiffAt.mpr (fun s => (moment_analyticAt n s).contDiffAt)

theorem normalizer_analyticAt (s : ℝ) : AnalyticAt ℝ expNormalizer s := by
  have heq : expNormalizer = moment 0 := funext normalizer_eq_moment
  rw [heq]
  exact moment_analyticAt 0 s

theorem normalizer_contDiff : ContDiff ℝ (∞ : WithTop ℕ∞) expNormalizer :=
  contDiff_iff_contDiffAt.mpr (fun s => (normalizer_analyticAt s).contDiffAt)

theorem normalizer_hasDerivAt (s : ℝ) : HasDerivAt expNormalizer (moment 1 s) s := by
  have heq : expNormalizer = moment 0 := funext normalizer_eq_moment
  rw [heq]
  exact moment_hasDerivAt 0 s

/-- Weighted square, given by `angularMean (fun θ => (Real.cos θ - c) ^ 2 * Real.exp (s *
Real.cos θ))`. -/
def weightedSquare (s c : ℝ) : ℝ :=
  angularMean (fun θ => (Real.cos θ - c) ^ 2 * Real.exp (s * Real.cos θ))

theorem weightedSquare_pos (s c : ℝ) : 0 < weightedSquare s c := by
  unfold weightedSquare angularMean
  apply div_pos _ period_pos
  apply intervalIntegral.integral_pos period_pos
  · exact (((Real.continuous_cos.sub continuous_const).pow 2).mul
      (Real.continuous_exp.comp (continuous_const.mul Real.continuous_cos))).continuousOn
  · intro θ _
    exact mul_nonneg (sq_nonneg _) (le_of_lt (Real.exp_pos _))
  · by_cases hc : c = 1
    · refine ⟨Real.pi, ⟨Real.pi_pos.le, by linarith [Real.pi_pos]⟩, ?_⟩
      rw [hc, Real.cos_pi]
      positivity
    · refine ⟨0, ⟨le_rfl, period_pos.le⟩, ?_⟩
      rw [Real.cos_zero]
      apply mul_pos
      · exact sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm hc))
      · exact Real.exp_pos _

theorem weightedSquare_expansion (s c : ℝ) :
    weightedSquare s c = moment 2 s - (2 * c) * moment 1 s + c ^ 2 * moment 0 s := by
  have he : Continuous (fun θ => Real.exp (s * Real.cos θ)) :=
    Real.continuous_exp.comp (continuous_const.mul Real.continuous_cos)
  have h₁ : Continuous (fun θ => Real.cos θ * Real.exp (s * Real.cos θ)) :=
    Real.continuous_cos.mul he
  have h₂ : Continuous (fun θ => Real.cos θ ^ 2 * Real.exp (s * Real.cos θ)) :=
    (Real.continuous_cos.pow 2).mul he
  have heq : (fun θ => (Real.cos θ - c) ^ 2 * Real.exp (s * Real.cos θ)) =
      (fun θ => (Real.cos θ ^ 2 * Real.exp (s * Real.cos θ) -
        (2 * c) * (Real.cos θ * Real.exp (s * Real.cos θ))) +
        c ^ 2 * Real.exp (s * Real.cos θ)) := by funext θ; ring
  unfold weightedSquare
  rw [heq, angularMean_add _ _ (h₂.fun_sub (continuous_const.fun_mul h₁)) (continuous_const.fun_mul
      he),
    angularMean_sub _ _ h₂ (continuous_const.fun_mul h₁), angularMean_const_mul,
    angularMean_const_mul, moment_eq_angularMean, moment_eq_angularMean, moment_eq_angularMean]
  simp only [pow_one, pow_zero, one_mul]

/-- Log slope, given by `moment 1 s / moment 0 s`. -/
def logSlope (s : ℝ) : ℝ := moment 1 s / moment 0 s

theorem moment_determinant_pos (s : ℝ) :
    0 < moment 2 s * moment 0 s - moment 1 s ^ 2 := by
  have hp := mul_pos (moment_zero_pos s) (weightedSquare_pos s (logSlope s))
  have hid : moment 0 s * weightedSquare s (logSlope s) =
      moment 2 s * moment 0 s - moment 1 s ^ 2 := by
    rw [weightedSquare_expansion]
    unfold logSlope
    have hnz := ne_of_gt (moment_zero_pos s)
    field_simp; ring
  rwa [hid] at hp

theorem logSlope_hasDerivAt (s : ℝ) :
    HasDerivAt logSlope
      ((moment 2 s * moment 0 s - moment 1 s ^ 2) / moment 0 s ^ 2) s := by
  convert! (moment_hasDerivAt 1 s).div (moment_hasDerivAt 0 s) (ne_of_gt (moment_zero_pos s)) using
      1
  ring

theorem logSlope_strictMono : StrictMono logSlope := by
  apply strictMono_of_hasDerivAt_pos logSlope_hasDerivAt
  intro s
  exact div_pos (moment_determinant_pos s) (sq_pos_of_pos (moment_zero_pos s))

/-- The variance of the normalized exponential density itself. The scaled
tilt variance is obtained by multiplication and the substitution `s=μp`. -/
def baseVariance (s : ℝ) : ℝ := expNormalizer (2 * s) / expNormalizer s ^ 2 - 1

theorem baseVariance_eq_integral (s : ℝ) :
    baseVariance s = angularMean (fun θ => (normalizedExp s θ - 1) ^ 2) :=
  (normalizedExp_variance s).symm

theorem baseVariance_zero : baseVariance 0 = 0 := by
  simp [baseVariance, expNormalizer_zero]

theorem baseVariance_nonneg (s : ℝ) : 0 ≤ baseVariance s := by
  rw [baseVariance_eq_integral]
  exact angularMean_nonneg _ (fun θ => sq_nonneg _)

theorem baseVariance_add_one_pos (s : ℝ) : 0 < baseVariance s + 1 := by
  have hp := div_pos (expNormalizer_pos (2 * s)) (sq_pos_of_pos (expNormalizer_pos s))
  dsimp [baseVariance]
  linarith

theorem baseVariance_analyticAt (s : ℝ) : AnalyticAt ℝ baseVariance s := by
  apply AnalyticAt.sub _ analyticAt_const
  exact ((normalizer_analyticAt (2 * s)).comp (analyticAt_const.mul analyticAt_id)).div
    ((normalizer_analyticAt s).pow 2) (pow_ne_zero 2 (ne_of_gt (expNormalizer_pos s)))

theorem baseVariance_contDiff : ContDiff ℝ (∞ : WithTop ℕ∞) baseVariance :=
  contDiff_iff_contDiffAt.mpr (fun s => (baseVariance_analyticAt s).contDiffAt)

theorem baseVariance_hasDerivAt (s : ℝ) :
    HasDerivAt baseVariance (2 * (baseVariance s + 1) * (logSlope (2 * s) - logSlope s)) s := by
  have h := (((normalizer_hasDerivAt (2 * s)).comp s ((hasDerivAt_id s).const_mul 2)).div
    ((normalizer_hasDerivAt s).pow 2) (pow_ne_zero 2 (ne_of_gt (expNormalizer_pos s)))).sub_const 1
  convert! h using 1
  dsimp [baseVariance, logSlope]
  rw [normalizer_eq_moment, normalizer_eq_moment]
  have hnz := ne_of_gt (moment_zero_pos s)
  have hnz₂ := ne_of_gt (moment_zero_pos (2 * s))
  field_simp; ring

theorem baseVariance_deriv_pos {s : ℝ} (hs : 0 < s) : 0 < deriv baseVariance s := by
  rw [(baseVariance_hasDerivAt s).deriv]
  have hlog := logSlope_strictMono (show s < 2 * s by linarith)
  exact mul_pos (mul_pos (by norm_num) (baseVariance_add_one_pos s)) (sub_pos.mpr hlog)

theorem baseVariance_strictMonoOn : StrictMonoOn baseVariance (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) baseVariance_contDiff.continuous.continuousOn
  intro s hs
  rw [interior_Ici] at hs
  exact baseVariance_deriv_pos hs

theorem normalizer_even (s : ℝ) : expNormalizer (-s) = expNormalizer s := by
  let f : ℝ → ℝ := fun θ => Real.exp (s * Real.cos θ)
  have hp : Function.Periodic f (2 * Real.pi) := by
    intro θ
    dsimp [f]
    rw [Real.cos_periodic θ]
  have heq : (fun θ => Real.exp (-s * Real.cos θ)) = fun θ => f (θ + Real.pi) := by
    funext θ
    dsimp [f]
    rw [Real.cos_add_pi]
    congr 1
    ring
  unfold expNormalizer angularMean
  rw [heq, intervalIntegral.integral_comp_add_right]
  have hi := hp.intervalIntegral_add_eq Real.pi 0
  simpa only [zero_add, add_comm (2 * Real.pi) Real.pi] using
    congrArg (fun x : ℝ => x / (2 * Real.pi)) hi

theorem baseVariance_even (s : ℝ) : baseVariance (-s) = baseVariance s := by
  unfold baseVariance
  rw [show 2 * -s = -(2 * s) by ring, normalizer_even, normalizer_even]

theorem baseVariance_pos {s : ℝ} (hs : s ≠ 0) : 0 < baseVariance s := by
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · rw [← baseVariance_even s]
    have h := baseVariance_strictMonoOn (show (0 : ℝ) ∈ Ici (0 : ℝ) by simp)
      (show -s ∈ Ici (0 : ℝ) from le_of_lt (neg_pos.mpr hneg)) (neg_pos.mpr hneg)
    simpa only [baseVariance_zero] using h
  · have h := baseVariance_strictMonoOn (show (0 : ℝ) ∈ Ici (0 : ℝ) by simp)
      (show s ∈ Ici (0 : ℝ) from le_of_lt hpos) hpos
    simpa only [baseVariance_zero] using h

theorem moment_zero_at_zero : moment 0 0 = 1 := by
  rw [← normalizer_eq_moment, expNormalizer_zero]

theorem moment_one_at_zero : moment 1 0 = 0 := by
  rw [moment_eq_angularMean]
  simpa only [pow_one, zero_mul, Real.exp_zero, mul_one] using angularMean_cos

theorem moment_two_at_zero : moment 2 0 = 1 / 2 := by
  rw [moment_eq_angularMean]
  simpa only [zero_mul, Real.exp_zero, mul_one] using angularMean_cos_sq

theorem logSlope_zero : logSlope 0 = 0 := by
  simp only [logSlope, moment_one_at_zero, zero_div]

theorem logSlope_hasDerivAt_zero : HasDerivAt logSlope (1 / 2) 0 := by
  simpa only [moment_zero_at_zero, moment_one_at_zero, moment_two_at_zero,
    mul_one, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero, one_pow, div_one] using
    logSlope_hasDerivAt 0

theorem baseVariance_hasDerivAt_zero : HasDerivAt baseVariance 0 0 := by
  simpa only [baseVariance_zero, mul_zero, logSlope_zero, sub_self] using baseVariance_hasDerivAt 0

theorem baseVariance_deriv_zero : deriv baseVariance 0 = 0 := baseVariance_hasDerivAt_zero.deriv

theorem baseVariance_deriv_hasDerivAt_zero : HasDerivAt (deriv baseVariance) 1 0 := by
  have hd : deriv baseVariance = fun s =>
      2 * (baseVariance s + 1) * (logSlope (2 * s) - logSlope s) :=
    funext (fun s => (baseVariance_hasDerivAt s).deriv)
  rw [hd]
  have hout : HasDerivAt logSlope (1 / 2) (2 * (0 : ℝ)) := by
    simpa only [mul_zero] using logSlope_hasDerivAt_zero
  have h := ((baseVariance_hasDerivAt_zero.add_const 1).const_mul 2).mul
    ((hout.comp 0 ((hasDerivAt_id 0).const_mul 2)).sub
      logSlope_hasDerivAt_zero)
  convert! h using 1
  norm_num [Function.comp_def, baseVariance_zero, logSlope_zero]

theorem baseVariance_second_deriv_zero : iteratedDeriv 2 baseVariance 0 = 1 := by
  rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
  exact baseVariance_deriv_hasDerivAt_zero.deriv

/-- The second divided difference extends `R(s)/s²` analytically across zero. -/
def quadraticFactor : ℝ → ℝ := dslope (dslope baseVariance 0) 0

theorem quadraticFactor_zero : quadraticFactor 0 = 1 / 2 := by
  have hp := (baseVariance_analyticAt 0).hasFPowerSeriesAt
  have hd := hp.has_fpower_series_dslope_fslope.deriv
  rw [quadraticFactor, dslope_same]
  rw [hd]
  change (FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => iteratedDeriv n baseVariance 0 / (n.factorial : ℝ))).fslope.coeff 1 = 1 / 2
  rw [FormalMultilinearSeries.coeff_fslope, FormalMultilinearSeries.coeff_ofScalars,
    baseVariance_second_deriv_zero]
  norm_num

theorem quadraticFactor_identity (s : ℝ) : baseVariance s = s ^ 2 * quadraticFactor s := by
  have h₁ := sub_smul_dslope baseVariance (0 : ℝ) s
  have h₂ := sub_smul_dslope (dslope baseVariance 0) (0 : ℝ) s
  simp only [sub_zero, smul_eq_mul, baseVariance_zero, dslope_same, baseVariance_deriv_zero]
      at h₁ h₂
  change baseVariance s = s ^ 2 * dslope (dslope baseVariance 0) 0 s
  nlinarith [congrArg (fun z : ℝ => s * z) h₂]

theorem quadraticFactor_analyticAt (s : ℝ) : AnalyticAt ℝ quadraticFactor s := by
  by_cases hs : s = 0
  · subst s
    obtain ⟨p, hp⟩ := baseVariance_analyticAt 0
    exact ⟨p.fslope.fslope,
      hp.has_fpower_series_dslope_fslope.has_fpower_series_dslope_fslope⟩
  · have hq : AnalyticAt ℝ (fun t => baseVariance t / t ^ 2) s :=
      (baseVariance_analyticAt s).div (analyticAt_id.pow 2) (pow_ne_zero 2 hs)
    apply hq.congr
    filter_upwards [eventually_ne_nhds hs] with t ht
    rw [quadraticFactor_identity t]
    exact mul_div_cancel_left₀ _ (pow_ne_zero 2 ht)

theorem quadraticFactor_pos (s : ℝ) : 0 < quadraticFactor s := by
  by_cases hs : s = 0
  · rw [hs, quadraticFactor_zero]
    norm_num
  · have h := baseVariance_pos hs
    rw [quadraticFactor_identity] at h
    exact pos_of_mul_pos_right h (sq_nonneg s)

theorem quadraticFactor_even (s : ℝ) : quadraticFactor (-s) = quadraticFactor s := by
  by_cases hs : s = 0
  · simp [hs]
  · have h := baseVariance_even s
    rw [quadraticFactor_identity (-s), quadraticFactor_identity s, neg_sq] at h
    exact mul_left_cancel₀ (pow_ne_zero 2 hs) h

/-- This signed square root is analytic even at the zero-variance point. -/
def signedRoot (s : ℝ) : ℝ := s * Real.sqrt (quadraticFactor s)

theorem signedRoot_contDiff : ContDiff ℝ ω signedRoot := by
  apply contDiff_iff_contDiffAt.mpr
  intro s
  exact contDiffAt_id.mul ((quadraticFactor_analyticAt s).contDiffAt.sqrt
    (ne_of_gt (quadraticFactor_pos s)))

theorem signedRoot_sq (s : ℝ) : signedRoot s ^ 2 = baseVariance s := by
  rw [signedRoot, mul_pow, Real.sq_sqrt (le_of_lt (quadraticFactor_pos s)),
    quadraticFactor_identity]

theorem signedRoot_zero : signedRoot 0 = 0 := by simp [signedRoot]

theorem signedRoot_odd (s : ℝ) : signedRoot (-s) = -signedRoot s := by
  simp only [signedRoot, quadraticFactor_even, neg_mul]

theorem signedRoot_hasDerivAt_zero : HasDerivAt signedRoot (Real.sqrt (1 / 2)) 0 := by
  have hgc : ContDiffAt ℝ (∞ : WithTop ℕ∞) (fun s => Real.sqrt (quadraticFactor s)) 0 :=
    ((quadraticFactor_analyticAt 0).contDiffAt.sqrt
      (ne_of_gt (quadraticFactor_pos 0)))
  have hg := hgc.differentiableAt (by simp)
  have h := (hasDerivAt_id (0 : ℝ)).fun_mul hg.hasDerivAt
  unfold signedRoot
  simpa only [id_eq, one_mul, zero_mul, add_zero, quadraticFactor_zero] using h

theorem normalizer_centered (s : ℝ) :
    expNormalizer s = (∫ θ in -Real.pi..Real.pi, Real.exp (s * Real.cos θ)) / (2 * Real.pi) := by
  have hp : Function.Periodic (fun θ => Real.exp (s * Real.cos θ)) (2 * Real.pi) := by
    intro θ
    dsimp only
    rw [Real.cos_periodic θ]
  have hi := hp.intervalIntegral_add_eq (-Real.pi) 0
  have htop : -Real.pi + 2 * Real.pi = Real.pi := by ring
  simp only [htop, zero_add] at hi
  unfold expNormalizer angularMean
  rw [hi]

/-- Gaussian mass, given by `∫ x : ℝ, Real.exp (-(2 / Real.pi ^ 2) * x ^ 2)`. -/
def gaussianMass : ℝ := ∫ x : ℝ, Real.exp (-(2 / Real.pi ^ 2) * x ^ 2)

theorem gaussianCoefficient_pos : (0 : ℝ) < 2 / Real.pi ^ 2 :=
  div_pos (by norm_num) (sq_pos_of_pos Real.pi_pos)

theorem gaussianMass_pos : 0 < gaussianMass := by
  unfold gaussianMass
  rw [integral_gaussian]
  exact Real.sqrt_pos.mpr (div_pos Real.pi_pos gaussianCoefficient_pos)

theorem gaussian_scaled_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : ℝ => Real.exp (-(2 / Real.pi ^ 2) * (t * x) ^ 2)) := by
  exact (integrable_exp_neg_mul_sq gaussianCoefficient_pos).comp_mul_left' (ne_of_gt ht)

theorem gaussian_scaled_integral (t : ℝ) (ht : 0 < t) :
    (∫ x : ℝ, Real.exp (-(2 / Real.pi ^ 2) * (t * x) ^ 2)) = gaussianMass / t := by
  have h := MeasureTheory.Measure.integral_comp_mul_left
    (fun x : ℝ => Real.exp (-(2 / Real.pi ^ 2) * x ^ 2)) t
  calc
    _ = |t⁻¹| * gaussianMass := by simpa only [smul_eq_mul, gaussianMass] using h
    _ = gaussianMass / t := by rw [abs_of_pos (inv_pos.mpr ht)]; ring

/-- The upper Laplace bound uses Jordan's quadratic cosine inequality and
the ordinary Gaussian integral on the whole real line. -/
theorem normalizer_square_upper (t : ℝ) (ht : 0 < t) :
    expNormalizer (t ^ 2) ≤ Real.exp (t ^ 2) * gaussianMass / ((2 * Real.pi) * t) := by
  have hp : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have he : Continuous (fun x => Real.exp (t ^ 2 * Real.cos x)) :=
    Real.continuous_exp.comp (continuous_const.mul Real.continuous_cos)
  have hg : Continuous (fun x : ℝ => Real.exp (-(2 / Real.pi ^ 2) * (t * x) ^ 2)) := by
    fun_prop
  have hbound : ∀ x ∈ Icc (-Real.pi) Real.pi,
      Real.exp (t ^ 2 * Real.cos x) ≤
        Real.exp (t ^ 2) * Real.exp (-(2 / Real.pi ^ 2) * (t * x) ^ 2) := by
    intro x hx
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hc := Real.cos_le_one_sub_mul_cos_sq (abs_le.mpr hx)
    have hm := mul_le_mul_of_nonneg_left hc (sq_nonneg t)
    convert! hm using 1
    ring
  have hloc := intervalIntegral.integral_mono_on (μ := volume) hp (he.intervalIntegrable _ _)
    ((continuous_const.fun_mul hg).intervalIntegrable _ _) hbound
  rw [intervalIntegral.integral_const_mul] at hloc
  have hglobal : (∫ x in -Real.pi..Real.pi, Real.exp (-(2 / Real.pi ^ 2) * (t * x) ^ 2)) ≤
      gaussianMass / t := by
    rw [← gaussian_scaled_integral t ht, intervalIntegral.integral_of_le hp]
    exact setIntegral_le_integral (gaussian_scaled_integrable t ht)
      (Filter.Eventually.of_forall (fun x => Real.exp_nonneg _))
  have hfull := hloc.trans (mul_le_mul_of_nonneg_left hglobal (Real.exp_nonneg _))
  rw [normalizer_centered]
  apply (div_le_div_of_nonneg_right hfull period_pos.le).trans_eq
  ring

/-- A matching lower bound follows by integrating over `[-1/t,1/t]`.
Only `t≥1` is required, and every constant is explicit. -/
theorem normalizer_double_square_lower (t : ℝ) (ht : 1 ≤ t) :
    2 * Real.exp (2 * t ^ 2 - 1) / ((2 * Real.pi) * t) ≤ expNormalizer (2 * t ^ 2) := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hinvpos : 0 < 1 / t := one_div_pos.mpr htpos
  have hinvone : 1 / t ≤ 1 := (div_le_one htpos).mpr ht
  have hinvpi : 1 / t ≤ Real.pi := le_trans hinvone (by linarith [Real.two_le_pi])
  have hab : -(1 / t) ≤ 1 / t := by linarith
  have he : Continuous (fun x => Real.exp ((2 * t ^ 2) * Real.cos x)) :=
    Real.continuous_exp.comp (continuous_const.mul Real.continuous_cos)
  have hbound : ∀ x ∈ Icc (-(1 / t)) (1 / t),
      Real.exp (2 * t ^ 2 - 1) ≤ Real.exp ((2 * t ^ 2) * Real.cos x) := by
    intro x hx
    have htxhi : t * x ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hx.2 htpos.le
      simpa only [mul_one_div_cancel (ne_of_gt htpos)] using h
    have htxlo : -1 ≤ t * x := by
      have h := mul_le_mul_of_nonneg_left hx.1 htpos.le
      simpa only [mul_neg, mul_one_div_cancel (ne_of_gt htpos)] using h
    have hsq : (t * x) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (show 0 ≤ 1 - t * x by linarith)
        (show 0 ≤ 1 + t * x by linarith)]
    apply Real.exp_le_exp.mpr
    have hc := Real.one_sub_sq_div_two_le_cos (x := x)
    have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 * t ^ 2 by positivity)
    nlinarith
  have hloc := intervalIntegral.integral_mono_on (μ := volume) hab
    (continuous_const.intervalIntegrable _ _) (he.intervalIntegrable _ _) hbound
  rw [intervalIntegral.integral_const] at hloc
  have hsub : (∫ x in -(1 / t)..(1 / t), Real.exp ((2 * t ^ 2) * Real.cos x)) ≤
      ∫ x in -Real.pi..Real.pi, Real.exp ((2 * t ^ 2) * Real.cos x) := by
    exact intervalIntegral.integral_mono_interval (neg_le_neg hinvpi) hab hinvpi
      (Filter.Eventually.of_forall (fun x => Real.exp_nonneg _)) (he.intervalIntegrable _ _)
  have hfull := hloc.trans hsub
  rw [normalizer_centered]
  convert! div_le_div_of_nonneg_right hfull period_pos.le using 1
  simp only [smul_eq_mul]
  ring

/-- Growth constant, given by `2 * (2 * Real.pi) * Real.exp (-1) / gaussianMass ^ 2`. -/
def growthConstant : ℝ := 2 * (2 * Real.pi) * Real.exp (-1) / gaussianMass ^ 2

theorem growthConstant_pos : 0 < growthConstant := by
  unfold growthConstant
  exact div_pos (mul_pos (mul_pos (by norm_num) period_pos) (Real.exp_pos _))
    (sq_pos_of_pos gaussianMass_pos)

theorem baseVariance_square_growth (t : ℝ) (ht : 1 ≤ t) :
    growthConstant * t ≤ baseVariance (t ^ 2) + 1 := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  let U := Real.exp (t ^ 2) * gaussianMass / ((2 * Real.pi) * t)
  let L := 2 * Real.exp (2 * t ^ 2 - 1) / ((2 * Real.pi) * t)
  have hU : 0 < U := by
    have hC := gaussianMass_pos
    dsimp [U]
    positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hden : expNormalizer (t ^ 2) ^ 2 ≤ U ^ 2 :=
    pow_le_pow_left₀ (expNormalizer_pos _).le (normalizer_square_upper t htpos) 2
  have hcalc : growthConstant * t = L / U ^ 2 := by
    dsimp [growthConstant, L, U]
    rw [show 2 * t ^ 2 - 1 = (t ^ 2 + t ^ 2) + (-1) by ring,
      Real.exp_add, Real.exp_add]
    have hT := period_ne_zero
    have htne := ne_of_gt htpos
    have hC := ne_of_gt gaussianMass_pos
    field_simp
  calc
    growthConstant * t = L / U ^ 2 := hcalc
    _ ≤ L / expNormalizer (t ^ 2) ^ 2 :=
      div_le_div_of_nonneg_left hL.le (sq_pos_of_pos (expNormalizer_pos _)) hden
    _ ≤ expNormalizer (2 * t ^ 2) / expNormalizer (t ^ 2) ^ 2 :=
      div_le_div_of_nonneg_right (normalizer_double_square_lower t ht)
        (sq_nonneg (expNormalizer (t ^ 2)))
    _ = baseVariance (t ^ 2) + 1 := by unfold baseVariance; ring

theorem baseVariance_unbounded (B : ℝ) : ∃ s : ℝ, 0 ≤ s ∧ B ≤ baseVariance s := by
  let t := max 1 ((B + 1) / growthConstant)
  have ht : 1 ≤ t := le_max_left _ _
  have hBt : B + 1 ≤ growthConstant * t := by
    have hc := growthConstant_pos
    have h := le_max_right (1 : ℝ) ((B + 1) / growthConstant)
    exact (div_le_iff₀ hc).mp h |>.trans_eq (mul_comm _ _)
  refine ⟨t ^ 2, sq_nonneg t, ?_⟩
  have hg := baseVariance_square_growth t ht
  linarith

theorem baseVariance_tendsto_atTop : Filter.Tendsto baseVariance Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro B
  obtain ⟨s, hs, hB⟩ := baseVariance_unbounded B
  refine ⟨s, fun t ht => hB.trans ?_⟩
  exact baseVariance_strictMonoOn.monotoneOn hs (le_trans hs ht) ht

theorem baseVariance_deriv_neg {s : ℝ} (hs : s < 0) : deriv baseVariance s < 0 := by
  rw [(baseVariance_hasDerivAt s).deriv]
  have hlog := logSlope_strictMono (show 2 * s < s by linarith)
  exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) (baseVariance_add_one_pos s))
    (sub_neg.mpr hlog)

theorem signedRoot_deriv_pos (s : ℝ) : 0 < deriv signedRoot s := by
  by_cases hs : s = 0
  · rw [hs, signedRoot_hasDerivAt_zero.deriv]
    exact Real.sqrt_pos.mpr (by norm_num)
  have hdiff := signedRoot_contDiff.differentiable (by simp)
  have hsq := (hdiff s).hasDerivAt.fun_pow 2
  have heq : (fun x => signedRoot x ^ 2) = baseVariance := funext signedRoot_sq
  rw [heq] at hsq
  have hid : deriv baseVariance s = 2 * signedRoot s * deriv signedRoot s := by
    simpa using hsq.deriv
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · have hR := baseVariance_deriv_neg hneg
    have hS : signedRoot s < 0 :=
      mul_neg_of_neg_of_pos hneg (Real.sqrt_pos.mpr (quadraticFactor_pos s))
    nlinarith
  · have hR := baseVariance_deriv_pos hpos
    have hS : 0 < signedRoot s :=
      mul_pos hpos (Real.sqrt_pos.mpr (quadraticFactor_pos s))
    nlinarith

theorem signedRoot_strictMono : StrictMono signedRoot :=
  strictMono_of_deriv_pos signedRoot_deriv_pos

theorem signedRoot_surjective : Function.Surjective signedRoot := by
  intro y
  obtain ⟨s, hs, hB⟩ := baseVariance_unbounded (y ^ 2 + 1)
  have hS : 0 ≤ signedRoot s := mul_nonneg hs (Real.sqrt_nonneg _)
  have hsq : y ^ 2 ≤ signedRoot s ^ 2 := by rw [signedRoot_sq]; linarith
  have habs : |y| ≤ signedRoot s := by
    simpa only [abs_of_nonneg hS] using (sq_le_sq.mp hsq)
  have hmem : y ∈ Icc (signedRoot (-s)) (signedRoot s) := by
    rw [signedRoot_odd]
    exact abs_le.mp habs
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc (show -s ≤ s by linarith)
    signedRoot_contDiff.continuous.continuousOn hmem
  exact ⟨x, hx⟩

/-- Root homeomorph, given by `(StrictMono.orderIsoOfSurjective signedRoot signedRoot_strictMono
signedRoot_surjective).toHomeomorph`. -/
def rootHomeomorph : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective signedRoot signedRoot_strictMono
      signedRoot_surjective).toHomeomorph

/-- Inverse root, given by `rootHomeomorph.symm`. -/
def inverseRoot : ℝ → ℝ := rootHomeomorph.symm

theorem inverseRoot_right (s : ℝ) : signedRoot (inverseRoot s) = s :=
  rootHomeomorph.apply_symm_apply s

theorem inverseRoot_left (s : ℝ) : inverseRoot (signedRoot s) = s :=
  rootHomeomorph.symm_apply_apply s

theorem inverseRoot_contDiff : ContDiff ℝ ω inverseRoot := by
  apply rootHomeomorph.contDiff_symm_deriv (fun s => ne_of_gt (signedRoot_deriv_pos s))
  · exact fun s => (signedRoot_contDiff.differentiable (by simp) s).hasDerivAt
  · exact signedRoot_contDiff

theorem inverseRoot_zero : inverseRoot 0 = 0 := by
  simpa only [signedRoot_zero] using inverseRoot_left 0

theorem inverseRoot_odd (s : ℝ) : inverseRoot (-s) = -inverseRoot s := by
  apply signedRoot_strictMono.injective
  rw [inverseRoot_right, signedRoot_odd, inverseRoot_right]

theorem inverseRoot_deriv_zero : deriv inverseRoot 0 = 1 / Real.sqrt (1 / 2) := by
  have hinv := (inverseRoot_contDiff.differentiable (by simp) 0).hasDerivAt
  have hout : HasDerivAt signedRoot (Real.sqrt (1 / 2)) (inverseRoot 0) := by
    rw [inverseRoot_zero]
    exact signedRoot_hasDerivAt_zero
  have hcomp := hout.comp 0 hinv
  have heq : signedRoot ∘ inverseRoot = id := funext inverseRoot_right
  rw [heq] at hcomp
  have hprod := hcomp.unique (hasDerivAt_id 0)
  have hroot : Real.sqrt (1 / 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  apply (eq_div_iff hroot).mpr
  nlinarith

/-- An analytic divided difference of the actual inverse, which removes the
apparent `1/p` singularity in the parameter-dependent variance solve. -/
def inverseSlope : ℝ → ℝ := dslope inverseRoot 0

theorem inverseSlope_zero : inverseSlope 0 = 1 / Real.sqrt (1 / 2) := by
  rw [inverseSlope, dslope_same, inverseRoot_deriv_zero]

theorem inverseSlope_identity (s : ℝ) : s * inverseSlope s = inverseRoot s := by
  simpa only [sub_zero, smul_eq_mul, inverseRoot_zero, inverseSlope] using
    sub_smul_dslope inverseRoot (0 : ℝ) s

theorem inverseSlope_analyticAt (s : ℝ) : AnalyticAt ℝ inverseSlope s := by
  by_cases hs : s = 0
  · subst s
    obtain ⟨p, hp⟩ := inverseRoot_contDiff.contDiffAt.analyticAt (x := (0 : ℝ))
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  · have hq : AnalyticAt ℝ (fun t => inverseRoot t / t) s :=
      inverseRoot_contDiff.contDiffAt.analyticAt.div analyticAt_id hs
    apply hq.congr
    filter_upwards [eventually_ne_nhds hs] with t ht
    rw [← inverseSlope_identity t]
    exact mul_div_cancel_left₀ _ ht

theorem inverseSlope_contDiff : ContDiff ℝ ω inverseSlope :=
  contDiff_iff_contDiffAt.mpr (fun s => (inverseSlope_analyticAt s).contDiffAt)

/-- Scaled root, given by `d * μ * Real.sqrt (quadraticFactor (μ * p))`. -/
def scaledRoot (d p μ : ℝ) : ℝ := d * μ * Real.sqrt (quadraticFactor (μ * p))

/-- Solve scale, given by `(r / d) * inverseSlope (p * (r / d))`. -/
def solveScale (d p r : ℝ) : ℝ := (r / d) * inverseSlope (p * (r / d))

theorem solveScale_mul (d p r : ℝ) : solveScale d p r * p = inverseRoot (p * (r / d)) := by
  rw [← inverseSlope_identity]
  unfold solveScale
  ring

theorem solveScale_spec (d p r : ℝ) (hd : d ≠ 0) :
    scaledRoot d p (solveScale d p r) = r := by
  by_cases hp : p = 0
  · subst p
    simp only [solveScale, zero_mul, inverseSlope_zero, scaledRoot, mul_zero, quadraticFactor_zero]
    have hroot : Real.sqrt (1 / 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
  · apply mul_right_cancel₀ hp
    calc
      scaledRoot d p (solveScale d p r) * p =
          d * signedRoot (solveScale d p r * p) := by unfold scaledRoot signedRoot; ring
      _ = d * signedRoot (inverseRoot (p * (r / d))) := by rw [solveScale_mul]
      _ = d * (p * (r / d)) := by rw [inverseRoot_right]
      _ = r * p := by field_simp

theorem scaledRoot_hasDerivAt (d p μ : ℝ) :
    HasDerivAt (scaledRoot d p) (d * deriv signedRoot (μ * p)) μ := by
  by_cases hp : p = 0
  · subst p
    have h := ((hasDerivAt_id μ).const_mul d).mul_const (Real.sqrt (quadraticFactor 0))
    unfold scaledRoot
    simpa only [scaledRoot, mul_zero, signedRoot_hasDerivAt_zero.deriv, quadraticFactor_zero,
      id_eq, mul_one] using h
  · have heq : scaledRoot d p = fun x => (d / p) * signedRoot (x * p) := by
      funext x
      unfold scaledRoot signedRoot
      field_simp
    rw [heq]
    have h := (((signedRoot_contDiff.differentiable (by simp) (μ * p)).hasDerivAt).comp μ
      ((hasDerivAt_id μ).mul_const p)).const_mul (d / p)
    convert! h using 1
    field_simp

theorem scaledRoot_strictMono (d p : ℝ) (hd : 0 < d) : StrictMono (scaledRoot d p) := by
  apply strictMono_of_hasDerivAt_pos (scaledRoot_hasDerivAt d p)
  intro μ
  exact mul_pos hd (signedRoot_deriv_pos _)

theorem scaledRoot_zero (d p : ℝ) : scaledRoot d p 0 = 0 := by simp [scaledRoot]

theorem solveScale_nonneg (d p r : ℝ) (hd : 0 < d) (hr : 0 ≤ r) : 0 ≤ solveScale d p r := by
  apply (scaledRoot_strictMono d p hd).le_iff_le.mp
  rw [scaledRoot_zero, solveScale_spec d p r (ne_of_gt hd)]
  exact hr

theorem solveScale_unique (d p r μ : ℝ) (hd : 0 < d)
    (hμ : scaledRoot d p μ = r) : μ = solveScale d p r := by
  apply (scaledRoot_strictMono d p hd).injective
  rw [hμ, solveScale_spec d p r (ne_of_gt hd)]

/-- Smooth dependence on the prescribed *signed square root* of variance,
including at `p=0` and `r=0`. -/
theorem solveScale_joint_contDiff (d : ℝ) :
    ContDiff ℝ ω (fun x : ℝ × ℝ => solveScale d x.1 x.2) := by
  exact (contDiff_snd.div_const d).mul
    (inverseSlope_contDiff.comp (contDiff_fst.mul (contDiff_snd.div_const d)))

theorem solveScale_smooth_family {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d p r : E → ℝ) (hd : ContDiff ℝ (∞ : WithTop ℕ∞) d)
    (hp : ContDiff ℝ (∞ : WithTop ℕ∞) p) (hr : ContDiff ℝ (∞ : WithTop ℕ∞) r)
    (hdne : ∀ x, d x ≠ 0) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (fun x => solveScale (d x) (p x) (r x)) := by
  have hratio := hr.div hd hdne
  exact hratio.mul ((inverseSlope_contDiff.of_le (by simp)).comp (hp.mul hratio))

/-- The globally regular formula for the manuscript's scaled variance. -/
def tiltVariance (d p μ : ℝ) : ℝ := d ^ 2 * μ ^ 2 * quadraticFactor (μ * p)

theorem scaledRoot_sq (d p μ : ℝ) : scaledRoot d p μ ^ 2 = tiltVariance d p μ := by
  unfold scaledRoot tiltVariance
  rw [mul_pow, mul_pow, Real.sq_sqrt (quadraticFactor_pos _).le]

theorem tiltVariance_formula (d p μ : ℝ) (hp : p ≠ 0) :
    tiltVariance d p μ = (d / p) ^ 2 * baseVariance (μ * p) := by
  rw [quadraticFactor_identity]
  unfold tiltVariance
  field_simp

theorem tiltVariance_zero_parameter (d μ : ℝ) : tiltVariance d 0 μ = d ^ 2 * μ ^ 2 / 2 := by
  simp only [tiltVariance, mul_zero, quadraticFactor_zero]
  ring

theorem tiltVariance_zero_amplitude (d p : ℝ) : tiltVariance d p 0 = 0 := by
  simp [tiltVariance]

theorem solveScale_variance (d p r : ℝ) (hd : d ≠ 0) :
    tiltVariance d p (solveScale d p r) = r ^ 2 := by
  rw [← scaledRoot_sq, solveScale_spec d p r hd]

theorem exists_unique_nonneg_variance_parameter (d p V : ℝ) (hd : 0 < d) (hV : 0 ≤ V) :
    ∃! μ : ℝ, 0 ≤ μ ∧ tiltVariance d p μ = V := by
  refine ⟨solveScale d p (Real.sqrt V),
    ⟨solveScale_nonneg d p _ hd (Real.sqrt_nonneg V), ?_⟩, ?_⟩
  · rw [solveScale_variance d p _ (ne_of_gt hd), Real.sq_sqrt hV]
  · intro μ hμ
    apply solveScale_unique d p (Real.sqrt V) μ hd
    have hnonneg : 0 ≤ scaledRoot d p μ := by
      exact mul_nonneg (mul_nonneg hd.le hμ.1) (Real.sqrt_nonneg _)
    have hsquare : scaledRoot d p μ ^ 2 = V := by rw [scaledRoot_sq, hμ.2]
    nlinarith [Real.sq_sqrt hV, Real.sqrt_nonneg V]

theorem tiltVariance_strictMonoOn (d p : ℝ) (hd : 0 < d) :
    StrictMonoOn (tiltVariance d p) (Ici 0) := by
  intro μ hμ ν hν hlt
  have hm := (scaledRoot_strictMono d p hd) hlt
  have hnonneg : 0 ≤ scaledRoot d p μ := by
    rw [← scaledRoot_zero d p]
    exact (scaledRoot_strictMono d p hd).monotone hμ
  rw [← scaledRoot_sq, ← scaledRoot_sq]
  nlinarith

theorem tiltVariance_tendsto_atTop (d p : ℝ) (hd : 0 < d) :
    Filter.Tendsto (tiltVariance d p) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro B
  obtain ⟨μ, hμ, _⟩ := exists_unique_nonneg_variance_parameter d p (max 0 B) hd (le_max_left _ _)
  refine ⟨μ, fun ν hν => (le_max_right 0 B).trans ?_⟩
  rw [← hμ.2]
  exact (tiltVariance_strictMonoOn d p hd).monotoneOn hμ.1 (le_trans hμ.1 hν) hν

theorem tiltVariance_eq_extended_integral (m d p μ : ℝ) :
    tiltVariance d p μ = angularMean (fun θ => (extendedExpTilt m d μ p θ - m) ^ 2) := by
  by_cases hp : p = 0
  · subst p
    rw [tiltVariance_zero_parameter, extendedExpTilt_variance_zero]
  · simp only [extendedExpTilt, ite_eq_right hp]
    rw [expTilt_variance, tiltVariance_formula d p μ hp]
    rfl

theorem dslope_zero_analyticAt (f : ℝ → ℝ) (hf : ∀ s, AnalyticAt ℝ f s) (s : ℝ) :
    AnalyticAt ℝ (dslope f 0) s := by
  by_cases hs : s = 0
  · subst s
    obtain ⟨p, hp⟩ := hf 0
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  · have hq : AnalyticAt ℝ (fun t => (f t - f 0) / t) s :=
      ((hf s).sub analyticAt_const).div analyticAt_id hs
    apply hq.congr
    filter_upwards [eventually_ne_nhds hs] with t ht
    rw [dslope_of_ne f ht, slope_def_field, sub_zero]

/-- Exp divided, given by `dslope Real.exp 0`. -/
def expDivided : ℝ → ℝ := dslope Real.exp 0

/-- Normalizer divided, given by `dslope expNormalizer 0`. -/
def normalizerDivided : ℝ → ℝ := dslope expNormalizer 0

theorem expDivided_contDiff : ContDiff ℝ ω expDivided :=
  contDiff_iff_contDiffAt.mpr (fun s =>
    (dslope_zero_analyticAt Real.exp (fun _ => analyticAt_rexp) s).contDiffAt)

theorem normalizerDivided_contDiff : ContDiff ℝ ω normalizerDivided :=
  contDiff_iff_contDiffAt.mpr (fun s =>
    (dslope_zero_analyticAt expNormalizer normalizer_analyticAt s).contDiffAt)

theorem expDivided_zero : expDivided 0 = 1 := by
  rw [expDivided, dslope_same, Real.deriv_exp, Real.exp_zero]

theorem normalizerDivided_zero : normalizerDivided 0 = 0 := by
  rw [normalizerDivided, dslope_same, (normalizer_hasDerivAt 0).deriv, moment_one_at_zero]

/-- Regularized density slope, given by `(Real.cos θ * expDivided (s * Real.cos θ) -
normalizerDivided s) / expNormalizer s`. -/
def regularizedDensitySlope (s θ : ℝ) : ℝ :=
  (Real.cos θ * expDivided (s * Real.cos θ) - normalizerDivided s) / expNormalizer s

theorem regularizedDensitySlope_zero (θ : ℝ) : regularizedDensitySlope 0 θ = Real.cos θ := by
  simp only [regularizedDensitySlope, zero_mul, expDivided_zero, normalizerDivided_zero,
    expNormalizer_zero, mul_one, sub_zero, div_one]

theorem regularizedDensitySlope_identity (s θ : ℝ) :
    s * regularizedDensitySlope s θ = normalizedExp s θ - 1 := by
  have h₁ := sub_smul_dslope Real.exp (0 : ℝ) (s * Real.cos θ)
  have h₂ := sub_smul_dslope expNormalizer (0 : ℝ) s
  simp only [sub_zero, smul_eq_mul, Real.exp_zero, expNormalizer_zero] at h₁ h₂
  unfold regularizedDensitySlope normalizedExp
  have hnz := ne_of_gt (expNormalizer_pos s)
  field_simp
  dsimp [expDivided, normalizerDivided]
  nlinarith

theorem regularizedDensitySlope_joint_contDiff :
    ContDiff ℝ ω (fun x : ℝ × ℝ => regularizedDensitySlope x.1 x.2) := by
  have hc : ContDiff ℝ ω (fun x : ℝ × ℝ => Real.cos x.2) := Real.contDiff_cos.comp contDiff_snd
  have hn : ContDiff ℝ ω expNormalizer :=
    contDiff_iff_contDiffAt.mpr (fun s => (normalizer_analyticAt s).contDiffAt)
  exact ((hc.mul (expDivided_contDiff.comp (contDiff_fst.mul hc))).sub
    (normalizerDivided_contDiff.comp contDiff_fst)).div (hn.comp contDiff_fst)
      (fun x => ne_of_gt (expNormalizer_pos x.1))

/-- A formula with no transverse-stress denominator, equal to the
manuscript's extended family for all parameters. -/
def regularizedTilt (m d μ p θ : ℝ) : ℝ :=
  m + d * μ * regularizedDensitySlope (μ * p) θ

theorem regularizedTilt_eq_extended (m d μ p θ : ℝ) :
    regularizedTilt m d μ p θ = extendedExpTilt m d μ p θ := by
  by_cases hp : p = 0
  · subst p
    simp [extendedExpTilt, regularizedTilt, regularizedDensitySlope_zero, cosineTilt]
  · simp only [extendedExpTilt, ite_eq_right hp, regularizedTilt, expTilt]
    rw [← regularizedDensitySlope_identity (μ * p) θ]
    field_simp

theorem extendedExpTilt_smooth_family {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m d μ p θ : E → ℝ)
    (hm : ContDiff ℝ (∞ : WithTop ℕ∞) m) (hd : ContDiff ℝ (∞ : WithTop ℕ∞) d)
    (hμ : ContDiff ℝ (∞ : WithTop ℕ∞) μ) (hp : ContDiff ℝ (∞ : WithTop ℕ∞) p)
    (hθ : ContDiff ℝ (∞ : WithTop ℕ∞) θ) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (fun x => extendedExpTilt (m x) (d x) (μ x) (p x) (θ x)) := by
  have heq : (fun x => extendedExpTilt (m x) (d x) (μ x) (p x) (θ x)) =
      (fun x => regularizedTilt (m x) (d x) (μ x) (p x) (θ x)) := by
    funext x
    exact (regularizedTilt_eq_extended _ _ _ _ _).symm
  rw [heq]
  have hreg : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun x : ℝ × ℝ => regularizedDensitySlope x.1 x.2) :=
    regularizedDensitySlope_joint_contDiff.of_le (by simp)
  have hargs : ContDiff ℝ (∞ : WithTop ℕ∞) (fun x => (μ x * p x, θ x)) :=
    (hμ.mul hp).prodMk hθ
  have hcomp := hreg.comp hargs
  exact hm.add ((hd.mul hμ).mul hcomp)

/-- Solved tilt, given by `extendedExpTilt m d (solveScale d p r) p θ`. -/
def solvedTilt (m d p r θ : ℝ) : ℝ := extendedExpTilt m d (solveScale d p r) p θ

theorem solvedTilt_periodic (m d p r : ℝ) : Function.Periodic (solvedTilt m d p r) (2 * Real.pi) :=
  extendedExpTilt_periodic m d (solveScale d p r) p

theorem solvedTilt_mean (m d p r : ℝ) : angularMean (solvedTilt m d p r) = m :=
  extendedExpTilt_mean m d (solveScale d p r) p

theorem solvedTilt_variance (m d p r : ℝ) (hd : d ≠ 0) :
    angularMean (fun θ => (solvedTilt m d p r θ - m) ^ 2) = r ^ 2 := by
  unfold solvedTilt
  rw [← tiltVariance_eq_extended_integral m d p (solveScale d p r)]
  exact solveScale_variance d p r hd

theorem solvedTilt_projection (p₁ m d p r : ℝ) (hd : 0 < d)
    (hmargin : 2 ≤ p₁ + p * m - d) :
    ∀ θ, 2 < p₁ + p * solvedTilt m d p r θ :=
  extendedExpTilt_projection_positive p₁ p m d (solveScale d p r) hd hmargin

/-- The solved exponential tilt is jointly C∞ in smooth mean/stress data,
angle, and prescribed signed square root of variance. This includes both
the `p=0` and `r=0` loci. -/
theorem solvedTilt_smooth_family {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m d p r θ : E → ℝ)
    (hm : ContDiff ℝ (∞ : WithTop ℕ∞) m) (hd : ContDiff ℝ (∞ : WithTop ℕ∞) d)
    (hp : ContDiff ℝ (∞ : WithTop ℕ∞) p) (hr : ContDiff ℝ (∞ : WithTop ℕ∞) r)
    (hθ : ContDiff ℝ (∞ : WithTop ℕ∞) θ) (hdne : ∀ x, d x ≠ 0) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (fun x => solvedTilt (m x) (d x) (p x) (r x) (θ x)) := by
  exact extendedExpTilt_smooth_family m d (fun x => solveScale (d x) (p x) (r x)) p θ
    hm hd (solveScale_smooth_family d p r hd hp hr hdne) hp hθ

theorem solvedTilt_contDiff (m d p r : ℝ) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (solvedTilt m d p r) :=
  extendedExpTilt_contDiff m d (solveScale d p r) p

theorem solvedTilt_zero_target (m d p θ : ℝ) : solvedTilt m d p 0 θ = m := by
  by_cases hp : p = 0 <;>
    simp [solvedTilt, solveScale, extendedExpTilt, hp, cosineTilt, expTilt,
      normalizedExp, expNormalizer_zero]

/-- The actual periodic analogue of `LoopMoments.exists_projected_twoPoint`:
all prescribed nonnegative variances are realized, with no cosine-amplitude
restriction. -/
theorem exists_smooth_projected_tilt (p₁ p₂ m V : ℝ)
    (hP : 2 < p₁ + p₂ * m) (hV : 0 ≤ V) :
    ∃ t : ℝ → ℝ, ContDiff ℝ (∞ : WithTop ℕ∞) t ∧
      Function.Periodic t (2 * Real.pi) ∧ angularMean t = m ∧
      angularMean (fun θ => (t θ - m) ^ 2) = V ∧
      ∀ θ, 2 < p₁ + p₂ * t θ := by
  let d := (p₁ + p₂ * m - 2) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hm : 2 ≤ p₁ + p₂ * m - d := by dsimp [d]; linarith
  refine ⟨solvedTilt m d p₂ (Real.sqrt V), solvedTilt_contDiff _ _ _ _,
    solvedTilt_periodic _ _ _ _, solvedTilt_mean _ _ _ _, ?_,
    solvedTilt_projection p₁ m d p₂ _ hd hm⟩
  rw [solvedTilt_variance _ _ _ _ (ne_of_gt hd), Real.sq_sqrt hV]

/-- Compact transverse-stress data have one amplitude that exceeds a
prescribed variance target everywhere, as required before choosing the
uniform cone margin in the manuscript. -/
theorem uniform_variance_amplitude {K : Set ℝ} (hK : IsCompact K)
    (d V : ℝ) (hd : 0 < d) (hV : 0 ≤ V) :
    ∃ M : ℝ, 0 < M ∧ ∀ p ∈ K, V < tiltVariance d p M := by
  let f : ℝ → ℝ := fun p => solveScale d p (Real.sqrt V)
  have hf : Continuous f := (solveScale_joint_contDiff d).continuous.comp
    (continuous_id.prodMk continuous_const)
  obtain ⟨B, hB⟩ := (hK.image hf).bddAbove
  let M := max B 0 + 1
  have hM : 0 < M := by dsimp [M]; linarith [le_max_right B (0 : ℝ)]
  refine ⟨M, hM, fun p hp => ?_⟩
  have hfp : 0 ≤ f p := solveScale_nonneg d p _ hd (Real.sqrt_nonneg _)
  have hfpB : f p ≤ B := hB (mem_image_of_mem f hp)
  have hfpM : f p < M := by dsimp [M]; linarith [le_max_left B (0 : ℝ)]
  have hvfp : tiltVariance d p (f p) = V := by
    rw [solveScale_variance d p _ (ne_of_gt hd), Real.sq_sqrt hV]
  rw [← hvfp]
  exact tiltVariance_strictMonoOn d p hd hfp hM.le hfpM

end

end NavierStokes.LoopVariance

end

end

@[expose] public section

namespace NavierStokes.TrueConeLoop

noncomputable section

open Set Filter MeasureTheory
open SmoothLoop LoopMoments LoopVariance ConeAlgebra
open scoped ContDiff Topology Interval

/-- Low speed, given by `2 + δ / 8`. -/
def lowSpeed (δ : ℝ) : ℝ := 2 + δ / 8
/-- High speed, given by `2 + δ / 4`. -/
def highSpeed (δ : ℝ) : ℝ := 2 + δ / 4
/-- Target speed, given by `2 + δ / 2`. -/
def targetSpeed (δ : ℝ) : ℝ := 2 + δ / 2

/-- Speed cutoff, given by `1 - Real.smoothTransition ((v - lowSpeed δ) / (δ / 8))`. -/
def speedCutoff (δ v : ℝ) : ℝ :=
  1 - Real.smoothTransition ((v - lowSpeed δ) / (δ / 8))

theorem speedCutoff_contDiff (δ : ℝ) : ContDiff ℝ ∞ (speedCutoff δ) := by
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const (δ / 8)))

theorem speedCutoff_mem_Icc (δ v : ℝ) : speedCutoff δ v ∈ Icc (0 : ℝ) 1 := by
  have hlo := Real.smoothTransition.nonneg ((v - lowSpeed δ) / (δ / 8))
  have hhi := Real.smoothTransition.le_one ((v - lowSpeed δ) / (δ / 8))
  unfold speedCutoff
  constructor <;> linarith

theorem speedCutoff_one (δ v : ℝ) (hδ : 0 < δ) (hv : v ≤ lowSpeed δ) : speedCutoff δ v = 1 := by
  have harg : (v - lowSpeed δ) / (δ / 8) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv) (by positivity)
  simp only [speedCutoff, Real.smoothTransition.zero_of_nonpos harg, sub_zero]

theorem speedCutoff_zero (δ v : ℝ) (hδ : 0 < δ) (hv : highSpeed δ ≤ v) : speedCutoff δ v = 0 := by
  have harg : 1 ≤ (v - lowSpeed δ) / (δ / 8) := by
    apply (le_div_iff₀ (by positivity : 0 < δ / 8)).mpr
    dsimp [lowSpeed, highSpeed] at *
    linarith
  simp only [speedCutoff, Real.smoothTransition.one_of_one_le harg, sub_self]

/-- Correction root, given by `speedCutoff δ v * Real.sqrt (targetSpeed δ - v)`. -/
def correctionRoot (δ v : ℝ) : ℝ := speedCutoff δ v * Real.sqrt (targetSpeed δ - v)
/-- Correction, given by `correctionRoot δ v ^ 2`. -/
def correction (δ v : ℝ) : ℝ := correctionRoot δ v ^ 2
/-- Corrected speed, given by `v + correction δ v`. -/
def correctedSpeed (δ v : ℝ) : ℝ := v + correction δ v

theorem correctionRoot_zero (δ v : ℝ) (hδ : 0 < δ) (hv : highSpeed δ ≤ v) :
    correctionRoot δ v = 0 := by
  simp only [correctionRoot, speedCutoff_zero δ v hδ hv, zero_mul]

theorem correctionRoot_contDiff (δ : ℝ) (hδ : 0 < δ) : ContDiff ℝ ∞ (correctionRoot δ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro v
  by_cases hv : v < targetSpeed δ
  · exact (speedCutoff_contDiff δ).contDiffAt.mul
      ((contDiffAt_const.sub contDiffAt_id).sqrt (ne_of_gt (sub_pos.mpr hv)))
  · have hhigh : highSpeed δ < v := by
      dsimp [highSpeed, targetSpeed] at *
      linarith
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) v).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hhigh] with w hw
    exact correctionRoot_zero δ w hδ hw.le

theorem correctionRoot_nonneg (δ v : ℝ) : 0 ≤ correctionRoot δ v :=
  mul_nonneg (speedCutoff_mem_Icc δ v).1 (Real.sqrt_nonneg _)

theorem correction_nonneg (δ v : ℝ) : 0 ≤ correction δ v := sq_nonneg _

theorem correction_formula (δ v : ℝ) (hδ : 0 < δ) :
    correction δ v = speedCutoff δ v ^ 2 * (targetSpeed δ - v) := by
  by_cases hv : highSpeed δ ≤ v
  · simp only [correction, correctionRoot_zero δ v hδ hv, speedCutoff_zero δ v hδ hv,
      zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul]
  · have hgap : 0 ≤ targetSpeed δ - v := by
      dsimp [targetSpeed, highSpeed] at *
      linarith
    simp only [correction, correctionRoot, mul_pow, Real.sq_sqrt hgap]

theorem correction_zero (δ v : ℝ) (hδ : 0 < δ) (hv : highSpeed δ ≤ v) : correction δ v = 0 := by
  simp only [correction, correctionRoot_zero δ v hδ hv, zero_pow (by decide : (2 : ℕ) ≠ 0)]

theorem correction_le_gap (δ v : ℝ) (hδ : 0 < δ) (hv : v ≤ highSpeed δ) :
    correction δ v ≤ targetSpeed δ - v := by
  have hz := speedCutoff_mem_Icc δ v
  have hzs : speedCutoff δ v ^ 2 ≤ 1 := by nlinarith [hz.1, hz.2]
  have hgap : 0 ≤ targetSpeed δ - v := by
    dsimp [highSpeed, targetSpeed] at *
    linarith
  rw [correction_formula δ v hδ]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hzs hgap

theorem correction_lt_three (δ v : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hv : 0 < v) :
    correction δ v < 3 := by
  by_cases hh : highSpeed δ ≤ v
  · rw [correction_zero δ v hδ hh]
    norm_num
  · have h := correction_le_gap δ v hδ (le_of_not_ge hh)
    dsimp [targetSpeed] at h
    linarith

theorem correctedSpeed_gt_two (δ v : ℝ) (hδ : 0 < δ) : 2 < correctedSpeed δ v := by
  by_cases hv : v ≤ lowSpeed δ
  · rw [correctedSpeed, correction_formula δ v hδ, speedCutoff_one δ v hδ hv]
    dsimp [targetSpeed]
    linarith
  · have hn := correction_nonneg δ v
    dsimp [correctedSpeed, lowSpeed] at *
    linarith

theorem correctedSpeed_le_target_of_active (δ v : ℝ) (hδ : 0 < δ)
    (hactive : speedCutoff δ v ≠ 0) : correctedSpeed δ v ≤ targetSpeed δ := by
  have hv : v ≤ highSpeed δ := by
    by_contra h
    exact hactive (speedCutoff_zero δ v hδ (le_of_lt (lt_of_not_ge h)))
  have h := correction_le_gap δ v hδ hv
  dsimp [correctedSpeed]
  linarith

/-- Variance root, given by `correctionRoot δ v / Real.sqrt a`. -/
def varianceRoot (a δ v : ℝ) : ℝ := correctionRoot δ v / Real.sqrt a

theorem varianceRoot_nonneg (a δ v : ℝ) : 0 ≤ varianceRoot a δ v :=
  div_nonneg (correctionRoot_nonneg δ v) (Real.sqrt_nonneg a)

theorem varianceRoot_sq (a δ v : ℝ) (ha : 0 < a) :
    varianceRoot a δ v ^ 2 = correction δ v / a := by
  simp only [varianceRoot, div_pow, Real.sq_sqrt ha.le, correction]

theorem varianceRoot_zero (a δ v : ℝ) (hδ : 0 < δ) (hv : highSpeed δ ≤ v) :
    varianceRoot a δ v = 0 := by
  simp only [varianceRoot, correctionRoot_zero δ v hδ hv, zero_div]

theorem varianceRoot_bound (amin a δ v : ℝ) (hmin : 0 < amin) (ha : amin ≤ a)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hv : 0 < v) :
    varianceRoot a δ v ≤ Real.sqrt (3 / amin) := by
  have hap : 0 < a := lt_of_lt_of_le hmin ha
  have hρ := (correction_lt_three δ v hδ hδ₁ hv).le
  have hsq : varianceRoot a δ v ^ 2 ≤ 3 / amin := by
    rw [varianceRoot_sq a δ v hap]
    exact (div_le_div_of_nonneg_right hρ hap.le).trans
      (div_le_div_of_nonneg_left (by norm_num) hmin ha)
  have hR := Real.sq_sqrt (show 0 ≤ 3 / amin by positivity)
  have hp := Real.sqrt_nonneg (3 / amin)
  nlinarith [varianceRoot_nonneg a δ v]

theorem solvedTilt_fixed_joint_contDiff (d : ℝ) (hd : d ≠ 0) :
    ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × (ℝ × ℝ) => solvedTilt z.1.1 d z.1.2 z.2.1 z.2.2) := by
  exact solvedTilt_smooth_family _ _ _ _ _ contDiff_fst.fst contDiff_const
    contDiff_fst.snd contDiff_snd.fst contDiff_snd.snd (fun _ => hd)

theorem solvedTilt_continuous_family {X : Type*} [TopologicalSpace X]
    (m p r θ : X → ℝ) (d : ℝ) (hd : d ≠ 0)
    (hm : Continuous m) (hp : Continuous p) (hr : Continuous r) (hθ : Continuous θ) :
    Continuous (fun x => solvedTilt (m x) d (p x) (r x) (θ x)) :=
  (solvedTilt_fixed_joint_contDiff d hd).continuous.comp ((hm.prodMk hp).prodMk (hr.prodMk hθ))

theorem uniform_tilt_cone_margin {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (m p₁ p₂ : X → ℝ)
    (hm : Continuous m) (hp₁ : Continuous p₁) (hp₂ : Continuous p₂)
    (d R : ℝ) (hd : 0 < d)
    (hmargin : ∀ x ∈ K, 2 ≤ p₁ x + p₂ x * m x - d) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ∀ r ∈ Icc (0 : ℝ) R, ∀ θ : ℝ,
      2 + ε ≤ coneBound (p₁ x + p₂ x * solvedTilt (m x) d (p₂ x) r θ)
        (p₂ x - p₁ x * solvedTilt (m x) d (p₂ x) r θ) := by
  let Q : Set (X × (ℝ × ℝ)) := K ×ˢ (Icc 0 R ×ˢ Icc 0 (2 * Real.pi))
  have hQ : IsCompact Q := hK.prod (isCompact_Icc.prod isCompact_Icc)
  let t : X × (ℝ × ℝ) → ℝ := fun z => solvedTilt (m z.1) d (p₂ z.1) z.2.1 z.2.2
  have ht : Continuous t := solvedTilt_continuous_family _ _ _ _ d (ne_of_gt hd)
    (hm.comp continuous_fst) (hp₂.comp continuous_fst) continuous_snd.fst continuous_snd.snd
  let P : X × (ℝ × ℝ) → ℝ := fun z => p₁ z.1 + p₂ z.1 * t z
  let J : X × (ℝ × ℝ) → ℝ := fun z => p₂ z.1 - p₁ z.1 * t z
  have hP : Continuous P := (hp₁.comp continuous_fst).add ((hp₂.comp continuous_fst).mul ht)
  have hJ : Continuous J := (hp₂.comp continuous_fst).sub ((hp₁.comp continuous_fst).mul ht)
  have hU : Continuous (fun z => coneBound (P z) (J z)) :=
    UniformCone.continuous_coneBound.comp (hP.prodMk
      (hJ.prodMk (continuous_const : Continuous (fun _ : X × (ℝ × ℝ) => (0 : ℝ)))))
  obtain ⟨ε, hε, hb⟩ := UniformCone.positive_uniform_margin hQ
    (hU.sub continuous_const).continuousOn (fun z hz => by
      apply sub_pos.mpr
      apply coneBound_gt_two
      exact solvedTilt_projection (p₁ z.1) (m z.1) d (p₂ z.1) z.2.1 hd (hmargin z.1 hz.1) z.2.2)
  refine ⟨ε, hε, fun x hx r hr θ => ?_⟩
  obtain ⟨θ₀, hθ₀, heq⟩ := (solvedTilt_periodic (m x) d (p₂ x) r).exists_mem_Ico₀ period_pos θ
  have hbound := hb (x, r, θ₀) ⟨hx, hr, ⟨hθ₀.1, hθ₀.2.le⟩⟩
  dsimp [P, J, t] at hbound
  rw [heq]
  linarith

/-- Nominal speed, given by `a * (1 + m ^ 2)`. -/
def nominalSpeed (a m : ℝ) : ℝ := a * (1 + m ^ 2)
/-- Seed rho, given by `correction δ (nominalSpeed a m)`. -/
def seedRho (a m δ : ℝ) : ℝ := correction δ (nominalSpeed a m)
/-- Seed speed, given by `correctedSpeed δ (nominalSpeed a m)`. -/
def seedSpeed (a m δ : ℝ) : ℝ := correctedSpeed δ (nominalSpeed a m)
/-- Seed tilt, given by `solvedTilt m d p (varianceRoot a δ (nominalSpeed a m)) θ`. -/
def seedTilt (a m d p δ θ : ℝ) : ℝ :=
  solvedTilt m d p (varianceRoot a δ (nominalSpeed a m)) θ

theorem seedSpeed_gt_two (a m δ : ℝ) (hδ : 0 < δ) : 2 < seedSpeed a m δ :=
  correctedSpeed_gt_two δ (nominalSpeed a m) hδ

theorem seedTilt_contDiff (a m d p δ : ℝ) : ContDiff ℝ ∞ (seedTilt a m d p δ) :=
  solvedTilt_contDiff _ _ _ _

theorem seedTilt_periodic (a m d p δ : ℝ) : Function.Periodic (seedTilt a m d p δ) (2 * Real.pi) :=
  solvedTilt_periodic _ _ _ _

theorem seedTilt_mean (a m d p δ : ℝ) : angularMean (seedTilt a m d p δ) = m :=
  solvedTilt_mean _ _ _ _

theorem seedTilt_variance (a m d p δ : ℝ) (ha : 0 < a) (hd : d ≠ 0) :
    angularMean (fun θ => (seedTilt a m d p δ θ - m) ^ 2) = seedRho a m δ / a := by
  unfold seedTilt
  rw [solvedTilt_variance _ _ _ _ hd, varianceRoot_sq a δ _ ha]
  rfl

theorem seedTilt_nominal_of_inactive (a m d p δ : ℝ)
    (hzero : speedCutoff δ (nominalSpeed a m) = 0) : seedTilt a m d p δ = (fun _ => m) := by
  funext θ
  unfold seedTilt varianceRoot correctionRoot
  rw [hzero, zero_mul, zero_div]
  exact solvedTilt_zero_target m d p θ

theorem seedSpeed_nominal_of_inactive (a m δ : ℝ)
    (hzero : speedCutoff δ (nominalSpeed a m) = 0) : seedSpeed a m δ = nominalSpeed a m := by
  simp only [seedSpeed, correctedSpeed, correction, correctionRoot, hzero,
    zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]

theorem seedTilt_nominal (a m d p δ : ℝ) (hδ : 0 < δ)
    (hh : highSpeed δ ≤ nominalSpeed a m) : seedTilt a m d p δ = (fun _ => m) :=
  seedTilt_nominal_of_inactive a m d p δ (speedCutoff_zero δ _ hδ hh)

theorem seed_cone (a m p₁ p₂ d δ R : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hR : Real.sqrt (3 / a) ≤ R)
    (hmargin : 2 ≤ p₁ + p₂ * m - d)
    (hrelaxed : nominalSpeed a m < coneBound (p₁ + p₂ * m) (p₂ - p₁ * m))
    (hU : ∀ r ∈ Icc (0 : ℝ) R, ∀ θ,
      2 + δ ≤ coneBound (p₁ + p₂ * solvedTilt m d p₂ r θ)
        (p₂ - p₁ * solvedTilt m d p₂ r θ)) :
    ∀ θ, 2 < p₁ + p₂ * seedTilt a m d p₂ δ θ ∧
      seedSpeed a m δ < coneBound (p₁ + p₂ * seedTilt a m d p₂ δ θ)
        (p₂ - p₁ * seedTilt a m d p₂ δ θ) := by
  intro θ
  constructor
  · exact solvedTilt_projection p₁ m d p₂ _ hd hmargin θ
  · by_cases hzero : speedCutoff δ (nominalSpeed a m) = 0
    · rw [seedTilt_nominal_of_inactive a m d p₂ δ hzero,
        seedSpeed_nominal_of_inactive a m δ hzero]
      exact hrelaxed
    · have hv0 : 0 < nominalSpeed a m := mul_pos ha (one_add_sq_pos m)
      have hr : varianceRoot a δ (nominalSpeed a m) ∈ Icc (0 : ℝ) R :=
        ⟨varianceRoot_nonneg _ _ _,
          (varianceRoot_bound a a δ _ ha le_rfl hδ hδ₁ hv0).trans hR⟩
      have hu := hU _ hr θ
      have hv := correctedSpeed_le_target_of_active δ (nominalSpeed a m) hδ hzero
      dsimp [targetSpeed] at hv
      change seedSpeed a m δ ≤ 2 + δ / 2 at hv
      change 2 + δ ≤ coneBound (p₁ + p₂ * seedTilt a m d p₂ δ θ)
        (p₂ - p₁ * seedTilt a m d p₂ δ θ) at hu
      linarith

/-- Seed density, constructed using `densityOfTilt`. -/
def seedDensity (a m d p δ : ℝ) (ha : 0 < a) (hd : d ≠ 0) (hδ : 0 < δ) : CircleDensity :=
  densityOfTilt (seedTilt a m d p δ) a m (seedRho a m δ) (seedSpeed a m δ) ha
    (lt_trans (by norm_num) (seedSpeed_gt_two a m δ hδ))
    (seedTilt_contDiff a m d p δ) (seedTilt_periodic a m d p δ)
    (seedTilt_mean a m d p δ) (seedTilt_variance a m d p δ ha hd) rfl

/-- Constructed A, given by `rephase (seedDensity a m d p δ ha hd hδ) (fun θ => loopA (seedSpeed
a m δ) (seedTilt a m d p δ θ))`. -/
def constructedA (a m d p δ : ℝ) (ha : 0 < a) (hd : d ≠ 0) (hδ : 0 < δ) : ℝ → ℝ :=
  rephase (seedDensity a m d p δ ha hd hδ) (fun θ => loopA (seedSpeed a m δ) (seedTilt a m d p δ θ))

/-- Constructed C, given by `rephase (seedDensity a m d p δ ha hd hδ) (fun θ => loopC (seedSpeed
a m δ) (seedTilt a m d p δ θ))`. -/
def constructedC (a m d p δ : ℝ) (ha : 0 < a) (hd : d ≠ 0) (hδ : 0 < δ) : ℝ → ℝ :=
  rephase (seedDensity a m d p δ ha hd hδ) (fun θ => loopC (seedSpeed a m δ) (seedTilt a m d p δ θ))

/-- In true cone, constructed using `0`. -/
def InTrueCone (p₁ p₂ A C : ℝ) : Prop :=
  0 < A ∧ 2 < A * (1 + (C / A) ^ 2) ∧ 2 < p₁ + p₂ * (C / A) ∧
    A * (1 + (C / A) ^ 2) < coneBound (p₁ + p₂ * (C / A)) (p₂ - p₁ * (C / A))

/-- Positive additive margins for all four scalar inequalities, including
the positive first shear component. -/
def HasConeMargin (ε p₁ p₂ A C : ℝ) : Prop :=
  ε ≤ A ∧ ε ≤ A * (1 + (C / A) ^ 2) - 2 ∧ ε ≤ p₁ + p₂ * (C / A) - 2 ∧
    ε ≤ coneBound (p₁ + p₂ * (C / A)) (p₂ - p₁ * (C / A)) - A * (1 + (C / A) ^ 2)

/-- Compact slow parameters and a periodic fast parameter turn strict
pointwise cone inequalities into one positive margin at every fast angle. -/
theorem compact_periodic_trueCone_margins {X : Type*} [TopologicalSpace X]
    (p₁ p₂ : X → ℝ) (A C : X × ℝ → ℝ) {K : Set X} (hK : IsCompact K)
    (hp₁ : ContinuousOn p₁ K) (hp₂ : ContinuousOn p₂ K)
    (hA : ContinuousOn A (K ×ˢ (univ : Set ℝ)))
    (hC : ContinuousOn C (K ×ˢ (univ : Set ℝ)))
    (hAp : ∀ x ∈ K, Function.Periodic (fun φ => A (x, φ)) 1)
    (hCp : ∀ x ∈ K, Function.Periodic (fun φ => C (x, φ)) 1)
    (hcone : ∀ x ∈ K, ∀ φ, InTrueCone (p₁ x) (p₂ x) (A (x, φ)) (C (x, φ))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ∀ φ,
      HasConeMargin ε (p₁ x) (p₂ x) (A (x, φ)) (C (x, φ)) := by
  let Q : Set (X × ℝ) := K ×ˢ Icc 0 1
  have hQ : IsCompact Q := hK.prod isCompact_Icc
  have hAQ : ContinuousOn A Q := hA.mono (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hCQ : ContinuousOn C Q := hC.mono (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hp₁Q : ContinuousOn (fun z : X × ℝ => p₁ z.1) Q :=
    hp₁.comp continuousOn_fst (fun _ hz => hz.1)
  have hp₂Q : ContinuousOn (fun z : X × ℝ => p₂ z.1) Q :=
    hp₂.comp continuousOn_fst (fun _ hz => hz.1)
  let t : X × ℝ → ℝ := fun z => C z / A z
  let P : X × ℝ → ℝ := fun z => p₁ z.1 + p₂ z.1 * t z
  let J : X × ℝ → ℝ := fun z => p₂ z.1 - p₁ z.1 * t z
  let v : X × ℝ → ℝ := fun z => A z * (1 + t z ^ 2)
  have ht : ContinuousOn t Q := hCQ.div hAQ
    (fun z hz => ne_of_gt (hcone z.1 hz.1 z.2).1)
  have hP : ContinuousOn P Q := hp₁Q.add (hp₂Q.mul ht)
  have hJ : ContinuousOn J Q := hp₂Q.sub (hp₁Q.mul ht)
  have hv : ContinuousOn v Q := hAQ.mul (continuousOn_const.add (ht.pow 2))
  obtain ⟨εa, hεa, hma⟩ := UniformCone.positive_uniform_margin hQ hAQ
    (fun z hz => (hcone z.1 hz.1 z.2).1)
  obtain ⟨εc, hεc, hmc⟩ := UniformCone.compact_trueCone_margins hQ hP hJ hv
    (fun z hz => (hcone z.1 hz.1 z.2).2)
  refine ⟨min εa εc, lt_min hεa hεc, fun x hx φ => ?_⟩
  have hpair : Function.Periodic (fun θ => (A (x, θ), C (x, θ))) 1 := by
    intro θ
    exact Prod.ext (hAp x hx θ) (hCp x hx θ)
  obtain ⟨θ, hθ, heq⟩ := hpair.exists_mem_Ico₀ (by norm_num) φ
  have hAE : A (x, φ) = A (x, θ) := congrArg Prod.fst heq
  have hCE : C (x, φ) = C (x, θ) := congrArg Prod.snd heq
  rw [hAE, hCE]
  have hmem : (x, θ) ∈ Q := ⟨hx, hθ.1, hθ.2.le⟩
  exact ⟨(min_le_left _ _).trans (hma (x, θ) hmem),
    (min_le_right _ _).trans (hmc (x, θ) hmem).1,
    (min_le_right _ _).trans (hmc (x, θ) hmem).2.1,
    (min_le_right _ _).trans (hmc (x, θ) hmem).2.2⟩

theorem constructed_smooth (a m d p δ : ℝ) (ha : 0 < a) (hd : d ≠ 0) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (constructedA a m d p δ ha hd hδ) ∧
      ContDiff ℝ ∞ (constructedC a m d p δ ha hd hδ) := by
  have h := smooth_loop_shears (seedTilt a m d p δ) (seedSpeed a m δ) (seedTilt_contDiff a m d p δ)
  exact ⟨rephase_contDiff _ _ h.1, rephase_contDiff _ _ h.2⟩

theorem constructed_periodic (a m d p δ : ℝ) (ha : 0 < a) (hd : d ≠ 0) (hδ : 0 < δ) :
    Function.Periodic (constructedA a m d p δ ha hd hδ) 1 ∧
      Function.Periodic (constructedC a m d p δ ha hd hδ) 1 := by
  have h := periodic_loop_shears (seedTilt a m d p δ) (seedSpeed a m δ) (seedTilt_periodic a m d p
      δ)
  exact ⟨rephase_periodic _ _ h.1, rephase_periodic _ _ h.2⟩

theorem constructed_means (a m d p δ : ℝ) (ha : 0 < a) (hd : d ≠ 0) (hδ : 0 < δ) :
    (∫ φ in (0 : ℝ)..1, constructedA a m d p δ ha hd hδ φ) = a ∧
      (∫ φ in (0 : ℝ)..1, constructedC a m d p δ ha hd hδ φ) = a * m := by
  have hs := smooth_loop_shears (seedTilt a m d p δ) (seedSpeed a m δ) (seedTilt_contDiff a m d p δ)
  have hv : seedSpeed a m δ ≠ 0 := ne_of_gt (lt_trans (by norm_num) (seedSpeed_gt_two a m δ hδ))
  have hmom := angular_rephasing_moments (seedTilt a m d p δ) a m (seedRho a m δ)
    (seedSpeed a m δ) (ne_of_gt ha) hv (seedTilt_contDiff a m d p δ).continuous
    (seedTilt_mean a m d p δ) (seedTilt_variance a m d p δ ha hd) rfl
  constructor
  · unfold constructedA
    rw [integral_rephase _ _ hs.1.continuous]
    change (∫ θ in (0 : ℝ)..(2 * Real.pi),
      loopA (seedSpeed a m δ) (seedTilt a m d p δ θ) *
      (phaseDensity a (seedSpeed a m δ) (seedTilt a m d p δ θ) / (2 * Real.pi))) = a
    simp_rw [← mul_div_assoc, mul_comm (loopA _ _) (phaseDensity _ _ _)]
    rw [intervalIntegral.integral_div]
    exact hmom.2.1
  · unfold constructedC
    rw [integral_rephase _ _ hs.2.continuous]
    change (∫ θ in (0 : ℝ)..(2 * Real.pi),
      loopC (seedSpeed a m δ) (seedTilt a m d p δ θ) *
      (phaseDensity a (seedSpeed a m δ) (seedTilt a m d p δ θ) / (2 * Real.pi))) = a * m
    simp_rw [← mul_div_assoc, mul_comm (loopC _ _) (phaseDensity _ _ _)]
    rw [intervalIntegral.integral_div]
    exact hmom.2.2

theorem constructed_trueCone (a m p₁ p₂ d δ R : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hR : Real.sqrt (3 / a) ≤ R)
    (hmargin : 2 ≤ p₁ + p₂ * m - d)
    (hrelaxed : nominalSpeed a m < coneBound (p₁ + p₂ * m) (p₂ - p₁ * m))
    (hU : ∀ r ∈ Icc (0 : ℝ) R, ∀ θ,
      2 + δ ≤ coneBound (p₁ + p₂ * solvedTilt m d p₂ r θ)
        (p₂ - p₁ * solvedTilt m d p₂ r θ)) :
    ∀ φ, InTrueCone p₁ p₂ (constructedA a m d p₂ δ ha (ne_of_gt hd) hδ φ)
      (constructedC a m d p₂ δ ha (ne_of_gt hd) hδ φ) := by
  intro φ
  have hv := seedSpeed_gt_two a m δ hδ
  have hvpos : 0 < seedSpeed a m δ := lt_trans (by norm_num) hv
  let θ := (phaseHomeomorph (seedDensity a m d p₂ δ ha (ne_of_gt hd) hδ)).symm φ
  have hc := seed_cone a m p₁ p₂ d δ R ha hd hδ hδ₁ hR hmargin hrelaxed hU θ
  change InTrueCone p₁ p₂ (loopA (seedSpeed a m δ) (seedTilt a m d p₂ δ θ))
    (loopC (seedSpeed a m δ) (seedTilt a m d p₂ δ θ))
  unfold InTrueCone
  rw [loop_slope _ _ (ne_of_gt hvpos), loop_speed]
  exact ⟨loopA_pos _ _ hvpos, hv, hc⟩

theorem constructed_nominal (a m d p δ : ℝ) (ha : 0 < a) (hd : d ≠ 0) (hδ : 0 < δ)
    (hh : highSpeed δ ≤ nominalSpeed a m) :
    constructedA a m d p δ ha hd hδ = (fun _ => a) ∧
      constructedC a m d p δ ha hd hδ = (fun _ => a * m) := by
  have hz := speedCutoff_zero δ (nominalSpeed a m) hδ hh
  have ht := seedTilt_nominal_of_inactive a m d p δ hz
  have hv := seedSpeed_nominal_of_inactive a m δ hz
  constructor <;> funext φ <;> dsimp [constructedA, constructedC, rephase]
  · rw [ht, hv]
    unfold loopA nominalSpeed
    exact mul_div_cancel_right₀ a (ne_of_gt (one_add_sq_pos m))
  · rw [ht, hv]
    unfold loopC nominalSpeed
    have hnz := ne_of_gt (one_add_sq_pos m)
    field_simp

/-- Fixed-parameter true-cone realization, with no assumed loop or margin.
The nominal data need only satisfy the relaxed cone. -/
theorem exists_trueCone_loop (a m p₁ p₂ : ℝ) (ha : 0 < a)
    (hP : 2 < p₁ + p₂ * m)
    (hrelaxed : nominalSpeed a m < coneBound (p₁ + p₂ * m) (p₂ - p₁ * m)) :
    ∃ A C : ℝ → ℝ, ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ C ∧
      Function.Periodic A 1 ∧ Function.Periodic C 1 ∧
      (∫ φ in (0 : ℝ)..1, A φ) = a ∧ (∫ φ in (0 : ℝ)..1, C φ) = a * m ∧
      ∀ φ, InTrueCone p₁ p₂ (A φ) (C φ) := by
  let d := (p₁ + p₂ * m - 2) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hmargin : 2 ≤ p₁ + p₂ * m - d := by dsimp [d]; linarith
  let R := Real.sqrt (3 / a)
  obtain ⟨ε, hε, hU⟩ := uniform_tilt_cone_margin (X := ℝ) (K := {0}) isCompact_singleton
    (fun _ => m) (fun _ => p₁) (fun _ => p₂) continuous_const continuous_const continuous_const
    d R hd (fun _ _ => hmargin)
  let δ := min ε 1
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδ₁ : δ ≤ 1 := min_le_right _ _
  have hUδ : ∀ r ∈ Icc (0 : ℝ) R, ∀ θ,
      2 + δ ≤ coneBound (p₁ + p₂ * solvedTilt m d p₂ r θ) (p₂ - p₁ * solvedTilt m d p₂ r θ) := by
    intro r hr θ
    exact (add_le_add_right (min_le_left ε 1) 2).trans (hU 0 (by simp) r hr θ)
  let A := constructedA a m d p₂ δ ha (ne_of_gt hd) hδ
  let C := constructedC a m d p₂ δ ha (ne_of_gt hd) hδ
  have hs := constructed_smooth a m d p₂ δ ha (ne_of_gt hd) hδ
  have hp := constructed_periodic a m d p₂ δ ha (ne_of_gt hd) hδ
  have hm := constructed_means a m d p₂ δ ha (ne_of_gt hd) hδ
  exact ⟨A, C, hs.1, hs.2, hp.1, hp.2, hm.1, hm.2,
    constructed_trueCone a m p₁ p₂ d δ R ha hd hδ hδ₁ le_rfl hmargin hrelaxed hUδ⟩

/-- Family choices data, collecting `aMin`, `d`, `radius`, `maxAmplitude`, `delta`, `aMin_pos`
and their compatibility conditions. -/
structure FamilyChoices {X : Type*} (a m p₁ p₂ : X → ℝ) (K B : Set X) where
  /-- A min of `FamilyChoices`, of type `ℝ`. -/
  aMin : ℝ
  /-- D of `FamilyChoices`, of type `ℝ`. -/
  d : ℝ
  /-- Radius of `FamilyChoices`, of type `ℝ`. -/
  radius : ℝ
  /-- Max amplitude of `FamilyChoices`, of type `ℝ`. -/
  maxAmplitude : ℝ
  /-- Delta of `FamilyChoices`, of type `ℝ`. -/
  delta : ℝ
  aMin_pos : 0 < aMin
  d_pos : 0 < d
  radius_eq : radius = Real.sqrt (3 / aMin)
  maxAmplitude_pos : 0 < maxAmplitude
  delta_pos : 0 < delta
  delta_le_one : delta ≤ 1
  aMin_le : ∀ x ∈ K, aMin ≤ a x
  projection_margin : ∀ x ∈ K, 2 ≤ p₁ x + p₂ x * m x - d
  amplitude_large : ∀ x ∈ K, 3 / aMin < tiltVariance d (p₂ x) maxAmplitude
  cone_margin : ∀ x ∈ K, ∀ r ∈ Icc (0 : ℝ) radius, ∀ θ,
    2 + delta ≤ coneBound (p₁ x + p₂ x * solvedTilt (m x) d (p₂ x) r θ)
      (p₂ x - p₁ x * solvedTilt (m x) d (p₂ x) r θ)
  boundary_inactive : ∀ x ∈ B, highSpeed delta < nominalSpeed (a x) (m x)

theorem exists_family_choices {X : Type*} [TopologicalSpace X]
    (a m p₁ p₂ : X → ℝ) {K B : Set X} (hK : IsCompact K) (hB : IsCompact B)
    (ha : Continuous a) (hm : Continuous m) (hp₁ : Continuous p₁) (hp₂ : Continuous p₂)
    (haK : ∀ x ∈ K, 0 < a x) (hPK : ∀ x ∈ K, 2 < p₁ x + p₂ x * m x)
    (htrueB : ∀ x ∈ B, 2 < nominalSpeed (a x) (m x)) :
    Nonempty (FamilyChoices a m p₁ p₂ K B) := by
  obtain ⟨amin, hamin, haminle⟩ := UniformCone.positive_uniform_margin hK ha.continuousOn haK
  obtain ⟨ep, hep, heple⟩ := UniformCone.positive_uniform_margin hK
    ((hp₁.fun_add (hp₂.fun_mul hm)).fun_sub continuous_const).continuousOn
    (fun x hx => sub_pos.mpr (hPK x hx))
  let d := ep / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hproj : ∀ x ∈ K, 2 ≤ p₁ x + p₂ x * m x - d := by
    intro x hx
    have h := heple x hx
    dsimp [d]
    linarith
  let R := Real.sqrt (3 / amin)
  obtain ⟨M, hM, hML⟩ := uniform_variance_amplitude (hK.image hp₂) d (3 / amin) hd (by positivity)
  obtain ⟨eu, heu, hmargin⟩ := uniform_tilt_cone_margin hK m p₁ p₂ hm hp₁ hp₂ d R hd hproj
  have hnom : Continuous (fun x => nominalSpeed (a x) (m x)) :=
    ha.mul (continuous_const.add (hm.pow 2))
  obtain ⟨eb, heb, heble⟩ := UniformCone.positive_uniform_margin hB
    (hnom.fun_sub continuous_const).continuousOn (fun x hx => sub_pos.mpr (htrueB x hx))
  let δ := min 1 (min eu eb)
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min heu heb)
  have hδu : δ ≤ eu := (min_le_right _ _).trans (min_le_left _ _)
  have hδb : δ ≤ eb := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨⟨amin, d, R, M, δ, hamin, hd, rfl, hM, hδ, min_le_left _ _, haminle,
    hproj, ?_, ?_, ?_⟩⟩
  · intro x hx
    exact hML (p₂ x) (mem_image_of_mem p₂ hx)
  · intro x hx r hr θ
    exact (add_le_add_right hδu 2).trans (hmargin x hx r hr θ)
  · intro x hx
    have h := heble x hx
    dsimp [highSpeed]
    linarith

theorem FamilyChoices.root_bound {X : Type*} {a m p₁ p₂ : X → ℝ} {K B : Set X}
    (c : FamilyChoices a m p₁ p₂ K B) {x : X} (hx : x ∈ K) :
    varianceRoot (a x) c.delta (nominalSpeed (a x) (m x)) ∈ Icc (0 : ℝ) c.radius := by
  have ha : 0 < a x := lt_of_lt_of_le c.aMin_pos (c.aMin_le x hx)
  rw [c.radius_eq]
  exact ⟨varianceRoot_nonneg _ _ _, varianceRoot_bound c.aMin (a x) c.delta _
    c.aMin_pos (c.aMin_le x hx) c.delta_pos c.delta_le_one (mul_pos ha (one_add_sq_pos _))⟩

theorem FamilyChoices.amplitude_bound {X : Type*} {a m p₁ p₂ : X → ℝ} {K B : Set X}
    (c : FamilyChoices a m p₁ p₂ K B) {x : X} (hx : x ∈ K) :
    0 ≤ solveScale c.d (p₂ x) (varianceRoot (a x) c.delta (nominalSpeed (a x) (m x))) ∧
      solveScale c.d (p₂ x) (varianceRoot (a x) c.delta (nominalSpeed (a x) (m x))) <
          c.maxAmplitude := by
  let r := varianceRoot (a x) c.delta (nominalSpeed (a x) (m x))
  have hr := c.root_bound hx
  have hμ := solveScale_nonneg c.d (p₂ x) r c.d_pos hr.1
  refine ⟨hμ, ?_⟩
  have htarget : tiltVariance c.d (p₂ x) (solveScale c.d (p₂ x) r) ≤ 3 / c.aMin := by
    rw [solveScale_variance _ _ _ (ne_of_gt c.d_pos)]
    have hR := Real.sq_sqrt (div_nonneg (by norm_num : (0 : ℝ) ≤ 3) c.aMin_pos.le)
    have hrle : r ≤ Real.sqrt (3 / c.aMin) := by simpa only [c.radius_eq] using hr.2
    have hsqnonneg := Real.sqrt_nonneg (3 / c.aMin)
    nlinarith [hr.1]
  by_contra hn
  have hμM : c.maxAmplitude ≤ solveScale c.d (p₂ x) r := le_of_not_gt hn
  have hmono := (tiltVariance_strictMonoOn c.d (p₂ x) c.d_pos).monotoneOn
    c.maxAmplitude_pos.le hμ hμM
  have hlarge := c.amplitude_large x hx
  linarith

section SmoothFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem nominalSpeed_family_contDiff (a m : E → ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) :
    ContDiff ℝ ∞ (fun x => nominalSpeed (a x) (m x)) :=
  ha.mul (contDiff_const.add (hm.pow 2))

theorem seedSpeed_family_contDiff (a m : E → ℝ) (δ : ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (fun x => seedSpeed (a x) (m x) δ) := by
  have hn := nominalSpeed_family_contDiff a m ha hm
  exact hn.add (((correctionRoot_contDiff δ hδ).comp hn).pow 2)

theorem seedTilt_family_contDiffOn (a m p : E → ℝ) (d δ : ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp : ContDiff ℝ ∞ p)
    (hd : d ≠ 0) (hδ : 0 < δ) :
    ContDiffOn ℝ ∞ (fun z : E × ℝ => seedTilt (a z.1) (m z.1) d (p z.1) δ z.2)
      ({x | 0 < a x} ×ˢ (univ : Set ℝ)) := by
  let S : Set (E × ℝ) := {x | 0 < a x} ×ˢ (univ : Set ℝ)
  have haf : ContDiffOn ℝ ∞ (fun z : E × ℝ => a z.1) S := (ha.comp contDiff_fst).contDiffOn
  have hmf : ContDiffOn ℝ ∞ (fun z : E × ℝ => m z.1) S := (hm.comp contDiff_fst).contDiffOn
  have hpf : ContDiffOn ℝ ∞ (fun z : E × ℝ => p z.1) S := (hp.comp contDiff_fst).contDiffOn
  have hnom : ContDiffOn ℝ ∞ (fun z : E × ℝ => nominalSpeed (a z.1) (m z.1)) S :=
    haf.mul (contDiffOn_const.add (hmf.pow 2))
  have hsqrt : ContDiffOn ℝ ∞ (fun z : E × ℝ => Real.sqrt (a z.1)) S :=
    haf.sqrt (fun z hz => ne_of_gt hz.1)
  have hroot : ContDiffOn ℝ ∞
      (fun z : E × ℝ => varianceRoot (a z.1) δ (nominalSpeed (a z.1) (m z.1))) S :=
    ((correctionRoot_contDiff δ hδ).comp_contDiffOn hnom).div hsqrt
      (fun z hz => ne_of_gt (Real.sqrt_pos.mpr hz.1))
  exact (solvedTilt_fixed_joint_contDiff d hd).comp_contDiffOn
    ((hmf.prodMk hpf).prodMk (hroot.prodMk contDiff_snd.contDiffOn))

/-- Constant density, bundling `rate`, `smooth`, `positive`, `periodic` and the required
compatibility proofs. -/
def constantDensity : CircleDensity where
  rate _ := 1 / (2 * Real.pi)
  smooth := contDiff_const
  positive _ := one_div_pos.mpr period_pos
  periodic := fun _ => rfl
  integral_one := by
    rw [intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    field_simp [Real.pi_ne_zero]

/-- Family density, defined pointwise by `if hx : 0 < a x then seedDensity (a x) (m x) d (p x) δ
hx hd hδ else constantDensity`. -/
def familyDensity (a m p : E → ℝ) (d δ : ℝ) (hd : d ≠ 0) (hδ : 0 < δ) : E → CircleDensity :=
  fun x => if hx : 0 < a x then seedDensity (a x) (m x) d (p x) δ hx hd hδ else constantDensity

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem familyDensity_eq (a m p : E → ℝ) (d δ : ℝ) (hd : d ≠ 0) (hδ : 0 < δ)
    (x : E) (hx : 0 < a x) :
    familyDensity a m p d δ hd hδ x = seedDensity (a x) (m x) d (p x) δ hx hd hδ := by
  simp only [familyDensity, dite_eq_left hx]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem familyDensity_rate_eq (a m p : E → ℝ) (d δ : ℝ) (hd : d ≠ 0) (hδ : 0 < δ)
    (x : E) (hx : 0 < a x) (θ : ℝ) :
    (familyDensity a m p d δ hd hδ x).rate θ =
      phaseDensity (a x) (seedSpeed (a x) (m x) δ) (seedTilt (a x) (m x) d (p x) δ θ) /
        (2 * Real.pi) := by
  rw [familyDensity_eq a m p d δ hd hδ x hx]
  rfl

theorem familyDensity_rate_contDiffOn (a m p : E → ℝ) (d δ : ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp : ContDiff ℝ ∞ p)
    (hd : d ≠ 0) (hδ : 0 < δ) :
    ContDiffOn ℝ ∞ (fun z : E × ℝ => (familyDensity a m p d δ hd hδ z.1).rate z.2)
      ({x | 0 < a x} ×ˢ (univ : Set ℝ)) := by
  have ht := seedTilt_family_contDiffOn a m p d δ ha hm hp hd hδ
  have hv : ContDiff ℝ ∞ (fun z : E × ℝ => seedSpeed (a z.1) (m z.1) δ) :=
    (seedSpeed_family_contDiff a m δ ha hm hδ).comp contDiff_fst
  have hrat : ContDiffOn ℝ ∞ (fun z : E × ℝ =>
      phaseDensity (a z.1) (seedSpeed (a z.1) (m z.1) δ) (seedTilt (a z.1) (m z.1) d (p z.1) δ z.2)
          /
        (2 * Real.pi)) ({x | 0 < a x} ×ˢ (univ : Set ℝ)) := by
    exact (((ha.comp contDiff_fst).contDiffOn.mul (contDiffOn_const.add (ht.pow 2))).div
      hv.contDiffOn (fun z _ => ne_of_gt (lt_trans (by norm_num)
        (seedSpeed_gt_two (a z.1) (m z.1) δ hδ)))).div_const _
  apply hrat.congr
  intro z hz
  exact familyDensity_rate_eq a m p d δ hd hδ z.1 hz.1 z.2

/-- Unphased A, given by `loopA (seedSpeed (a z.1) (m z.1) δ) (seedTilt (a z.1) (m z.1) d (p
z.1) δ z.2)`. -/
def unphasedA (a m p : E → ℝ) (d δ : ℝ) (z : E × ℝ) : ℝ :=
  loopA (seedSpeed (a z.1) (m z.1) δ) (seedTilt (a z.1) (m z.1) d (p z.1) δ z.2)

/-- Unphased C, given by `loopC (seedSpeed (a z.1) (m z.1) δ) (seedTilt (a z.1) (m z.1) d (p
z.1) δ z.2)`. -/
def unphasedC (a m p : E → ℝ) (d δ : ℝ) (z : E × ℝ) : ℝ :=
  loopC (seedSpeed (a z.1) (m z.1) δ) (seedTilt (a z.1) (m z.1) d (p z.1) δ z.2)

theorem unphased_contDiffOn (a m p : E → ℝ) (d δ : ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp : ContDiff ℝ ∞ p)
    (hd : d ≠ 0) (hδ : 0 < δ) :
    ContDiffOn ℝ ∞ (unphasedA a m p d δ) ({x | 0 < a x} ×ˢ (univ : Set ℝ)) ∧
      ContDiffOn ℝ ∞ (unphasedC a m p d δ) ({x | 0 < a x} ×ˢ (univ : Set ℝ)) := by
  have ht := seedTilt_family_contDiffOn a m p d δ ha hm hp hd hδ
  have hv : ContDiffOn ℝ ∞ (fun z : E × ℝ => seedSpeed (a z.1) (m z.1) δ)
      ({x | 0 < a x} ×ˢ (univ : Set ℝ)) :=
    ((seedSpeed_family_contDiff a m δ ha hm hδ).comp contDiff_fst).contDiffOn
  have hden : ContDiffOn ℝ ∞
      (fun z : E × ℝ => 1 + seedTilt (a z.1) (m z.1) d (p z.1) δ z.2 ^ 2)
      ({x | 0 < a x} ×ˢ (univ : Set ℝ)) := contDiffOn_const.add (ht.pow 2)
  have hnz : ∀ z ∈ ({x | 0 < a x} ×ˢ (univ : Set ℝ)),
      1 + seedTilt (a z.1) (m z.1) d (p z.1) δ z.2 ^ 2 ≠ 0 :=
    fun z _ => ne_of_gt (one_add_sq_pos _)
  exact ⟨hv.div hden hnz, (hv.mul ht).div hden hnz⟩

/-- Family A, given by `rephase (familyDensity a m p d δ hd hδ z.1) (fun θ => unphasedA a m p d
δ (z.1, θ)) z.2`. -/
def familyA (a m p : E → ℝ) (d δ : ℝ) (hd : d ≠ 0) (hδ : 0 < δ) (z : E × ℝ) : ℝ :=
  rephase (familyDensity a m p d δ hd hδ z.1)
    (fun θ => unphasedA a m p d δ (z.1, θ)) z.2

/-- Family C, given by `rephase (familyDensity a m p d δ hd hδ z.1) (fun θ => unphasedC a m p d
δ (z.1, θ)) z.2`. -/
def familyC (a m p : E → ℝ) (d δ : ℝ) (hd : d ≠ 0) (hδ : 0 < δ) (z : E × ℝ) : ℝ :=
  rephase (familyDensity a m p d δ hd hδ z.1)
    (fun θ => unphasedC a m p d δ (z.1, θ)) z.2

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem familyA_eq_constructed (a m p : E → ℝ) (d δ : ℝ) (hd : d ≠ 0) (hδ : 0 < δ)
    (x : E) (hx : 0 < a x) :
    (fun φ => familyA a m p d δ hd hδ (x, φ)) = constructedA (a x) (m x) d (p x) δ hx hd hδ := by
  funext φ
  unfold familyA
  rw [familyDensity_eq a m p d δ hd hδ x hx]
  rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem familyC_eq_constructed (a m p : E → ℝ) (d δ : ℝ) (hd : d ≠ 0) (hδ : 0 < δ)
    (x : E) (hx : 0 < a x) :
    (fun φ => familyC a m p d δ hd hδ (x, φ)) = constructedC (a x) (m x) d (p x) δ hx hd hδ := by
  funext φ
  unfold familyC
  rw [familyDensity_eq a m p d δ hd hδ x hx]
  rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem family_pointwise_properties (a m p₁ p₂ : E → ℝ) {K B : Set E}
    (c : FamilyChoices a m p₁ p₂ K B)
    (hrelaxed : ∀ x ∈ K, nominalSpeed (a x) (m x) <
      coneBound (p₁ x + p₂ x * m x) (p₂ x - p₁ x * m x)) :
    ∀ x ∈ K,
      Function.Periodic (fun φ => familyA a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos (x, φ))
          1 ∧
      Function.Periodic (fun φ => familyC a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos (x, φ))
          1 ∧
      (∫ φ in (0 : ℝ)..1, familyA a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos (x, φ)) = a x ∧
      (∫ φ in (0 : ℝ)..1, familyC a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos (x, φ)) = a x *
          m x ∧
      ∀ φ, InTrueCone (p₁ x) (p₂ x)
        (familyA a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos (x, φ))
        (familyC a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos (x, φ)) := by
  intro x hx
  have hax : 0 < a x := lt_of_lt_of_le c.aMin_pos (c.aMin_le x hx)
  have hAe := familyA_eq_constructed a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos x hax
  have hCe := familyC_eq_constructed a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos x hax
  have hp := constructed_periodic (a x) (m x) c.d (p₂ x) c.delta hax (ne_of_gt c.d_pos) c.delta_pos
  have hm := constructed_means (a x) (m x) c.d (p₂ x) c.delta hax (ne_of_gt c.d_pos) c.delta_pos
  have hR : Real.sqrt (3 / a x) ≤ c.radius := by
    rw [c.radius_eq]
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by norm_num) c.aMin_pos (c.aMin_le x hx))
  have hc := constructed_trueCone (a x) (m x) (p₁ x) (p₂ x) c.d c.delta c.radius hax c.d_pos
    c.delta_pos c.delta_le_one hR (c.projection_margin x hx) (hrelaxed x hx) (c.cone_margin x hx)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hAe]
    exact hp.1
  · rw [hCe]
    exact hp.2
  · simpa only [hAe] using hm.1
  · simpa only [hCe] using hm.2
  · intro φ
    rw [congrFun hAe φ, congrFun hCe φ]
    exact hc φ

omit [NormedSpace ℝ E] in
theorem family_nominal_neighborhood (a m p₁ p₂ : E → ℝ) {K B : Set E}
    (c : FamilyChoices a m p₁ p₂ K B) (ha : Continuous a) (hm : Continuous m) (hBK : B ⊆ K) :
    ∃ N : Set E, IsOpen N ∧ B ⊆ N ∧ N ⊆ {x | 0 < a x} ∧
      ∀ x ∈ N, ∀ φ,
        familyA a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos (x, φ) = a x ∧
        familyC a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos (x, φ) = a x * m x := by
  let N : Set E := {x | 0 < a x} ∩ {x | highSpeed c.delta < nominalSpeed (a x) (m x)}
  have hnom : Continuous (fun x => nominalSpeed (a x) (m x)) := ha.mul (continuous_const.add
      (hm.pow 2))
  have hN : IsOpen N := (isOpen_lt continuous_const ha).inter (isOpen_lt continuous_const hnom)
  have hBN : B ⊆ N := by
    intro x hx
    exact ⟨lt_of_lt_of_le c.aMin_pos (c.aMin_le x (hBK hx)), c.boundary_inactive x hx⟩
  refine ⟨N, hN, hBN, inter_subset_left, ?_⟩
  intro x hx φ
  have hAe := familyA_eq_constructed a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos x hx.1
  have hCe := familyC_eq_constructed a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos x hx.1
  have hn := constructed_nominal (a x) (m x) c.d (p₂ x) c.delta hx.1
    (ne_of_gt c.d_pos) c.delta_pos hx.2.le
  rw [congrFun hAe φ, congrFun hCe φ, hn.1, hn.2]
  exact ⟨rfl, rfl⟩

theorem family_joint_contDiffOn [FiniteDimensional ℝ E]
    (a m p : E → ℝ) (d δ : ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp : ContDiff ℝ ∞ p)
    (hd : d ≠ 0) (hδ : 0 < δ) :
    ContDiffOn ℝ ∞ (familyA a m p d δ hd hδ) ({x | 0 < a x} ×ˢ (univ : Set ℝ)) ∧
      ContDiffOn ℝ ∞ (familyC a m p d δ hd hδ) ({x | 0 < a x} ×ˢ (univ : Set ℝ)) := by
  have hU : IsOpen {x | 0 < a x} := isOpen_lt continuous_const ha.continuous
  have hrate := familyDensity_rate_contDiffOn a m p d δ ha hm hp hd hδ
  have hf := unphased_contDiffOn a m p d δ ha hm hp hd hδ
  exact ⟨ParametricRephase.rephaseFamily_contDiffOn (familyDensity a m p d δ hd hδ)
      (unphasedA a m p d δ) _ hU hrate hf.1,
    ParametricRephase.rephaseFamily_contDiffOn (familyDensity a m p d δ hd hδ)
      (unphasedC a m p d δ) _ hU hrate hf.2⟩

/-- Full compact-family true-cone realization. The set `B` can be the two
interval boundary faces (including any compact auxiliary parameter set).
The output agrees exactly with the nominal shear on an open neighborhood
of `B`, and is jointly C∞ in slow parameters and periodic angle. -/
theorem exists_compact_trueCone_family [FiniteDimensional ℝ E]
    (a m p₁ p₂ : E → ℝ) {K B : Set E}
    (hK : IsCompact K) (hB : IsCompact B) (hBK : B ⊆ K)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m)
    (hp₁ : ContDiff ℝ ∞ p₁) (hp₂ : ContDiff ℝ ∞ p₂)
    (haK : ∀ x ∈ K, 0 < a x)
    (hPK : ∀ x ∈ K, 2 < p₁ x + p₂ x * m x)
    (hrelaxed : ∀ x ∈ K, nominalSpeed (a x) (m x) <
      coneBound (p₁ x + p₂ x * m x) (p₂ x - p₁ x * m x))
    (htrueB : ∀ x ∈ B, 2 < nominalSpeed (a x) (m x)) :
    ∃ U N : Set E, ∃ A C : E × ℝ → ℝ,
      IsOpen U ∧ K ⊆ U ∧ IsOpen N ∧ B ⊆ N ∧ N ⊆ U ∧
      ContDiffOn ℝ ∞ A (U ×ˢ (univ : Set ℝ)) ∧
      ContDiffOn ℝ ∞ C (U ×ˢ (univ : Set ℝ)) ∧
      (∀ x ∈ K, Function.Periodic (fun φ => A (x, φ)) 1 ∧
        Function.Periodic (fun φ => C (x, φ)) 1 ∧
        (∫ φ in (0 : ℝ)..1, A (x, φ)) = a x ∧
        (∫ φ in (0 : ℝ)..1, C (x, φ)) = a x * m x ∧
        ∀ φ, InTrueCone (p₁ x) (p₂ x) (A (x, φ)) (C (x, φ))) ∧
      (∀ x ∈ N, ∀ φ, A (x, φ) = a x ∧ C (x, φ) = a x * m x) := by
  obtain ⟨c⟩ := exists_family_choices a m p₁ p₂ hK hB ha.continuous hm.continuous
    hp₁.continuous hp₂.continuous haK hPK htrueB
  let U : Set E := {x | 0 < a x}
  let A := familyA a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos
  let C := familyC a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos
  obtain ⟨N, hN, hBN, hNU, hmatch⟩ :=
    family_nominal_neighborhood a m p₁ p₂ c ha.continuous hm.continuous hBK
  have hs := family_joint_contDiffOn a m p₂ c.d c.delta ha hm hp₂ (ne_of_gt c.d_pos) c.delta_pos
  exact ⟨U, N, A, C, isOpen_lt continuous_const ha.continuous, haK,
    hN, hBN, hNU, hs.1, hs.2, family_pointwise_properties a m p₁ p₂ c hrelaxed, hmatch⟩

/-- The complete family theorem with one strictly positive margin valid
for every slow parameter in `K` and every fast angle. -/
theorem exists_compact_trueCone_family_with_margin [FiniteDimensional ℝ E]
    (a m p₁ p₂ : E → ℝ) {K B : Set E}
    (hK : IsCompact K) (hB : IsCompact B) (hBK : B ⊆ K)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m)
    (hp₁ : ContDiff ℝ ∞ p₁) (hp₂ : ContDiff ℝ ∞ p₂)
    (haK : ∀ x ∈ K, 0 < a x)
    (hPK : ∀ x ∈ K, 2 < p₁ x + p₂ x * m x)
    (hrelaxed : ∀ x ∈ K, nominalSpeed (a x) (m x) <
      coneBound (p₁ x + p₂ x * m x) (p₂ x - p₁ x * m x))
    (htrueB : ∀ x ∈ B, 2 < nominalSpeed (a x) (m x)) :
    ∃ ε : ℝ, ∃ U N : Set E, ∃ A C : E × ℝ → ℝ,
      0 < ε ∧ IsOpen U ∧ K ⊆ U ∧ IsOpen N ∧ B ⊆ N ∧ N ⊆ U ∧
      ContDiffOn ℝ ∞ A (U ×ˢ (univ : Set ℝ)) ∧
      ContDiffOn ℝ ∞ C (U ×ˢ (univ : Set ℝ)) ∧
      (∀ x ∈ K, Function.Periodic (fun φ => A (x, φ)) 1 ∧
        Function.Periodic (fun φ => C (x, φ)) 1 ∧
        (∫ φ in (0 : ℝ)..1, A (x, φ)) = a x ∧
        (∫ φ in (0 : ℝ)..1, C (x, φ)) = a x * m x ∧
        ∀ φ, InTrueCone (p₁ x) (p₂ x) (A (x, φ)) (C (x, φ)) ∧
          HasConeMargin ε (p₁ x) (p₂ x) (A (x, φ)) (C (x, φ))) ∧
      (∀ x ∈ N, ∀ φ, A (x, φ) = a x ∧ C (x, φ) = a x * m x) := by
  obtain ⟨U, N, A, C, hU, hKU, hN, hBN, hNU, hA, hC, hloops, hmatch⟩ :=
    exists_compact_trueCone_family a m p₁ p₂ hK hB hBK ha hm hp₁ hp₂ haK hPK hrelaxed htrueB
  have hsub : K ×ˢ (univ : Set ℝ) ⊆ U ×ˢ (univ : Set ℝ) :=
    fun _ hz => ⟨hKU hz.1, hz.2⟩
  obtain ⟨ε, hε, hmargin⟩ := compact_periodic_trueCone_margins p₁ p₂ A C hK
    hp₁.continuous.continuousOn hp₂.continuous.continuousOn
    (hA.continuousOn.mono hsub) (hC.continuousOn.mono hsub)
    (fun x hx => (hloops x hx).1) (fun x hx => (hloops x hx).2.1)
    (fun x hx => (hloops x hx).2.2.2.2)
  refine ⟨ε, U, N, A, C, hε, hU, hKU, hN, hBN, hNU, hA, hC, ?_, hmatch⟩
  intro x hx
  obtain ⟨hpA, hpC, hmA, hmC, hc⟩ := hloops x hx
  exact ⟨hpA, hpC, hmA, hmC, fun φ => ⟨hc φ, hmargin x hx φ⟩⟩

end SmoothFamily

end

end NavierStokes.TrueConeLoop

end

end

section

/-!
# Rapid radial modulation

Concrete chain rules, shear identities, and estimates for the modulation in
Proposition 6.2. Frequencies are positive real numbers; hence the results apply
in particular to positive integer frequencies. All derivatives are genuine
`deriv`/`fderiv` derivatives, rather than formal differential symbols.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.RadialModulation

open Set MeasureTheory
open scoped ContDiff Topology

/-- Phase point: an abbreviation for `ℝ × ℝ × ℝ`. -/
abbrev PhasePoint := ℝ × ℝ × ℝ
/-- Base profile: an abbreviation for `ℝ → ℝ → ℝ`. -/
abbrev BaseProfile := ℝ → ℝ → ℝ
/-- Primitive profile: an abbreviation for `PhasePoint → ℝ`. -/
abbrev PrimitiveProfile := PhasePoint → ℝ

/-- Phase point, given by `(X, η, n * Real.log X)`. -/
def phasePoint (n X η : ℝ) : PhasePoint := (X, η, n * Real.log X)
/-- Partial X, given by `fderiv ℝ A z (1, 0, 0)`. -/
def partialX (A : PrimitiveProfile) (z : PhasePoint) : ℝ := fderiv ℝ A z (1, 0, 0)
/-- Partial eta, given by `fderiv ℝ A z (0, 1, 0)`. -/
def partialEta (A : PrimitiveProfile) (z : PhasePoint) : ℝ := fderiv ℝ A z (0, 1, 0)
/-- Partial theta, given by `fderiv ℝ A z (0, 0, 1)`. -/
def partialTheta (A : PrimitiveProfile) (z : PhasePoint) : ℝ := fderiv ℝ A z (0, 0, 1)

/-- Modulated E, given by `E X η * Real.exp (A (phasePoint n X η) / n)`. -/
def modulatedE (n : ℝ) (E : BaseProfile) (A : PrimitiveProfile) (X η : ℝ) : ℝ :=
  E X η * Real.exp (A (phasePoint n X η) / n)

/-- Modulated U, given by `U X η + B (phasePoint n X η) / n`. -/
def modulatedU (n : ℝ) (U : BaseProfile) (B : PrimitiveProfile) (X η : ℝ) : ℝ :=
  U X η + B (phasePoint n X η) / n

/-- The logarithmic graph and modulated angular profile are genuinely smooth
at every positive radius (indeed at every nonzero radius). -/
theorem modulatedE_contDiffAt
    (E : BaseProfile) (A : PrimitiveProfile) (n X η : ℝ)
    (hE : ContDiff ℝ ∞ (Function.uncurry E)) (hA : ContDiff ℝ ∞ A) (hX : X ≠ 0) :
    ContDiffAt ℝ ∞ (Function.uncurry (modulatedE n E A)) (X, η) := by
  have hgraph : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => phasePoint n z.1 z.2) (X, η) :=
    contDiffAt_fst.prodMk (contDiffAt_snd.prodMk
      (contDiffAt_const.mul (contDiffAt_fst.log hX)))
  exact hE.contDiffAt.mul (((hA.contDiffAt.comp (X, η) hgraph).div_const n).exp)

theorem modulatedU_contDiffAt
    (U : BaseProfile) (B : PrimitiveProfile) (n X η : ℝ)
    (hU : ContDiff ℝ ∞ (Function.uncurry U)) (hB : ContDiff ℝ ∞ B) (hX : X ≠ 0) :
    ContDiffAt ℝ ∞ (Function.uncurry (modulatedU n U B)) (X, η) := by
  have hgraph : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => phasePoint n z.1 z.2) (X, η) :=
    contDiffAt_fst.prodMk (contDiffAt_snd.prodMk
      (contDiffAt_const.mul (contDiffAt_fst.log hX)))
  exact hU.contDiffAt.add ((hB.contDiffAt.comp (X, η) hgraph).div_const n)

/-- The rapid radial phase contributes exactly `(n/X) A_θ`. -/
theorem phase_hasDerivAt_X
    (A : PrimitiveProfile) (n X η : ℝ) (hX : X ≠ 0)
    (hA : DifferentiableAt ℝ A (phasePoint n X η)) :
    HasDerivAt (fun r => A (phasePoint n r η))
      (partialX A (phasePoint n X η) +
        (n / X) * partialTheta A (phasePoint n X η)) X := by
  have hg := (hasDerivAt_id X).prodMk
    ((hasDerivAt_const X η).prodMk ((Real.hasDerivAt_log hX).const_mul n))
  have hc := hA.hasFDerivAt.comp_hasDerivAt X hg
  have hv : (1, (0, n * X⁻¹)) =
      (1, 0, 0) + (n / X) • ((0, 0, 1) : PhasePoint) := by
    ext <;> simp [div_eq_mul_inv]
  rw [hv, map_add, map_smul] at hc
  simpa only [id_eq, phasePoint, Function.comp_def, partialX, partialTheta, smul_eq_mul] using hc

/-- The rapid phase is independent of η, so no frequency enters this derivative. -/
theorem phase_hasDerivAt_eta
    (A : PrimitiveProfile) (n X η : ℝ)
    (hA : DifferentiableAt ℝ A (phasePoint n X η)) :
    HasDerivAt (fun e => A (phasePoint n X e))
      (partialEta A (phasePoint n X η)) η := by
  have hg := (hasDerivAt_const η X).prodMk
    ((hasDerivAt_id η).prodMk (hasDerivAt_const η (n * Real.log X)))
  exact hA.hasFDerivAt.comp_hasDerivAt η hg

/-- Exact radial derivative of the multiplicative angular modulation. -/
theorem modulatedE_hasDerivAt_X
    (E : BaseProfile) (A : PrimitiveProfile) (n X η : ℝ) (hn : n ≠ 0) (hX : X ≠ 0)
    (hE : DifferentiableAt ℝ (fun r => E r η) X)
    (hA : DifferentiableAt ℝ A (phasePoint n X η)) :
    HasDerivAt (fun r => modulatedE n E A r η)
      (Real.exp (A (phasePoint n X η) / n) *
        (deriv (fun r => E r η) X + E X η *
          (partialX A (phasePoint n X η) / n + partialTheta A (phasePoint n X η) / X))) X := by
  have hd := hE.hasDerivAt.mul (((phase_hasDerivAt_X A n X η hX hA).div_const n).exp)
  apply hd.congr_deriv
  field_simp

/-- Exact radial derivative of the additive axial modulation. -/
theorem modulatedU_hasDerivAt_X
    (U : BaseProfile) (B : PrimitiveProfile) (n X η : ℝ) (hn : n ≠ 0) (hX : X ≠ 0)
    (hU : DifferentiableAt ℝ (fun r => U r η) X)
    (hB : DifferentiableAt ℝ B (phasePoint n X η)) :
    HasDerivAt (fun r => modulatedU n U B r η)
      (deriv (fun r => U r η) X + partialX B (phasePoint n X η) / n +
        partialTheta B (phasePoint n X η) / X) X := by
  have hd := hU.hasDerivAt.add ((phase_hasDerivAt_X B n X η hX hB).div_const n)
  apply hd.congr_deriv
  field_simp; ring

theorem modulatedE_hasDerivAt_eta
    (E : BaseProfile) (A : PrimitiveProfile) (n X η : ℝ)
    (hE : DifferentiableAt ℝ (E X) η)
    (hA : DifferentiableAt ℝ A (phasePoint n X η)) :
    HasDerivAt (modulatedE n E A X)
      (deriv (E X) η * Real.exp (A (phasePoint n X η) / n) +
        E X η * (Real.exp (A (phasePoint n X η) / n) *
          (partialEta A (phasePoint n X η) / n))) η := by
  exact hE.hasDerivAt.mul (((phase_hasDerivAt_eta A n X η hA).div_const n).exp)

theorem modulatedU_hasDerivAt_eta
    (U : BaseProfile) (B : PrimitiveProfile) (n X η : ℝ)
    (hU : DifferentiableAt ℝ (U X) η)
    (hB : DifferentiableAt ℝ B (phasePoint n X η)) :
    HasDerivAt (modulatedU n U B X)
      (deriv (U X) η + partialEta B (phasePoint n X η) / n) η := by
  exact hU.hasDerivAt.add ((phase_hasDerivAt_eta B n X η hB).div_const n)

/-- Exact angular shear: the only error after the primitive prescription is
the slow radial derivative of `A`, divided by frequency. -/
theorem angular_shear_exact
    (E : BaseProfile) (A : PrimitiveProfile) (n X η aL : ℝ)
    (hn : n ≠ 0) (hX : X ≠ 0) (hE0 : E X η ≠ 0)
    (hE : DifferentiableAt ℝ (fun r => E r η) X)
    (hA : DifferentiableAt ℝ A (phasePoint n X η))
    (hprescribed : partialTheta A (phasePoint n X η) =
      -(aL - (1 - 2 * X * deriv (fun r => E r η) X / E X η)) / 2) :
    1 - 2 * X * deriv (fun r => modulatedE n E A r η) X / modulatedE n E A X η =
      aL - 2 * X * partialX A (phasePoint n X η) / n := by
  rw [(modulatedE_hasDerivAt_X E A n X η hn hX hE hA).deriv]
  unfold modulatedE
  rw [hprescribed]
  field_simp [Real.exp_ne_zero]; ring

/-- Exact axial shear, including the multiplicative correction caused by the
changed angular velocity in its denominator. -/
theorem axial_shear_exact
    (E U : BaseProfile) (A B : PrimitiveProfile) (n X η bL : ℝ)
    (hn : n ≠ 0) (hX : X ≠ 0) (hE0 : E X η ≠ 0)
    (hU : DifferentiableAt ℝ (fun r => U r η) X)
    (hB : DifferentiableAt ℝ B (phasePoint n X η))
    (hprescribed : partialTheta B (phasePoint n X η) =
      E X η * (bL - 2 * X * deriv (fun r => U r η) X / E X η) / 2) :
    2 * X * deriv (fun r => modulatedU n U B r η) X / modulatedE n E A X η =
      (bL + 2 * X * partialX B (phasePoint n X η) / (n * E X η)) /
        Real.exp (A (phasePoint n X η) / n) := by
  rw [(modulatedU_hasDerivAt_X U B n X η hn hX hU hB).deriv]
  unfold modulatedE
  rw [hprescribed]
  field_simp [Real.exp_ne_zero]; ring

/-- Explicit uniform value estimate once the frequency exceeds the bound on A. -/
theorem angular_value_bound
    (E A n CE CA : ℝ) (hn : 0 < n) (hE : |E| ≤ CE) (hA : |A| ≤ CA) (hCA : CA ≤ n) :
    |E * Real.exp (A / n) - E| ≤ 2 * CE * CA / n := by
  have hCE : 0 ≤ CE := (abs_nonneg E).trans hE
  have hCA0 : 0 ≤ CA := (abs_nonneg A).trans hA
  have hsmall : |A / n| ≤ 1 := by
    rw [abs_div, abs_of_pos hn]
    exact (div_le_one hn).mpr (hA.trans hCA)
  calc
    |E * Real.exp (A / n) - E| = |E| * |Real.exp (A / n) - 1| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ CE * (2 * |A / n|) :=
      mul_le_mul hE (Real.abs_exp_sub_one_le hsmall) (abs_nonneg _) hCE
    _ ≤ CE * (2 * (CA / n)) := by
      rw [abs_div, abs_of_pos hn]
      gcongr
    _ = 2 * CE * CA / n := by ring

theorem axial_value_bound
    (U B n CB : ℝ) (hn : 0 < n) (hB : |B| ≤ CB) :
    |U + B / n - U| ≤ CB / n := by
  have heq : U + B / n - U = B / n := by ring
  rw [heq, abs_div, abs_of_pos hn]
  exact div_le_div_of_nonneg_right hB hn.le

/-- The primitive is an actual interval integral. -/
def periodicPrimitive (q : ℝ → ℝ) (θ : ℝ) : ℝ := intervalIntegral q 0 θ volume

theorem periodicPrimitive_hasDerivAt
    (q : ℝ → ℝ) (hq : Continuous q) (θ : ℝ) :
    HasDerivAt (periodicPrimitive q) (q θ) θ := by
  exact intervalIntegral.integral_hasDerivAt_right (hq.intervalIntegrable 0 θ)
    hq.aestronglyMeasurable.stronglyMeasurableAtFilter hq.continuousAt

/-- Zero mean is precisely what removes the drift of the integral primitive. -/
theorem periodicPrimitive_periodic
    (q : ℝ → ℝ) (hq : Continuous q) (hperiodic : Function.Periodic q 1)
    (hzero : intervalIntegral q 0 1 volume = 0) :
    Function.Periodic (periodicPrimitive q) 1 := by
  intro θ
  simpa only [periodicPrimitive, zero_add, hzero, add_zero] using
    hperiodic.intervalIntegral_add_eq_add 0 θ (fun a b => hq.intervalIntegrable a b)

/-- The integral primitive inherits all finite smoothness orders from q. -/
theorem periodicPrimitive_contDiff
    (q : ℝ → ℝ) (hq : ContDiff ℝ ∞ q) : ContDiff ℝ ∞ (periodicPrimitive q) := by
  apply contDiff_infty_iff_deriv.mpr
  have hd : deriv (periodicPrimitive q) = q :=
    funext (fun θ => (periodicPrimitive_hasDerivAt q hq.continuous θ).deriv)
  exact ⟨fun θ => (periodicPrimitive_hasDerivAt q hq.continuous θ).differentiableAt, hd.symm ▸ hq⟩

/-- Subtracting the primitive's mean fixes the zero-mean normalization. -/
def zeroMeanPrimitive (q : ℝ → ℝ) (θ : ℝ) : ℝ :=
  periodicPrimitive q θ - intervalIntegral (periodicPrimitive q) 0 1 volume

theorem zeroMeanPrimitive_hasDerivAt
    (q : ℝ → ℝ) (hq : Continuous q) (θ : ℝ) :
    HasDerivAt (zeroMeanPrimitive q) (q θ) θ := by
  exact (periodicPrimitive_hasDerivAt q hq θ).sub_const _

theorem zeroMeanPrimitive_integral
    (q : ℝ → ℝ) (hq : Continuous q) :
    intervalIntegral (zeroMeanPrimitive q) 0 1 volume = 0 := by
  have hd : Differentiable ℝ (periodicPrimitive q) :=
    fun θ => (periodicPrimitive_hasDerivAt q hq θ).differentiableAt
  have hc : Continuous (periodicPrimitive q) := hd.continuous
  unfold zeroMeanPrimitive
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable 0 1)
    (continuous_const.intervalIntegrable 0 1)]
  simp

/-- Every smooth period-one, mean-zero source has an actual smooth period-one,
mean-zero primitive, with its derivative proved by the fundamental theorem. -/
theorem exists_smooth_periodic_zeroMean_primitive
    (q : ℝ → ℝ) (hq : ContDiff ℝ ∞ q) (hperiodic : Function.Periodic q 1)
    (hzero : intervalIntegral q 0 1 volume = 0) :
    ∃ A : ℝ → ℝ, ContDiff ℝ ∞ A ∧ Function.Periodic A 1 ∧
      intervalIntegral A 0 1 volume = 0 ∧ ∀ θ, HasDerivAt A (q θ) θ := by
  refine ⟨zeroMeanPrimitive q, (periodicPrimitive_contDiff q hq).sub contDiff_const, ?_,
    zeroMeanPrimitive_integral q hq.continuous, zeroMeanPrimitive_hasDerivAt q hq.continuous⟩
  intro θ
  unfold zeroMeanPrimitive
  rw [periodicPrimitive_periodic q hq.continuous hperiodic hzero θ]

/-- Interface for a loop with prescribed mean: subtract the nominal shear and
scale it, then construct its normalized primitive. Choosing `c = -1/2` gives
the angular primitive; `c = E/2` gives the axial primitive. -/
theorem exists_primitive_of_prescribed_mean
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hperiodic : Function.Periodic f 1)
    (m c : ℝ) (hmean : intervalIntegral f 0 1 volume = m) :
    ∃ A : ℝ → ℝ, ContDiff ℝ ∞ A ∧ Function.Periodic A 1 ∧
      intervalIntegral A 0 1 volume = 0 ∧ ∀ θ, HasDerivAt A (c * (f θ - m)) θ := by
  have hq : ContDiff ℝ ∞ (fun θ => c * (f θ - m)) :=
    contDiff_const.mul (hf.sub contDiff_const)
  have hp : Function.Periodic (fun θ => c * (f θ - m)) 1 := by
    intro θ
    change c * (f (θ + 1) - m) = c * (f θ - m)
    rw [hperiodic θ]
  have hz : intervalIntegral (fun θ => c * (f θ - m)) 0 1 volume = 0 := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (hf.continuous.intervalIntegrable 0 1)
        (continuous_const.intervalIntegrable 0 1)]
    simp [hmean]
  exact exists_smooth_periodic_zeroMean_primitive (fun θ => c * (f θ - m)) hq hp hz

/-! ### Uniform bounds for every fixed parameter jet -/

/-- Coordinates are amplitude, radius, parameter, periodic angle. -/
abbrev FamilyPoint := ℝ × PhasePoint

/-- Eta direction, given by `(0, 0, 1, 0)`. -/
def etaDirection : FamilyPoint := (0, 0, 1, 0)
/-- Amplitude direction, given by `(1, 0, 0, 0)`. -/
def amplitudeDirection : FamilyPoint := (1, 0, 0, 0)

/-- Iterated genuine directional derivatives in the parameter coordinate. -/
def etaJet : ℕ → (FamilyPoint → ℝ) → FamilyPoint → ℝ
  | 0, F => F
  | k + 1, F => fun z => fderiv ℝ (etaJet k F) z etaDirection

theorem etaJet_contDiff (F : FamilyPoint → ℝ) (hF : ContDiff ℝ ∞ F) (k : ℕ) :
    ContDiff ℝ ∞ (etaJet k F) := by
  induction k with
  | zero => exact hF
  | succ k ih =>
    exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

/-- The directional jet is exactly the ordinary iterated derivative along η. -/
theorem etaJet_eq_iteratedDeriv
    (F : FamilyPoint → ℝ) (hF : ContDiff ℝ ∞ F) (k : ℕ) (ε X η θ : ℝ) :
    iteratedDeriv k (fun e => F (ε, X, e, θ)) η = etaJet k F (ε, X, η, θ) := by
  induction k generalizing η with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ]
    rw [show iteratedDeriv k (fun e => F (ε, X, e, θ)) =
      (fun e => etaJet k F (ε, X, e, θ)) from funext ih]
    have hd := ((etaJet_contDiff F hF k).differentiable (by simp) (ε, X, η, θ)).hasFDerivAt
    have hg := (hasDerivAt_const η ε).prodMk
      ((hasDerivAt_const η X).prodMk
        ((hasDerivAt_id η).prodMk (hasDerivAt_const η θ)))
    exact (hd.comp_hasDerivAt η hg).deriv

/-- A smooth periodic family varies by `C_k/n` in each fixed η derivative,
uniformly on compact radius/parameter sets and all angles. The constant is
proved to exist by compactness of the actual next derivative, then the MVT. -/
theorem uniform_periodic_family_eta_jets
    (F : FamilyPoint → ℝ) (hF : ContDiff ℝ ∞ F)
    (hperiodic : ∀ ε X η, Function.Periodic (fun θ => F (ε, X, η, θ)) 1)
    (KX Kη : Set ℝ) (hKX : IsCompact KX) (hKη : IsCompact Kη) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℝ, 1 ≤ n → ∀ X ∈ KX, ∀ η ∈ Kη, ∀ θ : ℝ,
      |iteratedDeriv k (fun e => F (1 / n, X, e, θ)) η -
        iteratedDeriv k (fun e => F (0, X, e, θ)) η| ≤ C / n := by
  have hj := etaJet_contDiff F hF k
  have hdj : ContDiff ℝ ∞ (fderiv ℝ (etaJet k F)) := hj.fderiv_right (by simp)
  have hd : Continuous (fun z => fderiv ℝ (etaJet k F) z amplitudeDirection) :=
    (hdj.clm_apply contDiff_const).continuous
  have hcompact : IsCompact ((Icc (0 : ℝ) 1) ×ˢ (KX ×ˢ (Kη ×ˢ Icc (0 : ℝ) 1))) :=
    isCompact_Icc.prod (hKX.prod (hKη.prod isCompact_Icc))
  obtain ⟨C₀, hC₀⟩ := hcompact.exists_bound_of_continuousOn hd.continuousOn
  let C := max C₀ 0
  have hlocal : ∀ ε ∈ Icc (0 : ℝ) 1, ∀ X ∈ KX, ∀ η ∈ Kη,
      ∀ θ ∈ Icc (0 : ℝ) 1,
      |etaJet k F (ε, X, η, θ) - etaJet k F (0, X, η, θ)| ≤ C * ε := by
    intro ε hε X hX η hη θ hθ
    have hderiv : ∀ s ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt (fun a => etaJet k F (a, X, η, θ))
          (fderiv ℝ (etaJet k F) (s, X, η, θ) amplitudeDirection) (Icc (0 : ℝ) 1) s := by
      intro s hs
      have hg := (hasDerivAt_id s).prodMk (hasDerivAt_const s ((X, η, θ) : PhasePoint))
      exact (((hj.differentiable (by simp) (s, X, η, θ)).hasFDerivAt).comp_hasDerivAt
        s hg).hasDerivWithinAt
    have hbound : ∀ s ∈ Icc (0 : ℝ) 1,
        ‖fderiv ℝ (etaJet k F) (s, X, η, θ) amplitudeDirection‖ ≤ C := by
      intro s hs
      exact (hC₀ (s, X, η, θ) ⟨hs, hX, hη, hθ⟩).trans (le_max_left _ _)
    have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      (convex_Icc (0 : ℝ) 1) (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩) hε
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hε.1] using hm
  refine ⟨C, le_max_right _ _, ?_⟩
  intro n hn X hX η hη θ
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hε : 1 / n ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg zero_le_one hn0.le, (div_le_one hn0).mpr hn⟩
  have hθ : Int.fract θ ∈ Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg θ, (Int.fract_lt_one θ).le⟩
  have heq : ∀ ε, (fun e => F (ε, X, e, θ)) = (fun e => F (ε, X, e, Int.fract θ)) := by
    intro ε
    funext e
    symm
    simpa only [Int.fract, mul_one] using
      (hperiodic ε X e).sub_int_mul_eq (x := θ) (Int.floor θ)
  rw [heq (1 / n), heq 0, etaJet_eq_iteratedDeriv F hF, etaJet_eq_iteratedDeriv F hF]
  have h := hlocal (1 / n) hε X hX η hη (Int.fract θ) hθ
  simpa only [mul_one_div] using h

/-- Angular family, given by `E z.2.1 z.2.2.1 * Real.exp (z.1 * A z.2)`. -/
def angularFamily (E : BaseProfile) (A : PrimitiveProfile) (z : FamilyPoint) : ℝ :=
  E z.2.1 z.2.2.1 * Real.exp (z.1 * A z.2)

/-- Axial family, given by `U z.2.1 z.2.2.1 + z.1 * B z.2`. -/
def axialFamily (U : BaseProfile) (B : PrimitiveProfile) (z : FamilyPoint) : ℝ :=
  U z.2.1 z.2.2.1 + z.1 * B z.2

/-- Uniform `O(1/n)` closeness in every fixed actual η derivative of E.
Taking `KX = [Xa,Xb]` with `0 < Xa` gives the manuscript's compact positive annulus. -/
theorem uniform_modulatedE_eta_jets
    (E : BaseProfile) (A : PrimitiveProfile)
    (hE : ContDiff ℝ ∞ (Function.uncurry E)) (hA : ContDiff ℝ ∞ A)
    (hperiodic : ∀ X η, Function.Periodic (fun θ => A (X, η, θ)) 1)
    (KX Kη : Set ℝ) (hKX : IsCompact KX) (hKη : IsCompact Kη) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℝ, 1 ≤ n → ∀ X ∈ KX, ∀ η ∈ Kη,
      |iteratedDeriv k (modulatedE n E A X) η - iteratedDeriv k (E X) η| ≤ C / n := by
  have hF : ContDiff ℝ ∞ (angularFamily E A) := by
    unfold angularFamily
    change ContDiff ℝ ∞ (fun z : FamilyPoint =>
      (Function.uncurry E) (z.2.1, z.2.2.1) * Real.exp (z.1 * A z.2))
    have hbase : ContDiff ℝ ∞ (fun z : FamilyPoint => (z.2.1, z.2.2.1)) :=
      contDiff_snd.fst.prodMk contDiff_snd.snd.fst
    exact (hE.comp hbase).mul ((contDiff_fst.mul (hA.comp contDiff_snd)).exp)
  have hP : ∀ ε X η, Function.Periodic (fun θ => angularFamily E A (ε, X, η, θ)) 1 := by
    intro ε X η θ
    simp only [angularFamily, hperiodic X η θ]
  obtain ⟨C, hC, hbound⟩ := uniform_periodic_family_eta_jets
    (angularFamily E A) hF hP KX Kη hKX hKη k
  refine ⟨C, hC, ?_⟩
  intro n hn X hX η hη
  unfold modulatedE
  simpa only [angularFamily, phasePoint, zero_mul, Real.exp_zero, mul_one,
    div_eq_mul_inv, one_mul, mul_comm (n⁻¹)] using hbound n hn X hX η hη (n * Real.log X)

/-- Uniform `O(1/n)` closeness in every fixed actual η derivative of U. -/
theorem uniform_modulatedU_eta_jets
    (U : BaseProfile) (B : PrimitiveProfile)
    (hU : ContDiff ℝ ∞ (Function.uncurry U)) (hB : ContDiff ℝ ∞ B)
    (hperiodic : ∀ X η, Function.Periodic (fun θ => B (X, η, θ)) 1)
    (KX Kη : Set ℝ) (hKX : IsCompact KX) (hKη : IsCompact Kη) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℝ, 1 ≤ n → ∀ X ∈ KX, ∀ η ∈ Kη,
      |iteratedDeriv k (modulatedU n U B X) η - iteratedDeriv k (U X) η| ≤ C / n := by
  have hF : ContDiff ℝ ∞ (axialFamily U B) := by
    unfold axialFamily
    change ContDiff ℝ ∞ (fun z : FamilyPoint =>
      (Function.uncurry U) (z.2.1, z.2.2.1) + z.1 * B z.2)
    have hbase : ContDiff ℝ ∞ (fun z : FamilyPoint => (z.2.1, z.2.2.1)) :=
      contDiff_snd.fst.prodMk contDiff_snd.snd.fst
    exact (hU.comp hbase).add (contDiff_fst.mul (hB.comp contDiff_snd))
  have hP : ∀ ε X η, Function.Periodic (fun θ => axialFamily U B (ε, X, η, θ)) 1 := by
    intro ε X η θ
    simp only [axialFamily, hperiodic X η θ]
  obtain ⟨C, hC, hbound⟩ := uniform_periodic_family_eta_jets
    (axialFamily U B) hF hP KX Kη hKX hKη k
  refine ⟨C, hC, ?_⟩
  intro n hn X hX η hη
  unfold modulatedU
  simpa only [axialFamily, phasePoint, zero_mul, add_zero,
    div_eq_mul_inv, one_mul, mul_comm (n⁻¹)] using hbound n hn X hX η hη (n * Real.log X)

end NavierStokes.RadialModulation

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ParametricModulation

open Set Filter MeasureTheory Function
open scoped Topology ContDiff

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- Primitive family, given by `RadialModulation.periodicPrimitive (fun θ => q (z.1, θ)) z.2`. -/
def primitiveFamily (q : P × ℝ → ℝ) (z : P × ℝ) : ℝ :=
  RadialModulation.periodicPrimitive (fun θ => q (z.1, θ)) z.2

/-- Normalized primitive family, given by `RadialModulation.zeroMeanPrimitive (fun θ => q (z.1,
θ)) z.2`. -/
def normalizedPrimitiveFamily (q : P × ℝ → ℝ) (z : P × ℝ) : ℝ :=
  RadialModulation.zeroMeanPrimitive (fun θ => q (z.1, θ)) z.2

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
/-- The variable-endpoint integral is an integral over the fixed unit interval. -/
theorem primitiveFamily_unit_interval (q : P × ℝ → ℝ) (z : P × ℝ) :
    primitiveFamily q z = z.2 * intervalIntegral (fun s => q (z.1, z.2 * s)) 0 1 volume := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (fun θ => q (z.1, θ)) z.2 (a := 0) (b := 1)
  simpa only [primitiveFamily, RadialModulation.periodicPrimitive, smul_eq_mul,
    mul_zero, mul_one] using h.symm

/-- Joint smoothness of the actual primitive; all domination comes from the
compact integration interval, through `SmoothParameterIntegral`. -/
theorem primitiveFamily_contDiffOn
    (q : P × ℝ → ℝ) (U : Set P) (hU : IsOpen U)
    (hq : ContDiffOn ℝ ∞ q (U ×ˢ (univ : Set ℝ))) :
    ContDiffOn ℝ ∞ (primitiveFamily q) (U ×ˢ (univ : Set ℝ)) := by
  let F : (P × ℝ) × ℝ → ℝ := fun z => q (z.1.1, z.1.2 * z.2)
  have hF : ContDiffOn ℝ ∞ F ((U ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set ℝ)) :=
    hq.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.mul contDiff_snd)).contDiffOn
      (fun z hz => ⟨hz.1.1, mem_univ _⟩)
  have hi := ParametricRephase.intervalIntegral_contDiffOn_of_joint F
    (U ×ˢ (univ : Set ℝ)) (hU.prod isOpen_univ) hF 0 1 (by norm_num)
  have heq : primitiveFamily q =
      (fun z => z.2 * intervalIntegral (fun s => F (z, s)) 0 1 volume) :=
    funext (primitiveFamily_unit_interval q)
  rw [heq]
  exact contDiff_snd.contDiffOn.mul hi

/-- Subtracting the actual parameter-dependent mean preserves joint smoothness. -/
theorem normalizedPrimitiveFamily_contDiffOn
    (q : P × ℝ → ℝ) (U : Set P) (hU : IsOpen U)
    (hq : ContDiffOn ℝ ∞ q (U ×ˢ (univ : Set ℝ))) :
    ContDiffOn ℝ ∞ (normalizedPrimitiveFamily q) (U ×ˢ (univ : Set ℝ)) := by
  have hp := primitiveFamily_contDiffOn q U hU hq
  have hm := ParametricRephase.intervalIntegral_contDiffOn_of_joint
    (primitiveFamily q) U hU hp 0 1 (by norm_num)
  exact hp.sub (hm.comp contDiff_fst.contDiffOn (fun _ hz => hz.1))

omit [FiniteDimensional ℝ P] in
theorem source_slice_contDiff
    (q : P × ℝ → ℝ) (U : Set P)
    (hq : ContDiffOn ℝ ∞ q (U ×ˢ (univ : Set ℝ))) (p : P) (hp : p ∈ U) :
    ContDiff ℝ ∞ (fun θ => q (p, θ)) := by
  apply hq.comp_contDiff (contDiff_const.prodMk contDiff_id)
  intro θ
  exact ⟨hp, mem_univ θ⟩

omit [FiniteDimensional ℝ P] in
theorem normalizedPrimitiveFamily_hasDerivAt
    (q : P × ℝ → ℝ) (U : Set P)
    (hq : ContDiffOn ℝ ∞ q (U ×ˢ (univ : Set ℝ))) (p : P) (hp : p ∈ U) (θ : ℝ) :
    HasDerivAt (fun s => normalizedPrimitiveFamily q (p, s)) (q (p, θ)) θ :=
  RadialModulation.zeroMeanPrimitive_hasDerivAt _
    (source_slice_contDiff q U hq p hp).continuous θ

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
theorem normalizedPrimitiveFamily_periodic
    (q : P × ℝ → ℝ) (p : P) (hq : Continuous (fun θ => q (p, θ)))
    (hper : Function.Periodic (fun θ => q (p, θ)) 1)
    (hmean : intervalIntegral (fun θ => q (p, θ)) 0 1 volume = 0) :
    Function.Periodic (fun θ => normalizedPrimitiveFamily q (p, θ)) 1 := by
  intro θ
  unfold normalizedPrimitiveFamily RadialModulation.zeroMeanPrimitive
  dsimp only
  rw [RadialModulation.periodicPrimitive_periodic _ hq hper hmean θ]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
theorem normalizedPrimitiveFamily_mean_zero
    (q : P × ℝ → ℝ) (p : P) (hq : Continuous (fun θ => q (p, θ))) :
    intervalIntegral (fun θ => normalizedPrimitiveFamily q (p, θ)) 0 1 volume = 0 :=
  RadialModulation.zeroMeanPrimitive_integral _ hq

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
/-- Exact vanishing, including the mean normalization, when the loop is nominal. -/
theorem normalizedPrimitiveFamily_zero
    (q : P × ℝ → ℝ) (p : P) (hq : ∀ θ, q (p, θ) = 0) (θ : ℝ) :
    normalizedPrimitiveFamily q (p, θ) = 0 := by
  unfold normalizedPrimitiveFamily RadialModulation.zeroMeanPrimitive
    RadialModulation.periodicPrimitive
  simp only [hq, intervalIntegral.integral_zero, sub_zero]

/-- A cutoff which equals one around K and vanishes locally outside U. -/
structure CompactCutoff (K U : Set P) where
  /-- Value of `CompactCutoff`, of type `P → ℝ`. -/
  value : P → ℝ
  smooth : ContDiff ℝ ∞ value
  /-- Neighborhood of `CompactCutoff`, of type `Set P`. -/
  neighborhood : Set P
  open_neighborhood : IsOpen neighborhood
  contains : K ⊆ neighborhood
  subset_domain : neighborhood ⊆ U
  one_on : ∀ p ∈ neighborhood, value p = 1
  zero_near : ∀ p, p ∉ U → value =ᶠ[𝓝 p] (fun _ => 0)

/-- A smooth plateau cutoff is constructed from a smooth function supported
exactly on U and its positive minimum over K. -/
theorem exists_compactCutoff (K U : Set P) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    Nonempty (CompactCutoff K U) := by
  obtain ⟨f, hsupp, hf, hrange⟩ := hU.exists_contDiff_support_eq
  have hnonneg : ∀ p, 0 ≤ f p := fun p => (hrange (mem_range_self p)).1
  have hpos : ∀ p ∈ K, 0 < f p := by
    intro p hp
    have hn : f p ≠ 0 := by simpa only [← hsupp, mem_support] using hKU hp
    exact lt_of_le_of_ne (hnonneg p) (Ne.symm hn)
  obtain ⟨δ, hδ, hδf⟩ := UniformCone.positive_uniform_margin hK hf.continuous.continuousOn hpos
  let O : Set P := {p | δ / 2 < f p}
  let χ : P → ℝ := fun p => Real.smoothTransition ((f p - δ / 4) / (δ / 4))
  have hd4 : 0 < δ / 4 := by positivity
  have hχ : ContDiff ℝ ∞ χ :=
    Real.smoothTransition.contDiff.comp ((hf.sub contDiff_const).div_const _)
  have hO : IsOpen O := isOpen_lt continuous_const hf.continuous
  have hKO : K ⊆ O := by
    intro p hp
    exact lt_of_lt_of_le (by linarith) (hδf p hp)
  have hOU : O ⊆ U := by
    intro p hp
    rw [← hsupp, mem_support]
    have hfp : 0 < f p := lt_trans (by positivity : 0 < δ / 2) hp
    exact ne_of_gt hfp
  have hχone : ∀ p ∈ O, χ p = 1 := by
    intro p hp
    apply Real.smoothTransition.one_of_one_le
    apply (le_div_iff₀ hd4).mpr
    dsimp [O] at hp
    linarith
  have hχzero : ∀ p, p ∉ U → χ =ᶠ[𝓝 p] (fun _ => 0) := by
    intro p hp
    have hfp : f p = 0 := by
      have hn : p ∉ support f := by simpa only [hsupp] using hp
      simpa only [mem_support, not_not] using hn
    have hnear : ∀ᶠ y in 𝓝 p, f y < δ / 4 :=
      hf.continuous.continuousAt.eventually (gt_mem_nhds (by simpa only [hfp] using hd4))
    filter_upwards [hnear] with y hy
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hd4.le
  exact ⟨⟨χ, hχ, O, hO, hKO, hOU, hχone, hχzero⟩⟩

omit [FiniteDimensional ℝ P] in
/-- Multiplication by the constructed cutoff extends a locally smooth periodic
profile to a globally smooth function, unchanged around K. -/
theorem CompactCutoff.mul_contDiff
    {K U : Set P} (χ : CompactCutoff K U) (hU : IsOpen U)
    (f : P × ℝ → ℝ) (hf : ContDiffOn ℝ ∞ f (U ×ˢ (univ : Set ℝ))) :
    ContDiff ℝ ∞ (fun z : P × ℝ => χ.value z.1 * f z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z.1 ∈ U
  · exact (χ.smooth.contDiffAt.comp z contDiffAt_fst).mul
      (hf.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hz, mem_univ _⟩))
  · have hzero : (fun w : P × ℝ => χ.value w.1 * f w) =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [(χ.zero_near z.1 hz).comp_tendsto continuous_fst.continuousAt] with w hw
      change χ.value w.1 = 0 at hw
      rw [hw, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hzero

/-- Centered source, given by `c z.1 * (f z - m z.1)`. -/
def centeredSource (f : P × ℝ → ℝ) (m c : P → ℝ) (z : P × ℝ) : ℝ :=
  c z.1 * (f z - m z.1)

/-- Extended primitive, given by `χ.value z.1 * normalizedPrimitiveFamily (centeredSource f m c)
z`. -/
def extendedPrimitive {K U : Set P} (χ : CompactCutoff K U)
    (f : P × ℝ → ℝ) (m c : P → ℝ) (z : P × ℝ) : ℝ :=
  χ.value z.1 * normalizedPrimitiveFamily (centeredSource f m c) z

omit [FiniteDimensional ℝ P] in
theorem centeredSource_contDiffOn
    (f : P × ℝ → ℝ) (m c : P → ℝ) (U : Set P)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ (univ : Set ℝ)))
    (hm : ContDiff ℝ ∞ m) (hc : ContDiff ℝ ∞ c) :
    ContDiffOn ℝ ∞ (centeredSource f m c) (U ×ˢ (univ : Set ℝ)) :=
  (hc.comp contDiff_fst).contDiffOn.mul (hf.sub (hm.comp contDiff_fst).contDiffOn)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
theorem centeredSource_periodic
    (f : P × ℝ → ℝ) (m c : P → ℝ) (p : P)
    (hf : Function.Periodic (fun θ => f (p, θ)) 1) :
    Function.Periodic (fun θ => centeredSource f m c (p, θ)) 1 := by
  intro θ
  change c p * (f (p, θ + 1) - m p) = c p * (f (p, θ) - m p)
  have h : f (p, θ + 1) = f (p, θ) := hf θ
  rw [h]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
theorem centeredSource_mean_zero
    (f : P × ℝ → ℝ) (m c : P → ℝ) (p : P)
    (hf : Continuous (fun θ => f (p, θ)))
    (hm : intervalIntegral (fun θ => f (p, θ)) 0 1 volume = m p) :
    intervalIntegral (fun θ => centeredSource f m c (p, θ)) 0 1 volume = 0 := by
  change intervalIntegral (fun θ => c p * (f (p, θ) - m p)) 0 1 volume = 0
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (hf.intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable 0 1)]
  simp [hm]

theorem extendedPrimitive_contDiff
    {K U : Set P} (χ : CompactCutoff K U) (hU : IsOpen U)
    (f : P × ℝ → ℝ) (m c : P → ℝ)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ (univ : Set ℝ)))
    (hm : ContDiff ℝ ∞ m) (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (extendedPrimitive χ f m c) :=
  χ.mul_contDiff hU _ (normalizedPrimitiveFamily_contDiffOn _ U hU
    (centeredSource_contDiffOn f m c U hf hm hc))

omit [FiniteDimensional ℝ P] in
theorem extendedPrimitive_periodic
    {K U : Set P} (χ : CompactCutoff K U)
    (f : P × ℝ → ℝ) (m c : P → ℝ)
    (hf : ∀ p ∈ U, Continuous (fun θ => f (p, θ)))
    (hper : ∀ p ∈ U, Function.Periodic (fun θ => f (p, θ)) 1)
    (hm : ∀ p ∈ U, intervalIntegral (fun θ => f (p, θ)) 0 1 volume = m p)
    (p : P) : Function.Periodic (fun θ => extendedPrimitive χ f m c (p, θ)) 1 := by
  by_cases hp : p ∈ U
  · have hq : Continuous (fun θ => centeredSource f m c (p, θ)) := by
      change Continuous (fun θ => c p * (f (p, θ) - m p))
      exact continuous_const.mul ((hf p hp).sub continuous_const)
    have hP := normalizedPrimitiveFamily_periodic _ p hq
      (centeredSource_periodic f m c p (hper p hp))
      (centeredSource_mean_zero f m c p (hf p hp) (hm p hp))
    intro θ
    change χ.value p * normalizedPrimitiveFamily (centeredSource f m c) (p, θ + 1) =
      χ.value p * normalizedPrimitiveFamily (centeredSource f m c) (p, θ)
    have h : normalizedPrimitiveFamily (centeredSource f m c) (p, θ + 1) =
        normalizedPrimitiveFamily (centeredSource f m c) (p, θ) := hP θ
    rw [h]
  · have hz : χ.value p = 0 := (χ.zero_near p hp).eq_of_nhds
    intro θ
    simp [extendedPrimitive, hz]

omit [FiniteDimensional ℝ P] in
theorem extendedPrimitive_mean_zero
    {K U : Set P} (χ : CompactCutoff K U)
    (f : P × ℝ → ℝ) (m c : P → ℝ)
    (hf : ∀ p ∈ U, Continuous (fun θ => f (p, θ))) (p : P) :
    intervalIntegral (fun θ => extendedPrimitive χ f m c (p, θ)) 0 1 volume = 0 := by
  by_cases hp : p ∈ U
  · have hq : Continuous (fun θ => centeredSource f m c (p, θ)) := by
      change Continuous (fun θ => c p * (f (p, θ) - m p))
      exact continuous_const.mul ((hf p hp).sub continuous_const)
    change intervalIntegral
      (fun θ => χ.value p * normalizedPrimitiveFamily (centeredSource f m c) (p, θ))
      0 1 volume = 0
    rw [intervalIntegral.integral_const_mul, normalizedPrimitiveFamily_mean_zero _ p hq,
      mul_zero]
  · have hz : χ.value p = 0 := (χ.zero_near p hp).eq_of_nhds
    simp [extendedPrimitive, hz]

omit [FiniteDimensional ℝ P] in
theorem extendedPrimitive_hasDerivAt
    {K U : Set P} (χ : CompactCutoff K U)
    (f : P × ℝ → ℝ) (m c : P → ℝ)
    (hf : ∀ p ∈ U, Continuous (fun θ => f (p, θ)))
    (p : P) (hp : p ∈ K) (θ : ℝ) :
    HasDerivAt (fun s => extendedPrimitive χ f m c (p, s))
      (c p * (f (p, θ) - m p)) θ := by
  have hq : Continuous (fun θ => centeredSource f m c (p, θ)) := by
    change Continuous (fun θ => c p * (f (p, θ) - m p))
    exact continuous_const.mul ((hf p (χ.subset_domain (χ.contains hp))).sub continuous_const)
  have hd := (RadialModulation.zeroMeanPrimitive_hasDerivAt
    (fun θ => centeredSource f m c (p, θ)) hq θ).const_mul (χ.value p)
  simpa only [extendedPrimitive, normalizedPrimitiveFamily, centeredSource,
    χ.one_on p (χ.contains hp), one_mul] using hd

omit [FiniteDimensional ℝ P] in
theorem extendedPrimitive_zero
    {K U : Set P} (χ : CompactCutoff K U)
    (f : P × ℝ → ℝ) (m c : P → ℝ) (p : P)
    (hf : ∀ θ, f (p, θ) = m p) (θ : ℝ) :
    extendedPrimitive χ f m c (p, θ) = 0 := by
  have hq : ∀ θ, centeredSource f m c (p, θ) = 0 := by
    intro s
    simp only [centeredSource, hf s, sub_self, mul_zero]
  unfold extendedPrimitive
  rw [normalizedPrimitiveFamily_zero _ p hq θ, mul_zero]

/-- The only choice data are the already constructed true-cone loop parameters
and an actual smooth compact-set cutoff. Primitives below are defined by integrals. -/
structure TrueConeRealization (a m p₁ p₂ : P → ℝ) (K B : Set P) where
  /-- Choices of `TrueConeRealization`, of type `TrueConeLoop.FamilyChoices a m p₁ p₂ K B`. -/
  choices : TrueConeLoop.FamilyChoices a m p₁ p₂ K B
  /-- Cutoff of `TrueConeRealization`, of type `CompactCutoff K {p | 0 < a p}`. -/
  cutoff : CompactCutoff K {p | 0 < a p}

theorem exists_trueConeRealization
    (a m p₁ p₂ : P → ℝ) (K B : Set P)
    (hK : IsCompact K) (hB : IsCompact B)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m)
    (hp₁ : ContDiff ℝ ∞ p₁) (hp₂ : ContDiff ℝ ∞ p₂)
    (haK : ∀ p ∈ K, 0 < a p) (hPK : ∀ p ∈ K, 2 < p₁ p + p₂ p * m p)
    (htrueB : ∀ p ∈ B, 2 < TrueConeLoop.nominalSpeed (a p) (m p)) :
    Nonempty (TrueConeRealization a m p₁ p₂ K B) := by
  obtain ⟨c⟩ := TrueConeLoop.exists_family_choices a m p₁ p₂ hK hB
    ha.continuous hm.continuous hp₁.continuous hp₂.continuous haK hPK htrueB
  obtain ⟨χ⟩ := exists_compactCutoff K {p | 0 < a p} hK
    (isOpen_lt continuous_const ha.continuous) haK
  exact ⟨⟨c, χ⟩⟩

namespace TrueConeRealization

variable {a m p₁ p₂ : P → ℝ} {K B : Set P}

/-- Angular loop, given by `TrueConeLoop.familyA a m p₂ r.choices.d r.choices.delta (ne_of_gt
r.choices.d_pos) r.choices.delta_pos`. -/
def angularLoop (r : TrueConeRealization a m p₁ p₂ K B) : P × ℝ → ℝ :=
  TrueConeLoop.familyA a m p₂ r.choices.d r.choices.delta
    (ne_of_gt r.choices.d_pos) r.choices.delta_pos

/-- This is the signed loop coordinate `-b_L`, in the convention of TrueConeLoop. -/
def signedAxialLoop (r : TrueConeRealization a m p₁ p₂ K B) : P × ℝ → ℝ :=
  TrueConeLoop.familyC a m p₂ r.choices.d r.choices.delta
    (ne_of_gt r.choices.d_pos) r.choices.delta_pos

/-- Angular primitive, given by `extendedPrimitive r.cutoff r.angularLoop a (fun _ => -1 / 2)`. -/
def angularPrimitive (r : TrueConeRealization a m p₁ p₂ K B) : P × ℝ → ℝ :=
  extendedPrimitive r.cutoff r.angularLoop a (fun _ => -1 / 2)

/-- Axial primitive, given by `extendedPrimitive r.cutoff r.signedAxialLoop (fun p => a p * m p)
(fun p => -E p / 2)`. -/
def axialPrimitive (r : TrueConeRealization a m p₁ p₂ K B) (E : P → ℝ) : P × ℝ → ℝ :=
  extendedPrimitive r.cutoff r.signedAxialLoop (fun p => a p * m p) (fun p => -E p / 2)

theorem loop_smooth (r : TrueConeRealization a m p₁ p₂ K B)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂) :
    ContDiffOn ℝ ∞ r.angularLoop ({p | 0 < a p} ×ˢ (univ : Set ℝ)) ∧
      ContDiffOn ℝ ∞ r.signedAxialLoop ({p | 0 < a p} ×ˢ (univ : Set ℝ)) :=
  TrueConeLoop.family_joint_contDiffOn a m p₂ r.choices.d r.choices.delta ha hm hp₂
    (ne_of_gt r.choices.d_pos) r.choices.delta_pos

omit [FiniteDimensional ℝ P] in
theorem loop_periods_means (r : TrueConeRealization a m p₁ p₂ K B)
    (p : P) (hp : 0 < a p) :
    Function.Periodic (fun θ => r.angularLoop (p, θ)) 1 ∧
      Function.Periodic (fun θ => r.signedAxialLoop (p, θ)) 1 ∧
      intervalIntegral (fun θ => r.angularLoop (p, θ)) 0 1 volume = a p ∧
      intervalIntegral (fun θ => r.signedAxialLoop (p, θ)) 0 1 volume = a p * m p := by
  have hA := TrueConeLoop.familyA_eq_constructed a m p₂ r.choices.d r.choices.delta
    (ne_of_gt r.choices.d_pos) r.choices.delta_pos p hp
  have hC := TrueConeLoop.familyC_eq_constructed a m p₂ r.choices.d r.choices.delta
    (ne_of_gt r.choices.d_pos) r.choices.delta_pos p hp
  have hper := TrueConeLoop.constructed_periodic (a p) (m p) r.choices.d (p₂ p)
    r.choices.delta hp (ne_of_gt r.choices.d_pos) r.choices.delta_pos
  have hmean := TrueConeLoop.constructed_means (a p) (m p) r.choices.d (p₂ p)
    r.choices.delta hp (ne_of_gt r.choices.d_pos) r.choices.delta_pos
  change Function.Periodic _ 1 ∧ Function.Periodic _ 1 ∧ _ = _ ∧ _ = _
  simpa only [angularLoop, signedAxialLoop, hA, hC] using
    And.intro hper.1 (And.intro hper.2 hmean)

theorem primitives_smooth (r : TrueConeRealization a m p₁ p₂ K B)
    (E : P → ℝ) (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m)
    (hp₂ : ContDiff ℝ ∞ p₂) (hE : ContDiff ℝ ∞ E) :
    ContDiff ℝ ∞ r.angularPrimitive ∧ ContDiff ℝ ∞ (r.axialPrimitive E) := by
  have hs := r.loop_smooth ha hm hp₂
  have hU : IsOpen {p | 0 < a p} := isOpen_lt continuous_const ha.continuous
  exact ⟨extendedPrimitive_contDiff r.cutoff hU _ _ _ hs.1 ha contDiff_const,
    extendedPrimitive_contDiff r.cutoff hU _ _ _ hs.2 (ha.mul hm) (hE.neg.div_const 2)⟩

theorem primitives_periodic (r : TrueConeRealization a m p₁ p₂ K B)
    (E : P → ℝ) (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m)
    (hp₂ : ContDiff ℝ ∞ p₂) (p : P) :
    Function.Periodic (fun θ => r.angularPrimitive (p, θ)) 1 ∧
      Function.Periodic (fun θ => r.axialPrimitive E (p, θ)) 1 := by
  have hs := r.loop_smooth ha hm hp₂
  have hca := fun p hp => (source_slice_contDiff _ _ hs.1 p hp).continuous
  have hcb := fun p hp => (source_slice_contDiff _ _ hs.2 p hp).continuous
  exact ⟨extendedPrimitive_periodic r.cutoff _ _ _ hca
      (fun p hp => (r.loop_periods_means p hp).1)
      (fun p hp => (r.loop_periods_means p hp).2.2.1) p,
    extendedPrimitive_periodic r.cutoff _ _ _ hcb
      (fun p hp => (r.loop_periods_means p hp).2.1)
      (fun p hp => (r.loop_periods_means p hp).2.2.2) p⟩

theorem primitives_mean_zero (r : TrueConeRealization a m p₁ p₂ K B)
    (E : P → ℝ) (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m)
    (hp₂ : ContDiff ℝ ∞ p₂) (p : P) :
    intervalIntegral (fun θ => r.angularPrimitive (p, θ)) 0 1 volume = 0 ∧
      intervalIntegral (fun θ => r.axialPrimitive E (p, θ)) 0 1 volume = 0 := by
  have hs := r.loop_smooth ha hm hp₂
  exact ⟨extendedPrimitive_mean_zero r.cutoff _ _ _
      (fun p hp => (source_slice_contDiff _ _ hs.1 p hp).continuous) p,
    extendedPrimitive_mean_zero r.cutoff _ _ _
      (fun p hp => (source_slice_contDiff _ _ hs.2 p hp).continuous) p⟩

theorem primitive_derivatives (r : TrueConeRealization a m p₁ p₂ K B)
    (E : P → ℝ) (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m)
    (hp₂ : ContDiff ℝ ∞ p₂) (p : P) (hp : p ∈ K) (θ : ℝ) :
    HasDerivAt (fun s => r.angularPrimitive (p, s))
        (-(r.angularLoop (p, θ) - a p) / 2) θ ∧
      HasDerivAt (fun s => r.axialPrimitive E (p, s))
        (E p * (-r.signedAxialLoop (p, θ) + a p * m p) / 2) θ := by
  have hs := r.loop_smooth ha hm hp₂
  have hca := fun p hp => (source_slice_contDiff _ _ hs.1 p hp).continuous
  have hcb := fun p hp => (source_slice_contDiff _ _ hs.2 p hp).continuous
  constructor
  · apply (extendedPrimitive_hasDerivAt r.cutoff _ a (fun _ => -1 / 2) hca p hp θ).congr_deriv
    ring
  · apply (extendedPrimitive_hasDerivAt r.cutoff _ (fun p => a p * m p)
      (fun p => -E p / 2) hcb p hp θ).congr_deriv
    ring

omit [FiniteDimensional ℝ P] in
theorem boundary_vanishing (r : TrueConeRealization a m p₁ p₂ K B)
    (E : P → ℝ) (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hBK : B ⊆ K) :
    ∃ N : Set P, IsOpen N ∧ B ⊆ N ∧ ∀ p ∈ N, ∀ θ,
      r.angularPrimitive (p, θ) = 0 ∧ r.axialPrimitive E (p, θ) = 0 := by
  obtain ⟨N, hN, hBN, hNU, hn⟩ := TrueConeLoop.family_nominal_neighborhood a m p₁ p₂
    r.choices ha.continuous hm.continuous hBK
  refine ⟨N, hN, hBN, ?_⟩
  intro p hp θ
  exact ⟨extendedPrimitive_zero r.cutoff _ _ _ p (fun s => (hn p hp s).1) θ,
    extendedPrimitive_zero r.cutoff _ _ _ p (fun s => (hn p hp s).2) θ⟩

omit [FiniteDimensional ℝ P] in
theorem loop_trueCone (r : TrueConeRealization a m p₁ p₂ K B)
    (hrelaxed : ∀ p ∈ K, TrueConeLoop.nominalSpeed (a p) (m p) <
      ConeAlgebra.coneBound (p₁ p + p₂ p * m p) (p₂ p - p₁ p * m p)) :
    ∀ p ∈ K, ∀ θ, TrueConeLoop.InTrueCone (p₁ p) (p₂ p)
      (r.angularLoop (p, θ)) (r.signedAxialLoop (p, θ)) := by
  intro p hp θ
  exact (TrueConeLoop.family_pointwise_properties a m p₁ p₂ r.choices hrelaxed p hp).2.2.2.2 θ

end TrueConeRealization

section RadialProfiles

/-- Radial parameter: an abbreviation for `ℝ × ℝ`. -/
abbrev RadialParameter := ℝ × ℝ

/-- Reassociation between slow-parameter/angle coordinates and the radial
modulation module's `(X,η,θ)` coordinates. -/
def asRadialPrimitive (Q : RadialParameter × ℝ → ℝ) : RadialModulation.PrimitiveProfile :=
  fun z => Q ((z.1, z.2.1), z.2.2)

theorem asRadialPrimitive_contDiff
    (Q : RadialParameter × ℝ → ℝ) (hQ : ContDiff ℝ ∞ Q) :
    ContDiff ℝ ∞ (asRadialPrimitive Q) :=
  hQ.comp ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd)

variable {a m p₁ p₂ : RadialParameter → ℝ} {K B : Set RadialParameter}

/-- Realized E, given by `RadialModulation.modulatedE n (fun X η => E (X, η)) (asRadialPrimitive
r.angularPrimitive) X η`. -/
def realizedE (r : TrueConeRealization a m p₁ p₂ K B) (E : RadialParameter → ℝ)
    (n X η : ℝ) : ℝ :=
  RadialModulation.modulatedE n (fun X η => E (X, η))
    (asRadialPrimitive r.angularPrimitive) X η

/-- Realized U, given by `RadialModulation.modulatedU n (fun X η => U (X, η)) (asRadialPrimitive
(r.axialPrimitive E)) X η`. -/
def realizedU (r : TrueConeRealization a m p₁ p₂ K B) (E U : RadialParameter → ℝ)
    (n X η : ℝ) : ℝ :=
  RadialModulation.modulatedU n (fun X η => U (X, η))
    (asRadialPrimitive (r.axialPrimitive E)) X η

/-- Smoothness of the realized profiles follows from the constructed integral
primitives, without any primitive-smoothness assumption. -/
theorem realized_profiles_contDiffAt
    (r : TrueConeRealization a m p₁ p₂ K B) (E U : RadialParameter → ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U) (n X η : ℝ) (hX : X ≠ 0) :
    ContDiffAt ℝ ∞ (Function.uncurry (realizedE r E n)) (X, η) ∧
      ContDiffAt ℝ ∞ (Function.uncurry (realizedU r E U n)) (X, η) := by
  have hprim := r.primitives_smooth E ha hm hp₂ hE
  exact ⟨RadialModulation.modulatedE_contDiffAt _ _ n X η hE
      (asRadialPrimitive_contDiff _ hprim.1) hX,
    RadialModulation.modulatedU_contDiffAt _ _ n X η hU
      (asRadialPrimitive_contDiff _ hprim.2) hX⟩

/-- Every fixed actual η jet is `O(1/n)`, now for the primitives constructed
from the actual TrueConeLoop family, uniformly on arbitrary compact sets. -/
theorem realized_profiles_uniform_eta_jets
    (r : TrueConeRealization a m p₁ p₂ K B) (E U : RadialParameter → ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (KX Kη : Set ℝ) (hKX : IsCompact KX) (hKη : IsCompact Kη) (k : ℕ) :
    ∃ CE CU : ℝ, 0 ≤ CE ∧ 0 ≤ CU ∧ ∀ n : ℝ, 1 ≤ n → ∀ X ∈ KX, ∀ η ∈ Kη,
      |iteratedDeriv k (realizedE r E n X) η - iteratedDeriv k (fun e => E (X, e)) η| ≤ CE / n ∧
      |iteratedDeriv k (realizedU r E U n X) η - iteratedDeriv k (fun e =>
          U (X, e)) η| ≤ CU / n := by
  have hprim := r.primitives_smooth E ha hm hp₂ hE
  have hperiodA : ∀ X η, Function.Periodic
      (fun θ => asRadialPrimitive r.angularPrimitive (X, η, θ)) 1 :=
    fun X η => (r.primitives_periodic E ha hm hp₂ (X, η)).1
  have hperiodB : ∀ X η, Function.Periodic
      (fun θ => asRadialPrimitive (r.axialPrimitive E) (X, η, θ)) 1 :=
    fun X η => (r.primitives_periodic E ha hm hp₂ (X, η)).2
  obtain ⟨CE, hCE, hbE⟩ := RadialModulation.uniform_modulatedE_eta_jets
    (fun X η => E (X, η)) (asRadialPrimitive r.angularPrimitive)
    hE (asRadialPrimitive_contDiff _ hprim.1) hperiodA KX Kη hKX hKη k
  obtain ⟨CU, hCU, hbU⟩ := RadialModulation.uniform_modulatedU_eta_jets
    (fun X η => U (X, η)) (asRadialPrimitive (r.axialPrimitive E))
    hU (asRadialPrimitive_contDiff _ hprim.2) hperiodB KX Kη hKX hKη k
  exact ⟨CE, CU, hCE, hCU, fun n hn X hX η hη => ⟨hbE n hn X hX η hη, hbU n hn X hX η hη⟩⟩

/-- The constructed profiles agree exactly with the nominal profiles on one
open neighborhood of the prescribed boundary set, for every frequency. -/
theorem realized_profiles_boundary_match
    (r : TrueConeRealization a m p₁ p₂ K B) (E U : RadialParameter → ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hBK : B ⊆ K) :
    ∃ N : Set RadialParameter, IsOpen N ∧ B ⊆ N ∧ ∀ n X η : ℝ, (X, η) ∈ N →
      realizedE r E n X η = E (X, η) ∧ realizedU r E U n X η = U (X, η) := by
  obtain ⟨N, hN, hBN, hz⟩ := r.boundary_vanishing E ha hm hBK
  refine ⟨N, hN, hBN, ?_⟩
  intro n X η hp
  have h := hz (X, η) hp (n * Real.log X)
  simp only [realizedE, realizedU, RadialModulation.modulatedE, RadialModulation.modulatedU,
    asRadialPrimitive, RadialModulation.phasePoint, h.1, h.2, zero_div,
    Real.exp_zero, mul_one, add_zero, and_self]

theorem theta_derivative_asRadialPrimitive
    (Q : RadialParameter × ℝ → ℝ) (hQ : ContDiff ℝ ∞ Q) (X η θ : ℝ) :
    HasDerivAt (fun s => Q ((X, η), s))
      (RadialModulation.partialTheta (asRadialPrimitive Q) (X, η, θ)) θ := by
  have hg := (hasDerivAt_const θ X).prodMk ((hasDerivAt_const θ η).prodMk (hasDerivAt_id θ))
  exact (((asRadialPrimitive_contDiff Q hQ).differentiable (by
      simp) (X, η, θ)).hasFDerivAt).comp_hasDerivAt θ hg

/-- The prescribed loop derivatives are established for the constructed
primitives, including the sign change from `C = -b_L`. -/
theorem realized_primitive_theta
    (r : TrueConeRealization a m p₁ p₂ K B) (E : RadialParameter → ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hE : ContDiff ℝ ∞ E) (X η θ : ℝ) (hp : (X, η) ∈ K) :
    RadialModulation.partialTheta (asRadialPrimitive r.angularPrimitive) (X, η, θ) =
        -(r.angularLoop ((X, η), θ) - a (X, η)) / 2 ∧
      RadialModulation.partialTheta (asRadialPrimitive (r.axialPrimitive E)) (X, η, θ) =
        E (X, η) * (-r.signedAxialLoop ((X, η), θ) + a (X, η) * m (X, η)) / 2 := by
  have hprim := r.primitives_smooth E ha hm hp₂ hE
  have hd := r.primitive_derivatives E ha hm hp₂ (X, η) hp θ
  exact ⟨(theta_derivative_asRadialPrimitive _ hprim.1 X η θ).unique hd.1,
    (theta_derivative_asRadialPrimitive _ hprim.2 X η θ).unique hd.2⟩

/-- Exact shear identities after composition of the constructed true-cone
loop, its actual integral primitives, and radial modulation. -/
theorem realized_shears_exact
    (r : TrueConeRealization a m p₁ p₂ K B) (E U : RadialParameter → ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (n X η : ℝ) (hn : n ≠ 0) (hX : X ≠ 0) (hE0 : E (X, η) ≠ 0) (hp : (X, η) ∈ K)
    (haNom : a (X, η) = 1 - 2 * X * deriv (fun x => E (x, η)) X / E (X, η))
    (hbNom : -a (X, η) * m (X, η) = 2 * X * deriv (fun x => U (x, η)) X / E (X, η)) :
    (1 - 2 * X * deriv (fun x => realizedE r E n x η) X / realizedE r E n X η =
      r.angularLoop ((X, η), n * Real.log X) -
        2 * X * RadialModulation.partialX (asRadialPrimitive r.angularPrimitive)
          (X, η, n * Real.log X) / n) ∧
    (2 * X * deriv (fun x => realizedU r E U n x η) X / realizedE r E n X η =
      (-r.signedAxialLoop ((X, η), n * Real.log X) +
        2 * X * RadialModulation.partialX (asRadialPrimitive (r.axialPrimitive E))
          (X, η, n * Real.log X) / (n * E (X, η))) /
            Real.exp (r.angularPrimitive ((X, η), n * Real.log X) / n)) := by
  have hprim := r.primitives_smooth E ha hm hp₂ hE
  have hθ := realized_primitive_theta r E ha hm hp₂ hE X η (n * Real.log X) hp
  have hEr : DifferentiableAt ℝ (fun x => E (x, η)) X :=
    (hE.differentiable (by simp) (X, η)).comp X
      (differentiableAt_id.prodMk (differentiableAt_const η))
  have hUr : DifferentiableAt ℝ (fun x => U (x, η)) X :=
    (hU.differentiable (by simp) (X, η)).comp X
      (differentiableAt_id.prodMk (differentiableAt_const η))
  constructor
  · apply RadialModulation.angular_shear_exact _ _ n X η _ hn hX hE0 hEr
      ((asRadialPrimitive_contDiff _ hprim.1).differentiable (by simp) _)
    simpa only [RadialModulation.phasePoint, haNom] using hθ.1
  · apply RadialModulation.axial_shear_exact _ _ _ _ n X η _ hn hX hE0 hUr
      ((asRadialPrimitive_contDiff _ hprim.2).differentiable (by simp) _)
    change RadialModulation.partialTheta (asRadialPrimitive (r.axialPrimitive E))
      (X, η, n * Real.log X) = _
    rw [hθ.2, ← hbNom]
    ring

/-- End-to-end existence from nominal scalar data: construct the actual
TrueConeLoop family, its normalized integral primitives, and modulated profiles.
All smoothness and finite-jet conclusions are proved for these constructions. -/
theorem exists_modulated_trueCone_profiles
    (a m p₁ p₂ E U : RadialParameter → ℝ) (KX Kη : Set ℝ) (B : Set RadialParameter)
    (hKX : IsCompact KX) (hKη : IsCompact Kη) (hB : IsCompact B) (hBK : B ⊆ KX ×ˢ Kη)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m)
    (hp₁ : ContDiff ℝ ∞ p₁) (hp₂ : ContDiff ℝ ∞ p₂)
    (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (haK : ∀ p ∈ KX ×ˢ Kη, 0 < a p)
    (hPK : ∀ p ∈ KX ×ˢ Kη, 2 < p₁ p + p₂ p * m p)
    (hrelaxed : ∀ p ∈ KX ×ˢ Kη, TrueConeLoop.nominalSpeed (a p) (m p) <
      ConeAlgebra.coneBound (p₁ p + p₂ p * m p) (p₂ p - p₁ p * m p))
    (htrueB : ∀ p ∈ B, 2 < TrueConeLoop.nominalSpeed (a p) (m p)) :
    ∃ r : TrueConeRealization a m p₁ p₂ (KX ×ˢ Kη) B,
      (∀ p ∈ KX ×ˢ Kη, ∀ θ, TrueConeLoop.InTrueCone (p₁ p) (p₂ p)
        (r.angularLoop (p, θ)) (r.signedAxialLoop (p, θ))) ∧
      (∀ n X η : ℝ, X ≠ 0 →
        ContDiffAt ℝ ∞ (Function.uncurry (realizedE r E n)) (X, η) ∧
        ContDiffAt ℝ ∞ (Function.uncurry (realizedU r E U n)) (X, η)) ∧
      (∀ k : ℕ, ∃ CE CU : ℝ, 0 ≤ CE ∧ 0 ≤ CU ∧
        ∀ n : ℝ, 1 ≤ n → ∀ X ∈ KX, ∀ η ∈ Kη,
          |iteratedDeriv k (realizedE r E n X) η - iteratedDeriv k (fun e => E (X, e)) η| ≤ CE / n ∧
          |iteratedDeriv k (realizedU r E U n X) η - iteratedDeriv k (fun e =>
              U (X, e)) η| ≤ CU / n) ∧
      (∃ N : Set RadialParameter, IsOpen N ∧ B ⊆ N ∧ ∀ n X η : ℝ, (X, η) ∈ N →
        realizedE r E n X η = E (X, η) ∧ realizedU r E U n X η = U (X, η)) := by
  obtain ⟨r⟩ := exists_trueConeRealization a m p₁ p₂ (KX ×ˢ Kη) B
    (hKX.prod hKη) hB ha hm hp₁ hp₂ haK hPK htrueB
  exact ⟨r, r.loop_trueCone hrelaxed,
    realized_profiles_contDiffAt r E U ha hm hp₂ hE hU,
    realized_profiles_uniform_eta_jets r E U ha hm hp₂ hE hU KX Kη hKX hKη,
    realized_profiles_boundary_match r E U ha hm hBK⟩

end RadialProfiles

end NavierStokes.ParametricModulation
