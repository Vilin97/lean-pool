/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothLoop
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Moments.MGFAnalytic

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
