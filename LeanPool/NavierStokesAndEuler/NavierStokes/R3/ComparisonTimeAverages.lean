/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonSetup
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonFiniteEnergy
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Time averages of finite-energy fields

These averages use the ordinary Bochner integral on a finite closed time
interval. Their spatial integrability follows from joint continuity and the
uniform spatial integral bounds; no time derivative or global spatial
derivative bound is used.
-/

@[expose] public section



noncomputable section

open Set MeasureTheory
open scoped ENNReal InnerProductSpace

namespace NavierStokesR3.Comparison

open ProblemStatement

/-- The time average against a scalar weight on the comparison interval. -/
def timeAverage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ) (a : ℝ → ℝ) (f : SpaceTime → E) (x : Space) : E :=
  ∫ t in Icc 0 T, a t • f (t, x)

/-- Joint continuity supplies measurability for the product of restricted
time measure and ordinary spatial volume. -/
theorem aestronglyMeasurable_slab {E : Type*} [NormedAddCommGroup E]
    {T : ℝ} {f : SpaceTime → E} (hf : ContinuousOn f (slab 0 T)) :
    AEStronglyMeasurable f
      (((volume : Measure ℝ).restrict (Icc 0 T)).prod (volume : Measure Space)) := by
  rw [Measure.restrict_prod_eq_prod_univ]
  exact hf.aestronglyMeasurable (measurableSet_Icc.prod MeasurableSet.univ)

/-- An integrable bound on the spatial norm integrals proves integrability on
the whole slab. -/
theorem integrable_slab_of_integral_norm_le {E : Type*} [NormedAddCommGroup E]
    {T : ℝ} {f : SpaceTime → E} {B : ℝ → ℝ}
    (hf : ContinuousOn f (slab 0 T))
    (hslice : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => f (t, x)))
    (hB : IntegrableOn B (Icc 0 T))
    (hbound : ∀ t ∈ Icc 0 T, (∫ x : Space, ‖f (t, x)‖) ≤ B t) :
    Integrable f
      (((volume : Measure ℝ).restrict (Icc 0 T)).prod (volume : Measure Space)) := by
  have hmeas := aestronglyMeasurable_slab hf
  apply (integrable_prod_iff hmeas).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hslice t ht
  · apply hB.mono' hmeas.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [Real.norm_of_nonneg (integral_nonneg (fun x : Space => norm_nonneg (f (t, x))))]
      using hbound t ht

/-- Weighting by a continuous scalar preserves slab continuity. -/
theorem continuousOn_time_weight {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} {a : ℝ → ℝ} {f : SpaceTime → E}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T)) :
    ContinuousOn (fun z : SpaceTime => a z.1 • f z) (slab 0 T) :=
  (ha.comp continuous_fst.continuousOn (fun _ hz => hz.1)).smul hf

/-- Each time slice at a fixed spatial point is integrable, including at the
endpoints of the closed time interval. -/
theorem timeAverage_timeSlice_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T : ℝ} {a : ℝ → ℝ} {f : SpaceTime → E}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T)) (x : Space) :
    IntegrableOn (fun t => a t • f (t, x)) (Icc 0 T) :=
  (ha.smul (hf.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun _ ht => ⟨ht, mem_univ x⟩))).integrableOn_Icc

/-- Bounded linear maps commute with these time averages pointwise. -/
theorem timeAverage_continuousLinearMap {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {T : ℝ} {a : ℝ → ℝ} {f : SpaceTime → E}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T))
    (L : E →L[ℝ] F) (x : Space) :
    timeAverage T a (fun z => L (f z)) x = L (timeAverage T a f x) := by
  simpa only [timeAverage, map_smul] using
    L.integral_comp_comm (timeAverage_timeSlice_integrable ha hf x)

/-- A field with a uniform spatial `L¹` bound has an integrable weighted
integrand on the time-space slab. -/
theorem timeAverage_integrand_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T M : ℝ} {a : ℝ → ℝ} {f : SpaceTime → E}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T))
    (hslice : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => f (t, x)))
    (hbound : ∀ t ∈ Icc 0 T, (∫ x : Space, ‖f (t, x)‖) ≤ M) :
    Integrable (fun z : SpaceTime => a z.1 • f z)
      (((volume : Measure ℝ).restrict (Icc 0 T)).prod (volume : Measure Space)) := by
  apply integrable_slab_of_integral_norm_le (continuousOn_time_weight ha hf)
    (fun t ht => (hslice t ht).smul (a t))
    (ha.norm.integrableOn_Icc.mul_const M)
  intro t ht
  simp only [norm_smul]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hbound t ht) (norm_nonneg _)

/-- The time average of a uniformly `L¹` field lies in spatial `L¹`. -/
theorem timeAverage_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T M : ℝ} {a : ℝ → ℝ} {f : SpaceTime → E}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T))
    (hslice : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => f (t, x)))
    (hbound : ∀ t ∈ Icc 0 T, (∫ x : Space, ‖f (t, x)‖) ≤ M) :
    Integrable (timeAverage T a f) :=
  (timeAverage_integrand_integrable ha hf hslice hbound).integral_prod_right

/-- The spatial `L¹` norm of an average is bounded by the uniform spatial
norm bound times the time integral of the weight's absolute value. -/
theorem timeAverage_norm_integral_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T M : ℝ} {a : ℝ → ℝ} {f : SpaceTime → E}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T))
    (hslice : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => f (t, x)))
    (hbound : ∀ t ∈ Icc 0 T, (∫ x : Space, ‖f (t, x)‖) ≤ M) :
    (∫ x : Space, ‖timeAverage T a f x‖) ≤ M * ∫ t in Icc 0 T, ‖a t‖ := by
  have hF := timeAverage_integrand_integrable ha hf hslice hbound
  calc
    (∫ x : Space, ‖timeAverage T a f x‖) ≤
        ∫ x : Space, ∫ t in Icc 0 T, ‖a t • f (t, x)‖ :=
      integral_mono hF.integral_prod_right.norm hF.integral_norm_prod_right
        (fun x => norm_integral_le_integral_norm (fun t => a t • f (t, x)))
    _ = ∫ t in Icc 0 T, ∫ x : Space, ‖a t • f (t, x)‖ :=
      (integral_integral_swap hF.norm).symm
    _ ≤ ∫ t in Icc 0 T, ‖a t‖ * M := by
      apply integral_mono_ae hF.integral_norm_prod_left (ha.norm.integrableOn_Icc.mul_const M)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simp only [norm_smul, integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hbound t ht) (norm_nonneg _)
    _ = M * ∫ t in Icc 0 T, ‖a t‖ := by rw [integral_mul_const]; ring

/-- Fubini for a uniformly `L¹` field and a continuous time weight. -/
theorem integral_timeAverage_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T M : ℝ} {a : ℝ → ℝ} {f : SpaceTime → E}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T))
    (hslice : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => f (t, x)))
    (hbound : ∀ t ∈ Icc 0 T, (∫ x : Space, ‖f (t, x)‖) ≤ M) :
    (∫ x : Space, timeAverage T a f x) =
      ∫ t in Icc 0 T, a t • (∫ x : Space, f (t, x)) := by
  have hF := timeAverage_integrand_integrable ha hf hslice hbound
  change (∫ x : Space, ∫ t in Icc 0 T, a t • f (t, x)) = _
  rw [← integral_integral_swap hF]
  simp only [integral_smul]

/-- Cauchy--Schwarz for a Bochner integral over a finite measure space. -/
theorem norm_integral_sq_le_measure_mul_integral_sq
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → E} (hf : MemLp f 2 μ) :
    ‖∫ x, f x ∂μ‖ ^ 2 ≤ μ.real univ * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hholder : (∫ x, ‖f x‖ ∂μ) ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (μ.real univ) := by
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (f := fun x => ‖f x‖) (g := fun _ : α => (1 : ℝ))
      (Filter.Eventually.of_forall (fun x => norm_nonneg (f x)))
      (Filter.Eventually.of_forall (fun _ : α => zero_le_one))
      (by simpa using hf.norm)
      (by simpa using (memLp_const (μ := μ) (p := (2 : ℝ≥0∞)) (1 : ℝ)))
    simpa only [mul_one, Real.rpow_two, one_pow, integral_const, smul_eq_mul,
      ← Real.sqrt_eq_rpow] using h
  have hnorm := (norm_integral_le_integral_norm f).trans hholder
  have hsq := mul_self_le_mul_self (norm_nonneg (∫ x, f x ∂μ)) hnorm
  have hsq' : ‖∫ x, f x ∂μ‖ ^ 2 ≤
      (Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (μ.real univ)) ^ 2 := by
    simpa only [pow_two] using hsq
  calc
    ‖∫ x, f x ∂μ‖ ^ 2 ≤
        (Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (μ.real univ)) ^ 2 := hsq'
    _ = μ.real univ * ∫ x, ‖f x‖ ^ 2 ∂μ := by
      rw [mul_pow, Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg ‖f x‖)),
        Real.sq_sqrt (show 0 ≤ μ.real univ from ENNReal.toReal_nonneg)]
      ring

/-- Integrating in the finite time variable sends a square-integrable joint
field to a square-integrable spatial field. -/
theorem memLp_two_timeIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T : ℝ} {f : SpaceTime → E}
    (hf : AEStronglyMeasurable f
      (((volume : Measure ℝ).restrict (Icc 0 T)).prod (volume : Measure Space)))
    (hsq : Integrable (fun z : SpaceTime => ‖f z‖ ^ 2)
      (((volume : Measure ℝ).restrict (Icc 0 T)).prod (volume : Measure Space))) :
    MemLp (fun x : Space => ∫ t in Icc 0 T, f (t, x)) 2 volume := by
  have havg := hf.prod_swap.integral_prod_right'
  apply (memLp_two_iff_integrable_sq_norm havg).2
  apply (hsq.integral_prod_right.const_mul
    (((volume : Measure ℝ).restrict (Icc 0 T)).real univ)).mono' (havg.norm.pow 2)
  filter_upwards [hsq.prod_left_ae, hf.prod_swap.prodMk_left] with x hxint hxmeas
  have hxtwo := (memLp_two_iff_integrable_sq_norm hxmeas).2 hxint
  simpa only [Pi.pow_apply, norm_pow, norm_norm, Prod.swap_prod_mk] using
    norm_integral_sq_le_measure_mul_integral_sq hxtwo

/-- The quantitative estimate behind square-integrability of the time
integral. -/
theorem l2Sq_timeIntegral_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T : ℝ} {f : SpaceTime → E}
    (hf : AEStronglyMeasurable f
      (((volume : Measure ℝ).restrict (Icc 0 T)).prod (volume : Measure Space)))
    (hsq : Integrable (fun z : SpaceTime => ‖f z‖ ^ 2)
      (((volume : Measure ℝ).restrict (Icc 0 T)).prod (volume : Measure Space))) :
    l2Sq (fun x : Space => ∫ t in Icc 0 T, f (t, x)) ≤
      ((volume : Measure ℝ).restrict (Icc 0 T)).real univ *
        ∫ t in Icc 0 T, ∫ x : Space, ‖f (t, x)‖ ^ 2 := by
  have hAvg := memLp_two_timeIntegral hf hsq
  have hAvgSq := (memLp_two_iff_integrable_sq_norm hAvg.1).1 hAvg
  calc
    l2Sq (fun x : Space => ∫ t in Icc 0 T, f (t, x)) ≤
        ∫ x : Space, ((volume : Measure ℝ).restrict (Icc 0 T)).real univ *
          ∫ t in Icc 0 T, ‖f (t, x)‖ ^ 2 := by
      apply integral_mono_ae hAvgSq (hsq.integral_prod_right.const_mul _)
      filter_upwards [hsq.prod_left_ae, hf.prod_swap.prodMk_left] with x hxint hxmeas
      have hxtwo := (memLp_two_iff_integrable_sq_norm hxmeas).2 hxint
      simpa only [Prod.swap_prod_mk] using norm_integral_sq_le_measure_mul_integral_sq hxtwo
    _ = ((volume : Measure ℝ).restrict (Icc 0 T)).real univ *
        ∫ t in Icc 0 T, ∫ x : Space, ‖f (t, x)‖ ^ 2 := by
      rw [integral_const_mul, ← integral_integral_swap hsq]

/-- Squared norm integrability of the weighted joint field follows from a
uniform spatial square-integral bound. -/
theorem timeAverage_integrand_integrable_sq_norm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T M : ℝ} {a : ℝ → ℝ} {f : SpaceTime → E}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T))
    (hslice : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => ‖f (t, x)‖ ^ 2))
    (hbound : ∀ t ∈ Icc 0 T, (∫ x : Space, ‖f (t, x)‖ ^ 2) ≤ M) :
    Integrable (fun z : SpaceTime => ‖a z.1 • f z‖ ^ 2)
      (((volume : Measure ℝ).restrict (Icc 0 T)).prod (volume : Measure Space)) := by
  have hslices : ∀ t ∈ Icc 0 T,
      Integrable (fun x : Space => ‖a t • f (t, x)‖ ^ 2) := by
    intro t ht
    simpa only [norm_smul, mul_pow] using (hslice t ht).const_mul (‖a t‖ ^ 2)
  apply integrable_slab_of_integral_norm_le (continuousOn_time_weight ha hf |>.norm.pow 2)
    hslices ((ha.norm.pow 2).integrableOn_Icc.mul_const M)
  intro t ht
  simp only [Pi.pow_apply, norm_pow, norm_norm, norm_smul, mul_pow, norm_mul]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hbound t ht) (sq_nonneg _)

/-- The time average of a uniformly square-integrable field lies in spatial
`L²`. -/
theorem timeAverage_memLp_two {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T M : ℝ} {a : ℝ → ℝ} {f : SpaceTime → E}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T))
    (hslice : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => ‖f (t, x)‖ ^ 2))
    (hbound : ∀ t ∈ Icc 0 T, (∫ x : Space, ‖f (t, x)‖ ^ 2) ≤ M) :
    MemLp (timeAverage T a f) 2 volume :=
  memLp_two_timeIntegral (aestronglyMeasurable_slab (continuousOn_time_weight ha hf))
    (timeAverage_integrand_integrable_sq_norm ha hf hslice hbound)

/-- A quantitative square-integral estimate using only the time weight and
the uniform spatial square-integral bound. -/
theorem timeAverage_l2Sq_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T M : ℝ} {a : ℝ → ℝ} {f : SpaceTime → E}
    (hT : 0 ≤ T) (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T))
    (hslice : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => ‖f (t, x)‖ ^ 2))
    (hbound : ∀ t ∈ Icc 0 T, (∫ x : Space, ‖f (t, x)‖ ^ 2) ≤ M) :
    l2Sq (timeAverage T a f) ≤ T * M * ∫ t in Icc 0 T, ‖a t‖ ^ 2 := by
  have hF := aestronglyMeasurable_slab (continuousOn_time_weight ha hf)
  have hFsq := timeAverage_integrand_integrable_sq_norm ha hf hslice hbound
  have hvol : ((volume : Measure ℝ).restrict (Icc 0 T)).real univ = T := by
    simp only [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
      ENNReal.toReal_ofReal hT]
  calc
    l2Sq (timeAverage T a f) ≤ T *
        ∫ t in Icc 0 T, ∫ x : Space, ‖a t • f (t, x)‖ ^ 2 := by
      simpa only [hvol, timeAverage] using! l2Sq_timeIntegral_le hF hFsq
    _ ≤ T * ∫ t in Icc 0 T, ‖a t‖ ^ 2 * M := by
      apply mul_le_mul_of_nonneg_left _ hT
      apply integral_mono_ae hFsq.integral_prod_left
        ((ha.norm.pow 2).integrableOn_Icc.mul_const M)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simp only [norm_smul, mul_pow, integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hbound t ht) (sq_nonneg _)
    _ = T * M * ∫ t in Icc 0 T, ‖a t‖ ^ 2 := by rw [integral_mul_const]; ring

/-- Uniform finite kinetic energy gives square-integrability of every
continuously weighted time average of a velocity. -/
theorem timeAverage_memLp_two_of_uniformFiniteEnergy {T : ℝ} {a : ℝ → ℝ}
    {u : VelocityField} (ha : ContinuousOn a (Icc 0 T))
    (hu_cont : ContinuousOn u (slab 0 T)) (hu : UniformFiniteEnergy (Icc 0 T) u) :
    MemLp (timeAverage T a u) 2 volume := by
  obtain ⟨M, _, hM⟩ := uniformFiniteEnergy_l2Sq_bound hu
  exact timeAverage_memLp_two ha hu_cont (fun t ht => (hM t ht).1)
    (fun t ht => (hM t ht).2)

/-- In particular, the averaged difference of two finite-energy velocities
belongs to spatial `L²`. The weight can equally be a continuous derivative of
a smooth time test function. -/
theorem timeAverage_difference_memLp_two {T : ℝ} {a : ℝ → ℝ}
    {u v : VelocityField} (ha : ContinuousOn a (Icc 0 T))
    (hu_cont : ContinuousOn u (slab 0 T)) (hv_cont : ContinuousOn v (slab 0 T))
    (hu : UniformFiniteEnergy (Icc 0 T) u) (hv : UniformFiniteEnergy (Icc 0 T) v) :
    MemLp (timeAverage T a (fun z => u z - v z)) 2 volume :=
  timeAverage_memLp_two_of_uniformFiniteEnergy ha (hu_cont.sub hv_cont)
    (uniformFiniteEnergy_sub_of_continuousOn hu_cont hv_cont hu hv)

/-- A uniform finite-energy bound also bounds every scalar coordinate's
ordinary spatial square integral. -/
theorem uniformFiniteEnergy_component_l2Sq_bound {T : ℝ} {u : VelocityField}
    (hu_cont : ContinuousOn u (slab 0 T)) (hu : UniformFiniteEnergy (Icc 0 T) u)
    (k : Fin 3) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T,
      Integrable (fun x : Space => ‖u (t, x) k‖ ^ 2) ∧
        (∫ x : Space, ‖u (t, x) k‖ ^ 2) ≤ M := by
  obtain ⟨M, hM0, hM⟩ := uniformFiniteEnergy_l2Sq_bound hu
  refine ⟨M, hM0, ?_⟩
  intro t ht
  have humeas : AEStronglyMeasurable (fun x : Space => u (t, x)) volume :=
    (continuous_slice_of_continuousOn hu_cont ht).aestronglyMeasurable
  have huLp := (squareIntegrableAtTime_iff_memLp humeas).1 (hM t ht).1
  have hscalarmeas :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable humeas
  have hscalar := huLp.of_le hscalarmeas
    (Filter.Eventually.of_forall (fun x : Space => PiLp.norm_apply_le (u (t, x)) k))
  have hscalarSq := (memLp_two_iff_integrable_sq_norm hscalar.1).1 hscalar
  refine ⟨hscalarSq, ?_⟩
  apply le_trans (integral_mono hscalarSq (hM t ht).1 ?_) (hM t ht).2
  intro x
  simpa only [pow_two, EuclideanSpace.coe_proj] using
    mul_self_le_mul_self (norm_nonneg (u (t, x) k)) (PiLp.norm_apply_le (u (t, x)) k)

/-- Coordinate square-integral bounds for the difference field. -/
theorem uniformFiniteEnergy_difference_component_l2Sq_bound {T : ℝ}
    {u v : VelocityField}
    (hu_cont : ContinuousOn u (slab 0 T)) (hv_cont : ContinuousOn v (slab 0 T))
    (hu : UniformFiniteEnergy (Icc 0 T) u) (hv : UniformFiniteEnergy (Icc 0 T) v)
    (k : Fin 3) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T,
      Integrable (fun x : Space => ‖(u (t, x) - v (t, x)) k‖ ^ 2) ∧
        (∫ x : Space, ‖(u (t, x) - v (t, x)) k‖ ^ 2) ≤ M :=
  uniformFiniteEnergy_component_l2Sq_bound (hu_cont.sub hv_cont)
    (uniformFiniteEnergy_sub_of_continuousOn hu_cont hv_cont hu hv) k

/-- A scalar coordinate of the averaged difference is in `L²`, including
when the continuous weight is a derivative of a time test function. -/
theorem timeAverage_difference_component_memLp_two {T : ℝ} {a : ℝ → ℝ}
    {u v : VelocityField} (ha : ContinuousOn a (Icc 0 T))
    (hu_cont : ContinuousOn u (slab 0 T)) (hv_cont : ContinuousOn v (slab 0 T))
    (hu : UniformFiniteEnergy (Icc 0 T) u) (hv : UniformFiniteEnergy (Icc 0 T) v)
    (k : Fin 3) :
    MemLp (timeAverage T a (fun z : SpaceTime => (u z - v z) k)) 2 volume := by
  obtain ⟨M, _, hM⟩ :=
    uniformFiniteEnergy_difference_component_l2Sq_bound hu_cont hv_cont hu hv k
  exact timeAverage_memLp_two ha
    ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous.comp_continuousOn (hu_cont.sub hv_cont))
    (fun t ht => (hM t ht).1) (fun t ht => (hM t ht).2)

/-- Each nonlinear tensor component is jointly continuous on the slab. -/
theorem continuousOn_tensorDiff_field {T : ℝ} {u v : VelocityField}
    (hu : ContinuousOn u (slab 0 T)) (hv : ContinuousOn v (slab 0 T))
    (i j : Fin 3) :
    ContinuousOn (fun z : SpaceTime => tensorDiff u v z.1 i j z.2) (slab 0 T) := by
  have hui := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp_continuousOn hu
  have huj := (EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp_continuousOn hu
  have hvi := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp_continuousOn hv
  have hvj := (EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp_continuousOn hv
  simpa only [tensorDiff, Prod.mk.eta, Pi.sub_apply, Pi.mul_apply, Function.comp_def,
      EuclideanSpace.coe_proj] using! (hui.mul huj).sub (hvi.mul hvj)

/-- Uniform finite kinetic energy gives spatial `L¹` for each averaged
nonlinear tensor component. -/
theorem timeAverage_tensorDiff_integrable {T : ℝ} {a : ℝ → ℝ}
    {u v : VelocityField} (ha : ContinuousOn a (Icc 0 T))
    (hu_cont : ContinuousOn u (slab 0 T)) (hv_cont : ContinuousOn v (slab 0 T))
    (hu : UniformFiniteEnergy (Icc 0 T) u) (hv : UniformFiniteEnergy (Icc 0 T) v)
    (i j : Fin 3) :
    Integrable (timeAverage T a (fun z : SpaceTime => tensorDiff u v z.1 i j z.2)) := by
  obtain ⟨M, _, hM⟩ := uniformFiniteEnergy_tensorDiff_bound
    (fun t ht => (continuous_slice_of_continuousOn hu_cont ht).aestronglyMeasurable)
    (fun t ht => (continuous_slice_of_continuousOn hv_cont ht).aestronglyMeasurable) hu hv
  exact timeAverage_integrable ha (continuousOn_tensorDiff_field hu_cont hv_cont i j)
    (fun t ht => (hM t ht i j).1) (fun t ht => (hM t ht i j).2)

/-- A deliberately coarse bound for the `L¹` norm of an `L²` pairing. It is
sufficient for the Fubini argument and uses no pointwise bound on either field. -/
theorem l2_inner_integrable_and_norm_integral_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {f g : Space → E} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) :
    Integrable (fun x => ⟪f x, g x⟫_ℝ) ∧
      (∫ x : Space, ‖⟪f x, g x⟫_ℝ‖) ≤ l2Sq f + l2Sq g := by
  have hf_sq := (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  have hg_sq := (memLp_two_iff_integrable_sq_norm hg.1).1 hg
  have hpoint (x : Space) : ‖⟪f x, g x⟫_ℝ‖ ≤ ‖f x‖ ^ 2 + ‖g x‖ ^ 2 := by
    apply (norm_inner_le_norm (f x) (g x)).trans
    nlinarith [sq_nonneg (‖f x‖ - ‖g x‖), mul_nonneg (norm_nonneg (f x)) (norm_nonneg (g x))]
  have hint := (hf_sq.add hg_sq).mono' (hf.1.inner hg.1) (Filter.Eventually.of_forall hpoint)
  refine ⟨hint, ?_⟩
  calc
    (∫ x : Space, ‖⟪f x, g x⟫_ℝ‖) ≤ ∫ x : Space, ‖f x‖ ^ 2 + ‖g x‖ ^ 2 :=
      integral_mono hint.norm (hf_sq.add hg_sq) hpoint
    _ = l2Sq f + l2Sq g := integral_add hf_sq hg_sq

/-- The spatial `L²` pairing commutes with time averaging. Compact smooth
spatial tests are covered as a special case of a continuous `L²` test. -/
theorem timeAverage_inner_integral {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {T M : ℝ} {a : ℝ → ℝ}
    {f : SpaceTime → E} {ψ : Space → E}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T))
    (hslice : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => ‖f (t, x)‖ ^ 2))
    (hbound : ∀ t ∈ Icc 0 T, (∫ x : Space, ‖f (t, x)‖ ^ 2) ≤ M)
    (hψcont : Continuous ψ) (hψ : MemLp ψ 2 volume) :
    (∫ x : Space, ⟪ψ x, timeAverage T a f x⟫_ℝ) =
      ∫ t in Icc 0 T, a t * (∫ x : Space, ⟪ψ x, f (t, x)⟫_ℝ) := by
  have hflp (t : ℝ) (ht : t ∈ Icc 0 T) : MemLp (fun x : Space => f (t, x)) 2 volume := by
    have hfc : ContinuousOn (fun x : Space => f (t, x)) univ :=
      hf.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun x _ => ⟨ht, mem_univ x⟩)
    have hfm : AEStronglyMeasurable (fun x : Space => f (t, x)) volume := by
      simpa only [Measure.restrict_univ] using hfc.aestronglyMeasurable MeasurableSet.univ
    exact (memLp_two_iff_integrable_sq_norm hfm).2 (hslice t ht)
  have hpaircont : ContinuousOn (fun z : SpaceTime => ⟪ψ z.2, f z⟫_ℝ) (slab 0 T) :=
    (hψcont.comp continuous_snd).continuousOn.inner hf
  have hpair (t : ℝ) (ht : t ∈ Icc 0 T) :=
    l2_inner_integrable_and_norm_integral_le hψ (hflp t ht)
  have hpairbound (t : ℝ) (ht : t ∈ Icc 0 T) :
      (∫ x : Space, ‖⟪ψ x, f (t, x)⟫_ℝ‖) ≤ l2Sq ψ + M :=
    (hpair t ht).2.trans (add_le_add_right (hbound t ht) (l2Sq ψ))
  have havg (x : Space) :
      timeAverage T a (fun z : SpaceTime => ⟪ψ z.2, f z⟫_ℝ) x =
        ⟪ψ x, timeAverage T a f x⟫_ℝ := by
    simpa only [timeAverage, inner_smul_right, smul_eq_mul] using
      integral_inner (𝕜 := ℝ) (timeAverage_timeSlice_integrable ha hf x) (ψ x)
  calc
    (∫ x : Space, ⟪ψ x, timeAverage T a f x⟫_ℝ) =
        ∫ x : Space, timeAverage T a (fun z : SpaceTime => ⟪ψ z.2, f z⟫_ℝ) x :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x => (havg x).symm))
    _ = ∫ t in Icc 0 T, a t * (∫ x : Space, ⟪ψ x, f (t, x)⟫_ℝ) := by
      simpa only [smul_eq_mul] using
        integral_timeAverage_eq ha hpaircont (fun t ht => (hpair t ht).1) hpairbound

/-- A complex scalar spatial test factors out of the time integral. -/
theorem timeAverage_complex_mul (T : ℝ) (a : ℝ → ℝ) (f : SpaceTime → ℝ)
    (ψ : Space → ℂ) (x : Space) :
    timeAverage T a (fun z : SpaceTime => (f z : ℂ) * ψ z.2) x =
      ((timeAverage T a f x : ℝ) : ℂ) * ψ x := by
  change (∫ t in Icc 0 T, a t • ((f (t, x) : ℂ) * ψ x)) = _
  calc
    (∫ t in Icc 0 T, a t • ((f (t, x) : ℂ) * ψ x)) =
        ∫ t in Icc 0 T, ((a t * f (t, x) : ℝ) : ℂ) * ψ x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => by
        simp only [Complex.real_smul, Complex.ofReal_mul, mul_assoc])
    _ = (∫ t in Icc 0 T, ((a t * f (t, x) : ℝ) : ℂ)) * ψ x := integral_mul_const _ _
    _ = ((timeAverage T a f x : ℝ) : ℂ) * ψ x := by rw [integral_complex_ofReal]; rfl

/-- Fubini for a complex spatial test once the tested field has a uniform
spatial `L¹` bound. -/
theorem timeAverage_complex_pairing_of_integrable {T M : ℝ} {a : ℝ → ℝ}
    {f : SpaceTime → ℝ} {ψ : Space → ℂ}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T))
    (hψ : Continuous ψ)
    (hslice : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => (f (t, x) : ℂ) * ψ x))
    (hbound : ∀ t ∈ Icc 0 T, (∫ x : Space, ‖(f (t, x) : ℂ) * ψ x‖) ≤ M) :
    (∫ x : Space, ((timeAverage T a f x : ℝ) : ℂ) * ψ x) =
      ∫ t in Icc 0 T, (a t : ℂ) * (∫ x : Space, (f (t, x) : ℂ) * ψ x) := by
  have hpaircont : ContinuousOn (fun z : SpaceTime => (f z : ℂ) * ψ z.2) (slab 0 T) :=
    (Complex.continuous_ofReal.comp_continuousOn hf).mul
      (hψ.comp continuous_snd).continuousOn
  simpa only [timeAverage_complex_mul, Complex.real_smul] using
    integral_timeAverage_eq ha hpaircont hslice hbound

/-- Uniformly `L¹` real fields may be tested against every bounded continuous
complex function before interchanging the time and spatial integrals. -/
theorem timeAverage_complex_pairing_of_bounded {T M : ℝ} {a : ℝ → ℝ}
    {f : SpaceTime → ℝ} {ψ : Space → ℂ}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T))
    (hslice : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => f (t, x)))
    (hbound : ∀ t ∈ Icc 0 T, (∫ x : Space, ‖f (t, x)‖) ≤ M)
    (hψ : Continuous ψ) (hψbound : ∃ C : ℝ, ∀ x : Space, ‖ψ x‖ ≤ C) :
    (∫ x : Space, ((timeAverage T a f x : ℝ) : ℂ) * ψ x) =
      ∫ t in Icc 0 T, (a t : ℂ) * (∫ x : Space, (f (t, x) : ℂ) * ψ x) := by
  obtain ⟨C, hC⟩ := hψbound
  have hC0 : 0 ≤ C := (norm_nonneg (ψ 0)).trans (hC 0)
  have hpair (t : ℝ) (ht : t ∈ Icc 0 T) :
      Integrable (fun x : Space => (f (t, x) : ℂ) * ψ x) := by
    simpa only [mul_comm] using!
      (hslice t ht).ofReal.bdd_mul hψ.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  apply timeAverage_complex_pairing_of_integrable ha hf hψ hpair
    (M := C * M)
  intro t ht
  calc
    (∫ x : Space, ‖(f (t, x) : ℂ) * ψ x‖) ≤
        ∫ x : Space, C * ‖f (t, x)‖ := by
      apply integral_mono (hpair t ht).norm ((hslice t ht).norm.const_mul C)
      intro x
      change ‖(f (t, x) : ℂ) * ψ x‖ ≤ C * ‖f (t, x)‖
      rw [norm_mul, Complex.norm_real]
      exact (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = C * ∫ x : Space, ‖f (t, x)‖ := integral_const_mul _ _
    _ ≤ C * M := mul_le_mul_of_nonneg_left (hbound t ht) hC0

/-- Spatial `L²` control makes a scalar field times a complex `L²` test
integrable, with a coarse bound sufficient for Fubini. -/
theorem l2_complex_mul_integrable_and_norm_integral_le {f : Space → ℝ} {ψ : Space → ℂ}
    (hf : MemLp f 2 volume) (hψ : MemLp ψ 2 volume) :
    Integrable (fun x : Space => (f x : ℂ) * ψ x) ∧
      (∫ x : Space, ‖(f x : ℂ) * ψ x‖) ≤ l2Sq f + l2Sq ψ := by
  have hf_sq := (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  have hψ_sq := (memLp_two_iff_integrable_sq_norm hψ.1).1 hψ
  have hpoint (x : Space) : ‖(f x : ℂ) * ψ x‖ ≤ ‖f x‖ ^ 2 + ‖ψ x‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real]
    nlinarith [sq_nonneg (‖f x‖ - ‖ψ x‖), mul_nonneg (norm_nonneg (f x)) (norm_nonneg (ψ x))]
  have hmeas := (Complex.continuous_ofReal.comp_aestronglyMeasurable hf.1).mul hψ.1
  have hint := (hf_sq.add hψ_sq).mono' hmeas (Filter.Eventually.of_forall hpoint)
  refine ⟨hint, ?_⟩
  calc
    (∫ x : Space, ‖(f x : ℂ) * ψ x‖) ≤ ∫ x : Space, ‖f x‖ ^ 2 + ‖ψ x‖ ^ 2 :=
      integral_mono hint.norm (hf_sq.add hψ_sq) hpoint
    _ = l2Sq f + l2Sq ψ := integral_add hf_sq hψ_sq

/-- A uniformly square-integrable real field can be paired with a continuous
complex `L²` spatial test before interchanging time and space. -/
theorem timeAverage_complex_pairing_of_memLp_two {T M : ℝ} {a : ℝ → ℝ}
    {f : SpaceTime → ℝ} {ψ : Space → ℂ}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T))
    (hslice : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => ‖f (t, x)‖ ^ 2))
    (hbound : ∀ t ∈ Icc 0 T, (∫ x : Space, ‖f (t, x)‖ ^ 2) ≤ M)
    (hψcont : Continuous ψ) (hψ : MemLp ψ 2 volume) :
    (∫ x : Space, ((timeAverage T a f x : ℝ) : ℂ) * ψ x) =
      ∫ t in Icc 0 T, (a t : ℂ) * (∫ x : Space, (f (t, x) : ℂ) * ψ x) := by
  have hflp (t : ℝ) (ht : t ∈ Icc 0 T) : MemLp (fun x : Space => f (t, x)) 2 volume := by
    have hfc : ContinuousOn (fun x : Space => f (t, x)) univ :=
      hf.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun x _ => ⟨ht, mem_univ x⟩)
    have hfm : AEStronglyMeasurable (fun x : Space => f (t, x)) volume := by
      simpa only [Measure.restrict_univ] using hfc.aestronglyMeasurable MeasurableSet.univ
    exact (memLp_two_iff_integrable_sq_norm hfm).2 (hslice t ht)
  have hpair (t : ℝ) (ht : t ∈ Icc 0 T) :=
    l2_complex_mul_integrable_and_norm_integral_le (hflp t ht) hψ
  apply timeAverage_complex_pairing_of_integrable ha hf hψcont (fun t ht => (hpair t ht).1)
    (M := M + l2Sq ψ)
  intro t ht
  exact (hpair t ht).2.trans (add_le_add_left (hbound t ht) (l2Sq ψ))

end NavierStokesR3.Comparison
