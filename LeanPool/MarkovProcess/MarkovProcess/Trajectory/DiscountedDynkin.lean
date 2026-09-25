/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Path.ExitTime
public import LeanPool.MarkovProcess.MarkovProcess.Path.OptionalStopping
public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.DynkinMartingale


/-!
# The discounted Dynkin formula

For the continuous-path process of a conservative Feller semigroup, this file proves that the
Dynkin process with exponential discount is a martingale and applies optional stopping at an exit
time truncated by a deterministic horizon.  At zero discount it agrees with the Dynkin process
of `Trajectory/DynkinMartingale.lean`.

Main results: `IsFellerKernelSemigroup.discountedDynkinProcess`,
`discountedDynkinProcess_apply`, `discountedDynkinProcess_zero`,
`norm_discountedDynkinProcess_le`, `continuous_discountedDynkinProcess`,
`stronglyMeasurable_integral_discountedGenerator`,
`stronglyMeasurable_discountedDynkinProcess_canonicalFiltration`,
`stronglyMeasurable_discountedDynkinProcess`, `adapted_discountedDynkinProcess`,
`integrable_discountedDynkinProcess`, `integral_discountedDynkinProcess`,
`discountedDynkinProcess_eq_add_shift`, `martingale_discountedDynkinProcess`,
`progMeasurable_discountedDynkinProcess`, `measurable_discountedDynkinProcess_stoppingTime`,
`integral_discountedDynkinProcess_stoppingTime`, and
`integral_exp_eval_exitTimeTrunc_sub_eq_integral_integral`.

No assertion is made at an unbounded stopping time or about passage to an infinite horizon.
-/

@[expose] public section

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}

section ProcessDefinition

/-- The discounted Dynkin process associated with a generator-domain function. -/
def IsFellerKernelSemigroup.discountedDynkinProcess
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain)
    (lam : ℝ) (t : NNReal) (omega : ContinuousPath alpha) : ℝ :=
  Real.exp (-lam * (t : ℝ)) * (f : C₀(alpha, ℝ)) (omega t) -
    ∫ s in (0 : ℝ)..t, Real.exp (-lam * s) *
      (hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ)))
        (omega (Real.toNNReal s))

omit [LocallyCompactSpace alpha] in
/-- The discounted Dynkin process, unfolded. -/
theorem IsFellerKernelSemigroup.discountedDynkinProcess_apply
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain)
    (lam : ℝ) (t : NNReal) (omega : ContinuousPath alpha) :
    hFeller.discountedDynkinProcess f lam t omega =
      Real.exp (-lam * (t : ℝ)) * (f : C₀(alpha, ℝ)) (omega t) -
        ∫ s in (0 : ℝ)..t, Real.exp (-lam * s) *
          (hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ)))
            (omega (Real.toNNReal s)) :=
  rfl

omit [LocallyCompactSpace alpha] in
/-- At zero discount, the discounted Dynkin process is the ordinary Dynkin process. -/
theorem IsFellerKernelSemigroup.discountedDynkinProcess_zero
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain) :
    hFeller.discountedDynkinProcess f 0 = hFeller.dynkinProcess f := by
  funext t omega
  simp only [IsFellerKernelSemigroup.discountedDynkinProcess_apply,
    IsFellerKernelSemigroup.dynkinProcess_apply, zero_mul, neg_zero, Real.exp_zero, one_mul,
    zero_smul, sub_zero]

/-- The exponential discount is bounded on a nonnegative bounded interval. -/
private theorem exp_neg_mul_le_exp_abs_mul {lam s v : ℝ} (hs : 0 ≤ s) (hsv : s ≤ v) :
    Real.exp (-lam * s) ≤ Real.exp (|lam| * v) := by
  apply Real.exp_le_exp.mpr
  calc
    -lam * s ≤ |lam| * s :=
      mul_le_mul_of_nonneg_right (neg_le_abs lam) hs
    _ ≤ |lam| * v := mul_le_mul_of_nonneg_left hsv (abs_nonneg lam)

omit [LocallyCompactSpace alpha] in
/-- The discounted Dynkin process is bounded uniformly in the path on bounded time intervals. -/
theorem IsFellerKernelSemigroup.norm_discountedDynkinProcess_le
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain)
    (lam : ℝ) (t : NNReal) (omega : ContinuousPath alpha) :
    ‖hFeller.discountedDynkinProcess f lam t omega‖ ≤
      Real.exp (|lam| * (t : ℝ)) *
        (‖(f : C₀(alpha, ℝ))‖ + (t : ℝ) *
          ‖hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ))‖) := by
  let g : C₀(alpha, ℝ) :=
    hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ))
  have hexp : Real.exp (-lam * (t : ℝ)) ≤ Real.exp (|lam| * (t : ℝ)) :=
    exp_neg_mul_le_exp_abs_mul t.coe_nonneg le_rfl
  have hterm : ‖Real.exp (-lam * (t : ℝ)) * (f : C₀(alpha, ℝ)) (omega t)‖ ≤
      Real.exp (|lam| * (t : ℝ)) * ‖(f : C₀(alpha, ℝ))‖ := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul hexp (norm_c0_apply_le _ _) (norm_nonneg _) (Real.exp_pos _).le)
  have hint : ‖∫ s in (0 : ℝ)..t, Real.exp (-lam * s) * g (omega (Real.toNNReal s))‖ ≤
      (t : ℝ) * (Real.exp (|lam| * (t : ℝ)) * ‖g‖) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (t : ℝ))
      (C := Real.exp (|lam| * (t : ℝ)) * ‖g‖)
      (f := fun s : ℝ ↦ Real.exp (-lam * s) * g (omega (Real.toNNReal s)))
      (fun s hs ↦ by
        rw [Set.uIoc_of_le t.coe_nonneg] at hs
        rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul (exp_neg_mul_le_exp_abs_mul hs.1.le hs.2)
          (norm_c0_apply_le _ _) (norm_nonneg _) (Real.exp_pos _).le)
    rwa [sub_zero, abs_of_nonneg t.coe_nonneg, mul_comm] at h
  rw [hFeller.discountedDynkinProcess_apply]
  change ‖_ - ∫ s in (0 : ℝ)..t, Real.exp (-lam * s) * g (omega (Real.toNNReal s))‖ ≤ _
  calc
    ‖_ - ∫ s in (0 : ℝ)..t, Real.exp (-lam * s) * g (omega (Real.toNNReal s))‖
        ≤ _ := norm_sub_le _ _
    _ ≤ Real.exp (|lam| * (t : ℝ)) * ‖(f : C₀(alpha, ℝ))‖ +
          (t : ℝ) * (Real.exp (|lam| * (t : ℝ)) * ‖g‖) := add_le_add hterm hint
    _ = Real.exp (|lam| * (t : ℝ)) *
          (‖(f : C₀(alpha, ℝ))‖ + (t : ℝ) * ‖g‖) := by ring

omit [LocallyCompactSpace alpha] in
/-- The discounted Dynkin process is continuous in time along every path. -/
theorem IsFellerKernelSemigroup.continuous_discountedDynkinProcess
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain)
    (lam : ℝ) (omega : ContinuousPath alpha) :
    Continuous fun t : NNReal ↦ hFeller.discountedDynkinProcess f lam t omega := by
  let g : C₀(alpha, ℝ) :=
    hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ))
  have hIntegrand : Continuous fun s : ℝ ↦
      Real.exp (-lam * s) * g (omega (Real.toNNReal s)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (g.continuous.comp (omega.continuous.comp continuous_real_toNNReal))
  have hIntegral : Continuous fun u : ℝ ↦
      ∫ s in (0 : ℝ)..u, Real.exp (-lam * s) * g (omega (Real.toNNReal s)) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact ((hIntegrand.integral_hasStrictDerivAt 0 u).hasDerivAt).continuousAt
  exact (((Real.continuous_exp.comp (continuous_const.mul NNReal.continuous_coe)).mul
      ((f : C₀(alpha, ℝ)).continuous.comp omega.continuous)).sub
        (hIntegral.comp NNReal.continuous_coe))

end ProcessDefinition

section Adapted

variable [SecondCountableTopology alpha]

omit [LocallyCompactSpace alpha] in
/-- The discounted generator integrand, clamped to a deterministic horizon, is jointly strongly
measurable for time and the canonical filtration at that horizon. -/
private theorem stronglyMeasurable_discountedGenerator_min
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain)
    (lam : ℝ) (t : NNReal) :
    StronglyMeasurable[(borel ℝ).prod (ContinuousPath.canonicalFiltration (alpha := alpha) t)]
      (fun p : ℝ × ContinuousPath alpha ↦ Real.exp (-lam * p.1) *
        (hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ)))
          (p.2 (min (Real.toNNReal p.1) t))) := by
  exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
      measurable_fst).stronglyMeasurable.mul
    ((hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ))).continuous.comp_stronglyMeasurable
      (ContinuousPath.measurable_clampedCoordinate (alpha := alpha) t).stronglyMeasurable)

omit [LocallyCompactSpace alpha] in
/-- The correction term of the discounted Dynkin process is strongly measurable at its horizon. -/
theorem IsFellerKernelSemigroup.stronglyMeasurable_integral_discountedGenerator
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain)
    (lam : ℝ) (t : NNReal) :
    StronglyMeasurable[ContinuousPath.canonicalFiltration (alpha := alpha) t]
      (fun omega : ContinuousPath alpha ↦
        ∫ s in (0 : ℝ)..t, Real.exp (-lam * s) *
          (hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ)))
            (omega (Real.toNNReal s))) := by
  let g : C₀(alpha, ℝ) :=
    hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ))
  have hprod := stronglyMeasurable_integral_prod (volume.restrict (Set.Ioc (0 : ℝ) t))
    (stronglyMeasurable_discountedGenerator_min hFeller f lam t)
  have hfun : (fun omega : ContinuousPath alpha ↦
      ∫ s in (0 : ℝ)..t, Real.exp (-lam * s) * g (omega (Real.toNNReal s))) =
      fun omega : ContinuousPath alpha ↦ ∫ s,
        Real.exp (-lam * s) * g (omega (min (Real.toNNReal s) t))
          ∂(volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    funext omega
    rw [intervalIntegral.integral_of_le t.coe_nonneg]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ ?_
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.mpr hs.2)]
  rw [hfun]
  exact hprod

omit [LocallyCompactSpace alpha] in
/-- The discounted Dynkin process is strongly measurable for the canonical filtration at time
`t`. -/
theorem IsFellerKernelSemigroup.stronglyMeasurable_discountedDynkinProcess_canonicalFiltration
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain)
    (lam : ℝ) (t : NNReal) :
    StronglyMeasurable[ContinuousPath.canonicalFiltration (alpha := alpha) t]
      (hFeller.discountedDynkinProcess f lam t) :=
  (((f : C₀(alpha, ℝ)).continuous.comp_stronglyMeasurable
      (ContinuousPath.measurable_coordinateProcess_canonicalFiltration
        (alpha := alpha) t).stronglyMeasurable).const_mul
          (Real.exp (-lam * (t : ℝ)))).sub
    (hFeller.stronglyMeasurable_integral_discountedGenerator f lam t)

omit [LocallyCompactSpace alpha] in
/-- The discounted Dynkin process at a deterministic time is Borel strongly measurable. -/
theorem IsFellerKernelSemigroup.stronglyMeasurable_discountedDynkinProcess
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain)
    (lam : ℝ) (t : NNReal) :
    StronglyMeasurable (hFeller.discountedDynkinProcess f lam t) :=
  (hFeller.stronglyMeasurable_discountedDynkinProcess_canonicalFiltration f lam t).mono
    ((ContinuousPath.canonicalFiltration (alpha := alpha)).le t)

omit [LocallyCompactSpace alpha] in
/-- The discounted Dynkin process is adapted to the canonical filtration. -/
theorem IsFellerKernelSemigroup.adapted_discountedDynkinProcess
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain)
    (lam : ℝ) :
    StronglyAdapted (ContinuousPath.canonicalFiltration (alpha := alpha))
      (hFeller.discountedDynkinProcess f lam) :=
  fun t ↦ hFeller.stronglyMeasurable_discountedDynkinProcess_canonicalFiltration f lam t

end Adapted

section Expectation

variable [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
variable (hP : P.IsConservative)

omit [LocallyCompactSpace alpha] in
/-- The discounted Dynkin process is integrable under the continuous-path process. -/
theorem IsFellerKernelSemigroup.integrable_discountedDynkinProcess
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain)
    (lam : ℝ) (t : NNReal) (y : alpha) :
    Integrable (hFeller.discountedDynkinProcess f lam t)
      (IsConservative.continuousProcess P hP y) :=
  Integrable.of_bound
    (hFeller.stronglyMeasurable_discountedDynkinProcess f lam t).aestronglyMeasurable _
    (Eventually.of_forall (hFeller.norm_discountedDynkinProcess_le f lam t))

/-- The expectation of the discounted Dynkin process is its initial value. -/
theorem IsFellerKernelSemigroup.integral_discountedDynkinProcess
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (f : hFeller.c0Semigroup.generatorDomain) (lam : ℝ) (t : NNReal) (y : alpha) :
    ∫ omega, hFeller.discountedDynkinProcess f lam t omega
        ∂(IsConservative.continuousProcess P hP y) =
      (f : C₀(alpha, ℝ)) y := by
  let Q : Measure (ContinuousPath alpha) := IsConservative.continuousProcess P hP y
  let g : C₀(alpha, ℝ) :=
    hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ))
  have hterm : Integrable (fun omega : ContinuousPath alpha ↦
      Real.exp (-lam * (t : ℝ)) * (f : C₀(alpha, ℝ)) (omega t)) Q := by
    have hmeas : Measurable (fun omega : ContinuousPath alpha ↦
        Real.exp (-lam * (t : ℝ)) * (f : C₀(alpha, ℝ)) (omega t)) :=
      ((f : C₀(alpha, ℝ)).continuous.measurable.comp
        (ContinuousPath.measurable_coordinateProcess (alpha := alpha) t)).const_mul _
    exact Integrable.of_bound hmeas.aestronglyMeasurable _
      (Eventually.of_forall fun omega ↦ by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_c0_apply_le _ _) (norm_nonneg _))
  have hcorr : Integrable (fun omega : ContinuousPath alpha ↦
      ∫ s in (0 : ℝ)..t, Real.exp (-lam * s) * g (omega (Real.toNNReal s))) Q := by
    have hmeas := (hFeller.stronglyMeasurable_integral_discountedGenerator f lam t).mono
      ((ContinuousPath.canonicalFiltration (alpha := alpha)).le t)
    refine Integrable.of_bound hmeas.aestronglyMeasurable
      ((t : ℝ) * (Real.exp (|lam| * (t : ℝ)) * ‖g‖))
      (Eventually.of_forall fun omega ↦ ?_)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (t : ℝ))
      (C := Real.exp (|lam| * (t : ℝ)) * ‖g‖)
      (f := fun s : ℝ ↦ Real.exp (-lam * s) * g (omega (Real.toNNReal s)))
      (fun s hs ↦ by
        rw [Set.uIoc_of_le t.coe_nonneg] at hs
        rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul (exp_neg_mul_le_exp_abs_mul hs.1.le hs.2)
          (norm_c0_apply_le _ _) (norm_nonneg _) (Real.exp_pos _).le)
    rwa [sub_zero, abs_of_nonneg t.coe_nonneg, mul_comm] at h
  have hstep :
      (∫ omega, Real.exp (-lam * (t : ℝ)) * (f : C₀(alpha, ℝ)) (omega t) ∂Q) -
          (f : C₀(alpha, ℝ)) y =
        ∫ s in (0 : ℝ)..t, ∫ omega, Real.exp (-lam * s) *
          g (omega (Real.toNNReal s)) ∂Q := by
    calc
      (∫ omega, Real.exp (-lam * (t : ℝ)) * (f : C₀(alpha, ℝ)) (omega t) ∂Q) -
            (f : C₀(alpha, ℝ)) y
          = c0EvalCLM y (Real.exp (-lam * (t : ℝ)) •
              hFeller.c0Semigroup t (f : C₀(alpha, ℝ)) - f) := by
            rw [map_sub, map_smul, c0EvalCLM_apply, c0EvalCLM_apply,
              smul_eq_mul, hFeller.c0Semigroup_apply_eq_integral P hP hK]
            rw [MeasureTheory.integral_const_mul]
      _ = c0EvalCLM y (∫ s in (0 : ℝ)..t, Real.exp (-lam * s) •
            hFeller.c0Semigroup (Real.toNNReal s) g) := by
          rw [hFeller.c0Semigroup.exp_smul_operator_sub_eq_integral f lam t]
      _ = ∫ s in (0 : ℝ)..t, c0EvalCLM y
            (Real.exp (-lam * s) • hFeller.c0Semigroup (Real.toNNReal s) g) := by
          rw [← (c0EvalCLM y).intervalIntegral_comp_comm]
          exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
            (hFeller.c0Semigroup.continuous_operator_toNNReal g)).intervalIntegrable _ _
      _ = ∫ s in (0 : ℝ)..t, ∫ omega, Real.exp (-lam * s) *
            g (omega (Real.toNNReal s)) ∂Q := by
          refine intervalIntegral.integral_congr fun s _ ↦ ?_
          rw [map_smul, c0EvalCLM_apply, smul_eq_mul,
            hFeller.c0Semigroup_apply_eq_integral P hP hK, MeasureTheory.integral_const_mul]
  have hcont : Continuous fun p : ℝ × ContinuousPath alpha ↦
      Real.exp (-lam * p.1) * g (p.2 (Real.toNNReal p.1)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_fst)).mul
      (g.continuous.comp ((ContinuousEval.continuous_eval.comp continuous_swap).comp
        (continuous_real_toNNReal.fst'.prodMk continuous_snd)))
  have hprodint : Integrable
      (Function.uncurry fun (s : ℝ) (omega : ContinuousPath alpha) ↦
        Real.exp (-lam * s) * g (omega (Real.toNNReal s)))
      ((volume.restrict (Set.Ioc (0 : ℝ) t)).prod Q) := by
    let C := Real.exp (|lam| * (t : ℝ)) * ‖g‖
    refine Integrable.of_bound hcont.aestronglyMeasurable C ?_
    change ∀ᵐ p : ℝ × ContinuousPath alpha
      ∂((volume.restrict (Set.Ioc (0 : ℝ) t)).prod Q),
        ‖Real.exp (-lam * p.1) * g (p.2 (Real.toNNReal p.1))‖ ≤ C
    rw [Measure.ae_prod_iff_ae_ae (measurableSet_le
      (hcont.norm.measurable) measurable_const)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact Eventually.of_forall fun omega ↦ by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (exp_neg_mul_le_exp_abs_mul hs.1.le hs.2)
        (norm_c0_apply_le _ _) (norm_nonneg _) (Real.exp_pos _).le
  have hswap :
      ∫ omega, (∫ s in (0 : ℝ)..t, Real.exp (-lam * s) *
          g (omega (Real.toNNReal s))) ∂Q =
        ∫ s in (0 : ℝ)..t, ∫ omega, Real.exp (-lam * s) *
          g (omega (Real.toNNReal s)) ∂Q := by
    calc
      ∫ omega, (∫ s in (0 : ℝ)..t, Real.exp (-lam * s) *
            g (omega (Real.toNNReal s))) ∂Q =
          ∫ omega, (∫ s in Set.Ioc (0 : ℝ) t, Real.exp (-lam * s) *
            g (omega (Real.toNNReal s))) ∂Q := by
        refine integral_congr_ae (Eventually.of_forall fun omega ↦ ?_)
        exact intervalIntegral.integral_of_le t.coe_nonneg
      _ = ∫ s in Set.Ioc (0 : ℝ) t, ∫ omega, Real.exp (-lam * s) *
            g (omega (Real.toNNReal s)) ∂Q := (integral_integral_swap hprodint).symm
      _ = ∫ s in (0 : ℝ)..t, ∫ omega, Real.exp (-lam * s) *
            g (omega (Real.toNNReal s)) ∂Q :=
        (intervalIntegral.integral_of_le t.coe_nonneg).symm
  change ∫ omega, (Real.exp (-lam * (t : ℝ)) * (f : C₀(alpha, ℝ)) (omega t) -
      ∫ s in (0 : ℝ)..t, Real.exp (-lam * s) * g (omega (Real.toNNReal s))) ∂Q = _
  rw [integral_sub hterm hcorr]
  linarith only [hstep, hswap]

end Expectation

section Decomposition

omit [LocallyCompactSpace alpha] in
/-- The discounted Dynkin process decomposes at an intermediate deterministic time. -/
theorem IsFellerKernelSemigroup.discountedDynkinProcess_eq_add_shift
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain)
    (lam : ℝ) (s t : NNReal) (hst : s ≤ t) (omega : ContinuousPath alpha) :
    hFeller.discountedDynkinProcess f lam t omega =
      hFeller.discountedDynkinProcess f lam s omega -
        Real.exp (-lam * (s : ℝ)) * (f : C₀(alpha, ℝ)) (omega s) +
        Real.exp (-lam * (s : ℝ)) *
          hFeller.discountedDynkinProcess f lam (t - s) (ContinuousPath.shift s omega) := by
  let g : C₀(alpha, ℝ) :=
    hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ))
  let q : ℝ → ℝ := fun v ↦ Real.exp (-lam * v) * g (omega (Real.toNNReal v))
  have hscaledTail : Real.exp (-lam * (s : ℝ)) *
        (∫ u in (0 : ℝ)..((t - s : NNReal) : ℝ), Real.exp (-lam * u) *
          g (omega (s + Real.toNNReal u))) =
      ∫ v in (s : ℝ)..(t : ℝ), q v := by
    rw [← intervalIntegral.integral_const_mul]
    have hcongr : (∫ u in (0 : ℝ)..((t - s : NNReal) : ℝ),
          Real.exp (-lam * (s : ℝ)) *
            (Real.exp (-lam * u) * g (omega (s + Real.toNNReal u)))) =
        ∫ u in (0 : ℝ)..((t - s : NNReal) : ℝ), q (u + s) := by
      refine intervalIntegral.integral_congr fun u hu ↦ ?_
      have hu0 : (0 : ℝ) ≤ u := by
        rw [Set.uIcc_of_le (t - s : NNReal).coe_nonneg] at hu
        exact hu.1
      have hcoe : Real.toNNReal (u + s) = s + Real.toNNReal u := by
        apply NNReal.coe_injective
        rw [NNReal.coe_add, Real.coe_toNNReal u hu0,
          Real.coe_toNNReal _ (add_nonneg hu0 s.coe_nonneg)]
        ring
      dsimp only [q]
      rw [hcoe, ← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [hcongr, intervalIntegral.integral_comp_add_right q (s : ℝ), zero_add]
    congr 1
    rw [NNReal.coe_sub hst]
    ring
  have hcont : Continuous q :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (g.continuous.comp (omega.continuous.comp continuous_real_toNNReal))
  have hsplit : (∫ v in (0 : ℝ)..(s : ℝ), q v) +
      (∫ v in (s : ℝ)..(t : ℝ), q v) = ∫ v in (0 : ℝ)..(t : ℝ), q v :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  have hExp : Real.exp (-lam * (t : ℝ)) =
      Real.exp (-lam * (s : ℝ)) * Real.exp (-lam * ((t - s : NNReal) : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    rw [NNReal.coe_sub hst]
    ring
  simp only [IsFellerKernelSemigroup.discountedDynkinProcess_apply,
    ContinuousPath.shift_apply, add_tsub_cancel_of_le hst]
  change _ - ∫ v in (0 : ℝ)..(t : ℝ), q v =
    (_ - ∫ v in (0 : ℝ)..(s : ℝ), q v) - _ +
      Real.exp (-lam * (s : ℝ)) *
        (_ - ∫ u in (0 : ℝ)..((t - s : NNReal) : ℝ),
          Real.exp (-lam * u) * g (omega (s + Real.toNNReal u)))
  rw [hExp, mul_assoc, mul_sub, hscaledTail]
  linarith only [hsplit]

end Decomposition

section Martingale

variable [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
variable (hP : P.IsConservative)

/-- The exponentially discounted Dynkin process is a martingale for the canonical filtration. -/
theorem IsFellerKernelSemigroup.martingale_discountedDynkinProcess
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (f : hFeller.c0Semigroup.generatorDomain) (lam : ℝ) (x : alpha) :
    Martingale (hFeller.discountedDynkinProcess f lam)
      (ContinuousPath.canonicalFiltration (alpha := alpha))
      (IsConservative.continuousProcess P hP x) := by
  refine ⟨hFeller.adapted_discountedDynkinProcess f lam, fun s t hst ↦ ?_⟩
  let c : ℝ := Real.exp (-lam * (s : ℝ))
  let A : ContinuousPath alpha → ℝ := fun omega ↦
    hFeller.discountedDynkinProcess f lam s omega - c * (f : C₀(alpha, ℝ)) (omega s)
  let F : ContinuousPath alpha → ℝ := fun eta ↦
    c * hFeller.discountedDynkinProcess f lam (t - s) eta
  have hdecomp : hFeller.discountedDynkinProcess f lam t =
      A + fun omega ↦ F (ContinuousPath.shift s omega) := by
    funext omega
    exact hFeller.discountedDynkinProcess_eq_add_shift f lam s t hst omega
  have hmeasA : StronglyMeasurable[ContinuousPath.canonicalFiltration (alpha := alpha) s] A :=
    (hFeller.stronglyMeasurable_discountedDynkinProcess_canonicalFiltration f lam s).sub
      (((f : C₀(alpha, ℝ)).continuous.comp_stronglyMeasurable
        (ContinuousPath.measurable_coordinateProcess_canonicalFiltration
          (alpha := alpha) s).stronglyMeasurable).const_mul c)
  have hintA : Integrable A (IsConservative.continuousProcess P hP x) := by
    refine Integrable.of_bound
      (hmeasA.mono
        ((ContinuousPath.canonicalFiltration (alpha := alpha)).le s)).aestronglyMeasurable
      (Real.exp (|lam| * (s : ℝ)) *
        (‖(f : C₀(alpha, ℝ))‖ + (s : ℝ) *
          ‖hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ))‖) +
        ‖c‖ * ‖(f : C₀(alpha, ℝ))‖)
      (Eventually.of_forall fun omega ↦ ?_)
    exact (norm_sub_le _ _).trans (add_le_add
      (hFeller.norm_discountedDynkinProcess_le f lam s omega)
      (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_c0_apply_le _ _) (norm_nonneg _)))
  have hmeasF : StronglyMeasurable F :=
    (hFeller.stronglyMeasurable_discountedDynkinProcess f lam (t - s)).const_mul c
  have hboundF : ∀ eta : ContinuousPath alpha, ‖F eta‖ ≤
      ‖c‖ * (Real.exp (|lam| * ((t - s : NNReal) : ℝ)) *
        (‖(f : C₀(alpha, ℝ))‖ + ((t - s : NNReal) : ℝ) *
          ‖hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ))‖)) := by
    intro eta
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (hFeller.norm_discountedDynkinProcess_le f lam (t - s) eta) (norm_nonneg _)
  have hintB : Integrable (fun omega : ContinuousPath alpha ↦
      F (ContinuousPath.shift s omega)) (IsConservative.continuousProcess P hP x) :=
    Integrable.of_bound
      (hmeasF.comp_measurable
        (ContinuousPath.measurable_shift_fixed (alpha := alpha) s)).aestronglyMeasurable
      _ (Eventually.of_forall fun omega ↦ hboundF (ContinuousPath.shift s omega))
  have hcondA := condExp_of_stronglyMeasurable
    ((ContinuousPath.canonicalFiltration (alpha := alpha)).le s) hmeasA hintA
  have hcondB := hFeller.continuousProcess_condExp_shift P hP hK x s F hmeasF _ hboundF
  have hcondB' : (IsConservative.continuousProcess P hP x)[fun omega ↦
      F (ContinuousPath.shift s omega) | ContinuousPath.canonicalFiltration (alpha := alpha) s]
        =ᵐ[IsConservative.continuousProcess P hP x]
      fun omega : ContinuousPath alpha ↦ c * (f : C₀(alpha, ℝ)) (omega s) := by
    refine hcondB.trans (Eventually.of_forall fun omega ↦ ?_)
    dsimp only [F]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    exact hFeller.integral_discountedDynkinProcess hP hK f lam (t - s) (omega s)
  rw [hdecomp]
  refine (condExp_add hintA hintB _).trans ?_
  rw [hcondA]
  refine (EventuallyEq.add (EventuallyEq.refl _ _) hcondB').trans
    (Eventually.of_forall fun omega ↦ ?_)
  simp only [Pi.add_apply, A]
  ring

end Martingale

section OptionalStopping

variable [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
variable (hP : P.IsConservative)

omit [CompleteSpace alpha] [Nonempty alpha] in
omit [LocallyCompactSpace alpha] in
/-- The discounted Dynkin process is progressively measurable. -/
theorem IsFellerKernelSemigroup.progMeasurable_discountedDynkinProcess
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain)
    (lam : ℝ) :
    IsStronglyProgressive (ContinuousPath.canonicalFiltration (alpha := alpha))
      (hFeller.discountedDynkinProcess f lam) :=
  (hFeller.adapted_discountedDynkinProcess f lam).isStronglyProgressive_of_continuous fun omega ↦
    hFeller.continuous_discountedDynkinProcess f lam omega

omit [CompleteSpace alpha] [Nonempty alpha] in
omit [LocallyCompactSpace alpha] in
/-- The discounted Dynkin process evaluated at a finite stopping time is Borel measurable. -/
theorem IsFellerKernelSemigroup.measurable_discountedDynkinProcess_stoppingTime
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain)
    (lam : ℝ) (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal))) :
    Measurable fun omega ↦ hFeller.discountedDynkinProcess f lam (T omega) omega := by
  have h := (measurable_stoppedValue (hFeller.progMeasurable_discountedDynkinProcess f lam) hT).mono
    hT.measurableSpace_le le_rfl
  simpa only [stoppedValue] using! h

/-- Optional stopping for the discounted Dynkin process at a bounded finite stopping time. -/
theorem IsFellerKernelSemigroup.integral_discountedDynkinProcess_stoppingTime
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (f : hFeller.c0Semigroup.generatorDomain) (lam : ℝ)
    (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    {K : NNReal} (hTK : ∀ omega, T omega ≤ K) (x : alpha) :
    ∫ omega, hFeller.discountedDynkinProcess f lam (T omega) omega
        ∂(IsConservative.continuousProcess P hP x) =
      (f : C₀(alpha, ℝ)) x := by
  let g : C₀(alpha, ℝ) :=
    hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ))
  have hbound : ∀ v : NNReal, ∃ C : ℝ, ∀ t ≤ v, ∀ omega : ContinuousPath alpha,
      ‖hFeller.discountedDynkinProcess f lam t omega‖ ≤ C := by
    intro v
    refine ⟨Real.exp (|lam| * (v : ℝ)) *
      (‖(f : C₀(alpha, ℝ))‖ + (v : ℝ) * ‖g‖), fun t ht omega ↦
        (hFeller.norm_discountedDynkinProcess_le f lam t omega).trans ?_⟩
    have hexp : Real.exp (|lam| * (t : ℝ)) ≤ Real.exp (|lam| * (v : ℝ)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr ht) (abs_nonneg lam)
    have hinside : ‖(f : C₀(alpha, ℝ))‖ + (t : ℝ) * ‖g‖ ≤
        ‖(f : C₀(alpha, ℝ))‖ + (v : ℝ) * ‖g‖ :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_right
        (NNReal.coe_le_coe.mpr ht) (norm_nonneg g))
    exact mul_le_mul hexp hinside
      (add_nonneg (norm_nonneg _) (mul_nonneg t.coe_nonneg (norm_nonneg g)))
      (Real.exp_pos _).le
  have hright : ∀ (omega : ContinuousPath alpha) (v : NNReal),
      ContinuousWithinAt (fun t : NNReal ↦ hFeller.discountedDynkinProcess f lam t omega)
        (Set.Ici v) v :=
    fun omega _ ↦ (hFeller.continuous_discountedDynkinProcess f lam omega).continuousWithinAt
  rw [MarkovProcess.integral_stoppedValue_eq_of_locallyBounded
    (hFeller.martingale_discountedDynkinProcess hP hK f lam x) hbound hright hT hTK]
  exact hFeller.integral_discountedDynkinProcess hP hK f lam 0 x

/-- **The discounted Dynkin formula at a truncated exit time.** -/
theorem IsFellerKernelSemigroup.integral_exp_eval_exitTimeTrunc_sub_eq_integral_integral
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (f : hFeller.c0Semigroup.generatorDomain) (U : Set alpha) (hU : IsOpen U)
    (K : NNReal) (lam : ℝ) (x : alpha) :
    ∫ omega, Real.exp (-lam * (ContinuousPath.exitTimeTrunc U K omega : ℝ)) *
          (f : C₀(alpha, ℝ)) (omega (ContinuousPath.exitTimeTrunc U K omega))
        ∂(IsConservative.continuousProcess P hP x) - (f : C₀(alpha, ℝ)) x =
      ∫ omega, (∫ s in (0 : ℝ)..(ContinuousPath.exitTimeTrunc U K omega : ℝ),
          Real.exp (-lam * s) *
            (hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ)))
              (omega (Real.toNNReal s)))
        ∂(IsConservative.continuousProcess P hP x) := by
  let T := ContinuousPath.exitTimeTrunc U K
  let Q : Measure (ContinuousPath alpha) := IsConservative.continuousProcess P hP x
  have hT := ContinuousPath.isStoppingTime_exitTimeTrunc U hU K
  have hTK := ContinuousPath.exitTimeTrunc_le U K
  have hstop := hFeller.integral_discountedDynkinProcess_stoppingTime hP hK f lam T hT hTK x
  have hterminal : Integrable (fun omega : ContinuousPath alpha ↦
      Real.exp (-lam * (T omega : ℝ)) * (f : C₀(alpha, ℝ)) (omega (T omega))) Q := by
    have hmeasT : Measurable T := ContinuousPath.measurable_of_isStoppingTime T hT
    have hmeas : Measurable (fun omega : ContinuousPath alpha ↦
        Real.exp (-lam * (T omega : ℝ)) * (f : C₀(alpha, ℝ)) (omega (T omega))) :=
      (Real.continuous_exp.measurable.comp
        (measurable_const.mul (measurable_coe_nnreal_real.comp hmeasT))).mul
      ((f : C₀(alpha, ℝ)).continuous.measurable.comp
        (ContinuousPath.measurable_eval_stoppingTime_borel T hT))
    refine Integrable.of_bound hmeas.aestronglyMeasurable
      (Real.exp (|lam| * (K : ℝ)) * ‖(f : C₀(alpha, ℝ))‖)
      (Eventually.of_forall fun omega ↦ ?_)
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (exp_neg_mul_le_exp_abs_mul (T omega).coe_nonneg
      (NNReal.coe_le_coe.mpr (hTK omega))) (norm_c0_apply_le _ _)
      (norm_nonneg _) (Real.exp_pos _).le
  have hcorrection : Integrable (fun omega : ContinuousPath alpha ↦
      ∫ s in (0 : ℝ)..(T omega : ℝ), Real.exp (-lam * s) *
        (hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ)))
          (omega (Real.toNNReal s))) Q := by
    have hdiff : (fun omega : ContinuousPath alpha ↦
        ∫ s in (0 : ℝ)..(T omega : ℝ), Real.exp (-lam * s) *
          (hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ)))
            (omega (Real.toNNReal s))) =
      fun omega ↦ Real.exp (-lam * (T omega : ℝ)) *
          (f : C₀(alpha, ℝ)) (omega (T omega)) -
        hFeller.discountedDynkinProcess f lam (T omega) omega := by
      funext omega
      rw [hFeller.discountedDynkinProcess_apply]
      ring
    rw [hdiff]
    exact hterminal.sub (Integrable.of_bound
      (hFeller.measurable_discountedDynkinProcess_stoppingTime f lam T hT).aestronglyMeasurable
      (Real.exp (|lam| * (K : ℝ)) *
        (‖(f : C₀(alpha, ℝ))‖ + (K : ℝ) *
          ‖hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ))‖))
      (Eventually.of_forall fun omega ↦
        (hFeller.norm_discountedDynkinProcess_le f lam (T omega) omega).trans
          (mul_le_mul
            (by apply Real.exp_le_exp.mpr
                exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr (hTK omega))
                  (abs_nonneg lam))
            (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right
              (NNReal.coe_le_coe.mpr (hTK omega)) (norm_nonneg _)))
            (add_nonneg (norm_nonneg _) (mul_nonneg (T omega).coe_nonneg (norm_nonneg _)))
            (Real.exp_pos _).le)))
  change (∫ omega, _ ∂Q) - _ = ∫ omega, _ ∂Q
  have hsplit : ∫ omega, hFeller.discountedDynkinProcess f lam (T omega) omega ∂Q =
      (∫ omega, Real.exp (-lam * (T omega : ℝ)) *
        (f : C₀(alpha, ℝ)) (omega (T omega)) ∂Q) -
      ∫ omega, (∫ s in (0 : ℝ)..(T omega : ℝ), Real.exp (-lam * s) *
        (hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ)))
          (omega (Real.toNNReal s))) ∂Q := by
    simp only [IsFellerKernelSemigroup.discountedDynkinProcess_apply]
    exact integral_sub hterminal hcorrection
  linarith only [hstop, hsplit]

end OptionalStopping

end

end MarkovProcess.SubMarkovKernelSemigroup

end PortComputability
