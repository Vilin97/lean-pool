/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Killed.Kernel

/-!
# The killed resolvent

The resolvent of the process killed at the exit of an open set `U`, at the shift `λ > 0`, is the
Laplace transform of the killed kernels,

  `killedResolvent λ f x = ∫ t in (0, ∞), e^{-λ t} (∫ f d(killedKernel t x)) dt`,

and this file proves the path-space formula

  `killedResolvent λ f x = E_x ∫_0^{τ_U} e^{-λ t} f(ω_t) dt`

(`killedResolvent_eq_lintegral`), for nonnegative extended measurable `f`; the integral over time
runs up to the exit time, where the survival indicator vanishes. The statement is an identity of
`ℝ≥0∞`-valued integrals, proved by Tonelli's theorem, so it carries no integrability hypothesis;
a consumer working with real-valued bounded `f` splits it into its positive and negative parts.

This is the probabilistic side of the Dirichlet resolvent `(λ − L)⁻¹` on `U` with zero boundary
values: the identification with the analytic resolvent of a given operator is the consumer's
statement about that operator.  One order fact is recorded alongside: the killed resolvent is
antitone in the shift (`IsConservative.killedResolvent_antitone`), because a larger shift
discounts the future more.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)

/-- The killed resolvent at the shift `lam`, applied to a nonnegative extended function: the
Laplace transform in time of the killed kernels. -/
noncomputable def IsConservative.killedResolvent (lam : ℝ) (f : alpha → ℝ≥0∞) (x : alpha) :
    ℝ≥0∞ :=
  ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
    ∫⁻ y, f y ∂(IsConservative.killedKernel P hP U hU (Real.toNNReal t) x)

/-- An integral against a killed kernel is an integral over the survival event. -/
theorem IsConservative.lintegral_killedKernel (t : NNReal) (x : alpha) {f : alpha → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ y, f y ∂(IsConservative.killedKernel P hP U hU t x) =
      ∫⁻ omega, {omega : ContinuousPath alpha | (t : ℝ≥0∞) < ContinuousPath.exitTime U omega}.indicator
        (fun omega ↦ f (omega t)) omega ∂(IsConservative.continuousProcess P hP x) := by
  have hmeas : Measurable (fun omega : ContinuousPath alpha ↦ omega t) :=
    ContinuousPath.measurable_coordinateProcess (alpha := alpha) t
  rw [IsConservative.killedKernel_eq_map, lintegral_map hf hmeas,
    ← lintegral_indicator (ContinuousPath.measurableSet_lt_exitTime U hU t)]

/-- **The killed resolvent on path space.**  For nonnegative extended measurable `f` and `lam > 0`
(only the measurability is used),
`killedResolvent lam f x = E_x ∫_0^{τ_U} e^{-lam t} f(ω_t) dt`, the time integral being cut off at
the exit time by the survival indicator. -/
theorem IsConservative.killedResolvent_eq_lintegral (lam : ℝ) {f : alpha → ℝ≥0∞}
    (hf : Measurable f) (x : alpha) :
    IsConservative.killedResolvent P hP U hU lam f x =
      ∫⁻ omega, (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
          {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega}.indicator
            (fun t ↦ f (omega (Real.toNNReal t))) t)
        ∂(IsConservative.continuousProcess P hP x) := by
  have heval : Measurable fun p : ℝ × ContinuousPath alpha ↦ p.2 (Real.toNNReal p.1) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hS : MeasurableSet {p : ℝ × ContinuousPath alpha |
      ((Real.toNNReal p.1 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U p.2} :=
    measurableSet_lt (measurable_coe_nnreal_ennreal.comp (measurable_real_toNNReal.comp measurable_fst))
      ((ContinuousPath.measurable_exitTime U hU).comp measurable_snd)
  have hjoint : Measurable (Function.uncurry fun (t : ℝ) (omega : ContinuousPath alpha) ↦
      ENNReal.ofReal (Real.exp (-lam * t)) *
        {omega : ContinuousPath alpha |
          ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega}.indicator
          (fun omega ↦ f (omega (Real.toNNReal t))) omega) := by
    have hrw : (Function.uncurry fun (t : ℝ) (omega : ContinuousPath alpha) ↦
        ENNReal.ofReal (Real.exp (-lam * t)) *
          {omega : ContinuousPath alpha |
            ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega}.indicator
            (fun omega ↦ f (omega (Real.toNNReal t))) omega) =
        fun p : ℝ × ContinuousPath alpha ↦ ENNReal.ofReal (Real.exp (-lam * p.1)) *
          {p : ℝ × ContinuousPath alpha |
            ((Real.toNNReal p.1 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U p.2}.indicator
            (fun p ↦ f (p.2 (Real.toNNReal p.1))) p := by
      funext p
      simp only [Function.uncurry, Set.indicator_apply, Set.mem_ofPred_eq]
    rw [hrw]
    refine Measurable.mul ?_ ((hf.comp heval).indicator hS)
    exact ENNReal.measurable_ofReal.comp
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
        measurable_fst)
  have hinner : ∀ t : ℝ, ENNReal.ofReal (Real.exp (-lam * t)) *
      ∫⁻ y, f y ∂(IsConservative.killedKernel P hP U hU (Real.toNNReal t) x) =
      ∫⁻ omega, ENNReal.ofReal (Real.exp (-lam * t)) *
        {omega : ContinuousPath alpha |
          ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega}.indicator
          (fun omega ↦ f (omega (Real.toNNReal t))) omega ∂(IsConservative.continuousProcess P hP x) := by
    intro t
    have hg : Measurable (fun omega : ContinuousPath alpha ↦ f (omega (Real.toNNReal t))) :=
      hf.comp (ContinuousPath.measurable_coordinateProcess (alpha := alpha) _)
    rw [IsConservative.lintegral_killedKernel P hP U hU _ x hf]
    exact (lintegral_const_mul _ (hg.indicator (ContinuousPath.measurableSet_lt_exitTime U hU _))).symm
  unfold IsConservative.killedResolvent
  simp_rw [hinner]
  rw [lintegral_lintegral_swap hjoint.aemeasurable]
  refine lintegral_congr fun omega ↦ ?_
  refine setLIntegral_congr_fun measurableSet_Ioi ?_
  intro t _
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]

/-- **The killed resolvent is antitone in the shift.**  A larger shift discounts the future more,
so it produces a smaller resolvent. -/
theorem IsConservative.killedResolvent_antitone (f : alpha → ℝ≥0∞) (x : alpha) {lam mu : ℝ}
    (hle : lam ≤ mu) :
    IsConservative.killedResolvent P hP U hU mu f x ≤
      IsConservative.killedResolvent P hP U hU lam f x := by
  unfold IsConservative.killedResolvent
  refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ ?_)
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)) _
  exact mul_le_mul_of_nonneg_right (neg_le_neg hle) (le_of_lt ht)

end MarkovProcess.SubMarkovKernelSemigroup
