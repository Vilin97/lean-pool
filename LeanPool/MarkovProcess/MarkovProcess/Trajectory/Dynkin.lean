/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Main
public import LeanPool.MarkovProcess.MarkovProcess.Kernel.PositiveC0OperatorMeasure
public import LeanPool.MarkovProcess.MarkovProcess.Semigroup.Generator
public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.AllTimeMarginals
public import Mathlib.MeasureTheory.Integral.Prod


/-!
# Dynkin's formula at deterministic times

For the continuous-path process `Q = continuousProcess P hP` of a conservative Feller semigroup
`P`, the `C₀` semigroup `hFeller.c0Semigroup` acts by `(S t f) x = E_x f(ω_t)`
(`c0Semigroup_apply_eq_integral`, from the one-time marginal `continuousProcess_map_eval_nnreal`
at every real time).  Combining this with the fundamental identity of the generator
`S t f - f = ∫₀ᵗ S s (L f) ds` and Fubini's theorem gives **Dynkin's formula**
(`integral_eval_sub_eq_integral_integral_generator`): for `f` in the generator domain,

  `E_x f(ω_t) - f x = E_x ∫₀ᵗ (L f)(ω_s) ds`.

The evaluation functional `c0EvalCLM x : C₀(α, ℝ) →L[ℝ] ℝ` is the tool that moves the Bochner
integral in `C₀` to a pointwise integral; `evalC0CLM` is the same functional under its original
name, kept for consumers.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

section Eval

variable {alpha : Type*} [TopologicalSpace alpha]

/-- Evaluation at a point, as a continuous linear functional on `C₀(α, ℝ)`. -/
noncomputable def evalC0CLM (x : alpha) : C₀(alpha, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ f x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    1 (fun f ↦ by
      rw [one_mul, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
      exact BoundedContinuousFunction.norm_coe_le_norm f.toBCF x)

/-- Evaluation, unfolded. -/
@[simp]
theorem evalC0CLM_apply (x : alpha) (f : C₀(alpha, ℝ)) : evalC0CLM x f = f x := rfl

end Eval

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- One-time marginal at every real time: evaluating the continuous-path process at time `t`
gives the transition kernel of `P` at `t`. -/
theorem IsFellerKernelSemigroup.continuousProcess_map_eval_nnreal
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) (t : NNReal) :
    (IsConservative.continuousProcess P hP).map (fun omega ↦ omega t) = P t :=
  IsConservative.continuousPathTrajectory_map_eval_nnreal P hP hFeller _ hK t

/-- The expectation of a `C₀` function of the position at time `t` is its integral against the
transition measure at time `t`. -/
theorem IsFellerKernelSemigroup.integral_eval_continuousProcess
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) (t : NNReal) (x : alpha)
    (f : C₀(alpha, ℝ)) :
    ∫ omega, f (omega t) ∂(IsConservative.continuousProcess P hP x) = ∫ y, f y ∂(P t x) := by
  have hmeas : Measurable (fun omega : ContinuousPath alpha ↦ omega t) :=
    ContinuousPath.measurable_coordinateProcess (alpha := alpha) t
  have h := integral_map (μ := IsConservative.continuousProcess P hP x) hmeas.aemeasurable
    (f := fun y ↦ f y) f.continuous.aestronglyMeasurable
  rw [← h, ← Kernel.map_apply _ hmeas, hFeller.continuousProcess_map_eval_nnreal P hP hK t]

/-- A measurable real-valued observable evaluated at a deterministic time has the corresponding
transition-kernel integral. -/
theorem IsFellerKernelSemigroup.integral_eval_continuousProcess_of_measurable
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (t : NNReal) (x : alpha) {f : alpha → ℝ} (hf : Measurable f) :
    ∫ omega, f (omega t) ∂(IsConservative.continuousProcess P hP x) =
      ∫ y, f y ∂(P t x) := by
  have heval := ContinuousPath.measurable_coordinateProcess (alpha := alpha) t
  calc
    (∫ omega, f (omega t) ∂(IsConservative.continuousProcess P hP x)) =
        ∫ y, f y ∂Measure.map (fun omega : ContinuousPath alpha ↦ omega t)
          (IsConservative.continuousProcess P hP x) :=
      (integral_map heval.aemeasurable hf.stronglyMeasurable.aestronglyMeasurable).symm
    _ = ∫ y, f y ∂(P t x) := by
      change ∫ y, f y ∂Measure.map (ContinuousPath.coordinateProcess (alpha := alpha) t)
        (IsConservative.continuousProcess P hP x) = _
      rw [← Kernel.map_apply _ heval]
      exact congrArg (fun K : Kernel alpha alpha ↦ ∫ y, f y ∂K x)
        (hFeller.continuousProcess_map_eval_nnreal P hP hK t)

/-- The `C₀` semigroup of a Feller semigroup is the expectation semigroup of its continuous-path
process: `(S t f) x = E_x f(ω_t)`. -/
theorem IsFellerKernelSemigroup.c0Semigroup_apply_eq_integral
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) (t : NNReal) (x : alpha)
    (f : C₀(alpha, ℝ)) :
    hFeller.c0Semigroup t f x =
      ∫ omega, f (omega t) ∂(IsConservative.continuousProcess P hP x) := by
  rw [IsFellerKernelSemigroup.c0Semigroup_apply_apply, kernelIntegral,
    hFeller.integral_eval_continuousProcess P hP hK t x f]

/-- **Dynkin's formula at a deterministic time.**  For `f` in the generator domain of the `C₀`
semigroup of `P`, with generator `L f`, and every starting point `x`,

  `E_x f(ω_t) - f x = E_x ∫₀ᵗ (L f)(ω_s) ds`. -/
theorem IsFellerKernelSemigroup.integral_eval_sub_eq_integral_integral_generator
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (f : hFeller.c0Semigroup.generatorDomain) (t : NNReal) (x : alpha) :
    ∫ omega, (f : C₀(alpha, ℝ)) (omega t) ∂(IsConservative.continuousProcess P hP x) -
        (f : C₀(alpha, ℝ)) x =
      ∫ omega, (∫ s in (0 : ℝ)..t, (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)))
        ∂(IsConservative.continuousProcess P hP x) := by
  have hint : IntervalIntegrable
      (fun s : ℝ ↦ hFeller.c0Semigroup (Real.toNNReal s) (hFeller.c0Semigroup.generator f))
      volume 0 t :=
    (hFeller.c0Semigroup.continuous_operator_toNNReal _).intervalIntegrable _ _
  have hstep : ∫ omega, (f : C₀(alpha, ℝ)) (omega t) ∂(IsConservative.continuousProcess P hP x) -
      (f : C₀(alpha, ℝ)) x =
      ∫ s in (0 : ℝ)..t, ∫ omega, (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s))
        ∂(IsConservative.continuousProcess P hP x) := by
    calc ∫ omega, (f : C₀(alpha, ℝ)) (omega t) ∂(IsConservative.continuousProcess P hP x) -
          (f : C₀(alpha, ℝ)) x
        = c0EvalCLM x (hFeller.c0Semigroup t (f : C₀(alpha, ℝ)) - (f : C₀(alpha, ℝ))) := by
          rw [map_sub, c0EvalCLM_apply, c0EvalCLM_apply,
            hFeller.c0Semigroup_apply_eq_integral P hP hK t x]
      _ = c0EvalCLM x (∫ s in (0 : ℝ)..t,
            hFeller.c0Semigroup (Real.toNNReal s) (hFeller.c0Semigroup.generator f)) := by
          rw [hFeller.c0Semigroup.operator_sub_eq_integral f t]
      _ = ∫ s in (0 : ℝ)..t,
            c0EvalCLM x (hFeller.c0Semigroup (Real.toNNReal s) (hFeller.c0Semigroup.generator f)) :=
          ((c0EvalCLM x).intervalIntegral_comp_comm hint).symm
      _ = ∫ s in (0 : ℝ)..t, ∫ omega, (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s))
            ∂(IsConservative.continuousProcess P hP x) := by
          refine intervalIntegral.integral_congr fun s _ ↦ ?_
          rw [c0EvalCLM_apply, hFeller.c0Semigroup_apply_eq_integral P hP hK]
  rw [hstep]
  have hcont : Continuous fun p : ℝ × ContinuousPath alpha ↦
      (hFeller.c0Semigroup.generator f) (p.2 (Real.toNNReal p.1)) :=
    (hFeller.c0Semigroup.generator f).continuous.comp
      ((ContinuousEval.continuous_eval.comp continuous_swap).comp
        (continuous_real_toNNReal.fst'.prodMk continuous_snd))
  have hbound : ∀ p : ℝ × ContinuousPath alpha,
      ‖(hFeller.c0Semigroup.generator f) (p.2 (Real.toNNReal p.1))‖ ≤
        ‖hFeller.c0Semigroup.generator f‖ := fun p ↦ by
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    exact BoundedContinuousFunction.norm_coe_le_norm (hFeller.c0Semigroup.generator f).toBCF
      (p.2 (Real.toNNReal p.1))
  have hprodint : Integrable
      (Function.uncurry fun (s : ℝ) (omega : ContinuousPath alpha) ↦
        (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)))
      ((volume.restrict (Set.Ioc (0 : ℝ) t)).prod (IsConservative.continuousProcess P hP x)) :=
    Integrable.of_bound hcont.aestronglyMeasurable _ (Eventually.of_forall hbound)
  rw [intervalIntegral.integral_of_le t.coe_nonneg, integral_integral_swap hprodint]
  refine integral_congr_ae (Eventually.of_forall fun omega ↦ ?_)
  exact (intervalIntegral.integral_of_le t.coe_nonneg).symm

end MarkovProcess.SubMarkovKernelSemigroup
