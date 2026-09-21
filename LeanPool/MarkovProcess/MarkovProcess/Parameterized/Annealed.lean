/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Parameterized.ContinuousProcessProperties

/-!
# The annealed law of a parameterized continuous-path process

For a measurably parameterized family of semigroups with quenched continuous-path process
`Q : Kernel (Theta × alpha) (ContinuousPath alpha)` and a law `mu` on the parameter space, the
**annealed process** is the kernel from the starting state to path space obtained by averaging
the parameter,

  `annealedProcess P hP mu x = ∫ Q (theta, x) mu(dtheta)`

(`annealedProcess_apply`, as a `Measure.bind`).  This file records the facts a consumer needs to
pass between quenched and annealed expectations: the annealed process is a Markov kernel when
`mu` is a probability law; annealed expectations are the `mu`-averages of quenched expectations
(`lintegral_annealedProcess`, `integral_annealedProcess`); and the annealed finite-dimensional
distributions and starting law are the averages of the quenched ones
(`annealedProcess_map_finiteEvaluation_apply`, `annealedProcess_map_eval_zero`).

The annealed process is in general not Markov in the probabilistic sense (the averaged law does
not have the Markov property); nothing of that kind is claimed.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace MarkovProcess.ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)
variable (mu : Measure Theta) [SFinite mu]

/-- The annealed continuous-path process: the parameterized process with its parameter averaged
over the law `mu`, as a kernel from the starting state to path space. -/
noncomputable def IsConservative.annealedProcess : Kernel alpha (ContinuousPath alpha) :=
  (IsConservative.continuousProcess P hP).comp (Kernel.const alpha mu ×ₖ Kernel.id)

omit [SFinite mu] in
/-- Freezing the starting state, the quenched law is a measurable function of the parameter. -/
theorem IsConservative.measurable_continuousProcess_prodMk (x : alpha) :
    Measurable fun theta ↦ IsConservative.continuousProcess P hP (theta, x) :=
  (IsConservative.continuousProcess P hP).measurable.comp (measurable_id.prodMk measurable_const)

/-- The annealed law at a starting point is the `mu`-average of the quenched laws. -/
theorem IsConservative.annealedProcess_apply (x : alpha) :
    IsConservative.annealedProcess P hP mu x =
      mu.bind (fun theta ↦ IsConservative.continuousProcess P hP (theta, x)) := by
  rw [IsConservative.annealedProcess, Kernel.comp_apply, Kernel.prod_apply, Kernel.const_apply,
    Kernel.id_apply, Measure.prod_dirac]
  have hpm : Measurable fun theta : Theta ↦ (theta, x) := measurable_prodMk_right
  refine Measure.ext fun s hs ↦ ?_
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.bind_apply hs (IsConservative.measurable_continuousProcess_prodMk P hP x).aemeasurable,
    lintegral_map ((IsConservative.continuousProcess P hP).measurable_coe hs) hpm]

/-- For a probability law on the parameters, the annealed process is a Markov kernel. -/
instance isMarkovKernel_annealedProcess [IsProbabilityMeasure mu] :
    IsMarkovKernel (IsConservative.annealedProcess P hP mu) := by
  unfold IsConservative.annealedProcess
  infer_instance

/-- Annealed expectations of nonnegative extended functionals are the averages of the quenched
expectations. -/
theorem IsConservative.lintegral_annealedProcess (x : alpha) {g : ContinuousPath alpha → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ omega, g omega ∂(IsConservative.annealedProcess P hP mu x) =
      ∫⁻ theta, ∫⁻ omega, g omega ∂(IsConservative.continuousProcess P hP (theta, x)) ∂mu := by
  rw [IsConservative.annealedProcess_apply,
    Measure.lintegral_bind (IsConservative.measurable_continuousProcess_prodMk P hP x).aemeasurable
      hg.aemeasurable]

/-- Annealed expectations of bounded strongly measurable functionals are the averages of the
quenched expectations: `∫ F d(annealed x) = ∫ (∫ F dQ(theta, x)) mu(dtheta)`. -/
theorem IsConservative.integral_annealedProcess [IsProbabilityMeasure mu] (x : alpha)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ContinuousPath alpha → E)
    (hF : StronglyMeasurable F) (C : ℝ)
    (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ∫ omega, F omega ∂(IsConservative.annealedProcess P hP mu x) =
      ∫ theta, ∫ omega, F omega ∂(IsConservative.continuousProcess P hP (theta, x)) ∂mu := by
  have hint : Integrable F (IsConservative.annealedProcess P hP mu x) :=
    Integrable.of_bound hF.aestronglyMeasurable C (Eventually.of_forall hFC)
  have hG : StronglyMeasurable fun p : Theta × alpha ↦
      ∫ omega, F omega ∂(IsConservative.continuousProcess P hP p) :=
    hF.integral_kernel (κ := IsConservative.continuousProcess P hP)
  have hpm : Measurable fun theta : Theta ↦ (theta, x) := measurable_prodMk_right
  rw [IsConservative.annealedProcess] at hint ⊢
  rw [Kernel.integral_comp hint, Kernel.prod_apply, Kernel.const_apply, Kernel.id_apply,
    Measure.prod_dirac, integral_map hpm.aemeasurable hG.aestronglyMeasurable]

variable [LocallyCompactSpace alpha]

/-- The annealed finite-dimensional distributions are the `mu`-averages of the quenched ones:
on every measurable set `s` of the coordinate space, the annealed law of the coordinates at `I`
is the average over the parameter of the finite-set kernels of the semigroups. -/
theorem IsConservative.annealedProcess_map_finiteEvaluation_apply
    (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) (x : alpha) (I : Finset NNReal) {s : Set (I → alpha)}
    (hs : MeasurableSet s) :
    (IsConservative.annealedProcess P hP mu x).map (ContinuousPath.finsetEvaluation I) s =
      ∫⁻ theta, SubMarkovKernelSemigroup.finiteSetKernel (P.toSubMarkovKernelSemigroup theta) I x s
        ∂mu := by
  have hphi : Measurable (ContinuousPath.finsetEvaluation (alpha := alpha) I) :=
    ContinuousPath.measurable_finsetEvaluation I
  rw [Measure.map_apply hphi hs, IsConservative.annealedProcess_apply,
    Measure.bind_apply (hphi hs) (IsConservative.measurable_continuousProcess_prodMk P hP
        x).aemeasurable]
  refine lintegral_congr fun theta ↦ ?_
  rw [← Measure.map_apply hphi hs,
    IsConservative.continuousProcess_map_finiteEvaluation P hP hFeller hK theta x I]

omit [LocallyCompactSpace alpha] in
/-- The annealed process starts where it is told: for a probability law on the parameters, the
time-zero coordinate has law the Dirac measure at the starting point. -/
theorem IsConservative.annealedProcess_map_eval_zero [IsProbabilityMeasure mu]
    (hK : P.KolmogorovRegular hP) (x : alpha) :
    (IsConservative.annealedProcess P hP mu x).map (fun omega ↦ omega 0) = Measure.dirac x := by
  have hmeas0 : Measurable (fun omega : ContinuousPath alpha ↦ omega 0) :=
    ContinuousPath.measurable_coordinateProcess (alpha := alpha) 0
  refine Measure.ext fun s hs ↦ ?_
  rw [Measure.map_apply hmeas0 hs, IsConservative.annealedProcess_apply,
    Measure.bind_apply (hmeas0 hs)
      (IsConservative.measurable_continuousProcess_prodMk P hP x).aemeasurable]
  have hfib : ∀ theta, IsConservative.continuousProcess P hP (theta, x)
      ((fun omega : ContinuousPath alpha ↦ omega 0) ⁻¹' s) = Measure.dirac x s := by
    intro theta
    rw [← Measure.map_apply hmeas0 hs, IsConservative.continuousProcess_map_eval_zero P hP hK]
  rw [lintegral_congr hfib, lintegral_const, measure_univ, mul_one]

end MarkovProcess.ParameterizedSubMarkovKernelSemigroup
