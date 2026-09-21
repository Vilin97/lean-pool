/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.HarmonicRepresentation
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.StoppingLtTop

/-!
# Stopped laws and exit distributions

For the continuous-path process `Q` of a conservative semigroup, this file packages as kernels the
laws that the strong Markov property and the boundary value problems of a domain consume:

* `stoppedLaw T hT : Kernel alpha (NNReal × alpha)`, the joint law of a finite stopping time and
  the position at that time, with its two marginals;
* `exitLawTrunc U hU K : Kernel alpha alpha`, the law of the position at the exit time of an open
  set `U` truncated at the horizon `K`; from a starting point in `U` it lives on the closure of `U`
  (`exitLawTrunc_apply_compl_closure`);
* `exitLaw U hU : Kernel alpha alpha`, the exit distribution (harmonic measure): the law of the
  position at the exit time on the event that the path leaves `U`; its total mass is the exit
  probability, and from a starting point in `U` it lives on the frontier of `U`
  (`exitLaw_apply_compl_frontier`).

The harmonic representation of `Trajectory/HarmonicRepresentation.lean` reads, in these terms,
`∫ f d(exitLawTrunc U hU K x) = f x` whenever `L f = 0` on `U`
(`integral_exitLawTrunc_eq_of_generator_eq_zero`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]

/-- The finite value of a finite exit time, read through `untopD`, is its `toNNReal`. -/
theorem untopD_exitTimeTop_eq_toNNReal (U : Set alpha) (omega : ContinuousPath alpha)
    (h : exitTime U omega ≠ ⊤) :
    (exitTimeTop U omega).untopD 0 = (exitTime U omega).toNNReal := by
  rw [exitTimeTop_apply, ← ENNReal.coe_toNNReal h]
  rfl

variable [MeasurableSpace alpha] [BorelSpace alpha]

/-- The event that a path leaves the open set `U` is measurable. -/
theorem measurableSet_exitTime_lt_top (U : Set alpha) (hU : IsOpen U) :
    MeasurableSet {omega : ContinuousPath alpha | exitTime U omega < ⊤} :=
  measurableSet_lt (measurable_exitTime U hU) measurable_const

/-- The pair of a finite stopping time and the position at that time is measurable. -/
theorem measurable_prodMk_stoppingTime (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal))) :
    Measurable fun omega : ContinuousPath alpha ↦ (T omega, omega (T omega)) :=
  (measurable_of_isStoppingTime T hT).prodMk (measurable_eval_stoppingTime_borel T hT)

/-- The position at the exit time of an open set, on the event that the path leaves it, is
measurable. -/
theorem measurable_eval_untopD_exitTimeTop (U : Set alpha) (hU : IsOpen U) :
    Measurable fun omega : ContinuousPath alpha ↦ omega ((exitTimeTop U omega).untopD 0) :=
  measurable_eval_untopD_stoppingTime _ (isStoppingTime_exitTime U hU)

end ContinuousPath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable {P : SubMarkovKernelSemigroup alpha} (hP : P.IsConservative)

section StoppedLaw

variable (T : ContinuousPath alpha → NNReal)
  (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
    (fun omega ↦ (T omega : WithTop NNReal)))

/-- The stopped law: the joint law of a finite stopping time and the position at that time, as a
kernel from the starting point. -/
noncomputable def IsConservative.stoppedLaw : Kernel alpha (NNReal × alpha) :=
  Kernel.mapOfMeasurable (IsConservative.continuousProcess P hP)
    (fun omega ↦ (T omega, omega (T omega))) (ContinuousPath.measurable_prodMk_stoppingTime T hT)

theorem IsConservative.stoppedLaw_apply (x : alpha) :
    IsConservative.stoppedLaw hP T hT x =
      (IsConservative.continuousProcess P hP x).map (fun omega ↦ (T omega, omega (T omega))) := by
  rw [IsConservative.stoppedLaw, Kernel.mapOfMeasurable_eq_map,
    Kernel.map_apply _ (ContinuousPath.measurable_prodMk_stoppingTime T hT)]

/-- The stopped law is a Markov kernel. -/
instance isMarkovKernel_stoppedLaw : IsMarkovKernel (IsConservative.stoppedLaw hP T hT) := by
  rw [IsConservative.stoppedLaw, Kernel.mapOfMeasurable_eq_map]
  exact Kernel.IsMarkovKernel.map _ (ContinuousPath.measurable_prodMk_stoppingTime T hT)

/-- The first marginal of the stopped law is the law of the stopping time. -/
theorem IsConservative.stoppedLaw_map_fst :
    (IsConservative.stoppedLaw hP T hT).map Prod.fst =
      (IsConservative.continuousProcess P hP).map T := by
  refine Kernel.ext fun x ↦ ?_
  rw [Kernel.map_apply _ measurable_fst, IsConservative.stoppedLaw_apply,
    Measure.map_map measurable_fst (ContinuousPath.measurable_prodMk_stoppingTime T hT),
    Kernel.map_apply _ (ContinuousPath.measurable_of_isStoppingTime T hT)]
  rfl

/-- The second marginal of the stopped law is the law of the stopped position. -/
theorem IsConservative.stoppedLaw_map_snd :
    (IsConservative.stoppedLaw hP T hT).map Prod.snd =
      (IsConservative.continuousProcess P hP).map (fun omega ↦ omega (T omega)) := by
  refine Kernel.ext fun x ↦ ?_
  rw [Kernel.map_apply _ measurable_snd, IsConservative.stoppedLaw_apply,
    Measure.map_map measurable_snd (ContinuousPath.measurable_prodMk_stoppingTime T hT),
    Kernel.map_apply _ (ContinuousPath.measurable_eval_stoppingTime_borel T hT)]
  rfl

end StoppedLaw

section ExitLaw

variable (U : Set alpha) (hU : IsOpen U)

/-- The law of the position at the exit time of `U` truncated at the horizon `K`. -/
noncomputable def IsConservative.exitLawTrunc (K : NNReal) : Kernel alpha alpha :=
  Kernel.mapOfMeasurable (IsConservative.continuousProcess P hP)
    (fun omega ↦ omega (ContinuousPath.exitTimeTrunc U K omega))
    (ContinuousPath.measurable_eval_stoppingTime_borel _
      (ContinuousPath.isStoppingTime_exitTimeTrunc U hU K))

theorem IsConservative.exitLawTrunc_apply (K : NNReal) (x : alpha) :
    IsConservative.exitLawTrunc hP U hU K x =
      (IsConservative.continuousProcess P hP x).map
        (fun omega ↦ omega (ContinuousPath.exitTimeTrunc U K omega)) := by
  rw [IsConservative.exitLawTrunc, Kernel.mapOfMeasurable_eq_map, Kernel.map_apply _
    (ContinuousPath.measurable_eval_stoppingTime_borel _
      (ContinuousPath.isStoppingTime_exitTimeTrunc U hU K))]

/-- The truncated exit law is a Markov kernel. -/
instance isMarkovKernel_exitLawTrunc (K : NNReal) :
    IsMarkovKernel (IsConservative.exitLawTrunc hP U hU K) := by
  rw [IsConservative.exitLawTrunc, Kernel.mapOfMeasurable_eq_map]
  exact Kernel.IsMarkovKernel.map _
    (ContinuousPath.measurable_eval_stoppingTime_borel _
      (ContinuousPath.isStoppingTime_exitTimeTrunc U hU K))

/-- Integrals against the truncated exit law are expectations of the stopped position. -/
theorem IsConservative.integral_exitLawTrunc (K : NNReal) (x : alpha) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : alpha → E) (hf : StronglyMeasurable f) :
    ∫ y, f y ∂(IsConservative.exitLawTrunc hP U hU K x) =
      ∫ omega, f (omega (ContinuousPath.exitTimeTrunc U K omega))
        ∂(IsConservative.continuousProcess P hP x) := by
  rw [IsConservative.exitLawTrunc_apply]
  exact integral_map (ContinuousPath.measurable_eval_stoppingTime_borel _
    (ContinuousPath.isStoppingTime_exitTimeTrunc U hU K)).aemeasurable hf.aestronglyMeasurable

/-- From a starting point in `U`, the truncated exit law lives on the closure of `U`. -/
theorem IsConservative.exitLawTrunc_apply_compl_closure (hK : P.KolmogorovRegular hP)
    (K : NNReal) {x : alpha} (hx : x ∈ U) :
    IsConservative.exitLawTrunc hP U hU K x (closure U)ᶜ = 0 := by
  rw [IsConservative.exitLawTrunc_apply,
    Measure.map_apply (ContinuousPath.measurable_eval_stoppingTime_borel _
      (ContinuousPath.isStoppingTime_exitTimeTrunc U hU K)) isClosed_closure.measurableSet.compl]
  refine measure_mono_null (fun omega homega ↦ ?_) ((ae_iff).mp
    (IsConservative.ae_eval_zero_eq hP hK x))
  intro h0
  exact homega (ContinuousPath.stopped_exitTimeTrunc_mem_closure U hU K omega (h0 ▸ hx))

/-- The exit distribution (harmonic measure) of `U`: the law of the position at the exit time, on
the event that the path leaves `U`. -/
noncomputable def IsConservative.exitLaw : Kernel alpha alpha :=
  ((IsConservative.continuousProcess P hP).restrict
      (ContinuousPath.measurableSet_exitTime_lt_top U hU)).map
    (fun omega ↦ omega ((ContinuousPath.exitTimeTop U omega).untopD 0))

/-- The exit distribution evaluated on a measurable set. -/
theorem IsConservative.exitLaw_apply (x : alpha) {B : Set alpha} (hB : MeasurableSet B) :
    IsConservative.exitLaw hP U hU x B =
      IsConservative.continuousProcess P hP x
        {omega | ContinuousPath.exitTime U omega < ⊤ ∧
          omega ((ContinuousPath.exitTimeTop U omega).untopD 0) ∈ B} := by
  rw [IsConservative.exitLaw,
    Kernel.map_apply' _ (ContinuousPath.measurable_eval_untopD_exitTimeTop U hU) _ hB,
    Kernel.restrict_apply' _ _ _ ((ContinuousPath.measurable_eval_untopD_exitTimeTop U hU) hB)]
  congr 1
  ext omega
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
  exact and_comm

/-- The total mass of the exit distribution is the probability of leaving `U`. -/
theorem IsConservative.exitLaw_apply_univ (x : alpha) :
    IsConservative.exitLaw hP U hU x Set.univ =
      IsConservative.continuousProcess P hP x {omega | ContinuousPath.exitTime U omega < ⊤} := by
  rw [IsConservative.exitLaw_apply hP U hU x MeasurableSet.univ]
  simp only [Set.mem_univ, and_true]

/-- From a starting point in `U`, the exit distribution lives on the frontier of `U`. -/
theorem IsConservative.exitLaw_apply_compl_frontier (hK : P.KolmogorovRegular hP) {x : alpha}
    (hx : x ∈ U) : IsConservative.exitLaw hP U hU x (frontier U)ᶜ = 0 := by
  rw [IsConservative.exitLaw_apply hP U hU x isClosed_frontier.measurableSet.compl]
  refine measure_mono_null (fun omega homega ↦ ?_) ((ae_iff).mp
    (IsConservative.ae_eval_zero_eq hP hK x))
  intro h0
  obtain ⟨hfin, hnot⟩ := homega
  rw [ContinuousPath.untopD_exitTimeTop_eq_toNNReal U omega hfin.ne] at hnot
  exact hnot (ContinuousPath.coordinate_exitTime_mem_frontier U hU omega (h0 ▸ hx) hfin.ne)

variable [LocallyCompactSpace alpha]

/-- **Harmonic representation in kernel form.**  If `L f = 0` on `U`, then `f x` is the integral of
`f` against the truncated exit law from `x`, for every horizon. -/
theorem IsFellerKernelSemigroup.integral_exitLawTrunc_eq_of_generator_eq_zero
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (f : hFeller.c0Semigroup.generatorDomain)
    (hLf : ∀ y ∈ U, (hFeller.c0Semigroup.generator f) y = 0) (K : NNReal) (x : alpha) :
    ∫ y, (f : C₀(alpha, ℝ)) y ∂(IsConservative.exitLawTrunc hP U hU K x) = (f : C₀(alpha, ℝ)) x
        := by
  rw [IsConservative.integral_exitLawTrunc hP U hU K x (fun y ↦ (f : C₀(alpha, ℝ)) y)
    (f : C₀(alpha, ℝ)).continuous.stronglyMeasurable]
  exact hFeller.integral_eval_exitTimeTrunc_eq_of_generator_eq_zero hP hK f U hU hLf K x

end ExitLaw

end SubMarkovKernelSemigroup

end MarkovProcess
