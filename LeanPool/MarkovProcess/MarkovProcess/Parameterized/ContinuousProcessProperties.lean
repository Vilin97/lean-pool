/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Parameterized.ContinuousProcess


/-!
# Properties of the parameterized continuous-path process

Every property of the continuous-path process of a single semigroup, as exposed in
`MarkovProcess/Main.lean`, restated for the measurably parameterized process
`ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess P hP` at a point
`(theta, x)` of the parameter-and-state space.  The hypotheses are the fibrewise ones: fibrewise
conservativity `hP`, fibrewise Feller property `hFeller` where the single-semigroup statement needs
it, and fibrewise Kolmogorov regularity `hK`.

Every proof is a transport through the exact fibre identity
`IsConservative.continuousProcess_apply`; consumers never need that identity themselves.  The
restarted kernels are written as the parameterized kernel composed with the map
`omega ↦ (theta, omega (T omega))`, so that the parameter is carried along the restart.

Main statements: `continuousProcess_map_eval`, `continuousProcess_map_eval_zero` (and its kernel
form `continuousProcess_map_eval_zero'`), `continuousProcess_map_finiteEvaluation`,
`continuousProcess_map_finiteEvaluation_denseTime`, `continuousProcess_map_shift`,
`continuousProcess_restrict_map_shift`, `continuousProcess_restrict_map_shift_stoppingTime`,
`continuousProcess_condExp_shift`, `continuousProcess_condExp_shift_stoppingTime`,
`continuousProcess_condExp_shift_countableStoppingTime`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]

/-- Evaluation of a continuous path at a finite set of times is measurable. -/
theorem measurable_finsetEvaluation (I : Finset NNReal) :
    Measurable (finsetEvaluation (alpha := alpha) I) := by
  rw [measurable_pi_iff]
  intro t
  exact measurable_coordinateProcess (alpha := alpha) (t : NNReal)

end ContinuousPath

namespace ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)

section Fibre

/-- Freezing the parameter of the parameterized process, as a function of the starting state, is
the process of that parameter's semigroup. -/
theorem IsConservative.continuousProcess_comp_prodMk (theta : Theta) :
    (fun x ↦ IsConservative.continuousProcess P hP (theta, x)) =
      SubMarkovKernelSemigroup.IsConservative.continuousProcess
        (P.toSubMarkovKernelSemigroup theta) (hP theta) := by
  funext x
  exact IsConservative.continuousProcess_apply P hP theta x

omit [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha] in
/-- The map `omega ↦ (theta, omega s)` carrying the parameter along the state at time `s` is
measurable. -/
theorem measurable_prodMk_coordinateProcess (theta : Theta) (s : NNReal) :
    Measurable (fun omega : ContinuousPath alpha ↦ (theta, omega s)) :=
  measurable_const.prodMk (ContinuousPath.measurable_coordinateProcess (alpha := alpha) s)

omit [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha] in
/-- The map `omega ↦ (theta, omega (T omega))` carrying the parameter along the state at a finite
stopping time `T` is measurable. -/
theorem measurable_prodMk_eval_stoppingTime (theta : Theta) (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal))) :
    Measurable (fun omega : ContinuousPath alpha ↦ (theta, omega (T omega))) :=
  measurable_const.prodMk (ContinuousPath.measurable_eval_stoppingTime_borel T hT)

end Fibre

section Marginals

/-- One-time marginal at a rational time: the law of `omega (r)` under the parameterized process
at `(theta, x)` is the transition measure of the semigroup at `theta`. -/
theorem IsConservative.continuousProcess_map_eval (hK : P.KolmogorovRegular hP)
    (theta : Theta) (x : alpha) (r : DenseTime) :
    (IsConservative.continuousProcess P hP (theta, x)).map
        (fun omega ↦ omega (DenseTime.castOrderEmbedding r)) =
      (P.toSubMarkovKernelSemigroup theta) (DenseTime.castOrderEmbedding r) x := by
  have hmeas : Measurable (fun omega : ContinuousPath alpha ↦
      omega (DenseTime.castOrderEmbedding r)) :=
    ContinuousPath.measurable_coordinateProcess (alpha := alpha) _
  rw [IsConservative.continuousProcess_apply, ← Kernel.map_apply _ hmeas,
    SubMarkovKernelSemigroup.IsConservative.continuousProcess_map_eval _ _ (hK theta)]

/-- The parameterized process starts where it is told: at `(theta, x)` the time-zero coordinate
has law the Dirac measure at `x`. -/
theorem IsConservative.continuousProcess_map_eval_zero (hK : P.KolmogorovRegular hP)
    (theta : Theta) (x : alpha) :
    (IsConservative.continuousProcess P hP (theta, x)).map (fun omega ↦ omega 0) =
      Measure.dirac x := by
  have hmeas : Measurable (fun omega : ContinuousPath alpha ↦ omega 0) :=
    ContinuousPath.measurable_coordinateProcess (alpha := alpha) 0
  rw [IsConservative.continuousProcess_apply, ← Kernel.map_apply _ hmeas,
    SubMarkovKernelSemigroup.IsConservative.continuousProcess_map_eval_zero _ _ (hK theta),
    Kernel.id_apply]

/-- Kernel form of the starting law: the time-zero coordinate of the parameterized process is the
deterministic kernel projecting `(theta, x)` to `x`. -/
theorem IsConservative.continuousProcess_map_eval_zero' (hK : P.KolmogorovRegular hP) :
    (IsConservative.continuousProcess P hP).map (fun omega ↦ omega 0) =
      Kernel.deterministic Prod.snd measurable_snd := by
  have hmeas : Measurable (fun omega : ContinuousPath alpha ↦ omega 0) :=
    ContinuousPath.measurable_coordinateProcess (alpha := alpha) 0
  refine Kernel.ext fun p ↦ ?_
  rw [Kernel.map_apply _ hmeas, Kernel.deterministic_apply]
  exact IsConservative.continuousProcess_map_eval_zero P hP hK p.1 p.2

/-- Finite-dimensional distributions at rational times, without any Feller hypothesis. -/
theorem IsConservative.continuousProcess_map_finiteEvaluation_denseTime
    (hK : P.KolmogorovRegular hP) (theta : Theta) (x : alpha) (I : Finset DenseTime) :
    (IsConservative.continuousProcess P hP (theta, x)).map
        (ContinuousPath.finsetEvaluation (SubMarkovKernelSemigroup.denseTimePhysicalSet I)) =
      SubMarkovKernelSemigroup.finiteSetKernel (P.toSubMarkovKernelSemigroup theta)
        (SubMarkovKernelSemigroup.denseTimePhysicalSet I) x := by
  rw [IsConservative.continuousProcess_apply,
    ← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation _),
    SubMarkovKernelSemigroup.IsConservative.continuousProcess_map_finiteEvaluation_denseTime _ _
      (hK theta)]

variable [LocallyCompactSpace alpha]
  (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)

include hFeller

/-- Finite-dimensional distributions at all real times: under the parameterized process at
`(theta, x)`, the law of the coordinates at a finite set `I` of times is the finite-set kernel of
the semigroup at `theta`, started at `x`. -/
theorem IsConservative.continuousProcess_map_finiteEvaluation (hK : P.KolmogorovRegular hP)
    (theta : Theta) (x : alpha) (I : Finset NNReal) :
    (IsConservative.continuousProcess P hP (theta, x)).map (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel (P.toSubMarkovKernelSemigroup theta) I x := by
  rw [IsConservative.continuousProcess_apply,
    ← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation _),
    (hFeller theta).continuousProcess_map_finiteEvaluation _ _ (hK theta)]

/-- Simple Markov property of the parameterized process: shifting by a deterministic time `s`
gives the process at the same parameter, started from the time-`s` state, averaged over the
transition measure of the semigroup at `theta`. -/
theorem IsConservative.continuousProcess_map_shift (hK : P.KolmogorovRegular hP)
    (theta : Theta) (x : alpha) (s : NNReal) :
    (IsConservative.continuousProcess P hP (theta, x)).map (ContinuousPath.shift s) =
      ((P.toSubMarkovKernelSemigroup theta) s x).bind
        (fun y ↦ IsConservative.continuousProcess P hP (theta, y)) := by
  rw [IsConservative.continuousProcess_apply,
    ← Kernel.map_apply _ (ContinuousPath.measurable_shift_fixed s),
    (hFeller theta).continuousProcess_map_shift _ _ (hK theta) s, Kernel.comp_apply,
    IsConservative.continuousProcess_comp_prodMk]

/-- Restart at a deterministic time: after restriction to an event of the canonical filtration at
time `s`, the law of the shifted path is the parameterized process at the same parameter started
from the time-`s` state. -/
theorem IsConservative.continuousProcess_restrict_map_shift (hK : P.KolmogorovRegular hP)
    (theta : Theta) (x : alpha) (s : NNReal) (A : Set (ContinuousPath alpha))
    (hA : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := alpha) s] A) :
    ((IsConservative.continuousProcess P hP (theta, x)).restrict A).map
        (ContinuousPath.shift s) =
      Kernel.comap (IsConservative.continuousProcess P hP) (fun omega ↦ (theta, omega s))
          (measurable_prodMk_coordinateProcess theta s)
        ∘ₘ ((IsConservative.continuousProcess P hP (theta, x)).restrict A) := by
  have h := (hFeller theta).continuousProcess_restrict_map_shift _ _ (hK theta) x s A hA
  rw [IsConservative.continuousProcess_apply]
  refine h.trans (congrArg (Measure.bind _) ?_)
  funext omega
  exact (IsConservative.continuousProcess_apply P hP theta (omega s)).symm

/-- Strong Markov property at a finite stopping time, in restart form: after restriction to an
event of the stopped sigma-algebra, the law of the path shifted at the stopping time is the
parameterized process at the same parameter started from the state at that time. -/
theorem IsConservative.continuousProcess_restrict_map_shift_stoppingTime
    (hK : P.KolmogorovRegular hP) (theta : Theta) (x : alpha)
    (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    (A : Set (ContinuousPath alpha)) (hA : MeasurableSet[hT.measurableSpace] A) :
    ((IsConservative.continuousProcess P hP (theta, x)).restrict A).map
        (fun omega ↦ ContinuousPath.shift (T omega) omega) =
      Kernel.comap (IsConservative.continuousProcess P hP)
          (fun omega ↦ (theta, omega (T omega)))
          (measurable_prodMk_eval_stoppingTime theta T hT)
        ∘ₘ ((IsConservative.continuousProcess P hP (theta, x)).restrict A) := by
  have h := (hFeller theta).continuousProcess_restrict_map_shift_stoppingTime _ _ (hK theta) x T
    hT A hA
  rw [IsConservative.continuousProcess_apply]
  refine h.trans (congrArg (Measure.bind _) ?_)
  funext omega
  exact (IsConservative.continuousProcess_apply P hP theta (omega (T omega))).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/-- Simple Markov property in conditional-expectation form: given the canonical filtration at a
deterministic time `s`, the conditional expectation of a bounded functional of the shifted path is
its expectation under the parameterized process at the same parameter, started from the current
state. -/
theorem IsConservative.continuousProcess_condExp_shift (hK : P.KolmogorovRegular hP)
    (theta : Theta) (x : alpha) (s : NNReal) (F : ContinuousPath alpha → E)
    (hF : StronglyMeasurable F) (C : ℝ) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    (IsConservative.continuousProcess P hP (theta, x))[fun omega ↦
        F (ContinuousPath.shift s omega)|ContinuousPath.canonicalFiltration (alpha := alpha) s]
      =ᵐ[IsConservative.continuousProcess P hP (theta, x)]
      fun omega ↦ ∫ eta, F eta ∂IsConservative.continuousProcess P hP (theta, omega s) := by
  have h := (hFeller theta).continuousProcess_condExp_shift _ _ (hK theta) x s F hF C hFC
  rw [← IsConservative.continuousProcess_apply P hP theta x,
    ← IsConservative.continuousProcess_comp_prodMk P hP theta] at h
  exact h

/-- Strong Markov property in conditional-expectation form at a finite stopping time: given the
stopped sigma-algebra, the conditional expectation of a bounded functional of the path shifted at
the stopping time is its expectation under the parameterized process at the same parameter,
started from the state at the stopping time. -/
theorem IsConservative.continuousProcess_condExp_shift_stoppingTime (hK : P.KolmogorovRegular hP)
    (theta : Theta) (x : alpha) (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : ℝ) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    (IsConservative.continuousProcess P hP (theta, x))[fun omega ↦
        F (ContinuousPath.shift (T omega) omega)|hT.measurableSpace]
      =ᵐ[IsConservative.continuousProcess P hP (theta, x)]
      fun omega ↦ ∫ eta, F eta ∂IsConservative.continuousProcess P hP (theta, omega (T omega)) := by
  have h := (hFeller theta).continuousProcess_condExp_shift_stoppingTime _ _ (hK theta) x T hT F
    hF C hFC
  rw [← IsConservative.continuousProcess_apply P hP theta x,
    ← IsConservative.continuousProcess_comp_prodMk P hP theta] at h
  exact h

/-- Strong Markov property at a finite stopping time with countable range, in
conditional-expectation form, for the parameterized process. -/
theorem IsConservative.continuousProcess_condExp_shift_countableStoppingTime
    (hK : P.KolmogorovRegular hP) (theta : Theta) (x : alpha)
    (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    (hTrange : (Set.range T).Countable)
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : ℝ) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    (IsConservative.continuousProcess P hP (theta, x))[fun omega ↦
        F (ContinuousPath.shift (T omega) omega)|hT.measurableSpace]
      =ᵐ[IsConservative.continuousProcess P hP (theta, x)]
      fun omega ↦ ∫ eta, F eta ∂IsConservative.continuousProcess P hP (theta, omega (T omega)) := by
  have h := (hFeller theta).continuousProcess_condExp_shift_countableStoppingTime _ _ (hK theta)
    x T hT hTrange F hF C hFC
  rw [← IsConservative.continuousProcess_apply P hP theta x,
    ← IsConservative.continuousProcess_comp_prodMk P hP theta] at h
  exact h

end Marginals

end ParameterizedSubMarkovKernelSemigroup

end MarkovProcess
