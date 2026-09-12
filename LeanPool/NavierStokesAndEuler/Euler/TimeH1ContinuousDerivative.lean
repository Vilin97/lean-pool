/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TerminalTimePrimitive
import LeanPool.NavierStokesAndEuler.Euler.TimeH1PointwiseBounds
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Continuous derivatives upgrade genuine time-H¹ paths to classical paths

If the actual L² derivative has a continuous representative, terminal
integration constructs a C¹ extension agreeing with the original AC path.
Thus the time derivative holds at every interior time and within the closed
interval at both endpoints.
-/

@[expose] public section


noncomputable section

namespace EulerTimeH1ContinuousDerivative

open Set MeasureTheory EulerTimeLp EulerTerminalTimePrimitive EulerTimeH1PointwiseBounds
  EulerVolterraConvolution
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Integrating the genuine continuous derivative after clamping time. -/
def continuousIntegral (T : ℝ) (hT : 0 ≤ T) (q : C(Icc (0 : ℝ) T, E)) (t : ℝ) : E :=
  ∫ r in T..t, extendPath T hT q r

/-- This concrete integral has the prescribed derivative everywhere. -/
theorem continuousIntegral_hasDerivAt (T : ℝ) (hT : 0 ≤ T)
    (q : C(Icc (0 : ℝ) T, E)) (t : ℝ) :
    HasDerivAt (continuousIntegral T hT q) (extendPath T hT q t) t := by
  have hq := extendPath_continuous T hT q
  exact intervalIntegral.integral_hasDerivAt_right (hq.intervalIntegrable T t)
    hq.aestronglyMeasurable.stronglyMeasurableAtFilter hq.continuousAt

/-- The concrete integral is C¹ as a map on the real line. -/
theorem continuousIntegral_contDiff (T : ℝ) (hT : 0 ≤ T) (q : C(Icc (0 : ℝ) T, E)) :
    ContDiff ℝ 1 (continuousIntegral T hT q) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (continuousIntegral_hasDerivAt T hT q t).differentiableAt, ?_⟩
  have heq : deriv (continuousIntegral T hT q) = extendPath T hT q :=
    funext (fun t => (continuousIntegral_hasDerivAt T hT q t).deriv)
  exact heq.symm ▸ extendPath_continuous T hT q

/-- The continuous integral is the actual terminal primitive of its L² representative. -/
theorem continuousIntegral_eq_realPrimitive (T : ℝ) (hT : 0 ≤ T)
    (q : TimeLp T E) (qC : C(Icc (0 : ℝ) T, E))
    (hq : (q : ℝ → E) =ᵐ[timeMeasure T] extendPath T hT qC)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    continuousIntegral T hT qC t = realPrimitive T q t := by
  have hac : AbsolutelyContinuousOnInterval (continuousIntegral T hT qC) 0 T :=
    (continuousIntegral_contDiff T hT qC).contDiffOn.absolutelyContinuousOnInterval
  have hd : ∀ᵐ r ∂timeMeasure T, HasDerivAt (continuousIntegral T hT qC) (q r) r := by
    filter_upwards [hq] with r hr
    exact (continuousIntegral_hasDerivAt T hT qC r).congr_deriv hr.symm
  exact eq_realPrimitive_of_ac_hasDerivAt_ae T hT q (continuousIntegral T hT qC) hac hd
    (by simp only [continuousIntegral, intervalIntegral.integral_same]) t ht

/-- A genuine H¹ path agrees with a concrete C¹ extension when its actual
L² derivative has a continuous representative. -/
theorem eq_continuousIntegral_add_terminal (T : ℝ) (hT : 0 ≤ T)
    (q : TimeLp T E) (qC : C(Icc (0 : ℝ) T, E))
    (hq : (q : ℝ → E) =ᵐ[timeMeasure T] extendPath T hT qC)
    (η : ℝ → E) (hη : AbsolutelyContinuousOnInterval η 0 T)
    (hder : ∀ᵐ r ∂timeMeasure T, HasDerivAt η (q r) r)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    η t = continuousIntegral T hT qC t + η T :=
  (eq_primitive_add_terminal T hT q η hη hder t ht).trans
    (congrArg (fun z : E => z+η T) (continuousIntegral_eq_realPrimitive T hT q qC hq t ht).symm)

/-- The actual derivative is classical throughout the closed time interval,
interpreting endpoint derivatives within that interval. -/
theorem hasDerivWithinAt_of_continuous_representative (T : ℝ) (hT : 0 ≤ T)
    (q : TimeLp T E) (qC : C(Icc (0 : ℝ) T, E))
    (hq : (q : ℝ → E) =ᵐ[timeMeasure T] extendPath T hT qC)
    (η : ℝ → E) (hη : AbsolutelyContinuousOnInterval η 0 T)
    (hder : ∀ᵐ r ∂timeMeasure T, HasDerivAt η (q r) r)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt η (qC t) (Icc (0 : ℝ) T) t := by
  have h : HasDerivWithinAt (fun r => continuousIntegral T hT qC r+η T)
      (extendPath T hT qC t) (Icc (0 : ℝ) T) t :=
    ((continuousIntegral_hasDerivAt T hT qC t).add_const (η T)).hasDerivWithinAt
  have h' := h.congr_of_mem
    (fun r hr => eq_continuousIntegral_add_terminal T hT q qC hq η hη hder r hr) t.property
  simpa only [extendPath, projIcc_of_mem hT t.property] using h'

/-- At every interior time the actual AC path has an ordinary two-sided derivative. -/
theorem hasDerivAt_of_continuous_representative (T : ℝ) (hT : 0 ≤ T)
    (q : TimeLp T E) (qC : C(Icc (0 : ℝ) T, E))
    (hq : (q : ℝ → E) =ᵐ[timeMeasure T] extendPath T hT qC)
    (η : ℝ → E) (hη : AbsolutelyContinuousOnInterval η 0 T)
    (hder : ∀ᵐ r ∂timeMeasure T, HasDerivAt η (q r) r)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt η (qC ⟨t, ht.1.le, ht.2.le⟩) t :=
  (hasDerivWithinAt_of_continuous_representative T hT q qC hq η hη hder
    ⟨t, ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end EulerTimeH1ContinuousDerivative
