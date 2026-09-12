/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryOperator
public import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientTime
public import LeanPool.NavierStokesAndEuler.Euler.MeanFixedTranslation
public import LeanPool.NavierStokesAndEuler.Euler.SmoothCoefficientPath
import LeanPool.NavierStokesAndEuler.Euler.MeanTranslatedInverse
import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryFrechet
import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPathJets
import LeanPool.NavierStokesAndEuler.Euler.MeanConcreteTranslation
import LeanPool.NavierStokesAndEuler.Euler.MeanFixedCoefficientRegularity

/-!
# Spatial regularity of the actual source mean operator

All coefficient families here are formed from literal bounded smooth matrix
fields and smooth compact cutoffs. Their operator regularity is proved by
those constructions and then passed through the genuine fixed mean inverse.
-/

@[expose] public section


noncomputable section

namespace EulerMeanSourceOperatorRegularity

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
    EulerMeanCoefficients
  EulerMeanBoundary EulerMeanOperatorTranslation EulerMeanTimeTranslation EulerMeanFixedTranslation
  EulerMeanFixedCoefficientRegularity EulerMeanFixedSpaceInverse EulerMeanTranslatedInverse
  EulerTimeLp EulerCoerciveProjection
open scoped ContDiff

-- Reuse the nested Hilbert-space instances before forming operator families.
/-- Cache the standard `NormedAddCommGroup solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanSourceOperatorRegularity1 : NormedAddCommGroup solenoidalSpace :=
    inferInstance
/-- Cache the standard `InnerProductSpace ℝ solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanSourceOperatorRegularity2 : InnerProductSpace ℝ solenoidalSpace :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (TimeLp T L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanSourceOperatorRegularity3 (T : ℝ) : NormedAddCommGroup (TimeLp T L2) :=
    inferInstance
/-- Cache the standard `InnerProductSpace ℝ (TimeLp T L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanSourceOperatorRegularity4 (T : ℝ) : InnerProductSpace ℝ (TimeLp T L2) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (TimeLp T solenoidalSpace)` instance to shorten
typeclass synthesis. -/
local instance instMeanSourceOperatorRegularity5 (T : ℝ) : NormedAddCommGroup (TimeLp T
    solenoidalSpace) := inferInstance
/-- Cache the standard `InnerProductSpace ℝ (TimeLp T solenoidalSpace)` instance to shorten
typeclass synthesis. -/
local instance instMeanSourceOperatorRegularity6 (T : ℝ) : InnerProductSpace ℝ (TimeLp T
    solenoidalSpace) := inferInstance

variable (T : ℝ) (hT : 0 ≤ T)
  (F F₁ H : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (M0 : BoundedSmoothField (Space →L[ℝ] Space)) (χ : Cutoff) (L : ℝ)

/-- The entire translated source mean operator is genuinely smooth in the spatial shift. -/
theorem translatedSourceOperator_contDiff :
    ContDiff ℝ ∞ (fun a : Space => translatedMeanOperator T hT a
      (operatorPath T F.field) (operatorPath T F₁.field) (operatorPath T H.field)
      (multiplier M0.field) (boundaryOperator χ) L) := by
  have hA : ContDiff ℝ ∞ (fun a : Space => boundaryOperator (χ.translate a)) :=
    mixedBoundaryOperator_contDiff χ χ
  have h := contDiff_fixedMeanOperator T hT
    (fun a => operatorPath T (translatedPath T F.field a))
    (fun a => operatorPath T (translatedPath T F₁.field a))
    (fun a => operatorPath T (translatedPath T H.field a))
    (fun a => multiplier (translated M0.field a))
    (fun a => boundaryOperator (χ.translate a)) L
    (operatorPathTranslation_contDiff T F) (operatorPathTranslation_contDiff T F₁)
    (operatorPathTranslation_contDiff T H) (multiplierTranslation_contDiff M0) hA
  simpa only [translatedMeanOperator, translatePath_operatorPath,
    translateOperator_multiplier, translateOperator_boundary] using h

/-- The translated primitive in the forcing term is a genuinely smooth operator family. -/
theorem translatedSourcePrimitive_contDiff :
    ContDiff ℝ ∞ (fun a : Space => translatedMeanPrimitive T hT a
      (operatorPath T F.field) (operatorPath T F₁.field)) := by
  have h := contDiff_fixedMeanPrimitive T hT
    (fun a => operatorPath T (translatedPath T F.field a))
    (fun a => operatorPath T (translatedPath T F₁.field a))
    (operatorPathTranslation_contDiff T F) (operatorPathTranslation_contDiff T F₁)
  simpa only [translatedMeanPrimitive, translatePath_operatorPath] using h

/-- The actual source inverse has a smooth spatial orbit when the given forcing does.
The coercivity certificate is supplied by the already proved source boundary estimate. -/
theorem sourceSolution_translation_contDiff (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ v, c * ‖v‖ ^ 2 ≤
      ⟪fixedMeanOperator T hT (operatorPath T F.field) (operatorPath T F₁.field)
        (operatorPath T H.field) (multiplier M0.field) (boundaryOperator χ) L v,
   v⟫_ℝ)
    (f : TimeLp T L2) (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f)) :
    ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a
      (coerciveInverse (fixedMeanOperator T hT (operatorPath T F.field) (operatorPath T F₁.field)
        (operatorPath T H.field) (multiplier M0.field) (boundaryOperator χ) L) c hc hcoercive
          (-(fixedMeanPrimitive T hT (operatorPath T F.field) (operatorPath T F₁.field)).adjoint
              f))) :=
  solution_translation_contDiff T hT (operatorPath T F.field) (operatorPath T F₁.field)
    (operatorPath T H.field) (multiplier M0.field) (boundaryOperator χ) L c hc hcoercive f
    (translatedSourceOperator_contDiff T hT F F₁ H M0 χ L)
    (translatedSourcePrimitive_contDiff T hT F F₁) hf

end EulerMeanSourceOperatorRegularity
