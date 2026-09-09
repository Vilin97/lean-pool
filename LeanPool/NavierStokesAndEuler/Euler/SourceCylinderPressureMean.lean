/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderMeanZero
public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderPressureSource
public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderClassicalEquation
public import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarAverage

@[expose] public section

/-!
# The solved normal pressure source has zero angular mean

The zero mode is proved for the actual Duhamel solution and then transferred
to its continuous scalar representative. No zero-mean condition on the
solution or on its pressure residual is assumed.
-/

noncomputable section

namespace EulerSourceCylinderEquation

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerLpCylinderRectangular EulerSourceNormalCoefficient EulerCylinderAngleAverage
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (S : Set Space) (hS : MeasurableSet S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] Space))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c*‖v‖^2 ≤ ‖Q.field t x v‖^2)
  (f : C(Icc (0 : ℝ) T,Supported P Space S hS)) (a₀ : Supported P U S hS)
  (M : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (m : SmoothCoefficientPath (Icc (0 : ℝ) T) Space)
  (cm : ℝ) (hcm : 0 < cm) (hm : ∀ t x, cm ≤ ‖m.field t x‖^2)

theorem pressureSource_average_zero
    (hf₀ : ∀ t, average P (f t : CylinderL2 P Space) = 0)
    (ha₀ : average P (a₀ : CylinderL2 P U) = 0) (t : Icc (0 : ℝ) T) :
    average P (pressureSource P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm t :
      CylinderL2 P ℝ) = 0 := by
  change average P (fullOperatorMap P (normalFunctional m cm hcm hm t)
    ((f t : CylinderL2 P Space) - (2 : ℝ) • fullOperatorMap P (M.field t)
      (velocity P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P Space))) = 0
  rw [average_fullOperator, map_sub, map_smul, average_fullOperator,
    velocity_average_zero P S hS T hT Q Q₁ c hc hQ f a₀ hf₀ ha₀ t,
    hf₀ t, map_zero, smul_zero, sub_self, map_zero]

theorem pressureSource_slice_contDiff (hSc : IsCompact S)
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (includePath P S hS f)))
    (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a (a₀ : CylinderL2 P U)))
    (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun a : LiftTangent => translate P a
      (pressureSource P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm t : CylinderL2 P ℝ)) := by
  exact (ContinuousMap.evalCLM ℝ t : C(Icc (0 : ℝ) T,CylinderL2 P ℝ) →L[ℝ]
    CylinderL2 P ℝ).contDiff.comp
      (pressureSource_contDiff P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm hSc hf ha₀)

end EulerSourceCylinderEquation

namespace EulerSourceCylinderClassical

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerSourceCylinderEquation EulerCylinderSmoothOrbit EulerCylinderAngleAverage
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (S : Set Space) (hS : MeasurableSet S) (hSc : IsCompact S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] Space))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c*‖v‖^2 ≤ ‖Q.field t x v‖^2)
  (f : C(Icc (0 : ℝ) T,Supported P Space S hS)) (a₀ : Supported P U S hS)
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (includePath P S hS f)))
  (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a (a₀ : CylinderL2 P U)))
  (M : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (m : SmoothCoefficientPath (Icc (0 : ℝ) T) Space)
  (cm : ℝ) (hcm : 0 < cm) (hm : ∀ t x, cm ≤ ‖m.field t x‖^2)

omit [Fact (0 < P)] in
include hcm hm in
theorem normal_ne_zero_of_lower (t : Icc (0 : ℝ) T) (x : Space) :
    m.field t x ≠ 0 := by
  intro he
  have h := hm t x
  rw [he, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
  exact (not_le_of_gt hcm) h

/-- The actual scalar L² class represents the literal normal quotient. -/
theorem pressureSource_ae_normalResidual (t : Icc (0 : ℝ) T) :
    (pressureSource P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm t : CylinderL2 P ℝ) =ᵐ[liftMeasure
      P]
      normalResidual P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m t := by
  filter_upwards [pressureSource_ae P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm t,
    field_ae P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t,
    pointField_ae P (includePath P S hS f) hf t] with x hs hv hforce
  change (f t : CylinderL2 P Space) x = pointField P (includePath P S hS f) hf t x at hforce
  rw [hs, hv, hforce]
  rfl

include hcm hm in
/-- Zero mean of the forcing and initial coordinate implies zero mean of the
literal pressure source of the constructed solution. -/
theorem normalResidual_mean_zero
    (hf₀ : ∀ t, average P (f t : CylinderL2 P Space) = 0)
    (ha₀zero : average P (a₀ : CylinderL2 P U) = 0)
    (t : Icc (0 : ℝ) T) (y : Space) :
    (∫ s in (0 : ℝ)..P,
      normalResidual P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m t (y,(s : AddCircle P))) = 0 := by
  exact EulerCylinderScalarPrimitive.scalar_mean_zero P
    (pressureSource P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm t)
    (pressureSource_slice_contDiff P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm hSc hf ha₀ t)
    (normalResidual P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m t)
    (normalResidual_continuous P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m
      (normal_ne_zero_of_lower T m cm hcm hm) t)
    (pressureSource_ae_normalResidual P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm t)
    (pressureSource_average_zero P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm hf₀ ha₀zero t) y

end EulerSourceCylinderClassical
