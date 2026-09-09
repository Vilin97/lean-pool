/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderPressureField
public import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarTime

@[expose] public section

/-! The literal pressure integral is the genuine jointly continuous scalar path representative. -/

noncomputable section

namespace EulerSourceCylinderClassical

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerSourceCylinderEquation EulerCylinderScalarPrimitive EulerCylinderAngleAverage
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
  (hf₀ : ∀ t, average P (f t : CylinderL2 P Space) = 0)
  (ha₀zero : average P (a₀ : CylinderL2 P U) = 0)

theorem pressureField_eq_pointField (t : Icc (0 : ℝ) T) :
    pressureField P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm hf₀ ha₀zero t =
      scalarPointField P (pressurePath P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm)
        (pressurePath_contDiff P S hS T hT Q Q₁ c hc hQ f a₀ M m cm hcm hm hSc hf ha₀) t :=
  (scalarPointField_eq P _ _ t _
    (pressureField_continuous P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm hf₀ ha₀zero t)
    (pressureField_ae P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm hf₀ ha₀zero t)).symm

theorem pressureField_joint_continuous :
    Continuous (fun z : Icc (0 : ℝ) T × LiftDomain P =>
      pressureField P S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ M m cm hcm hm hf₀ ha₀zero z.1 z.2) :=
        by
  simp_rw [pressureField_eq_pointField]
  exact scalarPointField_joint_continuous P _ _

end EulerSourceCylinderClassical
