/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderRegularity
public import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeRegularity
public import LeanPool.NavierStokesAndEuler.Euler.CylinderRawSupport

@[expose] public section

/-!
# The solved forward field as an actual smooth cylinder field

The representative is recovered by bounded H3 evaluation of the genuine
L² solution. It is jointly continuous, spatially and angularly smooth,
compactly supported, and has the true pointwise within-time derivative.
-/

noncomputable section

namespace EulerSourceCylinderClassical

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMetricTransport EulerMeanCoefficients EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerSourceCylinderEquation EulerCylinderSmoothOrbit EulerVolterraConvolution
open scoped ContDiff BoundedContinuousFunction

variable (period : ℝ) [Fact (0 < period)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (S : Set Space) (hS : MeasurableSet S) (hSc : IsCompact S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] Space))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c*‖v‖^2 ≤ ‖Q.field t x v‖^2)
  (f : C(Icc (0 : ℝ) T,Supported period Space S hS)) (a₀ : Supported period U S hS)
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS f)))
  (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate period a (a₀ : CylinderL2 period U)))

/-- The actual physical field, reconstructed from the solved L² class. -/
def field (t : Icc (0 : ℝ) T) (x : LiftDomain period) : Space :=
  pointField period (includePath period S hS (velocity period S hS T hT Q Q₁ c hc hQ f a₀))
    (velocity_contDiff period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀) t x

/-- The reconstructed actual product-rule time derivative. -/
def derivativeField (t : Icc (0 : ℝ) T) (x : LiftDomain period) : Space :=
  pointField period (includePath period S hS (velocityDerivative period S hS T hT Q Q₁ c hc hQ f
    a₀))
    (velocityDerivative_contDiff period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀) t x

theorem field_joint_continuous :
    Continuous (fun z : Icc (0 : ℝ) T × LiftDomain period =>
      field period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ z.1 z.2) :=
  pointField_joint_continuous period _ _

theorem field_smooth (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (field period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t) x)
      :=
  pointField_smooth period _ _ t x

theorem derivativeField_smooth (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (derivativeField period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf
      ha₀ t) x) :=
  pointField_smooth period _ _ t x

theorem field_ae (t : Icc (0 : ℝ) T) :
    (velocity period S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 period Space) =ᵐ[liftMeasure period]
      field period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t :=
  pointField_ae period (includePath period S hS (velocity period S hS T hT Q Q₁ c hc hQ f a₀))
    (velocity_contDiff period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀) t

theorem derivativeField_ae (t : Icc (0 : ℝ) T) :
    (velocityDerivative period S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 period Space)
      =ᵐ[liftMeasure period]
      derivativeField period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t :=
  pointField_ae period (includePath period S hS (velocityDerivative period S hS T hT Q Q₁ c hc hQ f
    a₀))
    (velocityDerivative_contDiff period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀) t

theorem field_tsupport_subset (t : Icc (0 : ℝ) T) :
    tsupport (field period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t) ⊆ spatialSet period S := by
  change tsupport (pointField period _ _ t) ⊆ _
  rw [pointField_eq_representative]
  exact representative_tsupport_subset period S hS hSc.isClosed _ _
    (velocity period S hS T hT Q Q₁ c hc hQ f a₀ t).property

theorem field_hasCompactSupport (t : Icc (0 : ℝ) T) :
    HasCompactSupport (field period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t) := by
  change HasCompactSupport (pointField period _ _ t)
  rw [pointField_eq_representative]
  exact representative_hasCompactSupport period S hS hSc _ _
    (velocity period S hS T hT Q Q₁ c hc hQ f a₀ t).property

/-- Inclusion in full cylinder L² preserves the already proved time derivative. -/
theorem fullVelocity_hasDerivWithinAt
    (hQt : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
      HasDerivWithinAt (fun s => extendPath T hT Q.field s x)
        (extendPath T hT Q₁.field t x) (Icc (0 : ℝ) T) t)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (includePath period S hS
      (velocity period S hS T hT Q Q₁ c hc hQ f a₀)))
      (includePath period S hS (velocityDerivative period S hS T hT Q Q₁ c hc hQ f a₀) t)
      (Icc (0 : ℝ) T) t := by
  let L : Supported period Space S hS →L[ℝ] LiftL2 period := (Supported period Space S hS).subtypeL
  exact L.hasFDerivAt.comp_hasDerivWithinAt (t : ℝ)
    (velocity_hasDerivWithinAt period S hS T hT Q Q₁ c hc hQ f a₀ hQt t)

/-- No global time extension is assumed: the true time derivative holds within
the closed source interval, at every cylinder point. -/
theorem field_hasDerivWithinAt
    (hQt : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
      HasDerivWithinAt (fun s => extendPath T hT Q.field s x)
        (extendPath T hT Q₁.field t x) (Icc (0 : ℝ) T) t)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    HasDerivWithinAt (fun s => field period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ (projIcc 0 T hT
      s) x)
      (derivativeField period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀ t x) (Icc (0 : ℝ) T) t :=
  pointField_hasDerivWithinAt period T hT
    (includePath period S hS (velocity period S hS T hT Q Q₁ c hc hQ f a₀))
    (includePath period S hS (velocityDerivative period S hS T hT Q Q₁ c hc hQ f a₀))
    (velocity_contDiff period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀)
    (velocityDerivative_contDiff period S hS hSc T hT Q Q₁ c hc hQ f a₀ hf ha₀)
    (fullVelocity_hasDerivWithinAt period S hS T hT Q Q₁ c hc hQ f a₀ hQt) t x

end EulerSourceCylinderClassical
