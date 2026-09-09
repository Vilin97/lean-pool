/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPathAdvection
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangularRegularity

@[expose] public section

/-! Actual nonlinear and coefficient operations on raw cylinder-path witnesses. -/

noncomputable section

namespace EulerPacketCylinderField.Field

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerCylinderPathProduct
  EulerCylinderConstantMap EulerLpCylinderRectangular EulerMeanCoefficients EulerMetricTransport
  EulerLiftedWeakDerivative EulerCylinderSobolev EulerPacketProfileRecursion
open scoped ContDiff BoundedContinuousFunction

variable {P T : ℝ} [Fact (0 < P)] {raw raw' : VectorField}

def map (G : Field P T raw) (L : Space →L[ℝ] Space) :
    Field P T (fun z => L (raw z)) :=
  ofLifted (pathMap P L G.path) (pathMap_orbit_contDiff P L G.path G.orbit)
    (fun t x => L (pointField P G.path G.orbit t x))
    (fun t => L.continuous.comp (smoothField_continuous P _ (pointField_smooth P G.path G.orbit t)))
    (fun t => by
      filter_upwards [map_ae P L (G.path t),pointField_ae P G.path G.orbit t] with x hL hG
      exact hL.trans (congrArg L hG))
    (fun t x θ => congrArg L (G.raw_eq t x θ))

/-- The literal mixed derivative is represented by the actual derivative path. -/
def derivative (G : Field P T raw) (i : Fin 4) :
    Field P T (fun z => fderiv ℝ (fun y => raw (z.1,y)) z.2 (standardDirection i)) where
  path := derivativePath P G.path i
  orbit := derivativePath_orbit P G.path G.orbit i
  raw_eq t x θ := by
    rw [G.raw_fderiv]
    exact (pointField_derivativePath P G.path G.orbit i t (x,(θ : AddCircle P))).symm

def scalarProduct (G : Field P T raw) (H : Field P T raw')
    (L : Space →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) : Field P T (fun z => L (raw z) • raw' z) where
  path := scalarProductPath P L hL G.path H.path G.orbit H.orbit
  orbit := scalarProductPath_orbit P L hL G.path H.path G.orbit H.orbit
  raw_eq t x θ := by
    rw [G.raw_eq,H.raw_eq]
    exact (pointField_scalarProductPath P L hL G.path H.path G.orbit H.orbit t (x,(θ : AddCircle
      P))).symm

def bilinear (G : Field P T raw) (H : Field P T raw')
    (B : Space →L[ℝ] Space →L[ℝ] Space) : Field P T (fun z => B (raw z) (raw' z)) where
  path := bilinearProductPath P B G.path H.path G.orbit H.orbit
  orbit := bilinearProductPath_orbit P B G.path H.path G.orbit H.orbit
  raw_eq t x θ := by
    rw [G.raw_eq,H.raw_eq]
    exact (pointField_bilinearProductPath P B G.path H.path G.orbit H.orbit t (x,(θ : AddCircle
      P))).symm

/-- Spatial advection is the literal ordinary derivative of the second raw field. -/
def advection (G : Field P T raw) (H : Field P T raw') :
    Field P T (fun z => fderiv ℝ (fun y : Space => raw' (z.1,(y,z.2.2))) z.2.1 (raw z)) where
  path := advectionPath P G.path H.path G.orbit H.orbit
  orbit := advectionPath_orbit P G.path H.path G.orbit H.orbit
  raw_eq t x θ := by
    have he : (fun y : Space => raw' (t,(y,θ))) =
        fun y : Space => pointField P H.path H.orbit t (y,(θ : AddCircle P)) :=
      funext (fun y => H.raw_eq t y θ)
    rw [he,coverField_spatial_fderiv P _ (pointField_smooth P H.path H.orbit t),
      G.raw_eq,comp_apply,inl_apply]
    exact (pointField_advectionPath P G.path H.path G.orbit H.orbit t (x,(θ : AddCircle P))).symm

private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) := inferInstance

/-- A genuine smooth coefficient path multiplies a raw field without a new regularity premise. -/
def multiply (G : Field P T raw) (A : C(Icc (0 : ℝ) T,Space →ᵇ Space →L[ℝ] Space))
    (hA : ContDiff ℝ ∞ (translateCoefficientPath A))
    (coef : EulerPacketPointJets.Domain → Space →L[ℝ] Space)
    (hcoef : ∀ (t : Icc (0 : ℝ) T) x θ, coef (t,(x,θ)) = A t x) :
    Field P T (fun z => coef z (raw z)) :=
  ofLifted (fullMultiplierMap P A G.path) (product_orbit_contDiff P A hA G.path G.orbit)
    (fun t x => A t x.1 (pointField P G.path G.orbit t x))
    (fun t => ((A t).continuous.comp continuous_fst).clm_apply
      (smoothField_continuous P _ (pointField_smooth P G.path G.orbit t)))
    (fun t => by
      filter_upwards [EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (A t)) (G.path t),
        pointField_ae P G.path G.orbit t] with x hM hG
      exact hM.trans (congrArg (A t x.1) hG))
    (fun t x θ => by rw [hcoef,G.raw_eq])

end EulerPacketCylinderField.Field
