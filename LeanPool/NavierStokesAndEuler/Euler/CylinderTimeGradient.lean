/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeWords

@[expose] public section

/-! Time regularity of the full genuine covering derivative, reconstructed from its four
  directions. -/

noncomputable section

namespace EulerCylinderSmoothOrbit

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMetricTransport EulerTransportDerivatives EulerCylinderCoordinates EulerCylinderSobolev
  EulerLpCylinderTranslation EulerVolterraConvolution EulerLiftedWeakDerivative
open scoped ContDiff

def tangentCoordinate (i : Fin 4) : LiftTangent →L[ℝ] ℝ :=
  (EuclideanSpace.proj i).comp coordinateEquiv.symm.toContinuousLinearMap

def fromCoordinates : (Fin 4 → Space) →L[ℝ] (LiftTangent →L[ℝ] Space) :=
  ∑ i : Fin 4, (ContinuousLinearMap.smulRightL ℝ LiftTangent Space (tangentCoordinate i)).comp
    (ContinuousLinearMap.proj i)

theorem fromCoordinates_apply (u : Fin 4 → Space) (v : LiftTangent) :
    fromCoordinates u v = ∑ i : Fin 4, (coordinateEquiv.symm v i) • u i := by
  simp [fromCoordinates, tangentCoordinate]

theorem tangent_sum_coordinates (v : LiftTangent) :
    (∑ i : Fin 4, (coordinateEquiv.symm v i) • standardDirection i) = v := by
  have he : (∑ i : Fin 4, (coordinateEquiv.symm v i) • EuclideanSpace.single i (1 : ℝ)) =
      coordinateEquiv.symm v := by
    ext i
    simp [Pi.single_apply, mul_ite]
  change (∑ i : Fin 4, (coordinateEquiv.symm v i) • coordinateEquiv (EuclideanSpace.single i (1 :
    ℝ))) = v
  simp_rw [← map_smul]
  rw [← map_sum, he, ContinuousLinearEquiv.apply_symm_apply]

theorem fromCoordinates_eq (D : LiftTangent →L[ℝ] Space) :
    fromCoordinates (fun i => D (standardDirection i)) = D := by
  apply ContinuousLinearMap.ext
  intro v
  rw [fromCoordinates_apply]
  calc
    _ = D (∑ i : Fin 4, (coordinateEquiv.symm v i) • standardDirection i) := by
      simp only [map_sum, map_smul]
    _ = D v := congrArg D (tangent_sum_coordinates v)

variable (P : ℝ) [Fact (0 < P)]

theorem pointField_fderiv_joint_continuous {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (p : C(K,LiftL2 P)) (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) :
    Continuous (fun z : K × LiftDomain P => fieldFDeriv P (pointField P p hp z.1) z.2) := by
  have hc : Continuous (fun z : K × LiftDomain P =>
      fun i : Fin 4 => fieldFDeriv P (pointField P p hp z.1) z.2 (standardDirection i)) := by
    apply continuous_pi
    intro i
    exact pointField_word_joint_continuous P p hp 1 (fun _ => i)
  simpa only [Function.comp_def, fromCoordinates_eq] using fromCoordinates.continuous.comp hc

variable (T : ℝ) (hT : 0 ≤ T) (p f : C(Icc (0 : ℝ) T,LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a f))
  (hd : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT p) (f t) (Icc (0 : ℝ) T) t)

include hd in
/-- Differentiating the full covering derivative in time gives the covering derivative of the true RHS. -/
theorem pointField_fderiv_hasDerivWithinAt (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    HasDerivWithinAt
      (fun r => fieldFDeriv P (pointField P p hp (projIcc 0 T hT r)) x)
      (fieldFDeriv P (pointField P f hf t) x) (Icc (0 : ℝ) T) t := by
  have hD : HasDerivWithinAt
      (fun r => fun i : Fin 4 => fieldFDeriv P (pointField P p hp (projIcc 0 T hT r)) x
        (standardDirection i))
      (fun i : Fin 4 => fieldFDeriv P (pointField P f hf t) x (standardDirection i))
      (Icc (0 : ℝ) T) t := by
    apply hasDerivWithinAt_pi.mpr
    intro i
    exact pointField_word_hasDerivWithinAt P T hT p f hp hf hd 1 (fun _ => i) t x
  have h := fromCoordinates.hasFDerivAt.comp_hasDerivWithinAt (t : ℝ) hD
  simpa only [Function.comp_def, fromCoordinates_eq] using h

end EulerCylinderSmoothOrbit
