/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletTranslation
import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletNaturality
import LeanPool.NavierStokesAndEuler.Euler.FixedEvolutionRegularity

/-!
# Actual mixed-translation smoothness of the cylinder history

The translated variational problems live on one fixed Hilbert space.
Smoothness follows from their genuine coercive inverses, and exact covariance
identifies that family with the translation orbit of the constructed field.
No regularity assumption is imposed on a solved history field.
-/

@[expose] public section


noncomputable section

namespace EulerCylinderDirichlet.Coefficients

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderRectangular
  EulerTimeLp EulerTimeLpBoundedMap EulerVolterraConvolution EulerMeanCoefficients
open scoped BoundedContinuousFunction ContDiff

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E)

/-- Cache the standard `NormedAddCommGroup (CylinderL2 P U)` instance to shorten typeclass
synthesis. -/
local instance instCylinderDirichletRegularity1 : NormedAddCommGroup (CylinderL2 P U) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (CylinderL2 P U)` instance to shorten typeclass synthesis. -/
local instance instCylinderDirichletRegularity2 : NormedSpace ℝ (CylinderL2 P U) := inferInstance
/-- Cache the standard `NormedAddCommGroup (CylinderL2 P E)` instance to shorten typeclass
synthesis. -/
local instance instCylinderDirichletRegularity3 : NormedAddCommGroup (CylinderL2 P E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (CylinderL2 P E)` instance to shorten typeclass synthesis. -/
local instance instCylinderDirichletRegularity4 : NormedSpace ℝ (CylinderL2 P E) := inferInstance
/-- Cache the standard `NormedAddCommGroup (CylinderL2 P U →L[ℝ] CylinderL2 P E)` instance to
shorten typeclass synthesis. -/
local instance instCylinderDirichletRegularity5 : NormedAddCommGroup (CylinderL2 P U →L[ℝ]
    CylinderL2 P E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (CylinderL2 P U →L[ℝ] CylinderL2 P E)` instance to shorten
typeclass synthesis. -/
local instance instCylinderDirichletRegularity6 : NormedSpace ℝ (CylinderL2 P U →L[ℝ] CylinderL2 P
    E) := inferInstance
/-- Cache the standard `NormedAddCommGroup (CylinderL2 P E →L[ℝ] CylinderL2 P E)` instance to
shorten typeclass synthesis. -/
local instance instCylinderDirichletRegularity7 : NormedAddCommGroup (CylinderL2 P E →L[ℝ]
    CylinderL2 P E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (CylinderL2 P E →L[ℝ] CylinderL2 P E)` instance to shorten
typeclass synthesis. -/
local instance instCylinderDirichletRegularity8 : NormedSpace ℝ (CylinderL2 P E →L[ℝ] CylinderL2 P
    E) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 P U →L[ℝ] CylinderL2 P E)`
instance to shorten typeclass synthesis. -/
local instance instCylinderDirichletRegularity9 : NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 P U
    →L[ℝ] CylinderL2 P E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 P U →L[ℝ] CylinderL2 P E)`
instance to shorten typeclass synthesis. -/
local instance instCylinderDirichletRegularity10 : NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 P U
    →L[ℝ] CylinderL2 P E) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 P E →L[ℝ] CylinderL2 P E)`
instance to shorten typeclass synthesis. -/
local instance instCylinderDirichletRegularity11 : NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 P
    E →L[ℝ] CylinderL2 P E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 P E →L[ℝ] CylinderL2 P E)`
instance to shorten typeclass synthesis. -/
local instance instCylinderDirichletRegularity12 : NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 P E
    →L[ℝ] CylinderL2 P E) :=
    inferInstance

theorem fullPathMap_comp_contDiff {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    {g : LiftTangent → C(Icc (0 : ℝ) T, Space →ᵇ (X →L[ℝ] Y))} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun a => fullPathMap (K := Icc (0 : ℝ) T) (E := X) (F := Y) P (g a)) :=
  (fullPathMap (K := Icc (0 : ℝ) T) (E := X) (F := Y) P).contDiff.comp hg

omit [CompleteSpace U] [CompleteSpace E] in
theorem frameOrbit_contDiff (hQ : ContDiff ℝ ∞ (translateCoefficientPath D.Q)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => (D.shifted a.1).frame P) :=
  fullPathMap_comp_contDiff P (hQ.comp contDiff_fst)

omit [CompleteSpace U] [CompleteSpace E] in
theorem frameDerivativeOrbit_contDiff (hQ₁ : ContDiff ℝ ∞ (translateCoefficientPath D.Q₁)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => (D.shifted a.1).frameDerivative P) :=
  fullPathMap_comp_contDiff P (hQ₁.comp contDiff_fst)

omit [CompleteSpace U] [CompleteSpace E] in
theorem hessianOrbit_contDiff (hH : ContDiff ℝ ∞ (translateCoefficientPath D.H)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => (D.shifted a.1).hessian P) :=
  fullPathMap_comp_contDiff P (hH.comp contDiff_fst)

theorem accelerationLp_translation (a : LiftTangent) (f : TimeLp T (CylinderL2 P E)) :
    (D.shifted a.1).accelerationLp P
        (timeLift T (translate (V := E) P a).toContinuousLinearMap f) =
      timeLift T (translate (V := U) P a).toContinuousLinearMap (D.accelerationLp P f) :=
  D.accelerationLp_intertwines P (D.shifted a.1)
    (translate (V := U) P a).toContinuousLinearMap (translate (V := E) P a).toContinuousLinearMap
    (D.shifted_frame P a) (D.shifted_frameDerivative P a)
    (D.shifted_frame_back P a) (D.shifted_frameDerivative_back P a) (D.shifted_hessian P a) f

variable (hQ : ContDiff ℝ ∞ (translateCoefficientPath D.Q))
  (hQ₁ : ContDiff ℝ ∞ (translateCoefficientPath D.Q₁))
  (hH : ContDiff ℝ ∞ (translateCoefficientPath D.H))

include hQ hQ₁ hH

theorem velocityLp_orbit_contDiff (f : TimeLp T (CylinderL2 P E))
    (hf : ContDiff ℝ ∞ (fun a => timeLift T (translate (V := E) P a).toContinuousLinearMap f)) :
    ContDiff ℝ ∞ (fun a =>
      timeLift T (translate (V := U) P a).toContinuousLinearMap (D.velocityLp P f)) :=
        by
  have hs := EulerTransverseFixedEvolution.velocityLp_contDiff
    (X := LiftTangent) (U := CylinderL2 P U) (E := CylinderL2 P E) (n := ∞) T D.time_pos.le
    (fun a : LiftTangent => (D.shifted a.1).frame P)
    (fun a : LiftTangent => (D.shifted a.1).frameDerivative P)
    (fun a : LiftTangent => (D.shifted a.1).hessian P)
    D.lower D.lower_pos (fun a => (D.shifted a.1).frame_lower P)
    (fun a => (D.shifted a.1).frame_derivative P)
    D.potential D.potential_nonneg (fun a => (D.shifted a.1).hessian_upper P) D.small
    (D.frameOrbit_contDiff P hQ) (D.frameDerivativeOrbit_contDiff P hQ₁) (D.hessianOrbit_contDiff P
        hH)
    (fun a => timeLift T (translate (V := E) P a).toContinuousLinearMap f) hf
  convert hs using 1
  funext a
  refine (D.velocityLp_translation P a f).symm.trans (DFunLike.congr_fun ?_ _)
  rfl

theorem accelerationLp_orbit_contDiff (f : TimeLp T (CylinderL2 P E))
    (hf : ContDiff ℝ ∞ (fun a => timeLift T (translate (V := E) P a).toContinuousLinearMap f)) :
    ContDiff ℝ ∞ (fun a =>
      timeLift T (translate (V := U) P a).toContinuousLinearMap (D.accelerationLp P f))
        := by
  have hs := EulerTransverseFixedEvolution.accelerationLp_contDiff
    (X := LiftTangent) (U := CylinderL2 P U) (E := CylinderL2 P E) (n := ∞) T D.time_pos.le
    (fun a : LiftTangent => (D.shifted a.1).frame P)
    (fun a : LiftTangent => (D.shifted a.1).frameDerivative P)
    (fun a : LiftTangent => (D.shifted a.1).hessian P)
    D.lower D.lower_pos (fun a => (D.shifted a.1).frame_lower P)
    (fun a => (D.shifted a.1).frame_derivative P)
    D.potential D.potential_nonneg (fun a => (D.shifted a.1).hessian_upper P) D.small
    (D.frameOrbit_contDiff P hQ) (D.frameDerivativeOrbit_contDiff P hQ₁) (D.hessianOrbit_contDiff P
        hH)
    (fun a => timeLift T (translate (V := E) P a).toContinuousLinearMap f) hf
  convert hs using 1
  funext a
  refine (D.accelerationLp_translation P a f).symm.trans (DFunLike.congr_fun ?_ _)
  rfl

theorem velocityPath_orbit_contDiff (f : C(Icc (0 : ℝ) T, CylinderL2 P E))
    (hf : ContDiff ℝ ∞ (fun a => pathTranslate (K := Icc (0 : ℝ) T) (V := E) P a f)) :
    ContDiff ℝ ∞ (fun a => pathTranslate (K := Icc (0 : ℝ) T) (V := U) P a
      (D.velocityPath P (pathLp T D.time_pos.le f))) := by
  have hs := EulerTransverseFixedEvolution.continuousVelocity_contDiff T D.time_pos.le
    (fun a : LiftTangent => (D.shifted a.1).frame P)
    (fun a : LiftTangent => (D.shifted a.1).frameDerivative P)
    (fun a : LiftTangent => (D.shifted a.1).hessian P)
    D.lower D.lower_pos (fun a => (D.shifted a.1).frame_lower P)
    (fun a => (D.shifted a.1).frame_derivative P)
    D.potential D.potential_nonneg (fun a => (D.shifted a.1).hessian_upper P) D.small
    (D.frameOrbit_contDiff P hQ) (D.frameDerivativeOrbit_contDiff P hQ₁) (D.hessianOrbit_contDiff P
        hH)
    (fun a => pathTranslate (K := Icc (0 : ℝ) T) (V := E) P a f) hf
  convert hs using 1
  funext a
  apply ContinuousMap.ext
  intro t
  refine (D.continuousVelocity_translation P a f t).symm.trans (DFunLike.congr_fun ?_ t)
  refine DFunLike.congr_fun ?_ _
  rfl

theorem accelerationPath_orbit_contDiff (f : C(Icc (0 : ℝ) T, CylinderL2 P E))
    (hf : ContDiff ℝ ∞ (fun a => pathTranslate (K := Icc (0 : ℝ) T) (V := E) P a f)) :
    ContDiff ℝ ∞ (fun a =>
      pathTranslate (K := Icc (0 : ℝ) T) (V := U) P a (D.accelerationPath P f)) := by
  have hs := EulerTransverseFixedEvolution.classicalAcceleration_contDiff T D.time_pos.le
    (fun a : LiftTangent => (D.shifted a.1).frame P)
    (fun a : LiftTangent => (D.shifted a.1).frameDerivative P)
    (fun a : LiftTangent => (D.shifted a.1).hessian P)
    D.lower D.lower_pos (fun a => (D.shifted a.1).frame_lower P)
    (fun a => (D.shifted a.1).frame_derivative P)
    D.potential D.potential_nonneg (fun a => (D.shifted a.1).hessian_upper P) D.small
    (D.frameOrbit_contDiff P hQ) (D.frameDerivativeOrbit_contDiff P hQ₁) (D.hessianOrbit_contDiff P
        hH)
    (fun a => pathTranslate (K := Icc (0 : ℝ) T) (V := E) P a f) hf
  convert hs using 1
  funext a
  apply ContinuousMap.ext
  intro t
  refine (D.accelerationPath_translation P a f t).symm.trans (DFunLike.congr_fun ?_ t)
  rfl

theorem physicalVelocity_orbit_contDiff (f : C(Icc (0 : ℝ) T, CylinderL2 P E))
    (hf : ContDiff ℝ ∞ (fun a => pathTranslate (K := Icc (0 : ℝ) T) (V := E) P a f)) :
    ContDiff ℝ ∞ (fun a =>
      pathTranslate (K := Icc (0 : ℝ) T) (V := E) P a (D.physicalVelocity P f)) := by
  have hs := EulerTransverseFixedEvolution.physicalVelocity_contDiff T D.time_pos.le
    (fun a : LiftTangent => (D.shifted a.1).frame P)
    (fun a : LiftTangent => (D.shifted a.1).frameDerivative P)
    (fun a : LiftTangent => (D.shifted a.1).hessian P)
    D.lower D.lower_pos (fun a => (D.shifted a.1).frame_lower P)
    (fun a => (D.shifted a.1).frame_derivative P)
    D.potential D.potential_nonneg (fun a => (D.shifted a.1).hessian_upper P) D.small
    (D.frameOrbit_contDiff P hQ) (D.frameDerivativeOrbit_contDiff P hQ₁) (D.hessianOrbit_contDiff P
        hH)
    (fun a => pathTranslate (K := Icc (0 : ℝ) T) (V := E) P a f) hf
  convert hs using 1
  funext a
  apply ContinuousMap.ext
  intro t
  refine (D.physicalVelocity_translation P a f t).symm.trans (DFunLike.congr_fun ?_ t)
  rfl

theorem physicalDerivative_orbit_contDiff (f : C(Icc (0 : ℝ) T, CylinderL2 P E))
    (hf : ContDiff ℝ ∞ (fun a => pathTranslate (K := Icc (0 : ℝ) T) (V := E) P a f)) :
    ContDiff ℝ ∞ (fun a =>
      pathTranslate (K := Icc (0 : ℝ) T) (V := E) P a (D.physicalDerivative P f)) := by
  have hs := EulerTransverseFixedEvolution.physicalDerivative_contDiff T D.time_pos.le
    (fun a : LiftTangent => (D.shifted a.1).frame P)
    (fun a : LiftTangent => (D.shifted a.1).frameDerivative P)
    (fun a : LiftTangent => (D.shifted a.1).hessian P)
    D.lower D.lower_pos (fun a => (D.shifted a.1).frame_lower P)
    (fun a => (D.shifted a.1).frame_derivative P)
    D.potential D.potential_nonneg (fun a => (D.shifted a.1).hessian_upper P) D.small
    (D.frameOrbit_contDiff P hQ) (D.frameDerivativeOrbit_contDiff P hQ₁) (D.hessianOrbit_contDiff P
        hH)
    (fun a => pathTranslate (K := Icc (0 : ℝ) T) (V := E) P a f) hf
  convert hs using 1
  funext a
  apply ContinuousMap.ext
  intro t
  refine (D.physicalDerivative_translation P a f t).symm.trans (DFunLike.congr_fun ?_ t)
  rfl

end EulerCylinderDirichlet.Coefficients
