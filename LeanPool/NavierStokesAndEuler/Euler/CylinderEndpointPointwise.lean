/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointLabels
public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointRegularity
public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointEquation
public import LeanPool.NavierStokesAndEuler.Euler.CylinderRetractRepresentative
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPathIntegral
public import LeanPool.NavierStokesAndEuler.Euler.FixedEndpointClassical

@[expose] public section

/-!
The actual cylinder endpoint inverse agrees at every spatial/angular point
with the finite-dimensional stationary history. The proof first recovers
genuine coordinate representatives and their time derivatives, then uses
the proved two-endpoint energy uniqueness theorem.
-/

noncomputable section

namespace EulerCylinderDirichlet.Coefficients

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerVolterraConvolution
  EulerCylinderRetractRepresentative EulerTransverseGramInverse EulerMetricTransport
    EulerMeanCoefficients
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Coefficients T U Space)
  (J : U →L[ℝ] Space) (L : Space →L[ℝ] U)
  (hQ : ContDiff ℝ ∞ (translateCoefficientPath D.Q))
  (hQ₁ : ContDiff ℝ ∞ (translateCoefficientPath D.Q₁))
  (hH : ContDiff ℝ ∞ (translateCoefficientPath D.H))
  (Y : CylinderL2 P U) (hY : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a Y))

include hQ hQ₁ hH hY in
theorem endpointDisplacement_orbit_contDiff :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (D.endpointDisplacement P Y)) :=
  EulerCylinderPathIntegral.orbit_contDiff_of_derivative P T D.time_pos.le
    (D.endpointDisplacement P Y) (D.endpointCoordinate P Y)
    (D.endpointCoordinate_orbit_contDiff P hQ hQ₁ hH Y hY)
    (D.endpointDisplacement_hasDerivWithinAt P Y) (D.endpointDisplacement_initial P Y)

def endpointPointDisplacement (x : LiftDomain P) : C(Icc (0 : ℝ) T,U) :=
  pointPath P J L (D.endpointDisplacement P Y)
    (D.endpointDisplacement_orbit_contDiff P hQ hQ₁ hH Y hY) x

def endpointPointCoordinate (x : LiftDomain P) : C(Icc (0 : ℝ) T,U) :=
  pointPath P J L (D.endpointCoordinate P Y)
    (D.endpointCoordinate_orbit_contDiff P hQ hQ₁ hH Y hY) x

def endpointPointAcceleration (x : LiftDomain P) : C(Icc (0 : ℝ) T,U) :=
  pointPath P J L (D.endpointAcceleration P Y)
    (D.endpointAcceleration_orbit_contDiff P hQ hQ₁ hH Y hY) x

theorem endpointPointDisplacement_hasDerivWithinAt (x : LiftDomain P) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt
      (extendPath T D.time_pos.le (D.endpointPointDisplacement P J L hQ hQ₁ hH Y hY x))
      (D.endpointPointCoordinate P J L hQ hQ₁ hH Y hY x t) (Icc (0 : ℝ) T) t :=
  pointPath_hasDerivWithinAt P J L T D.time_pos.le
    (D.endpointDisplacement P Y) (D.endpointCoordinate P Y)
    (D.endpointDisplacement_orbit_contDiff P hQ hQ₁ hH Y hY)
    (D.endpointCoordinate_orbit_contDiff P hQ hQ₁ hH Y hY)
    (D.endpointDisplacement_hasDerivWithinAt P Y) x t

theorem endpointPointCoordinate_hasDerivWithinAt (x : LiftDomain P) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt
      (extendPath T D.time_pos.le (D.endpointPointCoordinate P J L hQ hQ₁ hH Y hY x))
      (D.endpointPointAcceleration P J L hQ hQ₁ hH Y hY x t) (Icc (0 : ℝ) T) t :=
  pointPath_hasDerivWithinAt P J L T D.time_pos.le
    (D.endpointCoordinate P Y) (D.endpointAcceleration P Y)
    (D.endpointCoordinate_orbit_contDiff P hQ hQ₁ hH Y hY)
    (D.endpointAcceleration_orbit_contDiff P hQ hQ₁ hH Y hY)
    (D.endpointCoordinate_hasDerivWithinAt P Y) x t

variable (hL : ∀ v : U, L (J v) = v)

include hL in
theorem endpointPointCoordinate_ae (t : Icc (0 : ℝ) T) :
    D.endpointCoordinate P Y t =ᵐ[liftMeasure P]
      fun x => D.endpointPointCoordinate P J L hQ hQ₁ hH Y hY x t :=
  pointField_ae P J L (D.endpointCoordinate P Y)
    (D.endpointCoordinate_orbit_contDiff P hQ hQ₁ hH Y hY) hL t

include hL in
theorem endpointPointAcceleration_ae (t : Icc (0 : ℝ) T) :
    D.endpointAcceleration P Y t =ᵐ[liftMeasure P]
      fun x => D.endpointPointAcceleration P J L hQ hQ₁ hH Y hY x t :=
  pointField_ae P J L (D.endpointAcceleration P Y)
    (D.endpointAcceleration_orbit_contDiff P hQ hQ₁ hH Y hY) hL t

include hL in
theorem endpointPointDisplacement_initial (x : LiftDomain P) :
    D.endpointPointDisplacement P J L hQ hQ₁ hH Y hY x ⟨0,le_rfl,D.time_pos.le⟩ = 0 := by
  have he := pointField_eq P J L (D.endpointDisplacement P Y)
    (D.endpointDisplacement_orbit_contDiff P hQ hQ₁ hH Y hY) hL
    ⟨0,le_rfl,D.time_pos.le⟩ (fun _ => (0 : U)) continuous_const
    (by rw [D.endpointDisplacement_initial P Y]; exact Lp.coeFn_zero U 2 (liftMeasure P))
  exact congrFun he x

include hL in
theorem endpointPointDisplacement_terminal (f : LiftDomain P → U) (hf : Continuous f)
    (hrep : Y =ᵐ[liftMeasure P] f) (x : LiftDomain P) :
    D.endpointPointDisplacement P J L hQ hQ₁ hH Y hY x ⟨T,D.time_pos.le,le_rfl⟩ = f x := by
  have he := pointField_eq P J L (D.endpointDisplacement P Y)
    (D.endpointDisplacement_orbit_contDiff P hQ hQ₁ hH Y hY) hL
    ⟨T,D.time_pos.le,le_rfl⟩ f hf
    (by rw [D.endpointDisplacement_terminal P Y]; exact hrep)
  exact congrFun he x

include hL in
theorem endpointPoint_projected_equation (x : LiftDomain P) (t : Icc (0 : ℝ) T) :
    gram (D.Q t x.1) (D.endpointPointAcceleration P J L hQ hQ₁ hH Y hY x t) =
      (D.Q t x.1).adjoint ((-2 : ℝ) • D.Q₁ t x.1
        (D.endpointPointCoordinate P J L hQ hQ₁ hH Y hY x t)) := by
  have hcQ : Continuous (fun x : LiftDomain P => D.Q t x.1) :=
    (D.Q t).continuous.comp continuous_fst
  have hcQ₁ : Continuous (fun x : LiftDomain P => D.Q₁ t x.1) :=
    (D.Q₁ t).continuous.comp continuous_fst
  have hcAdj : Continuous (fun x : LiftDomain P => (D.Q t x.1).adjoint) :=
    (realAdjoint (U := U) (E := Space)).continuous.comp hcQ
  have hcv := pointField_continuous P J L (D.endpointCoordinate P Y)
    (D.endpointCoordinate_orbit_contDiff P hQ hQ₁ hH Y hY) t
  have hca := pointField_continuous P J L (D.endpointAcceleration P Y)
    (D.endpointAcceleration_orbit_contDiff P hQ hQ₁ hH Y hY) t
  have he : (fun x : LiftDomain P =>
      gram (D.Q t x.1) (D.endpointPointAcceleration P J L hQ hQ₁ hH Y hY x t)) =ᵐ[liftMeasure P]
      (fun x => (D.Q t x.1).adjoint ((-2 : ℝ) • D.Q₁ t x.1
        (D.endpointPointCoordinate P J L hQ hQ₁ hH Y hY x t))) := by
    filter_upwards [D.endpoint_coordinate_equation_ae P Y t,
      D.endpointPointCoordinate_ae P J L hQ hQ₁ hH Y hY hL t,
      D.endpointPointAcceleration_ae P J L hQ hQ₁ hH Y hY hL t] with x hx hv ha
    simpa only [hv,ha] using hx
  exact congrFun (Measure.eq_of_ae_eq he (hcAdj.clm_apply (hcQ.clm_apply hca))
    (hcAdj.clm_apply ((hcQ₁.clm_apply hcv).const_smul (-2 : ℝ)))) x

include hL in
theorem endpointPointCoordinate_eq_label (f : LiftDomain P → U) (hf : Continuous f)
    (hrep : Y =ᵐ[liftMeasure P] f) (x : LiftDomain P) :
    D.endpointPointCoordinate P J L hQ hQ₁ hH Y hY x = D.labelCoordinate x.1 (f x) := by
  exact (EulerFixedEndpointClassical.unique T D.time_pos.le (D.labelFrame x.1)
    (D.labelFrameDerivative x.1) (D.labelHessian x.1)
    D.lower D.lower_pos (D.labelFrame_lower x.1) (D.labelFrame_derivative x.1)
    D.potential D.potential_nonneg (D.labelHessian_upper x.1) D.small
    (D.labelFrameSecond x.1) D.time_pos (D.labelFrame_second_derivative x.1) (D.labelFrame_equation
      x.1)
    (f x) (D.endpointPointDisplacement P J L hQ hQ₁ hH Y hY x)
    (D.endpointPointCoordinate P J L hQ hQ₁ hH Y hY x)
    (D.endpointPointAcceleration P J L hQ hQ₁ hH Y hY x)
    (D.endpointPointDisplacement_hasDerivWithinAt P J L hQ hQ₁ hH Y hY x)
    (D.endpointPointCoordinate_hasDerivWithinAt P J L hQ hQ₁ hH Y hY x)
    (D.endpointPointDisplacement_initial P J L hQ hQ₁ hH Y hY hL x)
    (D.endpointPointDisplacement_terminal P J L hQ hQ₁ hH Y hY hL f hf hrep x)
    (D.endpointPoint_projected_equation P J L hQ hQ₁ hH Y hY hL x)).2

include hL in
theorem endpointVelocity_pointwise (f : LiftDomain P → U) (hf : Continuous f)
    (hrep : Y =ᵐ[liftMeasure P] f) (x : LiftDomain P) (t : Icc (0 : ℝ) T) :
    EulerCylinderSmoothOrbit.pointField P (D.endpointVelocity P Y)
      (D.endpointVelocity_orbit_contDiff P hQ hQ₁ hH Y hY) t x =
      D.labelVelocity x.1 (f x) t := by
  have he : (fun x => EulerCylinderSmoothOrbit.pointField P (D.endpointVelocity P Y)
      (D.endpointVelocity_orbit_contDiff P hQ hQ₁ hH Y hY) t x) =ᵐ[liftMeasure P]
      (fun x => D.Q t x.1 (D.endpointPointCoordinate P J L hQ hQ₁ hH Y hY x t)) := by
    filter_upwards [D.endpointVelocity_ae P Y t,
      D.endpointPointCoordinate_ae P J L hQ hQ₁ hH Y hY hL t,
      EulerCylinderSmoothOrbit.pointField_ae P (D.endpointVelocity P Y)
        (D.endpointVelocity_orbit_contDiff P hQ hQ₁ hH Y hY) t] with x hx hv hp
    rw [← hp,hx,hv]
  have hevery := Measure.eq_of_ae_eq he
    (smoothField_continuous P _ (EulerCylinderSmoothOrbit.pointField_smooth P
      (D.endpointVelocity P Y) (D.endpointVelocity_orbit_contDiff P hQ hQ₁ hH Y hY) t))
    (((D.Q t).continuous.comp continuous_fst).clm_apply
      (pointField_continuous P J L (D.endpointCoordinate P Y)
        (D.endpointCoordinate_orbit_contDiff P hQ hQ₁ hH Y hY) t))
  rw [congrFun hevery x,D.endpointPointCoordinate_eq_label P J L hQ hQ₁ hH Y hY hL f hf hrep x]
  exact (D.labelVelocity_apply x.1 (f x) t).symm

end EulerCylinderDirichlet.Coefficients
