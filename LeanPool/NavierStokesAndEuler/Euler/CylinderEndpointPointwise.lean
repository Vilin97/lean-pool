/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointLabels
public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointRegularity
import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl
import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointEquation
import LeanPool.NavierStokesAndEuler.Euler.FixedEndpointClassical
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderTranslation
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeIntegral
public import LeanPool.NavierStokesAndEuler.Euler.CylinderConstantMap
public import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeRegularity

/-!
The actual cylinder endpoint inverse agrees at every spatial/angular point
with the finite-dimensional stationary history. The proof first recovers
genuine coordinate representatives and their time derivatives, then uses
the proved two-endpoint energy uniqueness theorem.
-/

section

/-!
Actual pointwise representatives for coordinate spaces embedded in Space.
A fixed bounded embedding and left inverse transfer the proved H³ point
evaluation. This will apply to the two-dimensional reference plane, without
identifying an L² normal with a pointwise normal vector.
-/

@[expose] public section

noncomputable section

namespace EulerCylinderRetractRepresentative

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerCylinderConstantMap EulerVolterraConvolution EulerMetricTransport
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {U : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  (J : U →L[ℝ] Space) (L : Space →L[ℝ] U)
  {K : Type*} [TopologicalSpace K] [CompactSpace K]
  (p : C(K, CylinderL2 P U))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))

/-- Point field, given by `L (EulerCylinderSmoothOrbit.pointField P (pathMap P J p)
(pathMap_orbit_contDiff P J p hp) t x)`. -/
def pointField (t : K) (x : LiftDomain P) : U :=
  L (EulerCylinderSmoothOrbit.pointField P (pathMap P J p) (pathMap_orbit_contDiff P J p hp) t x)

theorem pointField_joint_continuous :
    Continuous (fun z : K × LiftDomain P => pointField P J L p hp z.1 z.2) :=
  L.continuous.comp (EulerCylinderSmoothOrbit.pointField_joint_continuous P
    (pathMap P J p) (pathMap_orbit_contDiff P J p hp))

theorem pointField_smooth (t : K) (x : LiftDomain P) :
    ContDiff ℝ ∞ (localFieldLift P (pointField P J L p hp t) x) :=
  L.contDiff.comp (EulerCylinderSmoothOrbit.pointField_smooth P
    (pathMap P J p) (pathMap_orbit_contDiff P J p hp) t x)

theorem pointField_continuous (t : K) : Continuous (pointField P J L p hp t) :=
  smoothField_continuous P _ (pointField_smooth P J L p hp t)

/-- Point path as an element of `C(K,U)`. -/
def pointPath (x : LiftDomain P) : C(K,U) :=
  ⟨fun t => pointField P J L p hp t x,
    L.continuous.comp ((EulerSobolevPointEvaluation.pointEvaluation P x).continuous.comp
      (EulerCylinderSmoothOrbit.sobolevPath P 3 (pathMap P J p)
        (pathMap_orbit_contDiff P J p hp)).continuous)⟩

theorem pointField_ae (hL : ∀ v : U, L (J v) = v) (t : K) :
    p t =ᵐ[liftMeasure P] pointField P J L p hp t := by
  filter_upwards [map_ae P J (p t),EulerCylinderSmoothOrbit.pointField_ae P
    (pathMap P J p) (pathMap_orbit_contDiff P J p hp) t] with x hm he
  change (map P J (p t)) x = _ at he
  change p t x = L _
  rw [← he,hm,hL]

theorem pointField_eq (hL : ∀ v : U, L (J v) = v) (t : K)
    (f : LiftDomain P → U) (hf : Continuous f) (hrep : p t =ᵐ[liftMeasure P] f) :
    pointField P J L p hp t = f :=
  Measure.eq_of_ae_eq ((pointField_ae P J L p hp hL t).symm.trans hrep)
    (pointField_continuous P J L p hp t) hf

section Time

variable (T : ℝ) (hT : 0 ≤ T)
  (p q : C(Icc (0 : ℝ) T, CylinderL2 P U))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hq : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a q))
  (hd : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT p) (q t) (Icc (0 : ℝ) T) t)

include hd in
theorem pointPath_hasDerivWithinAt (x : LiftDomain P) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (pointPath P J L p hp x))
      (pointPath P J L q hq x t) (Icc (0 : ℝ) T) t := by
  have hdJ (s : Icc (0 : ℝ) T) :
      HasDerivWithinAt (extendPath T hT (pathMap P J p)) (pathMap P J q s)
        (Icc (0 : ℝ) T) s :=
    (map P J).hasFDerivAt.comp_hasDerivWithinAt (s : ℝ) (hd s)
  exact L.hasFDerivAt.comp_hasDerivWithinAt (t : ℝ)
    (EulerCylinderSmoothOrbit.pointField_hasDerivWithinAt P T hT
      (pathMap P J p) (pathMap P J q) (pathMap_orbit_contDiff P J p hp)
      (pathMap_orbit_contDiff P J q hq) hdJ t x)

end Time
end EulerCylinderRetractRepresentative

end
end

end

section

/-! Initial time integration commutes with the genuine mixed cylinder action. -/

@[expose] public section

noncomputable section

namespace EulerCylinderPathIntegral

open Set ContinuousLinearMap EulerLpCylinderTranslation EulerLiftedGradientSpace
  EulerVolterraConvolution EulerContinuousTimeIntegral
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  (T : ℝ) (hT : 0 ≤ T)

theorem integral_translate (p : C(Icc (0 : ℝ) T, CylinderL2 P V)) (a : LiftTangent) :
    integral T hT (pathTranslate P a p) = pathTranslate P a (integral T hT p) := by
  apply ContinuousMap.ext
  intro t
  exact (translate P a).intervalIntegral_comp_comm (extendPath T hT p)

theorem integral_orbit_contDiff (p : C(Icc (0 : ℝ) T, CylinderL2 P V))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (integral T hT p)) := by
  have hh := (integral (E := CylinderL2 P V) T hT).contDiff.comp hp
  convert hh using 1
  funext a
  exact (integral_translate P T hT p a).symm

theorem orbit_contDiff_of_derivative
    (p q : C(Icc (0 : ℝ) T, CylinderL2 P V))
    (hq : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a q))
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT p) (q t) (Icc (0 : ℝ) T) t)
    (hzero : p ⟨0,le_rfl,hT⟩ = 0) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p) := by
  have he : p = integral T hT q := by
    apply ContinuousMap.ext
    intro t
    have hh := eq_initial_add_integral T hT q (extendPath T hT p) hd t
    simpa only [extendPath,projIcc_of_mem hT t.property,
      projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩),hzero,zero_add] using hh
  rw [he]
  exact integral_orbit_contDiff P T hT q hq

end EulerCylinderPathIntegral

end
end

end

@[expose] public section

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

/-- Endpoint point displacement, given by `pointPath P J L (D.endpointDisplacement P Y)
(D.endpointDisplacement_orbit_contDiff P hQ hQ₁ hH Y hY) x`. -/
def endpointPointDisplacement (x : LiftDomain P) : C(Icc (0 : ℝ) T,U) :=
  pointPath P J L (D.endpointDisplacement P Y)
    (D.endpointDisplacement_orbit_contDiff P hQ hQ₁ hH Y hY) x

/-- Endpoint point coordinate, given by `pointPath P J L (D.endpointCoordinate P Y)
(D.endpointCoordinate_orbit_contDiff P hQ hQ₁ hH Y hY) x`. -/
def endpointPointCoordinate (x : LiftDomain P) : C(Icc (0 : ℝ) T,U) :=
  pointPath P J L (D.endpointCoordinate P Y)
    (D.endpointCoordinate_orbit_contDiff P hQ hQ₁ hH Y hY) x

/-- Endpoint point acceleration, given by `pointPath P J L (D.endpointAcceleration P Y)
(D.endpointAcceleration_orbit_contDiff P hQ hQ₁ hH Y hY) x`. -/
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
