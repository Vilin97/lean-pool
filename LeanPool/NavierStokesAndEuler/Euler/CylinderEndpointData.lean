/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletData
public import LeanPool.NavierStokesAndEuler.Euler.FixedEndpointStrong

@[expose] public section

/-!
# The actual affine-terminal inverse on the cylinder

The terminal coordinate below is an element of the genuine cylinder L²
space. The affine lift and its zero-endpoint correction are constructed by
the same coercive form as the forced history inverse. In particular, no
spatially constant nonzero vector is silently treated as L² data.
-/

noncomputable section

namespace EulerCylinderDirichlet.Coefficients

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerTimeLp
  EulerVolterraConvolution EulerTimeH1FrameTransport EulerTerminalTimePrimitive
  EulerInitialTimePrimitive EulerTimeH1OperatorProduct EulerTransverseFixedEndpoint
  EulerTransverseEndpointParameter EulerTransverseEndpointCoordinates
  EulerTransverseGramInverse EulerTransverseForwardInverse
  EulerTransverseInitialCoordinates EulerTransverseInitialInverse

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (P : ℝ) [Fact (0 < P)] {T : ℝ} (D : Coefficients T U E)

/-- The genuine zero-trace correction to the affine terminal lift. -/
def endpointCorrection : CylinderL2 P U →L[ℝ]
    zeroTraceDerivatives (U := CylinderL2 P U) T D.time_pos.le :=
  fixedEndpointCorrection T D.time_pos.le (D.frame P) (D.frameDerivative P) (D.hessian P)
    D.lower D.lower_pos (D.frame_lower P) (D.frame_derivative P)
    D.potential D.potential_nonneg (D.hessian_upper P) D.small
    (affineTrial T D.time_pos.le (D.frame P) (D.frameDerivative P))

/-- The actual coordinate derivative in L² time. -/
def endpointSlope : CylinderL2 P U →L[ℝ] TimeLp T (CylinderL2 P U) :=
  coordinateSlope T D.time_pos.le (D.frame P) (D.frameDerivative P) (D.hessian P)
    D.lower D.lower_pos (D.frame_lower P) (D.frame_derivative P)
    D.potential D.potential_nonneg (D.hessian_upper P) D.small

/-- The actual coordinate displacement with prescribed terminal trace. -/
def endpointDisplacement : CylinderL2 P U →L[ℝ] C(Icc (0 : ℝ) T,CylinderL2 P U) :=
  (initialPrimitive T D.time_pos.le).comp (D.endpointSlope P)

/-- Bounded H¹ reconstruction of the stationary coordinate velocity. -/
def endpointCoordinate : CylinderL2 P U →L[ℝ] C(Icc (0 : ℝ) T,CylinderL2 P U) :=
  continuousCoordinateVelocity T D.time_pos.le (D.frame P) (D.frameDerivative P) (D.hessian P)
    D.lower D.lower_pos (D.frame_lower P) (D.frame_derivative P)
    D.potential D.potential_nonneg (D.hessian_upper P) D.small

/-- Its acceleration is the actual homogeneous right hand side. -/
def endpointAcceleration : CylinderL2 P U →L[ℝ] C(Icc (0 : ℝ) T,CylinderL2 P U) :=
  (EulerContinuousTimeIntegral.multiplier
    (generator T (D.frame P) (D.frameDerivative P) D.lower D.lower_pos (D.frame_lower P))).comp
      (D.endpointCoordinate P)

/-- The physical history velocity, with a genuine L² terminal datum. -/
def endpointVelocity : CylinderL2 P U →L[ℝ] C(Icc (0 : ℝ) T,CylinderL2 P E) :=
  (EulerContinuousTimeIntegral.multiplier (D.frame P)).comp (D.endpointCoordinate P)

/-- The product-rule expression for the actual physical time derivative. -/
def endpointDerivative : CylinderL2 P U →L[ℝ] C(Icc (0 : ℝ) T,CylinderL2 P E) :=
  (EulerContinuousTimeIntegral.multiplier (D.frameDerivative P)).comp (D.endpointCoordinate P)+
    (EulerContinuousTimeIntegral.multiplier (D.frame P)).comp (D.endpointAcceleration P)

theorem endpointDisplacement_initial (Y : CylinderL2 P U) :
    D.endpointDisplacement P Y ⟨0,le_rfl,D.time_pos.le⟩ = 0 :=
  initialPrimitive_initial T D.time_pos.le _

theorem endpointDisplacement_terminal (Y : CylinderL2 P U) :
    D.endpointDisplacement P Y ⟨T,D.time_pos.le,le_rfl⟩ = Y := by
  have hr : initialTrace T D.time_pos.le
      (D.endpointCorrection P Y : TimeLp T (CylinderL2 P U)) = 0 :=
    (D.endpointCorrection P Y).property
  change initialPrimitive T D.time_pos.le
    (constantFieldOperator T D.time_pos.le (T⁻¹ • Y)-
      (D.endpointCorrection P Y : TimeLp T (CylinderL2 P U))) _ = Y
  rw [map_sub,ContinuousMap.sub_apply,initialPrimitive_constantFieldOperator,
    initialPrimitive_eq_terminal_sub,terminalPrimitive_terminal]
  change T • (T⁻¹ • Y)-(0-initialTrace T D.time_pos.le
    (D.endpointCorrection P Y : TimeLp T (CylinderL2 P U))) = Y
  rw [hr,sub_self,sub_zero,smul_smul,mul_inv_cancel₀ D.time_pos.ne',one_smul]

theorem endpointCoordinate_eq (Y : CylinderL2 P U) (t : Icc (0 : ℝ) T) :
    D.endpointCoordinate P Y t =
      EulerTransverseEndpointVelocity.coordinateVelocityPath T D.time_pos.le
        (D.frame P) (D.frameDerivative P) D.lower D.lower_pos (D.frame_lower P) (D.hessian P)
        (fixedEndpointDerivative T D.time_pos.le (D.frame P) (D.frameDerivative P) (D.hessian P)
          D.lower D.lower_pos (D.frame_lower P) (D.frame_derivative P)
          D.potential D.potential_nonneg (D.hessian_upper P) D.small
          (affineTrial T D.time_pos.le (D.frame P) (D.frameDerivative P)) Y) t :=
  EulerFixedEndpointStrong.continuousCoordinateVelocity_eq T D.time_pos.le
    (D.frame P) (D.frameDerivative P) (D.hessian P)
    D.lower D.lower_pos (D.frame_lower P) (D.frame_derivative P)
    D.potential D.potential_nonneg (D.hessian_upper P) D.small
    (D.frameSecond P) D.time_pos (D.frame_second_derivative P) (D.frame_equation P) Y t

/-- This reconstruction has the original L² coordinate derivative as its
almost-everywhere representative. -/
theorem endpointCoordinate_ae (Y : CylinderL2 P U) :
    (D.endpointSlope P Y : ℝ → CylinderL2 P U) =ᵐ[timeMeasure T]
      extendPath T D.time_pos.le (D.endpointCoordinate P Y) := by
  have ha := EulerFixedEndpointStrong.coordinateSlope_ae T D.time_pos.le
    (D.frame P) (D.frameDerivative P) (D.hessian P)
    D.lower D.lower_pos (D.frame_lower P) (D.frame_derivative P)
    D.potential D.potential_nonneg (D.hessian_upper P) D.small D.time_pos Y
  filter_upwards [ha,ae_restrict_mem measurableSet_Icc] with t ht hmem
  change D.endpointSlope P Y t = _ at ht
  rw [ht]
  change _ = D.endpointCoordinate P Y (projIcc 0 T D.time_pos.le t)
  rw [projIcc_of_mem D.time_pos.le hmem]
  exact (D.endpointCoordinate_eq P Y ⟨t,hmem⟩).symm

theorem endpointDisplacement_hasDerivWithinAt (Y : CylinderL2 P U) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T D.time_pos.le (D.endpointDisplacement P Y))
      (D.endpointCoordinate P Y t) (Icc (0 : ℝ) T) t := by
  have hd := EulerTimeH1ContinuousDerivative.hasDerivWithinAt_of_continuous_representative
    T D.time_pos.le (D.endpointSlope P Y) (D.endpointCoordinate P Y)
    (D.endpointCoordinate_ae P Y) (initialRealPrimitive T (D.endpointSlope P Y))
    (initialRealPrimitive_absolutelyContinuous T _)
    (initialRealPrimitive_hasDerivAt_ae T _) t
  apply hd.congr_of_mem _ t.property
  intro s hs
  change initialRealPrimitive T (D.endpointSlope P Y) (projIcc 0 T D.time_pos.le s) = _
  rw [projIcc_of_mem D.time_pos.le hs]

/-- Equation (10) holds throughout the closed time interval for the actual
affine-terminal solution. -/
theorem endpointCoordinate_hasDerivWithinAt (Y : CylinderL2 P U) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T D.time_pos.le (D.endpointCoordinate P Y))
      (D.endpointAcceleration P Y t) (Icc (0 : ℝ) T) t :=
  EulerFixedEndpointStrong.continuousCoordinateVelocity_hasDerivWithinAt_generator
    T D.time_pos.le (D.frame P) (D.frameDerivative P) (D.hessian P)
    D.lower D.lower_pos (D.frame_lower P) (D.frame_derivative P)
    D.potential D.potential_nonneg (D.hessian_upper P) D.small
    (D.frameSecond P) D.time_pos (D.frame_second_derivative P) (D.frame_equation P) Y t

theorem endpointVelocity_hasDerivWithinAt (Y : CylinderL2 P U) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T D.time_pos.le (D.endpointVelocity P Y))
      (D.endpointDerivative P Y t) (Icc (0 : ℝ) T) t := by
  have hd := (D.frame_derivative P t).clm_apply (D.endpointCoordinate_hasDerivWithinAt P Y t)
  change HasDerivWithinAt
    (fun s => extendPath (Y := CylinderL2 P U →L[ℝ] CylinderL2 P E) T D.time_pos.le (D.frame P) s
      (extendPath T D.time_pos.le (D.endpointCoordinate P Y) s))
    (D.frameDerivative P t (D.endpointCoordinate P Y t)+
      D.frame P t (D.endpointAcceleration P Y t)) (Icc (0 : ℝ) T) t
  simpa only [extendPath,projIcc_of_mem D.time_pos.le t.property] using hd

/-- The literal homogeneous projected equation, with no prescribed solution
or strong derivative among the data. -/
theorem endpoint_projected_equation (Y : CylinderL2 P U) (t : Icc (0 : ℝ) T) :
    gram (D.frame P t) (D.endpointAcceleration P Y t) =
      (D.frame P t).adjoint (-(2 : ℝ) • D.frameDerivative P t (D.endpointCoordinate P Y t)) := by
  change gram (D.frame P t) ((-2 : ℝ) • gramInverse (D.frame P t) D.lower D.lower_pos
    (D.frame_lower P t) ((D.frame P t).adjoint
      (D.frameDerivative P t (D.endpointCoordinate P Y t)))) = _
  rw [map_smul,gram_inverse_apply,map_smul]

end EulerCylinderDirichlet.Coefficients
