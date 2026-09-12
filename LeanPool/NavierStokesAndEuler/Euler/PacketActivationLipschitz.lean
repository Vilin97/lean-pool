/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointLabels
public import LeanPool.NavierStokesAndEuler.Euler.TransverseHistoryBounds
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistoryData
import LeanPool.NavierStokesAndEuler.Euler.PacketCoefficientLipschitz
import LeanPool.NavierStokesAndEuler.Euler.TransverseHistoryLipschitz

/-! Genuine label sensitivity of the stationary source history.  All
constants below are computed from the supplied smooth coefficient paths;
no continuity or estimate for the solved history is assumed. -/

@[expose] public section


noncomputable section

namespace EulerPacketActivationHistory

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerTransversePacketProvider EulerTransverseSourceCoefficientPath
  EulerTransverseHistoryBounds EulerTimeH1FrameTransport
  EulerTransverseEndpointCoordinates
open scoped BoundedContinuousFunction

private theorem transport_polynomial_mono {ci T q Q p P : ℝ}
    (hci : 0 ≤ ci) (hT : 0 ≤ T) (hq0 : 0 ≤ q) (hp0 : 0 ≤ p)
    (hq : q ≤ Q) (hp : p ≤ P) :
    1+((2*ci^2*q^2*p+ci*p)*T+ci*q) ≤ 1+((2*ci^2*Q^2*P+ci*P)*T+ci*Q) := by
  gcongr

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (B : HistoryData D)

/-- Cache the standard `NormedAddCommGroup (U →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketActivationLipschitz1 : NormedAddCommGroup (U →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (U →L[ℝ] Space)` instance to shorten typeclass synthesis. -/
local instance instPacketActivationLipschitz2 : NormedSpace ℝ (U →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ (U →L[ℝ] Space))` instance to shorten
typeclass synthesis. -/
local instance instPacketActivationLipschitz3 : NormedAddCommGroup (Space →ᵇ (U →L[ℝ] Space)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ (U →L[ℝ] Space))` instance to shorten typeclass
synthesis. -/
local instance instPacketActivationLipschitz4 : NormedSpace ℝ (Space →ᵇ (U →L[ℝ] Space)) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) D.T,Space →ᵇ (U →L[ℝ] Space))` instance
to shorten typeclass synthesis. -/
local instance instPacketActivationLipschitz5 : NormedAddCommGroup C(Icc (0 : ℝ) D.T,Space →ᵇ (U
    →L[ℝ] Space)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) D.T,Space →ᵇ (U →L[ℝ] Space))` instance to
shorten typeclass synthesis. -/
local instance instPacketActivationLipschitz6 : NormedSpace ℝ C(Icc (0 : ℝ) D.T,Space →ᵇ (U →L[ℝ]
    Space)) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] (U →L[ℝ] Space))` instance to shorten
typeclass synthesis. -/
local instance instPacketActivationLipschitz7 : NormedAddCommGroup (Space →L[ℝ] (U →L[ℝ] Space)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] (U →L[ℝ] Space))` instance to shorten
typeclass synthesis. -/
local instance instPacketActivationLipschitz8 : NormedSpace ℝ (Space →L[ℝ] (U →L[ℝ] Space)) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ (Space →L[ℝ] (U →L[ℝ] Space)))` instance to
shorten typeclass synthesis. -/
local instance instPacketActivationLipschitz9 : NormedAddCommGroup (Space →ᵇ (Space →L[ℝ] (U →L[ℝ]
    Space))) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ (Space →L[ℝ] (U →L[ℝ] Space)))` instance to
shorten typeclass synthesis. -/
local instance instPacketActivationLipschitz10 : NormedSpace ℝ (Space →ᵇ (Space →L[ℝ] (U →L[ℝ]
    Space))) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) D.T,Space →ᵇ (Space →L[ℝ] (U →L[ℝ]
Space)))` instance to shorten typeclass synthesis. -/
local instance instPacketActivationLipschitz11 : NormedAddCommGroup C(Icc (0 : ℝ) D.T,Space →ᵇ
    (Space →L[ℝ] (U →L[ℝ]
    Space))) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) D.T,Space →ᵇ (Space →L[ℝ] (U →L[ℝ] Space)))`
instance to shorten typeclass synthesis. -/
local instance instPacketActivationLipschitz12 : NormedSpace ℝ C(Icc (0 : ℝ) D.T,Space →ᵇ (Space
    →L[ℝ] (U →L[ℝ] Space))) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketActivationLipschitz13 : NormedAddCommGroup (Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketActivationLipschitz14 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ (Space →L[ℝ] Space))` instance to shorten
typeclass synthesis. -/
local instance instPacketActivationLipschitz15 : NormedAddCommGroup (Space →ᵇ (Space →L[ℝ] Space))
    := inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ (Space →L[ℝ] Space))` instance to shorten
typeclass synthesis. -/
local instance instPacketActivationLipschitz16 : NormedSpace ℝ (Space →ᵇ (Space →L[ℝ] Space)) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) D.T,Space →ᵇ (Space →L[ℝ] Space))`
instance to shorten typeclass synthesis. -/
local instance instPacketActivationLipschitz17 : NormedAddCommGroup C(Icc (0 : ℝ) D.T,Space →ᵇ
    (Space →L[ℝ] Space)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) D.T,Space →ᵇ (Space →L[ℝ] Space))` instance
to shorten typeclass synthesis. -/
local instance instPacketActivationLipschitz18 : NormedSpace ℝ C(Icc (0 : ℝ) D.T,Space →ᵇ (Space
    →L[ℝ] Space)) :=
    inferInstance

/-- History transport cost as an element of `ℝ`. -/
def historyTransportCost : ℝ :=
  1+((2*(D.frameLower⁻¹)^2*‖D.frame.field‖^2*‖D.frameDerivative.field‖+
    D.frameLower⁻¹*‖D.frameDerivative.field‖)*D.T+D.frameLower⁻¹*‖D.frame.field‖)

/-- History label size cost, constructed using `historyCost`. -/
def historyLabelSizeCost : ℝ :=
  historyCost D.T D.frameLower ‖D.frame.field‖ ‖D.frameDerivative.field‖
    (D.T*‖D.frameDerivative.field‖+‖D.frame.field‖) (1+D.T^2*‖B.H.field‖)
    (historyTransportCost (D := D))

/-- History label difference cost, constructed using `historyDifferenceCost`. -/
def historyLabelDifferenceCost : ℝ :=
  historyDifferenceCost D.T D.frameLower ‖D.frame.field‖ ‖D.frameDerivative.field‖
    (D.T*‖D.frameDerivative.field‖+‖D.frame.field‖) (1+D.T^2*‖B.H.field‖)
    (historyTransportCost (D := D)) ‖D.frame.derivative.field‖
    ‖D.frameDerivative.derivative.field‖ ‖B.H.derivative.field‖

omit [CompleteSpace U] in
theorem historyTransportCost_nonneg : 0 ≤ historyTransportCost (D := D) := by
  have := D.T_pos
  have := D.frameLower_pos
  unfold historyTransportCost
  positivity

omit [CompleteSpace U] in
theorem label_transportCost_le (x : Space) :
    transportCost D.T (B.coefficients.labelFrame x) (B.coefficients.labelFrameDerivative x)
      D.frameLower ≤ historyTransportCost (D := D) := by
  have hq := coefficient_label_norm D.frame x
  have hq₁ := coefficient_label_norm D.frameDerivative x
  unfold transportCost historyTransportCost
  change 1+((2*(D.frameLower⁻¹)^2*‖pathEvaluation x D.frame.field‖^2 *
      ‖pathEvaluation x D.frameDerivative.field‖+
      D.frameLower⁻¹*‖pathEvaluation x D.frameDerivative.field‖)*D.T +
      D.frameLower⁻¹*‖pathEvaluation x D.frame.field‖) ≤ _
  exact transport_polynomial_mono (inv_nonneg.mpr D.frameLower_pos.le) D.T_pos.le
    (norm_nonneg _) (norm_nonneg _) hq hq₁

omit [CompleteSpace U] in
theorem label_derivative_size (x : Space) :
    D.T*‖B.coefficients.labelFrameDerivative x‖+‖B.coefficients.labelFrame x‖ ≤
      D.T*‖D.frameDerivative.field‖+‖D.frame.field‖ :=
  add_le_add (mul_le_mul_of_nonneg_left (coefficient_label_norm D.frameDerivative x) D.T_pos.le)
    (coefficient_label_norm D.frame x)

omit [CompleteSpace U] in
theorem label_energy_size (x : Space) :
    1+D.T^2*‖B.coefficients.labelHessian x‖ ≤ 1+D.T^2*‖B.H.field‖ :=
  add_le_add le_rfl (mul_le_mul_of_nonneg_left (coefficient_label_norm B.H x) (sq_nonneg D.T))

omit [CompleteSpace U] in
theorem historyLabelDifferenceCost_nonneg : 0 ≤ historyLabelDifferenceCost B := by
  apply historyDifferenceCost_nonneg
  · exact D.T_pos.le
  · exact D.frameLower_pos.le
  · positivity
  · positivity
  · positivity [D.T_pos]
  · positivity
  · exact historyTransportCost_nonneg (D := D)
  · positivity
  · positivity
  · positivity

theorem labelVelocity_norm (x : Space) :
    ‖B.coefficients.labelVelocity x‖ ≤ historyLabelSizeCost B := by
  exact historyVelocity_norm_le D.T D.T_pos.le
    (B.coefficients.labelFrame x) (B.coefficients.labelFrameDerivative x)
    (B.coefficients.labelHessian x) D.frameLower D.frameLower_pos
    (B.coefficients.labelFrame_lower x) (B.coefficients.labelFrame_derivative x)
    B.potential B.potential_nonneg (B.coefficients.labelHessian_upper x) B.small D.T_pos
    ‖D.frame.field‖ ‖D.frameDerivative.field‖
    (D.T*‖D.frameDerivative.field‖+‖D.frame.field‖) (1+D.T^2*‖B.H.field‖)
    (historyTransportCost (D := D)) (coefficient_label_norm D.frame x)
    (coefficient_label_norm D.frameDerivative x) (label_derivative_size B x)
    (label_energy_size B x) (label_transportCost_le B x)

theorem labelVelocity_difference (x y : Space) :
    ‖B.coefficients.labelVelocity x-B.coefficients.labelVelocity y‖ ≤
      historyLabelDifferenceCost B*‖x-y‖ := by
  exact historyVelocity_sub_norm_le_of_coefficient_bounds D.T D.T_pos.le
    (B.coefficients.labelFrame x) (B.coefficients.labelFrameDerivative x)
    (B.coefficients.labelHessian x) D.frameLower D.frameLower_pos
    (B.coefficients.labelFrame_lower x) (B.coefficients.labelFrame_derivative x)
    B.potential B.potential_nonneg (B.coefficients.labelHessian_upper x) B.small
    (B.coefficients.labelFrame y) (B.coefficients.labelFrameDerivative y)
    (B.coefficients.labelHessian y) (B.coefficients.labelFrame_lower y)
    (B.coefficients.labelFrame_derivative y) (B.coefficients.labelHessian_upper y) D.T_pos
    ‖D.frame.field‖ ‖D.frameDerivative.field‖
    (D.T*‖D.frameDerivative.field‖+‖D.frame.field‖) (1+D.T^2*‖B.H.field‖)
    (historyTransportCost (D := D)) (coefficient_label_norm D.frame x)
    (coefficient_label_norm D.frame y) (coefficient_label_norm D.frameDerivative x)
    (coefficient_label_norm D.frameDerivative y) (label_derivative_size B x) (label_derivative_size
        B y)
    (label_energy_size B x) (label_energy_size B y) (label_transportCost_le B x)
    (label_transportCost_le B y) ‖D.frame.derivative.field‖ ‖D.frameDerivative.derivative.field‖
    ‖B.H.derivative.field‖ ‖x-y‖ (coefficient_label_difference D.frame x y)
    (coefficient_label_difference D.frameDerivative x y) (coefficient_label_difference B.H x y)

theorem labelVelocity_point_difference (x y : Space) (ξ : U) (t : Icc (0 : ℝ) D.T) :
    ‖B.coefficients.labelVelocity x ξ t-B.coefficients.labelVelocity y ξ t‖ ≤
      historyLabelDifferenceCost B*‖x-y‖*‖ξ‖ := by
  exact (((B.coefficients.labelVelocity x-B.coefficients.labelVelocity y) ξ).norm_coe_le_norm
      t).trans
    (((B.coefficients.labelVelocity x-B.coefficients.labelVelocity y).le_opNorm ξ).trans
      (mul_le_mul_of_nonneg_right (labelVelocity_difference B x y) (norm_nonneg ξ)))

end EulerPacketActivationHistory
