/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistoryPressure
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPressureParity

@[expose] public section

/-! Joint parity of the actual source history inverse and its normalized pressure. -/

noncomputable section

namespace EulerTransversePacketProvider.HistoryData

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderSmoothOrbit
    EulerCylinderFieldReflection
  EulerPacketProfileRecursion EulerCylinderScalarPrimitive EulerMetricTransport

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (B : HistoryData D) {raw : VectorField} (G : Forcing P D raw)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
  (hH : ∀ t x, B.H.field t (-x) = B.H.field t x)
  (hraw : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw (t,(-x,-θ)) = -raw (t,(x,θ)))

include hF hM hH hraw

theorem coordinatePath_reflection_neg (t : Icc (0 : ℝ) D.T) :
    reflection P (B.coordinatePath G t) = -B.coordinatePath G t :=
  B.coefficients.velocityPath_odd P (D.frame_even hF) (D.frameDerivative_even hF hM) hH
    (forcingPath G) (G.path_reflection_neg hraw) t

theorem velocityPath_reflection_neg (t : Icc (0 : ℝ) D.T) :
    reflection P (B.velocityPath G t) = -B.velocityPath G t :=
  B.coefficients.physicalVelocity_odd P (D.frame_even hF) (D.frameDerivative_even hF hM) hH
    (forcingPath G) (G.path_reflection_neg hraw) t

theorem derivativePath_reflection_neg (t : Icc (0 : ℝ) D.T) :
    reflection P (B.derivativePath G t) = -B.derivativePath G t :=
  B.coefficients.physicalDerivative_odd P (D.frame_even hF) (D.frameDerivative_even hF hM) hH
    (forcingPath G) (G.path_reflection_neg hraw) t

theorem field_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    B.field G t (-x,((-θ : ℝ) : AddCircle P)) = -B.field G t (x,(θ : AddCircle P)) := by
  have he := representative_of_reflection P (B.velocityPath G t) (B.field G t)
    (B.field_ae G t) (smoothField_continuous P _ (B.field_smooth G t)) (-1)
    (by simpa only [neg_one_smul] using B.velocityPath_reflection_neg G hF hM hH hraw t)
    (x,(θ : AddCircle P))
  simpa only [Prod.neg_mk,AddCircle.coe_neg,neg_one_smul] using he

theorem normalResidual_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    B.normalResidual G t (-x,((-θ : ℝ) : AddCircle P)) =
      -B.normalResidual G t (x,(θ : AddCircle P)) := by
  have hf : forceField G t (-x,((-θ : ℝ) : AddCircle P)) =
      -forceField G t (x,(θ : AddCircle P)) := by
    change pointField P (forcingPath G) G.path_orbit t (-x,((-θ : ℝ) : AddCircle P)) =
      -pointField P (forcingPath G) G.path_orbit t (x,(θ : AddCircle P))
    rw [← G.raw_eq t (-x) (-θ),← G.raw_eq t x θ]
    exact hraw t x θ
  change (⟪D.normal.field t (-x),forceField G t (-x,((-θ : ℝ) : AddCircle P))⟫_ℝ-
    2*⟪D.normal.field t (-x),D.M.field t (-x) (B.field G t (-x,((-θ : ℝ) : AddCircle P)))⟫_ℝ)/
    ‖D.normal.field t (-x)‖^2 = _
  rw [D.normal_even hF,hM,hf,B.field_odd G hF hM hH hraw]
  simp only [map_neg,inner_neg_right,normalResidual]
  ring

theorem pressureField_even (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    B.pressureField G t (-x,((-θ : ℝ) : AddCircle P)) =
      B.pressureField G t (x,(θ : AddCircle P)) :=
  classicalPrimitive_joint_even P (B.normalResidual G t) (B.normalResidual_continuous G t)
    (B.normalResidual_mean_zero G t) (B.normalResidual_odd G hF hM hH hraw t) x θ

end EulerTransversePacketProvider.HistoryData
