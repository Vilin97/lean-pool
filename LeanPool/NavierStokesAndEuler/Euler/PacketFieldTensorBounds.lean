/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldGraphBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderScalarGradient

@[expose] public section

/-! Full space-angle derivative tensors are bounded by the actual packet
word budgets. This includes the scalar pressure via its norm-one embedding. -/

noncomputable section

namespace EulerPacketCylinderField.Field

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSobolev EulerCylinderSmoothOrbit EulerPacketProfileRecursion
  EulerCylinderPhysicalTensor EulerSobolevPointEvaluation EulerGevrey
  EulerMetricTransport EulerCylinderSobolevSpace EulerCylinderCoordinates
  EulerCylinderScalarPrimitive
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField} (G : Field P T raw)

theorem raw_eq_euclidean (t : Icc (0 : ℝ) T) :
    (fun z : LiftTangent => raw (t,z)) =
      euclideanLift P (G.toFieldTower.pointField t) 0 ∘
        coordinateEquiv.symm.toContinuousLinearMap := by
  funext z
  have hz : coordinateEquiv (coordinateEquiv.symm.toContinuousLinearMap z) = z :=
    coordinateEquiv.apply_symm_apply z
  simp only [Function.comp_apply,euclideanLift,localFieldLift,
    Prod.fst_zero,Prod.snd_zero,zero_add,hz]
  exact (G.toFieldTower_pointField_raw t z.1 z.2).symm

variable {G} {q d : ℕ} {R A : ℝ}

theorem WordBound.raw_tensor_le (hG : G.WordBound q R A d) (hq : 3 ≤ q)
    (t : Icc (0 : ℝ) T) (n : ℕ) (z : LiftTangent) :
    ‖iteratedFDeriv ℝ n (fun y : LiftTangent => raw (t,y)) z‖ ≤
      ‖coordinateEquiv.symm.toContinuousLinearMap‖^n *
        (sobolevEmbeddingConstant P 3*A*majorant R d n) := by
  have hf := G.toFieldTower.pointField_smooth t
  have ht := euclideanLift_tensor_norm_le P n (G.toFieldTower.pointField t) hf 0
    (coordinateEquiv.symm z)
  have he (w : Fin n → Fin 4) :
      euclideanLift P (iteratedFieldDerivative P w (G.toFieldTower.pointField t)) 0
        (coordinateEquiv.symm z) =
      iteratedFieldDerivative P w (G.toFieldTower.pointField t) (z.1,(z.2 : AddCircle P)) := by
    simp only [euclideanLift,Function.comp_apply,localFieldLift,ContinuousLinearEquiv.apply_symm_apply,
      Prod.fst_zero,Prod.snd_zero,zero_add]
  simp_rw [he] at ht
  rw [G.raw_eq_euclidean t,
    coordinateEquiv.symm.toContinuousLinearMap.iteratedFDeriv_comp_right
      (euclideanLift_smooth P _ hf 0) z (by simp)]
  have hc := (iteratedFDeriv ℝ n (euclideanLift P (G.toFieldTower.pointField t) 0)
    (coordinateEquiv.symm z)).norm_compContinuousLinearMap_le
      (fun _ : Fin n => coordinateEquiv.symm.toContinuousLinearMap)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hc
  exact hc.trans ((mul_le_mul_of_nonneg_right
    (ht.trans (hG.pointField_wordSum_le hq t n _)) (pow_nonneg (norm_nonneg _) n)).trans_eq
      (mul_comm _ _))

theorem WordBound.raw_fderiv_le (hG : G.WordBound q R A d) (hq : 3 ≤ q)
    (t : Icc (0 : ℝ) T) (z : LiftTangent) :
    ‖fderiv ℝ (fun y : LiftTangent => raw (t,y)) z‖ ≤
      ‖coordinateEquiv.symm.toContinuousLinearMap‖ *
        (sobolevEmbeddingConstant P 3*A*majorant R d 1) := by
  simpa only [norm_iteratedFDeriv_one,pow_one] using hG.raw_tensor_le hq t 1 z

end EulerPacketCylinderField.Field
