/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldSobolev
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerPointwiseGevrey
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPhysicalTensor

@[expose] public section

/-! Pointwise physical graph bounds for the actual packet fields. The
estimates use the constructed Sobolev tower and its canonical representative. -/

noncomputable section

namespace EulerPacketCylinderField.Field

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSobolev EulerCylinderSmoothOrbit EulerPacketProfileRecursion
  EulerCylinderPhysicalTensor EulerGraphPullback EulerSobolevPointEvaluation
  EulerGevrey EulerMetricTransport EulerCylinderSobolevSpace
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField} (G : Field P T raw)

theorem toFieldTower_pointField_raw (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) :
    G.toFieldTower.pointField t (x,(θ : AddCircle P)) = raw (t,(x,θ)) := by
  have he := G.toFieldTower.pointField_unique t (pointField P G.path G.orbit t)
    (smoothField_continuous P _ (pointField_smooth P G.path G.orbit t))
    (pointField_ae P G.path G.orbit t)
  exact (congrFun he (x,(θ : AddCircle P))).trans (G.raw_eq t x θ).symm

theorem raw_graph_eq_pointField (t : Icc (0 : ℝ) T) (k : ℝ) (m : Space) :
    (fun x : Space => raw (t,(x,k*inner ℝ m x))) =
      physicalField P k m (G.toFieldTower.pointField t) := by
  funext x
  exact (G.toFieldTower_pointField_raw t x (k*inner ℝ m x)).symm

include G in
theorem raw_graph_contDiff (t : Icc (0 : ℝ) T) (k : ℝ) (m : Space) :
    ContDiff ℝ ∞ (fun x : Space => raw (t,(x,k*inner ℝ m x))) := by
  rw [G.raw_graph_eq_pointField]
  exact physicalField_contDiff P k m _ (G.toFieldTower.pointField_smooth t)

variable {G} {q d : ℕ} {R A : ℝ}

theorem WordBound.pointField_wordSum_le (hG : G.WordBound q R A d) (hq : 3 ≤ q)
    (t : Icc (0 : ℝ) T) (n : ℕ) (x : LiftDomain P) :
    (∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w (G.toFieldTower.pointField t) x‖) ≤
      sobolevEmbeddingConstant P 3*A*majorant R d n := by
  have h := G.toFieldTower.pointField_wordSum_le_block (n+q) q n hq le_rfl t x
  exact (h.trans (mul_le_mul_of_nonneg_left
    ((G.toFieldTower_blockNorm_le (n+q) q n le_rfl t).trans (hG n))
    (sobolevEmbeddingConstant_nonneg P 3))).trans_eq (by ring)

theorem WordBound.raw_graph_tensor_le (hG : G.WordBound q R A d) (hq : 3 ≤ q)
    (t : Icc (0 : ℝ) T) (k : ℝ) (m : Space) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (fun y : Space => raw (t,(y,k*inner ℝ m y))) x‖ ≤
      frequencyFactor k m^n*(sobolevEmbeddingConstant P 3*A*majorant R d n) := by
  rw [G.raw_graph_eq_pointField]
  exact (physicalTensor_norm_le P k m _ (G.toFieldTower.pointField_smooth t) n x).trans
    (mul_le_mul_of_nonneg_left (hG.pointField_wordSum_le hq t n _)
      (pow_nonneg (frequencyFactor_nonneg k m) n))

theorem WordBound.raw_graph_norm_le (hG : G.WordBound q R A 0) (hq : 3 ≤ q)
    (t : Icc (0 : ℝ) T) (k : ℝ) (m : Space) (x : Space) :
    ‖raw (t,(x,k*inner ℝ m x))‖ ≤ sobolevEmbeddingConstant P 3*A := by
  simpa [majorant] using hG.raw_graph_tensor_le hq t k m 0 x

theorem WordBound.raw_graph_fderiv_le (hG : G.WordBound q R A 0) (hq : 3 ≤ q)
    (t : Icc (0 : ℝ) T) (k : ℝ) (m : Space) (x : Space) :
    ‖fderiv ℝ (fun y : Space => raw (t,(y,k*inner ℝ m y))) x‖ ≤
      frequencyFactor k m*(sobolevEmbeddingConstant P 3*A*R) := by
  simpa [majorant] using hG.raw_graph_tensor_le hq t k m 1 x

/-- Composing the real graph field with a differentiable inverse map
preserves the amplitude and contributes its actual derivative norm. -/
theorem WordBound.raw_physical_fderiv_le (hG : G.WordBound q R A 0) (hq : 3 ≤ q)
    (t : Icc (0 : ℝ) T) (k : ℝ) (m : Space) (Y : Space → Space)
    (x : Space) (hY : DifferentiableAt ℝ Y x) :
    ‖fderiv ℝ (fun y : Space => raw (t,(Y y,k*inner ℝ m (Y y)))) x‖ ≤
      (frequencyFactor k m*(sobolevEmbeddingConstant P 3*A*R))*‖fderiv ℝ Y x‖ := by
  have hg := (G.raw_graph_contDiff t k m).differentiable (by simp) (Y x)
  change ‖fderiv ℝ ((fun y : Space => raw (t,(y,k*inner ℝ m y))) ∘ Y) x‖ ≤ _
  rw [fderiv_comp x hg hY]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (hG.raw_graph_fderiv_le hq t k m (Y x)) (norm_nonneg _))

end EulerPacketCylinderField.Field
