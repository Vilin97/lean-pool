/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftGraph
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftPressureBounds
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerPointwiseGevrey

@[expose] public section

/-! Pointwise mixed-word Gevrey estimates for the actual common
correction, its signed pressure gradient, and its actual time derivative. -/

noncomputable section

namespace EulerAllOrderDriftCorrection

open Set Finset EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerAllOrderCorrectionData
  EulerSobolevGevreyOperators EulerCylinderSobolev EulerMetricTransport
  EulerSobolevPointEvaluation

variable (P : ℝ) [Fact (0 < P)]
  {T : ℝ} {hT : 0 < T} {A : Data P T} (B : Budget P hT A)

/-- The canonical representative of the actual derivative tower is the
same time derivative already selected by the finite PDE construction. -/
theorem Budget.timeDerivativeTower_pointField (t : Icc (0 : ℝ) T) :
    (B.timeDerivativeTower P).pointField t = B.pointTimeDerivative P t := by
  funext x
  rw [(B.timeDerivativeTower P).pointField_eq_high 6 (by omega) t x,
    ← B.source_eq_timeDerivativeTower P 6 le_rfl t,
    ← B.solution_eq_realization P 6 le_rfl]
  rfl

theorem Budget.pointField_wordSum_bound (n : ℕ) (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    (∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w (B.pointField P t) x‖) ≤
      (sobolevEmbeddingConstant P 3*B.correctionSize P)*(B.reducedRadius P)⁻¹^n*(n.factorial : ℝ)^2
        := by
  have h := (B.fieldTower P).pointField_wordSum_gevrey (n+6) 6 n n (by omega) (by omega) le_rfl
    (B.reducedRadius P) (B.correctionSize P) (B.reducedRadius_pos P) t
    (B.fieldTower_reducedNorm P (n+6) n (by omega) t) x
  simpa only [B.correctionTower_pointField P t] using h

theorem Budget.pointPressure_wordSum_bound (n : ℕ) (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    (∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w (B.pointPressure P t) x‖) ≤
      (sobolevEmbeddingConstant P 3*(B.pressureCost P (n+6) (by omega)*B.delta))*
        (B.reducedRadius P)⁻¹^n*(n.factorial : ℝ)^2 := by
  have h := (B.pressureTower P).pointField_wordSum_gevrey (n+6) 6 n n (by omega) (by omega) le_rfl
    (B.reducedRadius P) (B.pressureCost P (n+6) (by omega)*B.delta) (B.reducedRadius_pos P) t
    (B.pressureTower_reducedNorm_delta P (n+6) (by omega) n (by omega) (n+6) (by omega) t) x
  simpa only [B.pressureTower_pointField P t] using h

theorem Budget.pointTimeDerivative_wordSum_bound (n : ℕ) (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    (∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w (B.pointTimeDerivative P t) x‖) ≤
      (sobolevEmbeddingConstant P 3*(B.timeDerivativeCost P (n+6) (by omega)*B.delta))*
        (B.reducedRadius P)⁻¹^n*(n.factorial : ℝ)^2 := by
  have h := (B.timeDerivativeTower P).pointField_wordSum_gevrey (n+6) 6 n n (by omega) (by omega)
    le_rfl
    (B.reducedRadius P) (B.timeDerivativeCost P (n+6) (by omega)*B.delta) (B.reducedRadius_pos P) t
    (B.timeDerivativeTower_reducedNorm_delta P (n+6) (by omega) n (by omega) (n+6) (by omega) t) x
  simpa only [B.timeDerivativeTower_pointField P t] using h

end EulerAllOrderDriftCorrection
