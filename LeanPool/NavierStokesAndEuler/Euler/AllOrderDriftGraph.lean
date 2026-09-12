/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerCanonicalGraph
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblySourceTower
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftPressure
import Mathlib.Algebra.Order.Star.Real

/-! Actual spatial L² paths of the constructed correction and its pressure
on every fixed continuous phase graph, including every cylinder word and
the genuine time derivative. -/

@[expose] public section


noncomputable section

namespace EulerAllOrderDriftCorrection

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolev
  EulerMetricTransport EulerVolterraConvolution EulerAllOrderCorrectionData

variable (P : ℝ) [Fact (0 < P)]
  {T : ℝ} {hT : 0 < T} {A : Data P T}
  (B : Budget P hT A)
  (θ : Vector3 → AddCircle P) (hθ : Continuous θ)

/-- Spatial L² path of the word derivative of the correction, restricted to the graph of `θ`. -/
def Budget.graphCorrectionWordPath (n : ℕ) (w : Fin n → Fin 4) :
    C(Icc (0 : ℝ) T,Lp Vector3 2 (volume : Measure Vector3)) :=
  (B.fieldTower P).canonicalGraphWordPath θ hθ n w

/-- Spatial L² path of the word derivative of the time derivative, on the graph of `θ`. -/
def Budget.graphTimeDerivativeWordPath (n : ℕ) (w : Fin n → Fin 4) :
    C(Icc (0 : ℝ) T,Lp Vector3 2 (volume : Measure Vector3)) :=
  (B.timeDerivativeTower P).canonicalGraphWordPath θ hθ n w

/-- Spatial L² path of the word derivative of the pressure, restricted to the graph of `θ`. -/
def Budget.graphPressureWordPath (n : ℕ) (w : Fin n → Fin 4) :
    C(Icc (0 : ℝ) T,Lp Vector3 2 (volume : Measure Vector3)) :=
  (B.pressureTower P).canonicalGraphWordPath θ hθ n w

theorem Budget.correctionTower_pointField (t : Icc (0 : ℝ) T) :
    (B.fieldTower P).pointField t = B.pointField P t :=
  (B.fieldTower P).pointField_unique t (B.pointField P t)
    (Continuous.uncurry_left t (B.pointField_joint_continuous P)) (B.pointField_ae P t)

theorem Budget.pressureTower_pointField (t : Icc (0 : ℝ) T) :
    (B.pressureTower P).pointField t = B.pointPressure P t :=
  (B.pressureTower P).pointField_unique t (B.pointPressure P t)
    (Continuous.uncurry_left t (B.pointPressure_joint_continuous P)) (B.pointPressure_ae P t)

theorem Budget.graphCorrectionWordPath_ae (n : ℕ) (w : Fin n → Fin 4)
    (t : Icc (0 : ℝ) T) :
    (B.graphCorrectionWordPath P θ hθ n w t : Vector3 → Vector3) =ᵐ[volume]
      fun x => iteratedFieldDerivative P w (B.pointField P t) (x,θ x) := by
  simpa only [Budget.graphCorrectionWordPath,B.correctionTower_pointField P t] using
    (B.fieldTower P).canonicalGraphWordPath_ae θ hθ n w t

theorem Budget.graphPressureWordPath_ae (n : ℕ) (w : Fin n → Fin 4)
    (t : Icc (0 : ℝ) T) :
    (B.graphPressureWordPath P θ hθ n w t : Vector3 → Vector3) =ᵐ[volume]
      fun x => iteratedFieldDerivative P w (B.pointPressure P t) (x,θ x) := by
  simpa only [Budget.graphPressureWordPath,B.pressureTower_pointField P t] using
    (B.pressureTower P).canonicalGraphWordPath_ae θ hθ n w t

theorem Budget.graphCorrectionWordPath_hasDerivAt (n : ℕ) (w : Fin n → Fin 4)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT.le (B.graphCorrectionWordPath P θ hθ n w))
      (B.graphTimeDerivativeWordPath P θ hθ n w ⟨t,ht.1.le,ht.2.le⟩) t :=
  (B.fieldTower P).canonicalGraphWordPath_hasDerivAt θ hθ (B.timeDerivativeTower P)
    hT.le n w (n+6) (by omega) t ht
    (B.fieldTower_hasDerivAt_timeDerivativeTower P (n+6) (by omega) t ht)

theorem Budget.graphCorrectionWordPath_initial (n : ℕ) (w : Fin n → Fin 4) :
    B.graphCorrectionWordPath P θ hθ n w ⟨0,le_rfl,hT.le⟩ = 0 := by
  have h := (B.fieldTower P).canonicalGraphWordPath_norm_sq_le θ hθ n w ⟨0,le_rfl,hT.le⟩
  rw [B.fieldTower_initial P (n+1),norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero] at h
  apply norm_eq_zero.mp
  change ‖(B.fieldTower P).canonicalGraphWordPath θ hθ n w ⟨0,le_rfl,hT.le⟩‖ = 0
  nlinarith [norm_nonneg ((B.fieldTower P).canonicalGraphWordPath θ hθ n w ⟨0,le_rfl,hT.le⟩)]

end EulerAllOrderDriftCorrection
