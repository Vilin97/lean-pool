/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerCanonicalGraph
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPhysicalTensorLp

/-! Canonical spatial fields and all their actual derivative tensors are
in physical L². Their bounds have only explicit polynomial frequency loss. -/

@[expose] public section


noncomputable section

namespace EulerCylinderPhysicalTensor

open InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
  EulerCylinderCoordinates

/-- Physical phase, given by `(k*inner ℝ m x : ℝ)`. -/
def physicalPhase (P k : ℝ) (m : Vector3) (x : Vector3) : AddCircle P :=
  (k*inner ℝ m x : ℝ)

theorem physicalPhase_continuous (P k : ℝ) (m : Vector3) :
    Continuous (physicalPhase P k m) :=
  (AddCircle.continuous_mk' P).comp (continuous_const.mul (continuous_const.inner continuous_id))

theorem frequencyFactor_le_linear (k : ℝ) (hk : 1 ≤ k) (m : Vector3) :
    frequencyFactor k m ≤
      (‖coordinateEquiv.symm.toContinuousLinearMap‖*(1+‖m‖))*k := by
  unfold frequencyFactor
  rw [abs_of_nonneg (by linarith)]
  have h := mul_le_mul_of_nonneg_left (by nlinarith : 1+k*‖m‖ ≤ (1+‖m‖)*k)
    (norm_nonneg coordinateEquiv.symm.toContinuousLinearMap)
  exact h.trans_eq (mul_assoc _ _ _).symm

end EulerCylinderPhysicalTensor

namespace EulerAllOrderCorrectionData.FieldTower

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolev
  EulerMetricTransport EulerCylinderPhysicalTensor EulerGraphPressurePotential
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)] (A : EulerAllOrderCorrectionData.FieldTower P T)
  (k : ℝ) (m : Vector3)

/-- Physical point field, given by `physicalField P k m (A.pointField t)`. -/
def physicalPointField (t : Icc (0 : ℝ) T) : Vector3 → Vector3 :=
  physicalField P k m (A.pointField t)

theorem physicalPointField_smooth (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (A.physicalPointField k m t) :=
  physicalField_contDiff P k m (A.pointField t) (A.pointField_smooth t)

theorem physicalTensor_memLp (n : ℕ) (t : Icc (0 : ℝ) T) :
    MemLp (iteratedFDeriv ℝ n (A.physicalPointField k m t)) 2 volume :=
  EulerCylinderPhysicalTensor.physicalTensor_memLp P k m (A.pointField t) (A.pointField_smooth t) n
    (fun w => A.canonicalGraphWordPath (physicalPhase P k m) (physicalPhase_continuous P k m) n w t)
    (fun w => A.canonicalGraphWordPath_ae (physicalPhase P k m) (physicalPhase_continuous P k m) n
        w t)

/-- Physical tensor value, constructed using `physicalTensorLp`. -/
def physicalTensorValue (n : ℕ) (t : Icc (0 : ℝ) T) :
    Lp (Vector3 [×n]→L[ℝ] Vector3) 2 (volume : Measure Vector3) :=
  physicalTensorLp P k m (A.pointField t) (A.pointField_smooth t) n
    (fun w => A.canonicalGraphWordPath (physicalPhase P k m) (physicalPhase_continuous P k m) n w t)
    (fun w => A.canonicalGraphWordPath_ae (physicalPhase P k m) (physicalPhase_continuous P k m) n
        w t)

theorem physicalTensorValue_ae (n : ℕ) (t : Icc (0 : ℝ) T) :
    (A.physicalTensorValue k m n t : Vector3 → (Vector3 [×n]→L[ℝ] Vector3)) =ᵐ[volume]
      iteratedFDeriv ℝ n (A.physicalPointField k m t) :=
  physicalTensorLp_ae P k m (A.pointField t) (A.pointField_smooth t) n _ _

theorem physicalTensorValue_norm_le (n : ℕ) (t : Icc (0 : ℝ) T) :
    ‖A.physicalTensorValue k m n t‖ ≤ frequencyFactor k m^n * (4 : ℝ)^n *
      Real.sqrt (2/P+2*P)*‖A.realization (n+1) t‖ := by
  let θ := physicalPhase P k m
  have hθ := physicalPhase_continuous P k m
  have hP : 0 < P := Fact.out
  have hC : 0 ≤ 2/P+2*P := by positivity
  have hw (w : Fin n → Fin 4) :
      ‖A.canonicalGraphWordPath θ hθ n w t‖ ≤
        Real.sqrt (2/P+2*P)*‖A.realization (n+1) t‖ := by
    have h := Real.le_sqrt_of_sq_le (A.canonicalGraphWordPath_norm_sq_le θ hθ n w t)
    simpa only [Real.sqrt_mul hC,Real.sqrt_sq_eq_abs,abs_norm] using h
  have hs := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (Fin n → Fin 4))) => hw w)
  have hsum : (∑ w : Fin n → Fin 4, ‖A.canonicalGraphWordPath θ hθ n w t‖) ≤
      (4 : ℝ)^n*(Real.sqrt (2/P+2*P)*‖A.realization (n+1) t‖) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
      nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat] using hs
  have h := physicalTensorLp_norm_le P k m (A.pointField t) (A.pointField_smooth t) n
    (fun w => A.canonicalGraphWordPath θ hθ n w t)
    (fun w => A.canonicalGraphWordPath_ae θ hθ n w t)
  exact (h.trans (mul_le_mul_of_nonneg_left hsum
    (pow_nonneg (frequencyFactor_nonneg k m) n))).trans_eq (by ring)

end EulerAllOrderCorrectionData.FieldTower
