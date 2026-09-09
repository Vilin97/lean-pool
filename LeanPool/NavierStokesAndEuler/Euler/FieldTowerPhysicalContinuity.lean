/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerPhysicalL2
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPhysicalTensorDifference

@[expose] public section

/-! Every ordinary spatial derivative tensor of the actual physical graph
field is a continuous L² path. The proof controls differences by the genuine
continuous cylinder-word graph paths. -/

noncomputable section

namespace EulerAllOrderCorrectionData.FieldTower

open Set MeasureTheory Filter EulerLiftedGradientSpace EulerCylinderSobolev
  EulerMetricTransport EulerCylinderPhysicalTensor
open scoped Topology

variable {P T : ℝ} [Fact (0 < P)] (A : EulerAllOrderCorrectionData.FieldTower P T)
  (k : ℝ) (m : Vector3)

theorem physicalTensorValue_sub_norm_le (n : ℕ) (t s : Icc (0 : ℝ) T) :
    ‖A.physicalTensorValue k m n t-A.physicalTensorValue k m n s‖ ≤
      frequencyFactor k m^n * ∑ w : Fin n → Fin 4,
        ‖A.canonicalGraphWordPath (physicalPhase P k m) (physicalPhase_continuous P k m) n w t-
          A.canonicalGraphWordPath (physicalPhase P k m) (physicalPhase_continuous P k m) n w s‖ :=
  physicalTensor_difference_norm_le P k m (A.pointField t) (A.pointField s)
    (A.pointField_smooth t) (A.pointField_smooth s) n
    (fun w => A.canonicalGraphWordPath (physicalPhase P k m) (physicalPhase_continuous P k m) n w t)
    (fun w => A.canonicalGraphWordPath (physicalPhase P k m) (physicalPhase_continuous P k m) n w s)
    (fun w => A.canonicalGraphWordPath_ae (physicalPhase P k m) (physicalPhase_continuous P k m) n
      w t)
    (fun w => A.canonicalGraphWordPath_ae (physicalPhase P k m) (physicalPhase_continuous P k m) n
      w s)
    (A.physicalTensorValue k m n t) (A.physicalTensorValue k m n s)
    (A.physicalTensorValue_ae k m n t) (A.physicalTensorValue_ae k m n s)

theorem physicalTensorValue_continuous (n : ℕ) :
    Continuous (A.physicalTensorValue k m n) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun s => norm_nonneg _)
    (fun s => A.physicalTensorValue_sub_norm_le k m n s t) ?_
  have hc : Continuous (fun s : Icc (0 : ℝ) T => frequencyFactor k m^n * ∑ w : Fin n → Fin 4,
      ‖A.canonicalGraphWordPath (physicalPhase P k m) (physicalPhase_continuous P k m) n w s-
        A.canonicalGraphWordPath (physicalPhase P k m) (physicalPhase_continuous P k m) n w t‖) :=
    continuous_const.mul (continuous_finsetSum _ (fun w _ =>
      ((A.canonicalGraphWordPath (physicalPhase P k m)
        (physicalPhase_continuous P k m) n w).continuous.sub continuous_const).norm))
  simpa only [sub_self,norm_zero,Finset.sum_const_zero,mul_zero] using hc.tendsto t

/-- The physical tensor path is constructed from the actual graph field;
continuity is a theorem rather than an additional packet hypothesis. -/
def physicalTensorPath (n : ℕ) :
    C(Icc (0 : ℝ) T,Lp (Vector3 [×n]→L[ℝ] Vector3) 2 (volume : Measure Vector3)) :=
  ⟨A.physicalTensorValue k m n,A.physicalTensorValue_continuous k m n⟩

theorem physicalTensorPath_ae (n : ℕ) (t : Icc (0 : ℝ) T) :
    (A.physicalTensorPath k m n t : Vector3 → (Vector3 [×n]→L[ℝ] Vector3)) =ᵐ[volume]
      iteratedFDeriv ℝ n (A.physicalPointField k m t) :=
  A.physicalTensorValue_ae k m n t

end EulerAllOrderCorrectionData.FieldTower
