/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerPhysicalL2
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPhysicalTensor
import LeanPool.NavierStokesAndEuler.Euler.CylinderPhysicalTensorLp
import LeanPool.NavierStokesAndEuler.Euler.Foundations.MollifierUniform
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder

/-! Every ordinary spatial derivative tensor of the actual physical graph
field is a continuous L² path. The proof controls differences by the genuine
continuous cylinder-word graph paths. -/

section

/-! The physical tensor estimate controls differences of actual L²
representatives, which supplies time continuity without a domination premise. -/

@[expose] public section

noncomputable section

namespace EulerCylinderPhysicalTensor

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolev
  EulerGraphPressurePotential EulerMetricTransport
open scoped ContDiff

variable (P k : ℝ) (m : Vector3)

theorem physicalTensor_norm_le_of_ae (f : LiftDomain P → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift P f x)) (n : ℕ)
    (u : (Fin n → Fin 4) → Lp Vector3 2 (volume : Measure Vector3))
    (hu : ∀ w, (u w : Vector3 → Vector3) =ᵐ[volume]
      fun x => iteratedFieldDerivative P w f (cylinderGraph P k m x))
    (v : Lp (Vector3 [×n]→L[ℝ] Vector3) 2 (volume : Measure Vector3))
    (hv : (v : Vector3 → (Vector3 [×n]→L[ℝ] Vector3)) =ᵐ[volume]
      iteratedFDeriv ℝ n (physicalField P k m f)) :
    ‖v‖ ≤ frequencyFactor k m^n * ∑ w, ‖u w‖ := by
  have he : v = physicalTensorLp P k m f hf n u hu :=
    Lp.ext (hv.trans (physicalTensorLp_ae P k m f hf n u hu).symm)
  rw [he]
  exact physicalTensorLp_norm_le P k m f hf n u hu

theorem physicalTensor_difference_norm_le (f g : LiftDomain P → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift P f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift P g x)) (n : ℕ)
    (u v : (Fin n → Fin 4) → Lp Vector3 2 (volume : Measure Vector3))
    (hu : ∀ w, (u w : Vector3 → Vector3) =ᵐ[volume]
      fun x => iteratedFieldDerivative P w f (cylinderGraph P k m x))
    (hv : ∀ w, (v w : Vector3 → Vector3) =ᵐ[volume]
      fun x => iteratedFieldDerivative P w g (cylinderGraph P k m x))
    (F G : Lp (Vector3 [×n]→L[ℝ] Vector3) 2 (volume : Measure Vector3))
    (hF : (F : Vector3 → (Vector3 [×n]→L[ℝ] Vector3)) =ᵐ[volume]
      iteratedFDeriv ℝ n (physicalField P k m f))
    (hG : (G : Vector3 → (Vector3 [×n]→L[ℝ] Vector3)) =ᵐ[volume]
      iteratedFDeriv ℝ n (physicalField P k m g)) :
    ‖F-G‖ ≤ frequencyFactor k m^n * ∑ w, ‖u w-v w‖ := by
  refine physicalTensor_norm_le_of_ae P k m (fun x => f x-g x)
    (fun x => (hf x).sub (hg x)) n (fun w => u w-v w) ?_ (F-G) ?_
  · intro w
    filter_upwards [Lp.coeFn_sub (u w) (v w),hu w,hv w] with x hs hx hy
    exact hs.trans ((congrArg₂ (·-·) hx hy).trans
      (congrFun (EulerMollifierUniform.word_sub P w f g hf hg) (cylinderGraph P k m x)).symm)
  · filter_upwards [Lp.coeFn_sub F G,hF,hG] with x hs hx hy
    have hd := iteratedFDeriv_sub_apply (x := x)
      ((physicalField_contDiff P k m f hf).of_le (by simp : (n : ℕ∞ω) ≤ ∞)).contDiffAt
      ((physicalField_contDiff P k m g hg).of_le (by simp : (n : ℕ∞ω) ≤ ∞)).contDiffAt
    exact hs.trans ((congrArg₂ (·-·) hx hy).trans hd.symm)

end EulerCylinderPhysicalTensor

end
end

end

@[expose] public section

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
        ‖A.canonicalGraphWordPath (physicalPhase P k m) (physicalPhase_continuous P k m) n w t -
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
      ‖A.canonicalGraphWordPath (physicalPhase P k m) (physicalPhase_continuous P k m) n w s -
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
