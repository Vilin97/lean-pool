/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderPhysicalTensor

@[expose] public section

/-! Ordinary derivative tensors of the actual graph field lie in spatial
L², with explicit frequency loss and the genuine graph-word norms. -/

noncomputable section

namespace EulerCylinderPhysicalTensor

open Set MeasureTheory EulerLiftedGradientSpace EulerMetricTransport
  EulerCylinderSobolev EulerGraphPressurePotential
open scoped ContDiff ENNReal NNReal

variable (P : ℝ) (k : ℝ) (m : Vector3)
  (f : LiftDomain P → Vector3)
  (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift P f x)) (n : ℕ)
  (u : (Fin n → Fin 4) → Lp Vector3 2 (volume : Measure Vector3))
  (hu : ∀ w, (u w : Vector3 → Vector3) =ᵐ[volume]
    fun x => iteratedFieldDerivative P w f (cylinderGraph P k m x))

include hu in
theorem graphWord_memLp (w : Fin n → Fin 4) :
    MemLp (fun x => iteratedFieldDerivative P w f (cylinderGraph P k m x)) 2 volume :=
  (memLp_congr_ae (hu w)).1 (Lp.memLp (u w))

include hf hu in
theorem physicalTensor_memLp :
    MemLp (iteratedFDeriv ℝ n (physicalField P k m f)) 2 volume := by
  have hs : MemLp (fun x => ∑ w : Fin n → Fin 4,
      ‖iteratedFieldDerivative P w f (cylinderGraph P k m x)‖) 2 volume :=
    memLp_finsetSum _ (fun w _ => (graphWord_memLp P k m f n u hu w).norm)
  have hm := hs.const_mul (frequencyFactor k m^n)
  have hc : Continuous (iteratedFDeriv ℝ n (physicalField P k m f)) :=
    (physicalField_contDiff P k m f hf).continuous_iteratedFDeriv (by simp)
  apply hm.of_le hc.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (frequencyFactor_nonneg k m) n)
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))]
  exact physicalTensor_norm_le P k m f hf n x

def physicalTensorLp : Lp (Vector3 [×n]→L[ℝ] Vector3) 2 (volume : Measure Vector3) :=
  (physicalTensor_memLp P k m f hf n u hu).toLp (iteratedFDeriv ℝ n (physicalField P k m f))

theorem physicalTensorLp_ae :
    (physicalTensorLp P k m f hf n u hu : Vector3 → (Vector3 [×n]→L[ℝ] Vector3)) =ᵐ[volume]
      iteratedFDeriv ℝ n (physicalField P k m f) :=
  (physicalTensor_memLp P k m f hf n u hu).coeFn_toLp

theorem physicalTensorLp_norm_le :
    ‖physicalTensorLp P k m f hf n u hu‖ ≤ frequencyFactor k m^n * ∑ w, ‖u w‖ := by
  let β : ℝ≥0 := ⟨frequencyFactor k m^n,pow_nonneg (frequencyFactor_nonneg k m) n⟩
  have hA : eLpNorm (iteratedFDeriv ℝ n (physicalField P k m f)) 2 volume ≤
      (β : ℝ≥0∞)*eLpNorm (fun x => ∑ w : Fin n → Fin 4,
        ‖iteratedFieldDerivative P w f (cylinderGraph P k m x)‖) 2 volume := by
    apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    filter_upwards [] with x
    apply NNReal.coe_le_coe.mp
    change ‖iteratedFDeriv ℝ n (physicalField P k m f) x‖ ≤
      (frequencyFactor k m^n)*‖∑ w : Fin n → Fin 4,
        ‖iteratedFieldDerivative P w f (cylinderGraph P k m x)‖‖
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    exact physicalTensor_norm_le P k m f hf n x
  have he : (fun x => ∑ w : Fin n → Fin 4,
      ‖iteratedFieldDerivative P w f (cylinderGraph P k m x)‖) =
      ∑ w : Fin n → Fin 4, (fun x => ‖iteratedFieldDerivative P w f (cylinderGraph P k m x)‖) := by
    funext x
    simp only [Finset.sum_apply]
  rw [he] at hA
  have hB := eLpNorm_sum_le (fun w (_ : w ∈ (Finset.univ : Finset (Fin n → Fin 4))) =>
    (graphWord_memLp P k m f n u hu w).1.norm) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  simp only [eLpNorm_norm] at hB
  have hfinit : (β : ℝ≥0∞) * ∑ w : Fin n → Fin 4,
      eLpNorm (fun x => iteratedFieldDerivative P w f (cylinderGraph P k m x)) 2 volume ≠ ⊤ := by
    apply ENNReal.mul_ne_top ENNReal.coe_ne_top
    exact ENNReal.sum_ne_top.2 (fun w _ => (graphWord_memLp P k m f n u hu w).eLpNorm_ne_top)
  have hm : (β : ℝ≥0∞)*eLpNorm
      (∑ w : Fin n → Fin 4, (fun x => ‖iteratedFieldDerivative P w f (cylinderGraph P k m x)‖)) 2
        volume ≤
      (β : ℝ≥0∞)*∑ w : Fin n → Fin 4,
        eLpNorm (fun x => iteratedFieldDerivative P w f (cylinderGraph P k m x)) 2 volume := by
    gcongr
  have hR := ENNReal.toReal_mono hfinit (hA.trans hm)
  rw [ENNReal.toReal_mul,ENNReal.coe_toReal,
    ENNReal.toReal_sum (fun w _ => (graphWord_memLp P k m f n u hu w).eLpNorm_ne_top)] at hR
  have hn (w : Fin n → Fin 4) :
      (eLpNorm (fun x => iteratedFieldDerivative P w f (cylinderGraph P k m x)) 2 volume).toReal =
        ‖u w‖ := by
    rw [Lp.norm_def,eLpNorm_congr_ae (hu w)]
  have hβ : (β : ℝ) = frequencyFactor k m^n := rfl
  rw [hβ] at hR
  simpa only [physicalTensorLp,Lp.norm_toLp,hn] using hR

end EulerCylinderPhysicalTensor
