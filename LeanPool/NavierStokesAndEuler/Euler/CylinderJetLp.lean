/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderCoverTensor
public import LeanPool.NavierStokesAndEuler.Euler.CylinderDescentJets

@[expose] public section

/-! The genuine descended derivative tensors of a smooth cylinder field
lie in cylinder L² whenever its actual coordinate words do. The bound
keeps the ordered-word sum; there is no extra alphabet factor. -/

noncomputable section


namespace EulerCylinderJetLp

open Set MeasureTheory EulerLiftedGradientSpace EulerMetricTransport EulerCylinderCoordinates
  EulerCylinderSobolev EulerCylinderSmoothOrbit EulerCylinderCoverDescent
open scoped ContDiff ENNReal NNReal

variable (P : ℝ) [Fact (0 < P)] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [Fact (0 < P)] [NormedAddCommGroup V] [NormedSpace ℝ V] in
theorem cover_periodic (f : LiftDomain P → V) (c : AddSubgroup.zmultiples P) (z : LiftTangent) :
    f (coveringMap P (z.1,(c : ℝ)+z.2)) = f (coveringMap P z) :=
  congrArg f (EulerCylinderMeasureDescent.coveringMap_deck P c z)

def tensor (f : LiftDomain P → V) (n : ℕ) (q : LiftDomain P) : LiftTangent [×n]→L[ℝ] V :=
  jetSeries P (fun z => f (coveringMap P z)) q n

theorem tensor_continuous (f : LiftDomain P → V)
    (hf : ∀ q, ContDiff ℝ ∞ (localFieldLift P f q)) (n : ℕ) :
    Continuous (tensor P f n) :=
  descend_continuous P _
    ((coverField_contDiff P f hf).continuous_iteratedFDeriv (by simp))
    (fiber_constant_of_deck P _ (iteratedFDeriv_deck P _ (cover_periodic P f) n))

theorem tensor_norm_le (f : LiftDomain P → V)
    (hf : ∀ q, ContDiff ℝ ∞ (localFieldLift P f q)) (n : ℕ) (q : LiftDomain P) :
    ‖tensor P f n q‖ ≤ ‖coordinateEquiv.symm.toContinuousLinearMap‖^n *
      ∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w f q‖ := by
  have h := coverField_tensor_norm_le P n f hf (sectionPoint P q)
  simpa only [tensor, jetSeries, descend, coveringMap_sectionPoint] using h

theorem tensor_memLp (f : LiftDomain P → V)
    (hf : ∀ q, ContDiff ℝ ∞ (localFieldLift P f q)) (n : ℕ)
    (hLp : ∀ w : Fin n → Fin 4, MemLp (iteratedFieldDerivative P w f) 2 (liftMeasure P)) :
    MemLp (tensor P f n) 2 (liftMeasure P) := by
  have hs : MemLp (fun q => ∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w f q‖)
      2 (liftMeasure P) := memLp_finsetSum _ (fun w _ => (hLp w).norm)
  apply (hs.const_mul (‖coordinateEquiv.symm.toContinuousLinearMap‖^n)).of_le
    (tensor_continuous P f hf n).aestronglyMeasurable
  filter_upwards [] with q
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) n)
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))]
  exact tensor_norm_le P f hf n q

theorem tensor_eLpNorm_le (f : LiftDomain P → V)
    (hf : ∀ q, ContDiff ℝ ∞ (localFieldLift P f q)) (n : ℕ)
    (hLp : ∀ w : Fin n → Fin 4, MemLp (iteratedFieldDerivative P w f) 2 (liftMeasure P)) :
    (eLpNorm (tensor P f n) 2 (liftMeasure P)).toReal ≤
      ‖coordinateEquiv.symm.toContinuousLinearMap‖^n *
        ∑ w : Fin n → Fin 4, (eLpNorm (iteratedFieldDerivative P w f) 2 (liftMeasure P)).toReal :=
          by
  let C : ℝ≥0 := ⟨‖coordinateEquiv.symm.toContinuousLinearMap‖^n, pow_nonneg (norm_nonneg _) n⟩
  have hA : eLpNorm (tensor P f n) 2 (liftMeasure P) ≤
      (C : ℝ≥0∞) * eLpNorm
        (fun q => ∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w f q‖) 2 (liftMeasure P) := by
    apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    filter_upwards [] with q
    apply NNReal.coe_le_coe.mp
    change ‖tensor P f n q‖ ≤ ‖coordinateEquiv.symm.toContinuousLinearMap‖^n *
      ‖∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w f q‖‖
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    exact tensor_norm_le P f hf n q
  have he : (fun q => ∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w f q‖) =
      ∑ w : Fin n → Fin 4, (fun q => ‖iteratedFieldDerivative P w f q‖) := by
    funext q
    simp only [Finset.sum_apply]
  rw [he] at hA
  have hB := eLpNorm_sum_le
    (fun w (_ : w ∈ (Finset.univ : Finset (Fin n → Fin 4))) => (hLp w).1.norm)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  simp only [eLpNorm_norm] at hB
  have hC : (C : ℝ≥0∞) * ∑ w : Fin n → Fin 4,
      eLpNorm (iteratedFieldDerivative P w f) 2 (liftMeasure P) ≠ ⊤ := by
    apply ENNReal.mul_ne_top ENNReal.coe_ne_top
    exact ENNReal.sum_ne_top.mpr (fun w _ => (hLp w).eLpNorm_ne_top)
  have hm : (C : ℝ≥0∞) * eLpNorm
      (∑ w : Fin n → Fin 4, (fun q => ‖iteratedFieldDerivative P w f q‖)) 2 (liftMeasure P) ≤
      (C : ℝ≥0∞) * ∑ w : Fin n → Fin 4,
        eLpNorm (iteratedFieldDerivative P w f) 2 (liftMeasure P) := by gcongr
  have h := ENNReal.toReal_mono hC (hA.trans hm)
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_sum (fun w _ => (hLp w).eLpNorm_ne_top)] at h
  exact h

end EulerCylinderJetLp
