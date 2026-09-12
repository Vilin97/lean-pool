/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderSobolev
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedWeakDerivative
import LeanPool.NavierStokesAndEuler.Euler.Foundations.VectorCylinder

/-! Actual full cylinder gradients from the coordinate derivative Sobolev norms. -/

@[expose] public section

noncomputable section

namespace EulerCylinderGradient

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerCylinderCoordinates EulerVectorCylinder
open EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
    EulerLiftedWeakDerivative
open scoped ENNReal ContDiff

variable (period : ℝ) [Fact (0 < period)]

/-- All low-order real vector derivative words are bounded by the actual H⁶ norm. -/
theorem vector_word_pointwise_le_H6 (q : ℕ) {m : ℕ} (hm : m ≤ 3) (w : Fin m → Fin 4)
    (f : LiftDomain period → Domain q) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ 6, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure
        period))
    (x : LiftDomain period) :
    ‖iteratedFieldDerivative period w f x‖ ≤
      ((q : ℝ) * cylinderEmbeddingConstant period) * (85 * liftSobolevNorm period 6 f) := by
  have hA := vector_cylinder_pointwise_le_H3 period q (iteratedFieldDerivative period w f)
    (iteratedFieldDerivative_smooth period w f hf)
    (fun j hj v => word_memLp period (by omega : m+j ≤ 6) v w f hfL2) x
  exact hA.trans (mul_le_mul_of_nonneg_left (word_H3_le_H6 period hm w f)
    (mul_nonneg (Nat.cast_nonneg _) (cylinderEmbeddingConstant_nonneg period)))

section General
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [Fact (0 < period)] in
theorem tangent_coordinate_norm_le (v : LiftTangent) (i : Fin 4) :
    ‖coordinateEquiv.symm v i‖ ≤ ‖v‖ := by
  cases i using Fin.cases with
  | zero => simpa using norm_snd_le v
  | succ i => exact (PiLp.norm_apply_le v.1 i).trans (norm_fst_le v)

omit [Fact (0 < period)] in
/-- The full product-tangent operator norm is bounded by its four coordinate values. -/
theorem linear_norm_le_standard_sum (A : LiftTangent →L[ℝ] F) :
    ‖A‖ ≤ ∑ i : Fin 4, ‖A (standardDirection i)‖ := by
  apply A.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro v
  have he : (∑ i : Fin 4, (coordinateEquiv.symm v i) • EuclideanSpace.single i (1 : ℝ)) =
      coordinateEquiv.symm v := by
    ext i
    simp [Pi.single_apply, mul_ite]
  have hv : (∑ i : Fin 4, (coordinateEquiv.symm v i) • standardDirection i) = v := by
    change (∑ i : Fin 4, (coordinateEquiv.symm v i) • coordinateEquiv (EuclideanSpace.single i (1 :
        ℝ))) = v
    simp_rw [← map_smul]
    rw [← map_sum, he, ContinuousLinearEquiv.apply_symm_apply]
  have hA : A v = ∑ i : Fin 4, (coordinateEquiv.symm v i) • A (standardDirection i) := by
    simp_rw [← map_smul]
    rw [← map_sum, hv]
  rw [hA]
  calc
    _ ≤ ∑ i : Fin 4, ‖(coordinateEquiv.symm v i) • A (standardDirection i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin 4, ‖coordinateEquiv.symm v i‖ * ‖A (standardDirection i)‖ := by
        simp only [norm_smul]
    _ ≤ ∑ i : Fin 4, ‖v‖ * ‖A (standardDirection i)‖ := by
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (tangent_coordinate_norm_le v
          i) (norm_nonneg _))
    _ = _ := by rw [← Finset.mul_sum]; ring

omit [Fact (0 < period)] in
theorem fieldFDeriv_norm_le_standard_sum (f : LiftDomain period → F) (x : LiftDomain period) :
    ‖fieldFDeriv period f x‖ ≤ ∑ i : Fin 4, ‖fieldDerivative period (standardDirection i) f x‖ :=
  linear_norm_le_standard_sum (fieldFDeriv period f x)

/-- Actual full gradient integrability follows from the four genuine coordinate derivatives. -/
theorem fieldFDeriv_memLp_of_coordinates (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hD : ∀ i : Fin 4, MemLp (fieldDerivative period (standardDirection i) f) 2 (liftMeasure
        period)) :
    MemLp (fieldFDeriv period f) 2 (liftMeasure period) := by
  have hsum : MemLp (fun x => ∑ i : Fin 4, ‖fieldDerivative period (standardDirection i) f x‖) 2
      (liftMeasure period) :=
    memLp_finsetSum _ (fun i _ => (hD i).norm)
  have hc : Continuous (fieldFDeriv period f) := smoothField_continuous period _
      (fieldFDeriv_smooth period f hf)
  apply hsum.of_le hc.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
  exact fieldFDeriv_norm_le_standard_sum period f x

/-- The full-gradient L² norm is quantitatively bounded by the coordinate-gradient L² sum. -/
theorem fieldFDeriv_L2_le_coordinate_sum (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hD : ∀ i : Fin 4, MemLp (fieldDerivative period (standardDirection i) f) 2 (liftMeasure
        period)) :
    ‖(fieldFDeriv_memLp_of_coordinates period f hf hD).toLp (fieldFDeriv period f)‖ ≤
      ∑ i : Fin 4, (eLpNorm (fieldDerivative period (standardDirection i) f) 2 (liftMeasure
          period)).toReal := by
  have hA : eLpNorm (fieldFDeriv period f) 2 (liftMeasure period) ≤
      eLpNorm (fun x => ∑ i : Fin 4, ‖fieldDerivative period (standardDirection i) f x‖) 2
          (liftMeasure period) := by
    apply eLpNorm_mono
    intro x
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    exact fieldFDeriv_norm_le_standard_sum period f x
  have he : (fun x => ∑ i : Fin 4, ‖fieldDerivative period (standardDirection i) f x‖) =
      ∑ i : Fin 4, (fun x => ‖fieldDerivative period (standardDirection i) f x‖) := by
          funext x; simp
  rw [he] at hA
  have hB := eLpNorm_sum_le (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) => (hD i).1.norm)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  simp only [eLpNorm_norm] at hB
  have hC := ENNReal.toReal_mono (ENNReal.sum_ne_top.2 (fun i _ => (hD i).eLpNorm_ne_top))
      (hA.trans hB)
  rw [ENNReal.toReal_sum (fun i _ => (hD i).eLpNorm_ne_top)] at hC
  rw [Lp.norm_toLp]
  exact hC

end General
end EulerCylinderGradient
