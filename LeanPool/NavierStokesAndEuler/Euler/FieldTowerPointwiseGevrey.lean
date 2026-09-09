/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerRepresentative
public import LeanPool.NavierStokesAndEuler.Euler.SobolevWordLevel
public import LeanPool.NavierStokesAndEuler.Euler.GevreyRadiusReduction

@[expose] public section

/-! Actual pointwise mixed derivatives from the finite weighted Sobolev
norms of one coherent field tower. No pointwise estimate is assumed. -/

noncomputable section

namespace EulerAllOrderCorrectionData.FieldTower

open Set MeasureTheory Finset EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerSpatialSobolevInverse EulerSobolevPointEvaluation
  EulerSobolevWordLevel EulerH6Pressure EulerStrongSmoothJet EulerMetricTransport
  EulerSobolevGevreyOperators EulerPacketWeights
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)] (A : EulerAllOrderCorrectionData.FieldTower P T)

/-- The canonical representative has exactly the mixed derivative
represented by the genuine Sobolev word at any retained high order. -/
theorem pointField_wordAtLevel (s q n : ℕ) (hq : 3 ≤ q) (hn : n+q ≤ s)
    (w : Fin n → Fin 4) (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    iteratedFieldDerivative P w (A.pointField t) x =
      pointEvaluation P x (restrictOperator P hq
        (wordAtLevel P q n w hn (A.realization s t))) := by
  symm
  apply pointEvaluation_eq
  · exact smoothField_continuous P _ (iteratedFieldDerivative_smooth P w _ (A.pointField_smooth t))
  · have ha : (value P (A.realization s t) : LiftDomain P → Vector3) =ᵐ[liftMeasure P]
        A.pointField t := by rw [A.value_eq]; exact A.pointField_ae t
    exact wordAtLevel_ae P q n w hn (A.realization s t) (A.pointField t) ha (A.pointField_smooth t)

/-- The sum of all mixed pointwise words is bounded by the actual
external Sobolev block, with a fixed base-order evaluation constant. -/
theorem pointField_wordSum_le_block (s q n : ℕ) (hq : 3 ≤ q) (hn : n+q ≤ s)
    (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    (∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w (A.pointField t) x‖) ≤
      sobolevEmbeddingConstant P 3*blockNorm P (toJet P (A.realization s t)) q n := by
  have hS := sobolevEmbeddingConstant_nonneg P 3
  have hw (w : Fin n → Fin 4) :
      ‖iteratedFieldDerivative P w (A.pointField t) x‖ ≤
        sobolevEmbeddingConstant P 3*sobolevSize P (directions := standardDirection) q
          ((toJet P (A.realization s t)).word w) := by
    rw [A.pointField_wordAtLevel s q n hq hn w t x]
    have hb := representative_bound P
      (restrictOperator P hq (wordAtLevel P q n w hn (A.realization s t))) x
    have hr := restrictOperator_bound P hq (wordAtLevel P q n w hn (A.realization s t))
    have hu := norm_le_sumNorm P (wordAtLevel P q n w hn (A.realization s t))
    have he : sumNorm P (wordAtLevel P q n w hn (A.realization s t)) =
        sobolevSize P (directions := standardDirection) q ((toJet P (A.realization s t)).word w) :=
          by
      rw [sumNorm_wordAtLevel, sobolevSize_eq P
        (EulerH6Pressure.SpatialJet.derivativeJet (toJet P (A.realization s t)) w hn)]
    exact hb.trans (mul_le_mul_of_nonneg_left ((hr.trans hu).trans_eq he) hS)
  calc
    _ ≤ ∑ w : Fin n → Fin 4, sobolevEmbeddingConstant P 3*
        sobolevSize P (directions := standardDirection) q ((toJet P (A.realization s t)).word w) :=
      sum_le_sum fun w _ => hw w
    _ = _ := by rw [← mul_sum, blockNorm_eq_word_sizes (toJet P (A.realization s t)) hn]

/-- Selecting the actual nth summand of a weighted Sobolev norm gives
the full pointwise mixed-word bound, without an alphabet factor. -/
theorem pointField_wordSum_weighted (s q N n : ℕ) (hq : 3 ≤ q)
    (hns : n+q ≤ s) (hnN : n ≤ N) (ρ : ℝ) (hρ : 0 < ρ)
    (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    weight ρ n*(∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w (A.pointField t) x‖) ≤
      sobolevEmbeddingConstant P 3*weightedNorm P q N ρ (A.realization s t) := by
  have hs := single_le_sum (s := range (N+1))
    (fun j _ => mul_nonneg (weight_pos hρ j).le
      (blockNorm_nonneg (q := q) (n := j) (toJet P (A.realization s t))))
    (show n ∈ range (N+1) by simp; omega)
  have hw := mul_le_mul_of_nonneg_left (A.pointField_wordSum_le_block s q n hq hns t x)
    (weight_pos hρ n).le
  calc
    _ ≤ weight ρ n*(sobolevEmbeddingConstant P 3*blockNorm P (toJet P (A.realization s t)) q n) :=
      hw
    _ = sobolevEmbeddingConstant P 3*(weight ρ n*blockNorm P (toJet P (A.realization s t)) q n) :=
      by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (sobolevEmbeddingConstant_nonneg P 3)

/-- A genuine weighted Hq bound gives the literal pointwise Gevrey
estimate for every spatial/angular word, with radius reciprocal 1/ρ. -/
theorem pointField_wordSum_gevrey (s q N n : ℕ) (hq : 3 ≤ q)
    (hns : n+q ≤ s) (hnN : n ≤ N) (ρ C : ℝ) (hρ : 0 < ρ)
    (t : Icc (0 : ℝ) T) (hC : weightedNorm P q N ρ (A.realization s t) ≤ C)
    (x : LiftDomain P) :
    (∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w (A.pointField t) x‖) ≤
      (sobolevEmbeddingConstant P 3*C)*(ρ⁻¹)^n*(n.factorial : ℝ)^2 := by
  have hw := (A.pointField_wordSum_weighted s q N n hq hns hnN ρ hρ t x).trans
    (mul_le_mul_of_nonneg_left hC (sobolevEmbeddingConstant_nonneg P 3))
  have hd : (∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w (A.pointField t) x‖) ≤
      (sobolevEmbeddingConstant P 3*C)/weight ρ n := by
    apply (le_div_iff₀ (weight_pos hρ n)).mpr
    simpa only [mul_comm] using hw
  exact hd.trans_eq (by rw [weight, div_div_eq_mul_div, inv_pow]; ring)

theorem pointField_word_gevrey (s q N n : ℕ) (hq : 3 ≤ q)
    (hns : n+q ≤ s) (hnN : n ≤ N) (ρ C : ℝ) (hρ : 0 < ρ)
    (t : Icc (0 : ℝ) T) (hC : weightedNorm P q N ρ (A.realization s t) ≤ C)
    (w : Fin n → Fin 4) (x : LiftDomain P) :
    ‖iteratedFieldDerivative P w (A.pointField t) x‖ ≤
      (sobolevEmbeddingConstant P 3*C)*(ρ⁻¹)^n*(n.factorial : ℝ)^2 :=
  (single_le_sum (fun v _ => norm_nonneg (iteratedFieldDerivative P v (A.pointField t) x))
    (mem_univ w)).trans
    (A.pointField_wordSum_gevrey s q N n hq hns hnN ρ C hρ t hC x)

end EulerAllOrderCorrectionData.FieldTower
