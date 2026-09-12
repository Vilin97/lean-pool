/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderJetLp
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerSmoothTimeField
import LeanPool.NavierStokesAndEuler.Euler.Foundations.StrongSmoothJet

/-! Descended derivative tensors of a coherent Sobolev field tower have
their actual cylinder L² bounds. The estimate selects a summand of the
weighted H6 norm and has no loss depending on the derivative order. -/

@[expose] public section


noncomputable section


namespace EulerAllOrderCorrectionData.FieldTower

open Set MeasureTheory Finset EulerLiftedGradientSpace EulerMetricTransport
  EulerCylinderSobolevSpace EulerCylinderSobolev EulerSpatialSobolevInverse
  EulerStrongSmoothJet EulerSobolevGevreyOperators EulerH6Pressure EulerPacketWeights
  EulerCylinderCoordinates EulerCylinderJetLp EulerCylinderCoverDescent EulerJetProductBounds
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)] (A : FieldTower P T)

theorem pointField_word_ae (s n : ℕ) (hn : n ≤ s) (w : Fin n → Fin 4)
    (t : Icc (0 : ℝ) T) :
    ((toJet P (A.realization s t)).word w : LiftDomain P → Vector3) =ᵐ[liftMeasure P]
      iteratedFieldDerivative P w (A.pointField t) := by
  apply jet_word_ae P hn (value P (A.realization s t)) (toJet P (A.realization s t)) w
    (A.pointField t)
  · rw [A.value_eq]
    exact A.pointField_ae t
  · exact A.pointField_smooth t

theorem pointField_word_memLp (n : ℕ) (w : Fin n → Fin 4) (t : Icc (0 : ℝ) T) :
    MemLp (iteratedFieldDerivative P w (A.pointField t)) 2 (liftMeasure P) :=
  (Lp.memLp ((toJet P (A.realization n t)).word w)).ae_eq
    (A.pointField_word_ae n n le_rfl w t)

theorem pointField_word_norm (s n : ℕ) (hn : n ≤ s) (w : Fin n → Fin 4)
    (t : Icc (0 : ℝ) T) :
    (eLpNorm (iteratedFieldDerivative P w (A.pointField t)) 2 (liftMeasure P)).toReal =
      ‖(toJet P (A.realization s t)).word w‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (A.pointField_word_ae s n hn w t)]

theorem coverTensor_memLp (n : ℕ) (t : Icc (0 : ℝ) T) :
    MemLp (tensor P (A.pointField t) n) 2 (liftMeasure P) :=
  tensor_memLp P (A.pointField t) (A.pointField_smooth t) n
    (fun w => A.pointField_word_memLp n w t)

theorem coverTensor_norm_le_level (s n : ℕ) (hn : n ≤ s) (t : Icc (0 : ℝ) T) :
    (eLpNorm (tensor P (A.pointField t) n) 2 (liftMeasure P)).toReal ≤
      ‖coordinateEquiv.symm.toContinuousLinearMap‖^n * levelNorm P (toJet P (A.realization s t)) n
          := by
  have h := tensor_eLpNorm_le P (A.pointField t) (A.pointField_smooth t) n
    (fun w => A.pointField_word_memLp n w t)
  simpa only [A.pointField_word_norm s n hn, levelNorm_eq_words] using h

theorem coverTensor_weighted (n : ℕ) (ρ C : ℝ) (hρ : 0 < ρ)
    (t : Icc (0 : ℝ) T)
    (hb : weightedNorm P 6 n ρ (A.realization (n + 6) t) ≤ C) :
    (eLpNorm (tensor P (A.pointField t) n) 2 (liftMeasure P)).toReal ≤
      C * (‖coordinateEquiv.symm.toContinuousLinearMap‖*ρ⁻¹)^n * (n.factorial : ℝ)^2 := by
  let J := toJet P (A.realization (n+6) t)
  have hl : levelNorm P J n ≤ blockNorm P J 6 n := by
    have h := single_le_sum (s := range (6+1)) (f := fun r => levelNorm P J (n+r))
      (fun r _ => levelNorm_nonneg J) (show 0 ∈ range (6+1) by norm_num)
    simpa only [blockNorm, Nat.add_zero] using h
  have hw := single_le_sum (s := range (n+1))
    (f := fun j => weight ρ j * blockNorm P J 6 j)
    (fun j _ => mul_nonneg (weight_pos hρ j).le (blockNorm_nonneg J))
    (show n ∈ range (n+1) by simp)
  have hlevel : levelNorm P J n ≤ C / weight ρ n := by
    apply (le_div_iff₀ (weight_pos hρ n)).mpr
    have h := (mul_le_mul_of_nonneg_left hl (weight_pos hρ n).le).trans (hw.trans hb)
    simpa only [mul_comm] using h
  apply (A.coverTensor_norm_le_level (n+6) n (by omega) t).trans
  calc
    _ ≤ ‖coordinateEquiv.symm.toContinuousLinearMap‖^n * (C / weight ρ n) :=
      mul_le_mul_of_nonneg_left hlevel (pow_nonneg (norm_nonneg _) n)
    _ = _ := by rw [weight, div_div_eq_mul_div, mul_pow, inv_pow]; ring

theorem toSmoothTimeField_jetSeries (n : ℕ) (t : Icc (0 : ℝ) T) :
    (fun q => jetSeries P (A.toSmoothTimeField.field t : LiftTangent → Vector3) q n) =
      tensor P (A.pointField t) n := rfl

end EulerAllOrderCorrectionData.FieldTower
