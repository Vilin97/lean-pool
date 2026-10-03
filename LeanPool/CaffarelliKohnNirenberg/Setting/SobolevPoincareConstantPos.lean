/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBall
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Sobolev Poincare Constant Pos

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal


noncomputable section

namespace CKN

/-- The Sobolev inequality constant `SNormLESNormFDerivOfEqConst` for `E := Vec 3`,
`F := ℝ`, `μ := volume`, and `p := 2` is positive. -/
theorem sNormLESNormFDerivOfEqConst_vec3_two_pos :
    0 < SNormLESNormFDerivOfEqConst (E := Vec 3) ℝ (volume : Measure (Vec 3)) (2 : ℝ) := by
  by_contra! hC
  have hCzero : SNormLESNormFDerivOfEqConst (E := Vec 3) ℝ (volume : Measure (Vec 3)) (2 : ℝ) = 0 :=
    le_antisymm hC (zero_le)
  -- Take a smooth bump function φ centered at 0 with φ(0) = 1
  let φ : ContDiffBump (0 : Vec 3) := ⟨1, 2, by norm_num, by norm_num⟩
  have hφ_contDiff : ContDiff ℝ 1 φ := φ.contDiff
  have hφ_support : HasCompactSupport φ := φ.hasCompactSupport
  have hφ_one : φ 0 = 1 := by
    have : (0 : Vec 3) ∈ Metric.closedBall (0 : Vec 3) φ.rIn :=
      Metric.mem_closedBall_self (by norm_num : 0 ≤ φ.rIn)
    simpa using φ.one_of_mem_closedBall this
  have hφ_cont : Continuous φ := φ.continuous
  -- Apply the Gagliardo–Nirenberg–Sobolev inequality with p = 2, p' = 6
  have h_finrank : 0 < Module.finrank ℝ (Vec 3) := by
    rw [Module.finrank_fin_fun]
    norm_num
  have hp' : ((6 : NNReal) : ℝ)⁻¹ = ((2 : NNReal) : ℝ)⁻¹ - ((Module.finrank ℝ (Vec 3) : ℝ)⁻¹) := by
    rw [Module.finrank_fin_fun]
    norm_num
  have h_gns := MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq
    (μ := volume) (u := φ) hφ_contDiff hφ_support
    (by norm_num : (1 : NNReal) ≤ 2) h_finrank hp'
  -- Since SNormLESNormFDerivOfEqConst = 0, the RHS is 0
  have h_rhs_zero :
      ((SNormLESNormFDerivOfEqConst (E := Vec 3) ℝ (volume : Measure (Vec 3))
        ((2 : NNReal) : ℝ)) : ℝ≥0∞) *
        eLpNorm (fderiv ℝ φ) (2 : NNReal) volume = 0 := by
    have hCzero' :
        (SNormLESNormFDerivOfEqConst (E := Vec 3) ℝ (volume : Measure (Vec 3))
          ((2 : NNReal) : ℝ)) = 0 := by
      simpa [show ((2 : NNReal) : ℝ) = (2 : ℝ) by norm_num] using hCzero
    rw [hCzero']
    simp
  have h_eLpNorm_zero : eLpNorm (φ : Vec 3 → ℝ) (6 : NNReal) volume = 0 := by
    have h_le : eLpNorm (φ : Vec 3 → ℝ) (6 : NNReal) volume ≤ 0 := by
      calc
        eLpNorm (φ : Vec 3 → ℝ) (6 : NNReal) volume ≤
            ((SNormLESNormFDerivOfEqConst (E := Vec 3) ℝ (volume : Measure (Vec 3))
              ((2 : NNReal) : ℝ)) : ℝ≥0∞) *
              eLpNorm (fderiv ℝ φ) (2 : NNReal) volume := h_gns
        _ = 0 := h_rhs_zero
    have h_nonneg : 0 ≤ eLpNorm (φ : Vec 3 → ℝ) (6 : NNReal) volume := by
      positivity
    exact le_antisymm h_le h_nonneg
  have hp_ne_zero : (6 : ℝ≥0∞) ≠ 0 := by norm_num
  have h_ae : (φ : Vec 3 → ℝ) =ᵐ[volume] (0 : Vec 3 → ℝ) := by
    have := (MeasureTheory.eLpNorm_eq_zero_iff (p := 6) hp_ne_zero).mp h_eLpNorm_zero
    simpa using this
  -- Since both φ and 0 are continuous, ae equality implies pointwise equality
  have h_eq : (φ : Vec 3 → ℝ) = (0 : Vec 3 → ℝ) :=
    ((hφ_cont.ae_eq_iff_eq volume continuous_zero).mp h_ae)
  -- But φ(0) = 1, contradiction
  rw [h_eq] at hφ_one
  norm_num at hφ_one

/-- `localSobolevConstant` is positive. -/
theorem localSobolevConstant_pos : 0 < localSobolevConstant := by
  unfold localSobolevConstant
  have h : 0 < SNormLESNormFDerivOfEqConst (E := Vec 3) ℝ (volume : Measure (Vec 3)) (2 : ℝ) :=
    sNormLESNormFDerivOfEqConst_vec3_two_pos
  have h3pos : (0 : ℝ≥0∞) < (3 : NNReal) := by norm_num
  have hpos' :
      (0 : ℝ≥0∞) < (SNormLESNormFDerivOfEqConst (E := Vec 3) ℝ (volume : Measure (Vec 3))
        (2 : ℝ) : ℝ≥0∞) := by
    exact_mod_cast h
  exact ENNReal.mul_pos (by norm_num : (3 : ℝ≥0∞) ≠ 0) (ne_of_gt hpos')

/-- `sobolevPoincareL6Constant` is positive. -/
theorem sobolevPoincareL6Constant_pos : 0 < sobolevPoincareL6Constant := by
  unfold sobolevPoincareL6Constant
  dsimp only
  have h_mul_pos : 0 < localSobolevConstant *
      ((2 * (1 + 2 * 675 ^ 2 * 64 + 2 * 3042 ^ 2 * 648) +
        2 * 32 ^ 2 * 6337 * euclideanBallPoincareConstant) ^ (1 / 2 : ℝ) +
      32 * ((6337 : ℝ≥0∞) ^ (1 / 2 : ℝ) * euclideanBallPoincareConstant ^ (1 / 2 : ℝ))) := by
    refine ENNReal.mul_pos (ne_of_gt localSobolevConstant_pos) ?_
    -- Show the second factor is nonzero
    let Cg : ℝ≥0∞ :=
      2 * (1 + 2 * 675 ^ 2 * 64 + 2 * 3042 ^ 2 * 648) +
        2 * 32 ^ 2 * 6337 * euclideanBallPoincareConstant
    have hCg_pos : 0 < Cg := by
      dsimp [Cg]
      have h_first : (0 : ℝ≥0∞) < 2 * (1 + 2 * 675 ^ 2 * 64 + 2 * 3042 ^ 2 * 648) := by
        norm_num
      have h_second : 0 ≤ 2 * 32 ^ 2 * 6337 * euclideanBallPoincareConstant := by
        positivity
      exact add_pos_of_pos_of_nonneg h_first h_second
    have h_rpow_pos : 0 < Cg ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_pos_of_nonneg hCg_pos (by norm_num : (0 : ℝ) ≤ 1/2)
    have h_rest_nonneg :
        0 ≤ 32 * ((6337 : ℝ≥0∞) ^ (1 / 2 : ℝ) * euclideanBallPoincareConstant ^ (1 / 2 : ℝ)) := by
      positivity
    have h_sum_pos : 0 < Cg ^ (1 / 2 : ℝ) +
        32 * ((6337 : ℝ≥0∞) ^ (1 / 2 : ℝ) * euclideanBallPoincareConstant ^ (1 / 2 : ℝ)) :=
      add_pos_of_pos_of_nonneg h_rpow_pos h_rest_nonneg
    exact ne_of_gt h_sum_pos
  exact h_mul_pos

end CKN
