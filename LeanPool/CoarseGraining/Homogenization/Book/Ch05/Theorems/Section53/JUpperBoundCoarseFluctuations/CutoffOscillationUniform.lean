/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.RHSConversion

/-! # Cutoff Oscillation Uniform -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundCoarseFluctuations

open MeasureTheory

/-!
# Uniform cutoff-oscillation absorption

This file removes the non-uniform ratio argument from the cutoff-oscillation
term in the third Section 5.3 lemma.
-/

noncomputable section

private theorem two_mul_beta_le_one
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    2 * section53CoarseFluctuationBeta hP4 ≤ 1 := by
  have hsum := sUpper_add_sLower_add_four_beta_le_one hP4
  have hupper := hP4.sUpper_nonneg
  have hlower := hP4.sLower_nonneg
  have hbeta := section53CoarseFluctuationBeta_nonneg hP4
  nlinarith

private theorem cutoff_decay_le_low_tail_decay
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (N : ℕ) :
    ((3 : ℝ) ^ N)⁻¹ ≤
      Real.rpow (3 : ℝ)
        (-2 * section53CoarseFluctuationBeta hP4 * (N : ℝ)) := by
  have htwo : 2 * section53CoarseFluctuationBeta hP4 ≤ 1 :=
    two_mul_beta_le_one hP4
  have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
  have hexp :
      -(N : ℝ) ≤
        -2 * section53CoarseFluctuationBeta hP4 * (N : ℝ) := by
    nlinarith
  have hrpow :
      Real.rpow (3 : ℝ) (-(N : ℝ)) ≤
        Real.rpow (3 : ℝ)
          (-2 * section53CoarseFluctuationBeta hP4 * (N : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
  have hpow_pos : 0 < (3 : ℝ) ^ N := pow_pos (by norm_num) N
  have hpow_eq : ((3 : ℝ) ^ N)⁻¹ = Real.rpow (3 : ℝ) (-(N : ℝ)) := by
    calc
      ((3 : ℝ) ^ N)⁻¹ = (Real.rpow (3 : ℝ) (N : ℝ))⁻¹ := by
        simp [Real.rpow_natCast]
      _ = Real.rpow (3 : ℝ) (-(N : ℝ)) := by
        exact (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3) (N : ℝ)).symm
  rw [hpow_eq]
  exact hrpow

private theorem cutoffCoeff_le_uniform_low_tail_coeff
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) {k m : ℕ} (hkm : k < m)
    {ε : ℝ} (hε : 0 < ε) (hε_le : ε ≤ 1) :
    let β := section53CoarseFluctuationBeta hP4
    let Q : TriadicCube d := originCube d (m : ℤ)
    let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
    JUpperBoundWeakNorms.section53CutoffOscillationConstant Q *
        JUpperBoundWeakNorms.section53CutoffScaleSep Q j
      ≤
        (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
          ε⁻¹ * (β ^ 2)⁻¹ *
          Real.rpow (3 : ℝ)
            (-2 * β * (((m - k : ℕ) : ℝ))) := by
  intro β Q j
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hε_inv_ge_one : 1 ≤ ε⁻¹ := by
    exact (one_le_inv₀ hε).mpr hε_le
  have hβ_sq_inv_ge_one : 1 ≤ (β ^ 2)⁻¹ := by
    have hβ_le_one : β ≤ 1 := by
      have htwo := two_mul_beta_le_one hP4
      have hβ_nonneg : 0 ≤ β := hβ_pos.le
      nlinarith
    have hsquare_le_one : β ^ 2 ≤ 1 := by
      nlinarith
    exact (one_le_inv₀ (sq_pos_of_pos hβ_pos)).mpr hsquare_le_one
  have hosc :=
      JUpperBoundWeakNorms.section53CutoffOscillationConstant_mul_scaleSep_eq Q j
  have hbound := JUpperBoundWeakNorms.section53CutoffBound_le_two_pow_card Q
  have hgrad_nonneg := quantitativeCubeCutoffGradientConst_nonneg d
  have htwo_pow_nonneg : 0 ≤ (2 : ℝ) ^ d := pow_nonneg (by norm_num) d
  have hcut_base :
        JUpperBoundWeakNorms.section53CutoffOscillationConstant Q *
            JUpperBoundWeakNorms.section53CutoffScaleSep Q j
          ≤
            (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
              ((3 : ℝ) ^ j)⁻¹ := by
      calc
        JUpperBoundWeakNorms.section53CutoffOscillationConstant Q *
            JUpperBoundWeakNorms.section53CutoffScaleSep Q j
            =
          (8 * quantitativeCubeCutoffGradientConst d *
              JUpperBoundWeakNorms.section53CutoffBound Q) *
            ((3 : ℝ) ^ j)⁻¹ := hosc
        _ ≤
          (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
            ((3 : ℝ) ^ j)⁻¹ := by
            exact mul_le_mul_of_nonneg_right
              (by
                nlinarith [mul_le_mul_of_nonneg_left hbound
                  (mul_nonneg (by norm_num : 0 ≤ (8 : ℝ)) hgrad_nonneg)])
              (inv_nonneg.mpr (pow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) j))
  have hmk_nat : j = m - k := by
    dsimp [j]
    omega
  have hdecay :
        ((3 : ℝ) ^ j)⁻¹ ≤
          Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) := by
    simpa [β, hmk_nat, mul_assoc] using
        cutoff_decay_le_low_tail_decay hP4 (m - k)
  have hbase_nonneg :
        0 ≤ 8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d := by
    exact mul_nonneg
        (mul_nonneg (by norm_num) hgrad_nonneg) htwo_pow_nonneg
  have htail_nonneg :
        0 ≤ Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have htail_le :
      Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) ≤
        ε⁻¹ * (β ^ 2)⁻¹ *
          Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) := by
    have hfac : 1 ≤ ε⁻¹ * (β ^ 2)⁻¹ := by
      nlinarith [hε_inv_ge_one, hβ_sq_inv_ge_one]
    calc
      Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))
          =
        1 * Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) := by ring
      _ ≤
        (ε⁻¹ * (β ^ 2)⁻¹) *
          Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right hfac htail_nonneg
  calc
      JUpperBoundWeakNorms.section53CutoffOscillationConstant Q *
          JUpperBoundWeakNorms.section53CutoffScaleSep Q j
        ≤
          (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
            ((3 : ℝ) ^ j)⁻¹ := hcut_base
      _ ≤
          (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
            Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hdecay hbase_nonneg
      _ ≤
          (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
            ε⁻¹ * (β ^ 2)⁻¹ *
            Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) := by
          calc
            (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
                Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))
              ≤
                (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
                  (ε⁻¹ * (β ^ 2)⁻¹ *
                    Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))) :=
                mul_le_mul_of_nonneg_left htail_le hbase_nonneg
            _ =
                (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
                  ε⁻¹ * (β ^ 2)⁻¹ *
                  Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) := by ring

private theorem expectedResponseJCubeSet_nonneg
    {d : ℕ} (P : Ch04.RestrictionCoeffLaw d) (Q : TriadicCube d) (p q : Vec d) :
    0 ≤ Ch04.expectedResponseJCubeSet P Q p q := by
  dsimp [Ch04.expectedResponseJCubeSet]
  exact integral_nonneg fun a => by
    exact Ch04.restrictionResponseJObservableCubeSet_nonneg Q p q a

/-- Uniform cutoff-oscillation absorption.  The constant is chosen before the
law, scales, vector, and `ε`. -/
theorem cutoffOscillation_special_expectedResponse_le_lowScaleTail_uniform
    {d : ℕ} [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
        (hP4 : QuantitativeCoarseGrainedEllipticity P)
        {k m : ℕ}, k < m →
        ∀ e : Vec d, vecNormSq e = 1 →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
      let β := section53CoarseFluctuationBeta hP4
      let Q : TriadicCube d := originCube d (m : ℤ)
      let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
      let p_e := specialPAtScale hP hStruct (m : ℤ) e
      let q_e := specialQAtScale hP hStruct (m : ℤ) e
      JUpperBoundWeakNorms.section53CutoffOscillationConstant Q *
          JUpperBoundWeakNorms.section53CutoffScaleSep Q j *
          Ch04.expectedResponseJCubeSet P Q p_e q_e
        ≤
          C * ε⁻¹ * (β ^ 2)⁻¹ *
            Real.rpow (3 : ℝ)
              (-2 * β * (((m - k : ℕ) : ℝ))) *
            coarseFluctuationScalarWeightAtScale hP hStruct m *
              (thetaAtScale hP hStruct (m : ℤ) - 1) := by
  refine ⟨8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d,
    mul_nonneg (mul_nonneg (by norm_num) (quantitativeCubeCutoffGradientConst_nonneg d))
      (pow_nonneg (by norm_num) d), ?_⟩
  intro P hP hStruct hP4 k m hkm e he ε hε hε_le
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let Q : TriadicCube d := originCube d (m : ℤ)
  let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
  let θ := thetaAtScale hP hStruct (m : ℤ)
  have hCoeff :=
    cutoffCoeff_le_uniform_low_tail_coeff hP4 hkm hε hε_le
  have hWeight : 1 ≤ coarseFluctuationScalarWeightAtScale hP hStruct m :=
    one_le_coarseFluctuationScalarWeightAtScale hP hStruct hP4 m
  have hθ_one : 1 ≤ θ := by
    simpa [θ] using one_le_thetaAtScale_of_P4 hP hStruct hP4 m
  have hθ_sub_nonneg : 0 ≤ θ - 1 := by linarith
  have hJ_le :
      Ch04.expectedResponseJCubeSet P Q
          (specialPAtScale hP hStruct (m : ℤ) e)
          (specialQAtScale hP hStruct (m : ℤ) e) ≤
        θ - 1 := by
    simpa [Q, θ] using
      expectedResponseJCubeSet_special_le_thetaAtScale_sub_one_of_vecNormSq_eq_one
        hP hStruct hP4 m e he
  have hJ_nonneg :
      0 ≤ Ch04.expectedResponseJCubeSet P Q
          (specialPAtScale hP hStruct (m : ℤ) e)
          (specialQAtScale hP hStruct (m : ℤ) e) :=
    expectedResponseJCubeSet_nonneg P Q
      (specialPAtScale hP hStruct (m : ℤ) e)
      (specialQAtScale hP hStruct (m : ℤ) e)
  have hCoeffTail_nonneg :
      0 ≤
        (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
          ε⁻¹ * (β ^ 2)⁻¹ *
          Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) := by
    have hbase :
        0 ≤ 8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d :=
      mul_nonneg
        (mul_nonneg (by norm_num) (quantitativeCubeCutoffGradientConst_nonneg d))
        (pow_nonneg (by norm_num) d)
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hbase (inv_nonneg.mpr hε.le))
        (inv_nonneg.mpr (sq_nonneg _)))
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  calc
    JUpperBoundWeakNorms.section53CutoffOscillationConstant Q *
          JUpperBoundWeakNorms.section53CutoffScaleSep Q j *
          Ch04.expectedResponseJCubeSet P Q
            (specialPAtScale hP hStruct (m : ℤ) e)
            (specialQAtScale hP hStruct (m : ℤ) e)
      ≤
        ((8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
          ε⁻¹ * (β ^ 2)⁻¹ *
          Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))) *
          (θ - 1) := by
        exact mul_le_mul hCoeff hJ_le hJ_nonneg hCoeffTail_nonneg
    _ ≤
        ((8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
          ε⁻¹ * (β ^ 2)⁻¹ *
          Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) *
          coarseFluctuationScalarWeightAtScale hP hStruct m) *
          (θ - 1) := by
        exact mul_le_mul_of_nonneg_right
          (by
            calc
              (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
                  ε⁻¹ * (β ^ 2)⁻¹ *
                  Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))
                =
                  ((8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
                    ε⁻¹ * (β ^ 2)⁻¹ *
                    Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))) * 1 := by
                    ring
              _ ≤
                  ((8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
                    ε⁻¹ * (β ^ 2)⁻¹ *
                    Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))) *
                    coarseFluctuationScalarWeightAtScale hP hStruct m :=
                    mul_le_mul_of_nonneg_left hWeight hCoeffTail_nonneg)
          hθ_sub_nonneg
    _ =
        (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
          ε⁻¹ * (β ^ 2)⁻¹ *
          Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) *
          coarseFluctuationScalarWeightAtScale hP hStruct m * (θ - 1) := by
        ring

end

end JUpperBoundCoarseFluctuations
end Section53
end Ch05
end Book
end Homogenization
