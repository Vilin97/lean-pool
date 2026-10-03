/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.SmallContrastAssembly.MatrixAverageCompression

/-! # Matrix Average Geometric -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace SmallContrastAssembly

open Section54.VarianceBoundGoodScale

/-- Parameter-only version of the small-contrast basic refined variance budget. -/
noncomputable def refinedVarianceBasicBudgetSmallContrastConstParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  1 + 4 * pairPointwiseBudgetConstParams params +
    8 * pairPointwiseBudgetConstParams params ^ (2 : ℕ)

/-- Parameter-only version of the uniform one-probe root-square constant. -/
noncomputable def normalizedQuadraticProbeAverageUniformRootSqConstParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  (Ch04.rosenthalDescendantsAtScaleLpConst d 0 2 +
      Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 2) ^ (2 : ℕ) *
    (refinedMatrixBudgetConst d *
      refinedVarianceBasicBudgetSmallContrastConstParams params * 16)

/-- Parameter-only constant for the compressed matrix-average geometric estimate. -/
noncomputable def normalizedMatrixAverageGeometricConstParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  ((Fintype.card (BlockCoord d) : ℝ) ^ (6 : ℕ)) * 9 *
    normalizedQuadraticProbeAverageUniformRootSqConstParams params

@[simp]
theorem refinedVarianceBasicBudgetSmallContrastConstParams_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    refinedVarianceBasicBudgetSmallContrastConstParams hP4.params =
      refinedVarianceBasicBudgetSmallContrastConst hP4 := rfl

@[simp]
theorem normalizedQuadraticProbeAverageUniformRootSqConstParams_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    normalizedQuadraticProbeAverageUniformRootSqConstParams hP4.params =
      normalizedQuadraticProbeAverageUniformRootSqConst hP4 := rfl

@[simp]
theorem normalizedMatrixAverageGeometricConstParams_eq_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    normalizedMatrixAverageGeometricConstParams hP4.params =
      normalizedMatrixAverageGeometricConst hP4 := rfl

theorem descendantsAtScale_originCube_nat_card_inv_eq_rpow
    (d child parent : ℕ) (hchild_parent : child ≤ parent) :
    (((descendantsAtScale (originCube d (parent : ℤ)) (child : ℤ)).card : ℝ)⁻¹) =
      Real.rpow (3 : ℝ) (-(d : ℝ) * ((parent - child : ℕ) : ℝ)) := by
  have hscale_le : (child : ℤ) ≤ (parent : ℤ) := by
    exact_mod_cast hchild_parent
  have htoNat :
      Int.toNat ((parent : ℤ) - (child : ℤ)) = parent - child := by
    have hsub :
        (parent : ℤ) - (child : ℤ) = ((parent - child : ℕ) : ℤ) := by
      omega
    rw [hsub]
    simp
  rw [Section52.section52_descendantsAtScale_originCube_large_card d parent hscale_le]
  rw [htoNat]
  have hcast :
      (((3 ^ d) ^ (parent - child) : ℕ) : ℝ) =
        ((3 : ℝ) ^ (d * (parent - child))) := by
    rw [Nat.cast_pow, Nat.cast_pow]
    rw [← pow_mul]
    norm_num
  rw [hcast]
  rw [← Real.rpow_natCast (3 : ℝ) (d * (parent - child))]
  rw [show ((d * (parent - child) : ℕ) : ℝ) =
      (d : ℝ) * ((parent - child : ℕ) : ℝ) by rw [Nat.cast_mul]]
  simpa [neg_mul] using
    (Real.rpow_neg (by norm_num : 0 ≤ (3 : ℝ))
      ((d : ℝ) * ((parent - child : ℕ) : ℝ))).symm

theorem descendantsAverageNormalizedFluctuationOperatorNormSq_integral_le_geometric_of_smallContrast
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hsmall : widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2)
    {child parent : ℕ} (hchild_parent : child ≤ parent) :
    ∫ a,
        descendantsAverageNormalizedFluctuationOperatorNormSq
          hP hStruct (child : ℤ) (originCube d (parent : ℤ))
            (parent - child) a ∂P ≤
      normalizedMatrixAverageGeometricConst hP4 *
        Real.rpow (3 : ℝ) (-(d : ℝ) * ((parent - child : ℕ) : ℝ)) := by
  have hprobe :=
    descendantsAverageNormalizedFluctuationOperatorNormSq_integral_le_probeRootBudget
      hP hStruct hP4 hchild_parent
  have hbudget :=
    normalizedMatrixAverageProbeRootBudget_le_card_inv_mul_smallContrastConst
      hP hStruct hP4 hsmall hchild_parent
  have hcard :=
    descendantsAtScale_originCube_nat_card_inv_eq_rpow d child parent hchild_parent
  calc
    ∫ a,
        descendantsAverageNormalizedFluctuationOperatorNormSq
          hP hStruct (child : ℤ) (originCube d (parent : ℤ))
            (parent - child) a ∂P ≤
        normalizedMatrixAverageProbeRootBudget hP hStruct child parent := hprobe
    _ ≤ (((descendantsAtScale (originCube d (parent : ℤ)) (child : ℤ)).card : ℝ)⁻¹) *
          normalizedMatrixAverageGeometricConst hP4 := hbudget
    _ = normalizedMatrixAverageGeometricConst hP4 *
          Real.rpow (3 : ℝ) (-(d : ℝ) * ((parent - child : ℕ) : ℝ)) := by
        rw [hcard]
        ring

/--
Manuscript-style small-contrast matrix-average estimate.

The constant is chosen before the law `P`; it depends only on the quantitative
ellipticity parameters and the dimension.
-/
theorem descendantsAverageNormalizedFluctuationOperatorNormSq_homogenizationScale
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2 →
      ∀ {child parent : ℕ}, child ≤ parent →
        ∫ a,
            descendantsAverageNormalizedFluctuationOperatorNormSq
              hP hStruct (child : ℤ) (originCube d (parent : ℤ))
                (parent - child) a ∂P ≤
          C * Real.rpow (3 : ℝ)
            (-(d : ℝ) * ((parent - child : ℕ) : ℝ)) := by
  let C : ℝ := max 1 (normalizedMatrixAverageGeometricConstParams params)
  have hC_pos : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C, hC_pos, ?_⟩
  intro P hP hStruct hP4 hparams hsmall child parent hchild_parent
  have hmain :=
    descendantsAverageNormalizedFluctuationOperatorNormSq_integral_le_geometric_of_smallContrast
      hP hStruct hP4 hsmall hchild_parent
  have hconst_le : normalizedMatrixAverageGeometricConst hP4 ≤ C := by
    dsimp [C]
    rw [← hparams]
    rw [normalizedMatrixAverageGeometricConstParams_eq_of_P4 hP4]
    exact le_max_right _ _
  have hrpow_nonneg :
      0 ≤ Real.rpow (3 : ℝ)
        (-(d : ℝ) * ((parent - child : ℕ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  exact hmain.trans (mul_le_mul_of_nonneg_right hconst_le hrpow_nonneg)

end SmallContrastAssembly

end

end Section56
end Ch05
end Book
end Homogenization
