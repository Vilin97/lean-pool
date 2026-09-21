/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.RefinedScalarVariance
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.MatrixVariance

/-! # Refined Assembly -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace VarianceBoundGoodScale

open MeasureTheory
open scoped BigOperators

noncomputable section

/-!
# Refined matrix assembly

This file plugs the refined scalar probe estimates into the finite-dimensional
matrix upgrade.  The per-scale budget is now expressed in terms of `delta` and
`\widetilde\Theta_0`.
-/

/-- Refined coordinate-probe scalar variance budget at scale `j`. -/
noncomputable def coordinateProbeRefinedVarianceBound
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (delta : ℝ) (j : ℕ) (α : BlockCoord d) : ℝ :=
  refinedScalarProbeVarianceBound delta (fullBlockCoordinateProbe α)
    (coordinateProbeRefinedDescendantAverageK hP4 delta j)

/-- Refined plus-pair scalar variance budget at scale `j`. -/
noncomputable def plusProbeRefinedVarianceBound
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (delta : ℝ) (j : ℕ) (α β : BlockCoord d) : ℝ :=
  refinedScalarProbeVarianceBound delta (fullBlockPlusProbe α β)
    (pairProbeRefinedDescendantAverageK hP4 delta j)

/-- Refined minus-pair scalar variance budget at scale `j`. -/
noncomputable def minusProbeRefinedVarianceBound
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (delta : ℝ) (j : ℕ) (α β : BlockCoord d) : ℝ :=
  refinedScalarProbeVarianceBound delta (fullBlockMinusProbe α β)
    (pairProbeRefinedDescendantAverageK hP4 delta j)

/-- Refined finite-probe matrix variance budget at one scale. -/
noncomputable def refinedMatrixVarianceScaleBound
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (delta : ℝ) (j : ℕ) : ℝ :=
  ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
    ((Fintype.card (BlockCoord d) : ℝ) *
      ∑ α : BlockCoord d,
        (Fintype.card (BlockCoord d) : ℝ) *
          ∑ β : BlockCoord d,
            3 *
              (coordinateProbeRefinedVarianceBound hP4 delta j α +
                (if α = β then
                  16 * coordinateProbeRefinedVarianceBound hP4 delta j α
                else
                  plusProbeRefinedVarianceBound hP4 delta j α β) +
                (if α = β then
                  0
                else
                  minusProbeRefinedVarianceBound hP4 delta j α β)))

private theorem integral_plusProbe_self_sq_eq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (m j : ℕ) (α : BlockCoord d) :
    ∫ a,
        (fullBlockQuadratic
          (fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ)
            (cubeSet (originCube d (j : ℤ))) a)
          (fullBlockPlusProbe α α)) ^ (2 : ℕ) ∂P =
      16 *
        ∫ a,
          (fullBlockQuadratic
            (fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ)
              (cubeSet (originCube d (j : ℤ))) a)
            (fullBlockCoordinateProbe α)) ^ (2 : ℕ) ∂P := by
  have hpoint :
      (fun a : RegCoeffField d =>
        (fullBlockQuadratic
          (fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ)
            (cubeSet (originCube d (j : ℤ))) a)
          (fullBlockPlusProbe α α)) ^ (2 : ℕ))
        =
      fun a : RegCoeffField d =>
        16 *
          (fullBlockQuadratic
            (fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ)
              (cubeSet (originCube d (j : ℤ))) a)
            (fullBlockCoordinateProbe α)) ^ (2 : ℕ) := by
    funext a
    rw [fullBlockQuadratic_plusProbe_self]
    ring
  rw [hpoint, integral_const_mul]

private theorem integral_minusProbe_self_sq_eq_zero
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (m j : ℕ) (α : BlockCoord d) :
    ∫ a,
        (fullBlockQuadratic
          (fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ)
            (cubeSet (originCube d (j : ℤ))) a)
          (fullBlockMinusProbe α α)) ^ (2 : ℕ) ∂P = 0 := by
  have hpoint :
      (fun a : RegCoeffField d =>
        (fullBlockQuadratic
          (fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ)
            (cubeSet (originCube d (j : ℤ))) a)
          (fullBlockMinusProbe α α)) ^ (2 : ℕ))
        =
      fun _a : RegCoeffField d => 0 := by
    funext a
    rw [fullBlockQuadratic_minusProbe_self]
    norm_num
  rw [hpoint, integral_zero]

/-- Per-scale matrix variance bound using the refined scalar probe estimates. -/
theorem fullBlockNormalizedFluctuationOperatorNormSqAtScale_integral_le_refinedMatrixVarianceScaleBound
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (m j : ℕ) (hj : j ≤ m)
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) :
    ∫ a,
        Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct (m : ℤ) (originCube d (j : ℤ)) a ∂P ≤
      refinedMatrixVarianceScaleBound hP4 delta j := by
  let Ccoord : BlockCoord d → ℝ :=
    coordinateProbeRefinedVarianceBound hP4 delta j
  let Cplus : BlockCoord d → BlockCoord d → ℝ := fun α β =>
    if α = β then 16 * Ccoord α else plusProbeRefinedVarianceBound hP4 delta j α β
  let Cminus : BlockCoord d → BlockCoord d → ℝ := fun α β =>
    if α = β then 0 else minusProbeRefinedVarianceBound hP4 delta j α β
  have hcoord_int : ∀ α : BlockCoord d,
      Integrable
        (fun a : RegCoeffField d =>
          (fullBlockQuadratic
            (fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ)
              (cubeSet (originCube d (j : ℤ))) a)
            (fullBlockCoordinateProbe α)) ^ (2 : ℕ)) P := by
    intro α
    exact integrable_fluctuationQuadratic_sq_from_P4
      hP hStruct hP4 m j (fullBlockCoordinateProbe α)
  have hplus_int : ∀ α β : BlockCoord d,
      Integrable
        (fun a : RegCoeffField d =>
          (fullBlockQuadratic
            (fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ)
              (cubeSet (originCube d (j : ℤ))) a)
            (fullBlockPlusProbe α β)) ^ (2 : ℕ)) P := by
    intro α β
    exact integrable_fluctuationQuadratic_sq_from_P4
      hP hStruct hP4 m j (fullBlockPlusProbe α β)
  have hminus_int : ∀ α β : BlockCoord d,
      Integrable
        (fun a : RegCoeffField d =>
          (fullBlockQuadratic
            (fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ)
              (cubeSet (originCube d (j : ℤ))) a)
            (fullBlockMinusProbe α β)) ^ (2 : ℕ)) P := by
    intro α β
    exact integrable_fluctuationQuadratic_sq_from_P4
      hP hStruct hP4 m j (fullBlockMinusProbe α β)
  have hcoord : ∀ α : BlockCoord d,
      (∫ a,
        (fullBlockQuadratic
          (fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ)
            (cubeSet (originCube d (j : ℤ))) a)
          (fullBlockCoordinateProbe α)) ^ (2 : ℕ) ∂P) ≤ Ccoord α := by
    intro α
    rw [integral_fluctuationQuadratic_sq_eq_integral_abs_sub_dotProduct_sq
      hP hStruct hP4 m j (fullBlockCoordinateProbe α)]
    simpa [Ccoord, coordinateProbeRefinedVarianceBound, refinedScalarProbeVarianceBound] using
      coordinateProbe_scalarVariance_good_origin_le_refined
        hP hStruct hP4 hdelta_nonneg m j hj hgood_upper hgood_lower α
  have hplus : ∀ α β : BlockCoord d,
      (∫ a,
        (fullBlockQuadratic
          (fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ)
            (cubeSet (originCube d (j : ℤ))) a)
          (fullBlockPlusProbe α β)) ^ (2 : ℕ) ∂P) ≤ Cplus α β := by
    intro α β
    by_cases hαβ : α = β
    · subst β
      rw [integral_plusProbe_self_sq_eq hP hStruct m j α]
      have hc :
          (∫ a,
            fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ)
              (cubeSet (originCube d (j : ℤ))) a α α ^ (2 : ℕ) ∂P) ≤
            Ccoord α := by
        simpa using hcoord α
      simp [Cplus]
      nlinarith
    · rw [integral_fluctuationQuadratic_sq_eq_integral_abs_sub_dotProduct_sq
        hP hStruct hP4 m j (fullBlockPlusProbe α β)]
      simpa [Cplus, hαβ, plusProbeRefinedVarianceBound,
        refinedScalarProbeVarianceBound] using
        plusProbe_scalarVariance_good_origin_le_refined
          hP hStruct hP4 hdelta_nonneg m j hj hgood_upper hgood_lower hαβ
  have hminus : ∀ α β : BlockCoord d,
      (∫ a,
        (fullBlockQuadratic
          (fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ)
            (cubeSet (originCube d (j : ℤ))) a)
          (fullBlockMinusProbe α β)) ^ (2 : ℕ) ∂P) ≤ Cminus α β := by
    intro α β
    by_cases hαβ : α = β
    · subst β
      rw [integral_minusProbe_self_sq_eq_zero hP hStruct m j α]
      simp [Cminus]
    · rw [integral_fluctuationQuadratic_sq_eq_integral_abs_sub_dotProduct_sq
        hP hStruct hP4 m j (fullBlockMinusProbe α β)]
      simpa [Cminus, hαβ, minusProbeRefinedVarianceBound,
        refinedScalarProbeVarianceBound] using
        minusProbe_scalarVariance_good_origin_le_refined
          hP hStruct hP4 hdelta_nonneg m j hj hgood_upper hgood_lower hαβ
  simpa [refinedMatrixVarianceScaleBound, Ccoord, Cplus, Cminus] using
    fullBlockNormalizedFluctuationOperatorNormSqAtScale_integral_le_probeBounds
      hP hStruct hP4 m j Ccoord Cplus Cminus
      hcoord_int hplus_int hminus_int hcoord hplus hminus

/-- The variance sum is bounded by the beta-weighted refined per-scale budgets. -/
theorem varianceGoodScaleFullBlockSumAtScale_le_weighted_refinedMatrixVarianceScaleBound
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (m : ℕ)
    (hgood_upper :
      hP.barSigmaAtScale hStruct 0 ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (m : ℤ))
    (hgood_lower :
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ ≤
        (1 + delta) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) :
    varianceGoodScaleFullBlockSumAtScale hP hStruct hP4 m ≤
      ∑ j ∈ Finset.Icc 1 m,
        varianceWeight (section54VarianceBeta hP4) m j *
          refinedMatrixVarianceScaleBound hP4 delta j := by
  refine varianceGoodScaleFullBlockSumAtScale_le_weighted_sum hP hStruct hP4 m ?_
  intro j hj
  exact
    fullBlockNormalizedFluctuationOperatorNormSqAtScale_integral_le_refinedMatrixVarianceScaleBound
      hP hStruct hP4 hdelta_nonneg m j (Finset.mem_Icc.mp hj).2
      hgood_upper hgood_lower

end

end VarianceBoundGoodScale
end Section54
end Ch05
end Book
end Homogenization
