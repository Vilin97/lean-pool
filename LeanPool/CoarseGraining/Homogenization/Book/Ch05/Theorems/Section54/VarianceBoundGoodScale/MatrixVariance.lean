/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.ScalarVariance

/-! # Matrix Variance -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace VarianceBoundGoodScale

open MeasureTheory
open scoped BigOperators

noncomputable section

/-!
# Matrix variance from finite scalar probes

This file integrates the finite-dimensional probe bound.  It is deliberately
internal: scalar probe integrability and bounds are supplied by the preceding
Section 5.4 files before the public lemma is assembled.
-/

private theorem fullBlockQuadratic_smul
    {d : ℕ} (M : FullBlockMat d) (c : ℝ) (q : FullBlockVec d) :
    fullBlockQuadratic M (c • q) = c ^ (2 : ℕ) * fullBlockQuadratic M q := by
  unfold fullBlockQuadratic
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp [pow_two, smul_eq_mul, mul_assoc]

private theorem fullBlockPlusProbe_self
    {d : ℕ} (α : BlockCoord d) :
    fullBlockPlusProbe α α = (2 : ℝ) • fullBlockCoordinateProbe α := by
  classical
  ext γ
  by_cases hγα : γ = α
  · subst γ
    simp [fullBlockPlusProbe, fullBlockCoordinateProbe]
    norm_num
  · simp [fullBlockPlusProbe, fullBlockCoordinateProbe, hγα]

private theorem fullBlockMinusProbe_self
    {d : ℕ} (α : BlockCoord d) :
    fullBlockMinusProbe α α = 0 := by
  classical
  ext γ
  by_cases hγα : γ = α
  · subst γ
    simp [fullBlockMinusProbe, fullBlockCoordinateProbe]
  · simp [fullBlockMinusProbe, fullBlockCoordinateProbe, hγα]

theorem fullBlockQuadratic_plusProbe_self
    {d : ℕ} (M : FullBlockMat d) (α : BlockCoord d) :
    fullBlockQuadratic M (fullBlockPlusProbe α α) =
      4 * fullBlockQuadratic M (fullBlockCoordinateProbe α) := by
  rw [fullBlockPlusProbe_self, fullBlockQuadratic_smul]
  norm_num

theorem fullBlockQuadratic_minusProbe_self
    {d : ℕ} (M : FullBlockMat d) (α : BlockCoord d) :
    fullBlockQuadratic M (fullBlockMinusProbe α α) = 0 := by
  rw [fullBlockMinusProbe_self]
  unfold fullBlockQuadratic
  simp [dotProduct, Matrix.mulVec]

theorem integral_fluctuationQuadratic_sq_eq_integral_abs_sub_dotProduct_sq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m j : ℕ) (q : FullBlockVec d) :
    ∫ a,
        (fullBlockQuadratic
          (fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ)
            (cubeSet (originCube d (j : ℤ))) a) q) ^ (2 : ℕ) ∂P =
      ∫ a,
        |fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ) q
          (cubeSet (originCube d (j : ℤ))) a - dotProduct q q| ^
          (2 : ℕ) ∂P := by
  apply integral_congr_ae
  filter_upwards with a
  have hquad :=
    fullBlockNormalizedQuadraticObservable_sub_dotProduct_eq_fluctuationQuadratic
      hP hStruct hP4 m q (cubeSet (originCube d (j : ℤ))) a
  symm
  rw [hquad, sq_abs]

theorem integrable_fluctuationQuadratic_sq_from_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m j : ℕ) (q : FullBlockVec d) :
    Integrable
      (fun a : RegCoeffField d =>
        (fullBlockQuadratic
          (fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ)
            (cubeSet (originCube d (j : ℤ))) a) q) ^ (2 : ℕ)) P := by
  have hcenter :=
    integrable_abs_sub_dotProduct_sq_fullBlockNormalizedQuadraticObservable_from_P4
      hP hStruct hP4 m j q
  refine hcenter.congr ?_
  filter_upwards with a
  have hquad :=
    fullBlockNormalizedQuadraticObservable_sub_dotProduct_eq_fluctuationQuadratic
      hP hStruct hP4 m q (cubeSet (originCube d (j : ℤ))) a
  rw [hquad, sq_abs]

/-- Integrating the finite-probe pointwise bound reduces the full-block matrix
variance to scalar quadratic-probe variances. -/
theorem fullBlockNormalizedFluctuationOperatorNormSqAtScale_integral_le_probeBounds
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m j : ℕ)
    (Ccoord : BlockCoord d → ℝ)
    (Cplus Cminus : BlockCoord d → BlockCoord d → ℝ)
    (hcoord_int :
      ∀ α : BlockCoord d,
        Integrable
          (fun a : RegCoeffField d =>
            (fullBlockQuadratic
              (fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ)
                (cubeSet (originCube d (j : ℤ))) a)
              (fullBlockCoordinateProbe α)) ^ (2 : ℕ)) P)
    (hplus_int :
      ∀ α β : BlockCoord d,
        Integrable
          (fun a : RegCoeffField d =>
            (fullBlockQuadratic
              (fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ)
                (cubeSet (originCube d (j : ℤ))) a)
              (fullBlockPlusProbe α β)) ^ (2 : ℕ)) P)
    (hminus_int :
      ∀ α β : BlockCoord d,
        Integrable
          (fun a : RegCoeffField d =>
            (fullBlockQuadratic
              (fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ)
                (cubeSet (originCube d (j : ℤ))) a)
              (fullBlockMinusProbe α β)) ^ (2 : ℕ)) P)
    (hcoord :
      ∀ α : BlockCoord d,
        (∫ a,
          (fullBlockQuadratic
            (fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ)
              (cubeSet (originCube d (j : ℤ))) a)
            (fullBlockCoordinateProbe α)) ^ (2 : ℕ) ∂P) ≤ Ccoord α)
    (hplus :
      ∀ α β : BlockCoord d,
        (∫ a,
          (fullBlockQuadratic
            (fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ)
              (cubeSet (originCube d (j : ℤ))) a)
            (fullBlockPlusProbe α β)) ^ (2 : ℕ) ∂P) ≤ Cplus α β)
    (hminus :
      ∀ α β : BlockCoord d,
        (∫ a,
          (fullBlockQuadratic
            (fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ)
              (cubeSet (originCube d (j : ℤ))) a)
            (fullBlockMinusProbe α β)) ^ (2 : ℕ) ∂P) ≤ Cminus α β) :
    ∫ a,
        Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct (m : ℤ) (originCube d (j : ℤ)) a ∂P ≤
      ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
        ((Fintype.card (BlockCoord d) : ℝ) *
          ∑ α : BlockCoord d,
            (Fintype.card (BlockCoord d) : ℝ) *
              ∑ β : BlockCoord d,
                3 * (Ccoord α + Cplus α β + Cminus α β)) := by
  let : IsProbabilityMeasure P := hP.isProbability
  let Q : TriadicCube d := originCube d (j : ℤ)
  let M : RegCoeffField d → FullBlockMat d := fun a =>
    fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ) (cubeSet Q) a
  have hF_int :
      Integrable
        (Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct (m : ℤ) Q) P := by
    simpa [Q] using
      integrable_origin_fullBlockNormalizedFluctuationOperatorNormSqAtScale_from_P4
        hP hStruct hP4 (m : ℤ) j
  have hterm_int : ∀ α β : BlockCoord d,
      Integrable
        (fun a : RegCoeffField d =>
          3 * ((fullBlockQuadratic (M a) (fullBlockCoordinateProbe α)) ^ (2 : ℕ) +
            (fullBlockQuadratic (M a) (fullBlockPlusProbe α β)) ^ (2 : ℕ) +
            (fullBlockQuadratic (M a) (fullBlockMinusProbe α β)) ^ (2 : ℕ))) P := by
    intro α β
    have hsum :
        Integrable
              (fun a : RegCoeffField d =>
            (fullBlockQuadratic (M a) (fullBlockCoordinateProbe α)) ^ (2 : ℕ) +
              (fullBlockQuadratic (M a) (fullBlockPlusProbe α β)) ^ (2 : ℕ) +
              (fullBlockQuadratic (M a) (fullBlockMinusProbe α β)) ^ (2 : ℕ)) P := by
      have hci :
          Integrable
            (fun a : RegCoeffField d =>
              (fullBlockQuadratic (M a) (fullBlockCoordinateProbe α)) ^ (2 : ℕ)) P := by
        simpa [M, Q] using hcoord_int α
      have hpi :
          Integrable
            (fun a : RegCoeffField d =>
              (fullBlockQuadratic (M a) (fullBlockPlusProbe α β)) ^ (2 : ℕ)) P := by
        simpa [M, Q] using hplus_int α β
      have hmi :
          Integrable
            (fun a : RegCoeffField d =>
              (fullBlockQuadratic (M a) (fullBlockMinusProbe α β)) ^ (2 : ℕ)) P := by
        simpa [M, Q] using hminus_int α β
      exact (hci.add hpi).add hmi
    exact hsum.const_mul 3
  have hbudget_int :
      Integrable
        (fun a : RegCoeffField d =>
          fullBlockProbeSqBudget (M a)) P := by
    unfold fullBlockProbeSqBudget
    refine (MeasureTheory.integrable_finsetSum _ ?_).const_mul _
    intro α _hα
    refine (MeasureTheory.integrable_finsetSum _ ?_).const_mul _
    intro β _hβ
    simpa [M] using hterm_int α β
  have hpoint :
      (fun a : RegCoeffField d =>
        Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct (m : ℤ) Q a)
      ≤ᵐ[P]
        fun a : RegCoeffField d =>
          ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
            fullBlockProbeSqBudget (M a) := by
    simpa [M, Q] using
      fullBlockNormalizedFluctuationOperatorNormSqAtScale_le_probeSqBudget_ae
        hP hStruct (m : ℤ) Q
  have hfirst :
      ∫ a,
        Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct (m : ℤ) Q a ∂P ≤
        ∫ a,
          ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
            fullBlockProbeSqBudget (M a) ∂P := by
    exact integral_mono_ae hF_int (hbudget_int.const_mul _) hpoint
  have hbudget_eval :
      ∫ a, fullBlockProbeSqBudget (M a) ∂P =
        (Fintype.card (BlockCoord d) : ℝ) *
          ∑ α : BlockCoord d,
            (Fintype.card (BlockCoord d) : ℝ) *
              ∑ β : BlockCoord d,
                3 *
                  (∫ a,
                      (fullBlockQuadratic (M a) (fullBlockCoordinateProbe α)) ^
                        (2 : ℕ) ∂P +
                    ∫ a,
                      (fullBlockQuadratic (M a) (fullBlockPlusProbe α β)) ^
                        (2 : ℕ) ∂P +
                    ∫ a,
                      (fullBlockQuadratic (M a) (fullBlockMinusProbe α β)) ^
                        (2 : ℕ) ∂P) := by
    unfold fullBlockProbeSqBudget
    rw [integral_const_mul]
    congr 1
    rw [integral_finsetSum]
    · congr 1
      ext α
      rw [integral_const_mul]
      congr 1
      rw [integral_finsetSum]
      · congr 1
        ext β
        rw [integral_const_mul]
        congr 1
        have hci :
            Integrable
              (fun a : RegCoeffField d =>
                (fullBlockQuadratic (M a) (fullBlockCoordinateProbe α)) ^ (2 : ℕ)) P := by
          simpa [M, Q] using hcoord_int α
        have hpi :
            Integrable
              (fun a : RegCoeffField d =>
                (fullBlockQuadratic (M a) (fullBlockPlusProbe α β)) ^ (2 : ℕ)) P := by
          simpa [M, Q] using hplus_int α β
        have hmi :
            Integrable
              (fun a : RegCoeffField d =>
                (fullBlockQuadratic (M a) (fullBlockMinusProbe α β)) ^ (2 : ℕ)) P := by
          simpa [M, Q] using hminus_int α β
        calc
          ∫ a,
              (fullBlockQuadratic (M a) (fullBlockCoordinateProbe α)) ^ (2 : ℕ) +
                  (fullBlockQuadratic (M a) (fullBlockPlusProbe α β)) ^ (2 : ℕ) +
                (fullBlockQuadratic (M a) (fullBlockMinusProbe α β)) ^ (2 : ℕ) ∂P
              =
            ∫ a,
              (fullBlockQuadratic (M a) (fullBlockCoordinateProbe α)) ^ (2 : ℕ) +
                (fullBlockQuadratic (M a) (fullBlockPlusProbe α β)) ^ (2 : ℕ) ∂P +
              ∫ a,
                (fullBlockQuadratic (M a) (fullBlockMinusProbe α β)) ^ (2 : ℕ) ∂P := by
                simpa [Pi.add_apply, add_assoc] using
                  integral_add (hci.add hpi) hmi
          _ =
            (∫ a,
                (fullBlockQuadratic (M a) (fullBlockCoordinateProbe α)) ^ (2 : ℕ) ∂P +
              ∫ a,
                (fullBlockQuadratic (M a) (fullBlockPlusProbe α β)) ^ (2 : ℕ) ∂P) +
              ∫ a,
                (fullBlockQuadratic (M a) (fullBlockMinusProbe α β)) ^ (2 : ℕ) ∂P := by
                rw [integral_add hci hpi]
          _ =
            ∫ a,
                (fullBlockQuadratic (M a) (fullBlockCoordinateProbe α)) ^ (2 : ℕ) ∂P +
              ∫ a,
                (fullBlockQuadratic (M a) (fullBlockPlusProbe α β)) ^ (2 : ℕ) ∂P +
              ∫ a,
                (fullBlockQuadratic (M a) (fullBlockMinusProbe α β)) ^ (2 : ℕ) ∂P := by
                ring
      · intro β _hβ
        simpa [M] using hterm_int α β
    · intro α _hα
      refine (MeasureTheory.integrable_finsetSum _ ?_).const_mul _
      intro β _hβ
      simpa [M] using hterm_int α β
  have hbudget_bound :
      ∫ a, fullBlockProbeSqBudget (M a) ∂P ≤
        (Fintype.card (BlockCoord d) : ℝ) *
          ∑ α : BlockCoord d,
            (Fintype.card (BlockCoord d) : ℝ) *
              ∑ β : BlockCoord d,
                3 * (Ccoord α + Cplus α β + Cminus α β) := by
    rw [hbudget_eval]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine Finset.sum_le_sum ?_
    intro α _hα
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine Finset.sum_le_sum ?_
    intro β _hβ
    have hc := hcoord α
    have hp := hplus α β
    have hm := hminus α β
    nlinarith
  calc
    ∫ a,
        Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct (m : ℤ) (originCube d (j : ℤ)) a ∂P
        = ∫ a,
          Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
            hP hStruct (m : ℤ) Q a ∂P := rfl
    _ ≤ ∫ a,
          ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
            fullBlockProbeSqBudget (M a) ∂P := hfirst
    _ = ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
          ∫ a, fullBlockProbeSqBudget (M a) ∂P := by
          rw [integral_const_mul]
    _ ≤ ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
        ((Fintype.card (BlockCoord d) : ℝ) *
          ∑ α : BlockCoord d,
            (Fintype.card (BlockCoord d) : ℝ) *
              ∑ β : BlockCoord d,
                3 * (Ccoord α + Cplus α β + Cminus α β)) := by
          exact mul_le_mul_of_nonneg_left hbudget_bound (sq_nonneg _)

end

end VarianceBoundGoodScale
end Section54
end Ch05
end Book
end Homogenization
