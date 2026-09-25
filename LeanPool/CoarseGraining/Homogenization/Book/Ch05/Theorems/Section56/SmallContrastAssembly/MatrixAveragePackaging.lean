/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.VarianceEstimateQuadratic
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.FiniteNet

/-! # Matrix Average Packaging -/

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

theorem fullBlockFluctuationMatrixWithNormalizer_isSymm_of_isSymmetricBlockMat
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S : FullBlockMat d) {U : Set (Vec d)} {a : RegCoeffField d}
    (hA : IsSymmetricBlockMat (coarseBlockMatrix U a)) :
    (fullBlockFluctuationMatrixWithNormalizer hP hStruct center S U a).IsSymm := by
  let A := coarseBlockMatrix U a
  let Abar := Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center
  have hA_full : (toFullBlockMat A).IsSymm := by
    simpa [A] using isSymm_toFullBlockMat_of_isSymmetricBlockMat hA
  have hAbar_full : (toFullBlockMat Abar).IsSymm :=
    isSymm_toFullBlockMat_of_isSymmetricBlockMat
      (isSymmetricBlockMat_scalarAnnealedBlockMatrixAtScale hP hStruct center)
  have hsub : (toFullBlockMat A - toFullBlockMat Abar).IsSymm :=
    hA_full.sub hAbar_full
  have hHerm :
      (toFullBlockMat A - toFullBlockMat Abar).IsHermitian := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hsub
  have hconj :
      (Matrix.conjTranspose S * (toFullBlockMat A - toFullBlockMat Abar) * S).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_mul S hHerm
  simpa [fullBlockFluctuationMatrixWithNormalizer, A, Abar, Matrix.conjTranspose,
    Matrix.IsHermitian, Matrix.IsSymm] using! hconj

theorem fullBlockFluctuationMatrixWithNormalizer_isSymm_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S : FullBlockMat d) (Q : TriadicCube d) :
    ∀ᵐ a ∂P,
      (fullBlockFluctuationMatrixWithNormalizer
        hP hStruct center S (cubeSet Q) a).IsSymm := by
  filter_upwards [isSymmetricBlockMat_coarseBlockMatrix_cubeSet_ae hP Q] with a hA
  exact
    fullBlockFluctuationMatrixWithNormalizer_isSymm_of_isSymmetricBlockMat
      hP hStruct center S hA

theorem descendantsAverageFullBlockMat_isSymm
    {d : ℕ} {Q : TriadicCube d} {j : ℕ} {F : TriadicCube d → FullBlockMat d}
    (hF : ∀ R, R ∈ descendantsAtDepth Q j → (F R).IsSymm) :
    (descendantsAverageFullBlockMat Q j F).IsSymm := by
  ext α β
  unfold descendantsAverageFullBlockMat descendantsAverage
  refine congrArg (fun x => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * x) ?_
  exact Finset.sum_congr rfl fun R hR => by
    exact (hF R hR).apply α β

theorem descendantsAverageFluctuationMatrixWithNormalizer_isSymm_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S : FullBlockMat d) (Q : TriadicCube d) (j : ℕ) :
    ∀ᵐ a ∂P,
      (descendantsAverageFluctuationMatrixWithNormalizer
        hP hStruct center S Q j a).IsSymm := by
  have hchild :
      ∀ R ∈ descendantsAtDepth Q j,
        ∀ᵐ a ∂P,
          (fullBlockFluctuationMatrixWithNormalizer
            hP hStruct center S (cubeSet R) a).IsSymm := by
    intro R _hR
    exact fullBlockFluctuationMatrixWithNormalizer_isSymm_ae
      hP hStruct center S R
  have hall :
      ∀ᵐ a ∂P, ∀ R, R ∈ descendantsAtDepth Q j →
        (fullBlockFluctuationMatrixWithNormalizer
          hP hStruct center S (cubeSet R) a).IsSymm :=
    Ch04.ae_forall_mem_finset (P := P) (descendantsAtDepth Q j) hchild
  filter_upwards [hall] with a ha
  simpa [descendantsAverageFluctuationMatrixWithNormalizer] using
    descendantsAverageFullBlockMat_isSymm (Q := Q) (j := j)
      (F := fun R =>
        fullBlockFluctuationMatrixWithNormalizer hP hStruct center S
          (cubeSet R) a) ha

theorem descendantsAverageFluctuationOperatorNormSqWithNormalizer_le_probeSqBudget_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S : FullBlockMat d) (Q : TriadicCube d) (j : ℕ) :
    (fun a : RegCoeffField d =>
      descendantsAverageFluctuationOperatorNormSqWithNormalizer
        hP hStruct center S Q j a)
      ≤ᵐ[P]
    fun a : RegCoeffField d =>
      ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
        Section54.VarianceBoundGoodScale.fullBlockProbeSqBudget
          (descendantsAverageFluctuationMatrixWithNormalizer
            hP hStruct center S Q j a) := by
  filter_upwards
    [descendantsAverageFluctuationMatrixWithNormalizer_isSymm_ae
      hP hStruct center S Q j] with a hM
  simpa [descendantsAverageFluctuationOperatorNormSqWithNormalizer] using
    Section54.VarianceBoundGoodScale.fullBlock_operatorNorm_sq_le_probeSqBudget hM

theorem descendantsAverageFluctuationOperatorNormSqWithNormalizer_integral_le_probeBounds
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m n k : ℕ) (hk : k ≤ n) (S : FullBlockMat d)
    (Ccoord : BlockCoord d → ℝ)
    (Cplus Cminus : BlockCoord d → BlockCoord d → ℝ)
    (hcoord_int :
      ∀ α : BlockCoord d,
        Integrable
          (fun a : RegCoeffField d =>
            (fullBlockQuadratic
              (descendantsAverageFluctuationMatrixWithNormalizer
                hP hStruct (m : ℤ) S (originCube d (n : ℤ)) (n - k) a)
              (Section54.VarianceBoundGoodScale.fullBlockCoordinateProbe α)) ^ (2 : ℕ)) P)
    (hplus_int :
      ∀ α β : BlockCoord d,
        Integrable
          (fun a : RegCoeffField d =>
            (fullBlockQuadratic
              (descendantsAverageFluctuationMatrixWithNormalizer
                hP hStruct (m : ℤ) S (originCube d (n : ℤ)) (n - k) a)
              (Section54.VarianceBoundGoodScale.fullBlockPlusProbe α β)) ^ (2 : ℕ)) P)
    (hminus_int :
      ∀ α β : BlockCoord d,
        Integrable
          (fun a : RegCoeffField d =>
            (fullBlockQuadratic
              (descendantsAverageFluctuationMatrixWithNormalizer
                hP hStruct (m : ℤ) S (originCube d (n : ℤ)) (n - k) a)
              (Section54.VarianceBoundGoodScale.fullBlockMinusProbe α β)) ^ (2 : ℕ)) P)
    (hcoord :
      ∀ α : BlockCoord d,
        (∫ a,
          (fullBlockQuadratic
            (descendantsAverageFluctuationMatrixWithNormalizer
              hP hStruct (m : ℤ) S (originCube d (n : ℤ)) (n - k) a)
            (Section54.VarianceBoundGoodScale.fullBlockCoordinateProbe α)) ^
              (2 : ℕ) ∂P) ≤ Ccoord α)
    (hplus :
      ∀ α β : BlockCoord d,
        (∫ a,
          (fullBlockQuadratic
            (descendantsAverageFluctuationMatrixWithNormalizer
              hP hStruct (m : ℤ) S (originCube d (n : ℤ)) (n - k) a)
            (Section54.VarianceBoundGoodScale.fullBlockPlusProbe α β)) ^
              (2 : ℕ) ∂P) ≤ Cplus α β)
    (hminus :
      ∀ α β : BlockCoord d,
        (∫ a,
          (fullBlockQuadratic
            (descendantsAverageFluctuationMatrixWithNormalizer
              hP hStruct (m : ℤ) S (originCube d (n : ℤ)) (n - k) a)
            (Section54.VarianceBoundGoodScale.fullBlockMinusProbe α β)) ^
              (2 : ℕ) ∂P) ≤ Cminus α β) :
    ∫ a,
        descendantsAverageFluctuationOperatorNormSqWithNormalizer
          hP hStruct (m : ℤ) S (originCube d (n : ℤ)) (n - k) a ∂P ≤
      ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
        ((Fintype.card (BlockCoord d) : ℝ) *
          ∑ α : BlockCoord d,
            (Fintype.card (BlockCoord d) : ℝ) *
              ∑ β : BlockCoord d,
                3 * (Ccoord α + Cplus α β + Cminus α β)) := by
  let Q : TriadicCube d := originCube d (n : ℤ)
  let j : ℕ := n - k
  let M : RegCoeffField d → FullBlockMat d :=
    fun a =>
      descendantsAverageFluctuationMatrixWithNormalizer
        hP hStruct (m : ℤ) S Q j a
  have hF_int :
      Integrable
        (descendantsAverageFluctuationOperatorNormSqWithNormalizer
          hP hStruct (m : ℤ) S Q j) P := by
    simpa [Q, j] using
      integrable_descendantsAverageFluctuationOperatorNormSqWithNormalizer_from_P4_of_stationary
        hP hStruct hP4 m n k hk S
  have hterm_int : ∀ α β : BlockCoord d,
      Integrable
        (fun a : RegCoeffField d =>
          3 *
            ((fullBlockQuadratic (M a)
                (Section54.VarianceBoundGoodScale.fullBlockCoordinateProbe α)) ^ (2 : ℕ) +
              (fullBlockQuadratic (M a)
                (Section54.VarianceBoundGoodScale.fullBlockPlusProbe α β)) ^ (2 : ℕ) +
              (fullBlockQuadratic (M a)
                (Section54.VarianceBoundGoodScale.fullBlockMinusProbe α β)) ^ (2 : ℕ))) P := by
    intro α β
    have hsum :
        Integrable
          (fun a : RegCoeffField d =>
            (fullBlockQuadratic (M a)
                (Section54.VarianceBoundGoodScale.fullBlockCoordinateProbe α)) ^ (2 : ℕ) +
              (fullBlockQuadratic (M a)
                (Section54.VarianceBoundGoodScale.fullBlockPlusProbe α β)) ^ (2 : ℕ) +
              (fullBlockQuadratic (M a)
                (Section54.VarianceBoundGoodScale.fullBlockMinusProbe α β)) ^ (2 : ℕ)) P := by
      have hci :
          Integrable
            (fun a : RegCoeffField d =>
              (fullBlockQuadratic (M a)
                (Section54.VarianceBoundGoodScale.fullBlockCoordinateProbe α)) ^
                  (2 : ℕ)) P := by
        simpa [M, Q, j] using hcoord_int α
      have hpi :
          Integrable
            (fun a : RegCoeffField d =>
              (fullBlockQuadratic (M a)
                (Section54.VarianceBoundGoodScale.fullBlockPlusProbe α β)) ^
                  (2 : ℕ)) P := by
        simpa [M, Q, j] using hplus_int α β
      have hmi :
          Integrable
            (fun a : RegCoeffField d =>
              (fullBlockQuadratic (M a)
                (Section54.VarianceBoundGoodScale.fullBlockMinusProbe α β)) ^
                  (2 : ℕ)) P := by
        simpa [M, Q, j] using hminus_int α β
      exact (hci.add hpi).add hmi
    exact hsum.const_mul 3
  have hbudget_int :
        Integrable
          (fun a : RegCoeffField d =>
            Section54.VarianceBoundGoodScale.fullBlockProbeSqBudget (M a)) P := by
    unfold Section54.VarianceBoundGoodScale.fullBlockProbeSqBudget
    refine (MeasureTheory.integrable_finsetSum _ ?_).const_mul _
    intro α _hα
    refine (MeasureTheory.integrable_finsetSum _ ?_).const_mul _
    intro β _hβ
    simpa [M] using hterm_int α β
  have hpoint :
      (fun a : RegCoeffField d =>
        descendantsAverageFluctuationOperatorNormSqWithNormalizer
          hP hStruct (m : ℤ) S Q j a)
      ≤ᵐ[P]
        fun a : RegCoeffField d =>
          ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
            Section54.VarianceBoundGoodScale.fullBlockProbeSqBudget (M a) := by
    simpa [M, Q, j] using
      descendantsAverageFluctuationOperatorNormSqWithNormalizer_le_probeSqBudget_ae
        hP hStruct (m : ℤ) S Q j
  have hfirst :
      ∫ a,
        descendantsAverageFluctuationOperatorNormSqWithNormalizer
          hP hStruct (m : ℤ) S Q j a ∂P ≤
        ∫ a,
          ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
            Section54.VarianceBoundGoodScale.fullBlockProbeSqBudget (M a) ∂P :=
    integral_mono_ae hF_int (hbudget_int.const_mul _) hpoint
  have hbudget_eval :
      ∫ a, Section54.VarianceBoundGoodScale.fullBlockProbeSqBudget (M a) ∂P =
        (Fintype.card (BlockCoord d) : ℝ) *
          ∑ α : BlockCoord d,
            (Fintype.card (BlockCoord d) : ℝ) *
              ∑ β : BlockCoord d,
                3 *
                  (∫ a,
                      (fullBlockQuadratic (M a)
                        (Section54.VarianceBoundGoodScale.fullBlockCoordinateProbe α)) ^
                        (2 : ℕ) ∂P +
                    ∫ a,
                      (fullBlockQuadratic (M a)
                        (Section54.VarianceBoundGoodScale.fullBlockPlusProbe α β)) ^
                        (2 : ℕ) ∂P +
                    ∫ a,
                      (fullBlockQuadratic (M a)
                        (Section54.VarianceBoundGoodScale.fullBlockMinusProbe α β)) ^
                        (2 : ℕ) ∂P) := by
    unfold Section54.VarianceBoundGoodScale.fullBlockProbeSqBudget
    rw [integral_const_mul]
    congr 1
    rw [integral_finsetSum]
    · congr
      ext α
      rw [integral_const_mul]
      congr 1
      rw [integral_finsetSum]
      · congr
        ext β
        let f : RegCoeffField d → ℝ :=
          fun a =>
            (fullBlockQuadratic (M a)
              (Section54.VarianceBoundGoodScale.fullBlockCoordinateProbe α)) ^
                (2 : ℕ)
        let g : RegCoeffField d → ℝ :=
          fun a =>
            (fullBlockQuadratic (M a)
              (Section54.VarianceBoundGoodScale.fullBlockPlusProbe α β)) ^
                (2 : ℕ)
        let h : RegCoeffField d → ℝ :=
          fun a =>
            (fullBlockQuadratic (M a)
              (Section54.VarianceBoundGoodScale.fullBlockMinusProbe α β)) ^
                (2 : ℕ)
        have hf_int : Integrable f P := by
          simpa [f, M, Q, j] using hcoord_int α
        have hg_int : Integrable g P := by
          simpa [g, M, Q, j] using hplus_int α β
        have hh_int : Integrable h P := by
          simpa [h, M, Q, j] using hminus_int α β
        change
          ∫ a, 3 * (f a + g a + h a) ∂P =
            3 * (∫ a, f a ∂P + ∫ a, g a ∂P + ∫ a, h a ∂P)
        rw [integral_const_mul]
        change
          3 * ∫ a, (fun a => f a + g a) a + h a ∂P =
            3 * (∫ a, f a ∂P + ∫ a, g a ∂P + ∫ a, h a ∂P)
        have hfg_fun : (fun a : RegCoeffField d => f a + g a) = f + g := by
          ext a
          rfl
        rw [hfg_fun]
        rw [integral_add (hf_int.add hg_int) hh_int]
        change
          3 * (∫ a, f a + g a ∂P + ∫ a, h a ∂P) =
            3 * (∫ a, f a ∂P + ∫ a, g a ∂P + ∫ a, h a ∂P)
        rw [integral_add hf_int hg_int]
      · intro β _hβ
        exact hterm_int α β
    · intro α _hα
      exact (MeasureTheory.integrable_finsetSum _ fun β _hβ =>
        hterm_int α β).const_mul _
  have hbudget_bound :
      ∫ a, Section54.VarianceBoundGoodScale.fullBlockProbeSqBudget (M a) ∂P ≤
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
    exact mul_le_mul_of_nonneg_left
      (by nlinarith [hcoord α, hplus α β, hminus α β])
      (by norm_num)
  calc
    ∫ a,
        descendantsAverageFluctuationOperatorNormSqWithNormalizer
          hP hStruct (m : ℤ) S (originCube d (n : ℤ)) (n - k) a ∂P
        =
      ∫ a,
        descendantsAverageFluctuationOperatorNormSqWithNormalizer
          hP hStruct (m : ℤ) S Q j a ∂P := by
          rfl
    _ ≤
      ∫ a,
          ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
            Section54.VarianceBoundGoodScale.fullBlockProbeSqBudget (M a) ∂P := hfirst
    _ =
      ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
        ∫ a, Section54.VarianceBoundGoodScale.fullBlockProbeSqBudget (M a) ∂P := by
          rw [integral_const_mul]
    _ ≤
      ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
        ((Fintype.card (BlockCoord d) : ℝ) *
          ∑ α : BlockCoord d,
            (Fintype.card (BlockCoord d) : ℝ) *
              ∑ β : BlockCoord d,
                3 * (Ccoord α + Cplus α β + Cminus α β)) := by
          exact mul_le_mul_of_nonneg_left hbudget_bound (sq_nonneg _)

end SmallContrastAssembly

end

end Section56
end Ch05
end Book
end Homogenization
