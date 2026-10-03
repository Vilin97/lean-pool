/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.SmallContrastAssembly.MatrixAveragePackaging

/-! # Trace Average Packaging -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace SmallContrastAssembly

theorem blockJTraceAverageWithNormalizers_eq_sum_descendantsAverage
    {d : ℕ} (S T : FullBlockMat d) (Q : TriadicCube d) (j : ℕ)
    (a : RegCoeffField d) :
    blockJTraceAverageWithNormalizers S T Q j a =
      ∑ α : BlockCoord d,
        descendantsAverage Q j
          (fun R =>
            blockJObservableCubeSetBlockVec R
              (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α) a) := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  unfold blockJTraceAverageWithNormalizers descendantsAverage
  change
    (D.card : ℝ)⁻¹ *
        (∑ R ∈ D,
          ∑ α : BlockCoord d,
            blockJObservableCubeSetBlockVec R
              (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α) a) =
      ∑ α : BlockCoord d,
        (D.card : ℝ)⁻¹ *
          ∑ R ∈ D,
            blockJObservableCubeSetBlockVec R
              (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α) a
  calc
    (D.card : ℝ)⁻¹ *
        (∑ R ∈ D,
          ∑ α : BlockCoord d,
            blockJObservableCubeSetBlockVec R
              (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α) a)
        =
      (D.card : ℝ)⁻¹ *
        (∑ α : BlockCoord d,
          ∑ R ∈ D,
            blockJObservableCubeSetBlockVec R
              (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α) a) := by
          rw [Finset.sum_comm]
    _ =
      ∑ α : BlockCoord d,
        (D.card : ℝ)⁻¹ *
          ∑ R ∈ D,
            blockJObservableCubeSetBlockVec R
              (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α) a := by
          rw [Finset.mul_sum]

theorem integral_blockJTraceAverageWithNormalizers_eq_sum_originCube_of_stationary
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (child parent : ℕ) (hchild_parent : child ≤ parent)
    (S T : FullBlockMat d) :
    ∫ a,
        blockJTraceAverageWithNormalizers S T
          (originCube d (parent : ℤ)) (parent - child) a ∂P =
      ∑ α : BlockCoord d,
        Ch04.expectedBlockJCubeSet P (originCube d (child : ℤ))
          (fullBlockMatrixProbe S α).1 (fullBlockMatrixProbe T α).2
          (fullBlockMatrixProbe S α).2 (fullBlockMatrixProbe T α).1 := by
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let Q : TriadicCube d := originCube d (parent : ℤ)
  let j : ℕ := parent - child
  have hscale_le : (child : ℤ) ≤ (parent : ℤ) := by
    exact_mod_cast hchild_parent
  have hdepth_scale :
      descendantsAtDepth Q j = descendantsAtScale Q (child : ℤ) := by
    simpa [Q, j, originCube] using
      (descendantsAtScale_eq_descendantsAtDepth (originCube d (parent : ℤ))
        hscale_le).symm
  have hdesc_int :
      ∀ α : BlockCoord d,
        Integrable
          (fun a : RegCoeffField d =>
            descendantsAverage Q j
              (fun R =>
                blockJObservableCubeSetBlockVec R
                  (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α) a)) P := by
    intro α
    refine Ch04.integrable_descendantsAverage ?_
    intro R hR
    have hRscale : R ∈ descendantsAtScale Q (child : ℤ) := by
      simpa [hdepth_scale] using hR
    have hR_nonneg : 0 ≤ R.scale := by
      have hscale : R.scale = (child : ℤ) := scale_eq_of_mem_descendantsAtScale hRscale
      rw [hscale]
      exact_mod_cast Nat.zero_le child
    have hmem :=
      memLp_two_blockJObservableCubeSetBlockVec_from_P4_of_stationary
        hP hStruct hP4 R hR_nonneg
        (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α)
    exact hmem.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  calc
    ∫ a,
        blockJTraceAverageWithNormalizers S T
          (originCube d (parent : ℤ)) (parent - child) a ∂P
        =
      ∫ a,
        ∑ α : BlockCoord d,
          descendantsAverage Q j
            (fun R =>
              blockJObservableCubeSetBlockVec R
                (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α) a) ∂P := by
          apply integral_congr_ae
          filter_upwards with a
          simpa [Q, j] using
            blockJTraceAverageWithNormalizers_eq_sum_descendantsAverage
              S T Q j a
    _ =
      ∑ α : BlockCoord d,
        ∫ a,
          descendantsAverage Q j
            (fun R =>
              blockJObservableCubeSetBlockVec R
                (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α) a) ∂P := by
          rw [MeasureTheory.integral_finsetSum]
          intro α _hα
          exact hdesc_int α
    _ =
      ∑ α : BlockCoord d,
        Ch04.expectedBlockJCubeSet P (originCube d (child : ℤ))
          (fullBlockMatrixProbe S α).1 (fullBlockMatrixProbe T α).2
          (fullBlockMatrixProbe S α).2 (fullBlockMatrixProbe T α).1 := by
          congr 1
          ext α
          let Pα : BlockVec d := fullBlockMatrixProbe S α
          let Qα : BlockVec d := fullBlockMatrixProbe T α
          have hB :
              ∀ R, R ∈ descendantsAtScale (originCube d (parent : ℤ)) (child : ℤ) →
                Integrable
                  (Ch04.blockJObservableCubeSet R Pα.1 Qα.2 Pα.2 Qα.1) P := by
            intro R hR
            have hR_nonneg : 0 ≤ R.scale := by
              have hscale : R.scale = (child : ℤ) :=
                scale_eq_of_mem_descendantsAtScale hR
              rw [hscale]
              exact_mod_cast Nat.zero_le child
            have hmem :=
              memLp_two_blockJObservableCubeSetBlockVec_from_P4_of_stationary
                hP hStruct hP4 R hR_nonneg Pα Qα
            simpa [blockJObservableCubeSetBlockVec, Pα, Qα] using
              hmem.integrable (by norm_num : (1 : ENNReal) ≤ 2)
          simpa [Q, j, Pα, Qα, blockJObservableCubeSetBlockVec] using
            hP.integral_descendantsAverage_blockJObservableCubeSet_eq_originCube_of_stationary
              hStruct.stationary hStruct.adjoint_invariant
              (by exact_mod_cast Nat.zero_le child) hscale_le
              Pα.1 Qα.2 Pα.2 Qα.1 hB

end SmallContrastAssembly

end

end Section56
end Ch05
end Book
end Homogenization
