/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.VarianceEstimateQuadratic.MatrixTools

/-! # Error Bounds -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

theorem restrictsTo_descendantsDomainPartition_of_aelocallyUniformlyEllipticField
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) :
    let F : Ch02.TriadicCoeffFamily d :=
      Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    let Pcell : Ch02.DomainPartition (Ch02.cubeDomain Q) :=
      Ch02.descendantsDomainPartition Q j
    ∀ i : Pcell.Cell, Ch02.CoeffOn.RestrictsTo (F.coeffOn Q) (F.coeffOn i.1) := by
  intro F Pcell i
  let k : ℤ := Q.scale - (j : ℤ)
  have hk : k ≤ Q.scale := by
    dsimp [k]
    have hj : (0 : ℤ) ≤ (j : ℤ) := by exact_mod_cast Nat.zero_le j
    linarith
  have hiScale : i.1 ∈ descendantsAtScale Q k := by
    rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
    simp [k, i.2]
  exact F.restrictsTo_descendant hk hiScale

theorem normalizedPositiveError_trace_le_two_upperBlockJTraceAverage
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (Q : TriadicCube d) (j : ℕ) {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a) :
    Ch02.fullBlockTrace
        (normalizedCoarseAveragePositiveErrorMatrix hP hStruct (m : ℤ) Q j a) ≤
      2 * normalizedUpperBlockJTraceAverage hP hStruct (m : ℤ) Q j a := by
  classical
  let b := hP.barSigmaAtScale hStruct (m : ℤ)
  let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let r : BlockCoord d → ℝ := Ch04.scalarFullBlockInvSqrtDiag b c
  let D : FullBlockMat d := Matrix.diagonal r
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let Pcell : Ch02.DomainPartition (Ch02.cubeDomain Q) :=
    Ch02.descendantsDomainPartition Q j
  have hb : 0 < b := by
    simpa [b] using Section54.Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 m
  have hc : 0 < c := by
    simpa [c] using Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hcb : c ≤ b := by
    simpa [b, c] using
      Section54.VarianceBoundGoodScale.barSigmaStarAtScale_le_barSigmaAtScale_of_P4
        hP hStruct hP4 m
  have hsqrtb_ne : Real.sqrt b ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hb)
  have hcp2 : (Real.sqrt b)⁻¹ * (Real.sqrt b)⁻¹ = b⁻¹ := by
    field_simp [hsqrtb_ne]
    rw [Real.sq_sqrt hb.le]
  have hcq2 : Real.sqrt b * Real.sqrt b = b := by
    simpa [sq] using Real.sq_sqrt hb.le
  have hcpq : (Real.sqrt b)⁻¹ * Real.sqrt b = 1 :=
    inv_mul_cancel₀ hsqrtb_ne
  have hrUpper : ∀ i : Fin d, r (Sum.inl i) * r (Sum.inl i) ≤ b⁻¹ := by
    intro i
    dsimp [r, Ch04.scalarFullBlockInvSqrtDiag]
    exact le_of_eq hcp2
  have hrLower : ∀ i : Fin d, r (Sum.inr i) * r (Sum.inr i) ≤ b := by
    intro i
    dsimp [r, Ch04.scalarFullBlockInvSqrtDiag]
    calc
      Real.sqrt c * Real.sqrt c = c := by
        simpa [sq] using Real.sq_sqrt hc.le
      _ ≤ b := hcb
  have hcell :
      ∀ i : Pcell.Cell, Ch02.CoeffOn.RestrictsTo (F.coeffOn Q) (F.coeffOn i.1) := by
    simpa [F, Pcell] using
      restrictsTo_descendantsDomainPartition_of_aelocallyUniformlyEllipticField
        ha Q j
  have hParent :
      coarseBlockMatrix (cubeSet Q) a.toFun =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q) := by
    simpa [F] using
      Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha Q
  have hTerm :
      (fun R : TriadicCube d =>
          Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (F.coeffOn R)) =
        fun R : TriadicCube d => coarseBlockMatrix (cubeSet R) a.toFun := by
    funext R
    simpa [F] using
      (Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha R).symm
  have hAvg :
      Pcell.weightedBlockAverage
          (fun i : Pcell.Cell =>
            Ch02.coarseBlockMatrix (Pcell.cell i) (F.coeffOn i.1)) =
        descendantsAverageBlockMat Q j (fun R => coarseBlockMatrix (cubeSet R) a.toFun) := by
    calc
      Pcell.weightedBlockAverage
          (fun i : Pcell.Cell =>
            Ch02.coarseBlockMatrix (Pcell.cell i) (F.coeffOn i.1))
          =
        descendantsAverageBlockMat Q j
          (fun R : TriadicCube d =>
            Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (F.coeffOn R)) := by
            simpa [Pcell, Ch02.descendantsDomainPartition] using
              Ch02.descendantsDomainPartition_weightedBlockAverage Q j
                (fun R : TriadicCube d =>
                  Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (F.coeffOn R))
      _ = descendantsAverageBlockMat Q j
            (fun R => coarseBlockMatrix (cubeSet R) a.toFun) := by
            rw [hTerm]
  have hD :
      Matrix.diagonal r =
        Matrix.diagonal
          (Ch04.scalarFullBlockInvSqrtDiag
            (hP.barSigmaAtScale hStruct (m : ℤ))
            (hP.barSigmaStarAtScale hStruct (m : ℤ))) := by
    rfl
  have hJ :
      Pcell.weightedAverage
          (fun i : Pcell.Cell =>
            ∑ l : Fin d,
              Ch02.doubledResponseJ (Pcell.cell i) (F.coeffOn i.1)
                ((Real.sqrt b)⁻¹ • (Pi.single l 1 : Vec d), (0 : Vec d))
                (Real.sqrt b • (Pi.single l 1 : Vec d), (0 : Vec d))) =
        normalizedUpperBlockJTraceAverage hP hStruct (m : ℤ) Q j a := by
    calc
      Pcell.weightedAverage
          (fun i : Pcell.Cell =>
            ∑ l : Fin d,
              Ch02.doubledResponseJ (Pcell.cell i) (F.coeffOn i.1)
                ((Real.sqrt b)⁻¹ • (Pi.single l 1 : Vec d), (0 : Vec d))
                (Real.sqrt b • (Pi.single l 1 : Vec d), (0 : Vec d)))
          =
        descendantsAverage Q j
          (fun R =>
            ∑ l : Fin d,
              Ch02.doubledResponseJ (Ch02.cubeDomain R) (F.coeffOn R)
                ((Real.sqrt b)⁻¹ • (Pi.single l 1 : Vec d), (0 : Vec d))
                (Real.sqrt b • (Pi.single l 1 : Vec d), (0 : Vec d))) := by
            simpa [Pcell] using!
              Ch02.descendantsDomainPartition_weightedAverage Q j
                (fun R : TriadicCube d =>
                  ∑ l : Fin d,
                    Ch02.doubledResponseJ (Ch02.cubeDomain R) (F.coeffOn R)
                      ((Real.sqrt b)⁻¹ • (Pi.single l 1 : Vec d), (0 : Vec d))
                      (Real.sqrt b • (Pi.single l 1 : Vec d), (0 : Vec d)))
      _ = normalizedUpperBlockJTraceAverage hP hStruct (m : ℤ) Q j a := by
            unfold normalizedUpperBlockJTraceAverage
            congr 1
            funext R
            refine Finset.sum_congr rfl ?_
            intro l _hl
            rw [doubledResponseJ_eq_blockJObservableCubeSetBlockVec_of_aelocallyUniformlyEllipticField
              ha R]
            rw [normalizedInvSqrtBlockProbe_inl_eq hP hStruct (m : ℤ) l,
              normalizedSqrtBlockProbe_inl_eq hP hStruct (m : ℤ) l]
  have htrace :=
    Ch02.weightedBlockAverage_wrapAround_normalizedTrace_le_specialCoordinateDoubledResponseJ
      (a := F.coeffOn Q) (Pcell := Pcell)
      (aCell := fun i : Pcell.Cell => F.coeffOn i.1) hcell
      (σ := b) (cp := (Real.sqrt b)⁻¹) (cq := Real.sqrt b)
      hcp2 hcq2 hcpq r hrUpper hrLower
  have hPositive :=
    normalizedCoarseAveragePositiveErrorMatrix_eq_diagonal_blockSub
      hP hStruct (m : ℤ) Q j a
  rw [hPositive]
  simpa [b, c, r, D, F, Pcell, hParent.symm, hAvg, hD, hJ] using htrace

theorem positiveErrorWithNormalizer_trace_le_two_blockJTraceAverageWithNormalizers
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S T : FullBlockMat d) (Q : TriadicCube d) (j : ℕ)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a) :
    Ch02.fullBlockTrace
        (coarseAveragePositiveErrorMatrixWithNormalizer
          hP hStruct center S Q j a) ≤
      2 * blockJTraceAverageWithNormalizers S T Q j a := by
  classical
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let Pcell : Ch02.DomainPartition (Ch02.cubeDomain Q) :=
    Ch02.descendantsDomainPartition Q j
  have hcell :
      ∀ i : Pcell.Cell, Ch02.CoeffOn.RestrictsTo (F.coeffOn Q) (F.coeffOn i.1) := by
    simpa [F, Pcell] using
      restrictsTo_descendantsDomainPartition_of_aelocallyUniformlyEllipticField
        ha Q j
  have hParent :
      coarseBlockMatrix (cubeSet Q) a.toFun =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q) := by
    simpa [F] using
      Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha Q
  have hTerm :
      (fun R : TriadicCube d =>
          Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (F.coeffOn R)) =
        fun R : TriadicCube d => coarseBlockMatrix (cubeSet R) a.toFun := by
    funext R
    simpa [F] using
      (Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha R).symm
  have hAvg :
      Pcell.weightedBlockAverage
          (fun i : Pcell.Cell =>
            Ch02.coarseBlockMatrix (Pcell.cell i) (F.coeffOn i.1)) =
        descendantsAverageBlockMat Q j (fun R => coarseBlockMatrix (cubeSet R) a.toFun) := by
    calc
      Pcell.weightedBlockAverage
          (fun i : Pcell.Cell =>
            Ch02.coarseBlockMatrix (Pcell.cell i) (F.coeffOn i.1))
          =
        descendantsAverageBlockMat Q j
          (fun R : TriadicCube d =>
            Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (F.coeffOn R)) := by
            simpa [Pcell, Ch02.descendantsDomainPartition] using
              Ch02.descendantsDomainPartition_weightedBlockAverage Q j
                (fun R : TriadicCube d =>
                  Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (F.coeffOn R))
      _ = descendantsAverageBlockMat Q j
            (fun R => coarseBlockMatrix (cubeSet R) a.toFun) := by
            rw [hTerm]
  have hJ :
      Pcell.weightedAverage
          (fun i : Pcell.Cell =>
            ∑ α : BlockCoord d,
              Ch02.doubledResponseJ (Pcell.cell i) (F.coeffOn i.1)
                (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α)) =
        blockJTraceAverageWithNormalizers S T Q j a := by
    calc
      Pcell.weightedAverage
          (fun i : Pcell.Cell =>
            ∑ α : BlockCoord d,
              Ch02.doubledResponseJ (Pcell.cell i) (F.coeffOn i.1)
                (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α))
          =
        descendantsAverage Q j
          (fun R =>
            ∑ α : BlockCoord d,
              Ch02.doubledResponseJ (Ch02.cubeDomain R) (F.coeffOn R)
                (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α)) := by
            simpa [Pcell] using!
              Ch02.descendantsDomainPartition_weightedAverage Q j
                (fun R : TriadicCube d =>
                  ∑ α : BlockCoord d,
                    Ch02.doubledResponseJ (Ch02.cubeDomain R) (F.coeffOn R)
                      (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α))
      _ = blockJTraceAverageWithNormalizers S T Q j a := by
            unfold blockJTraceAverageWithNormalizers
            congr 1
            funext R
            refine Finset.sum_congr rfl ?_
            intro α _hα
            rw [doubledResponseJ_eq_blockJObservableCubeSetBlockVec_of_aelocallyUniformlyEllipticField
              ha R]
  have hParentBudget_nonneg :
      0 ≤ fullBlockJTraceBudgetWithNormalizers S T (coarseBlockMatrix (cubeSet Q) a.toFun) := by
    rw [hParent]
    rw [← sum_doubledResponseJ_fullBlockNormalizers_eq_traceBudget
      (U := Ch02.cubeDomain Q) (a := F.coeffOn Q) S T]
    exact Finset.sum_nonneg fun α _hα =>
      Ch02.doubledResponseJ_nonneg (Ch02.cubeDomain Q) (F.coeffOn Q)
        (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α)
  have hBudgetAvg :
      fullBlockJTraceBudgetWithNormalizers S T
          (descendantsAverageBlockMat Q j
            (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) =
        blockJTraceAverageWithNormalizers S T Q j a := by
    calc
      fullBlockJTraceBudgetWithNormalizers S T
          (descendantsAverageBlockMat Q j
            (fun R => coarseBlockMatrix (cubeSet R) a.toFun))
          =
        fullBlockJTraceBudgetWithNormalizers S T
          (Pcell.weightedBlockAverage
            (fun i : Pcell.Cell =>
              Ch02.coarseBlockMatrix (Pcell.cell i) (F.coeffOn i.1))) := by
            rw [hAvg]
      _ =
        Pcell.weightedAverage
          (fun i : Pcell.Cell =>
            fullBlockJTraceBudgetWithNormalizers S T
              (Ch02.coarseBlockMatrix (Pcell.cell i) (F.coeffOn i.1))) := by
            rw [fullBlockJTraceBudgetWithNormalizers_weightedBlockAverage]
      _ =
        Pcell.weightedAverage
          (fun i : Pcell.Cell =>
            ∑ α : BlockCoord d,
              Ch02.doubledResponseJ (Pcell.cell i) (F.coeffOn i.1)
                (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α)) := by
            unfold Ch02.DomainPartition.weightedAverage
            refine Finset.sum_congr rfl ?_
            intro i _hi
            change
              Pcell.weight i *
                  fullBlockJTraceBudgetWithNormalizers S T
                    (Ch02.coarseBlockMatrix (Pcell.cell i) (F.coeffOn i.1)) =
                Pcell.weight i *
                  (∑ α : BlockCoord d,
                    Ch02.doubledResponseJ (Pcell.cell i) (F.coeffOn i.1)
                      (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α))
            rw [← sum_doubledResponseJ_fullBlockNormalizers_eq_traceBudget
              (U := Pcell.cell i) (a := F.coeffOn i.1) S T]
      _ = blockJTraceAverageWithNormalizers S T Q j a := hJ
  have hAB :
      BlockMatLoewnerLE
        (coarseBlockMatrix (cubeSet Q) a.toFun)
        (descendantsAverageBlockMat Q j
          (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) := by
    let k : ℤ := Q.scale - (j : ℤ)
    have hk : k ≤ Q.scale := by
      dsimp [k]
      have hj : (0 : ℤ) ≤ (j : ℤ) := by exact_mod_cast Nat.zero_le j
      linarith
    simpa [k] using
      Ch04.coarseBlockMatrix_le_descendantsAverageBlockMat_cubeSet_of_aelocallyUniformlyEllipticField
        ha Q hk
  have htrace :=
    fullBlockTrace_transpose_blockSub_le_two_fullBlockJTraceBudgetWithNormalizers
      S T hAB (BlockMatLoewnerLE.blockReflect' hAB) hParentBudget_nonneg
  have hPositive :=
    coarseAveragePositiveErrorMatrixWithNormalizer_eq_transpose_blockSub
      hP hStruct center S Q j a
  rw [hPositive]
  simpa [hBudgetAvg] using htrace

theorem normalizedCoarseAveragePositiveErrorMatrix_posSemidef
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) (j : ℕ) {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a) :
    (normalizedCoarseAveragePositiveErrorMatrix hP hStruct center Q j a).PosSemidef := by
  classical
  let b := hP.barSigmaAtScale hStruct center
  let c := hP.barSigmaStarAtScale hStruct center
  let r : BlockCoord d → ℝ := Ch04.scalarFullBlockInvSqrtDiag b c
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let Pcell : Ch02.DomainPartition (Ch02.cubeDomain Q) :=
    Ch02.descendantsDomainPartition Q j
  let k : ℤ := Q.scale - (j : ℤ)
  have hk : k ≤ Q.scale := by
    dsimp [k]
    have hj : (0 : ℤ) ≤ (j : ℤ) := by exact_mod_cast Nat.zero_le j
    linarith
  have hSub :
      BlockMatLoewnerLE
        (coarseBlockMatrix (cubeSet Q) a.toFun)
        (descendantsAverageBlockMat Q j
          (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) := by
    simpa [k] using
      Ch04.coarseBlockMatrix_le_descendantsAverageBlockMat_cubeSet_of_aelocallyUniformlyEllipticField
        ha Q hk
  have hParentSymm :
      IsSymmetricBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) := by
    have hParent :
        coarseBlockMatrix (cubeSet Q) a.toFun =
          Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q) := by
      simpa [F] using
        Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
          ha Q
    rw [hParent]
    exact Ch02.isSymmetricBlockMat_coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q)
  have hTerm :
      (fun R : TriadicCube d =>
          Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (F.coeffOn R)) =
        fun R : TriadicCube d => coarseBlockMatrix (cubeSet R) a.toFun := by
    funext R
    simpa [F] using
      (Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha R).symm
  have hAvg :
      Pcell.weightedBlockAverage
          (fun i : Pcell.Cell =>
            Ch02.coarseBlockMatrix (Pcell.cell i) (F.coeffOn i.1)) =
        descendantsAverageBlockMat Q j (fun R => coarseBlockMatrix (cubeSet R) a.toFun) := by
    calc
      Pcell.weightedBlockAverage
          (fun i : Pcell.Cell =>
            Ch02.coarseBlockMatrix (Pcell.cell i) (F.coeffOn i.1))
          =
        descendantsAverageBlockMat Q j
          (fun R : TriadicCube d =>
            Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (F.coeffOn R)) := by
            simpa [Pcell, Ch02.descendantsDomainPartition] using
              Ch02.descendantsDomainPartition_weightedBlockAverage Q j
                (fun R : TriadicCube d =>
                  Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (F.coeffOn R))
      _ = descendantsAverageBlockMat Q j
            (fun R => coarseBlockMatrix (cubeSet R) a.toFun) := by
            rw [hTerm]
  have hAvgSymm :
      IsSymmetricBlockMat
        (descendantsAverageBlockMat Q j
          (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) := by
    have hWeightedSymm :
        IsSymmetricBlockMat
          (Pcell.weightedBlockAverage
            (fun i : Pcell.Cell =>
              Ch02.coarseBlockMatrix (Pcell.cell i) (F.coeffOn i.1))) :=
      Ch02.isSymmetricBlockMat_weightedBlockAverage Pcell
        (fun i : Pcell.Cell =>
          Ch02.coarseBlockMatrix (Pcell.cell i) (F.coeffOn i.1))
        (fun i => Ch02.isSymmetricBlockMat_coarseBlockMatrix (Pcell.cell i) (F.coeffOn i.1))
    simpa [hAvg] using hWeightedSymm
  have hPositive :=
    normalizedCoarseAveragePositiveErrorMatrix_eq_diagonal_blockSub
      hP hStruct center Q j a
  rw [hPositive]
  exact diagonal_blockSub_posSemidef_of_blockMatLoewnerLE
    r hSub hParentSymm hAvgSymm

theorem coarseAveragePositiveErrorMatrixWithNormalizer_posSemidef
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S : FullBlockMat d) (Q : TriadicCube d) (j : ℕ)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a) :
    (coarseAveragePositiveErrorMatrixWithNormalizer
      hP hStruct center S Q j a).PosSemidef := by
  classical
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let Pcell : Ch02.DomainPartition (Ch02.cubeDomain Q) :=
    Ch02.descendantsDomainPartition Q j
  let k : ℤ := Q.scale - (j : ℤ)
  have hk : k ≤ Q.scale := by
    dsimp [k]
    have hj : (0 : ℤ) ≤ (j : ℤ) := by exact_mod_cast Nat.zero_le j
    linarith
  have hSub :
      BlockMatLoewnerLE
        (coarseBlockMatrix (cubeSet Q) a.toFun)
        (descendantsAverageBlockMat Q j
          (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) := by
    simpa [k] using
      Ch04.coarseBlockMatrix_le_descendantsAverageBlockMat_cubeSet_of_aelocallyUniformlyEllipticField
        ha Q hk
  have hParentSymm :
      IsSymmetricBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) := by
    have hParent :
        coarseBlockMatrix (cubeSet Q) a.toFun =
          Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q) := by
      simpa [F] using
        Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
          ha Q
    rw [hParent]
    exact Ch02.isSymmetricBlockMat_coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q)
  have hTerm :
      (fun R : TriadicCube d =>
          Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (F.coeffOn R)) =
        fun R : TriadicCube d => coarseBlockMatrix (cubeSet R) a.toFun := by
    funext R
    simpa [F] using
      (Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha R).symm
  have hAvg :
      Pcell.weightedBlockAverage
          (fun i : Pcell.Cell =>
            Ch02.coarseBlockMatrix (Pcell.cell i) (F.coeffOn i.1)) =
        descendantsAverageBlockMat Q j (fun R => coarseBlockMatrix (cubeSet R) a.toFun) := by
    calc
      Pcell.weightedBlockAverage
          (fun i : Pcell.Cell =>
            Ch02.coarseBlockMatrix (Pcell.cell i) (F.coeffOn i.1))
          =
        descendantsAverageBlockMat Q j
          (fun R : TriadicCube d =>
            Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (F.coeffOn R)) := by
            simpa [Pcell, Ch02.descendantsDomainPartition] using
              Ch02.descendantsDomainPartition_weightedBlockAverage Q j
                (fun R : TriadicCube d =>
                  Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (F.coeffOn R))
      _ = descendantsAverageBlockMat Q j
            (fun R => coarseBlockMatrix (cubeSet R) a.toFun) := by
            rw [hTerm]
  have hAvgSymm :
      IsSymmetricBlockMat
        (descendantsAverageBlockMat Q j
          (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) := by
    have hWeightedSymm :
        IsSymmetricBlockMat
          (Pcell.weightedBlockAverage
            (fun i : Pcell.Cell =>
              Ch02.coarseBlockMatrix (Pcell.cell i) (F.coeffOn i.1))) :=
      Ch02.isSymmetricBlockMat_weightedBlockAverage Pcell
        (fun i : Pcell.Cell =>
          Ch02.coarseBlockMatrix (Pcell.cell i) (F.coeffOn i.1))
        (fun i => Ch02.isSymmetricBlockMat_coarseBlockMatrix (Pcell.cell i) (F.coeffOn i.1))
    simpa [hAvg] using hWeightedSymm
  have hPositive :=
    coarseAveragePositiveErrorMatrixWithNormalizer_eq_transpose_blockSub
      hP hStruct center S Q j a
  rw [hPositive]
  exact transpose_blockSub_posSemidef_of_blockMatLoewnerLE
    S hSub hParentSymm hAvgSymm

theorem coarseAverageErrorOperatorNormSqWithNormalizer_le_four_blockJTraceAverageSqWithNormalizers
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S T : FullBlockMat d) (Q : TriadicCube d) (j : ℕ)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a) :
    coarseAverageErrorOperatorNormSqWithNormalizer hP hStruct center S Q j a ≤
      4 * blockJTraceAverageSqWithNormalizers S T Q j a := by
  classical
  let M : FullBlockMat d :=
    coarseAveragePositiveErrorMatrixWithNormalizer hP hStruct center S Q j a
  let J : ℝ := blockJTraceAverageWithNormalizers S T Q j a
  have hErrorMatrix :
      coarseAverageErrorMatrixWithNormalizer hP hStruct center S Q j a = -M := by
    simp [M, coarseAverageErrorMatrixWithNormalizer,
      coarseAveragePositiveErrorMatrixWithNormalizer, sub_eq_add_neg, add_comm]
  have hErrorSq :
      coarseAverageErrorOperatorNormSqWithNormalizer hP hStruct center S Q j a =
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ^ (2 : ℕ) := by
    simp [coarseAverageErrorOperatorNormSqWithNormalizer, hErrorMatrix]
  have hPSD : M.PosSemidef := by
    simpa [M] using
      coarseAveragePositiveErrorMatrixWithNormalizer_posSemidef
        hP hStruct center S Q j ha
  have htrace :
      Ch02.fullBlockTrace M ≤ 2 * J := by
    simpa [M, J] using
      positiveErrorWithNormalizer_trace_le_two_blockJTraceAverageWithNormalizers
        hP hStruct center S T Q j ha
  have htrace_nonneg : 0 ≤ Ch02.fullBlockTrace M := by
    have hfull : Ch02.fullBlockTrace M = M.trace := by
      simp [Ch02.fullBlockTrace, Matrix.trace]
    rw [hfull]
    exact hPSD.trace_nonneg
  calc
    coarseAverageErrorOperatorNormSqWithNormalizer hP hStruct center S Q j a
        = ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ^ (2 : ℕ) :=
          hErrorSq
    _ ≤ Ch02.fullBlockTrace M ^ (2 : ℕ) :=
          fullBlockOperatorNormSq_le_trace_sq_of_posSemidef M hPSD
    _ ≤ (2 * J) ^ (2 : ℕ) :=
          pow_le_pow_left₀ htrace_nonneg htrace 2
    _ = 4 * blockJTraceAverageSqWithNormalizers S T Q j a := by
          simp [blockJTraceAverageSqWithNormalizers, J]
          ring

theorem coarseAverageErrorOperatorNormSqWithNormalizer_le_four_blockJTraceAverageSqWithNormalizers_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S T : FullBlockMat d) (Q : TriadicCube d) (j : ℕ) :
    (fun a : RegCoeffField d =>
      coarseAverageErrorOperatorNormSqWithNormalizer hP hStruct center S Q j a)
      ≤ᵐ[P]
    fun a : RegCoeffField d =>
      4 * blockJTraceAverageSqWithNormalizers S T Q j a := by
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  exact coarseAverageErrorOperatorNormSqWithNormalizer_le_four_blockJTraceAverageSqWithNormalizers
    hP hStruct center S T Q j ha

theorem normalizedCoarseAverageErrorOperatorNormSq_le_four_normalizedBlockJTraceAverageSq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (Q : TriadicCube d) (j : ℕ) {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a) :
    normalizedCoarseAverageErrorOperatorNormSq hP hStruct (m : ℤ) Q j a ≤
      4 * normalizedBlockJTraceAverageSq hP hStruct (m : ℤ) Q j a := by
  classical
  let M : FullBlockMat d :=
    normalizedCoarseAveragePositiveErrorMatrix hP hStruct (m : ℤ) Q j a
  let J : ℝ := normalizedBlockJTraceAverage hP hStruct (m : ℤ) Q j a
  have hErrorMatrix :
      normalizedCoarseAverageErrorMatrix hP hStruct (m : ℤ) Q j a = -M := by
    simp [M, normalizedCoarseAverageErrorMatrix,
      normalizedCoarseAveragePositiveErrorMatrix, sub_eq_add_neg, add_comm]
  have hErrorSq :
      normalizedCoarseAverageErrorOperatorNormSq hP hStruct (m : ℤ) Q j a =
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ^ (2 : ℕ) := by
    simp [normalizedCoarseAverageErrorOperatorNormSq, hErrorMatrix]
  have hPSD : M.PosSemidef := by
    simpa [M] using
      normalizedCoarseAveragePositiveErrorMatrix_posSemidef
        hP hStruct (m : ℤ) Q j ha
  have htraceUpper :=
    normalizedPositiveError_trace_le_two_upperBlockJTraceAverage
      hP hStruct hP4 m Q j ha
  have hupper_le :
      normalizedUpperBlockJTraceAverage hP hStruct (m : ℤ) Q j a ≤ J := by
    simpa [J] using
      normalizedUpperBlockJTraceAverage_le_normalizedBlockJTraceAverage
        hP hStruct (m : ℤ) Q j a
  have htrace : Ch02.fullBlockTrace M ≤ 2 * J := by
    simpa [M, J] using htraceUpper.trans (by nlinarith)
  have htrace_nonneg : 0 ≤ Ch02.fullBlockTrace M := by
    have hfull : Ch02.fullBlockTrace M = M.trace := by
      simp [Ch02.fullBlockTrace, Matrix.trace]
    rw [hfull]
    exact hPSD.trace_nonneg
  calc
    normalizedCoarseAverageErrorOperatorNormSq hP hStruct (m : ℤ) Q j a
        = ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ^ (2 : ℕ) :=
          hErrorSq
    _ ≤ Ch02.fullBlockTrace M ^ (2 : ℕ) :=
          fullBlockOperatorNormSq_le_trace_sq_of_posSemidef M hPSD
    _ ≤ (2 * J) ^ (2 : ℕ) :=
          pow_le_pow_left₀ htrace_nonneg htrace 2
    _ = 4 * normalizedBlockJTraceAverageSq hP hStruct (m : ℤ) Q j a := by
          simp [normalizedBlockJTraceAverageSq, J]
          ring

theorem normalizedCoarseAverageErrorOperatorNormSq_le_four_normalizedBlockJTraceAverageSq_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (Q : TriadicCube d) (j : ℕ) :
    (fun a : RegCoeffField d =>
      normalizedCoarseAverageErrorOperatorNormSq hP hStruct (m : ℤ) Q j a)
      ≤ᵐ[P]
    fun a : RegCoeffField d =>
      4 * normalizedBlockJTraceAverageSq hP hStruct (m : ℤ) Q j a := by
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  exact normalizedCoarseAverageErrorOperatorNormSq_le_four_normalizedBlockJTraceAverageSq
    hP hStruct hP4 m Q j ha
end

end Section56
end Ch05
end Book
end Homogenization
