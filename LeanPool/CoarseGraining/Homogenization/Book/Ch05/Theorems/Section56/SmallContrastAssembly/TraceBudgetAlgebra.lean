/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.SmallContrastAssembly.TraceAveragePackaging
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.VarianceEstimateQuadratic.MatrixTools
import Mathlib.Algebra.Order.Chebyshev

/-! # Trace Budget Algebra -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace SmallContrastAssembly

open Section54.VarianceBoundGoodScale

theorem normalizedBlockJTraceAverage_eq_blockJTraceAverageWithNormalizers
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) (j : ℕ) (a : RegCoeffField d) :
    let b := hP.barSigmaAtScale hStruct center
    let c := hP.barSigmaStarAtScale hStruct center
    let S : FullBlockMat d :=
      Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
    let T : FullBlockMat d := Matrix.diagonal (scalarFullBlockSqrtDiag b c)
    normalizedBlockJTraceAverage hP hStruct center Q j a =
      blockJTraceAverageWithNormalizers S T Q j a := by
  intro b c S T
  unfold normalizedBlockJTraceAverage blockJTraceAverageWithNormalizers
  congr 1
  funext R
  congr 1
  funext α
  congr 1 <;>
    simp [fullBlockMatrixProbe, normalizedInvSqrtBlockProbe,
      normalizedSqrtBlockProbe, S, T, b, c]

theorem blockJTraceAverageWithNormalizers_eq_traceBudget_descendantsAverageBlockMat
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (S T : FullBlockMat d) (Q : TriadicCube d) (j : ℕ) :
    blockJTraceAverageWithNormalizers S T Q j a =
      fullBlockJTraceBudgetWithNormalizers S T
        (descendantsAverageBlockMat Q j
          (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) := by
  classical
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let Pcell : Ch02.DomainPartition (Ch02.cubeDomain Q) :=
    Ch02.descendantsDomainPartition Q j
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
  calc
    blockJTraceAverageWithNormalizers S T Q j a
        = Pcell.weightedAverage
          (fun i : Pcell.Cell =>
            ∑ α : BlockCoord d,
              Ch02.doubledResponseJ (Pcell.cell i) (F.coeffOn i.1)
                (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α)) := hJ.symm
    _ =
        Pcell.weightedAverage
          (fun i : Pcell.Cell =>
            fullBlockJTraceBudgetWithNormalizers S T
              (Ch02.coarseBlockMatrix (Pcell.cell i) (F.coeffOn i.1))) := by
            unfold Ch02.DomainPartition.weightedAverage
            refine Finset.sum_congr rfl ?_
            intro i _hi
            change
              Pcell.weight i *
                  (∑ α : BlockCoord d,
                    Ch02.doubledResponseJ (Pcell.cell i) (F.coeffOn i.1)
                      (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α)) =
                Pcell.weight i *
                  fullBlockJTraceBudgetWithNormalizers S T
                    (Ch02.coarseBlockMatrix (Pcell.cell i) (F.coeffOn i.1))
            have hbudget :
                (∑ α : BlockCoord d,
                    Ch02.doubledResponseJ (Pcell.cell i) (F.coeffOn i.1)
                      (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α)) =
                  fullBlockJTraceBudgetWithNormalizers S T
                    (Ch02.coarseBlockMatrix (Pcell.cell i) (F.coeffOn i.1)) :=
              sum_doubledResponseJ_fullBlockNormalizers_eq_traceBudget
                (Pcell.cell i) (F.coeffOn i.1) S T
            rw [hbudget]
    _ =
        fullBlockJTraceBudgetWithNormalizers S T
          (Pcell.weightedBlockAverage
            (fun i : Pcell.Cell =>
              Ch02.coarseBlockMatrix (Pcell.cell i) (F.coeffOn i.1))) := by
            rw [fullBlockJTraceBudgetWithNormalizers_weightedBlockAverage]
    _ =
        fullBlockJTraceBudgetWithNormalizers S T
          (descendantsAverageBlockMat Q j
            (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) := by
          rw [hAvg]

private theorem vecDot_indicator_self {d : ℕ} (i : Fin d) (r s : ℝ) :
    vecDot (fun j => if j = i then r else 0)
        (fun j => if j = i then s else 0) =
      r * s := by
  have h1 :
      (fun j : Fin d => if j = i then r else 0) =
        r • (Pi.single i 1 : Vec d) := by
    funext j
    by_cases h : j = i <;> simp [h, smul_eq_mul]
  have h2 :
      (fun j : Fin d => if j = i then s else 0) =
        s • (Pi.single i 1 : Vec d) := by
    funext j
    by_cases h : j = i <;> simp [h, smul_eq_mul]
  rw [h1, h2]
  simp [vecDot_smul_left, vecDot_smul_right, vecDot_single_left]
  ring

private theorem fullBlockMatrixProbe_diagonal_dot
    {d : ℕ} (r s : BlockCoord d → ℝ) (α : BlockCoord d) :
    blockVecDot
        (fullBlockMatrixProbe (Matrix.diagonal r) α)
        (fullBlockMatrixProbe (Matrix.diagonal s) α) =
      r α * s α := by
  cases α with
  | inl i =>
      simp [fullBlockMatrixProbe, ofFullBlockVec, Matrix.mulVec, Matrix.diagonal,
        blockVecDot]
      have hmain :
          vecDot (fun j : Fin d => if j = i then r (Sum.inl j) else 0)
              (fun j : Fin d => if j = i then s (Sum.inl j) else 0) =
            r (Sum.inl i) * s (Sum.inl i) := by
        convert vecDot_indicator_self i (r (Sum.inl i)) (s (Sum.inl i)) using 2
        · funext j
          by_cases h : j = i <;> simp [h]
        · funext j
          by_cases h : j = i <;> simp [h]
      rw [hmain]
      simp [vecDot]
  | inr i =>
      simp [fullBlockMatrixProbe, ofFullBlockVec, Matrix.mulVec, Matrix.diagonal,
        blockVecDot]
      have hmain :
          vecDot (fun j : Fin d => if j = i then r (Sum.inr j) else 0)
              (fun j : Fin d => if j = i then s (Sum.inr j) else 0) =
            r (Sum.inr i) * s (Sum.inr i) := by
        convert vecDot_indicator_self i (r (Sum.inr i)) (s (Sum.inr i)) using 2
        · funext j
          by_cases h : j = i <;> simp [h]
        · funext j
          by_cases h : j = i <;> simp [h]
      rw [hmain]
      simp [vecDot]

private theorem normalized_diagonal_probe_dot_eq_one
    {d : ℕ} {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (α : BlockCoord d) :
    blockVecDot
        (fullBlockMatrixProbe
          (Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)) α)
        (fullBlockMatrixProbe
          (Matrix.diagonal (scalarFullBlockSqrtDiag b c)) α) =
      1 := by
  have hdot :=
    fullBlockMatrixProbe_diagonal_dot
      (d := d) (Ch04.scalarFullBlockInvSqrtDiag b c)
      (scalarFullBlockSqrtDiag b c) α
  cases α with
  | inl i =>
      calc
        blockVecDot
            (fullBlockMatrixProbe
              (Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)) (Sum.inl i))
            (fullBlockMatrixProbe
              (Matrix.diagonal (scalarFullBlockSqrtDiag b c)) (Sum.inl i))
            = (√b)⁻¹ * √b := by
              simpa [Ch04.scalarFullBlockInvSqrtDiag, scalarFullBlockSqrtDiag] using hdot
        _ = 1 := inv_mul_cancel₀ (ne_of_gt ((Real.sqrt_pos).2 hb))
  | inr i =>
      calc
        blockVecDot
            (fullBlockMatrixProbe
              (Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)) (Sum.inr i))
            (fullBlockMatrixProbe
              (Matrix.diagonal (scalarFullBlockSqrtDiag b c)) (Sum.inr i))
            = √c * (√c)⁻¹ := by
              simpa [Ch04.scalarFullBlockInvSqrtDiag, scalarFullBlockSqrtDiag] using hdot
        _ = 1 := mul_inv_cancel₀ (ne_of_gt ((Real.sqrt_pos).2 hc))

private theorem normalized_reflect_trace_eq_theta_trace
    {d : ℕ} {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (A : BlockMat d) :
    let D : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
    let T : FullBlockMat d := Matrix.diagonal (scalarFullBlockSqrtDiag b c)
    let θ : ℝ := b * c⁻¹
    Ch02.fullBlockTrace (T * toFullBlockMat (blockReflect A) * T) =
      θ * Ch02.fullBlockTrace (D * toFullBlockMat A * D) := by
  intro D T θ
  classical
  unfold Ch02.fullBlockTrace
  simp [D, T, θ, Ch04.scalarFullBlockInvSqrtDiag, scalarFullBlockSqrtDiag,
    blockReflect, toFullBlockMat, Matrix.mul_apply, Matrix.diagonal]
  have hsqrtb_sq : √b * √b = b := by simpa [sq] using Real.sq_sqrt hb.le
  have hsqrtc_sq : √c * √c = c := by simpa [sq] using Real.sq_sqrt hc.le
  have hsqrtb_ne : √b ≠ 0 := ne_of_gt ((Real.sqrt_pos).2 hb)
  have hsqrtc_ne : √c ≠ 0 := ne_of_gt ((Real.sqrt_pos).2 hc)
  have hinvb : (√b)⁻¹ * (√b)⁻¹ = b⁻¹ := by
    field_simp [hsqrtb_ne]
    simpa [sq] using hsqrtb_sq.symm
  have hinvc : (√c)⁻¹ * (√c)⁻¹ = c⁻¹ := by
    field_simp [hsqrtc_ne]
    simpa [sq] using hsqrtc_sq.symm
  have hL1 : (∑ x, √b * A.lowerRight x x * √b) =
      ∑ x, b * A.lowerRight x x := by
    refine Finset.sum_congr rfl ?_
    intro x _
    calc
      √b * A.lowerRight x x * √b = (√b * √b) * A.lowerRight x x := by ring
      _ = b * A.lowerRight x x := by rw [hsqrtb_sq]
  have hL2 : (∑ x, (√c)⁻¹ * A.upperLeft x x * (√c)⁻¹) =
      ∑ x, c⁻¹ * A.upperLeft x x := by
    refine Finset.sum_congr rfl ?_
    intro x _
    calc
      (√c)⁻¹ * A.upperLeft x x * (√c)⁻¹ =
          ((√c)⁻¹ * (√c)⁻¹) * A.upperLeft x x := by ring
      _ = c⁻¹ * A.upperLeft x x := by rw [hinvc]
  have hR1 : (∑ x, (√b)⁻¹ * A.upperLeft x x * (√b)⁻¹) =
      ∑ x, b⁻¹ * A.upperLeft x x := by
    refine Finset.sum_congr rfl ?_
    intro x _
    calc
      (√b)⁻¹ * A.upperLeft x x * (√b)⁻¹ =
          ((√b)⁻¹ * (√b)⁻¹) * A.upperLeft x x := by ring
      _ = b⁻¹ * A.upperLeft x x := by rw [hinvb]
  have hR2 : (∑ x, √c * A.lowerRight x x * √c) =
      ∑ x, c * A.lowerRight x x := by
    refine Finset.sum_congr rfl ?_
    intro x _
    calc
      √c * A.lowerRight x x * √c = (√c * √c) * A.lowerRight x x := by ring
      _ = c * A.lowerRight x x := by rw [hsqrtc_sq]
  rw [hL1, hL2, hR1, hR2]
  have hbne : b ≠ 0 := ne_of_gt hb
  have hcne : c ≠ 0 := ne_of_gt hc
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  field_simp [hbne, hcne]
  ring

theorem fullBlockJTraceBudgetWithNormalizers_normalized_eq_trace
    {d : ℕ} {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (A : BlockMat d) :
    let D : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
    let T : FullBlockMat d := Matrix.diagonal (scalarFullBlockSqrtDiag b c)
    let θ : ℝ := b * c⁻¹
    fullBlockJTraceBudgetWithNormalizers D T A =
      ((1 + θ) / 2) * Ch02.fullBlockTrace (D * toFullBlockMat A * D) -
        (Fintype.card (BlockCoord d) : ℝ) := by
  intro D T θ
  classical
  have hDtrans : Matrix.transpose D = D := by
    ext α β
    by_cases h : α = β
    · subst β
      simp [D, Matrix.transpose_apply, Matrix.diagonal]
    · have hba : β ≠ α := fun h' => h h'.symm
      simp [D, Matrix.transpose_apply, Matrix.diagonal, h, hba]
  have hTtrans : Matrix.transpose T = T := by
    ext α β
    by_cases h : α = β
    · subst β
      simp [T, Matrix.transpose_apply, Matrix.diagonal]
    · have hba : β ≠ α := fun h' => h h'.symm
      simp [T, Matrix.transpose_apply, Matrix.diagonal, h, hba]
  have hfirst :
      (∑ α : BlockCoord d,
        blockVecDot (fullBlockMatrixProbe D α)
          (blockMatVecMul A (fullBlockMatrixProbe D α))) =
        Ch02.fullBlockTrace (D * toFullBlockMat A * D) := by
    simpa [hDtrans] using
      (fullBlockTrace_transpose_mul_mul_eq_sum_blockVecDot D (toFullBlockMat A)).symm
  have hsecond :
      (∑ α : BlockCoord d,
        blockVecDot (fullBlockMatrixProbe T α)
          (blockMatVecMul (blockReflect A) (fullBlockMatrixProbe T α))) =
        Ch02.fullBlockTrace (T * toFullBlockMat (blockReflect A) * T) := by
    simpa [hTtrans] using
      (fullBlockTrace_transpose_mul_mul_eq_sum_blockVecDot T
        (toFullBlockMat (blockReflect A))).symm
  have hpair :
      (∑ α : BlockCoord d,
        blockVecDot (fullBlockMatrixProbe D α) (fullBlockMatrixProbe T α)) =
        (Fintype.card (BlockCoord d) : ℝ) := by
    calc
      (∑ α : BlockCoord d,
        blockVecDot (fullBlockMatrixProbe D α) (fullBlockMatrixProbe T α))
          = ∑ _α : BlockCoord d, (1 : ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro α _hα
              simpa [D, T] using normalized_diagonal_probe_dot_eq_one hb hc α
      _ = (Fintype.card (BlockCoord d) : ℝ) := by simp
  have hreflect :=
    normalized_reflect_trace_eq_theta_trace (d := d) hb hc A
  have hreflect' :
      Ch02.fullBlockTrace (T * toFullBlockMat (blockReflect A) * T) =
        θ * Ch02.fullBlockTrace (D * toFullBlockMat A * D) := by
    simpa [D, T, θ] using hreflect
  unfold fullBlockJTraceBudgetWithNormalizers
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [hfirst, hsecond, hpair]
  rw [hreflect']
  ring

theorem descendantsAverageNormalizedFluctuationMatrix_eq_diagonal_average_sub_annealed
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) (j : ℕ) (a : RegCoeffField d) :
    let b := hP.barSigmaAtScale hStruct center
    let c := hP.barSigmaStarAtScale hStruct center
    let D : FullBlockMat d :=
      Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
    descendantsAverageNormalizedFluctuationMatrix hP hStruct center Q j a =
      D *
        (toFullBlockMat
            (descendantsAverageBlockMat Q j
              (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) -
          toFullBlockMat (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center)) *
        D := by
  intro b c D
  let Abar : FullBlockMat d :=
    toFullBlockMat (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center)
  let F : TriadicCube d → FullBlockMat d :=
    fun R => toFullBlockMat (coarseBlockMatrix (cubeSet R) a.toFun)
  have hAvg :
      descendantsAverageNormalizedFluctuationMatrix hP hStruct center Q j a =
        D * (descendantsAverageFullBlockMat Q j F - Abar) * D := by
    simpa [descendantsAverageNormalizedFluctuationMatrix, F, Abar,
      fullBlockNormalizedFluctuationMatrix, D, b, c] using
      descendantsAverageFullBlockMat_diagonal_sub_const_mul_diagonal
        (Q := Q) (j := j) D Abar F
  calc
    descendantsAverageNormalizedFluctuationMatrix hP hStruct center Q j a
        = D * (descendantsAverageFullBlockMat Q j F - Abar) * D := hAvg
    _ =
        D *
          (toFullBlockMat
              (descendantsAverageBlockMat Q j
                (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) -
            toFullBlockMat (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center)) *
          D := by
          rw [toFullBlockMat_descendantsAverageBlockMat]

theorem fullBlockTrace_sq_le_card_sq_operatorNormSq
    {d : ℕ} [NeZero d] (M : FullBlockMat d) :
    Ch02.fullBlockTrace M ^ (2 : ℕ) ≤
      (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ) *
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ^ (2 : ℕ) := by
  classical
  let f : BlockCoord d → ℝ := fun α =>
    fullBlockQuadratic M (fullBlockCoordinateProbe α)
  have htrace_eq : Ch02.fullBlockTrace M = ∑ α : BlockCoord d, f α := by
    simp [Ch02.fullBlockTrace, f, fullBlockQuadratic_coordinateProbe]
  have hsum :
      (∑ α : BlockCoord d, f α) ^ (2 : ℕ) ≤
        (Fintype.card (BlockCoord d) : ℝ) *
          ∑ α : BlockCoord d, f α ^ (2 : ℕ) := by
    simpa using
      (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (BlockCoord d)))
        (f := f))
  have hterm :
      ∀ α : BlockCoord d,
        f α ^ (2 : ℕ) ≤
          ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ^ (2 : ℕ) := by
    intro α
    have hquad :=
      fullBlockQuadratic_abs_sq_le_operatorNorm_sq_mul_dotProduct_sq
        M (fullBlockCoordinateProbe α)
    have habs_sq :
        f α ^ (2 : ℕ) = |f α| ^ (2 : ℕ) := by
      rw [sq_abs]
    have hdot :
        dotProduct (fullBlockCoordinateProbe α) (fullBlockCoordinateProbe α) = 1 := by
      rw [← fullBlockQuadratic_one]
      simp
    rw [habs_sq]
    simpa [f, hdot] using hquad
  calc
    Ch02.fullBlockTrace M ^ (2 : ℕ)
        = (∑ α : BlockCoord d, f α) ^ (2 : ℕ) := by rw [htrace_eq]
    _ ≤ (Fintype.card (BlockCoord d) : ℝ) *
          ∑ α : BlockCoord d, f α ^ (2 : ℕ) := hsum
    _ ≤ (Fintype.card (BlockCoord d) : ℝ) *
          ∑ _α : BlockCoord d,
            ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ^ (2 : ℕ) := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun α _hα => hterm α) (Nat.cast_nonneg _)
    _ =
        (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ) *
          ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ^ (2 : ℕ) := by
          simp
          ring

end SmallContrastAssembly

end

end Section56
end Ch05
end Book
end Homogenization
