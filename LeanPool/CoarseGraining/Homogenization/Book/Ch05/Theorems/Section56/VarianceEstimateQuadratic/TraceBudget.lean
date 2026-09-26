/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.VarianceEstimateQuadratic.Basic

/-! # Trace Budget -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

noncomputable def fullBlockJTraceBudgetWithNormalizers
    {d : ℕ} (S T : FullBlockMat d) (A : BlockMat d) : ℝ :=
  ∑ α : BlockCoord d,
    ((1 / 2 : ℝ) *
        blockVecDot (fullBlockMatrixProbe S α)
          (blockMatVecMul A (fullBlockMatrixProbe S α)) +
      (1 / 2 : ℝ) *
        blockVecDot (fullBlockMatrixProbe T α)
          (blockMatVecMul (blockReflect A) (fullBlockMatrixProbe T α)) -
      blockVecDot (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α))

theorem sum_doubledResponseJ_fullBlockNormalizers_eq_traceBudget
    {d : ℕ} (U : Ch02.Domain d) (a : Ch02.CoeffOn U)
    (S T : FullBlockMat d) :
    (∑ α : BlockCoord d,
      Ch02.doubledResponseJ U a
        (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α)) =
      fullBlockJTraceBudgetWithNormalizers S T (Ch02.coarseBlockMatrix U a) := by
  classical
  unfold fullBlockJTraceBudgetWithNormalizers
  refine Finset.sum_congr rfl ?_
  intro α _hα
  rw [(Ch02.blockCoarseMatrixTheory U a).doubled_response_splitting]
  rw [(Ch02.blockCoarseMatrixTheory U a).starred_inverse_formula]

theorem weightedAverage_const_mul'
    {d : ℕ} {U : Ch02.Domain d}
    (Pcell : Ch02.DomainPartition U) (c : ℝ) (f : Pcell.Cell → ℝ) :
    Pcell.weightedAverage (fun i => c * f i) = c * Pcell.weightedAverage f := by
  classical
  let : Fintype Pcell.Cell := Pcell.instFintype
  unfold Ch02.DomainPartition.weightedAverage
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

theorem vecDot_matVecMul_weightedMatAverage'
    {d : ℕ} {U : Ch02.Domain d} (Pcell : Ch02.DomainPartition U)
    (F : Pcell.Cell → Mat d) (x y : Vec d) :
    vecDot x (matVecMul (Pcell.weightedMatAverage F) y) =
      Pcell.weightedAverage fun i => vecDot x (matVecMul (F i) y) := by
  classical
  let : Fintype Pcell.Cell := Pcell.instFintype
  simp [Ch02.DomainPartition.weightedMatAverage, Ch02.DomainPartition.weightedAverage,
    vecDot, matVecMul, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  ring_nf
  let W : Pcell.Cell → Fin d → Fin d → ℝ :=
    fun c i j => F c i j * x i * y j * Pcell.weight c
  change (∑ i : Fin d, ∑ j : Fin d, ∑ c : Pcell.Cell, W c i j) =
    ∑ c : Pcell.Cell, ∑ i : Fin d, ∑ j : Fin d, W c i j
  calc
    (∑ i : Fin d, ∑ j : Fin d, ∑ c : Pcell.Cell, W c i j)
        = ∑ i : Fin d, ∑ c : Pcell.Cell, ∑ j : Fin d, W c i j := by
          congr with i
          rw [Finset.sum_comm]
    _ = ∑ c : Pcell.Cell, ∑ i : Fin d, ∑ j : Fin d, W c i j := by
          rw [Finset.sum_comm]

theorem blockVecDot_blockMatVecMul_weightedBlockAverage'
    {d : ℕ} {U : Ch02.Domain d} (Pcell : Ch02.DomainPartition U)
    (F : Pcell.Cell → BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (Pcell.weightedBlockAverage F) X) =
      Pcell.weightedAverage
        (fun c => blockVecDot X (blockMatVecMul (F c) X)) := by
  classical
  let : Fintype Pcell.Cell := Pcell.instFintype
  rcases X with ⟨p, q⟩
  rw [blockMatVecMul, blockVecDot, vecDot_add_right, vecDot_add_right]
  change
    vecDot p (matVecMul (Pcell.weightedMatAverage fun i => (F i).upperLeft) p) +
          vecDot p (matVecMul (Pcell.weightedMatAverage fun i => (F i).upperRight) q) +
        (vecDot q (matVecMul (Pcell.weightedMatAverage fun i => (F i).lowerLeft) p) +
          vecDot q (matVecMul (Pcell.weightedMatAverage fun i => (F i).lowerRight) q)) =
      Pcell.weightedAverage fun i => blockVecDot (p, q) (blockMatVecMul (F i) (p, q))
  rw [vecDot_matVecMul_weightedMatAverage' Pcell (fun i => (F i).upperLeft)]
  rw [vecDot_matVecMul_weightedMatAverage' Pcell (fun i => (F i).upperRight)]
  rw [vecDot_matVecMul_weightedMatAverage' Pcell (fun i => (F i).lowerLeft)]
  rw [vecDot_matVecMul_weightedMatAverage' Pcell (fun i => (F i).lowerRight)]
  simp [Ch02.DomainPartition.weightedAverage, blockMatVecMul, blockVecDot,
    vecDot_add_right, Finset.sum_add_distrib, mul_add, add_assoc]

theorem blockReflect_weightedBlockAverage
    {d : ℕ} {U : Ch02.Domain d} (Pcell : Ch02.DomainPartition U)
    (F : Pcell.Cell → BlockMat d) :
    blockReflect (Pcell.weightedBlockAverage F) =
      Pcell.weightedBlockAverage (fun c => blockReflect (F c)) := by
  classical
  let : Fintype Pcell.Cell := Pcell.instFintype
  rfl

theorem blockVecDot_blockReflect_weightedBlockAverage'
    {d : ℕ} {U : Ch02.Domain d} (Pcell : Ch02.DomainPartition U)
    (F : Pcell.Cell → BlockMat d) (X : BlockVec d) :
    blockVecDot X
        (blockMatVecMul (blockReflect (Pcell.weightedBlockAverage F)) X) =
      Pcell.weightedAverage
        (fun c => blockVecDot X (blockMatVecMul (blockReflect (F c)) X)) := by
  rw [blockReflect_weightedBlockAverage]
  exact blockVecDot_blockMatVecMul_weightedBlockAverage' Pcell
    (fun c => blockReflect (F c)) X

theorem sum_weightedAverage_two_terms_sub_const
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : κ → ℝ) (hw : ∑ c : κ, w c = 1)
    (f g : ι → κ → ℝ) (h : ι → ℝ) :
    ∑ α : ι,
        ((1 / 2 : ℝ) * (∑ c : κ, w c * f α c) +
          (1 / 2 : ℝ) * (∑ c : κ, w c * g α c) - h α) =
      ∑ c : κ,
        w c * ∑ α : ι,
          ((1 / 2 : ℝ) * f α c + (1 / 2 : ℝ) * g α c - h α) := by
  have hinner :
      ∀ α : ι,
        (1 / 2 : ℝ) * (∑ c : κ, w c * f α c) +
            (1 / 2 : ℝ) * (∑ c : κ, w c * g α c) - h α =
          ∑ c : κ,
            w c * ((1 / 2 : ℝ) * f α c + (1 / 2 : ℝ) * g α c - h α) := by
    intro α
    calc
      (1 / 2 : ℝ) * (∑ c : κ, w c * f α c) +
            (1 / 2 : ℝ) * (∑ c : κ, w c * g α c) - h α
          =
        (∑ c : κ, (1 / 2 : ℝ) * (w c * f α c)) +
            (∑ c : κ, (1 / 2 : ℝ) * (w c * g α c)) -
          (∑ c : κ, w c) * h α := by
            rw [Finset.mul_sum, Finset.mul_sum, hw]
            ring
      _ =
          ∑ c : κ,
            ((1 / 2 : ℝ) * (w c * f α c) +
              (1 / 2 : ℝ) * (w c * g α c) - w c * h α) := by
            symm
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul]
      _ =
          ∑ c : κ,
            w c * ((1 / 2 : ℝ) * f α c + (1 / 2 : ℝ) * g α c - h α) := by
            refine Finset.sum_congr rfl ?_
            intro c _hc
            ring
  calc
    ∑ α : ι,
        ((1 / 2 : ℝ) * (∑ c : κ, w c * f α c) +
          (1 / 2 : ℝ) * (∑ c : κ, w c * g α c) - h α)
        = ∑ α : ι, ∑ c : κ,
            w c * ((1 / 2 : ℝ) * f α c + (1 / 2 : ℝ) * g α c - h α) := by
          refine Finset.sum_congr rfl ?_
          intro α _hα
          exact hinner α
    _ = ∑ c : κ, ∑ α : ι,
          w c * ((1 / 2 : ℝ) * f α c + (1 / 2 : ℝ) * g α c - h α) := by
          rw [Finset.sum_comm]
    _ = ∑ c : κ,
        w c * ∑ α : ι,
          ((1 / 2 : ℝ) * f α c + (1 / 2 : ℝ) * g α c - h α) := by
          refine Finset.sum_congr rfl ?_
          intro c _hc
          rw [Finset.mul_sum]

theorem fullBlockJTraceBudgetWithNormalizers_weightedBlockAverage
    {d : ℕ} {U : Ch02.Domain d} (Pcell : Ch02.DomainPartition U)
    (S T : FullBlockMat d) (F : Pcell.Cell → BlockMat d) :
    fullBlockJTraceBudgetWithNormalizers S T (Pcell.weightedBlockAverage F) =
      Pcell.weightedAverage
        (fun c => fullBlockJTraceBudgetWithNormalizers S T (F c)) := by
  classical
  let : Fintype Pcell.Cell := Pcell.instFintype
  unfold fullBlockJTraceBudgetWithNormalizers
  simp_rw [blockVecDot_blockMatVecMul_weightedBlockAverage',
    blockVecDot_blockReflect_weightedBlockAverage']
  unfold Ch02.DomainPartition.weightedAverage
  exact sum_weightedAverage_two_terms_sub_const
    (w := Pcell.weight) Pcell.weight_sum_one
    (f := fun α c =>
      blockVecDot (fullBlockMatrixProbe S α)
        (blockMatVecMul (F c) (fullBlockMatrixProbe S α)))
    (g := fun α c =>
      blockVecDot (fullBlockMatrixProbe T α)
        (blockMatVecMul (blockReflect (F c)) (fullBlockMatrixProbe T α)))
    (h := fun α => blockVecDot (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α))

theorem fullBlockTrace_transpose_mul_mul_eq_sum_blockVecDot
    {d : ℕ} (S M : FullBlockMat d) :
    Ch02.fullBlockTrace (Matrix.transpose S * M * S) =
      ∑ α : BlockCoord d,
        blockVecDot (fullBlockMatrixProbe S α)
          (blockMatVecMul (ofFullBlockMat M) (fullBlockMatrixProbe S α)) := by
  classical
  have htranspose :
      ∀ x y : FullBlockVec d,
        dotProduct x (Matrix.mulVec (Matrix.transpose S) y) =
          dotProduct (Matrix.mulVec S x) y := by
    intro x y
    rw [Matrix.dotProduct_mulVec]
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      mul_comm]
  have hdiag :
      ∀ α : BlockCoord d,
        (Matrix.transpose S * M * S) α α =
          dotProduct (Matrix.mulVec S (Pi.single α 1))
            (Matrix.mulVec M (Matrix.mulVec S (Pi.single α 1))) := by
    intro α
    let e : FullBlockVec d := Pi.single α 1
    calc
      (Matrix.transpose S * M * S) α α
          = dotProduct e
              (Matrix.mulVec (Matrix.transpose S * M * S) e) := by
              simp [e]
      _ = dotProduct e
              (Matrix.mulVec (Matrix.transpose S)
                (Matrix.mulVec M (Matrix.mulVec S e))) := by
              rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = dotProduct (Matrix.mulVec S e)
              (Matrix.mulVec M (Matrix.mulVec S e)) := htranspose e _
  calc
    Ch02.fullBlockTrace (Matrix.transpose S * M * S)
        = Matrix.trace (Matrix.transpose S * M * S) := by
          simp [Ch02.fullBlockTrace, Matrix.trace]
    _ = ∑ α : BlockCoord d,
          dotProduct (Matrix.mulVec S (Pi.single α 1))
            (Matrix.mulVec M (Matrix.mulVec S (Pi.single α 1))) := by
          unfold Matrix.trace
          exact Finset.sum_congr rfl (fun α _hα => hdiag α)
    _ = ∑ α : BlockCoord d,
        blockVecDot (fullBlockMatrixProbe S α)
          (blockMatVecMul (ofFullBlockMat M) (fullBlockMatrixProbe S α)) := by
          refine Finset.sum_congr rfl ?_
          intro α _hα
          rw [← dotProduct_toFullBlockVec (fullBlockMatrixProbe S α)
            (blockMatVecMul (ofFullBlockMat M) (fullBlockMatrixProbe S α))]
          simp [fullBlockMatrixProbe, toFullBlockVec_blockMatVecMul]

theorem fullBlockTrace_transpose_blockSub_le_two_fullBlockJTraceBudgetWithNormalizers
    {d : ℕ} (S T : FullBlockMat d) {A B : BlockMat d}
    (hAB : BlockMatLoewnerLE A B)
    (hStarAB : BlockMatLoewnerLE (blockReflect A) (blockReflect B))
    (hParentBudget_nonneg : 0 ≤ fullBlockJTraceBudgetWithNormalizers S T A) :
    Ch02.fullBlockTrace
        (Matrix.transpose S * (toFullBlockMat B - toFullBlockMat A) * S) ≤
      2 * fullBlockJTraceBudgetWithNormalizers S T B := by
  classical
  have hx_nonneg :
      ∀ α : BlockCoord d,
        0 ≤
          blockVecDot (fullBlockMatrixProbe S α)
            (blockMatVecMul (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A))
              (fullBlockMatrixProbe S α)) := by
    intro α
    have h := hAB (fullBlockMatrixProbe S α)
    have hdiff :=
      blockVecDot_blockMatVecMul_ofFullBlockMat_sub B A (fullBlockMatrixProbe S α)
    rw [hdiff]
    nlinarith
  have hy_nonneg :
      ∀ α : BlockCoord d,
        0 ≤
          blockVecDot (fullBlockMatrixProbe T α)
            (blockMatVecMul
              (ofFullBlockMat
                (toFullBlockMat (blockReflect B) - toFullBlockMat (blockReflect A)))
              (fullBlockMatrixProbe T α)) := by
    intro α
    have h := hStarAB (fullBlockMatrixProbe T α)
    have hdiff :=
      blockVecDot_blockMatVecMul_ofFullBlockMat_sub
        (blockReflect B) (blockReflect A) (fullBlockMatrixProbe T α)
    rw [hdiff]
    nlinarith
  have htrace_eq :
      Ch02.fullBlockTrace
          (Matrix.transpose S * (toFullBlockMat B - toFullBlockMat A) * S) =
        ∑ α : BlockCoord d,
          blockVecDot (fullBlockMatrixProbe S α)
            (blockMatVecMul (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A))
              (fullBlockMatrixProbe S α)) :=
    fullBlockTrace_transpose_mul_mul_eq_sum_blockVecDot S
      (toFullBlockMat B - toFullBlockMat A)
  have hbudget_sub :
      fullBlockJTraceBudgetWithNormalizers S T B -
          fullBlockJTraceBudgetWithNormalizers S T A =
        ∑ α : BlockCoord d,
          ((1 / 2 : ℝ) *
              blockVecDot (fullBlockMatrixProbe S α)
                (blockMatVecMul
                  (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A))
                  (fullBlockMatrixProbe S α)) +
            (1 / 2 : ℝ) *
              blockVecDot (fullBlockMatrixProbe T α)
                (blockMatVecMul
                  (ofFullBlockMat
                    (toFullBlockMat (blockReflect B) - toFullBlockMat (blockReflect A)))
                  (fullBlockMatrixProbe T α))) := by
    unfold fullBlockJTraceBudgetWithNormalizers
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro α _hα
    rw [blockVecDot_blockMatVecMul_ofFullBlockMat_sub B A]
    rw [blockVecDot_blockMatVecMul_ofFullBlockMat_sub (blockReflect B) (blockReflect A)]
    ring
  have htrace_le_twice_sub :
      Ch02.fullBlockTrace
          (Matrix.transpose S * (toFullBlockMat B - toFullBlockMat A) * S) ≤
        2 * (fullBlockJTraceBudgetWithNormalizers S T B -
          fullBlockJTraceBudgetWithNormalizers S T A) := by
    rw [htrace_eq, hbudget_sub, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro α _hα
    have hx := hx_nonneg α
    have hy := hy_nonneg α
    ring_nf
    linarith
  nlinarith

theorem BlockMatLoewnerLE.blockReflect'
    {d : ℕ} {A B : BlockMat d} (hAB : BlockMatLoewnerLE A B) :
    BlockMatLoewnerLE (blockReflect A) (blockReflect B) := by
  intro X
  simpa using hAB (X.2, X.1)
end

end Section56
end Ch05
end Book
end Homogenization
