/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module

public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Block

/-! # Entry bounds for positive definite block matrices -/

@[expose] public section

namespace Homogenization.Book.Ch02

noncomputable section

theorem blockMatVecMul_sub
    {d : ℕ} (A : BlockMat d) (X Y : BlockVec d) :
    blockMatVecMul A (X - Y) = blockMatVecMul A X - blockMatVecMul A Y := by
  have hneg : blockMatVecMul A (-Y) = -blockMatVecMul A Y := by
    simpa using blockMatVecMul_smul A (-1) Y
  rw [sub_eq_add_neg, blockMatVecMul_add, hneg]
  rfl

theorem blockVecDot_sub_left
    {d : ℕ} (X Y Z : BlockVec d) :
    blockVecDot (X - Y) Z = blockVecDot X Z - blockVecDot Y Z := by
  have hneg : blockVecDot (-Y) Z = -blockVecDot Y Z := by
    simpa using blockVecDot_smul_left (-1) Y Z
  rw [sub_eq_add_neg, blockVecDot_add_left, hneg]
  rfl

theorem blockBasis_sub_pairing
    {d : ℕ} (A : BlockMat d) (α β : BlockCoord d) :
    blockVecDot (blockBasis α - blockBasis β)
        (blockMatVecMul A (blockBasis α - blockBasis β)) =
      blockMatEntry A α α - blockMatEntry A α β -
        blockMatEntry A β α + blockMatEntry A β β := by
  rw [blockMatVecMul_sub, blockVecDot_sub_left]
  rw [blockVecDot_sub_right]
  rw [blockVecDot_sub_right]
  rw [blockBasis_pairing, blockBasis_pairing, blockBasis_pairing, blockBasis_pairing]
  ring

theorem blockBasis_add_ne_zero
    {d : ℕ} {α β : BlockCoord d} (hαβ : α ≠ β) :
    blockBasis α + blockBasis β ≠ (0 : BlockVec d) := by
  intro hzero
  have hcoord := congrArg (fun X : BlockVec d => toFullBlockVec X α) hzero
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          have hij : i ≠ j := by
            intro h
            exact hαβ (by simp [h])
          simp [blockBasis, toFullBlockVec, Pi.single_eq_of_ne hij] at hcoord
      | inr j =>
          simp [blockBasis, toFullBlockVec] at hcoord
  | inr i =>
      cases β with
      | inl j =>
          simp [blockBasis, toFullBlockVec] at hcoord
      | inr j =>
          have hij : i ≠ j := by
            intro h
            exact hαβ (by simp [h])
          simp [blockBasis, toFullBlockVec, Pi.single_eq_of_ne hij] at hcoord

theorem blockBasis_sub_ne_zero
    {d : ℕ} {α β : BlockCoord d} (hαβ : α ≠ β) :
    blockBasis α - blockBasis β ≠ (0 : BlockVec d) := by
  intro hzero
  have hcoord := congrArg (fun X : BlockVec d => toFullBlockVec X α) hzero
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          have hij : i ≠ j := by
            intro h
            exact hαβ (by simp [h])
          simp [blockBasis, toFullBlockVec, Pi.single_eq_of_ne hij] at hcoord
      | inr j =>
          simp [blockBasis, toFullBlockVec] at hcoord
  | inr i =>
      cases β with
      | inl j =>
          simp [blockBasis, toFullBlockVec] at hcoord
      | inr j =>
          have hij : i ≠ j := by
            intro h
            exact hαβ (by simp [h])
          simp [blockBasis, toFullBlockVec, Pi.single_eq_of_ne hij] at hcoord

theorem abs_cross_blockMatEntry_le_diag_sum_of_blockPosDef
    {d : ℕ} {A : BlockMat d} (hSymm : IsSymmetricBlockMat A)
    (hPos : Ch02.BlockPosDef A) {α β : BlockCoord d} (hαβ : α ≠ β) :
    |blockMatEntry A α β| ≤
      (1 / 2 : ℝ) * (blockMatEntry A α α + blockMatEntry A β β) := by
  have hplus_pos :=
    hPos (blockBasis α + blockBasis β) (blockBasis_add_ne_zero hαβ)
  have hminus_pos :=
    hPos (blockBasis α - blockBasis β) (blockBasis_sub_ne_zero hαβ)
  have hplus :
      0 <
        blockMatEntry A α α + blockMatEntry A α β +
          blockMatEntry A β α + blockMatEntry A β β := by
    simpa [blockBasis_sum_pairing] using hplus_pos
  have hminus :
      0 <
        blockMatEntry A α α - blockMatEntry A α β -
          blockMatEntry A β α + blockMatEntry A β β := by
    simpa [blockBasis_sub_pairing] using hminus_pos
  have hsymm : blockMatEntry A β α = blockMatEntry A α β := (hSymm α β).symm
  rw [abs_le]
  constructor <;> nlinarith

end

end Homogenization.Book.Ch02
