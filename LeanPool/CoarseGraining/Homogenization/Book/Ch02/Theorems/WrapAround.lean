/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.BlockCoarseMatrix
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError.ResponseBounds

/-! # Wrap Around -/

namespace Homogenization
namespace Book
namespace Ch02

open scoped BigOperators

noncomputable section

/-!
# Deterministic wrap-around estimates

This file contains the Chapter 2 deterministic engine behind the wrap-around
argument: finite partition subadditivity for coarse block matrices, expressed
as a normalized trace defect controlled by the averaged special-coordinate
doubled-response `J` budget.
-/

/-- Full-block trace of a finite matrix. -/
noncomputable def fullBlockTrace {d : ℕ} (M : FullBlockMat d) : ℝ :=
  ∑ α : BlockCoord d, M α α

/-- A block Löwner comparison controls diagonal entries of the upper-left
block. -/
theorem blockMatLoewnerLE_upperLeft_apply {d : ℕ} {A B : BlockMat d}
    (h : BlockMatLoewnerLE A B) (i : Fin d) :
    A.upperLeft i i ≤ B.upperLeft i i := by
  have hquad := h (Pi.single i 1, 0)
  have hA :
      blockVecDot (Pi.single i 1, 0)
          (blockMatVecMul A (Pi.single i 1, 0)) = A.upperLeft i i := by
    simp [blockVecDot, blockMatVecMul, vecDot, matVecMul, Pi.single_apply]
  have hB :
      blockVecDot (Pi.single i 1, 0)
          (blockMatVecMul B (Pi.single i 1, 0)) = B.upperLeft i i := by
    simp [blockVecDot, blockMatVecMul, vecDot, matVecMul, Pi.single_apply]
  simpa [hA, hB] using hquad

/-- A block Löwner comparison controls diagonal entries of the lower-right
block. -/
theorem blockMatLoewnerLE_lowerRight_apply {d : ℕ} {A B : BlockMat d}
    (h : BlockMatLoewnerLE A B) (i : Fin d) :
    A.lowerRight i i ≤ B.lowerRight i i := by
  have hquad := h (0, Pi.single i 1)
  have hA :
      blockVecDot (0, Pi.single i 1)
          (blockMatVecMul A (0, Pi.single i 1)) = A.lowerRight i i := by
    simp [blockVecDot, blockMatVecMul, vecDot, matVecMul, Pi.single_apply]
  have hB :
      blockVecDot (0, Pi.single i 1)
          (blockMatVecMul B (0, Pi.single i 1)) = B.lowerRight i i := by
    simp [blockVecDot, blockMatVecMul, vecDot, matVecMul, Pi.single_apply]
  simpa [hA, hB] using hquad

/-- The diagonal block-J trace budget associated with the special coordinate
probes `(σ^{-1/2} e_i, σ^{1/2} e_i)`, written directly in terms of a block
matrix. -/
noncomputable def specialCoordinateBlockJTraceBudget {d : ℕ} (σ : ℝ)
    (A : BlockMat d) : ℝ :=
  ∑ i : Fin d,
    ((1 / 2 : ℝ) * (σ⁻¹ * A.upperLeft i i) +
      (1 / 2 : ℝ) * (σ * A.lowerRight i i) - 1)

theorem specialCoordinateBlockJTraceBudget_sub
    {d : ℕ} (σ : ℝ) (A B : BlockMat d) :
    specialCoordinateBlockJTraceBudget σ B -
        specialCoordinateBlockJTraceBudget σ A =
      ∑ i : Fin d,
        ((1 / 2 : ℝ) * (σ⁻¹ * (B.upperLeft i i - A.upperLeft i i)) +
          (1 / 2 : ℝ) * (σ * (B.lowerRight i i - A.lowerRight i i))) := by
  unfold specialCoordinateBlockJTraceBudget
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

/-- The normalized trace of a positive block additivity defect is controlled
by the special-coordinate trace budget of the upper matrix. -/
theorem normalizedBlockSubTrace_le_specialCoordinateBlockJTraceBudget
    {d : ℕ} {A B : BlockMat d} {σ : ℝ} (r : BlockCoord d → ℝ)
    (hAB : BlockMatLoewnerLE A B)
    (hrUpper : ∀ i : Fin d, r (Sum.inl i) * r (Sum.inl i) ≤ σ⁻¹)
    (hrLower : ∀ i : Fin d, r (Sum.inr i) * r (Sum.inr i) ≤ σ)
    (hParentBudget_nonneg : 0 ≤ specialCoordinateBlockJTraceBudget σ A) :
    fullBlockTrace
        (Matrix.diagonal r * (toFullBlockMat B - toFullBlockMat A) *
          Matrix.diagonal r) ≤
      2 * specialCoordinateBlockJTraceBudget σ B := by
  have hUL_nonneg : ∀ i : Fin d, 0 ≤ B.upperLeft i i - A.upperLeft i i := by
    intro i
    exact sub_nonneg.mpr (blockMatLoewnerLE_upperLeft_apply hAB i)
  have hLR_nonneg : ∀ i : Fin d, 0 ≤ B.lowerRight i i - A.lowerRight i i := by
    intro i
    exact sub_nonneg.mpr (blockMatLoewnerLE_lowerRight_apply hAB i)
  have htrace_le :
      fullBlockTrace
          (Matrix.diagonal r * (toFullBlockMat B - toFullBlockMat A) *
            Matrix.diagonal r) ≤
        ∑ i : Fin d,
          (σ⁻¹ * (B.upperLeft i i - A.upperLeft i i) +
            σ * (B.lowerRight i i - A.lowerRight i i)) := by
    unfold fullBlockTrace
    rw [Fintype.sum_sum_type]
    calc
      (∑ i : Fin d,
            (Matrix.diagonal r * (toFullBlockMat B - toFullBlockMat A) *
              Matrix.diagonal r) (Sum.inl i) (Sum.inl i)) +
          ∑ i : Fin d,
            (Matrix.diagonal r * (toFullBlockMat B - toFullBlockMat A) *
              Matrix.diagonal r) (Sum.inr i) (Sum.inr i)
          =
        ∑ i : Fin d,
            (r (Sum.inl i) * r (Sum.inl i)) *
              (B.upperLeft i i - A.upperLeft i i) +
          ∑ i : Fin d,
            (r (Sum.inr i) * r (Sum.inr i)) *
              (B.lowerRight i i - A.lowerRight i i) := by
          congr 1
          · refine Finset.sum_congr rfl ?_
            intro i _hi
            simp [Matrix.mul_apply, Matrix.diagonal, toFullBlockMat]
            ring
          · refine Finset.sum_congr rfl ?_
            intro i _hi
            simp [Matrix.mul_apply, Matrix.diagonal, toFullBlockMat]
            ring
      _ ≤
        ∑ i : Fin d, σ⁻¹ * (B.upperLeft i i - A.upperLeft i i) +
          ∑ i : Fin d, σ * (B.lowerRight i i - A.lowerRight i i) := by
          exact add_le_add
            (Finset.sum_le_sum fun i _hi =>
              mul_le_mul_of_nonneg_right (hrUpper i) (hUL_nonneg i))
            (Finset.sum_le_sum fun i _hi =>
              mul_le_mul_of_nonneg_right (hrLower i) (hLR_nonneg i))
      _ =
        ∑ i : Fin d,
          (σ⁻¹ * (B.upperLeft i i - A.upperLeft i i) +
            σ * (B.lowerRight i i - A.lowerRight i i)) := by
          rw [Finset.sum_add_distrib]
  have hbudget_sub := specialCoordinateBlockJTraceBudget_sub σ A B
  have htwice :
      ∑ i : Fin d,
          (σ⁻¹ * (B.upperLeft i i - A.upperLeft i i) +
            σ * (B.lowerRight i i - A.lowerRight i i)) =
        2 * (specialCoordinateBlockJTraceBudget σ B -
          specialCoordinateBlockJTraceBudget σ A) := by
    rw [hbudget_sub]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    ring
  calc
    fullBlockTrace
        (Matrix.diagonal r * (toFullBlockMat B - toFullBlockMat A) *
          Matrix.diagonal r)
        ≤ ∑ i : Fin d,
          (σ⁻¹ * (B.upperLeft i i - A.upperLeft i i) +
            σ * (B.lowerRight i i - A.lowerRight i i)) := htrace_le
    _ = 2 * (specialCoordinateBlockJTraceBudget σ B -
          specialCoordinateBlockJTraceBudget σ A) := htwice
    _ ≤ 2 * specialCoordinateBlockJTraceBudget σ B := by
        nlinarith

theorem sum_doubledResponseJ_coordinateScales_eq_specialCoordinateBlockJTraceBudget
    {d : ℕ} (U : Domain d) (a : CoeffOn U)
    {σ cp cq : ℝ} (hcp2 : cp * cp = σ⁻¹) (hcq2 : cq * cq = σ)
    (hcpq : cp * cq = 1) :
    (∑ i : Fin d,
      doubledResponseJ U a (cp • Pi.single i 1, 0)
        (cq • Pi.single i 1, 0)) =
      specialCoordinateBlockJTraceBudget σ (coarseBlockMatrix U a) := by
  classical
  unfold specialCoordinateBlockJTraceBudget
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [(blockCoarseMatrixTheory U a).doubled_response_splitting]
  rw [(blockCoarseMatrixTheory U a).starred_inverse_formula]
  simp [blockVecDot, blockMatVecMul, blockReflect, matVecMul_smul,
    vecDot_smul_left, vecDot_smul_right, matVecMul_single,
    vecDot_single_left, vecDot_single_right, matVecMul_zero,
    vecDot_zero_left, vecDot_zero_right]
  have hcpq' : cq * cp = 1 := by nlinarith
  have hcp2' : cp ^ (2 : ℕ) = σ⁻¹ := by nlinarith
  have hcq2' : cq ^ (2 : ℕ) = σ := by nlinarith
  ring_nf
  rw [hcp2', hcq2', hcpq]
  ring

/-- The special-coordinate block-J trace budget commutes with a finite
partition average. -/
theorem specialCoordinateBlockJTraceBudget_weightedBlockAverage
    {d : ℕ} {U : Domain d} (Pcell : DomainPartition U)
    (σ : ℝ) (F : Pcell.Cell → BlockMat d) :
    specialCoordinateBlockJTraceBudget σ (Pcell.weightedBlockAverage F) =
      Pcell.weightedAverage (fun c => specialCoordinateBlockJTraceBudget σ (F c)) := by
  classical
  let : Fintype Pcell.Cell := Pcell.instFintype
  unfold specialCoordinateBlockJTraceBudget DomainPartition.weightedBlockAverage
    DomainPartition.weightedMatAverage DomainPartition.weightedAverage
  simp only
  symm
  calc
    (∑ x, Pcell.weight x * ∑ i,
        (1 / 2 * (σ⁻¹ * (F x).upperLeft i i) +
            1 / 2 * (σ * (F x).lowerRight i i) - 1)) =
      ∑ x, ∑ i,
        Pcell.weight x *
          (1 / 2 * (σ⁻¹ * (F x).upperLeft i i) +
            1 / 2 * (σ * (F x).lowerRight i i) - 1) := by
        refine Finset.sum_congr rfl ?_
        intro x _hx
        rw [Finset.mul_sum]
    _ = ∑ i, ∑ x,
        Pcell.weight x *
          (1 / 2 * (σ⁻¹ * (F x).upperLeft i i) +
            1 / 2 * (σ * (F x).lowerRight i i) - 1) := by
        rw [Finset.sum_comm]
    _ = ∑ i,
        (1 / 2 * (σ⁻¹ * ∑ x, Pcell.weight x * (F x).upperLeft i i) +
          1 / 2 * (σ * ∑ x, Pcell.weight x * (F x).lowerRight i i) - 1) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        have hUL :
            (∑ x, 1 / 2 * (σ⁻¹ * (Pcell.weight x * (F x).upperLeft i i))) =
              1 / 2 * (σ⁻¹ * ∑ x, Pcell.weight x * (F x).upperLeft i i) := by
          calc
            (∑ x, 1 / 2 * (σ⁻¹ * (Pcell.weight x * (F x).upperLeft i i))) =
                ∑ x, (1 / 2 * σ⁻¹) * (Pcell.weight x * (F x).upperLeft i i) := by
                  refine Finset.sum_congr rfl ?_
                  intro x _hx
                  ring
            _ = (1 / 2 * σ⁻¹) * ∑ x, Pcell.weight x * (F x).upperLeft i i := by
                  rw [Finset.mul_sum]
            _ = 1 / 2 * (σ⁻¹ * ∑ x, Pcell.weight x * (F x).upperLeft i i) := by
                  ring
        have hLR :
            (∑ x, 1 / 2 * (σ * (Pcell.weight x * (F x).lowerRight i i))) =
              1 / 2 * (σ * ∑ x, Pcell.weight x * (F x).lowerRight i i) := by
          calc
            (∑ x, 1 / 2 * (σ * (Pcell.weight x * (F x).lowerRight i i))) =
                ∑ x, (1 / 2 * σ) * (Pcell.weight x * (F x).lowerRight i i) := by
                  refine Finset.sum_congr rfl ?_
                  intro x _hx
                  ring
            _ = (1 / 2 * σ) * ∑ x, Pcell.weight x * (F x).lowerRight i i := by
                  rw [Finset.mul_sum]
            _ = 1 / 2 * (σ * ∑ x, Pcell.weight x * (F x).lowerRight i i) := by
                  ring
        calc
          (∑ x, Pcell.weight x *
              (1 / 2 * (σ⁻¹ * (F x).upperLeft i i) +
                1 / 2 * (σ * (F x).lowerRight i i) - 1))
              =
            ∑ x,
              ((1 / 2 * (σ⁻¹ * (Pcell.weight x * (F x).upperLeft i i))) +
                (1 / 2 * (σ * (Pcell.weight x * (F x).lowerRight i i))) -
                Pcell.weight x) := by
              refine Finset.sum_congr rfl ?_
              intro x _hx
              ring
          _ =
            (∑ x, 1 / 2 * (σ⁻¹ * (Pcell.weight x * (F x).upperLeft i i))) +
              (∑ x, 1 / 2 * (σ * (Pcell.weight x * (F x).lowerRight i i))) -
              ∑ x, Pcell.weight x := by
              rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
          _ =
            1 / 2 * (σ⁻¹ * ∑ x, Pcell.weight x * (F x).upperLeft i i) +
              1 / 2 * (σ * ∑ x, Pcell.weight x * (F x).lowerRight i i) - 1 := by
              rw [hUL, hLR, Pcell.weight_sum_one]

/-- Weighted averages of symmetric block matrices remain symmetric. -/
theorem isSymmetricBlockMat_weightedBlockAverage
    {d : ℕ} {U : Domain d} (Pcell : DomainPartition U)
    (F : Pcell.Cell → BlockMat d)
    (hF : ∀ c : Pcell.Cell, IsSymmetricBlockMat (F c)) :
    IsSymmetricBlockMat (Pcell.weightedBlockAverage F) := by
  classical
  let : Fintype Pcell.Cell := Pcell.instFintype
  intro α β
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          simp [DomainPartition.weightedBlockAverage,
            DomainPartition.weightedMatAverage, DomainPartition.weightedAverage,
            blockMatEntry]
          refine Finset.sum_congr rfl ?_
          intro c _hc
          have h := hF c (Sum.inl j) (Sum.inl i)
          simp [blockMatEntry] at h
          rw [h]
      | inr j =>
          simp [DomainPartition.weightedBlockAverage,
            DomainPartition.weightedMatAverage, DomainPartition.weightedAverage,
            blockMatEntry]
          refine Finset.sum_congr rfl ?_
          intro c _hc
          have h := hF c (Sum.inr j) (Sum.inl i)
          simp [blockMatEntry] at h
          rw [h]
  | inr i =>
      cases β with
      | inl j =>
          simp [DomainPartition.weightedBlockAverage,
            DomainPartition.weightedMatAverage, DomainPartition.weightedAverage,
            blockMatEntry]
          refine Finset.sum_congr rfl ?_
          intro c _hc
          have h := hF c (Sum.inl j) (Sum.inr i)
          simp [blockMatEntry] at h
          rw [h]
      | inr j =>
          simp [DomainPartition.weightedBlockAverage,
            DomainPartition.weightedMatAverage, DomainPartition.weightedAverage,
            blockMatEntry]
          refine Finset.sum_congr rfl ?_
          intro c _hc
          have h := hF c (Sum.inr j) (Sum.inr i)
          simp [blockMatEntry] at h
          rw [h]

/-- Main deterministic wrap-around engine: the normalized trace defect between
a parent coarse block matrix and the weighted average of its children is
controlled by the averaged special-coordinate doubled-response budget. -/
theorem weightedBlockAverage_wrapAround_normalizedTrace_le_specialCoordinateDoubledResponseJ
    {d : ℕ} {U : Domain d} (a : CoeffOn U)
    (Pcell : DomainPartition U)
    (aCell : ∀ c : Pcell.Cell, CoeffOn (Pcell.cell c))
    (hcell : ∀ c : Pcell.Cell, CoeffOn.RestrictsTo a (aCell c))
    {σ cp cq : ℝ} (hcp2 : cp * cp = σ⁻¹) (hcq2 : cq * cq = σ)
    (hcpq : cp * cq = 1) (r : BlockCoord d → ℝ)
    (hrUpper : ∀ i : Fin d, r (Sum.inl i) * r (Sum.inl i) ≤ σ⁻¹)
    (hrLower : ∀ i : Fin d, r (Sum.inr i) * r (Sum.inr i) ≤ σ) :
    let A := coarseBlockMatrix U a
    let B := Pcell.weightedBlockAverage fun c =>
      coarseBlockMatrix (Pcell.cell c) (aCell c)
    let J := Pcell.weightedAverage fun c =>
      ∑ i : Fin d,
        doubledResponseJ (Pcell.cell c) (aCell c)
          (cp • Pi.single i 1, 0) (cq • Pi.single i 1, 0)
    fullBlockTrace
        (Matrix.diagonal r * (toFullBlockMat B - toFullBlockMat A) *
          Matrix.diagonal r) ≤
      2 * J := by
  classical
  let : Fintype Pcell.Cell := Pcell.instFintype
  intro A B J
  have hAB : BlockMatLoewnerLE A B := by
    dsimp [A, B]
    exact (blockCoarseMatrixTheory U a).block_matrix_subadditive Pcell aCell hcell
  have hParentBudget_nonneg : 0 ≤ specialCoordinateBlockJTraceBudget σ A := by
    dsimp [A]
    rw [← sum_doubledResponseJ_coordinateScales_eq_specialCoordinateBlockJTraceBudget
      (U := U) (a := a) hcp2 hcq2 hcpq]
    exact Finset.sum_nonneg fun i _hi =>
      doubledResponseJ_nonneg U a
        (cp • Pi.single i 1, 0) (cq • Pi.single i 1, 0)
  have hBudget_eq : specialCoordinateBlockJTraceBudget σ B = J := by
    dsimp [B, J]
    calc
      specialCoordinateBlockJTraceBudget σ
          (Pcell.weightedBlockAverage fun c =>
            coarseBlockMatrix (Pcell.cell c) (aCell c)) =
        Pcell.weightedAverage
          (fun c => specialCoordinateBlockJTraceBudget σ
            (coarseBlockMatrix (Pcell.cell c) (aCell c))) := by
          exact specialCoordinateBlockJTraceBudget_weightedBlockAverage Pcell σ
            (fun c => coarseBlockMatrix (Pcell.cell c) (aCell c))
      _ = Pcell.weightedAverage fun c =>
          ∑ i : Fin d,
            doubledResponseJ (Pcell.cell c) (aCell c)
              (cp • Pi.single i 1, 0) (cq • Pi.single i 1, 0) := by
          unfold DomainPartition.weightedAverage
          refine Finset.sum_congr rfl ?_
          intro c _hc
          change
            Pcell.weight c *
                specialCoordinateBlockJTraceBudget σ
                  (coarseBlockMatrix (Pcell.cell c) (aCell c)) =
              Pcell.weight c *
                (∑ i : Fin d,
                  doubledResponseJ (Pcell.cell c) (aCell c)
                    (cp • Pi.single i 1, 0) (cq • Pi.single i 1, 0))
          rw [← sum_doubledResponseJ_coordinateScales_eq_specialCoordinateBlockJTraceBudget
            (U := Pcell.cell c) (a := aCell c) hcp2 hcq2 hcpq]
  have htrace :=
    normalizedBlockSubTrace_le_specialCoordinateBlockJTraceBudget
      (A := A) (B := B) (σ := σ) r hAB hrUpper hrLower hParentBudget_nonneg
  simpa [hBudget_eq] using htrace

end

end Ch02
end Book
end Homogenization
