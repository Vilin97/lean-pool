/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.PartitionAverage

/-! # Quadratic Probe Bounds -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace VarianceBoundGoodScale

open MeasureTheory
open scoped BigOperators

noncomputable section

/-!
# Pointwise bounds for normalized quadratic probes

This file supplies the remaining Section 5.4-local bridge from the normalized
quadratic probes used in the finite-dimensional upgrade to the unit-scale
coarse-grained ellipticity factors controlled by `(P4)`.
-/

/-- Unit-scale sum of the two coarse-grained ellipticity observables appearing
in `(P4)`. -/
noncomputable def unitScaleEllipticityFactorSum
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (a : RegCoeffField d) : ℝ :=
  Ch04.LambdaSqCoeffField (originCube d 0) hP4.sUpper (.finite 1) a +
    (Ch04.lambdaSqCoeffField (originCube d 0) hP4.sLower (.finite 1) a)⁻¹

theorem unitScaleEllipticityFactorSum_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (a : RegCoeffField d) :
    0 ≤ unitScaleEllipticityFactorSum hP4 a := by
  unfold unitScaleEllipticityFactorSum
  exact add_nonneg
    (Ch04.LambdaSqCoeffField_finite_nonneg (originCube d 0) a
      hP4.sUpper_pos (by norm_num : (1 : ℝ) ≤ 1))
    (inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d 0) a
        hP4.sLower_pos (by norm_num : (1 : ℝ) ≤ 1)))

private theorem blockMatVecMul_sub'
    {d : ℕ} (A : BlockMat d) (X Y : BlockVec d) :
    blockMatVecMul A (X - Y) = blockMatVecMul A X - blockMatVecMul A Y := by
  have hneg : blockMatVecMul A (-Y) = -blockMatVecMul A Y := by
    simpa using blockMatVecMul_smul A (-1) Y
  rw [sub_eq_add_neg, blockMatVecMul_add, hneg]
  rfl

private theorem blockVecDot_sub_left'
    {d : ℕ} (X Y Z : BlockVec d) :
    blockVecDot (X - Y) Z = blockVecDot X Z - blockVecDot Y Z := by
  have hneg : blockVecDot (-Y) Z = -blockVecDot Y Z := by
    simpa using blockVecDot_smul_left (-1) Y Z
  rw [sub_eq_add_neg, blockVecDot_add_left, hneg]
  rfl

private theorem blockBasis_sub_pairing'
    {d : ℕ} (A : BlockMat d) (α β : BlockCoord d) :
    blockVecDot (blockBasis α - blockBasis β)
        (blockMatVecMul A (blockBasis α - blockBasis β)) =
      blockMatEntry A α α - blockMatEntry A α β -
        blockMatEntry A β α + blockMatEntry A β β := by
  rw [blockMatVecMul_sub', blockVecDot_sub_left']
  rw [blockVecDot_sub_right]
  rw [blockVecDot_sub_right]
  rw [blockBasis_pairing, blockBasis_pairing, blockBasis_pairing, blockBasis_pairing]
  ring

private theorem blockBasis_add_ne_zero'
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

private theorem blockBasis_sub_ne_zero'
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

private theorem abs_cross_blockMatEntry_le_diag_sum_of_blockPosDef'
    {d : ℕ} {A : BlockMat d} (hSymm : IsSymmetricBlockMat A)
    (hPos : Ch02.BlockPosDef A) {α β : BlockCoord d} (hαβ : α ≠ β) :
    |blockMatEntry A α β| ≤
      (1 / 2 : ℝ) * (blockMatEntry A α α + blockMatEntry A β β) := by
  have hplus_pos :=
    hPos (blockBasis α + blockBasis β) (blockBasis_add_ne_zero' hαβ)
  have hminus_pos :=
    hPos (blockBasis α - blockBasis β) (blockBasis_sub_ne_zero' hαβ)
  have hplus :
      0 <
        blockMatEntry A α α + blockMatEntry A α β +
          blockMatEntry A β α + blockMatEntry A β β := by
    simpa [blockBasis_sum_pairing] using hplus_pos
  have hminus :
      0 <
        blockMatEntry A α α - blockMatEntry A α β -
          blockMatEntry A β α + blockMatEntry A β β := by
    simpa [blockBasis_sub_pairing'] using hminus_pos
  have hsymm : blockMatEntry A β α = blockMatEntry A α β := (hSymm α β).symm
  rw [abs_le]
  constructor <;> nlinarith

/-- Entrywise domination of the unit coarse block matrix by the two unit-scale
coarse-grained ellipticity factors from `(P4)`. -/
theorem blockMatEntry_abs_le_unitScaleEllipticityFactorSum_origin_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (α β : BlockCoord d) :
    (fun a : RegCoeffField d =>
        |blockMatEntry (coarseBlockMatrix (cubeSet (originCube d 0)) a) α β|)
      ≤ᵐ[P] fun a => unitScaleEllipticityFactorSum hP4 a := by
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  let Q : TriadicCube d := originCube d 0
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  have hEq :
      coarseBlockMatrix (cubeSet Q) a.toFun =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q) := by
    simpa [F] using
      Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha Q
  have hSymm : IsSymmetricBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) := by
    rw [hEq]
    exact Ch02.isSymmetricBlockMat_coarseBlockMatrix
      (Ch02.cubeDomain Q) (F.coeffOn Q)
  have hPos : Ch02.BlockPosDef (coarseBlockMatrix (cubeSet Q) a.toFun) := by
    rw [hEq]
    exact
      (Ch02.blockCoarseMatrixTheory (Ch02.cubeDomain Q)
        (F.coeffOn Q)).block_matrix_posDef
  have hUpperEntry : ∀ i j : Fin d,
      |(coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft i j| ≤
        Ch04.LambdaSqCoeffField Q hP4.sUpper (.finite 1) a := by
    intro i j
    calc
      |(coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft i j|
          = |(Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q)).upperLeft i j| := by
            rw [hEq]
      _ ≤ Ch02.coarseBMatrixNorm Q F := by
            simpa [Ch02.coarseBMatrixNorm, Ch02.matrixNorm_eq_matrixOperatorNorm] using
              Ch02.abs_entry_le_matrixOperatorNorm
                ((Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q)).upperLeft) i j
      _ ≤ Ch02.LambdaSq Q hP4.sUpper (.finite 1) F :=
            Ch02.oneCube_b_le_LambdaSq_finite Q F hP4.sUpper_pos
              (by norm_num : (1 : ℝ) ≤ 1)
      _ = Ch04.LambdaSqCoeffField Q hP4.sUpper (.finite 1) a := by
          simp [Ch04.LambdaSqCoeffField, ha, F]
  have hLowerEntry : ∀ i j : Fin d,
      |(coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight i j| ≤
        (Ch04.lambdaSqCoeffField Q hP4.sLower (.finite 1) a)⁻¹ := by
    intro i j
    calc
      |(coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight i j|
          = |(Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q)).lowerRight i j| := by
            rw [hEq]
      _ ≤ Ch02.coarseSigmaStarInvMatrixNorm Q F := by
            simpa [Ch02.coarseSigmaStarInvMatrixNorm, Ch02.matrixNorm_eq_matrixOperatorNorm] using
              Ch02.abs_entry_le_matrixOperatorNorm
                ((Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q)).lowerRight) i j
      _ ≤ (Ch02.lambdaSq Q hP4.sLower (.finite 1) F)⁻¹ :=
            Ch02.oneCube_sigmaStarInv_le_lambdaSq_finite_inv Q F hP4.sLower_pos
              (by norm_num : (1 : ℝ) ≤ 1)
      _ = (Ch04.lambdaSqCoeffField Q hP4.sLower (.finite 1) a)⁻¹ := by
          simp [Ch04.lambdaSqCoeffField, ha, F]
  have hX_nonneg :
      0 ≤ Ch04.LambdaSqCoeffField Q hP4.sUpper (.finite 1) a :=
    Ch04.LambdaSqCoeffField_finite_nonneg Q a hP4.sUpper_pos
      (by norm_num : (1 : ℝ) ≤ 1)
  have hY_nonneg :
      0 ≤ (Ch04.lambdaSqCoeffField Q hP4.sLower (.finite 1) a)⁻¹ :=
    inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg Q a hP4.sLower_pos
        (by norm_num : (1 : ℝ) ≤ 1))
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          exact (hUpperEntry i j).trans (by
            unfold unitScaleEllipticityFactorSum Q
            linarith)
      | inr j =>
          have hcross :
              |blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) (Sum.inl i) (Sum.inr j)| ≤
                (1 / 2 : ℝ) *
                  (blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) (Sum.inl i) (Sum.inl i) +
                    blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) (Sum.inr j) (Sum.inr j)) :=
            abs_cross_blockMatEntry_le_diag_sum_of_blockPosDef' hSymm hPos
              (by intro h; cases h)
          have hUL :
              blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) (Sum.inl i) (Sum.inl i) ≤
                Ch04.LambdaSqCoeffField Q hP4.sUpper (.finite 1) a := by
            exact (le_abs_self _).trans (by simpa [blockMatEntry] using hUpperEntry i i)
          have hLR :
              blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) (Sum.inr j) (Sum.inr j) ≤
                (Ch04.lambdaSqCoeffField Q hP4.sLower (.finite 1) a)⁻¹ := by
            exact (le_abs_self _).trans (by simpa [blockMatEntry] using hLowerEntry j j)
          have htarget :
              |blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) (Sum.inl i) (Sum.inr j)| ≤
                Ch04.LambdaSqCoeffField Q hP4.sUpper (.finite 1) a +
                  (Ch04.lambdaSqCoeffField Q hP4.sLower (.finite 1) a)⁻¹ := by
            linarith
          simpa [Q, unitScaleEllipticityFactorSum] using htarget
  | inr i =>
      cases β with
      | inl j =>
          have hcross :
              |blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) (Sum.inr i) (Sum.inl j)| ≤
                (1 / 2 : ℝ) *
                  (blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) (Sum.inr i) (Sum.inr i) +
                    blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) (Sum.inl j) (Sum.inl j)) :=
            abs_cross_blockMatEntry_le_diag_sum_of_blockPosDef' hSymm hPos
              (by intro h; cases h)
          have hLR :
              blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) (Sum.inr i) (Sum.inr i) ≤
                (Ch04.lambdaSqCoeffField Q hP4.sLower (.finite 1) a)⁻¹ := by
            exact (le_abs_self _).trans (by simpa [blockMatEntry] using hLowerEntry i i)
          have hUL :
              blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) (Sum.inl j) (Sum.inl j) ≤
                Ch04.LambdaSqCoeffField Q hP4.sUpper (.finite 1) a := by
            exact (le_abs_self _).trans (by simpa [blockMatEntry] using hUpperEntry j j)
          have htarget :
              |blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) (Sum.inr i) (Sum.inl j)| ≤
                Ch04.LambdaSqCoeffField Q hP4.sUpper (.finite 1) a +
                  (Ch04.lambdaSqCoeffField Q hP4.sLower (.finite 1) a)⁻¹ := by
            linarith
          simpa [Q, unitScaleEllipticityFactorSum] using htarget
      | inr j =>
          exact (hLowerEntry i j).trans (by
            unfold unitScaleEllipticityFactorSum Q
            linarith)

theorem isSymm_diagonal_mul_toFullBlockMat_mul_diagonal
    {d : ℕ} (r : BlockCoord d → ℝ) {A : BlockMat d}
    (hA : IsSymmetricBlockMat A) :
    (Matrix.diagonal r * toFullBlockMat A * Matrix.diagonal r).IsSymm := by
  have hM : (toFullBlockMat A).IsSymm := by
    simpa using isSymm_toFullBlockMat_of_isSymmetricBlockMat hA
  rw [Matrix.IsSymm]
  ext α β
  simp [Matrix.transpose_apply, Matrix.mul_apply, Matrix.diagonal]
  have h := hM.apply α β
  rw [h]
  ring

theorem fullBlockQuadratic_diagonal_coordinateProbe
    {d : ℕ} (r : BlockCoord d → ℝ) (A : BlockMat d)
    (α : BlockCoord d) :
    fullBlockQuadratic (Matrix.diagonal r * toFullBlockMat A * Matrix.diagonal r)
        (fullBlockCoordinateProbe α) =
      r α * blockMatEntry A α α * r α := by
  classical
  rw [fullBlockQuadratic_coordinateProbe]
  simp [Matrix.mul_apply, Matrix.diagonal, toFullBlockMat, blockMatEntry]

theorem fullBlockQuadratic_diagonal_plusProbe_of_ne
    {d : ℕ} (r : BlockCoord d → ℝ) {A : BlockMat d}
    (hA : IsSymmetricBlockMat A) {α β : BlockCoord d} (hαβ : α ≠ β) :
    fullBlockQuadratic (Matrix.diagonal r * toFullBlockMat A * Matrix.diagonal r)
        (fullBlockPlusProbe α β) =
      r α * blockMatEntry A α α * r α +
        2 * (r α * blockMatEntry A α β * r β) +
        r β * blockMatEntry A β β * r β := by
  classical
  have hDMD := isSymm_diagonal_mul_toFullBlockMat_mul_diagonal r hA
  rw [fullBlockQuadratic_plusProbe_of_ne hDMD hαβ]
  simp [Matrix.mul_apply, Matrix.diagonal, toFullBlockMat, blockMatEntry]

theorem fullBlockQuadratic_diagonal_minusProbe_of_ne
    {d : ℕ} (r : BlockCoord d → ℝ) {A : BlockMat d}
    (hA : IsSymmetricBlockMat A) {α β : BlockCoord d} (hαβ : α ≠ β) :
    fullBlockQuadratic (Matrix.diagonal r * toFullBlockMat A * Matrix.diagonal r)
        (fullBlockMinusProbe α β) =
      r α * blockMatEntry A α α * r α -
        2 * (r α * blockMatEntry A α β * r β) +
        r β * blockMatEntry A β β * r β := by
  classical
  have hDMD := isSymm_diagonal_mul_toFullBlockMat_mul_diagonal r hA
  rw [fullBlockQuadratic_minusProbe_of_ne hDMD hαβ]
  simp [Matrix.mul_apply, Matrix.diagonal, toFullBlockMat, blockMatEntry]

/-- Coefficient in the unit-scale factor bound for a normalized coordinate
probe. -/
noncomputable def coordinateProbeFactor
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (α : BlockCoord d) : ℝ :=
  let b := hP.barSigmaAtScale hStruct center
  let c := hP.barSigmaStarAtScale hStruct center
  let r := Ch04.scalarFullBlockInvSqrtDiag (d := d) b c
  |r α| * |r α|

theorem coordinateProbeFactor_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (α : BlockCoord d) :
    0 ≤ coordinateProbeFactor hP hStruct center α := by
  unfold coordinateProbeFactor
  exact mul_nonneg (abs_nonneg _) (abs_nonneg _)

/-- Coefficient in the unit-scale factor bound for a normalized plus/minus
pair probe. -/
noncomputable def pairProbeFactor
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (α β : BlockCoord d) : ℝ :=
  let b := hP.barSigmaAtScale hStruct center
  let c := hP.barSigmaStarAtScale hStruct center
  let r := Ch04.scalarFullBlockInvSqrtDiag (d := d) b c
  |r α| * |r α| + 2 * (|r α| * |r β|) + |r β| * |r β|

theorem pairProbeFactor_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (α β : BlockCoord d) :
    0 ≤ pairProbeFactor hP hStruct center α β := by
  unfold pairProbeFactor
  nlinarith [abs_nonneg (Ch04.scalarFullBlockInvSqrtDiag
    (hP.barSigmaAtScale hStruct center) (hP.barSigmaStarAtScale hStruct center) α),
    abs_nonneg (Ch04.scalarFullBlockInvSqrtDiag
      (hP.barSigmaAtScale hStruct center) (hP.barSigmaStarAtScale hStruct center) β)]

theorem abs_mul_entry_mul_le_factor
    {F x y e : ℝ} (he : |e| ≤ F) :
    |x * e * y| ≤ |x| * |y| * F := by
  calc
    |x * e * y| = |x| * |y| * |e| := by
      rw [abs_mul, abs_mul]
      ring
    _ ≤ |x| * |y| * F := by
      exact mul_le_mul_of_nonneg_left he
        (mul_nonneg (abs_nonneg x) (abs_nonneg y))

/-- The normalized coordinate quadratic probe is pointwise dominated, a.s.,
by the `(P4)` unit-scale ellipticity factor sum. -/
theorem fullBlockNormalizedQuadraticObservable_coordinateProbe_abs_le_factorSum_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (center : ℤ) (α : BlockCoord d) :
    (fun a : RegCoeffField d =>
        |fullBlockNormalizedQuadraticObservable hP hStruct center
          (fullBlockCoordinateProbe α) (cubeSet (originCube d 0)) a|)
      ≤ᵐ[P]
        fun a =>
          coordinateProbeFactor hP hStruct center α *
            unitScaleEllipticityFactorSum hP4 a := by
  filter_upwards
    [blockMatEntry_abs_le_unitScaleEllipticityFactorSum_origin_ae
      hP hP4 α α] with a hentry
  let b := hP.barSigmaAtScale hStruct center
  let c := hP.barSigmaStarAtScale hStruct center
  let r := Ch04.scalarFullBlockInvSqrtDiag (d := d) b c
  have hF_nonneg := unitScaleEllipticityFactorSum_nonneg hP4 a
  have hquad :
      fullBlockNormalizedQuadraticObservable hP hStruct center
          (fullBlockCoordinateProbe α) (cubeSet (originCube d 0)) a =
        r α *
          blockMatEntry (coarseBlockMatrix (cubeSet (originCube d 0)) a) α α *
          r α := by
    simpa [fullBlockNormalizedQuadraticObservable, b, c, r] using
      fullBlockQuadratic_diagonal_coordinateProbe r
        (coarseBlockMatrix (cubeSet (originCube d 0)) a) α
  calc
    |fullBlockNormalizedQuadraticObservable hP hStruct center
        (fullBlockCoordinateProbe α) (cubeSet (originCube d 0)) a|
        = |r α *
            blockMatEntry (coarseBlockMatrix (cubeSet (originCube d 0)) a) α α *
            r α| := by rw [hquad]
    _ ≤ |r α| * |r α| * unitScaleEllipticityFactorSum hP4 a :=
      abs_mul_entry_mul_le_factor hentry
    _ = coordinateProbeFactor hP hStruct center α *
        unitScaleEllipticityFactorSum hP4 a := by
      simp [coordinateProbeFactor, b, c, r]

private theorem fullBlockNormalizedQuadraticObservable_pairProbe_abs_le_factorSum_ae_aux
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (center : ℤ) {α β : BlockCoord d} (_hαβ : α ≠ β)
    (probe : FullBlockVec d) (s : ℝ) (hs : |s| = 2)
    (hexpand :
      ∀ (r : BlockCoord d → ℝ) {A : BlockMat d},
        IsSymmetricBlockMat A →
        fullBlockQuadratic (Matrix.diagonal r * toFullBlockMat A * Matrix.diagonal r)
            probe =
          r α * blockMatEntry A α α * r α +
            s * (r α * blockMatEntry A α β * r β) +
            r β * blockMatEntry A β β * r β) :
    (fun a : RegCoeffField d =>
        |fullBlockNormalizedQuadraticObservable hP hStruct center
          probe (cubeSet (originCube d 0)) a|)
      ≤ᵐ[P]
        fun a =>
          pairProbeFactor hP hStruct center α β *
            unitScaleEllipticityFactorSum hP4 a := by
  filter_upwards
    [hP.ae_locallyUniformlyEllipticField,
      blockMatEntry_abs_le_unitScaleEllipticityFactorSum_origin_ae hP hP4 α α,
      blockMatEntry_abs_le_unitScaleEllipticityFactorSum_origin_ae hP hP4 α β,
      blockMatEntry_abs_le_unitScaleEllipticityFactorSum_origin_ae hP hP4 β β]
    with a ha hdiagα hoff hdiagβ
  let Q : TriadicCube d := originCube d 0
  let b := hP.barSigmaAtScale hStruct center
  let c := hP.barSigmaStarAtScale hStruct center
  let r := Ch04.scalarFullBlockInvSqrtDiag (d := d) b c
  let Fsum := unitScaleEllipticityFactorSum hP4 a
  let A := coarseBlockMatrix (cubeSet Q) a.toFun
  let Tα := r α * blockMatEntry A α α * r α
  let Tβ := r β * blockMatEntry A β β * r β
  let Tαβ := r α * blockMatEntry A α β * r β
  have hEq :
      A = Ch02.coarseBlockMatrix (Ch02.cubeDomain Q)
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) := by
    simpa [A, Q] using
      Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha Q
  have hSymm : IsSymmetricBlockMat A := by
    rw [hEq]
    exact Ch02.isSymmetricBlockMat_coarseBlockMatrix
      (Ch02.cubeDomain Q)
      ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
  have hF_nonneg : 0 ≤ Fsum := by
    simpa [Fsum] using unitScaleEllipticityFactorSum_nonneg hP4 a
  have hTα : |Tα| ≤ |r α| * |r α| * Fsum := by
    simpa [Tα, A, Fsum, Q] using
      abs_mul_entry_mul_le_factor
        (x := r α) (y := r α)
        (e := blockMatEntry (coarseBlockMatrix (cubeSet (originCube d 0)) a) α α)
        hdiagα
  have hTβ : |Tβ| ≤ |r β| * |r β| * Fsum := by
    simpa [Tβ, A, Fsum, Q] using
      abs_mul_entry_mul_le_factor
        (x := r β) (y := r β)
        (e := blockMatEntry (coarseBlockMatrix (cubeSet (originCube d 0)) a) β β)
        hdiagβ
  have hTαβ : |Tαβ| ≤ |r α| * |r β| * Fsum := by
    simpa [Tαβ, A, Fsum, Q] using
      abs_mul_entry_mul_le_factor
        (x := r α) (y := r β)
        (e := blockMatEntry (coarseBlockMatrix (cubeSet (originCube d 0)) a) α β)
        hoff
  have hquad :
      fullBlockNormalizedQuadraticObservable hP hStruct center
          probe (cubeSet Q) a =
        Tα + s * Tαβ + Tβ := by
    simpa [fullBlockNormalizedQuadraticObservable, b, c, r, A, Tα, Tαβ, Tβ] using
      hexpand r hSymm
  have h_abs :
      |Tα + s * Tαβ + Tβ| ≤
        (|r α| * |r α| + 2 * (|r α| * |r β|) + |r β| * |r β|) * Fsum := by
    calc
      |Tα + s * Tαβ + Tβ|
          ≤ |Tα| + |2 * Tαβ| + |Tβ| := by
            simpa [hs] using abs_add_three Tα (s * Tαβ) Tβ
      _ ≤ |r α| * |r α| * Fsum +
            2 * (|r α| * |r β| * Fsum) +
            |r β| * |r β| * Fsum := by
          have htwo : |2 * Tαβ| = 2 * |Tαβ| := by simp
          rw [htwo]
          nlinarith [hTα, hTβ, hTαβ]
      _ = (|r α| * |r α| + 2 * (|r α| * |r β|) +
            |r β| * |r β|) * Fsum := by ring
  calc
    |fullBlockNormalizedQuadraticObservable hP hStruct center
        probe (cubeSet (originCube d 0)) a|
        = |Tα + s * Tαβ + Tβ| := by
          simpa [Q] using congrArg abs hquad
    _ ≤ (|r α| * |r α| + 2 * (|r α| * |r β|) +
            |r β| * |r β|) * Fsum := h_abs
    _ = pairProbeFactor hP hStruct center α β *
          unitScaleEllipticityFactorSum hP4 a := by
          simp [pairProbeFactor, b, c, r, Fsum]

/-- The normalized plus-pair quadratic probe is pointwise dominated, a.s.,
by the `(P4)` unit-scale ellipticity factor sum. -/
theorem fullBlockNormalizedQuadraticObservable_plusProbe_abs_le_factorSum_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (center : ℤ) {α β : BlockCoord d} (hαβ : α ≠ β) :
    (fun a : RegCoeffField d =>
        |fullBlockNormalizedQuadraticObservable hP hStruct center
          (fullBlockPlusProbe α β) (cubeSet (originCube d 0)) a|)
      ≤ᵐ[P]
        fun a =>
          pairProbeFactor hP hStruct center α β *
            unitScaleEllipticityFactorSum hP4 a :=
  fullBlockNormalizedQuadraticObservable_pairProbe_abs_le_factorSum_ae_aux
    hP hStruct hP4 center hαβ (fullBlockPlusProbe α β) 2 (by norm_num)
    (fun r A hA => fullBlockQuadratic_diagonal_plusProbe_of_ne r hA hαβ)

/-- The normalized minus-pair quadratic probe is pointwise dominated, a.s.,
by the `(P4)` unit-scale ellipticity factor sum. -/
theorem fullBlockNormalizedQuadraticObservable_minusProbe_abs_le_factorSum_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (center : ℤ) {α β : BlockCoord d} (hαβ : α ≠ β) :
    (fun a : RegCoeffField d =>
        |fullBlockNormalizedQuadraticObservable hP hStruct center
          (fullBlockMinusProbe α β) (cubeSet (originCube d 0)) a|)
      ≤ᵐ[P]
        fun a =>
          pairProbeFactor hP hStruct center α β *
            unitScaleEllipticityFactorSum hP4 a := by
  refine
    fullBlockNormalizedQuadraticObservable_pairProbe_abs_le_factorSum_ae_aux
      hP hStruct hP4 center hαβ (fullBlockMinusProbe α β) (-2) (by norm_num) ?_
  intro r A hA
  simpa [sub_eq_add_neg] using
    fullBlockQuadratic_diagonal_minusProbe_of_ne r hA hαβ

private theorem fullBlockNormalizedQuadraticObservable_origin_regular
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (q : FullBlockVec d) :
    AEMeasurable
      (fun a : RegCoeffField d =>
        fullBlockNormalizedQuadraticObservable hP hStruct center q
          (cubeSet (originCube d 0)) a) P := by
  rcases exists_isRestrictionLocalRandomVariable_ae_eq_fullBlockNormalizedQuadraticObservable_cubeSet
      hP hStruct center q (originCube d 0) with ⟨Y, hY_local, hY_eq⟩
  exact (hP.aemeasurable_of_isLocalRandomVariable hY_local).congr hY_eq.symm

private theorem centeredOriginMomentRoot_le_factorSum_of_probe_abs_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {center : ℤ} {q : FullBlockVec d} {C : ℝ} (hC : 0 ≤ C)
    (hbound :
      (fun a : RegCoeffField d =>
          |fullBlockNormalizedQuadraticObservable hP hStruct center q
            (cubeSet (originCube d 0)) a|)
        ≤ᵐ[P]
          fun a => C * unitScaleEllipticityFactorSum hP4 a) :
    Integrable
        (fun a =>
          |Ch04.restrictionCenteredOriginObservable P 0
            (fullBlockNormalizedQuadraticObservableR hP hStruct center q) a| ^
              hP4.xi) P ∧
      Ch04.annealedMomentRoot P hP4.xi
          (fun a =>
            |Ch04.restrictionCenteredOriginObservable P 0
              (fullBlockNormalizedQuadraticObservableR hP hStruct center q) a|)
        ≤
          2 * C *
            (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
              Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) := by
  let X : RegCoeffField d → ℝ :=
    fun a =>
      fullBlockNormalizedQuadraticObservable hP hStruct center q
        (cubeSet (originCube d 0)) a
  have hX_meas : AEMeasurable X P := by
    simpa [X] using
      fullBlockNormalizedQuadraticObservable_origin_regular
        hP hStruct center q
  have hbridge :=
    section54_centeredOrigin_momentRoot_le_factor_sum_of_abs_le
      hP hStruct hP4 hC (X := X) hX_meas
      (by simpa [X, unitScaleEllipticityFactorSum] using hbound)
  simpa [X, Ch04.restrictionCenteredOriginObservable] using! hbridge

/-- Centered origin moment input for normalized coordinate probes. -/
theorem coordinateProbe_centeredOrigin_momentRoot_le_factorSum
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (center : ℤ) (α : BlockCoord d) :
    Integrable
        (fun a =>
          |Ch04.restrictionCenteredOriginObservable P 0
            (fullBlockNormalizedQuadraticObservableR hP hStruct center
              (fullBlockCoordinateProbe α)) a| ^ hP4.xi) P ∧
      Ch04.annealedMomentRoot P hP4.xi
          (fun a =>
            |Ch04.restrictionCenteredOriginObservable P 0
              (fullBlockNormalizedQuadraticObservableR hP hStruct center
                (fullBlockCoordinateProbe α)) a|)
        ≤
          2 * coordinateProbeFactor hP hStruct center α *
            (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
              Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) :=
  centeredOriginMomentRoot_le_factorSum_of_probe_abs_le
    hP hStruct hP4
    (coordinateProbeFactor_nonneg hP hStruct center α)
    (fullBlockNormalizedQuadraticObservable_coordinateProbe_abs_le_factorSum_ae
      hP hStruct hP4 center α)

/-- Centered origin moment input for normalized plus-pair probes. -/
theorem plusProbe_centeredOrigin_momentRoot_le_factorSum
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (center : ℤ) {α β : BlockCoord d} (hαβ : α ≠ β) :
    Integrable
        (fun a =>
          |Ch04.restrictionCenteredOriginObservable P 0
            (fullBlockNormalizedQuadraticObservableR hP hStruct center
              (fullBlockPlusProbe α β)) a| ^ hP4.xi) P ∧
      Ch04.annealedMomentRoot P hP4.xi
          (fun a =>
            |Ch04.restrictionCenteredOriginObservable P 0
              (fullBlockNormalizedQuadraticObservableR hP hStruct center
                (fullBlockPlusProbe α β)) a|)
        ≤
          2 * pairProbeFactor hP hStruct center α β *
            (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
              Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) :=
  centeredOriginMomentRoot_le_factorSum_of_probe_abs_le
    hP hStruct hP4
    (pairProbeFactor_nonneg hP hStruct center α β)
    (fullBlockNormalizedQuadraticObservable_plusProbe_abs_le_factorSum_ae
      hP hStruct hP4 center hαβ)

/-- Centered origin moment input for normalized minus-pair probes. -/
theorem minusProbe_centeredOrigin_momentRoot_le_factorSum
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (center : ℤ) {α β : BlockCoord d} (hαβ : α ≠ β) :
    Integrable
        (fun a =>
          |Ch04.restrictionCenteredOriginObservable P 0
            (fullBlockNormalizedQuadraticObservableR hP hStruct center
              (fullBlockMinusProbe α β)) a| ^ hP4.xi) P ∧
      Ch04.annealedMomentRoot P hP4.xi
          (fun a =>
            |Ch04.restrictionCenteredOriginObservable P 0
              (fullBlockNormalizedQuadraticObservableR hP hStruct center
                (fullBlockMinusProbe α β)) a|)
        ≤
          2 * pairProbeFactor hP hStruct center α β *
            (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
              Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) :=
  centeredOriginMomentRoot_le_factorSum_of_probe_abs_le
    hP hStruct hP4
    (pairProbeFactor_nonneg hP hStruct center α β)
    (fullBlockNormalizedQuadraticObservable_minusProbe_abs_le_factorSum_ae
      hP hStruct hP4 center hαβ)

private theorem factorMomentSum_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤
      Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
        Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi :=
  add_nonneg
    (Ch04.LambdaMomentAtScale_nonneg P 0 hP4.xi hP4.sUpper_pos)
    (Ch04.lambdaInvMomentAtScale_nonneg P 0 hP4.xi hP4.sLower_pos)

private theorem coordinateProbe_partition_K_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (center : ℤ) (α : BlockCoord d) :
    0 ≤
      2 * coordinateProbeFactor hP hStruct center α *
        (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
          Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) := by
  exact mul_nonneg
    (mul_nonneg (by norm_num) (coordinateProbeFactor_nonneg hP hStruct center α))
    (factorMomentSum_nonneg hP4)

private theorem pairProbe_partition_K_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (center : ℤ) (α β : BlockCoord d) :
    0 ≤
      2 * pairProbeFactor hP hStruct center α β *
        (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
          Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi) := by
  exact mul_nonneg
    (mul_nonneg (by norm_num) (pairProbeFactor_nonneg hP hStruct center α β))
    (factorMomentSum_nonneg hP4)

/-- Rosenthal partition-average estimate for normalized coordinate probes,
with the origin moment supplied internally by `(P4)`. -/
theorem coordinateProbe_restrictionCenteredDescendantAverage_pow_rpow_inv_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {center m : ℤ} (hm : 0 ≤ m) (α : BlockCoord d) :
    let K :=
      2 * coordinateProbeFactor hP hStruct center α *
        (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
          Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)
    (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 m
          (fullBlockNormalizedQuadraticObservableR hP hStruct center
            (fullBlockCoordinateProbe α)) a| ^ hP4.xi ∂P) ^
        (1 / (hP4.xi : ℝ)) ≤
      ((descendantsAtScale (originCube d m) 0).card : ℝ)⁻¹ *
        (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
            ((descendantsAtScale (originCube d m) 0).card : ℝ) ^
              (1 / (hP4.xi : ℝ)) * K +
          Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
            Real.sqrt ((descendantsAtScale (originCube d m) 0).card : ℝ) * K) := by
  classical
  dsimp only
  let K :=
    2 * coordinateProbeFactor hP hStruct center α *
      (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
        Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)
  have hOrigin :=
    coordinateProbe_centeredOrigin_momentRoot_le_factorSum
      hP hStruct hP4 center α
  exact
    fullBlockNormalizedQuadraticObservable_restrictionCenteredDescendantAverage_pow_rpow_inv_le
      hP hStruct hP4 (q := fullBlockCoordinateProbe α)
      (center := center) (n := 0) (m := m) (K := K)
      (by norm_num) hm
      (by simpa [K] using
        coordinateProbe_partition_K_nonneg hP hStruct hP4 center α)
      hOrigin.1 (by simpa [K, Ch04.annealedMomentRoot, one_div] using hOrigin.2)

/-- Rosenthal partition-average estimate for normalized plus-pair probes,
with the origin moment supplied internally by `(P4)`. -/
theorem plusProbe_restrictionCenteredDescendantAverage_pow_rpow_inv_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {center m : ℤ} (hm : 0 ≤ m) {α β : BlockCoord d} (hαβ : α ≠ β) :
    let K :=
      2 * pairProbeFactor hP hStruct center α β *
        (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
          Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)
    (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 m
          (fullBlockNormalizedQuadraticObservableR hP hStruct center
            (fullBlockPlusProbe α β)) a| ^ hP4.xi ∂P) ^
        (1 / (hP4.xi : ℝ)) ≤
      ((descendantsAtScale (originCube d m) 0).card : ℝ)⁻¹ *
        (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
            ((descendantsAtScale (originCube d m) 0).card : ℝ) ^
              (1 / (hP4.xi : ℝ)) * K +
          Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
            Real.sqrt ((descendantsAtScale (originCube d m) 0).card : ℝ) * K) := by
  classical
  dsimp only
  let K :=
    2 * pairProbeFactor hP hStruct center α β *
      (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
        Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)
  have hOrigin :=
    plusProbe_centeredOrigin_momentRoot_le_factorSum
      hP hStruct hP4 center hαβ
  exact
    fullBlockNormalizedQuadraticObservable_restrictionCenteredDescendantAverage_pow_rpow_inv_le
      hP hStruct hP4 (q := fullBlockPlusProbe α β)
      (center := center) (n := 0) (m := m) (K := K)
      (by norm_num) hm
      (by simpa [K] using
        pairProbe_partition_K_nonneg hP hStruct hP4 center α β)
      hOrigin.1 (by simpa [K, Ch04.annealedMomentRoot, one_div] using hOrigin.2)

/-- Rosenthal partition-average estimate for normalized minus-pair probes,
with the origin moment supplied internally by `(P4)`. -/
theorem minusProbe_restrictionCenteredDescendantAverage_pow_rpow_inv_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {center m : ℤ} (hm : 0 ≤ m) {α β : BlockCoord d} (hαβ : α ≠ β) :
    let K :=
      2 * pairProbeFactor hP hStruct center α β *
        (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
          Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)
    (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 m
          (fullBlockNormalizedQuadraticObservableR hP hStruct center
            (fullBlockMinusProbe α β)) a| ^ hP4.xi ∂P) ^
        (1 / (hP4.xi : ℝ)) ≤
      ((descendantsAtScale (originCube d m) 0).card : ℝ)⁻¹ *
        (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
            ((descendantsAtScale (originCube d m) 0).card : ℝ) ^
              (1 / (hP4.xi : ℝ)) * K +
          Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
            Real.sqrt ((descendantsAtScale (originCube d m) 0).card : ℝ) * K) := by
  classical
  dsimp only
  let K :=
    2 * pairProbeFactor hP hStruct center α β *
      (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
        Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)
  have hOrigin :=
    minusProbe_centeredOrigin_momentRoot_le_factorSum
      hP hStruct hP4 center hαβ
  exact
    fullBlockNormalizedQuadraticObservable_restrictionCenteredDescendantAverage_pow_rpow_inv_le
      hP hStruct hP4 (q := fullBlockMinusProbe α β)
      (center := center) (n := 0) (m := m) (K := K)
      (by norm_num) hm
      (by simpa [K] using
        pairProbe_partition_K_nonneg hP hStruct hP4 center α β)
      hOrigin.1 (by simpa [K, Ch04.annealedMomentRoot, one_div] using hOrigin.2)

end

end VarianceBoundGoodScale
end Section54
end Ch05
end Book
end Homogenization
