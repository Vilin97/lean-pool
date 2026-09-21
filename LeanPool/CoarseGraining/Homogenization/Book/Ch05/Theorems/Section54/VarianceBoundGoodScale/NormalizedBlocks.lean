/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.Pigeonhole.ScalarChain
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.GeometricSum

/-! # Normalized Blocks -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace VarianceBoundGoodScale

open MeasureTheory

noncomputable section

/-!
# Normalized full-block fluctuation wrappers

This file records the Section 5.4-facing consequences of the public Ch4 and
Section 5.2 APIs for the normalized full-block fluctuation observable appearing
in the variance bound at a good scale.
-/

/-- The quadratic form associated with a full-block matrix. -/
def fullBlockQuadratic {d : ℕ} (M : FullBlockMat d) (x : FullBlockVec d) : ℝ :=
  dotProduct x (Matrix.mulVec M x)

/-- Quadratic form of the identity full-block matrix. -/
theorem fullBlockQuadratic_one {d : ℕ} (q : FullBlockVec d) :
    fullBlockQuadratic (1 : FullBlockMat d) q = dotProduct q q := by
  simp [fullBlockQuadratic, Matrix.one_mulVec]

/-- The Euclidean dot product of a full-block vector with itself is
nonnegative. -/
theorem dotProduct_self_nonneg {d : ℕ} (q : FullBlockVec d) :
    0 ≤ dotProduct q q := by
  simpa using dotProduct_star_self_nonneg (v := q)

private theorem norm_sq_toFullBlockVec {d : ℕ} (X : BlockVec d) :
    ‖(WithLp.toLp 2 (toFullBlockVec X) :
        PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 =
      blockVecDot X X := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]
  rcases X with ⟨p, q⟩
  simp [toFullBlockVec, blockVecDot, vecDot, sq]

private theorem abs_blockVecDot_le_norm_mul_norm {d : ℕ} (X Y : BlockVec d) :
    |blockVecDot X Y| ≤
      ‖(WithLp.toLp 2 (toFullBlockVec X) :
          PiLp 2 (fun _ : BlockCoord d => ℝ))‖ *
        ‖(WithLp.toLp 2 (toFullBlockVec Y) :
          PiLp 2 (fun _ : BlockCoord d => ℝ))‖ := by
  let x : PiLp 2 (fun _ : BlockCoord d => ℝ) := WithLp.toLp 2 (toFullBlockVec X)
  let y : PiLp 2 (fun _ : BlockCoord d => ℝ) := WithLp.toLp 2 (toFullBlockVec Y)
  have hinner : inner ℝ x y = blockVecDot X Y := by
    rw [← dotProduct_toFullBlockVec X Y]
    simp [x, y, PiLp.inner_apply, dotProduct, mul_comm]
  simpa [hinner] using abs_real_inner_le_norm x y

private theorem fullBlockMat_mulVec_norm_sq_le_operatorNorm_sq
    {d : ℕ} [NeZero d] (M : FullBlockMat d) (X : BlockVec d) :
    blockVecDot (blockMatVecMul (ofFullBlockMat M) X)
        (blockMatVecMul (ofFullBlockMat M) X) ≤
      ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ^ 2 *
        blockVecDot X X := by
  let x : PiLp 2 (fun _ : BlockCoord d => ℝ) := WithLp.toLp 2 (toFullBlockVec X)
  let y : PiLp 2 (fun _ : BlockCoord d => ℝ) :=
    WithLp.toLp 2 (toFullBlockVec (blockMatVecMul (ofFullBlockMat M) X))
  have hy : (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M) x = y := by
    simp [x, y, Matrix.toEuclideanCLM_toLp, toFullBlockVec_blockMatVecMul]
  have hnorm :
      ‖y‖ ≤ ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ * ‖x‖ := by
    simpa [hy] using
      (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M).le_opNorm x
  have hsq :
      ‖y‖ ^ 2 ≤
        (‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ * ‖x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg y) hnorm 2
  calc
    blockVecDot (blockMatVecMul (ofFullBlockMat M) X)
        (blockMatVecMul (ofFullBlockMat M) X) = ‖y‖ ^ 2 := by
          rw [norm_sq_toFullBlockVec]
    _ ≤ (‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ * ‖x‖) ^ 2 := hsq
    _ =
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ^ 2 *
          blockVecDot X X := by
          rw [mul_pow, norm_sq_toFullBlockVec]

/-- A scalar full-block quadratic probe is controlled by the squared
Euclidean operator norm of the matrix. -/
theorem fullBlockQuadratic_abs_sq_le_operatorNorm_sq_mul_dotProduct_sq
    {d : ℕ} [NeZero d] (M : FullBlockMat d) (q : FullBlockVec d) :
    |fullBlockQuadratic M q| ^ (2 : ℕ) ≤
      ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ^ (2 : ℕ) *
        (dotProduct q q) ^ (2 : ℕ) := by
  let X : BlockVec d := ofFullBlockVec q
  let Y : BlockVec d := blockMatVecMul (ofFullBlockMat M) X
  have hquad : fullBlockQuadratic M q = blockVecDot X Y := by
    rw [← dotProduct_toFullBlockVec X Y]
    simp [fullBlockQuadratic, X, Y, toFullBlockVec_blockMatVecMul]
  have hcs := abs_blockVecDot_le_norm_mul_norm X Y
  have hcs_sq := pow_le_pow_left₀ (abs_nonneg (blockVecDot X Y)) hcs 2
  have hY := fullBlockMat_mulVec_norm_sq_le_operatorNorm_sq M X
  have hXX : blockVecDot X X = dotProduct q q := by
    rw [← dotProduct_toFullBlockVec X X]
    simp [X]
  have hX_nonneg : 0 ≤ blockVecDot X X := by
    rw [hXX]
    exact dotProduct_self_nonneg q
  have hnormX_sq :
      ‖(WithLp.toLp 2 (toFullBlockVec X) :
          PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 =
        blockVecDot X X := norm_sq_toFullBlockVec X
  have hnormY_sq :
      ‖(WithLp.toLp 2 (toFullBlockVec Y) :
          PiLp 2 (fun _ : BlockCoord d => ℝ))‖ ^ 2 =
        blockVecDot Y Y := norm_sq_toFullBlockVec Y
  calc
    |fullBlockQuadratic M q| ^ (2 : ℕ) = |blockVecDot X Y| ^ (2 : ℕ) := by
      rw [hquad]
    _ ≤ (‖(WithLp.toLp 2 (toFullBlockVec X) :
            PiLp 2 (fun _ : BlockCoord d => ℝ))‖ *
          ‖(WithLp.toLp 2 (toFullBlockVec Y) :
            PiLp 2 (fun _ : BlockCoord d => ℝ))‖) ^ (2 : ℕ) := hcs_sq
    _ = (blockVecDot X X) * (blockVecDot Y Y) := by
      rw [mul_pow, hnormX_sq, hnormY_sq]
    _ ≤ (blockVecDot X X) *
          (‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ^ (2 : ℕ) *
            blockVecDot X X) :=
        mul_le_mul_of_nonneg_left hY hX_nonneg
    _ =
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ^ (2 : ℕ) *
          (dotProduct q q) ^ (2 : ℕ) := by
      rw [hXX]
      ring

/-- Quadratic forms are linear in the matrix argument. -/
theorem fullBlockQuadratic_sub {d : ℕ} (M N : FullBlockMat d)
    (q : FullBlockVec d) :
    fullBlockQuadratic (M - N) q =
      fullBlockQuadratic M q - fullBlockQuadratic N q := by
  unfold fullBlockQuadratic
  rw [Matrix.sub_mulVec, dotProduct_sub]

private theorem dotProduct_diagonal_mulVec_left_eq_right
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r x y : ι → ℝ) :
    dotProduct (Matrix.mulVec (Matrix.diagonal r) x) y =
      dotProduct x (Matrix.mulVec (Matrix.diagonal r) y) := by
  simp [dotProduct, Matrix.mulVec, Matrix.diagonal, mul_left_comm, mul_comm]

/-- Diagonal normalization of a block quadratic form is the block quadratic
form evaluated on the diagonally normalized vector. -/
theorem fullBlockQuadratic_diagonal_toFullBlockMat_eq_blockVecDot
    {d : ℕ} (r : BlockCoord d → ℝ) (A : BlockMat d) (q : FullBlockVec d) :
    fullBlockQuadratic (Matrix.diagonal r * toFullBlockMat A * Matrix.diagonal r) q =
      blockVecDot (ofFullBlockVec (Matrix.mulVec (Matrix.diagonal r) q))
        (blockMatVecMul A (ofFullBlockVec (Matrix.mulVec (Matrix.diagonal r) q))) := by
  unfold fullBlockQuadratic
  rw [← Matrix.mulVec_mulVec q (Matrix.diagonal r * toFullBlockMat A) (Matrix.diagonal r)]
  change dotProduct q
      ((Matrix.diagonal r * toFullBlockMat A).mulVec ((Matrix.diagonal r).mulVec q)) = _
  rw [← Matrix.mulVec_mulVec ((Matrix.diagonal r).mulVec q) (Matrix.diagonal r)
    (toFullBlockMat A)]
  rw [← dotProduct_diagonal_mulVec_left_eq_right]
  have hdot := dotProduct_toFullBlockVec
    (ofFullBlockVec (Matrix.mulVec (Matrix.diagonal r) q))
    (blockMatVecMul A (ofFullBlockVec (Matrix.mulVec (Matrix.diagonal r) q)))
  rw [toFullBlockVec_ofFullBlockVec, toFullBlockVec_blockMatVecMul] at hdot
  simpa using hdot

private theorem diagonal_quadratic_le_mul_dotProduct
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ι → ℝ} {C : ℝ} (q : ι → ℝ)
    (hr : ∀ α, r α ≤ C) :
    dotProduct q (Matrix.mulVec (Matrix.diagonal r) q) ≤ C * dotProduct q q := by
  classical
  unfold dotProduct
  simp [Matrix.mulVec, diagonal_dotProduct]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro α _hα
  have hsq : 0 ≤ q α * q α := by nlinarith [sq_nonneg (q α)]
  have h := mul_le_mul_of_nonneg_right (hr α) hsq
  nlinarith

private theorem mul_dotProduct_le_diagonal_quadratic
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ι → ℝ} {C : ℝ} (q : ι → ℝ)
    (hr : ∀ α, C ≤ r α) :
    C * dotProduct q q ≤ dotProduct q (Matrix.mulVec (Matrix.diagonal r) q) := by
  classical
  unfold dotProduct
  simp [Matrix.mulVec, diagonal_dotProduct]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro α _hα
  have hsq : 0 ≤ q α * q α := by nlinarith [sq_nonneg (q α)]
  have h := mul_le_mul_of_nonneg_right (hr α) hsq
  nlinarith

/-- A diagonal full-block quadratic form is controlled above by the largest
diagonal coefficient. -/
theorem fullBlockQuadratic_diagonal_le_mul_dotProduct
    {d : ℕ} {r : BlockCoord d → ℝ} {C : ℝ} (q : FullBlockVec d)
    (hr : ∀ α, r α ≤ C) :
    fullBlockQuadratic (Matrix.diagonal r) q ≤ C * dotProduct q q :=
  diagonal_quadratic_le_mul_dotProduct q hr

/-- A diagonal full-block quadratic form is controlled below by the smallest
diagonal coefficient. -/
theorem mul_dotProduct_le_fullBlockQuadratic_diagonal
    {d : ℕ} {r : BlockCoord d → ℝ} {C : ℝ} (q : FullBlockVec d)
    (hr : ∀ α, C ≤ r α) :
    C * dotProduct q q ≤ fullBlockQuadratic (Matrix.diagonal r) q :=
  mul_dotProduct_le_diagonal_quadratic q hr

/-- Symmetry is preserved by diagonal congruence of a full-block matrix. -/
theorem isSymm_diagonal_mul_fullBlockMat_mul_diagonal
    {d : ℕ} (r : BlockCoord d → ℝ) {M : FullBlockMat d}
    (hM : M.IsSymm) :
    (Matrix.diagonal r * M * Matrix.diagonal r).IsSymm := by
  rw [Matrix.IsSymm]
  ext α β
  simp [Matrix.transpose_apply, Matrix.mul_apply, Matrix.diagonal]
  have h := hM.apply α β
  rw [h]
  ring

/-- Scalar annealed full-block matrices remain diagonal after scalar
normalization. -/
theorem normalizedScalarAnnealedBlockMatrix_eq_diagonal
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center n : ℤ) :
    let b := hP.barSigmaAtScale hStruct center
    let c := hP.barSigmaStarAtScale hStruct center
    let bn := hP.barSigmaAtScale hStruct n
    let cn := hP.barSigmaStarAtScale hStruct n
    let D : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
    D * toFullBlockMat (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct n) * D =
      Matrix.diagonal (fun α : BlockCoord d =>
        match α with
        | Sum.inl _ => (Real.sqrt b)⁻¹ * bn * (Real.sqrt b)⁻¹
        | Sum.inr _ => Real.sqrt c * cn⁻¹ * Real.sqrt c) := by
  classical
  dsimp only
  ext α β
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          by_cases hij : i = j
          · subst j
            simp [Ch04.scalarAnnealedBlockMatrixAtScale, Ch02.blockDiag, toFullBlockMat,
              Ch04.scalarFullBlockInvSqrtDiag, Matrix.mul_apply, Matrix.diagonal]
          · simp [Ch04.scalarAnnealedBlockMatrixAtScale, Ch02.blockDiag, toFullBlockMat,
              Ch04.scalarFullBlockInvSqrtDiag, Matrix.mul_apply, Matrix.diagonal, hij]
      | inr j =>
          simp [Ch04.scalarAnnealedBlockMatrixAtScale, Ch02.blockDiag, toFullBlockMat,
            Ch04.scalarFullBlockInvSqrtDiag, Matrix.mul_apply, Matrix.diagonal]
  | inr i =>
      cases β with
      | inl j =>
          simp [Ch04.scalarAnnealedBlockMatrixAtScale, Ch02.blockDiag, toFullBlockMat,
            Ch04.scalarFullBlockInvSqrtDiag, Matrix.mul_apply, Matrix.diagonal]
      | inr j =>
          by_cases hij : i = j
          · subst j
            simp [Ch04.scalarAnnealedBlockMatrixAtScale, Ch02.blockDiag, toFullBlockMat,
              Ch04.scalarFullBlockInvSqrtDiag, Matrix.mul_apply, Matrix.diagonal]
          · simp [Ch04.scalarAnnealedBlockMatrixAtScale, Ch02.blockDiag, toFullBlockMat,
              Ch04.scalarFullBlockInvSqrtDiag, Matrix.mul_apply, Matrix.diagonal, hij]

/-- At the center scale, scalar normalization turns the scalar annealed block
into the identity. -/
theorem normalizedScalarAnnealedBlockMatrix_self_eq_one
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    let b := hP.barSigmaAtScale hStruct (m : ℤ)
    let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
    let D : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
    D * toFullBlockMat (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct (m : ℤ)) * D =
      1 := by
  classical
  dsimp only
  let b := hP.barSigmaAtScale hStruct (m : ℤ)
  let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
  have hb : 0 < b := by
    simpa [b] using Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 m
  have hc : 0 < c := by
    simpa [c] using Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hdiag := normalizedScalarAnnealedBlockMatrix_eq_diagonal hP hStruct (m : ℤ) (m : ℤ)
  dsimp only at hdiag
  rw [hdiag]
  ext α β
  by_cases hαβ : α = β
  · subst β
    cases α with
    | inl i =>
        simp [Matrix.diagonal]
        field_simp [ne_of_gt (Real.sqrt_pos.mpr (by simpa [b] using hb))]
        rw [Real.sq_sqrt (by simpa [b] using hb.le)]
    | inr i =>
        simp [Matrix.diagonal]
        field_simp [ne_of_gt (Real.sqrt_pos.mpr (by simpa [c] using hc))]
        rw [Real.sq_sqrt (by simpa [c] using hc.le)]
        field_simp [ne_of_gt (by simpa [c] using hc)]
  · simp [Matrix.diagonal, hαβ]

/-- Under the structural law, the annealed full block is exactly the scalar
block diagonal used to normalize the manuscript fluctuation observable. -/
theorem annealedBlockMatrixAtScale_eq_scalarAnnealedBlockMatrixAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (n : ℤ) :
    Ch04.annealedBlockMatrixAtScale P n =
      Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct n := by
  rw [Ch04.scalarAnnealedBlockMatrixAtScale, Ch04.annealedBlockMatrixAtScale,
    Ch04.annealedBlockMatrix, Ch02.blockDiag]
  refine Eq.mpr (BlockMat.mk.injEq _ _ _ _ _ _ _ _) ?_
  constructor
  · change Ch04.annealedBAtScale P n = hP.barSigmaAtScale hStruct n • 1
    rw [hP.annealedBAtScale_eq_barBAtScale hStruct n,
      hP.barSigmaAtScale_eq_barBAtScale hStruct n]
  constructor
  · have hLowerLeft :
        (Ch04.annealedBlockMatrix P (cubeSet (originCube d n))).lowerLeft = 0 := by
      have h :=
        (Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw
          hP hStruct n).sigmaStarInvKappaMean_eq_zero
      simpa [Ch04.annealedSigmaStarInvKappaMeanAtScale,
        Ch04.annealedSigmaStarInvKappaMean] using congrArg Neg.neg h
    have hSymm :
        (Ch04.annealedBlockMatrix P (cubeSet (originCube d n))).upperRight = 0 := by
      ext i j
      have hEntry :
          (Ch04.annealedBlockMatrix P (cubeSet (originCube d n))).upperRight i j =
            (Ch04.annealedBlockMatrix P (cubeSet (originCube d n))).lowerLeft j i := by
        apply integral_congr_ae
        filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
        let F : Ch02.TriadicCoeffFamily d :=
          Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
        have hEq :
            coarseBlockMatrix (cubeSet (originCube d n)) a =
              Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d n))
                (F.coeffOn (originCube d n)) := by
          simpa [F] using
            Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
              ha (originCube d n)
        have hSymm :=
          Ch02.isSymmetricBlockMat_coarseBlockMatrix
            (Ch02.cubeDomain (originCube d n)) (F.coeffOn (originCube d n))
        have hentry := hSymm (Sum.inl i) (Sum.inr j)
        simpa [hEq, blockMatEntry] using hentry
      rw [hEntry, hLowerLeft]
      simp
    simpa [Ch04.annealedBlockMatrix] using hSymm
  constructor
  · have hLowerLeft :
        (Ch04.annealedBlockMatrix P (cubeSet (originCube d n))).lowerLeft = 0 := by
      have h :=
        (Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw
          hP hStruct n).sigmaStarInvKappaMean_eq_zero
      simpa [Ch04.annealedSigmaStarInvKappaMeanAtScale,
        Ch04.annealedSigmaStarInvKappaMean] using congrArg Neg.neg h
    simpa [Ch04.annealedBlockMatrix] using hLowerLeft
  · change Ch04.annealedSigmaStarInvAtScale P n =
      (hP.barSigmaStarAtScale hStruct n)⁻¹ • 1
    rw [hP.annealedSigmaStarInvAtScale_eq_barSigmaStarInvAtScale hStruct n,
      hP.barSigmaStarAtScale_eq_inv_barSigmaStarInvAtScale hStruct n]
    simp

/-- The scalar annealed block matrix is symmetric as a doubled block matrix. -/
theorem isSymmetricBlockMat_scalarAnnealedBlockMatrixAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (center : ℤ) :
    IsSymmetricBlockMat (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center) := by
  intro α β
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          by_cases hij : i = j
          · subst j
            simp [Ch04.scalarAnnealedBlockMatrixAtScale, Ch02.blockDiag, blockMatEntry]
          · have hji : j ≠ i := fun h => hij h.symm
            simp [Ch04.scalarAnnealedBlockMatrixAtScale, Ch02.blockDiag, blockMatEntry,
              hij, hji]
      | inr j =>
          simp [Ch04.scalarAnnealedBlockMatrixAtScale, Ch02.blockDiag, blockMatEntry]
  | inr i =>
      cases β with
      | inl j =>
          simp [Ch04.scalarAnnealedBlockMatrixAtScale, Ch02.blockDiag, blockMatEntry]
      | inr j =>
          by_cases hij : i = j
          · subst j
            simp [Ch04.scalarAnnealedBlockMatrixAtScale, Ch02.blockDiag, blockMatEntry]
          · have hji : j ≠ i := fun h => hij h.symm
            simp [Ch04.scalarAnnealedBlockMatrixAtScale, Ch02.blockDiag, blockMatEntry,
              hij, hji]

/-- At the center scale, scalar normalization turns the annealed block into
the identity. -/
theorem normalizedAnnealedBlockMatrix_self_eq_one
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    let b := hP.barSigmaAtScale hStruct (m : ℤ)
    let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
    let D : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
    D * toFullBlockMat (Ch04.annealedBlockMatrixAtScale P (m : ℤ)) * D = 1 := by
  rw [annealedBlockMatrixAtScale_eq_scalarAnnealedBlockMatrixAtScale hP hStruct (m : ℤ)]
  exact normalizedScalarAnnealedBlockMatrix_self_eq_one hP hStruct hP4 m

/-- The normalized full-block fluctuation observable is nonnegative. -/
theorem fullBlockNormalizedFluctuationOperatorNormSqAtScale_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (R : TriadicCube d) (a : RegCoeffField d) :
    0 ≤
      Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
        hP hStruct center R a := by
  unfold Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
  unfold Ch04.fullBlockNormalizedFluctuationOperatorNormSq
  exact sq_nonneg _

/-- The normalized full-block fluctuation matrix whose Euclidean operator norm
is squared in the manuscript observable. -/
noncomputable def fullBlockNormalizedFluctuationMatrix
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (U : Set (Vec d)) (a : CoeffField d) : FullBlockMat d :=
  let b := hP.barSigmaAtScale hStruct center
  let c := hP.barSigmaStarAtScale hStruct center
  let D : FullBlockMat d :=
    Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
  let A := coarseBlockMatrix U a
  let Abar := Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center
  D * (toFullBlockMat A - toFullBlockMat Abar) * D

/-- The normalized full-block fluctuation matrix is symmetric whenever the
underlying coarse block matrix is symmetric. -/
theorem fullBlockNormalizedFluctuationMatrix_isSymm_of_isSymmetricBlockMat
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) {U : Set (Vec d)} {a : CoeffField d}
    (hA : IsSymmetricBlockMat (coarseBlockMatrix U a)) :
    (fullBlockNormalizedFluctuationMatrix hP hStruct center U a).IsSymm := by
  let b := hP.barSigmaAtScale hStruct center
  let c := hP.barSigmaStarAtScale hStruct center
  let D : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
  let A := coarseBlockMatrix U a
  let Abar := Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center
  have hA_full : (toFullBlockMat A).IsSymm := by
    simpa [A] using isSymm_toFullBlockMat_of_isSymmetricBlockMat hA
  have hAbar_full : (toFullBlockMat Abar).IsSymm :=
    isSymm_toFullBlockMat_of_isSymmetricBlockMat
      (isSymmetricBlockMat_scalarAnnealedBlockMatrixAtScale hP hStruct center)
  have hsub : (toFullBlockMat A - toFullBlockMat Abar).IsSymm := hA_full.sub hAbar_full
  simpa [fullBlockNormalizedFluctuationMatrix, b, c, D, A, Abar] using
    isSymm_diagonal_mul_fullBlockMat_mul_diagonal
      (Ch04.scalarFullBlockInvSqrtDiag (d := d) b c) hsub

/-- On cube sets, the public coarse block matrix is symmetric almost surely. -/
theorem isSymmetricBlockMat_coarseBlockMatrix_cubeSet_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (Q : TriadicCube d) :
    ∀ᵐ a ∂P, IsSymmetricBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) := by
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  have hEq :
      coarseBlockMatrix (cubeSet Q) a.toFun =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q) := by
    simpa [F] using
      Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha Q
  rw [hEq]
  exact Ch02.isSymmetricBlockMat_coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q)

/-- On cube sets, the normalized full-block fluctuation matrix is symmetric
almost surely. -/
theorem fullBlockNormalizedFluctuationMatrix_isSymm_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) :
    ∀ᵐ a ∂P,
      (fullBlockNormalizedFluctuationMatrix hP hStruct center (cubeSet Q) a.toFun).IsSymm := by
  filter_upwards [isSymmetricBlockMat_coarseBlockMatrix_cubeSet_ae hP Q] with a hA
  exact fullBlockNormalizedFluctuationMatrix_isSymm_of_isSymmetricBlockMat
    hP hStruct center hA

/-- The Ch4 normalized fluctuation observable is the squared operator norm of
`fullBlockNormalizedFluctuationMatrix`. -/
theorem fullBlockNormalizedFluctuationOperatorNormSq_eq_norm_sq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (U : Set (Vec d)) (a : CoeffField d) :
    Ch04.fullBlockNormalizedFluctuationOperatorNormSq hP hStruct center U a =
      ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (fullBlockNormalizedFluctuationMatrix hP hStruct center U a)‖ ^ (2 : ℕ) := by
  rfl

/-- Normalized quadratic probe observable used before the finite-probe upgrade
in the good-scale variance bound.  This is linear in the coarse block matrix;
centering is supplied by `Ch04.restrictionCenteredOriginObservable`. -/
noncomputable def fullBlockNormalizedQuadraticObservable
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (q : FullBlockVec d) (U : Set (Vec d))
    (a : CoeffField d) : ℝ :=
  let b := hP.barSigmaAtScale hStruct center
  let c := hP.barSigmaStarAtScale hStruct center
  let D : FullBlockMat d :=
    Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
  fullBlockQuadratic (D * toFullBlockMat (coarseBlockMatrix U a) * D) q

/-- Carrier realization of the normalized quadratic probe observable, applied
to the honest sample of a carrier field.  This is the form consumed by the
Ch4 descendant-average machinery. -/
noncomputable def fullBlockNormalizedQuadraticObservableR
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (q : FullBlockVec d) (U : Set (Vec d))
    (a : RegCoeffField d) : ℝ :=
  fullBlockNormalizedQuadraticObservable hP hStruct center q U a.toFun

/-- Centering a normalized quadratic probe at the center-scale annealed value
is the quadratic form of the normalized fluctuation matrix. -/
theorem fullBlockNormalizedQuadraticObservable_sub_dotProduct_eq_fluctuationQuadratic
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ)
    (q : FullBlockVec d) (U : Set (Vec d)) (a : CoeffField d) :
    fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ) q U a -
        dotProduct q q =
      fullBlockQuadratic
        (fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ) U a) q := by
  classical
  let b := hP.barSigmaAtScale hStruct (m : ℤ)
  let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let D : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
  let A := coarseBlockMatrix U a
  let Abar := Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct (m : ℤ)
  have hcenter : D * toFullBlockMat Abar * D = 1 := by
    simpa [D, Abar, b, c] using
      normalizedScalarAnnealedBlockMatrix_self_eq_one hP hStruct hP4 m
  have hmat : D * toFullBlockMat A * D - 1 =
      D * (toFullBlockMat A - toFullBlockMat Abar) * D := by
    rw [← hcenter]
    ext α β
    simp [Matrix.mul_apply, Finset.sum_sub_distrib, sub_mul, mul_sub]
  calc
    fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ) q U a - dotProduct q q
        = fullBlockQuadratic (D * toFullBlockMat A * D) q - fullBlockQuadratic 1 q := by
          rw [fullBlockQuadratic_one]
          simp [fullBlockNormalizedQuadraticObservable, D, A, b, c]
    _ = fullBlockQuadratic (D * toFullBlockMat A * D - 1) q := by
          rw [fullBlockQuadratic_sub]
    _ = fullBlockQuadratic
          (fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ) U a) q := by
          rw [hmat]
          rfl

private theorem blockPosDef_quadratic_nonneg
    {d : ℕ} {A : BlockMat d} (hA : Ch02.BlockPosDef A) (X : BlockVec d) :
    0 ≤ blockVecDot X (blockMatVecMul A X) := by
  by_cases hX : X = 0
  · subst X
    simp [blockVecDot, blockMatVecMul, vecDot, matVecMul]
  · exact (hA X hX).le

/-- Normalized quadratic probes are nonnegative on cube sets, almost surely. -/
theorem fullBlockNormalizedQuadraticObservable_nonneg_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (q : FullBlockVec d) (Q : TriadicCube d) :
    ∀ᵐ a ∂P,
      0 ≤ fullBlockNormalizedQuadraticObservable hP hStruct center q (cubeSet Q) a.toFun := by
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  let b := hP.barSigmaAtScale hStruct center
  let c := hP.barSigmaStarAtScale hStruct center
  let D : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
  let X : BlockVec d := ofFullBlockVec (Matrix.mulVec D q)
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  have hEq :
      coarseBlockMatrix (cubeSet Q) a.toFun =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q) := by
    simpa [F] using
      Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha Q
  have hPos : Ch02.BlockPosDef (coarseBlockMatrix (cubeSet Q) a.toFun) := by
    rw [hEq]
    exact
      (Ch02.blockCoarseMatrixTheory (Ch02.cubeDomain Q) (F.coeffOn Q)).block_matrix_posDef
  have hobs :
      fullBlockNormalizedQuadraticObservable hP hStruct center q (cubeSet Q) a.toFun =
        blockVecDot X (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a.toFun) X) := by
    dsimp [fullBlockNormalizedQuadraticObservable, fullBlockQuadratic, b, c, D, X]
    simpa [D] using!
      fullBlockQuadratic_diagonal_toFullBlockMat_eq_blockVecDot
        (Ch04.scalarFullBlockInvSqrtDiag (d := d) b c)
        (coarseBlockMatrix (cubeSet Q) a.toFun) q
  rw [hobs]
  exact blockPosDef_quadratic_nonneg hPos X

/-- Translation covariance of the normalized quadratic probe observable. -/
theorem fullBlockNormalizedQuadraticObservable_translation_covariant
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (q : FullBlockVec d) :
    IsTranslationCovariant
      (fun U : Set (Vec d) => fun a : CoeffField d =>
        fullBlockNormalizedQuadraticObservable hP hStruct center q U a) := by
  intro U z a
  simp [fullBlockNormalizedQuadraticObservable, translateByInt,
    coarseBlockMatrix_translateSet_eq_translateCoeffField]

/-- `(P4)` supplies integrability of the normalized full-block fluctuation on
origin cubes. -/
theorem integrable_origin_fullBlockNormalizedFluctuationOperatorNormSqAtScale_from_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (center : ℤ) (n : ℕ) :
    Integrable
      (Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
        hP hStruct center (originCube d (n : ℤ))) P :=
  Section52.integrable_fullBlockNormalizedFluctuationOperatorNormSqAtScale_originCube_from_P4
    hP hStruct hP4 center n

/-- Integer-scale version of the origin-cube integrability consequence of
`(P4)`. -/
theorem integrable_origin_fullBlockNormalizedFluctuationOperatorNormSqAtScale_from_P4_of_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (center n : ℤ)
    (hn : 0 ≤ n) :
    Integrable
      (Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
        hP hStruct center (originCube d n)) P := by
  have hnat :=
    integrable_origin_fullBlockNormalizedFluctuationOperatorNormSqAtScale_from_P4
      hP hStruct hP4 center (Int.toNat n)
  simpa [Int.toNat_of_nonneg hn] using hnat

/-- Under `(P4)` and stationarity, the normalized full-block fluctuation is
integrable on every nonnegative-scale cube. -/
theorem integrable_fullBlockNormalizedFluctuationOperatorNormSqAtScale_from_P4_of_nonneg_scale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (center : ℤ)
    (R : TriadicCube d) (hR_nonneg : 0 ≤ R.scale) :
    Integrable
      (Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
        hP hStruct center R) P := by
  have hOrigin :
      Integrable
        (Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d R.scale)) P :=
    integrable_origin_fullBlockNormalizedFluctuationOperatorNormSqAtScale_from_P4_of_nonneg
      hP hStruct hP4 center R.scale hR_nonneg
  exact
    hP.integrable_fullBlockNormalizedFluctuationOperatorNormSqAtScale_of_stationary
      hStruct.stationary hStruct center R hR_nonneg hOrigin

/-- Stationarity identifies the expectation on a nonnegative-scale cube with
the corresponding origin-cube expectation, with integrability supplied by
`(P4)`. -/
theorem integral_fullBlockNormalizedFluctuationOperatorNormSqAtScale_eq_originCube_from_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (center : ℤ)
    (R : TriadicCube d) (hR_nonneg : 0 ≤ R.scale) :
    ∫ a,
        Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center R a ∂P =
      ∫ a,
        Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d R.scale) a ∂P := by
  have hOrigin :
      Integrable
        (Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d R.scale)) P :=
    integrable_origin_fullBlockNormalizedFluctuationOperatorNormSqAtScale_from_P4_of_nonneg
      hP hStruct hP4 center R.scale hR_nonneg
  exact
    hP.integral_fullBlockNormalizedFluctuationOperatorNormSqAtScale_eq_originCube_of_stationary
      hStruct.stationary hStruct center R hR_nonneg hOrigin

/-- `(P4)` supplies the integrability hypothesis needed for descendant
averages of the normalized full-block fluctuation observable. -/
theorem integrable_fullBlockNormalizedFluctuationOperatorNormSqAtScale_of_mem_descendants_from_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (center : ℤ)
    {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale (originCube d m) n) :
    Integrable
      (Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
        hP hStruct center R) P := by
  have hOrigin :
      Integrable
        (Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d n)) P :=
    integrable_origin_fullBlockNormalizedFluctuationOperatorNormSqAtScale_from_P4_of_nonneg
      hP hStruct hP4 center n hn
  exact
    hP.integrable_fullBlockNormalizedFluctuationOperatorNormSqAtScale_of_mem_descendantsAtScale_originCube
      hStruct.stationary hStruct center hn hnm hR hOrigin

/-- Expectation of a descendant average of normalized full-block fluctuations
collapses to the corresponding origin-cube expectation under stationarity, with
integrability supplied by `(P4)`. -/
theorem integral_descendantsAverage_fullBlockNormalizedFluctuationOperatorNormSqAtScale_eq_originCube_from_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (center : ℤ)
    {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m) :
    ∫ a,
        descendantsAverage (originCube d m) (Int.toNat (m - n))
          (fun R =>
            Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct center R a) ∂P =
      ∫ a,
        Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d n) a ∂P := by
  have hOrigin :
      Integrable
        (Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d n)) P :=
    integrable_origin_fullBlockNormalizedFluctuationOperatorNormSqAtScale_from_P4_of_nonneg
      hP hStruct hP4 center n hn
  exact
    hP.integral_descendantsAverage_fullBlockNormalizedFluctuationOperatorNormSqAtScale_eq_originCube_of_stationary
      hStruct.stationary hStruct center hn hnm hOrigin

end

end VarianceBoundGoodScale
end Section54
end Ch05
end Book
end Homogenization
