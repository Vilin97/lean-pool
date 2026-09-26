/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError.Finite
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.Properties
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.WrapAround
public import LeanPool.CoarseGraining.Homogenization.Ambient.ScalarMatrix

/-! # Ellipticity Control -/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius Matrix.Norms.L2Operator

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-!
# Ellipticity control by the homogenization error

This file starts the Ch2 bridge from the normalized homogenization error
`\mathcal E` to the coarse-grained ellipticity factors.  The first endpoint
needed downstream is the finite `q = 2`, scalar-normalized estimate.
-/

private theorem ofFullBlockVec_mulVec_toFullBlockVec_eq_blockMatVecMul
    {d : ℕ} (M : FullBlockMat d) (P : BlockVec d) :
    ofFullBlockVec (Matrix.mulVec M (toFullBlockVec P)) =
      blockMatVecMul (ofFullBlockMat M) P := by
  simpa using
    (congrArg ofFullBlockVec
      (toFullBlockVec_blockMatVecMul (A := ofFullBlockMat M) P)).symm

private theorem blockMatVecMul_ofFullBlockMat_mul
    {d : ℕ} (M N : FullBlockMat d) (P : BlockVec d) :
    blockMatVecMul (ofFullBlockMat M) (blockMatVecMul (ofFullBlockMat N) P) =
      blockMatVecMul (ofFullBlockMat (M * N)) P := by
  rw [← ofFullBlockVec_toFullBlockVec
      (blockMatVecMul (ofFullBlockMat M) (blockMatVecMul (ofFullBlockMat N) P))]
  rw [← ofFullBlockVec_toFullBlockVec
      (blockMatVecMul (ofFullBlockMat (M * N)) P)]
  congr 1
  rw [toFullBlockVec_blockMatVecMul, toFullBlockVec_blockMatVecMul,
    toFullBlockMat_ofFullBlockMat, toFullBlockMat_ofFullBlockMat]
  simp [toFullBlockVec_blockMatVecMul, toFullBlockMat_ofFullBlockMat,
    Matrix.mulVec_mulVec]

theorem constantFullBlockMatrix_posDef_of_isEllipticMatrix
    {d : ℕ} [NeZero d] {lam Lam : ℝ} {a0 : Mat d}
    (ha0 : IsEllipticMatrix lam Lam a0) :
    (constantFullBlockMatrix a0).PosDef := by
  classical
  let M := constantFullBlockMatrix a0
  have hsymm : M.IsSymm := by
    dsimp [M, constantFullBlockMatrix]
    simpa [constantBlockMatrix, blockMatrixOfCoeff] using
      isSymm_toFullBlockMat_of_isSymmetricBlockMat
        (isSymmetricBlockMat_blockMatrixOfCoeff a0)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · simpa [Matrix.IsHermitian, Matrix.IsSymm] using hsymm
  · intro x hx
    let X : BlockVec d := ofFullBlockVec x
    have hX : X ≠ 0 := by
      intro hX0
      apply hx
      have hx0 : x = toFullBlockVec (0 : BlockVec d) := by
        simpa [X] using congrArg toFullBlockVec hX0
      have hzero : toFullBlockVec (0 : BlockVec d) = (0 : FullBlockVec d) := by
        ext i
        cases i <;> simp [toFullBlockVec]
      simpa [hzero] using hx0
    have hblock :
        0 < blockVecDot X (blockMatVecMul (constantBlockMatrix a0) X) := by
      simpa [constantBlockMatrix, blockMatrixOfCoeff] using!
        blockMatrixOfCoeff_quadratic_pos_of_isEllipticMatrix ha0 hX
    have hdot :
        0 < dotProduct (toFullBlockVec X)
          (Matrix.mulVec (constantFullBlockMatrix a0) (toFullBlockVec X)) := by
      have hEq :
          dotProduct (toFullBlockVec X)
              (Matrix.mulVec (toFullBlockMat (constantBlockMatrix a0))
                (toFullBlockVec X)) =
            blockVecDot X (blockMatVecMul (constantBlockMatrix a0) X) := by
        rw [← dotProduct_toFullBlockVec X
          (blockMatVecMul (constantBlockMatrix a0) X)]
        simp [toFullBlockVec_blockMatVecMul]
      have :
          0 < dotProduct (toFullBlockVec X)
            (Matrix.mulVec (toFullBlockMat (constantBlockMatrix a0))
              (toFullBlockVec X)) := by
        rwa [hEq]
      simpa [constantFullBlockMatrix] using this
    simpa [M, X] using hdot

theorem constantFullBlockMatrixSqrt_isSymm {d : ℕ} [NeZero d]
    (a0 : Mat d) :
    (constantFullBlockMatrixSqrt a0).IsSymm := by
  let M := constantFullBlockMatrix a0
  have hpsd : (constantFullBlockMatrixSqrt a0).PosSemidef := by
    dsimp [constantFullBlockMatrixSqrt, M]
    exact (Matrix.nonneg_iff_posSemidef (A := CFC.sqrt M)).mp (CFC.sqrt_nonneg M)
  simpa [Matrix.IsHermitian, Matrix.IsSymm] using hpsd.isHermitian

theorem fullBlockVecNormSq_constantFullBlockMatrixSqrt_mul_toFullBlockVec_eq
    {d : ℕ} [NeZero d] {a0 : Mat d} {lam Lam : ℝ}
    (ha0 : IsEllipticMatrix lam Lam a0) (P : BlockVec d) :
    fullBlockVecNormSq
        (Matrix.mulVec (constantFullBlockMatrixSqrt a0) (toFullBlockVec P)) =
      blockVecDot P (blockMatVecMul (constantBlockMatrix a0) P) := by
  let S := constantFullBlockMatrixSqrt a0
  let B := ofFullBlockMat S
  have hSsymm : S.IsSymm := constantFullBlockMatrixSqrt_isSymm a0
  have hBsymm : IsSymmetricBlockMat B := isSymmetricBlockMat_of_isSymm hSsymm
  calc
    fullBlockVecNormSq (Matrix.mulVec S (toFullBlockVec P)) =
        blockVecDot
          (ofFullBlockVec (Matrix.mulVec S (toFullBlockVec P)))
          (ofFullBlockVec (Matrix.mulVec S (toFullBlockVec P))) := by
            symm
            exact blockVecDot_ofFullBlockVec_self_eq_fullBlockVecNormSq _
    _ = blockVecDot (blockMatVecMul B P) (blockMatVecMul B P) := by
          rw [ofFullBlockVec_mulVec_toFullBlockVec_eq_blockMatVecMul]
    _ = blockVecDot P (blockMatVecMul B (blockMatVecMul B P)) := by
          symm
          exact blockVecDot_blockMatVecMul_comm_of_isSymmetricBlockMat hBsymm P
            (blockMatVecMul B P)
    _ = blockVecDot P (blockMatVecMul (ofFullBlockMat (S * S)) P) := by
          rw [blockMatVecMul_ofFullBlockMat_mul]
    _ = blockVecDot P (blockMatVecMul (constantBlockMatrix a0) P) := by
          let M := constantFullBlockMatrix a0
          have hMpos : M.PosDef := constantFullBlockMatrix_posDef_of_isEllipticMatrix
            (a0 := a0) ha0
          have hsq : S ^ 2 = M := by
            dsimp [S, M, constantFullBlockMatrixSqrt]
            simpa using CFC.sq_sqrt M hMpos.posSemidef.nonneg
          rw [pow_two] at hsq
          rw [hsq]
          simp [M, constantFullBlockMatrix]

theorem normalizedBlockResponseValueSet_mem_of_constantBlockQuadratic_eq_one
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : TriadicCoeffFamily d)
    {a0 : Mat d} {lam Lam : ℝ} (ha0 : IsEllipticMatrix lam Lam a0)
    (P : BlockVec d)
    (hquad :
      blockVecDot P (blockMatVecMul (constantBlockMatrix a0) P) = 1) :
    doubledResponseJ (cubeDomain Q) (a.coeffOn Q) P
        (blockMatVecMul (constantBlockMatrix a0) P) ∈
      normalizedBlockResponseValueSet Q a a0 := by
  classical
  let M := constantFullBlockMatrix a0
  let S := constantFullBlockMatrixSqrt a0
  let e : FullBlockVec d := Matrix.mulVec S (toFullBlockVec P)
  have hMpos : M.PosDef := by
    dsimp [M]
    exact constantFullBlockMatrix_posDef_of_isEllipticMatrix (a0 := a0) ha0
  have hSunit : IsUnit S := by
    dsimp [S, M, constantFullBlockMatrixSqrt]
    simpa using (CFC.isUnit_sqrt_iff M).2 hMpos.isUnit
  have he : fullBlockVecNormSq e = 1 := by
    simpa [e] using
      (fullBlockVecNormSq_constantFullBlockMatrixSqrt_mul_toFullBlockVec_eq
        (a0 := a0) ha0 P).trans hquad
  refine ⟨e, he, ?_⟩
  have hP :
      ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e) = P := by
    dsimp [constantFullBlockMatrixInvSqrt, e, S]
    have hSdet : IsUnit (Matrix.det S) := (Matrix.isUnit_iff_isUnit_det (A := S)).mp hSunit
    calc
      ofFullBlockVec (Matrix.mulVec S⁻¹ (Matrix.mulVec S (toFullBlockVec P))) =
          ofFullBlockVec (Matrix.mulVec (S⁻¹ * S) (toFullBlockVec P)) := by
            exact congrArg ofFullBlockVec (Matrix.mulVec_mulVec (toFullBlockVec P) S⁻¹ S)
      _ = ofFullBlockVec (toFullBlockVec P) := by
            rw [Matrix.nonsing_inv_mul S hSdet]
            simp
      _ = P := by simp
  have hQ :
      ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e) =
        blockMatVecMul (constantBlockMatrix a0) P := by
    have hsq : S ^ 2 = M := by
      dsimp [S, M, constantFullBlockMatrixSqrt]
      simpa using CFC.sq_sqrt M hMpos.posSemidef.nonneg
    rw [pow_two] at hsq
    change
      ofFullBlockVec (Matrix.mulVec S (Matrix.mulVec S (toFullBlockVec P))) =
        blockMatVecMul (constantBlockMatrix a0) P
    calc
      ofFullBlockVec (Matrix.mulVec S (Matrix.mulVec S (toFullBlockVec P))) =
          ofFullBlockVec (Matrix.mulVec (S * S) (toFullBlockVec P)) := by
            exact congrArg ofFullBlockVec
              (Matrix.mulVec_mulVec (toFullBlockVec P) S S)
      _ = ofFullBlockVec (Matrix.mulVec M (toFullBlockVec P)) := by rw [hsq]
      _ = blockMatVecMul (ofFullBlockMat M) P := by
            exact ofFullBlockVec_mulVec_toFullBlockVec_eq_blockMatVecMul M P
      _ = blockMatVecMul (constantBlockMatrix a0) P := by
            simp [M, constantFullBlockMatrix]
  simp [hP, hQ]

theorem matrixNorm_le_trace_of_posSemidef {d : ℕ}
    (M : Mat d) (hM : M.PosSemidef) :
    matrixNorm M ≤ Matrix.trace M := by
  classical
  let hHerm : M.IsHermitian := hM.isHermitian
  have heig_nonneg : ∀ i : Fin d, 0 ≤ hHerm.eigenvalues i :=
    hM.eigenvalues_nonneg
  have hsum_nonneg : 0 ≤ ∑ i : Fin d, hHerm.eigenvalues i :=
    Finset.sum_nonneg fun i _hi => heig_nonneg i
  let D : Mat d := Matrix.diagonal hHerm.eigenvalues
  have hspectral : M = Unitary.conjStarAlgAut ℝ _ hHerm.eigenvectorUnitary D := by
    simpa [D] using hHerm.spectral_theorem
  calc
    matrixNorm M = ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) M‖ := rfl
    _ = ‖M‖ := Matrix.l2_opNorm_toEuclideanCLM M
    _ = ‖Unitary.conjStarAlgAut ℝ _ hHerm.eigenvectorUnitary D‖ :=
          congrArg (fun N : Mat d => ‖N‖) hspectral
    _ = ‖D‖ := by
          calc
            ‖Unitary.conjStarAlgAut ℝ _ hHerm.eigenvectorUnitary D‖ =
                ‖(hHerm.eigenvectorUnitary : Mat d) * D *
                  star (hHerm.eigenvectorUnitary : Mat d)‖ := by
                  simp [Unitary.conjStarAlgAut_apply]
            _ = ‖D * star (hHerm.eigenvectorUnitary : Mat d)‖ := by
                  rw [mul_assoc, CStarRing.norm_coe_unitary_mul]
            _ = ‖D * (star hHerm.eigenvectorUnitary : unitary (Mat d))‖ := by
                  simp
            _ = ‖D‖ := by
                  rw [CStarRing.norm_mul_coe_unitary]
    _ = ‖hHerm.eigenvalues‖ := by
          simp [D]
    _ ≤ ∑ i : Fin d, hHerm.eigenvalues i := by
          refine (pi_norm_le_iff_of_nonneg hsum_nonneg).mpr ?_
          intro i
          calc
            ‖hHerm.eigenvalues i‖ = hHerm.eigenvalues i := by
              simp [Real.norm_eq_abs, abs_of_nonneg (heig_nonneg i)]
            _ ≤ ∑ j : Fin d, hHerm.eigenvalues j :=
              Finset.single_le_sum (fun j _hj => heig_nonneg j) (Finset.mem_univ i)
    _ = Matrix.trace M := by
          symm
          simpa using hHerm.trace_eq_sum_eigenvalues

theorem matTranspose_scalarMatrix {d : ℕ} (σ : ℝ) :
    matTranspose (scalarMatrix (d := d) σ) = scalarMatrix (d := d) σ := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [matTranspose, scalarMatrix]
  · have hji : j ≠ i := Ne.symm hij
    simp [matTranspose, scalarMatrix, hij, hji]

theorem symmPart_scalarMatrix {d : ℕ} (σ : ℝ) :
    symmPart (scalarMatrix (d := d) σ) = scalarMatrix (d := d) σ := by
  rw [symmPart_eq_smul_add_transpose, matTranspose_scalarMatrix]
  ext i j
  simp [scalarMatrix]
  ring

theorem skewPart_scalarMatrix {d : ℕ} (σ : ℝ) :
    skewPart (scalarMatrix (d := d) σ) = (0 : Mat d) := by
  rw [skewPart_eq_smul_sub_transpose, matTranspose_scalarMatrix]
  simp

theorem constantBlockMatrix_scalarMatrix {d : ℕ} {σ : ℝ}
    (hσ : 0 < σ) :
    constantBlockMatrix (scalarMatrix (d := d) σ) =
      { upperLeft := scalarMatrix (d := d) σ
        upperRight := 0
        lowerLeft := 0
        lowerRight := scalarMatrix (d := d) σ⁻¹ } := by
  have hInv : ((scalarMatrix (d := d) σ)⁻¹ : Mat d) =
      scalarMatrix (d := d) σ⁻¹ := by
    rw [scalarMatrix, nonsing_inv_smul σ (ne_of_gt hσ) (by simp)]
    simp [scalarMatrix]
  unfold constantBlockMatrix
  rw [BlockMat.mk.injEq]
  constructor
  · ext i j
    simp [symmPart_scalarMatrix, skewPart_scalarMatrix, hInv, scalarMatrix]
  constructor
  · ext i j
    simp [symmPart_scalarMatrix, skewPart_scalarMatrix, hInv, scalarMatrix,
      matTranspose]
  constructor
  · ext i j
    simp [symmPart_scalarMatrix, skewPart_scalarMatrix, hInv, scalarMatrix]
  · ext i j
    simp [symmPart_scalarMatrix, hInv, scalarMatrix]

private theorem blockMatVecMul_constantBlockMatrix_scalarMatrix_probe
    {d : ℕ} {σ : ℝ} (hσ : 0 < σ) (i : Fin d) :
    blockMatVecMul (constantBlockMatrix (scalarMatrix (d := d) σ))
      ((Real.sqrt σ)⁻¹ • Pi.single i 1, 0) =
    (Real.sqrt σ • Pi.single i 1, 0) := by
  rw [constantBlockMatrix_scalarMatrix hσ]
  ext k
  · simp [blockMatVecMul, matVecMul_zero, matVecMul_scalarMatrix]
    by_cases hki : k = i
    · subst k
      simp
      field_simp [Real.sqrt_pos.2 hσ]
      rw [Real.sq_sqrt hσ.le]
    · simp [Pi.single_eq_of_ne hki]
  · simp [blockMatVecMul, matVecMul_zero, matVecMul_scalarMatrix, matVecMul]

private theorem vecDot_single_self_one {d : ℕ} (i : Fin d) :
    vecDot (Pi.single i 1 : Vec d) (Pi.single i 1) = 1 := by
  rw [vecDot, Finset.sum_eq_single i]
  · simp
  · intro j _h hij
    simp [Pi.single_eq_of_ne hij]
  · simp

private theorem scalarCoordinateProbe_constantBlockQuadratic_eq_one
    {d : ℕ} {σ : ℝ} (hσ : 0 < σ) (i : Fin d) :
    blockVecDot ((Real.sqrt σ)⁻¹ • Pi.single i 1, 0)
      (blockMatVecMul (constantBlockMatrix (scalarMatrix (d := d) σ))
        ((Real.sqrt σ)⁻¹ • Pi.single i 1, 0)) = 1 := by
  rw [blockMatVecMul_constantBlockMatrix_scalarMatrix_probe hσ i]
  rw [blockVecDot, vecDot_smul_left, vecDot_smul_right, vecDot_single_self_one]
  simp [vecDot]
  field_simp [Real.sqrt_pos.2 hσ]

theorem doubledResponseJ_scalarCoordinateProbe_le_normalizedBlockResponseMax
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {σ : ℝ} (hσ : 0 < σ)
    (i : Fin d) :
    doubledResponseJ (cubeDomain Q) (a.coeffOn Q)
      ((Real.sqrt σ)⁻¹ • Pi.single i 1, 0)
      (Real.sqrt σ • Pi.single i 1, 0) ≤
    normalizedBlockResponseMax Q a (scalarMatrix (d := d) σ) := by
  let P : BlockVec d := ((Real.sqrt σ)⁻¹ • Pi.single i 1, 0)
  have hquad :
      blockVecDot P
        (blockMatVecMul (constantBlockMatrix (scalarMatrix (d := d) σ)) P) = 1 := by
    simpa [P] using scalarCoordinateProbe_constantBlockQuadratic_eq_one hσ i
  have hmem0 := normalizedBlockResponseValueSet_mem_of_constantBlockQuadratic_eq_one
    (Q := Q) (a := a) (a0 := scalarMatrix (d := d) σ)
    (lam := σ) (Lam := σ) (isEllipticMatrix_scalarMatrix hσ) P hquad
  have hmem :
      doubledResponseJ (cubeDomain Q) (a.coeffOn Q)
        ((Real.sqrt σ)⁻¹ • Pi.single i 1, 0)
        (Real.sqrt σ • Pi.single i 1, 0) ∈
      normalizedBlockResponseValueSet Q a (scalarMatrix (d := d) σ) := by
    simpa [P, blockMatVecMul_constantBlockMatrix_scalarMatrix_probe hσ i] using hmem0
  unfold normalizedBlockResponseMax
  exact le_csSup
    (normalizedBlockResponseValueSet_bddAbove_of_mem_descendantsAtScale
      (a := a) (Q := Q) (R := Q) (k := Q.scale) (scalarMatrix (d := d) σ)
      (by simp [descendantsAtScale_self])) hmem

theorem specialCoordinateBlockJTraceBudget_le_card_mul_normalizedBlockResponseMax
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {σ : ℝ} (hσ : 0 < σ) :
    specialCoordinateBlockJTraceBudget σ
        (coarseBlockMatrix (cubeDomain Q) (a.coeffOn Q)) ≤
      (Fintype.card (Fin d) : ℝ) *
        normalizedBlockResponseMax Q a (scalarMatrix (d := d) σ) := by
  have hcp2 : (Real.sqrt σ)⁻¹ * (Real.sqrt σ)⁻¹ = σ⁻¹ := by
    field_simp [Real.sqrt_pos.2 hσ]
    rw [Real.sq_sqrt hσ.le]
  have hcq2 : Real.sqrt σ * Real.sqrt σ = σ := by
    simpa [pow_two] using Real.sq_sqrt hσ.le
  have hcpq : (Real.sqrt σ)⁻¹ * Real.sqrt σ = 1 := by
    field_simp [Real.sqrt_pos.2 hσ]
  calc
    specialCoordinateBlockJTraceBudget σ
        (coarseBlockMatrix (cubeDomain Q) (a.coeffOn Q))
        =
      ∑ i : Fin d,
        doubledResponseJ (cubeDomain Q) (a.coeffOn Q)
          ((Real.sqrt σ)⁻¹ • Pi.single i 1, 0)
          (Real.sqrt σ • Pi.single i 1, 0) := by
          symm
          exact sum_doubledResponseJ_coordinateScales_eq_specialCoordinateBlockJTraceBudget
            (U := cubeDomain Q) (a := a.coeffOn Q) (σ := σ)
            (cp := (Real.sqrt σ)⁻¹) (cq := Real.sqrt σ) hcp2 hcq2 hcpq
    _ ≤ ∑ _i : Fin d,
        normalizedBlockResponseMax Q a (scalarMatrix (d := d) σ) := by
          exact Finset.sum_le_sum fun i _hi =>
            doubledResponseJ_scalarCoordinateProbe_le_normalizedBlockResponseMax
              Q a hσ i
    _ =
      (Fintype.card (Fin d) : ℝ) *
        normalizedBlockResponseMax Q a (scalarMatrix (d := d) σ) := by
          simp [Finset.sum_const, nsmul_eq_mul]

theorem weightedTrace_coarseBlockMatrix_eq_two_mul_budget_add_card
    {d : ℕ} (U : Domain d) (a : CoeffOn U) (σ : ℝ) :
    σ⁻¹ * Matrix.trace (bCoarse U a) +
        σ * Matrix.trace (sigmaStarInvCoarse U a) =
      2 * (specialCoordinateBlockJTraceBudget σ (coarseBlockMatrix U a) +
        (Fintype.card (Fin d) : ℝ)) := by
  unfold specialCoordinateBlockJTraceBudget
  simp [Matrix.trace, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul]
  have hB :
      (∑ x : Fin d, (2 : ℝ)⁻¹ * (σ⁻¹ * bCoarse U a x x)) =
        (2 : ℝ)⁻¹ * ∑ x : Fin d, σ⁻¹ * bCoarse U a x x := by
    rw [Finset.mul_sum]
  have hS :
      (∑ x : Fin d, (2 : ℝ)⁻¹ * (σ * sigmaStarInvCoarse U a x x)) =
        (2 : ℝ)⁻¹ * ∑ x : Fin d, σ * sigmaStarInvCoarse U a x x := by
    rw [Finset.mul_sum]
  rw [hB, hS]
  rw [Finset.mul_sum, Finset.mul_sum]
  ring

theorem weightedCoarseEllipticityNorm_le_card_mul_normalizedBlockResponseMax_add_one
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {σ : ℝ} (hσ : 0 < σ) :
    σ⁻¹ * coarseBMatrixNorm Q a + σ * coarseSigmaStarInvMatrixNorm Q a ≤
      2 * (Fintype.card (Fin d) : ℝ) *
        (normalizedBlockResponseMax Q a (scalarMatrix (d := d) σ) + 1) := by
  let U : Domain d := cubeDomain Q
  let aQ : CoeffOn U := a.coeffOn Q
  let M : ℝ := normalizedBlockResponseMax Q a (scalarMatrix (d := d) σ)
  have hbTrace :
      coarseBMatrixNorm Q a ≤ Matrix.trace (bCoarse U aQ) := by
    simpa [U, aQ, coarseBMatrixNorm] using
      matrixNorm_le_trace_of_posSemidef (bCoarse U aQ)
        (bCoarse_posSemidef U aQ)
  have hsTrace :
      coarseSigmaStarInvMatrixNorm Q a ≤
        Matrix.trace (sigmaStarInvCoarse U aQ) := by
    simpa [U, aQ, coarseSigmaStarInvMatrixNorm] using
      matrixNorm_le_trace_of_posSemidef (sigmaStarInvCoarse U aQ)
        (sigmaStarInvCoarse_posDef U aQ).posSemidef
  have hnormTrace :
      σ⁻¹ * coarseBMatrixNorm Q a + σ * coarseSigmaStarInvMatrixNorm Q a ≤
        σ⁻¹ * Matrix.trace (bCoarse U aQ) +
          σ * Matrix.trace (sigmaStarInvCoarse U aQ) :=
    add_le_add
      (mul_le_mul_of_nonneg_left hbTrace (inv_nonneg.mpr hσ.le))
      (mul_le_mul_of_nonneg_left hsTrace hσ.le)
  have hbudget :
      specialCoordinateBlockJTraceBudget σ (coarseBlockMatrix U aQ) ≤
        (Fintype.card (Fin d) : ℝ) * M := by
    simpa [U, aQ, M] using
      specialCoordinateBlockJTraceBudget_le_card_mul_normalizedBlockResponseMax
        Q a hσ
  have htrace :
      σ⁻¹ * Matrix.trace (bCoarse U aQ) +
          σ * Matrix.trace (sigmaStarInvCoarse U aQ) ≤
        2 * (Fintype.card (Fin d) : ℝ) * (M + 1) := by
    calc
      σ⁻¹ * Matrix.trace (bCoarse U aQ) +
          σ * Matrix.trace (sigmaStarInvCoarse U aQ)
          =
        2 * (specialCoordinateBlockJTraceBudget σ (coarseBlockMatrix U aQ) +
          (Fintype.card (Fin d) : ℝ)) :=
            weightedTrace_coarseBlockMatrix_eq_two_mul_budget_add_card U aQ σ
      _ ≤ 2 * ((Fintype.card (Fin d) : ℝ) * M +
          (Fintype.card (Fin d) : ℝ)) := by
            nlinarith
      _ = 2 * (Fintype.card (Fin d) : ℝ) * (M + 1) := by
            ring
  exact hnormTrace.trans htrace

theorem inv_mul_coarseBMatrixNorm_le_card_mul_normalizedBlockResponseMax_add_one
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {σ : ℝ} (hσ : 0 < σ) :
    σ⁻¹ * coarseBMatrixNorm Q a ≤
      2 * (Fintype.card (Fin d) : ℝ) *
        (normalizedBlockResponseMax Q a (scalarMatrix (d := d) σ) + 1) := by
  have htotal :=
    weightedCoarseEllipticityNorm_le_card_mul_normalizedBlockResponseMax_add_one
      Q a hσ
  have hlower_nonneg : 0 ≤ σ * coarseSigmaStarInvMatrixNorm Q a :=
    mul_nonneg hσ.le (coarseSigmaStarInvMatrixNorm_nonneg Q a)
  nlinarith

theorem sigma_mul_coarseSigmaStarInvMatrixNorm_le_card_mul_normalizedBlockResponseMax_add_one
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {σ : ℝ} (hσ : 0 < σ) :
    σ * coarseSigmaStarInvMatrixNorm Q a ≤
      2 * (Fintype.card (Fin d) : ℝ) *
        (normalizedBlockResponseMax Q a (scalarMatrix (d := d) σ) + 1) := by
  have htotal :=
    weightedCoarseEllipticityNorm_le_card_mul_normalizedBlockResponseMax_add_one
      Q a hσ
  have hupper_nonneg : 0 ≤ σ⁻¹ * coarseBMatrixNorm Q a :=
    mul_nonneg (inv_nonneg.mpr hσ.le) (coarseBMatrixNorm_nonneg Q a)
  nlinarith

theorem inv_mul_maxDescendantBMatrixNormAtScale_le_card_mul_maxResponse_add_one
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (a : TriadicCoeffFamily d) {σ : ℝ} (hσ : 0 < σ) :
    σ⁻¹ * maxDescendantBMatrixNormAtScale Q k a ≤
      2 * (Fintype.card (Fin d) : ℝ) *
        (maxDescendantNormalizedBlockResponseAtScale Q k a
          (scalarMatrix (d := d) σ) + 1) := by
  let C : ℝ :=
    2 * (Fintype.card (Fin d) : ℝ) *
      (maxDescendantNormalizedBlockResponseAtScale Q k a
        (scalarMatrix (d := d) σ) + 1)
  have hD : (descendantsAtScale Q k).Nonempty :=
    descendantsAtScale_nonempty Q hk
  have hpoint :
      ∀ R ∈ descendantsAtScale Q k, coarseBMatrixNorm R a ≤ σ * C := by
    intro R hR
    have hRone :=
      inv_mul_coarseBMatrixNorm_le_card_mul_normalizedBlockResponseMax_add_one
        R a hσ
    have hMle :
        normalizedBlockResponseMax R a (scalarMatrix (d := d) σ) ≤
          maxDescendantNormalizedBlockResponseAtScale Q k a
            (scalarMatrix (d := d) σ) :=
      normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale
        a (scalarMatrix (d := d) σ) hR
    have hcoef_nonneg : 0 ≤ 2 * (Fintype.card (Fin d) : ℝ) := by
      positivity
    have hRleC : σ⁻¹ * coarseBMatrixNorm R a ≤ C := by
      dsimp [C]
      exact hRone.trans
        (mul_le_mul_of_nonneg_left (by linarith : _ ≤ _) hcoef_nonneg)
    exact (inv_mul_le_iff₀ hσ).mp hRleC
  have hsup :
      maxDescendantBMatrixNormAtScale Q k a ≤ σ * C := by
    simpa [maxDescendantBMatrixNormAtScale] using
      finsetSupReal_le (descendantsAtScale Q k) hD hpoint
  calc
    σ⁻¹ * maxDescendantBMatrixNormAtScale Q k a ≤ σ⁻¹ * (σ * C) :=
      mul_le_mul_of_nonneg_left hsup (inv_nonneg.mpr hσ.le)
    _ = C := by
      field_simp [hσ.ne']

theorem sigma_mul_maxDescendantSigmaStarInvMatrixNormAtScale_le_card_mul_maxResponse_add_one
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (a : TriadicCoeffFamily d) {σ : ℝ} (hσ : 0 < σ) :
    σ * maxDescendantSigmaStarInvMatrixNormAtScale Q k a ≤
      2 * (Fintype.card (Fin d) : ℝ) *
        (maxDescendantNormalizedBlockResponseAtScale Q k a
          (scalarMatrix (d := d) σ) + 1) := by
  let C : ℝ :=
    2 * (Fintype.card (Fin d) : ℝ) *
      (maxDescendantNormalizedBlockResponseAtScale Q k a
        (scalarMatrix (d := d) σ) + 1)
  have hD : (descendantsAtScale Q k).Nonempty :=
    descendantsAtScale_nonempty Q hk
  have hpoint :
      ∀ R ∈ descendantsAtScale Q k,
        coarseSigmaStarInvMatrixNorm R a ≤ σ⁻¹ * C := by
    intro R hR
    have hRone :=
      sigma_mul_coarseSigmaStarInvMatrixNorm_le_card_mul_normalizedBlockResponseMax_add_one
        R a hσ
    have hMle :
        normalizedBlockResponseMax R a (scalarMatrix (d := d) σ) ≤
          maxDescendantNormalizedBlockResponseAtScale Q k a
            (scalarMatrix (d := d) σ) :=
      normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale
        a (scalarMatrix (d := d) σ) hR
    have hcoef_nonneg : 0 ≤ 2 * (Fintype.card (Fin d) : ℝ) := by
      positivity
    have hRleC : σ * coarseSigmaStarInvMatrixNorm R a ≤ C := by
      dsimp [C]
      exact hRone.trans
        (mul_le_mul_of_nonneg_left (by linarith : _ ≤ _) hcoef_nonneg)
    exact (le_inv_mul_iff₀ hσ).mpr hRleC
  have hsup :
      maxDescendantSigmaStarInvMatrixNormAtScale Q k a ≤ σ⁻¹ * C := by
    simpa [maxDescendantSigmaStarInvMatrixNormAtScale] using
      finsetSupReal_le (descendantsAtScale Q k) hD hpoint
  calc
    σ * maxDescendantSigmaStarInvMatrixNormAtScale Q k a ≤ σ * (σ⁻¹ * C) :=
      mul_le_mul_of_nonneg_left hsup hσ.le
    _ = C := by
      field_simp [hσ.ne']

theorem summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) (a0 : Mat d)
    {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ =>
      geometricWeight s 2 n *
        maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (n : ℤ)) a a0) := by
  refine Homogenization.summable_geometricWeight_mul_of_nonneg_of_le
    (s := s) (q := 2) (C := normalizedBlockResponseUniformBound Q a a0)
    (by nlinarith : 0 < s * (2 : ℝ)) ?_ ?_
  · intro n
    have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    exact maxDescendantNormalizedBlockResponseAtScale_nonneg Q
      (sub_le_self Q.scale hn) a a0
  · intro n
    have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    exact maxDescendantNormalizedBlockResponseAtScale_le_uniform Q
      (sub_le_self Q.scale hn) a a0

theorem tsum_geometricWeight_two_mul_maxResponse_add_one_eq_homogenizationError_sq_add_one
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) (a0 : Mat d)
    {s : ℝ} (hs : 0 < s) :
    (∑' n : ℕ,
      geometricWeight s 2 n *
        (maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (n : ℤ)) a a0 + 1)) =
      (HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0) ^ 2 + 1 := by
  let M : ℕ → ℝ := fun n =>
    maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (n : ℤ)) a a0
  let w : ℕ → ℝ := fun n => geometricWeight s 2 n
  have hsumM : Summable (fun n : ℕ => w n * M n) := by
    simpa [w, M] using
      summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
        Q a a0 hs
  have hsumW : Summable w := by
    simpa [w, geometricWeight_eq_old] using
      Homogenization.summable_geometricWeight (s := s) (q := 2)
        (by nlinarith : 0 < s * (2 : ℝ))
  calc
    (∑' n : ℕ,
        geometricWeight s 2 n *
          (maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (n : ℤ)) a a0 + 1))
        = ∑' n : ℕ, (w n * M n + w n) := by
          congr with n
          simp [w, M]
          ring
    _ = (∑' n : ℕ, w n * M n) + ∑' n : ℕ, w n := by
          exact hsumM.tsum_add hsumW
    _ = (HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0) ^ 2 + 1 := by
          rw [homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q hs a a0]
          rw [show (∑' n : ℕ, w n) = 1 by
            simpa [w, geometricWeight_eq_old] using
              Homogenization.tsum_geometricWeight_eq_one (s := s) (q := 2)
                (by nlinarith : 0 < s * (2 : ℝ))]

theorem inv_mul_LambdaSq_finite_two_le_card_mul_homogenizationError_sq_add_one
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d)
    {s σ : ℝ} (hs : 0 < s) (hσ : 0 < σ) :
    σ⁻¹ * LambdaSq Q s (.finite 2) a ≤
      2 * (Fintype.card (Fin d) : ℝ) *
        ((HomogenizationErrorOnCube Q s .infinity (.finite 2) a
          (scalarMatrix (d := d) σ)) ^ 2 + 1) := by
  let B : ℕ → ℝ := fun n =>
    maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a
  let M : ℕ → ℝ := fun n =>
    maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (n : ℤ)) a
      (scalarMatrix (d := d) σ)
  let w : ℕ → ℝ := fun n => geometricWeight s 2 n
  let C : ℝ := 2 * (Fintype.card (Fin d) : ℝ)
  have hLambda_eq : LambdaSq Q s (.finite 2) a = ∑' n : ℕ, w n * B n := by
    have h := LambdaSqFinite_rpow_q_div_two_eq_tsum Q s 2 a
      (by norm_num : (0 : ℝ) < 2) (by nlinarith : 0 ≤ s * (2 : ℝ))
    simpa [w, B, Real.rpow_one] using h
  have hsumB : Summable (fun n : ℕ => w n * B n) := by
    have h := summable_B_series_pointwiseCoeffField Q a hs
      (by norm_num : (0 : ℝ) < 2)
    simpa [w, B, Real.rpow_one] using h
  have hsumR : Summable (fun n : ℕ => w n * (M n + 1)) := by
    have hsumM : Summable (fun n : ℕ => w n * M n) := by
      simpa [w, M] using
        summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
          Q a (scalarMatrix (d := d) σ) hs
    have hsumW : Summable w := by
      simpa [w, geometricWeight_eq_old] using
        Homogenization.summable_geometricWeight (s := s) (q := 2)
          (by nlinarith : 0 < s * (2 : ℝ))
    have hsumAdd := hsumM.add hsumW
    simpa [mul_add, w, M] using hsumAdd
  have hterm : ∀ n : ℕ, σ⁻¹ * (w n * B n) ≤ C * (w n * (M n + 1)) := by
    intro n
    have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    have hscale :=
      inv_mul_maxDescendantBMatrixNormAtScale_le_card_mul_maxResponse_add_one
        (Q := Q) (k := Q.scale - (n : ℤ)) (sub_le_self Q.scale hn) a hσ
    have hw_nonneg : 0 ≤ w n := by
      simpa [w, geometricWeight_eq_old] using
        Homogenization.geometricWeight_nonneg (s := s) (q := 2) n
          (by nlinarith : 0 ≤ s * (2 : ℝ))
    dsimp [C, B, M, w] at hscale ⊢
    calc
      σ⁻¹ * (geometricWeight s 2 n *
          maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
          =
        geometricWeight s 2 n *
          (σ⁻¹ * maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) := by
            ring
      _ ≤
        geometricWeight s 2 n *
          (2 * (Fintype.card (Fin d) : ℝ) *
            (maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (n : ℤ)) a
              (scalarMatrix σ) + 1)) :=
            mul_le_mul_of_nonneg_left hscale hw_nonneg
      _ =
        2 * (Fintype.card (Fin d) : ℝ) *
          (geometricWeight s 2 n *
            (maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (n : ℤ)) a
              (scalarMatrix σ) + 1)) := by
            ring
  calc
    σ⁻¹ * LambdaSq Q s (.finite 2) a
        = ∑' n : ℕ, σ⁻¹ * (w n * B n) := by
          rw [hLambda_eq]
          exact (hsumB.tsum_mul_left σ⁻¹).symm
    _ ≤ ∑' n : ℕ, C * (w n * (M n + 1)) := by
          exact (hsumB.mul_left σ⁻¹).tsum_le_tsum hterm
            (hsumR.mul_left C)
    _ = C * (∑' n : ℕ, w n * (M n + 1)) := by
          exact hsumR.tsum_mul_left C
    _ = C * ((HomogenizationErrorOnCube Q s .infinity (.finite 2) a
          (scalarMatrix (d := d) σ)) ^ 2 + 1) := by
          rw [tsum_geometricWeight_two_mul_maxResponse_add_one_eq_homogenizationError_sq_add_one
            Q a (scalarMatrix (d := d) σ) hs]

theorem sigma_mul_lambdaSq_finite_two_inv_le_card_mul_homogenizationError_sq_add_one
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d)
    {s σ : ℝ} (hs : 0 < s) (hσ : 0 < σ) :
    σ * (lambdaSq Q s (.finite 2) a)⁻¹ ≤
      2 * (Fintype.card (Fin d) : ℝ) *
        ((HomogenizationErrorOnCube Q s .infinity (.finite 2) a
          (scalarMatrix (d := d) σ)) ^ 2 + 1) := by
  let S : ℕ → ℝ := fun n =>
    maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a
  let M : ℕ → ℝ := fun n =>
    maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (n : ℤ)) a
      (scalarMatrix (d := d) σ)
  let w : ℕ → ℝ := fun n => geometricWeight s 2 n
  let C : ℝ := 2 * (Fintype.card (Fin d) : ℝ)
  have hlambda_eq : (lambdaSq Q s (.finite 2) a)⁻¹ = ∑' n : ℕ, w n * S n := by
    have h := lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q s 2 a
      (by norm_num : (0 : ℝ) < 2) (by nlinarith : 0 ≤ s * (2 : ℝ))
    simpa [w, S, Real.rpow_one, Real.rpow_neg_one] using h
  have hsumS : Summable (fun n : ℕ => w n * S n) := by
    have h := summable_sigmaStarInv_series_pointwiseCoeffField Q a hs
      (by norm_num : (0 : ℝ) < 2)
    simpa [w, S, Real.rpow_one] using h
  have hsumR : Summable (fun n : ℕ => w n * (M n + 1)) := by
    have hsumM : Summable (fun n : ℕ => w n * M n) := by
      simpa [w, M] using
        summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
          Q a (scalarMatrix (d := d) σ) hs
    have hsumW : Summable w := by
      simpa [w, geometricWeight_eq_old] using
        Homogenization.summable_geometricWeight (s := s) (q := 2)
          (by nlinarith : 0 < s * (2 : ℝ))
    have hsumAdd := hsumM.add hsumW
    simpa [mul_add, w, M] using hsumAdd
  have hterm : ∀ n : ℕ, σ * (w n * S n) ≤ C * (w n * (M n + 1)) := by
    intro n
    have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    have hscale :=
      sigma_mul_maxDescendantSigmaStarInvMatrixNormAtScale_le_card_mul_maxResponse_add_one
        (Q := Q) (k := Q.scale - (n : ℤ)) (sub_le_self Q.scale hn) a hσ
    have hw_nonneg : 0 ≤ w n := by
      simpa [w, geometricWeight_eq_old] using
        Homogenization.geometricWeight_nonneg (s := s) (q := 2) n
          (by nlinarith : 0 ≤ s * (2 : ℝ))
    dsimp [C, S, M, w] at hscale ⊢
    calc
      σ * (geometricWeight s 2 n *
          maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
          =
        geometricWeight s 2 n *
          (σ * maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) a) := by
            ring
      _ ≤
        geometricWeight s 2 n *
          (2 * (Fintype.card (Fin d) : ℝ) *
            (maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (n : ℤ)) a
              (scalarMatrix σ) + 1)) :=
            mul_le_mul_of_nonneg_left hscale hw_nonneg
      _ =
        2 * (Fintype.card (Fin d) : ℝ) *
          (geometricWeight s 2 n *
            (maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (n : ℤ)) a
              (scalarMatrix σ) + 1)) := by
            ring
  calc
    σ * (lambdaSq Q s (.finite 2) a)⁻¹
        = ∑' n : ℕ, σ * (w n * S n) := by
          rw [hlambda_eq]
          exact (hsumS.tsum_mul_left σ).symm
    _ ≤ ∑' n : ℕ, C * (w n * (M n + 1)) := by
          exact (hsumS.mul_left σ).tsum_le_tsum hterm
            (hsumR.mul_left C)
    _ = C * (∑' n : ℕ, w n * (M n + 1)) := by
          exact hsumR.tsum_mul_left C
    _ = C * ((HomogenizationErrorOnCube Q s .infinity (.finite 2) a
          (scalarMatrix (d := d) σ)) ^ 2 + 1) := by
          rw [tsum_geometricWeight_two_mul_maxResponse_add_one_eq_homogenizationError_sq_add_one
            Q a (scalarMatrix (d := d) σ) hs]

theorem max_weightedEllipticity_finite_two_le_card_mul_homogenizationError_sq_add_one
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d)
    {s σ : ℝ} (hs : 0 < s) (hσ : 0 < σ) :
    max (σ⁻¹ * LambdaSq Q s (.finite 2) a)
        (σ * (lambdaSq Q s (.finite 2) a)⁻¹) ≤
      2 * (Fintype.card (Fin d) : ℝ) *
        ((HomogenizationErrorOnCube Q s .infinity (.finite 2) a
          (scalarMatrix (d := d) σ)) ^ 2 + 1) := by
  exact max_le
    (inv_mul_LambdaSq_finite_two_le_card_mul_homogenizationError_sq_add_one
      Q a hs hσ)
    (sigma_mul_lambdaSq_finite_two_inv_le_card_mul_homogenizationError_sq_add_one
      Q a hs hσ)

theorem weightedEllipticity_finite_two_le_card_mul_homogenizationError_sq_add_one
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d)
    {s σ : ℝ} (hs : 0 < s) (hσ : 0 < σ) :
    σ⁻¹ * LambdaSq Q s (.finite 2) a +
        σ * (lambdaSq Q s (.finite 2) a)⁻¹ ≤
      4 * (Fintype.card (Fin d) : ℝ) *
        ((HomogenizationErrorOnCube Q s .infinity (.finite 2) a
          (scalarMatrix (d := d) σ)) ^ 2 + 1) := by
  have hupper :=
    inv_mul_LambdaSq_finite_two_le_card_mul_homogenizationError_sq_add_one
      Q a hs hσ
  have hlower :=
    sigma_mul_lambdaSq_finite_two_inv_le_card_mul_homogenizationError_sq_add_one
      Q a hs hσ
  nlinarith

end

end Ch02
end Book
end Homogenization
