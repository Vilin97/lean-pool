/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.Response
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.Existence
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.HodgeCubeBridge
import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMetric

/-! # Private Lemmas -/

namespace Homogenization

noncomputable section

open scoped BigOperators MatrixOrder Pointwise

/-!
# Deterministic coarse-grained flux-response inequalities

This file packages the Chapter-3 `q = 1` weak-norm estimate for the coarse
flux defect under an explicit one-cube response hypothesis.

At the current checkpoint we isolate the genuinely local linear-response input
from the downstream multiscale summation argument. The local hypothesis is the
square bound on descendant cube averages that the note proof produces on each
cube, and the main theorem turns it into a note-normalized negative Besov
seminorm estimate with `HomogenizationErrorOnCube`.
-/

private theorem ofFullBlockVec_mulVec_toFullBlockVec_eq_blockMatVecMul {d : ℕ}
    (M : FullBlockMat d) (P : BlockVec d) :
    ofFullBlockVec (Matrix.mulVec M (toFullBlockVec P)) =
      blockMatVecMul (ofFullBlockMat M) P := by
  simpa using
    (congrArg ofFullBlockVec
      (toFullBlockVec_blockMatVecMul (A := ofFullBlockMat M) P)).symm

private theorem blockMatVecMul_ofFullBlockMat_mul {d : ℕ}
    (M N : FullBlockMat d) (P : BlockVec d) :
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

private theorem blockVecDot_self_eq_zero {d : ℕ} {P : BlockVec d}
    (hP : blockVecDot P P = 0) :
    P = 0 := by
  rcases P with ⟨p, q⟩
  have hpq : vecNormSq p + vecNormSq q = 0 := by
    simpa [blockVecDot, vecNormSq] using hP
  have hp : vecNormSq p = 0 := by
    nlinarith [vecNormSq_nonneg p, vecNormSq_nonneg q, hpq]
  have hq : vecNormSq q = 0 := by
    nlinarith [vecNormSq_nonneg p, vecNormSq_nonneg q, hpq]
  ext i <;> simp [vecNormSq_eq_zero hp, vecNormSq_eq_zero hq]

theorem symmPart_eq_of_isSymm {d : ℕ} {A : Mat d} (hA : A.IsSymm) :
    symmPart A = A := by
  ext i j
  have hAij : A j i = A i j := (Matrix.IsSymm.ext_iff.mp hA) i j
  simp [symmPart, hAij]

private theorem blockJValueSet_homogeneous {d : ℕ} (U : Set (Vec d)) (P Q : BlockVec d)
    (a : CoeffField d) {c : ℝ} (hc : c ≠ 0) :
    blockJValueSet U (c • P) (c • Q) a = (c ^ 2 : ℝ) • blockJValueSet U P Q a := by
  ext m
  constructor
  · intro hm
    change ∃ y, y ∈ blockJValueSet U P Q a ∧ (c ^ 2 : ℝ) * y = m
    have hm' : (c⁻¹ : ℝ) ^ 2 * m ∈ blockJValueSet U P Q a := by
      simpa [smul_smul, hc, pow_two] using
        (blockResponse_blockJValueSet_smul_mem (P := c • P) (Q := c • Q) hm c⁻¹)
    refine ⟨(c⁻¹ : ℝ) ^ 2 * m, hm', ?_⟩
    field_simp [hc]
  · rintro ⟨m', hm', rfl⟩
    simpa [smul_eq_mul] using blockResponse_blockJValueSet_smul_mem hm' c

private theorem blockJ_homogeneous {d : ℕ} (U : Set (Vec d)) (P Q : BlockVec d)
    (a : CoeffField d) {c : ℝ} (hc : c ≠ 0) :
    BlockJ U (c • P) (c • Q) a = c ^ 2 * BlockJ U P Q a := by
  rw [BlockJ, blockJValueSet_homogeneous U P Q a hc]
  simpa [smul_eq_mul] using!
    (Real.sSup_smul_of_nonneg (show 0 ≤ (c ^ 2 : ℝ) by positivity)
      (blockJValueSet U P Q a))

private theorem blockJ_zero_zero_eq_zero_of_isEllipticFieldOn {d : ℕ}
    (R : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet R) a) :
    BlockJ (cubeSet R) 0 0 a = 0 := by
  have hnonneg : 0 ≤ BlockJ (cubeSet R) 0 0 a :=
    blockJ_nonneg (cubeSet R) 0 0 a
  have hvol : (MeasureTheory.volume (cubeSet R)).toReal ≠ 0 := by
    rw [volume_cubeSet_toReal]
    exact (cubeVolume_pos R).ne'
  have hle :
      BlockJ (cubeSet R) (0 : BlockVec d) (0 : BlockVec d) a ≤
        blockResponsePlainUpperBound (d := d) lam Lam (0 : BlockVec d) (0 : BlockVec d) := by
    exact blockJ_le_plainUpperBound_of_isEllipticFieldOn
      (a := a) (U := cubeSet R) (measurableSet_cubeSet R) hEll hvol 0 0
  have hbound :
      blockResponsePlainUpperBound (d := d) lam Lam (0 : BlockVec d) (0 : BlockVec d) = 0 := by
    simp [blockResponsePlainUpperBound, blockVecDot, vecDot_zero_right]
  have hle0 : BlockJ (cubeSet R) 0 0 a ≤ 0 := by
    simpa [hbound] using hle
  linarith

private theorem constantFullBlockMatrix_posDef_of_isEllipticMatrix {d : ℕ}
    {lam Lam : ℝ} {a0 : Mat d} (ha0 : IsEllipticMatrix lam Lam a0) :
    (constantFullBlockMatrix a0).PosDef := by
  classical
  let M := constantFullBlockMatrix a0
  have hsymm : M.IsSymm := by
    dsimp [M, constantFullBlockMatrix]
    simpa using isSymm_toFullBlockMat_of_isSymmetricBlockMat
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
        0 < blockVecDot X (blockMatVecMul (blockMatrixOfCoeff a0) X) :=
      blockMatrixOfCoeff_quadratic_pos_of_isEllipticMatrix ha0 hX
    have hdot :
        0 < dotProduct (toFullBlockVec X)
          (Matrix.mulVec (constantFullBlockMatrix a0) (toFullBlockVec X)) := by
      have hEq :
          dotProduct (toFullBlockVec X)
              (Matrix.mulVec (toFullBlockMat (blockMatrixOfCoeff a0)) (toFullBlockVec X)) =
            blockVecDot X (blockMatVecMul (blockMatrixOfCoeff a0) X) := by
        rw [← dotProduct_toFullBlockVec X (blockMatVecMul (blockMatrixOfCoeff a0) X)]
        simp [toFullBlockVec_blockMatVecMul]
      have :
          0 < dotProduct (toFullBlockVec X)
            (Matrix.mulVec (toFullBlockMat (blockMatrixOfCoeff a0)) (toFullBlockVec X)) := by
        rwa [hEq]
      simpa [constantFullBlockMatrix] using this
    simpa [M, X] using hdot

private theorem constantFullBlockMatrixSqrt_isSymm {d : ℕ} (a0 : Mat d) :
    (constantFullBlockMatrixSqrt a0).IsSymm := by
  let M := constantFullBlockMatrix a0
  have hpsd : (constantFullBlockMatrixSqrt a0).PosSemidef := by
    dsimp [constantFullBlockMatrixSqrt, M]
    exact (Matrix.nonneg_iff_posSemidef (A := CFC.sqrt M)).mp (CFC.sqrt_nonneg M)
  simpa [Matrix.IsHermitian, Matrix.IsSymm] using hpsd.isHermitian

private theorem fullBlockVecNormSq_constantFullBlockMatrixSqrt_mul_toFullBlockVec_eq {d : ℕ}
    {a0 : Mat d} {lam Lam : ℝ} (ha0 : IsEllipticMatrix lam Lam a0) (P : BlockVec d) :
    fullBlockVecNormSq
        (Matrix.mulVec (constantFullBlockMatrixSqrt a0) (toFullBlockVec P)) =
      blockVecDot P (blockMatVecMul (blockMatrixOfCoeff a0) P) := by
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
    _ = blockVecDot P (blockMatVecMul (blockMatrixOfCoeff a0) P) := by
          let M := constantFullBlockMatrix a0
          have hMpos : M.PosDef := constantFullBlockMatrix_posDef_of_isEllipticMatrix
            (a0 := a0) ha0
          have hsq : S ^ 2 = M := by
            dsimp [S, M, constantFullBlockMatrixSqrt]
            simpa using CFC.sq_sqrt M hMpos.posSemidef.nonneg
          rw [pow_two] at hsq
          rw [hsq]
          simp [M, constantFullBlockMatrix]

private theorem normalizedBlockResponseValueSet_mem_of_blockQuadratic_eq_one {d : ℕ}
    (R : TriadicCube d) (a : CoeffField d) {a0 : Mat d} {lam Lam : ℝ}
    (ha0 : IsEllipticMatrix lam Lam a0) (P : BlockVec d)
    (hquad :
      blockVecDot P (blockMatVecMul (blockMatrixOfCoeff a0) P) = 1) :
    BlockJ (cubeSet R) P (blockMatVecMul (blockMatrixOfCoeff a0) P) a ∈
      normalizedBlockResponseValueSet R a a0 := by
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
        blockMatVecMul (blockMatrixOfCoeff a0) P := by
    have hsq : S ^ 2 = M := by
      dsimp [S, M, constantFullBlockMatrixSqrt]
      simpa using CFC.sq_sqrt M hMpos.posSemidef.nonneg
    rw [pow_two] at hsq
    change
      ofFullBlockVec (Matrix.mulVec S (Matrix.mulVec S (toFullBlockVec P))) =
        blockMatVecMul (blockMatrixOfCoeff a0) P
    calc
      ofFullBlockVec (Matrix.mulVec S (Matrix.mulVec S (toFullBlockVec P))) =
          ofFullBlockVec (Matrix.mulVec (S * S) (toFullBlockVec P)) := by
            exact congrArg ofFullBlockVec
              (Matrix.mulVec_mulVec (toFullBlockVec P) S S)
      _ = ofFullBlockVec (Matrix.mulVec M (toFullBlockVec P)) := by rw [hsq]
      _ = blockMatVecMul (ofFullBlockMat M) P := by
            exact ofFullBlockVec_mulVec_toFullBlockVec_eq_blockMatVecMul M P
      _ = blockMatVecMul (blockMatrixOfCoeff a0) P := by
            simp [M, constantFullBlockMatrix]
  simp [hP, hQ]

theorem blockJ_le_normalizedBlockResponseMax_mul_blockQuadratic_of_isEllipticMatrix {d : ℕ}
    (R : TriadicCube d) (a : CoeffField d) (a0 : Mat d) {lam Lam lam0 Lam0 : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet R) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0) (P : BlockVec d) :
    BlockJ (cubeSet R) P (blockMatVecMul (blockMatrixOfCoeff a0) P) a ≤
      normalizedBlockResponseMax R a a0 *
        blockVecDot P (blockMatVecMul (blockMatrixOfCoeff a0) P) := by
  let t := blockVecDot P (blockMatVecMul (blockMatrixOfCoeff a0) P)
  have hcoeff_pos : 0 < lam0 / (1 + 2 * Lam0 ^ 2) := by
    rcases ha0 with ⟨hlam_pos, -, -, -⟩
    positivity
  have hcoeff_nonneg : 0 ≤ lam0 / (1 + 2 * Lam0 ^ 2) := by
    exact le_of_lt hcoeff_pos
  have ht_nonneg : 0 ≤ t := by
    have hcoerc := blockMatrixOfCoeff_coercive_of_isEllipticMatrix (A := a0) ha0 P
    exact le_trans (mul_nonneg hcoeff_nonneg (blockVecDot_nonneg P)) hcoerc
  by_cases ht : t = 0
  · have hzero_norm : blockVecDot P P = 0 := by
      have hcoerc := blockMatrixOfCoeff_coercive_of_isEllipticMatrix (A := a0) ha0 P
      by_contra hnorm
      have hnorm_ne : blockVecDot P P ≠ 0 := by
        simpa [eq_comm] using hnorm
      have hnorm_pos : 0 < blockVecDot P P := by
        exact lt_of_le_of_ne (blockVecDot_nonneg P) (by simpa [eq_comm] using hnorm_ne)
      nlinarith
    have hP0 : P = 0 := blockVecDot_self_eq_zero hzero_norm
    have hblock0 :
        BlockJ (cubeSet R) 0 0 a = 0 :=
      blockJ_zero_zero_eq_zero_of_isEllipticFieldOn R a hEll
    have hQzero : blockMatVecMul (blockMatrixOfCoeff a0) (0 : BlockVec d) = 0 := by
      ext <;> simp [blockMatVecMul, matVecMul]
    rw [hP0, hQzero, hblock0]
    have hmax_nonneg : 0 ≤ normalizedBlockResponseMax R a a0 := normalizedBlockResponseMax_nonneg R a a0
    have hrhs_nonneg : 0 ≤ normalizedBlockResponseMax R a a0 * blockVecDot (0 : BlockVec d) 0 := by
      exact mul_nonneg hmax_nonneg (blockVecDot_nonneg 0)
    nlinarith
  · have ht_pos : 0 < t := lt_of_le_of_ne ht_nonneg (by simpa [eq_comm] using ht)
    let c : ℝ := Real.sqrt t
    have hc_ne : c ≠ 0 := by
      exact Real.sqrt_ne_zero'.2 ht_pos
    let P' : BlockVec d := c⁻¹ • P
    have hquad_one :
        blockVecDot P' (blockMatVecMul (blockMatrixOfCoeff a0) P') = 1 := by
      dsimp [P', c, t]
      rw [blockMatVecMul_smul, blockVecDot_smul_left, blockVecDot_smul_right]
      have hsq : Real.sqrt t ^ 2 = t := by
        exact Real.sq_sqrt ht_nonneg
      calc
        (Real.sqrt t)⁻¹ * ((Real.sqrt t)⁻¹ * blockVecDot P (blockMatVecMul (blockMatrixOfCoeff a0) P))
            = ((Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹) * t := by ring
        _ = 1 := by
            have hmul_ne : Real.sqrt t * Real.sqrt t ≠ 0 := mul_ne_zero hc_ne hc_ne
            refine (mul_right_cancel₀ hmul_ne) ?_
            calc
              (((Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹) * t) * (Real.sqrt t * Real.sqrt t) = t := by
                field_simp [hc_ne]
              _ = 1 * (Real.sqrt t * Real.sqrt t) := by
                nlinarith [hsq]
    have hmem :
        BlockJ (cubeSet R) P' (blockMatVecMul (blockMatrixOfCoeff a0) P') a ∈
          normalizedBlockResponseValueSet R a a0 :=
      normalizedBlockResponseValueSet_mem_of_blockQuadratic_eq_one
        R a ha0 P' hquad_one
    have hunit :
        BlockJ (cubeSet R) P' (blockMatVecMul (blockMatrixOfCoeff a0) P') a ≤
          normalizedBlockResponseMax R a a0 := by
      unfold normalizedBlockResponseMax
      exact le_csSup
        (normalizedBlockResponseValueSet_bddAbove_of_isEllipticFieldOn R a a0 hEll) hmem
    have hscale :
        BlockJ (cubeSet R) P (blockMatVecMul (blockMatrixOfCoeff a0) P) a =
          c ^ 2 *
            BlockJ (cubeSet R) P' (blockMatVecMul (blockMatrixOfCoeff a0) P') a := by
      have hhom :=
        blockJ_homogeneous (U := cubeSet R) (P := P')
          (Q := blockMatVecMul (blockMatrixOfCoeff a0) P') a (c := c) hc_ne
      simpa [P', blockMatVecMul_smul, smul_smul, hc_ne] using hhom
    calc
      BlockJ (cubeSet R) P (blockMatVecMul (blockMatrixOfCoeff a0) P) a =
          c ^ 2 * BlockJ (cubeSet R) P' (blockMatVecMul (blockMatrixOfCoeff a0) P') a :=
            hscale
      _ ≤ c ^ 2 * normalizedBlockResponseMax R a a0 := by
            exact mul_le_mul_of_nonneg_left hunit (by positivity)
      _ = normalizedBlockResponseMax R a a0 * t := by
            have hsq : c ^ 2 = t := by
              dsimp [c]
              exact Real.sq_sqrt ht_nonneg
            rw [hsq]
            ring

end

end Homogenization
