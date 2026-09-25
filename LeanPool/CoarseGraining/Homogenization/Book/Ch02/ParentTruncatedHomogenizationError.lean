/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.CoeffRestriction
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError.ResponseBounds
public import LeanPool.CoarseGraining.Homogenization.Ambient.ScalarMatrix
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.UnitCubeEuclideanL2

/-! # Parent Truncated Homogenization Error -/

@[expose] public section

open scoped BigOperators ENNReal MatrixOrder Matrix.Norms.Frobenius

namespace Homogenization
namespace Book.Ch02

noncomputable section

private noncomputable def normalizedBlockResponseESetOnCube {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffOn (cubeDomain Q))
    (a0 : Mat d) : Set ℝ≥0∞ :=
  {y | ∃ e : FullBlockVec d, fullBlockVecNormSq e = 1 ∧
    y = ENNReal.ofReal
      (doubledResponseJ (cubeDomain Q) a
        (ofFullBlockVec
          (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e))
        (ofFullBlockVec
          (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e)))}

private noncomputable def normalizedBlockResponseEMaxOnCube {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffOn (cubeDomain Q))
    (a0 : Mat d) : ℝ≥0∞ :=
  sSup (normalizedBlockResponseESetOnCube Q a a0)

private noncomputable def parentMaxNormalizedBlockResponseAtScale {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (k : ℤ) (hk : k ≤ Q.scale)
    (a : CoeffOn (cubeDomain Q)) (a0 : Mat d) : ℝ≥0∞ := by
  classical
  exact (descendantsAtScale Q k).attach.sup fun R =>
    normalizedBlockResponseEMaxOnCube R.1
      (a.restrictToSubcube
        (openCubeSet_subset_of_mem_descendantsAtScale hk R.2)) a0

private noncomputable def homogenizationErrorGeometricEWeight
    (s q : ℝ) (j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - Real.rpow 3 (-s * q)) *
    ENNReal.ofReal (Real.rpow 3 (-s * q * (j : ℝ)))

private noncomputable def parentTruncatedHomogenizationErrorInfinityFinite
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ)
    (hn : n ≤ Q.scale) (a : CoeffOn (cubeDomain Q))
    (a0 : Mat d) (s q : ℝ) : ℝ≥0∞ :=
  (∑' j : ℕ,
      homogenizationErrorGeometricEWeight s q j *
        (parentMaxNormalizedBlockResponseAtScale Q
          (n - (j : ℤ)) (by omega) a a0) ^ (q / 2)) ^ (1 / q)

/-- The source-order, scalar-comparator, `q = 1` truncated response error.

At each physical scale it maximizes over descendants of the one parent
coefficient, and only then performs the weighted scale sum. -/
noncomputable def parentTruncatedHomogenizationErrorInfinityOneScalar
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ)
    (hn : n ≤ Q.scale) (a : CoeffOn (cubeDomain Q))
    (sigma0 : ℝ) (_hsigma0 : 0 < sigma0)
    (s : FractionalOrder) : ℝ≥0∞ :=
  parentTruncatedHomogenizationErrorInfinityFinite Q n hn a
    (scalarMatrix (d := d) sigma0) s.1 1

/-- The source-order, scalar-comparator, `q = 2` truncated response error. -/
noncomputable def parentTruncatedHomogenizationErrorInfinityTwoScalar
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ)
    (hn : n ≤ Q.scale) (a : CoeffOn (cubeDomain Q))
    (sigma0 : ℝ) (_hsigma0 : 0 < sigma0)
    (s : FractionalOrder) : ℝ≥0∞ :=
  parentTruncatedHomogenizationErrorInfinityFinite Q n hn a
    (scalarMatrix (d := d) sigma0) s.1 2

/-- The canonical scalar-comparator parent response maximum at physical scale
`k`.  This is the finite supremum over the descendants of `Q` at that scale,
using literal restrictions of the one parent coefficient. -/
noncomputable def parentTruncatedNormalizedBlockResponseScalarEMaxAtScale
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (k : ℤ) (hk : k ≤ Q.scale)
    (a : CoeffOn (cubeDomain Q)) (sigma0 : ℝ) (_hsigma0 : 0 < sigma0) : ℝ≥0∞ := by
  classical
  exact (descendantsAtScale Q k).attach.sup fun R =>
    normalizedBlockResponseEMaxOnCube R.1
      (a.restrictToSubcube
        (openCubeSet_subset_of_mem_descendantsAtScale hk R.2))
      (scalarMatrix (d := d) sigma0)

/-- Exact series characterization of the canonical scalar `q = 1` truncated
parent error.  This only unfolds its frozen definition. -/
theorem parentTruncatedHomogenizationErrorInfinityOneScalar_eq_tsum
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : CoeffOn (cubeDomain Q)) (sigma0 : ℝ) (hsigma0 : 0 < sigma0)
    (s : FractionalOrder) :
    parentTruncatedHomogenizationErrorInfinityOneScalar Q n hn a sigma0 hsigma0 s =
      ∑' j : ℕ,
        (ENNReal.ofReal (1 - Real.rpow 3 (-s.1)) *
          ENNReal.ofReal (Real.rpow 3 (-s.1 * (j : ℝ)))) *
        (parentTruncatedNormalizedBlockResponseScalarEMaxAtScale Q
          (n - (j : ℤ)) (by omega) a sigma0 hsigma0) ^ (1 / 2 : ℝ) := by
  simp [parentTruncatedHomogenizationErrorInfinityOneScalar,
    parentTruncatedHomogenizationErrorInfinityFinite,
    homogenizationErrorGeometricEWeight,
    parentMaxNormalizedBlockResponseAtScale,
    parentTruncatedNormalizedBlockResponseScalarEMaxAtScale]

/-- Exact series characterization of the canonical scalar `q = 2` truncated
parent error.  This only unfolds its frozen definition. -/
theorem parentTruncatedHomogenizationErrorInfinityTwoScalar_eq_tsum
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : CoeffOn (cubeDomain Q)) (sigma0 : ℝ) (hsigma0 : 0 < sigma0)
    (s : FractionalOrder) :
    parentTruncatedHomogenizationErrorInfinityTwoScalar Q n hn a sigma0 hsigma0 s =
      (∑' j : ℕ,
        (ENNReal.ofReal (1 - Real.rpow 3 (-s.1 * 2)) *
          ENNReal.ofReal (Real.rpow 3 (-s.1 * 2 * (j : ℝ)))) *
        parentTruncatedNormalizedBlockResponseScalarEMaxAtScale Q
          (n - (j : ℤ)) (by omega) a sigma0 hsigma0) ^ (1 / 2 : ℝ) := by
  norm_num [parentTruncatedHomogenizationErrorInfinityTwoScalar,
    parentTruncatedHomogenizationErrorInfinityFinite,
    homogenizationErrorGeometricEWeight,
    parentMaxNormalizedBlockResponseAtScale,
    parentTruncatedNormalizedBlockResponseScalarEMaxAtScale]

private theorem normalizedBlockResponseESetOnCube_nonempty {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffOn (cubeDomain Q))
    (a0 : Mat d) :
    (normalizedBlockResponseESetOnCube Q a a0).Nonempty := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  let i0 : BlockCoord d := Sum.inl ⟨0, hd⟩
  let e : FullBlockVec d := Pi.single i0 1
  refine ⟨ENNReal.ofReal
    (doubledResponseJ (cubeDomain Q) a
      (ofFullBlockVec
        (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e))
      (ofFullBlockVec
        (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e))), ?_⟩
  refine ⟨e, ?_, rfl⟩
  unfold fullBlockVecNormSq e
  rw [Fintype.sum_eq_single i0]
  · simp
  · intro b hb
    simp [hb]

private theorem normalizedBlockResponseESetOnCube_elements_ne_top {d : ℕ}
    [NeZero d] {Q : TriadicCube d} {a : CoeffOn (cubeDomain Q)}
    {a0 : Mat d} {y : ℝ≥0∞}
    (hy : y ∈ normalizedBlockResponseESetOnCube Q a a0) :
    y ≠ ∞ := by
  rcases hy with ⟨e, he, rfl⟩
  exact ENNReal.ofReal_ne_top

private theorem normalizedBlockResponseESetOnCube_elements_nonneg_real {d : ℕ}
    [NeZero d] {Q : TriadicCube d} {a : CoeffOn (cubeDomain Q)}
    {a0 : Mat d} {e : FullBlockVec d}
    (_he : fullBlockVecNormSq e = 1) :
    0 ≤ doubledResponseJ (cubeDomain Q) a
      (ofFullBlockVec
        (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e))
      (ofFullBlockVec
        (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e)) :=
  doubledResponseJ_nonneg (cubeDomain Q) a _ _

private noncomputable def normalizedBlockResponseEUpperBoundOnCube {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffOn (cubeDomain Q))
    (a0 : Mat d) : ℝ≥0∞ :=
  let c : ℝ := (a.lam / (1 + 2 * a.Lam ^ 2))⁻¹
  ENNReal.ofReal
    (c * fullBlockMatRowAbsSqBound (constantFullBlockMatrixSqrt a0) +
      c * blockMatrixOfCoeffNormSqBound a.lam a.Lam *
        fullBlockMatRowAbsSqBound (constantFullBlockMatrixInvSqrt a0))

private theorem normalizedBlockResponseESetOnCube_le_upperBound {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffOn (cubeDomain Q))
    (a0 : Mat d) {y : ℝ≥0∞}
    (hy : y ∈ normalizedBlockResponseESetOnCube Q a a0) :
    y ≤ normalizedBlockResponseEUpperBoundOnCube Q a a0 := by
  rcases hy with ⟨e, he, rfl⟩
  let U := cubeDomain Q
  let apw : CoeffOn U :=
    Internal.Ch02.BookCh02.pointwiseCoeffOn U a
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField U a
  let MInv := constantFullBlockMatrixInvSqrt a0
  let MSqrt := constantFullBlockMatrixSqrt a0
  let P := ofFullBlockVec (Matrix.mulVec MInv e)
  let Q' := ofFullBlockVec (Matrix.mulVec MSqrt e)
  let c : ℝ := (a.lam / (1 + 2 * a.Lam ^ 2))⁻¹
  let B : ℝ :=
    c * fullBlockMatRowAbsSqBound MSqrt +
      c * blockMatrixOfCoeffNormSqBound a.lam a.Lam *
        fullBlockMatRowAbsSqBound MInv
  have hEll :
      IsEllipticFieldOn a.lam a.Lam (openCubeSet Q) A := by
    simpa [U, A] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn U a
  have haeeq : CoeffOn.AEEq a apw := by
    exact (Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U a).symm
  have hJ : doubledResponseJ U a P Q' = BlockJ (openCubeSet Q) P Q' A := by
    calc
      doubledResponseJ U a P Q' = doubledResponseJ U apw P Q' := by
        rw [doubledResponseJ_eq_ofAEEq haeeq P Q']
      _ = BlockJ (U : Set (Vec d)) P Q' apw.toCoeffField := by
        exact
          Internal.Ch02.BookCh02.book_doubledResponseJ_eq_BlockJ_of_isEllipticFieldOn
            U apw (by simpa [apw, U] using! hEll) P Q'
      _ = BlockJ (openCubeSet Q) P Q' A := by rfl
  have hvol : (MeasureTheory.volume (openCubeSet Q)).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos Q).ne'
  have hc_nonneg : 0 ≤ c := by
    have hden_pos : 0 < 1 + 2 * a.Lam ^ 2 := by positivity
    have hfrac_pos : 0 < a.lam / (1 + 2 * a.Lam ^ 2) :=
      div_pos a.lam_pos hden_pos
    dsimp [c]
    positivity
  have hcoeff_nonneg :
      0 ≤ blockMatrixOfCoeffNormSqBound a.lam a.Lam := by
    unfold blockMatrixOfCoeffNormSqBound
    have hLamSq : 0 ≤ a.Lam ^ 2 := sq_nonneg _
    have hInvSq : 0 ≤ a.lam⁻¹ * a.lam⁻¹ := mul_self_nonneg _
    have hFactor : 0 ≤ 2 * a.Lam ^ 2 + 1 := by nlinarith
    have hTail :
        0 ≤ 2 * (2 * a.Lam ^ 2 + 1) *
          (a.lam⁻¹ * a.lam⁻¹) * (a.Lam ^ 2 + 1) := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hFactor) hInvSq)
        (by nlinarith)
    nlinarith
  have hP : blockVecDot P P ≤ fullBlockMatRowAbsSqBound MInv := by
    dsimp [P, MInv]
    rw [blockVecDot_ofFullBlockVec_self_eq_fullBlockVecNormSq]
    exact fullBlockVecNormSq_mulVec_le_rowAbsSqBound_of_eq_one _ he
  have hQ : blockVecDot Q' Q' ≤ fullBlockMatRowAbsSqBound MSqrt := by
    dsimp [Q', MSqrt]
    rw [blockVecDot_ofFullBlockVec_self_eq_fullBlockVecNormSq]
    exact fullBlockVecNormSq_mulVec_le_rowAbsSqBound_of_eq_one _ he
  have hreal : doubledResponseJ U a P Q' ≤ B := by
    rw [hJ]
    let : MeasureTheory.IsFiniteMeasure
        (volumeMeasureOn (openCubeSet Q)) := by
      simpa [volumeMeasureOn] using
        (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
    calc
      BlockJ (openCubeSet Q) P Q' A ≤
          blockResponsePlainUpperBound a.lam a.Lam P Q' := by
        exact blockJ_le_plainUpperBound_of_isEllipticFieldOn
          (a := A) (U := openCubeSet Q) (measurableSet_openCubeSet Q)
          hEll hvol P Q'
      _ ≤ B := by
        have htermQ :
            c * blockVecDot Q' Q' ≤
              c * fullBlockMatRowAbsSqBound MSqrt :=
          mul_le_mul_of_nonneg_left hQ hc_nonneg
        have htermP :
            c * blockMatrixOfCoeffNormSqBound a.lam a.Lam * blockVecDot P P ≤
              c * blockMatrixOfCoeffNormSqBound a.lam a.Lam *
                fullBlockMatRowAbsSqBound MInv :=
          mul_le_mul_of_nonneg_left hP (mul_nonneg hc_nonneg hcoeff_nonneg)
        dsimp [B, c]
        unfold blockResponsePlainUpperBound
        dsimp [c] at htermQ htermP
        linarith
  simpa [normalizedBlockResponseEUpperBoundOnCube, B, c, P, Q', U] using
    ENNReal.ofReal_le_ofReal hreal

private theorem normalizedBlockResponseESetOnCube_bddAbove {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffOn (cubeDomain Q))
    (a0 : Mat d) :
    BddAbove (normalizedBlockResponseESetOnCube Q a a0) :=
  ⟨normalizedBlockResponseEUpperBoundOnCube Q a a0,
    fun _ hy => normalizedBlockResponseESetOnCube_le_upperBound Q a a0 hy⟩

private theorem normalizedBlockResponseEMaxOnCube_le_upperBound {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffOn (cubeDomain Q))
    (a0 : Mat d) :
    normalizedBlockResponseEMaxOnCube Q a a0 ≤
      normalizedBlockResponseEUpperBoundOnCube Q a a0 := by
  unfold normalizedBlockResponseEMaxOnCube
  exact sSup_le fun _ hy =>
    normalizedBlockResponseESetOnCube_le_upperBound Q a a0 hy

private theorem normalizedBlockResponseEMaxOnCube_lt_top {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffOn (cubeDomain Q))
    (a0 : Mat d) :
    normalizedBlockResponseEMaxOnCube Q a a0 < ∞ :=
  lt_of_le_of_lt
    (normalizedBlockResponseEMaxOnCube_le_upperBound Q a a0)
    ENNReal.ofReal_lt_top

private theorem normalizedBlockResponseESetOnCube_le_eMax {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffOn (cubeDomain Q))
    (a0 : Mat d) {y : ℝ≥0∞}
    (hy : y ∈ normalizedBlockResponseESetOnCube Q a a0) :
    y ≤ normalizedBlockResponseEMaxOnCube Q a a0 := by
  unfold normalizedBlockResponseEMaxOnCube
  exact le_sSup hy

private theorem normalizedBlockResponseEMaxOnCube_isLUB {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffOn (cubeDomain Q))
    (a0 : Mat d) :
    IsLUB (normalizedBlockResponseESetOnCube Q a a0)
      (normalizedBlockResponseEMaxOnCube Q a a0) := by
  constructor
  · intro y hy
    exact normalizedBlockResponseESetOnCube_le_eMax Q a a0 hy
  · intro b hb
    unfold normalizedBlockResponseEMaxOnCube
    exact sSup_le hb

/-- The `ℝ≥0∞`-valued unit-sphere response values for the positive scalar
comparator `sigma0 I` on one cube.

This is a scalar-facing wrapper around the private matrix implementation.  In
particular, it deliberately exposes a supremum API below, rather than claiming
that a maximizing vector has been constructed. -/
noncomputable def normalizedBlockResponseScalarEValueSetOnCube {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffOn (cubeDomain Q))
    (sigma0 : ℝ) (_hsigma0 : 0 < sigma0) : Set ℝ≥0∞ :=
  normalizedBlockResponseESetOnCube Q a (scalarMatrix (d := d) sigma0)

/-- The one-cube scalar-comparator response supremum.  This definition does
not assert that the supremum is attained. -/
noncomputable def normalizedBlockResponseScalarEMaxOnCube {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffOn (cubeDomain Q))
    (sigma0 : ℝ) (hsigma0 : 0 < sigma0) : ℝ≥0∞ :=
  sSup (normalizedBlockResponseScalarEValueSetOnCube Q a sigma0 hsigma0)

/-- Membership in the scalar response value set is exactly the nonnegative
extended-real encoding of a unit-sphere doubled response. -/
theorem mem_normalizedBlockResponseScalarEValueSetOnCube_iff {d : ℕ}
    [NeZero d] {Q : TriadicCube d} {a : CoeffOn (cubeDomain Q)}
    {sigma0 : ℝ} {hsigma0 : 0 < sigma0} {y : ℝ≥0∞} :
    y ∈ normalizedBlockResponseScalarEValueSetOnCube Q a sigma0 hsigma0 ↔
      ∃ e : FullBlockVec d, fullBlockVecNormSq e = 1 ∧
        y = ENNReal.ofReal
          (doubledResponseJ (cubeDomain Q) a
            (ofFullBlockVec
              (Matrix.mulVec
                (constantFullBlockMatrixInvSqrt (scalarMatrix (d := d) sigma0)) e))
            (ofFullBlockVec
              (Matrix.mulVec
                (constantFullBlockMatrixSqrt (scalarMatrix (d := d) sigma0)) e))) :=
  Iff.rfl

/-- Every scalar response value is finite, as follows from its
`ENNReal.ofReal` representation. -/
theorem normalizedBlockResponseScalarEValueSetOnCube_ne_top {d : ℕ}
    [NeZero d] {Q : TriadicCube d} {a : CoeffOn (cubeDomain Q)}
    {sigma0 : ℝ} {hsigma0 : 0 < sigma0} {y : ℝ≥0∞}
    (hy : y ∈ normalizedBlockResponseScalarEValueSetOnCube Q a sigma0 hsigma0) :
    y ≠ ∞ :=
  normalizedBlockResponseESetOnCube_elements_ne_top hy

/-- The real response encoded by the scalar value set is nonnegative. -/
theorem normalizedBlockResponseScalar_nonneg {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffOn (cubeDomain Q))
    (sigma0 : ℝ) (_hsigma0 : 0 < sigma0) (e : FullBlockVec d)
    (_he : fullBlockVecNormSq e = 1) :
    0 ≤ doubledResponseJ (cubeDomain Q) a
      (ofFullBlockVec
        (Matrix.mulVec
          (constantFullBlockMatrixInvSqrt (scalarMatrix (d := d) sigma0)) e))
      (ofFullBlockVec
        (Matrix.mulVec
          (constantFullBlockMatrixSqrt (scalarMatrix (d := d) sigma0)) e)) :=
  normalizedBlockResponseESetOnCube_elements_nonneg_real
    (a0 := scalarMatrix (d := d) sigma0) _he

/-- The scalar response value set is nonempty. -/
theorem normalizedBlockResponseScalarEValueSetOnCube_nonempty {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffOn (cubeDomain Q))
    (sigma0 : ℝ) (hsigma0 : 0 < sigma0) :
    (normalizedBlockResponseScalarEValueSetOnCube Q a sigma0 hsigma0).Nonempty :=
  normalizedBlockResponseESetOnCube_nonempty Q a
    (scalarMatrix (d := d) sigma0)

/-- The scalar response value set is bounded above in `ℝ≥0∞`. -/
theorem normalizedBlockResponseScalarEValueSetOnCube_bddAbove {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffOn (cubeDomain Q))
    (sigma0 : ℝ) (hsigma0 : 0 < sigma0) :
    BddAbove (normalizedBlockResponseScalarEValueSetOnCube Q a sigma0 hsigma0) :=
  normalizedBlockResponseESetOnCube_bddAbove Q a
    (scalarMatrix (d := d) sigma0)

/-- Every scalar response value is bounded by the one-cube response
supremum. -/
theorem normalizedBlockResponseScalarEValueSetOnCube_le_eMax {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffOn (cubeDomain Q))
    (sigma0 : ℝ) (hsigma0 : 0 < sigma0) {y : ℝ≥0∞}
    (hy : y ∈ normalizedBlockResponseScalarEValueSetOnCube Q a sigma0 hsigma0) :
    y ≤ normalizedBlockResponseScalarEMaxOnCube Q a sigma0 hsigma0 :=
  normalizedBlockResponseESetOnCube_le_eMax Q a
    (scalarMatrix (d := d) sigma0) hy

/-- The scalar response maximum is the least upper bound of the value set.
No attainment assertion is included. -/
theorem normalizedBlockResponseScalarEMaxOnCube_isLUB {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffOn (cubeDomain Q))
    (sigma0 : ℝ) (hsigma0 : 0 < sigma0) :
    IsLUB (normalizedBlockResponseScalarEValueSetOnCube Q a sigma0 hsigma0)
      (normalizedBlockResponseScalarEMaxOnCube Q a sigma0 hsigma0) :=
  normalizedBlockResponseEMaxOnCube_isLUB Q a
    (scalarMatrix (d := d) sigma0)

/-- The scalar response supremum is finite. -/
theorem normalizedBlockResponseScalarEMaxOnCube_lt_top {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffOn (cubeDomain Q))
    (sigma0 : ℝ) (hsigma0 : 0 < sigma0) :
    normalizedBlockResponseScalarEMaxOnCube Q a sigma0 hsigma0 < ∞ :=
  normalizedBlockResponseEMaxOnCube_lt_top Q a
    (scalarMatrix (d := d) sigma0)

end

end Book.Ch02
end Homogenization
