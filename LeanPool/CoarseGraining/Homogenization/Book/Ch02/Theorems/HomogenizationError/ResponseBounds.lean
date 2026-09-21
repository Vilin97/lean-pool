/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError.Translation

/-! # Response Bounds -/

open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section


/-!
# Response Bounds for Chapter 2.5 Homogenization Error

This file proves the public basic properties of the homogenization error
`\mathcal E_{s,\infty,1}` from Sec. 2.5.
-/

theorem CoeffOn.RestrictsTo.transpose {d : ℕ} {U V : Domain d}
    {a : CoeffOn U} {b : CoeffOn V} (h : CoeffOn.RestrictsTo a b) :
    CoeffOn.RestrictsTo a.transpose b.transpose :=
  h.mono fun x hx => by
    simp [hx]

/-- The public partition of an open triadic cube into descendants at a fixed
depth. -/
noncomputable def descendantsDomainPartition {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) : DomainPartition (cubeDomain Q) where
  Cell := {R : TriadicCube d // R ∈ descendantsAtDepth Q j}
  instFintype := inferInstance
  cell i := cubeDomain i.1
  cell_subset_parent i := by
    simpa [cubeDomain_coe] using openCubeSet_subset_of_mem_descendantsAtDepth i.2
  weight _ := ((Fintype.card {R : TriadicCube d // R ∈ descendantsAtDepth Q j} : ℝ)⁻¹)
  weight_nonneg _ := by positivity
  weight_sum_one := by
    let D := descendantsAtDepth Q j
    have hDne : D.Nonempty := descendantsAtDepth_nonempty Q j
    have hcardD : (D.card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr hDne
    simp [Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ hcardD
  triadic_realization := by
    refine ⟨Q, j, rfl, ?_⟩
    refine ⟨Equiv.refl _, ?_⟩
    intro i
    simp [cubeDomain_coe]

theorem descendantsDomainPartition_weightedAverage {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → ℝ) :
    (descendantsDomainPartition Q j).weightedAverage (fun i => F i.1) =
      descendantsAverage Q j F := by
  classical
  let D := descendantsAtDepth Q j
  have hsumSubtype :
      (∑ s : {R : TriadicCube d // R ∈ D}, F s.1) = D.sum F := by
    simpa using Finset.sum_attach D F
  unfold DomainPartition.weightedAverage descendantsAverage descendantsDomainPartition
  dsimp [D] at hsumSubtype ⊢
  rw [← hsumSubtype]
  simp [Finset.mul_sum]

/-- The public descendant partition's weighted matrix average is the
entrywise descendant average. -/
theorem descendantsDomainPartition_weightedMatAverage {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → Mat d) :
    (descendantsDomainPartition Q j).weightedMatAverage (fun i => F i.1) =
      descendantsAverageMat Q j F := by
  ext i k
  simp [DomainPartition.weightedMatAverage, descendantsAverageMat,
    descendantsDomainPartition_weightedAverage Q j (fun R => F R i k)]

/-- The public descendant partition's weighted block-matrix average is the
entrywise descendant average. -/
theorem descendantsDomainPartition_weightedBlockAverage {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → BlockMat d) :
    (descendantsDomainPartition Q j).weightedBlockAverage (fun i => F i.1) =
      descendantsAverageBlockMat Q j F := by
  simp [DomainPartition.weightedBlockAverage, descendantsAverageBlockMat]
  exact
    ⟨descendantsDomainPartition_weightedMatAverage Q j (fun R => (F R).upperLeft),
      descendantsDomainPartition_weightedMatAverage Q j (fun R => (F R).upperRight),
      descendantsDomainPartition_weightedMatAverage Q j (fun R => (F R).lowerLeft),
      descendantsDomainPartition_weightedMatAverage Q j (fun R => (F R).lowerRight)⟩

theorem doubledResponseJ_nonneg {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (P Q : BlockVec d) :
    0 ≤ doubledResponseJ U a P Q := by
  rcases P with ⟨p, q⟩
  rcases Q with ⟨qStar, pStar⟩
  rw [(doubledResponseTheory U a).doubledResponseJ_eq_scalar p pStar q qStar]
  have h1 : 0 ≤ responseJ U a (p - pStar) (qStar - q) :=
    responseJ_nonneg U a (p - pStar) (qStar - q)
  have h2 : 0 ≤ responseJ U a.transpose (pStar + p) (qStar + q) :=
    responseJ_nonneg U a.transpose (pStar + p) (qStar + q)
  nlinarith

theorem normalizedBlockResponseMax_nonneg {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) (a0 : Mat d) :
    0 ≤ normalizedBlockResponseMax Q a a0 := by
  unfold normalizedBlockResponseMax
  refine Real.sSup_nonneg ?_
  rintro x ⟨e, -, rfl⟩
  exact doubledResponseJ_nonneg (cubeDomain Q) (a.coeffOn Q)
    (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e))
    (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e))

theorem normalizedBlockResponseValueSet_nonempty {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) (a0 : Mat d) :
    (normalizedBlockResponseValueSet Q a a0).Nonempty := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  let i0 : BlockCoord d := Sum.inl ⟨0, hd⟩
  let e : FullBlockVec d := Pi.single i0 1
  refine ⟨doubledResponseJ (cubeDomain Q) (a.coeffOn Q)
    (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e))
    (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e)), ?_⟩
  refine ⟨e, ?_, rfl⟩
  unfold fullBlockVecNormSq e
  rw [Fintype.sum_eq_single i0]
  · simp
  · intro b hb
    simp [hb]

/-- A uniform deterministic bound for normalized block response on descendants
of `Q`, depending only on the root cube coefficient object and on `a0`. -/
noncomputable def normalizedBlockResponseUniformBound {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) (a0 : Mat d) : ℝ :=
  let c : ℝ := ((a.coeffOn Q).lam / (1 + 2 * (a.coeffOn Q).Lam ^ 2))⁻¹
  c * fullBlockMatRowAbsSqBound (constantFullBlockMatrixSqrt a0) +
    c * blockMatrixOfCoeffNormSqBound (a.coeffOn Q).lam (a.coeffOn Q).Lam *
      fullBlockMatRowAbsSqBound (constantFullBlockMatrixInvSqrt a0)

theorem normalizedBlockResponseValueSet_bddAbove_of_mem_descendantsAtScale
    {d : ℕ} [NeZero d] (a : TriadicCoeffFamily d)
    {Q R : TriadicCube d} {k : ℤ} (a0 : Mat d)
    (hR : R ∈ descendantsAtScale Q k) :
    BddAbove (normalizedBlockResponseValueSet R a a0) := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  let MInv := constantFullBlockMatrixInvSqrt a0
  let MSqrt := constantFullBlockMatrixSqrt a0
  let c : ℝ := ((a.coeffOn Q).lam / (1 + 2 * (a.coeffOn Q).Lam ^ 2))⁻¹
  let B : ℝ :=
    c * fullBlockMatRowAbsSqBound MSqrt +
      c * blockMatrixOfCoeffNormSqBound (a.coeffOn Q).lam (a.coeffOn Q).Lam *
        fullBlockMatRowAbsSqBound MInv
  refine ⟨B, ?_⟩
  have hk : k ≤ Q.scale := descendant_scale_le_of_mem_descendantsAtScale hR
  have hsub : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtScale hk hR
  have hEllQ :
      IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
        (openCubeSet Q) A := by
    simpa [A] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (cubeDomain Q) (a.coeffOn Q)
  have hEllR :
      IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
        (openCubeSet R) A :=
    IsEllipticFieldOn.mono hEllQ (measurableSet_openCubeSet R) hsub
  rintro m ⟨e, he, rfl⟩
  let aRpw : CoeffOn (cubeDomain R) :=
    pointwiseCoeffOnRestrict (a.coeffOn Q) hsub
  let P := ofFullBlockVec (Matrix.mulVec MInv e)
  let Q' := ofFullBlockVec (Matrix.mulVec MSqrt e)
  have haeeq : CoeffOn.AEEq (a.coeffOn R) aRpw := by
    simpa [aRpw] using
      coeffOn_descendant_aeeq_pointwiseCoeffOnRestrict (a := a) hk hR
  have hEllRpw :
      IsEllipticFieldOn aRpw.lam aRpw.Lam
        (cubeDomain R : Set (Vec d)) aRpw.toCoeffField := by
    simpa [aRpw, cubeDomain_coe, A] using! hEllR
  have hJ :
      doubledResponseJ (cubeDomain R) (a.coeffOn R) P Q' =
        BlockJ (openCubeSet R) P Q' A := by
    calc
      doubledResponseJ (cubeDomain R) (a.coeffOn R) P Q' =
          doubledResponseJ (cubeDomain R) aRpw P Q' := by
            rw [doubledResponseJ_eq_ofAEEq haeeq P Q']
      _ = BlockJ (cubeDomain R : Set (Vec d)) P Q' aRpw.toCoeffField := by
            exact
              Internal.Ch02.BookCh02.book_doubledResponseJ_eq_BlockJ_of_isEllipticFieldOn
                (cubeDomain R) aRpw hEllRpw P Q'
      _ = BlockJ (openCubeSet R) P Q' A := by
            rfl
  have hvolR : (MeasureTheory.volume (openCubeSet R)).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos R).ne'
  have hcoeff_nonneg : 0 ≤ c := by
    have hden_pos : 0 < 1 + 2 * (a.coeffOn Q).Lam ^ 2 := by positivity
    have hfrac_pos : 0 < (a.coeffOn Q).lam / (1 + 2 * (a.coeffOn Q).Lam ^ 2) :=
      div_pos (a.coeffOn Q).lam_pos hden_pos
    dsimp [c]
    positivity
  have hbound_nonneg :
      0 ≤ blockMatrixOfCoeffNormSqBound (a.coeffOn Q).lam (a.coeffOn Q).Lam := by
    unfold blockMatrixOfCoeffNormSqBound
    have hLamSq : 0 ≤ (a.coeffOn Q).Lam ^ 2 := sq_nonneg _
    have hInvSq : 0 ≤ (a.coeffOn Q).lam⁻¹ * (a.coeffOn Q).lam⁻¹ :=
      mul_self_nonneg _
    have hFactor : 0 ≤ 2 * (a.coeffOn Q).Lam ^ 2 + 1 := by nlinarith
    have hTail :
        0 ≤
          2 * (2 * (a.coeffOn Q).Lam ^ 2 + 1) *
              ((a.coeffOn Q).lam⁻¹ * (a.coeffOn Q).lam⁻¹) *
            ((a.coeffOn Q).Lam ^ 2 + 1) := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hFactor) hInvSq)
        (by nlinarith)
    nlinarith
  have hP :
      blockVecDot P P ≤ fullBlockMatRowAbsSqBound MInv := by
    dsimp [P, MInv]
    rw [blockVecDot_ofFullBlockVec_self_eq_fullBlockVecNormSq]
    exact fullBlockVecNormSq_mulVec_le_rowAbsSqBound_of_eq_one _ he
  have hQ :
      blockVecDot Q' Q' ≤ fullBlockMatRowAbsSqBound MSqrt := by
    dsimp [Q', MSqrt]
    rw [blockVecDot_ofFullBlockVec_self_eq_fullBlockVecNormSq]
    exact fullBlockVecNormSq_mulVec_le_rowAbsSqBound_of_eq_one _ he
  rw [hJ]
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet R).isFiniteMeasure_restrict_volume
  calc
    BlockJ (openCubeSet R) P Q' A ≤
        blockResponsePlainUpperBound (a.coeffOn Q).lam (a.coeffOn Q).Lam P Q' := by
      exact blockJ_le_plainUpperBound_of_isEllipticFieldOn
        (a := A) (U := openCubeSet R) (measurableSet_openCubeSet R)
        hEllR hvolR P Q'
    _ ≤ B := by
      have htermQ :
          c * blockVecDot Q' Q' ≤ c * fullBlockMatRowAbsSqBound MSqrt :=
        mul_le_mul_of_nonneg_left hQ hcoeff_nonneg
      have htermP :
          c * blockMatrixOfCoeffNormSqBound (a.coeffOn Q).lam (a.coeffOn Q).Lam *
              blockVecDot P P ≤
            c * blockMatrixOfCoeffNormSqBound (a.coeffOn Q).lam (a.coeffOn Q).Lam *
              fullBlockMatRowAbsSqBound MInv :=
        mul_le_mul_of_nonneg_left hP (mul_nonneg hcoeff_nonneg hbound_nonneg)
      dsimp [B, c]
      unfold blockResponsePlainUpperBound
      dsimp [c] at htermQ htermP
      linarith

theorem normalizedBlockResponseMax_le_uniform_of_mem_descendantsAtScale
    {d : ℕ} [NeZero d] (a : TriadicCoeffFamily d)
    {Q R : TriadicCube d} {k : ℤ} (a0 : Mat d)
    (hR : R ∈ descendantsAtScale Q k) :
    normalizedBlockResponseMax R a a0 ≤
      normalizedBlockResponseUniformBound Q a a0 := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  let MInv := constantFullBlockMatrixInvSqrt a0
  let MSqrt := constantFullBlockMatrixSqrt a0
  let c : ℝ := ((a.coeffOn Q).lam / (1 + 2 * (a.coeffOn Q).Lam ^ 2))⁻¹
  let B : ℝ :=
    c * fullBlockMatRowAbsSqBound MSqrt +
      c * blockMatrixOfCoeffNormSqBound (a.coeffOn Q).lam (a.coeffOn Q).Lam *
        fullBlockMatRowAbsSqBound MInv
  have hB :
      B = normalizedBlockResponseUniformBound Q a a0 := by
    rfl
  have hk : k ≤ Q.scale := descendant_scale_le_of_mem_descendantsAtScale hR
  have hsub : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtScale hk hR
  have hEllQ :
      IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
        (openCubeSet Q) A := by
    simpa [A] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (cubeDomain Q) (a.coeffOn Q)
  have hEllR :
      IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
        (openCubeSet R) A :=
    IsEllipticFieldOn.mono hEllQ (measurableSet_openCubeSet R) hsub
  unfold normalizedBlockResponseMax
  refine csSup_le (normalizedBlockResponseValueSet_nonempty R a a0) ?_
  rintro m ⟨e, he, rfl⟩
  let aRpw : CoeffOn (cubeDomain R) :=
    pointwiseCoeffOnRestrict (a.coeffOn Q) hsub
  let P := ofFullBlockVec (Matrix.mulVec MInv e)
  let Q' := ofFullBlockVec (Matrix.mulVec MSqrt e)
  have haeeq : CoeffOn.AEEq (a.coeffOn R) aRpw := by
    simpa [aRpw] using
      coeffOn_descendant_aeeq_pointwiseCoeffOnRestrict (a := a) hk hR
  have hEllRpw :
      IsEllipticFieldOn aRpw.lam aRpw.Lam
        (cubeDomain R : Set (Vec d)) aRpw.toCoeffField := by
    simpa [aRpw, cubeDomain_coe, A] using! hEllR
  have hJ :
      doubledResponseJ (cubeDomain R) (a.coeffOn R) P Q' =
        BlockJ (openCubeSet R) P Q' A := by
    calc
      doubledResponseJ (cubeDomain R) (a.coeffOn R) P Q' =
          doubledResponseJ (cubeDomain R) aRpw P Q' := by
            rw [doubledResponseJ_eq_ofAEEq haeeq P Q']
      _ = BlockJ (cubeDomain R : Set (Vec d)) P Q' aRpw.toCoeffField := by
            exact
              Internal.Ch02.BookCh02.book_doubledResponseJ_eq_BlockJ_of_isEllipticFieldOn
                (cubeDomain R) aRpw hEllRpw P Q'
      _ = BlockJ (openCubeSet R) P Q' A := by
            rfl
  have hvolR : (MeasureTheory.volume (openCubeSet R)).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos R).ne'
  have hcoeff_nonneg : 0 ≤ c := by
    have hden_pos : 0 < 1 + 2 * (a.coeffOn Q).Lam ^ 2 := by positivity
    have hfrac_pos : 0 < (a.coeffOn Q).lam / (1 + 2 * (a.coeffOn Q).Lam ^ 2) :=
      div_pos (a.coeffOn Q).lam_pos hden_pos
    dsimp [c]
    positivity
  have hbound_nonneg :
      0 ≤ blockMatrixOfCoeffNormSqBound (a.coeffOn Q).lam (a.coeffOn Q).Lam := by
    unfold blockMatrixOfCoeffNormSqBound
    have hLamSq : 0 ≤ (a.coeffOn Q).Lam ^ 2 := sq_nonneg _
    have hInvSq : 0 ≤ (a.coeffOn Q).lam⁻¹ * (a.coeffOn Q).lam⁻¹ :=
      mul_self_nonneg _
    have hFactor : 0 ≤ 2 * (a.coeffOn Q).Lam ^ 2 + 1 := by nlinarith
    have hTail :
        0 ≤
          2 * (2 * (a.coeffOn Q).Lam ^ 2 + 1) *
              ((a.coeffOn Q).lam⁻¹ * (a.coeffOn Q).lam⁻¹) *
            ((a.coeffOn Q).Lam ^ 2 + 1) := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hFactor) hInvSq)
        (by nlinarith)
    nlinarith
  have hP :
      blockVecDot P P ≤ fullBlockMatRowAbsSqBound MInv := by
    dsimp [P, MInv]
    rw [blockVecDot_ofFullBlockVec_self_eq_fullBlockVecNormSq]
    exact fullBlockVecNormSq_mulVec_le_rowAbsSqBound_of_eq_one _ he
  have hQ :
      blockVecDot Q' Q' ≤ fullBlockMatRowAbsSqBound MSqrt := by
    dsimp [Q', MSqrt]
    rw [blockVecDot_ofFullBlockVec_self_eq_fullBlockVecNormSq]
    exact fullBlockVecNormSq_mulVec_le_rowAbsSqBound_of_eq_one _ he
  rw [hJ, ← hB]
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet R).isFiniteMeasure_restrict_volume
  calc
    BlockJ (openCubeSet R) P Q' A ≤
        blockResponsePlainUpperBound (a.coeffOn Q).lam (a.coeffOn Q).Lam P Q' := by
      exact blockJ_le_plainUpperBound_of_isEllipticFieldOn
        (a := A) (U := openCubeSet R) (measurableSet_openCubeSet R)
        hEllR hvolR P Q'
    _ ≤ B := by
      have htermQ :
          c * blockVecDot Q' Q' ≤ c * fullBlockMatRowAbsSqBound MSqrt :=
        mul_le_mul_of_nonneg_left hQ hcoeff_nonneg
      have htermP :
          c * blockMatrixOfCoeffNormSqBound (a.coeffOn Q).lam (a.coeffOn Q).Lam *
              blockVecDot P P ≤
            c * blockMatrixOfCoeffNormSqBound (a.coeffOn Q).lam (a.coeffOn Q).Lam *
              fullBlockMatRowAbsSqBound MInv :=
        mul_le_mul_of_nonneg_left hP (mul_nonneg hcoeff_nonneg hbound_nonneg)
      dsimp [B, c]
      unfold blockResponsePlainUpperBound
      dsimp [c] at htermQ htermP
      linarith

theorem normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {k : ℤ}
    (a : TriadicCoeffFamily d) (a0 : Mat d)
    (hR : R ∈ descendantsAtScale Q k) :
    normalizedBlockResponseMax R a a0 ≤
      maxDescendantNormalizedBlockResponseAtScale Q k a a0 := by
  unfold maxDescendantNormalizedBlockResponseAtScale finsetSupReal
  have hBdd :
      BddAbove
        ((fun S => normalizedBlockResponseMax S a a0) ''
          (↑(descendantsAtScale Q k) : Set (TriadicCube d))) := by
    exact ((Set.toFinite _).image (fun S => normalizedBlockResponseMax S a a0)).bddAbove
  exact le_csSup hBdd ⟨R, hR, rfl⟩

theorem maxDescendantNormalizedBlockResponseAtScale_le_of_mem_descendantsAtScale
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {k l : ℤ}
    (a : TriadicCoeffFamily d) (a0 : Mat d)
    (hR : R ∈ descendantsAtScale Q k) (hl : l ≤ R.scale) :
    maxDescendantNormalizedBlockResponseAtScale R l a a0 ≤
      maxDescendantNormalizedBlockResponseAtScale Q l a a0 := by
  unfold maxDescendantNormalizedBlockResponseAtScale finsetSupReal
  have hne :
      ((fun S => normalizedBlockResponseMax S a a0) ''
        (↑(descendantsAtScale R l) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty R hl with ⟨S, hS⟩
    exact ⟨normalizedBlockResponseMax S a a0, ⟨S, hS, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨S, hS, rfl⟩
  have hBdd :
      BddAbove
        ((fun T => normalizedBlockResponseMax T a a0) ''
          (↑(descendantsAtScale Q l) : Set (TriadicCube d))) := by
    exact ((Set.toFinite _).image (fun T => normalizedBlockResponseMax T a a0)).bddAbove
  exact le_csSup hBdd ⟨S, mem_descendantsAtScale_trans hR hS, rfl⟩

theorem normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale_of_le
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) (a : TriadicCoeffFamily d) (a0 : Mat d) :
    normalizedBlockResponseMax Q a a0 ≤
      maxDescendantNormalizedBlockResponseAtScale Q k a a0 := by
  classical
  let j : ℕ := Int.toNat (Q.scale - k)
  let Pcell : DomainPartition (cubeDomain Q) := descendantsDomainPartition Q j
  have hj : (j : ℤ) = Q.scale - k := by
    dsimp [j]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hk)
  have hcell :
      ∀ i : Pcell.Cell, CoeffOn.RestrictsTo (a.coeffOn Q) (a.coeffOn i.1) := by
    intro i
    have hiScale : i.1 ∈ descendantsAtScale Q k := by
      rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
      change i.1 ∈ descendantsAtDepth Q j
      exact i.2
    exact a.restrictsTo_descendant hk hiScale
  unfold normalizedBlockResponseMax
  refine csSup_le (normalizedBlockResponseValueSet_nonempty Q a a0) ?_
  rintro x ⟨e, he, rfl⟩
  let P := ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e)
  let Q' := ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e)
  let F : TriadicCube d → ℝ := fun R =>
    responseJ (cubeDomain R) (a.coeffOn R) (P.1 - Q'.2) (Q'.1 - P.2)
  let G : TriadicCube d → ℝ := fun R =>
    responseJ (cubeDomain R) (a.coeffOn R).transpose (Q'.2 + P.1) (Q'.1 + P.2)
  have hrespF :
      responseJ (cubeDomain Q) (a.coeffOn Q) (P.1 - Q'.2) (Q'.1 - P.2) ≤
        descendantsAverage Q j F := by
    have hsub :=
      (responseSubadditivityAndScalingTheory (cubeDomain Q) (a.coeffOn Q)).responseJ_subadditive
        Pcell (fun i : Pcell.Cell => a.coeffOn i.1) hcell
        (P.1 - Q'.2) (Q'.1 - P.2)
    calc
      responseJ (cubeDomain Q) (a.coeffOn Q) (P.1 - Q'.2) (Q'.1 - P.2)
          ≤ Pcell.weightedAverage
              (fun i : Pcell.Cell =>
                responseJ (cubeDomain i.1) (a.coeffOn i.1)
                  (P.1 - Q'.2) (Q'.1 - P.2)) := by
            simpa [Pcell, descendantsDomainPartition] using hsub
      _ = descendantsAverage Q j F := by
            simpa [Pcell, F] using
              descendantsDomainPartition_weightedAverage Q j F
  have hrespG :
      responseJ (cubeDomain Q) (a.coeffOn Q).transpose (Q'.2 + P.1) (Q'.1 + P.2) ≤
        descendantsAverage Q j G := by
    have hcellT :
        ∀ i : Pcell.Cell,
          CoeffOn.RestrictsTo (a.coeffOn Q).transpose (a.coeffOn i.1).transpose :=
      fun i => (hcell i).transpose
    have hsub :=
      (responseSubadditivityAndScalingTheory (cubeDomain Q)
          (a.coeffOn Q).transpose).responseJ_subadditive
        Pcell (fun i : Pcell.Cell => (a.coeffOn i.1).transpose) hcellT
        (Q'.2 + P.1) (Q'.1 + P.2)
    calc
      responseJ (cubeDomain Q) (a.coeffOn Q).transpose (Q'.2 + P.1) (Q'.1 + P.2)
          ≤ Pcell.weightedAverage
              (fun i : Pcell.Cell =>
                responseJ (cubeDomain i.1) (a.coeffOn i.1).transpose
                  (Q'.2 + P.1) (Q'.1 + P.2)) := by
            simpa [Pcell, descendantsDomainPartition] using hsub
      _ = descendantsAverage Q j G := by
            simpa [Pcell, G] using
              descendantsDomainPartition_weightedAverage Q j G
  have hcombine :
      (1 / 2 : ℝ) * descendantsAverage Q j F +
          (1 / 2 : ℝ) * descendantsAverage Q j G =
        descendantsAverage Q j (fun R => (1 / 2 : ℝ) * F R + (1 / 2 : ℝ) * G R) := by
    calc
      (1 / 2 : ℝ) * descendantsAverage Q j F +
          (1 / 2 : ℝ) * descendantsAverage Q j G =
          descendantsAverage Q j (fun R => (1 / 2 : ℝ) * F R) +
            descendantsAverage Q j (fun R => (1 / 2 : ℝ) * G R) := by
            rw [descendantsAverage_smul, descendantsAverage_smul]
      _ = descendantsAverage Q j
          (fun R => (1 / 2 : ℝ) * F R + (1 / 2 : ℝ) * G R) := by
            symm
            exact descendantsAverage_add Q j
              (fun R => (1 / 2 : ℝ) * F R)
              (fun R => (1 / 2 : ℝ) * G R)
  have hresp :
      doubledResponseJ (cubeDomain Q) (a.coeffOn Q) P Q' ≤
        descendantsAverage Q j
          (fun R => (1 / 2 : ℝ) * F R + (1 / 2 : ℝ) * G R) := by
    calc
      doubledResponseJ (cubeDomain Q) (a.coeffOn Q) P Q' =
          (1 / 2 : ℝ) *
              responseJ (cubeDomain Q) (a.coeffOn Q)
                (P.1 - Q'.2) (Q'.1 - P.2) +
            (1 / 2 : ℝ) *
              responseJ (cubeDomain Q) (a.coeffOn Q).transpose
                (Q'.2 + P.1) (Q'.1 + P.2) := by
            simpa [P, Q'] using
              (doubledResponseTheory (cubeDomain Q) (a.coeffOn Q)).doubledResponseJ_eq_scalar
                P.1 Q'.2 P.2 Q'.1
      _ ≤ (1 / 2 : ℝ) * descendantsAverage Q j F +
            (1 / 2 : ℝ) * descendantsAverage Q j G := by
            nlinarith
      _ = descendantsAverage Q j
          (fun R => (1 / 2 : ℝ) * F R + (1 / 2 : ℝ) * G R) := hcombine
  have hpointwise :
      ∀ R ∈ descendantsAtDepth Q j,
        (1 / 2 : ℝ) * F R + (1 / 2 : ℝ) * G R ≤
          normalizedBlockResponseMax R a a0 := by
    intro R hRdepth
    have hRk : R ∈ descendantsAtScale Q k := by
      rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
      simpa [j] using hRdepth
    have hmem :
        (1 / 2 : ℝ) * F R + (1 / 2 : ℝ) * G R ∈
          normalizedBlockResponseValueSet R a a0 := by
      refine ⟨e, he, ?_⟩
      dsimp [F, G, P, Q']
      exact
        ((doubledResponseTheory (cubeDomain R) (a.coeffOn R)).doubledResponseJ_eq_scalar
          P.1 Q'.2 P.2 Q'.1).symm
    unfold normalizedBlockResponseMax
    exact le_csSup
      (normalizedBlockResponseValueSet_bddAbove_of_mem_descendantsAtScale
        (a := a) (Q := Q) (R := R) (k := k) a0 hRk)
      hmem
  have havg :
      descendantsAverage Q j
          (fun R => (1 / 2 : ℝ) * F R + (1 / 2 : ℝ) * G R) ≤
        descendantsAverage Q j (fun R => normalizedBlockResponseMax R a a0) :=
    descendantsAverage_le_descendantsAverage Q j hpointwise
  have hmax :
      descendantsAverage Q j (fun R => normalizedBlockResponseMax R a a0) ≤
        maxDescendantNormalizedBlockResponseAtScale Q k a a0 := by
    unfold maxDescendantNormalizedBlockResponseAtScale
    rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
    simpa [j, finsetSupReal_eq_finsetSsup] using
      descendantsAverage_le_finsetSsup Q j
        (fun R => normalizedBlockResponseMax R a a0)
  exact le_trans hresp (le_trans havg hmax)

theorem maxDescendantNormalizedBlockResponseAtScale_nonneg {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (a : TriadicCoeffFamily d) (a0 : Mat d) :
    0 ≤ maxDescendantNormalizedBlockResponseAtScale Q k a a0 := by
  rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
  exact le_trans (normalizedBlockResponseMax_nonneg R a a0)
    (normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale
      a a0 hR)

theorem maxDescendantNormalizedBlockResponseAtScale_le_uniform
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) (a : TriadicCoeffFamily d) (a0 : Mat d) :
    maxDescendantNormalizedBlockResponseAtScale Q k a a0 ≤
      normalizedBlockResponseUniformBound Q a a0 := by
  unfold maxDescendantNormalizedBlockResponseAtScale finsetSupReal
  have hne :
      ((fun R => normalizedBlockResponseMax R a a0) ''
        (↑(descendantsAtScale Q k) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
    exact ⟨normalizedBlockResponseMax R a a0, ⟨R, hR, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  exact normalizedBlockResponseMax_le_uniform_of_mem_descendantsAtScale
    (a := a) (Q := Q) (R := R) (k := k) a0 hR

theorem maxDescendantNormalizedBlockResponseAtScale_le_of_le
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k l : ℤ}
    (hkl : k ≤ l) (hlQ : l ≤ Q.scale)
    (a : TriadicCoeffFamily d) (a0 : Mat d) :
    maxDescendantNormalizedBlockResponseAtScale Q l a a0 ≤
      maxDescendantNormalizedBlockResponseAtScale Q k a a0 := by
  unfold maxDescendantNormalizedBlockResponseAtScale finsetSupReal
  have hne :
      ((fun R => normalizedBlockResponseMax R a a0) ''
        (↑(descendantsAtScale Q l) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty Q hlQ with ⟨R, hR⟩
    exact ⟨normalizedBlockResponseMax R a a0, ⟨R, hR, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  have hRscale : R.scale = l := descendant_scale_eq_of_mem_descendantsAtScale hR
  have hkR : k ≤ R.scale := by
    simpa [hRscale] using hkl
  have hRle :
      normalizedBlockResponseMax R a a0 ≤
        maxDescendantNormalizedBlockResponseAtScale R k a a0 :=
    normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale_of_le
      (Q := R) (k := k) hkR a a0
  have hRQ :
      maxDescendantNormalizedBlockResponseAtScale R k a a0 ≤
        maxDescendantNormalizedBlockResponseAtScale Q k a a0 :=
    maxDescendantNormalizedBlockResponseAtScale_le_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := l) (l := k) a a0 hR hkR
  exact le_trans hRle hRQ

theorem scaleResponseAtScale_infinity_nonneg {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (a : TriadicCoeffFamily d) (a0 : Mat d) :
    0 ≤ scaleResponseAtScale Q k .infinity a a0 := by
  rw [scaleResponseAtScale_infinity_eq]
  exact Real.rpow_nonneg
    (maxDescendantNormalizedBlockResponseAtScale_nonneg Q hk a a0) _

theorem scaleResponseAtScale_infinity_le_of_mem_descendantsAtScale {d : ℕ}
    [NeZero d] {Q R : TriadicCube d} {k l : ℤ}
    (a : TriadicCoeffFamily d) (a0 : Mat d)
    (hR : R ∈ descendantsAtScale Q k) (hl : l ≤ R.scale) :
    scaleResponseAtScale R l .infinity a a0 ≤
      scaleResponseAtScale Q l .infinity a a0 := by
  rw [scaleResponseAtScale_infinity_eq, scaleResponseAtScale_infinity_eq]
  refine Real.rpow_le_rpow
    (maxDescendantNormalizedBlockResponseAtScale_nonneg R hl a a0)
    (maxDescendantNormalizedBlockResponseAtScale_le_of_mem_descendantsAtScale
      a a0 hR hl) ?_
  norm_num

theorem scaleResponseAtScale_infinity_le_of_le
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k l : ℤ}
    (hkl : k ≤ l) (hlQ : l ≤ Q.scale)
    (a : TriadicCoeffFamily d) (a0 : Mat d) :
    scaleResponseAtScale Q l .infinity a a0 ≤
      scaleResponseAtScale Q k .infinity a a0 := by
  rw [scaleResponseAtScale_infinity_eq, scaleResponseAtScale_infinity_eq]
  refine Real.rpow_le_rpow
    (maxDescendantNormalizedBlockResponseAtScale_nonneg Q hlQ a a0)
    (maxDescendantNormalizedBlockResponseAtScale_le_of_le
      (Q := Q) (k := k) (l := l) hkl hlQ a a0) ?_
  norm_num

theorem scaleResponseAtScale_infinity_self_le
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) (a : TriadicCoeffFamily d) (a0 : Mat d) :
    scaleResponseAtScale Q Q.scale .infinity a a0 ≤
      scaleResponseAtScale Q k .infinity a a0 :=
  scaleResponseAtScale_infinity_le_of_le
    (Q := Q) (k := k) (l := Q.scale) hk le_rfl a a0

theorem scaleResponseAtScale_infinity_le_uniform
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) (a : TriadicCoeffFamily d) (a0 : Mat d) :
    scaleResponseAtScale Q k .infinity a a0 ≤
      Real.rpow (normalizedBlockResponseUniformBound Q a a0) (1 / 2 : ℝ) := by
  rw [scaleResponseAtScale_infinity_eq]
  exact Real.rpow_le_rpow
    (maxDescendantNormalizedBlockResponseAtScale_nonneg Q hk a a0)
    (maxDescendantNormalizedBlockResponseAtScale_le_uniform Q hk a a0)
    (by norm_num)

end

end Ch02
end Book
end Homogenization
