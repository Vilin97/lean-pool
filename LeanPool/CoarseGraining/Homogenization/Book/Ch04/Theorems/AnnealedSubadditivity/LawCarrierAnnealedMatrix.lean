/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError.ResponseBounds
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Basic
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAveragesDefinitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.StationaryExpectations
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.ScalarizationDefinitions

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.AnnealedSubadditivity.LawCarrierAEBounds

/-! # Law Carrier Annealed Matrix -/

namespace Homogenization
namespace Book
namespace Ch04

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace RestrictionLawCarrier

/- Annealed response subadditivity from the a.e. deterministic comparison,
finite descendant integrability, and stationarity. -/
private theorem annealedResponseJAtScale_le_of_ae_descendantsAverage
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hstat : RestrictionStationaryLaw P) {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    (p q : Vec d)
    (hParentInt : Integrable (restrictionResponseJObservableCubeSet (originCube d m) p q) P)
    (hDescInt :
      ∀ R, R ∈ descendantsAtScale (originCube d m) n →
        Integrable (restrictionResponseJObservableCubeSet R p q) P)
    (hSub :
      restrictionResponseJObservableCubeSet (originCube d m) p q ≤ᵐ[P]
        fun a : RegCoeffField d =>
          descendantsAverage (originCube d m) (Int.toNat (m - n))
            (fun R => restrictionResponseJObservableCubeSet R p q a)) :
    annealedResponseJAtScale P m p q ≤ annealedResponseJAtScale P n p q := by
  have hDescIntDepth :
      ∀ R, R ∈ descendantsAtDepth (originCube d m) (Int.toNat (m - n)) →
        Integrable (restrictionResponseJObservableCubeSet R p q) P := by
    intro R hR
    exact hDescInt R (by
      simpa [descendantsAtScale_eq_descendantsAtDepth (originCube d m) hnm] using! hR)
  have hAvgInt :
      Integrable
        (fun a : RegCoeffField d =>
          descendantsAverage (originCube d m) (Int.toNat (m - n))
            (fun R => restrictionResponseJObservableCubeSet R p q a)) P :=
    integrable_descendantsAverage_restrictionResponseJObservableCubeSet hDescIntDepth
  calc
    annealedResponseJAtScale P m p q
        = ∫ a, restrictionResponseJObservableCubeSet (originCube d m) p q a ∂P := rfl
    _ ≤ ∫ a,
          descendantsAverage (originCube d m) (Int.toNat (m - n))
            (fun R => restrictionResponseJObservableCubeSet R p q a) ∂P :=
        integral_mono_ae hParentInt hAvgInt hSub
    _ = expectedResponseJCubeSet P (originCube d n) p q :=
        hP.integral_descendantsAverage_restrictionResponseJObservableCubeSet_eq_originCube_of_stationary
          hstat hn hnm p q hDescInt
    _ = annealedResponseJAtScale P n p q := rfl

/-- Law-facing annealed response subadditivity.  Ch4 supplies the deterministic
a.e. descendant comparison; callers only provide the integrability and
stationarity hypotheses used by the expectation step. -/
theorem annealedResponseJAtScale_le
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hstat : RestrictionStationaryLaw P) {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    (p q : Vec d)
    (hParentInt : Integrable (restrictionResponseJObservableCubeSet (originCube d m) p q) P)
    (hDescInt :
      ∀ R, R ∈ descendantsAtScale (originCube d m) n →
        Integrable (restrictionResponseJObservableCubeSet R p q) P) :
    annealedResponseJAtScale P m p q ≤ annealedResponseJAtScale P n p q :=
  hP.annealedResponseJAtScale_le_of_ae_descendantsAverage hstat hn hnm p q
    hParentInt hDescInt
    (hP.restrictionResponseJObservableCubeSet_le_descendantsAverage_ae hnm p q)

/-- Entrywise expectation of the deterministic descendant-average coarse block
matrix is the annealed origin-cube block matrix at the child scale. -/
private theorem integral_descendantsAverageBlockMat_entry_eq_annealedBlockMatrixAtScale
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hstat : RestrictionStationaryLaw P) {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    (hDescInt :
      ∀ R, R ∈ descendantsAtScale (originCube d m) n →
        ∀ α β, Integrable
          (fun a : RegCoeffField d => blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) α β) P)
    (α β : BlockCoord d) :
    ∫ a,
        blockMatEntry
          (descendantsAverageBlockMat (originCube d m) (Int.toNat (m - n))
            (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) α β ∂P =
      blockMatEntry (annealedBlockMatrixAtScale P n) α β := by
  classical
  let Q : TriadicCube d := originCube d m
  let j : ℕ := Int.toNat (m - n)
  have hDescIntDepth :
      ∀ R, R ∈ descendantsAtDepth Q j →
        Integrable
          (fun a : RegCoeffField d => blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) α β) P := by
    intro R hR
    exact hDescInt R (by
      simpa [Q, j, descendantsAtScale_eq_descendantsAtDepth Q hnm] using! hR) α β
  have hEntryFun :
      (fun a : RegCoeffField d =>
        blockMatEntry
          (descendantsAverageBlockMat Q j (fun R => coarseBlockMatrix (cubeSet R) a.toFun))
          α β) =
        fun a : RegCoeffField d =>
          descendantsAverage Q j
            (fun R => blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) α β) := by
    funext a
    cases α <;> cases β <;> rfl
  rw [show
      (fun a : RegCoeffField d =>
        blockMatEntry
          (descendantsAverageBlockMat (originCube d m) (Int.toNat (m - n))
            (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) α β) =
        fun a : RegCoeffField d =>
          descendantsAverage Q j
            (fun R => blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) α β) by
        simpa [Q, j] using hEntryFun]
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  have hDscale : D = descendantsAtScale Q n := by
    simpa [D, Q, j, originCube] using (descendantsAtScale_eq_descendantsAtDepth Q hnm).symm
  have hD_nonempty : D.Nonempty := by
    simpa [D] using descendantsAtDepth_nonempty Q j
  have hcard_ne : ((D.card : ℝ) ≠ 0) := by
    exact_mod_cast Finset.card_ne_zero.mpr hD_nonempty
  calc
    ∫ a,
        descendantsAverage Q j
          (fun R => blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) α β) ∂P
        =
      descendantsAverage Q j
        (fun R =>
          ∫ a, blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) α β ∂P) :=
        integral_descendantsAverage_eq_descendantsAverage_integral hDescIntDepth
    _ =
      (D.card : ℝ)⁻¹ *
        (∑ R ∈ D,
          ∫ a, blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) α β ∂P) := by
        rfl
    _ =
      (D.card : ℝ)⁻¹ *
        (∑ _R ∈ D,
          ∫ a,
            blockMatEntry (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun) α β ∂P) := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro R hR
        exact
          hP.integral_coarseBlockMatrix_entry_cubeSet_eq_originCube_of_mem_descendantsAtScale_originCube
            hstat hn hnm (by simpa [Q, hDscale] using hR) α β
    _ =
      ∫ a, blockMatEntry (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun) α β ∂P := by
        simp [Finset.sum_const, nsmul_eq_mul, hcard_ne]
    _ = blockMatEntry (annealedBlockMatrixAtScale P n) α β := by
        cases α <;> cases β <;> rfl

/-- Law-facing annealed block monotonicity.  Ch4 supplies the deterministic
a.e. block comparison and the stationarity step; callers provide only the
entrywise integrability needed to take expectations. -/
theorem blockMatLoewnerLE_annealedBlockMatrixAtScale
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hstat : RestrictionStationaryLaw P) {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    (hParentInt :
      ∀ α β, Integrable
        (fun a : RegCoeffField d =>
          blockMatEntry (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) α β) P)
    (hDescInt :
      ∀ R, R ∈ descendantsAtScale (originCube d m) n →
        ∀ α β, Integrable
          (fun a : RegCoeffField d => blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) α β) P) :
    BlockMatLoewnerLE (annealedBlockMatrixAtScale P m)
      (annealedBlockMatrixAtScale P n) := by
  let Q : TriadicCube d := originCube d m
  let j : ℕ := Int.toNat (m - n)
  let parentBlock : RegCoeffField d → BlockMat d :=
    fun a => coarseBlockMatrix (cubeSet Q) a.toFun
  let childAverageBlock : RegCoeffField d → BlockMat d :=
    fun a => descendantsAverageBlockMat Q j (fun R => coarseBlockMatrix (cubeSet R) a.toFun)
  have hDescIntDepth :
      ∀ R, R ∈ descendantsAtDepth Q j →
        ∀ α β, Integrable
          (fun a : RegCoeffField d => blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) α β) P := by
    intro R hR α β
    exact hDescInt R (by
      simpa [Q, j, descendantsAtScale_eq_descendantsAtDepth Q hnm] using! hR) α β
  have hChildAverageEntryInt :
      ∀ α β, Integrable (fun a : RegCoeffField d => blockMatEntry (childAverageBlock a) α β) P := by
    intro α β
    have hEntryFun :
        (fun a : RegCoeffField d => blockMatEntry (childAverageBlock a) α β) =
          fun a : RegCoeffField d =>
            descendantsAverage Q j
              (fun R => blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) α β) := by
      funext a
      cases α <;> cases β <;> rfl
    rw [hEntryFun]
    exact integrable_descendantsAverage (fun R hR => hDescIntDepth R hR α β)
  have hChildAverageBlockEq :
      { upperLeft := fun i k => ∫ a, (childAverageBlock a).upperLeft i k ∂P
        upperRight := fun i k => ∫ a, (childAverageBlock a).upperRight i k ∂P
        lowerLeft := fun i k => ∫ a, (childAverageBlock a).lowerLeft i k ∂P
        lowerRight := fun i k => ∫ a, (childAverageBlock a).lowerRight i k ∂P } =
        annealedBlockMatrixAtScale P n := by
    let C : BlockMat d :=
      { upperLeft := fun i k => ∫ a, (childAverageBlock a).upperLeft i k ∂P
        upperRight := fun i k => ∫ a, (childAverageBlock a).upperRight i k ∂P
        lowerLeft := fun i k => ∫ a, (childAverageBlock a).lowerLeft i k ∂P
        lowerRight := fun i k => ∫ a, (childAverageBlock a).lowerRight i k ∂P }
    change C = annealedBlockMatrixAtScale P n
    have hUL : C.upperLeft = (annealedBlockMatrixAtScale P n).upperLeft := by
      funext i k
      simpa [blockMatEntry, childAverageBlock, Q, j, C] using!
        hP.integral_descendantsAverageBlockMat_entry_eq_annealedBlockMatrixAtScale
          hstat hn hnm hDescInt (Sum.inl i) (Sum.inl k)
    have hUR : C.upperRight = (annealedBlockMatrixAtScale P n).upperRight := by
      funext i k
      simpa [blockMatEntry, childAverageBlock, Q, j, C] using!
        hP.integral_descendantsAverageBlockMat_entry_eq_annealedBlockMatrixAtScale
          hstat hn hnm hDescInt (Sum.inl i) (Sum.inr k)
    have hLL : C.lowerLeft = (annealedBlockMatrixAtScale P n).lowerLeft := by
      funext i k
      simpa [blockMatEntry, childAverageBlock, Q, j, C] using!
        hP.integral_descendantsAverageBlockMat_entry_eq_annealedBlockMatrixAtScale
          hstat hn hnm hDescInt (Sum.inr i) (Sum.inl k)
    have hLR : C.lowerRight = (annealedBlockMatrixAtScale P n).lowerRight := by
      funext i k
      simpa [blockMatEntry, childAverageBlock, Q, j, C] using!
        hP.integral_descendantsAverageBlockMat_entry_eq_annealedBlockMatrixAtScale
          hstat hn hnm hDescInt (Sum.inr i) (Sum.inr k)
    exact (BlockMat.mk.injEq C.upperLeft C.upperRight C.lowerLeft C.lowerRight
      (annealedBlockMatrixAtScale P n).upperLeft (annealedBlockMatrixAtScale P n).upperRight
      (annealedBlockMatrixAtScale P n).lowerLeft
      (annealedBlockMatrixAtScale P n).lowerRight).mpr ⟨hUL, hUR, hLL, hLR⟩
  refine
    blockMatLoewnerLE_of_integral_quadratic_mono
      (P := P)
      (A := annealedBlockMatrixAtScale P m)
      (B := annealedBlockMatrixAtScale P n)
      (F := fun X a =>
        (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul (parentBlock a) X))
      (G := fun X a =>
        (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul (childAverageBlock a) X))
      ?hFint ?hGint ?hA ?hB ?hMono
  · intro X
    exact
      (integrable_blockVecDot_blockMatVecMul_of_integrable_entries
        (by simpa [parentBlock, Q] using hParentInt) X X).const_mul (1 / 2 : ℝ)
  · intro X
    exact
      (integrable_blockVecDot_blockMatVecMul_of_integrable_entries
        hChildAverageEntryInt X X).const_mul (1 / 2 : ℝ)
  · intro X
    have hInt :=
      integral_blockVecDot_blockMatVecMul_eq_of_integrable_entries
        (B := parentBlock)
        (by simpa [parentBlock, Q] using hParentInt) X X
    calc
      (1 / 2 : ℝ) * blockVecDot X
          (blockMatVecMul (annealedBlockMatrixAtScale P m) X)
          =
        (1 / 2 : ℝ) *
          ∫ a, blockVecDot X (blockMatVecMul (parentBlock a) X) ∂P := by
          simpa [parentBlock, Q, annealedBlockMatrixAtScale, annealedBlockMatrix] using
            congrArg (fun t => (1 / 2 : ℝ) * t) hInt.symm
      _ =
        ∫ a,
          (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul (parentBlock a) X) ∂P := by
          rw [integral_const_mul]
  · intro X
    have hInt :=
      integral_blockVecDot_blockMatVecMul_eq_of_integrable_entries
        (B := childAverageBlock) hChildAverageEntryInt X X
    calc
      ∫ a,
          (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul (childAverageBlock a) X) ∂P
          =
        (1 / 2 : ℝ) *
          ∫ a, blockVecDot X (blockMatVecMul (childAverageBlock a) X) ∂P := by
          rw [integral_const_mul]
      _ =
        (1 / 2 : ℝ) * blockVecDot X
          (blockMatVecMul (annealedBlockMatrixAtScale P n) X) := by
          rw [hInt]
          rw [hChildAverageBlockEq]
  · intro X
    filter_upwards [hP.coarseBlockMatrix_le_descendantsAverageBlockMat_ae hnm] with a ha
    simpa [parentBlock, childAverageBlock, Q, j] using ha X

end RestrictionLawCarrier

/-- The starred annealed block monotonicity follows from annealed block
monotonicity by the built-in block reflection. -/
theorem blockMatLoewnerLE_annealedStarredBlockMatrixInvAtScale_of_block
    {d : ℕ} {P : RestrictionCoeffLaw d} {n m : ℤ}
    (hBlock : BlockMatLoewnerLE (annealedBlockMatrixAtScale P m)
      (annealedBlockMatrixAtScale P n)) :
    BlockMatLoewnerLE (annealedStarredBlockMatrixInvAtScale P m)
      (annealedStarredBlockMatrixInvAtScale P n) := by
  simpa [annealedStarredBlockMatrixInvAtScale, annealedStarredBlockMatrixInv] using!
    blockMatLoewnerLE_blockReflect hBlock

/-- Matrix monotonicity of `σ_*⁻¹` follows from annealed block monotonicity. -/
theorem matLoewnerLE_annealedSigmaStarInvAtScale_of_block
    {d : ℕ} {P : RestrictionCoeffLaw d} {n m : ℤ}
    (hBlock : BlockMatLoewnerLE (annealedBlockMatrixAtScale P m)
      (annealedBlockMatrixAtScale P n)) :
    MatLoewnerLE (annealedSigmaStarInvAtScale P m)
      (annealedSigmaStarInvAtScale P n) := by
  simpa [annealedSigmaStarInvAtScale, annealedSigmaStarInv,
    annealedBlockMatrixAtScale] using
      matLoewnerLE_lowerRight_of_blockMatLoewnerLE hBlock

/-- Matrix monotonicity of `b` follows from annealed block monotonicity. -/
theorem matLoewnerLE_annealedBAtScale_of_block
    {d : ℕ} {P : RestrictionCoeffLaw d} {n m : ℤ}
    (hBlock : BlockMatLoewnerLE (annealedBlockMatrixAtScale P m)
      (annealedBlockMatrixAtScale P n)) :
    MatLoewnerLE (annealedBAtScale P m) (annealedBAtScale P n) := by
  simpa [annealedBAtScale, annealedB, annealedBlockMatrixAtScale] using
    matLoewnerLE_upperLeft_of_blockMatLoewnerLE hBlock

/-- Scalar monotonicity of the primitive inverse-star coefficient from matrix
monotonicity. -/
private theorem barSigmaStarInv_le_of_annealedSigmaStarInvAtScale_mono
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {n m : ℤ}
    (hm : Internal.AnnealedPrimitiveScalarizationData (d := d) P m)
    (hn : Internal.AnnealedPrimitiveScalarizationData (d := d) P n)
    (hMono : MatLoewnerLE (annealedSigmaStarInvAtScale P m)
      (annealedSigmaStarInvAtScale P n)) :
    hm.barSigmaStarInv ≤ hn.barSigmaStarInv :=
  Internal.AnnealedPrimitiveScalarizationData.barSigmaStarInv_le_of_matLoewnerLE hm hn hMono

/-- Scalar monotonicity of the primitive upper-left coefficient from matrix
monotonicity. -/
private theorem barB_le_of_annealedBAtScale_mono
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {n m : ℤ}
    (hm : Internal.AnnealedPrimitiveScalarizationData (d := d) P m)
    (hn : Internal.AnnealedPrimitiveScalarizationData (d := d) P n)
    (hMono : MatLoewnerLE (annealedBAtScale P m) (annealedBAtScale P n)) :
    hm.barB ≤ hn.barB :=
  Internal.AnnealedPrimitiveScalarizationData.barB_le_of_matLoewnerLE hm hn hMono

/-- The scalar chain
`\barσ_{*,n} ≤ \barσ_{*,m} ≤ \barσ_m ≤ \barσ_n` from primitive
scalarization data and matrix monotonicity. -/
private theorem scalar_chain_of_primitive_matrix_mono
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {n m : ℤ}
    (hScal : Internal.AnnealedScalarizationTheory (d := d) P)
    (hm : Internal.AnnealedPrimitiveScalarizationData (d := d) P m)
    (hn : Internal.AnnealedPrimitiveScalarizationData (d := d) P n)
    (hStarMono : MatLoewnerLE (annealedSigmaStarInvAtScale P m)
      (annealedSigmaStarInvAtScale P n))
    (hBMono : MatLoewnerLE (annealedBAtScale P m) (annealedBAtScale P n))
    (hStar_m_pos : 0 < hm.barSigmaStarInv)
    (hContrast_m : 1 ≤ hm.contrast) :
    hScal.barSigmaStar n ≤ hScal.barSigmaStar m ∧
      hScal.barSigmaStar m ≤ hScal.barSigma m ∧
        hScal.barSigma m ≤ hScal.barSigma n := by
  have hStar_le : hm.barSigmaStarInv ≤ hn.barSigmaStarInv :=
    barSigmaStarInv_le_of_annealedSigmaStarInvAtScale_mono hm hn hStarMono
  have hB_le : hm.barB ≤ hn.barB :=
    barB_le_of_annealedBAtScale_mono hm hn hBMono
  constructor
  · exact
      Internal.AnnealedPrimitiveScalarizationData.barSigmaStar_le_of_barSigmaStarInv_le
        hScal hm hn hStar_le hStar_m_pos
  · constructor
    · exact
        Internal.AnnealedPrimitiveScalarizationData.barSigmaStar_le_barSigma_of_one_le_contrast
          hScal hm hContrast_m hStar_m_pos
    · exact
        Internal.AnnealedPrimitiveScalarizationData.barSigma_le_of_barB_le
          hScal hm hn hB_le

/-- The scalar chain
`\barσ_{*,n} ≤ \barσ_{*,m} ≤ \barσ_m ≤ \barσ_n` from primitive
scalarization data and annealed block monotonicity. -/
theorem scalar_chain_of_primitive_block_mono
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {n m : ℤ}
    (hScal : Internal.AnnealedScalarizationTheory (d := d) P)
    (hm : Internal.AnnealedPrimitiveScalarizationData (d := d) P m)
    (hn : Internal.AnnealedPrimitiveScalarizationData (d := d) P n)
    (hBlock : BlockMatLoewnerLE (annealedBlockMatrixAtScale P m)
      (annealedBlockMatrixAtScale P n))
    (hStar_m_pos : 0 < hm.barSigmaStarInv)
    (hContrast_m : 1 ≤ hm.contrast) :
    hScal.barSigmaStar n ≤ hScal.barSigmaStar m ∧
      hScal.barSigmaStar m ≤ hScal.barSigma m ∧
        hScal.barSigma m ≤ hScal.barSigma n :=
  scalar_chain_of_primitive_matrix_mono hScal hm hn
    (matLoewnerLE_annealedSigmaStarInvAtScale_of_block hBlock)
    (matLoewnerLE_annealedBAtScale_of_block hBlock)
    hStar_m_pos hContrast_m

/-- Primitive contrast monotonicity from primitive scalarization data and
matrix monotonicity. -/
private theorem primitive_contrast_le_of_matrix_mono
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {n m : ℤ}
    (hm : Internal.AnnealedPrimitiveScalarizationData (d := d) P m)
    (hn : Internal.AnnealedPrimitiveScalarizationData (d := d) P n)
    (hStarMono : MatLoewnerLE (annealedSigmaStarInvAtScale P m)
      (annealedSigmaStarInvAtScale P n))
    (hBMono : MatLoewnerLE (annealedBAtScale P m) (annealedBAtScale P n))
    (hStar_m_nonneg : 0 ≤ hm.barSigmaStarInv)
    (hB_n_nonneg : 0 ≤ hn.barB) :
    hm.contrast ≤ hn.contrast :=
  Internal.AnnealedPrimitiveScalarizationData.contrast_le_of_component_le hm hn
    (barB_le_of_annealedBAtScale_mono hm hn hBMono)
    (barSigmaStarInv_le_of_annealedSigmaStarInvAtScale_mono hm hn hStarMono)
    hStar_m_nonneg hB_n_nonneg

/-- Primitive contrast monotonicity from primitive scalarization data and
annealed block monotonicity. -/
theorem primitive_contrast_le_of_block_mono
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {n m : ℤ}
    (hm : Internal.AnnealedPrimitiveScalarizationData (d := d) P m)
    (hn : Internal.AnnealedPrimitiveScalarizationData (d := d) P n)
    (hBlock : BlockMatLoewnerLE (annealedBlockMatrixAtScale P m)
      (annealedBlockMatrixAtScale P n))
    (hStar_m_nonneg : 0 ≤ hm.barSigmaStarInv)
    (hB_n_nonneg : 0 ≤ hn.barB) :
    hm.contrast ≤ hn.contrast :=
  primitive_contrast_le_of_matrix_mono hm hn
    (matLoewnerLE_annealedSigmaStarInvAtScale_of_block hBlock)
    (matLoewnerLE_annealedBAtScale_of_block hBlock)
    hStar_m_nonneg hB_n_nonneg

/-- Scalar contrast monotonicity from primitive scalarization data and annealed
block monotonicity, stated for the public scalarization theory. -/
theorem scalar_contrast_le_of_primitive_block_mono
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {n m : ℤ}
    (hScal : Internal.AnnealedScalarizationTheory (d := d) P)
    (hm : Internal.AnnealedPrimitiveScalarizationData (d := d) P m)
    (hn : Internal.AnnealedPrimitiveScalarizationData (d := d) P n)
    (hBlock : BlockMatLoewnerLE (annealedBlockMatrixAtScale P m)
      (annealedBlockMatrixAtScale P n))
    (hStar_m_nonneg : 0 ≤ hm.barSigmaStarInv)
    (hB_n_nonneg : 0 ≤ hn.barB) :
    hScal.contrast m ≤ hScal.contrast n := by
  simpa [Internal.AnnealedPrimitiveScalarizationData.scalar_contrast_eq hScal hm,
    Internal.AnnealedPrimitiveScalarizationData.scalar_contrast_eq hScal hn] using
      primitive_contrast_le_of_block_mono hm hn hBlock
        hStar_m_nonneg hB_n_nonneg

private theorem sq_matrix_entry_le_matNormSq
    {d : ℕ} (A : Mat d) (i j : Fin d) :
    A i j ^ 2 ≤ matNormSq A := by
  unfold matNormSq
  exact le_trans
    (Finset.single_le_sum (fun k _ => sq_nonneg (A i k)) (Finset.mem_univ j))
    (Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg (A k l))
      (Finset.mem_univ i))

private theorem abs_matrix_entry_le_matNorm
    {d : ℕ} (A : Mat d) (i j : Fin d) :
    |A i j| ≤ matNorm A := by
  calc
    |A i j| = Real.sqrt (A i j ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt (matNormSq A) :=
      Real.sqrt_le_sqrt (sq_matrix_entry_le_matNormSq A i j)
    _ = matNorm A := rfl

private theorem blockMatVecMul_sub
    {d : ℕ} (A : BlockMat d) (X Y : BlockVec d) :
    blockMatVecMul A (X - Y) = blockMatVecMul A X - blockMatVecMul A Y := by
  have hneg : blockMatVecMul A (-Y) = -blockMatVecMul A Y := by
    simpa using blockMatVecMul_smul A (-1) Y
  rw [sub_eq_add_neg, blockMatVecMul_add, hneg]
  rfl

private theorem blockVecDot_sub_left
    {d : ℕ} (X Y Z : BlockVec d) :
    blockVecDot (X - Y) Z = blockVecDot X Z - blockVecDot Y Z := by
  have hneg : blockVecDot (-Y) Z = -blockVecDot Y Z := by
    simpa using blockVecDot_smul_left (-1) Y Z
  rw [sub_eq_add_neg, blockVecDot_add_left, hneg]
  rfl

private theorem blockBasis_sub_pairing
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

private theorem blockBasis_add_ne_zero
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

private theorem blockBasis_sub_ne_zero
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

private theorem abs_cross_blockMatEntry_le_diag_sum_of_blockPosDef
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

theorem abs_blockMatEntry_le_diagonalBlockNorms_of_symm_pos
    {d : ℕ} {A : BlockMat d} (hSymm : IsSymmetricBlockMat A)
    (hPos : Ch02.BlockPosDef A) (α β : BlockCoord d) :
    |blockMatEntry A α β| ≤ matNorm A.upperLeft + matNorm A.lowerRight := by
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          exact le_trans (abs_matrix_entry_le_matNorm A.upperLeft i j)
            (by nlinarith [matNorm_nonneg A.lowerRight])
      | inr j =>
          have hcross :
              |blockMatEntry A (Sum.inl i) (Sum.inr j)| ≤
                (1 / 2 : ℝ) *
                  (blockMatEntry A (Sum.inl i) (Sum.inl i) +
                    blockMatEntry A (Sum.inr j) (Sum.inr j)) :=
            abs_cross_blockMatEntry_le_diag_sum_of_blockPosDef hSymm hPos
              (by intro h; cases h)
          have hUL : A.upperLeft i i ≤ matNorm A.upperLeft :=
            le_trans (le_abs_self (A.upperLeft i i))
              (abs_matrix_entry_le_matNorm A.upperLeft i i)
          have hLR : A.lowerRight j j ≤ matNorm A.lowerRight :=
            le_trans (le_abs_self (A.lowerRight j j))
              (abs_matrix_entry_le_matNorm A.lowerRight j j)
          have hcross' :
              |A.upperRight i j| ≤
                (1 / 2 : ℝ) * (A.upperLeft i i + A.lowerRight j j) := by
            simpa [blockMatEntry] using hcross
          have hle :
              |A.upperRight i j| ≤ matNorm A.upperLeft + matNorm A.lowerRight := by
            nlinarith [hcross', hUL, hLR, matNorm_nonneg A.upperLeft,
              matNorm_nonneg A.lowerRight]
          simpa [blockMatEntry] using hle
  | inr i =>
      cases β with
      | inl j =>
          have hcross :
              |blockMatEntry A (Sum.inr i) (Sum.inl j)| ≤
                (1 / 2 : ℝ) *
                  (blockMatEntry A (Sum.inr i) (Sum.inr i) +
                    blockMatEntry A (Sum.inl j) (Sum.inl j)) :=
            abs_cross_blockMatEntry_le_diag_sum_of_blockPosDef hSymm hPos
              (by intro h; cases h)
          have hLR : A.lowerRight i i ≤ matNorm A.lowerRight :=
            le_trans (le_abs_self (A.lowerRight i i))
              (abs_matrix_entry_le_matNorm A.lowerRight i i)
          have hUL : A.upperLeft j j ≤ matNorm A.upperLeft :=
            le_trans (le_abs_self (A.upperLeft j j))
              (abs_matrix_entry_le_matNorm A.upperLeft j j)
          have hcross' :
              |A.lowerLeft i j| ≤
                (1 / 2 : ℝ) * (A.lowerRight i i + A.upperLeft j j) := by
            simpa [blockMatEntry] using hcross
          have hle :
              |A.lowerLeft i j| ≤ matNorm A.upperLeft + matNorm A.lowerRight := by
            nlinarith [hcross', hUL, hLR, matNorm_nonneg A.upperLeft,
              matNorm_nonneg A.lowerRight]
          simpa [blockMatEntry] using hle
      | inr j =>
          exact le_trans (abs_matrix_entry_le_matNorm A.lowerRight i j)
            (by nlinarith [matNorm_nonneg A.upperLeft])


end

end Ch04
end Book
end Homogenization
