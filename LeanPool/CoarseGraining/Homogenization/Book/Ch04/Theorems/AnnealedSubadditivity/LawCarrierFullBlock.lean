/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError.ResponseBounds
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Basic
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAveragesDefinitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.StationaryExpectations
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.ScalarizationDefinitions

public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.AnnealedSubadditivity.LawCarrierAnnealedMatrix

/-! # Law Carrier Full Block -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch04

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace RestrictionLawCarrier

/-- Integrability of the two diagonal coarse-block norms implies integrability
of the full doubled coarse block matrix.

This is the source theorem for the full-block hypotheses used by the public
annealed subadditivity and scalarization endpoints.  The mixed blocks are
controlled by the positive definiteness of the Chapter 2 coarse block matrix,
so downstream code should not assemble entrywise integrability by hand. -/
theorem integrable_coarseFullBlockMatrixAtCube_of_integrable_diagonalBlockNorms
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d)
    (hBInt : Integrable (fun a : RegCoeffField d => coarseBBlockNorm Q a.toFun) P)
    (hStarInt :
      Integrable (fun a : RegCoeffField d => coarseSigmaStarInvBlockNorm Q a.toFun) P) :
    Integrable (coarseFullBlockMatrixAtCube Q) P := by
  refine MeasureTheory.Integrable.of_eval ?_
  intro α
  refine MeasureTheory.Integrable.of_eval ?_
  intro β
  have hEntryMeas :
      AEMeasurable
        (fun a : RegCoeffField d =>
          blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) α β) P := by
    cases α with
    | inl i =>
        cases β with
        | inl j =>
            simpa [blockMatEntry] using
              hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet Q i j
        | inr j =>
            simpa [blockMatEntry] using
              hP.aemeasurable_coarseBlockMatrix_upperRight_apply_cubeSet Q i j
    | inr i =>
        cases β with
        | inl j =>
            simpa [blockMatEntry] using
              hP.aemeasurable_coarseBlockMatrix_lowerLeft_apply_cubeSet Q i j
        | inr j =>
            simpa [blockMatEntry] using
              hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet Q i j
  have hStrong :
      AEStronglyMeasurable
        (fun a : RegCoeffField d => coarseFullBlockMatrixAtCube Q a α β) P := by
    simpa [coarseFullBlockMatrixAtCube, coarseFullBlockMatrixObservable,
      toFullBlockMat, blockMatEntry] using hEntryMeas.aestronglyMeasurable
  refine (hBInt.add hStarInt).mono' hStrong ?_
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  have hEq :
      coarseBlockMatrix (cubeSet Q) a.toFun =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q) := by
    simpa [F] using
      RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
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
  have hBound :=
    abs_blockMatEntry_le_diagonalBlockNorms_of_symm_pos
      (A := coarseBlockMatrix (cubeSet Q) a.toFun) hSymm hPos α β
  simpa [Real.norm_eq_abs, coarseFullBlockMatrixAtCube, coarseFullBlockMatrixObservable,
    toFullBlockMat, blockMatEntry, coarseBBlockNorm, coarseSigmaStarInvBlockNorm]
    using hBound

/-- Full coarse-block integrability gives entrywise integrability of the
corresponding doubled coarse matrix. -/
theorem integrable_blockMatEntry_coarseBlockMatrix_cubeSet_of_integrable_coarseFullBlockMatrixAtCube
    {d : ℕ} {P : RestrictionCoeffLaw d} {Q : TriadicCube d}
    (hInt : Integrable (coarseFullBlockMatrixAtCube Q) P) :
    ∀ α β,
      Integrable
        (fun a : RegCoeffField d => blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) α β) P := by
  intro α β
  have hα : Integrable (fun a : RegCoeffField d => coarseFullBlockMatrixAtCube Q a α) P :=
    MeasureTheory.Integrable.eval hInt α
  have hαβ : Integrable (fun a : RegCoeffField d => coarseFullBlockMatrixAtCube Q a α β) P :=
    MeasureTheory.Integrable.eval hα β
  simpa [coarseFullBlockMatrixAtCube, coarseFullBlockMatrixObservable, toFullBlockMat,
    blockMatEntry] using hαβ

/-- Under a law carrier, the lower-right coarse block is a.e. positive
definite on every deterministic triadic cube. -/
theorem coarseBlockMatrix_lowerRight_posDef_cubeSet_ae
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) :
    ∀ᵐ a ∂P, (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight.PosDef := by
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  have hEq :
      coarseBlockMatrix (cubeSet Q) a.toFun =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q) := by
    simpa [F] using
      RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha Q
  rw [hEq]
  simpa using Ch02.sigmaStarInvCoarse_posDef (Ch02.cubeDomain Q) (F.coeffOn Q)

/-- Under a law carrier, the upper-left coarse block is a.e. positive
definite on every deterministic triadic cube. -/
theorem coarseBlockMatrix_upperLeft_posDef_cubeSet_ae
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) :
    ∀ᵐ a ∂P, (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft.PosDef := by
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  have hEq :
      coarseBlockMatrix (cubeSet Q) a.toFun =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q) := by
    simpa [F] using
      RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha Q
  rw [hEq]
  simpa using Ch02.bCoarse_posDef (Ch02.cubeDomain Q) (F.coeffOn Q)

/-- Full coarse-block integrability and primitive scalarization make the
inverse-star scalar coefficient strictly positive. -/
theorem Internal.barSigmaStarInv_pos_of_integrable_coarseFullBlockMatrixAtCube
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P) {n : ℤ}
    (hPrim : Internal.AnnealedPrimitiveScalarizationData (d := d) P n)
    (hBlock : Integrable (coarseFullBlockMatrixAtCube (originCube d n)) P) :
    0 < hPrim.barSigmaStarInv := by
  let : IsProbabilityMeasure P := hP.isProbability
  let F : RegCoeffField d → Mat d :=
    fun a => (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).lowerRight
  have hFint : Integrable F P := by
    refine MeasureTheory.Integrable.of_eval ?_
    intro i
    refine MeasureTheory.Integrable.of_eval ?_
    intro j
    exact
      integrable_blockMatEntry_coarseBlockMatrix_cubeSet_of_integrable_coarseFullBlockMatrixAtCube
        hBlock (Sum.inr i) (Sum.inr j)
  have hScalar : (∫ a, F a ∂P) = hPrim.barSigmaStarInv • (1 : Mat d) := by
    calc
      (∫ a, F a ∂P) = annealedSigmaStarInvAtScale P n := by
        ext i j
        rw [integral_matrix_apply (μ := P) (f := F) hFint i j]
        rfl
      _ = hPrim.barSigmaStarInv • (1 : Mat d) := hPrim.sigmaStarInv_eq
  exact
    scalar_coefficient_pos_of_smul_one_eq_integral_posDef
      (μ := P) (F := F) hFint
      (hP.coarseBlockMatrix_lowerRight_posDef_cubeSet_ae (originCube d n))
      hScalar

/-- Full coarse-block integrability and primitive scalarization make the
upper-left scalar coefficient strictly positive. -/
theorem Internal.barB_pos_of_integrable_coarseFullBlockMatrixAtCube
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P) {n : ℤ}
    (hPrim : Internal.AnnealedPrimitiveScalarizationData (d := d) P n)
    (hBlock : Integrable (coarseFullBlockMatrixAtCube (originCube d n)) P) :
    0 < hPrim.barB := by
  let : IsProbabilityMeasure P := hP.isProbability
  let F : RegCoeffField d → Mat d :=
    fun a => (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).upperLeft
  have hFint : Integrable F P := by
    refine MeasureTheory.Integrable.of_eval ?_
    intro i
    refine MeasureTheory.Integrable.of_eval ?_
    intro j
    exact
      integrable_blockMatEntry_coarseBlockMatrix_cubeSet_of_integrable_coarseFullBlockMatrixAtCube
        hBlock (Sum.inl i) (Sum.inl j)
  have hScalar : (∫ a, F a ∂P) = hPrim.barB • (1 : Mat d) := by
    calc
      (∫ a, F a ∂P) = annealedBAtScale P n := by
        ext i j
        rw [integral_matrix_apply (μ := P) (f := F) hFint i j]
        rfl
      _ = hPrim.barB • (1 : Mat d) := hPrim.b_eq
  exact
    scalar_coefficient_pos_of_smul_one_eq_integral_posDef
      (μ := P) (F := F) hFint
      (hP.coarseBlockMatrix_upperLeft_posDef_cubeSet_ae (originCube d n))
      hScalar

/-- Full coarse-block integrability makes the public scalar
`\bar\sigma_n` strictly positive. -/
theorem barSigmaAtScale_pos_of_integrable_coarseFullBlockMatrixAtCube
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P) {n : ℤ}
    (hBlock : Integrable (coarseFullBlockMatrixAtCube (originCube d n)) P) :
    0 < hP.barSigmaAtScale hStruct n := by
  have hPrim :=
    Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct n
  have hB : 0 < hPrim.barB :=
    Internal.barB_pos_of_integrable_coarseFullBlockMatrixAtCube hP hPrim hBlock
  simpa [RestrictionLawCarrier.barSigmaAtScale_eq_barBAtScale, RestrictionLawCarrier.barBAtScale,
    Internal.AnnealedPrimitiveScalarizationData.barB, hPrim]
    using hB

/-- Law-facing primitive lower bound `1 <= Theta_n`, stated at the primitive
scalarization level. -/
theorem Internal.one_le_primitive_contrast_of_integrable_coarseFullBlockMatrixAtCube
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P) {n : ℤ}
    (hPrim : Internal.AnnealedPrimitiveScalarizationData (d := d) P n)
    (hBlock : Integrable (coarseFullBlockMatrixAtCube (originCube d n)) P) :
    1 ≤ hPrim.contrast := by
  let : IsProbabilityMeasure P := hP.isProbability
  let e : Vec d := Pi.single (0 : Fin d) 1
  let s : ℝ := hPrim.barSigmaStarInv
  let b : ℝ := hPrim.barB
  let p : Vec d := s • e
  let q : Vec d := e
  have hExpected_nonneg :
      0 ≤ ∫ a, restrictionResponseJObservableCubeSet (originCube d n) p q a ∂P := by
    exact MeasureTheory.integral_nonneg_of_ae (by
      filter_upwards with a
      exact responseJ_nonneg (cubeSet (originCube d n)) p q a)
  have hLowerLeftZero :
      (annealedBlockMatrix P (cubeSet (originCube d n))).lowerLeft = 0 := by
    have h := hPrim.sigmaStarInvKappaMean_eq_zero
    simpa [annealedSigmaStarInvKappaMeanAtScale,
      annealedSigmaStarInvKappaMean] using congrArg Neg.neg h
  have hStar :
      (annealedBlockMatrix P (cubeSet (originCube d n))).lowerRight =
        s • (1 : Mat d) := by
    simpa [s, annealedSigmaStarInvAtScale, annealedSigmaStarInv] using
      hPrim.sigmaStarInv_eq
  have hB :
      (annealedBlockMatrix P (cubeSet (originCube d n))).upperLeft =
        b • (1 : Mat d) := by
    simpa [b, annealedBAtScale, annealedB] using hPrim.b_eq
  have hFormula :=
    hP.integral_restrictionResponseJObservableCubeSet_eq_quadratic_annealedBlockMatrix
      (originCube d n) p q hBlock
  have hOneP : matVecMul (1 : Mat d) p = p := by
    change (1 : Matrix (Fin d) (Fin d) ℝ).mulVec p = p
    exact Matrix.one_mulVec p
  have hZeroP : matVecMul (0 : Mat d) p = 0 := by
    funext i
    simp [matVecMul]
  have hEval :
      ∫ a, restrictionResponseJObservableCubeSet (originCube d n) p q a ∂P =
        (b * s - 1) * (s / 2) := by
    rw [hFormula, hLowerLeftZero, hStar, hB]
    simp [smul_matVecMul, hOneP, hZeroP, vecDot_smul_left,
      vecDot_smul_right, p, q, e, s, b, matVecMul_single, vecDot_single_left]
    ring_nf
  rw [hEval] at hExpected_nonneg
  have hStar_pos : 0 < s := by
    dsimp [s]
    exact Internal.barSigmaStarInv_pos_of_integrable_coarseFullBlockMatrixAtCube hP
      hPrim hBlock
  have hs_div_pos : 0 < s / 2 := by positivity
  have htheta_minus_nonneg : 0 ≤ b * s - 1 :=
    nonneg_of_mul_nonneg_left hExpected_nonneg hs_div_pos
  have htheta_ge : 1 ≤ b * s := sub_nonneg.mp htheta_minus_nonneg
  simpa [Internal.AnnealedPrimitiveScalarizationData.contrast, b, s] using htheta_ge

/-- Full coarse-block integrability and primitive scalarization make the
upper-left scalar coefficient nonnegative. -/
theorem Internal.barB_nonneg_of_integrable_coarseFullBlockMatrixAtCube
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P) {n : ℤ}
    (hPrim : Internal.AnnealedPrimitiveScalarizationData (d := d) P n)
    (hBlock : Integrable (coarseFullBlockMatrixAtCube (originCube d n)) P) :
    0 ≤ hPrim.barB := by
  have hContrast :
      1 ≤ hPrim.contrast :=
    Internal.one_le_primitive_contrast_of_integrable_coarseFullBlockMatrixAtCube hP
      hPrim hBlock
  have hContrast_nonneg : 0 ≤ hPrim.contrast :=
    le_trans zero_le_one hContrast
  have hStar_pos :
      0 < hPrim.barSigmaStarInv :=
    Internal.barSigmaStarInv_pos_of_integrable_coarseFullBlockMatrixAtCube hP
      hPrim hBlock
  exact
    nonneg_of_mul_nonneg_right
      (by
        simpa [Internal.AnnealedPrimitiveScalarizationData.contrast, mul_comm] using
          hContrast_nonneg)
      hStar_pos

/-- Law-facing scalar lower bound `1 <= Theta_n`, stated for the public
scalarization theory. -/
theorem Internal.one_le_scalar_contrast_of_primitive_of_integrable_coarseFullBlockMatrixAtCube
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P) {n : ℤ}
    (hScal : Internal.AnnealedScalarizationTheory (d := d) P)
    (hPrim : Internal.AnnealedPrimitiveScalarizationData (d := d) P n)
    (hBlock : Integrable (coarseFullBlockMatrixAtCube (originCube d n)) P) :
    1 ≤ hScal.contrast n := by
  simpa [Internal.AnnealedPrimitiveScalarizationData.scalar_contrast_eq hScal hPrim] using
    Internal.one_le_primitive_contrast_of_integrable_coarseFullBlockMatrixAtCube hP
      hPrim hBlock

/-- Law-facing annealed block monotonicity from full coarse-block
integrability.  This is the Ch5-facing version of
`RestrictionLawCarrier.blockMatLoewnerLE_annealedBlockMatrixAtScale`: downstream callers
should not assemble entrywise integrability by hand. -/
theorem blockMatLoewnerLE_annealedBlockMatrixAtScale_of_integrable_coarseFullBlockMatrixAtCube
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hstat : RestrictionStationaryLaw P) {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    (hParentInt : Integrable (coarseFullBlockMatrixAtCube (originCube d m)) P)
    (hDescInt :
      ∀ R, R ∈ descendantsAtScale (originCube d m) n →
        Integrable (coarseFullBlockMatrixAtCube R) P) :
    BlockMatLoewnerLE (annealedBlockMatrixAtScale P m)
      (annealedBlockMatrixAtScale P n) :=
  hP.blockMatLoewnerLE_annealedBlockMatrixAtScale hstat hn hnm
    (integrable_blockMatEntry_coarseBlockMatrix_cubeSet_of_integrable_coarseFullBlockMatrixAtCube
      hParentInt)
    (fun R hR =>
      integrable_blockMatEntry_coarseBlockMatrix_cubeSet_of_integrable_coarseFullBlockMatrixAtCube
        (hDescInt R hR))

/-- Law-facing scalar chain from full coarse-block integrability. -/
theorem Internal.scalar_chain_of_primitive_of_integrable_coarseFullBlockMatrixAtCube
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hstat : RestrictionStationaryLaw P) {n m : ℤ} (hn_nonneg : 0 ≤ n) (hnm : n ≤ m)
    (hScal : Internal.AnnealedScalarizationTheory (d := d) P)
    (hPrim_m : Internal.AnnealedPrimitiveScalarizationData (d := d) P m)
    (hPrim_n : Internal.AnnealedPrimitiveScalarizationData (d := d) P n)
    (hParentInt : Integrable (coarseFullBlockMatrixAtCube (originCube d m)) P)
    (hDescInt :
      ∀ R, R ∈ descendantsAtScale (originCube d m) n →
        Integrable (coarseFullBlockMatrixAtCube R) P)
    (hStar_m_pos : 0 < hPrim_m.barSigmaStarInv)
    (hContrast_m : 1 ≤ hPrim_m.contrast) :
    hScal.barSigmaStar n ≤ hScal.barSigmaStar m ∧
      hScal.barSigmaStar m ≤ hScal.barSigma m ∧
        hScal.barSigma m ≤ hScal.barSigma n :=
  scalar_chain_of_primitive_block_mono hScal hPrim_m hPrim_n
    (hP.blockMatLoewnerLE_annealedBlockMatrixAtScale_of_integrable_coarseFullBlockMatrixAtCube
      hstat hn_nonneg hnm hParentInt hDescInt)
    hStar_m_pos hContrast_m

/-- Law-facing primitive contrast monotonicity from full coarse-block
integrability. -/
theorem Internal.primitive_contrast_le_of_integrable_coarseFullBlockMatrixAtCube
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hstat : RestrictionStationaryLaw P) {n m : ℤ} (hn_nonneg : 0 ≤ n) (hnm : n ≤ m)
    (hPrim_m : Internal.AnnealedPrimitiveScalarizationData (d := d) P m)
    (hPrim_n : Internal.AnnealedPrimitiveScalarizationData (d := d) P n)
    (hParentInt : Integrable (coarseFullBlockMatrixAtCube (originCube d m)) P)
    (hDescInt :
      ∀ R, R ∈ descendantsAtScale (originCube d m) n →
        Integrable (coarseFullBlockMatrixAtCube R) P)
    (hStar_m_nonneg : 0 ≤ hPrim_m.barSigmaStarInv)
    (hB_n_nonneg : 0 ≤ hPrim_n.barB) :
    hPrim_m.contrast ≤ hPrim_n.contrast :=
  primitive_contrast_le_of_block_mono hPrim_m hPrim_n
    (hP.blockMatLoewnerLE_annealedBlockMatrixAtScale_of_integrable_coarseFullBlockMatrixAtCube
      hstat hn_nonneg hnm hParentInt hDescInt)
    hStar_m_nonneg hB_n_nonneg

/-- Law-facing scalar contrast monotonicity from full coarse-block
integrability. -/
theorem Internal.scalar_contrast_le_of_primitive_of_integrable_coarseFullBlockMatrixAtCube
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hstat : RestrictionStationaryLaw P) {n m : ℤ} (hn_nonneg : 0 ≤ n) (hnm : n ≤ m)
    (hScal : Internal.AnnealedScalarizationTheory (d := d) P)
    (hPrim_m : Internal.AnnealedPrimitiveScalarizationData (d := d) P m)
    (hPrim_n : Internal.AnnealedPrimitiveScalarizationData (d := d) P n)
    (hParentInt : Integrable (coarseFullBlockMatrixAtCube (originCube d m)) P)
    (hDescInt :
      ∀ R, R ∈ descendantsAtScale (originCube d m) n →
        Integrable (coarseFullBlockMatrixAtCube R) P)
    (hStar_m_nonneg : 0 ≤ hPrim_m.barSigmaStarInv)
    (hB_n_nonneg : 0 ≤ hPrim_n.barB) :
    hScal.contrast m ≤ hScal.contrast n :=
  scalar_contrast_le_of_primitive_block_mono hScal hPrim_m hPrim_n
    (hP.blockMatLoewnerLE_annealedBlockMatrixAtScale_of_integrable_coarseFullBlockMatrixAtCube
      hstat hn_nonneg hnm hParentInt hDescInt)
    hStar_m_nonneg hB_n_nonneg

end RestrictionLawCarrier

end

end Ch04
end Book
end Homogenization
