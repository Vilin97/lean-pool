/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.Expectations
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.Scalarization
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.TriadicCubeTranslation
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Translation
import LeanPool.CoarseGraining.Homogenization.Probability.LocalObservable

/-! # Stationary Expectations -/

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Stationary response expectations

This file is the public Chapter 4 surface for the stationarity step used by
the expectation/moment arguments: at nonnegative scales, deterministic child
cubes are integer translates of the origin cube at the same scale, so
stationarity identifies their annealed response expectations.

The statements are phrased directly in terms of the clean response expectation
objects from `Expectations.lean`.
-/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise

/-- Scalar response is translation-covariant as a set-indexed coefficient-field
observable. -/
theorem responseJCubeSet_translation_covariant {d : ℕ} (p q : Vec d) :
    IsTranslationCovariant
      (fun U : Set (Vec d) => fun a : CoeffField d => ResponseJ U p q a) := by
  intro U z a
  simpa [translateByInt] using
    ResponseJ_translateSet_eq_translateCoeffField (intVecToRealVec z) U p q a

/-- Coarse block matrix entries are translation-covariant as set-indexed
coefficient-field observables. -/
theorem coarseBlockMatrix_entry_translation_covariant {d : ℕ}
    (α β : BlockCoord d) :
    IsTranslationCovariant
      (fun U : Set (Vec d) => fun a : CoeffField d =>
        blockMatEntry (coarseBlockMatrix U a) α β) := by
  intro U z a
  simpa [translateByInt] using
    congrArg (fun A : BlockMat d => blockMatEntry A α β)
      (coarseBlockMatrix_translateSet_eq_translateCoeffField
        (intVecToRealVec z) U a)

/-- Scalar block diagonal center used to normalize full-block fluctuations at a
structural-law scale.  The lower-right block is the inverse starred scalar. -/
noncomputable def scalarAnnealedBlockMatrixAtScale {d : ℕ} [NeZero d]
    {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P) (hStruct : RestrictionStructuralLaw P)
    (m : ℤ) : BlockMat d :=
  Ch02.blockDiag
    (hP.barSigmaAtScale hStruct m • (1 : Mat d))
    ((hP.barSigmaStarAtScale hStruct m)⁻¹ • (1 : Mat d))

/-- Diagonal full-block normalization associated with scalar blocks `b,c`. -/
noncomputable def scalarFullBlockInvSqrtDiag {d : ℕ} (b c : ℝ) :
    BlockCoord d → ℝ
  | Sum.inl _ => (Real.sqrt b)⁻¹
  | Sum.inr _ => Real.sqrt c

/-- Manuscript normalized full-block fluctuation observable at center scale
`m`, written for an arbitrary deterministic set.  The norm is the Euclidean
operator norm of the associated full block matrix. -/
noncomputable def fullBlockNormalizedFluctuationOperatorNormSq
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d}
    (hP : RestrictionLawCarrier P) (hStruct : RestrictionStructuralLaw P)
    (m : ℤ) (U : Set (Vec d)) (a : CoeffField d) : ℝ :=
  let b := hP.barSigmaAtScale hStruct m
  let c := hP.barSigmaStarAtScale hStruct m
  let D : FullBlockMat d := Matrix.diagonal (scalarFullBlockInvSqrtDiag b c)
  let A := coarseBlockMatrix U a
  let Abar := scalarAnnealedBlockMatrixAtScale hP hStruct m
  ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
      (D * (toFullBlockMat A - toFullBlockMat Abar) * D)‖ ^ 2

/-- Manuscript normalized full-block fluctuation observable on a triadic cube.
The norm is the Euclidean operator norm, not the Frobenius norm. -/
noncomputable def fullBlockNormalizedFluctuationOperatorNormSqAtScale
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d}
    (hP : RestrictionLawCarrier P) (hStruct : RestrictionStructuralLaw P)
    (m : ℤ) (R : TriadicCube d) (a : RegCoeffField d) : ℝ :=
  fullBlockNormalizedFluctuationOperatorNormSq hP hStruct m (cubeSet R) a.toFun

/-- The normalized full-block fluctuation observable is translation-covariant
in its deterministic set argument. -/
theorem fullBlockNormalizedFluctuationOperatorNormSq_translation_covariant
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d}
    (hP : RestrictionLawCarrier P) (hStruct : RestrictionStructuralLaw P) (m : ℤ) :
    IsTranslationCovariant
      (fun U : Set (Vec d) => fun a : CoeffField d =>
        fullBlockNormalizedFluctuationOperatorNormSq hP hStruct m U a) := by
  intro U z a
  simp [fullBlockNormalizedFluctuationOperatorNormSq, translateByInt,
    coarseBlockMatrix_translateSet_eq_translateCoeffField]

/-- Carrier bridge for integer translation: precomposition on the carrier
projects to the raw integer translation (rfl). -/
theorem translateReg_toFun {d : ℕ} (z : Fin d → ℤ) (a : RegCoeffField d) :
    (translateReg (intVecToRealVec z) a).toFun = translateByInt z a.toFun := rfl

/-- Translation transfer under a restriction-stationary carrier law for a raw
translation-covariant observable
composed with `toFun` integrates equally on translated sets under a stationary
carrier law.  Uses `IsStationaryR.integral_comp_translateReg` and the
`translateReg`/`translateByInt` bridge. -/
theorem integral_comp_toFun_translation_transfer_of_restrictionStationaryLaw
    {d : ℕ} {P : RestrictionCoeffLaw d} {X : Set (Vec d) → CoeffField d → ℝ}
    (hstat : RestrictionStationaryLaw P) {U : Set (Vec d)}
    (hmeas : AEStronglyMeasurable (fun a : RegCoeffField d => X U a.toFun) P)
    (hcov : IsTranslationCovariant X) (z : Fin d → ℤ) :
    ∫ a, X (translateSet (intVecToRealVec z) U) a.toFun ∂P =
      ∫ a, X U a.toFun ∂P := by
  have hbridge :
      (fun a : RegCoeffField d => X (translateSet (intVecToRealVec z) U) a.toFun) =
        fun a : RegCoeffField d =>
          (fun a : RegCoeffField d => X U a.toFun) (translateReg (intVecToRealVec z) a) := by
    funext a
    show X (translateSet (intVecToRealVec z) U) a.toFun =
      X U (translateReg (intVecToRealVec z) a).toFun
    rw [hcov U z a.toFun, translateReg_toFun]
  calc
    ∫ a, X (translateSet (intVecToRealVec z) U) a.toFun ∂P
        = ∫ a, (fun a : RegCoeffField d => X U a.toFun)
            (translateReg (intVecToRealVec z) a) ∂P := by rw [hbridge]
    _ = ∫ a, X U a.toFun ∂P :=
          hstat.integral_comp_translateReg z (fun a => X U a.toFun) hmeas

/-- Restriction translation covariance: a set-indexed carrier observable commutes
with spatial integer translation via the carrier translation `translateReg`. -/
def IsRestrictionTranslationCovariant {β : Type*} {d : ℕ}
    (X : Set (Vec d) → RegCoeffField d → β) : Prop :=
  ∀ (U : Set (Vec d)) (z : Fin d → ℤ) (a : RegCoeffField d),
    X (translateSet (intVecToRealVec z) U) a =
      X U (translateReg (intVecToRealVec z) a)

/-- A raw translation-covariant observable, precomposed with `toFun`, is
restriction translation covariant. -/
theorem isRestrictionTranslationCovariant_comp_toFun {β : Type*} {d : ℕ}
    {X : Set (Vec d) → CoeffField d → β} (hX : IsTranslationCovariant X) :
    IsRestrictionTranslationCovariant (fun U a => X U a.toFun) := by
  intro U z a
  show X (translateSet (intVecToRealVec z) U) a.toFun =
    X U (translateReg (intVecToRealVec z) a).toFun
  rw [hX U z a.toFun, translateReg_toFun]

/-- Restriction-carrier analogue of
`comp_translateByInt_eq_of_isTranslationCovariant`. -/
theorem comp_translateReg_eq_of_isRestrictionTranslationCovariant {β : Type*} {d : ℕ}
    {X : Set (Vec d) → RegCoeffField d → β} (hX : IsRestrictionTranslationCovariant X)
    (U : Set (Vec d)) (z : Fin d → ℤ) :
    X (translateSet (intVecToRealVec z) U) =
      X U ∘ translateReg (intVecToRealVec z) := by
  funext a
  exact hX U z a

/-- Restriction-carrier analogue of
`map_eq_map_translateByInt_of_isTranslationCovariant`. -/
theorem map_eq_map_translateReg_of_isRestrictionTranslationCovariant {β : Type*}
    [MeasurableSpace β] {d : ℕ} {P : RestrictionCoeffLaw d}
    {X : Set (Vec d) → RegCoeffField d → β}
    (hP : RestrictionStationaryLaw P) {U : Set (Vec d)} (hX_meas : Measurable (X U))
    (hX_cov : IsRestrictionTranslationCovariant X) (z : Fin d → ℤ) :
    Measure.map (X (translateSet (intVecToRealVec z) U)) P =
      Measure.map (X U) P := by
  calc
    Measure.map (X (translateSet (intVecToRealVec z) U)) P =
        Measure.map (X U ∘ translateReg (intVecToRealVec z)) P := by
          rw [comp_translateReg_eq_of_isRestrictionTranslationCovariant hX_cov U z]
    _ = Measure.map (X U) (Measure.map (translateReg (intVecToRealVec z)) P) := by
          symm
          simpa [Function.comp] using
            (Measure.map_map hX_meas (measurable_translateReg (intVecToRealVec z))
              (μ := P))
    _ = Measure.map (X U) P := by rw [hP z]

/-- A.e.-measurable carrier analogue of
`map_eq_map_translateByInt_of_isTranslationCovariant_aemeasurable`. -/
theorem map_eq_map_translateReg_of_isRestrictionTranslationCovariant_aemeasurable {β : Type*}
    [MeasurableSpace β] {d : ℕ} {P : RestrictionCoeffLaw d}
    {X : Set (Vec d) → RegCoeffField d → β}
    (hP : RestrictionStationaryLaw P) {U : Set (Vec d)} (hX_aemeas : AEMeasurable (X U) P)
    (hX_cov : IsRestrictionTranslationCovariant X) (z : Fin d → ℤ) :
    Measure.map (X (translateSet (intVecToRealVec z) U)) P =
      Measure.map (X U) P := by
  calc
    Measure.map (X (translateSet (intVecToRealVec z) U)) P =
        Measure.map (X U ∘ translateReg (intVecToRealVec z)) P := by
          rw [comp_translateReg_eq_of_isRestrictionTranslationCovariant hX_cov U z]
    _ = Measure.map (X U) (Measure.map (translateReg (intVecToRealVec z)) P) := by
          symm
          exact AEMeasurable.map_map_of_aemeasurable
            (by simpa [hP z] using hX_aemeas)
            (measurable_translateReg (intVecToRealVec z)).aemeasurable
    _ = Measure.map (X U) P := by rw [hP z]

/-- Carrier analogue of
`integral_eq_of_isTranslationCovariant_of_isStationary`. -/
theorem integral_eq_of_isRestrictionTranslationCovariant_of_stationary {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {d : ℕ} {P : RestrictionCoeffLaw d} {X : Set (Vec d) → RegCoeffField d → E}
    (hP : RestrictionStationaryLaw P) {U : Set (Vec d)}
    (hX_meas : Measurable (X U))
    (hX_cov : IsRestrictionTranslationCovariant X) (z : Fin d → ℤ) :
    ∫ a, X (translateSet (intVecToRealVec z) U) a ∂P = ∫ a, X U a ∂P := by
  rw [comp_translateReg_eq_of_isRestrictionTranslationCovariant hX_cov U z]
  exact integral_comp_eq_of_map_eq
    (measurable_translateReg (intVecToRealVec z)) (hP z) (X U)
    hX_meas.aestronglyMeasurable

/-- A.e.-strongly-measurable carrier analogue of
`integral_eq_of_isTranslationCovariant_of_isStationary_aestronglyMeasurable`. -/
theorem integral_eq_of_isRestrictionTranslationCovariant_of_stationary_aestronglyMeasurable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {d : ℕ} {P : RestrictionCoeffLaw d} {X : Set (Vec d) → RegCoeffField d → E}
    (hP : RestrictionStationaryLaw P) {U : Set (Vec d)}
    (hX_aemeas : AEStronglyMeasurable (X U) P)
    (hX_cov : IsRestrictionTranslationCovariant X) (z : Fin d → ℤ) :
    ∫ a, X (translateSet (intVecToRealVec z) U) a ∂P = ∫ a, X U a ∂P := by
  rw [comp_translateReg_eq_of_isRestrictionTranslationCovariant hX_cov U z]
  exact integral_comp_eq_of_map_eq
    (measurable_translateReg (intVecToRealVec z)) (hP z) (X U) hX_aemeas

namespace RestrictionLawCarrier

/-- Under stationarity, the annealed response on a nonnegative-scale cube is
the annealed response on the origin cube at the same scale. -/
theorem expectedResponseJCubeSet_eq_originCube_of_stationary
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hstat : RestrictionStationaryLaw P) (R : TriadicCube d) (hR_nonneg : 0 ≤ R.scale)
    (p q : Vec d) :
    expectedResponseJCubeSet P R p q =
      expectedResponseJCubeSet P (originCube d R.scale) p q := by
  have hshift :=
    cubeSet_eq_translateSet_originCube_of_nonneg_scale (R := R) hR_nonneg
  calc
    expectedResponseJCubeSet P R p q
        = ∫ a, ResponseJ (cubeSet R) p q a.toFun ∂P := rfl
    _ =
        ∫ a,
          ResponseJ
            (translateSet (intVecToRealVec (scaleTranslationShift R.scale R))
              (cubeSet (originCube d R.scale))) p q a.toFun ∂P := by
          rw [hshift]
    _ = ∫ a, ResponseJ (cubeSet (originCube d R.scale)) p q a.toFun ∂P :=
          integral_comp_toFun_translation_transfer_of_restrictionStationaryLaw (P := P) hstat
            (X := fun U a => ResponseJ U p q a)
            (U := cubeSet (originCube d R.scale))
            (by
              simpa [restrictionResponseJObservableCubeSet] using!
                hP.aestronglyMeasurable_restrictionResponseJObservableCubeSet
                  (originCube d R.scale) p q)
            (responseJCubeSet_translation_covariant p q)
            (scaleTranslationShift R.scale R)
    _ = expectedResponseJCubeSet P (originCube d R.scale) p q := rfl

/-- Under stationarity, every coarse block matrix entry on a nonnegative-scale
cube has the same expectation as the corresponding origin-cube entry. -/
theorem integral_coarseBlockMatrix_entry_cubeSet_eq_originCube_of_stationary
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hstat : RestrictionStationaryLaw P) (R : TriadicCube d) (hR_nonneg : 0 ≤ R.scale)
    (α β : BlockCoord d) :
    ∫ a, blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) α β ∂P =
      ∫ a,
        blockMatEntry (coarseBlockMatrix (cubeSet (originCube d R.scale)) a.toFun) α β ∂P := by
  have hshift :=
    cubeSet_eq_translateSet_originCube_of_nonneg_scale (R := R) hR_nonneg
  have hmeas :
      AEStronglyMeasurable
        (fun a : RegCoeffField d =>
          blockMatEntry (coarseBlockMatrix (cubeSet (originCube d R.scale)) a.toFun) α β) P := by
    cases α with
    | inl i =>
        cases β with
        | inl j =>
            simpa [blockMatEntry] using
              (hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet
                (originCube d R.scale) i j).aestronglyMeasurable
        | inr j =>
            simpa [blockMatEntry] using
              (hP.aemeasurable_coarseBlockMatrix_upperRight_apply_cubeSet
                (originCube d R.scale) i j).aestronglyMeasurable
    | inr i =>
        cases β with
        | inl j =>
            simpa [blockMatEntry] using
              (hP.aemeasurable_coarseBlockMatrix_lowerLeft_apply_cubeSet
                (originCube d R.scale) i j).aestronglyMeasurable
        | inr j =>
            simpa [blockMatEntry] using
              (hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet
                (originCube d R.scale) i j).aestronglyMeasurable
  calc
    ∫ a, blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) α β ∂P
        =
      ∫ a,
        blockMatEntry
          (coarseBlockMatrix
            (translateSet (intVecToRealVec (scaleTranslationShift R.scale R))
              (cubeSet (originCube d R.scale))) a.toFun) α β ∂P := by
          rw [hshift]
    _ =
      ∫ a,
        blockMatEntry (coarseBlockMatrix (cubeSet (originCube d R.scale)) a.toFun) α β ∂P :=
          integral_comp_toFun_translation_transfer_of_restrictionStationaryLaw (P := P) hstat
            (X := fun U a => blockMatEntry (coarseBlockMatrix U a) α β)
            (U := cubeSet (originCube d R.scale)) hmeas
            (coarseBlockMatrix_entry_translation_covariant α β)
            (scaleTranslationShift R.scale R)

/-- Under stationarity, a child cube of an origin cube has the same annealed
response as the origin cube at the child scale. -/
theorem expectedResponseJCubeSet_eq_originCube_of_mem_descendantsAtScale_originCube
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hstat : RestrictionStationaryLaw P) {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale (originCube d m) n)
    (p q : Vec d) :
    expectedResponseJCubeSet P R p q =
      expectedResponseJCubeSet P (originCube d n) p q := by
  have hscale : R.scale = n :=
    scale_eq_of_mem_descendantsAtScale_originCube hnm hR
  have hR_nonneg : 0 ≤ R.scale := by
    simpa [hscale] using hn
  calc
    expectedResponseJCubeSet P R p q =
        expectedResponseJCubeSet P (originCube d R.scale) p q :=
      hP.expectedResponseJCubeSet_eq_originCube_of_stationary hstat R hR_nonneg p q
    _ = expectedResponseJCubeSet P (originCube d n) p q := by
      rw [hscale]

/-- Under stationarity, every coarse block matrix entry on a child cube of an
origin cube has the same expectation as the corresponding origin-cube entry at
the child scale. -/
theorem integral_coarseBlockMatrix_entry_cubeSet_eq_originCube_of_mem_descendantsAtScale_originCube
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hstat : RestrictionStationaryLaw P) {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale (originCube d m) n)
    (α β : BlockCoord d) :
    ∫ a, blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) α β ∂P =
      ∫ a, blockMatEntry (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun) α β ∂P := by
  have hscale : R.scale = n :=
    scale_eq_of_mem_descendantsAtScale_originCube hnm hR
  have hR_nonneg : 0 ≤ R.scale := by
    simpa [hscale] using hn
  calc
    ∫ a, blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) α β ∂P
        =
      ∫ a,
        blockMatEntry (coarseBlockMatrix (cubeSet (originCube d R.scale)) a.toFun) α β ∂P :=
        hP.integral_coarseBlockMatrix_entry_cubeSet_eq_originCube_of_stationary
          hstat R hR_nonneg α β
    _ =
      ∫ a, blockMatEntry (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun) α β ∂P := by
        rw [hscale]

/-- Under stationarity, the normalized full-block fluctuation on a
nonnegative-scale cube has the same expectation as the corresponding
origin-cube fluctuation.  The norm is the Euclidean operator norm of the full
block matrix. -/
theorem integral_fullBlockNormalizedFluctuationOperatorNormSqAtScale_eq_originCube_of_stationary
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hstat : RestrictionStationaryLaw P) (hStruct : RestrictionStructuralLaw P) (center : ℤ)
    (R : TriadicCube d) (hR_nonneg : 0 ≤ R.scale)
    (hOrigin :
      Integrable
        (fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d R.scale)) P) :
    ∫ a, fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct center R a ∂P =
      ∫ a,
        fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d R.scale) a ∂P := by
  have hshift :=
    cubeSet_eq_translateSet_originCube_of_nonneg_scale (R := R) hR_nonneg
  calc
    ∫ a, fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct center R a ∂P
        =
      ∫ a,
        fullBlockNormalizedFluctuationOperatorNormSq hP hStruct center
          (translateSet (intVecToRealVec (scaleTranslationShift R.scale R))
            (cubeSet (originCube d R.scale))) a.toFun ∂P := by
          simp only [fullBlockNormalizedFluctuationOperatorNormSqAtScale, hshift]
    _ =
      ∫ a,
        fullBlockNormalizedFluctuationOperatorNormSq hP hStruct center
          (cubeSet (originCube d R.scale)) a.toFun ∂P :=
          integral_comp_toFun_translation_transfer_of_restrictionStationaryLaw (P := P) hstat
            (X := fun U a =>
              fullBlockNormalizedFluctuationOperatorNormSq hP hStruct center U a)
            (U := cubeSet (originCube d R.scale))
            (by
              simpa [fullBlockNormalizedFluctuationOperatorNormSqAtScale] using!
                hOrigin.aestronglyMeasurable)
            (fullBlockNormalizedFluctuationOperatorNormSq_translation_covariant
              hP hStruct center)
            (scaleTranslationShift R.scale R)
    _ =
      ∫ a,
        fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d R.scale) a ∂P := rfl

/-- Under stationarity, integrability of the origin-cube normalized full-block
fluctuation transfers to every same-scale cube. -/
theorem integrable_fullBlockNormalizedFluctuationOperatorNormSqAtScale_of_stationary
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hstat : RestrictionStationaryLaw P) (hStruct : RestrictionStructuralLaw P) (center : ℤ)
    (R : TriadicCube d) (hR_nonneg : 0 ≤ R.scale)
    (hOrigin :
      Integrable
        (fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d R.scale)) P) :
    Integrable
      (fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct center R) P := by
  let z : Fin d → ℤ := scaleTranslationShift R.scale R
  have hset :
      cubeSet R =
        translateSet (intVecToRealVec z) (cubeSet (originCube d R.scale)) := by
    simpa [z] using
      cubeSet_eq_translateSet_originCube_of_nonneg_scale (R := R) hR_nonneg
  have hmap :
      Integrable
        (fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct center
          (originCube d R.scale))
        (Measure.map (translateReg (intVecToRealVec z)) P) := by
    rw [hstat z]; exact hOrigin
  have hcomp := hmap.comp_measurable (measurable_translateReg (intVecToRealVec z))
  refine hcomp.congr ?_
  filter_upwards with a
  show fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct center
        (originCube d R.scale) (translateReg (intVecToRealVec z) a) =
      fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct center R a
  simp only [fullBlockNormalizedFluctuationOperatorNormSqAtScale, translateReg_toFun]
  rw [hset]
  exact
    (fullBlockNormalizedFluctuationOperatorNormSq_translation_covariant
      hP hStruct center (cubeSet (originCube d R.scale)) z a.toFun).symm

/-- Under stationarity, integrability of the origin-cube normalized full-block
fluctuation at the child scale transfers to descendants of a larger origin
cube. -/
theorem integrable_fullBlockNormalizedFluctuationOperatorNormSqAtScale_of_mem_descendantsAtScale_originCube
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hstat : RestrictionStationaryLaw P) (hStruct : RestrictionStructuralLaw P) (center : ℤ)
    {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale (originCube d m) n)
    (hOrigin :
      Integrable
        (fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d n)) P) :
    Integrable
      (fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct center R) P := by
  have hscale : R.scale = n :=
    scale_eq_of_mem_descendantsAtScale_originCube hnm hR
  have hR_nonneg : 0 ≤ R.scale := by
    simpa [hscale] using hn
  exact
    hP.integrable_fullBlockNormalizedFluctuationOperatorNormSqAtScale_of_stationary
      hstat hStruct center R hR_nonneg (by simpa [hscale] using hOrigin)

/-- Under stationarity, the expectation of a descendant average of normalized
full-block fluctuation observables is the corresponding origin-cube
expectation at the descendant scale.  The observable uses the Euclidean
operator norm of the full block matrix. -/
theorem integral_descendantsAverage_fullBlockNormalizedFluctuationOperatorNormSqAtScale_eq_originCube_of_stationary
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hstat : RestrictionStationaryLaw P) (hStruct : RestrictionStructuralLaw P) (center : ℤ)
    {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    (hOrigin :
      Integrable
        (fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d n)) P) :
    ∫ a,
        descendantsAverage (originCube d m) (Int.toNat (m - n))
          (fun R =>
            fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct center R a) ∂P =
      ∫ a,
        fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d n) a ∂P := by
  classical
  let Q : TriadicCube d := originCube d m
  let j : ℕ := Int.toNat (m - n)
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  have hDepth :
      ∀ R, R ∈ descendantsAtDepth Q j →
        Integrable
          (fullBlockNormalizedFluctuationOperatorNormSqAtScale
            hP hStruct center R) P := by
    intro R hR
    have hRscale : R ∈ descendantsAtScale (originCube d m) n := by
      simpa [Q, j, descendantsAtScale_eq_descendantsAtDepth (originCube d m) hnm] using! hR
    exact
      hP.integrable_fullBlockNormalizedFluctuationOperatorNormSqAtScale_of_mem_descendantsAtScale_originCube
        hstat hStruct center hn hnm hRscale hOrigin
  calc
    ∫ a,
        descendantsAverage (originCube d m) (Int.toNat (m - n))
          (fun R =>
            fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct center R a) ∂P
        =
      descendantsAverage Q j
        (fun R =>
          ∫ a,
            fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct center R a ∂P) :=
        integral_descendantsAverage_eq_descendantsAverage_integral
          (P := P) (Q := Q) (j := j)
          (F := fun R a =>
            fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct center R a) hDepth
    _ =
      descendantsAverage Q j
        (fun _R =>
          ∫ a,
            fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct center (originCube d n) a ∂P) := by
        unfold descendantsAverage
        refine congrArg (fun t : ℝ => ((D.card : ℝ)⁻¹) * t) ?_
        refine Finset.sum_congr rfl ?_
        intro R hR
        have hRscale : R ∈ descendantsAtScale (originCube d m) n := by
          simpa [Q, j, descendantsAtScale_eq_descendantsAtDepth (originCube d m) hnm] using! hR
        have hscale : R.scale = n :=
          scale_eq_of_mem_descendantsAtScale_originCube hnm hRscale
        have hR_nonneg : 0 ≤ R.scale := by
          simpa [hscale] using hn
        calc
          ∫ a,
              fullBlockNormalizedFluctuationOperatorNormSqAtScale
                hP hStruct center R a ∂P
              =
            ∫ a,
              fullBlockNormalizedFluctuationOperatorNormSqAtScale
                hP hStruct center (originCube d R.scale) a ∂P :=
              hP.integral_fullBlockNormalizedFluctuationOperatorNormSqAtScale_eq_originCube_of_stationary
                hstat hStruct center R hR_nonneg (by simpa [hscale] using hOrigin)
          _ =
            ∫ a,
              fullBlockNormalizedFluctuationOperatorNormSqAtScale
                hP hStruct center (originCube d n) a ∂P := by
              rw [hscale]
    _ =
      ∫ a,
        fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d n) a ∂P := by
        simp [descendantsAverage_const]

/-- Full coarse-block integrability transfers from the origin cube at scale
`n` to every scale-`n` descendant of the origin cube at a larger scale.  This
is the stationarity source theorem for the descendant integrability hypotheses
in annealed subadditivity. -/
theorem integrable_coarseFullBlockMatrixAtCube_of_mem_descendantsAtScale_originCube
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (_hP : RestrictionLawCarrier P)
    (hstat : RestrictionStationaryLaw P) {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale (originCube d m) n)
    (hOrigin : Integrable (coarseFullBlockMatrixAtCube (originCube d n)) P) :
    Integrable (coarseFullBlockMatrixAtCube R) P := by
  let z : Fin d → ℤ := scaleTranslationShift n R
  have hset :
      cubeSet R =
        translateSet (intVecToRealVec z) (cubeSet (originCube d n)) := by
    simpa [z] using
      cubeSet_eq_translateSet_originCube_of_mem_descendantsAtScale_originCube
        hn hnm hR
  have hmap :
      Integrable (coarseFullBlockMatrixAtCube (originCube d n))
        (Measure.map (translateReg (intVecToRealVec z)) P) := by
    rw [hstat z]; exact hOrigin
  have hcomp := hmap.comp_measurable (measurable_translateReg (intVecToRealVec z))
  refine hcomp.congr ?_
  filter_upwards with a
  show coarseFullBlockMatrixAtCube (originCube d n) (translateReg (intVecToRealVec z) a) =
      coarseFullBlockMatrixAtCube R a
  simp only [coarseFullBlockMatrixAtCube, coarseFullBlockMatrixObservable, translateReg_toFun]
  rw [hset, coarseBlockMatrix_translateSet_eq_translateCoeffField]
  rfl

/-- Under stationarity, the finite descendant average of child annealed
responses equals the annealed response on the origin cube at the child scale. -/
theorem expectedDescendantsAverageResponseJCubeSet_eq_originCube_of_stationary
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hstat : RestrictionStationaryLaw P) {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    (p q : Vec d) :
    expectedDescendantsAverageResponseJCubeSet P (originCube d m)
        (Int.toNat (m - n)) p q =
      expectedResponseJCubeSet P (originCube d n) p q := by
  classical
  let D : Finset (TriadicCube d) :=
    descendantsAtDepth (originCube d m) (Int.toNat (m - n))
  have hDscale : D = descendantsAtScale (originCube d m) n := by
    simpa [D, originCube] using
      (descendantsAtScale_eq_descendantsAtDepth (originCube d m) hnm).symm
  have hD_nonempty : D.Nonempty := by
    simpa [D] using descendantsAtDepth_nonempty (originCube d m) (Int.toNat (m - n))
  have hcard_ne : ((D.card : ℝ) ≠ 0) := by
    exact_mod_cast Finset.card_ne_zero.mpr hD_nonempty
  calc
    expectedDescendantsAverageResponseJCubeSet P (originCube d m)
        (Int.toNat (m - n)) p q
        =
      (D.card : ℝ)⁻¹ *
        (∑ R ∈ D, expectedResponseJCubeSet P R p q) := by
          simp [expectedDescendantsAverageResponseJCubeSet, descendantsAverage, D]
    _ =
      (D.card : ℝ)⁻¹ *
        (∑ _R ∈ D, expectedResponseJCubeSet P (originCube d n) p q) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro R hR
          exact
            hP.expectedResponseJCubeSet_eq_originCube_of_mem_descendantsAtScale_originCube
              hstat hn hnm (by simpa [hDscale] using hR) p q
    _ = expectedResponseJCubeSet P (originCube d n) p q := by
          simp [Finset.sum_const, nsmul_eq_mul, hcard_ne]

/-- Under stationarity, the expectation of the finite descendant average of
response observables is the annealed response on the origin cube at the child
scale. -/
theorem integral_descendantsAverage_restrictionResponseJObservableCubeSet_eq_originCube_of_stationary
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hstat : RestrictionStationaryLaw P) {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    (p q : Vec d)
    (hJ : ∀ R, R ∈ descendantsAtScale (originCube d m) n →
      Integrable (restrictionResponseJObservableCubeSet R p q) P) :
    ∫ a,
        descendantsAverage (originCube d m) (Int.toNat (m - n))
          (fun R => restrictionResponseJObservableCubeSet R p q a) ∂P =
      expectedResponseJCubeSet P (originCube d n) p q := by
  have hJ_depth :
      ∀ R, R ∈ descendantsAtDepth (originCube d m) (Int.toNat (m - n)) →
        Integrable (restrictionResponseJObservableCubeSet R p q) P := by
    intro R hR
    exact hJ R (by
      simpa [descendantsAtScale_eq_descendantsAtDepth (originCube d m) hnm] using! hR)
  calc
    ∫ a,
        descendantsAverage (originCube d m) (Int.toNat (m - n))
          (fun R => restrictionResponseJObservableCubeSet R p q a) ∂P
        =
      expectedDescendantsAverageResponseJCubeSet P (originCube d m)
        (Int.toNat (m - n)) p q :=
        integral_descendantsAverage_restrictionResponseJObservableCubeSet_eq_expectedDescendantsAverageResponseJCubeSet
          (P := P) (Q := originCube d m) (j := Int.toNat (m - n)) p q hJ_depth
    _ = expectedResponseJCubeSet P (originCube d n) p q :=
        hP.expectedDescendantsAverageResponseJCubeSet_eq_originCube_of_stationary
          hstat hn hnm p q

/-- Weighted finite descendant response averages reduce to the average of the
deterministic weights times the origin-cube expectation under stationarity.

This is the source theorem for the cancellation step in Section 5.3: Ch5
supplies the cutoff weights and the scalar identity saying their finite
descendant average is zero. -/
theorem integral_weightedDescendantsAverage_restrictionResponseJObservableCubeSet_eq_weight_average_mul_originCube_of_stationary
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hstat : RestrictionStationaryLaw P) {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    (weight : TriadicCube d → ℝ) (p q : Vec d)
    (hJ : ∀ R, R ∈ descendantsAtScale (originCube d m) n →
      Integrable (restrictionResponseJObservableCubeSet R p q) P) :
    ∫ a,
        descendantsAverage (originCube d m) (Int.toNat (m - n))
          (fun R => weight R * restrictionResponseJObservableCubeSet R p q a) ∂P =
      descendantsAverage (originCube d m) (Int.toNat (m - n)) weight *
        expectedResponseJCubeSet P (originCube d n) p q := by
  classical
  let Q : TriadicCube d := originCube d m
  let j : ℕ := Int.toNat (m - n)
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  have hJ_depth :
      ∀ R, R ∈ descendantsAtDepth Q j →
        Integrable (fun a : RegCoeffField d =>
          weight R * restrictionResponseJObservableCubeSet R p q a) P := by
    intro R hR
    have hRscale : R ∈ descendantsAtScale (originCube d m) n := by
      simpa [Q, j, descendantsAtScale_eq_descendantsAtDepth (originCube d m) hnm] using! hR
    exact (hJ R hRscale).const_mul (weight R)
  calc
    ∫ a,
        descendantsAverage (originCube d m) (Int.toNat (m - n))
          (fun R => weight R * restrictionResponseJObservableCubeSet R p q a) ∂P
        =
      descendantsAverage (originCube d m) (Int.toNat (m - n))
        (fun R => ∫ a, weight R * restrictionResponseJObservableCubeSet R p q a ∂P) :=
        integral_descendantsAverage_eq_descendantsAverage_integral
          (P := P) (Q := Q) (j := j)
          (F := fun R a => weight R * restrictionResponseJObservableCubeSet R p q a) hJ_depth
    _ =
      descendantsAverage (originCube d m) (Int.toNat (m - n))
        (fun R => weight R * expectedResponseJCubeSet P (originCube d n) p q) := by
        unfold descendantsAverage
        refine congrArg (fun t : ℝ => ((D.card : ℝ)⁻¹) * t) ?_
        refine Finset.sum_congr rfl ?_
        intro R hR
        have hRscale : R ∈ descendantsAtScale (originCube d m) n := by
          simpa [Q, j, descendantsAtScale_eq_descendantsAtDepth (originCube d m) hnm] using! hR
        have hstationary :
            expectedResponseJCubeSet P R p q =
              expectedResponseJCubeSet P (originCube d n) p q :=
          hP.expectedResponseJCubeSet_eq_originCube_of_mem_descendantsAtScale_originCube
            hstat hn hnm hRscale p q
        rw [integral_const_mul]
        change weight R * expectedResponseJCubeSet P R p q =
          weight R * expectedResponseJCubeSet P (originCube d n) p q
        rw [hstationary]
    _ =
      descendantsAverage (originCube d m) (Int.toNat (m - n)) weight *
        expectedResponseJCubeSet P (originCube d n) p q := by
        let C : ℝ := expectedResponseJCubeSet P (originCube d n) p q
        change ((D.card : ℝ)⁻¹ * ∑ R ∈ D, weight R * C) =
          (((D.card : ℝ)⁻¹ * ∑ R ∈ D, weight R) * C)
        rw [← Finset.sum_mul]
        ring

end RestrictionLawCarrier

end

end Ch04
end Book
end Homogenization
