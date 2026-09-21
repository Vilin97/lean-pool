/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.ScalarizationDefinitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.Scalarization
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.WidetildeTheta
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.AnnealedSubadditivity
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAverageMoments.Theory

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.MomentFactorBounds.FactorBounds

/-! # Apex -/

namespace Homogenization
namespace Book
namespace Ch04

open MeasureTheory
open scoped Matrix.Norms.Elementwise Matrix.Norms.L2Operator BigOperators

noncomputable section

namespace RestrictionLawCarrier

/-- A full coarse block is integrable as soon as the two factor observables on
the same cube have finite `ξ` moments.

This is the Ch4 source theorem that prevents Ch5 from carrying a separate
full-block integrability hypothesis once it has the factor moments. -/
theorem integrable_coarseFullBlockMatrixAtCube_of_integrable_factor_observables
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d)
    {sUpper sLower : ℝ} {ξ : ℕ}
    (hsUpper : 0 < sUpper) (hsLower : 0 < sLower) (hξ : 1 ≤ ξ)
    (hUpperPowInt :
      Integrable
        (fun a : RegCoeffField d =>
          (LambdaSqCoeffField Q sUpper (.finite 1) a) ^ ξ) P)
    (hLowerPowInt :
      Integrable
        (fun a : RegCoeffField d =>
          ((lambdaSqCoeffField Q sLower (.finite 1) a)⁻¹) ^ ξ) P) :
    Integrable (coarseFullBlockMatrixAtCube Q) P := by
  let : IsProbabilityMeasure P := hP.isProbability
  have hUpperEntryAbsInt :
      ∀ i j : Fin d,
        Integrable
          (fun a : RegCoeffField d =>
            |(coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft i j|) P := by
    intro i j
    let X : RegCoeffField d → ℝ :=
      fun a => (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft i j
    let Y : RegCoeffField d → ℝ :=
      fun a => LambdaSqCoeffField Q sUpper (.finite 1) a
    have hX_meas : AEMeasurable X P := by
      simpa [X] using hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet Q i j
    have hY_nonneg : ∀ᵐ a ∂P, 0 ≤ Y a :=
      Filter.Eventually.of_forall fun a =>
        LambdaSqCoeffField_finite_nonneg Q a hsUpper (by norm_num : (1 : ℝ) ≤ 1)
    have hXY : (fun a => |X a|) ≤ᵐ[P] Y := by
      simpa [X, Y] using
        upperLeft_abs_entry_le_LambdaSqCoeffField_ae hP Q hsUpper i j
    have hAbsPowInt : Integrable (fun a => |X a| ^ ξ) P :=
      integrable_abs_pow_of_ae_abs_le_nonneg hX_meas hY_nonneg hXY
        (by simpa [Y] using hUpperPowInt)
    have hAbsMeas : AEMeasurable (fun a => |X a|) P := by
      simpa [Real.norm_eq_abs] using hX_meas.norm
    have hAbsNonneg : ∀ᵐ a ∂P, 0 ≤ |X a| :=
      Filter.Eventually.of_forall fun a => abs_nonneg (X a)
    simpa [X] using
      integrable_of_ae_nonneg_pow_integrable hξ hAbsMeas hAbsNonneg hAbsPowInt
  have hLowerEntryAbsInt :
      ∀ i j : Fin d,
        Integrable
          (fun a : RegCoeffField d =>
            |(coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight i j|) P := by
    intro i j
    let X : RegCoeffField d → ℝ :=
      fun a => (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight i j
    let Y : RegCoeffField d → ℝ :=
      fun a => (lambdaSqCoeffField Q sLower (.finite 1) a)⁻¹
    have hX_meas : AEMeasurable X P := by
      simpa [X] using hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet Q i j
    have hY_nonneg : ∀ᵐ a ∂P, 0 ≤ Y a :=
      Filter.Eventually.of_forall fun a =>
        inv_nonneg.mpr
          (lambdaSqCoeffField_finite_nonneg Q a hsLower (by norm_num : (1 : ℝ) ≤ 1))
    have hXY : (fun a => |X a|) ≤ᵐ[P] Y := by
      simpa [X, Y] using
        lowerRight_abs_entry_le_lambdaSqCoeffField_inv_ae hP Q hsLower i j
    have hAbsPowInt : Integrable (fun a => |X a| ^ ξ) P :=
      integrable_abs_pow_of_ae_abs_le_nonneg hX_meas hY_nonneg hXY
        (by simpa [Y] using hLowerPowInt)
    have hAbsMeas : AEMeasurable (fun a => |X a|) P := by
      simpa [Real.norm_eq_abs] using hX_meas.norm
    have hAbsNonneg : ∀ᵐ a ∂P, 0 ≤ |X a| :=
      Filter.Eventually.of_forall fun a => abs_nonneg (X a)
    simpa [X] using
      integrable_of_ae_nonneg_pow_integrable hξ hAbsMeas hAbsNonneg hAbsPowInt
  have hBInt : Integrable (fun a : RegCoeffField d => coarseBBlockNorm Q a.toFun) P := by
    have hSumInt :
        Integrable
          (fun a : RegCoeffField d =>
            ∑ i : Fin d, ∑ j : Fin d,
              |(coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft i j|) P := by
      refine integrable_finsetSum Finset.univ ?_
      intro i _hi
      refine integrable_finsetSum Finset.univ ?_
      intro j _hj
      exact hUpperEntryAbsInt i j
    have hBMeas :
        AEMeasurable (fun a : RegCoeffField d => coarseBBlockNorm Q a.toFun) P := by
      have hSqMeas :
          AEMeasurable
            (fun a : RegCoeffField d =>
              matNormSq (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft) P := by
        unfold matNormSq
        exact
          Finset.aemeasurable_fun_sum Finset.univ fun i _hi =>
            Finset.aemeasurable_fun_sum Finset.univ fun j _hj =>
              (hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet Q i j).pow_const 2
      simpa [coarseBBlockNorm, matNorm] using hSqMeas.sqrt
    refine hSumInt.mono' hBMeas.aestronglyMeasurable ?_
    filter_upwards with a
    have hbound :=
      Ch02.matNorm_le_sum_abs_entries
        ((coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft)
    have hsum_nonneg :
        0 ≤ ∑ i : Fin d, ∑ j : Fin d,
          |(coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft i j| := by
      exact Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => abs_nonneg _
    have hleft :
        ‖coarseBBlockNorm Q a.toFun‖ = coarseBBlockNorm Q a.toFun := by
      simp [Real.norm_eq_abs, abs_of_nonneg (coarseBBlockNorm_nonneg Q a)]
    have hright :
        ‖(∑ i : Fin d, ∑ j : Fin d,
          |(coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft i j|)‖ =
            ∑ i : Fin d, ∑ j : Fin d,
              |(coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft i j| := by
      simp [Real.norm_eq_abs, abs_of_nonneg hsum_nonneg]
    have hbound_abs :
        |matNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft| ≤
          ∑ i : Fin d, ∑ j : Fin d,
            |(coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft i j| := by
      simpa [abs_of_nonneg (matNorm_nonneg _)] using hbound
    simpa [hleft, hright, coarseBBlockNorm] using hbound_abs
  have hStarInt :
      Integrable (fun a : RegCoeffField d => coarseSigmaStarInvBlockNorm Q a.toFun) P := by
    have hSumInt :
        Integrable
          (fun a : RegCoeffField d =>
            ∑ i : Fin d, ∑ j : Fin d,
              |(coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight i j|) P := by
      refine integrable_finsetSum Finset.univ ?_
      intro i _hi
      refine integrable_finsetSum Finset.univ ?_
      intro j _hj
      exact hLowerEntryAbsInt i j
    have hStarMeas :
        AEMeasurable (fun a : RegCoeffField d => coarseSigmaStarInvBlockNorm Q a.toFun) P := by
      have hSqMeas :
          AEMeasurable
            (fun a : RegCoeffField d =>
              matNormSq (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight) P := by
        unfold matNormSq
        exact
          Finset.aemeasurable_fun_sum Finset.univ fun i _hi =>
            Finset.aemeasurable_fun_sum Finset.univ fun j _hj =>
              (hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet Q i j).pow_const 2
      simpa [coarseSigmaStarInvBlockNorm, matNorm] using hSqMeas.sqrt
    refine hSumInt.mono' hStarMeas.aestronglyMeasurable ?_
    filter_upwards with a
    have hbound :=
      Ch02.matNorm_le_sum_abs_entries
        ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight)
    have hsum_nonneg :
        0 ≤ ∑ i : Fin d, ∑ j : Fin d,
          |(coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight i j| := by
      exact Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => abs_nonneg _
    have hleft :
        ‖coarseSigmaStarInvBlockNorm Q a.toFun‖ = coarseSigmaStarInvBlockNorm Q a.toFun := by
      simp [Real.norm_eq_abs, abs_of_nonneg (coarseSigmaStarInvBlockNorm_nonneg Q a)]
    have hright :
        ‖(∑ i : Fin d, ∑ j : Fin d,
          |(coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight i j|)‖ =
            ∑ i : Fin d, ∑ j : Fin d,
              |(coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight i j| := by
      simp [Real.norm_eq_abs, abs_of_nonneg hsum_nonneg]
    have hbound_abs :
        |matNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight| ≤
          ∑ i : Fin d, ∑ j : Fin d,
            |(coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight i j| := by
      simpa [abs_of_nonneg (matNorm_nonneg _)] using hbound
    simpa [hleft, hright, coarseSigmaStarInvBlockNorm] using hbound_abs
  exact
    hP.integrable_coarseFullBlockMatrixAtCube_of_integrable_diagonalBlockNorms
      Q hBInt hStarInt

/-- The unit full coarse block is integrable as soon as the two unit factor
observables in `(P4)` have finite `ξ` moments. -/
theorem integrable_coarseFullBlockMatrixAtCube_origin_of_integrable_factor_observables
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    {sUpper sLower : ℝ} {ξ : ℕ}
    (hsUpper : 0 < sUpper) (hsLower : 0 < sLower) (hξ : 1 ≤ ξ)
    (hUpperPowInt :
      Integrable
        (fun a : RegCoeffField d =>
          (LambdaSqCoeffField (originCube d 0) sUpper (.finite 1) a) ^ ξ) P)
    (hLowerPowInt :
      Integrable
        (fun a : RegCoeffField d =>
          ((lambdaSqCoeffField (originCube d 0) sLower (.finite 1) a)⁻¹) ^ ξ) P) :
    Integrable (coarseFullBlockMatrixAtCube (originCube d (0 : ℤ))) P := by
  simpa using
    hP.integrable_coarseFullBlockMatrixAtCube_of_integrable_factor_observables
      (originCube d (0 : ℤ)) hsUpper hsLower hξ hUpperPowInt hLowerPowInt

/-- Law-facing construction of the primitive moment-factor package.

This theorem owns the deterministic one-cube ellipticity domination, the
passage from scalar annealed blocks to coefficient-field ellipticity
observables, and the `L^ξ` mean-to-root comparison. -/
private theorem annealedPrimitiveMomentFactorBounds_of_integrable_factor_observables
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    {sUpper sLower : ℝ} {ξ : ℕ}
    (hsUpper : 0 < sUpper) (hsLower : 0 < sLower) (hξ : 1 ≤ ξ)
    (hBlock :
      ∀ n : ℕ,
        Integrable (coarseFullBlockMatrixAtCube (originCube d (n : ℤ))) P)
    (hUpperMeas :
      ∀ n : ℕ,
        AEMeasurable
          (fun a : RegCoeffField d =>
            LambdaSqCoeffField (originCube d (n : ℤ)) sUpper (.finite 1) a) P)
    (hLowerMeas :
      ∀ n : ℕ,
        AEMeasurable
          (fun a : RegCoeffField d =>
            (lambdaSqCoeffField (originCube d (n : ℤ)) sLower (.finite 1) a)⁻¹) P)
    (hUpperPowInt :
      ∀ n : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            (LambdaSqCoeffField (originCube d (n : ℤ)) sUpper (.finite 1) a) ^ ξ) P)
    (hLowerPowInt :
      ∀ n : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            ((lambdaSqCoeffField (originCube d (n : ℤ)) sLower (.finite 1) a)⁻¹) ^ ξ) P) :
    AnnealedPrimitiveMomentFactorBounds (d := d) P sUpper sLower ξ where
  upper := by
    intro primitive n
    let : IsProbabilityMeasure P := hP.isProbability
    let Q : TriadicCube d := originCube d (n : ℤ)
    let X : RegCoeffField d → ℝ :=
      fun a => (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft 0 0
    let Y : RegCoeffField d → ℝ :=
      fun a => LambdaSqCoeffField Q sUpper (.finite 1) a
    have hEntryInt : Integrable X P := by
      simpa [X, Q, blockMatEntry] using
        integrable_blockMatEntry_coarseBlockMatrix_cubeSet_of_integrable_coarseFullBlockMatrixAtCube
          (hBlock n) (Sum.inl (0 : Fin d)) (Sum.inl (0 : Fin d))
    have hY_nonneg : ∀ᵐ a ∂P, 0 ≤ Y a :=
      Filter.Eventually.of_forall fun a => by
        exact LambdaSqCoeffField_finite_nonneg Q a hsUpper (by norm_num : (1 : ℝ) ≤ 1)
    have hYInt : Integrable Y P :=
      integrable_of_ae_nonneg_pow_integrable hξ
        (by simpa [Y, Q] using hUpperMeas n) hY_nonneg
        (by simpa [Y, Q] using hUpperPowInt n)
    have hYMeanLeRoot :
        ∫ a, Y a ∂P ≤ LambdaMomentAtScale P (n : ℤ) sUpper ξ := by
      simpa [Y, Q, LambdaMomentAtScale] using
        integral_le_annealedMomentRoot_of_ae_nonneg hξ
          (by simpa [Y, Q] using hUpperMeas n) hY_nonneg
          (by simpa [Y, Q] using hUpperPowInt n)
    have hEntryEq :
        ∫ a, X a ∂P = Internal.barBAtScaleOfPrimitive (primitive n) := by
      simpa [X, Q, Internal.barBAtScaleOfPrimitive, annealedBAtScale, annealedB,
        annealedBlockMatrix] using
          congrArg (fun M : Mat d => M 0 0) (primitive n).b_eq
    calc
      Internal.barBAtScaleOfPrimitive (primitive n)
          = ∫ a, X a ∂P := hEntryEq.symm
      _ ≤ ∫ a, Y a ∂P :=
          integral_mono_ae hEntryInt hYInt
            (by
              simpa [X, Y, Q] using
                upperLeft_entry_le_LambdaSqCoeffField_ae hP Q hsUpper)
      _ ≤ LambdaMomentAtScale P (n : ℤ) sUpper ξ := hYMeanLeRoot
  lower := by
    intro primitive n
    let : IsProbabilityMeasure P := hP.isProbability
    let Q : TriadicCube d := originCube d (n : ℤ)
    let X : RegCoeffField d → ℝ :=
      fun a => (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight 0 0
    let Y : RegCoeffField d → ℝ :=
      fun a => (lambdaSqCoeffField Q sLower (.finite 1) a)⁻¹
    have hEntryInt : Integrable X P := by
      simpa [X, Q, blockMatEntry] using
        integrable_blockMatEntry_coarseBlockMatrix_cubeSet_of_integrable_coarseFullBlockMatrixAtCube
          (hBlock n) (Sum.inr (0 : Fin d)) (Sum.inr (0 : Fin d))
    have hY_nonneg : ∀ᵐ a ∂P, 0 ≤ Y a :=
      Filter.Eventually.of_forall fun a => by
        exact inv_nonneg.mpr
          (lambdaSqCoeffField_finite_nonneg Q a hsLower (by norm_num : (1 : ℝ) ≤ 1))
    have hYInt : Integrable Y P :=
      integrable_of_ae_nonneg_pow_integrable hξ
        (by simpa [Y, Q] using hLowerMeas n) hY_nonneg
        (by simpa [Y, Q] using hLowerPowInt n)
    have hYMeanLeRoot :
        ∫ a, Y a ∂P ≤ lambdaInvMomentAtScale P (n : ℤ) sLower ξ := by
      simpa [Y, Q, lambdaInvMomentAtScale] using
        integral_le_annealedMomentRoot_of_ae_nonneg hξ
          (by simpa [Y, Q] using hLowerMeas n) hY_nonneg
          (by simpa [Y, Q] using hLowerPowInt n)
    have hEntryEq :
        ∫ a, X a ∂P = Internal.barSigmaStarInvAtScaleOfPrimitive (primitive n) := by
      simpa [X, Q, Internal.barSigmaStarInvAtScaleOfPrimitive, annealedSigmaStarInvAtScale,
        annealedSigmaStarInv, annealedBlockMatrix] using
          congrArg (fun M : Mat d => M 0 0) (primitive n).sigmaStarInv_eq
    calc
      Internal.barSigmaStarInvAtScaleOfPrimitive (primitive n)
          = ∫ a, X a ∂P := hEntryEq.symm
      _ ≤ ∫ a, Y a ∂P :=
          integral_mono_ae hEntryInt hYInt
            (by
              simpa [X, Y, Q] using
                lowerRight_entry_le_lambdaSqCoeffField_inv_ae hP Q hsLower)
      _ ≤ lambdaInvMomentAtScale P (n : ℤ) sLower ξ := hYMeanLeRoot

/-- Structural-law upper scalar factor bound from integrable moment
observables. -/
theorem barSigmaAtScale_le_LambdaMomentAtScale_of_integrable_factor_observables
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P)
    {sUpper sLower : ℝ} {ξ : ℕ}
    (hsUpper : 0 < sUpper) (hsLower : 0 < sLower) (hξ : 1 ≤ ξ)
    (hBlock :
      ∀ n : ℕ,
        Integrable (coarseFullBlockMatrixAtCube (originCube d (n : ℤ))) P)
    (hUpperMeas :
      ∀ n : ℕ,
        AEMeasurable
          (fun a : RegCoeffField d =>
            LambdaSqCoeffField (originCube d (n : ℤ)) sUpper (.finite 1) a) P)
    (hLowerMeas :
      ∀ n : ℕ,
        AEMeasurable
          (fun a : RegCoeffField d =>
            (lambdaSqCoeffField (originCube d (n : ℤ)) sLower (.finite 1) a)⁻¹) P)
    (hUpperPowInt :
      ∀ n : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            (LambdaSqCoeffField (originCube d (n : ℤ)) sUpper (.finite 1) a) ^ ξ) P)
    (hLowerPowInt :
      ∀ n : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            ((lambdaSqCoeffField (originCube d (n : ℤ)) sLower (.finite 1) a)⁻¹) ^ ξ) P)
    (n : ℕ) :
    hP.barSigmaAtScale hStruct (n : ℤ) ≤
      LambdaMomentAtScale P (n : ℤ) sUpper ξ := by
  let primitive : AnnealedPrimitiveScalarizationFamily (d := d) P :=
    fun n => Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct (n : ℤ)
  have hBounds :=
    hP.annealedPrimitiveMomentFactorBounds_of_integrable_factor_observables
      hsUpper hsLower hξ hBlock hUpperMeas hLowerMeas hUpperPowInt hLowerPowInt
  have hbar := hP.barSigmaAtScale_eq_barBAtScale hStruct (n : ℤ)
  rw [hbar]
  simpa [barBAtScale, primitive] using hBounds.upper primitive n

/-- Structural-law lower inverse-star scalar factor bound from integrable
moment observables. -/
theorem barSigmaStarAtScale_inv_le_lambdaInvMomentAtScale_of_integrable_factor_observables
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P)
    {sUpper sLower : ℝ} {ξ : ℕ}
    (hsUpper : 0 < sUpper) (hsLower : 0 < sLower) (hξ : 1 ≤ ξ)
    (hBlock :
      ∀ n : ℕ,
        Integrable (coarseFullBlockMatrixAtCube (originCube d (n : ℤ))) P)
    (hUpperMeas :
      ∀ n : ℕ,
        AEMeasurable
          (fun a : RegCoeffField d =>
            LambdaSqCoeffField (originCube d (n : ℤ)) sUpper (.finite 1) a) P)
    (hLowerMeas :
      ∀ n : ℕ,
        AEMeasurable
          (fun a : RegCoeffField d =>
            (lambdaSqCoeffField (originCube d (n : ℤ)) sLower (.finite 1) a)⁻¹) P)
    (hUpperPowInt :
      ∀ n : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            (LambdaSqCoeffField (originCube d (n : ℤ)) sUpper (.finite 1) a) ^ ξ) P)
    (hLowerPowInt :
      ∀ n : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            ((lambdaSqCoeffField (originCube d (n : ℤ)) sLower (.finite 1) a)⁻¹) ^ ξ) P)
    (n : ℕ) :
    (hP.barSigmaStarAtScale hStruct (n : ℤ))⁻¹ ≤
      lambdaInvMomentAtScale P (n : ℤ) sLower ξ := by
  let primitive : AnnealedPrimitiveScalarizationFamily (d := d) P :=
    fun n => Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct (n : ℤ)
  have hBounds :=
    hP.annealedPrimitiveMomentFactorBounds_of_integrable_factor_observables
      hsUpper hsLower hξ hBlock hUpperMeas hLowerMeas hUpperPowInt hLowerPowInt
  have hstar := hP.barSigmaStarAtScale_eq_inv_barSigmaStarInvAtScale hStruct (n : ℤ)
  rw [hstar, inv_inv]
  simpa [barSigmaStarInvAtScale, primitive] using hBounds.lower primitive n

/-- Direct structural-law comparison `Theta_n <= widetildeTheta_n` from
integrable moment observables. -/
theorem thetaAtScale_le_widetildeThetaAtScale_of_integrable_factor_observables
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P)
    {sUpper sLower : ℝ} {ξ : ℕ}
    (hsUpper : 0 < sUpper) (hsLower : 0 < sLower) (hξ : 1 ≤ ξ)
    (hBlock :
      ∀ n : ℕ,
        Integrable (coarseFullBlockMatrixAtCube (originCube d (n : ℤ))) P)
    (hUpperMeas :
      ∀ n : ℕ,
        AEMeasurable
          (fun a : RegCoeffField d =>
            LambdaSqCoeffField (originCube d (n : ℤ)) sUpper (.finite 1) a) P)
    (hLowerMeas :
      ∀ n : ℕ,
        AEMeasurable
          (fun a : RegCoeffField d =>
            (lambdaSqCoeffField (originCube d (n : ℤ)) sLower (.finite 1) a)⁻¹) P)
    (hUpperPowInt :
      ∀ n : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            (LambdaSqCoeffField (originCube d (n : ℤ)) sUpper (.finite 1) a) ^ ξ) P)
    (hLowerPowInt :
      ∀ n : ℕ,
        Integrable
          (fun a : RegCoeffField d =>
            ((lambdaSqCoeffField (originCube d (n : ℤ)) sLower (.finite 1) a)⁻¹) ^ ξ) P)
    (n : ℕ) :
    hP.thetaAtScale hStruct (n : ℤ) ≤
      widetildeThetaAtScale P (n : ℤ) sUpper sLower ξ := by
  have hUpper :
      hP.barSigmaAtScale hStruct (n : ℤ) ≤
        LambdaMomentAtScale P (n : ℤ) sUpper ξ :=
    hP.barSigmaAtScale_le_LambdaMomentAtScale_of_integrable_factor_observables
      hStruct hsUpper hsLower hξ hBlock hUpperMeas hLowerMeas hUpperPowInt
      hLowerPowInt n
  have hLower :
      (hP.barSigmaStarAtScale hStruct (n : ℤ))⁻¹ ≤
        lambdaInvMomentAtScale P (n : ℤ) sLower ξ :=
    hP.barSigmaStarAtScale_inv_le_lambdaInvMomentAtScale_of_integrable_factor_observables
      hStruct hsUpper hsLower hξ hBlock hUpperMeas hLowerMeas hUpperPowInt
      hLowerPowInt n
  have hStarInv_nonneg :
      0 ≤ (hP.barSigmaStarAtScale hStruct (n : ℤ))⁻¹ := by
    have hstar := hP.barSigmaStarAtScale_eq_inv_barSigmaStarInvAtScale hStruct (n : ℤ)
    rw [hstar, inv_inv]
    simpa [barSigmaStarInvAtScale] using
      (Internal.barSigmaStarInv_pos_of_integrable_coarseFullBlockMatrixAtCube hP
        (Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct (n : ℤ))
        (hBlock n)).le
  have hUpperMoment_nonneg :
      0 ≤ LambdaMomentAtScale P (n : ℤ) sUpper ξ :=
    LambdaMomentAtScale_nonneg P (n : ℤ) ξ hsUpper
  simpa [thetaAtScale, widetildeThetaAtScale] using
    mul_le_mul hUpper hLower hStarInv_nonneg hUpperMoment_nonneg

end RestrictionLawCarrier

end

end Ch04
end Book
end Homogenization
