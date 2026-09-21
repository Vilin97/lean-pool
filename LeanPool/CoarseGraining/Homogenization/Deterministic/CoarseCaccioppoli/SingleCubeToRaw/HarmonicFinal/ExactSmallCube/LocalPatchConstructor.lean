/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.ExactSmallCube.LocalPatchConstructor.ConstantBranch
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.InputSpecializations.LocalPatchNoteRawBridge
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.ExactSmallCube.CenteredFactors
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.QuantitativeCutoffInputs.LocalPatch
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.LocalConstantBranch

/-! # Local Patch Constructor -/

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# Local-patch exact small-cube coefficient constructors

This file contains the final coefficient-package constructors for the
arbitrary-center local-patch exact small-cube route. Factor and branch estimates
live in the `LocalPatchConstructor/` submodules.
-/

/-- Direct split local-patch exact-to-parent-raw coefficient bounds from
closed-cube ellipticity.

The constant branch is paid by `Ccross`, while the centered branch and the
integerized height are paid by `Calpha`. -/
theorem
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeLocalPatchBufferedExactRawCoefficientBoundsSplit.of_closedCubeEllipticity_of_localPatchBufferedCutoffRadiusConst_of_centeredFronts
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (center : Vec d) (a : CoeffField d)
    (s t Clocal Calpha Ccross : ℝ) {lam Lam : ℝ}
    (hClocal : 0 ≤ Clocal) (hCalpha : 0 ≤ Calpha)
    (hwork_constant_cross :
      (81 : ℝ) * Real.rpow (3 : ℝ) (2 * s) *
          ((Fintype.card (Fin d) : ℝ) * Clocal) ≤
        (Fintype.card (Fin d) : ℝ) * Ccross)
    (hwork_centered_fronts_alpha :
      (81 : ℝ) *
          (6 * coarseCaccioppoliCenteredAverageFront d s
              ((Fintype.card (Fin d) : ℝ) * Clocal) +
            12 * coarseCaccioppoliCenteredBesovHessianFront d s
              ((Fintype.card (Fin d) : ℝ) * Clocal) +
            6 * coarseCaccioppoliCenteredBesovGradientFront d s
              ((Fintype.card (Fin d) : ℝ) * Clocal)) ≤
        ((Fintype.card (Fin d) : ℝ) * Calpha) / (s * (1 - s)))
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hlarge :
      (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) *
          (geometricDiscount (1 : ℝ) 1)⁻¹ *
        (12 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
              (cubeRadius Q) ^ (2 : ℕ)) +
          6 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)) ≤
        (Fintype.card (Fin d) : ℝ) * Clocal) :
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeLocalPatchBufferedExactRawCoefficientBoundsSplit
      Q center a s t Clocal Calpha Ccross := by
  let CeffLocal : ℝ := (Fintype.card (Fin d) : ℝ) * Clocal
  let CeffAlpha : ℝ := (Fintype.card (Fin d) : ℝ) * Calpha
  let CeffCross : ℝ := (Fintype.card (Fin d) : ℝ) * Ccross
  let hheight : ℝ → ℝ → ℝ :=
    coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t CeffAlpha
      coarseCaccioppoliTriadicGapScale
  let Scenter : ℝ :=
    6 * coarseCaccioppoliCenteredAverageFront d s CeffLocal +
      12 * coarseCaccioppoliCenteredBesovHessianFront d s CeffLocal +
      6 * coarseCaccioppoliCenteredBesovGradientFront d s CeffLocal
  have hcard_nonneg : 0 ≤ (Fintype.card (Fin d) : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card (Fin d))
  have hCeffLocal_nonneg : 0 ≤ CeffLocal := mul_nonneg hcard_nonneg hClocal
  have hCeffAlpha_nonneg : 0 ≤ CeffAlpha := mul_nonneg hcard_nonneg hCalpha
  have hs1 : s < 1 := by nlinarith [ht, hst]
  have hScenter_nonneg : 0 ≤ Scenter := by
    dsimp [Scenter]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6)
          (coarseCaccioppoliCenteredAverageFront_nonneg d hCeffLocal_nonneg hs))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12)
          (coarseCaccioppoliCenteredBesovHessianFront_nonneg d hCeffLocal_nonneg hs)))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6)
        (coarseCaccioppoliCenteredBesovGradientFront_nonneg d hCeffLocal_nonneg hs hs1))
  have hcentered_alpha : (81 : ℝ) * Scenter ≤ CeffAlpha / (s * (1 - s)) := by
    simpa [Scenter, CeffLocal, CeffAlpha] using hwork_centered_fronts_alpha
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
  have hRec :
      OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam) :=
    openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
      (Q := Q) (a := a) hEllCube hOrigin
  have hData : OpenCubeDescendantDeterministicCoarseData Q a :=
    openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec
  have hBsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_qone_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
      Q a s hs hEllCube hData
  have hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_qone_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
      Q a t ht hEllCube hData
  let hconst :
      ∀ n : ℕ,
        let ρ₁ : ℝ := coarseCaccioppoliRadiusSequence n
        let ρ₂ : ℝ := coarseCaccioppoliRadiusSequence (n + 1)
        let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
        let CeffAlpha : ℝ := (Fintype.card (Fin d) : ℝ) * Calpha
        let CeffCross : ℝ := (Fintype.card (Fin d) : ℝ) * Ccross
        let hheight : ℝ → ℝ → ℝ :=
          coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t CeffAlpha
            coarseCaccioppoliTriadicGapScale
        let j : ℕ :=
          coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice Q a s t
            CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂ + 1
        let ξ : Vec d → Vec d :=
          scalarCutoffGradientField (coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm)
        let B : ℝ := coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁ ρm
        let K : ℝ :=
          coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s CeffCross 1 hheight ρ₁ ρ₂
        ∀ R ∈ descendantsAtDepth Q j,
          coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
              (B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ) ≤ K :=
    faithfulWorkSmallCubeExactRawConstantBranchSplit_of_closedCubeEllipticity_of_localPatchBufferedCutoffRadiusConst
      (Q := Q) (center := center) (a := a) (s := s) (t := t)
      (Clocal := Clocal) (Calpha := Calpha) (Ccross := Ccross)
      hClocal hwork_constant_cross hs ht hst hEllCube hlarge
  intro n
  let ρ₁ : ℝ := coarseCaccioppoliRadiusSequence n
  let ρ₂ : ℝ := coarseCaccioppoliRadiusSequence (n + 1)
  let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
  let k : ℕ := coarseCaccioppoliTriadicGapScale ρ₁ ρ₂
  let j0 : ℕ :=
    coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice Q a s t
      CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂
  let j : ℕ := j0 + 1
  have hρ₁ : (1 / 3 : ℝ) ≤ ρ₁ := by
    simpa [ρ₁] using (coarseCaccioppoliRadiusSequence_mem_Icc n).1
  have hρ₁_pos : 0 < ρ₁ := by
    exact (show (0 : ℝ) < 1 / 3 by norm_num).trans_le hρ₁
  have hlt : ρ₁ < ρ₂ := by
    simpa [ρ₁, ρ₂] using
      coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self n)
  have hρ₂ : ρ₂ ≤ 1 := by
    simpa [ρ₂] using (coarseCaccioppoliRadiusSequence_mem_Icc (n + 1)).2
  have hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂ := by
    simpa [k, ρ₁, ρ₂] using coarseCaccioppoliTriadicGapScale_spec hρ₁ hlt hρ₂
  have hjk : k ≤ j0 := by
    simpa [k, j0, CeffAlpha, ρ₁, ρ₂] using
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice_ge_scaleChoice
        Q a s t CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂)
  have hheight_le_j0 : hheight ρ₁ ρ₂ ≤ (j0 : ℝ) := by
    simpa [hheight, j0, CeffAlpha, ρ₁, ρ₂,
      coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice,
      coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice] using
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale_le_depth
        Q a s t CeffAlpha (coarseCaccioppoliTriadicGapScale ρ₁ ρ₂))
  have hscale :
      Scenter * Real.rpow (3 : ℝ) (k : ℝ) ≤
        CeffAlpha / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂ :=
    localPatch_centered_fronts_scale_mul_le_workGap_of_triadicGapScaleChoice
      hScenter_nonneg hcentered_alpha hchoice hlt
  constructor
  · intro R hR
    simpa [CeffAlpha, CeffCross, hheight, ρ₁, ρ₂, ρm, j,
      coarseCaccioppoliLocalPatchCutoffHessianBound]
      using hconst n R hR
  · intro R hR
    simpa [CeffLocal, CeffAlpha, hheight, ρ₁, ρ₂, ρm, j, Scenter,
      coarseCaccioppoliLocalPatchCutoffHessianBound]
      using
        (coarseCaccioppoliFluxEnergyExactCenteredCoeff_localPatchBuffered_localAcirc_le_alpha_of_scale
          (Q := Q) (R := R) (center := center) (a := a) (s := s) (t := t)
          (CeffLocal := CeffLocal) (CeffWork := CeffAlpha)
          (k := k) (j := j0) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
          (hheight := hheight)
          hρ₁_pos hCeffLocal_nonneg hCeffAlpha_nonneg hs ht hst hEllCube hR
          hBsum_s hSigmaSum_t hchoice hlt hjk
          (by simpa [Scenter] using hscale) hheight_le_j0)

/-- All-radii direct split local-patch exact-to-parent-raw coefficient bounds
from closed-cube ellipticity.

This is the proof-producing coefficient package for the standard radius
iteration in the arbitrary-center boundary route. -/
theorem
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeLocalPatchBufferedExactRawCoefficientBoundsSplitAllRadii.of_closedCubeEllipticity_of_localPatchBufferedCutoffRadiusConst_of_centeredFronts
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (center : Vec d) (a : CoeffField d)
    (s t Clocal Calpha Ccross : ℝ) {lam Lam : ℝ}
    (hClocal : 0 ≤ Clocal) (hCalpha : 0 ≤ Calpha)
    (hwork_constant_cross :
      (81 : ℝ) * Real.rpow (3 : ℝ) (2 * s) *
          ((Fintype.card (Fin d) : ℝ) * Clocal) ≤
        (Fintype.card (Fin d) : ℝ) * Ccross)
    (hwork_centered_fronts_alpha :
      (81 : ℝ) *
          (6 * coarseCaccioppoliCenteredAverageFront d s
              ((Fintype.card (Fin d) : ℝ) * Clocal) +
            12 * coarseCaccioppoliCenteredBesovHessianFront d s
              ((Fintype.card (Fin d) : ℝ) * Clocal) +
            6 * coarseCaccioppoliCenteredBesovGradientFront d s
              ((Fintype.card (Fin d) : ℝ) * Clocal)) ≤
        ((Fintype.card (Fin d) : ℝ) * Calpha) / (s * (1 - s)))
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hlarge :
      (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) *
          (geometricDiscount (1 : ℝ) 1)⁻¹ *
        (12 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
              (cubeRadius Q) ^ (2 : ℕ)) +
          6 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)) ≤
        (Fintype.card (Fin d) : ℝ) * Clocal) :
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeLocalPatchBufferedExactRawCoefficientBoundsSplitAllRadii
      Q center a s t Clocal Calpha Ccross := by
  let CeffLocal : ℝ := (Fintype.card (Fin d) : ℝ) * Clocal
  let CeffAlpha : ℝ := (Fintype.card (Fin d) : ℝ) * Calpha
  let CeffCross : ℝ := (Fintype.card (Fin d) : ℝ) * Ccross
  let hheight : ℝ → ℝ → ℝ :=
    coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t CeffAlpha
      coarseCaccioppoliTriadicGapScale
  let Scenter : ℝ :=
    6 * coarseCaccioppoliCenteredAverageFront d s CeffLocal +
      12 * coarseCaccioppoliCenteredBesovHessianFront d s CeffLocal +
      6 * coarseCaccioppoliCenteredBesovGradientFront d s CeffLocal
  have hcard_nonneg : 0 ≤ (Fintype.card (Fin d) : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card (Fin d))
  have hCeffLocal_nonneg : 0 ≤ CeffLocal := mul_nonneg hcard_nonneg hClocal
  have hCeffAlpha_nonneg : 0 ≤ CeffAlpha := mul_nonneg hcard_nonneg hCalpha
  have hs1 : s < 1 := by nlinarith [ht, hst]
  have hScenter_nonneg : 0 ≤ Scenter := by
    dsimp [Scenter]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6)
          (coarseCaccioppoliCenteredAverageFront_nonneg d hCeffLocal_nonneg hs))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12)
          (coarseCaccioppoliCenteredBesovHessianFront_nonneg d hCeffLocal_nonneg hs)))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6)
        (coarseCaccioppoliCenteredBesovGradientFront_nonneg d hCeffLocal_nonneg hs hs1))
  have hcentered_alpha : (81 : ℝ) * Scenter ≤ CeffAlpha / (s * (1 - s)) := by
    simpa [Scenter, CeffLocal, CeffAlpha] using hwork_centered_fronts_alpha
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
  have hRec :
      OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam) :=
    openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
      (Q := Q) (a := a) hEllCube hOrigin
  have hData : OpenCubeDescendantDeterministicCoarseData Q a :=
    openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec
  have hBsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_qone_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
      Q a s hs hEllCube hData
  have hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_qone_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
      Q a t ht hEllCube hData
  let hconst :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
        let CeffAlpha : ℝ := (Fintype.card (Fin d) : ℝ) * Calpha
        let CeffCross : ℝ := (Fintype.card (Fin d) : ℝ) * Ccross
        let hheight : ℝ → ℝ → ℝ :=
          coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t CeffAlpha
            coarseCaccioppoliTriadicGapScale
        let j : ℕ :=
          coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice Q a s t
            CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂ + 1
        let ξ : Vec d → Vec d :=
          scalarCutoffGradientField (coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm)
        let B : ℝ := coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁ ρm
        let K : ℝ :=
          coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s CeffCross 1 hheight ρ₁ ρ₂
        ∀ R ∈ descendantsAtDepth Q j,
          coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
              (B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ) ≤ K :=
    faithfulWorkSmallCubeExactRawConstantBranchSplitAllRadii_of_closedCubeEllipticity_of_localPatchBufferedCutoffRadiusConst
      (Q := Q) (center := center) (a := a) (s := s) (t := t)
      (Clocal := Clocal) (Calpha := Calpha) (Ccross := Ccross)
      hClocal hwork_constant_cross hs ht hst hEllCube hlarge
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
  let k : ℕ := coarseCaccioppoliTriadicGapScale ρ₁ ρ₂
  let j0 : ℕ :=
    coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice Q a s t
      CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂
  let j : ℕ := j0 + 1
  have hρ₁_pos : 0 < ρ₁ := by
    exact (show (0 : ℝ) < 1 / 3 by norm_num).trans_le hρ₁
  have hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂ := by
    simpa [k] using coarseCaccioppoliTriadicGapScale_spec hρ₁ hlt hρ₂
  have hjk : k ≤ j0 := by
    simpa [k, j0, CeffAlpha] using
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice_ge_scaleChoice
        Q a s t CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂)
  have hheight_le_j0 : hheight ρ₁ ρ₂ ≤ (j0 : ℝ) := by
    simpa [hheight, j0, CeffAlpha,
      coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice,
      coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice] using
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale_le_depth
        Q a s t CeffAlpha (coarseCaccioppoliTriadicGapScale ρ₁ ρ₂))
  have hscale :
      Scenter * Real.rpow (3 : ℝ) (k : ℝ) ≤
        CeffAlpha / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂ :=
    localPatch_centered_fronts_scale_mul_le_workGap_of_triadicGapScaleChoice
      hScenter_nonneg hcentered_alpha hchoice hlt
  constructor
  · intro R hR
    simpa [CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeLocalPatchBufferedExactRawCoefficientBoundsSplitAllRadii,
      CeffAlpha, CeffCross, hheight, ρm, j, coarseCaccioppoliLocalPatchCutoffHessianBound]
      using hconst hρ₁ hlt hρ₂ R hR
  · intro R hR
    simpa [CeffLocal, CeffAlpha, hheight, ρm, j, Scenter,
      coarseCaccioppoliLocalPatchCutoffHessianBound]
      using
        (coarseCaccioppoliFluxEnergyExactCenteredCoeff_localPatchBuffered_localAcirc_le_alpha_of_scale
          (Q := Q) (R := R) (center := center) (a := a) (s := s) (t := t)
          (CeffLocal := CeffLocal) (CeffWork := CeffAlpha)
          (k := k) (j := j0) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
          (hheight := hheight)
          hρ₁_pos hCeffLocal_nonneg hCeffAlpha_nonneg hs ht hst hEllCube hR
          hBsum_s hSigmaSum_t hchoice hlt hjk
          (by simpa [Scenter] using hscale) hheight_le_j0)

end

end Homogenization
