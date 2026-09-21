/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicQuantitativeCutoff

/-! # Harmonic Coefficient Bounds -/

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# Harmonic canonical cutoff coefficient localization

This file removes the direct raw-coefficient hypothesis from the strongest
canonical harmonic wrappers by rebuilding it from the note-shaped ingredients:
single-cube coefficient bounds plus the localized multiscale ellipticity
comparison.
-/

/-- Canonical raw coefficient bounds from the note's single-cube coefficient
bounds and localized explicit-height coefficient localization. -/
theorem
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalRawCoefficientBounds.of_coefficientBounds_of_multiscaleEllipticity_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ)
    (U Xi D A1 AS : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds
        Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        U Xi D A1 AS)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData :
      ∀ j ≤ Q.scale, ∀ R ∈ descendantsAtScale Q j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det)
    (hBsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalRawCoefficientBounds
      Q a s t C uL2Sq
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
      U Xi D A1 AS := by
  exact
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalRawCoefficientBounds.of_coefficientBounds_of_localization
      Q a s t C uL2Sq
      (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
      U Xi D A1 AS hcoeff
      (CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization.of_triadicGapScaleChoice_of_localizedExplicitHeightOfScaleChoice_of_isEllipticFieldOn_of_isSigmaCoarse
        Q a C uL2Sq k hC hs ht hst hscale hEll hData hBsum_s hSigmaSum_t)

/-- Boundary canonical harmonic Caccioppoli with the raw coefficient hypothesis
rebuilt from localized multiscale coefficient data. -/
theorem
    coarseCaccioppoli_boundary_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_scalarCutoffControls_of_coefficientBounds_of_localizationData_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hlower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) →
        (hρ₂ : ρ₂ ≤ 1) →
        F ρ₁ ≤
          cubeAverage Q
            (fun x =>
              QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x *
                scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) = F ρ₂)
    (hfluxMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (huMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp (fun x => (w ρ₁ ρ₂).toH1 x)
          (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hgMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp (g ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hscalar :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliScalarCutoffControls Q s
          (fun x => (w ρ₁ ρ₂).toH1 x) (g ρ₁ ρ₂)
          (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
          (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C)
    (hAcirc1_nonneg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤ Acirc1 ρ₁ ρ₂)
    (hAcircS_nonneg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤ AcircS ρ₁ ρ₂)
    (hU :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => (w ρ₁ ρ₂).toH1 x) ≤ U ρ₁ ρ₂)
    (hA1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        Acirc1 ρ₁ ρ₂ ≤ A1 ρ₁ ρ₂)
    (hAS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        U
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        A1 AS)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData :
      ∀ j ≤ Q.scale, ∀ R ∈ descendantsAtScale Q j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det)
    (hBsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq := by
  exact
    coarseCaccioppoli_boundary_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_scalarCutoffControls_of_coefficientBounds_of_multiscaleEllipticity_of_localizedExplicitHeightOfScaleChoice
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := k) (F := F) (w := w) (g := g)
      (Acirc1 := Acirc1) (AcircS := AcircS) (U := U) (A1 := A1) (AS := AS)
      hC hs ht hst hu hnonneg hbounded hscale hlower henergyAvg hfluxMem huMem
      hgMem hfluxEnergy hscalar hAcirc1_nonneg hAcircS_nonneg hU hA1 hAS hEll
      (CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalRawCoefficientBounds.of_coefficientBounds_of_multiscaleEllipticity_of_localizedExplicitHeightOfScaleChoice
        Q a s t C uL2Sq k U
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        A1 AS hC hs ht hst hscale hcoeff hEll hData hBsum_s hSigmaSum_t)

/-- Interior canonical harmonic Caccioppoli with the raw coefficient hypothesis
rebuilt from localized multiscale coefficient data. -/
theorem
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_scalarCutoffControls_of_coefficientBounds_of_localizationData_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F G₀ : ℝ → ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hagree : CoarseCaccioppoliRadiusAgreement F G₀)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G₀ ρ)
    (hG_bounded : CoarseCaccioppoliRadiusBoundedAbove G₀)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hlower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) →
        (hρ₂ : ρ₂ ≤ 1) →
        G₀ ρ₁ ≤
          cubeAverage Q
            (fun x =>
              QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x *
                scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) =
          G₀ ρ₂)
    (hfluxMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (huMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp (fun x => (w ρ₁ ρ₂).toH1 x)
          (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hgMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp (g ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hscalar :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliScalarCutoffControls Q s
          (fun x => (w ρ₁ ρ₂).toH1 x) (g ρ₁ ρ₂)
          (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
          (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C)
    (hAcirc1_nonneg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤ Acirc1 ρ₁ ρ₂)
    (hAcircS_nonneg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤ AcircS ρ₁ ρ₂)
    (hU :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => (w ρ₁ ρ₂).toH1 x) ≤ U ρ₁ ρ₂)
    (hA1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        Acirc1 ρ₁ ρ₂ ≤ A1 ρ₁ ρ₂)
    (hAS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        U
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        A1 AS)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData :
      ∀ j ≤ Q.scale, ∀ R ∈ descendantsAtScale Q j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det)
    (hBsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := by
  exact
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_scalarCutoffControls_of_coefficientBounds_of_multiscaleEllipticity_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := k) (F := F) (G₀ := G₀) (w := w) (g := g)
      (Acirc1 := Acirc1) (AcircS := AcircS) (U := U) (A1 := A1) (AS := AS)
      hC hs ht hst hu hagree hG_nonneg hG_bounded hscale hlower henergyAvg
      hfluxMem huMem hgMem hfluxEnergy hscalar hAcirc1_nonneg hAcircS_nonneg
      hU hA1 hAS hEll
      (CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalRawCoefficientBounds.of_coefficientBounds_of_multiscaleEllipticity_of_localizedExplicitHeightOfScaleChoice
        Q a s t C uL2Sq k U
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        A1 AS hC hs ht hst hscale hcoeff hEll hData hBsum_s hSigmaSum_t)

/-- The canonical quantitative cutoff supplies the scalar cutoff-control
bundle once the projected Poincare and Besov `circ` bounds are available. -/
theorem CoarseCaccioppoliScalarCutoffControls.of_canonicalQuantitativeCutoff
    {d : ℕ} (Q : TriadicCube d) (s C : ℝ) {ρ₁ ρ₂ : ℝ}
    (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂)
    (u g energy : Vec d → ℝ) (Acirc1 AcircS : ℝ)
    (hBgConst :
      0 ≤
        coarseCaccioppoliConstantCutoffSize Q u
          (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂))
    (hBgCent :
      0 ≤
        coarseCaccioppoliCenteredCutoffSize Q s
          (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
          Acirc1 AcircS (Real.sqrt (cubeAverage Q energy))
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C)
    (hC : 0 ≤ C)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C (cubeFluctuation Q u) g N)
    (hgCirc1 : ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤
        Acirc1 * Real.sqrt (cubeAverage Q energy))
    (hgCircS : ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤
        AcircS * Real.sqrt (cubeAverage Q energy)) :
    CoarseCaccioppoliScalarCutoffControls Q s u g
      (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
      energy Acirc1 AcircS (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂)
      C := by
  let ηρ : QuantitativeCubeCutoff Q ρ₁ ρ₂ :=
    coarseCaccioppoliCanonicalQuantitativeCutoff Q hρ₁ hlt
  have hB :
      0 ≤ coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ :=
    coarseCaccioppoliQuantitativeCutoffHessianBound_nonneg Q ηρ
  simpa [ηρ, coarseCaccioppoliCanonicalQuantitativeCutoff,
    QuantitativeCubeCutoff.canonical, coarseCaccioppoliQuantitativeCutoffHessianBound]
    using
      (CoarseCaccioppoliScalarCutoffControls.of_quantitativeCubeCutoff
        (Q := Q) (s := s) (u := u) (g := g) (energy := energy) (η := ηρ)
        (Acirc1 := Acirc1) (AcircS := AcircS) (C := C)
        (by simpa [coarseCaccioppoliQuantitativeCutoffHessianBound] using hB)
        (by simpa [ηρ, coarseCaccioppoliCanonicalQuantitativeCutoff,
          QuantitativeCubeCutoff.canonical, coarseCaccioppoliQuantitativeCutoffHessianBound]
          using hBgConst)
        (by simpa [ηρ, coarseCaccioppoliCanonicalQuantitativeCutoff,
          QuantitativeCubeCutoff.canonical, coarseCaccioppoliQuantitativeCutoffHessianBound]
          using hBgCent)
        hC hproj hgCirc1 hgCircS)

/-- A positivity-factor version of the canonical scalar cutoff-control
constructor.  This replaces the raw strict-positivity hypotheses for the two
exact cutoff sizes by simpler positive inputs. -/
theorem
    CoarseCaccioppoliScalarCutoffControls.of_canonicalQuantitativeCutoff_of_positiveFactors
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s C : ℝ) {ρ₁ ρ₂ : ℝ}
    (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂)
    (u g energy : Vec d → ℝ) (Acirc1 AcircS : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hu : 0 < cubeLpNorm Q (2 : ℝ≥0∞) u)
    (hAcirc1 : 0 < Acirc1) (hAcircS : 0 ≤ AcircS)
    (hE : 0 < Real.sqrt (cubeAverage Q energy)) (hC : 0 < C)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C (cubeFluctuation Q u) g N)
    (hgCirc1 : ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤
        Acirc1 * Real.sqrt (cubeAverage Q energy))
    (hgCircS : ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤
        AcircS * Real.sqrt (cubeAverage Q energy)) :
    CoarseCaccioppoliScalarCutoffControls Q s u g
      (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
      energy Acirc1 AcircS (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂)
      C := by
  have hBpos :
      0 < coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ :=
    coarseCaccioppoliQuantitativeCutoffHessianBound_pos Q hlt
  have hBgConst :
      0 <
        coarseCaccioppoliConstantCutoffSize Q u
          (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) :=
    coarseCaccioppoliConstantCutoffSize_pos_of_cubeLpNorm_pos_of_B_pos
      Q u
      (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
      hu hBpos
  have hBgCent :
      0 <
        coarseCaccioppoliCenteredCutoffSize Q s
          (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
          Acirc1 AcircS (Real.sqrt (cubeAverage Q energy))
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C :=
    coarseCaccioppoliCenteredCutoffSize_pos_of_first_branch
      Q
      (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
      hs0 hs1 hAcirc1 hAcircS hE hBpos hC
  exact
    CoarseCaccioppoliScalarCutoffControls.of_canonicalQuantitativeCutoff
      (Q := Q) (s := s) (C := C) hρ₁ hlt u g energy Acirc1 AcircS
      hBgConst.le hBgCent.le hC.le hproj hgCirc1 hgCircS

/-- Vector-Poincare analogue of
`CoarseCaccioppoliScalarCutoffControls.of_canonicalQuantitativeCutoff_of_positiveFactors`.

The strict positivity of the centered cutoff size uses the effective
scalar-facing constant `(Fintype.card (Fin d) : ℝ) * C`. -/
theorem
    CoarseCaccioppoliVectorCutoffControls.of_canonicalQuantitativeCutoff_of_positiveFactors
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s C : ℝ) {ρ₁ ρ₂ : ℝ}
    (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂)
    (u energy : Vec d → ℝ) (G : Vec d → Vec d) (Acirc1 AcircS : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hu : 0 < cubeLpNorm Q (2 : ℝ≥0∞) u)
    (hAcirc1 : 0 < Acirc1) (hAcircS : 0 ≤ AcircS)
    (hE : 0 < Real.sqrt (cubeAverage Q energy)) (hC : 0 < C)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 * Real.sqrt (cubeAverage Q energy))
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS * Real.sqrt (cubeAverage Q energy)) :
    CoarseCaccioppoliVectorCutoffControls Q s u G
      (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
      energy Acirc1 AcircS (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂)
      C := by
  have hBpos :
      0 < coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ :=
    coarseCaccioppoliQuantitativeCutoffHessianBound_pos Q hlt
  have hBgConst :
      0 <
        coarseCaccioppoliConstantCutoffSize Q u
          (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) :=
    coarseCaccioppoliConstantCutoffSize_pos_of_cubeLpNorm_pos_of_B_pos
      Q u
      (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
      hu hBpos
  have hcard_pos : 0 < (Fintype.card (Fin d) : ℝ) := by
    simp [Fintype.card_fin, Nat.pos_iff_ne_zero, NeZero.ne d]
  have hCeff_pos : 0 < (Fintype.card (Fin d) : ℝ) * C :=
    mul_pos hcard_pos hC
  have hBgCent :
      0 <
        coarseCaccioppoliCenteredCutoffSize Q s
          (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
          Acirc1 AcircS (Real.sqrt (cubeAverage Q energy))
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂)
          ((Fintype.card (Fin d) : ℝ) * C) :=
    coarseCaccioppoliCenteredCutoffSize_pos_of_first_branch
      Q
      (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
      hs0 hs1 hAcirc1 hAcircS hE hBpos hCeff_pos
  let ηρ : QuantitativeCubeCutoff Q ρ₁ ρ₂ :=
    coarseCaccioppoliCanonicalQuantitativeCutoff Q hρ₁ hlt
  have hB :
      0 ≤ coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ :=
    hBpos.le
  simpa [ηρ, coarseCaccioppoliCanonicalQuantitativeCutoff,
    QuantitativeCubeCutoff.canonical, coarseCaccioppoliQuantitativeCutoffHessianBound]
    using
      (CoarseCaccioppoliVectorCutoffControls.of_quantitativeCubeCutoff
        (Q := Q) (s := s) (u := u) (G := G) (energy := energy) (η := ηρ)
        (Acirc1 := Acirc1) (AcircS := AcircS) (C := C)
        (by simpa [coarseCaccioppoliQuantitativeCutoffHessianBound] using hB)
        hAcircS
        (by simpa [ηρ, coarseCaccioppoliCanonicalQuantitativeCutoff,
          QuantitativeCubeCutoff.canonical, coarseCaccioppoliQuantitativeCutoffHessianBound]
          using hBgConst.le)
        (by simpa [ηρ, coarseCaccioppoliCanonicalQuantitativeCutoff,
          QuantitativeCubeCutoff.canonical, coarseCaccioppoliQuantitativeCutoffHessianBound]
          using hBgCent.le)
        hC.le hproj hGcirc1 hGcircS)

/-- Boundary canonical harmonic Caccioppoli with the scalar cutoff-control
bundle rebuilt from the canonical cutoff-product/Poincare inputs. -/
theorem
    coarseCaccioppoli_boundary_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_cutoffProductControls_of_coefficientBounds_of_localizationData_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hlower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) →
        (hρ₂ : ρ₂ ≤ 1) →
        F ρ₁ ≤
          cubeAverage Q
            (fun x =>
              QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x *
                scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) = F ρ₂)
    (hfluxMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (huMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp (fun x => (w ρ₁ ρ₂).toH1 x)
          (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hgMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp (g ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hBgConst :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) →
        (hρ₂ : ρ₂ ≤ 1) →
        0 ≤
          coarseCaccioppoliConstantCutoffSize Q (fun x => (w ρ₁ ρ₂).toH1 x)
            (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
            (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂))
    (hBgCent :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) →
        (hρ₂ : ρ₂ ≤ 1) →
        0 ≤
          coarseCaccioppoliCenteredCutoffSize Q s
            (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
            (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
            (Real.sqrt
              (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)))
            (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C)
    (hAcirc1_nonneg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤ Acirc1 ρ₁ ρ₂)
    (hAcircS_nonneg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤ AcircS ρ₁ ρ₂)
    (hproj :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C
          (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x)) (g ρ₁ ρ₂) N)
    (hgCirc1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (g ρ₁ ρ₂) ≤
          Acirc1 ρ₁ ρ₂ *
            Real.sqrt
              (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)))
    (hgCircS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (g ρ₁ ρ₂) ≤
          AcircS ρ₁ ρ₂ *
            Real.sqrt
              (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)))
    (hU :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => (w ρ₁ ρ₂).toH1 x) ≤ U ρ₁ ρ₂)
    (hA1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        Acirc1 ρ₁ ρ₂ ≤ A1 ρ₁ ρ₂)
    (hAS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        U
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        A1 AS)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData :
      ∀ j ≤ Q.scale, ∀ R ∈ descendantsAtScale Q j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det)
    (hBsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq := by
  have hscalar :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliScalarCutoffControls Q s
          (fun x => (w ρ₁ ρ₂).toH1 x) (g ρ₁ ρ₂)
          (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
          (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    exact
      CoarseCaccioppoliScalarCutoffControls.of_canonicalQuantitativeCutoff
        (Q := Q) (s := s) (C := C) hρ₁ hlt
        (fun x => (w ρ₁ ρ₂).toH1 x) (g ρ₁ ρ₂)
        (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
        (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
        (hBgConst hρ₁ hlt hρ₂) (hBgCent hρ₁ hlt hρ₂) hC
        (hproj hρ₁ hlt hρ₂) (hgCirc1 hρ₁ hlt hρ₂) (hgCircS hρ₁ hlt hρ₂)
  exact
    coarseCaccioppoli_boundary_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_scalarCutoffControls_of_coefficientBounds_of_localizationData_of_localizedExplicitHeightOfScaleChoice
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := k) (F := F) (w := w) (g := g)
      (Acirc1 := Acirc1) (AcircS := AcircS) (U := U) (A1 := A1) (AS := AS)
      hC hs ht hst hu hnonneg hbounded hscale hlower henergyAvg hfluxMem huMem
      hgMem hfluxEnergy hscalar hAcirc1_nonneg hAcircS_nonneg hU hA1 hAS hcoeff
      hEll hData hBsum_s hSigmaSum_t

/-- Interior canonical harmonic Caccioppoli with the scalar cutoff-control
bundle rebuilt from the canonical cutoff-product/Poincare inputs. -/
theorem
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_cutoffProductControls_of_coefficientBounds_of_localizationData_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F G₀ : ℝ → ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hagree : CoarseCaccioppoliRadiusAgreement F G₀)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G₀ ρ)
    (hG_bounded : CoarseCaccioppoliRadiusBoundedAbove G₀)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hlower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) →
        (hρ₂ : ρ₂ ≤ 1) →
        G₀ ρ₁ ≤
          cubeAverage Q
            (fun x =>
              QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x *
                scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) =
          G₀ ρ₂)
    (hfluxMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (huMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp (fun x => (w ρ₁ ρ₂).toH1 x)
          (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hgMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp (g ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hBgConst :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) →
        (hρ₂ : ρ₂ ≤ 1) →
        0 ≤
          coarseCaccioppoliConstantCutoffSize Q (fun x => (w ρ₁ ρ₂).toH1 x)
            (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
            (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂))
    (hBgCent :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) →
        (hρ₂ : ρ₂ ≤ 1) →
        0 ≤
          coarseCaccioppoliCenteredCutoffSize Q s
            (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
            (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
            (Real.sqrt
              (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)))
            (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C)
    (hAcirc1_nonneg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤ Acirc1 ρ₁ ρ₂)
    (hAcircS_nonneg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤ AcircS ρ₁ ρ₂)
    (hproj :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C
          (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x)) (g ρ₁ ρ₂) N)
    (hgCirc1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (g ρ₁ ρ₂) ≤
          Acirc1 ρ₁ ρ₂ *
            Real.sqrt
              (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)))
    (hgCircS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (g ρ₁ ρ₂) ≤
          AcircS ρ₁ ρ₂ *
            Real.sqrt
              (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)))
    (hU :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => (w ρ₁ ρ₂).toH1 x) ≤ U ρ₁ ρ₂)
    (hA1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        Acirc1 ρ₁ ρ₂ ≤ A1 ρ₁ ρ₂)
    (hAS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        U
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        A1 AS)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData :
      ∀ j ≤ Q.scale, ∀ R ∈ descendantsAtScale Q j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det)
    (hBsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := by
  have hscalar :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliScalarCutoffControls Q s
          (fun x => (w ρ₁ ρ₂).toH1 x) (g ρ₁ ρ₂)
          (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
          (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    exact
      CoarseCaccioppoliScalarCutoffControls.of_canonicalQuantitativeCutoff
        (Q := Q) (s := s) (C := C) hρ₁ hlt
        (fun x => (w ρ₁ ρ₂).toH1 x) (g ρ₁ ρ₂)
        (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
        (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
        (hBgConst hρ₁ hlt hρ₂) (hBgCent hρ₁ hlt hρ₂) hC
        (hproj hρ₁ hlt hρ₂) (hgCirc1 hρ₁ hlt hρ₂) (hgCircS hρ₁ hlt hρ₂)
  exact
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_scalarCutoffControls_of_coefficientBounds_of_localizationData_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := k) (F := F) (G₀ := G₀) (w := w) (g := g)
      (Acirc1 := Acirc1) (AcircS := AcircS) (U := U) (A1 := A1) (AS := AS)
      hC hs ht hst hu hagree hG_nonneg hG_bounded hscale hlower henergyAvg
      hfluxMem huMem hgMem hfluxEnergy hscalar hAcirc1_nonneg hAcircS_nonneg
      hU hA1 hAS hcoeff hEll hData hBsum_s hSigmaSum_t

end

end Homogenization
