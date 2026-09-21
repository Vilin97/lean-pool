/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.FinalWrappers

/-! # Standard -/

namespace Homogenization

noncomputable section

open scoped ENNReal

/-- Boundary coarse Caccioppoli for the actual harmonic family, with the
testing inequality discharged by the weak-testing bridge and a quantitative
cutoff family. -/
theorem
    coarseCaccioppoli_boundary_qone_of_quantitativeCutoff_of_aHarmonicFamily_of_coefficientBounds_of_multiscaleEllipticity_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ)
    (η : ∀ ρ₁ ρ₂ : ℝ, QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hlower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        F ρ₁ ≤
          cubeAverage Q
            (fun x => η ρ₁ ρ₂ x * scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hη_tsupport :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        tsupport (η ρ₁ ρ₂) ⊆ openCubeSet Q)
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
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤
          coarseCaccioppoliConstantCutoffSize Q (fun x => (w ρ₁ ρ₂).toH1 x)
            (scalarCutoffGradientField (η ρ₁ ρ₂))
            (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂))
    (hBgCent :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤
          coarseCaccioppoliCenteredCutoffSize Q s
            (scalarCutoffGradientField (η ρ₁ ρ₂))
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
  exact
    coarseCaccioppoli_boundary_qone_of_radiusEnergyBridgeCanonicalAnalyticInputs_of_coefficientBounds_of_multiscaleEllipticity_of_localizedExplicitHeightOfScaleChoice
      Q a s t C uL2Sq k
      (fun ρ₁ ρ₂ x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
      (fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1 x)
      g
      (fun ρ₁ ρ₂ => scalarCutoffGradientField (η ρ₁ ρ₂))
      (fun ρ₁ ρ₂ x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
      Acirc1 AcircS
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      U
      (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      A1 AS
      hC hs ht hst hu hnonneg hbounded hscale
      (CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs.of_quantitativeCubeCutoff_of_aHarmonicFamily
          Q a s C
          (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
          (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
          F w g η Acirc1 AcircS U A1 AS
          hEll hlower hη_tsupport henergyAvg hfluxMem huMem hgMem hfluxEnergy
          hBgConst hBgCent hC hAcirc1_nonneg hAcircS_nonneg hproj hgCirc1 hgCircS
          hU hA1 hAS)
      hcoeff hEll hData hBsum_s hSigmaSum_t

/-- Boundary coarse Caccioppoli for the actual harmonic family, with cutoff
support discharged from the strict outer-radius condition `ρ₂ < 1`. -/
theorem
    coarseCaccioppoli_boundary_qone_of_quantitativeCutoff_of_aHarmonicFamily_of_outerRadius_lt_one_of_coefficientBounds_of_multiscaleEllipticity_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ)
    (η : ∀ ρ₁ ρ₂ : ℝ, QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hlower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        F ρ₁ ≤
          cubeAverage Q
            (fun x => η ρ₁ ρ₂ x * scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (houter :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ρ₂ < 1)
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
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤
          coarseCaccioppoliConstantCutoffSize Q (fun x => (w ρ₁ ρ₂).toH1 x)
            (scalarCutoffGradientField (η ρ₁ ρ₂))
            (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂))
    (hBgCent :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤
          coarseCaccioppoliCenteredCutoffSize Q s
            (scalarCutoffGradientField (η ρ₁ ρ₂))
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
  exact
    coarseCaccioppoli_boundary_qone_of_radiusEnergyBridgeCanonicalAnalyticInputs_of_coefficientBounds_of_multiscaleEllipticity_of_localizedExplicitHeightOfScaleChoice
      Q a s t C uL2Sq k
      (fun ρ₁ ρ₂ x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
      (fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1 x)
      g
      (fun ρ₁ ρ₂ => scalarCutoffGradientField (η ρ₁ ρ₂))
      (fun ρ₁ ρ₂ x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
      Acirc1 AcircS
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      U
      (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      A1 AS
      hC hs ht hst hu hnonneg hbounded hscale
      (CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs.of_quantitativeCubeCutoff_of_aHarmonicFamily_of_outerRadius_lt_one
          Q a s C
          (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
          (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
          F w g η Acirc1 AcircS U A1 AS
          hEll hlower houter henergyAvg hfluxMem huMem hgMem hfluxEnergy
          hBgConst hBgCent hC hAcirc1_nonneg hAcircS_nonneg hproj hgCirc1 hgCircS
          hU hA1 hAS)
      hcoeff hEll hData hBsum_s hSigmaSum_t

/-- Interior coarse Caccioppoli for the actual harmonic family, transported
across the radius agreement used for the centered quantity. -/
theorem
    coarseCaccioppoli_interior_qone_of_quantitativeCutoff_of_aHarmonicFamily_of_coefficientBounds_of_multiscaleEllipticity_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F G₀ : ℝ → ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ)
    (η : ∀ ρ₁ ρ₂ : ℝ, QuantitativeCubeCutoff Q ρ₁ ρ₂)
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
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        G₀ ρ₁ ≤
          cubeAverage Q
            (fun x => η ρ₁ ρ₂ x * scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hη_tsupport :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        tsupport (η ρ₁ ρ₂) ⊆ openCubeSet Q)
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) = G₀ ρ₂)
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
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤
          coarseCaccioppoliConstantCutoffSize Q (fun x => (w ρ₁ ρ₂).toH1 x)
            (scalarCutoffGradientField (η ρ₁ ρ₂))
            (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂))
    (hBgCent :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤
          coarseCaccioppoliCenteredCutoffSize Q s
            (scalarCutoffGradientField (η ρ₁ ρ₂))
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
  exact
    coarseCaccioppoli_interior_qone_of_radiusEnergyBridgeCanonicalAnalyticInputs_of_coefficientBounds_of_multiscaleEllipticity_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
      Q a s t C uL2Sq k
      (fun ρ₁ ρ₂ x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
      (fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1 x)
      g
      (fun ρ₁ ρ₂ => scalarCutoffGradientField (η ρ₁ ρ₂))
      (fun ρ₁ ρ₂ x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
      Acirc1 AcircS
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      U
      (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      A1 AS
      hC hs ht hst hu hagree hG_nonneg hG_bounded hscale
      (CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs.of_quantitativeCubeCutoff_of_aHarmonicFamily
          Q a s C
          (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
          (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
          G₀ w g η Acirc1 AcircS U A1 AS
          hEll hlower hη_tsupport henergyAvg hfluxMem huMem hgMem hfluxEnergy
          hBgConst hBgCent hC hAcirc1_nonneg hAcircS_nonneg hproj hgCirc1 hgCircS
          hU hA1 hAS)
      hcoeff hEll hData hBsum_s hSigmaSum_t

/-- Interior coarse Caccioppoli for the actual harmonic family, with cutoff
support discharged from the strict outer-radius condition `ρ₂ < 1`. -/
theorem
    coarseCaccioppoli_interior_qone_of_quantitativeCutoff_of_aHarmonicFamily_of_outerRadius_lt_one_of_coefficientBounds_of_multiscaleEllipticity_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F G₀ : ℝ → ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ)
    (η : ∀ ρ₁ ρ₂ : ℝ, QuantitativeCubeCutoff Q ρ₁ ρ₂)
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
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        G₀ ρ₁ ≤
          cubeAverage Q
            (fun x => η ρ₁ ρ₂ x * scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (houter :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ρ₂ < 1)
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) = G₀ ρ₂)
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
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤
          coarseCaccioppoliConstantCutoffSize Q (fun x => (w ρ₁ ρ₂).toH1 x)
            (scalarCutoffGradientField (η ρ₁ ρ₂))
            (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂))
    (hBgCent :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤
          coarseCaccioppoliCenteredCutoffSize Q s
            (scalarCutoffGradientField (η ρ₁ ρ₂))
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
  exact
    coarseCaccioppoli_interior_qone_of_radiusEnergyBridgeCanonicalAnalyticInputs_of_coefficientBounds_of_multiscaleEllipticity_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
      Q a s t C uL2Sq k
      (fun ρ₁ ρ₂ x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
      (fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1 x)
      g
      (fun ρ₁ ρ₂ => scalarCutoffGradientField (η ρ₁ ρ₂))
      (fun ρ₁ ρ₂ x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
      Acirc1 AcircS
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      U
      (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      A1 AS
      hC hs ht hst hu hagree hG_nonneg hG_bounded hscale
      (CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs.of_quantitativeCubeCutoff_of_aHarmonicFamily_of_outerRadius_lt_one
          Q a s C
          (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
          (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
          G₀ w g η Acirc1 AcircS U A1 AS
          hEll hlower houter henergyAvg hfluxMem huMem hgMem hfluxEnergy
          hBgConst hBgCent hC hAcirc1_nonneg hAcircS_nonneg hproj hgCirc1 hgCircS
          hU hA1 hAS)
      hcoeff hEll hData hBsum_s hSigmaSum_t


end

end Homogenization
