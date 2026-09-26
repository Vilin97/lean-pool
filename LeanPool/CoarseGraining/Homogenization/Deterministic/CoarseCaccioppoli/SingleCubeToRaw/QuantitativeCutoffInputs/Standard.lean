/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.QuantitativeCutoffInputs.Setup

/-! # Standard -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-- Specialized analytic-input builder for the actual coarse Caccioppoli
harmonic family.  This removes the external `htest` hypothesis once the caller
supplies the weighted-energy lower bound and the cutoff topological-support
condition needed by the weak-testing bridge. -/
theorem
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs.of_quantitativeCubeCutoff_of_aHarmonicFamily
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ) {lam Lam : ℝ}
    (k h : ℝ → ℝ → ℝ) (F : ℝ → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ)
    (η : ∀ ρ₁ ρ₂ : ℝ, QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
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
    (hC : 0 ≤ C)
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
        AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂) :
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs Q a s C
      k h F
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
      A1 AS := by
  refine
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs.of_quantitativeCubeCutoff
      Q a s C k h F
      (fun ρ₁ ρ₂ x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
      (fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1 x)
      g
      (fun ρ₁ ρ₂ x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
      η Acirc1 AcircS U A1 AS ?_ henergyAvg hfluxMem huMem hgMem
      hfluxEnergy hBgConst hBgCent hC hAcirc1_nonneg hAcircS_nonneg
      hproj hgCirc1 hgCircS hU hA1 hAS
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  exact
    le_abs_cubeAverage_vecDot_flux_scalarCutoffGradientField_of_aHarmonicFunction_of_le_cubeAverage_mul_scalarVariationEnergyIntegrand
      Q a (w ρ₁ ρ₂) hEll (η ρ₁ ρ₂).smooth (η ρ₁ ρ₂).hasCompactSupport
      (hη_tsupport hρ₁ hlt hρ₂) (hlower hρ₁ hlt hρ₂)

theorem
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs.of_quantitativeCubeCutoff_of_aHarmonicFamily_of_scalarCutoffControls
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ) {lam Lam : ℝ}
    (k h : ℝ → ℝ → ℝ) (F : ℝ → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ)
    (η : ∀ ρ₁ ρ₂ : ℝ, QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
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
    (hscalar :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliScalarCutoffControls Q s
          (fun x => (w ρ₁ ρ₂).toH1 x) (g ρ₁ ρ₂)
          (scalarCutoffGradientField (η ρ₁ ρ₂))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
          (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C)
    (hC : 0 ≤ C)
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
        AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂) :
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs Q a s C
      k h F
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
      A1 AS := by
  refine
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs.of_quantitativeCubeCutoff_of_aHarmonicFamily
      Q a s C k h F w g η Acirc1 AcircS U A1 AS
      hEll hlower hη_tsupport henergyAvg hfluxMem huMem hgMem hfluxEnergy
      ?_ ?_ hC hAcirc1_nonneg hAcircS_nonneg ?_ ?_ ?_ hU hA1 hAS
  · intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    rcases hscalar hρ₁ hlt hρ₂ with
      ⟨hB, hBgConst, hBgCent, hC', hproj, hξ, hderiv, hgCirc1, hgCircS⟩
    exact hBgConst
  · intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    rcases hscalar hρ₁ hlt hρ₂ with
      ⟨hB, hBgConst, hBgCent, hC', hproj, hξ, hderiv, hgCirc1, hgCircS⟩
    exact hBgCent
  · intro ρ₁ ρ₂ hρ₁ hlt hρ₂ N
    rcases hscalar hρ₁ hlt hρ₂ with
      ⟨hB, hBgConst, hBgCent, hC', hproj, hξ, hderiv, hgCirc1, hgCircS⟩
    exact hproj N
  · intro ρ₁ ρ₂ hρ₁ hlt hρ₂ N
    rcases hscalar hρ₁ hlt hρ₂ with
      ⟨hB, hBgConst, hBgCent, hC', hproj, hξ, hderiv, hgCirc1, hgCircS⟩
    exact hgCirc1 N
  · intro ρ₁ ρ₂ hρ₁ hlt hρ₂ N
    rcases hscalar hρ₁ hlt hρ₂ with
      ⟨hB, hBgConst, hBgCent, hC', hproj, hξ, hderiv, hgCirc1, hgCircS⟩
    exact hgCircS N

theorem
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs.of_quantitativeCubeCutoff_of_aHarmonicFamily_of_outerRadius_lt_one
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ) {lam Lam : ℝ}
    (k h : ℝ → ℝ → ℝ) (F : ℝ → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ)
    (η : ∀ ρ₁ ρ₂ : ℝ, QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
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
    (hC : 0 ≤ C)
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
        AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂) :
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs Q a s C
      k h F
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
      A1 AS := by
  refine
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs.of_quantitativeCubeCutoff_of_aHarmonicFamily
      Q a s C k h F w g η Acirc1 AcircS U A1 AS hEll hlower ?_
      henergyAvg hfluxMem huMem hgMem hfluxEnergy hBgConst hBgCent hC
      hAcirc1_nonneg hAcircS_nonneg hproj hgCirc1 hgCircS hU hA1 hAS
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  have hρ₂_nonneg : 0 ≤ ρ₂ := by
    exact le_trans (by norm_num : 0 ≤ (1 / 3 : ℝ)) <|
      le_trans hρ₁ (le_of_lt hlt)
  exact (η ρ₁ ρ₂).tsupport_subset_openCubeSet_of_lt_one
    hρ₂_nonneg (houter hρ₁ hlt hρ₂)

/-- Quantitative-cutoff harmonic analytic inputs with the scalar cutoff package
bundled as `CoarseCaccioppoliScalarCutoffControls`. -/
theorem
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs.of_quantitativeCubeCutoff_of_aHarmonicFamily_of_outerRadius_lt_one_of_scalarCutoffControls
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ) {lam Lam : ℝ}
    (k h : ℝ → ℝ → ℝ) (F : ℝ → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ)
    (η : ∀ ρ₁ ρ₂ : ℝ, QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
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
    (hscalar :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliScalarCutoffControls Q s
          (fun x => (w ρ₁ ρ₂).toH1 x) (g ρ₁ ρ₂)
          (scalarCutoffGradientField (η ρ₁ ρ₂))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
          (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C)
    (hC : 0 ≤ C)
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
        AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂) :
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs Q a s C
      k h F
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
      A1 AS := by
  refine
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs.of_quantitativeCubeCutoff_of_aHarmonicFamily_of_scalarCutoffControls
      Q a s C k h F w g η Acirc1 AcircS U A1 AS
      hEll hlower ?_ henergyAvg hfluxMem huMem hgMem hfluxEnergy hscalar
      hC hAcirc1_nonneg hAcircS_nonneg hU hA1 hAS
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  have hρ₂_nonneg : 0 ≤ ρ₂ := by
    exact le_trans (by norm_num : 0 ≤ (1 / 3 : ℝ)) <|
      le_trans hρ₁ (le_of_lt hlt)
  exact (η ρ₁ ρ₂).tsupport_subset_openCubeSet_of_lt_one
    hρ₂_nonneg (houter hρ₁ hlt hρ₂)

/-- Canonical analytic-input builder for the actual harmonic family using the
chapter-3 canonical quantitative cube cutoff.  The cutoff data are discharged
from the canonical smooth formula plus the strict outer-radius condition
`ρ₂ < 1`. -/
theorem
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs.of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_outerRadius_lt_one
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ) {lam Lam : ℝ}
    (k h : ℝ → ℝ → ℝ) (F : ℝ → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hlower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) → (hρ₂ : ρ₂ ≤ 1) →
        F ρ₁ ≤
          cubeAverage Q
            (fun x =>
              QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x *
                scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (houter :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) → (hρ₂ : ρ₂ ≤ 1) →
        ρ₂ < 1)
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
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) → (hρ₂ : ρ₂ ≤ 1) →
        0 ≤
          coarseCaccioppoliConstantCutoffSize Q (fun x => (w ρ₁ ρ₂).toH1 x)
            (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
            (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂))
    (hBgCent :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) → (hρ₂ : ρ₂ ≤ 1) →
        0 ≤
          coarseCaccioppoliCenteredCutoffSize Q s
            (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
            (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
            (Real.sqrt
              (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)))
            (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C)
    (hC : 0 ≤ C)
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
        AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂) :
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs Q a s C
      k h F
      (fun ρ₁ ρ₂ x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
      (fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1 x)
      g
      (fun ρ₁ ρ₂ => scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
      (fun ρ₁ ρ₂ x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
      Acirc1 AcircS
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      U
      (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      A1 AS := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  let ηρ : QuantitativeCubeCutoff Q ρ₁ ρ₂ :=
    coarseCaccioppoliCanonicalQuantitativeCutoff Q hρ₁ hlt
  have hB_nonneg :
      0 ≤ coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ :=
    coarseCaccioppoliQuantitativeCutoffHessianBound_nonneg Q ηρ
  have hBgConstρ :
      0 ≤
        coarseCaccioppoliConstantCutoffSize Q (fun x => (w ρ₁ ρ₂).toH1 x)
          (scalarCutoffGradientField ηρ)
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) := by
    simpa [ηρ, coarseCaccioppoliCanonicalQuantitativeCutoff,
      QuantitativeCubeCutoff.canonical] using hBgConst hρ₁ hlt hρ₂
  have hBgCentρ :
      0 ≤
        coarseCaccioppoliCenteredCutoffSize Q s
          (scalarCutoffGradientField ηρ)
          (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
          (Real.sqrt
            (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)))
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C := by
    simpa [ηρ, coarseCaccioppoliCanonicalQuantitativeCutoff,
      QuantitativeCubeCutoff.canonical] using hBgCent hρ₁ hlt hρ₂
  have hscalar :
      CoarseCaccioppoliScalarCutoffControls Q s
        (fun x => (w ρ₁ ρ₂).toH1 x) (g ρ₁ ρ₂)
        (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
        (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
        (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C := by
    simpa [ηρ, coarseCaccioppoliCanonicalQuantitativeCutoff,
      QuantitativeCubeCutoff.canonical] using!
      (CoarseCaccioppoliScalarCutoffControls.of_quantitativeCubeCutoff
        (Q := Q) (s := s)
        (u := fun x => (w ρ₁ ρ₂).toH1 x) (g := g ρ₁ ρ₂)
        (energy := fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
        (η := ηρ) (Acirc1 := Acirc1 ρ₁ ρ₂) (AcircS := AcircS ρ₁ ρ₂) (C := C)
        hB_nonneg hBgConstρ hBgCentρ hC
        (hproj hρ₁ hlt hρ₂) (hgCirc1 hρ₁ hlt hρ₂) (hgCircS hρ₁ hlt hρ₂))
  have htest :
      F ρ₁ ≤
        |cubeAverage Q
          (fun x =>
            vecDot (matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
              ((w ρ₁ ρ₂).toH1 x •
                scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x))| := by
    simpa [ηρ, coarseCaccioppoliCanonicalQuantitativeCutoff,
      QuantitativeCubeCutoff.canonical] using
      (le_abs_cubeAverage_vecDot_flux_scalarCutoffGradientField_of_aHarmonicFunction_of_le_cubeAverage_mul_scalarVariationEnergyIntegrand
        Q a (w ρ₁ ρ₂) hEll ηρ.smooth ηρ.hasCompactSupport
        (coarseCaccioppoliCanonicalQuantitativeCutoff_tsupport_subset_openCubeSet_of_lt_one
          Q hρ₁ hlt (houter hρ₁ hlt hρ₂))
        (hlower hρ₁ hlt hρ₂))
  have hξ_mem :
      MeasureTheory.MemLp
        (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
        (⊤ : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa [ηρ, coarseCaccioppoliCanonicalQuantitativeCutoff,
      QuantitativeCubeCutoff.canonical] using
      quantitativeCubeCutoff_memLp_top_gradientField Q ηρ
  have hXi :
      cubeLpNorm Q (⊤ : ℝ≥0∞)
        (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂)) ≤
          coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂ := by
    simpa [ηρ, coarseCaccioppoliCanonicalQuantitativeCutoff,
      QuantitativeCubeCutoff.canonical] using!
      quantitativeCubeCutoff_cubeLpNorm_infty_gradientField_le Q ηρ
  exact
    ⟨htest, henergyAvg hρ₁ hlt hρ₂, hfluxMem hρ₁ hlt hρ₂,
      huMem hρ₁ hlt hρ₂, hgMem hρ₁ hlt hρ₂, hξ_mem,
      hfluxEnergy hρ₁ hlt hρ₂, hscalar, hB_nonneg,
      hAcirc1_nonneg hρ₁ hlt hρ₂, hAcircS_nonneg hρ₁ hlt hρ₂,
      hU hρ₁ hlt hρ₂, hXi, le_rfl, hA1 hρ₁ hlt hρ₂, hAS hρ₁ hlt hρ₂⟩


end

end Homogenization
