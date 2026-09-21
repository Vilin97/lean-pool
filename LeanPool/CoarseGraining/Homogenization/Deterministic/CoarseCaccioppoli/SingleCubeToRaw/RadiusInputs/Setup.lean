/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.Localization
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.LocalEstimate.Split

/-! # Setup -/

namespace Homogenization

noncomputable section

open scoped ENNReal

/-- Radius-indexed local data sufficient for the energy bridge to produce the
single-cube note estimate at every radius pair.  This packages the testing
inequality, `L^p` hypotheses, flux-energy controls, scalar cutoff controls, and
the two exact local coefficient inequalities. -/
def CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s C uL2Sq : ℝ) (k h : ℝ → ℝ → ℝ) (F : ℝ → ℝ)
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    (F ρ₁ ≤
        |cubeAverage Q
          (fun x => vecDot (flux ρ₁ ρ₂ x) ((u ρ₁ ρ₂ x) • ξ ρ₁ ρ₂ x))|) ∧
      cubeAverage Q (energy ρ₁ ρ₂) = F ρ₂ ∧
      MeasureTheory.MemLp (flux ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      MeasureTheory.MemLp (u ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      MeasureTheory.MemLp (g ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      MeasureTheory.MemLp (ξ ρ₁ ρ₂) ∞ (normalizedCubeMeasure Q) ∧
      CoarseCaccioppoliFluxEnergyControls Q a s (flux ρ₁ ρ₂) (energy ρ₁ ρ₂) ∧
      CoarseCaccioppoliScalarCutoffControls Q s (u ρ₁ ρ₂) (g ρ₁ ρ₂) (ξ ρ₁ ρ₂)
        (energy ρ₁ ρ₂) (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂) (B ρ₁ ρ₂) C ∧
      CoarseCaccioppoliSingleCubeCoefficientControls Q a s C (k ρ₁ ρ₂) (h ρ₁ ρ₂)
        uL2Sq (u ρ₁ ρ₂) (ξ ρ₁ ρ₂) (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
        (B ρ₁ ρ₂)

/-- Radius-indexed energy bridge inputs with the final coefficient comparison
kept in the separated factor form supplied by
`CoarseCaccioppoliSingleCubeCoefficientControls.of_factor_bounds`. -/
def CoarseCaccioppoliBoundaryRadiusEnergyBridgeFactorInputs {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s C uL2Sq : ℝ) (k h : ℝ → ℝ → ℝ) (F : ℝ → ℝ)
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B A G X Y : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    (F ρ₁ ≤
        |cubeAverage Q
          (fun x => vecDot (flux ρ₁ ρ₂ x) ((u ρ₁ ρ₂ x) • ξ ρ₁ ρ₂ x))|) ∧
      cubeAverage Q (energy ρ₁ ρ₂) = F ρ₂ ∧
      MeasureTheory.MemLp (flux ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      MeasureTheory.MemLp (u ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      MeasureTheory.MemLp (g ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      MeasureTheory.MemLp (ξ ρ₁ ρ₂) ∞ (normalizedCubeMeasure Q) ∧
      CoarseCaccioppoliFluxEnergyControls Q a s (flux ρ₁ ρ₂) (energy ρ₁ ρ₂) ∧
      CoarseCaccioppoliScalarCutoffControls Q s (u ρ₁ ρ₂) (g ρ₁ ρ₂) (ξ ρ₁ ρ₂)
        (energy ρ₁ ρ₂) (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂) (B ρ₁ ρ₂) C ∧
      0 ≤ A ρ₁ ρ₂ ∧
      coarseCaccioppoliFluxEnergyExactConstantCoeff Q a ≤ A ρ₁ ρ₂ ∧
      coarseCaccioppoliConstantCutoffSize Q (u ρ₁ ρ₂) (ξ ρ₁ ρ₂) (B ρ₁ ρ₂) ≤
        G ρ₁ ρ₂ ∧
      A ρ₁ ρ₂ * G ρ₁ ρ₂ ≤
        coarseCaccioppoliSingleCubeBoundaryConstantCoeff Q a C (k ρ₁ ρ₂) uL2Sq ∧
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff Q a (ξ ρ₁ ρ₂)
        (Acirc1 ρ₁ ρ₂) C ≤ X ρ₁ ρ₂ ∧
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff Q a s (ξ ρ₁ ρ₂)
        (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂) (B ρ₁ ρ₂) C ≤ Y ρ₁ ρ₂ ∧
      X ρ₁ ρ₂ + Y ρ₁ ρ₂ ≤
        coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C (k ρ₁ ρ₂) (h ρ₁ ρ₂)

/-- Radius-indexed energy bridge inputs with the coefficient comparison stated
in primitive separated scalar factors.  This is the closest current interface
to a concrete cutoff construction: callers provide bounds for `‖u‖₂`,
`‖ξ‖∞`, `‖∇ξ‖∞`, the two scalar projected-Poincare factors, and the three
coefficient factors. -/
def CoarseCaccioppoliBoundaryRadiusEnergyBridgeSeparatedFactorInputs {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) (F : ℝ → ℝ)
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B AavgConst AavgCent Aflux1 AfluxS U Xi D A1 AS :
      ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    (F ρ₁ ≤
        |cubeAverage Q
          (fun x => vecDot (flux ρ₁ ρ₂ x) ((u ρ₁ ρ₂ x) • ξ ρ₁ ρ₂ x))|) ∧
      cubeAverage Q (energy ρ₁ ρ₂) = F ρ₂ ∧
      MeasureTheory.MemLp (flux ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      MeasureTheory.MemLp (u ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      MeasureTheory.MemLp (g ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      MeasureTheory.MemLp (ξ ρ₁ ρ₂) ∞ (normalizedCubeMeasure Q) ∧
      CoarseCaccioppoliFluxEnergyControls Q a s (flux ρ₁ ρ₂) (energy ρ₁ ρ₂) ∧
      CoarseCaccioppoliScalarCutoffControls Q s (u ρ₁ ρ₂) (g ρ₁ ρ₂) (ξ ρ₁ ρ₂)
        (energy ρ₁ ρ₂) (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂) (B ρ₁ ρ₂) C ∧
      0 ≤ B ρ₁ ρ₂ ∧
      0 ≤ Acirc1 ρ₁ ρ₂ ∧
      0 ≤ AcircS ρ₁ ρ₂ ∧
      Real.sqrt (coarseBBlockNorm Q a) ≤ AavgConst ρ₁ ρ₂ ∧
      Real.sqrt (coarseBBlockNorm Q a) ≤ AavgCent ρ₁ ρ₂ ∧
      (geometricDiscount (1 : ℝ) 1)⁻¹ *
          Real.rpow (LambdaSq Q (1 : ℝ) (.finite 1) a) (1 / 2 : ℝ) ≤
        Aflux1 ρ₁ ρ₂ ∧
      (geometricDiscount s 1)⁻¹ *
          Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) ≤
        AfluxS ρ₁ ρ₂ ∧
      cubeLpNorm Q (2 : ℝ≥0∞) (u ρ₁ ρ₂) ≤ U ρ₁ ρ₂ ∧
      cubeLpNorm Q ∞ (ξ ρ₁ ρ₂) ≤ Xi ρ₁ ρ₂ ∧
      B ρ₁ ρ₂ ≤ D ρ₁ ρ₂ ∧
      Acirc1 ρ₁ ρ₂ ≤ A1 ρ₁ ρ₂ ∧
      AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂ ∧
      coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound Q
            (AavgConst ρ₁ ρ₂) (Aflux1 ρ₁ ρ₂) *
          coarseCaccioppoliConstantCutoffSizeFactorBound Q
            (U ρ₁ ρ₂) (Xi ρ₁ ρ₂) (D ρ₁ ρ₂) ≤
        coarseCaccioppoliSingleCubeBoundaryConstantCoeff Q a C (k ρ₁ ρ₂) uL2Sq ∧
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
          (d := d) (AavgCent ρ₁ ρ₂) (Xi ρ₁ ρ₂) (A1 ρ₁ ρ₂) C +
        coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound Q s
          (AavgCent ρ₁ ρ₂) (AfluxS ρ₁ ρ₂)
          (coarseCaccioppoliCenteredCutoffCoeffFactorBound Q s
            (Xi ρ₁ ρ₂) (D ρ₁ ρ₂) (A1 ρ₁ ρ₂) (AS ρ₁ ρ₂) C) ≤
      coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C (k ρ₁ ρ₂) (h ρ₁ ρ₂)

/-- Radius-indexed energy bridge inputs with the coefficient factors fixed to
the canonical `LambdaSq` choices.  This removes the four average/flux
coefficient slots from the caller-facing local interface; the bounds for those
slots are recovered from the flux-energy summability hypotheses. -/
def CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalFactorInputs {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) (F : ℝ → ℝ)
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B U Xi D A1 AS : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    (F ρ₁ ≤
        |cubeAverage Q
          (fun x => vecDot (flux ρ₁ ρ₂ x) ((u ρ₁ ρ₂ x) • ξ ρ₁ ρ₂ x))|) ∧
      cubeAverage Q (energy ρ₁ ρ₂) = F ρ₂ ∧
      MeasureTheory.MemLp (flux ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      MeasureTheory.MemLp (u ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      MeasureTheory.MemLp (g ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      MeasureTheory.MemLp (ξ ρ₁ ρ₂) ∞ (normalizedCubeMeasure Q) ∧
      CoarseCaccioppoliFluxEnergyControls Q a s (flux ρ₁ ρ₂) (energy ρ₁ ρ₂) ∧
      CoarseCaccioppoliScalarCutoffControls Q s (u ρ₁ ρ₂) (g ρ₁ ρ₂) (ξ ρ₁ ρ₂)
        (energy ρ₁ ρ₂) (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂) (B ρ₁ ρ₂) C ∧
      0 ≤ B ρ₁ ρ₂ ∧
      0 ≤ Acirc1 ρ₁ ρ₂ ∧
      0 ≤ AcircS ρ₁ ρ₂ ∧
      cubeLpNorm Q (2 : ℝ≥0∞) (u ρ₁ ρ₂) ≤ U ρ₁ ρ₂ ∧
      cubeLpNorm Q ∞ (ξ ρ₁ ρ₂) ≤ Xi ρ₁ ρ₂ ∧
      B ρ₁ ρ₂ ≤ D ρ₁ ρ₂ ∧
      Acirc1 ρ₁ ρ₂ ≤ A1 ρ₁ ρ₂ ∧
      AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂ ∧
      coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound Q
            (coarseCaccioppoliLambdaFactor Q a (1 : ℝ))
            (coarseCaccioppoliLambdaFactor Q a (1 : ℝ)) *
          coarseCaccioppoliConstantCutoffSizeFactorBound Q
            (U ρ₁ ρ₂) (Xi ρ₁ ρ₂) (D ρ₁ ρ₂) ≤
        coarseCaccioppoliSingleCubeBoundaryConstantCoeff Q a C (k ρ₁ ρ₂) uL2Sq ∧
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
          (d := d) (coarseCaccioppoliLambdaFactor Q a s)
          (Xi ρ₁ ρ₂) (A1 ρ₁ ρ₂) C +
        coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound Q s
          (coarseCaccioppoliLambdaFactor Q a s)
          (coarseCaccioppoliLambdaFactor Q a s)
          (coarseCaccioppoliCenteredCutoffCoeffFactorBound Q s
            (Xi ρ₁ ρ₂) (D ρ₁ ρ₂) (A1 ρ₁ ρ₂) (AS ρ₁ ρ₂) C) ≤
        coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C (k ρ₁ ρ₂) (h ρ₁ ρ₂)

/-- Analytic/local part of the canonical radius-indexed energy bridge inputs.
This deliberately omits the final two single-cube coefficient inequalities:
those are separated below so an actual cutoff construction can first prove the
testing, integrability, flux-energy, scalar-cutoff, and primitive scalar bounds
without also carrying the coefficient-localization algebra. -/
def CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ)
    (_k _h : ℝ → ℝ → ℝ) (F : ℝ → ℝ)
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B U Xi D A1 AS : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    (F ρ₁ ≤
        |cubeAverage Q
          (fun x => vecDot (flux ρ₁ ρ₂ x) ((u ρ₁ ρ₂ x) • ξ ρ₁ ρ₂ x))|) ∧
      cubeAverage Q (energy ρ₁ ρ₂) = F ρ₂ ∧
      MeasureTheory.MemLp (flux ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      MeasureTheory.MemLp (u ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      MeasureTheory.MemLp (g ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      MeasureTheory.MemLp (ξ ρ₁ ρ₂) ∞ (normalizedCubeMeasure Q) ∧
      CoarseCaccioppoliFluxEnergyControls Q a s (flux ρ₁ ρ₂) (energy ρ₁ ρ₂) ∧
      CoarseCaccioppoliScalarCutoffControls Q s (u ρ₁ ρ₂) (g ρ₁ ρ₂) (ξ ρ₁ ρ₂)
        (energy ρ₁ ρ₂) (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂) (B ρ₁ ρ₂) C ∧
      0 ≤ B ρ₁ ρ₂ ∧
      0 ≤ Acirc1 ρ₁ ρ₂ ∧
      0 ≤ AcircS ρ₁ ρ₂ ∧
      cubeLpNorm Q (2 : ℝ≥0∞) (u ρ₁ ρ₂) ≤ U ρ₁ ρ₂ ∧
      cubeLpNorm Q ∞ (ξ ρ₁ ρ₂) ≤ Xi ρ₁ ρ₂ ∧
      B ρ₁ ρ₂ ≤ D ρ₁ ρ₂ ∧
      Acirc1 ρ₁ ρ₂ ≤ A1 ρ₁ ρ₂ ∧
      AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂

/-- Vector-Poincare version of
`CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs`.

The local cutoff package uses a vector Poincare constant `C`; downstream
coefficient and height bounds are stated with the effective scalar-facing
constant `(Fintype.card (Fin d) : ℝ) * C`. -/
def CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalVectorAnalyticInputs {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ)
    (_k _h : ℝ → ℝ → ℝ) (F : ℝ → ℝ)
    (flux : ℝ → ℝ → Vec d → Vec d) (u : ℝ → ℝ → Vec d → ℝ)
    (G : ℝ → ℝ → Vec d → Vec d)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B U Xi D A1 AS : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    (F ρ₁ ≤
        |cubeAverage Q
          (fun x => vecDot (flux ρ₁ ρ₂ x) ((u ρ₁ ρ₂ x) • ξ ρ₁ ρ₂ x))|) ∧
      cubeAverage Q (energy ρ₁ ρ₂) = F ρ₂ ∧
      MeasureTheory.MemLp (flux ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      MeasureTheory.MemLp (u ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      (∀ i : Fin d,
        MeasureTheory.MemLp (fun x => G ρ₁ ρ₂ x i) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q)) ∧
      MeasureTheory.MemLp (ξ ρ₁ ρ₂) ∞ (normalizedCubeMeasure Q) ∧
      CoarseCaccioppoliFluxEnergyControls Q a s (flux ρ₁ ρ₂) (energy ρ₁ ρ₂) ∧
      CoarseCaccioppoliVectorCutoffControls Q s (u ρ₁ ρ₂) (G ρ₁ ρ₂) (ξ ρ₁ ρ₂)
        (energy ρ₁ ρ₂) (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂) (B ρ₁ ρ₂) C ∧
      0 ≤ B ρ₁ ρ₂ ∧
      0 ≤ Acirc1 ρ₁ ρ₂ ∧
      0 ≤ AcircS ρ₁ ρ₂ ∧
      cubeLpNorm Q (2 : ℝ≥0∞) (u ρ₁ ρ₂) ≤ U ρ₁ ρ₂ ∧
      cubeLpNorm Q ∞ (ξ ρ₁ ρ₂) ≤ Xi ρ₁ ρ₂ ∧
      B ρ₁ ρ₂ ≤ D ρ₁ ρ₂ ∧
      Acirc1 ρ₁ ρ₂ ≤ A1 ρ₁ ρ₂ ∧
      AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂

/-- The two radius-indexed coefficient inequalities left after the canonical
local analytic inputs have been supplied.  This is the formal target for the
Chapter 3 cutoff-scale algebra: constant branch and centered branch. -/
def CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) (U Xi D A1 AS : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound Q
          (coarseCaccioppoliLambdaFactor Q a (1 : ℝ))
          (coarseCaccioppoliLambdaFactor Q a (1 : ℝ)) *
        coarseCaccioppoliConstantCutoffSizeFactorBound Q
          (U ρ₁ ρ₂) (Xi ρ₁ ρ₂) (D ρ₁ ρ₂) ≤
      coarseCaccioppoliSingleCubeBoundaryConstantCoeff Q a C (k ρ₁ ρ₂) uL2Sq ∧
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
        (d := d) (coarseCaccioppoliLambdaFactor Q a s)
        (Xi ρ₁ ρ₂) (A1 ρ₁ ρ₂) C +
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound Q s
        (coarseCaccioppoliLambdaFactor Q a s)
        (coarseCaccioppoliLambdaFactor Q a s)
        (coarseCaccioppoliCenteredCutoffCoeffFactorBound Q s
          (Xi ρ₁ ρ₂) (D ρ₁ ρ₂) (A1 ρ₁ ρ₂) (AS ρ₁ ρ₂) C) ≤
      coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C (k ρ₁ ρ₂) (h ρ₁ ρ₂)

/-- Direct radius-indexed comparison from the canonical factor bounds to the
final boundary raw coefficients.  This is the natural top-level bookkeeping
surface once the local estimate is targeted straight at the note's raw
radius recursion rather than routed through the intermediate single-cube
coefficients. -/
def CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalRawCoefficientBounds {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ) (U Xi D A1 AS : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound Q
          (coarseCaccioppoliLambdaFactor Q a (1 : ℝ))
          (coarseCaccioppoliLambdaFactor Q a (1 : ℝ)) *
        coarseCaccioppoliConstantCutoffSizeFactorBound Q
          (U ρ₁ ρ₂) (Xi ρ₁ ρ₂) (D ρ₁ ρ₂) ≤
      coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq h ρ₁ ρ₂ ∧
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
        (d := d) (coarseCaccioppoliLambdaFactor Q a s)
        (Xi ρ₁ ρ₂) (A1 ρ₁ ρ₂) C +
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound Q s
        (coarseCaccioppoliLambdaFactor Q a s)
        (coarseCaccioppoliLambdaFactor Q a s)
        (coarseCaccioppoliCenteredCutoffCoeffFactorBound Q s
          (Xi ρ₁ ρ₂) (D ρ₁ ρ₂) (A1 ρ₁ ρ₂) (AS ρ₁ ρ₂) C) ≤
      coarseCaccioppoliBoundaryAlphaOfHeight Q a s t C h ρ₁ ρ₂

theorem CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalRawCoefficientBounds.of_coefficientBounds_of_localization
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) (U Xi D A1 AS : ℝ → ℝ → ℝ)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds
        Q a s C uL2Sq k h U Xi D A1 AS)
    (hloc :
      CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization Q a s t C uL2Sq
        k h) :
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalRawCoefficientBounds
      Q a s t C uL2Sq h U Xi D A1 AS := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  rcases hcoeff hρ₁ hlt hρ₂ with ⟨hconst, hcentered⟩
  rcases hloc with ⟨hlocConst, hlocCent⟩
  exact
    ⟨le_trans hconst (hlocConst hρ₁ hlt hρ₂),
      le_trans hcentered (hlocCent hρ₁ hlt hρ₂)⟩

theorem abs_cubeAverage_vecDot_scalar_smul_le_boundaryRawEstimate_of_canonical_factor_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (flux : Vec d → Vec d) (u g : Vec d → ℝ) (ξ : Vec d → Vec d)
    (energy : Vec d → ℝ)
    {Acirc1 AcircS B C U Xi D A1 AS Alpha Bcross : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (huMem : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hgMem : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls Q a s flux energy)
    (hscalar : CoarseCaccioppoliScalarCutoffControls Q s u g ξ energy Acirc1 AcircS B C)
    (hAcirc1_nonneg : 0 ≤ Acirc1) (hAcircS_nonneg : 0 ≤ AcircS)
    (hu : cubeLpNorm Q (2 : ℝ≥0∞) u ≤ U)
    (hξ : cubeLpNorm Q ∞ ξ ≤ Xi)
    (hB : B ≤ D) (hAcirc1 : Acirc1 ≤ A1) (hAcircS : AcircS ≤ AS)
    (hconst :
      coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound Q
            (coarseCaccioppoliLambdaFactor Q a (1 : ℝ))
            (coarseCaccioppoliLambdaFactor Q a (1 : ℝ)) *
          coarseCaccioppoliConstantCutoffSizeFactorBound Q U Xi D ≤
        Bcross)
    (hcentered :
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
          (d := d) (coarseCaccioppoliLambdaFactor Q a s) Xi A1 C +
        coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound Q s
          (coarseCaccioppoliLambdaFactor Q a s)
          (coarseCaccioppoliLambdaFactor Q a s)
          (coarseCaccioppoliCenteredCutoffCoeffFactorBound Q s Xi D A1 AS C) ≤
          Alpha) :
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      Alpha * cubeAverage Q energy +
        Bcross * Real.sqrt (cubeAverage Q energy) := by
  have hscalar_controls := hscalar
  rcases hscalar_controls with
    ⟨hB_nonneg, _, _, hC, _, _, _, _, _⟩
  have henergy_nonneg :
      0 ≤ cubeAverage Q energy :=
    cubeAverage_nonneg_of_nonneg_on (Q := Q) hfluxEnergy.1
  have hU_nonneg : 0 ≤ U := le_trans (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) u) hu
  have hXi_nonneg : 0 ≤ Xi := le_trans (cubeLpNorm_nonneg Q ∞ ξ) hξ
  have hD_nonneg : 0 ≤ D := le_trans hB_nonneg hB
  have hA1_nonneg : 0 ≤ A1 := le_trans hAcirc1_nonneg hAcirc1
  have hAS_nonneg : 0 ≤ AS := le_trans hAcircS_nonneg hAcircS
  have hconstCoeff_nonneg :
      0 ≤ coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound Q
        (coarseCaccioppoliLambdaFactor Q a (1 : ℝ))
        (coarseCaccioppoliLambdaFactor Q a (1 : ℝ)) := by
    exact
      coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound_nonneg Q
        (coarseCaccioppoliLambdaFactor_nonneg Q a (by norm_num : 0 ≤ (1 : ℝ)))
        (coarseCaccioppoliLambdaFactor_nonneg Q a (by norm_num : 0 ≤ (1 : ℝ)))
  have hconstCutoff_nonneg :
      0 ≤ coarseCaccioppoliConstantCutoffSize Q u ξ B := by
    exact coarseCaccioppoliConstantCutoffSize_nonneg Q u ξ hB_nonneg
  have hconstCoeff_le :
      coarseCaccioppoliFluxEnergyExactConstantCoeff Q a ≤
        coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound Q
          (coarseCaccioppoliLambdaFactor Q a (1 : ℝ))
          (coarseCaccioppoliLambdaFactor Q a (1 : ℝ)) := by
    exact
      coarseCaccioppoliFluxEnergyExactConstantCoeff_le_factorBound
        Q a
        (sqrt_coarseBBlockNorm_le_coarseCaccioppoliLambdaFactor
          Q a (by norm_num : 0 < (1 : ℝ)) hfluxEnergy.2.2.2.1)
        (by simp [coarseCaccioppoliLambdaFactor])
  have hconstCutoff_le :
      coarseCaccioppoliConstantCutoffSize Q u ξ B ≤
        coarseCaccioppoliConstantCutoffSizeFactorBound Q U Xi D := by
    exact
      coarseCaccioppoliConstantCutoffSize_le_factorBound
        Q u ξ hU_nonneg hB_nonneg hu hξ hB
  have hconstFactor_le :
      coarseCaccioppoliFluxEnergyExactConstantCoeff Q a *
          coarseCaccioppoliConstantCutoffSize Q u ξ B ≤
        coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound Q
            (coarseCaccioppoliLambdaFactor Q a (1 : ℝ))
            (coarseCaccioppoliLambdaFactor Q a (1 : ℝ)) *
          coarseCaccioppoliConstantCutoffSizeFactorBound Q U Xi D := by
    exact
      mul_le_mul hconstCoeff_le hconstCutoff_le
        hconstCutoff_nonneg hconstCoeff_nonneg
  have hconstRhs :
      coarseCaccioppoliFluxEnergyExactConstantRhs Q a u ξ energy B ≤
        Bcross * Real.sqrt (cubeAverage Q energy) := by
    rw [coarseCaccioppoliFluxEnergyExactConstantRhs_eq_coeff_mul]
    exact mul_le_mul_of_nonneg_right (le_trans hconstFactor_le hconst)
      (Real.sqrt_nonneg _)
  have havgCoeff_le :
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff Q a ξ Acirc1 C ≤
        coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
          (d := d) (coarseCaccioppoliLambdaFactor Q a s) Xi A1 C := by
    exact
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff_le_factorBound
        Q a ξ
        (coarseCaccioppoliLambdaFactor_nonneg Q a hs0.le)
        hXi_nonneg hAcirc1_nonneg hC
        (sqrt_coarseBBlockNorm_le_coarseCaccioppoliLambdaFactor
          Q a hs0 hfluxEnergy.2.2.2.2)
        hξ hAcirc1
  have hBgCentCoeff_nonneg :
      0 ≤ coarseCaccioppoliCenteredCutoffCoeff Q s ξ Acirc1 AcircS B C := by
    exact
      coarseCaccioppoliCenteredCutoffCoeff_nonneg
        Q ξ hs0 hAcirc1_nonneg hAcircS_nonneg hB_nonneg hC
  have hBgCent_le :
      coarseCaccioppoliCenteredCutoffCoeff Q s ξ Acirc1 AcircS B C ≤
        coarseCaccioppoliCenteredCutoffCoeffFactorBound Q s Xi D A1 AS C := by
    exact
      coarseCaccioppoliCenteredCutoffCoeff_le_factorBound
        Q ξ hs0 hAcirc1_nonneg hAcircS_nonneg hXi_nonneg hD_nonneg hC
        hξ hB hAcirc1 hAcircS
  have hbesovCoeff_le :
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff Q a s ξ Acirc1 AcircS B C ≤
        coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound Q s
          (coarseCaccioppoliLambdaFactor Q a s)
          (coarseCaccioppoliLambdaFactor Q a s)
          (coarseCaccioppoliCenteredCutoffCoeffFactorBound Q s Xi D A1 AS C) := by
    exact
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff_le_factorBound
        Q a s ξ
        (coarseCaccioppoliLambdaFactor_nonneg Q a hs0.le)
        (coarseCaccioppoliLambdaFactor_nonneg Q a hs0.le)
        hBgCentCoeff_nonneg
        (sqrt_coarseBBlockNorm_le_coarseCaccioppoliLambdaFactor
          Q a hs0 hfluxEnergy.2.2.2.2)
        (by simp [coarseCaccioppoliLambdaFactor])
        hBgCent_le
  have hcentCoeff_le :
      coarseCaccioppoliFluxEnergyExactCenteredCoeff Q a s ξ Acirc1 AcircS B C ≤ Alpha := by
    rw [coarseCaccioppoliFluxEnergyExactCenteredCoeff_eq_average_add_besov]
    exact le_trans (add_le_add havgCoeff_le hbesovCoeff_le) hcentered
  have hsqrt_sq :
      Real.sqrt (cubeAverage Q energy) * Real.sqrt (cubeAverage Q energy) =
        cubeAverage Q energy := by
    simpa [pow_two] using (Real.sq_sqrt henergy_nonneg)
  have hcentRhs :
      coarseCaccioppoliFluxEnergyExactCenteredRhs Q a s ξ energy Acirc1 AcircS B C ≤
        Alpha * cubeAverage Q energy := by
    rw [coarseCaccioppoliFluxEnergyExactCenteredRhs_eq_coeff_mul_sqrt_sq, hsqrt_sq]
    exact mul_le_mul_of_nonneg_right hcentCoeff_le henergy_nonneg
  calc
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))|
        ≤ coarseCaccioppoliFluxEnergyExactRhs Q a s u ξ energy Acirc1 AcircS B C := by
          exact
            abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_controls
              (Q := Q) (a := a) (s := s) (flux := flux) (u := u) (g := g) (ξ := ξ)
              (energy := energy) (Acirc1 := Acirc1) (AcircS := AcircS) (B := B) (C := C)
              hs0 hs1 hfluxMem huMem hgMem hξLp hfluxEnergy hscalar
    _ =
        coarseCaccioppoliFluxEnergyExactConstantRhs Q a u ξ energy B +
          coarseCaccioppoliFluxEnergyExactCenteredRhs Q a s ξ energy Acirc1 AcircS B C := by
          rw [coarseCaccioppoliFluxEnergyExactRhs_eq_constant_add_centered]
    _ ≤ Bcross * Real.sqrt (cubeAverage Q energy) +
          Alpha * cubeAverage Q energy := by
          exact add_le_add hconstRhs hcentRhs
    _ = Alpha * cubeAverage Q energy +
          Bcross * Real.sqrt (cubeAverage Q energy) := by
          ring

theorem CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalFactorInputs.of_analyticInputs_of_coefficientBounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) (F : ℝ → ℝ)
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B U Xi D A1 AS : ℝ → ℝ → ℝ)
    (hanalytic :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs Q a s C
        k h F flux u g ξ energy Acirc1 AcircS B U Xi D A1 AS)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds
        Q a s C uL2Sq k h U Xi D A1 AS) :
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalFactorInputs Q a s C uL2Sq
      k h F flux u g ξ energy Acirc1 AcircS B U Xi D A1 AS := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  rcases hanalytic hρ₁ hlt hρ₂ with
    ⟨htest, henergyAvg, hfluxMem, huMem, hg, hξLp, hfluxEnergy, hscalar,
      hB_nonneg, hAcirc1_nonneg, hAcircS_nonneg, huBound, hξBound, hB, hAcirc1,
      hAcircS⟩
  rcases hcoeff hρ₁ hlt hρ₂ with ⟨hconst, hcentered⟩
  exact
    ⟨htest, henergyAvg, hfluxMem, huMem, hg, hξLp, hfluxEnergy, hscalar,
      hB_nonneg, hAcirc1_nonneg, hAcircS_nonneg, huBound, hξBound, hB, hAcirc1,
      hAcircS, hconst, hcentered⟩

theorem coarseCaccioppoli_boundary_noteRawEstimate_of_radiusEnergyBridgeCanonicalAnalyticInputs_of_rawCoefficientBounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B U Xi D A1 AS : ℝ → ℝ → ℝ)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hanalytic :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs Q a s C
        (fun _ _ => 0) h F flux u g ξ energy Acirc1 AcircS B U Xi D A1 AS)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalRawCoefficientBounds
        Q a s t C uL2Sq h U Xi D A1 AS) :
    CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq h F := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  rcases hanalytic hρ₁ hlt hρ₂ with
    ⟨htest, henergyAvg, hfluxMem, huMem, hgMem, hξLp, hfluxEnergy, hscalar,
      hB_nonneg, hAcirc1_nonneg, hAcircS_nonneg, hU, hXi, hD, hA1, hAS⟩
  rcases hcoeff hρ₁ hlt hρ₂ with ⟨hconst, hcentered⟩
  refine le_trans htest ?_
  simpa [henergyAvg] using
    (abs_cubeAverage_vecDot_scalar_smul_le_boundaryRawEstimate_of_canonical_factor_bounds
      (Q := Q) (a := a) (s := s)
      (flux := flux ρ₁ ρ₂) (u := u ρ₁ ρ₂) (g := g ρ₁ ρ₂) (ξ := ξ ρ₁ ρ₂)
      (energy := energy ρ₁ ρ₂)
      (Acirc1 := Acirc1 ρ₁ ρ₂) (AcircS := AcircS ρ₁ ρ₂) (B := B ρ₁ ρ₂)
      (C := C) (U := U ρ₁ ρ₂) (Xi := Xi ρ₁ ρ₂)
      (D := D ρ₁ ρ₂) (A1 := A1 ρ₁ ρ₂) (AS := AS ρ₁ ρ₂)
      (Alpha := coarseCaccioppoliBoundaryAlphaOfHeight Q a s t C h ρ₁ ρ₂)
      (Bcross := coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq h ρ₁ ρ₂)
      hs0 hs1 hfluxMem huMem hgMem hξLp hfluxEnergy hscalar
      hAcirc1_nonneg hAcircS_nonneg hU hXi hD hA1 hAS hconst hcentered)

end

end Homogenization
