/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.CoefficientBounds
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.InputSpecializations.FaithfulDescendant
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.DescendantSummationFullDual
import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.Ellipticity.QOneRoot

/-! # Coefficient Localization -/

namespace Homogenization

noncomputable section

open scoped ENNReal

/-- Split exact-to-parent-raw coefficient comparisons for the buffered
localized-energy route.

The explicit height and absorption coefficient are chosen with `Calpha`, while
the constant/cross branch is charged to `Ccross`.  This is the coefficient
surface needed to keep the public note constant split all the way back to the
small-cube estimates. -/
def
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeBufferedExactRawCoefficientBoundsSplit
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t Clocal Calpha Ccross : ℝ) : Prop :=
  ∀ n : ℕ,
    let ρ₁ : ℝ := coarseCaccioppoliRadiusSequence n
    let ρ₂ : ℝ := coarseCaccioppoliRadiusSequence (n + 1)
    let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
    let CeffLocal : ℝ := (Fintype.card (Fin d) : ℝ) * Clocal
    let CeffAlpha : ℝ := (Fintype.card (Fin d) : ℝ) * Calpha
    let CeffCross : ℝ := (Fintype.card (Fin d) : ℝ) * Ccross
    let hheight : ℝ → ℝ → ℝ :=
      coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t CeffAlpha
        coarseCaccioppoliTriadicGapScale
    let j : ℕ :=
      coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice Q a s t
        CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂
    let ξ : Vec d → Vec d :=
      scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρm)
    let B : ℝ := coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρm
    let Acirc1 : TriadicCube d → ℝ := fun R =>
      coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm
    let AcircS : TriadicCube d → ℝ := fun R =>
      coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρm
    let K : ℝ :=
      coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s CeffCross 1 hheight ρ₁ ρ₂
    let Alpha : ℝ := coarseCaccioppoliBoundaryAlphaOfHeight Q a s t CeffAlpha hheight ρ₁ ρ₂
    (∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
          (B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ) ≤ K) ∧
    (∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactCenteredCoeff R a s ξ (Acirc1 R) (AcircS R) B
          CeffLocal ≤
        Alpha)

/-- All-radii split exact-to-parent-raw coefficient comparisons for the
buffered localized-energy route.  This is the coefficient package needed by
the standard beta-dependent radius iteration. -/
def
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeBufferedExactRawCoefficientBoundsSplitAllRadii
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t Clocal Calpha Ccross : ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
    let CeffLocal : ℝ := (Fintype.card (Fin d) : ℝ) * Clocal
    let CeffAlpha : ℝ := (Fintype.card (Fin d) : ℝ) * Calpha
    let CeffCross : ℝ := (Fintype.card (Fin d) : ℝ) * Ccross
    let hheight : ℝ → ℝ → ℝ :=
      coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t CeffAlpha
        coarseCaccioppoliTriadicGapScale
    let j : ℕ :=
      coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice Q a s t
        CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂
    let ξ : Vec d → Vec d :=
      scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρm)
    let B : ℝ := coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρm
    let Acirc1 : TriadicCube d → ℝ := fun R =>
      coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm
    let AcircS : TriadicCube d → ℝ := fun R =>
      coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρm
    let K : ℝ :=
      coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s CeffCross 1 hheight ρ₁ ρ₂
    let Alpha : ℝ := coarseCaccioppoliBoundaryAlphaOfHeight Q a s t CeffAlpha hheight ρ₁ ρ₂
    (∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
          (B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ) ≤ K) ∧
    (∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactCenteredCoeff R a s ξ (Acirc1 R) (AcircS R) B
          CeffLocal ≤
        Alpha)

/-- The all-radii split coefficient package restricts to the legacy
Chapter-3 radius sequence. -/
theorem
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeBufferedExactRawCoefficientBoundsSplit.of_allRadii
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t Clocal Calpha Ccross : ℝ)
    (h :
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeBufferedExactRawCoefficientBoundsSplitAllRadii
        Q a s t Clocal Calpha Ccross) :
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeBufferedExactRawCoefficientBoundsSplit
      Q a s t Clocal Calpha Ccross := by
  intro n
  have hρ₁ : (1 / 3 : ℝ) ≤ coarseCaccioppoliRadiusSequence n :=
    (coarseCaccioppoliRadiusSequence_mem_Icc n).1
  have hlt :
      coarseCaccioppoliRadiusSequence n <
        coarseCaccioppoliRadiusSequence (n + 1) :=
    coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self n)
  have hρ₂ : coarseCaccioppoliRadiusSequence (n + 1) ≤ 1 :=
    (coarseCaccioppoliRadiusSequence_mem_Icc (n + 1)).2
  simpa [
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeBufferedExactRawCoefficientBoundsSplit,
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeBufferedExactRawCoefficientBoundsSplitAllRadii]
    using h hρ₁ hlt hρ₂


end

end Homogenization
