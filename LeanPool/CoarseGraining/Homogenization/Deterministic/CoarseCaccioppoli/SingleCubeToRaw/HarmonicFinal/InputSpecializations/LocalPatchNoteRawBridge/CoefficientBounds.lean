/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.InputSpecializations.NoteRawBridge
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.LocalPatchWeakTesting

/-! # Coefficient Bounds -/

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# Local-patch note raw bridge

This sidecar ties the arbitrary-center local-patch descendant summation to the
harmonic weak-testing identity.  It covers the interior-contained local patch
case: the translated cutoff support is required to lie inside the parent open
cube, so the compact-support test function is admissible without a boundary
zero-trace argument.
-/

/-- Split exact-to-parent-raw coefficient comparisons for the arbitrary-center
local patch route.

`Calpha` controls the centered/front branch and may carry the small-`s`
front budget.  `Ccross` controls only the local constant/cross branch, so the
later note-facing constant can stay dimension-only in that branch. -/
def
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeLocalPatchBufferedExactRawCoefficientBoundsSplit
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (center : Vec d) (a : CoeffField d)
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
        CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂ + 1
    let ξ : Vec d → Vec d :=
      scalarCutoffGradientField
        (coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm)
    let B : ℝ :=
      quantitativeCubeCutoffHessianConst d / (((ρm - ρ₁) * (cubeRadius Q / 3)) ^ 2)
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
arbitrary-center local-patch route.  This is the coefficient package needed by
the standard beta-dependent radius iteration. -/
def
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeLocalPatchBufferedExactRawCoefficientBoundsSplitAllRadii
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (center : Vec d) (a : CoeffField d)
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
        CeffAlpha coarseCaccioppoliTriadicGapScale ρ₁ ρ₂ + 1
    let ξ : Vec d → Vec d :=
      scalarCutoffGradientField
        (coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm)
    let B : ℝ := coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁ ρm
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

/-- The all-radii local-patch split coefficient package restricts to the
legacy Chapter-3 radius sequence. -/
theorem
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeLocalPatchBufferedExactRawCoefficientBoundsSplit.of_allRadii
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (center : Vec d) (a : CoeffField d)
    (s t Clocal Calpha Ccross : ℝ)
    (h :
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeLocalPatchBufferedExactRawCoefficientBoundsSplitAllRadii
        Q center a s t Clocal Calpha Ccross) :
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeLocalPatchBufferedExactRawCoefficientBoundsSplit
      Q center a s t Clocal Calpha Ccross := by
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
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeLocalPatchBufferedExactRawCoefficientBoundsSplit,
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeLocalPatchBufferedExactRawCoefficientBoundsSplitAllRadii,
    coarseCaccioppoliLocalPatchCutoffHessianBound]
    using h hρ₁ hlt hρ₂

end

end Homogenization
