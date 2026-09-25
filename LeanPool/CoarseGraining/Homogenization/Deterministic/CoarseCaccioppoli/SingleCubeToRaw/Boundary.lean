/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.RadiusInputs
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.Boundary.ExplicitHeight

/-! # Boundary -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-- Radius-indexed energy bridge inputs plus the single-cube-to-raw
coefficient-localization controls produce the note-shaped raw radius estimate.
-/
theorem coarseCaccioppoli_boundary_noteRawEstimate_of_radiusEnergyBridgeInputs
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq k h F flux u g ξ
        energy Acirc1 AcircS B)
    (hctrl :
      CoarseCaccioppoliBoundarySingleCubeToRawCoefficientControl Q a s t C uL2Sq
        k h F) :
    CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq h F := by
  exact
    coarseCaccioppoli_boundary_noteRawEstimate_of_singleCubeRawEstimate
      Q a s t C uL2Sq k h
      (coarseCaccioppoli_boundary_singleCubeRawEstimate_of_radiusEnergyBridgeInputs
        Q a s C uL2Sq k h flux u g ξ energy Acirc1 AcircS B hs0 hs1 hinputs)
      hctrl

/-- Radius-indexed energy bridge inputs produce the note-shaped raw estimate
from pure coefficient-localization data plus nonnegativity of the radius
energy. -/
theorem coarseCaccioppoli_boundary_noteRawEstimate_of_radiusEnergyBridgeInputs_of_coefficientLocalization
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq k h F flux u g ξ
        energy Acirc1 AcircS B)
    (hloc :
      CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization Q a s t C uL2Sq
        k h) :
    CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq h F := by
  exact
    coarseCaccioppoli_boundary_noteRawEstimate_of_radiusEnergyBridgeInputs
      Q a s t C uL2Sq k h flux u g ξ energy Acirc1 AcircS B hs0 hs1 hinputs
      (CoarseCaccioppoliBoundarySingleCubeToRawCoefficientControl.of_localization
        Q a s t C uL2Sq k h F hnonneg hloc)

/-- Raw boundary note estimate from the primitive scale and ellipticity
localization inputs. -/
theorem coarseCaccioppoli_boundary_noteRawEstimate_of_radiusEnergyBridgeInputs_of_scale_of_ellipticity
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs0 : 0 < s) (hs1 : s < 1)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq k h F flux u g ξ
        energy Acirc1 AcircS B)
    (hscaleLoc : CoarseCaccioppoliBoundarySingleCubeScaleLocalization s t k h)
    (helliptic :
      CoarseCaccioppoliBoundarySingleCubeEllipticityLocalization Q a s t) :
    CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq h F := by
  exact
    coarseCaccioppoli_boundary_noteRawEstimate_of_radiusEnergyBridgeInputs_of_coefficientLocalization
      Q a s t C uL2Sq k h flux u g ξ energy Acirc1 AcircS B hs0 hs1 hnonneg hinputs
      (CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization.of_scale_of_ellipticity
        Q a s t C uL2Sq k h hC hs0 hs1 hscaleLoc helliptic)

/-- Raw boundary note estimate from radius-indexed energy bridge inputs using
the localized explicit height and the standard multiscale ellipticity data. -/
theorem coarseCaccioppoli_boundary_noteRawEstimate_of_radiusEnergyBridgeInputs_of_multiscaleEllipticity_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        F flux u g ξ energy Acirc1 AcircS B)
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
    CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k) F := by
  exact
    coarseCaccioppoli_boundary_noteRawEstimate_of_radiusEnergyBridgeInputs_of_coefficientLocalization
      Q a s t C uL2Sq
      (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
      flux u g ξ energy Acirc1 AcircS B hs (by linarith) hnonneg hinputs
      (CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization.of_triadicGapScaleChoice_of_localizedExplicitHeightOfScaleChoice_of_isEllipticFieldOn_of_isSigmaCoarse
        Q a C uL2Sq k hC hs ht hst hscale hEll hData hBsum_s hSigmaSum_t)

/-- Explicit-height boundary pre-recurrence from radius-indexed energy bridge
inputs using the localized explicit height and standard multiscale ellipticity
data. -/
theorem coarseCaccioppoli_boundary_explicitHeightPreRecurrence_of_radiusEnergyBridgeInputs_of_multiscaleEllipticity_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        F flux u g ξ energy Acirc1 AcircS B)
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
    CoarseCaccioppoliBoundaryExplicitHeightPreRecurrence Q a s t C uL2Sq F := by
  have hheight :
      CoarseCaccioppoliBoundaryHeightChoice Q a s t C
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k) :=
    coarseCaccioppoli_boundary_heightChoice_of_localizedExplicitHeightOfScaleChoice
      Q a s t C k hC hs ht hst hscale
  have habs :
      CoarseCaccioppoliBoundaryNoteAbsorptionCondition Q a s t C
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k) :=
    coarseCaccioppoli_boundary_noteAbsorptionCondition_of_heightChoice
      Q a s t C
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
      hC hs ht hst hheight
  exact
    coarseCaccioppoli_boundary_explicitHeightPreRecurrence_of_noteEstimate_of_absorptionCondition_of_explicitCrossTermBound
      Q a s t C uL2Sq
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
      hC hs ht hst
      (coarseCaccioppoli_boundary_noteRawEstimate_of_radiusEnergyBridgeInputs_of_multiscaleEllipticity_of_localizedExplicitHeightOfScaleChoice
        Q a s t C uL2Sq k flux u g ξ energy Acirc1 AcircS B
        hC hs ht hst hnonneg hscale hinputs hEll hData hBsum_s hSigmaSum_t)
      habs
      (coarseCaccioppoli_boundary_noteCrossTermBound_of_localizedExplicitHeightOfScaleChoice
        Q a s t C uL2Sq k hC hs ht hst hu hscale)

/-- Raw boundary note estimate from canonical `LambdaSq` factor inputs using
the localized explicit height and standard multiscale ellipticity data. -/
theorem coarseCaccioppoli_boundary_noteRawEstimate_of_radiusEnergyBridgeCanonicalFactorInputs_of_multiscaleEllipticity_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B U Xi D A1 AS : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalFactorInputs Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        F flux u g ξ energy Acirc1 AcircS B U Xi D A1 AS)
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
    CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k) F := by
  exact
    coarseCaccioppoli_boundary_noteRawEstimate_of_radiusEnergyBridgeInputs_of_multiscaleEllipticity_of_localizedExplicitHeightOfScaleChoice
      Q a s t C uL2Sq k flux u g ξ energy Acirc1 AcircS B
      hC hs ht hst hnonneg hscale
      (CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs.of_canonicalFactorInputs
        Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        F flux u g ξ energy Acirc1 AcircS B U Xi D A1 AS hC hs hinputs)
      hEll hData hBsum_s hSigmaSum_t

/-- Boundary explicit-height pre-recurrence from canonical `LambdaSq` factor
inputs using localized explicit height and standard multiscale ellipticity data.
-/
theorem coarseCaccioppoli_boundary_explicitHeightPreRecurrence_of_radiusEnergyBridgeCanonicalFactorInputs_of_multiscaleEllipticity_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B U Xi D A1 AS : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalFactorInputs Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        F flux u g ξ energy Acirc1 AcircS B U Xi D A1 AS)
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
    CoarseCaccioppoliBoundaryExplicitHeightPreRecurrence Q a s t C uL2Sq F := by
  exact
    coarseCaccioppoli_boundary_explicitHeightPreRecurrence_of_radiusEnergyBridgeInputs_of_multiscaleEllipticity_of_localizedExplicitHeightOfScaleChoice
      Q a s t C uL2Sq k flux u g ξ energy Acirc1 AcircS B
      hC hs ht hst hu hnonneg hscale
      (CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs.of_canonicalFactorInputs
        Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        F flux u g ξ energy Acirc1 AcircS B U Xi D A1 AS hC hs hinputs)
      hEll hData hBsum_s hSigmaSum_t

/-- The same radius-indexed energy bridge inputs also feed the absorbed
pre-recurrence layer, once the note-specific absorption and cross-term
bookkeeping are available. -/
theorem coarseCaccioppoli_boundary_preRecurrence_of_radiusEnergyBridgeInputs
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq k h F flux u g ξ
        energy Acirc1 AcircS B)
    (hctrl :
      CoarseCaccioppoliBoundarySingleCubeToRawCoefficientControl Q a s t C uL2Sq
        k h F)
    (habs : CoarseCaccioppoliBoundaryNoteAbsorptionCondition Q a s t C h)
    (hcross : CoarseCaccioppoliBoundaryNoteCrossTermBound Q a s t C uL2Sq h) :
    CoarseCaccioppoliBoundaryPreRecurrence Q a s t C uL2Sq F := by
  exact
    coarseCaccioppoli_boundary_preRecurrence_of_noteEstimate_of_absorptionCondition_of_crossTermBound
      Q a s t C uL2Sq h hC hs ht hst
      (coarseCaccioppoli_boundary_noteRawEstimate_of_radiusEnergyBridgeInputs
        Q a s t C uL2Sq k h flux u g ξ energy Acirc1 AcircS B hs (by linarith)
        hinputs hctrl)
      habs hcross

/-- Boundary pre-recurrence from radius-indexed energy bridge inputs and pure
coefficient localization. -/
theorem coarseCaccioppoli_boundary_preRecurrence_of_radiusEnergyBridgeInputs_of_coefficientLocalization
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq k h F flux u g ξ
        energy Acirc1 AcircS B)
    (hloc :
      CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization Q a s t C uL2Sq
        k h)
    (habs : CoarseCaccioppoliBoundaryNoteAbsorptionCondition Q a s t C h)
    (hcross : CoarseCaccioppoliBoundaryNoteCrossTermBound Q a s t C uL2Sq h) :
    CoarseCaccioppoliBoundaryPreRecurrence Q a s t C uL2Sq F := by
  exact
    coarseCaccioppoli_boundary_preRecurrence_of_radiusEnergyBridgeInputs
      Q a s t C uL2Sq k h flux u g ξ energy Acirc1 AcircS B hC hs ht hst hinputs
      (CoarseCaccioppoliBoundarySingleCubeToRawCoefficientControl.of_localization
        Q a s t C uL2Sq k h F hnonneg hloc)
      habs hcross

/-- Boundary pre-recurrence from the primitive scale and ellipticity
localization inputs. -/
theorem coarseCaccioppoli_boundary_preRecurrence_of_radiusEnergyBridgeInputs_of_scale_of_ellipticity
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq k h F flux u g ξ
        energy Acirc1 AcircS B)
    (hscaleLoc : CoarseCaccioppoliBoundarySingleCubeScaleLocalization s t k h)
    (helliptic :
      CoarseCaccioppoliBoundarySingleCubeEllipticityLocalization Q a s t)
    (habs : CoarseCaccioppoliBoundaryNoteAbsorptionCondition Q a s t C h)
    (hcross : CoarseCaccioppoliBoundaryNoteCrossTermBound Q a s t C uL2Sq h) :
    CoarseCaccioppoliBoundaryPreRecurrence Q a s t C uL2Sq F := by
  exact
    coarseCaccioppoli_boundary_preRecurrence_of_radiusEnergyBridgeInputs_of_coefficientLocalization
      Q a s t C uL2Sq k h flux u g ξ energy Acirc1 AcircS B hC hs ht hst
      hnonneg hinputs
      (CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization.of_scale_of_ellipticity
        Q a s t C uL2Sq k h hC hs (by linarith) hscaleLoc helliptic)
      habs hcross

/-- Boundary coarse Caccioppoli from radius-indexed single-cube estimates,
explicit-height choice, and the single-cube-to-raw coefficient-localization
controls. -/
theorem coarseCaccioppoli_boundary_qone_of_singleCubeRawEstimate_of_explicitHeightOfScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hsingle :
      CoarseCaccioppoliBoundarySingleCubeRawEstimate Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k) F)
    (hctrl :
      CoarseCaccioppoliBoundarySingleCubeToRawCoefficientControl Q a s t C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k) F) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq := by
  exact
    coarseCaccioppoli_boundary_qone_of_noteEstimate_of_explicitHeightOfScaleChoice
      Q a s t C uL2Sq k hC hs ht hst hu hnonneg hbounded hscale
      (coarseCaccioppoli_boundary_noteRawEstimate_of_singleCubeRawEstimate
        Q a s t C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k)
        hsingle hctrl)

/-- Boundary coarse Caccioppoli directly from the radius-indexed energy bridge
inputs, explicit-height choice, and the single-cube-to-raw
coefficient-localization controls. -/
theorem coarseCaccioppoli_boundary_qone_of_radiusEnergyBridgeInputs_of_explicitHeightOfScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k)
        F flux u g ξ energy Acirc1 AcircS B)
    (hctrl :
      CoarseCaccioppoliBoundarySingleCubeToRawCoefficientControl Q a s t C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k) F) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq := by
  exact
    coarseCaccioppoli_boundary_qone_of_singleCubeRawEstimate_of_explicitHeightOfScaleChoice
      Q a s t C uL2Sq k hC hs ht hst hu hnonneg hbounded hscale
      (coarseCaccioppoli_boundary_singleCubeRawEstimate_of_radiusEnergyBridgeInputs
        Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k)
        flux u g ξ energy Acirc1 AcircS B hs (by linarith) hinputs)
      hctrl

/-- Boundary coarse Caccioppoli from radius-indexed energy bridge inputs and
pure coefficient-localization data.  This is the same as
`coarseCaccioppoli_boundary_qone_of_radiusEnergyBridgeInputs_of_explicitHeightOfScaleChoice`,
but it assembles the mixed single-cube-to-raw coefficient-control bundle from
the already-available nonnegativity hypothesis. -/
theorem coarseCaccioppoli_boundary_qone_of_radiusEnergyBridgeInputs_of_coefficientLocalization_of_explicitHeightOfScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k)
        F flux u g ξ energy Acirc1 AcircS B)
    (hloc :
      CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization Q a s t C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k)) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq := by
  exact
    coarseCaccioppoli_boundary_qone_of_radiusEnergyBridgeInputs_of_explicitHeightOfScaleChoice
      Q a s t C uL2Sq k flux u g ξ energy Acirc1 AcircS B
      hC hs ht hst hu hnonneg hbounded hscale hinputs
      (CoarseCaccioppoliBoundarySingleCubeToRawCoefficientControl.of_localization
        Q a s t C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k)
        F hnonneg hloc)

/-- Boundary coarse Caccioppoli from the two primitive localization inputs:
the scale-only radius inequality and the ellipticity-only comparison. -/
theorem coarseCaccioppoli_boundary_qone_of_radiusEnergyBridgeInputs_of_scale_of_ellipticity_of_explicitHeightOfScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k)
        F flux u g ξ energy Acirc1 AcircS B)
    (hscaleLoc :
      CoarseCaccioppoliBoundarySingleCubeScaleLocalization s t
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k))
    (helliptic :
      CoarseCaccioppoliBoundarySingleCubeEllipticityLocalization Q a s t) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq := by
  exact
    coarseCaccioppoli_boundary_qone_of_radiusEnergyBridgeInputs_of_coefficientLocalization_of_explicitHeightOfScaleChoice
      Q a s t C uL2Sq k flux u g ξ energy Acirc1 AcircS B
      hC hs ht hst hu hnonneg hbounded hscale hinputs
      (CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization.of_scale_of_ellipticity
        Q a s t C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k)
        hC hs (by linarith) hscaleLoc helliptic)

/-- Boundary coarse Caccioppoli from radius-indexed energy bridge inputs and
fully composed localization data: triadic gap scale choice, concrete lower
bounds on the explicit height, and the standard multiscale ellipticity data. -/
theorem coarseCaccioppoli_boundary_qone_of_radiusEnergyBridgeInputs_of_height_lower_bounds_of_multiscaleEllipticity_of_explicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hheight_const :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        (4 : ℝ) / s ≤
          coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k ρ₁ ρ₂)
    (hheight_cent :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        (4 : ℝ) / (s + t) ≤
          coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k ρ₁ ρ₂)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k)
        F flux u g ξ energy Acirc1 AcircS B)
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
    coarseCaccioppoli_boundary_qone_of_radiusEnergyBridgeInputs_of_coefficientLocalization_of_explicitHeightOfScaleChoice
      Q a s t C uL2Sq k flux u g ξ energy Acirc1 AcircS B
      hC hs ht hst hu hnonneg hbounded hscale hinputs
      (CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization.of_triadicGapScaleChoice_of_height_lower_bounds_of_isEllipticFieldOn_of_isSigmaCoarse
        Q a C uL2Sq k
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k)
        hC hs ht hst hscale hheight_const hheight_cent hEll hData hBsum_s hSigmaSum_t)

/-- Boundary coarse Caccioppoli from radius-indexed energy bridge inputs using
the localized explicit height.  The localized height supplies the scale-side
lower bounds internally, so callers only provide the triadic gap choice and the
standard multiscale ellipticity data. -/
theorem coarseCaccioppoli_boundary_qone_of_radiusEnergyBridgeInputs_of_multiscaleEllipticity_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        F flux u g ξ energy Acirc1 AcircS B)
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
    coarseCaccioppoli_boundary_qone_of_explicitHeightPreRecurrence
      Q a s t C uL2Sq hC hs ht hst hu hnonneg hbounded
      (coarseCaccioppoli_boundary_explicitHeightPreRecurrence_of_radiusEnergyBridgeInputs_of_multiscaleEllipticity_of_localizedExplicitHeightOfScaleChoice
        Q a s t C uL2Sq k flux u g ξ energy Acirc1 AcircS B
        hC hs ht hst hu hnonneg hscale hinputs hEll hData hBsum_s hSigmaSum_t)


end

end Homogenization
