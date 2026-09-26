/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.Boundary
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.Interior

/-! # Interior -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-- Interior note-shaped raw estimate from radius-indexed boundary-style
energy bridge inputs, transported across the radius agreement used in the
centering step. -/
theorem coarseCaccioppoli_interior_noteRawEstimate_of_radiusEnergyBridgeInputs_of_radiusAgreement
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) {F G : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq k h G flux u g ξ
        energy Acirc1 AcircS B)
    (hctrl :
      CoarseCaccioppoliBoundarySingleCubeToRawCoefficientControl Q a s t C uL2Sq
        k h G) :
    CoarseCaccioppoliInteriorNoteRawEstimate Q a s t C uL2Sq h F := by
  exact
    coarseCaccioppoli_interior_noteRawEstimate_of_boundary_noteEstimate_of_radiusAgreement
      Q a s t C uL2Sq h hagree
      (coarseCaccioppoli_boundary_noteRawEstimate_of_radiusEnergyBridgeInputs
        Q a s t C uL2Sq k h flux u g ξ energy Acirc1 AcircS B hs0 hs1
        hinputs hctrl)

/-- Interior note raw estimate from radius-indexed energy bridge inputs and
pure coefficient localization, transported across radius agreement. -/
theorem coarseCaccioppoli_interior_noteRawEstimate_of_radiusEnergyBridgeInputs_of_radiusAgreement_of_coefficientLocalization
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) {F G : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G ρ)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq k h G flux u g ξ
        energy Acirc1 AcircS B)
    (hloc :
      CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization Q a s t C uL2Sq
        k h) :
    CoarseCaccioppoliInteriorNoteRawEstimate Q a s t C uL2Sq h F := by
  exact
    coarseCaccioppoli_interior_noteRawEstimate_of_radiusEnergyBridgeInputs_of_radiusAgreement
      Q a s t C uL2Sq k h flux u g ξ energy Acirc1 AcircS B hs0 hs1
      hagree hinputs
      (CoarseCaccioppoliBoundarySingleCubeToRawCoefficientControl.of_localization
        Q a s t C uL2Sq k h G hG_nonneg hloc)

/-- Interior note raw estimate from the primitive scale and ellipticity
localization inputs, transported across radius agreement. -/
theorem coarseCaccioppoli_interior_noteRawEstimate_of_radiusEnergyBridgeInputs_of_scale_of_ellipticity_of_radiusAgreement
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) {F G : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs0 : 0 < s) (hs1 : s < 1)
    (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G ρ)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq k h G flux u g ξ
        energy Acirc1 AcircS B)
    (hscaleLoc : CoarseCaccioppoliBoundarySingleCubeScaleLocalization s t k h)
    (helliptic :
      CoarseCaccioppoliBoundarySingleCubeEllipticityLocalization Q a s t) :
    CoarseCaccioppoliInteriorNoteRawEstimate Q a s t C uL2Sq h F := by
  exact
    coarseCaccioppoli_interior_noteRawEstimate_of_radiusEnergyBridgeInputs_of_radiusAgreement_of_coefficientLocalization
      Q a s t C uL2Sq k h flux u g ξ energy Acirc1 AcircS B hs0 hs1
      hagree hG_nonneg hinputs
      (CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization.of_scale_of_ellipticity
        Q a s t C uL2Sq k h hC hs0 hs1 hscaleLoc helliptic)

/-- Interior note raw estimate from radius-indexed energy bridge inputs using
the localized explicit height and standard multiscale ellipticity data,
transported across radius agreement. -/
theorem coarseCaccioppoli_interior_noteRawEstimate_of_radiusEnergyBridgeInputs_of_multiscaleEllipticity_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F G : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G ρ)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        G flux u g ξ energy Acirc1 AcircS B)
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
    CoarseCaccioppoliInteriorNoteRawEstimate Q a s t C uL2Sq
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k) F := by
  exact
    coarseCaccioppoli_interior_noteRawEstimate_of_radiusEnergyBridgeInputs_of_radiusAgreement_of_coefficientLocalization
      Q a s t C uL2Sq
      (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
      flux u g ξ energy Acirc1 AcircS B hs (by linarith)
      hagree hG_nonneg hinputs
      (CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization.of_triadicGapScaleChoice_of_localizedExplicitHeightOfScaleChoice_of_isEllipticFieldOn_of_isSigmaCoarse
        Q a C uL2Sq k hC hs ht hst hscale hEll hData hBsum_s hSigmaSum_t)

/-- Interior explicit-height pre-recurrence from radius-indexed energy bridge
inputs using the localized explicit height and standard multiscale ellipticity
data, transported across radius agreement. -/
theorem coarseCaccioppoli_interior_explicitHeightPreRecurrence_of_radiusEnergyBridgeInputs_of_multiscaleEllipticity_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F G : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G ρ)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        G flux u g ξ energy Acirc1 AcircS B)
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
    CoarseCaccioppoliInteriorExplicitHeightPreRecurrence Q a s t C uL2Sq F := by
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
  have hraw :
      CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k) F := by
    exact
      coarseCaccioppoli_interior_noteRawEstimate_of_radiusEnergyBridgeInputs_of_multiscaleEllipticity_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
        Q a s t C uL2Sq k flux u g ξ energy Acirc1 AcircS B
        hC hs ht hst hagree hG_nonneg hscale hinputs hEll hData hBsum_s hSigmaSum_t
  unfold CoarseCaccioppoliInteriorExplicitHeightPreRecurrence
  exact
    coarseCaccioppoli_boundary_explicitHeightPreRecurrence_of_noteEstimate_of_absorptionCondition_of_explicitCrossTermBound
      Q a s t C uL2Sq
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
      hC hs ht hst hraw habs
      (coarseCaccioppoli_boundary_noteCrossTermBound_of_localizedExplicitHeightOfScaleChoice
        Q a s t C uL2Sq k hC hs ht hst hu hscale)

/-- Interior raw note estimate from canonical `LambdaSq` factor inputs using
localized explicit height, radius agreement, and standard multiscale
ellipticity data. -/
theorem coarseCaccioppoli_interior_noteRawEstimate_of_radiusEnergyBridgeCanonicalFactorInputs_of_multiscaleEllipticity_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F G : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B U Xi D A1 AS : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G ρ)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalFactorInputs Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        G flux u g ξ energy Acirc1 AcircS B U Xi D A1 AS)
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
    CoarseCaccioppoliInteriorNoteRawEstimate Q a s t C uL2Sq
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k) F := by
  exact
    coarseCaccioppoli_interior_noteRawEstimate_of_radiusEnergyBridgeInputs_of_multiscaleEllipticity_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
      Q a s t C uL2Sq k flux u g ξ energy Acirc1 AcircS B
      hC hs ht hst hagree hG_nonneg hscale
      (CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs.of_canonicalFactorInputs
        Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        G flux u g ξ energy Acirc1 AcircS B U Xi D A1 AS hC hs hinputs)
      hEll hData hBsum_s hSigmaSum_t

/-- Interior explicit-height pre-recurrence from canonical `LambdaSq` factor
inputs using localized explicit height, radius agreement, and standard
multiscale ellipticity data. -/
theorem coarseCaccioppoli_interior_explicitHeightPreRecurrence_of_radiusEnergyBridgeCanonicalFactorInputs_of_multiscaleEllipticity_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F G : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B U Xi D A1 AS : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G ρ)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalFactorInputs Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        G flux u g ξ energy Acirc1 AcircS B U Xi D A1 AS)
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
    CoarseCaccioppoliInteriorExplicitHeightPreRecurrence Q a s t C uL2Sq F := by
  exact
    coarseCaccioppoli_interior_explicitHeightPreRecurrence_of_radiusEnergyBridgeInputs_of_multiscaleEllipticity_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
      Q a s t C uL2Sq k flux u g ξ energy Acirc1 AcircS B
      hC hs ht hst hu hagree hG_nonneg hscale
      (CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs.of_canonicalFactorInputs
        Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        G flux u g ξ energy Acirc1 AcircS B U Xi D A1 AS hC hs hinputs)
      hEll hData hBsum_s hSigmaSum_t

/-- Interior pre-recurrence from the radius-indexed energy bridge inputs after
transporting the raw estimate across the centering radius agreement. -/
theorem coarseCaccioppoli_interior_preRecurrence_of_radiusEnergyBridgeInputs_of_radiusAgreement
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) {F G : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq k h G flux u g ξ
        energy Acirc1 AcircS B)
    (hctrl :
      CoarseCaccioppoliBoundarySingleCubeToRawCoefficientControl Q a s t C uL2Sq
        k h G)
    (habs : CoarseCaccioppoliInteriorNoteAbsorptionCondition Q a s t C h)
    (hcross : CoarseCaccioppoliInteriorNoteCrossTermBound Q a s t C uL2Sq h) :
    CoarseCaccioppoliInteriorPreRecurrence Q a s t C uL2Sq F := by
  exact
    coarseCaccioppoli_interior_preRecurrence_of_noteEstimate_of_absorptionCondition_of_crossTermBound
      Q a s t C uL2Sq h hC hs ht hst
      (coarseCaccioppoli_interior_noteRawEstimate_of_radiusEnergyBridgeInputs_of_radiusAgreement
        Q a s t C uL2Sq k h flux u g ξ energy Acirc1 AcircS B hs (by linarith)
        hagree hinputs hctrl)
      habs hcross

/-- Interior pre-recurrence from radius-indexed energy bridge inputs and pure
coefficient localization, transported across radius agreement. -/
theorem coarseCaccioppoli_interior_preRecurrence_of_radiusEnergyBridgeInputs_of_radiusAgreement_of_coefficientLocalization
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) {F G : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G ρ)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq k h G flux u g ξ
        energy Acirc1 AcircS B)
    (hloc :
      CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization Q a s t C uL2Sq
        k h)
    (habs : CoarseCaccioppoliInteriorNoteAbsorptionCondition Q a s t C h)
    (hcross : CoarseCaccioppoliInteriorNoteCrossTermBound Q a s t C uL2Sq h) :
    CoarseCaccioppoliInteriorPreRecurrence Q a s t C uL2Sq F := by
  exact
    coarseCaccioppoli_interior_preRecurrence_of_radiusEnergyBridgeInputs_of_radiusAgreement
      Q a s t C uL2Sq k h flux u g ξ energy Acirc1 AcircS B hC hs ht hst
      hagree hinputs
      (CoarseCaccioppoliBoundarySingleCubeToRawCoefficientControl.of_localization
        Q a s t C uL2Sq k h G hG_nonneg hloc)
      habs hcross

/-- Interior pre-recurrence from the primitive scale and ellipticity
localization inputs, transported across radius agreement. -/
theorem coarseCaccioppoli_interior_preRecurrence_of_radiusEnergyBridgeInputs_of_scale_of_ellipticity_of_radiusAgreement
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) {F G : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G ρ)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq k h G flux u g ξ
        energy Acirc1 AcircS B)
    (hscaleLoc : CoarseCaccioppoliBoundarySingleCubeScaleLocalization s t k h)
    (helliptic :
      CoarseCaccioppoliBoundarySingleCubeEllipticityLocalization Q a s t)
    (habs : CoarseCaccioppoliInteriorNoteAbsorptionCondition Q a s t C h)
    (hcross : CoarseCaccioppoliInteriorNoteCrossTermBound Q a s t C uL2Sq h) :
    CoarseCaccioppoliInteriorPreRecurrence Q a s t C uL2Sq F := by
  exact
    coarseCaccioppoli_interior_preRecurrence_of_radiusEnergyBridgeInputs_of_radiusAgreement_of_coefficientLocalization
      Q a s t C uL2Sq k h flux u g ξ energy Acirc1 AcircS B hC hs ht hst
      hagree hG_nonneg hinputs
      (CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization.of_scale_of_ellipticity
        Q a s t C uL2Sq k h hC hs (by linarith) hscaleLoc helliptic)
      habs hcross

/-- Interior coarse Caccioppoli from radius-indexed single-cube estimates,
explicit-height choice, coefficient-localization controls, and the radius
agreement that identifies the centered interior quantity with the
boundary-style local quantity. -/
theorem coarseCaccioppoli_interior_qone_of_singleCubeRawEstimate_of_radiusAgreement_of_explicitHeightOfScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k : ℝ → ℝ → ℕ) {F G : ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G ρ)
    (hG_bounded : CoarseCaccioppoliRadiusBoundedAbove G)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hsingle :
      CoarseCaccioppoliBoundarySingleCubeRawEstimate Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k) G)
    (hctrl :
      CoarseCaccioppoliBoundarySingleCubeToRawCoefficientControl Q a s t C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k) G) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := by
  exact
    coarseCaccioppoli_interior_qone_of_boundary_noteEstimate_of_radiusAgreement_of_explicitHeightOfScaleChoice
      Q a s t C uL2Sq k hC hs ht hst hu hagree hG_nonneg hG_bounded hscale
      (coarseCaccioppoli_boundary_noteRawEstimate_of_singleCubeRawEstimate
        Q a s t C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k)
        hsingle hctrl)

/-- Interior coarse Caccioppoli directly from the radius-indexed energy bridge
inputs, explicit-height choice, coefficient-localization controls, and the
radius agreement used for centering. -/
theorem coarseCaccioppoli_interior_qone_of_radiusEnergyBridgeInputs_of_radiusAgreement_of_explicitHeightOfScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k : ℝ → ℝ → ℕ) {F G : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G ρ)
    (hG_bounded : CoarseCaccioppoliRadiusBoundedAbove G)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k)
        G flux u g ξ energy Acirc1 AcircS B)
    (hctrl :
      CoarseCaccioppoliBoundarySingleCubeToRawCoefficientControl Q a s t C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k) G) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := by
  exact
    coarseCaccioppoli_interior_qone_of_singleCubeRawEstimate_of_radiusAgreement_of_explicitHeightOfScaleChoice
      Q a s t C uL2Sq k hC hs ht hst hu hagree hG_nonneg hG_bounded hscale
      (coarseCaccioppoli_boundary_singleCubeRawEstimate_of_radiusEnergyBridgeInputs
        Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k)
        flux u g ξ energy Acirc1 AcircS B hs (by linarith) hinputs)
      hctrl

/-- Interior coarse Caccioppoli from radius-indexed energy bridge inputs and
pure coefficient-localization data, transported across the centering radius
agreement. -/
theorem coarseCaccioppoli_interior_qone_of_radiusEnergyBridgeInputs_of_coefficientLocalization_of_radiusAgreement_of_explicitHeightOfScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k : ℝ → ℝ → ℕ) {F G : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G ρ)
    (hG_bounded : CoarseCaccioppoliRadiusBoundedAbove G)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k)
        G flux u g ξ energy Acirc1 AcircS B)
    (hloc :
      CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization Q a s t C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k)) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := by
  exact
    coarseCaccioppoli_interior_qone_of_radiusEnergyBridgeInputs_of_radiusAgreement_of_explicitHeightOfScaleChoice
      Q a s t C uL2Sq k flux u g ξ energy Acirc1 AcircS B
      hC hs ht hst hu hagree hG_nonneg hG_bounded hscale hinputs
      (CoarseCaccioppoliBoundarySingleCubeToRawCoefficientControl.of_localization
        Q a s t C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k)
        G hG_nonneg hloc)

/-- Interior coarse Caccioppoli from the two primitive localization inputs,
after transporting the boundary-style local quantity across radius agreement.
-/
theorem coarseCaccioppoli_interior_qone_of_radiusEnergyBridgeInputs_of_scale_of_ellipticity_of_radiusAgreement_of_explicitHeightOfScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k : ℝ → ℝ → ℕ) {F G : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G ρ)
    (hG_bounded : CoarseCaccioppoliRadiusBoundedAbove G)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k)
        G flux u g ξ energy Acirc1 AcircS B)
    (hscaleLoc :
      CoarseCaccioppoliBoundarySingleCubeScaleLocalization s t
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k))
    (helliptic :
      CoarseCaccioppoliBoundarySingleCubeEllipticityLocalization Q a s t) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := by
  exact
    coarseCaccioppoli_interior_qone_of_radiusEnergyBridgeInputs_of_coefficientLocalization_of_radiusAgreement_of_explicitHeightOfScaleChoice
      Q a s t C uL2Sq k flux u g ξ energy Acirc1 AcircS B
      hC hs ht hst hu hagree hG_nonneg hG_bounded hscale hinputs
      (CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization.of_scale_of_ellipticity
        Q a s t C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k)
        hC hs (by linarith) hscaleLoc helliptic)

/-- Interior coarse Caccioppoli from radius-indexed energy bridge inputs and
fully composed localization data, transported across radius agreement. -/
theorem coarseCaccioppoli_interior_qone_of_radiusEnergyBridgeInputs_of_height_lower_bounds_of_multiscaleEllipticity_of_radiusAgreement_of_explicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F G : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G ρ)
    (hG_bounded : CoarseCaccioppoliRadiusBoundedAbove G)
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
        G flux u g ξ energy Acirc1 AcircS B)
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
    coarseCaccioppoli_interior_qone_of_radiusEnergyBridgeInputs_of_coefficientLocalization_of_radiusAgreement_of_explicitHeightOfScaleChoice
      Q a s t C uL2Sq k flux u g ξ energy Acirc1 AcircS B
      hC hs ht hst hu hagree hG_nonneg hG_bounded hscale hinputs
      (CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization.of_triadicGapScaleChoice_of_height_lower_bounds_of_isEllipticFieldOn_of_isSigmaCoarse
        Q a C uL2Sq k
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k)
        hC hs ht hst hscale hheight_const hheight_cent hEll hData hBsum_s hSigmaSum_t)

/-- Interior coarse Caccioppoli from radius-indexed energy bridge inputs using
the localized explicit height and standard multiscale ellipticity data. -/
theorem coarseCaccioppoli_interior_qone_of_radiusEnergyBridgeInputs_of_multiscaleEllipticity_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F G : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G ρ)
    (hG_bounded : CoarseCaccioppoliRadiusBoundedAbove G)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        G flux u g ξ energy Acirc1 AcircS B)
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
    coarseCaccioppoli_interior_qone_of_explicitHeightPreRecurrence
      Q a s t C uL2Sq hC hs ht hst hu
      (coarseCaccioppoli_nonneg_of_radiusAgreement hagree hG_nonneg)
      (coarseCaccioppoli_radiusBoundedAbove_of_radiusAgreement hagree hG_bounded)
      (coarseCaccioppoli_interior_explicitHeightPreRecurrence_of_radiusEnergyBridgeInputs_of_multiscaleEllipticity_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
        Q a s t C uL2Sq k flux u g ξ energy Acirc1 AcircS B
        hC hs ht hst hu hagree hG_nonneg hscale hinputs hEll hData hBsum_s hSigmaSum_t)

end

end Homogenization
