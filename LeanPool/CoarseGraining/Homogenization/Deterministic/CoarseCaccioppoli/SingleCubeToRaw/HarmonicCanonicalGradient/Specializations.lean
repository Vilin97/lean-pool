/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicCanonicalGradient.Definitions
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicGradientControls
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.LocalizedEnergyProfile
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.TriadicScale
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeBesovPoincare

/-! # Specializations -/

namespace Homogenization

noncomputable section

open scoped ENNReal

/-- Interior canonical harmonic Caccioppoli specialized to a fixed localized
energy radius profile for the centered quantity. -/
theorem
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_canonicalHarmonicL2GradientAcircCoefficientBounds_of_fixedLocalizedEnergyProfile
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (baseEnergy : Vec d → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hagree :
      CoarseCaccioppoliRadiusAgreement F
        (coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy))
    (hbase_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ baseEnergy x)
    (hbase_int :
      MeasureTheory.IntegrableOn baseEnergy (cubeSet Q) MeasureTheory.volume)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hinner_energy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∀ x ∈ scaledClosedCubeSet Q ρ₁,
          baseEnergy x = scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) =
          coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy ρ₂)
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hnonzeroFactors :
      CoarseCaccioppoliBoundaryCanonicalGradientNonzeroEnergyFactors Q a w)
    (hlambda1 : 0 < lambdaSq Q (1 : ℝ) (.finite 1) a)
    (hgrad :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CubeAverageGradientEnergyControl Q a (fun x => (w ρ₁ ρ₂).toH1.grad x)
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hprojected :
      CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareFamily Q a C w i)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        (coarseCaccioppoliCanonicalHarmonicL2Profile Q a w)
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        (coarseCaccioppoliCanonicalGradientAcircOne Q a)
        (coarseCaccioppoliCanonicalGradientAcircOneSub Q a s))
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
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := by
  exact
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_canonicalHarmonicL2GradientAcircCoefficientBounds_of_localizationData_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := k) (F := F)
      (G₀ := coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy)
      (w := w) (i := i)
      hC hs ht hst hu hagree
      (coarseCaccioppoliLocalizedEnergyRadiusProfile_nonneg Q hbase_nonneg)
      (coarseCaccioppoliLocalizedEnergyRadiusProfile_boundedAbove Q hbase_nonneg hbase_int)
      hscale
      (CoarseCaccioppoliLocalizedEnergyProfileLowerControls.of_fixedEnergy_eq_pairEnergy
        Q hbase_int
        (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
          (hfluxEnergy (ρ₁ := ρ₁) (ρ₂ := ρ₂) hρ₁ hlt hρ₂).2.1)
        hinner_energy)
      henergyAvg hfluxEnergy hnonzeroFactors hlambda1 hgrad hprojected hcoeff
      hEll hData hSigmaSum_t

/-- Interior canonical harmonic Caccioppoli with the interior iterated radius
profile specialized directly to the fixed localized energy profile.  This is
the no-public-`hagree` version of the fixed-profile wrapper. -/
theorem
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_canonicalHarmonicL2GradientAcircCoefficientBounds_of_fixedLocalizedEnergyProfile_self
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ)
    (baseEnergy : Vec d → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hbase_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ baseEnergy x)
    (hbase_int :
      MeasureTheory.IntegrableOn baseEnergy (cubeSet Q) MeasureTheory.volume)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hinner_energy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∀ x ∈ scaledClosedCubeSet Q ρ₁,
          baseEnergy x = scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) =
          coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy ρ₂)
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hnonzeroFactors :
      CoarseCaccioppoliBoundaryCanonicalGradientNonzeroEnergyFactors Q a w)
    (hlambda1 : 0 < lambdaSq Q (1 : ℝ) (.finite 1) a)
    (hgrad :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CubeAverageGradientEnergyControl Q a (fun x => (w ρ₁ ρ₂).toH1.grad x)
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hprojected :
      CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareFamily Q a C w i)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        (coarseCaccioppoliCanonicalHarmonicL2Profile Q a w)
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        (coarseCaccioppoliCanonicalGradientAcircOne Q a)
        (coarseCaccioppoliCanonicalGradientAcircOneSub Q a s))
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
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy (1 / 3 : ℝ) ≤
      coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := by
  exact
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_canonicalHarmonicL2GradientAcircCoefficientBounds_of_fixedLocalizedEnergyProfile
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := k)
      (F := coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy)
      (baseEnergy := baseEnergy) (w := w) (i := i)
      hC hs ht hst hu
      (fun {_ρ} _ _ => rfl)
      hbase_nonneg hbase_int hscale hinner_energy henergyAvg hfluxEnergy
      hnonzeroFactors hlambda1 hgrad hprojected hcoeff hEll hData hSigmaSum_t

/-- Boundary fixed-localized-energy canonical harmonic Caccioppoli with the
canonical Chapter 3 triadic gap scale installed. -/
theorem
    coarseCaccioppoli_boundary_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_canonicalHarmonicL2GradientAcircCoefficientBounds_of_fixedLocalizedEnergyProfile_of_canonicalTriadicGapScale
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (baseEnergy : Vec d → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hbase_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ baseEnergy x)
    (hbase_int :
      MeasureTheory.IntegrableOn baseEnergy (cubeSet Q) MeasureTheory.volume)
    (hinner_energy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∀ x ∈ scaledClosedCubeSet Q ρ₁,
          baseEnergy x = scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) =
          coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy ρ₂)
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hnonzeroFactors :
      CoarseCaccioppoliBoundaryCanonicalGradientNonzeroEnergyFactors Q a w)
    (hlambda1 : 0 < lambdaSq Q (1 : ℝ) (.finite 1) a)
    (hgrad :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CubeAverageGradientEnergyControl Q a (fun x => (w ρ₁ ρ₂).toH1.grad x)
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hprojected :
      CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareFamily Q a C w i)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (coarseCaccioppoliTriadicGapScale ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C
          coarseCaccioppoliTriadicGapScale)
        (coarseCaccioppoliCanonicalHarmonicL2Profile Q a w)
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        (coarseCaccioppoliCanonicalGradientAcircOne Q a)
        (coarseCaccioppoliCanonicalGradientAcircOneSub Q a s))
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
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy (1 / 3 : ℝ) ≤
      coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq := by
  exact
    coarseCaccioppoli_boundary_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_canonicalHarmonicL2GradientAcircCoefficientBounds_of_fixedLocalizedEnergyProfile
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := coarseCaccioppoliTriadicGapScale) (baseEnergy := baseEnergy)
      (w := w) (i := i)
      hC hs ht hst hu hbase_nonneg hbase_int
      (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
        coarseCaccioppoliTriadicGapScale_spec hρ₁ hlt hρ₂)
      hinner_energy henergyAvg hfluxEnergy hnonzeroFactors hlambda1 hgrad
      hprojected hcoeff hEll hData hSigmaSum_t

/-- Interior fixed-localized-energy canonical harmonic Caccioppoli with both
the fixed profile and canonical Chapter 3 triadic gap scale installed. -/
theorem
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_canonicalHarmonicL2GradientAcircCoefficientBounds_of_fixedLocalizedEnergyProfile_self_of_canonicalTriadicGapScale
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (baseEnergy : Vec d → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hbase_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ baseEnergy x)
    (hbase_int :
      MeasureTheory.IntegrableOn baseEnergy (cubeSet Q) MeasureTheory.volume)
    (hinner_energy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∀ x ∈ scaledClosedCubeSet Q ρ₁,
          baseEnergy x = scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) =
          coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy ρ₂)
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hnonzeroFactors :
      CoarseCaccioppoliBoundaryCanonicalGradientNonzeroEnergyFactors Q a w)
    (hlambda1 : 0 < lambdaSq Q (1 : ℝ) (.finite 1) a)
    (hgrad :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CubeAverageGradientEnergyControl Q a (fun x => (w ρ₁ ρ₂).toH1.grad x)
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hprojected :
      CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareFamily Q a C w i)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (coarseCaccioppoliTriadicGapScale ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C
          coarseCaccioppoliTriadicGapScale)
        (coarseCaccioppoliCanonicalHarmonicL2Profile Q a w)
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        (coarseCaccioppoliCanonicalGradientAcircOne Q a)
        (coarseCaccioppoliCanonicalGradientAcircOneSub Q a s))
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
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy (1 / 3 : ℝ) ≤
      coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := by
  exact
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_canonicalHarmonicL2GradientAcircCoefficientBounds_of_fixedLocalizedEnergyProfile_self
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := coarseCaccioppoliTriadicGapScale) (baseEnergy := baseEnergy)
      (w := w) (i := i)
      hC hs ht hst hu hbase_nonneg hbase_int
      (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
        coarseCaccioppoliTriadicGapScale_spec hρ₁ hlt hρ₂)
      hinner_energy henergyAvg hfluxEnergy hnonzeroFactors hlambda1 hgrad
      hprojected hcoeff hEll hData hSigmaSum_t

/-- Boundary fixed-localized-energy canonical harmonic Caccioppoli with the
canonical Chapter 3 triadic gap scale installed, requiring only domination of
the fixed localized energy by the pair-dependent energy on each inner cube. -/
theorem
    coarseCaccioppoli_boundary_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_canonicalHarmonicL2GradientAcircCoefficientBounds_of_fixedLocalizedEnergyProfile_le_of_canonicalTriadicGapScale
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (baseEnergy : Vec d → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hbase_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ baseEnergy x)
    (hbase_int :
      MeasureTheory.IntegrableOn baseEnergy (cubeSet Q) MeasureTheory.volume)
    (hinner_energy_le :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∀ x ∈ scaledClosedCubeSet Q ρ₁,
          baseEnergy x ≤ scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) =
          coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy ρ₂)
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hnonzeroFactors :
      CoarseCaccioppoliBoundaryCanonicalGradientNonzeroEnergyFactors Q a w)
    (hlambda1 : 0 < lambdaSq Q (1 : ℝ) (.finite 1) a)
    (hgrad :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CubeAverageGradientEnergyControl Q a (fun x => (w ρ₁ ρ₂).toH1.grad x)
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hprojected :
      CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareFamily Q a C w i)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (coarseCaccioppoliTriadicGapScale ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C
          coarseCaccioppoliTriadicGapScale)
        (coarseCaccioppoliCanonicalHarmonicL2Profile Q a w)
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        (coarseCaccioppoliCanonicalGradientAcircOne Q a)
        (coarseCaccioppoliCanonicalGradientAcircOneSub Q a s))
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
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy (1 / 3 : ℝ) ≤
      coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq := by
  exact
    coarseCaccioppoli_boundary_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_canonicalHarmonicL2GradientAcircCoefficientBounds_of_localizationData_of_localizedExplicitHeightOfScaleChoice
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := coarseCaccioppoliTriadicGapScale)
      (F := coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy)
      (w := w) (i := i)
      hC hs ht hst hu
      (coarseCaccioppoliLocalizedEnergyRadiusProfile_nonneg Q hbase_nonneg)
      (coarseCaccioppoliLocalizedEnergyRadiusProfile_boundedAbove Q hbase_nonneg hbase_int)
      (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
        coarseCaccioppoliTriadicGapScale_spec hρ₁ hlt hρ₂)
      (CoarseCaccioppoliLocalizedEnergyProfileLowerControls.of_fixedEnergy_le_pairEnergy
        Q hbase_int
        (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
          (hfluxEnergy (ρ₁ := ρ₁) (ρ₂ := ρ₂) hρ₁ hlt hρ₂).2.1)
        hinner_energy_le)
      henergyAvg hfluxEnergy hnonzeroFactors hlambda1 hgrad hprojected hcoeff
      hEll hData hSigmaSum_t

/-- Interior fixed-localized-energy canonical harmonic Caccioppoli with the
canonical Chapter 3 triadic gap scale installed, requiring only domination of
the fixed localized energy by the pair-dependent energy on each inner cube. -/
theorem
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_canonicalHarmonicL2GradientAcircCoefficientBounds_of_fixedLocalizedEnergyProfile_self_le_of_canonicalTriadicGapScale
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (baseEnergy : Vec d → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hbase_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ baseEnergy x)
    (hbase_int :
      MeasureTheory.IntegrableOn baseEnergy (cubeSet Q) MeasureTheory.volume)
    (hinner_energy_le :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∀ x ∈ scaledClosedCubeSet Q ρ₁,
          baseEnergy x ≤ scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) =
          coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy ρ₂)
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hnonzeroFactors :
      CoarseCaccioppoliBoundaryCanonicalGradientNonzeroEnergyFactors Q a w)
    (hlambda1 : 0 < lambdaSq Q (1 : ℝ) (.finite 1) a)
    (hgrad :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CubeAverageGradientEnergyControl Q a (fun x => (w ρ₁ ρ₂).toH1.grad x)
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hprojected :
      CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareFamily Q a C w i)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (coarseCaccioppoliTriadicGapScale ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C
          coarseCaccioppoliTriadicGapScale)
        (coarseCaccioppoliCanonicalHarmonicL2Profile Q a w)
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        (coarseCaccioppoliCanonicalGradientAcircOne Q a)
        (coarseCaccioppoliCanonicalGradientAcircOneSub Q a s))
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
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy (1 / 3 : ℝ) ≤
      coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := by
  exact
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_canonicalHarmonicL2GradientAcircCoefficientBounds_of_localizationData_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := coarseCaccioppoliTriadicGapScale)
      (F := coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy)
      (G₀ := coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy)
      (w := w) (i := i)
      hC hs ht hst hu
      (fun {_ρ} _ _ => rfl)
      (coarseCaccioppoliLocalizedEnergyRadiusProfile_nonneg Q hbase_nonneg)
      (coarseCaccioppoliLocalizedEnergyRadiusProfile_boundedAbove Q hbase_nonneg hbase_int)
      (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
        coarseCaccioppoliTriadicGapScale_spec hρ₁ hlt hρ₂)
      (CoarseCaccioppoliLocalizedEnergyProfileLowerControls.of_fixedEnergy_le_pairEnergy
        Q hbase_int
        (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
          (hfluxEnergy (ρ₁ := ρ₁) (ρ₂ := ρ₂) hρ₁ hlt hρ₂).2.1)
        hinner_energy_le)
      henergyAvg hfluxEnergy hnonzeroFactors hlambda1 hgrad hprojected hcoeff
      hEll hData hSigmaSum_t

end

end Homogenization
