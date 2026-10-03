/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.CorePositiveFactors

/-! # Coefficient Bounds -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-- Boundary fixed-localized-energy coarse Caccioppoli from canonical raw
coefficient bounds, with the older nonzero-energy/`lambdaSq` positivity split
kept as a compatibility surface. -/
theorem
    coarseCaccioppoli_boundary_qone_of_canonicalHarmonicRawCoefficientBounds
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
    (hrawcoeff :
      CoarseCaccioppoliBoundaryCanonicalHarmonicRawCoefficientBounds Q a s t C uL2Sq w)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy (1 / 3 : ℝ) ≤
      coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq := by
  exact
    coarseCaccioppoli_boundary_qone_of_canonicalHarmonicPositiveFactors_of_canonicalHarmonicRawCoefficientBounds
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (baseEnergy := baseEnergy) (w := w) (i := i)
      hC hs ht hst hu hbase_nonneg hbase_int hinner_energy_le henergyAvg
      hfluxEnergy (hnonzeroFactors.to_positiveFactors Q a w hlambda1) hgrad hprojected
      hrawcoeff hEll hSigmaSum_t

/-- Interior fixed-localized-energy coarse Caccioppoli from canonical raw
coefficient bounds, with the older nonzero-energy/`lambdaSq` positivity split
kept as a compatibility surface. -/
theorem
    coarseCaccioppoli_interior_qone_of_canonicalHarmonicRawCoefficientBounds
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
    (hrawcoeff :
      CoarseCaccioppoliBoundaryCanonicalHarmonicRawCoefficientBounds Q a s t C uL2Sq w)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy (1 / 3 : ℝ) ≤
      coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := by
  exact
    coarseCaccioppoli_interior_qone_of_canonicalHarmonicPositiveFactors_of_canonicalHarmonicRawCoefficientBounds
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (baseEnergy := baseEnergy) (w := w) (i := i)
      hC hs ht hst hu hbase_nonneg hbase_int hinner_energy_le henergyAvg
      hfluxEnergy (hnonzeroFactors.to_positiveFactors Q a w hlambda1) hgrad hprojected
      hrawcoeff hEll hSigmaSum_t

/-- Boundary fixed-localized-energy coarse Caccioppoli with all canonical
radius/cutoff/profile choices installed, using the canonical gradient positive
factor package directly.  This is the same endpoint as the shorter wrapper
below, but it avoids splitting strict positivity into separate nonzero-energy
and `lambdaSq` hypotheses. -/
theorem
    coarseCaccioppoli_boundary_qone_of_canonicalHarmonicPositiveFactors_of_canonicalHarmonicCoefficientBounds
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
    (hpositiveFactors :
      CoarseCaccioppoliBoundaryCanonicalGradientPositiveFactors Q a w)
    (hgrad :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CubeAverageGradientEnergyControl Q a (fun x => (w ρ₁ ρ₂).toH1.grad x)
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hprojected :
      CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareFamily Q a C w i)
    (hcoeff :
      CoarseCaccioppoliBoundaryCanonicalHarmonicCoefficientBounds Q a s t C uL2Sq w)
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
    coarseCaccioppoli_boundary_qone_of_canonicalHarmonicPositiveFactors_of_canonicalHarmonicRawCoefficientBounds
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (baseEnergy := baseEnergy) (w := w) (i := i)
      hC hs ht hst hu hbase_nonneg hbase_int hinner_energy_le henergyAvg
      hfluxEnergy hpositiveFactors hgrad hprojected
      (CoarseCaccioppoliBoundaryCanonicalHarmonicRawCoefficientBounds.of_coefficientBounds_of_multiscaleEllipticity
        Q a s t C uL2Sq w hC hs ht hst hcoeff hEll hData
        (summable_bBlock_geometricWeight_s_of_fluxEnergyControls_family Q a s hfluxEnergy)
        hSigmaSum_t)
      hEll hSigmaSum_t

/-- Interior fixed-localized-energy coarse Caccioppoli with all canonical
radius/cutoff/profile choices installed, using the canonical gradient positive
factor package directly. -/
theorem
    coarseCaccioppoli_interior_qone_of_canonicalHarmonicPositiveFactors_of_canonicalHarmonicCoefficientBounds
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
    (hpositiveFactors :
      CoarseCaccioppoliBoundaryCanonicalGradientPositiveFactors Q a w)
    (hgrad :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CubeAverageGradientEnergyControl Q a (fun x => (w ρ₁ ρ₂).toH1.grad x)
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hprojected :
      CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareFamily Q a C w i)
    (hcoeff :
      CoarseCaccioppoliBoundaryCanonicalHarmonicCoefficientBounds Q a s t C uL2Sq w)
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
    coarseCaccioppoli_interior_qone_of_canonicalHarmonicPositiveFactors_of_canonicalHarmonicRawCoefficientBounds
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (baseEnergy := baseEnergy) (w := w) (i := i)
      hC hs ht hst hu hbase_nonneg hbase_int hinner_energy_le henergyAvg
      hfluxEnergy hpositiveFactors hgrad hprojected
      (CoarseCaccioppoliBoundaryCanonicalHarmonicRawCoefficientBounds.of_coefficientBounds_of_multiscaleEllipticity
        Q a s t C uL2Sq w hC hs ht hst hcoeff hEll hData
        (summable_bBlock_geometricWeight_s_of_fluxEnergyControls_family Q a s hfluxEnergy)
        hSigmaSum_t)
      hEll hSigmaSum_t

/-- Boundary fixed-localized-energy coarse Caccioppoli with all canonical
radius/cutoff/profile choices installed and the remaining coefficient algebra
named as `CoarseCaccioppoliBoundaryCanonicalHarmonicCoefficientBounds`. -/
theorem
    coarseCaccioppoli_boundary_qone_of_canonicalHarmonicCoefficientBounds
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
      CoarseCaccioppoliBoundaryCanonicalHarmonicCoefficientBounds Q a s t C uL2Sq w)
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
    coarseCaccioppoli_boundary_qone_of_canonicalHarmonicPositiveFactors_of_canonicalHarmonicCoefficientBounds
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (baseEnergy := baseEnergy) (w := w) (i := i)
      hC hs ht hst hu hbase_nonneg hbase_int hinner_energy_le henergyAvg
      hfluxEnergy (hnonzeroFactors.to_positiveFactors Q a w hlambda1) hgrad hprojected
      hcoeff hEll hData
      hSigmaSum_t

/-- Interior fixed-localized-energy coarse Caccioppoli with all canonical
radius/cutoff/profile choices installed and the remaining coefficient algebra
named as `CoarseCaccioppoliBoundaryCanonicalHarmonicCoefficientBounds`. -/
theorem
    coarseCaccioppoli_interior_qone_of_canonicalHarmonicCoefficientBounds
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
      CoarseCaccioppoliBoundaryCanonicalHarmonicCoefficientBounds Q a s t C uL2Sq w)
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
    coarseCaccioppoli_interior_qone_of_canonicalHarmonicPositiveFactors_of_canonicalHarmonicCoefficientBounds
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (baseEnergy := baseEnergy) (w := w) (i := i)
      hC hs ht hst hu hbase_nonneg hbase_int hinner_energy_le henergyAvg
      hfluxEnergy (hnonzeroFactors.to_positiveFactors Q a w hlambda1) hgrad hprojected
      hcoeff hEll hData
      hSigmaSum_t

/-- Boundary fixed-localized-energy coarse Caccioppoli with the solution-side
analytic/profile assumptions bundled into
`CoarseCaccioppoliBoundaryCanonicalHarmonicAnalyticInputs`. -/
theorem
    coarseCaccioppoli_boundary_qone_of_canonicalHarmonicAnalyticInputs_of_canonicalHarmonicCoefficientBounds
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (baseEnergy : Vec d → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hAnalytic :
      CoarseCaccioppoliBoundaryCanonicalHarmonicAnalyticInputs Q a s C baseEnergy w i)
    (hlambda1 : 0 < lambdaSq Q (1 : ℝ) (.finite 1) a)
    (hcoeff :
      CoarseCaccioppoliBoundaryCanonicalHarmonicCoefficientBounds Q a s t C uL2Sq w)
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
    coarseCaccioppoli_boundary_qone_of_canonicalHarmonicCoefficientBounds
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (baseEnergy := baseEnergy) (w := w) (i := i)
      hC hs ht hst hu
      hAnalytic.base_nonneg hAnalytic.base_integrable hAnalytic.inner_energy_le
      hAnalytic.energy_average hAnalytic.flux_energy hAnalytic.nonzero_energy_factors
      hlambda1 hAnalytic.gradient_energy hAnalytic.projected_poincare hcoeff hEll hData
      hSigmaSum_t

/-- Interior fixed-localized-energy coarse Caccioppoli with the solution-side
analytic/profile assumptions bundled into
`CoarseCaccioppoliBoundaryCanonicalHarmonicAnalyticInputs`. -/
theorem
    coarseCaccioppoli_interior_qone_of_canonicalHarmonicAnalyticInputs_of_canonicalHarmonicCoefficientBounds
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (baseEnergy : Vec d → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hAnalytic :
      CoarseCaccioppoliBoundaryCanonicalHarmonicAnalyticInputs Q a s C baseEnergy w i)
    (hlambda1 : 0 < lambdaSq Q (1 : ℝ) (.finite 1) a)
    (hcoeff :
      CoarseCaccioppoliBoundaryCanonicalHarmonicCoefficientBounds Q a s t C uL2Sq w)
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
    coarseCaccioppoli_interior_qone_of_canonicalHarmonicCoefficientBounds
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (baseEnergy := baseEnergy) (w := w) (i := i)
      hC hs ht hst hu
      hAnalytic.base_nonneg hAnalytic.base_integrable hAnalytic.inner_energy_le
      hAnalytic.energy_average hAnalytic.flux_energy hAnalytic.nonzero_energy_factors
      hlambda1 hAnalytic.gradient_energy hAnalytic.projected_poincare hcoeff hEll hData
      hSigmaSum_t

/-- Boundary fixed-localized-energy coarse Caccioppoli where the solution-side
flux/gradient controls, descendant deterministic data, and `Sigma*` summability
are derived from closed-cube ellipticity and the origin recovery theorem.

This is not yet the pure open-cube note endpoint, but it removes the main
energy-control bookkeeping hypotheses from the public boundary wrapper under
the currently available coarse-Poincare compatibility hypothesis. -/
theorem
    coarseCaccioppoli_boundary_qone_of_closedCubeHarmonicEnergyControls_of_canonicalHarmonicCoefficientBounds
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (baseEnergy : Vec d → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
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
    (hnonzeroFactors :
      CoarseCaccioppoliBoundaryCanonicalGradientNonzeroEnergyFactors Q a w)
    (hlambda1 : 0 < lambdaSq Q (1 : ℝ) (.finite 1) a)
    (hprojected :
      CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareFamily Q a C w i)
    (hcoeff :
      CoarseCaccioppoliBoundaryCanonicalHarmonicCoefficientBounds Q a s t C uL2Sq w) :
    coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy (1 / 3 : ℝ) ≤
      coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq := by
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
  have hRec :
      OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam) :=
    openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
      (Q := Q) (a := a) hEllCube hOrigin
  have hData : OpenCubeDescendantDeterministicCoarseData Q a :=
    openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec
  have hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_qone_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeOriginEllipticRecoveryExistence
      (Q := Q) (a := a) (s := t) ht hEllCube hOrigin
  have hEllOpen : IsEllipticFieldOn lam Lam (openCubeSet Q) a :=
    hEllCube.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  exact
    coarseCaccioppoli_boundary_qone_of_canonicalHarmonicAnalyticInputs_of_canonicalHarmonicCoefficientBounds
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (baseEnergy := baseEnergy) (w := w) (i := i)
      hC hs ht hst hu
      (CoarseCaccioppoliBoundaryCanonicalHarmonicAnalyticInputs.of_closedCubeHarmonicEnergyControls
        Q a s C baseEnergy w i hs hEllCube hbase_nonneg hbase_int hinner_energy_le
        henergyAvg hnonzeroFactors hprojected)
      hlambda1 hcoeff hEllOpen hData hSigmaSum_t

/-- Interior fixed-localized-energy coarse Caccioppoli with the same
closed-cube compatibility discharge as the boundary wrapper above. -/
theorem
    coarseCaccioppoli_interior_qone_of_closedCubeHarmonicEnergyControls_of_canonicalHarmonicCoefficientBounds
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (baseEnergy : Vec d → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
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
    (hnonzeroFactors :
      CoarseCaccioppoliBoundaryCanonicalGradientNonzeroEnergyFactors Q a w)
    (hlambda1 : 0 < lambdaSq Q (1 : ℝ) (.finite 1) a)
    (hprojected :
      CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareFamily Q a C w i)
    (hcoeff :
      CoarseCaccioppoliBoundaryCanonicalHarmonicCoefficientBounds Q a s t C uL2Sq w) :
    coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy (1 / 3 : ℝ) ≤
      coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := by
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
  have hRec :
      OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam) :=
    openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
      (Q := Q) (a := a) hEllCube hOrigin
  have hData : OpenCubeDescendantDeterministicCoarseData Q a :=
    openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec
  have hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_qone_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeOriginEllipticRecoveryExistence
      (Q := Q) (a := a) (s := t) ht hEllCube hOrigin
  have hEllOpen : IsEllipticFieldOn lam Lam (openCubeSet Q) a :=
    hEllCube.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  exact
    coarseCaccioppoli_interior_qone_of_canonicalHarmonicAnalyticInputs_of_canonicalHarmonicCoefficientBounds
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (baseEnergy := baseEnergy) (w := w) (i := i)
      hC hs ht hst hu
      (CoarseCaccioppoliBoundaryCanonicalHarmonicAnalyticInputs.of_closedCubeHarmonicEnergyControls
        Q a s C baseEnergy w i hs hEllCube hbase_nonneg hbase_int hinner_energy_le
        henergyAvg hnonzeroFactors hprojected)
      hlambda1 hcoeff hEllOpen hData hSigmaSum_t


end

end Homogenization
