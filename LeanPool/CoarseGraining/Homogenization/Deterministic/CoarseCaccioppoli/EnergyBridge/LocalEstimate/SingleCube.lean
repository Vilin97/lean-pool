/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.LocalEstimate.Cutoff

/-! # Single Cube -/

namespace Homogenization

/-!
# Local energy estimate: single-cube note RHS bridge
-/

noncomputable section

open scoped BigOperators ENNReal

/-- Note single-cube estimate obtained from the exact local bridge once the
remaining coefficient-domination obligation has been supplied. -/
theorem abs_cubeAverage_vecDot_scalar_smul_le_singleCubeBoundaryNoteRhs_of_controls
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (flux : Vec d → Vec d) (u g : Vec d → ℝ) (ξ : Vec d → Vec d)
    (energy : Vec d → ℝ)
    {Acirc1 AcircS B C k h uL2Sq : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls Q a s flux energy)
    (hscalar : CoarseCaccioppoliScalarCutoffControls Q s u g ξ energy Acirc1 AcircS B C)
    (hdom :
      CoarseCaccioppoliSingleCubeCoefficientDomination Q a s C k h uL2Sq u ξ energy
        Acirc1 AcircS B) :
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      coarseCaccioppoliSingleCubeBoundaryNoteRhs Q a s C k h uL2Sq
        (cubeAverage Q energy) := by
  exact le_trans
    (abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_controls
      (Q := Q) (a := a) (s := s) (flux := flux) (u := u) (g := g) (ξ := ξ)
      (energy := energy) (Acirc1 := Acirc1) (AcircS := AcircS) (B := B) (C := C)
      hs0 hs1 hfluxMem hu hg hξLp hfluxEnergy hscalar)
    hdom

/-- Note single-cube estimate from the vector projected-Poincare package and a
coefficient-domination proof stated for the effective scalar-facing constant
`(Fintype.card (Fin d) : ℝ) * C`. -/
theorem abs_cubeAverage_vecDot_scalar_smul_le_singleCubeBoundaryNoteRhs_of_vectorControls
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (G ξ : Vec d → Vec d)
    (energy : Vec d → ℝ)
    {Acirc1 AcircS B C k h uL2Sq : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls Q a s flux energy)
    (hvector : CoarseCaccioppoliVectorCutoffControls Q s u G ξ energy Acirc1 AcircS B C)
    (hdom :
      CoarseCaccioppoliSingleCubeCoefficientDomination Q a s
        ((Fintype.card (Fin d) : ℝ) * C) k h uL2Sq u ξ energy Acirc1 AcircS B) :
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      coarseCaccioppoliSingleCubeBoundaryNoteRhs Q a s
        ((Fintype.card (Fin d) : ℝ) * C) k h uL2Sq
        (cubeAverage Q energy) := by
  exact le_trans
    (abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_vectorControls
      (Q := Q) (a := a) (s := s) (flux := flux) (u := u) (G := G) (ξ := ξ)
      (energy := energy) (Acirc1 := Acirc1) (AcircS := AcircS) (B := B) (C := C)
      hs0 hs1 hfluxMem hu hG hξLp hfluxEnergy hvector)
    hdom

/-- Note single-cube estimate on a descendant cube using a parent quantitative
cutoff, after the small-cube coefficient domination has been supplied. -/
theorem abs_cubeAverage_vecDot_scalar_smul_le_singleCubeBoundaryNoteRhs_of_parentQuantitativeCutoff_on_descendant
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    (a : CoeffField d) (s : ℝ) {ρ₁ ρ₂ : ℝ}
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (energy : Vec d → ℝ) (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    {Acirc1 AcircS C k h uL2Sq : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls R a s flux energy)
    (hB :
      0 ≤ quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
    (hAcircS : 0 ≤ AcircS)
    (hBgConst :
      0 ≤
        coarseCaccioppoliConstantCutoffSize R u (scalarCutoffGradientField η)
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2)))
    (hBgCent :
      0 ≤
        coarseCaccioppoliCenteredCutoffSize R s (scalarCutoffGradientField η) Acirc1 AcircS
          (Real.sqrt (cubeAverage R energy))
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C))
    (hC : 0 ≤ C)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate R C (cubeFluctuation R u) G N)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 * Real.sqrt (cubeAverage R energy))
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS * Real.sqrt (cubeAverage R energy))
    (hdom :
      CoarseCaccioppoliSingleCubeCoefficientDomination R a s
        ((Fintype.card (Fin d) : ℝ) * C) k h uL2Sq u (scalarCutoffGradientField η)
        energy Acirc1 AcircS
        (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))) :
    |cubeAverage R (fun x => vecDot (flux x) (u x • scalarCutoffGradientField η x))| ≤
      coarseCaccioppoliSingleCubeBoundaryNoteRhs R a s
        ((Fintype.card (Fin d) : ℝ) * C) k h uL2Sq
        (cubeAverage R energy) := by
  exact le_trans
    (abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_parentQuantitativeCutoff_on_descendant
      (Q := Q) (R := R) (j := j) hR (a := a) (s := s) (flux := flux) (u := u)
      (G := G) (energy := energy) (η := η) (Acirc1 := Acirc1) (AcircS := AcircS)
      (C := C) hs0 hs1 hfluxMem hu hG hfluxEnergy hB hAcircS hBgConst hBgCent
      hC hproj hGcirc1 hGcircS)
    hdom

/-- Note single-cube estimate obtained directly from the factored coefficient
controls.  The nonnegativity of the averaged energy is supplied by the
flux-energy bundle, so callers only need the two scalar coefficient
inequalities. -/
theorem abs_cubeAverage_vecDot_scalar_smul_le_singleCubeBoundaryNoteRhs_of_coefficientControls
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (flux : Vec d → Vec d) (u g : Vec d → ℝ) (ξ : Vec d → Vec d)
    (energy : Vec d → ℝ)
    {Acirc1 AcircS B C k h uL2Sq : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls Q a s flux energy)
    (hscalar : CoarseCaccioppoliScalarCutoffControls Q s u g ξ energy Acirc1 AcircS B C)
    (hcoeff :
      CoarseCaccioppoliSingleCubeCoefficientControls Q a s C k h uL2Sq u ξ
        Acirc1 AcircS B) :
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      coarseCaccioppoliSingleCubeBoundaryNoteRhs Q a s C k h uL2Sq
        (cubeAverage Q energy) := by
  have henergy :
      0 ≤ cubeAverage Q energy :=
    cubeAverage_nonneg_of_nonneg_on (Q := Q) hfluxEnergy.1
  exact
    abs_cubeAverage_vecDot_scalar_smul_le_singleCubeBoundaryNoteRhs_of_controls
      (Q := Q) (a := a) (s := s) (flux := flux) (u := u) (g := g) (ξ := ξ)
      (energy := energy) (Acirc1 := Acirc1) (AcircS := AcircS) (B := B) (C := C)
      (k := k) (h := h) (uL2Sq := uL2Sq)
      hs0 hs1 hfluxMem hu hg hξLp hfluxEnergy hscalar
      (CoarseCaccioppoliSingleCubeCoefficientDomination.of_coefficientControls
        Q a s C k h uL2Sq u ξ energy Acirc1 AcircS B henergy hcoeff)

/-- Note single-cube estimate from the most separated coefficient inputs:
a constant coefficient bound, a constant cutoff-size bound, and termwise
centered average/Besov bounds. -/
theorem abs_cubeAverage_vecDot_scalar_smul_le_singleCubeBoundaryNoteRhs_of_factor_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (flux : Vec d → Vec d) (u g : Vec d → ℝ) (ξ : Vec d → Vec d)
    (energy : Vec d → ℝ)
    {Acirc1 AcircS B C k h uL2Sq A G X Y : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls Q a s flux energy)
    (hscalar : CoarseCaccioppoliScalarCutoffControls Q s u g ξ energy Acirc1 AcircS B C)
    (hA_nonneg : 0 ≤ A)
    (hconstCoeff : coarseCaccioppoliFluxEnergyExactConstantCoeff Q a ≤ A)
    (hconstCutoff : coarseCaccioppoliConstantCutoffSize Q u ξ B ≤ G)
    (hconst :
      A * G ≤ coarseCaccioppoliSingleCubeBoundaryConstantCoeff Q a C k uL2Sq)
    (havg :
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff Q a ξ Acirc1 C ≤ X)
    (hbesov :
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff Q a s ξ Acirc1 AcircS B C ≤ Y)
    (hcentered :
      X + Y ≤ coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C k h) :
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      coarseCaccioppoliSingleCubeBoundaryNoteRhs Q a s C k h uL2Sq
        (cubeAverage Q energy) := by
  exact
    abs_cubeAverage_vecDot_scalar_smul_le_singleCubeBoundaryNoteRhs_of_coefficientControls
      (Q := Q) (a := a) (s := s) (flux := flux) (u := u) (g := g) (ξ := ξ)
      (energy := energy) (Acirc1 := Acirc1) (AcircS := AcircS) (B := B) (C := C)
      (k := k) (h := h) (uL2Sq := uL2Sq)
      hs0 hs1 hfluxMem hu hg hξLp hfluxEnergy hscalar
      (CoarseCaccioppoliSingleCubeCoefficientControls.of_factor_bounds
        Q a s C k h uL2Sq u ξ Acirc1 AcircS hA_nonneg hscalar.1
        hconstCoeff hconstCutoff hconst havg hbesov hcentered)

/-- Note single-cube estimate from canonical coefficient factors and primitive
scalar cutoff bounds.  This is the fixed-cube counterpart of the canonical
radius-energy input in `CoarseCaccioppoliSingleCubeToRaw`. -/
theorem abs_cubeAverage_vecDot_scalar_smul_le_singleCubeBoundaryNoteRhs_of_canonical_factor_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (flux : Vec d → Vec d) (u g : Vec d → ℝ) (ξ : Vec d → Vec d)
    (energy : Vec d → ℝ)
    {Acirc1 AcircS B C k h uL2Sq U Xi D A1 AS : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (huMem : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls Q a s flux energy)
    (hscalar : CoarseCaccioppoliScalarCutoffControls Q s u g ξ energy Acirc1 AcircS B C)
    (hAcirc1_nonneg : 0 ≤ Acirc1)
    (hAcircS_nonneg : 0 ≤ AcircS)
    (hu : cubeLpNorm Q (2 : ℝ≥0∞) u ≤ U)
    (hξ : cubeLpNorm Q ∞ ξ ≤ Xi)
    (hB : B ≤ D) (hAcirc1 : Acirc1 ≤ A1) (hAcircS : AcircS ≤ AS)
    (hconst :
      coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound Q
            (coarseCaccioppoliLambdaFactor Q a (1 : ℝ))
            (coarseCaccioppoliLambdaFactor Q a (1 : ℝ)) *
          coarseCaccioppoliConstantCutoffSizeFactorBound Q U Xi D ≤
        coarseCaccioppoliSingleCubeBoundaryConstantCoeff Q a C k uL2Sq)
    (hcentered :
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
          (d := d) (coarseCaccioppoliLambdaFactor Q a s) Xi A1 C +
        coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound Q s
          (coarseCaccioppoliLambdaFactor Q a s)
          (coarseCaccioppoliLambdaFactor Q a s)
          (coarseCaccioppoliCenteredCutoffCoeffFactorBound Q s Xi D A1 AS C) ≤
          coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C k h) :
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      coarseCaccioppoliSingleCubeBoundaryNoteRhs Q a s C k h uL2Sq
        (cubeAverage Q energy) := by
  exact
    abs_cubeAverage_vecDot_scalar_smul_le_singleCubeBoundaryNoteRhs_of_coefficientControls
      (Q := Q) (a := a) (s := s) (flux := flux) (u := u) (g := g) (ξ := ξ)
      (energy := energy) (Acirc1 := Acirc1) (AcircS := AcircS) (B := B) (C := C)
      (k := k) (h := h) (uL2Sq := uL2Sq)
      hs0 hs1 hfluxMem huMem hg hξLp hfluxEnergy hscalar
      (CoarseCaccioppoliSingleCubeCoefficientControls.of_canonical_factor_bounds
        Q a s C k h uL2Sq u ξ Acirc1 AcircS hs0 hscalar.2.2.2.1
        hfluxEnergy.2.2.2.1 hfluxEnergy.2.2.2.2 hscalar.1 hAcirc1_nonneg
        hAcircS_nonneg hu hξ hB hAcirc1 hAcircS hconst hcentered)

end

end Homogenization
