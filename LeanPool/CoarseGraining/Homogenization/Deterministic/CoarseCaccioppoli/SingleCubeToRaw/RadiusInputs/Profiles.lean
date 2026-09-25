/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.Localization
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.RadiusInputs.Setup
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.LocalEstimate.SingleCube

/-! # Profiles -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-- Single-pair raw boundary estimate from the vector projected-Poincare
cutoff package and canonical coefficient factor bounds.  The raw coefficients
are evaluated at the effective scalar-facing constant
`(Fintype.card (Fin d) : ℝ) * C`. -/
theorem abs_cubeAverage_vecDot_scalar_smul_le_boundaryRawEstimate_of_canonical_vector_factor_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (G ξ : Vec d → Vec d)
    (energy : Vec d → ℝ)
    {Acirc1 AcircS B C U Xi D A1 AS Alpha Bcross : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (huMem : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hGMem : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls Q a s flux energy)
    (hvector : CoarseCaccioppoliVectorCutoffControls Q s u G ξ energy Acirc1 AcircS B C)
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
          (d := d) (coarseCaccioppoliLambdaFactor Q a s) Xi A1
          ((Fintype.card (Fin d) : ℝ) * C) +
        coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound Q s
          (coarseCaccioppoliLambdaFactor Q a s)
          (coarseCaccioppoliLambdaFactor Q a s)
          (coarseCaccioppoliCenteredCutoffCoeffFactorBound Q s Xi D A1 AS
            ((Fintype.card (Fin d) : ℝ) * C)) ≤
          Alpha) :
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      Alpha * cubeAverage Q energy +
        Bcross * Real.sqrt (cubeAverage Q energy) := by
  have hvector_controls := hvector
  rcases hvector with
    ⟨hB_nonneg, _, _, _, hC, _, _, _, _, _⟩
  let Ceff : ℝ := (Fintype.card (Fin d) : ℝ) * C
  have hCeff_nonneg : 0 ≤ Ceff := by
    have hcard_nonneg : 0 ≤ (Fintype.card (Fin d) : ℝ) := by
      exact_mod_cast (Nat.zero_le (Fintype.card (Fin d)))
    exact mul_nonneg hcard_nonneg hC
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
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff Q a ξ Acirc1 Ceff ≤
        coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
          (d := d) (coarseCaccioppoliLambdaFactor Q a s) Xi A1 Ceff := by
    exact
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff_le_factorBound
        Q a ξ
        (coarseCaccioppoliLambdaFactor_nonneg Q a hs0.le)
        hXi_nonneg hAcirc1_nonneg hCeff_nonneg
        (sqrt_coarseBBlockNorm_le_coarseCaccioppoliLambdaFactor
          Q a hs0 hfluxEnergy.2.2.2.2)
        hξ hAcirc1
  have hBgCentCoeff_nonneg :
      0 ≤ coarseCaccioppoliCenteredCutoffCoeff Q s ξ Acirc1 AcircS B Ceff := by
    exact
      coarseCaccioppoliCenteredCutoffCoeff_nonneg
        Q ξ hs0 hAcirc1_nonneg hAcircS_nonneg hB_nonneg hCeff_nonneg
  have hBgCent_le :
      coarseCaccioppoliCenteredCutoffCoeff Q s ξ Acirc1 AcircS B Ceff ≤
        coarseCaccioppoliCenteredCutoffCoeffFactorBound Q s Xi D A1 AS Ceff := by
    exact
      coarseCaccioppoliCenteredCutoffCoeff_le_factorBound
        Q ξ hs0 hAcirc1_nonneg hAcircS_nonneg hXi_nonneg hD_nonneg hCeff_nonneg
        hξ hB hAcirc1 hAcircS
  have hbesovCoeff_le :
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff Q a s ξ Acirc1 AcircS B Ceff ≤
        coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound Q s
          (coarseCaccioppoliLambdaFactor Q a s)
          (coarseCaccioppoliLambdaFactor Q a s)
          (coarseCaccioppoliCenteredCutoffCoeffFactorBound Q s Xi D A1 AS Ceff) := by
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
      coarseCaccioppoliFluxEnergyExactCenteredCoeff Q a s ξ Acirc1 AcircS B Ceff ≤
        Alpha := by
    rw [coarseCaccioppoliFluxEnergyExactCenteredCoeff_eq_average_add_besov]
    exact le_trans (add_le_add havgCoeff_le hbesovCoeff_le) hcentered
  have hsqrt_sq :
      Real.sqrt (cubeAverage Q energy) * Real.sqrt (cubeAverage Q energy) =
        cubeAverage Q energy := by
    simpa [pow_two] using (Real.sq_sqrt henergy_nonneg)
  have hcentRhs :
      coarseCaccioppoliFluxEnergyExactCenteredRhs Q a s ξ energy Acirc1 AcircS B Ceff ≤
        Alpha * cubeAverage Q energy := by
    rw [coarseCaccioppoliFluxEnergyExactCenteredRhs_eq_coeff_mul_sqrt_sq, hsqrt_sq]
    exact mul_le_mul_of_nonneg_right hcentCoeff_le henergy_nonneg
  calc
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))|
        ≤ coarseCaccioppoliFluxEnergyExactRhs Q a s u ξ energy Acirc1 AcircS B Ceff := by
          simpa [Ceff] using
            abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_vectorControls
              (Q := Q) (a := a) (s := s) (flux := flux) (u := u) (G := G) (ξ := ξ)
              (energy := energy) (Acirc1 := Acirc1) (AcircS := AcircS) (B := B)
              (C := C) hs0 hs1 hfluxMem huMem hGMem hξLp hfluxEnergy hvector_controls
    _ =
        coarseCaccioppoliFluxEnergyExactConstantRhs Q a u ξ energy B +
          coarseCaccioppoliFluxEnergyExactCenteredRhs Q a s ξ energy Acirc1 AcircS B Ceff := by
          rw [coarseCaccioppoliFluxEnergyExactRhs_eq_constant_add_centered]
    _ ≤ Bcross * Real.sqrt (cubeAverage Q energy) +
          Alpha * cubeAverage Q energy := by
          exact add_le_add hconstRhs hcentRhs
    _ = Alpha * cubeAverage Q energy +
          Bcross * Real.sqrt (cubeAverage Q energy) := by
          ring

/-- Vector-Poincare raw boundary estimate from the radius-indexed analytic
package and raw coefficient bounds stated with the effective scalar-facing
constant `(Fintype.card (Fin d) : ℝ) * C`. -/
theorem
    coarseCaccioppoli_boundary_noteRawEstimate_of_radiusEnergyBridgeCanonicalVectorAnalyticInputs_of_rawCoefficientBounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u : ℝ → ℝ → Vec d → ℝ)
    (G : ℝ → ℝ → Vec d → Vec d)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B U Xi D A1 AS : ℝ → ℝ → ℝ)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hanalytic :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalVectorAnalyticInputs Q a s C
        (fun _ _ => 0) h F flux u G ξ energy Acirc1 AcircS B U Xi D A1 AS)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalRawCoefficientBounds
        Q a s t ((Fintype.card (Fin d) : ℝ) * C) uL2Sq h U Xi D A1 AS) :
    CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t ((Fintype.card (Fin d) : ℝ) * C)
      uL2Sq h F := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  rcases hanalytic hρ₁ hlt hρ₂ with
    ⟨htest, henergyAvg, hfluxMem, huMem, hGMem, hξLp, hfluxEnergy, hvector,
      hB_nonneg, hAcirc1_nonneg, hAcircS_nonneg, hU, hXi, hD, hA1, hAS⟩
  rcases hcoeff hρ₁ hlt hρ₂ with ⟨hconst, hcentered⟩
  refine le_trans htest ?_
  simpa [henergyAvg] using
    (abs_cubeAverage_vecDot_scalar_smul_le_boundaryRawEstimate_of_canonical_vector_factor_bounds
      (Q := Q) (a := a) (s := s)
      (flux := flux ρ₁ ρ₂) (u := u ρ₁ ρ₂) (G := G ρ₁ ρ₂) (ξ := ξ ρ₁ ρ₂)
      (energy := energy ρ₁ ρ₂)
      (Acirc1 := Acirc1 ρ₁ ρ₂) (AcircS := AcircS ρ₁ ρ₂) (B := B ρ₁ ρ₂)
      (C := C) (U := U ρ₁ ρ₂) (Xi := Xi ρ₁ ρ₂)
      (D := D ρ₁ ρ₂) (A1 := A1 ρ₁ ρ₂) (AS := AS ρ₁ ρ₂)
      (Alpha :=
        coarseCaccioppoliBoundaryAlphaOfHeight Q a s t
          ((Fintype.card (Fin d) : ℝ) * C) h ρ₁ ρ₂)
      (Bcross :=
        coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s
          ((Fintype.card (Fin d) : ℝ) * C) uL2Sq h ρ₁ ρ₂)
      hs0 hs1 hfluxMem huMem hGMem hξLp hfluxEnergy hvector
      hAcirc1_nonneg hAcircS_nonneg hU hXi hD hA1 hAS hconst hcentered)

/-- Vector-Poincare single-cube estimate from the radius-indexed analytic
package and the note-shaped single-cube coefficient bounds.  The local vector
Poincare constant is `C`; the scalar-facing single-cube RHS uses the effective
constant `(Fintype.card (Fin d) : ℝ) * C`. -/
theorem
    coarseCaccioppoli_boundary_singleCubeRawEstimate_of_radiusEnergyBridgeCanonicalVectorAnalyticInputs_of_coefficientBounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u : ℝ → ℝ → Vec d → ℝ)
    (G : ℝ → ℝ → Vec d → Vec d)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B U Xi D A1 AS : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs0 : 0 < s) (hs1 : s < 1)
    (hanalytic :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalVectorAnalyticInputs Q a s C
        k h F flux u G ξ energy Acirc1 AcircS B U Xi D A1 AS)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds
        Q a s ((Fintype.card (Fin d) : ℝ) * C) uL2Sq k h U Xi D A1 AS) :
    CoarseCaccioppoliBoundarySingleCubeRawEstimate Q a s
      ((Fintype.card (Fin d) : ℝ) * C) uL2Sq k h F := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  rcases hanalytic hρ₁ hlt hρ₂ with
    ⟨htest, henergyAvg, hfluxMem, huMem, hGMem, hξLp, hfluxEnergy, hvector,
      hB_nonneg, hAcirc1_nonneg, hAcircS_nonneg, hU, hXi, hD, hA1, hAS⟩
  rcases hcoeff hρ₁ hlt hρ₂ with ⟨hconst, hcentered⟩
  let Ceff : ℝ := (Fintype.card (Fin d) : ℝ) * C
  have hCeff_nonneg : 0 ≤ Ceff := by
    exact mul_nonneg (by exact_mod_cast Nat.zero_le (Fintype.card (Fin d))) hC
  have hcontrols :
      CoarseCaccioppoliSingleCubeCoefficientControls Q a s Ceff
        (k ρ₁ ρ₂) (h ρ₁ ρ₂) uL2Sq
        (u ρ₁ ρ₂) (ξ ρ₁ ρ₂) (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
        (B ρ₁ ρ₂) := by
    exact
      CoarseCaccioppoliSingleCubeCoefficientControls.of_canonical_factor_bounds
        Q a s Ceff (k ρ₁ ρ₂) (h ρ₁ ρ₂) uL2Sq
        (u ρ₁ ρ₂) (ξ ρ₁ ρ₂) (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
        hs0 hCeff_nonneg hfluxEnergy.2.2.2.1 hfluxEnergy.2.2.2.2
        hB_nonneg hAcirc1_nonneg hAcircS_nonneg hU hXi hD hA1 hAS
        (by simpa [Ceff] using hconst)
        (by simpa [Ceff] using hcentered)
  have henergy_nonneg :
      0 ≤ cubeAverage Q (energy ρ₁ ρ₂) :=
    cubeAverage_nonneg_of_nonneg_on (Q := Q) hfluxEnergy.1
  have hdom :
      CoarseCaccioppoliSingleCubeCoefficientDomination Q a s Ceff
        (k ρ₁ ρ₂) (h ρ₁ ρ₂) uL2Sq
        (u ρ₁ ρ₂) (ξ ρ₁ ρ₂) (energy ρ₁ ρ₂)
        (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂) (B ρ₁ ρ₂) :=
    CoarseCaccioppoliSingleCubeCoefficientDomination.of_coefficientControls
      Q a s Ceff (k ρ₁ ρ₂) (h ρ₁ ρ₂) uL2Sq
      (u ρ₁ ρ₂) (ξ ρ₁ ρ₂) (energy ρ₁ ρ₂)
      (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂) (B ρ₁ ρ₂)
      henergy_nonneg hcontrols
  have hsingle :
      |cubeAverage Q
          (fun x => vecDot (flux ρ₁ ρ₂ x) ((u ρ₁ ρ₂ x) • ξ ρ₁ ρ₂ x))| ≤
        coarseCaccioppoliSingleCubeBoundaryNoteRhs Q a s Ceff
          (k ρ₁ ρ₂) (h ρ₁ ρ₂) uL2Sq
          (cubeAverage Q (energy ρ₁ ρ₂)) :=
    abs_cubeAverage_vecDot_scalar_smul_le_singleCubeBoundaryNoteRhs_of_vectorControls
      (Q := Q) (a := a) (s := s)
      (flux := flux ρ₁ ρ₂) (u := u ρ₁ ρ₂) (G := G ρ₁ ρ₂) (ξ := ξ ρ₁ ρ₂)
      (energy := energy ρ₁ ρ₂)
      (Acirc1 := Acirc1 ρ₁ ρ₂) (AcircS := AcircS ρ₁ ρ₂) (B := B ρ₁ ρ₂)
      (C := C) (k := k ρ₁ ρ₂) (h := h ρ₁ ρ₂) (uL2Sq := uL2Sq)
      hs0 hs1 hfluxMem huMem hGMem hξLp hfluxEnergy hvector
      (by simpa [Ceff] using hdom)
  exact le_trans htest
    (by
      simpa [henergyAvg, Ceff] using hsingle)

theorem CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs.of_factorInputs
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) (F : ℝ → ℝ)
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B A G X Y : ℝ → ℝ → ℝ)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeFactorInputs Q a s C uL2Sq k h F
        flux u g ξ energy Acirc1 AcircS B A G X Y) :
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq k h F
      flux u g ξ energy Acirc1 AcircS B := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  rcases hinputs hρ₁ hlt hρ₂ with
    ⟨htest, henergyAvg, hfluxMem, hu, hg, hξLp, hfluxEnergy, hscalar, hA_nonneg,
      hconstCoeff, hconstCutoff, hconst, havg, hbesov, hcentered⟩
  exact
    ⟨htest, henergyAvg, hfluxMem, hu, hg, hξLp, hfluxEnergy, hscalar,
      CoarseCaccioppoliSingleCubeCoefficientControls.of_factor_bounds
        Q a s C (k ρ₁ ρ₂) (h ρ₁ ρ₂) uL2Sq (u ρ₁ ρ₂) (ξ ρ₁ ρ₂)
        (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂) hA_nonneg hscalar.1
        hconstCoeff hconstCutoff hconst havg hbesov hcentered⟩

theorem CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs.of_separatedFactorInputs
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) (F : ℝ → ℝ)
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B AavgConst AavgCent Aflux1 AfluxS U Xi D A1 AS :
      ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs0 : 0 < s)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeSeparatedFactorInputs Q a s C uL2Sq
        k h F flux u g ξ energy Acirc1 AcircS B AavgConst AavgCent Aflux1 AfluxS
        U Xi D A1 AS) :
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq k h F
      flux u g ξ energy Acirc1 AcircS B := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  rcases hinputs hρ₁ hlt hρ₂ with
    ⟨htest, henergyAvg, hfluxMem, huMem, hg, hξLp, hfluxEnergy, hscalar,
      hB_nonneg, hAcirc1_nonneg, hAcircS_nonneg, hAavgConst, hAavgCent,
      hAflux1, hAfluxS, huBound, hξBound, hB, hAcirc1, hAcircS, hconst,
      hcentered⟩
  exact
    ⟨htest, henergyAvg, hfluxMem, huMem, hg, hξLp, hfluxEnergy, hscalar,
      CoarseCaccioppoliSingleCubeCoefficientControls.of_separated_factor_bounds
        Q a s C (k ρ₁ ρ₂) (h ρ₁ ρ₂) uL2Sq (u ρ₁ ρ₂) (ξ ρ₁ ρ₂)
        (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂) hs0 hC
        hB_nonneg hAcirc1_nonneg hAcircS_nonneg hAavgConst hAavgCent hAflux1 hAfluxS
        huBound hξBound hB hAcirc1 hAcircS hconst hcentered⟩

theorem CoarseCaccioppoliBoundaryRadiusEnergyBridgeSeparatedFactorInputs.of_canonicalFactorInputs
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) (F : ℝ → ℝ)
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B U Xi D A1 AS : ℝ → ℝ → ℝ)
    (hs0 : 0 < s)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalFactorInputs Q a s C uL2Sq
        k h F flux u g ξ energy Acirc1 AcircS B U Xi D A1 AS) :
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeSeparatedFactorInputs Q a s C uL2Sq
      k h F flux u g ξ energy Acirc1 AcircS B
      (fun _ _ => coarseCaccioppoliLambdaFactor Q a (1 : ℝ))
      (fun _ _ => coarseCaccioppoliLambdaFactor Q a s)
      (fun _ _ => coarseCaccioppoliLambdaFactor Q a (1 : ℝ))
      (fun _ _ => coarseCaccioppoliLambdaFactor Q a s)
      U Xi D A1 AS := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  rcases hinputs hρ₁ hlt hρ₂ with
    ⟨htest, henergyAvg, hfluxMem, huMem, hg, hξLp, hfluxEnergy, hscalar,
      hB_nonneg, hAcirc1_nonneg, hAcircS_nonneg, huBound, hξBound, hB, hAcirc1,
      hAcircS, hconst, hcentered⟩
  have hAavgConst :
      Real.sqrt (coarseBBlockNorm Q a) ≤
        coarseCaccioppoliLambdaFactor Q a (1 : ℝ) := by
    exact
      sqrt_coarseBBlockNorm_le_coarseCaccioppoliLambdaFactor
        Q a (by norm_num : 0 < (1 : ℝ)) hfluxEnergy.2.2.2.1
  have hAavgCent :
      Real.sqrt (coarseBBlockNorm Q a) ≤
        coarseCaccioppoliLambdaFactor Q a s := by
    exact
      sqrt_coarseBBlockNorm_le_coarseCaccioppoliLambdaFactor
        Q a hs0 hfluxEnergy.2.2.2.2
  exact
    ⟨htest, henergyAvg, hfluxMem, huMem, hg, hξLp, hfluxEnergy, hscalar,
      hB_nonneg, hAcirc1_nonneg, hAcircS_nonneg, hAavgConst, hAavgCent,
      le_rfl, le_rfl, huBound, hξBound, hB, hAcirc1, hAcircS, hconst, hcentered⟩

theorem CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs.of_canonicalFactorInputs
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) (F : ℝ → ℝ)
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B U Xi D A1 AS : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs0 : 0 < s)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalFactorInputs Q a s C uL2Sq
        k h F flux u g ξ energy Acirc1 AcircS B U Xi D A1 AS) :
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq k h F
      flux u g ξ energy Acirc1 AcircS B := by
  exact
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs.of_separatedFactorInputs
      Q a s C uL2Sq k h F flux u g ξ energy Acirc1 AcircS B
      (fun _ _ => coarseCaccioppoliLambdaFactor Q a (1 : ℝ))
      (fun _ _ => coarseCaccioppoliLambdaFactor Q a s)
      (fun _ _ => coarseCaccioppoliLambdaFactor Q a (1 : ℝ))
      (fun _ _ => coarseCaccioppoliLambdaFactor Q a s)
      U Xi D A1 AS hC hs0
      (CoarseCaccioppoliBoundaryRadiusEnergyBridgeSeparatedFactorInputs.of_canonicalFactorInputs
        Q a s C uL2Sq k h F flux u g ξ energy Acirc1 AcircS B U Xi D A1 AS
        hs0 hinputs)

theorem coarseCaccioppoli_boundary_singleCubeRawEstimate_of_radiusEnergyBridgeInputs
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B : ℝ → ℝ → ℝ)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs Q a s C uL2Sq k h F flux u g ξ
        energy Acirc1 AcircS B) :
    CoarseCaccioppoliBoundarySingleCubeRawEstimate Q a s C uL2Sq k h F := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  rcases hinputs hρ₁ hlt hρ₂ with
    ⟨htest, henergyAvg, hfluxMem, hu, hg, hξLp, hfluxEnergy, hscalar, hcoeff⟩
  have hsingle :
      |cubeAverage Q
          (fun x => vecDot (flux ρ₁ ρ₂ x) ((u ρ₁ ρ₂ x) • ξ ρ₁ ρ₂ x))| ≤
        coarseCaccioppoliSingleCubeBoundaryNoteRhs Q a s C (k ρ₁ ρ₂) (h ρ₁ ρ₂)
          uL2Sq (F ρ₂) := by
    simpa [henergyAvg] using
      (abs_cubeAverage_vecDot_scalar_smul_le_singleCubeBoundaryNoteRhs_of_coefficientControls
        (Q := Q) (a := a) (s := s) (flux := flux ρ₁ ρ₂) (u := u ρ₁ ρ₂)
        (g := g ρ₁ ρ₂) (ξ := ξ ρ₁ ρ₂) (energy := energy ρ₁ ρ₂)
        (Acirc1 := Acirc1 ρ₁ ρ₂) (AcircS := AcircS ρ₁ ρ₂) (B := B ρ₁ ρ₂)
        (C := C) (k := k ρ₁ ρ₂) (h := h ρ₁ ρ₂) (uL2Sq := uL2Sq)
        hs0 hs1 hfluxMem hu hg hξLp hfluxEnergy hscalar hcoeff)
  exact le_trans htest
    hsingle

/-- Radius-indexed factor inputs produce the note-facing single-cube raw
estimate after assembling the bundled coefficient controls. -/
theorem coarseCaccioppoli_boundary_singleCubeRawEstimate_of_radiusEnergyBridgeFactorInputs
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B A G X Y : ℝ → ℝ → ℝ)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeFactorInputs Q a s C uL2Sq k h F
        flux u g ξ energy Acirc1 AcircS B A G X Y) :
    CoarseCaccioppoliBoundarySingleCubeRawEstimate Q a s C uL2Sq k h F := by
  exact
    coarseCaccioppoli_boundary_singleCubeRawEstimate_of_radiusEnergyBridgeInputs
      Q a s C uL2Sq k h flux u g ξ energy Acirc1 AcircS B hs0 hs1
      (CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs.of_factorInputs
        Q a s C uL2Sq k h F flux u g ξ energy Acirc1 AcircS B A G X Y hinputs)

/-- Radius-indexed primitive separated factor inputs produce the note-facing
single-cube raw estimate. -/
theorem coarseCaccioppoli_boundary_singleCubeRawEstimate_of_radiusEnergyBridgeSeparatedFactorInputs
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B AavgConst AavgCent Aflux1 AfluxS U Xi D A1 AS :
      ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs0 : 0 < s) (hs1 : s < 1)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeSeparatedFactorInputs Q a s C uL2Sq
        k h F flux u g ξ energy Acirc1 AcircS B AavgConst AavgCent Aflux1 AfluxS
        U Xi D A1 AS) :
    CoarseCaccioppoliBoundarySingleCubeRawEstimate Q a s C uL2Sq k h F := by
  exact
    coarseCaccioppoli_boundary_singleCubeRawEstimate_of_radiusEnergyBridgeInputs
      Q a s C uL2Sq k h flux u g ξ energy Acirc1 AcircS B hs0 hs1
      (CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs.of_separatedFactorInputs
        Q a s C uL2Sq k h F flux u g ξ energy Acirc1 AcircS B
        AavgConst AavgCent Aflux1 AfluxS U Xi D A1 AS hC hs0 hinputs)

/-- Radius-indexed canonical factor inputs produce the note-facing single-cube
raw estimate. -/
theorem coarseCaccioppoli_boundary_singleCubeRawEstimate_of_radiusEnergyBridgeCanonicalFactorInputs
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (ξ : ℝ → ℝ → Vec d → Vec d) (energy : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS B U Xi D A1 AS : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs0 : 0 < s) (hs1 : s < 1)
    (hinputs :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalFactorInputs Q a s C uL2Sq
        k h F flux u g ξ energy Acirc1 AcircS B U Xi D A1 AS) :
    CoarseCaccioppoliBoundarySingleCubeRawEstimate Q a s C uL2Sq k h F := by
  exact
    coarseCaccioppoli_boundary_singleCubeRawEstimate_of_radiusEnergyBridgeInputs
      Q a s C uL2Sq k h flux u g ξ energy Acirc1 AcircS B hs0 hs1
      (CoarseCaccioppoliBoundaryRadiusEnergyBridgeInputs.of_canonicalFactorInputs
        Q a s C uL2Sq k h F flux u g ξ energy Acirc1 AcircS B U Xi D A1 AS
        hC hs0 hinputs)


end

end Homogenization
