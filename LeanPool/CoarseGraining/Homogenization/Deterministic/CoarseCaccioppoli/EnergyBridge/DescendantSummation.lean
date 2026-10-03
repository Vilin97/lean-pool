/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.DescendantSummation.ExactRhs

/-! # Descendant Summation -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped BigOperators ENNReal

/-!
# Descendant summation for the small-cube Caccioppoli route

The LaTeX proof estimates the cutoff pairing on small cubes and then sums over
those cubes.  This file isolates the measure-theoretic bookkeeping: a
cube-average over `Q` is the descendants-average of the cube-averages over the
depth-`j` descendants, hence its absolute value is controlled by the
descendants-average of the local absolute values.
-/

/-- Small-cube Caccioppoli estimate in the exact-RHS proof shape.

This theorem is the direct descendant route: estimate the cutoff pairing on
each depth-`j` cube using the parent quantitative cutoff, average the local
exact RHS values, and collapse the result to the parent raw RHS by finite
Cauchy. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_raw_of_parentQuantitativeCutoff_on_descendants
    {d : ℕ} {Q : TriadicCube d} (j : ℕ)
    (a : CoeffField d) (s : ℝ) {ρ₁ ρ₂ : ℝ}
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (energy : Vec d → ℝ) (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    {Acirc1 AcircS C K Alpha Bcross : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hpair_int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (flux x) (u x • scalarCutoffGradientField η x))
        (cubeSet Q) MeasureTheory.volume)
    (huQ : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hfluxMem : ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hu : ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hG : ∀ R ∈ descendantsAtDepth Q j, ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hfluxEnergy : ∀ R ∈ descendantsAtDepth Q j,
      CoarseCaccioppoliFluxEnergyControls R a s flux energy)
    (hB :
      0 ≤ quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
    (hAcircS : 0 ≤ AcircS)
    (hBgConst : ∀ R ∈ descendantsAtDepth Q j,
      0 ≤
        coarseCaccioppoliConstantCutoffSize R u (scalarCutoffGradientField η)
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2)))
    (hBgCent : ∀ R ∈ descendantsAtDepth Q j,
      0 ≤
        coarseCaccioppoliCenteredCutoffSize R s (scalarCutoffGradientField η) Acirc1 AcircS
          (Real.sqrt (cubeAverage R energy))
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C))
    (hC : 0 ≤ C)
    (hproj : ∀ R ∈ descendantsAtDepth Q j, ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate R C (cubeFluctuation R u) G N)
    (hGcirc1 : ∀ R ∈ descendantsAtDepth Q j, ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 * Real.sqrt (cubeAverage R energy))
    (hGcircS : ∀ R ∈ descendantsAtDepth Q j, ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS * Real.sqrt (cubeAverage R energy))
    (hK_nonneg : 0 ≤ K)
    (hKparent : K * cubeLpNorm Q (2 : ℝ≥0∞) u ≤ Bcross)
    (hconst : ∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2) +
            cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ (scalarCutoffGradientField η)) ≤ K)
    (hcent : ∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactCenteredCoeff R a s (scalarCutoffGradientField η)
          Acirc1 AcircS
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C) ≤ Alpha) :
    |cubeAverage Q
        (fun x => vecDot (flux x) (u x • scalarCutoffGradientField η x))| ≤
      Alpha * cubeAverage Q energy + Bcross * Real.sqrt (cubeAverage Q energy) := by
  refine le_trans
    (abs_cubeAverage_vecDot_scalar_smul_le_descendantsAverage_of_local_bounds
      Q j flux (scalarCutoffGradientField η) u
      (fun R =>
        coarseCaccioppoliFluxEnergyExactRhs R a s u (scalarCutoffGradientField η) energy
          Acirc1 AcircS
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C))
      hpair_int ?_) ?_
  · intro R hR
    exact
      abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_parentQuantitativeCutoff_on_descendant
        (Q := Q) (R := R) (j := j) hR (a := a) (s := s) (flux := flux) (u := u)
        (G := G) (energy := energy) (η := η) (Acirc1 := Acirc1) (AcircS := AcircS)
        (C := C) hs0 hs1 (hfluxMem R hR) (hu R hR) (hG R hR)
        (hfluxEnergy R hR) hB hAcircS (hBgConst R hR) (hBgCent R hR) hC
        (hproj R hR) (hGcirc1 R hR) (hGcircS R hR)
  · exact
      descendantsAverage_fluxEnergyExactRhs_le_raw_of_pointwise_coefficients
        Q j a s u (scalarCutoffGradientField η) energy Acirc1 AcircS
        (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
        ((Fintype.card (Fin d) : ℝ) * C) K Alpha Bcross
        huQ henergy_nonneg henergy_int hK_nonneg hKparent hconst hcent

/-- Variable-`Acirc` version of
`abs_cubeAverage_vecDot_scalar_smul_le_raw_of_parentQuantitativeCutoff_on_descendants`.

The local descendant pairing and the averaged exact RHS both use
`Acirc1 R` and `AcircS R`. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_raw_of_parentQuantitativeCutoff_on_descendants_variableAcirc
    {d : ℕ} {Q : TriadicCube d} (j : ℕ)
    (a : CoeffField d) (s : ℝ) {ρ₁ ρ₂ : ℝ}
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (energy : Vec d → ℝ) (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (Acirc1 AcircS : TriadicCube d → ℝ) {C K Alpha Bcross : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hpair_int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (flux x) (u x • scalarCutoffGradientField η x))
        (cubeSet Q) MeasureTheory.volume)
    (huQ : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hfluxMem : ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hu : ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hG : ∀ R ∈ descendantsAtDepth Q j, ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hfluxEnergy : ∀ R ∈ descendantsAtDepth Q j,
      CoarseCaccioppoliFluxEnergyControls R a s flux energy)
    (hB :
      0 ≤ quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
    (hAcircS : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ AcircS R)
    (hBgConst : ∀ R ∈ descendantsAtDepth Q j,
      0 ≤
        coarseCaccioppoliConstantCutoffSize R u (scalarCutoffGradientField η)
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2)))
    (hBgCent : ∀ R ∈ descendantsAtDepth Q j,
      0 ≤
        coarseCaccioppoliCenteredCutoffSize R s (scalarCutoffGradientField η)
          (Acirc1 R) (AcircS R)
          (Real.sqrt (cubeAverage R energy))
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C))
    (hC : 0 ≤ C)
    (hproj : ∀ R ∈ descendantsAtDepth Q j, ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate R C (cubeFluctuation R u) G N)
    (hGcirc1 : ∀ R ∈ descendantsAtDepth Q j, ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 R * Real.sqrt (cubeAverage R energy))
    (hGcircS : ∀ R ∈ descendantsAtDepth Q j, ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS R * Real.sqrt (cubeAverage R energy))
    (hK_nonneg : 0 ≤ K)
    (hKparent : K * cubeLpNorm Q (2 : ℝ≥0∞) u ≤ Bcross)
    (hconst : ∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2) +
            cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ (scalarCutoffGradientField η)) ≤ K)
    (hcent : ∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactCenteredCoeff R a s (scalarCutoffGradientField η)
          (Acirc1 R) (AcircS R)
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C) ≤ Alpha) :
    |cubeAverage Q
        (fun x => vecDot (flux x) (u x • scalarCutoffGradientField η x))| ≤
      Alpha * cubeAverage Q energy + Bcross * Real.sqrt (cubeAverage Q energy) := by
  refine le_trans
    (abs_cubeAverage_vecDot_scalar_smul_le_descendantsAverage_of_local_bounds
      Q j flux (scalarCutoffGradientField η) u
      (fun R =>
        coarseCaccioppoliFluxEnergyExactRhs R a s u (scalarCutoffGradientField η) energy
          (Acirc1 R) (AcircS R)
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C))
      hpair_int ?_) ?_
  · intro R hR
    exact
      abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_parentQuantitativeCutoff_on_descendant
        (Q := Q) (R := R) (j := j) hR (a := a) (s := s) (flux := flux) (u := u)
        (G := G) (energy := energy) (η := η) (Acirc1 := Acirc1 R) (AcircS := AcircS R)
        (C := C) hs0 hs1 (hfluxMem R hR) (hu R hR) (hG R hR)
        (hfluxEnergy R hR) hB (hAcircS R hR) (hBgConst R hR) (hBgCent R hR) hC
        (hproj R hR) (hGcirc1 R hR) (hGcircS R hR)
  · exact
      descendantsAverage_fluxEnergyExactRhs_le_raw_of_pointwise_coefficients_variableAcirc
        Q j a s u (scalarCutoffGradientField η) energy Acirc1 AcircS
        (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
        ((Fintype.card (Fin d) : ℝ) * C) K Alpha Bcross
        huQ henergy_nonneg henergy_int hK_nonneg hKparent hconst hcent

/-- Localized-energy descendant summation for a cutoff pairing, assuming the
local descendant bounds are already stated with the outer-radius localized
energy density.

This is the purely summation-level replacement for the old final rewrite by a
full-cube/localized energy equality: the parent exact-RHS collapse is performed
directly on `(scaledClosedCubeSet Q ρ).indicator energy`. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_localized_raw_of_local_exactRhs_bounds_variableAcirc
    {d : ℕ} {Q : TriadicCube d} (j : ℕ) (ρ : ℝ)
    (a : CoeffField d) (s : ℝ)
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (ξ : Vec d → Vec d)
    (energy : Vec d → ℝ)
    (Acirc1 AcircS : TriadicCube d → ℝ) {B C K Alpha Bcross : ℝ}
    (hpair_int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (flux x) (u x • ξ x))
        (cubeSet Q) MeasureTheory.volume)
    (huQ : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hK_nonneg : 0 ≤ K)
    (hKparent : K * cubeLpNorm Q (2 : ℝ≥0∞) u ≤ Bcross)
    (hconst : ∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
          (B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ) ≤ K)
    (hcent : ∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactCenteredCoeff R a s ξ
          (Acirc1 R) (AcircS R) B C ≤ Alpha)
    (hlocal : ∀ R ∈ descendantsAtDepth Q j,
      |cubeAverage R (fun x => vecDot (flux x) (u x • ξ x))| ≤
        coarseCaccioppoliFluxEnergyExactRhs R a s u ξ
          ((scaledClosedCubeSet Q ρ).indicator energy)
          (Acirc1 R) (AcircS R) B C) :
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      Alpha * coarseCaccioppoliLocalizedEnergyProfile Q ρ energy +
        Bcross * Real.sqrt (coarseCaccioppoliLocalizedEnergyProfile Q ρ energy) := by
  refine le_trans
    (abs_cubeAverage_vecDot_scalar_smul_le_descendantsAverage_of_local_bounds
      Q j flux ξ u
      (fun R =>
        coarseCaccioppoliFluxEnergyExactRhs R a s u ξ
          ((scaledClosedCubeSet Q ρ).indicator energy)
          (Acirc1 R) (AcircS R) B C)
      hpair_int hlocal) ?_
  exact
    descendantsAverage_fluxEnergyExactRhs_le_localized_raw_of_pointwise_coefficients_variableAcirc
      Q j ρ a s u ξ energy Acirc1 AcircS B C K Alpha Bcross
      huQ henergy_nonneg henergy_int hK_nonneg hKparent hconst hcent

/-- Arbitrary-center local-patch analogue of
`abs_cubeAverage_vecDot_scalar_smul_le_localized_raw_of_local_exactRhs_bounds_variableAcirc`. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_localPatch_raw_of_local_exactRhs_bounds_variableAcirc
    {d : ℕ} {Q : TriadicCube d} (center : Vec d) (j : ℕ) (rho : ℝ)
    (a : CoeffField d) (s : ℝ)
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (ξ : Vec d → Vec d)
    (energy : Vec d → ℝ)
    (Acirc1 AcircS : TriadicCube d → ℝ) {B C K Alpha Bcross : ℝ}
    (hpair_int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (flux x) (u x • ξ x))
        (cubeSet Q) MeasureTheory.volume)
    (huQ : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hK_nonneg : 0 ≤ K)
    (hKparent : K * cubeLpNorm Q (2 : ℝ≥0∞) u ≤ Bcross)
    (hconst : ∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
          (B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ) ≤ K)
    (hcent : ∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactCenteredCoeff R a s ξ
          (Acirc1 R) (AcircS R) B C ≤ Alpha)
    (hlocal : ∀ R ∈ descendantsAtDepth Q j,
      |cubeAverage R (fun x => vecDot (flux x) (u x • ξ x))| ≤
        coarseCaccioppoliFluxEnergyExactRhs R a s u ξ
          ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)
          (Acirc1 R) (AcircS R) B C) :
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      Alpha * coarseCaccioppoliLocalEnergyProfile Q center rho energy +
        Bcross * Real.sqrt
          (coarseCaccioppoliLocalEnergyProfile Q center rho energy) := by
  refine le_trans
    (abs_cubeAverage_vecDot_scalar_smul_le_descendantsAverage_of_local_bounds
      Q j flux ξ u
      (fun R =>
        coarseCaccioppoliFluxEnergyExactRhs R a s u ξ
          ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)
          (Acirc1 R) (AcircS R) B C)
      hpair_int hlocal) ?_
  exact
    descendantsAverage_fluxEnergyExactRhs_le_localPatch_raw_of_pointwise_coefficients_variableAcirc
      Q center j rho a s u ξ energy Acirc1 AcircS B C K Alpha Bcross
      huQ henergy_nonneg henergy_int hK_nonneg hKparent hconst hcent

/-- Parent-cutoff specialization of
`abs_cubeAverage_vecDot_scalar_smul_le_localized_raw_of_local_exactRhs_bounds_variableAcirc`.

The only analytic input not supplied here is the genuinely local, support-aware
exact-RHS estimate with the outer localized energy density. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_localized_raw_of_parentQuantitativeCutoff_on_descendants_variableAcirc
    {d : ℕ} {Q : TriadicCube d} (j : ℕ)
    (a : CoeffField d) (s : ℝ) {ρ₁ ρ₂ : ℝ}
    (flux : Vec d → Vec d) (u : Vec d → ℝ)
    (energy : Vec d → ℝ) (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (Acirc1 AcircS : TriadicCube d → ℝ) {B C K Alpha Bcross : ℝ}
    (hpair_int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (flux x) (u x • scalarCutoffGradientField η x))
        (cubeSet Q) MeasureTheory.volume)
    (huQ : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hK_nonneg : 0 ≤ K)
    (hKparent : K * cubeLpNorm Q (2 : ℝ≥0∞) u ≤ Bcross)
    (hconst : ∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
          (B + cubeBesovScaleWeight 1 R *
            cubeLpNorm R ∞ (scalarCutoffGradientField η)) ≤ K)
    (hcent : ∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactCenteredCoeff R a s
          (scalarCutoffGradientField η) (Acirc1 R) (AcircS R) B C ≤ Alpha)
    (hlocal : ∀ R ∈ descendantsAtDepth Q j,
      |cubeAverage R
        (fun x => vecDot (flux x) (u x • scalarCutoffGradientField η x))| ≤
        coarseCaccioppoliFluxEnergyExactRhs R a s u
          (scalarCutoffGradientField η)
          ((scaledClosedCubeSet Q ρ₂).indicator energy)
          (Acirc1 R) (AcircS R) B C) :
    |cubeAverage Q
        (fun x => vecDot (flux x) (u x • scalarCutoffGradientField η x))| ≤
      Alpha * coarseCaccioppoliLocalizedEnergyProfile Q ρ₂ energy +
        Bcross * Real.sqrt (coarseCaccioppoliLocalizedEnergyProfile Q ρ₂ energy) := by
  exact
    abs_cubeAverage_vecDot_scalar_smul_le_localized_raw_of_local_exactRhs_bounds_variableAcirc
      (Q := Q) (j := j) (ρ := ρ₂) (a := a) (s := s)
      (flux := flux) (u := u) (ξ := scalarCutoffGradientField η)
      (energy := energy) (Acirc1 := Acirc1) (AcircS := AcircS)
      (B := B) (C := C) (K := K) (Alpha := Alpha) (Bcross := Bcross)
      hpair_int huQ henergy_nonneg henergy_int hK_nonneg hKparent
      hconst hcent hlocal

/-- Buffered localized-energy descendant summation for a parent cutoff.

The cutoff is supported in `scaledClosedCubeSet Q ρ₂`, while the RHS energy is
localized on the larger radius `ρ`.  The buffer hypothesis says every
depth-`j` descendant is small enough that a cube touching the cutoff support is
contained in the larger localization cube; descendants missing the support have
zero local pairing. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_localized_raw_of_parentQuantitativeCutoff_on_descendants_variableAcirc_of_support_buffer
    {d : ℕ} {Q : TriadicCube d} (j : ℕ)
    (a : CoeffField d) (s : ℝ) {ρ₁ ρ₂ ρ : ℝ}
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (energy : Vec d → ℝ) (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (Acirc1 AcircS : TriadicCube d → ℝ) {C K Alpha Bcross : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hbuffer : ∀ R ∈ descendantsAtDepth Q j,
      cubeScaleFactor R ≤ (ρ - ρ₂) * cubeRadius Q)
    (hpair_int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (flux x) (u x • scalarCutoffGradientField η x))
        (cubeSet Q) MeasureTheory.volume)
    (huQ : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hfluxMem : ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hu : ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hG : ∀ R ∈ descendantsAtDepth Q j, ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hfluxEnergy : ∀ R ∈ descendantsAtDepth Q j,
      CoarseCaccioppoliFluxEnergyControls R a s flux energy)
    (hB :
      0 ≤ quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
    (hAcirc1 : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ Acirc1 R)
    (hAcircS : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ AcircS R)
    (hBgConst : ∀ R ∈ descendantsAtDepth Q j,
      0 ≤
        coarseCaccioppoliConstantCutoffSize R u (scalarCutoffGradientField η)
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2)))
    (hBgCent : ∀ R ∈ descendantsAtDepth Q j,
      0 ≤
        coarseCaccioppoliCenteredCutoffSize R s (scalarCutoffGradientField η)
          (Acirc1 R) (AcircS R)
          (Real.sqrt (cubeAverage R energy))
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C))
    (hC : 0 ≤ C)
    (hproj : ∀ R ∈ descendantsAtDepth Q j, ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate R C (cubeFluctuation R u) G N)
    (hGcirc1 : ∀ R ∈ descendantsAtDepth Q j, ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 R * Real.sqrt (cubeAverage R energy))
    (hGcircS : ∀ R ∈ descendantsAtDepth Q j, ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS R * Real.sqrt (cubeAverage R energy))
    (hK_nonneg : 0 ≤ K)
    (hKparent : K * cubeLpNorm Q (2 : ℝ≥0∞) u ≤ Bcross)
    (hconst : ∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2) +
            cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ (scalarCutoffGradientField η)) ≤ K)
    (hcent : ∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactCenteredCoeff R a s (scalarCutoffGradientField η)
          (Acirc1 R) (AcircS R)
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C) ≤ Alpha) :
    |cubeAverage Q
        (fun x => vecDot (flux x) (u x • scalarCutoffGradientField η x))| ≤
      Alpha * coarseCaccioppoliLocalizedEnergyProfile Q ρ energy +
        Bcross * Real.sqrt (coarseCaccioppoliLocalizedEnergyProfile Q ρ energy) := by
  exact
    abs_cubeAverage_vecDot_scalar_smul_le_localized_raw_of_local_exactRhs_bounds_variableAcirc
      (Q := Q) (j := j) (ρ := ρ) (a := a) (s := s)
      (flux := flux) (u := u) (ξ := scalarCutoffGradientField η)
      (energy := energy) (Acirc1 := Acirc1) (AcircS := AcircS)
      (B := quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
      (C := (Fintype.card (Fin d) : ℝ) * C)
      (K := K) (Alpha := Alpha) (Bcross := Bcross)
      hpair_int huQ henergy_nonneg henergy_int hK_nonneg hKparent
      hconst hcent
      (fun R hR =>
        abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_indicator_of_parentQuantitativeCutoff_on_descendant_of_support_buffer
          (Q := Q) (R := R) (j := j) hR (a := a) (s := s)
          (ρ := ρ) (flux := flux) (u := u) (G := G) (energy := energy)
          (η := η) (Acirc1 := Acirc1 R) (AcircS := AcircS R) (C := C)
          (hbuffer R hR) hs0 hs1 (hfluxMem R hR) (hu R hR) (hG R hR)
          (hfluxEnergy R hR) hB (hAcirc1 R hR) (hAcircS R hR)
          (hBgConst R hR) (hBgCent R hR) hC (hproj R hR)
          (hGcirc1 R hR) (hGcircS R hR))

/-- Buffered arbitrary-center local-patch descendant summation for the
translated canonical cutoff.  This is the summation-level form of the boundary
Caccioppoli radius step from the notes. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_localPatch_raw_of_localCanonicalCutoff_on_descendants_variableAcirc_of_support_buffer
    {d : ℕ} {Q : TriadicCube d} (center : Vec d) (j : ℕ)
    (a : CoeffField d) (s : ℝ) {rhoInner rhoOuter rho : ℝ}
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (energy : Vec d → ℝ)
    (Acirc1 AcircS : TriadicCube d → ℝ) {C K Alpha Bcross : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hbuffer : ∀ R ∈ descendantsAtDepth Q j,
      cubeScaleFactor R ≤ (rho - rhoOuter) * (cubeRadius Q / 3))
    (hpair_int :
      MeasureTheory.IntegrableOn
        (fun x =>
          vecDot (flux x)
            (u x •
              scalarCutoffGradientField
                (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) x))
        (cubeSet Q) MeasureTheory.volume)
    (huQ : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hfluxMem : ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hu : ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hG : ∀ R ∈ descendantsAtDepth Q j, ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hfluxEnergy : ∀ R ∈ descendantsAtDepth Q j,
      CoarseCaccioppoliFluxEnergyControls R a s flux energy)
    (hB :
      0 ≤
        quantitativeCubeCutoffHessianConst d /
          (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
    (hAcirc1 : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ Acirc1 R)
    (hAcircS : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ AcircS R)
    (hBgConst : ∀ R ∈ descendantsAtDepth Q j,
      0 ≤
        coarseCaccioppoliConstantCutoffSize R u
          (scalarCutoffGradientField
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
          (quantitativeCubeCutoffHessianConst d /
            (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2)))
    (hBgCent : ∀ R ∈ descendantsAtDepth Q j,
      0 ≤
        coarseCaccioppoliCenteredCutoffSize R s
          (scalarCutoffGradientField
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
          (Acirc1 R) (AcircS R)
          (Real.sqrt (cubeAverage R energy))
          (quantitativeCubeCutoffHessianConst d /
            (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C))
    (hC : 0 ≤ C)
    (hproj : ∀ R ∈ descendantsAtDepth Q j, ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate R C (cubeFluctuation R u) G N)
    (hGcirc1 : ∀ R ∈ descendantsAtDepth Q j, ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 R * Real.sqrt (cubeAverage R energy))
    (hGcircS : ∀ R ∈ descendantsAtDepth Q j, ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS R * Real.sqrt (cubeAverage R energy))
    (hK_nonneg : 0 ≤ K)
    (hKparent : K * cubeLpNorm Q (2 : ℝ≥0∞) u ≤ Bcross)
    (hconst : ∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
          (quantitativeCubeCutoffHessianConst d /
              (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2) +
            cubeBesovScaleWeight 1 R *
              cubeLpNorm R ∞
                (scalarCutoffGradientField
                  (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))) ≤ K)
    (hcent : ∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactCenteredCoeff R a s
          (scalarCutoffGradientField
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
          (Acirc1 R) (AcircS R)
          (quantitativeCubeCutoffHessianConst d /
            (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C) ≤ Alpha) :
    |cubeAverage Q
        (fun x =>
          vecDot (flux x)
            (u x •
              scalarCutoffGradientField
                (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) x))| ≤
      Alpha * coarseCaccioppoliLocalEnergyProfile Q center rho energy +
        Bcross * Real.sqrt (coarseCaccioppoliLocalEnergyProfile Q center rho energy) := by
  exact
    abs_cubeAverage_vecDot_scalar_smul_le_localPatch_raw_of_local_exactRhs_bounds_variableAcirc
      (Q := Q) (center := center) (j := j) (rho := rho)
      (a := a) (s := s) (flux := flux) (u := u)
      (ξ := scalarCutoffGradientField
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
      (energy := energy) (Acirc1 := Acirc1) (AcircS := AcircS)
      (B := quantitativeCubeCutoffHessianConst d /
        (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
      (C := (Fintype.card (Fin d) : ℝ) * C)
      (K := K) (Alpha := Alpha) (Bcross := Bcross)
      hpair_int huQ henergy_nonneg henergy_int hK_nonneg hKparent hconst hcent
      (fun R hR =>
        abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_indicator_of_localCanonicalCutoff_on_descendant_of_support_buffer
          (Q := Q) (R := R) (j := j) hR
          (center := center) (a := a) (s := s)
          (rhoInner := rhoInner) (rhoOuter := rhoOuter) (rho := rho)
          (flux := flux) (u := u) (G := G) (energy := energy)
          (Acirc1 := Acirc1 R) (AcircS := AcircS R) (C := C)
          hinner hinnerOuter (hbuffer R hR) hs0 hs1
          (hfluxMem R hR) (hu R hR) (hG R hR) (hfluxEnergy R hR) hB
          (hAcirc1 R hR) (hAcircS R hR)
          (hBgConst R hR) (hBgCent R hR) hC (hproj R hR)
          (hGcirc1 R hR) (hGcircS R hR))

end

end Homogenization
