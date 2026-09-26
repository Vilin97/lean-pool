/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.DescendantSummation
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.LocalEstimateFullDual

/-! # Descendant Summation Full Dual -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped BigOperators ENNReal

/-!
# Full-dual descendant summation

This sidecar is the corrected descendant summation corridor for the vector
small-cube Caccioppoli route.  It is parallel to the legacy projected theorem
in `DescendantSummation.lean`, but the local estimate is supplied by the
full-dual/local-multiscale exact-RHS theorem.
-/

/-- Variable-`Acirc` descendant raw estimate using full-dual vector Poincare
and the finite local-multiscale estimate on every descendant. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_raw_of_parentQuantitativeCutoff_on_descendants_variableAcirc_vectorFullDualLocalMultiscale
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
    (hfull : ∀ R ∈ descendantsAtDepth Q j, ∀ N : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate R C (cubeFluctuation R u) G N)
    (hlocal : ∀ R ∈ descendantsAtDepth Q j, ∀ N : ℕ,
      CubeLocalMultiscalePoincareVectorEstimate R
        (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)))
        (cubeFluctuation R u) G N)
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
      abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_parentQuantitativeCutoff_on_descendant_vectorFullDualLocalMultiscale
        (Q := Q) (R := R) (j := j) hR (a := a) (s := s) (flux := flux) (u := u)
        (G := G) (energy := energy) (η := η) (Acirc1 := Acirc1 R) (AcircS := AcircS R)
        (C := C) hs0 hs1 (hfluxMem R hR) (hu R hR) (hG R hR)
        (hfluxEnergy R hR) hB (hAcirc1 R hR) (hAcircS R hR)
        (hBgConst R hR) (hBgCent R hR) hC
        (hfull R hR) (hlocal R hR) (hGcirc1 R hR) (hGcircS R hR)
  · exact
      descendantsAverage_fluxEnergyExactRhs_le_raw_of_pointwise_coefficients_variableAcirc
        Q j a s u (scalarCutoffGradientField η) energy Acirc1 AcircS
        (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
        ((Fintype.card (Fin d) : ℝ) * C) K Alpha Bcross
        huQ henergy_nonneg henergy_int hK_nonneg hKparent hconst hcent

/-- Buffered localized-energy descendant summation using full-dual Poincare and
the infinite-depth full-circ route on every descendant. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_localized_raw_of_parentQuantitativeCutoff_on_descendants_variableAcirc_of_support_buffer_vectorFullDualFullCirc
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
    (hfull : ∀ R ∈ descendantsAtDepth Q j, ∀ N : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate R C (cubeFluctuation R u) G N)
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
        abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_indicator_of_parentQuantitativeCutoff_on_descendant_of_support_buffer_vectorFullDualFullCirc
          (Q := Q) (R := R) (j := j) hR (a := a) (s := s)
          (ρ := ρ) (flux := flux) (u := u) (G := G) (energy := energy)
          (η := η) (Acirc1 := Acirc1 R) (AcircS := AcircS R) (C := C)
          (hbuffer R hR) hs0 hs1 (hfluxMem R hR) (hu R hR) (hG R hR)
          (hfluxEnergy R hR) hB (hAcirc1 R hR) (hAcircS R hR)
          (hBgConst R hR) (hBgCent R hR) hC (hfull R hR)
          (hGcirc1 R hR) (hGcircS R hR))

/-- Buffered arbitrary-center local-patch descendant summation for the
translated canonical cutoff using the full-dual/full-circ route. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_localPatch_raw_of_localCanonicalCutoff_on_descendants_variableAcirc_of_support_buffer_vectorFullDualFullCirc
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
    (hfull : ∀ R ∈ descendantsAtDepth Q j, ∀ N : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate R C (cubeFluctuation R u) G N)
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
        abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_indicator_of_localCanonicalCutoff_on_descendant_of_support_buffer_vectorFullDualFullCirc
          (Q := Q) (R := R) (j := j) hR
          (center := center) (a := a) (s := s)
          (rhoInner := rhoInner) (rhoOuter := rhoOuter) (rho := rho)
          (flux := flux) (u := u) (G := G) (energy := energy)
          (Acirc1 := Acirc1 R) (AcircS := AcircS R) (C := C)
          hinner hinnerOuter (hbuffer R hR) hs0 hs1
          (hfluxMem R hR) (hu R hR) (hG R hR) (hfluxEnergy R hR) hB
          (hAcirc1 R hR) (hAcircS R hR)
          (hBgConst R hR) (hBgCent R hR) hC (hfull R hR)
          (hGcirc1 R hR) (hGcircS R hR))

end

end Homogenization
