/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.SplitPairing.VectorFullDual
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.LocalEstimate

/-! # Local Estimate Full Dual -/

namespace Homogenization

noncomputable section

open scoped BigOperators ENNReal

/-!
# Full-dual local Caccioppoli estimate

This sidecar is the corrected full-dual/local-multiscale analogue of the
vector projected-Poincare local estimate in `LocalEstimate.lean`.
-/

theorem
    abs_cubeAverage_vecDot_scalar_smul_le_split_of_fluxEnergyControl_of_contDiff_component_vector_bound_dualFull_localMultiscale
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (G ξ : Vec d → Vec d)
    (energy : Vec d → ℝ)
    {Acirc1 AcircS B C BgConst BgCent : ℝ}
    (hB : 0 ≤ B) (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBgConst : 0 ≤ BgConst) (hBgCent : 0 ≤ BgCent)
    (hC : 0 ≤ C) (hAcirc1 : 0 ≤ Acirc1) (hAcircS : 0 ≤ AcircS)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hfluxCtrl : CubeAverageFluxEnergyControl Q a flux energy)
    (hsum1 :
      Summable (fun n : ℕ =>
        geometricWeight (1 : ℝ) 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hsumS :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hfull : ∀ N : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hlocal : ∀ N : ℕ,
      CubeLocalMultiscalePoincareVectorEstimate Q
        (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)))
        (cubeFluctuation Q u) G N)
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 * Real.sqrt (cubeAverage Q energy))
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS * Real.sqrt (cubeAverage Q energy))
    (hBgConst_bound :
      cubeLpNorm Q (2 : ℝ≥0∞) u *
          (B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ ξ) ≤ BgConst)
    (hBgCent_bound :
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * C) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (Acirc1 * Real.sqrt (cubeAverage Q energy)))) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * C) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) *
              (AcircS * Real.sqrt (cubeAverage Q energy))))) ≤ BgCent) :
    let E : ℝ := Real.sqrt (cubeAverage Q energy)
    let Aavg : ℝ := Real.sqrt (coarseBBlockNorm Q a)
    let Aflux1 : ℝ :=
      (geometricDiscount (1 : ℝ) 1)⁻¹ *
        Real.rpow (LambdaSq Q (1 : ℝ) (.finite 1) a) (1 / 2 : ℝ)
    let AfluxS : ℝ :=
      (geometricDiscount s 1)⁻¹ *
        Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      (d : ℝ) *
        (((3 : ℝ) ^ ((d : ℝ) + 1) *
          (cubeBesovScaleWeight (-1) Q * (Aflux1 * E))) * BgConst) +
        ((d : ℝ) *
          ((Aavg * E) * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * C) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) * (Acirc1 * E)))) +
          (d : ℝ) *
            ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * (AfluxS * E))) *
              (cubeBesovScaleWeight s Q * BgCent)))) := by
  dsimp only
  have havgFlux :
      ‖cubeAverageVec Q flux‖ ≤
        Real.sqrt (coarseBBlockNorm Q a) * Real.sqrt (cubeAverage Q energy) :=
    norm_cubeAverageVec_le_sqrt_coarseBBlockNorm_mul_sqrt_cubeAverage_of_fluxEnergyControl
      Q a flux energy hfluxCtrl
  have hBcircS_nonneg :
      0 ≤ AcircS * Real.sqrt (cubeAverage Q energy) :=
    mul_nonneg hAcircS (Real.sqrt_nonneg _)
  exact
    abs_cubeAverage_vecDot_scalar_smul_le_split_collapsed_sharp_note_terms_of_dualFull_localMultiscale_effective_constant
      (Q := Q) (s := s) (flux := flux) (u := u) (G := G) (ξ := ξ)
      (Bu1 :=
        (geometricDiscount (1 : ℝ) 1)⁻¹ *
          Real.rpow (LambdaSq Q (1 : ℝ) (.finite 1) a) (1 / 2 : ℝ) *
          Real.sqrt (cubeAverage Q energy))
      (BuS :=
        (geometricDiscount s 1)⁻¹ *
          Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
          Real.sqrt (cubeAverage Q energy))
      (Bavg := Real.sqrt (coarseBBlockNorm Q a) * Real.sqrt (cubeAverage Q energy))
      (Bcirc1 := Acirc1 * Real.sqrt (cubeAverage Q energy))
      (BcircS := AcircS * Real.sqrt (cubeAverage Q energy))
      (B := B) (C := C) (BgConst := BgConst) (BgCent := BgCent)
      hB hs0 hs1 hfluxMem hu hG hξLp hBgConst hBgCent
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hC
      (mul_nonneg hAcirc1 (Real.sqrt_nonneg _))
      (mul_nonneg hAcircS (Real.sqrt_nonneg _)) havgFlux
      (fun N =>
        coarseCaccioppoli_flux_qone_partialBound_of_cubeAverageEnergyControl
          Q a (1 : ℝ) (by norm_num) flux energy N henergy_nonneg henergy_int hfluxCtrl hsum1)
      (fun N =>
        coarseCaccioppoli_flux_qone_partialBound_of_cubeAverageEnergyControl
          Q a s hs0 flux energy N henergy_nonneg henergy_int hfluxCtrl hsumS)
      hfull hlocal hξ hderiv hGcirc1 hGcircS hBgConst_bound hBgCent_bound

/-- Compact exact-RHS local Caccioppoli estimate using full-dual vector
Poincare plus the finite local-multiscale estimate. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_vectorFullDualLocalMultiscale
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (G ξ : Vec d → Vec d)
    (energy : Vec d → ℝ)
    {Acirc1 AcircS B C : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls Q a s flux energy)
    (hB : 0 ≤ B) (hAcirc1 : 0 ≤ Acirc1) (hAcircS : 0 ≤ AcircS)
    (hBgConst : 0 ≤ coarseCaccioppoliConstantCutoffSize Q u ξ B)
    (hBgCent :
      0 ≤
        coarseCaccioppoliCenteredCutoffSize Q s ξ Acirc1 AcircS
          (Real.sqrt (cubeAverage Q energy)) B ((Fintype.card (Fin d) : ℝ) * C))
    (hC : 0 ≤ C)
    (hfull : ∀ N : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hlocal : ∀ N : ℕ,
      CubeLocalMultiscalePoincareVectorEstimate Q
        (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)))
        (cubeFluctuation Q u) G N)
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 * Real.sqrt (cubeAverage Q energy))
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS * Real.sqrt (cubeAverage Q energy)) :
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      coarseCaccioppoliFluxEnergyExactRhs Q a s u ξ energy Acirc1 AcircS B
        ((Fintype.card (Fin d) : ℝ) * C) := by
  rcases hfluxEnergy with ⟨henergy_nonneg, henergy_int, hfluxCtrl, hsum1, hsumS⟩
  simpa [coarseCaccioppoliFluxEnergyExactRhs] using
    abs_cubeAverage_vecDot_scalar_smul_le_split_of_fluxEnergyControl_of_contDiff_component_vector_bound_dualFull_localMultiscale
      (Q := Q) (a := a) (s := s) (flux := flux) (u := u) (G := G) (ξ := ξ)
      (energy := energy) (Acirc1 := Acirc1) (AcircS := AcircS) (B := B) (C := C)
      (BgConst := coarseCaccioppoliConstantCutoffSize Q u ξ B)
      (BgCent :=
        coarseCaccioppoliCenteredCutoffSize Q s ξ Acirc1 AcircS
          (Real.sqrt (cubeAverage Q energy)) B ((Fintype.card (Fin d) : ℝ) * C))
      hB hs0 hs1 hfluxMem hu hG hξLp hBgConst hBgCent hC hAcirc1 hAcircS
      henergy_nonneg henergy_int hfluxCtrl hsum1 hsumS
      hfull hlocal hξ hderiv hGcirc1 hGcircS
      (by rfl)
      (by rfl)

/-- Exact local Caccioppoli estimate on a descendant cube using a cutoff
constructed on the parent cube, with the corrected full-dual/local-multiscale
Poincare inputs. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_parentQuantitativeCutoff_on_descendant_vectorFullDualLocalMultiscale
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    (a : CoeffField d) (s : ℝ) {ρ₁ ρ₂ : ℝ}
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (energy : Vec d → ℝ) (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    {Acirc1 AcircS C : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls R a s flux energy)
    (hB :
      0 ≤ quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
    (hAcirc1 : 0 ≤ Acirc1)
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
    (hfull : ∀ N : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate R C (cubeFluctuation R u) G N)
    (hlocal : ∀ N : ℕ,
      CubeLocalMultiscalePoincareVectorEstimate R
        (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)))
        (cubeFluctuation R u) G N)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 * Real.sqrt (cubeAverage R energy))
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS * Real.sqrt (cubeAverage R energy)) :
    |cubeAverage R (fun x => vecDot (flux x) (u x • scalarCutoffGradientField η x))| ≤
      coarseCaccioppoliFluxEnergyExactRhs R a s u (scalarCutoffGradientField η) energy
        Acirc1 AcircS
        (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
        ((Fintype.card (Fin d) : ℝ) * C) := by
  have hξLp :
      MeasureTheory.MemLp (scalarCutoffGradientField η) ∞ (normalizedCubeMeasure R) :=
    quantitativeCubeCutoff_memLp_top_gradientField_on_descendant hR η
  exact
    abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_vectorFullDualLocalMultiscale
      (Q := R) (a := a) (s := s) (flux := flux) (u := u) (G := G)
      (ξ := scalarCutoffGradientField η) (energy := energy)
      (Acirc1 := Acirc1) (AcircS := AcircS)
      (B := quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
      (C := C) hs0 hs1 hfluxMem hu hG hξLp hfluxEnergy hB hAcirc1 hAcircS
      hBgConst hBgCent hC hfull hlocal
      (fun i => contDiff_scalarCutoffGradientField_component η.smooth i)
      (quantitativeCubeCutoff_component_fderiv_bound_on_descendant hR η)
      hGcirc1 hGcircS

/-- Local Caccioppoli estimate using full-dual Poincare and infinite-depth
full-circ bounds, with no finite local-multiscale Poincare input. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_split_of_fluxEnergyControl_of_contDiff_component_vector_bound_dualFull_fullCirc
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (G ξ : Vec d → Vec d)
    (energy : Vec d → ℝ)
    {Acirc1 AcircS B C BgConst BgCent : ℝ}
    (hB : 0 ≤ B) (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBgConst : 0 ≤ BgConst) (hBgCent : 0 ≤ BgCent)
    (hC : 0 ≤ C) (hAcirc1 : 0 ≤ Acirc1) (hAcircS : 0 ≤ AcircS)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hfluxCtrl : CubeAverageFluxEnergyControl Q a flux energy)
    (hsum1 :
      Summable (fun n : ℕ =>
        geometricWeight (1 : ℝ) 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hsumS :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hfull : ∀ N : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 * Real.sqrt (cubeAverage Q energy))
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS * Real.sqrt (cubeAverage Q energy))
    (hBgConst_bound :
      cubeLpNorm Q (2 : ℝ≥0∞) u *
          (B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ ξ) ≤ BgConst)
    (hBgCent_bound :
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * C) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (Acirc1 * Real.sqrt (cubeAverage Q energy)))) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * C) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) *
              (AcircS * Real.sqrt (cubeAverage Q energy))))) ≤ BgCent) :
    let E : ℝ := Real.sqrt (cubeAverage Q energy)
    let Aavg : ℝ := Real.sqrt (coarseBBlockNorm Q a)
    let Aflux1 : ℝ :=
      (geometricDiscount (1 : ℝ) 1)⁻¹ *
        Real.rpow (LambdaSq Q (1 : ℝ) (.finite 1) a) (1 / 2 : ℝ)
    let AfluxS : ℝ :=
      (geometricDiscount s 1)⁻¹ *
        Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      (d : ℝ) *
        (((3 : ℝ) ^ ((d : ℝ) + 1) *
          (cubeBesovScaleWeight (-1) Q * (Aflux1 * E))) * BgConst) +
        ((d : ℝ) *
          ((Aavg * E) * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * C) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) * (Acirc1 * E)))) +
          (d : ℝ) *
            ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * (AfluxS * E))) *
              (cubeBesovScaleWeight s Q * BgCent)))) := by
  dsimp only
  have havgFlux :
      ‖cubeAverageVec Q flux‖ ≤
        Real.sqrt (coarseBBlockNorm Q a) * Real.sqrt (cubeAverage Q energy) :=
    norm_cubeAverageVec_le_sqrt_coarseBBlockNorm_mul_sqrt_cubeAverage_of_fluxEnergyControl
      Q a flux energy hfluxCtrl
  exact
    abs_cubeAverage_vecDot_scalar_smul_le_split_collapsed_sharp_note_terms_of_dualFull_fullCirc_effective_constant
      (Q := Q) (s := s) (flux := flux) (u := u) (G := G) (ξ := ξ)
      (Bu1 :=
        (geometricDiscount (1 : ℝ) 1)⁻¹ *
          Real.rpow (LambdaSq Q (1 : ℝ) (.finite 1) a) (1 / 2 : ℝ) *
          Real.sqrt (cubeAverage Q energy))
      (BuS :=
        (geometricDiscount s 1)⁻¹ *
          Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
          Real.sqrt (cubeAverage Q energy))
      (Bavg := Real.sqrt (coarseBBlockNorm Q a) * Real.sqrt (cubeAverage Q energy))
      (Bcirc1 := Acirc1 * Real.sqrt (cubeAverage Q energy))
      (BcircS := AcircS * Real.sqrt (cubeAverage Q energy))
      (B := B) (C := C) (BgConst := BgConst) (BgCent := BgCent)
      hB hs0 hs1 hfluxMem hu hG hξLp hBgConst hBgCent
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hC
      (mul_nonneg hAcirc1 (Real.sqrt_nonneg _))
      (mul_nonneg hAcircS (Real.sqrt_nonneg _)) havgFlux
      (fun N =>
        coarseCaccioppoli_flux_qone_partialBound_of_cubeAverageEnergyControl
          Q a (1 : ℝ) (by norm_num) flux energy N henergy_nonneg henergy_int hfluxCtrl hsum1)
      (fun N =>
        coarseCaccioppoli_flux_qone_partialBound_of_cubeAverageEnergyControl
          Q a s hs0 flux energy N henergy_nonneg henergy_int hfluxCtrl hsumS)
      hfull hξ hderiv hGcirc1 hGcircS hBgConst_bound hBgCent_bound

/-- Compact exact-RHS local Caccioppoli estimate using full-dual Poincare and
the infinite-depth full-circ bounds. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_vectorFullDualFullCirc
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (G ξ : Vec d → Vec d)
    (energy : Vec d → ℝ)
    {Acirc1 AcircS B C : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls Q a s flux energy)
    (hB : 0 ≤ B) (hAcirc1 : 0 ≤ Acirc1) (hAcircS : 0 ≤ AcircS)
    (hBgConst : 0 ≤ coarseCaccioppoliConstantCutoffSize Q u ξ B)
    (hBgCent :
      0 ≤
        coarseCaccioppoliCenteredCutoffSize Q s ξ Acirc1 AcircS
          (Real.sqrt (cubeAverage Q energy)) B ((Fintype.card (Fin d) : ℝ) * C))
    (hC : 0 ≤ C)
    (hfull : ∀ N : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 * Real.sqrt (cubeAverage Q energy))
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS * Real.sqrt (cubeAverage Q energy)) :
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      coarseCaccioppoliFluxEnergyExactRhs Q a s u ξ energy Acirc1 AcircS B
        ((Fintype.card (Fin d) : ℝ) * C) := by
  rcases hfluxEnergy with ⟨henergy_nonneg, henergy_int, hfluxCtrl, hsum1, hsumS⟩
  simpa [coarseCaccioppoliFluxEnergyExactRhs] using
    abs_cubeAverage_vecDot_scalar_smul_le_split_of_fluxEnergyControl_of_contDiff_component_vector_bound_dualFull_fullCirc
      (Q := Q) (a := a) (s := s) (flux := flux) (u := u) (G := G) (ξ := ξ)
      (energy := energy) (Acirc1 := Acirc1) (AcircS := AcircS) (B := B) (C := C)
      (BgConst := coarseCaccioppoliConstantCutoffSize Q u ξ B)
      (BgCent :=
        coarseCaccioppoliCenteredCutoffSize Q s ξ Acirc1 AcircS
          (Real.sqrt (cubeAverage Q energy)) B ((Fintype.card (Fin d) : ℝ) * C))
      hB hs0 hs1 hfluxMem hu hG hξLp hBgConst hBgCent hC hAcirc1 hAcircS
      henergy_nonneg henergy_int hfluxCtrl hsum1 hsumS
      hfull hξ hderiv hGcirc1 hGcircS
      (by rfl)
      (by rfl)

/-- Exact local Caccioppoli estimate on a descendant cube using a parent
quantitative cutoff and the full-dual/full-circ Poincare route. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_parentQuantitativeCutoff_on_descendant_vectorFullDualFullCirc
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    (a : CoeffField d) (s : ℝ) {ρ₁ ρ₂ : ℝ}
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (energy : Vec d → ℝ) (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    {Acirc1 AcircS C : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls R a s flux energy)
    (hB :
      0 ≤ quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
    (hAcirc1 : 0 ≤ Acirc1)
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
    (hfull : ∀ N : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate R C (cubeFluctuation R u) G N)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 * Real.sqrt (cubeAverage R energy))
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS * Real.sqrt (cubeAverage R energy)) :
    |cubeAverage R (fun x => vecDot (flux x) (u x • scalarCutoffGradientField η x))| ≤
      coarseCaccioppoliFluxEnergyExactRhs R a s u (scalarCutoffGradientField η) energy
        Acirc1 AcircS
        (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
        ((Fintype.card (Fin d) : ℝ) * C) := by
  have hξLp :
      MeasureTheory.MemLp (scalarCutoffGradientField η) ∞ (normalizedCubeMeasure R) :=
    quantitativeCubeCutoff_memLp_top_gradientField_on_descendant hR η
  exact
    abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_vectorFullDualFullCirc
      (Q := R) (a := a) (s := s) (flux := flux) (u := u) (G := G)
      (ξ := scalarCutoffGradientField η) (energy := energy)
      (Acirc1 := Acirc1) (AcircS := AcircS)
      (B := quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
      (C := C) hs0 hs1 hfluxMem hu hG hξLp hfluxEnergy hB hAcirc1 hAcircS
      hBgConst hBgCent hC hfull
      (fun i => contDiff_scalarCutoffGradientField_component η.smooth i)
      (quantitativeCubeCutoff_component_fderiv_bound_on_descendant hR η)
      hGcirc1 hGcircS

/-- Support-localized exact-RHS estimate on the contained-descendant branch,
using the full-dual/full-circ route. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_indicator_of_parentQuantitativeCutoff_on_descendant_of_cubeSet_subset_vectorFullDualFullCirc
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    (a : CoeffField d) (s : ℝ) {ρ₁ ρ₂ ρ : ℝ}
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (energy : Vec d → ℝ) (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    {Acirc1 AcircS C : ℝ}
    (hsub : cubeSet R ⊆ scaledClosedCubeSet Q ρ)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls R a s flux energy)
    (hB :
      0 ≤ quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
    (hAcirc1 : 0 ≤ Acirc1)
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
    (hfull : ∀ N : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate R C (cubeFluctuation R u) G N)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 * Real.sqrt (cubeAverage R energy))
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS * Real.sqrt (cubeAverage R energy)) :
    |cubeAverage R (fun x => vecDot (flux x) (u x • scalarCutoffGradientField η x))| ≤
      coarseCaccioppoliFluxEnergyExactRhs R a s u (scalarCutoffGradientField η)
        ((scaledClosedCubeSet Q ρ).indicator energy)
        Acirc1 AcircS
        (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
        ((Fintype.card (Fin d) : ℝ) * C) := by
  have havg :
      cubeAverage R ((scaledClosedCubeSet Q ρ).indicator energy) =
        cubeAverage R energy :=
    cubeAverage_indicator_scaledClosedCubeSet_eq_cubeAverage_of_cubeSet_subset
      (Q := Q) (R := R) ρ energy hsub
  have hfluxEnergy_indicator :
      CoarseCaccioppoliFluxEnergyControls R a s flux
        ((scaledClosedCubeSet Q ρ).indicator energy) :=
    hfluxEnergy.indicator_scaledClosedCubeSet_of_cubeSet_subset ρ hsub
  have hBgCent_indicator :
      0 ≤
        coarseCaccioppoliCenteredCutoffSize R s (scalarCutoffGradientField η) Acirc1 AcircS
          (Real.sqrt (cubeAverage R ((scaledClosedCubeSet Q ρ).indicator energy)))
          (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C) := by
    simpa [havg] using hBgCent
  have hGcirc1_indicator : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 *
          Real.sqrt (cubeAverage R ((scaledClosedCubeSet Q ρ).indicator energy)) := by
    intro i N
    simpa [havg] using hGcirc1 i N
  have hGcircS_indicator : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤
          AcircS *
            Real.sqrt (cubeAverage R ((scaledClosedCubeSet Q ρ).indicator energy)) := by
    intro i N
    simpa [havg] using hGcircS i N
  exact
    abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_parentQuantitativeCutoff_on_descendant_vectorFullDualFullCirc
      (Q := Q) (R := R) (j := j) hR (a := a) (s := s) (flux := flux) (u := u)
      (G := G) (energy := (scaledClosedCubeSet Q ρ).indicator energy) (η := η)
      (Acirc1 := Acirc1) (AcircS := AcircS) (C := C)
      hs0 hs1 hfluxMem hu hG hfluxEnergy_indicator hB hAcirc1 hAcircS hBgConst
      hBgCent_indicator hC hfull hGcirc1_indicator hGcircS_indicator

/-- Buffered support-localized local exact-RHS estimate using the
full-dual/full-circ route. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_indicator_of_parentQuantitativeCutoff_on_descendant_of_support_buffer_vectorFullDualFullCirc
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    (a : CoeffField d) (s : ℝ) {ρ₁ ρ₂ ρ : ℝ}
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (energy : Vec d → ℝ) (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    {Acirc1 AcircS C : ℝ}
    (hgap : cubeScaleFactor R ≤ (ρ - ρ₂) * cubeRadius Q)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls R a s flux energy)
    (hB :
      0 ≤ quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
    (hAcirc1 : 0 ≤ Acirc1)
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
    (hfull : ∀ N : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate R C (cubeFluctuation R u) G N)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 * Real.sqrt (cubeAverage R energy))
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS * Real.sqrt (cubeAverage R energy)) :
    |cubeAverage R (fun x => vecDot (flux x) (u x • scalarCutoffGradientField η x))| ≤
      coarseCaccioppoliFluxEnergyExactRhs R a s u (scalarCutoffGradientField η)
        ((scaledClosedCubeSet Q ρ).indicator energy)
        Acirc1 AcircS
        (quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
        ((Fintype.card (Fin d) : ℝ) * C) := by
  by_cases hinter : ∃ y ∈ cubeSet R, y ∈ scaledClosedCubeSet Q ρ₂
  · have hsub : cubeSet R ⊆ scaledClosedCubeSet Q ρ :=
      cubeSet_subset_scaledClosedCubeSet_of_intersects_scaledClosedCubeSet_of_scaleFactor_le_gap
        (Q := Q) (R := R) (ρinner := ρ₂) (ρouter := ρ) hgap hinter
    exact
      abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_indicator_of_parentQuantitativeCutoff_on_descendant_of_cubeSet_subset_vectorFullDualFullCirc
        (Q := Q) (R := R) (j := j) hR (a := a) (s := s) (ρ := ρ)
        (flux := flux) (u := u) (G := G) (energy := energy) (η := η)
        (Acirc1 := Acirc1) (AcircS := AcircS) (C := C)
        hsub hs0 hs1 hfluxMem hu hG hfluxEnergy hB hAcirc1 hAcircS hBgConst hBgCent
        hC hfull hGcirc1 hGcircS
  · have hout : ∀ x ∈ cubeSet R, x ∉ scaledClosedCubeSet Q ρ₂ := by
      intro x hxR hxρ₂
      exact hinter ⟨x, hxR, hxρ₂⟩
    exact
      abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_indicator_of_parentQuantitativeCutoff_on_descendant_of_forall_notMem_scaledClosedCubeSet
        (Q := Q) (R := R) (a := a) (s := s) (ρ := ρ)
        (flux := flux) (u := u) (energy := energy) (η := η)
        (Acirc1 := Acirc1) (AcircS := AcircS)
        (B := quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2))
        (C := (Fintype.card (Fin d) : ℝ) * C)
        hout hs0 hAcirc1 hAcircS hB
        (mul_nonneg (by positivity) hC)

/-- Exact local Caccioppoli estimate on a cube using the arbitrary-center local
canonical cutoff and the full-dual/full-circ route. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_localCanonicalCutoff_on_cube_vectorFullDualFullCirc
    {d : ℕ} (Q R : TriadicCube d) (center : Vec d)
    (a : CoeffField d) (s : ℝ) {rhoInner rhoOuter : ℝ}
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (energy : Vec d → ℝ)
    {Acirc1 AcircS C : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls R a s flux energy)
    (hB :
      0 ≤
        quantitativeCubeCutoffHessianConst d /
          (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
    (hAcirc1 : 0 ≤ Acirc1)
    (hAcircS : 0 ≤ AcircS)
    (hBgConst :
      0 ≤
        coarseCaccioppoliConstantCutoffSize R u
          (scalarCutoffGradientField
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
          (quantitativeCubeCutoffHessianConst d /
            (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2)))
    (hBgCent :
      0 ≤
        coarseCaccioppoliCenteredCutoffSize R s
          (scalarCutoffGradientField
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
          Acirc1 AcircS (Real.sqrt (cubeAverage R energy))
          (quantitativeCubeCutoffHessianConst d /
            (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C))
    (hC : 0 ≤ C)
    (hfull : ∀ N : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate R C (cubeFluctuation R u) G N)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 * Real.sqrt (cubeAverage R energy))
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS * Real.sqrt (cubeAverage R energy)) :
    |cubeAverage R
        (fun x =>
          vecDot (flux x)
            (u x •
              scalarCutoffGradientField
                (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) x))| ≤
      coarseCaccioppoliFluxEnergyExactRhs R a s u
        (scalarCutoffGradientField
          (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
        energy Acirc1 AcircS
        (quantitativeCubeCutoffHessianConst d /
          (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
        ((Fintype.card (Fin d) : ℝ) * C) := by
  have hξLp :
      MeasureTheory.MemLp
        (scalarCutoffGradientField
          (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
        ∞ (normalizedCubeMeasure R) :=
    coarseCaccioppoliLocalCanonicalFun_memLp_top_gradientField_on_cube
      Q R center hinner hinnerOuter
  exact
    abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_vectorFullDualFullCirc
      (Q := R) (a := a) (s := s) (flux := flux) (u := u) (G := G)
      (ξ := scalarCutoffGradientField
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
      (energy := energy) (Acirc1 := Acirc1) (AcircS := AcircS)
      (B := quantitativeCubeCutoffHessianConst d /
        (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
      (C := C) hs0 hs1 hfluxMem hu hG hξLp hfluxEnergy hB hAcirc1 hAcircS
      hBgConst hBgCent hC hfull
      (fun i =>
        contDiff_scalarCutoffGradientField_component
          (coarseCaccioppoliLocalCanonicalFun_smooth Q center hinner hinnerOuter) i)
      (coarseCaccioppoliLocalCanonicalFun_component_fderiv_bound_on_cubeSet
        Q R center hinner hinnerOuter)
      hGcirc1 hGcircS

/-- Local exact-RHS estimate for the arbitrary-center canonical cutoff, with
the RHS energy localized to a larger local cube, on the contained branch of
the full-dual/full-circ route. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_indicator_of_localCanonicalCutoff_on_cube_of_cubeSet_subset_vectorFullDualFullCirc
    {d : ℕ} {Q R : TriadicCube d} (center : Vec d)
    (a : CoeffField d) (s : ℝ) {rhoInner rhoOuter rho : ℝ}
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (energy : Vec d → ℝ)
    {Acirc1 AcircS C : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (hsub : cubeSet R ⊆ coarseCaccioppoliLocalClosedCube Q center rho)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls R a s flux energy)
    (hB :
      0 ≤
        quantitativeCubeCutoffHessianConst d /
          (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
    (hAcirc1 : 0 ≤ Acirc1)
    (hAcircS : 0 ≤ AcircS)
    (hBgConst :
      0 ≤
        coarseCaccioppoliConstantCutoffSize R u
          (scalarCutoffGradientField
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
          (quantitativeCubeCutoffHessianConst d /
            (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2)))
    (hBgCent :
      0 ≤
        coarseCaccioppoliCenteredCutoffSize R s
          (scalarCutoffGradientField
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
          Acirc1 AcircS (Real.sqrt (cubeAverage R energy))
          (quantitativeCubeCutoffHessianConst d /
            (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C))
    (hC : 0 ≤ C)
    (hfull : ∀ N : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate R C (cubeFluctuation R u) G N)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 * Real.sqrt (cubeAverage R energy))
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS * Real.sqrt (cubeAverage R energy)) :
    |cubeAverage R
        (fun x =>
          vecDot (flux x)
            (u x •
              scalarCutoffGradientField
                (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) x))| ≤
      coarseCaccioppoliFluxEnergyExactRhs R a s u
        (scalarCutoffGradientField
          (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
        ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)
        Acirc1 AcircS
        (quantitativeCubeCutoffHessianConst d /
          (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
        ((Fintype.card (Fin d) : ℝ) * C) := by
  have havg :
      cubeAverage R ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy) =
        cubeAverage R energy :=
    cubeAverage_indicator_coarseCaccioppoliLocalClosedCube_eq_cubeAverage_of_cubeSet_subset
      (Q := Q) (R := R) center rho energy hsub
  have hfluxEnergy_indicator :
      CoarseCaccioppoliFluxEnergyControls R a s flux
        ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy) :=
    hfluxEnergy.indicator_coarseCaccioppoliLocalClosedCube_of_cubeSet_subset
      center rho hsub
  have hBgCent_indicator :
      0 ≤
        coarseCaccioppoliCenteredCutoffSize R s
          (scalarCutoffGradientField
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
          Acirc1 AcircS
          (Real.sqrt
            (cubeAverage R
              ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)))
          (quantitativeCubeCutoffHessianConst d /
            (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C) := by
    simpa [havg] using hBgCent
  have hGcirc1_indicator : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 *
          Real.sqrt
            (cubeAverage R
              ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)) := by
    intro i N
    simpa [havg] using hGcirc1 i N
  have hGcircS_indicator : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤
          AcircS *
            Real.sqrt
              (cubeAverage R
                ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)) := by
    intro i N
    simpa [havg] using hGcircS i N
  exact
    abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_localCanonicalCutoff_on_cube_vectorFullDualFullCirc
      (Q := Q) (R := R) (center := center) (a := a) (s := s)
      (rhoInner := rhoInner) (rhoOuter := rhoOuter)
      (flux := flux) (u := u) (G := G)
      (energy := (coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)
      (Acirc1 := Acirc1) (AcircS := AcircS) (C := C)
      hinner hinnerOuter hs0 hs1 hfluxMem hu hG hfluxEnergy_indicator hB
      hAcirc1 hAcircS hBgConst hBgCent_indicator hC hfull hGcirc1_indicator
      hGcircS_indicator

/-- Buffered local exact-RHS estimate for the arbitrary-center canonical
cutoff using the full-dual/full-circ route. -/
theorem
    abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_indicator_of_localCanonicalCutoff_on_descendant_of_support_buffer_vectorFullDualFullCirc
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (_hR : R ∈ descendantsAtDepth Q j)
    (center : Vec d) (a : CoeffField d) (s : ℝ) {rhoInner rhoOuter rho : ℝ}
    (flux : Vec d → Vec d) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (energy : Vec d → ℝ)
    {Acirc1 AcircS C : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (hgap : cubeScaleFactor R ≤ (rho - rhoOuter) * (cubeRadius Q / 3))
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hG : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls R a s flux energy)
    (hB :
      0 ≤
        quantitativeCubeCutoffHessianConst d /
          (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
    (hAcirc1 : 0 ≤ Acirc1)
    (hAcircS : 0 ≤ AcircS)
    (hBgConst :
      0 ≤
        coarseCaccioppoliConstantCutoffSize R u
          (scalarCutoffGradientField
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
          (quantitativeCubeCutoffHessianConst d /
            (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2)))
    (hBgCent :
      0 ≤
        coarseCaccioppoliCenteredCutoffSize R s
          (scalarCutoffGradientField
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
          Acirc1 AcircS
          (Real.sqrt (cubeAverage R energy))
          (quantitativeCubeCutoffHessianConst d /
            (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C))
    (hC : 0 ≤ C)
    (hfull : ∀ N : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate R C (cubeFluctuation R u) G N)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 * Real.sqrt (cubeAverage R energy))
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS * Real.sqrt (cubeAverage R energy)) :
    |cubeAverage R
        (fun x =>
          vecDot (flux x)
            (u x •
              scalarCutoffGradientField
                (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) x))| ≤
      coarseCaccioppoliFluxEnergyExactRhs R a s u
        (scalarCutoffGradientField
          (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
        ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)
        Acirc1 AcircS
        (quantitativeCubeCutoffHessianConst d /
          (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
        ((Fintype.card (Fin d) : ℝ) * C) := by
  by_cases hinter :
      ∃ y ∈ cubeSet R, y ∈ coarseCaccioppoliLocalClosedCube Q center rhoOuter
  · have hsub : cubeSet R ⊆ coarseCaccioppoliLocalClosedCube Q center rho :=
      cubeSet_subset_coarseCaccioppoliLocalClosedCube_of_intersects_of_scaleFactor_le_gap
        (Q := Q) (R := R) (center := center)
        (rhoInner := rhoOuter) (rhoOuter := rho) hgap hinter
    exact
      abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_indicator_of_localCanonicalCutoff_on_cube_of_cubeSet_subset_vectorFullDualFullCirc
        (Q := Q) (R := R) (center := center) (a := a) (s := s)
        (rhoInner := rhoInner) (rhoOuter := rhoOuter) (rho := rho)
        (flux := flux) (u := u) (G := G) (energy := energy)
        (Acirc1 := Acirc1) (AcircS := AcircS) (C := C)
        hinner hinnerOuter hsub hs0 hs1 hfluxMem hu hG hfluxEnergy hB
        hAcirc1 hAcircS hBgConst hBgCent hC hfull hGcirc1 hGcircS
  · have hout :
        ∀ x ∈ cubeSet R, x ∉ coarseCaccioppoliLocalClosedCube Q center rhoOuter := by
      intro x hxR hxrhoOuter
      exact hinter ⟨x, hxR, hxrhoOuter⟩
    exact
      abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_indicator_of_localCanonicalCutoff_on_cube_of_forall_notMem_localClosedCube
        (Q := Q) (R := R) (center := center) (a := a) (s := s)
        (rhoInner := rhoInner) (rhoOuter := rhoOuter) (rho := rho)
        (flux := flux) (u := u) (energy := energy)
        (Acirc1 := Acirc1) (AcircS := AcircS)
        (B := quantitativeCubeCutoffHessianConst d /
          (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
        (C := (Fintype.card (Fin d) : ℝ) * C)
        hinner hinnerOuter hout hs0 hAcirc1 hAcircS hB
        (mul_nonneg (by positivity) hC)

end

end Homogenization
