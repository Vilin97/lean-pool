/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.QuantitativeCutoff
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.LocalPatchCutoff
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.LocalizedEnergyProfile
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.SingleCubeRhs
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.SplitPairing.Scalar
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.SplitPairing.Vector

/-! # Split -/

namespace Homogenization

/-!
# Local energy estimate: split exact RHS bridge
-/

noncomputable section

open scoped BigOperators ENNReal

/-- The split local Caccioppoli estimate with all flux-side Besov and average
hypotheses supplied by the coarse-Poincare flux energy-control interface.  The
remaining hypotheses are exactly the scalar projected-Poincare/cutoff-product
side and the elementary cutoff-size bounds. -/
theorem abs_cubeAverage_vecDot_scalar_smul_le_split_of_fluxEnergyControl_of_contDiff_component_bound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (flux : Vec d → Vec d) (u g : Vec d → ℝ) (ξ : Vec d → Vec d)
    (energy : Vec d → ℝ)
    {Acirc1 AcircS B C BgConst BgCent : ℝ}
    (hB : 0 ≤ B) (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBgConst : 0 ≤ BgConst) (hBgCent : 0 ≤ BgCent)
    (hC : 0 ≤ C)
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
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C (cubeFluctuation Q u) g N)
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hgCirc1 : ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤
        Acirc1 * Real.sqrt (cubeAverage Q energy))
    (hgCircS : ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤
        AcircS * Real.sqrt (cubeAverage Q energy))
    (hBgConst_bound :
      cubeLpNorm Q (2 : ℝ≥0∞) u *
          (B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ ξ) ≤ BgConst)
    (hBgCent_bound :
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (Acirc1 * Real.sqrt (cubeAverage Q energy)))) +
        cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
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
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (Acirc1 * E)))) +
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
    abs_cubeAverage_vecDot_scalar_smul_le_split_collapsed_sharp_note_terms_of_contDiff_component_bound
      (Q := Q) (s := s) (flux := flux) (u := u) (g := g) (ξ := ξ)
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
      hB hs0 hs1 hfluxMem hu hg hξLp hBgConst hBgCent
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hC havgFlux
      (fun N =>
        coarseCaccioppoli_flux_qone_partialBound_of_cubeAverageEnergyControl
          Q a (1 : ℝ) (by norm_num) flux energy N henergy_nonneg henergy_int hfluxCtrl hsum1)
      (fun N =>
        coarseCaccioppoli_flux_qone_partialBound_of_cubeAverageEnergyControl
          Q a s hs0 flux energy N henergy_nonneg henergy_int hfluxCtrl hsumS)
      hproj hξ hderiv hgCirc1 hgCircS hBgConst_bound hBgCent_bound

theorem abs_cubeAverage_vecDot_scalar_smul_le_split_of_fluxEnergyControl_of_contDiff_component_vector_bound
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
    (hC : 0 ≤ C) (hAcircS : 0 ≤ AcircS)
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
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C (cubeFluctuation Q u) G N)
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
    abs_cubeAverage_vecDot_scalar_smul_le_split_collapsed_sharp_note_terms_of_contDiff_component_vector_effective_constant
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
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hC hBcircS_nonneg havgFlux
      (fun N =>
        coarseCaccioppoli_flux_qone_partialBound_of_cubeAverageEnergyControl
          Q a (1 : ℝ) (by norm_num) flux energy N henergy_nonneg henergy_int hfluxCtrl hsum1)
      (fun N =>
        coarseCaccioppoli_flux_qone_partialBound_of_cubeAverageEnergyControl
          Q a s hs0 flux energy N henergy_nonneg henergy_int hfluxCtrl hsumS)
      hproj hξ hderiv hGcirc1 hGcircS hBgConst_bound hBgCent_bound

/-- Version of the flux-energy bridge using the exact cutoff sizes instead of
separate upper-bound hypotheses for `BgConst` and `BgCent`.

This is the last purely local bookkeeping step before the note-facing
single-cube estimate: the remaining work is to dominate these exact cutoff
sizes by the Chapter-3 radius/height coefficients. -/
theorem abs_cubeAverage_vecDot_scalar_smul_le_split_of_fluxEnergyControl_of_exact_cutoff_sizes
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (flux : Vec d → Vec d) (u g : Vec d → ℝ) (ξ : Vec d → Vec d)
    (energy : Vec d → ℝ)
    {Acirc1 AcircS B C : ℝ}
    (hB : 0 ≤ B) (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hBgConst :
      0 ≤ coarseCaccioppoliConstantCutoffSize Q u ξ B)
    (hBgCent :
      0 ≤
        coarseCaccioppoliCenteredCutoffSize Q s ξ Acirc1 AcircS
          (Real.sqrt (cubeAverage Q energy)) B C)
    (hC : 0 ≤ C)
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
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C (cubeFluctuation Q u) g N)
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hgCirc1 : ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤
        Acirc1 * Real.sqrt (cubeAverage Q energy))
    (hgCircS : ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤
        AcircS * Real.sqrt (cubeAverage Q energy)) :
    let E : ℝ := Real.sqrt (cubeAverage Q energy)
    let Aavg : ℝ := Real.sqrt (coarseBBlockNorm Q a)
    let Aflux1 : ℝ :=
      (geometricDiscount (1 : ℝ) 1)⁻¹ *
        Real.rpow (LambdaSq Q (1 : ℝ) (.finite 1) a) (1 / 2 : ℝ)
    let AfluxS : ℝ :=
      (geometricDiscount s 1)⁻¹ *
        Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)
    let BgConst : ℝ := coarseCaccioppoliConstantCutoffSize Q u ξ B
    let BgCent : ℝ := coarseCaccioppoliCenteredCutoffSize Q s ξ Acirc1 AcircS E B C
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      (d : ℝ) *
        (((3 : ℝ) ^ ((d : ℝ) + 1) *
          (cubeBesovScaleWeight (-1) Q * (Aflux1 * E))) * BgConst) +
        ((d : ℝ) *
          ((Aavg * E) * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (Acirc1 * E)))) +
          (d : ℝ) *
            ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * (AfluxS * E))) *
              (cubeBesovScaleWeight s Q * BgCent)))) := by
  dsimp only
  exact
    abs_cubeAverage_vecDot_scalar_smul_le_split_of_fluxEnergyControl_of_contDiff_component_bound
      (Q := Q) (a := a) (s := s) (flux := flux) (u := u) (g := g) (ξ := ξ)
      (energy := energy) (Acirc1 := Acirc1) (AcircS := AcircS) (B := B) (C := C)
      (BgConst := coarseCaccioppoliConstantCutoffSize Q u ξ B)
      (BgCent :=
        coarseCaccioppoliCenteredCutoffSize Q s ξ Acirc1 AcircS
          (Real.sqrt (cubeAverage Q energy)) B C)
      hB hs0 hs1 hfluxMem hu hg hξLp hBgConst hBgCent hC henergy_nonneg henergy_int
      hfluxCtrl hsum1 hsumS hproj hξ hderiv hgCirc1 hgCircS
      (by rfl)
      (by rfl)

/-- Bundled-hypothesis version of the flux-energy/exact-cutoff bridge. -/
theorem abs_cubeAverage_vecDot_scalar_smul_le_split_of_fluxEnergyControls_of_scalarCutoffControls
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (flux : Vec d → Vec d) (u g : Vec d → ℝ) (ξ : Vec d → Vec d)
    (energy : Vec d → ℝ)
    {Acirc1 AcircS B C : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls Q a s flux energy)
    (hscalar : CoarseCaccioppoliScalarCutoffControls Q s u g ξ energy Acirc1 AcircS B C) :
    let E : ℝ := Real.sqrt (cubeAverage Q energy)
    let Aavg : ℝ := Real.sqrt (coarseBBlockNorm Q a)
    let Aflux1 : ℝ :=
      (geometricDiscount (1 : ℝ) 1)⁻¹ *
        Real.rpow (LambdaSq Q (1 : ℝ) (.finite 1) a) (1 / 2 : ℝ)
    let AfluxS : ℝ :=
      (geometricDiscount s 1)⁻¹ *
        Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)
    let BgConst : ℝ := coarseCaccioppoliConstantCutoffSize Q u ξ B
    let BgCent : ℝ := coarseCaccioppoliCenteredCutoffSize Q s ξ Acirc1 AcircS E B C
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      (d : ℝ) *
        (((3 : ℝ) ^ ((d : ℝ) + 1) *
          (cubeBesovScaleWeight (-1) Q * (Aflux1 * E))) * BgConst) +
        ((d : ℝ) *
          ((Aavg * E) * (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (Acirc1 * E)))) +
          (d : ℝ) *
            ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * (AfluxS * E))) *
              (cubeBesovScaleWeight s Q * BgCent)))) := by
  rcases hfluxEnergy with ⟨henergy_nonneg, henergy_int, hfluxCtrl, hsum1, hsumS⟩
  rcases hscalar with
    ⟨hB, hBgConst, hBgCent, hC, hproj, hξ, hderiv, hgCirc1, hgCircS⟩
  exact
    abs_cubeAverage_vecDot_scalar_smul_le_split_of_fluxEnergyControl_of_exact_cutoff_sizes
      (Q := Q) (a := a) (s := s) (flux := flux) (u := u) (g := g) (ξ := ξ)
      (energy := energy) (Acirc1 := Acirc1) (AcircS := AcircS) (B := B) (C := C)
      hB hs0 hs1 hfluxMem hu hg hξLp hBgConst hBgCent hC henergy_nonneg henergy_int
      hfluxCtrl hsum1 hsumS hproj hξ hderiv hgCirc1 hgCircS

/-- Compact exact-RHS form of the local coarse Caccioppoli bridge. -/
theorem abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_controls
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (flux : Vec d → Vec d) (u g : Vec d → ℝ) (ξ : Vec d → Vec d)
    (energy : Vec d → ℝ)
    {Acirc1 AcircS B C : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hfluxMem : MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hfluxEnergy : CoarseCaccioppoliFluxEnergyControls Q a s flux energy)
    (hscalar : CoarseCaccioppoliScalarCutoffControls Q s u g ξ energy Acirc1 AcircS B C) :
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      coarseCaccioppoliFluxEnergyExactRhs Q a s u ξ energy Acirc1 AcircS B C := by
  simpa [coarseCaccioppoliFluxEnergyExactRhs] using
    abs_cubeAverage_vecDot_scalar_smul_le_split_of_fluxEnergyControls_of_scalarCutoffControls
      (Q := Q) (a := a) (s := s) (flux := flux) (u := u) (g := g) (ξ := ξ)
      (energy := energy) (Acirc1 := Acirc1) (AcircS := AcircS) (B := B) (C := C)
      hs0 hs1 hfluxMem hu hg hξLp hfluxEnergy hscalar

/-- Compact exact-RHS form of the local coarse Caccioppoli bridge, using the
vector projected-Poincare package.  The scalar-facing exact RHS receives the
effective constant `(Fintype.card (Fin d) : ℝ) * C`. -/
theorem abs_cubeAverage_vecDot_scalar_smul_le_fluxEnergyExactRhs_of_vectorControls
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
    (hvector : CoarseCaccioppoliVectorCutoffControls Q s u G ξ energy Acirc1 AcircS B C) :
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      coarseCaccioppoliFluxEnergyExactRhs Q a s u ξ energy Acirc1 AcircS B
        ((Fintype.card (Fin d) : ℝ) * C) := by
  rcases hfluxEnergy with ⟨henergy_nonneg, henergy_int, hfluxCtrl, hsum1, hsumS⟩
  rcases hvector with
    ⟨hB, hAcircS, hBgConst, hBgCent, hC, hproj, hξ, hderiv, hGcirc1, hGcircS⟩
  simpa [coarseCaccioppoliFluxEnergyExactRhs] using
    abs_cubeAverage_vecDot_scalar_smul_le_split_of_fluxEnergyControl_of_contDiff_component_vector_bound
      (Q := Q) (a := a) (s := s) (flux := flux) (u := u) (G := G) (ξ := ξ)
      (energy := energy) (Acirc1 := Acirc1) (AcircS := AcircS) (B := B) (C := C)
      (BgConst := coarseCaccioppoliConstantCutoffSize Q u ξ B)
      (BgCent :=
        coarseCaccioppoliCenteredCutoffSize Q s ξ Acirc1 AcircS
          (Real.sqrt (cubeAverage Q energy)) B ((Fintype.card (Fin d) : ℝ) * C))
      hB hs0 hs1 hfluxMem hu hG hξLp hBgConst hBgCent hC hAcircS
      henergy_nonneg henergy_int hfluxCtrl hsum1 hsumS
      hproj hξ hderiv hGcirc1 hGcircS
      (by rfl)
      (by rfl)

end

end Homogenization
