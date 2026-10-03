/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.QuantitativeCutoffInputs.Setup.ConstantCoeff

/-! # Canonical -/

@[expose] public section

namespace Homogenization

/-!
# Quantitative cutoff inputs: canonical cutoff packages
-/

noncomputable section

open scoped ENNReal

theorem coarseCaccioppoliQuantitativeCutoffHessianBound_nonneg {d : ℕ}
    (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ} (η : QuantitativeCubeCutoff Q ρ₁ ρ₂) :
    0 ≤ coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ := by
  exact le_trans (norm_nonneg _) (η.hessian_bound (cubeCenter Q))

theorem coarseCaccioppoliQuantitativeCutoffHessianBound_pos {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ} (hlt : ρ₁ < ρ₂) :
    0 < coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ := by
  unfold coarseCaccioppoliQuantitativeCutoffHessianBound
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hmax :
      0 <
        max 1 (max smoothTransitionProfile.derivBound
          smoothTransitionProfile.secondDerivBound) := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have hconst : 0 < quantitativeCubeCutoffHessianConst d := by
    unfold quantitativeCubeCutoffHessianConst
    exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 8) (sq_pos_of_pos hd))
      (sq_pos_of_pos hmax)
  have hgap :
      0 < (ρ₂ - ρ₁) * cubeRadius Q := by
    exact mul_pos (sub_pos.mpr hlt) (cubeRadius_pos Q)
  exact div_pos hconst (sq_pos_of_pos hgap)

/-- Canonical quantitative cube cutoff at an admissible radius pair
`(ρ₁, ρ₂)` with `ρ₁ ≥ 1/3` and `ρ₁ < ρ₂`. -/
noncomputable def coarseCaccioppoliCanonicalQuantitativeCutoff {d : ℕ}
    (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ}
    (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂) :
    QuantitativeCubeCutoff Q ρ₁ ρ₂ :=
  QuantitativeCubeCutoff.canonical Q ρ₁ ρ₂
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3) hρ₁) hlt

theorem
    coarseCaccioppoliCanonicalQuantitativeCutoff_tsupport_subset_openCubeSet_of_lt_one
    {d : ℕ} (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ}
    (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂) (hρ₂_lt_one : ρ₂ < 1) :
    tsupport (coarseCaccioppoliCanonicalQuantitativeCutoff Q hρ₁ hlt) ⊆
      openCubeSet Q := by
  have hρ₂_nonneg : 0 ≤ ρ₂ := by
    exact le_trans (by norm_num : 0 ≤ (1 / 3 : ℝ)) <|
      le_trans hρ₁ (le_of_lt hlt)
  exact
    QuantitativeCubeCutoff.tsupport_subset_openCubeSet_of_lt_one
      (η := coarseCaccioppoliCanonicalQuantitativeCutoff Q hρ₁ hlt)
      hρ₂_nonneg hρ₂_lt_one

theorem
    coarseCaccioppoliCanonicalQuantitativeCutoff_tsupport_subset_openCubeSet_on_radiusSequence
    {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    tsupport
        (coarseCaccioppoliCanonicalQuantitativeCutoff Q
          (coarseCaccioppoliRadiusSequence_mem_Icc n).1
          (coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self n))) ⊆
      openCubeSet Q := by
  exact
    coarseCaccioppoliCanonicalQuantitativeCutoff_tsupport_subset_openCubeSet_of_lt_one
      Q (coarseCaccioppoliRadiusSequence_mem_Icc n).1
      (coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self n))
      (coarseCaccioppoliRadiusSequence_lt_one (n + 1))

/-- A quantitative cube cutoff upgrades the external testing/flux/Poincare
hypotheses to the split canonical local analytic inputs used by the final
coarse Caccioppoli wrappers.  The cutoff contributes the vector field
`ξ = ∇η`, its `L^∞` control, and the component derivative bound. -/
theorem CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs.of_quantitativeCubeCutoff
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ)
    (k h : ℝ → ℝ → ℝ) (F : ℝ → ℝ)
    (flux : ℝ → ℝ → Vec d → Vec d) (u g : ℝ → ℝ → Vec d → ℝ)
    (energy : ℝ → ℝ -> Vec d → ℝ)
    (η : ∀ ρ₁ ρ₂ : ℝ, QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (htest :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        F ρ₁ ≤
          |cubeAverage Q
            (fun x =>
              vecDot (flux ρ₁ ρ₂ x)
                ((u ρ₁ ρ₂ x) • scalarCutoffGradientField (η ρ₁ ρ₂) x))|)
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (energy ρ₁ ρ₂) = F ρ₂)
    (hfluxMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp (flux ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (huMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp (u ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hgMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp (g ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s (flux ρ₁ ρ₂) (energy ρ₁ ρ₂))
    (hBgConst :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤
          coarseCaccioppoliConstantCutoffSize Q (u ρ₁ ρ₂)
            (scalarCutoffGradientField (η ρ₁ ρ₂))
            (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂))
    (hBgCent :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤
          coarseCaccioppoliCenteredCutoffSize Q s
            (scalarCutoffGradientField (η ρ₁ ρ₂))
            (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
            (Real.sqrt (cubeAverage Q (energy ρ₁ ρ₂)))
            (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C)
    (hC : 0 ≤ C)
    (hAcirc1_nonneg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤ Acirc1 ρ₁ ρ₂)
    (hAcircS_nonneg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤ AcircS ρ₁ ρ₂)
    (hproj :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C
          (cubeFluctuation Q (u ρ₁ ρ₂)) (g ρ₁ ρ₂) N)
    (hgCirc1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (g ρ₁ ρ₂) ≤
          Acirc1 ρ₁ ρ₂ * Real.sqrt (cubeAverage Q (energy ρ₁ ρ₂)))
    (hgCircS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (g ρ₁ ρ₂) ≤
          AcircS ρ₁ ρ₂ * Real.sqrt (cubeAverage Q (energy ρ₁ ρ₂)))
    (hU :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeLpNorm Q (2 : ℝ≥0∞) (u ρ₁ ρ₂) ≤ U ρ₁ ρ₂)
    (hA1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        Acirc1 ρ₁ ρ₂ ≤ A1 ρ₁ ρ₂)
    (hAS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂) :
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs Q a s C
      k h F flux u g
      (fun ρ₁ ρ₂ => scalarCutoffGradientField (η ρ₁ ρ₂))
      energy Acirc1 AcircS
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      U
      (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      A1 AS := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  let ηρ : QuantitativeCubeCutoff Q ρ₁ ρ₂ := η ρ₁ ρ₂
  have hB_nonneg :
      0 ≤ coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ :=
    coarseCaccioppoliQuantitativeCutoffHessianBound_nonneg Q ηρ
  have hscalar :
      CoarseCaccioppoliScalarCutoffControls Q s (u ρ₁ ρ₂) (g ρ₁ ρ₂)
        (scalarCutoffGradientField ηρ) (energy ρ₁ ρ₂)
        (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C := by
    exact
      CoarseCaccioppoliScalarCutoffControls.of_quantitativeCubeCutoff
        (Q := Q) (s := s) (u := u ρ₁ ρ₂) (g := g ρ₁ ρ₂) (energy := energy ρ₁ ρ₂)
        (η := ηρ) (Acirc1 := Acirc1 ρ₁ ρ₂) (AcircS := AcircS ρ₁ ρ₂) (C := C)
        hB_nonneg
        (by
          simpa [ηρ, coarseCaccioppoliQuantitativeCutoffHessianBound] using
            hBgConst hρ₁ hlt hρ₂)
        (by
          simpa [ηρ, coarseCaccioppoliQuantitativeCutoffHessianBound] using
            hBgCent hρ₁ hlt hρ₂)
        hC
        (hproj hρ₁ hlt hρ₂) (hgCirc1 hρ₁ hlt hρ₂) (hgCircS hρ₁ hlt hρ₂)
  exact
    ⟨htest hρ₁ hlt hρ₂, henergyAvg hρ₁ hlt hρ₂, hfluxMem hρ₁ hlt hρ₂,
      huMem hρ₁ hlt hρ₂, hgMem hρ₁ hlt hρ₂,
      quantitativeCubeCutoff_memLp_top_gradientField Q ηρ,
      hfluxEnergy hρ₁ hlt hρ₂, hscalar, hB_nonneg,
      hAcirc1_nonneg hρ₁ hlt hρ₂, hAcircS_nonneg hρ₁ hlt hρ₂,
      hU hρ₁ hlt hρ₂,
      quantitativeCubeCutoff_cubeLpNorm_infty_gradientField_le Q ηρ,
      le_rfl, hA1 hρ₁ hlt hρ₂, hAS hρ₁ hlt hρ₂⟩

/-- Vector-Poincare version of
`CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs.of_quantitativeCubeCutoff`.
The cutoff again supplies `ξ = ∇η`; the analytic package keeps the vector
cutoff controls rather than scalarizing to one gradient component. -/
theorem CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalVectorAnalyticInputs.of_quantitativeCubeCutoff
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ)
    (k h : ℝ → ℝ → ℝ) (F : ℝ → ℝ)
    (flux : ℝ → ℝ → Vec d → Vec d) (u : ℝ → ℝ → Vec d → ℝ)
    (G : ℝ → ℝ → Vec d → Vec d)
    (energy : ℝ → ℝ -> Vec d → ℝ)
    (η : ∀ ρ₁ ρ₂ : ℝ, QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (htest :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        F ρ₁ ≤
          |cubeAverage Q
            (fun x =>
              vecDot (flux ρ₁ ρ₂ x)
                ((u ρ₁ ρ₂ x) • scalarCutoffGradientField (η ρ₁ ρ₂) x))|)
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (energy ρ₁ ρ₂) = F ρ₂)
    (hfluxMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp (flux ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (huMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp (u ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hGMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ i : Fin d,
        MeasureTheory.MemLp (fun x => G ρ₁ ρ₂ x i) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q))
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s (flux ρ₁ ρ₂) (energy ρ₁ ρ₂))
    (hvector :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliVectorCutoffControls Q s (u ρ₁ ρ₂) (G ρ₁ ρ₂)
          (scalarCutoffGradientField (η ρ₁ ρ₂)) (energy ρ₁ ρ₂)
          (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C)
    (hAcirc1_nonneg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤ Acirc1 ρ₁ ρ₂)
    (hAcircS_nonneg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤ AcircS ρ₁ ρ₂)
    (hU :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeLpNorm Q (2 : ℝ≥0∞) (u ρ₁ ρ₂) ≤ U ρ₁ ρ₂)
    (hA1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        Acirc1 ρ₁ ρ₂ ≤ A1 ρ₁ ρ₂)
    (hAS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂) :
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalVectorAnalyticInputs Q a s C
      k h F flux u G
      (fun ρ₁ ρ₂ => scalarCutoffGradientField (η ρ₁ ρ₂))
      energy Acirc1 AcircS
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      U
      (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      A1 AS := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  let ηρ : QuantitativeCubeCutoff Q ρ₁ ρ₂ := η ρ₁ ρ₂
  have hB_nonneg :
      0 ≤ coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ :=
    coarseCaccioppoliQuantitativeCutoffHessianBound_nonneg Q ηρ
  exact
    ⟨htest hρ₁ hlt hρ₂, henergyAvg hρ₁ hlt hρ₂, hfluxMem hρ₁ hlt hρ₂,
      huMem hρ₁ hlt hρ₂, hGMem hρ₁ hlt hρ₂,
      quantitativeCubeCutoff_memLp_top_gradientField Q ηρ,
      hfluxEnergy hρ₁ hlt hρ₂, hvector hρ₁ hlt hρ₂, hB_nonneg,
      hAcirc1_nonneg hρ₁ hlt hρ₂, hAcircS_nonneg hρ₁ hlt hρ₂,
      hU hρ₁ hlt hρ₂,
      quantitativeCubeCutoff_cubeLpNorm_infty_gradientField_le Q ηρ,
      le_rfl, hA1 hρ₁ hlt hρ₂, hAS hρ₁ hlt hρ₂⟩

/-- Harmonic-family builder for the vector canonical analytic inputs.  The
weak-testing bridge supplies the testing inequality from the weighted energy
lower bound, while the caller supplies the vector cutoff controls. -/
theorem
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalVectorAnalyticInputs.of_quantitativeCubeCutoff_of_aHarmonicFamily
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ) {lam Lam : ℝ}
    (k h : ℝ → ℝ → ℝ) (F : ℝ → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (G : ℝ → ℝ → Vec d → Vec d)
    (η : ∀ ρ₁ ρ₂ : ℝ, QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hlower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        F ρ₁ ≤
          cubeAverage Q
            (fun x => η ρ₁ ρ₂ x * scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hη_tsupport :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        tsupport (η ρ₁ ρ₂) ⊆ openCubeSet Q)
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) = F ρ₂)
    (hfluxMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (huMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp (fun x => (w ρ₁ ρ₂).toH1 x)
          (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hGMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ i : Fin d,
        MeasureTheory.MemLp (fun x => G ρ₁ ρ₂ x i) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q))
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hvector :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliVectorCutoffControls Q s (fun x => (w ρ₁ ρ₂).toH1 x)
          (G ρ₁ ρ₂) (scalarCutoffGradientField (η ρ₁ ρ₂))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
          (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C)
    (hAcirc1_nonneg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤ Acirc1 ρ₁ ρ₂)
    (hAcircS_nonneg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        0 ≤ AcircS ρ₁ ρ₂)
    (hU :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => (w ρ₁ ρ₂).toH1 x) ≤ U ρ₁ ρ₂)
    (hA1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        Acirc1 ρ₁ ρ₂ ≤ A1 ρ₁ ρ₂)
    (hAS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂) :
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalVectorAnalyticInputs Q a s C
      k h F
      (fun ρ₁ ρ₂ x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
      (fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1 x)
      G
      (fun ρ₁ ρ₂ => scalarCutoffGradientField (η ρ₁ ρ₂))
      (fun ρ₁ ρ₂ x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
      Acirc1 AcircS
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      U
      (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      A1 AS := by
  refine
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalVectorAnalyticInputs.of_quantitativeCubeCutoff
      Q a s C k h F
      (fun ρ₁ ρ₂ x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
      (fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1 x)
      G
      (fun ρ₁ ρ₂ x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
      η Acirc1 AcircS U A1 AS ?_ henergyAvg hfluxMem huMem hGMem
      hfluxEnergy hvector hAcirc1_nonneg hAcircS_nonneg hU hA1 hAS
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  exact
    le_abs_cubeAverage_vecDot_flux_scalarCutoffGradientField_of_aHarmonicFunction_of_le_cubeAverage_mul_scalarVariationEnergyIntegrand
      Q a (w ρ₁ ρ₂) hEll (η ρ₁ ρ₂).smooth (η ρ₁ ρ₂).hasCompactSupport
      (hη_tsupport hρ₁ hlt hρ₂) (hlower hρ₁ hlt hρ₂)

end

end Homogenization
