/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.QuantitativeCutoffInputs.Standard

/-! # Canonical -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-- Canonical-cutoff harmonic analytic inputs with the scalar cutoff package
bundled as `CoarseCaccioppoliScalarCutoffControls`. -/
theorem
    coarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs_at_pair_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_outerRadius_lt_one_of_scalarCutoffControls
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ) {lam Lam : ℝ}
    (F : ℝ → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {ρ₁ ρ₂ : ℝ}
    (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂) (_hρ₂ : ρ₂ ≤ 1)
    (hlower :
      F ρ₁ ≤
        cubeAverage Q
          (fun x =>
            QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x *
              scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (houter : ρ₂ < 1)
    (henergyAvg :
      cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) = F ρ₂)
    (hfluxMem :
      MeasureTheory.MemLp
        (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (huMem :
      MeasureTheory.MemLp (fun x => (w ρ₁ ρ₂).toH1 x)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hgMem :
      MeasureTheory.MemLp (g ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hfluxEnergy :
      CoarseCaccioppoliFluxEnergyControls Q a s
        (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
        (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hscalar :
      CoarseCaccioppoliScalarCutoffControls Q s
        (fun x => (w ρ₁ ρ₂).toH1 x) (g ρ₁ ρ₂)
        (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
        (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
        (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C)
    (_hC : 0 ≤ C)
    (hAcirc1_nonneg : 0 ≤ Acirc1 ρ₁ ρ₂)
    (hAcircS_nonneg : 0 ≤ AcircS ρ₁ ρ₂)
    (hU :
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x => (w ρ₁ ρ₂).toH1 x) ≤ U ρ₁ ρ₂)
    (hA1 : Acirc1 ρ₁ ρ₂ ≤ A1 ρ₁ ρ₂)
    (hAS : AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂) :
    (F ρ₁ ≤
        |cubeAverage Q
          (fun x =>
            vecDot (matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
              ((w ρ₁ ρ₂).toH1 x •
                scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x))|) ∧
      cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) = F ρ₂ ∧
      MeasureTheory.MemLp
        (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      MeasureTheory.MemLp (fun x => (w ρ₁ ρ₂).toH1 x)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      MeasureTheory.MemLp (g ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      MeasureTheory.MemLp
        (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
        (⊤ : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      CoarseCaccioppoliFluxEnergyControls Q a s
        (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
        (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) ∧
      CoarseCaccioppoliScalarCutoffControls Q s
        (fun x => (w ρ₁ ρ₂).toH1 x) (g ρ₁ ρ₂)
        (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
        (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
        (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C ∧
      0 ≤ coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ ∧
      0 ≤ Acirc1 ρ₁ ρ₂ ∧
      0 ≤ AcircS ρ₁ ρ₂ ∧
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x => (w ρ₁ ρ₂).toH1 x) ≤ U ρ₁ ρ₂ ∧
      cubeLpNorm Q (⊤ : ℝ≥0∞)
        (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂)) ≤
          coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂ ∧
      coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ ≤
        coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ ∧
      Acirc1 ρ₁ ρ₂ ≤ A1 ρ₁ ρ₂ ∧
      AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂ := by
  let ηρ : QuantitativeCubeCutoff Q ρ₁ ρ₂ :=
    coarseCaccioppoliCanonicalQuantitativeCutoff Q hρ₁ hlt
  have hB_nonneg :
      0 ≤ coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ :=
    coarseCaccioppoliQuantitativeCutoffHessianBound_nonneg Q ηρ
  have htest :
      F ρ₁ ≤
        |cubeAverage Q
          (fun x =>
            vecDot (matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
              ((w ρ₁ ρ₂).toH1 x •
                scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x))| := by
    simpa [ηρ, coarseCaccioppoliCanonicalQuantitativeCutoff,
      QuantitativeCubeCutoff.canonical] using
      (le_abs_cubeAverage_vecDot_flux_scalarCutoffGradientField_of_aHarmonicFunction_of_le_cubeAverage_mul_scalarVariationEnergyIntegrand
        Q a (w ρ₁ ρ₂) hEll ηρ.smooth ηρ.hasCompactSupport
        (coarseCaccioppoliCanonicalQuantitativeCutoff_tsupport_subset_openCubeSet_of_lt_one
          Q hρ₁ hlt houter)
        hlower)
  have hξ_mem :
      MeasureTheory.MemLp
        (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
        (⊤ : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa [ηρ, coarseCaccioppoliCanonicalQuantitativeCutoff,
      QuantitativeCubeCutoff.canonical] using
      quantitativeCubeCutoff_memLp_top_gradientField Q ηρ
  have hXi :
      cubeLpNorm Q (⊤ : ℝ≥0∞)
        (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂)) ≤
          coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂ := by
    simpa [ηρ, coarseCaccioppoliCanonicalQuantitativeCutoff,
      QuantitativeCubeCutoff.canonical] using!
      quantitativeCubeCutoff_cubeLpNorm_infty_gradientField_le Q ηρ
  exact
    ⟨htest, henergyAvg, hfluxMem, huMem, hgMem, hξ_mem,
      hfluxEnergy, hscalar, hB_nonneg, hAcirc1_nonneg, hAcircS_nonneg,
      hU, hXi, le_rfl, hA1, hAS⟩

/-- Canonical-cutoff harmonic analytic inputs at the concrete Chapter-3 radius
sequence pair `(ρ_n, ρ_{n+1})`, with the strict outer-radius hypothesis
discharged by the sequence itself. -/
theorem
    coarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs_at_radiusSequence_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_scalarCutoffControls
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ) {lam Lam : ℝ}
    (F : ℝ → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (n : ℕ)
    (hlower :
      F (coarseCaccioppoliRadiusSequence n) ≤
        cubeAverage Q
          (fun x =>
            QuantitativeCubeCutoff.canonicalFun Q
              (coarseCaccioppoliRadiusSequence n)
              (coarseCaccioppoliRadiusSequence (n + 1)) x *
              scalarVariationEnergyIntegrand a
                (w (coarseCaccioppoliRadiusSequence n)
                  (coarseCaccioppoliRadiusSequence (n + 1))) x))
    (henergyAvg :
      cubeAverage Q
        (fun x =>
          scalarVariationEnergyIntegrand a
            (w (coarseCaccioppoliRadiusSequence n)
              (coarseCaccioppoliRadiusSequence (n + 1))) x) =
        F (coarseCaccioppoliRadiusSequence (n + 1)))
    (hfluxMem :
      MeasureTheory.MemLp
        (fun x =>
          matVecMul (a x)
            ((w (coarseCaccioppoliRadiusSequence n)
              (coarseCaccioppoliRadiusSequence (n + 1))).toH1.grad x))
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (huMem :
      MeasureTheory.MemLp
        (fun x =>
          (w (coarseCaccioppoliRadiusSequence n)
            (coarseCaccioppoliRadiusSequence (n + 1))).toH1 x)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hgMem :
      MeasureTheory.MemLp
        (g (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)))
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hfluxEnergy :
      CoarseCaccioppoliFluxEnergyControls Q a s
        (fun x =>
          matVecMul (a x)
            ((w (coarseCaccioppoliRadiusSequence n)
              (coarseCaccioppoliRadiusSequence (n + 1))).toH1.grad x))
        (fun x =>
          scalarVariationEnergyIntegrand a
            (w (coarseCaccioppoliRadiusSequence n)
              (coarseCaccioppoliRadiusSequence (n + 1))) x))
    (hscalar :
      CoarseCaccioppoliScalarCutoffControls Q s
        (fun x =>
          (w (coarseCaccioppoliRadiusSequence n)
            (coarseCaccioppoliRadiusSequence (n + 1))).toH1 x)
        (g (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)))
        (scalarCutoffGradientField
          (QuantitativeCubeCutoff.canonicalFun Q
            (coarseCaccioppoliRadiusSequence n)
            (coarseCaccioppoliRadiusSequence (n + 1))))
        (fun x =>
          scalarVariationEnergyIntegrand a
            (w (coarseCaccioppoliRadiusSequence n)
              (coarseCaccioppoliRadiusSequence (n + 1))) x)
        (Acirc1 (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)))
        (AcircS (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)))
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q
          (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1))) C)
    (hC : 0 ≤ C)
    (hAcirc1_nonneg :
      0 ≤ Acirc1 (coarseCaccioppoliRadiusSequence n)
        (coarseCaccioppoliRadiusSequence (n + 1)))
    (hAcircS_nonneg :
      0 ≤ AcircS (coarseCaccioppoliRadiusSequence n)
        (coarseCaccioppoliRadiusSequence (n + 1)))
    (hU :
      cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x =>
          (w (coarseCaccioppoliRadiusSequence n)
            (coarseCaccioppoliRadiusSequence (n + 1))).toH1 x) ≤
        U (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)))
    (hA1 :
      Acirc1 (coarseCaccioppoliRadiusSequence n)
        (coarseCaccioppoliRadiusSequence (n + 1)) ≤
        A1 (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)))
    (hAS :
      AcircS (coarseCaccioppoliRadiusSequence n)
        (coarseCaccioppoliRadiusSequence (n + 1)) ≤
        AS (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1))) :
    (F (coarseCaccioppoliRadiusSequence n) ≤
        |cubeAverage Q
          (fun x =>
            vecDot
              (matVecMul (a x)
                ((w (coarseCaccioppoliRadiusSequence n)
                  (coarseCaccioppoliRadiusSequence (n + 1))).toH1.grad x))
              ((w (coarseCaccioppoliRadiusSequence n)
                (coarseCaccioppoliRadiusSequence (n + 1))).toH1 x •
                scalarCutoffGradientField
                  (QuantitativeCubeCutoff.canonicalFun Q
                    (coarseCaccioppoliRadiusSequence n)
                    (coarseCaccioppoliRadiusSequence (n + 1))) x))|) ∧
      cubeAverage Q
        (fun x =>
          scalarVariationEnergyIntegrand a
            (w (coarseCaccioppoliRadiusSequence n)
              (coarseCaccioppoliRadiusSequence (n + 1))) x) =
        F (coarseCaccioppoliRadiusSequence (n + 1)) ∧
      MeasureTheory.MemLp
        (fun x =>
          matVecMul (a x)
            ((w (coarseCaccioppoliRadiusSequence n)
              (coarseCaccioppoliRadiusSequence (n + 1))).toH1.grad x))
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      MeasureTheory.MemLp
        (fun x =>
          (w (coarseCaccioppoliRadiusSequence n)
            (coarseCaccioppoliRadiusSequence (n + 1))).toH1 x)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      MeasureTheory.MemLp
        (g (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)))
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      MeasureTheory.MemLp
        (scalarCutoffGradientField
          (QuantitativeCubeCutoff.canonicalFun Q
            (coarseCaccioppoliRadiusSequence n)
            (coarseCaccioppoliRadiusSequence (n + 1))))
        (⊤ : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      CoarseCaccioppoliFluxEnergyControls Q a s
        (fun x =>
          matVecMul (a x)
            ((w (coarseCaccioppoliRadiusSequence n)
              (coarseCaccioppoliRadiusSequence (n + 1))).toH1.grad x))
        (fun x =>
          scalarVariationEnergyIntegrand a
            (w (coarseCaccioppoliRadiusSequence n)
              (coarseCaccioppoliRadiusSequence (n + 1))) x) ∧
      CoarseCaccioppoliScalarCutoffControls Q s
        (fun x =>
          (w (coarseCaccioppoliRadiusSequence n)
            (coarseCaccioppoliRadiusSequence (n + 1))).toH1 x)
        (g (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)))
        (scalarCutoffGradientField
          (QuantitativeCubeCutoff.canonicalFun Q
            (coarseCaccioppoliRadiusSequence n)
            (coarseCaccioppoliRadiusSequence (n + 1))))
        (fun x =>
          scalarVariationEnergyIntegrand a
            (w (coarseCaccioppoliRadiusSequence n)
              (coarseCaccioppoliRadiusSequence (n + 1))) x)
        (Acirc1 (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)))
        (AcircS (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)))
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q
          (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1))) C ∧
      0 ≤ coarseCaccioppoliQuantitativeCutoffHessianBound Q
        (coarseCaccioppoliRadiusSequence n)
        (coarseCaccioppoliRadiusSequence (n + 1)) ∧
      0 ≤ Acirc1 (coarseCaccioppoliRadiusSequence n)
        (coarseCaccioppoliRadiusSequence (n + 1)) ∧
      0 ≤ AcircS (coarseCaccioppoliRadiusSequence n)
        (coarseCaccioppoliRadiusSequence (n + 1)) ∧
      cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x =>
          (w (coarseCaccioppoliRadiusSequence n)
            (coarseCaccioppoliRadiusSequence (n + 1))).toH1 x) ≤
        U (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)) ∧
      cubeLpNorm Q (⊤ : ℝ≥0∞)
        (scalarCutoffGradientField
          (QuantitativeCubeCutoff.canonicalFun Q
            (coarseCaccioppoliRadiusSequence n)
            (coarseCaccioppoliRadiusSequence (n + 1)))) ≤
        coarseCaccioppoliQuantitativeCutoffGradientBound Q
          (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)) ∧
      coarseCaccioppoliQuantitativeCutoffHessianBound Q
          (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)) ≤
        coarseCaccioppoliQuantitativeCutoffHessianBound Q
          (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)) ∧
      Acirc1 (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)) ≤
        A1 (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)) ∧
      AcircS (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)) ≤
        AS (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)) := by
  exact
    coarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs_at_pair_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_outerRadius_lt_one_of_scalarCutoffControls
      Q a s C F w g Acirc1 AcircS U A1 AS hEll
      (coarseCaccioppoliRadiusSequence_mem_Icc n).1
      (coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self n))
      (coarseCaccioppoliRadiusSequence_mem_Icc (n + 1)).2
      hlower
      (coarseCaccioppoliRadiusSequence_lt_one (n + 1))
      henergyAvg hfluxMem huMem hgMem hfluxEnergy hscalar hC
      hAcirc1_nonneg hAcircS_nonneg hU hA1 hAS

/-- Canonical-cutoff harmonic analytic inputs with the scalar cutoff package
bundled as `CoarseCaccioppoliScalarCutoffControls`. -/
theorem
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs.of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_outerRadius_lt_one_of_scalarCutoffControls
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ) {lam Lam : ℝ}
    (k h : ℝ → ℝ → ℝ) (F : ℝ → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hlower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) → (hρ₂ : ρ₂ ≤ 1) →
        F ρ₁ ≤
          cubeAverage Q
            (fun x =>
              QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x *
                scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (houter :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) → (hρ₂ : ρ₂ ≤ 1) →
        ρ₂ < 1)
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
    (hgMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp (g ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hscalar :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) → (hρ₂ : ρ₂ ≤ 1) →
        CoarseCaccioppoliScalarCutoffControls Q s
          (fun x => (w ρ₁ ρ₂).toH1 x) (g ρ₁ ρ₂)
          (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
          (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C)
    (hC : 0 ≤ C)
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
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs Q a s C
      k h F
      (fun ρ₁ ρ₂ x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
      (fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1 x)
      g
      (fun ρ₁ ρ₂ => scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
      (fun ρ₁ ρ₂ x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
      Acirc1 AcircS
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      U
      (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      A1 AS := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  exact
    coarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs_at_pair_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_outerRadius_lt_one_of_scalarCutoffControls
      Q a s C F w g Acirc1 AcircS U A1 AS hEll hρ₁ hlt hρ₂
      (hlower hρ₁ hlt hρ₂) (houter hρ₁ hlt hρ₂)
      (henergyAvg hρ₁ hlt hρ₂) (hfluxMem hρ₁ hlt hρ₂) (huMem hρ₁ hlt hρ₂)
      (hgMem hρ₁ hlt hρ₂) (hfluxEnergy hρ₁ hlt hρ₂)
      (hscalar hρ₁ hlt hρ₂) hC (hAcirc1_nonneg hρ₁ hlt hρ₂)
      (hAcircS_nonneg hρ₁ hlt hρ₂) (hU hρ₁ hlt hρ₂)
      (hA1 hρ₁ hlt hρ₂) (hAS hρ₁ hlt hρ₂)

/-- Quantitative cutoff analytic inputs combine with the separated canonical
coefficient algebra to produce the full canonical factor inputs. -/
theorem CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalFactorInputs.of_quantitativeCubeCutoff_of_coefficientBounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C uL2Sq : ℝ)
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
        AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        k h U
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        A1 AS) :
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalFactorInputs Q a s C uL2Sq
      k h F flux u g
      (fun ρ₁ ρ₂ => scalarCutoffGradientField (η ρ₁ ρ₂))
      energy Acirc1 AcircS
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      U
      (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      A1 AS := by
  exact
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalFactorInputs.of_analyticInputs_of_coefficientBounds
      Q a s C uL2Sq k h F flux u g
      (fun ρ₁ ρ₂ => scalarCutoffGradientField (η ρ₁ ρ₂))
      energy Acirc1 AcircS
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      U
      (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      A1 AS
      (CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs.of_quantitativeCubeCutoff
        Q a s C k h F flux u g energy η Acirc1 AcircS U A1 AS
        htest henergyAvg hfluxMem huMem hgMem hfluxEnergy hBgConst hBgCent hC
        hAcirc1_nonneg hAcircS_nonneg hproj hgCirc1 hgCircS hU hA1 hAS)
      hcoeff

/-- Canonical Chapter-3 cutoff constructor for the full radius-indexed
canonical factor-input package.

This is the direct handoff from the actual smooth cutoff
`QuantitativeCubeCutoff.canonicalFun`: its `L∞` and derivative bounds fill the
`Xi` and `D` slots, while the remaining scalar-control and coefficient
inequalities stay explicit. -/
theorem
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalFactorInputs.of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_outerRadius_lt_one_of_scalarCutoffControls_of_coefficientBounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C uL2Sq : ℝ) {lam Lam : ℝ}
    (k h : ℝ → ℝ → ℝ) (F : ℝ → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (g : ℝ → ℝ → Vec d → ℝ)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hlower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) →
        (hρ₂ : ρ₂ ≤ 1) →
        F ρ₁ ≤
          cubeAverage Q
            (fun x =>
              QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x *
                scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (houter :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) →
        (hρ₂ : ρ₂ ≤ 1) → ρ₂ < 1)
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
    (hgMem :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.MemLp (g ρ₁ ρ₂) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hscalar :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) →
        (hρ₂ : ρ₂ ≤ 1) →
        CoarseCaccioppoliScalarCutoffControls Q s
          (fun x => (w ρ₁ ρ₂).toH1 x) (g ρ₁ ρ₂)
          (scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
          (Acirc1 ρ₁ ρ₂) (AcircS ρ₁ ρ₂)
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂) C)
    (hC : 0 ≤ C)
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
        AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        k h U
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        A1 AS) :
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalFactorInputs Q a s C uL2Sq
      k h F
      (fun ρ₁ ρ₂ x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
      (fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1 x)
      g
      (fun ρ₁ ρ₂ => scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
      (fun ρ₁ ρ₂ x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
      Acirc1 AcircS
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      U
      (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      A1 AS := by
  exact
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalFactorInputs.of_analyticInputs_of_coefficientBounds
      Q a s C uL2Sq k h F
      (fun ρ₁ ρ₂ x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
      (fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1 x)
      g
      (fun ρ₁ ρ₂ => scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
      (fun ρ₁ ρ₂ x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
      Acirc1 AcircS
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      U
      (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      A1 AS
      (CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalAnalyticInputs.of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_outerRadius_lt_one_of_scalarCutoffControls
        Q a s C k h F w g Acirc1 AcircS U A1 AS hEll hlower houter
        henergyAvg hfluxMem huMem hgMem hfluxEnergy hscalar hC
        hAcirc1_nonneg hAcircS_nonneg hU hA1 hAS)
      hcoeff


end

end Homogenization
