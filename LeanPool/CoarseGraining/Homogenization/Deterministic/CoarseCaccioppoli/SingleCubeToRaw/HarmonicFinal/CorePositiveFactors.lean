/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.Setup.CoefficientBounds
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.Setup.SolutionInputs
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.DescendantSummation

/-! # Core Positive Factors -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-- Boundary fixed-localized-energy coarse Caccioppoli from the canonical raw
coefficient bounds.  Compared with the coefficient-bound wrapper below, the
multiscale localization data has already been absorbed into `hrawcoeff`. -/
theorem
    coarseCaccioppoli_boundary_qone_of_canonicalHarmonicPositiveFactors_of_canonicalHarmonicRawCoefficientBounds
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
  have hs1 : s < 1 := by nlinarith [ht, hst]
  have hSigmaSum_one :
      Summable (fun n : ℕ =>
        geometricWeight (1 : ℝ) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_maxDescendantSigmaStarInvNormAtScale_geometricWeight_one_of_lt
      Q a ht (by nlinarith [hs, hst]) hSigmaSum_t
  have hSigmaSum_one_sub_s :
      Summable (fun n : ℕ =>
        geometricWeight (1 - s) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_maxDescendantSigmaStarInvNormAtScale_geometricWeight_one_of_lt
      Q a ht (by nlinarith [hst]) hSigmaSum_t
  let g : ℝ → ℝ → Vec d → ℝ := fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1.grad x i
  let U : ℝ → ℝ → ℝ := coarseCaccioppoliCanonicalHarmonicL2Profile Q a w
  let A1 : ℝ → ℝ → ℝ := coarseCaccioppoliCanonicalGradientAcircOne Q a
  let AS : ℝ → ℝ → ℝ := coarseCaccioppoliCanonicalGradientAcircOneSub Q a s
  have hscalarFactors :
      CoarseCaccioppoliBoundaryCanonicalScalarControlFactors Q a s C w g A1 AS := by
    exact
      CoarseCaccioppoliBoundaryCanonicalScalarControlFactors.of_positiveFactors_of_harmonicGradientComponent_of_fluxEnergyControls_canonicalGradientAcirc
        Q a s C w i hpositiveFactors hs1 hfluxEnergy hgrad
        hSigmaSum_one hSigmaSum_one_sub_s
        (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ N =>
          hprojected.projectedPoincare (ρ₁ := ρ₁) (ρ₂ := ρ₂) hρ₁ hlt hρ₂ N)
  exact
    coarseCaccioppoli_boundary_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_scalarCutoffControls_of_coefficientBounds_of_multiscaleEllipticity_of_localizedExplicitHeightOfScaleChoice
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := coarseCaccioppoliTriadicGapScale)
      (F := coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy)
      (w := w) (g := g) (Acirc1 := A1) (AcircS := AS)
      (U := U) (A1 := A1) (AS := AS)
      hC.le hs ht hst hu
      (coarseCaccioppoliLocalizedEnergyRadiusProfile_nonneg Q hbase_nonneg)
      (coarseCaccioppoliLocalizedEnergyRadiusProfile_boundedAbove Q hbase_nonneg hbase_int)
      (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
        coarseCaccioppoliTriadicGapScale_spec hρ₁ hlt hρ₂)
      ((CoarseCaccioppoliLocalizedEnergyProfileLowerControls.of_fixedEnergy_le_pairEnergy
          Q hbase_int
          (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
            (hfluxEnergy (ρ₁ := ρ₁) (ρ₂ := ρ₂) hρ₁ hlt hρ₂).2.1)
          hinner_energy_le).to_canonicalCutoffLower
        (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
          (hfluxEnergy (ρ₁ := ρ₁) (ρ₂ := ρ₂) hρ₁ hlt hρ₂).1)
        (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
          (hfluxEnergy (ρ₁ := ρ₁) (ρ₂ := ρ₂) hρ₁ hlt hρ₂).2.1))
      henergyAvg
      (by
        intro ρ₁ ρ₂ _ _ _
        exact memLp_harmonicFlux_normalizedCubeMeasure Q a (w ρ₁ ρ₂) hEll)
      (by
        intro ρ₁ ρ₂ _ _ _
        exact memLp_harmonicFunction_normalizedCubeMeasure Q a (w ρ₁ ρ₂))
      (by
        intro ρ₁ ρ₂ _ _ _
        exact memLp_harmonicGradientComponent_normalizedCubeMeasure Q a (w ρ₁ ρ₂) i)
      hfluxEnergy
      (by
        intro ρ₁ ρ₂ hρ₁ hlt hρ₂
        exact
          CoarseCaccioppoliBoundaryCanonicalScalarControlFactors.to_scalarCutoffControls
            Q a w g A1 AS hscalarFactors hs hs1 hC hρ₁ hlt hρ₂)
      (by
        intro ρ₁ ρ₂ _ _ _
        exact coarseCaccioppoliCanonicalGradientAcircOne_nonneg Q a ρ₁ ρ₂)
      (by
        intro ρ₁ ρ₂ _ _ _
        exact coarseCaccioppoliCanonicalGradientAcircOneSub_nonneg Q a hs1.le ρ₁ ρ₂)
      (by
        intro ρ₁ ρ₂ _ _ _
        exact le_rfl)
      (by
        intro ρ₁ ρ₂ _ _ _
        exact le_rfl)
      (by
        intro ρ₁ ρ₂ _ _ _
        exact le_rfl)
      hEll hrawcoeff

/-- Sequence-local note raw bridge from the vector projected-Poincare family
and canonical raw coefficient bounds stated for the effective scalar-facing
constant `(Fintype.card (Fin d) : ℝ) * C`.

This is the note-faithful bridge: it proves the local recurrence on the
Chapter-3 radius sequence before the recurrence is summed. -/
theorem
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridge.of_canonicalHarmonicRawCoefficientBounds
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (baseEnergy : Vec d → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
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
      CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareVectorFamily Q a C w)
    (hrawcoeff :
      CoarseCaccioppoliBoundaryCanonicalHarmonicRawCoefficientBounds Q a s t
        ((Fintype.card (Fin d) : ℝ) * C) uL2Sq w)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridge
      Q a s t C uL2Sq baseEnergy := by
  let Ceff : ℝ := (Fintype.card (Fin d) : ℝ) * C
  have hcard_pos : 0 < (Fintype.card (Fin d) : ℝ) := by
    simp [Fintype.card_fin, Nat.pos_iff_ne_zero, NeZero.ne d]
  have hCeff_pos : 0 < Ceff := by
    exact mul_pos hcard_pos hC
  have hs1 : s < 1 := by nlinarith [ht, hst]
  have hSigmaSum_one :
      Summable (fun n : ℕ =>
        geometricWeight (1 : ℝ) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_maxDescendantSigmaStarInvNormAtScale_geometricWeight_one_of_lt
      Q a ht (by nlinarith [hs, hst]) hSigmaSum_t
  have hSigmaSum_one_sub_s :
      Summable (fun n : ℕ =>
        geometricWeight (1 - s) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_maxDescendantSigmaStarInvNormAtScale_geometricWeight_one_of_lt
      Q a ht (by nlinarith [hst]) hSigmaSum_t
  let G : ℝ → ℝ → Vec d → Vec d := fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1.grad x
  let U : ℝ → ℝ → ℝ := coarseCaccioppoliCanonicalHarmonicL2Profile Q a w
  let A1 : ℝ → ℝ → ℝ := coarseCaccioppoliCanonicalGradientAcircOne Q a
  let AS : ℝ → ℝ → ℝ := coarseCaccioppoliCanonicalGradientAcircOneSub Q a s
  have hGcirc1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∀ i : Fin d, ∀ N : ℕ,
          cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
              (fun x => (w ρ₁ ρ₂).toH1.grad x i) ≤
            A1 ρ₁ ρ₂ *
              Real.sqrt
                (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)) := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂ i N
    let energy : Vec d → ℝ := fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x
    let Grad : Vec d → Vec d := fun x => (w ρ₁ ρ₂).toH1.grad x
    have hpartial :
        cubeBesovNegativeVectorPartialSeminorm Q (1 : ℝ) N Grad ≤
          (geometricDiscount (1 : ℝ) 1)⁻¹ *
            Real.rpow (lambdaSq Q (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ) *
            Real.sqrt (cubeAverage Q energy) := by
      exact
        coarseCaccioppoli_gradient_qone_partialBound_of_cubeAverageEnergyControl
          Q a (1 : ℝ) (by norm_num) Grad energy N
          (hfluxEnergy hρ₁ hlt hρ₂).1 (hfluxEnergy hρ₁ hlt hρ₂).2.1
          (by simpa [Grad, energy] using hgrad hρ₁ hlt hρ₂) hSigmaSum_one
    have hE_nonneg : 0 ≤ Real.sqrt (cubeAverage Q energy) :=
      Real.sqrt_nonneg _
    calc
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => Grad x i)
          ≤ cubeBesovScaleWeight (-1) Q *
              cubeBesovNegativeVectorPartialSeminorm Q 1 N Grad := by
            exact
              cubeBesovCircPartialNorm_two_one_component_le_scaleWeight_neg_mul_negativeVectorPartialSeminorm
                Q 1 Grad i N
      _ ≤
          cubeBesovScaleWeight (-1) Q *
            (((geometricDiscount (1 : ℝ) 1)⁻¹ *
              Real.rpow (lambdaSq Q (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)) *
              Real.sqrt (cubeAverage Q energy)) := by
            exact mul_le_mul_of_nonneg_left hpartial (cubeBesovScaleWeight_nonneg (-1) Q)
      _ =
          (cubeBesovScaleWeight (-1) Q *
            ((geometricDiscount (1 : ℝ) 1)⁻¹ *
              Real.rpow (lambdaSq Q (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ))) *
            Real.sqrt (cubeAverage Q energy) := by
            ring
      _ =
          A1 ρ₁ ρ₂ * Real.sqrt (cubeAverage Q energy) := by
            simp [A1, coarseCaccioppoliCanonicalGradientAcircOne,
              coarseCaccioppoliCanonicalGradientAcirc, energy]
  have hGcircS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∀ i : Fin d, ∀ N : ℕ,
          cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
              (fun x => (w ρ₁ ρ₂).toH1.grad x i) ≤
            AS ρ₁ ρ₂ *
              Real.sqrt
                (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)) := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂ i N
    let energy : Vec d → ℝ := fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x
    let Grad : Vec d → Vec d := fun x => (w ρ₁ ρ₂).toH1.grad x
    have hs_pos : 0 < 1 - s := by linarith
    have hpartial :
        cubeBesovNegativeVectorPartialSeminorm Q (1 - s) N Grad ≤
          (geometricDiscount (1 - s) 1)⁻¹ *
            Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ) *
            Real.sqrt (cubeAverage Q energy) := by
      exact
        coarseCaccioppoli_gradient_qone_partialBound_of_cubeAverageEnergyControl
          Q a (1 - s) hs_pos Grad energy N
          (hfluxEnergy hρ₁ hlt hρ₂).1 (hfluxEnergy hρ₁ hlt hρ₂).2.1
          (by simpa [Grad, energy] using hgrad hρ₁ hlt hρ₂) hSigmaSum_one_sub_s
    calc
      cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => Grad x i)
          ≤ cubeBesovScaleWeight (-(1 - s)) Q *
              cubeBesovNegativeVectorPartialSeminorm Q (1 - s) N Grad := by
            exact
              cubeBesovCircPartialNorm_two_one_component_le_scaleWeight_neg_mul_negativeVectorPartialSeminorm
                Q (1 - s) Grad i N
      _ ≤
          cubeBesovScaleWeight (-(1 - s)) Q *
            (((geometricDiscount (1 - s) 1)⁻¹ *
              Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ)) *
              Real.sqrt (cubeAverage Q energy)) := by
            exact mul_le_mul_of_nonneg_left hpartial
              (cubeBesovScaleWeight_nonneg (-(1 - s)) Q)
      _ =
          (cubeBesovScaleWeight (-(1 - s)) Q *
            ((geometricDiscount (1 - s) 1)⁻¹ *
              Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ))) *
            Real.sqrt (cubeAverage Q energy) := by
            ring
      _ =
          AS ρ₁ ρ₂ * Real.sqrt (cubeAverage Q energy) := by
            simp [AS, coarseCaccioppoliCanonicalGradientAcircOneSub,
              coarseCaccioppoliCanonicalGradientAcirc, energy]
  intro n
  let ρ₁ : ℝ := coarseCaccioppoliRadiusSequence n
  let ρ₂ : ℝ := coarseCaccioppoliRadiusSequence (n + 1)
  have hρ₁ : (1 / 3 : ℝ) ≤ ρ₁ := by
    simpa [ρ₁] using (coarseCaccioppoliRadiusSequence_mem_Icc n).1
  have hlt : ρ₁ < ρ₂ := by
    simpa [ρ₁, ρ₂] using
      coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self n)
  have hρ₂ : ρ₂ ≤ 1 := by
    simpa [ρ₂] using (coarseCaccioppoliRadiusSequence_mem_Icc (n + 1)).2
  let ηρ : QuantitativeCubeCutoff Q ρ₁ ρ₂ :=
    coarseCaccioppoliCanonicalQuantitativeCutoff Q hρ₁ hlt
  have hlowerρ :
      coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy ρ₁ ≤
        cubeAverage Q
          (fun x =>
            ηρ x * scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) := by
    have hlowerCanon :
        coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy ρ₁ ≤
          cubeAverage Q
            (fun x =>
              QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x *
                scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) :=
      ((CoarseCaccioppoliLocalizedEnergyProfileLowerControls.of_fixedEnergy_le_pairEnergy
          Q hbase_int
          (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
            (hfluxEnergy (ρ₁ := ρ₁) (ρ₂ := ρ₂) hρ₁ hlt hρ₂).2.1)
          hinner_energy_le).to_canonicalCutoffLower
        (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
          (hfluxEnergy (ρ₁ := ρ₁) (ρ₂ := ρ₂) hρ₁ hlt hρ₂).1)
        (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
          (hfluxEnergy (ρ₁ := ρ₁) (ρ₂ := ρ₂) hρ₁ hlt hρ₂).2.1))
        hρ₁ hlt hρ₂
    simpa [ηρ, coarseCaccioppoliCanonicalQuantitativeCutoff,
      QuantitativeCubeCutoff.canonical] using hlowerCanon
  have htest :
      coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy ρ₁ ≤
        |cubeAverage Q
          (fun x =>
            vecDot (matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
              (((w ρ₁ ρ₂).toH1 x) •
                scalarCutoffGradientField
                  (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂) x))| := by
    have houter : ρ₂ < 1 := by
      simpa [ρ₂] using coarseCaccioppoliRadiusSequence_lt_one (n + 1)
    have htestη :=
      le_abs_cubeAverage_vecDot_flux_scalarCutoffGradientField_of_aHarmonicFunction_of_le_cubeAverage_mul_scalarVariationEnergyIntegrand
        Q a (w ρ₁ ρ₂) hEll ηρ.smooth ηρ.hasCompactSupport
        (coarseCaccioppoliCanonicalQuantitativeCutoff_tsupport_subset_openCubeSet_of_lt_one
          Q hρ₁ hlt houter)
        hlowerρ
    simpa [ηρ, coarseCaccioppoliCanonicalQuantitativeCutoff,
      QuantitativeCubeCutoff.canonical] using htestη
  have hξLp :
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
  have hrawcoeff' :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalRawCoefficientBounds
        Q a s t Ceff uL2Sq
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t Ceff
          coarseCaccioppoliTriadicGapScale)
        U
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        A1 AS := by
    simpa [Ceff, U, A1, AS,
      CoarseCaccioppoliBoundaryCanonicalHarmonicRawCoefficientBounds] using hrawcoeff
  rcases hrawcoeff' hρ₁ hlt hρ₂ with ⟨hconst, hcentered⟩
  refine le_trans htest ?_
  simpa [CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridge, Ceff, ρ₁, ρ₂,
    henergyAvg hρ₁ hlt hρ₂] using
    (abs_cubeAverage_vecDot_scalar_smul_le_boundaryRawEstimate_of_canonical_vector_factor_bounds
      (Q := Q) (a := a) (s := s)
      (flux := fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
      (u := fun x => (w ρ₁ ρ₂).toH1 x)
      (G := fun x => (w ρ₁ ρ₂).toH1.grad x)
      (ξ := scalarCutoffGradientField (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂))
      (energy := fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
      (Acirc1 := A1 ρ₁ ρ₂) (AcircS := AS ρ₁ ρ₂)
      (B := coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂)
      (C := C) (U := U ρ₁ ρ₂)
      (Xi := coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
      (D := coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂)
      (A1 := A1 ρ₁ ρ₂) (AS := AS ρ₁ ρ₂)
      (Alpha := coarseCaccioppoliBoundaryAlphaOfHeight Q a s t Ceff
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t Ceff
          coarseCaccioppoliTriadicGapScale) ρ₁ ρ₂)
      (Bcross := coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s Ceff uL2Sq
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t Ceff
          coarseCaccioppoliTriadicGapScale) ρ₁ ρ₂)
      hs hs1
      (memLp_harmonicFlux_normalizedCubeMeasure Q a (w ρ₁ ρ₂) hEll)
      (memLp_harmonicFunction_normalizedCubeMeasure Q a (w ρ₁ ρ₂))
      (fun i => memLp_harmonicGradientComponent_normalizedCubeMeasure Q a (w ρ₁ ρ₂) i)
      hξLp
      (hfluxEnergy hρ₁ hlt hρ₂)
      (CoarseCaccioppoliVectorCutoffControls.of_canonicalQuantitativeCutoff_of_positiveFactors
        (Q := Q) (s := s) (C := C) hρ₁ hlt
        (fun x => (w ρ₁ ρ₂).toH1 x)
        (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
        (fun x => (w ρ₁ ρ₂).toH1.grad x)
        (A1 ρ₁ ρ₂) (AS ρ₁ ρ₂) hs hs1
        (hpositiveFactors hρ₁ hlt hρ₂).1
        (hpositiveFactors hρ₁ hlt hρ₂).2.1
        (coarseCaccioppoliCanonicalGradientAcircOneSub_nonneg Q a hs1.le ρ₁ ρ₂)
        (hpositiveFactors hρ₁ hlt hρ₂).2.2 hC
        (fun N => hprojected.vectorPoincare hρ₁ hlt hρ₂ N)
        (hGcirc1 hρ₁ hlt hρ₂) (hGcircS hρ₁ hlt hρ₂))
      (coarseCaccioppoliCanonicalGradientAcircOne_nonneg Q a ρ₁ ρ₂)
      (coarseCaccioppoliCanonicalGradientAcircOneSub_nonneg Q a hs1.le ρ₁ ρ₂)
      le_rfl hXi le_rfl le_rfl le_rfl hconst hcentered)

/-- Boundary fixed-localized-energy coarse Caccioppoli from the vector
projected-Poincare family and canonical raw coefficient bounds stated for the
effective scalar-facing constant `(Fintype.card (Fin d) : ℝ) * C`.

This is the note-facing replacement for the old componentwise projected
Poincare endpoint. -/
theorem
    coarseCaccioppoli_boundary_qone_of_canonicalHarmonicVectorPositiveFactors_of_canonicalHarmonicRawCoefficientBounds
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (baseEnergy : Vec d → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
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
      CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareVectorFamily Q a C w)
    (hrawcoeff :
      CoarseCaccioppoliBoundaryCanonicalHarmonicRawCoefficientBounds Q a s t
        ((Fintype.card (Fin d) : ℝ) * C) uL2Sq w)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy (1 / 3 : ℝ) ≤
      coarseCaccioppoliBoundaryExplicitHeightBound Q a s t
        ((Fintype.card (Fin d) : ℝ) * C) uL2Sq := by
  let Ceff : ℝ := (Fintype.card (Fin d) : ℝ) * C
  have hcard_pos : 0 < (Fintype.card (Fin d) : ℝ) := by
    simp [Fintype.card_fin, Nat.pos_iff_ne_zero, NeZero.ne d]
  have hCeff_nonneg : 0 ≤ Ceff := (mul_pos hcard_pos hC).le
  exact
    coarseCaccioppoli_boundary_qone_of_noteEstimate_on_radiusSequence_of_localizedExplicitHeightOfScaleChoice
      Q a s t Ceff uL2Sq coarseCaccioppoliTriadicGapScale
      hCeff_nonneg hs ht hst hu
      (coarseCaccioppoliLocalizedEnergyRadiusProfile_nonneg Q hbase_nonneg)
      (coarseCaccioppoliLocalizedEnergyRadiusProfile_boundedAbove Q hbase_nonneg hbase_int)
      (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
        coarseCaccioppoliTriadicGapScale_spec hρ₁ hlt hρ₂)
      (by
        simpa [Ceff, CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridge,
          Fintype.card_fin] using
          (CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridge.of_canonicalHarmonicRawCoefficientBounds
            (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
            (baseEnergy := baseEnergy) (w := w)
            hC hs ht hst hbase_int hinner_energy_le henergyAvg
            hfluxEnergy hpositiveFactors hgrad hprojected hrawcoeff hEll hSigmaSum_t))

/-- Interior fixed-localized-energy coarse Caccioppoli from the canonical raw
coefficient bounds. -/
theorem
    coarseCaccioppoli_interior_qone_of_canonicalHarmonicPositiveFactors_of_canonicalHarmonicRawCoefficientBounds
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
  have hs1 : s < 1 := by nlinarith [ht, hst]
  have hSigmaSum_one :
      Summable (fun n : ℕ =>
        geometricWeight (1 : ℝ) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_maxDescendantSigmaStarInvNormAtScale_geometricWeight_one_of_lt
      Q a ht (by nlinarith [hs, hst]) hSigmaSum_t
  have hSigmaSum_one_sub_s :
      Summable (fun n : ℕ =>
        geometricWeight (1 - s) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_maxDescendantSigmaStarInvNormAtScale_geometricWeight_one_of_lt
      Q a ht (by nlinarith [hst]) hSigmaSum_t
  let g : ℝ → ℝ → Vec d → ℝ := fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1.grad x i
  let U : ℝ → ℝ → ℝ := coarseCaccioppoliCanonicalHarmonicL2Profile Q a w
  let A1 : ℝ → ℝ → ℝ := coarseCaccioppoliCanonicalGradientAcircOne Q a
  let AS : ℝ → ℝ → ℝ := coarseCaccioppoliCanonicalGradientAcircOneSub Q a s
  have hscalarFactors :
      CoarseCaccioppoliBoundaryCanonicalScalarControlFactors Q a s C w g A1 AS := by
    exact
      CoarseCaccioppoliBoundaryCanonicalScalarControlFactors.of_positiveFactors_of_harmonicGradientComponent_of_fluxEnergyControls_canonicalGradientAcirc
        Q a s C w i hpositiveFactors hs1 hfluxEnergy hgrad
        hSigmaSum_one hSigmaSum_one_sub_s
        (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ N =>
          hprojected.projectedPoincare (ρ₁ := ρ₁) (ρ₂ := ρ₂) hρ₁ hlt hρ₂ N)
  exact
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_scalarCutoffControls_of_coefficientBounds_of_multiscaleEllipticity_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := coarseCaccioppoliTriadicGapScale)
      (F := coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy)
      (G₀ := coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy)
      (w := w) (g := g) (Acirc1 := A1) (AcircS := AS)
      (U := U) (A1 := A1) (AS := AS)
      hC.le hs ht hst hu
      (fun {_ρ} _ _ => rfl)
      (coarseCaccioppoliLocalizedEnergyRadiusProfile_nonneg Q hbase_nonneg)
      (coarseCaccioppoliLocalizedEnergyRadiusProfile_boundedAbove Q hbase_nonneg hbase_int)
      (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
        coarseCaccioppoliTriadicGapScale_spec hρ₁ hlt hρ₂)
      ((CoarseCaccioppoliLocalizedEnergyProfileLowerControls.of_fixedEnergy_le_pairEnergy
          Q hbase_int
          (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
            (hfluxEnergy (ρ₁ := ρ₁) (ρ₂ := ρ₂) hρ₁ hlt hρ₂).2.1)
          hinner_energy_le).to_canonicalCutoffLower
        (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
          (hfluxEnergy (ρ₁ := ρ₁) (ρ₂ := ρ₂) hρ₁ hlt hρ₂).1)
        (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
          (hfluxEnergy (ρ₁ := ρ₁) (ρ₂ := ρ₂) hρ₁ hlt hρ₂).2.1))
      henergyAvg
      (by
        intro ρ₁ ρ₂ _ _ _
        exact memLp_harmonicFlux_normalizedCubeMeasure Q a (w ρ₁ ρ₂) hEll)
      (by
        intro ρ₁ ρ₂ _ _ _
        exact memLp_harmonicFunction_normalizedCubeMeasure Q a (w ρ₁ ρ₂))
      (by
        intro ρ₁ ρ₂ _ _ _
        exact memLp_harmonicGradientComponent_normalizedCubeMeasure Q a (w ρ₁ ρ₂) i)
      hfluxEnergy
      (by
        intro ρ₁ ρ₂ hρ₁ hlt hρ₂
        exact
          CoarseCaccioppoliBoundaryCanonicalScalarControlFactors.to_scalarCutoffControls
            Q a w g A1 AS hscalarFactors hs hs1 hC hρ₁ hlt hρ₂)
      (by
        intro ρ₁ ρ₂ _ _ _
        exact coarseCaccioppoliCanonicalGradientAcircOne_nonneg Q a ρ₁ ρ₂)
      (by
        intro ρ₁ ρ₂ _ _ _
        exact coarseCaccioppoliCanonicalGradientAcircOneSub_nonneg Q a hs1.le ρ₁ ρ₂)
      (by
        intro ρ₁ ρ₂ _ _ _
        exact le_rfl)
      (by
        intro ρ₁ ρ₂ _ _ _
        exact le_rfl)
      (by
        intro ρ₁ ρ₂ _ _ _
        exact le_rfl)
      hEll hrawcoeff


end

end Homogenization
