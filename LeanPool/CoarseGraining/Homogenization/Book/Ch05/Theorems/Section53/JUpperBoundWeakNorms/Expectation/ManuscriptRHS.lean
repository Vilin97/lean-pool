/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Expectation.RHS

/-! # Manuscript RHS -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundWeakNorms

/-!
# ManuscriptRHS

Comparison between the manuscript pointwise RHS and the manuscript expected RHS.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

noncomputable section

theorem integral_jUpperWeakNormManuscriptPointwiseRHSAtScale_le_manuscriptExpectedRHSAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    {k m : ℤ} (hk_nonneg : 0 ≤ k) (hkm : k ≤ m)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (C Cosc scaleSep BφS BφT Cprod : ℝ)
    (p q p0 q0 : Vec d)
    (hC : 0 ≤ C) (hCprod : 0 ≤ Cprod)
    (hParent :
      Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q) P)
    (hDesc : ∀ R, R ∈ descendantsAtScale (originCube d m) k →
      Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P)
    (hGradWeak :
      Integrable
        (fun a : RegCoeffField d => Ch04.canonicalScalarResponseGradientWeakNormCubeSet
          (originCube d m) s p q p0 a.toFun) P)
    (hFluxWeak :
      Integrable
        (fun a : RegCoeffField d => Ch04.canonicalScalarResponseFluxWeakNormCubeSet
          (originCube d m) t p q q0 a.toFun) P)
    (hGradSq :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.canonicalScalarResponseGradientWeakNormCubeSet
            (originCube d m) s p q p0 a.toFun) ^ 2) P)
    (hFluxSq :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
            (originCube d m) t p q q0 a.toFun) ^ 2) P) :
    ∫ a,
        jUpperWeakNormManuscriptPointwiseRHSAtScale m k s t
          C Cosc scaleSep BφS BφT Cprod p q p0 q0 a ∂P
      ≤
        jUpperWeakNormManuscriptExpectedRHSAtScale P m k s t
          C Cosc scaleSep BφS BφT Cprod p q p0 q0 := by
  let : IsProbabilityMeasure P := hP.isProbability
  let Q : TriadicCube d := originCube d m
  let j : ℕ := Int.toNat (m - k)
  let childAverage : RegCoeffField d → ℝ :=
    fun a => descendantsAverage Q j (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a)
  let gradWeak : RegCoeffField d → ℝ :=
    fun a => Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun
  let fluxWeak : RegCoeffField d → ℝ :=
    fun a => Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun
  let gradCoeff : ℝ :=
    (3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovScaleWeight (-s) Q * BφS
  let fluxCoeff : ℝ :=
    (3 : ℝ) ^ ((d : ℝ) + t) * cubeBesovScaleWeight (-t) Q * BφT
  let scaledGrad : RegCoeffField d → ℝ := gradWeak
  let scaledFlux : RegCoeffField d → ℝ := fluxWeak
  let addPoint : RegCoeffField d → ℝ :=
    fun a =>
      (2 * C) *
        (Real.sqrt (responseJAdditivityDefectAtScale m k p q a) *
          Real.sqrt (childAverage a))
  let oscPoint : RegCoeffField d → ℝ :=
    fun a => Cosc * scaleSep * Ch04.restrictionResponseJObservableCubeSet Q p q a
  let gradPoint : RegCoeffField d → ℝ :=
    fun a =>
      (1 / 2 : ℝ) * ‖q0‖ *
        (((Fintype.card (Fin d) : ℝ) * gradCoeff) * gradWeak a)
  let fluxPoint : RegCoeffField d → ℝ :=
    fun a =>
      (1 / 2 : ℝ) * ‖p0‖ *
        (((Fintype.card (Fin d) : ℝ) * fluxCoeff) * fluxWeak a)
  let productPoint : RegCoeffField d → ℝ :=
    fun a => Cprod * (scaledGrad a * scaledFlux a)
  have hDescDepth :
      ∀ R, R ∈ descendantsAtDepth Q j →
        Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P := by
    intro R hR
    exact hDesc R (by
      simpa [Q, j, descendantsAtScale_eq_descendantsAtDepth (originCube d m) hkm]
        using! hR)
  have hChildInt : Integrable childAverage P := by
    simpa [childAverage, Q, j] using
      Ch04.integrable_descendantsAverage_restrictionResponseJObservableCubeSet hDescDepth
  have hDefectInt :
      Integrable (responseJAdditivityDefectAtScale m k p q) P :=
    integrable_responseJAdditivityDefectAtScale hkm p q hParent hDesc
  have hDefectNonneg :
      0 ≤ᵐ[P] responseJAdditivityDefectAtScale m k p q :=
    responseJAdditivityDefectAtScale_nonneg_ae hP hkm p q
  have hChildNonneg : 0 ≤ᵐ[P] childAverage := by
    filter_upwards with a
    simpa [childAverage, Q, j] using
      descendantsAverage_restrictionResponseJObservableCubeSet_nonneg Q j p q a
  have hSqrtProdInt :
      Integrable
        (fun a : RegCoeffField d =>
          Real.sqrt (responseJAdditivityDefectAtScale m k p q a) *
            Real.sqrt (childAverage a)) P :=
    integrable_sqrt_mul_sqrt_of_integrable_of_ae_nonneg
      (A := responseJAdditivityDefectAtScale m k p q)
      (B := childAverage) hDefectInt hChildInt hDefectNonneg hChildNonneg
  have hAddInt : Integrable addPoint P := by
    simpa [addPoint] using hSqrtProdInt.const_mul (2 * C)
  have hOscInt : Integrable oscPoint P := by
    simpa [oscPoint, Q] using hParent.const_mul (Cosc * scaleSep)
  have hGradInt : Integrable gradPoint P := by
    refine
      (hGradWeak.const_mul
        ((1 / 2 : ℝ) * ‖q0‖ * ((Fintype.card (Fin d) : ℝ) * gradCoeff))).congr ?_
    filter_upwards with a
    simp [gradPoint, gradWeak, Q, mul_assoc]
  have hFluxInt : Integrable fluxPoint P := by
    refine
      (hFluxWeak.const_mul
        ((1 / 2 : ℝ) * ‖p0‖ * ((Fintype.card (Fin d) : ℝ) * fluxCoeff))).congr ?_
    filter_upwards with a
    simp [fluxPoint, fluxWeak, Q, mul_assoc]
  have hGradNonneg : 0 ≤ᵐ[P] scaledGrad := by
    simpa [scaledGrad, gradWeak, Q] using
      canonicalScalarResponseGradientWeakNormCubeSet_nonneg_ae hP Q hs p q p0
  have hFluxNonneg : 0 ≤ᵐ[P] scaledFlux := by
    simpa [scaledFlux, fluxWeak, Q] using
      canonicalScalarResponseFluxWeakNormCubeSet_nonneg_ae hP Q ht p q q0
  have hScaledProdInt : Integrable (fun a => scaledGrad a * scaledFlux a) P :=
    integrable_mul_of_integrable_sq_of_ae_nonneg
      (X := scaledGrad) (Y := scaledFlux)
      (by simpa [scaledGrad, gradWeak, Q] using hGradSq)
      (by simpa [scaledFlux, fluxWeak, Q] using hFluxSq)
      hGradNonneg hFluxNonneg
  have hProductInt : Integrable productPoint P := by
    simpa [productPoint] using hScaledProdInt.const_mul Cprod
  have hRHS_eq :
      (fun a : RegCoeffField d =>
        jUpperWeakNormManuscriptPointwiseRHSAtScale m k s t
          C Cosc scaleSep BφS BφT Cprod p q p0 q0 a) =
        fun a => (addPoint a + oscPoint a) + ((gradPoint a + fluxPoint a) + productPoint a) := by
    funext a
    simp [jUpperWeakNormManuscriptPointwiseRHSAtScale, addPoint, oscPoint, gradPoint,
      fluxPoint, productPoint, childAverage, gradWeak, fluxWeak, scaledGrad,
      scaledFlux, gradCoeff, fluxCoeff, Q, j, add_assoc, add_comm, mul_assoc]
    ring
  have hIntegral_eq :
      ∫ a,
        jUpperWeakNormManuscriptPointwiseRHSAtScale m k s t
          C Cosc scaleSep BφS BφT Cprod p q p0 q0 a ∂P =
        ∫ a, addPoint a ∂P +
          (∫ a, oscPoint a ∂P +
            ((∫ a, gradPoint a ∂P + ∫ a, fluxPoint a ∂P) +
              ∫ a, productPoint a ∂P)) := by
    rw [hRHS_eq]
    rw [integral_add
      (f := fun a : RegCoeffField d => addPoint a + oscPoint a)
      (g := fun a : RegCoeffField d => (gradPoint a + fluxPoint a) + productPoint a)
      (hAddInt.add hOscInt) ((hGradInt.add hFluxInt).add hProductInt)]
    rw [integral_add (f := addPoint) (g := oscPoint) hAddInt hOscInt]
    rw [integral_add
      (f := fun a : RegCoeffField d => gradPoint a + fluxPoint a)
      (g := productPoint) (hGradInt.add hFluxInt) hProductInt]
    rw [integral_add (f := gradPoint) (g := fluxPoint) hGradInt hFluxInt]
    ring
  have hSqrtBound :
      ∫ a,
          Real.sqrt (responseJAdditivityDefectAtScale m k p q a) *
            Real.sqrt (childAverage a) ∂P ≤
        Real.sqrt (tauAtScale P m k p q) *
          Real.sqrt (Ch04.expectedResponseJCubeSet P (originCube d k) p q) := by
    simpa [childAverage, Q, j] using
      integral_sqrt_responseJAdditivityDefectAtScale_mul_sqrt_childResponseAverage_le
        hP hstat hk_nonneg hkm p q hParent hDesc
  have hAddBound :
      ∫ a, addPoint a ∂P ≤
        (2 * C) *
          (Real.sqrt (tauAtScale P m k p q) *
            Real.sqrt (Ch04.expectedResponseJCubeSet P (originCube d k) p q)) := by
    dsimp only [addPoint]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hSqrtBound (mul_nonneg (by norm_num) hC)
  have hOscIntegral :
      ∫ a, oscPoint a ∂P =
        Cosc * scaleSep * Ch04.expectedResponseJCubeSet P Q p q := by
    simp [oscPoint, Ch04.expectedResponseJCubeSet, integral_const_mul, mul_assoc]
  have hGradIntegral :
      ∫ a, gradPoint a ∂P =
        (1 / 2 : ℝ) * ‖q0‖ *
          (((Fintype.card (Fin d) : ℝ) * gradCoeff) *
            ∫ a, gradWeak a ∂P) := by
    simp [gradPoint, integral_const_mul, mul_assoc]
  have hFluxIntegral :
      ∫ a, fluxPoint a ∂P =
        (1 / 2 : ℝ) * ‖p0‖ *
          (((Fintype.card (Fin d) : ℝ) * fluxCoeff) *
            ∫ a, fluxWeak a ∂P) := by
    simp [fluxPoint, integral_const_mul, mul_assoc]
  have hCauchy :
      ∫ a, scaledGrad a * scaledFlux a ∂P ≤
        Real.sqrt (∫ a, (scaledGrad a) ^ 2 ∂P) *
          Real.sqrt (∫ a, (scaledFlux a) ^ 2 ∂P) :=
    integral_mul_le_sqrt_integral_sq_mul_sqrt_integral_sq_of_ae_nonneg
      (X := scaledGrad) (Y := scaledFlux)
      (by simpa [scaledGrad, gradWeak, Q] using hGradSq)
      (by simpa [scaledFlux, fluxWeak, Q] using hFluxSq)
      hGradNonneg hFluxNonneg
  have hProductBound :
      ∫ a, productPoint a ∂P ≤
        Cprod *
          (Real.sqrt (∫ a, (scaledGrad a) ^ 2 ∂P) *
            Real.sqrt (∫ a, (scaledFlux a) ^ 2 ∂P)) := by
    dsimp only [productPoint]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hCauchy hCprod
  calc
    ∫ a,
        jUpperWeakNormManuscriptPointwiseRHSAtScale m k s t
          C Cosc scaleSep BφS BφT Cprod p q p0 q0 a ∂P
        =
      ∫ a, addPoint a ∂P +
        (∫ a, oscPoint a ∂P +
          ((∫ a, gradPoint a ∂P + ∫ a, fluxPoint a ∂P) +
            ∫ a, productPoint a ∂P)) := hIntegral_eq
    _ ≤
      (2 * C) *
          (Real.sqrt (tauAtScale P m k p q) *
            Real.sqrt (Ch04.expectedResponseJCubeSet P (originCube d k) p q)) +
        (∫ a, oscPoint a ∂P +
          ((∫ a, gradPoint a ∂P + ∫ a, fluxPoint a ∂P) +
            Cprod *
              (Real.sqrt (∫ a, (scaledGrad a) ^ 2 ∂P) *
                Real.sqrt (∫ a, (scaledFlux a) ^ 2 ∂P)))) := by
          exact add_le_add hAddBound
            (add_le_add_left (add_le_add_left hProductBound _) _)
    _ =
        jUpperWeakNormManuscriptExpectedRHSAtScale P m k s t
          C Cosc scaleSep BφS BφT Cprod p q p0 q0 := by
        rw [hOscIntegral, hGradIntegral, hFluxIntegral]
        simp [jUpperWeakNormManuscriptExpectedRHSAtScale, gradWeak, fluxWeak,
          scaledGrad, scaledFlux, gradCoeff, fluxCoeff, Q, add_assoc, mul_assoc]

theorem integrable_jUpperWeakNormManuscriptPointwiseRHSAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) {k m : ℤ} (hkm : k ≤ m)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (C Cosc scaleSep BφS BφT Cprod : ℝ) (p q p0 q0 : Vec d)
    (hParent :
      Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q) P)
    (hDesc : ∀ R, R ∈ descendantsAtScale (originCube d m) k →
      Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P)
    (hGradWeak :
      Integrable
        (fun a : RegCoeffField d => Ch04.canonicalScalarResponseGradientWeakNormCubeSet
          (originCube d m) s p q p0 a.toFun) P)
    (hFluxWeak :
      Integrable
        (fun a : RegCoeffField d => Ch04.canonicalScalarResponseFluxWeakNormCubeSet
          (originCube d m) t p q q0 a.toFun) P)
    (hGradSq :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.canonicalScalarResponseGradientWeakNormCubeSet
            (originCube d m) s p q p0 a.toFun) ^ 2) P)
    (hFluxSq :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
            (originCube d m) t p q q0 a.toFun) ^ 2) P) :
    Integrable
      (jUpperWeakNormManuscriptPointwiseRHSAtScale m k s t
        C Cosc scaleSep BφS BφT Cprod p q p0 q0) P := by
  let : IsProbabilityMeasure P := hP.isProbability
  let Q : TriadicCube d := originCube d m
  let j : ℕ := Int.toNat (m - k)
  let childAverage : RegCoeffField d → ℝ :=
    fun a => descendantsAverage Q j (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a)
  let gradWeak : RegCoeffField d → ℝ :=
    fun a => Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun
  let fluxWeak : RegCoeffField d → ℝ :=
    fun a => Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun
  let gradCoeff : ℝ :=
    (3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovScaleWeight (-s) Q * BφS
  let fluxCoeff : ℝ :=
    (3 : ℝ) ^ ((d : ℝ) + t) * cubeBesovScaleWeight (-t) Q * BφT
  let scaledGrad : RegCoeffField d → ℝ := gradWeak
  let scaledFlux : RegCoeffField d → ℝ := fluxWeak
  let addPoint : RegCoeffField d → ℝ :=
    fun a =>
      (2 * C) *
        (Real.sqrt (responseJAdditivityDefectAtScale m k p q a) *
          Real.sqrt (childAverage a))
  let oscPoint : RegCoeffField d → ℝ :=
    fun a => Cosc * scaleSep * Ch04.restrictionResponseJObservableCubeSet Q p q a
  let gradPoint : RegCoeffField d → ℝ :=
    fun a =>
      (1 / 2 : ℝ) * ‖q0‖ *
        (((Fintype.card (Fin d) : ℝ) * gradCoeff) * gradWeak a)
  let fluxPoint : RegCoeffField d → ℝ :=
    fun a =>
      (1 / 2 : ℝ) * ‖p0‖ *
        (((Fintype.card (Fin d) : ℝ) * fluxCoeff) * fluxWeak a)
  let productPoint : RegCoeffField d → ℝ :=
    fun a => Cprod * (scaledGrad a * scaledFlux a)
  have hDescDepth :
      ∀ R, R ∈ descendantsAtDepth Q j →
        Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P := by
    intro R hR
    exact hDesc R (by
      simpa [Q, j, descendantsAtScale_eq_descendantsAtDepth (originCube d m) hkm]
        using! hR)
  have hChildInt : Integrable childAverage P := by
    simpa [childAverage, Q, j] using
      Ch04.integrable_descendantsAverage_restrictionResponseJObservableCubeSet hDescDepth
  have hDefectInt :
      Integrable (responseJAdditivityDefectAtScale m k p q) P :=
    integrable_responseJAdditivityDefectAtScale hkm p q hParent hDesc
  have hDefectNonneg :
      0 ≤ᵐ[P] responseJAdditivityDefectAtScale m k p q :=
    responseJAdditivityDefectAtScale_nonneg_ae hP hkm p q
  have hChildNonneg : 0 ≤ᵐ[P] childAverage := by
    filter_upwards with a
    simpa [childAverage, Q, j] using
      descendantsAverage_restrictionResponseJObservableCubeSet_nonneg Q j p q a
  have hSqrtProdInt :
      Integrable
        (fun a : RegCoeffField d =>
          Real.sqrt (responseJAdditivityDefectAtScale m k p q a) *
            Real.sqrt (childAverage a)) P :=
    integrable_sqrt_mul_sqrt_of_integrable_of_ae_nonneg
      (A := responseJAdditivityDefectAtScale m k p q)
      (B := childAverage) hDefectInt hChildInt hDefectNonneg hChildNonneg
  have hAddInt : Integrable addPoint P := by
    simpa [addPoint] using hSqrtProdInt.const_mul (2 * C)
  have hOscInt : Integrable oscPoint P := by
    simpa [oscPoint, Q] using hParent.const_mul (Cosc * scaleSep)
  have hGradInt : Integrable gradPoint P := by
    refine
      (hGradWeak.const_mul
        ((1 / 2 : ℝ) * ‖q0‖ * ((Fintype.card (Fin d) : ℝ) * gradCoeff))).congr ?_
    filter_upwards with a
    simp [gradPoint, gradWeak, Q, mul_assoc]
  have hFluxInt : Integrable fluxPoint P := by
    refine
      (hFluxWeak.const_mul
        ((1 / 2 : ℝ) * ‖p0‖ * ((Fintype.card (Fin d) : ℝ) * fluxCoeff))).congr ?_
    filter_upwards with a
    simp [fluxPoint, fluxWeak, Q, mul_assoc]
  have hGradNonneg : 0 ≤ᵐ[P] scaledGrad := by
    simpa [scaledGrad, gradWeak, Q] using
      canonicalScalarResponseGradientWeakNormCubeSet_nonneg_ae hP Q hs p q p0
  have hFluxNonneg : 0 ≤ᵐ[P] scaledFlux := by
    simpa [scaledFlux, fluxWeak, Q] using
      canonicalScalarResponseFluxWeakNormCubeSet_nonneg_ae hP Q ht p q q0
  have hScaledProdInt : Integrable (fun a => scaledGrad a * scaledFlux a) P :=
    integrable_mul_of_integrable_sq_of_ae_nonneg
      (X := scaledGrad) (Y := scaledFlux)
      (by simpa [scaledGrad, gradWeak, Q] using hGradSq)
      (by simpa [scaledFlux, fluxWeak, Q] using hFluxSq)
      hGradNonneg hFluxNonneg
  have hProductInt : Integrable productPoint P := by
    simpa [productPoint] using hScaledProdInt.const_mul Cprod
  have hSumInt :
      Integrable
        (fun a : RegCoeffField d =>
          (addPoint a + oscPoint a) + ((gradPoint a + fluxPoint a) + productPoint a)) P :=
    (hAddInt.add hOscInt).add ((hGradInt.add hFluxInt).add hProductInt)
  refine hSumInt.congr ?_
  filter_upwards with a
  simp [jUpperWeakNormManuscriptPointwiseRHSAtScale, addPoint, oscPoint, gradPoint,
    fluxPoint, productPoint, childAverage, gradWeak, fluxWeak, scaledGrad,
    scaledFlux, gradCoeff, fluxCoeff, Q, j, add_assoc, add_comm, mul_assoc]
  ring

end

end JUpperBoundWeakNorms
end Section53
end Ch05
end Book
end Homogenization
