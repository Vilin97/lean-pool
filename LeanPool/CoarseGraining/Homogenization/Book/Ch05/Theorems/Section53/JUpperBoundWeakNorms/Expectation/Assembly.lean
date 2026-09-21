/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Expectation.AEBound

/-! # Assembly -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundWeakNorms

/-!
# ExpectationAssembly

Final expectation assembly for the first Section 5.3 lemma.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

noncomputable section

/-- Expectation reduction against the named pointwise RHS for the first
Section 5.3 lemma.  This is still private: later steps prove the a.e. bound and
integrability from the deterministic cutoff construction and Ch4 law-facing
surfaces. -/
theorem expectedResponseJCubeSet_sub_half_dot_le_integral_jUpperWeakNormPointwiseRHSAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    {k m : ℤ} (hk_nonneg : 0 ≤ k) (hkm : k ≤ m)
    (s t : ℝ) (φ : Vec d → ℝ) (cutoffGradient : Vec d → Vec d)
    (C Cosc scaleSep BφS BφT cutoffCircOne poincareConst cutoffConstant
      centeredCutoffConstant : ℝ)
    (p q p0 q0 : Vec d)
    (hφ_int : IntegrableOn φ (cubeSet (originCube d m)) volume)
    (hMean : cubeAverage (originCube d m) φ = 1)
    (hParent :
      Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q) P)
    (hJ : ∀ R, R ∈ descendantsAtScale (originCube d m) k →
      Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P)
    (hRHS :
      Integrable
        (jUpperWeakNormPointwiseRHSAtScale m k s t cutoffGradient
          C Cosc scaleSep BφS BφT cutoffCircOne poincareConst cutoffConstant
          centeredCutoffConstant p q p0 q0) P)
    (hBound :
      ∀ᵐ a ∂P,
        |centeredJMinusCutoffWeightedChildAtScale m k φ p q p0 q0 a| ≤
          jUpperWeakNormPointwiseRHSAtScale m k s t cutoffGradient
            C Cosc scaleSep BφS BφT cutoffCircOne poincareConst cutoffConstant
            centeredCutoffConstant p q p0 q0 a) :
    Ch04.expectedResponseJCubeSet P (originCube d m) p q -
        (1 / 2 : ℝ) * vecDot p0 q0 ≤
      ∫ a,
        jUpperWeakNormPointwiseRHSAtScale m k s t cutoffGradient
          C Cosc scaleSep BφS BφT cutoffCircOne poincareConst cutoffConstant
          centeredCutoffConstant p q p0 q0 a ∂P := by
  exact
    integral_centeredJMinusCutoffWeightedChildAtScale_le_integral_of_ae_abs_le
      (P := P) hP hstat hk_nonneg hkm φ p q p0 q0
      (jUpperWeakNormPointwiseRHSAtScale m k s t cutoffGradient
        C Cosc scaleSep BφS BφT cutoffCircOne poincareConst cutoffConstant
        centeredCutoffConstant p q p0 q0)
      hφ_int hMean hParent hJ hRHS hBound

/-- Integrability of the Ch4-facing pointwise RHS from integrability of its
remaining scalar-response weak-norm and cutoff-product components. -/
theorem integrable_jUpperWeakNormPointwiseRHSAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    {k m : ℤ} (hkm : k ≤ m)
    (s t : ℝ) (cutoffGradient : Vec d → Vec d)
    (C Cosc scaleSep BφS BφT cutoffCircOne poincareConst cutoffConstant
      centeredCutoffConstant : ℝ)
    (p q p0 q0 : Vec d)
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
    (hProduct :
      Integrable
        (fun a : RegCoeffField d =>
          cutoffProductBridgeRHS (originCube d m) s cutoffGradient
            (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
              (originCube d m) 1 p q q0 a.toFun)
            (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
              (originCube d m) s p q q0 a.toFun)
            ‖Ch04.canonicalScalarResponseFluxAverageCubeSet
              (originCube d m) (originCube d m) p q a.toFun - q0‖
            cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant) P) :
    Integrable
      (jUpperWeakNormPointwiseRHSAtScale m k s t cutoffGradient
        C Cosc scaleSep BφS BφT cutoffCircOne poincareConst cutoffConstant
        centeredCutoffConstant p q p0 q0) P := by
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
    fun a =>
      cutoffProductBridgeRHS Q s cutoffGradient
        (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q 1 p q q0 a.toFun)
        (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q s p q q0 a.toFun)
        ‖Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun - q0‖
        cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant
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
  have hProductInt : Integrable productPoint P := by
    simpa [productPoint, Q] using hProduct
  have hSumInt :
      Integrable
        (fun a : RegCoeffField d =>
          (addPoint a + oscPoint a) + ((gradPoint a + fluxPoint a) + productPoint a)) P :=
    (hAddInt.add hOscInt).add ((hGradInt.add hFluxInt).add hProductInt)
  refine hSumInt.congr ?_
  filter_upwards with a
  simp [jUpperWeakNormPointwiseRHSAtScale, addPoint, oscPoint, gradPoint,
    fluxPoint, productPoint, childAverage, gradWeak, fluxWeak, gradCoeff,
    fluxCoeff, Q, j, add_assoc, add_comm, mul_assoc]

/-- Composed expectation assembly for the first Section 5.3 lemma: the
centered parent response is bounded directly by the expected manuscript RHS. -/
theorem expectedResponseJCubeSet_sub_half_dot_le_jUpperWeakNormExpectedRHSAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    {k m : ℤ} (hk_nonneg : 0 ≤ k) (hkm : k ≤ m)
    (s t : ℝ) (φ : Vec d → ℝ) (cutoffGradient : Vec d → Vec d)
    (C Cosc scaleSep BφS BφT cutoffCircOne poincareConst cutoffConstant
      centeredCutoffConstant : ℝ)
    (p q p0 q0 : Vec d)
    (hC : 0 ≤ C)
    (hφ_int : IntegrableOn φ (cubeSet (originCube d m)) volume)
    (hMean : cubeAverage (originCube d m) φ = 1)
    (hParent :
      Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q) P)
    (hJ : ∀ R, R ∈ descendantsAtScale (originCube d m) k →
      Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P)
    (hGradWeak :
      Integrable
        (fun a : RegCoeffField d => Ch04.canonicalScalarResponseGradientWeakNormCubeSet
          (originCube d m) s p q p0 a.toFun) P)
    (hFluxWeak :
      Integrable
        (fun a : RegCoeffField d => Ch04.canonicalScalarResponseFluxWeakNormCubeSet
          (originCube d m) t p q q0 a.toFun) P)
    (hProduct :
      Integrable
        (fun a : RegCoeffField d =>
          cutoffProductBridgeRHS (originCube d m) s cutoffGradient
            (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
              (originCube d m) 1 p q q0 a.toFun)
            (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
              (originCube d m) s p q q0 a.toFun)
            ‖Ch04.canonicalScalarResponseFluxAverageCubeSet
              (originCube d m) (originCube d m) p q a.toFun - q0‖
            cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant) P)
    (hBound :
      ∀ᵐ a ∂P,
        |centeredJMinusCutoffWeightedChildAtScale m k φ p q p0 q0 a| ≤
          jUpperWeakNormPointwiseRHSAtScale m k s t cutoffGradient
            C Cosc scaleSep BφS BφT cutoffCircOne poincareConst cutoffConstant
            centeredCutoffConstant p q p0 q0 a) :
    Ch04.expectedResponseJCubeSet P (originCube d m) p q -
        (1 / 2 : ℝ) * vecDot p0 q0 ≤
      jUpperWeakNormExpectedRHSAtScale P m k s t cutoffGradient
        C Cosc scaleSep BφS BφT cutoffCircOne poincareConst cutoffConstant
        centeredCutoffConstant p q p0 q0 := by
  have hRHS :
      Integrable
        (jUpperWeakNormPointwiseRHSAtScale m k s t cutoffGradient
          C Cosc scaleSep BφS BφT cutoffCircOne poincareConst cutoffConstant
          centeredCutoffConstant p q p0 q0) P :=
    integrable_jUpperWeakNormPointwiseRHSAtScale
      hP hkm s t cutoffGradient C Cosc scaleSep BφS BφT cutoffCircOne
      poincareConst cutoffConstant centeredCutoffConstant p q p0 q0
      hParent hJ hGradWeak hFluxWeak hProduct
  have hIntegralBound :
      Ch04.expectedResponseJCubeSet P (originCube d m) p q -
          (1 / 2 : ℝ) * vecDot p0 q0 ≤
        ∫ a,
          jUpperWeakNormPointwiseRHSAtScale m k s t cutoffGradient
            C Cosc scaleSep BφS BφT cutoffCircOne poincareConst cutoffConstant
            centeredCutoffConstant p q p0 q0 a ∂P :=
    expectedResponseJCubeSet_sub_half_dot_le_integral_jUpperWeakNormPointwiseRHSAtScale
      hP hstat hk_nonneg hkm s t φ cutoffGradient C Cosc scaleSep BφS BφT
      cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant p q p0 q0
      hφ_int hMean hParent hJ hRHS hBound
  have hExpectedBound :
      ∫ a,
          jUpperWeakNormPointwiseRHSAtScale m k s t cutoffGradient
            C Cosc scaleSep BφS BφT cutoffCircOne poincareConst cutoffConstant
            centeredCutoffConstant p q p0 q0 a ∂P
        ≤
          jUpperWeakNormExpectedRHSAtScale P m k s t cutoffGradient
            C Cosc scaleSep BφS BφT cutoffCircOne poincareConst cutoffConstant
            centeredCutoffConstant p q p0 q0 :=
    integral_jUpperWeakNormPointwiseRHSAtScale_le_expectedRHS
      hP hstat hk_nonneg hkm s t cutoffGradient C Cosc scaleSep BφS BφT
      cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant p q p0 q0
      hC hParent hJ hGradWeak hFluxWeak hProduct
  exact hIntegralBound.trans hExpectedBound

/-- Replace the remaining cutoff-product bridge expectation by the
manuscript-facing Cauchy product of note-normalized gradient/flux weak-norm
square expectations.  The pointwise product replacement is kept private here; it
is the next deterministic source theorem, not part of the public Section 5.3
statement. -/
theorem jUpperWeakNormExpectedRHSAtScale_le_manuscriptExpectedRHSAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (m k : ℤ) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t)
    (cutoffGradient : Vec d → Vec d)
    (C Cosc scaleSep BφS BφT cutoffCircOne poincareConst cutoffConstant
      centeredCutoffConstant Cprod : ℝ)
    (p q p0 q0 : Vec d)
    (hCprod : 0 ≤ Cprod)
    (hGradSq :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.canonicalScalarResponseGradientWeakNormCubeSet
            (originCube d m) s p q p0 a.toFun) ^ 2) P)
    (hFluxSq :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
            (originCube d m) t p q q0 a.toFun) ^ 2) P)
    (hProductInt :
      Integrable
        (fun a : RegCoeffField d =>
          cutoffProductBridgeRHS (originCube d m) s cutoffGradient
            (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
              (originCube d m) 1 p q q0 a.toFun)
            (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
              (originCube d m) s p q q0 a.toFun)
            ‖Ch04.canonicalScalarResponseFluxAverageCubeSet
              (originCube d m) (originCube d m) p q a.toFun - q0‖
            cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant) P)
    (hProductPoint :
      ∀ᵐ a ∂P,
        cutoffProductBridgeRHS (originCube d m) s cutoffGradient
            (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
              (originCube d m) 1 p q q0 a.toFun)
            (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
              (originCube d m) s p q q0 a.toFun)
            ‖Ch04.canonicalScalarResponseFluxAverageCubeSet
              (originCube d m) (originCube d m) p q a.toFun - q0‖
            cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant
          ≤
        Cprod *
          (Ch04.canonicalScalarResponseGradientWeakNormCubeSet
              (originCube d m) s p q p0 a.toFun *
            Ch04.canonicalScalarResponseFluxWeakNormCubeSet
              (originCube d m) t p q q0 a.toFun)) :
    jUpperWeakNormExpectedRHSAtScale P m k s t cutoffGradient
        C Cosc scaleSep BφS BφT cutoffCircOne poincareConst cutoffConstant
        centeredCutoffConstant p q p0 q0
      ≤
      jUpperWeakNormManuscriptExpectedRHSAtScale P m k s t
        C Cosc scaleSep BφS BφT Cprod p q p0 q0 := by
  let Q : TriadicCube d := originCube d m
  have hprod :
      ∫ a,
          cutoffProductBridgeRHS Q s cutoffGradient
            (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q 1 p q q0 a.toFun)
            (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q s p q q0 a.toFun)
            ‖Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun - q0‖
            cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant ∂P
        ≤
          Cprod *
            (Real.sqrt
                (∫ a,
                  (Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun) ^ 2 ∂P) *
              Real.sqrt
                (∫ a,
                  (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun) ^ 2 ∂P)) := by
    simpa [Q] using
      integral_cutoffProductBridgeRHS_le_weakNormSquareProduct
        (P := P) hP Q hs ht cutoffGradient cutoffCircOne poincareConst
        cutoffConstant centeredCutoffConstant Cprod p q p0 q0 hCprod
        hGradSq hFluxSq hProductInt hProductPoint
  simpa [jUpperWeakNormExpectedRHSAtScale,
    jUpperWeakNormManuscriptExpectedRHSAtScale, Q, add_assoc] using
    add_le_add_left hprod
      ((2 * C) *
          (Real.sqrt (tauAtScale P m k p q) *
            Real.sqrt (Ch04.expectedResponseJCubeSet P (originCube d k) p q)) +
        Cosc * scaleSep * Ch04.expectedResponseJCubeSet P Q p q +
          ((1 / 2 : ℝ) * ‖q0‖ *
              ((((Fintype.card (Fin d) : ℝ) *
                ((3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovScaleWeight (-s) Q * BφS)) *
                  ∫ a, Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun ∂P)) +
            (1 / 2 : ℝ) * ‖p0‖ *
              ((((Fintype.card (Fin d) : ℝ) *
                ((3 : ℝ) ^ ((d : ℝ) + t) * cubeBesovScaleWeight (-t) Q * BφT)) *
                  ∫ a, Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun ∂P))))

/-- Composed private assembly landing on the manuscript-facing expected RHS.
The only remaining non-manuscript input is the private deterministic product
replacement `hProductPoint`, which must be discharged by the next deterministic
cutoff-product theorem rather than exposed publicly. -/
theorem expectedResponseJCubeSet_sub_half_dot_le_jUpperWeakNormManuscriptExpectedRHSAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    {k m : ℤ} (hk_nonneg : 0 ≤ k) (hkm : k ≤ m)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (φ : Vec d → ℝ) (cutoffGradient : Vec d → Vec d)
    (C Cosc scaleSep BφS BφT cutoffCircOne poincareConst cutoffConstant
      centeredCutoffConstant Cprod : ℝ)
    (p q p0 q0 : Vec d)
    (hC : 0 ≤ C) (hCprod : 0 ≤ Cprod)
    (hφ_int : IntegrableOn φ (cubeSet (originCube d m)) volume)
    (hMean : cubeAverage (originCube d m) φ = 1)
    (hParent :
      Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q) P)
    (hJ : ∀ R, R ∈ descendantsAtScale (originCube d m) k →
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
            (originCube d m) t p q q0 a.toFun) ^ 2) P)
    (hProduct :
      Integrable
        (fun a : RegCoeffField d =>
          cutoffProductBridgeRHS (originCube d m) s cutoffGradient
            (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
              (originCube d m) 1 p q q0 a.toFun)
            (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
              (originCube d m) s p q q0 a.toFun)
            ‖Ch04.canonicalScalarResponseFluxAverageCubeSet
              (originCube d m) (originCube d m) p q a.toFun - q0‖
            cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant) P)
    (hProductPoint :
      ∀ᵐ a ∂P,
        cutoffProductBridgeRHS (originCube d m) s cutoffGradient
            (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
              (originCube d m) 1 p q q0 a.toFun)
            (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
              (originCube d m) s p q q0 a.toFun)
            ‖Ch04.canonicalScalarResponseFluxAverageCubeSet
              (originCube d m) (originCube d m) p q a.toFun - q0‖
            cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant
          ≤
        Cprod *
          (Ch04.canonicalScalarResponseGradientWeakNormCubeSet
              (originCube d m) s p q p0 a.toFun *
            Ch04.canonicalScalarResponseFluxWeakNormCubeSet
              (originCube d m) t p q q0 a.toFun))
    (hBound :
      ∀ᵐ a ∂P,
        |centeredJMinusCutoffWeightedChildAtScale m k φ p q p0 q0 a| ≤
          jUpperWeakNormPointwiseRHSAtScale m k s t cutoffGradient
            C Cosc scaleSep BφS BφT cutoffCircOne poincareConst cutoffConstant
            centeredCutoffConstant p q p0 q0 a) :
    Ch04.expectedResponseJCubeSet P (originCube d m) p q -
        (1 / 2 : ℝ) * vecDot p0 q0 ≤
      jUpperWeakNormManuscriptExpectedRHSAtScale P m k s t
        C Cosc scaleSep BφS BφT Cprod p q p0 q0 := by
  have hold :
      Ch04.expectedResponseJCubeSet P (originCube d m) p q -
          (1 / 2 : ℝ) * vecDot p0 q0 ≤
        jUpperWeakNormExpectedRHSAtScale P m k s t cutoffGradient
          C Cosc scaleSep BφS BφT cutoffCircOne poincareConst cutoffConstant
          centeredCutoffConstant p q p0 q0 :=
    expectedResponseJCubeSet_sub_half_dot_le_jUpperWeakNormExpectedRHSAtScale
      hP hstat hk_nonneg hkm s t φ cutoffGradient C Cosc scaleSep BφS BφT
      cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant p q p0 q0
      hC hφ_int hMean hParent hJ hGradWeak hFluxWeak hProduct hBound
  have hreplace :
      jUpperWeakNormExpectedRHSAtScale P m k s t cutoffGradient
          C Cosc scaleSep BφS BφT cutoffCircOne poincareConst cutoffConstant
          centeredCutoffConstant p q p0 q0
        ≤
        jUpperWeakNormManuscriptExpectedRHSAtScale P m k s t
          C Cosc scaleSep BφS BφT Cprod p q p0 q0 :=
    jUpperWeakNormExpectedRHSAtScale_le_manuscriptExpectedRHSAtScale
      hP m k hs ht cutoffGradient C Cosc scaleSep BφS BφT cutoffCircOne
      poincareConst cutoffConstant centeredCutoffConstant Cprod p q p0 q0
      hCprod hGradSq hFluxSq hProduct hProductPoint
  exact hold.trans hreplace

/-- Composed expectation assembly through the manuscript pointwise RHS.  This
route has no cutoff-product bridge expectation and no `hProductPoint` input. -/
theorem expectedResponseJCubeSet_sub_half_dot_le_jUpperWeakNormManuscriptExpectedRHSAtScale_of_manuscriptPointwise
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    {k m : ℤ} (hk_nonneg : 0 ≤ k) (hkm : k ≤ m)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (φ : Vec d → ℝ)
    (C Cosc scaleSep BφS BφT Cprod : ℝ)
    (p q p0 q0 : Vec d)
    (hC : 0 ≤ C) (hCprod : 0 ≤ Cprod)
    (hφ_int : IntegrableOn φ (cubeSet (originCube d m)) volume)
    (hMean : cubeAverage (originCube d m) φ = 1)
    (hParent :
      Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q) P)
    (hJ : ∀ R, R ∈ descendantsAtScale (originCube d m) k →
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
            (originCube d m) t p q q0 a.toFun) ^ 2) P)
    (hBound :
      ∀ᵐ a ∂P,
        |centeredJMinusCutoffWeightedChildAtScale m k φ p q p0 q0 a| ≤
          jUpperWeakNormManuscriptPointwiseRHSAtScale m k s t
            C Cosc scaleSep BφS BφT Cprod p q p0 q0 a) :
    Ch04.expectedResponseJCubeSet P (originCube d m) p q -
        (1 / 2 : ℝ) * vecDot p0 q0 ≤
      jUpperWeakNormManuscriptExpectedRHSAtScale P m k s t
        C Cosc scaleSep BφS BφT Cprod p q p0 q0 := by
  have hRHS :
      Integrable
        (jUpperWeakNormManuscriptPointwiseRHSAtScale m k s t
          C Cosc scaleSep BφS BφT Cprod p q p0 q0) P :=
    integrable_jUpperWeakNormManuscriptPointwiseRHSAtScale
      hP hkm hs ht C Cosc scaleSep BφS BφT Cprod p q p0 q0
      hParent hJ hGradWeak hFluxWeak hGradSq hFluxSq
  have hIntegralBound :
      Ch04.expectedResponseJCubeSet P (originCube d m) p q -
          (1 / 2 : ℝ) * vecDot p0 q0 ≤
        ∫ a,
          jUpperWeakNormManuscriptPointwiseRHSAtScale m k s t
            C Cosc scaleSep BφS BφT Cprod p q p0 q0 a ∂P :=
    integral_centeredJMinusCutoffWeightedChildAtScale_le_integral_of_ae_abs_le
      (P := P) hP hstat hk_nonneg hkm φ p q p0 q0
      (jUpperWeakNormManuscriptPointwiseRHSAtScale m k s t
        C Cosc scaleSep BφS BφT Cprod p q p0 q0)
      hφ_int hMean hParent hJ hRHS hBound
  have hExpectedBound :
      ∫ a,
          jUpperWeakNormManuscriptPointwiseRHSAtScale m k s t
            C Cosc scaleSep BφS BφT Cprod p q p0 q0 a ∂P
        ≤
          jUpperWeakNormManuscriptExpectedRHSAtScale P m k s t
            C Cosc scaleSep BφS BφT Cprod p q p0 q0 :=
    integral_jUpperWeakNormManuscriptPointwiseRHSAtScale_le_manuscriptExpectedRHSAtScale
      hP hstat hk_nonneg hkm hs ht C Cosc scaleSep BφS BφT Cprod p q p0 q0
      hC hCprod hParent hJ hGradWeak hFluxWeak hGradSq hFluxSq
  exact hIntegralBound.trans hExpectedBound

/-- Expectation assembly with the a.e. pointwise bridge supplied by the
deterministic cutoff controls.  The remaining inputs are law-facing
integrability/moment facts for the Ch4 observables, not fixed-coefficient proof
packages. -/
theorem expectedResponseJCubeSet_sub_half_dot_le_jUpperWeakNormManuscriptExpectedRHSAtScale_of_cutoffControls
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    {k m : ℤ} (hk_nonneg : 0 ≤ k) (hkm : k ≤ m)
    {s t : ℝ} (hs : 0 < s) (hs_lt_one : s < 1) (ht : 0 < t)
    (hst : s + t ≤ 1)
    (φ : Vec d → ℝ)
    (C B Cosc scaleSep BφS BφT cutoffDerivative Cprod : ℝ)
    (p q p0 q0 : Vec d)
    (hC : 0 ≤ C) (hCprod : 0 ≤ Cprod)
    (hCut :
      ∀ R ∈ descendantsAtDepth (originCube d m) (Int.toNat (m - k)),
        |1 - cubeAverage R φ| ≤ C)
    (hMean : cubeAverage (originCube d m) φ = 1)
    (hφ_meas : AEStronglyMeasurable φ (volumeMeasureOn (cubeSet (originCube d m))))
    (hφ_bound : ∀ᵐ x ∂ volumeMeasureOn (cubeSet (originCube d m)), ‖φ x‖ ≤ B)
    (hOscPoint :
      ∀ R ∈ descendantsAtDepth (originCube d m) (Int.toNat (m - k)),
        ∀ᵐ x ∂ volumeMeasureOn (cubeSet R),
          |cubeAverage R φ - φ x| ≤ Cosc * scaleSep)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ openCubeSet (originCube d m))
    (hcutoffDerivative : 0 ≤ cutoffDerivative)
    (hBφS : 0 ≤ BφS) (hBφT : 0 ≤ BφT)
    (hφDualS :
      ∀ N : ℕ,
        cubeBesovDualTestNorm (originCube d m) s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N φ ≤ BφS)
    (hφDualT :
      ∀ N : ℕ,
        cubeBesovDualTestNorm (originCube d m) t (2 : ℝ≥0∞) (1 : ℝ≥0∞) N φ ≤ BφT)
    (hφMem : CubeBesovDualLocalMemLpGlobal (originCube d m) (2 : ℝ≥0∞) φ)
    (hcutoffGradient :
      MemLp (scalarCutoffGradientField φ) ∞ (normalizedCubeMeasure (originCube d m)))
    (hcutoffSmooth :
      ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞)
        (fun x => scalarCutoffGradientField φ x i))
    (hcutoffDeriv :
      ∀ i : Fin d, ∀ z ∈ cubeSet (originCube d m),
        ‖fderiv ℝ (fun x => scalarCutoffGradientField φ x i) z‖ ≤ cutoffDerivative)
    (hProductCoeff :
      cutoffProductScaledWeakNormCoeff (originCube d m) s t cutoffDerivative
          (scalarCutoffGradientField φ) *
          cubeBesovScaleWeight (-s) (originCube d m) *
          cubeBesovScaleWeight (-t) (originCube d m) ≤ Cprod)
    (hParent :
      Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q) P)
    (hJ : ∀ R, R ∈ descendantsAtScale (originCube d m) k →
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
    Ch04.expectedResponseJCubeSet P (originCube d m) p q -
        (1 / 2 : ℝ) * vecDot p0 q0 ≤
      jUpperWeakNormManuscriptExpectedRHSAtScale P m k s t
        C Cosc scaleSep BφS BφT Cprod p q p0 q0 := by
  have hφ_int : IntegrableOn φ (cubeSet (originCube d m)) volume := by
    simpa [volumeMeasureOn] using
      (IntegrableOn.of_bound
        (μ := volume) (s := cubeSet (originCube d m)) (f := φ)
        (volume_cubeSet_lt_top (originCube d m))
        (by simpa [volumeMeasureOn] using hφ_meas) B
        (by simpa [volumeMeasureOn] using hφ_bound))
  have hBound :
      ∀ᵐ a ∂P,
        |centeredJMinusCutoffWeightedChildAtScale m k φ p q p0 q0 a| ≤
          jUpperWeakNormManuscriptPointwiseRHSAtScale m k s t
            C Cosc scaleSep BφS BφT Cprod p q p0 q0 a :=
    ae_abs_centeredJMinusCutoffWeightedChildAtScale_le_jUpperWeakNormManuscriptPointwiseRHS
      (P := P) hP m k s t φ p q p0 q0 hC hCut hMean hφ_meas hφ_bound
      hOscPoint hφ hφ_compact hφ_sub hcutoffDerivative hs hs_lt_one ht hst
      hBφS hBφT hφDualS hφDualT hφMem hcutoffGradient hcutoffSmooth hcutoffDeriv
      hProductCoeff
  exact
    expectedResponseJCubeSet_sub_half_dot_le_jUpperWeakNormManuscriptExpectedRHSAtScale_of_manuscriptPointwise
      hP hstat hk_nonneg hkm hs ht φ C Cosc scaleSep BφS BφT Cprod p q p0 q0
      hC hCprod hφ_int hMean hParent hJ hGradWeak hFluxWeak hGradSq hFluxSq hBound

end

end JUpperBoundWeakNorms
end Section53
end Ch05
end Book
end Homogenization
