/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.DeterministicAssembly

/-! # RHS -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundWeakNorms

/-!
# ExpectationRHS

Expected right-hand sides and nonnegativity facts.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

noncomputable section

/-- Total Ch4-facing pointwise RHS for the first Section 5.3 lemma after the
deterministic split has been assembled.  The only non-total deterministic
objects have been rewritten to Ch4 observables. -/
noncomputable def jUpperWeakNormPointwiseRHSAtScale {d : ℕ}
    (m k : ℤ) (s t : ℝ) (cutoffGradient : Vec d → Vec d)
    (C Cosc scaleSep BφS BφT cutoffCircOne poincareConst cutoffConstant
      centeredCutoffConstant : ℝ)
    (p q p0 q0 : Vec d) : RegCoeffField d → ℝ :=
  fun a =>
    let Q : TriadicCube d := originCube d m
    let j : ℕ := Int.toNat (m - k)
    let childAverage :=
      descendantsAverage Q j (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a)
    let gradWeak := Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun
    let fluxWeak := Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun
    let gradCoeff := (3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovScaleWeight (-s) Q * BφS
    let fluxCoeff := (3 : ℝ) ^ ((d : ℝ) + t) * cubeBesovScaleWeight (-t) Q * BφT
    (2 * C) *
        (Real.sqrt (responseJAdditivityDefectAtScale m k p q a) *
          Real.sqrt childAverage) +
      Cosc * scaleSep * Ch04.restrictionResponseJObservableCubeSet Q p q a +
        ((1 / 2 : ℝ) * ‖q0‖ *
            (((Fintype.card (Fin d) : ℝ) * gradCoeff) * gradWeak) +
          (1 / 2 : ℝ) * ‖p0‖ *
            (((Fintype.card (Fin d) : ℝ) * fluxCoeff) * fluxWeak)) +
          cutoffProductBridgeRHS Q s cutoffGradient
            (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q 1 p q q0 a.toFun)
            (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q s p q q0 a.toFun)
            ‖Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun - q0‖
            cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant

/-- Pointwise RHS with the cutoff-product term already in the manuscript Cauchy
product form. -/
noncomputable def jUpperWeakNormManuscriptPointwiseRHSAtScale {d : ℕ}
    (m k : ℤ) (s t : ℝ)
    (C Cosc scaleSep BφS BφT Cprod : ℝ)
    (p q p0 q0 : Vec d) : RegCoeffField d → ℝ :=
  fun a =>
    let Q : TriadicCube d := originCube d m
    let j : ℕ := Int.toNat (m - k)
    let childAverage :=
      descendantsAverage Q j (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a)
    let gradWeak := Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun
    let fluxWeak := Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun
    let gradCoeff := (3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovScaleWeight (-s) Q * BφS
    let fluxCoeff := (3 : ℝ) ^ ((d : ℝ) + t) * cubeBesovScaleWeight (-t) Q * BφT
    let scaledGrad := gradWeak
    let scaledFlux := fluxWeak
    (2 * C) *
        (Real.sqrt (responseJAdditivityDefectAtScale m k p q a) *
          Real.sqrt childAverage) +
      Cosc * scaleSep * Ch04.restrictionResponseJObservableCubeSet Q p q a +
        ((1 / 2 : ℝ) * ‖q0‖ *
            (((Fintype.card (Fin d) : ℝ) * gradCoeff) * gradWeak) +
          (1 / 2 : ℝ) * ‖p0‖ *
            (((Fintype.card (Fin d) : ℝ) * fluxCoeff) * fluxWeak)) +
          Cprod * (scaledGrad * scaledFlux)

/-- Expected right-hand side after the first stochastic assembly step for
Lemma `l.J.upper.bound.weak.norms.homogenization.scale`.  The square-root
additivity term has been converted to `sqrt tau * sqrt E[J_k]`; the remaining
weak-norm and cutoff-product terms are still written as expectations of the
Ch4 scalar-response observables. -/
noncomputable def jUpperWeakNormExpectedRHSAtScale {d : ℕ}
    (P : Ch04.RestrictionCoeffLaw d) (m k : ℤ) (s t : ℝ)
    (cutoffGradient : Vec d → Vec d)
    (C Cosc scaleSep BφS BφT cutoffCircOne poincareConst cutoffConstant
      centeredCutoffConstant : ℝ)
    (p q p0 q0 : Vec d) : ℝ :=
  let Q : TriadicCube d := originCube d m
  let gradWeak : RegCoeffField d → ℝ := fun a => Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun
  let fluxWeak : RegCoeffField d → ℝ := fun a => Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun
  let gradCoeff := (3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovScaleWeight (-s) Q * BφS
  let fluxCoeff := (3 : ℝ) ^ ((d : ℝ) + t) * cubeBesovScaleWeight (-t) Q * BφT
  (2 * C) *
      (Real.sqrt (tauAtScale P m k p q) *
        Real.sqrt (Ch04.expectedResponseJCubeSet P (originCube d k) p q)) +
    Cosc * scaleSep * Ch04.expectedResponseJCubeSet P Q p q +
      ((1 / 2 : ℝ) * ‖q0‖ *
          (((Fintype.card (Fin d) : ℝ) * gradCoeff) *
            ∫ a, gradWeak a ∂P) +
        (1 / 2 : ℝ) * ‖p0‖ *
          (((Fintype.card (Fin d) : ℝ) * fluxCoeff) *
            ∫ a, fluxWeak a ∂P)) +
        ∫ a,
          cutoffProductBridgeRHS Q s cutoffGradient
            (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q 1 p q q0 a.toFun)
            (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q s p q q0 a.toFun)
            ‖Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun - q0‖
            cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant ∂P

/-- Manuscript-facing expected RHS for Lemma
`l.J.upper.bound.weak.norms.homogenization.scale`.  Compared with
`jUpperWeakNormExpectedRHSAtScale`, the cutoff-product bridge expectation has
been replaced by the final Cauchy product of the note-normalized gradient and
flux weak-norm square expectations. -/
noncomputable def jUpperWeakNormManuscriptExpectedRHSAtScale {d : ℕ}
    (P : Ch04.RestrictionCoeffLaw d) (m k : ℤ) (s t : ℝ)
    (C Cosc scaleSep BφS BφT Cprod : ℝ)
    (p q p0 q0 : Vec d) : ℝ :=
  let Q : TriadicCube d := originCube d m
  let gradWeak : RegCoeffField d → ℝ := fun a => Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun
  let fluxWeak : RegCoeffField d → ℝ := fun a => Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun
  let gradCoeff := (3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovScaleWeight (-s) Q * BφS
  let fluxCoeff := (3 : ℝ) ^ ((d : ℝ) + t) * cubeBesovScaleWeight (-t) Q * BφT
  let scaledGrad : RegCoeffField d → ℝ := gradWeak
  let scaledFlux : RegCoeffField d → ℝ := fluxWeak
  (2 * C) *
      (Real.sqrt (tauAtScale P m k p q) *
        Real.sqrt (Ch04.expectedResponseJCubeSet P (originCube d k) p q)) +
    Cosc * scaleSep * Ch04.expectedResponseJCubeSet P Q p q +
      ((1 / 2 : ℝ) * ‖q0‖ *
          (((Fintype.card (Fin d) : ℝ) * gradCoeff) *
            ∫ a, gradWeak a ∂P) +
        (1 / 2 : ℝ) * ‖p0‖ *
          (((Fintype.card (Fin d) : ℝ) * fluxCoeff) *
            ∫ a, fluxWeak a ∂P)) +
        Cprod *
          (Real.sqrt (∫ a, (scaledGrad a) ^ 2 ∂P) *
            Real.sqrt (∫ a, (scaledFlux a) ^ 2 ∂P))

/-- At origin scales, the deterministic child response average for the Ch4
dependent family is the total Ch4 descendant response average. -/
theorem childResponseJAverageOnDependentFamilyAtScale_eq_ch04
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (m k : ℤ) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    childResponseJAverageOnFamilyAtDepth F (originCube d m) (Int.toNat (m - k)) p q =
      descendantsAverage (originCube d m) (Int.toNat (m - k))
        (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a) := by
  intro F
  unfold childResponseJAverageOnFamilyAtDepth
  exact descendantsAverage_congr_of_eq_on_descendants
    (originCube d m) (Int.toNat (m - k)) (by
      intro R _hR
      exact responseJOnDependentFamily_eq_restrictionResponseJObservableCubeSet a ha R p q)

/-- The total Ch4 descendant response average is pointwise nonnegative. -/
theorem descendantsAverage_restrictionResponseJObservableCubeSet_nonneg
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (p q : Vec d)
    (a : RegCoeffField d) :
    0 ≤ descendantsAverage Q j
      (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a) := by
  simpa [Ch04.restrictionResponseJObservableCubeSet] using
    descendantsAverage_nonneg Q j
      (fun R => ResponseJ (cubeSet R) p q a)
      (fun R _hR => Ch04.restrictionResponseJObservableCubeSet_nonneg R p q a)

/-- The private additivity-defect observable is integrable when the parent and
child response observables are integrable. -/
theorem integrable_responseJAdditivityDefectAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    {k m : ℤ} (hkm : k ≤ m) (p q : Vec d)
    (hParent :
      Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q) P)
    (hDesc : ∀ R, R ∈ descendantsAtScale (originCube d m) k →
      Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P) :
    Integrable (responseJAdditivityDefectAtScale m k p q) P := by
  have hDescDepth :
      ∀ R, R ∈ descendantsAtDepth (originCube d m) (Int.toNat (m - k)) →
        Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P := by
    intro R hR
    exact hDesc R (by
      simpa [descendantsAtScale_eq_descendantsAtDepth (originCube d m) hkm] using! hR)
  have hAvgInt :
      Integrable
        (fun a : RegCoeffField d =>
          descendantsAverage (originCube d m) (Int.toNat (m - k))
            (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a)) P :=
    Ch04.integrable_descendantsAverage_restrictionResponseJObservableCubeSet hDescDepth
  simpa [responseJAdditivityDefectAtScale] using! hAvgInt.sub hParent

/-- The additivity-defect observable is nonnegative on the a.s. elliptic
support of a Chapter 4 law carrier. -/
theorem responseJAdditivityDefectAtScale_nonneg_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) {k m : ℤ} (hkm : k ≤ m)
    (p q : Vec d) :
    0 ≤ᵐ[P] responseJAdditivityDefectAtScale m k p q := by
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  have hle :
      Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a ≤
        descendantsAverage (originCube d m) (Int.toNat (m - k))
          (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a) :=
    Ch04.restrictionResponseJObservableCubeSet_le_descendantsAverage_of_aelocallyUniformlyEllipticField
      (a := a) ha hkm p q
  simpa [responseJAdditivityDefectAtScale] using sub_nonneg.mpr hle

/-- The square-root additivity term is controlled in expectation by the
geometric mean of the `tau` defect and the child-scale annealed response. -/
theorem integral_sqrt_responseJAdditivityDefectAtScale_mul_sqrt_childResponseAverage_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    {k m : ℤ} (hk_nonneg : 0 ≤ k) (hkm : k ≤ m) (p q : Vec d)
    (hParent :
      Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q) P)
    (hDesc : ∀ R, R ∈ descendantsAtScale (originCube d m) k →
      Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P) :
    ∫ a,
        Real.sqrt (responseJAdditivityDefectAtScale m k p q a) *
          Real.sqrt
            (descendantsAverage (originCube d m) (Int.toNat (m - k))
              (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a)) ∂P
      ≤
        Real.sqrt (tauAtScale P m k p q) *
          Real.sqrt (Ch04.expectedResponseJCubeSet P (originCube d k) p q) := by
  have hDescDepth :
      ∀ R, R ∈ descendantsAtDepth (originCube d m) (Int.toNat (m - k)) →
        Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P := by
    intro R hR
    exact hDesc R (by
      simpa [descendantsAtScale_eq_descendantsAtDepth (originCube d m) hkm] using! hR)
  have hChildInt :
      Integrable
        (fun a : RegCoeffField d =>
          descendantsAverage (originCube d m) (Int.toNat (m - k))
            (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a)) P :=
    Ch04.integrable_descendantsAverage_restrictionResponseJObservableCubeSet hDescDepth
  have hDefectInt :
      Integrable (responseJAdditivityDefectAtScale m k p q) P :=
    integrable_responseJAdditivityDefectAtScale hkm p q hParent hDesc
  have hDefectNonneg :
      0 ≤ᵐ[P] responseJAdditivityDefectAtScale m k p q :=
    responseJAdditivityDefectAtScale_nonneg_ae hP hkm p q
  have hChildNonneg :
      0 ≤ᵐ[P]
        fun a : RegCoeffField d =>
          descendantsAverage (originCube d m) (Int.toNat (m - k))
            (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a) := by
    filter_upwards with a
    exact descendantsAverage_restrictionResponseJObservableCubeSet_nonneg
      (originCube d m) (Int.toNat (m - k)) p q a
  have hCauchy :=
    integral_sqrt_mul_sqrt_le_sqrt_integral_mul_sqrt_integral
      (μ := P)
      (A := responseJAdditivityDefectAtScale m k p q)
      (B := fun a : RegCoeffField d =>
        descendantsAverage (originCube d m) (Int.toNat (m - k))
          (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a))
      hDefectInt hChildInt hDefectNonneg hChildNonneg
  have hDefectIntegral :
      ∫ a, responseJAdditivityDefectAtScale m k p q a ∂P =
        tauAtScale P m k p q :=
    integral_responseJAdditivityDefectAtScale_eq_tauAtScale
      hP hstat hk_nonneg hkm p q hParent hDesc
  have hChildIntegral :
      ∫ a,
          descendantsAverage (originCube d m) (Int.toNat (m - k))
            (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a) ∂P =
        Ch04.expectedResponseJCubeSet P (originCube d k) p q :=
    hP.integral_descendantsAverage_restrictionResponseJObservableCubeSet_eq_originCube_of_stationary
      hstat hk_nonneg hkm p q hDesc
  have hChildIntegral' :
      ∫ a,
          descendantsAverage (originCube d m) (Int.toNat (m - k))
            (fun R => ResponseJ (cubeSet R) p q a) ∂P =
        Ch04.expectedResponseJCubeSet P (originCube d k) p q := by
    simpa [Ch04.restrictionResponseJObservableCubeSet] using hChildIntegral
  simpa [Ch04.restrictionResponseJObservableCubeSet, hDefectIntegral, hChildIntegral'] using hCauchy

/-- A.e. nonnegativity of the Ch4 scalar-response gradient weak norm. -/
theorem canonicalScalarResponseGradientWeakNormCubeSet_nonneg_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (Q : TriadicCube d) {s : ℝ} (hs : 0 < s)
    (p q p0 : Vec d) :
    0 ≤ᵐ[P] (fun a : RegCoeffField d => Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun) := by
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let aQ : Ch02.CoeffOn (Ch02.cubeDomain Q) := F.coeffOn Q
  have hpartial_nonneg :
      0 ≤ cubeBesovNegativeVectorPartialSeminorm Q s 0
        (canonicalMaximizerGradientDefectOnCube Q aQ p q p0) :=
    cubeBesovNegativeVectorPartialSeminorm_nonneg Q s 0
      (canonicalMaximizerGradientDefectOnCube Q aQ p q p0)
  have hpartial_le :
      cubeBesovNegativeVectorPartialSeminorm Q s 0
          (canonicalMaximizerGradientDefectOnCube Q aQ p q p0) ≤
        Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun := by
    simpa [F, aQ] using
      cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerGradientDefectOnDependentFamily_le_ch04WeakNorm
        a ha Q hs 0 p q p0
  exact hpartial_nonneg.trans hpartial_le

/-- A.e. nonnegativity of the Ch4 scalar-response flux weak norm. -/
theorem canonicalScalarResponseFluxWeakNormCubeSet_nonneg_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (Q : TriadicCube d) {t : ℝ} (ht : 0 < t)
    (p q q0 : Vec d) :
    0 ≤ᵐ[P] (fun a : RegCoeffField d => Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun) := by
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let aQ : Ch02.CoeffOn (Ch02.cubeDomain Q) := F.coeffOn Q
  have hpartial_nonneg :
      0 ≤ cubeBesovNegativeVectorPartialSeminorm Q t 0
        (canonicalMaximizerFluxDefectOnCube Q aQ p q q0) :=
    cubeBesovNegativeVectorPartialSeminorm_nonneg Q t 0
      (canonicalMaximizerFluxDefectOnCube Q aQ p q q0)
  have hpartial_le :
      cubeBesovNegativeVectorPartialSeminorm Q t 0
          (canonicalMaximizerFluxDefectOnCube Q aQ p q q0) ≤
        Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun := by
    simpa [F, aQ] using
      cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerFluxDefectOnDependentFamily_le_ch04WeakNorm
        a ha Q ht 0 p q q0
  exact hpartial_nonneg.trans hpartial_le

/-- A.e. nonnegativity of a scaled Ch4 scalar-response gradient weak norm. -/
theorem scaledCanonicalScalarResponseGradientWeakNorm_nonneg_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (Q : TriadicCube d) {s : ℝ} (hs : 0 < s)
    (p q p0 : Vec d) :
    0 ≤ᵐ[P]
      fun a : RegCoeffField d =>
        cubeBesovScaleWeight (-s) Q *
          Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun := by
  filter_upwards [canonicalScalarResponseGradientWeakNormCubeSet_nonneg_ae hP Q hs p q p0]
    with a ha
  exact mul_nonneg (cubeBesovScaleWeight_nonneg (-s) Q) ha

/-- A.e. nonnegativity of a scaled Ch4 scalar-response flux weak norm. -/
theorem scaledCanonicalScalarResponseFluxWeakNorm_nonneg_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (Q : TriadicCube d) {t : ℝ} (ht : 0 < t)
    (p q q0 : Vec d) :
    0 ≤ᵐ[P]
      fun a : RegCoeffField d =>
        cubeBesovScaleWeight (-t) Q *
          Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun := by
  filter_upwards [canonicalScalarResponseFluxWeakNormCubeSet_nonneg_ae hP Q ht p q q0]
    with a ha
  exact mul_nonneg (cubeBesovScaleWeight_nonneg (-t) Q) ha

/-- Expectation of the cutoff-product bridge is bounded by the manuscript
square-root product once the deterministic bridge has been pointwise replaced
by the note-normalized gradient/flux weak-norm product. -/
theorem integral_cutoffProductBridgeRHS_le_weakNormSquareProduct
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (Q : TriadicCube d) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t)
    (cutoffGradient : Vec d → Vec d)
    (cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant Cprod : ℝ)
    (p q p0 q0 : Vec d)
    (hCprod : 0 ≤ Cprod)
    (hGradSq :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun) ^ 2) P)
    (hFluxSq :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun) ^ 2) P)
    (hProductInt :
      Integrable
        (fun a : RegCoeffField d =>
          cutoffProductBridgeRHS Q s cutoffGradient
            (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q 1 p q q0 a.toFun)
            (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q s p q q0 a.toFun)
            ‖Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun - q0‖
            cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant) P)
    (hProductPoint :
      ∀ᵐ a ∂P,
        cutoffProductBridgeRHS Q s cutoffGradient
            (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q 1 p q q0 a.toFun)
            (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q s p q q0 a.toFun)
            ‖Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun - q0‖
            cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant
          ≤
        Cprod *
          (Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun *
            Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun)) :
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
  let : IsProbabilityMeasure P := hP.isProbability
  let scaledGrad : RegCoeffField d → ℝ :=
    fun a => Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun
  let scaledFlux : RegCoeffField d → ℝ :=
    fun a => Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun
  let productPoint : RegCoeffField d → ℝ :=
    fun a =>
      cutoffProductBridgeRHS Q s cutoffGradient
        (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q 1 p q q0 a.toFun)
        (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q s p q q0 a.toFun)
        ‖Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun - q0‖
        cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant
  have hGradNonneg : 0 ≤ᵐ[P] scaledGrad := by
    simpa [scaledGrad] using
      canonicalScalarResponseGradientWeakNormCubeSet_nonneg_ae hP Q hs p q p0
  have hFluxNonneg : 0 ≤ᵐ[P] scaledFlux := by
    simpa [scaledFlux] using
      canonicalScalarResponseFluxWeakNormCubeSet_nonneg_ae hP Q ht p q q0
  have hScaledProdInt : Integrable (fun a => scaledGrad a * scaledFlux a) P :=
    integrable_mul_of_integrable_sq_of_ae_nonneg
      (X := scaledGrad) (Y := scaledFlux)
      (by simpa [scaledGrad] using hGradSq)
      (by simpa [scaledFlux] using hFluxSq)
      hGradNonneg hFluxNonneg
  have hConstProdInt :
      Integrable (fun a => Cprod * (scaledGrad a * scaledFlux a)) P := by
    simpa using hScaledProdInt.const_mul Cprod
  have hMono :
      ∫ a, productPoint a ∂P ≤
        ∫ a, Cprod * (scaledGrad a * scaledFlux a) ∂P :=
    integral_mono_ae
      (by simpa [productPoint] using hProductInt) hConstProdInt
      (by simpa [productPoint, scaledGrad, scaledFlux] using! hProductPoint)
  have hCauchy :
      ∫ a, scaledGrad a * scaledFlux a ∂P ≤
        Real.sqrt (∫ a, (scaledGrad a) ^ 2 ∂P) *
          Real.sqrt (∫ a, (scaledFlux a) ^ 2 ∂P) :=
    integral_mul_le_sqrt_integral_sq_mul_sqrt_integral_sq_of_ae_nonneg
      (X := scaledGrad) (Y := scaledFlux)
      (by simpa [scaledGrad] using hGradSq)
      (by simpa [scaledFlux] using hFluxSq)
      hGradNonneg hFluxNonneg
  calc
    ∫ a, productPoint a ∂P
        ≤ ∫ a, Cprod * (scaledGrad a * scaledFlux a) ∂P := hMono
    _ = Cprod * ∫ a, scaledGrad a * scaledFlux a ∂P := by
          rw [integral_const_mul]
    _ ≤
        Cprod *
          (Real.sqrt (∫ a, (scaledGrad a) ^ 2 ∂P) *
            Real.sqrt (∫ a, (scaledFlux a) ^ 2 ∂P)) :=
          mul_le_mul_of_nonneg_left hCauchy hCprod
    _ =
        Cprod *
          (Real.sqrt
              (∫ a,
                (Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun) ^ 2 ∂P) *
            Real.sqrt
              (∫ a,
                (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun) ^ 2 ∂P)) := by
          simp [scaledGrad, scaledFlux]

end

end JUpperBoundWeakNorms
end Section53
end Ch05
end Book
end Homogenization
