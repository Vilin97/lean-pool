/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Expectation.PointwiseBound

/-! # Manuscript Pointwise Bound -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundWeakNorms

/-!
# ManuscriptPointwiseBound

Fixed-coefficient pointwise bound by the manuscript RHS.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

noncomputable section

/-- Pointwise bridge from the deterministic split directly to the
manuscript-product RHS at origin scales. -/
theorem abs_centeredJMinusCutoffWeightedChildAtScale_le_jUpperWeakNormManuscriptPointwiseRHS
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (m k : ℤ) (s t : ℝ) (φ : Vec d → ℝ) (p q p0 q0 : Vec d)
    {C B Cosc scaleSep BφS BφT cutoffDerivative Cprod : ℝ}
    (hC : 0 ≤ C)
    (hCut :
      ∀ R ∈ descendantsAtDepth (originCube d m) (Int.toNat (m - k)),
        |1 - cubeAverage R φ| ≤ C)
    (hφ_int : IntegrableOn φ (cubeSet (originCube d m)) volume)
    (hRem_int :
      IntegrableOn
        (fun x => (1 - φ x) *
          topHalfEnergyDensityOnCube (originCube d m)
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
              (originCube d m))
            p q x)
        (cubeSet (originCube d m)) volume)
    (hProduct_int :
      IntegrableOn
        (fun x => φ x *
          centeredProductDensityOnCube (originCube d m)
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
              (originCube d m))
            p q p0 q0 x)
        (cubeSet (originCube d m)) volume)
    (hGradLinear_int :
      IntegrableOn
        (fun x => φ x *
          centeredGradientLinearDensityOnCube (originCube d m)
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
              (originCube d m))
            p q p0 q0 x)
        (cubeSet (originCube d m)) volume)
    (hFluxLinear_int :
      IntegrableOn
        (fun x => φ x *
          centeredFluxLinearDensityOnCube (originCube d m)
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
              (originCube d m))
            p q p0 q0 x)
        (cubeSet (originCube d m)) volume)
    (hGradField :
      ∀ i : Fin d,
        IntegrableOn
          (fun x =>
            (φ x • canonicalMaximizerGradientDefectOnCube (originCube d m)
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
                (originCube d m))
              p q p0 x) i)
          (cubeSet (originCube d m)) volume)
    (hFluxField :
      ∀ i : Fin d,
        IntegrableOn
          (fun x =>
            (φ x • canonicalMaximizerFluxDefectOnCube (originCube d m)
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
                (originCube d m))
              p q q0 x) i)
          (cubeSet (originCube d m)) volume)
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
    (hs_pos : 0 < s) (hs_lt_one : s < 1) (ht_pos : 0 < t)
    (hst : s + t ≤ 1)
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
          cubeBesovScaleWeight (-t) (originCube d m) ≤ Cprod) :
    |centeredJMinusCutoffWeightedChildAtScale m k φ p q p0 q0 a| ≤
      jUpperWeakNormManuscriptPointwiseRHSAtScale m k s t
        C Cosc scaleSep BφS BφT Cprod p q p0 q0 a := by
  let Q : TriadicCube d := originCube d m
  let j : ℕ := Int.toNat (m - k)
  let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let productCoeff : ℝ :=
    cutoffProductScaledWeakNormCoeff Q s t cutoffDerivative (scalarCutoffGradientField φ)
  let gradWeak : ℝ :=
    Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun
  let fluxWeak : ℝ :=
    Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun
  let scaledGrad : ℝ := cubeBesovScaleWeight (-s) Q * gradWeak
  let scaledFlux : ℝ := cubeBesovScaleWeight (-t) Q * fluxWeak
  have hgradWeak_nonneg : 0 ≤ gradWeak := by
      let aQ : Ch02.CoeffOn (Ch02.cubeDomain Q) := F.coeffOn Q
      simpa [gradWeak, Q, F, aQ] using
        (cubeBesovNegativeVectorPartialSeminorm_nonneg Q s 0
          (canonicalMaximizerGradientDefectOnCube Q aQ p q p0)).trans
          (cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerGradientDefectOnDependentFamily_le_ch04WeakNorm
            a ha Q hs_pos 0 p q p0)
  have hfluxWeak_nonneg : 0 ≤ fluxWeak := by
      let aQ : Ch02.CoeffOn (Ch02.cubeDomain Q) := F.coeffOn Q
      simpa [fluxWeak, Q, F, aQ] using
        (cubeBesovNegativeVectorPartialSeminorm_nonneg Q t 0
          (canonicalMaximizerFluxDefectOnCube Q aQ p q q0)).trans
          (cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerFluxDefectOnDependentFamily_le_ch04WeakNorm
            a ha Q ht_pos 0 p q q0)
  have hscaledGrad_nonneg : 0 ≤ scaledGrad := by
    exact mul_nonneg (cubeBesovScaleWeight_nonneg (-s) Q) hgradWeak_nonneg
  have hscaledFlux_nonneg : 0 ≤ scaledFlux := by
    exact mul_nonneg (cubeBesovScaleWeight_nonneg (-t) Q) hfluxWeak_nonneg
  have hdet :
      |centeredResponseJOnCube Q (F.coeffOn Q) p q p0 q0 -
          cutoffWeightedChildResponseJOnFamilyAtDepth F Q j φ p q| ≤
        (2 * C) *
            (Real.sqrt (responseJPartitionDefectOnFamilyAtDepth F Q j p q) *
              Real.sqrt (childResponseJAverageOnFamilyAtDepth F Q j p q)) +
          Cosc * scaleSep * Ch04.restrictionResponseJObservableCubeSet Q p q a +
            ((1 / 2 : ℝ) * ‖q0‖ *
                (((Fintype.card (Fin d) : ℝ) *
                  ((3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovScaleWeight (-s) Q * BφS)) *
                    Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun) +
              (1 / 2 : ℝ) * ‖p0‖ *
                (((Fintype.card (Fin d) : ℝ) *
                  ((3 : ℝ) ^ ((d : ℝ) + t) * cubeBesovScaleWeight (-t) Q * BφT)) *
                    Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun)) +
              productCoeff * (scaledGrad * scaledFlux) := by
    simpa [Q, j, F, productCoeff, scaledGrad, scaledFlux] using
      abs_centeredResponseJOnCube_sub_cutoffWeightedChildResponseJOnDependentFamily_le_additivityDefect_add_cutoffOscillationBound_add_linearWeakNorms_add_scaledProduct
        (a := a) (ha := ha) (Q := Q) (j := j) (s := s) (t := t)
        (φ := φ) (p := p) (q := q) (p0 := p0) (q0 := q0)
        (C := C) (B := B) (Cosc := Cosc) (scaleSep := scaleSep)
        (BφS := BφS) (BφT := BφT) (cutoffDerivative := cutoffDerivative)
        hC (by simpa [Q, j] using hCut) (by simpa [Q] using hφ_int)
        (by simpa [Q, F] using hRem_int)
        (by simpa [Q, F] using hProduct_int)
        (by simpa [Q, F] using hGradLinear_int)
        (by simpa [Q, F] using hFluxLinear_int)
        (by simpa [Q, F] using hGradField)
        (by simpa [Q, F] using hFluxField)
        (by simpa [Q] using hMean)
        (by simpa [Q] using hφ_meas)
        (by simpa [Q] using hφ_bound)
        (by simpa [Q, j] using hOscPoint)
        hφ hφ_compact (by simpa [Q] using hφ_sub)
        hcutoffDerivative hs_pos hs_lt_one ht_pos hst hBφS hBφT
        (by simpa [Q] using hφDualS) (by simpa [Q] using hφDualT)
        (by simpa [Q] using hφMem)
        (by simpa [Q] using hcutoffGradient)
        hcutoffSmooth (by simpa [Q] using hcutoffDeriv)
  have hproductCoeff' : productCoeff * (scaledGrad * scaledFlux) ≤
      Cprod * (gradWeak * fluxWeak) := by
    have hprod_nonneg : 0 ≤ gradWeak * fluxWeak :=
      mul_nonneg hgradWeak_nonneg hfluxWeak_nonneg
    calc
      productCoeff * (scaledGrad * scaledFlux)
          =
        (productCoeff * cubeBesovScaleWeight (-s) Q *
            cubeBesovScaleWeight (-t) Q) * (gradWeak * fluxWeak) := by
          ring
      _ ≤ Cprod * (gradWeak * fluxWeak) :=
          mul_le_mul_of_nonneg_right
            (by simpa [Q, productCoeff, mul_assoc] using hProductCoeff) hprod_nonneg
  have hleft :
      centeredJMinusCutoffWeightedChildAtScale m k φ p q p0 q0 a =
        centeredResponseJOnCube Q (F.coeffOn Q) p q p0 q0 -
          cutoffWeightedChildResponseJOnFamilyAtDepth F Q j φ p q := by
    simpa [Q, j, F] using
      centeredJMinusCutoffWeightedChildAtScale_eq_dependentFamily_left
        a ha m k φ p q p0 q0
  have hpartition :
      responseJPartitionDefectOnFamilyAtDepth F Q j p q =
        responseJAdditivityDefectAtScale m k p q a := by
    simpa [Q, j, F] using
      responseJPartitionDefectOnDependentFamilyAtScale_eq_responseJAdditivityDefectAtScale
        a ha m k p q
  have hchild :
      childResponseJAverageOnFamilyAtDepth F Q j p q =
        descendantsAverage Q j (fun R => Ch04.restrictionResponseJObservableCubeSet R p q a) := by
    simpa [Q, j, F] using
      childResponseJAverageOnDependentFamilyAtScale_eq_ch04 a ha m k p q
  have hdet' :
      |centeredResponseJOnCube Q (F.coeffOn Q) p q p0 q0 -
          cutoffWeightedChildResponseJOnFamilyAtDepth F Q j φ p q| ≤
        (2 * C) *
            (Real.sqrt (responseJPartitionDefectOnFamilyAtDepth F Q j p q) *
              Real.sqrt (childResponseJAverageOnFamilyAtDepth F Q j p q)) +
          Cosc * scaleSep * Ch04.restrictionResponseJObservableCubeSet Q p q a +
            ((1 / 2 : ℝ) * ‖q0‖ *
                (((Fintype.card (Fin d) : ℝ) *
                  ((3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovScaleWeight (-s) Q * BφS)) *
                    Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun) +
              (1 / 2 : ℝ) * ‖p0‖ *
                (((Fintype.card (Fin d) : ℝ) *
                  ((3 : ℝ) ^ ((d : ℝ) + t) * cubeBesovScaleWeight (-t) Q * BφT)) *
                    Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun)) +
              Cprod * (gradWeak * fluxWeak) := by
    nlinarith [hdet, hproductCoeff']
  simpa [jUpperWeakNormManuscriptPointwiseRHSAtScale, Q, j, F, hleft,
    hpartition, hchild, gradWeak, fluxWeak, scaledGrad, scaledFlux, add_assoc] using hdet'

end

end JUpperBoundWeakNorms
end Section53
end Ch05
end Book
end Homogenization
