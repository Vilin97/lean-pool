/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Expectation.ExpectedRHSComparison

/-! # Pointwise Bound -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundWeakNorms

/-!
# PointwiseBound

Fixed-coefficient pointwise bound by the preliminary RHS.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

noncomputable section

/-- Pointwise bridge from the deterministic split to the total Ch4-facing RHS at
origin scales.  This is the a.e. ingredient that will be fed into the expectation
assembly theorem. -/
theorem abs_centeredJMinusCutoffWeightedChildAtScale_le_jUpperWeakNormPointwiseRHS
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (m k : ℤ) (s t : ℝ) (φ : Vec d → ℝ) (p q p0 q0 : Vec d)
    (dualField cutoffGradient : Vec d → Vec d)
    {C B Cosc scaleSep BφS BφT cutoffCircOne cutoffCircS cutoffDerivative
      poincareConst cutoffConstant centeredCutoffConstant : ℝ}
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
    (hcutoffGradient_eq : cutoffGradient = scalarCutoffGradientField φ)
    (hcutoffDerivative : 0 ≤ cutoffDerivative)
    (hs_pos : 0 < s) (hs_lt_one : s < 1) (ht_pos : 0 < t)
    (hBφS : 0 ≤ BφS) (hBφT : 0 ≤ BφT)
    (hφDualS :
      ∀ N : ℕ,
        cubeBesovDualTestNorm (originCube d m) s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N φ ≤ BφS)
    (hφDualT :
      ∀ N : ℕ,
        cubeBesovDualTestNorm (originCube d m) t (2 : ℝ≥0∞) (1 : ℝ≥0∞) N φ ≤ BφT)
    (hφMem : CubeBesovDualLocalMemLpGlobal (originCube d m) (2 : ℝ≥0∞) φ)
    (hdualField :
      ∀ i : Fin d,
        MemLp (fun x => dualField x i) (2 : ℝ≥0∞)
          (normalizedCubeMeasure (originCube d m)))
    (hcutoffGradient :
      MemLp cutoffGradient ∞ (normalizedCubeMeasure (originCube d m)))
    (hcutoffConstant : 0 ≤ cutoffConstant)
    (hcenteredCutoffConstant : 0 ≤ centeredCutoffConstant)
    (hpoincareConst : 0 ≤ poincareConst)
    (hcutoffCircOne : 0 ≤ cutoffCircOne)
    (hcutoffCircS : 0 ≤ cutoffCircS)
    (hfull :
      ∀ N : ℕ,
        CubeDescendantDualFullVectorPoincareEstimate (originCube d m) poincareConst
          (cubeFluctuation (originCube d m)
            (canonicalMaximizerPotentialDefectOnCube (originCube d m)
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
                (originCube d m))
              p q p0))
          dualField N)
    (hcutoffSmooth :
      ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => cutoffGradient x i))
    (hcutoffDeriv :
      ∀ i : Fin d, ∀ z ∈ cubeSet (originCube d m),
        ‖fderiv ℝ (fun x => cutoffGradient x i) z‖ ≤ cutoffDerivative)
    (hdualCircOne :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovCircPartialNorm (originCube d m) 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => dualField x i) ≤ cutoffCircOne)
    (hdualCircS :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovCircPartialNorm (originCube d m) (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => dualField x i) ≤ cutoffCircS)
    (hcutoffConstant_bound :
      cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
            (canonicalMaximizerPotentialDefectOnCube (originCube d m)
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
                (originCube d m))
              p q p0) *
          (cutoffDerivative + cubeBesovScaleWeight 1 (originCube d m) *
            cubeLpNorm (originCube d m) ∞ cutoffGradient) ≤
        cutoffConstant)
    (hcenteredCutoffConstant_bound :
      2 * (cubeScaleFactor (originCube d m) * cutoffDerivative *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * poincareConst) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) * cutoffCircOne)) +
        cubeLpNorm (originCube d m) ∞ cutoffGradient *
          (cubeBesovScaleWeight (-s) (originCube d m) *
            ((((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * poincareConst) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) * cutoffCircS))) ≤
        centeredCutoffConstant) :
    |centeredJMinusCutoffWeightedChildAtScale m k φ p q p0 q0 a| ≤
      jUpperWeakNormPointwiseRHSAtScale m k s t cutoffGradient
        C Cosc scaleSep BφS BφT cutoffCircOne poincareConst cutoffConstant
        centeredCutoffConstant p q p0 q0 a := by
  let Q : TriadicCube d := originCube d m
  let j : ℕ := Int.toNat (m - k)
  let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
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
              cutoffProductBridgeRHS Q s cutoffGradient
                (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q 1 p q q0 a.toFun)
                (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q s p q q0 a.toFun)
                ‖Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun - q0‖
                cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant := by
    simpa [Q, j, F] using
      abs_centeredResponseJOnCube_sub_cutoffWeightedChildResponseJOnDependentFamily_le_additivityDefect_add_cutoffOscillationBound_add_linearWeakNorms_add_cutoffProductBridgeRHS
        (a := a) (ha := ha) (Q := Q) (j := j) (s := s) (t := t)
        (φ := φ) (p := p) (q := q) (p0 := p0) (q0 := q0)
        (dualField := dualField) (cutoffGradient := cutoffGradient)
        (C := C) (B := B) (Cosc := Cosc) (scaleSep := scaleSep)
        (BφS := BφS) (BφT := BφT)
        (cutoffCircOne := cutoffCircOne) (cutoffCircS := cutoffCircS)
        (cutoffDerivative := cutoffDerivative) (poincareConst := poincareConst)
        (cutoffConstant := cutoffConstant)
        (centeredCutoffConstant := centeredCutoffConstant)
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
        hcutoffGradient_eq hcutoffDerivative hs_pos hs_lt_one ht_pos hBφS hBφT
        (by simpa [Q] using hφDualS) (by simpa [Q] using hφDualT)
        (by simpa [Q] using hφMem)
        (by simpa [Q] using hdualField)
        (by simpa [Q] using hcutoffGradient)
        hcutoffConstant hcenteredCutoffConstant hpoincareConst
        hcutoffCircOne hcutoffCircS
        (by simpa [Q, F] using hfull)
        hcutoffSmooth (by simpa [Q] using hcutoffDeriv)
        (by simpa [Q] using hdualCircOne)
        (by simpa [Q] using hdualCircS)
        (by simpa [Q, F] using hcutoffConstant_bound)
        (by simpa [Q] using hcenteredCutoffConstant_bound)
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
  simpa [jUpperWeakNormPointwiseRHSAtScale, Q, j, F, hleft, hpartition, hchild,
    add_assoc] using hdet

end

end JUpperBoundWeakNorms
end Section53
end Ch05
end Book
end Homogenization
