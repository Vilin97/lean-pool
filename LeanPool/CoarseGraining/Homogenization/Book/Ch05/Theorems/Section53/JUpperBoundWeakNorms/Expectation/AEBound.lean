/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Expectation.ManuscriptPointwiseBound

/-! # AEBound -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundWeakNorms

/-!
# AEBound

Law-relative a.e. pointwise bound for the manuscript RHS.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

noncomputable section

/-- Law-facing a.e. pointwise bridge from the fixed-coefficient deterministic
split to the manuscript RHS.

This theorem discharges the coefficient-dependent integrability inputs and the
a.s. ellipticity support.  The remaining hypotheses are deterministic cutoff
controls for the still-arbitrary manuscript cutoff `φ`. -/
theorem ae_abs_centeredJMinusCutoffWeightedChildAtScale_le_jUpperWeakNormManuscriptPointwiseRHS
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (m k : ℤ) (s t : ℝ) (φ : Vec d → ℝ) (p q p0 q0 : Vec d)
    {C B Cosc scaleSep BφS BφT cutoffDerivative Cprod : ℝ}
    (hC : 0 ≤ C)
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
    ∀ᵐ a ∂P,
      |centeredJMinusCutoffWeightedChildAtScale m k φ p q p0 q0 a| ≤
        jUpperWeakNormManuscriptPointwiseRHSAtScale m k s t
          C Cosc scaleSep BφS BφT Cprod p q p0 q0 a := by
  let Q : TriadicCube d := originCube d m
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let aQ : Ch02.CoeffOn (Ch02.cubeDomain Q) := F.coeffOn Q
  have hφ_int : IntegrableOn φ (cubeSet Q) volume := by
    simpa [Q, volumeMeasureOn] using
      (IntegrableOn.of_bound
        (μ := volume) (s := cubeSet Q) (f := φ)
        (volume_cubeSet_lt_top Q)
        (by simpa [Q, volumeMeasureOn] using hφ_meas) B
        (by simpa [Q, volumeMeasureOn] using hφ_bound))
  have hOneSub_meas :
      AEStronglyMeasurable (fun x : Vec d => (1 : ℝ) - φ x)
        (volumeMeasureOn (cubeSet Q)) := by
    simpa [sub_eq_add_neg] using!
      (aestronglyMeasurable_const (b := (1 : ℝ))).sub
        (by simpa [Q] using hφ_meas)
  have hOneSub_bound :
      ∀ᵐ x ∂ volumeMeasureOn (cubeSet Q),
        ‖(1 : ℝ) - φ x‖ ≤ |(1 : ℝ)| + B := by
    filter_upwards [by simpa [Q] using! hφ_bound] with x hx
    calc
      ‖(1 : ℝ) - φ x‖ = |(1 : ℝ) - φ x| := Real.norm_eq_abs _
      _ ≤ |(1 : ℝ)| + |φ x| := by
          simpa [sub_eq_add_neg] using abs_add_le (1 : ℝ) (-φ x)
      _ ≤ |(1 : ℝ)| + B := add_le_add le_rfl hx
  have hRem_int :
      IntegrableOn
        (fun x => (1 - φ x) *
          topHalfEnergyDensityOnCube Q aQ p q x)
        (cubeSet Q) volume :=
    integrableOn_mul_left_of_integrableOn_of_ae_bounded
      (topHalfEnergyDensityOnCube_integrableOn_cubeSet Q aQ p q)
      hOneSub_meas hOneSub_bound
  have hProduct_int :
      IntegrableOn
        (fun x => φ x * centeredProductDensityOnCube Q aQ p q p0 q0 x)
        (cubeSet Q) volume :=
    integrableOn_mul_left_of_integrableOn_of_ae_bounded
      (centeredProductDensityOnCube_integrableOn_cubeSet Q aQ p q p0 q0)
      (by simpa [Q] using hφ_meas) (by simpa [Q] using hφ_bound)
  have hGradLinear_int :
      IntegrableOn
        (fun x => φ x * centeredGradientLinearDensityOnCube Q aQ p q p0 q0 x)
        (cubeSet Q) volume :=
    integrableOn_mul_left_of_integrableOn_of_ae_bounded
      (centeredGradientLinearDensityOnCube_integrableOn_cubeSet Q aQ p q p0 q0)
      (by simpa [Q] using hφ_meas) (by simpa [Q] using hφ_bound)
  have hFluxLinear_int :
      IntegrableOn
        (fun x => φ x * centeredFluxLinearDensityOnCube Q aQ p q p0 q0 x)
        (cubeSet Q) volume :=
    integrableOn_mul_left_of_integrableOn_of_ae_bounded
      (centeredFluxLinearDensityOnCube_integrableOn_cubeSet Q aQ p q p0 q0)
      (by simpa [Q] using hφ_meas) (by simpa [Q] using hφ_bound)
  have hGradField :
      ∀ i : Fin d,
        IntegrableOn
          (fun x =>
            (φ x • canonicalMaximizerGradientDefectOnCube Q aQ p q p0 x) i)
          (cubeSet Q) volume := by
    intro i
    have hbase :=
      canonicalMaximizerGradientDefectOnCube_component_integrableOn Q aQ p q p0 i
    have hmul :
        IntegrableOn
          (fun x => φ x * canonicalMaximizerGradientDefectOnCube Q aQ p q p0 x i)
          (cubeSet Q) volume :=
      integrableOn_mul_left_of_integrableOn_of_ae_bounded
        hbase (by simpa [Q] using hφ_meas) (by simpa [Q] using hφ_bound)
    simpa [Pi.smul_apply, smul_eq_mul] using hmul
  have hFluxField :
      ∀ i : Fin d,
        IntegrableOn
          (fun x =>
            (φ x • canonicalMaximizerFluxDefectOnCube Q aQ p q q0 x) i)
          (cubeSet Q) volume := by
    intro i
    have hbase :=
      canonicalMaximizerFluxDefectOnCube_component_integrableOn Q aQ p q q0 i
    have hmul :
        IntegrableOn
          (fun x => φ x * canonicalMaximizerFluxDefectOnCube Q aQ p q q0 x i)
          (cubeSet Q) volume :=
      integrableOn_mul_left_of_integrableOn_of_ae_bounded
        hbase (by simpa [Q] using hφ_meas) (by simpa [Q] using hφ_bound)
    simpa [Pi.smul_apply, smul_eq_mul] using hmul
  simpa [Q, F, aQ] using
    abs_centeredJMinusCutoffWeightedChildAtScale_le_jUpperWeakNormManuscriptPointwiseRHS
      (a := a) (ha := ha) (m := m) (k := k) (s := s) (t := t)
      (φ := φ) (p := p) (q := q) (p0 := p0) (q0 := q0)
      (C := C) (B := B) (Cosc := Cosc) (scaleSep := scaleSep)
      (BφS := BφS) (BφT := BφT) (cutoffDerivative := cutoffDerivative)
      (Cprod := Cprod)
      hC hCut (by simpa [Q] using hφ_int)
      (by simpa [Q, F, aQ] using hRem_int)
      (by simpa [Q, F, aQ] using hProduct_int)
      (by simpa [Q, F, aQ] using hGradLinear_int)
      (by simpa [Q, F, aQ] using hFluxLinear_int)
      (by simpa [Q, F, aQ] using hGradField)
      (by simpa [Q, F, aQ] using hFluxField)
      hMean hφ_meas hφ_bound hOscPoint hφ hφ_compact hφ_sub
      hcutoffDerivative hs_pos hs_lt_one ht_pos hst hBφS hBφT
      hφDualS hφDualT hφMem hcutoffGradient hcutoffSmooth hcutoffDeriv hProductCoeff

end

end JUpperBoundWeakNorms
end Section53
end Ch05
end Book
end Homogenization
