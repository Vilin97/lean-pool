/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Product.Bound

/-! # Deterministic Assembly -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundWeakNorms

/-!
# DeterministicAssembly

Deterministic manuscript pointwise assembly.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

noncomputable section

/-- Deterministic assembled Section 5.3 estimate with the actual product term
replaced by the scalar-response weak-norm cutoff-product bridge.  The
cutoff-oscillation and linear-pair terms are still displayed separately here;
those are the next deterministic terms to insert before taking expectations. -/
theorem abs_centeredResponseJOnCube_sub_cutoffWeightedChildResponseJOnDependentFamily_le_additivityDefect_add_cutoffOscillation_add_linearPair_add_cutoffProductBridgeRHS
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d)
    (j : ℕ) (s : ℝ) (φ : Vec d → ℝ) (p q p0 q0 : Vec d)
    (dualField cutoffGradient : Vec d → Vec d)
    {C cutoffCircOne cutoffCircS cutoffDerivative poincareConst cutoffConstant
      centeredCutoffConstant : ℝ}
    (hC : 0 ≤ C)
    (hCut : ∀ R ∈ descendantsAtDepth Q j, |1 - cubeAverage R φ| ≤ C)
    (hφ_int : IntegrableOn φ (cubeSet Q) volume)
    (hRem_int :
      IntegrableOn
        (fun x => (1 - φ x) *
          topHalfEnergyDensityOnCube Q
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
            p q x)
        (cubeSet Q) volume)
    (hProduct_int :
      IntegrableOn
        (fun x => φ x *
          centeredProductDensityOnCube Q
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
            p q p0 q0 x)
        (cubeSet Q) volume)
    (hGradLinear_int :
      IntegrableOn
        (fun x => φ x *
          centeredGradientLinearDensityOnCube Q
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
            p q p0 q0 x)
        (cubeSet Q) volume)
    (hFluxLinear_int :
      IntegrableOn
        (fun x => φ x *
          centeredFluxLinearDensityOnCube Q
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
            p q p0 q0 x)
        (cubeSet Q) volume)
    (hOsc_int :
      ∀ R ∈ descendantsAtDepth Q j,
        IntegrableOn
          (fun x =>
            (cubeAverage R φ - φ x) *
              topHalfEnergyDensityOnCube Q
                ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
                p q x)
          (cubeSet R) volume)
    (hMean : cubeAverage Q φ = 1)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ openCubeSet Q)
    (hcutoffGradient_eq : cutoffGradient = scalarCutoffGradientField φ)
    (hcutoffDerivative : 0 ≤ cutoffDerivative)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hdualField :
      ∀ i : Fin d,
        MemLp (fun x => dualField x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hcutoffGradient : MemLp cutoffGradient ∞ (normalizedCubeMeasure Q))
    (hcutoffConstant : 0 ≤ cutoffConstant)
    (hcenteredCutoffConstant : 0 ≤ centeredCutoffConstant)
    (hpoincareConst : 0 ≤ poincareConst)
    (hcutoffCircOne : 0 ≤ cutoffCircOne)
    (hcutoffCircS : 0 ≤ cutoffCircS)
    (hfull :
      ∀ N : ℕ,
        CubeDescendantDualFullVectorPoincareEstimate Q poincareConst
          (cubeFluctuation Q
            (canonicalMaximizerPotentialDefectOnCube Q
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
              p q p0))
          dualField N)
    (hcutoffSmooth :
      ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => cutoffGradient x i))
    (hcutoffDeriv :
      ∀ i : Fin d, ∀ z ∈ cubeSet Q,
        ‖fderiv ℝ (fun x => cutoffGradient x i) z‖ ≤ cutoffDerivative)
    (hdualCircOne :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => dualField x i) ≤ cutoffCircOne)
    (hdualCircS :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => dualField x i) ≤ cutoffCircS)
    (hcutoffConstant_bound :
      cubeLpNorm Q (2 : ℝ≥0∞)
            (canonicalMaximizerPotentialDefectOnCube Q
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
              p q p0) *
          (cutoffDerivative + cubeBesovScaleWeight 1 Q *
            cubeLpNorm Q ∞ cutoffGradient) ≤
        cutoffConstant)
    (hcenteredCutoffConstant_bound :
      2 * (cubeScaleFactor Q * cutoffDerivative *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * poincareConst) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) * cutoffCircOne)) +
        cubeLpNorm Q ∞ cutoffGradient *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * poincareConst) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) * cutoffCircS))) ≤
        centeredCutoffConstant) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    |centeredResponseJOnCube Q (F.coeffOn Q) p q p0 q0 -
        cutoffWeightedChildResponseJOnFamilyAtDepth F Q j φ p q| ≤
      (2 * C) *
          (Real.sqrt (responseJPartitionDefectOnFamilyAtDepth F Q j p q) *
            Real.sqrt (childResponseJAverageOnFamilyAtDepth F Q j p q)) +
        |cutoffOscillationTermOnCubeAtDepth Q (F.coeffOn Q) j φ p q| +
          |cutoffLinearPairTermOnCube Q (F.coeffOn Q) φ p q p0 q0| +
            cutoffProductBridgeRHS Q s cutoffGradient
              (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q 1 p q q0 a.toFun)
              (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q s p q q0 a.toFun)
              ‖Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun - q0‖
              cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant := by
  intro F
  let P : ℝ :=
    cutoffProductBridgeRHS Q s cutoffGradient
      (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q 1 p q q0 a.toFun)
      (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q s p q q0 a.toFun)
      ‖Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun - q0‖
      cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant
  have hsplit :
      |centeredResponseJOnCube Q (F.coeffOn Q) p q p0 q0 -
          cutoffWeightedChildResponseJOnFamilyAtDepth F Q j φ p q| ≤
        (2 * C) *
            (Real.sqrt (responseJPartitionDefectOnFamilyAtDepth F Q j p q) *
              Real.sqrt (childResponseJAverageOnFamilyAtDepth F Q j p q)) +
          |cutoffOscillationTermOnCubeAtDepth Q (F.coeffOn Q) j φ p q| +
            |cutoffLinearPairTermOnCube Q (F.coeffOn Q) φ p q p0 q0| +
              |cutoffProductTermOnCube Q (F.coeffOn Q) φ p q p0 q0| := by
    simpa [F] using
      abs_centeredResponseJOnCube_sub_cutoffWeightedChildResponseJOnDependentFamily_le_additivityDefect_add_cutoffOscillation_add_linearPair_add_product
        (a := a) (ha := ha) (Q := Q) (j := j) (φ := φ)
        (p := p) (q := q) (p0 := p0) (q0 := q0)
        hC hCut hφ_int hRem_int hProduct_int hGradLinear_int hFluxLinear_int hOsc_int hMean
  have hprod :
      |cutoffProductTermOnCube Q (F.coeffOn Q) φ p q p0 q0| ≤ P := by
    simpa [F, P] using
      abs_cutoffProductTermOnDependentFamily_le_cutoffProductBridgeRHS
        (Q := Q) (s := s) (a := a) (ha := ha) (φ := φ)
        (p := p) (q := q) (p0 := p0) (q0 := q0)
        (dualField := dualField) (cutoffGradient := cutoffGradient)
        (cutoffCircOne := cutoffCircOne) (cutoffCircS := cutoffCircS)
        (cutoffDerivative := cutoffDerivative) (poincareConst := poincareConst)
        (cutoffConstant := cutoffConstant)
        (centeredCutoffConstant := centeredCutoffConstant)
        hφ hφ_compact hφ_sub hcutoffGradient_eq hcutoffDerivative
        hs_pos hs_lt_one hdualField hcutoffGradient hcutoffConstant
        hcenteredCutoffConstant hpoincareConst hcutoffCircOne hcutoffCircS
        hfull hcutoffSmooth hcutoffDeriv hdualCircOne hdualCircS
        hcutoffConstant_bound hcenteredCutoffConstant_bound
  exact hsplit.trans (by nlinarith [hprod])

/-- Deterministic assembled Section 5.3 estimate with both the cutoff
oscillation term and the product term replaced by their manuscript bounds.
The linear pair is the only displayed deterministic split term still not
inserted here. -/
theorem abs_centeredResponseJOnCube_sub_cutoffWeightedChildResponseJOnDependentFamily_le_additivityDefect_add_cutoffOscillationBound_add_linearPair_add_cutoffProductBridgeRHS
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d)
    (j : ℕ) (s : ℝ) (φ : Vec d → ℝ) (p q p0 q0 : Vec d)
    (dualField cutoffGradient : Vec d → Vec d)
    {C B Cosc scaleSep cutoffCircOne cutoffCircS cutoffDerivative
      poincareConst cutoffConstant centeredCutoffConstant : ℝ}
    (hC : 0 ≤ C)
    (hCut : ∀ R ∈ descendantsAtDepth Q j, |1 - cubeAverage R φ| ≤ C)
    (hφ_int : IntegrableOn φ (cubeSet Q) volume)
    (hRem_int :
      IntegrableOn
        (fun x => (1 - φ x) *
          topHalfEnergyDensityOnCube Q
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
            p q x)
        (cubeSet Q) volume)
    (hProduct_int :
      IntegrableOn
        (fun x => φ x *
          centeredProductDensityOnCube Q
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
            p q p0 q0 x)
        (cubeSet Q) volume)
    (hGradLinear_int :
      IntegrableOn
        (fun x => φ x *
          centeredGradientLinearDensityOnCube Q
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
            p q p0 q0 x)
        (cubeSet Q) volume)
    (hFluxLinear_int :
      IntegrableOn
        (fun x => φ x *
          centeredFluxLinearDensityOnCube Q
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
            p q p0 q0 x)
        (cubeSet Q) volume)
    (hMean : cubeAverage Q φ = 1)
    (hφ_meas : AEStronglyMeasurable φ (volumeMeasureOn (cubeSet Q)))
    (hφ_bound : ∀ᵐ x ∂ volumeMeasureOn (cubeSet Q), ‖φ x‖ ≤ B)
    (hOscPoint :
      ∀ R ∈ descendantsAtDepth Q j,
        ∀ᵐ x ∂ volumeMeasureOn (cubeSet R),
          |cubeAverage R φ - φ x| ≤ Cosc * scaleSep)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ openCubeSet Q)
    (hcutoffGradient_eq : cutoffGradient = scalarCutoffGradientField φ)
    (hcutoffDerivative : 0 ≤ cutoffDerivative)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hdualField :
      ∀ i : Fin d,
        MemLp (fun x => dualField x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hcutoffGradient : MemLp cutoffGradient ∞ (normalizedCubeMeasure Q))
    (hcutoffConstant : 0 ≤ cutoffConstant)
    (hcenteredCutoffConstant : 0 ≤ centeredCutoffConstant)
    (hpoincareConst : 0 ≤ poincareConst)
    (hcutoffCircOne : 0 ≤ cutoffCircOne)
    (hcutoffCircS : 0 ≤ cutoffCircS)
    (hfull :
      ∀ N : ℕ,
        CubeDescendantDualFullVectorPoincareEstimate Q poincareConst
          (cubeFluctuation Q
            (canonicalMaximizerPotentialDefectOnCube Q
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
              p q p0))
          dualField N)
    (hcutoffSmooth :
      ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => cutoffGradient x i))
    (hcutoffDeriv :
      ∀ i : Fin d, ∀ z ∈ cubeSet Q,
        ‖fderiv ℝ (fun x => cutoffGradient x i) z‖ ≤ cutoffDerivative)
    (hdualCircOne :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => dualField x i) ≤ cutoffCircOne)
    (hdualCircS :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => dualField x i) ≤ cutoffCircS)
    (hcutoffConstant_bound :
      cubeLpNorm Q (2 : ℝ≥0∞)
            (canonicalMaximizerPotentialDefectOnCube Q
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
              p q p0) *
          (cutoffDerivative + cubeBesovScaleWeight 1 Q *
            cubeLpNorm Q ∞ cutoffGradient) ≤
        cutoffConstant)
    (hcenteredCutoffConstant_bound :
      2 * (cubeScaleFactor Q * cutoffDerivative *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * poincareConst) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) * cutoffCircOne)) +
        cubeLpNorm Q ∞ cutoffGradient *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * poincareConst) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) * cutoffCircS))) ≤
        centeredCutoffConstant) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    |centeredResponseJOnCube Q (F.coeffOn Q) p q p0 q0 -
        cutoffWeightedChildResponseJOnFamilyAtDepth F Q j φ p q| ≤
      (2 * C) *
          (Real.sqrt (responseJPartitionDefectOnFamilyAtDepth F Q j p q) *
            Real.sqrt (childResponseJAverageOnFamilyAtDepth F Q j p q)) +
        Cosc * scaleSep * Ch04.restrictionResponseJObservableCubeSet Q p q a +
          |cutoffLinearPairTermOnCube Q (F.coeffOn Q) φ p q p0 q0| +
            cutoffProductBridgeRHS Q s cutoffGradient
              (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q 1 p q q0 a.toFun)
              (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q s p q q0 a.toFun)
              ‖Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun - q0‖
              cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant := by
  intro F
  let P : ℝ :=
    cutoffProductBridgeRHS Q s cutoffGradient
      (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q 1 p q q0 a.toFun)
      (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q s p q q0 a.toFun)
      ‖Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun - q0‖
      cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant
  have hOsc_int :
      ∀ R ∈ descendantsAtDepth Q j,
        IntegrableOn
          (fun x =>
            (cubeAverage R φ - φ x) *
              topHalfEnergyDensityOnCube Q (F.coeffOn Q) p q x)
          (cubeSet R) volume := by
    simpa [F] using
      cutoffOscillationTermOnCubeAtDepth_integrableOn_descendants_of_ae_bounded
        Q (F.coeffOn Q) j p q hφ_meas hφ_bound
  have hdet :
      |centeredResponseJOnCube Q (F.coeffOn Q) p q p0 q0 -
          cutoffWeightedChildResponseJOnFamilyAtDepth F Q j φ p q| ≤
        (2 * C) *
            (Real.sqrt (responseJPartitionDefectOnFamilyAtDepth F Q j p q) *
              Real.sqrt (childResponseJAverageOnFamilyAtDepth F Q j p q)) +
          |cutoffOscillationTermOnCubeAtDepth Q (F.coeffOn Q) j φ p q| +
            |cutoffLinearPairTermOnCube Q (F.coeffOn Q) φ p q p0 q0| +
              P := by
    simpa [F, P] using
      abs_centeredResponseJOnCube_sub_cutoffWeightedChildResponseJOnDependentFamily_le_additivityDefect_add_cutoffOscillation_add_linearPair_add_cutoffProductBridgeRHS
        (a := a) (ha := ha) (Q := Q) (j := j) (s := s) (φ := φ)
        (p := p) (q := q) (p0 := p0) (q0 := q0)
        (dualField := dualField) (cutoffGradient := cutoffGradient)
        (C := C) (cutoffCircOne := cutoffCircOne) (cutoffCircS := cutoffCircS)
        (cutoffDerivative := cutoffDerivative) (poincareConst := poincareConst)
        (cutoffConstant := cutoffConstant)
        (centeredCutoffConstant := centeredCutoffConstant)
        hC hCut hφ_int hRem_int hProduct_int hGradLinear_int hFluxLinear_int
        hOsc_int hMean hφ hφ_compact hφ_sub hcutoffGradient_eq
        hcutoffDerivative hs_pos hs_lt_one hdualField hcutoffGradient
        hcutoffConstant hcenteredCutoffConstant hpoincareConst
        hcutoffCircOne hcutoffCircS hfull hcutoffSmooth hcutoffDeriv
        hdualCircOne hdualCircS hcutoffConstant_bound hcenteredCutoffConstant_bound
  have hosc :
      |cutoffOscillationTermOnCubeAtDepth Q (F.coeffOn Q) j φ p q| ≤
        Cosc * scaleSep * Ch04.restrictionResponseJObservableCubeSet Q p q a := by
    simpa [F] using
      abs_cutoffOscillationTermOnDependentFamilyAtDepth_le_scale_mul_restrictionResponseJObservableCubeSet_of_ae_bounded_cutoff
        (a := a) (ha := ha) (Q := Q) (j := j) (φ := φ)
        (B := B) (C := Cosc) (scaleSep := scaleSep)
        p q hφ_meas hφ_bound hOscPoint
  exact hdet.trans (by nlinarith [hosc])

/-- Deterministic assembled Section 5.3 estimate with all four displayed
split terms replaced by their current deterministic manuscript bounds.  This
is the pointwise estimate to feed into the expectation step. -/
theorem abs_centeredResponseJOnCube_sub_cutoffWeightedChildResponseJOnDependentFamily_le_additivityDefect_add_cutoffOscillationBound_add_linearWeakNorms_add_cutoffProductBridgeRHS
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d)
    (j : ℕ) (s t : ℝ) (φ : Vec d → ℝ) (p q p0 q0 : Vec d)
    (dualField cutoffGradient : Vec d → Vec d)
    {C B Cosc scaleSep BφS BφT cutoffCircOne cutoffCircS cutoffDerivative
      poincareConst cutoffConstant centeredCutoffConstant : ℝ}
    (hC : 0 ≤ C)
    (hCut : ∀ R ∈ descendantsAtDepth Q j, |1 - cubeAverage R φ| ≤ C)
    (hφ_int : IntegrableOn φ (cubeSet Q) volume)
    (hRem_int :
      IntegrableOn
        (fun x => (1 - φ x) *
          topHalfEnergyDensityOnCube Q
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
            p q x)
        (cubeSet Q) volume)
    (hProduct_int :
      IntegrableOn
        (fun x => φ x *
          centeredProductDensityOnCube Q
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
            p q p0 q0 x)
        (cubeSet Q) volume)
    (hGradLinear_int :
      IntegrableOn
        (fun x => φ x *
          centeredGradientLinearDensityOnCube Q
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
            p q p0 q0 x)
        (cubeSet Q) volume)
    (hFluxLinear_int :
      IntegrableOn
        (fun x => φ x *
          centeredFluxLinearDensityOnCube Q
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
            p q p0 q0 x)
        (cubeSet Q) volume)
    (hGradField :
      ∀ i : Fin d,
        IntegrableOn
          (fun x =>
            (φ x • canonicalMaximizerGradientDefectOnCube Q
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
              p q p0 x) i)
          (cubeSet Q) volume)
    (hFluxField :
      ∀ i : Fin d,
        IntegrableOn
          (fun x =>
            (φ x • canonicalMaximizerFluxDefectOnCube Q
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
              p q q0 x) i)
          (cubeSet Q) volume)
    (hMean : cubeAverage Q φ = 1)
    (hφ_meas : AEStronglyMeasurable φ (volumeMeasureOn (cubeSet Q)))
    (hφ_bound : ∀ᵐ x ∂ volumeMeasureOn (cubeSet Q), ‖φ x‖ ≤ B)
    (hOscPoint :
      ∀ R ∈ descendantsAtDepth Q j,
        ∀ᵐ x ∂ volumeMeasureOn (cubeSet R),
          |cubeAverage R φ - φ x| ≤ Cosc * scaleSep)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ openCubeSet Q)
    (hcutoffGradient_eq : cutoffGradient = scalarCutoffGradientField φ)
    (hcutoffDerivative : 0 ≤ cutoffDerivative)
    (hs_pos : 0 < s) (hs_lt_one : s < 1) (ht_pos : 0 < t)
    (hBφS : 0 ≤ BφS) (hBφT : 0 ≤ BφT)
    (hφDualS :
      ∀ N : ℕ, cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N φ ≤ BφS)
    (hφDualT :
      ∀ N : ℕ, cubeBesovDualTestNorm Q t (2 : ℝ≥0∞) (1 : ℝ≥0∞) N φ ≤ BφT)
    (hφMem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) φ)
    (hdualField :
      ∀ i : Fin d,
        MemLp (fun x => dualField x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hcutoffGradient : MemLp cutoffGradient ∞ (normalizedCubeMeasure Q))
    (hcutoffConstant : 0 ≤ cutoffConstant)
    (hcenteredCutoffConstant : 0 ≤ centeredCutoffConstant)
    (hpoincareConst : 0 ≤ poincareConst)
    (hcutoffCircOne : 0 ≤ cutoffCircOne)
    (hcutoffCircS : 0 ≤ cutoffCircS)
    (hfull :
      ∀ N : ℕ,
        CubeDescendantDualFullVectorPoincareEstimate Q poincareConst
          (cubeFluctuation Q
            (canonicalMaximizerPotentialDefectOnCube Q
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
              p q p0))
          dualField N)
    (hcutoffSmooth :
      ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => cutoffGradient x i))
    (hcutoffDeriv :
      ∀ i : Fin d, ∀ z ∈ cubeSet Q,
        ‖fderiv ℝ (fun x => cutoffGradient x i) z‖ ≤ cutoffDerivative)
    (hdualCircOne :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => dualField x i) ≤ cutoffCircOne)
    (hdualCircS :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => dualField x i) ≤ cutoffCircS)
    (hcutoffConstant_bound :
      cubeLpNorm Q (2 : ℝ≥0∞)
            (canonicalMaximizerPotentialDefectOnCube Q
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
              p q p0) *
          (cutoffDerivative + cubeBesovScaleWeight 1 Q *
            cubeLpNorm Q ∞ cutoffGradient) ≤
        cutoffConstant)
    (hcenteredCutoffConstant_bound :
      2 * (cubeScaleFactor Q * cutoffDerivative *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * poincareConst) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) * cutoffCircOne)) +
        cubeLpNorm Q ∞ cutoffGradient *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * ((Fintype.card (Fin d) : ℝ) * poincareConst) *
              (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) * cutoffCircS))) ≤
        centeredCutoffConstant) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    let gradWeak := Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun
    let fluxWeak := Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun
    let gradCoeff :=
      (3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovScaleWeight (-s) Q * BφS
    let fluxCoeff :=
      (3 : ℝ) ^ ((d : ℝ) + t) * cubeBesovScaleWeight (-t) Q * BφT
    |centeredResponseJOnCube Q (F.coeffOn Q) p q p0 q0 -
        cutoffWeightedChildResponseJOnFamilyAtDepth F Q j φ p q| ≤
      (2 * C) *
          (Real.sqrt (responseJPartitionDefectOnFamilyAtDepth F Q j p q) *
            Real.sqrt (childResponseJAverageOnFamilyAtDepth F Q j p q)) +
        Cosc * scaleSep * Ch04.restrictionResponseJObservableCubeSet Q p q a +
          ((1 / 2 : ℝ) * ‖q0‖ *
              (((Fintype.card (Fin d) : ℝ) * gradCoeff) * gradWeak) +
            (1 / 2 : ℝ) * ‖p0‖ *
              (((Fintype.card (Fin d) : ℝ) * fluxCoeff) * fluxWeak)) +
            cutoffProductBridgeRHS Q s cutoffGradient
              (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q 1 p q q0 a.toFun)
              (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q s p q q0 a.toFun)
              ‖Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun - q0‖
              cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant := by
  intro F gradWeak fluxWeak gradCoeff fluxCoeff
  let P : ℝ :=
    cutoffProductBridgeRHS Q s cutoffGradient
      (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q 1 p q q0 a.toFun)
      (Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q s p q q0 a.toFun)
      ‖Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun - q0‖
      cutoffCircOne poincareConst cutoffConstant centeredCutoffConstant
  let L : ℝ :=
    (1 / 2 : ℝ) * ‖q0‖ *
        (((Fintype.card (Fin d) : ℝ) * gradCoeff) * gradWeak) +
      (1 / 2 : ℝ) * ‖p0‖ *
        (((Fintype.card (Fin d) : ℝ) * fluxCoeff) * fluxWeak)
  let A : ℝ :=
    (2 * C) *
        (Real.sqrt (responseJPartitionDefectOnFamilyAtDepth F Q j p q) *
          Real.sqrt (childResponseJAverageOnFamilyAtDepth F Q j p q)) +
      Cosc * scaleSep * Ch04.restrictionResponseJObservableCubeSet Q p q a
  have hdet :
      |centeredResponseJOnCube Q (F.coeffOn Q) p q p0 q0 -
          cutoffWeightedChildResponseJOnFamilyAtDepth F Q j φ p q| ≤
        A + |cutoffLinearPairTermOnCube Q (F.coeffOn Q) φ p q p0 q0| + P := by
    simpa [F, P, A, add_assoc] using
      abs_centeredResponseJOnCube_sub_cutoffWeightedChildResponseJOnDependentFamily_le_additivityDefect_add_cutoffOscillationBound_add_linearPair_add_cutoffProductBridgeRHS
        (a := a) (ha := ha) (Q := Q) (j := j) (s := s) (φ := φ)
        (p := p) (q := q) (p0 := p0) (q0 := q0)
        (dualField := dualField) (cutoffGradient := cutoffGradient)
        (C := C) (B := B) (Cosc := Cosc) (scaleSep := scaleSep)
        (cutoffCircOne := cutoffCircOne) (cutoffCircS := cutoffCircS)
        (cutoffDerivative := cutoffDerivative) (poincareConst := poincareConst)
        (cutoffConstant := cutoffConstant)
        (centeredCutoffConstant := centeredCutoffConstant)
        hC hCut hφ_int hRem_int hProduct_int hGradLinear_int hFluxLinear_int
        hMean hφ_meas hφ_bound hOscPoint hφ hφ_compact hφ_sub
        hcutoffGradient_eq hcutoffDerivative hs_pos hs_lt_one hdualField
        hcutoffGradient hcutoffConstant hcenteredCutoffConstant
        hpoincareConst hcutoffCircOne hcutoffCircS hfull hcutoffSmooth
        hcutoffDeriv hdualCircOne hdualCircS hcutoffConstant_bound
        hcenteredCutoffConstant_bound
  have hlin :
      |cutoffLinearPairTermOnCube Q (F.coeffOn Q) φ p q p0 q0| ≤ L := by
    simpa [F, gradWeak, fluxWeak, gradCoeff, fluxCoeff, L] using
      abs_cutoffLinearPairTermOnDependentFamily_le_ch04WeakNorms_of_cutoffDualBounds
        (a := a) (ha := ha) (Q := Q) (s := s) (t := t)
        (φ := φ) (p := p) (q := q) (p0 := p0) (q0 := q0)
        (BφS := BφS) (BφT := BφT)
        hGradField hFluxField hs_pos ht_pos hBφS hBφT hφDualS hφDualT hφMem
  have hreplace :
      A + |cutoffLinearPairTermOnCube Q (F.coeffOn Q) φ p q p0 q0| + P ≤
        A + L + P :=
    by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right (add_le_add_left hlin A) P
  have hmain := hdet.trans hreplace
  simpa [A, L, P, add_assoc] using hmain

/-- Deterministic pointwise estimate with the product term in the final
scaled-gradient/scaled-flux weak-norm form. -/
theorem abs_centeredResponseJOnCube_sub_cutoffWeightedChildResponseJOnDependentFamily_le_additivityDefect_add_cutoffOscillationBound_add_linearWeakNorms_add_scaledProduct
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d)
    (j : ℕ) (s t : ℝ) (φ : Vec d → ℝ) (p q p0 q0 : Vec d)
    {C B Cosc scaleSep BφS BφT cutoffDerivative : ℝ}
    (hC : 0 ≤ C)
    (hCut : ∀ R ∈ descendantsAtDepth Q j, |1 - cubeAverage R φ| ≤ C)
    (hφ_int : IntegrableOn φ (cubeSet Q) volume)
    (hRem_int :
      IntegrableOn
        (fun x => (1 - φ x) *
          topHalfEnergyDensityOnCube Q
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
            p q x)
        (cubeSet Q) volume)
    (hProduct_int :
      IntegrableOn
        (fun x => φ x *
          centeredProductDensityOnCube Q
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
            p q p0 q0 x)
        (cubeSet Q) volume)
    (hGradLinear_int :
      IntegrableOn
        (fun x => φ x *
          centeredGradientLinearDensityOnCube Q
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
            p q p0 q0 x)
        (cubeSet Q) volume)
    (hFluxLinear_int :
      IntegrableOn
        (fun x => φ x *
          centeredFluxLinearDensityOnCube Q
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
            p q p0 q0 x)
        (cubeSet Q) volume)
    (hGradField :
      ∀ i : Fin d,
        IntegrableOn
          (fun x =>
            (φ x • canonicalMaximizerGradientDefectOnCube Q
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
              p q p0 x) i)
          (cubeSet Q) volume)
    (hFluxField :
      ∀ i : Fin d,
        IntegrableOn
          (fun x =>
            (φ x • canonicalMaximizerFluxDefectOnCube Q
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
              p q q0 x) i)
          (cubeSet Q) volume)
    (hMean : cubeAverage Q φ = 1)
    (hφ_meas : AEStronglyMeasurable φ (volumeMeasureOn (cubeSet Q)))
    (hφ_bound : ∀ᵐ x ∂ volumeMeasureOn (cubeSet Q), ‖φ x‖ ≤ B)
    (hOscPoint :
      ∀ R ∈ descendantsAtDepth Q j,
        ∀ᵐ x ∂ volumeMeasureOn (cubeSet R),
          |cubeAverage R φ - φ x| ≤ Cosc * scaleSep)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ openCubeSet Q)
    (hcutoffDerivative : 0 ≤ cutoffDerivative)
    (hs_pos : 0 < s) (hs_lt_one : s < 1) (ht_pos : 0 < t)
    (hst : s + t ≤ 1)
    (hBφS : 0 ≤ BφS) (hBφT : 0 ≤ BφT)
    (hφDualS :
      ∀ N : ℕ, cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N φ ≤ BφS)
    (hφDualT :
      ∀ N : ℕ, cubeBesovDualTestNorm Q t (2 : ℝ≥0∞) (1 : ℝ≥0∞) N φ ≤ BφT)
    (hφMem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) φ)
    (hcutoffGradient :
      MemLp (scalarCutoffGradientField φ) ∞ (normalizedCubeMeasure Q))
    (hcutoffSmooth :
      ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞)
        (fun x => scalarCutoffGradientField φ x i))
    (hcutoffDeriv :
      ∀ i : Fin d, ∀ z ∈ cubeSet Q,
        ‖fderiv ℝ (fun x => scalarCutoffGradientField φ x i) z‖ ≤ cutoffDerivative) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    let gradWeak := Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun
    let fluxWeak := Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun
    let gradCoeff :=
      (3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovScaleWeight (-s) Q * BφS
    let fluxCoeff :=
      (3 : ℝ) ^ ((d : ℝ) + t) * cubeBesovScaleWeight (-t) Q * BφT
    let scaledGrad := cubeBesovScaleWeight (-s) Q * gradWeak
    let scaledFlux := cubeBesovScaleWeight (-t) Q * fluxWeak
    let productCoeff :=
      cutoffProductScaledWeakNormCoeff Q s t cutoffDerivative (scalarCutoffGradientField φ)
    |centeredResponseJOnCube Q (F.coeffOn Q) p q p0 q0 -
        cutoffWeightedChildResponseJOnFamilyAtDepth F Q j φ p q| ≤
      (2 * C) *
          (Real.sqrt (responseJPartitionDefectOnFamilyAtDepth F Q j p q) *
            Real.sqrt (childResponseJAverageOnFamilyAtDepth F Q j p q)) +
        Cosc * scaleSep * Ch04.restrictionResponseJObservableCubeSet Q p q a +
          ((1 / 2 : ℝ) * ‖q0‖ *
              (((Fintype.card (Fin d) : ℝ) * gradCoeff) * gradWeak) +
            (1 / 2 : ℝ) * ‖p0‖ *
              (((Fintype.card (Fin d) : ℝ) * fluxCoeff) * fluxWeak)) +
            productCoeff * (scaledGrad * scaledFlux) := by
  intro F gradWeak fluxWeak gradCoeff fluxCoeff scaledGrad scaledFlux productCoeff
  let L : ℝ :=
    (1 / 2 : ℝ) * ‖q0‖ *
        (((Fintype.card (Fin d) : ℝ) * gradCoeff) * gradWeak) +
      (1 / 2 : ℝ) * ‖p0‖ *
        (((Fintype.card (Fin d) : ℝ) * fluxCoeff) * fluxWeak)
  let P : ℝ := productCoeff * (scaledGrad * scaledFlux)
  let A : ℝ :=
    (2 * C) *
        (Real.sqrt (responseJPartitionDefectOnFamilyAtDepth F Q j p q) *
          Real.sqrt (childResponseJAverageOnFamilyAtDepth F Q j p q)) +
      Cosc * scaleSep * Ch04.restrictionResponseJObservableCubeSet Q p q a
  have hOsc_int :
      ∀ R ∈ descendantsAtDepth Q j,
        IntegrableOn
          (fun x =>
            (cubeAverage R φ - φ x) *
              topHalfEnergyDensityOnCube Q (F.coeffOn Q) p q x)
          (cubeSet R) volume := by
    simpa [F] using
      cutoffOscillationTermOnCubeAtDepth_integrableOn_descendants_of_ae_bounded
        Q (F.coeffOn Q) j p q hφ_meas hφ_bound
  have hdet :
      |centeredResponseJOnCube Q (F.coeffOn Q) p q p0 q0 -
          cutoffWeightedChildResponseJOnFamilyAtDepth F Q j φ p q| ≤
        (2 * C) *
            (Real.sqrt (responseJPartitionDefectOnFamilyAtDepth F Q j p q) *
              Real.sqrt (childResponseJAverageOnFamilyAtDepth F Q j p q)) +
          |cutoffOscillationTermOnCubeAtDepth Q (F.coeffOn Q) j φ p q| +
            |cutoffLinearPairTermOnCube Q (F.coeffOn Q) φ p q p0 q0| +
              |cutoffProductTermOnCube Q (F.coeffOn Q) φ p q p0 q0| := by
    simpa [F] using
      abs_centeredResponseJOnCube_sub_cutoffWeightedChildResponseJOnDependentFamily_le_additivityDefect_add_cutoffOscillation_add_linearPair_add_product
        (a := a) (ha := ha) (Q := Q) (j := j) (φ := φ)
        (p := p) (q := q) (p0 := p0) (q0 := q0)
        hC hCut hφ_int hRem_int hProduct_int hGradLinear_int hFluxLinear_int
        hOsc_int hMean
  have hosc :
      |cutoffOscillationTermOnCubeAtDepth Q (F.coeffOn Q) j φ p q| ≤
        Cosc * scaleSep * Ch04.restrictionResponseJObservableCubeSet Q p q a := by
    simpa [F] using
      abs_cutoffOscillationTermOnDependentFamilyAtDepth_le_scale_mul_restrictionResponseJObservableCubeSet_of_ae_bounded_cutoff
        (a := a) (ha := ha) (Q := Q) (j := j) (φ := φ)
        (B := B) (C := Cosc) (scaleSep := scaleSep)
        p q hφ_meas hφ_bound hOscPoint
  have hlin :
      |cutoffLinearPairTermOnCube Q (F.coeffOn Q) φ p q p0 q0| ≤ L := by
    simpa [F, gradWeak, fluxWeak, gradCoeff, fluxCoeff, L] using
      abs_cutoffLinearPairTermOnDependentFamily_le_ch04WeakNorms_of_cutoffDualBounds
        (a := a) (ha := ha) (Q := Q) (s := s) (t := t)
        (φ := φ) (p := p) (q := q) (p0 := p0) (q0 := q0)
        (BφS := BφS) (BφT := BφT)
        hGradField hFluxField hs_pos ht_pos hBφS hBφT hφDualS hφDualT hφMem
  have hprod :
      |cutoffProductTermOnCube Q (F.coeffOn Q) φ p q p0 q0| ≤ P := by
    simpa [F, gradWeak, fluxWeak, scaledGrad, scaledFlux, productCoeff, P,
      cutoffProductScaledWeakNormCoeff] using
      abs_cutoffProductTermOnDependentFamily_le_scaledWeakNormProduct
        (Q := Q) (s := s) (t := t) hs_pos hs_lt_one ht_pos hst
        (a := a) (ha := ha) (φ := φ) (p := p) (q := q) (p0 := p0) (q0 := q0)
        (B := cutoffDerivative) hcutoffDerivative
        hφ hφ_compact hφ_sub hcutoffGradient hcutoffSmooth hcutoffDeriv
  have hreplace :
      (2 * C) *
          (Real.sqrt (responseJPartitionDefectOnFamilyAtDepth F Q j p q) *
            Real.sqrt (childResponseJAverageOnFamilyAtDepth F Q j p q)) +
        |cutoffOscillationTermOnCubeAtDepth Q (F.coeffOn Q) j φ p q| +
          |cutoffLinearPairTermOnCube Q (F.coeffOn Q) φ p q p0 q0| +
            |cutoffProductTermOnCube Q (F.coeffOn Q) φ p q p0 q0| ≤
        A + L + P := by
    nlinarith [hosc, hlin, hprod]
  exact hdet.trans (by simpa [A, L, P, add_assoc] using hreplace)

end

end JUpperBoundWeakNorms
end Section53
end Ch05
end Book
end Homogenization
