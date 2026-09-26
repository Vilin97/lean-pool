/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Additivity.CrossTerm

/-! # Five Term Split -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundWeakNorms

/-!
# FiveTermSplit

Deterministic five-term splitting of the centered response.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

noncomputable section

/-- Cutoff insertion and descendant partition for the parent centered response,
before the mean-defect term is rewritten using child energies. -/
theorem centeredResponseJOnCube_eq_cutoffProduct_add_cutoffOscillation_add_meanDefect_add_linearPair
    {d : ℕ} (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (j : ℕ) (φ : Vec d → ℝ) (p q p0 q0 : Vec d)
    (hTop_int :
      IntegrableOn (topHalfEnergyDensityOnCube Q a p q)
        (cubeSet Q) volume)
    (hφ_int : IntegrableOn φ (cubeSet Q) volume)
    (hRem_int :
      IntegrableOn
        (fun x => (1 - φ x) * topHalfEnergyDensityOnCube Q a p q x)
        (cubeSet Q) volume)
    (hProduct_int :
      IntegrableOn
        (fun x => φ x * centeredProductDensityOnCube Q a p q p0 q0 x)
        (cubeSet Q) volume)
    (hGradLinear_int :
      IntegrableOn
        (fun x => φ x * centeredGradientLinearDensityOnCube Q a p q p0 q0 x)
        (cubeSet Q) volume)
    (hFluxLinear_int :
      IntegrableOn
        (fun x => φ x * centeredFluxLinearDensityOnCube Q a p q p0 q0 x)
        (cubeSet Q) volume)
    (hOsc_int :
      ∀ R ∈ descendantsAtDepth Q j,
        IntegrableOn
          (fun x =>
            (cubeAverage R φ - φ x) * topHalfEnergyDensityOnCube Q a p q x)
          (cubeSet R) volume)
    (hMean : cubeAverage Q φ = 1) :
    centeredResponseJOnCube Q a p q p0 q0 =
      cutoffProductTermOnCube Q a φ p q p0 q0 +
        cutoffOscillationTermOnCubeAtDepth Q a j φ p q +
          meanDefectTopEnergyTermOnCubeAtDepth Q a j φ p q +
            cutoffLinearPairTermOnCube Q a φ p q p0 q0 := by
  classical
  let F : Vec d → ℝ := topHalfEnergyDensityOnCube Q a p q
  let c : ℝ := (1 / 2 : ℝ) * vecDot p0 q0
  let Pden : Vec d → ℝ := centeredProductDensityOnCube Q a p q p0 q0
  let Gden : Vec d → ℝ := centeredGradientLinearDensityOnCube Q a p q p0 q0
  let Hden : Vec d → ℝ := centeredFluxLinearDensityOnCube Q a p q p0 q0
  have hF_norm : Integrable F (normalizedCubeMeasure Q) :=
    integrable_normalizedCubeMeasure_of_integrableOn_cubeSet Q
      (by simpa [F] using hTop_int)
  have hφ_norm : Integrable φ (normalizedCubeMeasure Q) :=
    integrable_normalizedCubeMeasure_of_integrableOn_cubeSet Q hφ_int
  have hRem_norm : Integrable (fun x => (1 - φ x) * F x) (normalizedCubeMeasure Q) :=
    integrable_normalizedCubeMeasure_of_integrableOn_cubeSet Q
      (by simpa [F] using hRem_int)
  have hProduct_norm :
      Integrable (fun x => φ x * Pden x) (normalizedCubeMeasure Q) :=
    integrable_normalizedCubeMeasure_of_integrableOn_cubeSet Q
      (by simpa [Pden] using hProduct_int)
  have hGrad_norm :
      Integrable (fun x => φ x * Gden x) (normalizedCubeMeasure Q) :=
    integrable_normalizedCubeMeasure_of_integrableOn_cubeSet Q
      (by simpa [Gden] using hGradLinear_int)
  have hFlux_norm :
      Integrable (fun x => φ x * Hden x) (normalizedCubeMeasure Q) :=
    integrable_normalizedCubeMeasure_of_integrableOn_cubeSet Q
      (by simpa [Hden] using hFluxLinear_int)
  have hCutPoint :
      (fun x => φ x * (F x - c)) =
        fun x => φ x * Pden x + (φ x * Gden x + φ x * Hden x) := by
    funext x
    have hcenter :
        F x - c = Pden x + Gden x + Hden x := by
      calc
        F x - c =
            centeredProductDensityOnCube Q a p q p0 q0 x +
              centeredGradientLinearDensityOnCube Q a p q p0 q0 x +
                centeredFluxLinearDensityOnCube Q a p q p0 q0 x := by
              simpa [F, c] using
                (centeredProduct_add_linear_densities_eq_topHalfEnergy_sub_half_dot
                  Q a p q p0 q0 x).symm
        _ = Pden x + Gden x + Hden x := by
              simp [Pden, Gden, Hden]
    rw [hcenter]
    ring
  have hCut_norm :
      Integrable (fun x => φ x * (F x - c)) (normalizedCubeMeasure Q) := by
    have hsum :
        Integrable
          (fun x => φ x * Pden x + (φ x * Gden x + φ x * Hden x))
          (normalizedCubeMeasure Q) :=
      hProduct_norm.add (hGrad_norm.add hFlux_norm)
    simpa [hCutPoint] using hsum
  have hCutoffInsert :
      cubeAverage Q F - c =
        cubeAverage Q (fun x => φ x * (F x - c)) +
          cubeAverage Q (fun x => (1 - φ x) * F x) :=
    cubeAverage_sub_const_eq_cubeAverage_cutoff_centered_add_cubeAverage_one_sub_cutoff_mul
      Q hF_norm hφ_norm hCut_norm hRem_norm hMean
  have hCutAvg :
      cubeAverage Q (fun x => φ x * (F x - c)) =
        cutoffProductTermOnCube Q a φ p q p0 q0 +
          cutoffLinearPairTermOnCube Q a φ p q p0 q0 := by
    rw [hCutPoint]
    rw [cubeAverage_add_of_integrableOn Q
      (fun x => φ x * Pden x)
      (fun x => φ x * Gden x + φ x * Hden x)]
    · rw [cubeAverage_add_of_integrableOn Q
        (fun x => φ x * Gden x) (fun x => φ x * Hden x)]
      · simp [Pden, Gden, Hden, cutoffProductTermOnCube,
          cutoffLinearPairTermOnCube, cutoffGradientLinearTermOnCube,
          cutoffFluxLinearTermOnCube]
      · simpa [Gden] using hGradLinear_int
      · simpa [Hden] using hFluxLinear_int
    · simpa [Pden] using hProduct_int
    · simpa [Gden, Hden] using! hGradLinear_int.add hFluxLinear_int
  have hRemAvg :
      cubeAverage Q (fun x => (1 - φ x) * F x) =
        cutoffOscillationTermOnCubeAtDepth Q a j φ p q +
          meanDefectTopEnergyTermOnCubeAtDepth Q a j φ p q := by
    have hpart :=
      cubeAverage_one_sub_cutoff_mul_eq_descendantsAverage_cutoff_oscillation_add_mean_defect
        Q j φ F
        (by simpa [F] using hRem_int)
        (by
          intro R hR
          simpa [F] using hOsc_int R hR)
        (by
          intro R hR
          exact hTop_int.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR))
    rw [hpart]
    rw [descendantsAverage_add]
    simp [F, cutoffOscillationTermOnCubeAtDepth,
      meanDefectTopEnergyTermOnCubeAtDepth]
  calc
    centeredResponseJOnCube Q a p q p0 q0
        = cubeAverage Q F - c := by
            simpa [F, c] using
              centeredResponseJOnCube_eq_cubeAverage_topHalfEnergy_sub_half_dot
                Q a p q p0 q0
    _ = cubeAverage Q (fun x => φ x * (F x - c)) +
          cubeAverage Q (fun x => (1 - φ x) * F x) := hCutoffInsert
    _ = (cutoffProductTermOnCube Q a φ p q p0 q0 +
          cutoffLinearPairTermOnCube Q a φ p q p0 q0) +
          (cutoffOscillationTermOnCubeAtDepth Q a j φ p q +
            meanDefectTopEnergyTermOnCubeAtDepth Q a j φ p q) := by
            rw [hCutAvg, hRemAvg]
    _ =
      cutoffProductTermOnCube Q a φ p q p0 q0 +
        cutoffOscillationTermOnCubeAtDepth Q a j φ p q +
          meanDefectTopEnergyTermOnCubeAtDepth Q a j φ p q +
            cutoffLinearPairTermOnCube Q a φ p q p0 q0 := by
          ring

/-- The parent-energy mean-defect term becomes additivity-cross plus the
cutoff-weighted child response once child energy has been identified. -/
theorem meanDefectTopEnergyTermOnCubeAtDepth_eq_additivityCross_add_cutoffWeightedChildResponseJ
    {d : ℕ} (a : Ch02.TriadicCoeffFamily d) (Q : TriadicCube d)
    (j : ℕ) (φ : Vec d → ℝ) (p q : Vec d)
    (cross : TriadicCube d → ℝ)
    (hChildEnergy :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeAverage R (topHalfEnergyDensityOnCube Q (a.coeffOn Q) p q) =
          cross R + Ch02.responseJ (Ch02.cubeDomain R) (a.coeffOn R) p q) :
    meanDefectTopEnergyTermOnCubeAtDepth Q (a.coeffOn Q) j φ p q =
      additivityCrossTermOnCubeAtDepth Q j φ cross +
        cutoffWeightedChildResponseJOnFamilyAtDepth a Q j φ p q := by
  classical
  unfold meanDefectTopEnergyTermOnCubeAtDepth additivityCrossTermOnCubeAtDepth
    cutoffWeightedChildResponseJOnFamilyAtDepth cutoffChildWeight
  rw [← descendantsAverage_add]
  refine descendantsAverage_congr_of_eq_on_descendants Q j ?_
  intro R hR
  rw [hChildEnergy R hR]
  ring

/-- Deterministic analytic core of the first Section 5.3 lemma: the centered
parent response minus the cutoff-weighted child response splits into the
additivity cross term, cutoff oscillation, linear terms, and product term. -/
theorem centeredResponseJOnCube_sub_cutoffWeightedChildResponseJ_eq_additivityCross_add_cutoffOscillation_add_linearPair_add_product
    {d : ℕ} (a : Ch02.TriadicCoeffFamily d) (Q : TriadicCube d)
    (j : ℕ) (φ : Vec d → ℝ) (p q p0 q0 : Vec d)
    (cross : TriadicCube d → ℝ)
    (hTop_int :
      IntegrableOn (topHalfEnergyDensityOnCube Q (a.coeffOn Q) p q)
        (cubeSet Q) volume)
    (hφ_int : IntegrableOn φ (cubeSet Q) volume)
    (hRem_int :
      IntegrableOn
        (fun x => (1 - φ x) * topHalfEnergyDensityOnCube Q (a.coeffOn Q) p q x)
        (cubeSet Q) volume)
    (hProduct_int :
      IntegrableOn
        (fun x => φ x *
          centeredProductDensityOnCube Q (a.coeffOn Q) p q p0 q0 x)
        (cubeSet Q) volume)
    (hGradLinear_int :
      IntegrableOn
        (fun x => φ x *
          centeredGradientLinearDensityOnCube Q (a.coeffOn Q) p q p0 q0 x)
        (cubeSet Q) volume)
    (hFluxLinear_int :
      IntegrableOn
        (fun x => φ x *
          centeredFluxLinearDensityOnCube Q (a.coeffOn Q) p q p0 q0 x)
        (cubeSet Q) volume)
    (hOsc_int :
      ∀ R ∈ descendantsAtDepth Q j,
        IntegrableOn
          (fun x =>
            (cubeAverage R φ - φ x) *
              topHalfEnergyDensityOnCube Q (a.coeffOn Q) p q x)
          (cubeSet R) volume)
    (hMean : cubeAverage Q φ = 1)
    (hChildEnergy :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeAverage R (topHalfEnergyDensityOnCube Q (a.coeffOn Q) p q) =
          cross R + Ch02.responseJ (Ch02.cubeDomain R) (a.coeffOn R) p q) :
    centeredResponseJOnCube Q (a.coeffOn Q) p q p0 q0 -
        cutoffWeightedChildResponseJOnFamilyAtDepth a Q j φ p q =
      additivityCrossTermOnCubeAtDepth Q j φ cross +
        cutoffOscillationTermOnCubeAtDepth Q (a.coeffOn Q) j φ p q +
          cutoffLinearPairTermOnCube Q (a.coeffOn Q) φ p q p0 q0 +
            cutoffProductTermOnCube Q (a.coeffOn Q) φ p q p0 q0 := by
  have hsplit :=
    centeredResponseJOnCube_eq_cutoffProduct_add_cutoffOscillation_add_meanDefect_add_linearPair
      Q (a.coeffOn Q) j φ p q p0 q0 hTop_int hφ_int hRem_int
      hProduct_int hGradLinear_int hFluxLinear_int hOsc_int hMean
  have hmean :=
    meanDefectTopEnergyTermOnCubeAtDepth_eq_additivityCross_add_cutoffWeightedChildResponseJ
      a Q j φ p q cross hChildEnergy
  rw [hsplit, hmean]
  ring

/-- Concrete deterministic analytic core, with the child-energy equality
discharged by the explicit additivity-cross density. -/
theorem centeredResponseJOnCube_sub_cutoffWeightedChildResponseJ_eq_concreteAdditivityCross_add_cutoffOscillation_add_linearPair_add_product
    {d : ℕ} [NeZero d] (a : Ch02.TriadicCoeffFamily d) (Q : TriadicCube d)
    (j : ℕ) (φ : Vec d → ℝ) (p q p0 q0 : Vec d)
    (hTop_int :
      IntegrableOn (topHalfEnergyDensityOnCube Q (a.coeffOn Q) p q)
        (cubeSet Q) volume)
    (hφ_int : IntegrableOn φ (cubeSet Q) volume)
    (hRem_int :
      IntegrableOn
        (fun x => (1 - φ x) * topHalfEnergyDensityOnCube Q (a.coeffOn Q) p q x)
        (cubeSet Q) volume)
    (hProduct_int :
      IntegrableOn
        (fun x => φ x *
          centeredProductDensityOnCube Q (a.coeffOn Q) p q p0 q0 x)
        (cubeSet Q) volume)
    (hGradLinear_int :
      IntegrableOn
        (fun x => φ x *
          centeredGradientLinearDensityOnCube Q (a.coeffOn Q) p q p0 q0 x)
        (cubeSet Q) volume)
    (hFluxLinear_int :
      IntegrableOn
        (fun x => φ x *
          centeredFluxLinearDensityOnCube Q (a.coeffOn Q) p q p0 q0 x)
        (cubeSet Q) volume)
    (hOsc_int :
      ∀ R ∈ descendantsAtDepth Q j,
        IntegrableOn
          (fun x =>
            (cubeAverage R φ - φ x) *
              topHalfEnergyDensityOnCube Q (a.coeffOn Q) p q x)
          (cubeSet R) volume)
    (hMean : cubeAverage Q φ = 1)
    (hCoeff :
      ∀ R ∈ descendantsAtDepth Q j,
        (a.coeffOn Q).toCoeffField = (a.coeffOn R).toCoeffField) :
    centeredResponseJOnCube Q (a.coeffOn Q) p q p0 q0 -
        cutoffWeightedChildResponseJOnFamilyAtDepth a Q j φ p q =
      concreteAdditivityCrossTermOnFamilyAtDepth a Q j φ p q +
        cutoffOscillationTermOnCubeAtDepth Q (a.coeffOn Q) j φ p q +
          cutoffLinearPairTermOnCube Q (a.coeffOn Q) φ p q p0 q0 +
            cutoffProductTermOnCube Q (a.coeffOn Q) φ p q p0 q0 := by
  simpa [concreteAdditivityCrossTermOnFamilyAtDepth] using
    centeredResponseJOnCube_sub_cutoffWeightedChildResponseJ_eq_additivityCross_add_cutoffOscillation_add_linearPair_add_product
      a Q j φ p q p0 q0
      (fun R => cubeAverage R (childAdditivityCrossDensityOnFamilyOnCube a Q R p q))
      hTop_int hφ_int hRem_int hProduct_int hGradLinear_int hFluxLinear_int
      hOsc_int hMean
      (by
        intro R hR
        exact
          cubeAverage_topHalfEnergyOnFamily_eq_childAdditivityCross_add_responseJOnChild
            a Q R p q (hCoeff R hR)
            (childAdditivityCrossDensityOnFamilyOnCube_integrableOn
              a Q hR p q))

/-- Concrete deterministic analytic core for the Chapter 4 dependent
coefficient family.  Here the parent and child representatives are definitionally
the sampled coefficient field, so no representative-equality hypothesis remains. -/
theorem centeredResponseJOnCube_sub_cutoffWeightedChildResponseJ_eq_concreteAdditivityCross_add_cutoffOscillation_add_linearPair_add_product_of_aELocallyUniformlyEllipticField
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d)
    (j : ℕ) (φ : Vec d → ℝ) (p q p0 q0 : Vec d)
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
    (hMean : cubeAverage Q φ = 1) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    centeredResponseJOnCube Q (F.coeffOn Q) p q p0 q0 -
        cutoffWeightedChildResponseJOnFamilyAtDepth F Q j φ p q =
      concreteAdditivityCrossTermOnFamilyAtDepth F Q j φ p q +
        cutoffOscillationTermOnCubeAtDepth Q (F.coeffOn Q) j φ p q +
          cutoffLinearPairTermOnCube Q (F.coeffOn Q) φ p q p0 q0 +
            cutoffProductTermOnCube Q (F.coeffOn Q) φ p q p0 q0 := by
  intro F
  exact
    centeredResponseJOnCube_sub_cutoffWeightedChildResponseJ_eq_concreteAdditivityCross_add_cutoffOscillation_add_linearPair_add_product
      F Q j φ p q p0 q0
      (topHalfEnergyDensityOnCube_integrableOn_cubeSet Q (F.coeffOn Q) p q)
      hφ_int hRem_int hProduct_int hGradLinear_int hFluxLinear_int hOsc_int
      hMean
      (by
        intro R _hR
        simp [F, Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField_coeffOn_toCoeffField])

/-- Deterministic assembled Section 5.3 estimate after the five-term split:
the additivity-cross term is in the manuscript response-partition-defect form,
while the cutoff oscillation, linear pair, and product terms remain as the
separate deterministic terms estimated elsewhere. -/
theorem abs_centeredResponseJOnCube_sub_cutoffWeightedChildResponseJOnDependentFamily_le_additivityDefect_add_cutoffOscillation_add_linearPair_add_product
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d)
    (j : ℕ) (φ : Vec d → ℝ) (p q p0 q0 : Vec d)
    {C : ℝ}
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
    (hMean : cubeAverage Q φ = 1) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    |centeredResponseJOnCube Q (F.coeffOn Q) p q p0 q0 -
        cutoffWeightedChildResponseJOnFamilyAtDepth F Q j φ p q| ≤
      (2 * C) *
          (Real.sqrt (responseJPartitionDefectOnFamilyAtDepth F Q j p q) *
            Real.sqrt (childResponseJAverageOnFamilyAtDepth F Q j p q)) +
        |cutoffOscillationTermOnCubeAtDepth Q (F.coeffOn Q) j φ p q| +
          |cutoffLinearPairTermOnCube Q (F.coeffOn Q) φ p q p0 q0| +
            |cutoffProductTermOnCube Q (F.coeffOn Q) φ p q p0 q0| := by
  intro F
  let X : ℝ := concreteAdditivityCrossTermOnFamilyAtDepth F Q j φ p q
  let O : ℝ := cutoffOscillationTermOnCubeAtDepth Q (F.coeffOn Q) j φ p q
  let L : ℝ := cutoffLinearPairTermOnCube Q (F.coeffOn Q) φ p q p0 q0
  let Prod : ℝ := cutoffProductTermOnCube Q (F.coeffOn Q) φ p q p0 q0
  let B : ℝ :=
    (2 * C) *
      (Real.sqrt (responseJPartitionDefectOnFamilyAtDepth F Q j p q) *
        Real.sqrt (childResponseJAverageOnFamilyAtDepth F Q j p q))
  have hsplit :
      centeredResponseJOnCube Q (F.coeffOn Q) p q p0 q0 -
          cutoffWeightedChildResponseJOnFamilyAtDepth F Q j φ p q =
        X + O + L + Prod := by
    simpa [F, X, O, L, Prod] using
      centeredResponseJOnCube_sub_cutoffWeightedChildResponseJ_eq_concreteAdditivityCross_add_cutoffOscillation_add_linearPair_add_product_of_aELocallyUniformlyEllipticField
        (a := a) (ha := ha) (Q := Q) (j := j) (φ := φ)
        (p := p) (q := q) (p0 := p0) (q0 := q0)
        hφ_int hRem_int hProduct_int hGradLinear_int hFluxLinear_int hOsc_int hMean
  have hcross : |X| ≤ B := by
    simpa [F, X, B] using
      abs_concreteAdditivityCrossTermOnDependentFamilyAtDepth_le_two_const_mul_sqrt_responseJPartitionDefect_mul_sqrt_childResponseJAverage
        (a := a) (ha := ha) (Q := Q) (j := j) (φ := φ)
        (p := p) (q := q) hC hCut
  have htri : |X + O + L + Prod| ≤ |X| + |O| + |L| + |Prod| := by
    calc
      |X + O + L + Prod| = |(X + O) + (L + Prod)| := by ring_nf
      _ ≤ |X + O| + |L + Prod| := abs_add_le _ _
      _ ≤ (|X| + |O|) + (|L| + |Prod|) := by
            exact add_le_add (abs_add_le X O) (abs_add_le L Prod)
      _ = |X| + |O| + |L| + |Prod| := by ring
  calc
    |centeredResponseJOnCube Q (F.coeffOn Q) p q p0 q0 -
        cutoffWeightedChildResponseJOnFamilyAtDepth F Q j φ p q|
        = |X + O + L + Prod| := by rw [hsplit]
    _ ≤ |X| + |O| + |L| + |Prod| := htri
    _ ≤ B + |O| + |L| + |Prod| := by nlinarith

/-- Raw Ch2 response for the Chapter 4 dependent coefficient family is the
Ch4 cube-set response observable. -/
theorem responseJOnDependentFamily_eq_restrictionResponseJObservableCubeSet
    {d : ℕ} [NeZero d] (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (p q : Vec d) :
    Ch02.responseJ (Ch02.cubeDomain Q)
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
        p q =
      Ch04.restrictionResponseJObservableCubeSet Q p q a := by
  let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  calc
    Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q) p q
        = ResponseJ (openCubeSet Q) p q a := by
            simpa [F, Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
              Ch04.coeffOnOfAEEllipticOn_toCoeffField, Ch02.cubeDomain_coe] using
              Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ
                (Ch02.cubeDomain Q) (F.coeffOn Q) p q
    _ = Ch04.restrictionResponseJObservableCubeSet Q p q a := by
          rw [← responseJ_cubeSet_eq_openCubeSet_of_triadicCube Q p q a]
          rfl

/-- At origin scales, the deterministic response partition defect for the Ch4
dependent family is the Ch4 additivity-defect observable. -/
theorem responseJPartitionDefectOnDependentFamilyAtScale_eq_responseJAdditivityDefectAtScale
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (m k : ℤ) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    responseJPartitionDefectOnFamilyAtDepth F (originCube d m) (Int.toNat (m - k)) p q =
      responseJAdditivityDefectAtScale m k p q a := by
  intro F
  unfold responseJPartitionDefectOnFamilyAtDepth childResponseJAverageOnFamilyAtDepth
    responseJAdditivityDefectAtScale
  congr 1
  · exact descendantsAverage_congr_of_eq_on_descendants
      (originCube d m) (Int.toNat (m - k)) (by
        intro R _hR
        exact responseJOnDependentFamily_eq_restrictionResponseJObservableCubeSet a ha R p q)
  · exact responseJOnDependentFamily_eq_restrictionResponseJObservableCubeSet a ha (originCube d m) p q

/-- Centered raw Ch2 response for the Chapter 4 dependent family is the Ch4
centered response observable. -/
theorem centeredResponseJOnDependentFamily_eq_restrictionCenteredResponseJObservableCubeSet
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (p q p0 q0 : Vec d) :
    centeredResponseJOnCube Q
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
        p q p0 q0 =
      Ch04.restrictionCenteredResponseJObservableCubeSet Q p q p0 q0 a := by
  simp [centeredResponseJOnCube, Ch04.restrictionCenteredResponseJObservableCubeSet,
    responseJOnDependentFamily_eq_restrictionResponseJObservableCubeSet a ha Q p q]

/-- The deterministic child-weighted raw Ch2 response average agrees with the
Ch4 response-observable average. -/
theorem cutoffWeightedChildResponseJOnDependentFamilyAtDepth_eq_ch04
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) (φ : Vec d → ℝ) (p q : Vec d) :
    cutoffWeightedChildResponseJOnFamilyAtDepth
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
        Q j φ p q =
      descendantsAverage Q j
        (fun R => cutoffChildWeight φ R * Ch04.restrictionResponseJObservableCubeSet R p q a) := by
  unfold cutoffWeightedChildResponseJOnFamilyAtDepth
  refine descendantsAverage_congr_of_eq_on_descendants Q j ?_
  intro R _hR
  rw [responseJOnDependentFamily_eq_restrictionResponseJObservableCubeSet a ha R p q]

/-- Pointwise bridge from the deterministic raw split left side to the Ch4
centered-minus-child expression used before taking expectations. -/
theorem centeredResponseJOnDependentFamily_sub_cutoffWeightedChildResponseJ_eq_ch04
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) (φ : Vec d → ℝ) (p q p0 q0 : Vec d) :
    centeredResponseJOnCube Q
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
        p q p0 q0 -
      cutoffWeightedChildResponseJOnFamilyAtDepth
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
        Q j φ p q =
      Ch04.restrictionCenteredResponseJObservableCubeSet Q p q p0 q0 a -
        descendantsAverage Q j
          (fun R => cutoffChildWeight φ R * Ch04.restrictionResponseJObservableCubeSet R p q a) := by
  rw [centeredResponseJOnDependentFamily_eq_restrictionCenteredResponseJObservableCubeSet a ha Q p q p0 q0,
    cutoffWeightedChildResponseJOnDependentFamilyAtDepth_eq_ch04 a ha Q j φ p q]

/-- Origin-scale version of the raw/Ch4 left-side bridge, matching the private
stochastic expression used above. -/
theorem centeredJMinusCutoffWeightedChildAtScale_eq_dependentFamily_left
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (m k : ℤ) (φ : Vec d → ℝ) (p q p0 q0 : Vec d) :
    centeredJMinusCutoffWeightedChildAtScale m k φ p q p0 q0 a =
      centeredResponseJOnCube (originCube d m)
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
          (originCube d m))
        p q p0 q0 -
        cutoffWeightedChildResponseJOnFamilyAtDepth
          (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
          (originCube d m) (Int.toNat (m - k)) φ p q := by
  rw [centeredResponseJOnDependentFamily_sub_cutoffWeightedChildResponseJ_eq_ch04
    a ha (originCube d m) (Int.toNat (m - k)) φ p q p0 q0]
  rfl

end

end JUpperBoundWeakNorms
end Section53
end Ch05
end Book
end Homogenization
