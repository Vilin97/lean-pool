/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Additivity.AnalyticInequalities

/-! # Cross Term -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundWeakNorms

/-!
# AdditivityCrossTerm

Averaged additivity-cross estimates.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

noncomputable section

/-- One-child additivity-cross Cauchy estimate with local obligations
discharged. -/
theorem abs_cubeAverage_childAdditivityCrossDensityOnFamilyOnCube_le_sqrt_diff_avg_mul_sqrt_sum_avg_of_descendant
    {d : ℕ} [NeZero d] (a : Ch02.TriadicCoeffFamily d)
    (Q : TriadicCube d) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    |cubeAverage R (childAdditivityCrossDensityOnFamilyOnCube a Q R p q)| ≤
      Real.sqrt
          (cubeAverage R (additivityDiffHalfEnergyDensityOnFamilyOnCube a Q R p q)) *
        Real.sqrt
          (cubeAverage R (additivitySumHalfEnergyDensityOnFamilyOnCube a Q R p q)) := by
  let F : Vec d → ℝ := childAdditivityCrossDensityOnFamilyOnCube a Q R p q
  let A : Vec d → ℝ := additivityDiffHalfEnergyDensityOnFamilyOnCube a Q R p q
  let B : Vec d → ℝ := additivitySumHalfEnergyDensityOnFamilyOnCube a Q R p q
  have hF_int : Integrable F (normalizedCubeMeasure R) :=
    integrable_normalizedCubeMeasure_of_integrableOn_cubeSet R
      (by simpa [F] using
        childAdditivityCrossDensityOnFamilyOnCube_integrableOn a Q hR p q)
  have hA_int : Integrable A (normalizedCubeMeasure R) :=
    integrable_normalizedCubeMeasure_of_integrableOn_cubeSet R
      (by simpa [A] using
        additivityDiffHalfEnergyDensityOnFamilyOnCube_integrableOn a Q hR p q)
  have hB_int : Integrable B (normalizedCubeMeasure R) :=
    integrable_normalizedCubeMeasure_of_integrableOn_cubeSet R
      (by simpa [B] using
        additivitySumHalfEnergyDensityOnFamilyOnCube_integrableOn a Q hR p q)
  have hEllOpen :
      IsAEEllipticFieldOn (a.coeffOn R).lam (a.coeffOn R).Lam
        (openCubeSet R) (a.coeffOn R).toCoeffField := by
    simpa [Ch02.cubeDomain_coe] using
      (ch02_coeffOn_isAEEllipticFieldOn (a.coeffOn R))
  have hEll :
      IsAEEllipticFieldOn (a.coeffOn R).lam (a.coeffOn R).Lam
        (cubeSet R) (a.coeffOn R).toCoeffField :=
    hEllOpen.cubeSet_of_openCubeSet
  have hEll_norm :
      ∀ᵐ x ∂ normalizedCubeMeasure R,
        IsEllipticMatrix (a.coeffOn R).lam (a.coeffOn R).Lam
          ((a.coeffOn R).toCoeffField x) := by
    change
      ∀ᵐ x ∂ ENNReal.ofReal ((cubeVolume R)⁻¹) • volume.restrict (cubeSet R),
        IsEllipticMatrix (a.coeffOn R).lam (a.coeffOn R).Lam
          ((a.coeffOn R).toCoeffField x)
    exact ae_smul_measure
      (by simpa [volumeMeasureOn] using hEll.ae_isEllipticMatrix)
      (ENNReal.ofReal ((cubeVolume R)⁻¹))
  have hA_nonneg : 0 ≤ᵐ[normalizedCubeMeasure R] A := by
    filter_upwards [hEll_norm] with x hx
    simpa [A] using
      additivityDiffHalfEnergyDensityOnFamilyOnCube_nonneg_of_isEllipticMatrix
        a Q R p q x hx
  have hB_nonneg : 0 ≤ᵐ[normalizedCubeMeasure R] B := by
    filter_upwards [hEll_norm] with x hx
    simpa [B] using
      additivitySumHalfEnergyDensityOnFamilyOnCube_nonneg_of_isEllipticMatrix
        a Q R p q x hx
  have hSqrtA_mem :
      MemLp (fun x => Real.sqrt (A x)) (2 : ℝ≥0∞)
        (normalizedCubeMeasure R) :=
    memLp_sqrt_two_of_integrable_of_ae_nonneg hA_int hA_nonneg
  have hSqrtB_mem :
      MemLp (fun x => Real.sqrt (B x)) (2 : ℝ≥0∞)
        (normalizedCubeMeasure R) :=
    memLp_sqrt_two_of_integrable_of_ae_nonneg hB_int hB_nonneg
  have hPoint :
      ∀ᵐ x ∂ normalizedCubeMeasure R,
        |F x| ≤ Real.sqrt (A x) * Real.sqrt (B x) := by
    filter_upwards [hEll_norm] with x hx
    simpa [F, A, B] using
      abs_childAdditivityCrossDensityOnFamilyOnCube_le_sqrt_diff_mul_sqrt_sum_of_isEllipticMatrix
        a Q R p q x hx
  simpa [F, A, B] using
    abs_cubeAverage_le_sqrt_cubeAverage_mul_sqrt_cubeAverage_of_ae_abs_le_sqrt_mul_sqrt
      R hF_int hA_nonneg hB_nonneg hSqrtA_mem hSqrtB_mem hPoint

/-- Child-energy replacement with the concrete additivity-cross density. -/
theorem cubeAverage_topHalfEnergyOnFamily_eq_childAdditivityCross_add_responseJOnChild
    {d : ℕ} (a : Ch02.TriadicCoeffFamily d) (Q R : TriadicCube d)
    (p q : Vec d)
    (hCoeff : (a.coeffOn Q).toCoeffField = (a.coeffOn R).toCoeffField)
    (hCross_int :
      IntegrableOn (childAdditivityCrossDensityOnFamilyOnCube a Q R p q)
        (cubeSet R) volume) :
    cubeAverage R (topHalfEnergyDensityOnCube Q (a.coeffOn Q) p q) =
      cubeAverage R (childAdditivityCrossDensityOnFamilyOnCube a Q R p q) +
        Ch02.responseJ (Ch02.cubeDomain R) (a.coeffOn R) p q := by
  let childEnergy : Vec d → ℝ :=
    topHalfEnergyDensityOnCube R (a.coeffOn R) p q
  have hChildEnergy_int :
      IntegrableOn childEnergy (cubeSet R) volume := by
    simpa [childEnergy] using
      topHalfEnergyDensityOnCube_integrableOn_cubeSet R (a.coeffOn R) p q
  have hPoint :
      topHalfEnergyDensityOnCube Q (a.coeffOn Q) p q =
        fun x => childAdditivityCrossDensityOnFamilyOnCube a Q R p q x +
          childEnergy x := by
    funext x
    have hquad :=
      half_quad_eq_additivity_cross_add_half_quad
        ((a.coeffOn R).toCoeffField x)
        (canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q x)
        (canonicalMaximizerGradientOnCube R (a.coeffOn R) p q x)
    simpa [topHalfEnergyDensityOnCube, childAdditivityCrossDensityOnFamilyOnCube,
      childEnergy, Ch02.variationEnergyIntegrand, canonicalMaximizerGradientOnCube,
      hCoeff] using hquad
  rw [hPoint]
  rw [cubeAverage_add_of_integrableOn R
    (childAdditivityCrossDensityOnFamilyOnCube a Q R p q)
    childEnergy hCross_int hChildEnergy_int]
  rw [← responseJOnCube_eq_cubeAverage_topHalfEnergy R (a.coeffOn R) p q]

/-- Averaged finite Cauchy for nonnegative scalar data. -/
theorem finset_average_sqrt_mul_sqrt_le_sqrt_average_mul_sqrt_average
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (hS : S.Nonempty)
    (A B : ι → ℝ)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i) :
    (S.card : ℝ)⁻¹ * (∑ i ∈ S, Real.sqrt (A i) * Real.sqrt (B i)) ≤
      Real.sqrt ((S.card : ℝ)⁻¹ * (∑ i ∈ S, A i)) *
        Real.sqrt ((S.card : ℝ)⁻¹ * (∑ i ∈ S, B i)) := by
  let invN : ℝ := (S.card : ℝ)⁻¹
  have hcard_pos_nat : 0 < S.card := Finset.card_pos.mpr hS
  have hcard_pos : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hcard_pos_nat
  have hinv_nonneg : 0 ≤ invN := inv_nonneg.mpr hcard_pos.le
  have hCauchy :
      (∑ i ∈ S, Real.sqrt (A i) * Real.sqrt (B i)) ≤
        Real.sqrt (∑ i ∈ S, A i) * Real.sqrt (∑ i ∈ S, B i) :=
    Real.sum_sqrt_mul_sqrt_le (s := S) (f := A) (g := B) hA hB
  have hScale :
      invN * (Real.sqrt (∑ i ∈ S, A i) * Real.sqrt (∑ i ∈ S, B i)) =
        Real.sqrt (invN * (∑ i ∈ S, A i)) *
          Real.sqrt (invN * (∑ i ∈ S, B i)) := by
    rw [Real.sqrt_mul hinv_nonneg, Real.sqrt_mul hinv_nonneg]
    rw [show
        invN * (Real.sqrt (∑ i ∈ S, A i) * Real.sqrt (∑ i ∈ S, B i)) =
          (Real.sqrt invN * Real.sqrt invN) *
            (Real.sqrt (∑ i ∈ S, A i) * Real.sqrt (∑ i ∈ S, B i)) by
        rw [← sq, Real.sq_sqrt hinv_nonneg]]
    ring
  calc
    invN * (∑ i ∈ S, Real.sqrt (A i) * Real.sqrt (B i))
        ≤ invN * (Real.sqrt (∑ i ∈ S, A i) * Real.sqrt (∑ i ∈ S, B i)) := by
          exact mul_le_mul_of_nonneg_left hCauchy hinv_nonneg
    _ =
        Real.sqrt (invN * (∑ i ∈ S, A i)) *
          Real.sqrt (invN * (∑ i ∈ S, B i)) := hScale

/-- Finite averaged Cauchy after a pointwise absolute-value estimate. -/
theorem abs_finset_average_le_const_mul_sqrt_average_mul_sqrt_average_of_abs_le
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (hS : S.Nonempty)
    {C : ℝ} (A B X : ι → ℝ)
    (hC : 0 ≤ C)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    (hX : ∀ i, |X i| ≤ C * (Real.sqrt (A i) * Real.sqrt (B i))) :
    |(S.card : ℝ)⁻¹ * (∑ i ∈ S, X i)| ≤
      C *
        (Real.sqrt ((S.card : ℝ)⁻¹ * (∑ i ∈ S, A i)) *
          Real.sqrt ((S.card : ℝ)⁻¹ * (∑ i ∈ S, B i))) := by
  let invN : ℝ := (S.card : ℝ)⁻¹
  have hcard_pos_nat : 0 < S.card := Finset.card_pos.mpr hS
  have hcard_pos : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hcard_pos_nat
  have hinv_nonneg : 0 ≤ invN := inv_nonneg.mpr hcard_pos.le
  have hAbsSum :
      |∑ i ∈ S, X i| ≤ ∑ i ∈ S, |X i| :=
    Finset.abs_sum_le_sum_abs (s := S) (f := X)
  have hTerm :
      ∑ i ∈ S, |X i| ≤
        ∑ i ∈ S, C * (Real.sqrt (A i) * Real.sqrt (B i)) :=
    Finset.sum_le_sum fun i _ => hX i
  have hAvgCauchy :=
    finset_average_sqrt_mul_sqrt_le_sqrt_average_mul_sqrt_average
      S hS A B hA hB
  calc
    |invN * (∑ i ∈ S, X i)|
        = invN * |∑ i ∈ S, X i| := by
          rw [abs_mul, abs_of_nonneg hinv_nonneg]
    _ ≤ invN * (∑ i ∈ S, |X i|) := by
          exact mul_le_mul_of_nonneg_left hAbsSum hinv_nonneg
    _ ≤ invN * (∑ i ∈ S, C * (Real.sqrt (A i) * Real.sqrt (B i))) := by
          exact mul_le_mul_of_nonneg_left hTerm hinv_nonneg
    _ = C * (invN * (∑ i ∈ S, Real.sqrt (A i) * Real.sqrt (B i))) := by
          rw [← Finset.mul_sum]
          ring
    _ ≤
        C *
          (Real.sqrt (invN * (∑ i ∈ S, A i)) *
            Real.sqrt (invN * (∑ i ∈ S, B i))) := by
          exact mul_le_mul_of_nonneg_left hAvgCauchy hC

/-- Descendant response subadditivity for the raw scalar response. -/
theorem responseJOnCube_le_childResponseJAverageOnFamilyAtDepth
    {d : ℕ} [NeZero d] (a : Ch02.TriadicCoeffFamily d)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    Ch02.responseJ (Ch02.cubeDomain Q) (a.coeffOn Q) p q ≤
      childResponseJAverageOnFamilyAtDepth a Q j p q := by
  let Pcell : Ch02.DomainPartition (Ch02.cubeDomain Q) :=
    Ch02.descendantsDomainPartition Q j
  have hcell :
      ∀ i : Pcell.Cell, Ch02.CoeffOn.RestrictsTo (a.coeffOn Q) (a.coeffOn i.1) := by
    intro i
    exact a.restrictsTo_of_subset
      (by simpa [Ch02.cubeDomain_coe] using
        openCubeSet_subset_of_mem_descendantsAtDepth i.2)
  have hsub :
      Ch02.responseJ (Ch02.cubeDomain Q) (a.coeffOn Q) p q ≤
        Pcell.weightedAverage fun i =>
          Ch02.responseJ (Pcell.cell i) (a.coeffOn i.1) p q :=
    (Ch02.responseSubadditivityAndScalingTheory
      (Ch02.cubeDomain Q) (a.coeffOn Q)).responseJ_subadditive
        Pcell (fun i : Pcell.Cell => a.coeffOn i.1) hcell p q
  let F : TriadicCube d → ℝ := fun R =>
    Ch02.responseJ (Ch02.cubeDomain R) (a.coeffOn R) p q
  calc
    Ch02.responseJ (Ch02.cubeDomain Q) (a.coeffOn Q) p q
        ≤ Pcell.weightedAverage fun i =>
          Ch02.responseJ (Pcell.cell i) (a.coeffOn i.1) p q := hsub
    _ = descendantsAverage Q j F := by
          simpa [Pcell, F] using!
            Ch02.descendantsDomainPartition_weightedAverage Q j F
    _ = childResponseJAverageOnFamilyAtDepth a Q j p q := by
          rfl

/-- Child-response averages are nonnegative. -/
theorem childResponseJAverageOnFamilyAtDepth_nonneg
    {d : ℕ} (a : Ch02.TriadicCoeffFamily d) (Q : TriadicCube d)
    (j : ℕ) (p q : Vec d) :
    0 ≤ childResponseJAverageOnFamilyAtDepth a Q j p q := by
  simpa [childResponseJAverageOnFamilyAtDepth] using
    descendantsAverage_nonneg Q j
      (fun R => Ch02.responseJ (Ch02.cubeDomain R) (a.coeffOn R) p q)
      (fun R _hR => Ch02.responseJ_nonneg (Ch02.cubeDomain R) (a.coeffOn R) p q)

/-- The cube average of the difference half-energy density is nonnegative. -/
theorem cubeAverage_additivityDiffHalfEnergyDensityOnFamilyOnCube_nonneg
    {d : ℕ} (a : Ch02.TriadicCoeffFamily d) (Q R : TriadicCube d)
    (p q : Vec d) :
    0 ≤ cubeAverage R (additivityDiffHalfEnergyDensityOnFamilyOnCube a Q R p q) := by
  have hEllOpen :
      IsAEEllipticFieldOn (a.coeffOn R).lam (a.coeffOn R).Lam
        (openCubeSet R) (a.coeffOn R).toCoeffField := by
    simpa [Ch02.cubeDomain_coe] using
      (ch02_coeffOn_isAEEllipticFieldOn (a.coeffOn R))
  have hEll :
      IsAEEllipticFieldOn (a.coeffOn R).lam (a.coeffOn R).Lam
        (cubeSet R) (a.coeffOn R).toCoeffField :=
    hEllOpen.cubeSet_of_openCubeSet
  have hEll_norm :
      ∀ᵐ x ∂ normalizedCubeMeasure R,
        IsEllipticMatrix (a.coeffOn R).lam (a.coeffOn R).Lam
          ((a.coeffOn R).toCoeffField x) := by
    change
      ∀ᵐ x ∂ ENNReal.ofReal ((cubeVolume R)⁻¹) • volume.restrict (cubeSet R),
        IsEllipticMatrix (a.coeffOn R).lam (a.coeffOn R).Lam
          ((a.coeffOn R).toCoeffField x)
    exact ae_smul_measure
      (by simpa [volumeMeasureOn] using hEll.ae_isEllipticMatrix)
      (ENNReal.ofReal ((cubeVolume R)⁻¹))
  have hNonneg :
      0 ≤ᵐ[normalizedCubeMeasure R]
        additivityDiffHalfEnergyDensityOnFamilyOnCube a Q R p q := by
    filter_upwards [hEll_norm] with x hx
    exact additivityDiffHalfEnergyDensityOnFamilyOnCube_nonneg_of_isEllipticMatrix
      a Q R p q x hx
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  exact integral_nonneg_of_ae hNonneg

/-- The cube average of the sum half-energy density is nonnegative. -/
theorem cubeAverage_additivitySumHalfEnergyDensityOnFamilyOnCube_nonneg
    {d : ℕ} (a : Ch02.TriadicCoeffFamily d) (Q R : TriadicCube d)
    (p q : Vec d) :
    0 ≤ cubeAverage R (additivitySumHalfEnergyDensityOnFamilyOnCube a Q R p q) := by
  have hEllOpen :
      IsAEEllipticFieldOn (a.coeffOn R).lam (a.coeffOn R).Lam
        (openCubeSet R) (a.coeffOn R).toCoeffField := by
    simpa [Ch02.cubeDomain_coe] using
      (ch02_coeffOn_isAEEllipticFieldOn (a.coeffOn R))
  have hEll :
      IsAEEllipticFieldOn (a.coeffOn R).lam (a.coeffOn R).Lam
        (cubeSet R) (a.coeffOn R).toCoeffField :=
    hEllOpen.cubeSet_of_openCubeSet
  have hEll_norm :
      ∀ᵐ x ∂ normalizedCubeMeasure R,
        IsEllipticMatrix (a.coeffOn R).lam (a.coeffOn R).Lam
          ((a.coeffOn R).toCoeffField x) := by
    change
      ∀ᵐ x ∂ ENNReal.ofReal ((cubeVolume R)⁻¹) • volume.restrict (cubeSet R),
        IsEllipticMatrix (a.coeffOn R).lam (a.coeffOn R).Lam
          ((a.coeffOn R).toCoeffField x)
    exact ae_smul_measure
      (by simpa [volumeMeasureOn] using hEll.ae_isEllipticMatrix)
      (ENNReal.ofReal ((cubeVolume R)⁻¹))
  have hNonneg :
      0 ≤ᵐ[normalizedCubeMeasure R]
        additivitySumHalfEnergyDensityOnFamilyOnCube a Q R p q := by
    filter_upwards [hEll_norm] with x hx
    exact additivitySumHalfEnergyDensityOnFamilyOnCube_nonneg_of_isEllipticMatrix
      a Q R p q x hx
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  exact integral_nonneg_of_ae hNonneg

/-- Pointwise comparison of the additivity sum energy with parent and child
half-energies on one child cube. -/
theorem additivitySumHalfEnergyDensityOnFamilyOnCube_le_two_topHalfEnergy_add_two_childHalfEnergy
    {d : ℕ} {lam Lam : ℝ} (a : Ch02.TriadicCoeffFamily d)
    (Q R : TriadicCube d) (p q : Vec d) (x : Vec d)
    (hEll : IsEllipticMatrix lam Lam ((a.coeffOn R).toCoeffField x))
    (hCoeff : (a.coeffOn Q).toCoeffField = (a.coeffOn R).toCoeffField) :
    additivitySumHalfEnergyDensityOnFamilyOnCube a Q R p q x ≤
      2 * topHalfEnergyDensityOnCube Q (a.coeffOn Q) p q x +
        2 * topHalfEnergyDensityOnCube R (a.coeffOn R) p q x := by
  let topGrad : Vec d := canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q x
  let childGrad : Vec d := canonicalMaximizerGradientOnCube R (a.coeffOn R) p q x
  let A : Mat d := (a.coeffOn R).toCoeffField x
  have hsum :=
    vecDot_matVecMul_symmPart_sub_le_two_mul_add_of_isEllipticMatrix
      (A := A) hEll topGrad (-childGrad)
  have hsum_add :
      vecDot (topGrad + childGrad) (matVecMul (symmPart A) (topGrad + childGrad)) ≤
        2 * (vecDot topGrad (matVecMul (symmPart A) topGrad) +
          vecDot childGrad (matVecMul (symmPart A) childGrad)) := by
    simpa [sub_neg_eq_add, matVecMul_neg, vecDot_neg_left, vecDot_neg_right]
      using hsum
  have hgoal :
      (1 / 2 : ℝ) *
          vecDot (topGrad + childGrad)
            (matVecMul (symmPart A) (topGrad + childGrad)) ≤
        vecDot topGrad (matVecMul (symmPart A) topGrad) +
          vecDot childGrad (matVecMul (symmPart A) childGrad) := by
    nlinarith
  simpa [additivitySumHalfEnergyDensityOnFamilyOnCube, topHalfEnergyDensityOnCube,
    Ch02.variationEnergyIntegrand, canonicalMaximizerGradientOnCube,
    topGrad, childGrad, A, hCoeff] using hgoal

/-- One-cube averaged comparison of sum energy with parent top energy plus
child response. -/
theorem cubeAverage_additivitySumHalfEnergyDensityOnFamilyOnCube_le_two_topHalfEnergy_add_two_childResponse
    {d : ℕ} [NeZero d] (a : Ch02.TriadicCoeffFamily d)
    (Q : TriadicCube d) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d)
    (hCoeff : (a.coeffOn Q).toCoeffField = (a.coeffOn R).toCoeffField) :
    cubeAverage R (additivitySumHalfEnergyDensityOnFamilyOnCube a Q R p q) ≤
      2 * cubeAverage R (topHalfEnergyDensityOnCube Q (a.coeffOn Q) p q) +
        2 * Ch02.responseJ (Ch02.cubeDomain R) (a.coeffOn R) p q := by
  let topF : Vec d → ℝ := topHalfEnergyDensityOnCube Q (a.coeffOn Q) p q
  let childF : Vec d → ℝ := topHalfEnergyDensityOnCube R (a.coeffOn R) p q
  let sumF : Vec d → ℝ := additivitySumHalfEnergyDensityOnFamilyOnCube a Q R p q
  have hsubset : cubeSet R ⊆ cubeSet Q :=
    cubeSet_subset_of_mem_descendantsAtDepth hR
  have hTop_int : IntegrableOn topF (cubeSet R) volume :=
    (topHalfEnergyDensityOnCube_integrableOn_cubeSet Q (a.coeffOn Q) p q).mono_set hsubset
  have hChild_int : IntegrableOn childF (cubeSet R) volume := by
    simpa [childF] using topHalfEnergyDensityOnCube_integrableOn_cubeSet R (a.coeffOn R) p q
  have hSum_int : IntegrableOn sumF (cubeSet R) volume := by
    simpa [sumF] using additivitySumHalfEnergyDensityOnFamilyOnCube_integrableOn
      a Q hR p q
  let μ : Measure (Vec d) := normalizedCubeMeasure R
  have hTop_norm : Integrable topF μ :=
    integrable_normalizedCubeMeasure_of_integrableOn_cubeSet R hTop_int
  have hChild_norm : Integrable childF μ :=
    integrable_normalizedCubeMeasure_of_integrableOn_cubeSet R hChild_int
  have hSum_norm : Integrable sumF μ :=
    integrable_normalizedCubeMeasure_of_integrableOn_cubeSet R hSum_int
  have hRhs_norm :
      Integrable (fun x => 2 * topF x + 2 * childF x) μ :=
    (hTop_norm.const_mul 2).add (hChild_norm.const_mul 2)
  have hEllOpen :
      IsAEEllipticFieldOn (a.coeffOn R).lam (a.coeffOn R).Lam
        (openCubeSet R) (a.coeffOn R).toCoeffField := by
    simpa [Ch02.cubeDomain_coe] using
      (ch02_coeffOn_isAEEllipticFieldOn (a.coeffOn R))
  have hEll :
      IsAEEllipticFieldOn (a.coeffOn R).lam (a.coeffOn R).Lam
        (cubeSet R) (a.coeffOn R).toCoeffField :=
    hEllOpen.cubeSet_of_openCubeSet
  have hEll_norm :
      ∀ᵐ x ∂ μ,
        IsEllipticMatrix (a.coeffOn R).lam (a.coeffOn R).Lam
          ((a.coeffOn R).toCoeffField x) := by
    change
      ∀ᵐ x ∂ ENNReal.ofReal ((cubeVolume R)⁻¹) • volume.restrict (cubeSet R),
        IsEllipticMatrix (a.coeffOn R).lam (a.coeffOn R).Lam
          ((a.coeffOn R).toCoeffField x)
    exact ae_smul_measure
      (by simpa [volumeMeasureOn] using hEll.ae_isEllipticMatrix)
      (ENNReal.ofReal ((cubeVolume R)⁻¹))
  have hpoint : sumF ≤ᵐ[μ] fun x => 2 * topF x + 2 * childF x := by
    filter_upwards [hEll_norm] with x hx
    simpa [sumF, topF, childF] using
      additivitySumHalfEnergyDensityOnFamilyOnCube_le_two_topHalfEnergy_add_two_childHalfEnergy
        a Q R p q x hx hCoeff
  have hInt_le :
      ∫ x, sumF x ∂μ ≤ ∫ x, (2 * topF x + 2 * childF x) ∂μ :=
    integral_mono_ae hSum_norm hRhs_norm hpoint
  calc
    cubeAverage R sumF = ∫ x, sumF x ∂μ := by
      rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    _ ≤ ∫ x, (2 * topF x + 2 * childF x) ∂μ := hInt_le
    _ = 2 * cubeAverage R topF + 2 * cubeAverage R childF := by
      rw [integral_add (hTop_norm.const_mul 2) (hChild_norm.const_mul 2)]
      rw [integral_const_mul, integral_const_mul]
      rw [cubeAverage_eq_integral_normalizedCubeMeasure,
        cubeAverage_eq_integral_normalizedCubeMeasure]
    _ = 2 * cubeAverage R (topHalfEnergyDensityOnCube Q (a.coeffOn Q) p q) +
          2 * Ch02.responseJ (Ch02.cubeDomain R) (a.coeffOn R) p q := by
      rw [← responseJOnCube_eq_cubeAverage_topHalfEnergy R (a.coeffOn R) p q]

/-- The descendant average of parent top half-energy over children is the
parent response. -/
theorem descendantsAverage_cubeAverage_topHalfEnergyOnCube_eq_responseJOnCube
    {d : ℕ} (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (j : ℕ) (p q : Vec d) :
    descendantsAverage Q j
        (fun R => cubeAverage R (topHalfEnergyDensityOnCube Q a p q)) =
      Ch02.responseJ (Ch02.cubeDomain Q) a p q := by
  let F : Vec d → ℝ := topHalfEnergyDensityOnCube Q a p q
  have hTop_int : IntegrableOn F (cubeSet Q) volume := by
    simpa [F] using topHalfEnergyDensityOnCube_integrableOn_cubeSet Q a p q
  calc
    descendantsAverage Q j (fun R => cubeAverage R F)
        = cubeAverage Q F := by
          rw [← cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
            (Q := Q) (j := j) (f := F) hTop_int]
    _ = Ch02.responseJ (Ch02.cubeDomain Q) a p q := by
          rw [← responseJOnCube_eq_cubeAverage_topHalfEnergy Q a p q]

/-- The descendant-averaged sum-energy factor is controlled by twice the parent
response plus twice the child-response average. -/
theorem descendantsAverage_additivitySumHalfEnergyOnDependentFamily_le_two_responseJ_add_two_childResponse
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    descendantsAverage Q j
        (fun R =>
          cubeAverage R (additivitySumHalfEnergyDensityOnFamilyOnCube F Q R p q)) ≤
      2 * Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q) p q +
        2 * childResponseJAverageOnFamilyAtDepth F Q j p q := by
  intro F
  classical
  let S : Finset (TriadicCube d) := descendantsAtDepth Q j
  have hS_nonempty : S.Nonempty := by
    simpa [S] using descendantsAtDepth_nonempty Q j
  have hinv_nonneg : 0 ≤ ((S.card : ℝ)⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg S.card)
  have hterm :
      ∀ R ∈ S,
        cubeAverage R (additivitySumHalfEnergyDensityOnFamilyOnCube F Q R p q) ≤
          2 * cubeAverage R (topHalfEnergyDensityOnCube Q (F.coeffOn Q) p q) +
            2 * Ch02.responseJ (Ch02.cubeDomain R) (F.coeffOn R) p q := by
    intro R hR
    exact
      cubeAverage_additivitySumHalfEnergyDensityOnFamilyOnCube_le_two_topHalfEnergy_add_two_childResponse
        F Q (by simpa [S] using hR) p q (by rfl)
  have hsum :
      ∑ R ∈ S,
        cubeAverage R (additivitySumHalfEnergyDensityOnFamilyOnCube F Q R p q) ≤
      ∑ R ∈ S,
        (2 * cubeAverage R (topHalfEnergyDensityOnCube Q (F.coeffOn Q) p q) +
          2 * Ch02.responseJ (Ch02.cubeDomain R) (F.coeffOn R) p q) :=
    Finset.sum_le_sum hterm
  have havg :
      descendantsAverage Q j
          (fun R => cubeAverage R
            (additivitySumHalfEnergyDensityOnFamilyOnCube F Q R p q)) ≤
        descendantsAverage Q j
          (fun R =>
            2 * cubeAverage R (topHalfEnergyDensityOnCube Q (F.coeffOn Q) p q) +
              2 * Ch02.responseJ (Ch02.cubeDomain R) (F.coeffOn R) p q) := by
    simpa [descendantsAverage, S] using
      mul_le_mul_of_nonneg_left hsum hinv_nonneg
  calc
    descendantsAverage Q j
        (fun R => cubeAverage R
          (additivitySumHalfEnergyDensityOnFamilyOnCube F Q R p q))
        ≤
          descendantsAverage Q j
            (fun R =>
              2 * cubeAverage R (topHalfEnergyDensityOnCube Q (F.coeffOn Q) p q) +
                2 * Ch02.responseJ (Ch02.cubeDomain R) (F.coeffOn R) p q) := havg
    _ =
          2 * descendantsAverage Q j
            (fun R => cubeAverage R (topHalfEnergyDensityOnCube Q (F.coeffOn Q) p q)) +
          2 * childResponseJAverageOnFamilyAtDepth F Q j p q := by
          rw [descendantsAverage_add]
          rw [descendantsAverage_smul, descendantsAverage_smul]
          rfl
    _ =
        2 * Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q) p q +
          2 * childResponseJAverageOnFamilyAtDepth F Q j p q := by
          rw [descendantsAverage_cubeAverage_topHalfEnergyOnCube_eq_responseJOnCube]

/-- The descendant-averaged sum-energy factor is bounded by four times the
child-response average. -/
theorem descendantsAverage_additivitySumHalfEnergyOnDependentFamily_le_four_childResponse
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    descendantsAverage Q j
        (fun R =>
          cubeAverage R (additivitySumHalfEnergyDensityOnFamilyOnCube F Q R p q)) ≤
      4 * childResponseJAverageOnFamilyAtDepth F Q j p q := by
  intro F
  have hsum :=
    descendantsAverage_additivitySumHalfEnergyOnDependentFamily_le_two_responseJ_add_two_childResponse
      a ha Q j p q
  have hparent_le_child :
      Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q) p q ≤
        childResponseJAverageOnFamilyAtDepth F Q j p q :=
    responseJOnCube_le_childResponseJAverageOnFamilyAtDepth F Q j p q
  calc
    descendantsAverage Q j
        (fun R => cubeAverage R
          (additivitySumHalfEnergyDensityOnFamilyOnCube F Q R p q))
        ≤
          2 * Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q) p q +
            2 * childResponseJAverageOnFamilyAtDepth F Q j p q := by
          simpa [F] using hsum
    _ ≤
          2 * childResponseJAverageOnFamilyAtDepth F Q j p q +
            2 * childResponseJAverageOnFamilyAtDepth F Q j p q := by
          nlinarith [hparent_le_child]
    _ = 4 * childResponseJAverageOnFamilyAtDepth F Q j p q := by
          ring

/-- Square-root form of a `4`-multiple upper bound. -/
theorem sqrt_le_two_mul_sqrt_of_le_four_mul {x y : ℝ}
    (hxy : x ≤ 4 * y) :
    Real.sqrt x ≤ 2 * Real.sqrt y := by
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num : 0 ≤ (4 : ℝ))
      (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num
  calc
    Real.sqrt x ≤ Real.sqrt (4 * y) := Real.sqrt_le_sqrt hxy
    _ = Real.sqrt (4 : ℝ) * Real.sqrt y := by
          rw [Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ)) y]
    _ = 2 * Real.sqrt y := by
          rw [hsqrt4]

/-- One-child additivity-cross estimate with the cutoff mean factor included. -/
theorem abs_one_sub_cubeAverage_mul_cubeAverage_childAdditivityCrossDensityOnFamilyOnCube_le_const_mul_sqrt_diff_avg_mul_sqrt_sum_avg
    {d : ℕ} [NeZero d] (a : Ch02.TriadicCoeffFamily d)
    (Q : TriadicCube d) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (φ : Vec d → ℝ)
    (p q : Vec d) {C : ℝ}
    (hCut : |1 - cubeAverage R φ| ≤ C) :
    |(1 - cubeAverage R φ) *
        cubeAverage R (childAdditivityCrossDensityOnFamilyOnCube a Q R p q)| ≤
      C *
        (Real.sqrt
            (cubeAverage R (additivityDiffHalfEnergyDensityOnFamilyOnCube a Q R p q)) *
          Real.sqrt
            (cubeAverage R (additivitySumHalfEnergyDensityOnFamilyOnCube a Q R p q))) := by
  have hC_nonneg : 0 ≤ C :=
    (abs_nonneg (1 - cubeAverage R φ)).trans hCut
  have hCross :=
    abs_cubeAverage_childAdditivityCrossDensityOnFamilyOnCube_le_sqrt_diff_avg_mul_sqrt_sum_avg_of_descendant
      (a := a) (Q := Q) (R := R) hR p q
  calc
    |(1 - cubeAverage R φ) *
        cubeAverage R (childAdditivityCrossDensityOnFamilyOnCube a Q R p q)|
        =
          |1 - cubeAverage R φ| *
            |cubeAverage R (childAdditivityCrossDensityOnFamilyOnCube a Q R p q)| := by
            rw [abs_mul]
    _ ≤
        C *
          (Real.sqrt
              (cubeAverage R (additivityDiffHalfEnergyDensityOnFamilyOnCube a Q R p q)) *
            Real.sqrt
              (cubeAverage R (additivitySumHalfEnergyDensityOnFamilyOnCube a Q R p q))) := by
          exact
            mul_le_mul hCut hCross
              (abs_nonneg
                (cubeAverage R (childAdditivityCrossDensityOnFamilyOnCube a Q R p q)))
              hC_nonneg

/-- Descendant-averaged additivity-cross term after the one-cube Cauchy step. -/
theorem abs_concreteAdditivityCrossTermOnFamilyAtDepth_le_const_mul_sqrt_descAvg_diffEnergy_mul_sqrt_descAvg_sumEnergy
    {d : ℕ} [NeZero d] (a : Ch02.TriadicCoeffFamily d)
    (Q : TriadicCube d) (j : ℕ) (φ : Vec d → ℝ) (p q : Vec d)
    {C : ℝ}
    (hC : 0 ≤ C)
    (hCut : ∀ R ∈ descendantsAtDepth Q j, |1 - cubeAverage R φ| ≤ C) :
    |concreteAdditivityCrossTermOnFamilyAtDepth a Q j φ p q| ≤
      C *
        (Real.sqrt
            (descendantsAverage Q j fun R =>
              cubeAverage R (additivityDiffHalfEnergyDensityOnFamilyOnCube a Q R p q)) *
          Real.sqrt
            (descendantsAverage Q j fun R =>
              cubeAverage R (additivitySumHalfEnergyDensityOnFamilyOnCube a Q R p q))) := by
  let A : TriadicCube d → ℝ := fun R =>
    cubeAverage R (additivityDiffHalfEnergyDensityOnFamilyOnCube a Q R p q)
  let B : TriadicCube d → ℝ := fun R =>
    cubeAverage R (additivitySumHalfEnergyDensityOnFamilyOnCube a Q R p q)
  let X : TriadicCube d → ℝ := fun R =>
    if R ∈ descendantsAtDepth Q j then
      (1 - cubeAverage R φ) *
        cubeAverage R (childAdditivityCrossDensityOnFamilyOnCube a Q R p q)
    else
      0
  have hCauchy :=
    abs_finset_average_le_const_mul_sqrt_average_mul_sqrt_average_of_abs_le
      (S := descendantsAtDepth Q j)
      (hS := descendantsAtDepth_nonempty Q j)
      (C := C) (A := A) (B := B) (X := X)
      hC
      (fun R => cubeAverage_additivityDiffHalfEnergyDensityOnFamilyOnCube_nonneg a Q R p q)
      (fun R => cubeAverage_additivitySumHalfEnergyDensityOnFamilyOnCube_nonneg a Q R p q)
      (by
        intro R
        by_cases hR : R ∈ descendantsAtDepth Q j
        · simpa [X, A, B, hR] using
            abs_one_sub_cubeAverage_mul_cubeAverage_childAdditivityCrossDensityOnFamilyOnCube_le_const_mul_sqrt_diff_avg_mul_sqrt_sum_avg
              (a := a) (Q := Q) (R := R) hR φ p q (hCut R hR)
        · have hRight_nonneg :
              0 ≤ C * (Real.sqrt (A R) * Real.sqrt (B R)) :=
            mul_nonneg hC (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
          simpa [X, hR] using hRight_nonneg)
  simpa [concreteAdditivityCrossTermOnFamilyAtDepth, additivityCrossTermOnCubeAtDepth,
    descendantsAverage, X, A, B] using hCauchy

/-- Deterministic additivity-cross bound for the Chapter 4 dependent family,
with the second energy factor reduced to child responses. -/
theorem abs_concreteAdditivityCrossTermOnDependentFamilyAtDepth_le_two_const_mul_sqrt_descAvg_diffEnergy_mul_sqrt_childResponseJAverage
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) (φ : Vec d → ℝ) (p q : Vec d)
    {C : ℝ}
    (hC : 0 ≤ C)
    (hCut : ∀ R ∈ descendantsAtDepth Q j, |1 - cubeAverage R φ| ≤ C) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    |concreteAdditivityCrossTermOnFamilyAtDepth F Q j φ p q| ≤
      (2 * C) *
        (Real.sqrt
            (descendantsAverage Q j fun R =>
              cubeAverage R (additivityDiffHalfEnergyDensityOnFamilyOnCube F Q R p q)) *
          Real.sqrt (childResponseJAverageOnFamilyAtDepth F Q j p q)) := by
  intro F
  let diffAvg : ℝ :=
    descendantsAverage Q j fun R =>
      cubeAverage R (additivityDiffHalfEnergyDensityOnFamilyOnCube F Q R p q)
  let sumAvg : ℝ :=
    descendantsAverage Q j fun R =>
      cubeAverage R (additivitySumHalfEnergyDensityOnFamilyOnCube F Q R p q)
  let childAvg : ℝ := childResponseJAverageOnFamilyAtDepth F Q j p q
  have hbase :
      |concreteAdditivityCrossTermOnFamilyAtDepth F Q j φ p q| ≤
        C * (Real.sqrt diffAvg * Real.sqrt sumAvg) := by
    simpa [diffAvg, sumAvg, F] using
      abs_concreteAdditivityCrossTermOnFamilyAtDepth_le_const_mul_sqrt_descAvg_diffEnergy_mul_sqrt_descAvg_sumEnergy
        (a := F) (Q := Q) (j := j) (φ := φ) (p := p) (q := q)
        hC hCut
  have hsum_le : sumAvg ≤ 4 * childAvg := by
    simpa [sumAvg, childAvg, F] using
      descendantsAverage_additivitySumHalfEnergyOnDependentFamily_le_four_childResponse
        a ha Q j p q
  have hsqrt_sum_le : Real.sqrt sumAvg ≤ 2 * Real.sqrt childAvg :=
    sqrt_le_two_mul_sqrt_of_le_four_mul hsum_le
  have hmul_sqrt :
      Real.sqrt diffAvg * Real.sqrt sumAvg ≤
        Real.sqrt diffAvg * (2 * Real.sqrt childAvg) :=
    mul_le_mul_of_nonneg_left hsqrt_sum_le (Real.sqrt_nonneg diffAvg)
  have hmul_C :
      C * (Real.sqrt diffAvg * Real.sqrt sumAvg) ≤
        C * (Real.sqrt diffAvg * (2 * Real.sqrt childAvg)) :=
    mul_le_mul_of_nonneg_left hmul_sqrt hC
  calc
    |concreteAdditivityCrossTermOnFamilyAtDepth F Q j φ p q|
        ≤ C * (Real.sqrt diffAvg * Real.sqrt sumAvg) := hbase
    _ ≤ C * (Real.sqrt diffAvg * (2 * Real.sqrt childAvg)) := hmul_C
    _ = (2 * C) * (Real.sqrt diffAvg * Real.sqrt childAvg) := by
          ring

/-- Deterministic additivity-cross bound in the manuscript form, with the
difference-energy factor identified as the response partition defect. -/
theorem abs_concreteAdditivityCrossTermOnDependentFamilyAtDepth_le_two_const_mul_sqrt_responseJPartitionDefect_mul_sqrt_childResponseJAverage
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) (φ : Vec d → ℝ) (p q : Vec d)
    {C : ℝ}
    (hC : 0 ≤ C)
    (hCut : ∀ R ∈ descendantsAtDepth Q j, |1 - cubeAverage R φ| ≤ C) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    |concreteAdditivityCrossTermOnFamilyAtDepth F Q j φ p q| ≤
      (2 * C) *
        (Real.sqrt (responseJPartitionDefectOnFamilyAtDepth F Q j p q) *
          Real.sqrt (childResponseJAverageOnFamilyAtDepth F Q j p q)) := by
  intro F
  have hbase :=
    abs_concreteAdditivityCrossTermOnDependentFamilyAtDepth_le_two_const_mul_sqrt_descAvg_diffEnergy_mul_sqrt_childResponseJAverage
      (a := a) (ha := ha) (Q := Q) (j := j) (φ := φ) (p := p) (q := q)
      hC hCut
  have hdefect :=
    descendantsAverage_additivityDiffHalfEnergyOnDependentFamily_eq_responseJPartitionDefectOnFamilyAtDepth
      a ha Q j p q
  simpa [F, hdefect] using hbase

end

end JUpperBoundWeakNorms
end Section53
end Ch05
end Book
end Homogenization
