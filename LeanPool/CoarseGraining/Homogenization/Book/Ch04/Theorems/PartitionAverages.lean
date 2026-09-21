/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.Concentration

/-! # Partition Averages -/

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Public partition-average concentration tools

This file contains proved, coefficient-free probability tools for the
finite-coloring step in Proposition
`p.local.partition.average.fluctuations.stationary.random.fields`.  The
locality and stationarity bridges remain separate; the aggregation of
independent color-class estimates is already a theorem.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {Ω κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

private theorem inv_mul_const_sum_sqrt_scale_le
    [DecidableEq κ] (colors : Finset κ) {A C K colorCount totalCount : ℝ}
    {classCount : κ → ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hK : 0 ≤ K) (hTotal : 0 < totalCount)
    (hSqrt :
      ∑ c ∈ colors, Real.sqrt (classCount c) ≤
        Real.sqrt colorCount * Real.sqrt totalCount) :
    totalCount⁻¹ * (A * ∑ c ∈ colors, C * Real.sqrt (classCount c) * K) ≤
      A * C * (Real.sqrt colorCount * (Real.sqrt totalCount / totalCount)) * K := by
  have hCK_nonneg : 0 ≤ C * K := mul_nonneg hC hK
  have hsum_eq :
      (∑ c ∈ colors, C * Real.sqrt (classCount c) * K) =
        (C * K) * ∑ c ∈ colors, Real.sqrt (classCount c) := by
    calc
      (∑ c ∈ colors, C * Real.sqrt (classCount c) * K)
          = ∑ c ∈ colors, (C * K) * Real.sqrt (classCount c) := by
              refine Finset.sum_congr rfl ?_
              intro c hc
              ring
      _ = (C * K) * ∑ c ∈ colors, Real.sqrt (classCount c) := by
              rw [Finset.mul_sum]
  have hsum_le :
      (∑ c ∈ colors, C * Real.sqrt (classCount c) * K) ≤
        (C * K) * (Real.sqrt colorCount * Real.sqrt totalCount) := by
    rw [hsum_eq]
    exact mul_le_mul_of_nonneg_left hSqrt hCK_nonneg
  calc
    totalCount⁻¹ * (A * ∑ c ∈ colors, C * Real.sqrt (classCount c) * K)
        = (totalCount⁻¹ * A) * ∑ c ∈ colors, C * Real.sqrt (classCount c) * K := by
            ring
    _ ≤ (totalCount⁻¹ * A) *
          ((C * K) * (Real.sqrt colorCount * Real.sqrt totalCount)) := by
            exact mul_le_mul_of_nonneg_left hsum_le
              (mul_nonneg (inv_nonneg.mpr hTotal.le) hA)
    _ = A * C * (Real.sqrt colorCount * (Real.sqrt totalCount / totalCount)) * K := by
            rw [div_eq_mul_inv]
            ring

/-- Aggregating `Gamma_sigma` color-class sum estimates and then dividing by
the total cardinality gives the partition-average square-root scale. -/
theorem isBigO_finsetAverage_colorClassSums_gammaSigma
    [DecidableEq κ] [IsFiniteMeasure μ]
    (colors : Finset κ) {Y : κ → Ω → ℝ}
    {classCount : κ → ℝ} {colorCount totalCount C K σ : ℝ}
    (hσ : 0 < σ) (hcolors : colors.Nonempty)
    (hClassCount : ∀ c ∈ colors, 0 < classCount c)
    (hTotal : 0 < totalCount)
    (hC : 0 < C) (hK : 0 < K)
    (hY :
      ∀ c ∈ colors,
        IsBigO μ (gammaSigma σ) (Y c)
          (C * Real.sqrt (classCount c) * K))
    (hYmeas : ∀ c ∈ colors, Measurable (Y c))
    (hSqrt :
      ∑ c ∈ colors, Real.sqrt (classCount c) ≤
        Real.sqrt colorCount * Real.sqrt totalCount) :
    IsBigO μ (gammaSigma σ)
      (fun ω => totalCount⁻¹ * ∑ c ∈ colors, Y c ω)
      (gammaTriangleConst σ * C *
        (Real.sqrt colorCount * (Real.sqrt totalCount / totalCount)) * K) := by
  let a : κ → ℝ := fun c => C * Real.sqrt (classCount c) * K
  have ha : ∀ c ∈ colors, 0 < a c := by
    intro c hc
    exact mul_pos (mul_pos hC (Real.sqrt_pos.2 (hClassCount c hc))) hK
  have hsum :
      IsBigO μ (gammaSigma σ) (fun ω => ∑ c ∈ colors, Y c ω)
        (gammaTriangleConst σ * ∑ c ∈ colors, a c) := by
    exact isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := μ) (s := colors) (X := Y) (a := a) (σ := σ)
      hσ hcolors ha (by simpa [a] using hY) hYmeas
  have hscaled :
      IsBigO μ (gammaSigma σ)
        (fun ω => totalCount⁻¹ * ∑ c ∈ colors, Y c ω)
        (totalCount⁻¹ * (gammaTriangleConst σ * ∑ c ∈ colors, a c)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      IndependentSums.IsBigO.const_mul (μ := μ) (Ψ := gammaSigma σ)
        (X := fun ω => ∑ c ∈ colors, Y c ω)
        (A := gammaTriangleConst σ * ∑ c ∈ colors, a c)
        (c := totalCount⁻¹) (inv_nonneg.mpr hTotal.le) hsum
  refine IndependentSums.IsBigO.mono_scale (μ := μ) (Ψ := gammaSigma σ)
    (X := fun ω => totalCount⁻¹ * ∑ c ∈ colors, Y c ω)
    (A := totalCount⁻¹ * (gammaTriangleConst σ * ∑ c ∈ colors, a c))
    (B := gammaTriangleConst σ * C *
      (Real.sqrt colorCount * (Real.sqrt totalCount / totalCount)) * K)
    hscaled ?_
  have hGamma_nonneg : 0 ≤ gammaTriangleConst σ := by
    have hGrowth_nonneg : 0 ≤ IndependentSums.gammaGrowthConst σ :=
      le_trans zero_le_two (IndependentSums.two_le_gammaGrowthConst σ)
    dsimp [gammaTriangleConst, IndependentSums.gammaTriangleConst]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg hGrowth_nonneg _)
  simpa [a, mul_assoc, mul_left_comm, mul_comm] using
    inv_mul_const_sum_sqrt_scale_le (colors := colors)
      (A := gammaTriangleConst σ) (C := C) (K := K)
      (colorCount := colorCount) (totalCount := totalCount)
      (classCount := classCount) hGamma_nonneg hC.le hK.le hTotal hSqrt

/-- Aggregating `Psi_sigma` color-class sum estimates and then dividing by the
total cardinality gives the partition-average square-root scale. -/
theorem isBigO_finsetAverage_colorClassSums_psiSigma
    [DecidableEq κ] [IsFiniteMeasure μ]
    (colors : Finset κ) {Y : κ → Ω → ℝ}
    {classCount : κ → ℝ} {colorCount totalCount C K σ : ℝ}
    (hσ : 1 ≤ σ) (hcolors : colors.Nonempty)
    (hClassCount : ∀ c ∈ colors, 0 < classCount c)
    (hTotal : 0 < totalCount)
    (hC : 0 < C) (hK : 0 < K)
    (hY :
      ∀ c ∈ colors,
        IsBigO μ (psiSigma σ) (Y c)
          (C * Real.sqrt (classCount c) * K))
    (hYmeas : ∀ c ∈ colors, Measurable (Y c))
    (hSqrt :
      ∑ c ∈ colors, Real.sqrt (classCount c) ≤
        Real.sqrt colorCount * Real.sqrt totalCount) :
    IsBigO μ (psiSigma σ)
      (fun ω => totalCount⁻¹ * ∑ c ∈ colors, Y c ω)
      (psiSigmaTriangleConst σ * C *
        (Real.sqrt colorCount * (Real.sqrt totalCount / totalCount)) * K) := by
  let a : κ → ℝ := fun c => C * Real.sqrt (classCount c) * K
  have ha : ∀ c ∈ colors, 0 < a c := by
    intro c hc
    exact mul_pos (mul_pos hC (Real.sqrt_pos.2 (hClassCount c hc))) hK
  have hsum :
      IsBigO μ (psiSigma σ) (fun ω => ∑ c ∈ colors, Y c ω)
        (psiSigmaTriangleConst σ * ∑ c ∈ colors, a c) := by
    exact isBigO_finset_sum_of_isBigO_psiSigma
      (μ := μ) (s := colors) (X := Y) (a := a) (σ := σ)
      hσ hcolors ha (by simpa [a] using hY) hYmeas
  have hscaled :
      IsBigO μ (psiSigma σ)
        (fun ω => totalCount⁻¹ * ∑ c ∈ colors, Y c ω)
        (totalCount⁻¹ * (psiSigmaTriangleConst σ * ∑ c ∈ colors, a c)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      IndependentSums.IsBigO.const_mul (μ := μ) (Ψ := psiSigma σ)
        (X := fun ω => ∑ c ∈ colors, Y c ω)
        (A := psiSigmaTriangleConst σ * ∑ c ∈ colors, a c)
        (c := totalCount⁻¹) (inv_nonneg.mpr hTotal.le) hsum
  refine IndependentSums.IsBigO.mono_scale (μ := μ) (Ψ := psiSigma σ)
    (X := fun ω => totalCount⁻¹ * ∑ c ∈ colors, Y c ω)
    (A := totalCount⁻¹ * (psiSigmaTriangleConst σ * ∑ c ∈ colors, a c))
    (B := psiSigmaTriangleConst σ * C *
      (Real.sqrt colorCount * (Real.sqrt totalCount / totalCount)) * K)
    hscaled ?_
  have hPsi_nonneg : 0 ≤ psiSigmaTriangleConst σ := by
    have hGrowth_nonneg : 0 ≤ IndependentSums.psiGrowthConst σ :=
      le_trans zero_le_two (IndependentSums.two_le_psiGrowthConst σ)
    dsimp [psiSigmaTriangleConst, IndependentSums.psiSigmaTriangleConst]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg hGrowth_nonneg _)
  simpa [a, mul_assoc, mul_left_comm, mul_comm] using
    inv_mul_const_sum_sqrt_scale_le (colors := colors)
      (A := psiSigmaTriangleConst σ) (C := C) (K := K)
      (colorCount := colorCount) (totalCount := totalCount)
      (classCount := classCount) hPsi_nonneg hC.le hK.le hTotal hSqrt

end

end Ch04
end Book
end Homogenization
