/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import Mathlib.Algebra.Order.Chebyshev
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.PartitionAverageConstants
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.ColorClassConcentration
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAveragesDefinitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAverages

/-! # Descendant Averages -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Public descendant-average concentration

This file composes the public color-class concentration estimates with the
finite-color aggregation theorem.  It is the coefficient-law-facing form of the
partition-average fluctuation input: the statements use `RestrictionUnitRangeDependentLaw`
and `IsRestrictionLocalRandomVariable`, while the old restriction-sigma machinery remains
outside the public theorem surface.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

private theorem gammaSigmaIndependentSumConst_pos {σ : ℝ} (hσ : 0 < σ) :
    0 < gammaSigmaIndependentSumConst σ := by
  dsimp [gammaSigmaIndependentSumConst]
  by_cases hσ_lt : σ < 1
  · simpa [hσ_lt, gammaSigmaHeavyTailEndpointConst] using!
      (mul_pos
        (Real.rpow_pos_of_pos (by norm_num : 0 < (2 : ℝ)) _)
        (IndependentSums.gammaSigmaHeavyTailConst_pos hσ))
  · have hσ_one : 1 ≤ σ := le_of_not_gt hσ_lt
    dsimp [gammaSigmaExpRegimeEndpointConst]
    by_cases hσ_eq : σ = 1
    · subst σ
      simpa [hσ_lt, gammaSigmaExpRegimeEndpointConst,
        IndependentSums.gammaSigmaExpRegimeEndpointConst] using
        (mul_pos (by norm_num : 0 < (2 : ℝ))
          IndependentSums.gammaOneExpRegimeConst_pos)
    · have hExpConst_pos : 0 < IndependentSums.gammaSigmaExpRegimeConst σ := by
        dsimp [IndependentSums.gammaSigmaExpRegimeConst]
        exact lt_of_lt_of_le
          (mul_pos (by positivity) (IndependentSums.gammaMomentConst_pos hσ))
          (le_max_left _ _)
      simpa [hσ_lt, hσ_eq, gammaSigmaExpRegimeEndpointConst,
        IndependentSums.gammaSigmaExpRegimeEndpointConst] using
        (mul_pos (by norm_num : 0 < (2 : ℝ)) hExpConst_pos)

private theorem psiSigmaIndependentSumConst_pos (σ : ℝ) :
    0 < psiSigmaIndependentSumConst σ :=
  IndependentSums.psiSigmaIndependentSumConst_pos σ

/-- The explicit descendant-average `Gamma_sigma` color-count constant is
positive. -/
theorem gammaSigmaDescendantsAtScaleConst_pos {d : ℕ} {k : ℤ} {σ : ℝ}
    (hσ : 0 < σ) :
    0 < gammaSigmaDescendantsAtScaleConst d k σ := by
  have hcolor_pos : 0 < ((((scaleColorPeriod k) ^ d : ℕ) : ℝ)) := by
    exact_mod_cast (pow_pos (scaleColorPeriod_pos k) d)
  exact mul_pos
    (mul_pos IndependentSums.gammaTriangleConst_pos (gammaSigmaIndependentSumConst_pos hσ))
    (Real.sqrt_pos.2 hcolor_pos)

/-- The explicit descendant-average `Psi_sigma` color-count constant is
positive. -/
theorem psiSigmaDescendantsAtScaleConst_pos {d : ℕ} {k : ℤ} {σ : ℝ} :
    0 < psiSigmaDescendantsAtScaleConst d k σ := by
  have hcolor_pos : 0 < ((((scaleColorPeriod k) ^ d : ℕ) : ℝ)) := by
    exact_mod_cast (pow_pos (scaleColorPeriod_pos k) d)
  have htriangle_pos : 0 < psiSigmaTriangleConst σ := by
    have hgrowth_pos : 0 < IndependentSums.psiGrowthConst σ :=
      lt_of_lt_of_le zero_lt_two (IndependentSums.two_le_psiGrowthConst σ)
    dsimp [psiSigmaTriangleConst, IndependentSums.psiSigmaTriangleConst]
    positivity
  exact mul_pos
    (mul_pos htriangle_pos (psiSigmaIndependentSumConst_pos σ))
    (Real.sqrt_pos.2 hcolor_pos)

private theorem scaleColorClass_nonempty_of_mem_image {d : ℕ}
    {Q : TriadicCube d} {k : ℤ} {c : ScaleColor d k}
    (hc : c ∈ (descendantsAtScale Q k).image (cubeScaleColor k)) :
    (descendantsAtScaleScaleColorClass Q k c).Nonempty := by
  rcases Finset.mem_image.mp hc with ⟨R, hR, rfl⟩
  exact ⟨R, mem_descendantsAtScaleScaleColorClass_self hR⟩

private theorem scaleColor_sqrt_card_sum_le {d : ℕ}
    (Q : TriadicCube d) (k : ℤ) :
    ∑ c ∈ (descendantsAtScale Q k).image (cubeScaleColor k),
        Real.sqrt (((descendantsAtScaleScaleColorClass Q k c).card : ℝ)) ≤
      Real.sqrt ((((scaleColorPeriod k) ^ d : ℕ) : ℝ)) *
        Real.sqrt (((descendantsAtScale Q k).card : ℝ)) := by
  let colors : Finset (ScaleColor d k) := (descendantsAtScale Q k).image (cubeScaleColor k)
  have hsum_card_eq :
      ∑ c ∈ colors, ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) =
        ((descendantsAtScale Q k).card : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast (card_descendantsAtScale_eq_sum_card_scaleColorClass_image Q k).symm
  have hsqrt_sum_le :
      ∑ c ∈ colors, Real.sqrt ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) ≤
        Real.sqrt (colors.card : ℝ) *
          Real.sqrt ((descendantsAtScale Q k).card : ℝ) := by
    simpa [hsum_card_eq] using
      (Real.sum_sqrt_mul_sqrt_le
        (s := colors)
        (f := fun _ => (1 : ℝ))
        (g := fun c => ((descendantsAtScaleScaleColorClass Q k c).card : ℝ))
        (hf := by intro c; positivity)
        (hg := by intro c; positivity))
  have hcolors_card_le :
      (colors.card : ℝ) ≤ ((((scaleColorPeriod k) ^ d : ℕ) : ℝ)) := by
    exact_mod_cast (card_image_cubeScaleColor_descendantsAtScale_le Q k)
  have hsqrt_colors_le :
      Real.sqrt (colors.card : ℝ) ≤
        Real.sqrt ((((scaleColorPeriod k) ^ d : ℕ) : ℝ)) :=
    Real.sqrt_le_sqrt hcolors_card_le
  exact hsqrt_sum_le.trans
    (mul_le_mul_of_nonneg_right hsqrt_colors_le (by positivity))

/-- Averaging over all descendants at scale `k` preserves `Gamma_sigma`
concentration for restriction-unit-range-dependent laws. -/
theorem isBigO_gammaSigma_restrictionDescendantAverage_of_restrictionUnitRangeDependentLaw
    {d : ℕ} {Q : TriadicCube d} {k : ℤ}
    {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P] {σ K : ℝ}
    (hk : k ≤ Q.scale)
    (hP : RestrictionUnitRangeDependentLaw P)
    (hσ₀ : 0 < σ) (hσ₂ : σ ≤ 2) (hK : 0 < K)
    (X : TriadicCube d → RegCoeffField d → ℝ)
    (hX_local :
      ∀ R ∈ descendantsAtScale Q k, IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (X R))
    (hX_meas : ∀ R ∈ descendantsAtScale Q k, Measurable (X R))
    (hX : ∀ R ∈ descendantsAtScale Q k, IsBigO P (gammaSigma σ) (X R) K)
    (h_mean : ∀ R ∈ descendantsAtScale Q k, ∫ a, X R a ∂P = 0) :
    IsBigO P (gammaSigma σ)
      (fun a => ((descendantsAtScale Q k).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtScale Q k, X R a)
      (gammaSigmaDescendantsAtScaleConst d k σ *
        (Real.sqrt ((descendantsAtScale Q k).card : ℝ) /
          ((descendantsAtScale Q k).card : ℝ)) * K) := by
  let colors : Finset (ScaleColor d k) := (descendantsAtScale Q k).image (cubeScaleColor k)
  let Y : ScaleColor d k → RegCoeffField d → ℝ :=
    fun c a => ∑ R ∈ descendantsAtScaleScaleColorClass Q k c, X R a
  let classCount : ScaleColor d k → ℝ :=
    fun c => ((descendantsAtScaleScaleColorClass Q k c).card : ℝ)
  let colorCount : ℝ := (((scaleColorPeriod k) ^ d : ℕ) : ℝ)
  let totalCount : ℝ := ((descendantsAtScale Q k).card : ℝ)
  have hcolors : colors.Nonempty := by
    rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
    exact ⟨cubeScaleColor k R, Finset.mem_image.mpr ⟨R, hR, rfl⟩⟩
  have hClassCount : ∀ c ∈ colors, 0 < classCount c := by
    intro c hc
    have hnonempty : (descendantsAtScaleScaleColorClass Q k c).Nonempty :=
      scaleColorClass_nonempty_of_mem_image (Q := Q) (k := k) (c := c) (by simpa [colors] using hc)
    dsimp [classCount]
    exact_mod_cast hnonempty.card_pos
  have hTotal : 0 < totalCount := by
    dsimp [totalCount]
    exact_mod_cast (descendantsAtScale_nonempty Q hk).card_pos
  have hY :
      ∀ c ∈ colors,
        IsBigO P (gammaSigma σ) (Y c)
          (gammaSigmaIndependentSumConst σ * Real.sqrt (classCount c) * K) := by
    intro c hc
    have hcolor :=
      isBigO_gammaSigma_finsetSum_descendantsAtScaleScaleColorClass_of_restrictionUnitRangeDependentLaw
        (Q := Q) (k := k) (c := c) (P := P) hP hσ₀ hσ₂ hK X
        (fun R hR => hX_local R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1)
        (fun R hR => hX_meas R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1)
        (fun R hR => hX R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1)
        (fun R hR => h_mean R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1)
    simpa [Y, classCount] using hcolor
  have hYmeas : ∀ c ∈ colors, Measurable (Y c) := by
    intro c hc
    simpa [Y] using
      (Finset.measurable_sum (descendantsAtScaleScaleColorClass Q k c)
        (fun R hR => hX_meas R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1))
  have hSqrt :
      ∑ c ∈ colors, Real.sqrt (classCount c) ≤
        Real.sqrt colorCount * Real.sqrt totalCount := by
    simpa [colors, classCount, colorCount, totalCount] using
      scaleColor_sqrt_card_sum_le Q k
  have haverage :=
    isBigO_finsetAverage_colorClassSums_gammaSigma
      (μ := P) (colors := colors) (Y := Y) (classCount := classCount)
      (colorCount := colorCount) (totalCount := totalCount)
      (C := gammaSigmaIndependentSumConst σ) (K := K) (σ := σ)
      hσ₀ hcolors hClassCount hTotal (gammaSigmaIndependentSumConst_pos hσ₀) hK
      hY hYmeas hSqrt
  have hsum_eq :
      (fun a => ∑ c ∈ colors, Y c a) =
        fun a => ∑ R ∈ descendantsAtScale Q k, X R a := by
    funext a
    calc
      ∑ c ∈ colors, Y c a =
          ∑ c ∈ colors, ∑ R ∈ descendantsAtScaleScaleColorClass Q k c, X R a := by
            refine Finset.sum_congr rfl ?_
            intro c hc
            simp [Y]
      _ = ∑ R ∈ colors.biUnion (descendantsAtScaleScaleColorClass Q k), X R a := by
            symm
            exact Finset.sum_biUnion (by
              intro c hc c' hc' hneq
              exact disjoint_descendantsAtScaleScaleColorClass_of_ne Q k hneq)
      _ = ∑ R ∈ descendantsAtScale Q k, X R a := by
            rw [show colors.biUnion (descendantsAtScaleScaleColorClass Q k) =
              descendantsAtScale Q k by
                simpa [colors] using descendantsAtScale_eq_biUnion_image_cubeScaleColor Q k]
  have haverage_fun_eq :
      (fun a => totalCount⁻¹ * ∑ c ∈ colors, Y c a) =
        fun a => ((descendantsAtScale Q k).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtScale Q k, X R a := by
    funext a
    rw [show (∑ c ∈ colors, Y c a) =
        ∑ R ∈ descendantsAtScale Q k, X R a from congrFun hsum_eq a]
  simpa [gammaSigmaDescendantsAtScaleConst, totalCount, colorCount, haverage_fun_eq,
    div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using haverage

/-- Averaging over all descendants at scale `k` preserves `Psi_sigma`
concentration for restriction-unit-range-dependent laws. -/
theorem isBigO_psiSigma_restrictionDescendantAverage_of_restrictionUnitRangeDependentLaw
    {d : ℕ} {Q : TriadicCube d} {k : ℤ}
    {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P] {σ K : ℝ}
    (hk : k ≤ Q.scale)
    (hP : RestrictionUnitRangeDependentLaw P)
    (hσ : 1 ≤ σ) (hK : 0 < K)
    (X : TriadicCube d → RegCoeffField d → ℝ)
    (hX_local :
      ∀ R ∈ descendantsAtScale Q k, IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (X R))
    (hX_meas : ∀ R ∈ descendantsAtScale Q k, Measurable (X R))
    (hX_int : ∀ R ∈ descendantsAtScale Q k, Integrable (X R) P)
    (hX : ∀ R ∈ descendantsAtScale Q k, IsBigO P (psiSigma σ) (X R) K)
    (h_mean : ∀ R ∈ descendantsAtScale Q k, ∫ a, X R a ∂P = 0) :
    IsBigO P (psiSigma σ)
      (fun a => ((descendantsAtScale Q k).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtScale Q k, X R a)
      (psiSigmaDescendantsAtScaleConst d k σ *
        (Real.sqrt ((descendantsAtScale Q k).card : ℝ) /
          ((descendantsAtScale Q k).card : ℝ)) * K) := by
  let colors : Finset (ScaleColor d k) := (descendantsAtScale Q k).image (cubeScaleColor k)
  let Y : ScaleColor d k → RegCoeffField d → ℝ :=
    fun c a => ∑ R ∈ descendantsAtScaleScaleColorClass Q k c, X R a
  let classCount : ScaleColor d k → ℝ :=
    fun c => ((descendantsAtScaleScaleColorClass Q k c).card : ℝ)
  let colorCount : ℝ := (((scaleColorPeriod k) ^ d : ℕ) : ℝ)
  let totalCount : ℝ := ((descendantsAtScale Q k).card : ℝ)
  have hcolors : colors.Nonempty := by
    rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
    exact ⟨cubeScaleColor k R, Finset.mem_image.mpr ⟨R, hR, rfl⟩⟩
  have hClassCount : ∀ c ∈ colors, 0 < classCount c := by
    intro c hc
    have hnonempty : (descendantsAtScaleScaleColorClass Q k c).Nonempty :=
      scaleColorClass_nonempty_of_mem_image (Q := Q) (k := k) (c := c) (by simpa [colors] using hc)
    dsimp [classCount]
    exact_mod_cast hnonempty.card_pos
  have hTotal : 0 < totalCount := by
    dsimp [totalCount]
    exact_mod_cast (descendantsAtScale_nonempty Q hk).card_pos
  have hY :
      ∀ c ∈ colors,
        IsBigO P (psiSigma σ) (Y c)
          (psiSigmaIndependentSumConst σ * Real.sqrt (classCount c) * K) := by
    intro c hc
    have hcolor :=
      isBigO_psiSigma_finsetSum_descendantsAtScaleScaleColorClass_of_restrictionUnitRangeDependentLaw
        (Q := Q) (k := k) (c := c) (P := P) hP hσ hK X
        (fun R hR => hX_local R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1)
        (fun R hR => hX_meas R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1)
        (fun R hR => hX_int R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1)
        (fun R hR => hX R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1)
        (fun R hR => h_mean R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1)
    simpa [Y, classCount] using hcolor
  have hYmeas : ∀ c ∈ colors, Measurable (Y c) := by
    intro c hc
    simpa [Y] using
      (Finset.measurable_sum (descendantsAtScaleScaleColorClass Q k c)
        (fun R hR => hX_meas R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1))
  have hSqrt :
      ∑ c ∈ colors, Real.sqrt (classCount c) ≤
        Real.sqrt colorCount * Real.sqrt totalCount := by
    simpa [colors, classCount, colorCount, totalCount] using
      scaleColor_sqrt_card_sum_le Q k
  have haverage :=
    isBigO_finsetAverage_colorClassSums_psiSigma
      (μ := P) (colors := colors) (Y := Y) (classCount := classCount)
      (colorCount := colorCount) (totalCount := totalCount)
      (C := psiSigmaIndependentSumConst σ) (K := K) (σ := σ)
      hσ hcolors hClassCount hTotal (psiSigmaIndependentSumConst_pos σ) hK
      hY hYmeas hSqrt
  have hsum_eq :
      (fun a => ∑ c ∈ colors, Y c a) =
        fun a => ∑ R ∈ descendantsAtScale Q k, X R a := by
    funext a
    calc
      ∑ c ∈ colors, Y c a =
          ∑ c ∈ colors, ∑ R ∈ descendantsAtScaleScaleColorClass Q k c, X R a := by
            refine Finset.sum_congr rfl ?_
            intro c hc
            simp [Y]
      _ = ∑ R ∈ colors.biUnion (descendantsAtScaleScaleColorClass Q k), X R a := by
            symm
            exact Finset.sum_biUnion (by
              intro c hc c' hc' hneq
              exact disjoint_descendantsAtScaleScaleColorClass_of_ne Q k hneq)
      _ = ∑ R ∈ descendantsAtScale Q k, X R a := by
            rw [show colors.biUnion (descendantsAtScaleScaleColorClass Q k) =
              descendantsAtScale Q k by
                simpa [colors] using descendantsAtScale_eq_biUnion_image_cubeScaleColor Q k]
  have haverage_fun_eq :
      (fun a => totalCount⁻¹ * ∑ c ∈ colors, Y c a) =
        fun a => ((descendantsAtScale Q k).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtScale Q k, X R a := by
    funext a
    rw [show (∑ c ∈ colors, Y c a) =
        ∑ R ∈ descendantsAtScale Q k, X R a from congrFun hsum_eq a]
  simpa [psiSigmaDescendantsAtScaleConst, totalCount, colorCount, haverage_fun_eq,
    div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using haverage

end

end Ch04
end Book
end Homogenization
