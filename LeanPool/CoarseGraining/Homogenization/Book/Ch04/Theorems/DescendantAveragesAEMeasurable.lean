/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.ConcentrationAEMeasurable
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.DescendantAverages

/-! # Descendant Averages AEMeasurable -/

namespace Homogenization
namespace Book
namespace Ch04

/-!
# A.e.-measurable descendant-average concentration

This file mirrors the Gamma descendant-average estimate from
`DescendantAverages`, replacing global measurability of the summands by
law-a.e. measurability.  The locality and unit-range assumptions are unchanged.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {Ω κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

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
        IndependentSums.gammaSigmaExpRegimeEndpointConst] using!
        (mul_pos (by norm_num : 0 < (2 : ℝ))
          IndependentSums.gammaOneExpRegimeConst_pos)
    · have hExpConst_pos : 0 < IndependentSums.gammaSigmaExpRegimeConst σ := by
        dsimp [IndependentSums.gammaSigmaExpRegimeConst]
        exact lt_of_lt_of_le
          (mul_pos (by positivity) (IndependentSums.gammaMomentConst_pos hσ))
          (le_max_left _ _)
      simpa [hσ_lt, hσ_eq, gammaSigmaExpRegimeEndpointConst,
        IndependentSums.gammaSigmaExpRegimeEndpointConst] using!
        (mul_pos (by norm_num : 0 < (2 : ℝ)) hExpConst_pos)

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

theorem isBigO_gammaSigma_finsetSum_descendantsAtScaleScaleColorClass_of_restrictionUnitRangeDependentLaw_aemeasurable
    {d : ℕ} {Q : TriadicCube d} {k : ℤ} {c : ScaleColor d k}
    {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P] {σ K : ℝ}
    (hP : RestrictionUnitRangeDependentLaw P)
    (hσ₀ : 0 < σ) (hσ₂ : σ ≤ 2) (hK : 0 < K)
    (X : TriadicCube d → RegCoeffField d → ℝ)
    (hX_local :
      ∀ R ∈ descendantsAtScaleScaleColorClass Q k c,
        IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (X R))
    (hX_aemeas :
      ∀ R ∈ descendantsAtScaleScaleColorClass Q k c, AEMeasurable (X R) P)
    (hX :
      ∀ R ∈ descendantsAtScaleScaleColorClass Q k c,
        IsBigO P (gammaSigma σ) (X R) K)
    (h_mean :
      ∀ R ∈ descendantsAtScaleScaleColorClass Q k c, ∫ a, X R a ∂P = 0) :
    IsBigO P (gammaSigma σ)
      (fun a => ∑ R ∈ descendantsAtScaleScaleColorClass Q k c, X R a)
      (gammaSigmaIndependentSumConst σ *
        Real.sqrt ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) * K) := by
  let S : Finset (TriadicCube d) := descendantsAtScaleScaleColorClass Q k c
  by_cases hS : S.Nonempty
  · let Y : {R : TriadicCube d // R ∈ S} → RegCoeffField d → ℝ :=
      fun R => X R.1
    have h_indep : ProbabilityTheory.iIndepFun Y P := by
      exact iIndepFun_descendantsAtScaleScaleColorClass_of_restrictionUnitRangeDependentLaw
        (Q := Q) (k := k) (c := c) (P := P) hP
        (fun R => hX_local R.1 R.2)
    have h_aemeas : ∀ R, AEMeasurable (Y R) P := by
      intro R
      exact hX_aemeas R.1 R.2
    have hY :
        ∀ R ∈ S.attach, IsBigO P (gammaSigma σ) (Y R) K := by
      intro R _hR
      exact hX R.1 R.2
    have h_meanY : ∀ R ∈ S.attach, ∫ a, Y R a ∂P = 0 := by
      intro R _hR
      exact h_mean R.1 R.2
    have hS_attach : S.attach.Nonempty := by
      simpa using hS
    have hsum_eq :
        (fun a => ∑ R ∈ S.attach, Y R a) =
          fun a => ∑ R ∈ S, X R a := by
      funext a
      simpa [Y] using
        (Finset.sum_attach (s := S) (f := fun R => X R a))
    have hsum :=
      isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero_aemeasurable
        (μ := P) (X := Y) (s := S.attach) (σ := σ) (K := K)
        h_indep h_aemeas hS_attach hσ₀ hσ₂ hK hY h_meanY
    simpa [S, hsum_eq, mul_assoc, mul_left_comm, mul_comm] using hsum
  · have hS_empty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [isBigO_gammaSigma_iff]
    intro t ht
    have htail_empty :
        absTailEvent (fun _ : RegCoeffField d => (0 : ℝ)) 0 = ∅ := by
      ext a
      simp [absTailEvent]
    simpa [S, hS_empty, htail_empty, absTailEvent, upperTailEvent] using
      (show (0 : ℝ) ≤ Real.exp (-(t ^ σ)) by positivity)

theorem isBigO_finsetAverage_colorClassSums_gammaSigma_aemeasurable
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
    (hY_aemeas : ∀ c, AEMeasurable (Y c) μ)
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
    exact isBigO_finset_sum_of_isBigO_gammaSigma_aemeasurable
      (μ := μ) (s := colors) (X := Y) (a := a) (σ := σ)
      hσ hcolors ha (by simpa [a] using hY) hY_aemeas
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

theorem isBigO_gammaSigma_restrictionDescendantAverage_of_restrictionUnitRangeDependentLaw_aemeasurable
    {d : ℕ} {Q : TriadicCube d} {k : ℤ}
    {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P] {σ K : ℝ}
    (hk : k ≤ Q.scale)
    (hP : RestrictionUnitRangeDependentLaw P)
    (hσ₀ : 0 < σ) (hσ₂ : σ ≤ 2) (hK : 0 < K)
    (X : TriadicCube d → RegCoeffField d → ℝ)
    (hX_local :
      ∀ R ∈ descendantsAtScale Q k, IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (X R))
    (hX_aemeas : ∀ R ∈ descendantsAtScale Q k, AEMeasurable (X R) P)
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
      isBigO_gammaSigma_finsetSum_descendantsAtScaleScaleColorClass_of_restrictionUnitRangeDependentLaw_aemeasurable
        (Q := Q) (k := k) (c := c) (P := P) hP hσ₀ hσ₂ hK X
        (fun R hR => hX_local R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1)
        (fun R hR => hX_aemeas R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1)
        (fun R hR => hX R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1)
        (fun R hR => h_mean R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1)
    simpa [Y, classCount] using hcolor
  have hYaemeas : ∀ c, AEMeasurable (Y c) P := by
    intro c
    convert
      (Finset.aemeasurable_sum (descendantsAtScaleScaleColorClass Q k c)
        (fun R hR => hX_aemeas R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1)
        ) using 1
    ext a
    simp [Y]
  have hSqrt :
      ∑ c ∈ colors, Real.sqrt (classCount c) ≤
        Real.sqrt colorCount * Real.sqrt totalCount := by
    simpa [colors, classCount, colorCount, totalCount] using
      scaleColor_sqrt_card_sum_le Q k
  have haverage :=
    isBigO_finsetAverage_colorClassSums_gammaSigma_aemeasurable
      (μ := P) colors (Y := Y) (classCount := classCount)
      (colorCount := colorCount) (totalCount := totalCount)
      (C := gammaSigmaIndependentSumConst σ) (K := K) (σ := σ)
      hσ₀ hcolors hClassCount hTotal (gammaSigmaIndependentSumConst_pos hσ₀) hK
      hY hYaemeas hSqrt
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
  simpa [gammaSigmaDescendantsAtScaleConst, totalCount, colorCount,
    haverage_fun_eq, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using haverage

end

end Ch04
end Book
end Homogenization
