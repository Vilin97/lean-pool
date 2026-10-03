/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.CardinalZeta
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Exact quadratic mass of the cardinal small cutoff. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Cutoff

theorem CardinalIntegral.cardinalZeta_sq_left {t : ℝ}
    (ht₂ : t ≤ -zetaCoreRadius) :
    cardinalZeta t ^ 2 = cardinalStep ((t + zetaOuterRadius) / zetaWidth) ^ 2 := by
  unfold cardinalZeta
  have hright : 1 ≤ (zetaOuterRadius - t) / zetaWidth := by
    rw [le_div_iff₀ zetaWidth_pos]
    nlinarith [zetaOuterRadius_sub_coreRadius, zetaCoreRadius_pos]
  rw [cardinalStep_one_of_one_le hright]
  ring

theorem CardinalIntegral.cardinalZeta_sq_right {t : ℝ}
    (ht₁ : zetaCoreRadius ≤ t) :
    cardinalZeta t ^ 2 = cardinalStep ((zetaOuterRadius - t) / zetaWidth) ^ 2 := by
  unfold cardinalZeta
  have hleft : 1 ≤ (t + zetaOuterRadius) / zetaWidth := by
    rw [le_div_iff₀ zetaWidth_pos]
    nlinarith [zetaOuterRadius_sub_coreRadius, zetaCoreRadius_pos]
  rw [cardinalStep_one_of_one_le hleft]
  ring

/-- Square of the cardinal transition profile. -/
def CardinalIntegral.stepSquare (x : ℝ) : ℝ := cardinalStep x ^ 2

/-- Square of the complementary cardinal transition profile. -/
def CardinalIntegral.stepComplementSquare (x : ℝ) : ℝ := (1 - cardinalStep x) ^ 2

theorem CardinalIntegral.stepSquare_integrable :
    IntervalIntegrable CardinalIntegral.stepSquare MeasureTheory.volume (0 : ℝ) 1 := by
  apply (cardinalStep_contDiff.continuous.pow 2).intervalIntegrable

theorem CardinalIntegral.stepComplementSquare_integrable :
    IntervalIntegrable CardinalIntegral.stepComplementSquare MeasureTheory.volume (0 : ℝ) 1 := by
  apply (((continuous_const.sub cardinalStep_contDiff.continuous).pow 2)).intervalIntegrable

theorem CardinalIntegral.stepProduct_integrable :
    IntervalIntegrable (fun x : ℝ => cardinalStep x * (1 - cardinalStep x))
      MeasureTheory.volume (0 : ℝ) 1 := by
  apply (cardinalStep_contDiff.continuous.mul
    (continuous_const.sub cardinalStep_contDiff.continuous)).intervalIntegrable

theorem CardinalIntegral.step_square_integral_eq_one_half_sub_mass :
    (∫ x in (0 : ℝ)..1, cardinalStep x ^ 2) = 1 / 2 - cardinalMass := by
  have hreflect :
      (∫ x in (0 : ℝ)..1, CardinalIntegral.stepComplementSquare x) =
        ∫ x in (0 : ℝ)..1, CardinalIntegral.stepSquare x := by
    calc
      (∫ x in (0 : ℝ)..1, CardinalIntegral.stepComplementSquare x) =
          ∫ x in (0 : ℝ)..1, CardinalIntegral.stepSquare (1 - x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp [CardinalIntegral.stepComplementSquare, CardinalIntegral.stepSquare,
            cardinalStep_one_sub]
      _ = ∫ x in (0 : ℝ)..1, CardinalIntegral.stepSquare x := by
        simpa [CardinalIntegral.stepSquare] using
          (intervalIntegral.integral_comp_sub_left
            (f := fun x : ℝ => cardinalStep x ^ 2) (a := (0 : ℝ)) (b := 1) 1)
  have hsum :
      (∫ x in (0 : ℝ)..1, CardinalIntegral.stepSquare x) +
          ∫ x in (0 : ℝ)..1, CardinalIntegral.stepComplementSquare x =
        ∫ x in (0 : ℝ)..1,
          (1 - 2 * (cardinalStep x * (1 - cardinalStep x))) := by
    calc
      _ = ∫ x in (0 : ℝ)..1, (CardinalIntegral.stepSquare x +
          CardinalIntegral.stepComplementSquare x) := by
        symm
        exact intervalIntegral.integral_add CardinalIntegral.stepSquare_integrable
          CardinalIntegral.stepComplementSquare_integrable
      _ = ∫ x in (0 : ℝ)..1,
          (1 - 2 * (cardinalStep x * (1 - cardinalStep x))) := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp only [CardinalIntegral.stepSquare, CardinalIntegral.stepComplementSquare]
        ring
  have hright :
      (∫ x in (0 : ℝ)..1,
          (1 - 2 * (cardinalStep x * (1 - cardinalStep x)))) =
        1 - 2 * cardinalMass := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (CardinalIntegral.stepProduct_integrable.const_mul 2)]
    simp [cardinalMass, intervalIntegral.integral_const]
  rw [hreflect] at hsum
  rw [hright] at hsum
  unfold CardinalIntegral.stepSquare at hsum
  nlinarith

theorem CardinalIntegral.square_profile_left_change :
    (∫ t in -zetaOuterRadius..-zetaCoreRadius,
        cardinalStep ((t + zetaOuterRadius) / zetaWidth) ^ 2) =
      zetaWidth * (∫ x in (0 : ℝ)..1, cardinalStep x ^ 2) := by
  have h := intervalIntegral.integral_comp_div_add
    (f := fun x : ℝ => cardinalStep x ^ 2)
    (a := -zetaOuterRadius) (b := -zetaCoreRadius) (c := zetaWidth)
    (d := zetaOuterRadius / zetaWidth) (ne_of_gt zetaWidth_pos)
  have hstart : -zetaOuterRadius / zetaWidth + zetaOuterRadius / zetaWidth = 0 := by ring
  have hend : -zetaCoreRadius / zetaWidth + zetaOuterRadius / zetaWidth = 1 := by
    calc
      -zetaCoreRadius / zetaWidth + zetaOuterRadius / zetaWidth =
          (zetaOuterRadius - zetaCoreRadius) / zetaWidth := by ring
      _ = 1 := by rw [zetaOuterRadius_sub_coreRadius]; exact div_self (ne_of_gt zetaWidth_pos)
  rw [show (fun t : ℝ => cardinalStep ((t + zetaOuterRadius) / zetaWidth) ^ 2) =
      (fun t => cardinalStep (t / zetaWidth + zetaOuterRadius / zetaWidth) ^ 2) by
        funext t
        congr 2
        ring] at *
  rw [hstart, hend] at h
  simpa [smul_eq_mul] using h

theorem CardinalIntegral.square_profile_right_change :
    (∫ t in zetaCoreRadius..zetaOuterRadius,
        cardinalStep ((zetaOuterRadius - t) / zetaWidth) ^ 2) =
      zetaWidth * (∫ x in (0 : ℝ)..1, cardinalStep x ^ 2) := by
  have h := intervalIntegral.integral_comp_sub_div
    (f := fun x : ℝ => cardinalStep x ^ 2)
    (a := zetaCoreRadius) (b := zetaOuterRadius) (c := zetaWidth)
    (d := zetaOuterRadius / zetaWidth) (ne_of_gt zetaWidth_pos)
  have hstart : zetaOuterRadius / zetaWidth - zetaOuterRadius / zetaWidth = 0 := by ring
  have hend : zetaOuterRadius / zetaWidth - zetaCoreRadius / zetaWidth = 1 := by
    calc
      zetaOuterRadius / zetaWidth - zetaCoreRadius / zetaWidth =
          (zetaOuterRadius - zetaCoreRadius) / zetaWidth := by ring
      _ = 1 := by rw [zetaOuterRadius_sub_coreRadius]; exact div_self (ne_of_gt zetaWidth_pos)
  rw [show (fun t : ℝ => cardinalStep ((zetaOuterRadius - t) / zetaWidth) ^ 2) =
      (fun t => cardinalStep (zetaOuterRadius / zetaWidth - t / zetaWidth) ^ 2) by
        funext t
        congr 2
        ring] at *
  rw [hstart, hend] at h
  simpa [smul_eq_mul] using h

theorem cardinalZeta_sq_integral :
    ∫ t, cardinalZeta t ^ 2 = 9 / 10 := by
  let f : ℝ → ℝ := fun t => cardinalZeta t ^ 2
  have hf : Continuous f := by
    dsimp [f]
    exact (cardinalZeta_contDiff.continuous).pow 2
  have hsupport : Function.support f ⊆ Set.Ioc (-1 : ℝ) 1 := by
    intro t ht
    have hne : f t ≠ 0 := by simpa [Function.mem_support] using ht
    constructor
    · by_contra hleft
      have hzero : cardinalZeta t = 0 := cardinalZeta_eq_zero_of_le (by
        have hout := zetaOuterRadius_le_one
        linarith)
      exact hne (by simp [f, hzero])
    · by_contra hright
      have hzero : cardinalZeta t = 0 := cardinalZeta_eq_zero_of_ge (by
        have hout := zetaOuterRadius_le_one
        linarith)
      exact hne (by simp [f, hzero])
  have hIleft : IntervalIntegrable f MeasureTheory.volume (-1) (-zetaOuterRadius) :=
    hf.intervalIntegrable _ _
  have hIleftBand : IntervalIntegrable f MeasureTheory.volume
      (-zetaOuterRadius) (-zetaCoreRadius) := hf.intervalIntegrable _ _
  have hIcore : IntervalIntegrable f MeasureTheory.volume
      (-zetaCoreRadius) zetaCoreRadius := hf.intervalIntegrable _ _
  have hIrightBand : IntervalIntegrable f MeasureTheory.volume
      zetaCoreRadius zetaOuterRadius := hf.intervalIntegrable _ _
  have hIright : IntervalIntegrable f MeasureTheory.volume zetaOuterRadius 1 :=
    hf.intervalIntegrable _ _
  have hIleftMid : IntervalIntegrable f MeasureTheory.volume (-1) (-zetaCoreRadius) :=
    hIleft.trans hIleftBand
  have hIleftCore : IntervalIntegrable f MeasureTheory.volume (-1) zetaCoreRadius :=
    hIleftMid.trans hIcore
  have hImidRight : IntervalIntegrable f MeasureTheory.volume
      (-zetaCoreRadius) zetaOuterRadius := hIcore.trans hIrightBand
  have hIleftRight : IntervalIntegrable f MeasureTheory.volume (-1) zetaOuterRadius :=
    hIleftCore.trans hIrightBand
  have hsplit :
      (((((∫ t in (-1 : ℝ)..(-zetaOuterRadius), f t) +
        (∫ t in (-zetaOuterRadius)..(-zetaCoreRadius), f t)) +
        (∫ t in (-zetaCoreRadius)..zetaCoreRadius, f t)) +
        (∫ t in zetaCoreRadius..zetaOuterRadius, f t)) +
        (∫ t in zetaOuterRadius..1, f t)) = ∫ t in (-1 : ℝ)..1, f t := by
    have h₁ := intervalIntegral.integral_add_adjacent_intervals hIleft hIleftBand
    have h₂ := intervalIntegral.integral_add_adjacent_intervals hIleftMid hIcore
    have h₃ := intervalIntegral.integral_add_adjacent_intervals hIleftCore hIrightBand
    have h₄ := intervalIntegral.integral_add_adjacent_intervals hIleftRight hIright
    calc
      (((((∫ t in (-1 : ℝ)..(-zetaOuterRadius), f t) +
            (∫ t in (-zetaOuterRadius)..(-zetaCoreRadius), f t)) +
            (∫ t in (-zetaCoreRadius)..zetaCoreRadius, f t)) +
            (∫ t in zetaCoreRadius..zetaOuterRadius, f t)) +
            (∫ t in zetaOuterRadius..1, f t)) =
            ((((∫ t in (-1 : ℝ)..(-zetaCoreRadius), f t) +
            (∫ t in (-zetaCoreRadius)..zetaCoreRadius, f t)) +
            (∫ t in zetaCoreRadius..zetaOuterRadius, f t)) +
            (∫ t in zetaOuterRadius..1, f t)) := by rw [h₁]
        _ = (((∫ t in (-1 : ℝ)..zetaCoreRadius, f t) +
            (∫ t in zetaCoreRadius..zetaOuterRadius, f t)) +
            (∫ t in zetaOuterRadius..1, f t)) := by rw [h₂]
        _ = (∫ t in (-1 : ℝ)..zetaOuterRadius, f t) +
            (∫ t in zetaOuterRadius..1, f t) := by rw [h₃]
        _ = ∫ t in (-1 : ℝ)..1, f t := h₄
  have hleftzero : (∫ t in (-1 : ℝ)..(-zetaOuterRadius), f t) = 0 := by
    have hord : (-1 : ℝ) ≤ -zetaOuterRadius := by linarith [zetaOuterRadius_le_one]
    have hEq : Set.EqOn f (fun _ => (0 : ℝ)) (Set.uIcc (-1 : ℝ) (-zetaOuterRadius)) := by
      intro t ht
      rw [Set.uIcc_of_le hord] at ht
      have ht' : t ≤ -zetaOuterRadius := ht.2
      simp [f, cardinalZeta_eq_zero_of_le ht']
    calc
      (∫ t in (-1 : ℝ)..(-zetaOuterRadius), f t) =
          ∫ t in (-1 : ℝ)..(-zetaOuterRadius), (0 : ℝ) :=
        intervalIntegral.integral_congr hEq
      _ = 0 := by simp
  have hrightzero : (∫ t in zetaOuterRadius..1, f t) = 0 := by
    have hord : zetaOuterRadius ≤ (1 : ℝ) := zetaOuterRadius_le_one
    have hEq : Set.EqOn f (fun _ => (0 : ℝ)) (Set.uIcc zetaOuterRadius (1 : ℝ)) := by
      intro t ht
      rw [Set.uIcc_of_le hord] at ht
      have ht' : zetaOuterRadius ≤ t := ht.1
      simp [f, cardinalZeta_eq_zero_of_ge ht']
    calc
      (∫ t in zetaOuterRadius..1, f t) =
          ∫ t in zetaOuterRadius..1, (0 : ℝ) := intervalIntegral.integral_congr hEq
      _ = 0 := by simp
  have hleftband :
      (∫ t in (-zetaOuterRadius)..(-zetaCoreRadius), f t) =
        zetaWidth * (∫ x in (0 : ℝ)..1, cardinalStep x ^ 2) := by
    calc
      (∫ t in (-zetaOuterRadius)..(-zetaCoreRadius), f t) =
          ∫ t in (-zetaOuterRadius)..(-zetaCoreRadius),
            cardinalStep ((t + zetaOuterRadius) / zetaWidth) ^ 2 := by
        apply intervalIntegral.integral_congr
        have hord : -zetaOuterRadius ≤ -zetaCoreRadius := by
          linarith [zetaOuterRadius_sub_coreRadius, zetaWidth_pos]
        intro t ht
        rw [Set.uIcc_of_le hord] at ht
        simp only [f]
        rw [CardinalIntegral.cardinalZeta_sq_left ht.2]
      _ = zetaWidth * (∫ x in (0 : ℝ)..1, cardinalStep x ^ 2) :=
        CardinalIntegral.square_profile_left_change
  have hrightband :
      (∫ t in zetaCoreRadius..zetaOuterRadius, f t) =
        zetaWidth * (∫ x in (0 : ℝ)..1, cardinalStep x ^ 2) := by
    calc
      (∫ t in zetaCoreRadius..zetaOuterRadius, f t) =
          ∫ t in zetaCoreRadius..zetaOuterRadius,
            cardinalStep ((zetaOuterRadius - t) / zetaWidth) ^ 2 := by
        apply intervalIntegral.integral_congr
        have hord : zetaCoreRadius ≤ zetaOuterRadius := by
          linarith [zetaOuterRadius_sub_coreRadius, zetaWidth_pos]
        intro t ht
        rw [Set.uIcc_of_le hord] at ht
        simp only [f]
        rw [CardinalIntegral.cardinalZeta_sq_right ht.1]
      _ = zetaWidth * (∫ x in (0 : ℝ)..1, cardinalStep x ^ 2) :=
        CardinalIntegral.square_profile_right_change
  have hcore : (∫ t in (-zetaCoreRadius)..zetaCoreRadius, f t) =
      2 * zetaCoreRadius := by
    have hord : -zetaCoreRadius ≤ zetaCoreRadius := by linarith [zetaCoreRadius_pos]
    calc
      (∫ t in (-zetaCoreRadius)..zetaCoreRadius, f t) =
          ∫ t in (-zetaCoreRadius)..zetaCoreRadius, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        rw [Set.uIcc_of_le hord]
        intro t ht
        simp [f, cardinalZeta_eq_one ht.1 ht.2]
      _ = 2 * zetaCoreRadius := by
        simp [intervalIntegral.integral_const]
        ring
  have hfull := intervalIntegral.integral_eq_integral_of_support_subset
    (μ := MeasureTheory.volume) hsupport
  have hw : zetaWidth = (20 * cardinalMass)⁻¹ := rfl
  have hwidthmass : zetaWidth * cardinalMass = 1 / 20 := by
    rw [hw]
    field_simp [ne_of_gt cardinalMass_pos]
  calc
    (∫ t, f t) = ∫ t in (-1 : ℝ)..1, f t := hfull.symm
    _ = (((((∫ t in (-1 : ℝ)..(-zetaOuterRadius), f t) +
        (∫ t in (-zetaOuterRadius)..(-zetaCoreRadius), f t)) +
        (∫ t in (-zetaCoreRadius)..zetaCoreRadius, f t)) +
        (∫ t in zetaCoreRadius..zetaOuterRadius, f t)) +
        (∫ t in zetaOuterRadius..1, f t)) := hsplit.symm
    _ = 9 / 10 := by
      rw [hleftzero, hrightzero, hleftband, hrightband, hcore,
        CardinalIntegral.step_square_integral_eq_one_half_sub_mass]
      simp only [zero_add, add_zero]
      nlinarith [zetaCoreRadius_add_width, hwidthmass]

end AVenhance.Infra.Cutoff
