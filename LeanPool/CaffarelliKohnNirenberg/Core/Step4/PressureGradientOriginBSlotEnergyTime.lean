/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginBSlotEnergyHolder
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Time masses of slice majorants for `prop:bootstrap`

The whole-carrier `6/5` time mass of the localized pressure source in
`eq:pressure-gradient-decomposition` is controlled by three slice integrals: the cube of
the velocity slice norm, the square of the gradient slice norm, and the `q`-th
power of the force slice norm.  This file isolates the measure-theoretic step
that converts those three integrals into the `6/5` mass of a majorant of the
shape `c₁ * (a * d) + c₂ * a ^ 2 + c₃ * F`.

Every constant here is explicit, and no estimate below depends on the solution.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace CKN.Core.Step4

/-- A lower power of a nonnegative function costs only the total mass: the
elementary split at the level one, used throughout `prop:bootstrap`. -/
theorem lintegral_rpow_le_measure_add_lintegral_rpow
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (h : α → ℝ≥0∞) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) :
    (∫⁻ x, h x ^ r ∂μ) ≤ μ Set.univ + ∫⁻ x, h x ^ t ∂μ := by
  calc
    _ ≤ ∫⁻ x, 1 + h x ^ t ∂μ := by
        refine lintegral_mono fun x => ?_
        by_cases hx : h x ≤ 1
        · exact (ENNReal.rpow_le_one hx hr).trans le_self_add
        · exact (ENNReal.rpow_le_rpow_of_exponent_le (le_of_not_ge hx) hrt).trans le_add_self
    _ = _ := by
        rw [lintegral_add_left measurable_const, lintegral_one]

/-- Young's inequality in `ℝ≥0∞`: an interpolated product never exceeds the sum
of its two endpoints. -/
theorem rpow_mul_rpow_le_add (x y : ℝ≥0∞) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    x ^ θ * y ^ (1 - θ) ≤ x + y := by
  have hx : x ^ θ ≤ (x + y) ^ θ := ENNReal.rpow_le_rpow le_self_add h0
  have hy : y ^ (1 - θ) ≤ (x + y) ^ (1 - θ) :=
    ENNReal.rpow_le_rpow le_add_self (by linarith only [h1])
  refine (mul_le_mul' hx hy).trans ?_
  rcases eq_or_ne (x + y) 0 with hz | hz
  · rw [hz]
    rcases eq_or_lt_of_le h0 with h | h
    · rw [← h]
      simp
    · rw [ENNReal.zero_rpow_of_pos h, zero_mul]
  · rcases eq_or_ne (x + y) ⊤ with ht | ht
    · rw [ht]
      exact le_top
    · rw [← ENNReal.rpow_add _ _ hz ht]
      simp

/-- Hölder's inequality at the exponents of `eq:pressure-gradient-decomposition`: the
`6/5` mass of a product is controlled by the cube and the square masses. -/
theorem lintegral_mul_six_fifths_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {a b : α → ℝ≥0∞}
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) :
    (∫⁻ x, (a x * b x) ^ (6 / 5 : ℝ) ∂μ) ≤
      (∫⁻ x, a x ^ (3 : ℝ) ∂μ) ^ (2 / 5 : ℝ) *
        (∫⁻ x, b x ^ (2 : ℝ) ∂μ) ^ (3 / 5 : ℝ) := by
  have hconj : (5 / 2 : ℝ).HolderConjugate (5 / 3 : ℝ) :=
    ⟨by norm_num, by norm_num, by norm_num⟩
  have hmain := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj
    (ha.pow_const (6 / 5 : ℝ)) (hb.pow_const (6 / 5 : ℝ))
  have hA : ∀ x, (a x ^ (6 / 5 : ℝ)) ^ (5 / 2 : ℝ) = a x ^ (3 : ℝ) := by
    intro x
    rw [← ENNReal.rpow_mul]
    norm_num
  have hB : ∀ x, (b x ^ (6 / 5 : ℝ)) ^ (5 / 3 : ℝ) = b x ^ (2 : ℝ) := by
    intro x
    rw [← ENNReal.rpow_mul]
    norm_num
  simp only [hA, hB, Pi.mul_apply] at hmain
  refine le_trans (le_of_eq ?_) (hmain.trans_eq ?_)
  · exact lintegral_congr fun x => ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  · norm_num

/-- The three-term majorant of `eq:pressure-gradient-decomposition` has an explicit `6/5`
time mass built from the three slice integrals. -/
theorem slice_majorant_time_mass_le
    {J : Set ℝ} {M a d F : ℝ → ℝ≥0∞} {c₁ c₂ c₃ : ℝ≥0∞} {qq : ℝ}
    (ha : AEMeasurable a (volume.restrict J)) (hd : AEMeasurable d (volume.restrict J))
    (hF : AEMeasurable F (volume.restrict J)) (hq : 6 / 5 ≤ qq)
    (hM : ∀ᵐ s ∂volume.restrict J,
      M s ≤ c₁ * (a s * d s) + c₂ * a s ^ (2 : ℝ) + c₃ * F s)
    {Ea Ed Ef : ℝ≥0∞}
    (hEa : (∫⁻ s in J, a s ^ (3 : ℝ)) ≤ Ea)
    (hEd : (∫⁻ s in J, d s ^ (2 : ℝ)) ≤ Ed)
    (hEf : (∫⁻ s in J, F s ^ qq) ≤ Ef) :
    (∫⁻ s in J, M s ^ (6 / 5 : ℝ)) ≤
      4 * (c₁ ^ (6 / 5 : ℝ) * (Ea + Ed) +
        c₂ ^ (6 / 5 : ℝ) * (volume J + Ea) +
        c₃ ^ (6 / 5 : ℝ) * (volume J + Ef)) := by
  have h65 : (0 : ℝ) ≤ 6 / 5 := by norm_num
  set A : ℝ → ℝ≥0∞ := fun s => c₁ ^ (6 / 5 : ℝ) * (a s * d s) ^ (6 / 5 : ℝ) with hA
  set B : ℝ → ℝ≥0∞ := fun s => c₂ ^ (6 / 5 : ℝ) * (a s ^ (2 : ℝ)) ^ (6 / 5 : ℝ) with hB
  set C : ℝ → ℝ≥0∞ := fun s => c₃ ^ (6 / 5 : ℝ) * F s ^ (6 / 5 : ℝ) with hC
  have hmA : AEMeasurable A (volume.restrict J) := by
    rw [hA]; exact aemeasurable_const.mul ((ha.mul hd).pow_const _)
  have hmB : AEMeasurable B (volume.restrict J) := by
    rw [hB]; exact aemeasurable_const.mul ((ha.pow_const _).pow_const _)
  have hmC : AEMeasurable C (volume.restrict J) := by
    rw [hC]; exact aemeasurable_const.mul (hF.pow_const _)
  have hstep : (∫⁻ s in J, M s ^ (6 / 5 : ℝ)) ≤ ∫⁻ s in J, 4 * (A s + B s + C s) := by
    refine lintegral_mono_ae ?_
    filter_upwards [hM] with s hs
    refine (ENNReal.rpow_le_rpow hs h65).trans ?_
    refine (three_add_rpow_six_fifths_le _ _ _).trans (le_of_eq ?_)
    have e1 : (c₁ * (a s * d s)) ^ (6 / 5 : ℝ) = A s :=
      ENNReal.mul_rpow_of_nonneg _ _ h65
    have e2 : (c₂ * a s ^ (2 : ℝ)) ^ (6 / 5 : ℝ) = B s :=
      ENNReal.mul_rpow_of_nonneg _ _ h65
    have e3 : (c₃ * F s) ^ (6 / 5 : ℝ) = C s :=
      ENNReal.mul_rpow_of_nonneg _ _ h65
    rw [e1, e2, e3]
  refine hstep.trans ?_
  have hmAB : AEMeasurable (fun s => A s + B s) (volume.restrict J) := hmA.add hmB
  have hmABC : AEMeasurable (fun s => A s + B s + C s) (volume.restrict J) := hmAB.add hmC
  rw [lintegral_const_mul'' _ hmABC, lintegral_add_left' hmAB, lintegral_add_left' hmA]
  refine mul_le_mul' le_rfl (add_le_add (add_le_add ?_ ?_) ?_)
  · have hp : AEMeasurable (fun s => (a s * d s) ^ (6 / 5 : ℝ)) (volume.restrict J) :=
      (ha.mul hd).pow_const _
    rw [hA]
    simp only []
    rw [lintegral_const_mul'' _ hp]
    refine mul_le_mul' le_rfl ?_
    refine (lintegral_mul_six_fifths_le ha hd).trans ?_
    refine le_trans (mul_le_mul' (ENNReal.rpow_le_rpow hEa (by norm_num))
      (ENNReal.rpow_le_rpow hEd (by norm_num))) ?_
    have hy := rpow_mul_rpow_le_add Ea Ed (θ := (2 / 5 : ℝ)) (by norm_num) (by norm_num)
    norm_num at hy
    exact hy
  · have hp : AEMeasurable (fun s => (a s ^ (2 : ℝ)) ^ (6 / 5 : ℝ)) (volume.restrict J) :=
      (ha.pow_const _).pow_const _
    rw [hB]
    simp only []
    rw [lintegral_const_mul'' _ hp]
    refine mul_le_mul' le_rfl ?_
    have hpow : ∀ s : ℝ, (a s ^ (2 : ℝ)) ^ (6 / 5 : ℝ) = a s ^ (12 / 5 : ℝ) := by
      intro s
      rw [← ENNReal.rpow_mul]
      norm_num
    simp only [hpow]
    refine (lintegral_rpow_le_measure_add_lintegral_rpow (volume.restrict J) a
      (by norm_num : (0 : ℝ) ≤ 12 / 5) (by norm_num : (12 / 5 : ℝ) ≤ 3)).trans ?_
    rw [Measure.restrict_apply_univ]
    exact add_le_add le_rfl hEa
  · have hp : AEMeasurable (fun s => F s ^ (6 / 5 : ℝ)) (volume.restrict J) :=
      hF.pow_const _
    rw [hC]
    simp only []
    rw [lintegral_const_mul'' _ hp]
    refine mul_le_mul' le_rfl ?_
    refine (lintegral_rpow_le_measure_add_lintegral_rpow (volume.restrict J) F
      (by norm_num : (0 : ℝ) ≤ 6 / 5) hq).trans ?_
    rw [Measure.restrict_apply_univ]
    exact add_le_add le_rfl hEf

end CKN.Core.Step4
