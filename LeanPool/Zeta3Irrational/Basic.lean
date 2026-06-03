/-
Copyright (c) 2026 Junqi Liu, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jujian Zhang
-/

import Mathlib.Data.Int.Star
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.NumberTheory.Chebyshev
import LeanPool.Zeta3Irrational.Bound
import LeanPool.Zeta3Irrational.LegendrePoly
import LeanPool.Zeta3Irrational.LinearForm

/-!
# LeanPool.Zeta3Irrational.Basic
-/

namespace LeanPool.Zeta3Irrational

open scoped Nat
open BigOperators Polynomial

/-- The Apéry integral after inserting two shifted Legendre polynomials. -/
noncomputable abbrev JJ (n : ℕ) : ℝ :=
    ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    (-(x.1 * x.2).log / (1 - x.1 * x.2) *
      (shiftedLegendre n).eval x.1 * (shiftedLegendre n).eval x.2)

/-- The transformed three-variable form of the Apéry integral. -/
noncomputable abbrev JJ' (n : ℕ) : ℝ :=
    ∫ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    (x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) /
    (1 - (1 - x.2.1 * x.2.2) * x.1)) ^ n / (1 - (1 - x.2.1 * x.2.2) * x.1)

/-- The extended nonnegative integral associated to `JJ'`. -/
noncomputable abbrev JJENN (n : ℕ) : ENNReal :=
    ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1, ENNReal.ofReal
    ((x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) /
    (1 - (1 - x.2.1 * x.2.2) * x.1)) ^ n / (1 - (1 - x.2.1 * x.2.2) * x.1))

/-- The denominator-cleared Apéry linear form. -/
noncomputable abbrev fun1 (n : ℕ) : ℝ := (d (Finset.Icc 1 n)) ^ 3 * JJ n

theorem linear_int (n : ℕ) : ∃ a b : ℕ → ℤ,
    fun1 n =
      a n + b n * (d (Finset.Icc 1 n) : ℤ) ^ 3 *
        ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  delta fun1 JJ
  obtain ⟨c, hc⟩ := shiftedLegendre_eq_int_poly n
  simp_rw [hc, Polynomial.eval_finsetSum, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  simp only [eval_mul, eval_intCast, eval_pow, eval_X]
  simp_rw [← mul_assoc, multi_integral_sum_comm, multi_integral_mul_const]
  simp only [Finset.mul_sum]
  obtain ⟨qq', ⟨pp', hqq'⟩⟩ := linear_int_aux
  use fun n => ∑ x ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1),
    d (Finset.Icc 1 n) ^ 3 * c x * c i * qq' x i / d (Finset.Icc 1 (Nat.max x i)) ^ 3
  use fun n => ∑ x ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1), c x * c i * pp' x i
  rw [← Nat.cast_pow, ← Int.cast_pow , ← Int.cast_mul, Finset.sum_mul]
  simp only [Nat.cast_pow, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  specialize hqq' x y
  rw [hqq', mul_add, mul_add, add_comm]
  congr 1
  · rw [Int.cast_div]
    · rw [mul_div_assoc', ← mul_div_assoc, div_eq_div_iff]
      · norm_cast
        rw [← mul_assoc, ← mul_assoc]
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
        Nat.cast_eq_zero]
        apply d_ne_zero
        simp
      · simp only [Int.cast_pow, Int.cast_natCast, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        pow_eq_zero_iff, Nat.cast_eq_zero]
        apply d_ne_zero
        simp
    · rw [mul_assoc, mul_assoc]
      apply Dvd.dvd.mul_right
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, IsIntegrallyClosed.pow_dvd_pow_iff]
      norm_cast
      apply d_dvd_d_of_le
      simp_all only [Finset.mem_range, Finset.le_eq_subset]
      intro a b
      simp_all only [Finset.mem_Icc, true_and]
      simp only [le_max_iff] at b
      rcases b with ⟨_ ,(c | c)⟩
      <;>
      linarith
    · simp only [Int.cast_pow, Int.cast_natCast, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff, Nat.cast_eq_zero]
      apply d_ne_zero
      simp
  · ring

lemma pos_aux (x : ℝ × ℝ × ℝ)
    (hx : (0 < x.1 ∧ x.1 < 1) ∧ (0 < x.2.1 ∧ x.2.1 < 1) ∧
      0 < x.2.2 ∧ x.2.2 < 1) :
    0 < (1 - (1 - x.2.1 * x.2.2) * x.1) := by
  simp only [sub_pos]
  suffices (1 - x.2.1 * x.2.2) * x.1 < x.1 by linarith
  rw [mul_lt_iff_lt_one_left]
  · simp only [sub_lt_self_iff]
    nlinarith
  · nlinarith

lemma JJENN_upper (n : ℕ) : JJENN n ≤
    ENNReal.ofReal (2 * (1 / 24) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3) := by
  calc
  _ ≤ ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ENNReal.ofReal ((1 / 24) ^ n / (1 - (1 - x.2.1 * x.2.2) * x.1)) := by
    rw [JJENN, ← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
    apply MeasureTheory.lintegral_mono
    intro x
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
    · simp only [h, ↓reduceIte]
      simp only [Set.mem_prod, Set.mem_Ioo] at h
      apply ENNReal.ofReal_le_ofReal
      rw [div_le_div_iff_of_pos_right]
      · apply pow_le_pow_left₀
        · apply div_nonneg
          · apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg (by linarith) (by linarith)
          · linarith [pos_aux x h]
        · suffices x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) /
            (1 - (1 - x.2.1 * x.2.2) * x.1) < (1 / 24 : ℝ)by linarith
          apply bound' <;> linarith
      · exact pos_aux x h
    · simp only [h, ↓reduceIte, le_refl]
  _ = ENNReal.ofReal ((1 / 24) ^ n) *
      ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ENNReal.ofReal (1 / (1 - (1 - x.2.1 * x.2.2) * x.1)) := by
    rw [← MeasureTheory.lintegral_const_mul]
    · rw [← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
      congr
      ext x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases h : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [h, ↓reduceIte]
        rw [← ENNReal.ofReal_mul, ← mul_one_div]
        apply pow_nonneg (by norm_num)
      · simp only [h, ↓reduceIte]
    · apply Measurable.ennreal_ofReal
      apply Measurable.const_div
      apply Measurable.const_sub
      apply Measurable.mul _ measurable_fst
      apply Measurable.const_sub
      apply Measurable.mul
      · exact Measurable.fun_comp measurable_fst measurable_snd
      · exact Measurable.fun_comp measurable_snd measurable_snd
  _ = ENNReal.ofReal (2 * (1 / 24) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3) := by
    have h := JENN_eq_triple 0 0
    simp only [pow_zero, mul_one] at h
    rw [← h, J_ENN_rr]
    simp only [one_div, inv_pow, zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, mul_zero,
      sub_zero]
    rw [← ENNReal.ofReal_mul (by norm_num), ← mul_assoc]
    nth_rw 2 [mul_comm]

lemma integrableOn_JJ' (n : ℕ) : MeasureTheory.Integrable (fun (x : ℝ × ℝ × ℝ) ↦
    (x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) /
      (1 - (1 - x.2.1 * x.2.2) * x.1)) ^ n /
    (1 - (1 - x.2.1 * x.2.2) * x.1))
    (MeasureTheory.volume.restrict (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1)) := by
  rw [MeasureTheory.Integrable]
  constructor
  · apply AEMeasurable.aestronglyMeasurable
    measurability
  · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    set k := _
    change k < ⊤
    have : k = JJENN n := by
      simp only [k, JJENN]
      rw [← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
      congr
      ext x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [hx, ↓reduceIte, norm_mul, norm_div, Real.norm_eq_abs, norm_pow]
        simp only [Set.mem_prod, Set.mem_Ioo] at hx
        rw [ENNReal.ofReal_eq_ofReal_iff]
        · congr 3
          · rw [abs_eq_self.2, abs_eq_self.2, abs_eq_self.2, abs_eq_self.2, abs_eq_self.2,
              abs_eq_self.2] <;> nlinarith
          · simp only [abs_eq_self, sub_nonneg]
            apply mul_le_one₀ (by nlinarith) (by linarith) (by linarith)
          · simp only [abs_eq_self, sub_nonneg]
            apply mul_le_one₀ (by nlinarith) (by linarith) (by linarith)
        · positivity
        · apply div_nonneg
          · apply pow_nonneg
            apply div_nonneg
            · apply mul_nonneg _ (by linarith)
              apply mul_nonneg _ (by linarith)
              apply mul_nonneg _ (by linarith)
              apply mul_nonneg _ (by linarith)
              apply mul_nonneg (by linarith) (by linarith)
            · linarith [pos_aux x hx]
          · linarith [pos_aux x hx]
      · simp only [hx, ↓reduceIte]
    rw [this]
    apply LE.le.trans_lt (JJENN_upper n)
    simp only [one_div, inv_pow, ENNReal.ofReal_lt_top]

lemma shiftedLegendre_bound (n : ℕ) (x : ℝ) (hx : 0 < x ∧ x < 1) :
  |eval x (shiftedLegendre n)| ≤
    ∑ x_1 ∈ Finset.range (n + 1), (n.choose x_1 : ℝ) * ((n + x_1).choose n) := by
  simp only [shiftedLegendre_eq_sum, map_pow, map_neg, map_one, eval_finsetSum,
    eval_mul, eval_pow, eval_neg, eval_one, eval_natCast, eval_X]
  have := Finset.abs_sum_le_sum_abs
    (f := fun y => (-1) ^ y * ↑(n.choose y) * ↑((n + y).choose n) * x ^ y)
    (s := Finset.range (n + 1))
  trans
  · apply this
  · apply Finset.sum_le_sum
    intro i _
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast, one_mul]
    trans ↑(n.choose i) * ↑((n + i).choose n) * 1
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply pow_le_one₀
      · simp
      · rw [abs_eq_self.2 (by linarith)]
        linarith
    · simp

lemma Measurable_one_div_aux :
    Measurable fun (x : ℝ × ℝ × ℝ) ↦
      ENNReal.ofReal (1 / (1 - (1 - x.2.1 * x.2.2) * x.1)) := by
  apply Measurable.ennreal_ofReal
  apply Measurable.const_div
  apply Measurable.const_sub
  apply Measurable.mul _ measurable_fst
  apply Measurable.const_sub
  apply Measurable.mul
  · exact Measurable.fun_comp measurable_fst measurable_snd
  · exact Measurable.fun_comp measurable_snd measurable_snd

lemma integrableOn_JJ1 (n : ℕ) : MeasureTheory.Integrable
  (Function.uncurry fun z x ↦
    eval x.1 (shiftedLegendre n) * eval x.2 (shiftedLegendre n) *
      (1 / (1 - (1 - x.1 * x.2) * z)))
  ((MeasureTheory.volume.restrict (Set.Ioo 0 1)).prod
    (MeasureTheory.volume.restrict (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1))) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.Integrable]
  constructor
  · apply AEMeasurable.aestronglyMeasurable
    measurability
  · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    set k := _
    set C := ∑ x_1 ∈ Finset.range (n + 1), (n.choose x_1 : ℝ) * ((n + x_1).choose n)
    change k < ⊤
    have : k ≤ ENNReal.ofReal (C ^ 2) *
        ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ENNReal.ofReal (1 / (1 - (1 - x.2.1 * x.2.2) * x.1)) := by
      simp only [k]
      rw [← MeasureTheory.lintegral_const_mul _ Measurable_one_div_aux]
      rw [← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
      apply MeasureTheory.lintegral_mono
      intro x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [hx, ↓reduceIte, Real.norm_eq_abs]
        simp only [Set.mem_prod, Set.mem_Ioo] at hx
        rw [← ENNReal.ofReal_mul]
        · rw [ENNReal.ofReal_le_ofReal_iff]
          · rw [Function.uncurry_apply_pair, mul_one_div, mul_one_div, abs_div, div_le_div_iff₀]
            · apply mul_le_mul _ _ (by linarith [pos_aux x hx]) (by positivity)
              · rw [abs_mul, pow_two]
                apply mul_le_mul _ _ (by positivity) (by positivity)
                · apply shiftedLegendre_bound _ _ hx.2.1
                · apply shiftedLegendre_bound _ _ hx.2.2
              · exact le_abs_self (1 - (1 - x.2.1 * x.2.2) * x.1)
            · simp only [abs_pos]; linarith [pos_aux x hx]
            · exact pos_aux x hx
          · rw [mul_one_div]
            apply div_nonneg (by positivity)
            linarith [pos_aux x hx]
        · positivity
      · simp [hx]
    apply LE.le.trans_lt this
    have h := JENN_eq_triple 0 0
    simp only [pow_zero, mul_one] at h
    rw [← h, J_ENN_rr, ← ENNReal.ofReal_mul]
    · exact ENNReal.ofReal_lt_top
    · positivity

lemma integrableOn_JJ2 (n : ℕ) : MeasureTheory.Integrable (Function.uncurry fun z x ↦
  eval x.1 (shiftedLegendre n) * (x.1 * x.2 * z) ^ n * (1 - x.2) ^ n /
    (1 - (1 - x.1 * x.2) * z) ^ (n + 1))
  ((MeasureTheory.volume.restrict (Set.Ioo 0 1)).prod
    (MeasureTheory.volume.restrict (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1))) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.Integrable]
  constructor
  · apply AEMeasurable.aestronglyMeasurable
    measurability
  · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    set k := _
    set C := ∑ x_1 ∈ Finset.range (n + 1), (n.choose x_1 : ℝ) * ((n + x_1).choose n)
    change k < ⊤
    have : k ≤ ENNReal.ofReal (|C|) *
        ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ENNReal.ofReal (1 / (1 - (1 - x.2.1 * x.2.2) * x.1)) := by
      simp only [k]
      rw [← MeasureTheory.lintegral_const_mul _ Measurable_one_div_aux]
      rw [← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
      apply MeasureTheory.lintegral_mono
      intro x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [hx, ↓reduceIte, Real.norm_eq_abs]
        simp only [Set.mem_prod, Set.mem_Ioo] at hx
        rw [← ENNReal.ofReal_mul]
        · rw [ENNReal.ofReal_le_ofReal_iff]
          · rw [Function.uncurry_apply_pair, pow_add, ← div_div, abs_div, mul_one_div,
              div_le_div_iff₀]
            · apply mul_le_mul _ _ (by linarith [pos_aux x hx]) (by positivity)
              · rw [← mul_div, mul_assoc, abs_mul, ← mul_one (a := |C|)]
                apply mul_le_mul _ _ (by positivity) (by positivity)
                · suffices |C| = C by
                    rw [this]
                    apply shiftedLegendre_bound _ _ hx.2.1
                  rw [abs_eq_self]
                  positivity
                · rcases x with ⟨x, ⟨y, z⟩⟩
                  simp only at hx ⊢
                  rcases hx with ⟨⟨hx0, hx1⟩, ⟨hy0, _⟩, ⟨hz0, hz1⟩⟩
                  rw [← div_pow, ← mul_pow, abs_pow]
                  suffices ineq1 : |y * z * x * ((1 - z) / (1 - (1 - y * z) * x))| ≤ 1 from
                    pow_le_one₀ (abs_nonneg _) ineq1
                  rw [show (1 - (1 - y * z) * x) = 1 - x + y * z * x by ring]
                  by_cases ineq : 1 - x + y * z * x = 0
                  · rw [ineq]
                    simp only [div_zero, mul_zero, abs_zero, zero_le_one]
                  · rw [
                    show y * z * x * ((1 - z) / (1 - x + y * z * x)) = (1-z)/((1-x)/(y*z*x) + 1) by
                      rw [mul_div, div_eq_div_iff]
                      · rw [mul_comm _ (1 - z), mul_assoc _ (y * z * x), mul_add,
                          mul_div_cancel₀]
                        · ring
                        · apply mul_ne_zero
                          · apply mul_ne_zero
                            · linarith
                            · linarith
                          · linarith
                      · exact ineq
                      · rw [div_add_one]
                        · intro r
                          rw [_root_.div_eq_zero_iff] at r
                          · refine ineq <| r.resolve_right ?_
                            apply mul_ne_zero
                            · apply mul_ne_zero <;> linarith
                            · linarith
                        · apply mul_ne_zero
                          · apply mul_ne_zero <;> linarith
                          · linarith, abs_div]
                    trans |1 - z|
                    · apply div_le_self (abs_nonneg _)
                      rw [abs_of_nonneg, le_add_iff_nonneg_left]
                      · apply div_nonneg
                        · linarith
                        · apply mul_nonneg
                          · apply mul_nonneg <;> linarith
                          · linarith
                      · apply add_nonneg
                        · apply div_nonneg
                          · linarith
                          · apply mul_nonneg
                            · apply mul_nonneg <;> linarith
                            · linarith
                        · linarith
                    rw [abs_le]
                    exact ⟨by linarith, by linarith⟩
              · simp only [pow_one]
                exact le_abs_self (1 - (1 - x.2.1 * x.2.2) * x.1)
            · simp only [abs_pos]; linarith [pos_aux x hx]
            · exact pos_aux x hx
          · rw [mul_one_div]
            apply div_nonneg (by positivity)
            linarith [pos_aux x hx]
        · positivity
      · simp [hx]
    apply LE.le.trans_lt this
    have h := JENN_eq_triple 0 0
    simp only [pow_zero, mul_one] at h
    rw [← h, J_ENN_rr, ← ENNReal.ofReal_mul]
    · exact ENNReal.ofReal_lt_top
    · positivity

lemma integrableOn_JJ3 (n : ℕ) : MeasureTheory.Integrable
  (Function.uncurry fun z x ↦
    eval x.1 (shiftedLegendre n) * (1 - z) ^ n * (1 - x.2) ^ n /
      (1 - (1 - x.1 * x.2) * z))
  ((MeasureTheory.volume.restrict (Set.Ioo 0 1)).prod
    (MeasureTheory.volume.restrict (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1))) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.Integrable]
  constructor
  · apply AEMeasurable.aestronglyMeasurable
    measurability
  · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    set k := _
    set C := ∑ x_1 ∈ Finset.range (n + 1), (n.choose x_1 : ℝ) * ((n + x_1).choose n)
    change k < ⊤
    have : k ≤
        ENNReal.ofReal (|C|) *
          ∫⁻ (x : ℝ × ℝ × ℝ) in
            Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
            ENNReal.ofReal (1 / (1 - (1 - x.2.1 * x.2.2) * x.1)) := by
      simp only [k]
      rw [← MeasureTheory.lintegral_const_mul _ Measurable_one_div_aux]
      rw [← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
      apply MeasureTheory.lintegral_mono
      intro x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [hx, ↓reduceIte, Real.norm_eq_abs]
        simp only [Set.mem_prod, Set.mem_Ioo] at hx
        rw [← ENNReal.ofReal_mul]
        · rw [ENNReal.ofReal_le_ofReal_iff]
          · rw [Function.uncurry_apply_pair, mul_one_div, abs_div, div_le_div_iff₀]
            · apply mul_le_mul _ _ (by linarith [pos_aux x hx]) (by positivity)
              · rw [abs_mul, ← mul_one (a := |C|)]
                apply mul_le_mul _ _ (by positivity) (by positivity)
                · rw [abs_mul, ← mul_one (a := |C|)]
                  apply mul_le_mul _ _ (by positivity) (by positivity)
                  · suffices |C| = C by
                      rw [this]
                      apply shiftedLegendre_bound _ _ hx.2.1
                    rw [abs_eq_self]
                    positivity
                  · simp only [abs_pow]
                    apply pow_le_one₀
                    · simp only [abs_nonneg]
                    · rw [abs_eq_self.2 (by linarith)]
                      linarith
                · simp only [abs_pow]
                  apply pow_le_one₀
                  · simp only [abs_nonneg]
                  · rw [abs_eq_self.2 (by linarith)]
                    linarith
              · exact le_abs_self (1 - (1 - x.2.1 * x.2.2) * x.1)
            · simp only [abs_pos]; linarith [pos_aux x hx]
            · exact pos_aux x hx
          · rw [mul_one_div]
            apply div_nonneg (by positivity)
            linarith [pos_aux x hx]
        · positivity
      · simp [hx]
    apply LE.le.trans_lt this
    have h := JENN_eq_triple 0 0
    simp only [pow_zero, mul_one] at h
    rw [← h, J_ENN_rr, ← ENNReal.ofReal_mul]
    · exact ENNReal.ofReal_lt_top
    · positivity

lemma eq1_integrableOn_aux1 (n : ℕ) (z : ℝ) (hz : z ∈ Set.Ioo 0 1) :
    MeasureTheory.Integrable
      (fun x ↦
        eval x.1 (shiftedLegendre n) * eval x.2 (shiftedLegendre n) *
          (1 / (1 - (1 - x.1 * x.2) * z)))
      ((MeasureTheory.volume.restrict (Set.Ioo 0 1)).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 1))) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
  apply MeasureTheory.IntegrableOn.integrable
  apply MeasureTheory.IntegrableOn.mono_set (t := Set.Icc 0 1 ×ˢ Set.Icc 0 1)
  · apply ContinuousOn.integrableOn_compact
    · simp only [Set.Icc_prod_Icc, Prod.mk_zero_zero, Prod.mk_one_one, isCompact_Icc]
    · simp only [shiftedLegendre_eq_sum, map_pow, map_neg, map_one]
      apply ContinuousOn.mul
      · apply ContinuousOn.mul
        · simp only [eval_finsetSum, eval_mul, eval_pow, eval_neg, eval_one, eval_natCast, eval_X]
          apply continuousOn_finsetSum
          intro i _
          apply ContinuousOn.mul continuousOn_const
          apply ContinuousOn.pow continuousOn_fst
        · simp only [eval_finsetSum, eval_mul, eval_pow, eval_neg, eval_one, eval_natCast, eval_X]
          apply continuousOn_finsetSum
          intro i _
          apply ContinuousOn.mul continuousOn_const
          apply ContinuousOn.pow continuousOn_snd
      · apply ContinuousOn.div continuousOn_const
        · apply ContinuousOn.sub continuousOn_const
          apply ContinuousOn.mul _ continuousOn_const
          apply ContinuousOn.sub continuousOn_const
          apply ContinuousOn.mul continuousOn_fst continuousOn_snd
        · intro x hx
          suffices 1 - (1 - x.1 * x.2) * z > 0 by linarith
          simp only [Set.mem_prod, Set.mem_Icc] at hx
          simp only [Set.mem_Ioo, gt_iff_lt, sub_pos] at hz ⊢
          suffices (1 - x.1 * x.2) * z ≤ z by linarith
          apply mul_le_of_le_one_left (by linarith)
          simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
          nlinarith
  · apply Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self

lemma eq1_integrableOn_aux2 (n : ℕ) (z : ℝ) (hz : z ∈ Set.Ioo 0 1) :
    MeasureTheory.Integrable
      (fun x ↦
        eval x.1 (shiftedLegendre n) * (x.1 * x.2 * z) ^ n * (1 - x.2) ^ n /
          (1 - (1 - x.1 * x.2) * z) ^ (n + 1))
      ((MeasureTheory.volume.restrict (Set.Ioo 0 1)).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 1))) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
  apply MeasureTheory.IntegrableOn.integrable
  apply MeasureTheory.IntegrableOn.mono_set (t := Set.Icc 0 1 ×ˢ Set.Icc 0 1)
  · apply ContinuousOn.integrableOn_compact
    · simp only [Set.Icc_prod_Icc, Prod.mk_zero_zero, Prod.mk_one_one, isCompact_Icc]
    · simp only [shiftedLegendre_eq_sum, map_pow, map_neg, map_one]
      apply ContinuousOn.div
      · apply ContinuousOn.mul
        · apply ContinuousOn.mul
          · simp only [eval_finsetSum, eval_mul, eval_pow, eval_neg, eval_one,
              eval_natCast, eval_X]
            apply continuousOn_finsetSum
            intro i _
            apply ContinuousOn.mul continuousOn_const
            apply ContinuousOn.pow continuousOn_fst
          · apply ContinuousOn.pow
            apply ContinuousOn.mul _ continuousOn_const
            apply ContinuousOn.mul continuousOn_fst continuousOn_snd
        · apply ContinuousOn.pow
          apply ContinuousOn.sub continuousOn_const continuousOn_snd
      · apply ContinuousOn.pow
        apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.mul _ continuousOn_const
        apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.mul continuousOn_fst continuousOn_snd
      · intro x hx
        suffices 1 - (1 - x.1 * x.2) * z > 0 by positivity
        simp only [Set.mem_prod, Set.mem_Icc] at hx
        simp only [Set.mem_Ioo, gt_iff_lt, sub_pos] at hz ⊢
        suffices (1 - x.1 * x.2) * z ≤ z by linarith
        apply mul_le_of_le_one_left (by linarith)
        simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
        nlinarith
  · apply Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self

lemma double_integral_eq1 (n : ℕ) (z : ℝ) (hz : z ∈ Set.Ioo 0 1) :
    ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      eval x.1 (shiftedLegendre n) * eval x.2 (shiftedLegendre n) *
        (1 / (1 - (1 - x.1 * x.2) * z)) =
    ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      eval x.1 (shiftedLegendre n) * (x.1 * x.2 * z) ^ n * (1 - x.2) ^ n /
        (1 - (1 - x.1 * x.2) * z) ^ (n + 1) := by
  calc
  _ = ∫ (x : ℝ) in Set.Ioo 0 1, eval x (shiftedLegendre n) * ∫ (y : ℝ) in Set.Ioo 0 1,
     eval y (shiftedLegendre n) * (1 / (1 - (1 - x * y) * z)) := by
    rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
        MeasureTheory.integral_prod]
    · apply MeasureTheory.setIntegral_congr_fun (by measurability)
      intro x _
      simp only
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num),
        ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num),
        ← intervalIntegral.integral_const_mul]
      simp only [one_div, ← mul_assoc]
    · exact eq1_integrableOn_aux1 n z hz
  _ = ∫ (x : ℝ) in Set.Ioo 0 1, eval x (shiftedLegendre n) * ∫ (y : ℝ) in Set.Ioo 0 1,
    (x * y * z) ^ n * (1 - y) ^ n / (1 - (1 - x * y) * z) ^ (n + 1) := by
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro x hx
    simp only
    congr 1
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num),
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num)]
    rw [legendre_integral_special n hx hz]
  _ = ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    eval x.1 (shiftedLegendre n) * (x.1 * x.2 * z) ^ n * (1 - x.2) ^ n /
      (1 - (1 - x.1 * x.2) * z) ^ (n + 1) := by
    rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
        MeasureTheory.integral_prod]
    · apply MeasureTheory.setIntegral_congr_fun (by measurability)
      intro x _
      simp only
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num),
        ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num),
        ← intervalIntegral.integral_const_mul]
      simp only [mul_div, ← mul_assoc]
    · exact eq1_integrableOn_aux2 n z hz

lemma ineq_aux (x : ℝ × ℝ) (z : ℝ)
    (hx : (0 < x.1 ∧ x.1 < 1) ∧ 0 < x.2 ∧ x.2 < 1) (hz : 0 ≤ z ∧ z ≤ 1) :
    0 ≤ (1 - z) / (1 - (1 - x.1 * x.2) * z) ∧
      (1 - z) / (1 - (1 - x.1 * x.2) * z) ≤ 1 := by
  constructor
  · apply div_nonneg (by linarith)
    simp only [sub_nonneg]
    apply mul_le_one₀ _ (by linarith) (by linarith)
    simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
    nlinarith
  · rw [div_le_iff₀]
    · simp only [one_mul, tsub_le_iff_right, sub_add, le_sub_self_iff, zero_add]
      by_cases h0 : z = 0
      · simp [h0]
      · suffices (1 - x.1 * x.2) * z < z by linarith
        rw [mul_lt_iff_lt_one_left]
        · simp only [sub_lt_self_iff]; nlinarith
        · by_contra!
          have : z = 0 := by linarith
          exact h0 this
    · simp only [sub_pos]
      rw [mul_comm]
      suffices z * (1 - x.1 * x.2) ≤ (1 - x.1 * x.2) by nlinarith
      apply mul_le_of_le_one_left (by nlinarith) hz.2

lemma ineq_aux1 (x : ℝ × ℝ) (z : ℝ)
    (hx : (0 < x.1 ∧ x.1 < 1) ∧ 0 < x.2 ∧ x.2 < 1) (hz : 0 ≤ z ∧ z ≤ 1) :
    1 - (1 - x.1 * x.2) * z ≠ 0 := by
  suffices (1 - x.1 * x.2) * z < 1 by linarith
  rw [mul_comm]
  suffices z * (1 - x.1 * x.2) ≤ (1 - x.1 * x.2) by nlinarith
  apply mul_le_of_le_one_left (by nlinarith) hz.2

lemma fun_eq_aux (x : ℝ × ℝ) (y : ℝ)
    (hx : (0 < x.1 ∧ x.1 < 1) ∧ 0 < x.2 ∧ x.2 < 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    deriv (fun z => (1 - z) / (1 - (1 - x.1 * x.2) * z)) y =
    (fun z => - x.1 * x.2 / (1 - (1 - x.1 * x.2) * z) ^ 2) y := by
  rw [deriv_fun_div]
  · rw [deriv_const_sub, deriv_const_sub, deriv_const_mul _ differentiableAt_id]
    simp only [deriv_id'', neg_mul, one_mul, neg_sub, mul_one]
    congr
    ring
  · apply DifferentiableAt.const_sub differentiableAt_id _
  · apply DifferentiableAt.const_sub (DifferentiableAt.const_mul differentiableAt_id _)
  · exact ineq_aux1 x y hx hy

lemma double_integral_eq2 (n : ℕ) (x : ℝ × ℝ)
    (hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) :
    ∫ (z : ℝ) in Set.Ioo 0 1,
      eval x.1 (shiftedLegendre n) * (x.1 * x.2 * z) ^ n * (1 - x.2) ^ n /
        (1 - (1 - x.1 * x.2) * z) ^ (n + 1) =
    ∫ (z : ℝ) in Set.Ioo 0 1,
      eval x.1 (shiftedLegendre n) * (1 - z) ^ n * (1 - x.2) ^ n /
        (1 - (1 - x.1 * x.2) * z) := by
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num),
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num)]
  simp only [← mul_div, mul_assoc]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  congr 1
  simp only [mul_div, ← mul_assoc]
  simp_rw [mul_comm (b := (1 - x.2) ^ n), ← mul_div]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  congr 1
  set g := fun z => (1 - z) / (1 - (1 - x.1 * x.2) * z)
  set g' := fun z => - x.1 * x.2 / (1 - (1 - x.1 * x.2) * z) ^ 2
  have hg : ContinuousOn (deriv g) (Set.uIcc 0 1) := by
    rw [continuousOn_congr (f := g')]
    · simp only [g']
      apply ContinuousOn.div continuousOn_const
      · apply ContinuousOn.pow
        apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.mul continuousOn_const continuousOn_id
      · intro y hy
        simp only [Set.mem_prod, Set.mem_Ioo, zero_le_one, Set.uIcc_of_le,
          Set.mem_Icc] at hx hy ⊢
        apply pow_ne_zero
        exact ineq_aux1 x y hx hy
    · intro y hy
      simp only [Set.mem_prod, Set.mem_Ioo, zero_le_one, Set.uIcc_of_le, Set.mem_Icc] at hx hy
      exact fun_eq_aux x y hx hy
  simp only [Set.mem_prod, Set.mem_Ioo] at hx
  symm
  calc
  _ = -∫ (y : ℝ) in (g 0)..g 1, (1 - y) ^ n / (1 - (1 - x.1 * x.2) * y) := by
    simp only [sub_zero, mul_zero, ne_eq, one_ne_zero, not_false_eq_true, div_self, sub_self,
      mul_one, sub_sub_cancel, zero_div, g]
    rw [intervalIntegral.integral_symm]
  _ = -∫ (y : ℝ) in (0)..1, (deriv g) y * (1 - g y) ^ n / (1 - (1 - x.1 * x.2) * g y) := by
    rw [neg_inj, ← intervalIntegral.integral_comp_mul_deriv' (f' := deriv g) (h' := hg)]
    · simp only [Function.comp_apply, div_mul_eq_mul_div, mul_comm]
    · intro y hy
      simp only [hasDerivAt_deriv_iff, g]
      apply DifferentiableAt.div (DifferentiableAt.const_sub differentiableAt_id _)
      · apply DifferentiableAt.const_sub (DifferentiableAt.const_mul differentiableAt_id _)
      · simp only [zero_le_one, Set.uIcc_of_le, Set.mem_Icc] at hy
        exact ineq_aux1 x y hx hy
    · have h1 : g '' Set.uIcc 0 1 = Set.Icc 0 1 := by
        simp only [zero_le_one, Set.uIcc_of_le, g]
        ext y
        constructor
        · intro hy
          simp only [Set.mem_image, Set.mem_Icc] at hy
          obtain ⟨z, hz, hz'⟩ := hy
          simp only [Set.mem_Icc]
          rw [← hz']
          exact ineq_aux x z hx hz
        · intro hy
          simp only [Set.mem_Icc] at hy
          simp only [Set.mem_image, Set.mem_Icc]
          use (1 - y) / (1 - (1 - x.1 * x.2) * y)
          constructor
          · exact ineq_aux x y hx hy
          · have eq1 :
                ((1 - (1 - x.1 * x.2) * y) - (1 - y)) /
                  (1 - (1 - x.1 * x.2) * y) =
                1 - (1 - y) / (1 - (1 - x.1 * x.2) * y) := by
                rw [sub_div, div_self (ineq_aux1 x y hx hy)]
            have eq2 : ((1 - (1 - x.1 * x.2) * y) - (1 - x.1 * x.2) * (1 - y)) /
                (1 - (1 - x.1 * x.2) * y) =
              1 - (1 - x.1 * x.2) * ((1 - y) /
                (1 - (1 - x.1 * x.2) * y)) := by
              rw [sub_div, div_self (ineq_aux1 x y hx hy), mul_div]
            rw [div_eq_iff]
            · rw [← eq1, ← eq2, mul_div,
                div_eq_div_iff (ineq_aux1 x y hx hy) (ineq_aux1 x y hx hy)]
              ring
            · rw [← eq2]
              apply div_ne_zero _ (ineq_aux1 x y hx hy)
              rw [mul_sub]
              simp only [mul_one, sub_sub_sub_cancel_right, sub_sub_cancel, ne_eq, mul_eq_zero,
                not_or]
              constructor <;> linarith
      rw [h1]
      apply ContinuousOn.div
      · apply ContinuousOn.pow
        apply ContinuousOn.sub continuousOn_const continuousOn_id
      · apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.mul continuousOn_const continuousOn_id
      · intro y hy
        simp only [Set.mem_Icc] at hy
        exact ineq_aux1 x y hx hy
  _ = ∫ (y : ℝ) in (0)..1,
    x.1 * x.2 / (1 - (1 - x.1 * x.2) * y) ^ 2 * (1 - g y) ^ n /
      (1 - (1 - x.1 * x.2) * g y) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro y hy
    simp only [zero_le_one, Set.uIcc_of_le, Set.mem_Icc] at hy ⊢
    simp only [g]
    rw [fun_eq_aux x y hx hy]
    simp [neg_div]
  _ = ∫ (y : ℝ) in (0)..1, (x.1 * x.2 * y) ^ n / (1 - (1 - x.1 * x.2) * y) ^ (n + 1) := by
    apply intervalIntegral.integral_congr
    intro y hy
    simp only [zero_le_one, Set.uIcc_of_le, Set.mem_Icc] at hy ⊢
    have eq1 : ((1 - (1 - x.1 * x.2) * y) - (1 - y)) / (1 - (1 - x.1 * x.2) * y) =
        1 - (1 - y) / (1 - (1 - x.1 * x.2) * y) := by
        rw [sub_div, div_self (ineq_aux1 x y hx hy)]
    have eq2 : ((1 - (1 - x.1 * x.2) * y) - (1 - x.1 * x.2) * (1 - y)) /
      (1 - (1 - x.1 * x.2) * y) = 1 - (1 - x.1 * x.2) * ((1 - y) / (1 - (1 - x.1 * x.2) * y)) := by
      rw [sub_div, div_self (ineq_aux1 x y hx hy), mul_div]
    rw [div_mul_eq_mul_div, div_div, div_eq_div_iff]
    · simp only [← eq1, sub_sub_sub_cancel_left, div_pow, ← eq2, g]
      rw [mul_div, mul_comm, mul_div, mul_div, mul_div, div_eq_div_iff]
      · ring
      · apply pow_ne_zero
        exact ineq_aux1 x y hx hy
      · exact ineq_aux1 x y hx hy
    · apply mul_ne_zero
      · apply pow_ne_zero
        exact ineq_aux1 x y hx hy
      · simp only [g, ← eq2]
        apply div_ne_zero _ (ineq_aux1 x y hx hy)
        rw [mul_sub]
        simp only [mul_one, sub_sub_sub_cancel_right, sub_sub_cancel, ne_eq, mul_eq_zero,
          not_or]
        constructor <;> linarith
    · apply pow_ne_zero
      exact ineq_aux1 x y hx hy

lemma eq3_integrableOn_aux (n : ℕ) (z : ℝ) (hz : z ∈ Set.Ioo 0 1) :
    MeasureTheory.Integrable
      (fun x ↦
        eval x.1 (shiftedLegendre n) * (1 - x.2) ^ n /
          (1 - (1 - x.1 * x.2) * z))
      ((MeasureTheory.volume.restrict (Set.Ioo 0 1)).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 1))) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
  apply MeasureTheory.IntegrableOn.integrable
  apply MeasureTheory.IntegrableOn.mono_set (t := Set.Icc 0 1 ×ˢ Set.Icc 0 1)
  · apply ContinuousOn.integrableOn_compact
    · simp only [Set.Icc_prod_Icc, Prod.mk_zero_zero, Prod.mk_one_one, isCompact_Icc]
    · simp only [shiftedLegendre_eq_sum, map_pow, map_neg, map_one]
      apply ContinuousOn.div
      · apply ContinuousOn.mul
        · simp only [eval_finsetSum, eval_mul, eval_pow, eval_neg, eval_one,
            eval_natCast, eval_X]
          apply continuousOn_finsetSum
          intro i _
          apply ContinuousOn.mul continuousOn_const
          apply ContinuousOn.pow continuousOn_fst
        · apply ContinuousOn.pow (ContinuousOn.sub continuousOn_const continuousOn_snd)
      · apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.mul _ continuousOn_const
        apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.mul continuousOn_fst continuousOn_snd
      · intro x hx
        suffices 1 - (1 - x.1 * x.2) * z > 0 by linarith
        simp only [Set.mem_prod, Set.mem_Icc] at hx
        simp only [Set.mem_Ioo, gt_iff_lt, sub_pos] at hz ⊢
        suffices (1 - x.1 * x.2) * z ≤ z by linarith
        apply mul_le_of_le_one_left (by linarith)
        simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
        nlinarith
  · apply Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self

lemma double_integral_eq3 (n : ℕ) (z : ℝ) (hz : z ∈ Set.Ioo 0 1) :
    ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      (x.1 * x.2 * z * (1 - x.1) * (1 - x.2)) ^ n /
        (1 - (1 - x.1 * x.2) * z) ^ (n + 1) =
    ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      eval x.1 (shiftedLegendre n) * (1 - x.2) ^ n /
        (1 - (1 - x.1 * x.2) * z) := by
  symm
  rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
      MeasureTheory.integral_prod, MeasureTheory.integral_integral_swap]
  · rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
    simp only
    calc
    _ = ∫ (y : ℝ) in Set.Ioo 0 1, (1 - y) ^ n * ∫ (x : ℝ) in Set.Ioo 0 1,
      eval x (shiftedLegendre n) / (1 - (1 - x * y) * z) := by
      apply MeasureTheory.setIntegral_congr_fun (by measurability)
      intro y hy
      simp only [Set.mem_Ioo] at hy ⊢
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num),
        ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num),
        ← intervalIntegral.integral_const_mul]
      simp [mul_div, mul_comm]
    _ = ∫ (y : ℝ) in Set.Ioo 0 1, (1 - y) ^ n *
        ∫ (x : ℝ) in (0)..1,
          (y * x * z) ^ n * (1 - x) ^ n /
            (1 - (1 - y * x) * z) ^ (n + 1) := by
      apply MeasureTheory.setIntegral_congr_fun (by measurability)
      intro y hy
      simp only
      congr 1
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num)]
      have := legendre_integral_special n hy hz
      simp only [mul_one_div] at this
      simp only [← this]
      simp only [mul_comm]
    _ = ∫ (y : ℝ) in Set.Ioo 0 1, ∫ (x : ℝ) in Set.Ioo 0 1,
      (1 - y) ^ n * (y * x * z) ^ n * (1 - x) ^ n /
        (1 - (1 - y * x) * z) ^ (n + 1) := by
      apply MeasureTheory.setIntegral_congr_fun (by measurability)
      intro y _
      simp only
      rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le (by norm_num),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
      simp_rw [mul_div, ← mul_assoc]
    _ = ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      (x.1 * x.2 * z * (1 - x.1) * (1 - x.2)) ^ n / (1 - (1 - x.1 * x.2) * z) ^ (n + 1) := by
      rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
        MeasureTheory.integral_prod]
      · simp [mul_pow, mul_comm]
      · rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
        apply MeasureTheory.IntegrableOn.integrable
        apply MeasureTheory.IntegrableOn.mono_set (t := Set.Icc 0 1 ×ˢ Set.Icc 0 1)
        · apply ContinuousOn.integrableOn_compact
          · simp only [Set.Icc_prod_Icc, Prod.mk_zero_zero, Prod.mk_one_one, isCompact_Icc]
          · apply ContinuousOn.div
            · apply ContinuousOn.pow
              apply ContinuousOn.mul _ (ContinuousOn.sub continuousOn_const continuousOn_snd)
              apply ContinuousOn.mul _ (ContinuousOn.sub continuousOn_const continuousOn_fst)
              apply ContinuousOn.mul _ continuousOn_const
              apply ContinuousOn.mul continuousOn_fst continuousOn_snd
            · apply ContinuousOn.pow
              apply ContinuousOn.sub continuousOn_const _
              apply ContinuousOn.mul _ continuousOn_const
              apply ContinuousOn.sub continuousOn_const _
              apply ContinuousOn.mul continuousOn_fst continuousOn_snd
            · intro x hx
              simp only [Set.mem_prod, Set.mem_Icc, Set.mem_Ioo] at hx hz
              apply pow_ne_zero
              suffices (1 - x.1 * x.2) * z ≤ z by linarith
              apply mul_le_of_le_one_left (by linarith)
              simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
              nlinarith
        · apply Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self
  · exact eq3_integrableOn_aux n z hz
  · exact eq3_integrableOn_aux n z hz

theorem JJ_eq_form (n : ℕ) : JJ n = JJ' n := by
  simp only [JJ, JJ']
  calc
  _ = ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    (∫ (z : ℝ) in Set.Ioo 0 1,
      eval x.1 (shiftedLegendre n) * eval x.2 (shiftedLegendre n) *
        (1 / (1 - (1 - x.1 * x.2) * z))) := by
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro x hx
    simp only [Set.mem_prod, Set.mem_Ioo] at hx ⊢
    rw [mul_assoc, mul_comm, ← integral1, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num),
      intervalIntegral.integral_const_mul] <;> nlinarith
  _ = ∫ (z : ℝ) in Set.Ioo 0 1, ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    eval x.1 (shiftedLegendre n) * eval x.2 (shiftedLegendre n) *
      (1 / (1 - (1 - x.1 * x.2) * z)) := by
    symm
    rw [MeasureTheory.integral_integral_swap]
    exact integrableOn_JJ1 n
  _ = ∫ (z : ℝ) in Set.Ioo 0 1, ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    eval x.1 (shiftedLegendre n) * (x.1 * x.2 * z) ^ n * (1 - x.2) ^ n /
      (1 - (1 - x.1 * x.2) * z) ^ (n + 1) := by
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro z hz
    simp only
    exact double_integral_eq1 n z hz
  _ = ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1, ∫ (z : ℝ) in Set.Ioo 0 1,
    eval x.1 (shiftedLegendre n) * (x.1 * x.2 * z) ^ n * (1 - x.2) ^ n /
      (1 - (1 - x.1 * x.2) * z) ^ (n + 1) := by
    rw [MeasureTheory.integral_integral_swap]
    exact integrableOn_JJ2 n
  _ = ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1, ∫ (z : ℝ) in Set.Ioo 0 1,
    eval x.1 (shiftedLegendre n) * (1 - z) ^ n * (1 - x.2) ^ n / (1 - (1 - x.1 * x.2) * z) := by
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro x hx
    simp only
    exact double_integral_eq2 n x hx
  _ = ∫ (z : ℝ) in Set.Ioo 0 1, ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    eval x.1 (shiftedLegendre n) * (1 - z) ^ n * (1 - x.2) ^ n / (1 - (1 - x.1 * x.2) * z) := by
    symm
    rw [MeasureTheory.integral_integral_swap]
    exact integrableOn_JJ3 n
  _ = ∫ (z : ℝ) in Set.Ioo 0 1, (1 - z) ^ n *
      ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    (x.1 * x.2 * z * (1 - x.1) * (1 - x.2)) ^ n / (1 - (1 - x.1 * x.2) * z) ^ (n + 1) := by
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro z hz
    simp only
    rw [double_integral_eq3 n z hz, mul_comm, ← smul_eq_mul, ← integral_smul_const]
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro x _
    simp only
    rw [smul_eq_mul]
    ring
  _ = ∫ (z : ℝ) in Set.Ioo 0 1, ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    (x.1 * x.2 * z * (1 - x.1) * (1 - x.2) * (1 - z)) ^ n /
      (1 - (1 - x.1 * x.2) * z) ^ (n + 1) := by
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro z hz
    simp only
    rw [mul_comm, ← smul_eq_mul, ← integral_smul_const]
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro x _
    simp only
    rw [smul_eq_mul, mul_comm, mul_div, ← mul_pow]
    ring
  _ = ∫ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    (x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) /
      (1 - (1 - x.2.1 * x.2.2) * x.1)) ^ n /
      (1 - (1 - x.2.1 * x.2.2) * x.1) := by
    symm
    rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
      MeasureTheory.integral_prod]
    · apply MeasureTheory.setIntegral_congr_fun (by measurability)
      intro x hx
      simp only
      apply MeasureTheory.setIntegral_congr_fun (by measurability)
      intro y _
      simp only
      rw [pow_add, ← div_div, div_pow]
      ring
    · rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
      exact integrableOn_JJ' n

theorem JJ_pos (n : ℕ) : 0 < JJ n := by
  rw [JJ_eq_form, JJ']
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae]
  · set F := _;
    change 0 < MeasureTheory.volume.restrict _ (Function.support F)
    have subset : Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ⊆ Function.support F := by
      intro a ha
      change F a ≠ 0
      simp only [div_pow, ne_eq, _root_.div_eq_zero_iff, pow_eq_zero_iff', mul_eq_zero, not_or,
        not_and, Decidable.not_not, F]
      simp only [Set.mem_prod, Set.mem_Ioo] at ha
      rcases ha with ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩, hz0, hz1⟩
      constructor
      · constructor
        · intro h
          rcases h with (h | h)
          · rcases h with (h | h)
            · rcases h with (h | h)
              · rcases h with (h | h)
                · rcases h with (h | h) <;> nlinarith
                · nlinarith
              · nlinarith
            · nlinarith
          · nlinarith
        · intro h
          suffices ¬1 - (1 - a.2.1 * a.2.2) * a.1 = 0 by tauto
          suffices 1 - (1 - a.2.1 * a.2.2) * a.1 > 0 by linarith
          simp only [gt_iff_lt, sub_pos]
          suffices (1 - a.2.1 * a.2.2) * a.1 < a.1 by linarith
          rw [mul_lt_iff_lt_one_left]
          · simp only [sub_lt_self_iff]
            nlinarith
          · exact hx0
      · suffices 1 - (1 - a.2.1 * a.2.2) * a.1 > 0 by linarith
        simp only [gt_iff_lt, sub_pos]
        suffices (1 - a.2.1 * a.2.2) * a.1 < a.1 by linarith
        rw [mul_lt_iff_lt_one_left]
        · simp only [sub_lt_self_iff]
          nlinarith
        · exact hx0
    rw [MeasureTheory.Measure.restrict_apply']
    · rw [Set.inter_eq_right.2 subset]
      simp only [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
      simp only [Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one, zero_lt_one]
    · measurability
  · apply MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
    · rw [MeasureTheory.IntegrableOn]
      exact integrableOn_JJ' n
    · rintro s hs -
      apply MeasureTheory.setIntegral_nonneg (by measurability)
      intro x hx
      by_cases h : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [Set.mem_prod, Set.mem_Ioo] at h
        apply div_nonneg
        · apply pow_nonneg
          apply div_nonneg
          · apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg (by linarith) (by linarith)
          · simp only [sub_nonneg]
            apply mul_le_one₀ (by nlinarith) (by linarith) (by linarith)
        · simp only [sub_nonneg]
          apply mul_le_one₀ (by nlinarith) (by linarith) (by linarith)
      · rw [Set.mem_inter_iff] at hx
        tauto
  · exact integrableOn_JJ' n

lemma Summable_of_zeta_two' : Summable (fun (n : ℕ) ↦ 1 / ((n : ℝ) + 1) ^ 2) := by
  rw [Summable]
  use Real.pi ^ 2 / 6
  obtain h := hasSum_zeta_two
  let f := fun (n : ℕ) ↦ 1 / (n : ℝ) ^ 2
  let g := fun (n : ℕ) => n + 1
  have h1 : Function.Injective g := by
    intro m n h
    simp only [g] at h
    linarith
  have h2 : ∀ x ∉ Set.range g, f x = 0 := by
    intro x hx
    simp only [Set.mem_range, not_exists] at hx
    suffices x = 0 by simp only [one_div, inv_eq_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_eq_zero_iff, Nat.cast_eq_zero, f, this]
    by_contra! h
    apply hx (x - 1)
    simp only [g]
    omega
  have h3 : f ∘ g = fun (n : ℕ) ↦ 1 / (n + 1 : ℝ) ^ 2 := by
    ext x
    simp [f, g]
  have := Function.Injective.hasSum_iff (f := f) (g := g) (a := (Real.pi ^ 2 / 6 : ℝ)) h1 h2
  rw [h3] at this
  rw [this]
  simp only [f]
  exact h

lemma zeta3_pos : 0 < ∑' (n : ℕ), 1 / ((n : ℝ) + 1) ^ 3 := by
  apply Summable.tsum_pos (g := fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 3) (i := 1)
  · apply summable_of_sum_range_le (c := Real.pi ^ 2 / 6)
    · intro _
      positivity
    · intro n
      suffices
          ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) ^ 3 ≤
            ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) ^ 2 by
        have : ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) ^ 2 ≤ Real.pi ^ 2 / 6 := by
          suffices
              ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) ^ 2 ≤
                ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 2 by
            have h : ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 2 = (riemannZeta 2).re := by
              rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simp)]
              simp_rw [← Complex.ofReal_natCast]
              norm_cast
            rw [h, riemannZeta_two] at this
            norm_cast at *
          apply Summable.sum_le_tsum
          · intro i _
            positivity
          · exact Summable_of_zeta_two'
        linarith
      apply Finset.sum_le_sum
      intro i _
      rw [div_le_div_iff₀, one_mul, one_mul]
      · apply pow_le_pow_right₀ <;> linarith
      · positivity
      · positivity
  · intro m
    simp only [one_div, pow_succ]
    positivity
  · positivity

theorem JJ_upper (n : ℕ) :
    JJ n ≤ 2 * (1 / 24) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  rw [JJ_eq_form, JJ', MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
  · trans
      (ENNReal.ofReal
        (2 * (1 / 24 : ℝ) ^ n * ∑' (n : ℕ), 1 / ((n : ℝ) + 1) ^ 3)).toReal
    · apply ENNReal.toReal_mono
      · exact ENNReal.ofReal_ne_top
      · exact JJENN_upper n
    · rw [ENNReal.toReal_ofReal]
      apply mul_nonneg (by norm_num)
      linarith [zeta3_pos]
  · apply MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
    · rw [MeasureTheory.IntegrableOn]
      exact integrableOn_JJ' n
    · rintro s hs -
      apply MeasureTheory.setIntegral_nonneg (by measurability)
      intro x hx
      by_cases h : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [Set.mem_prod, Set.mem_Ioo] at h
        apply div_nonneg
        · apply pow_nonneg
          apply div_nonneg
          · apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg (by linarith) (by linarith)
          · simp only [sub_nonneg]
            apply mul_le_one₀ (by nlinarith) (by linarith) (by linarith)
        · simp only [sub_nonneg]
          apply mul_le_one₀ (by nlinarith) (by linarith) (by linarith)
      · rw [Set.mem_inter_iff] at hx
        tauto
  · apply AEMeasurable.aestronglyMeasurable
    measurability

lemma zeta3_le_zeta2 :
    ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 <
      ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 2 := by
  apply Summable.tsum_lt_tsum_of_nonneg
    (f := fun n => 1 / ((n : ℝ) + 1) ^ 3)
    (g := fun n => 1 / ((n : ℝ) + 1) ^ 2) (i := 2)
  · intro n
    positivity
  · intro n
    rw [div_le_div_iff₀, one_mul, one_mul]
    · apply pow_le_pow_right₀ <;> linarith
    · positivity
    · positivity
  · norm_num
  · exact Summable_of_zeta_two'

end LeanPool.Zeta3Irrational
