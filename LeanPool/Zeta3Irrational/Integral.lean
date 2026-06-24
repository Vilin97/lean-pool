/-
Copyright (c) 2026 Junqi Liu, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jujian Zhang
-/

import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Common
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Util.CompileInductive

/-!
# LeanPool.Zeta3Irrational.Integral
-/

namespace LeanPool.Zeta3Irrational

open scoped Nat
open BigOperators Finset

lemma Nat_Ico_succ_right (a b : ℕ) : Finset.Ico a (b + 1) = Finset.Icc a b := by
  ext x
  simp only [Finset.mem_Ico, Finset.mem_Icc]
  omega

lemma Nat_Ico_succ_succ (a b : ℕ) :
    Finset.Ico (a + 1) (b + 1) = Finset.Ioc a b := by
  ext x
  simp only [Finset.mem_Ico, Finset.mem_Ioc]
  omega

/-- The two-variable Apéry integral with monomial weights. -/
noncomputable abbrev J (r s : ℕ) : ℝ :=
  ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
  -(x.1 * x.2).log / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s

/-- The extended nonnegative version of `J`. -/
noncomputable abbrev JENN (r s : ℕ) : ENNReal :=
  ∫⁻ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
  ENNReal.ofReal (- (x.1 * x.2).log / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s)

lemma log_rpow_integral_aux (n : ℝ) (a : ℝ) (ha : 0 < a ∧ a ≤ 1) :
    ∫ (x : ℝ) in Set.Ioc a 1, |-x.log * x ^ n| =
      ∫ (x : ℝ) in Set.Ioc a 1, -x.log * x ^ n := by
  apply MeasureTheory.setIntegral_congr_fun (by measurability)
  intro x hx
  simp only [Set.mem_Ioc, neg_mul, abs_neg, abs_eq_neg_self] at *
  rw [mul_nonpos_iff]
  right
  constructor
  · apply Real.log_nonpos <;> linarith
  · apply Real.rpow_nonneg
    linarith

lemma log_rpow_integral' (n : ℝ) (hn : n > -1) (a : ℝ) (ha : 0 < a ∧ a ≤ 1) :
    ∫ (x : ℝ) in Set.Ioc a 1, -x.log * x ^ n =
    1 / (n + 1) ^ 2 - (a ^ (n + 1) / (n + 1) ^ 2 - a ^ (n + 1) * a.log / (n + 1)) := by
  let f := fun x : ℝ => x ^ (n + 1) /(n + 1) ^ 2 - x ^ (n + 1) * x.log /(n + 1)
  rw [show 1 / (n + 1) ^ 2 - (a ^ (n + 1) / (n + 1) ^ 2 - a ^ (n + 1) * a.log / (n + 1)) =
    f 1 - f a by simp[f], ← intervalIntegral.integral_of_le ha.2]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.2 (a := a) (b := 1) (f := f)
    (f' := fun x : ℝ => -x.log * x ^ n ) ?_ ?_ ?_
  · change ContinuousOn
      (fun x : ℝ => x ^ (n + 1) / (n + 1) ^ 2 - x ^ (n + 1) * x.log / (n + 1))
      (Set.Icc a 1)
    refine ContinuousOn.sub (ContinuousOn.div_const ?_ (((n : ℝ) + 1) ^ 2)) ?_
    · apply ContinuousOn.rpow_const continuousOn_id
      intro x hx
      left
      simp only [gt_iff_lt, Set.mem_Icc, id_eq, ne_eq] at *
      linarith
    · apply ContinuousOn.div_const
      apply ContinuousOn.mul
      · apply ContinuousOn.rpow_const continuousOn_id
        intro x hx
        left
        simp only [gt_iff_lt, Set.mem_Icc, id_eq, ne_eq] at *
        linarith
      · apply ContinuousOn.log continuousOn_id
        intro x hx
        simp only [Set.mem_Icc, id_eq] at hx ⊢
        linarith
  · intro x hx
    simp only [Set.mem_Ioo] at hx
    simp only [f]
    rw [show -x.log * x ^ n = x ^ n / (↑n + 1) - (x ^ n * x.log + x ^ n / (↑n + 1)) by ring]
    apply HasDerivAt.sub
    · have h : x ^ n / (↑n + 1) = x ^ n * (↑n + 1) / (↑n + 1) ^ 2 := by
        rw[div_eq_div_iff (by linarith)]
        · ring
        · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
          linarith
      rw [h]
      apply HasDerivAt.div_const
      rw [mul_comm]
      nth_rw 3 [show n = n + 1 - 1 by simp]
      norm_cast
      apply Real.hasDerivAt_rpow_const
      left
      linarith
    · have h :
          x ^ n * x.log + x ^ n / (↑n + 1) =
            ((↑n + 1) * x ^ n * x.log + x ^ n) / (↑n + 1) := by
        rw [add_div]
        congr 1
        rw [eq_div_iff (by linarith)]
        ring
      rw[h]
      apply HasDerivAt.div_const
      nth_rw 2 [show x ^ n = x ^ (n + 1) * (1 / x) by
        rw [mul_div, eq_div_iff (by linarith), Real.rpow_add (by linarith), mul_one,
          Real.rpow_one]]
      apply HasDerivAt.mul
      · nth_rw 3 [show n = n + 1 - 1 by simp]
        norm_cast
        apply Real.hasDerivAt_rpow_const
        left
        linarith
      · apply HasDerivAt.log (hasDerivAt_id' x) (by linarith)
  · apply IntervalIntegrable.continuousOn_mul
    · apply intervalIntegral.intervalIntegrable_rpow
      right
      simp only [Set.uIcc_of_le ha.2, Set.mem_Icc, zero_le_one, and_true, not_le]
      linarith
    · apply ContinuousOn.neg
      apply ContinuousOn.log continuousOn_id
      intro x hx
      rw [Set.uIcc_of_le ha.2] at hx
      simp only [Set.mem_Icc, id_eq, ne_eq] at hx ⊢
      nlinarith

lemma log_rpow_integrable (n : ℝ) (hn : n > -1) :
    IntervalIntegrable (fun x ↦ -Real.log x * x ^ n) MeasureTheory.volume 0 1 := by
  let f := fun (x : ℝ) => -x.log * x ^ n
  apply MeasureTheory.IntegrableOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num), integrableOn_Icc_iff_integrableOn_Ioc]
  apply MeasureTheory.integrableOn_Ioc_of_intervalIntegral_norm_bounded_left (f := f)
    (l := Filter.atTop) (a := fun (n : ℕ) => 1 / (n + 1 : ℝ)) (a₀ := 0) (b := 1)
    (I := 1 / (n + 1) ^ 2)
  · intro i
    simp only [one_div, f]
    have hi :  0 < ((i : ℝ) + 1)⁻¹ ∧ ((i : ℝ) + 1)⁻¹ ≤ 1 := by
      constructor
      · simp only [inv_pos]; linarith
      · rw [← one_div, div_le_iff₀] <;> linarith
    rw [← Set.uIoc_of_le hi.2, ← intervalIntegrable_iff]
    apply IntervalIntegrable.continuousOn_mul
    · apply intervalIntegral.intervalIntegrable_rpow
      right
      simp only [Set.uIcc_of_le hi.2, Set.mem_Icc, zero_le_one, and_true, not_le]
      linarith
    · apply ContinuousOn.neg
      apply ContinuousOn.log continuousOn_id
      intro x hx
      rw [Set.uIcc_of_le hi.2] at hx
      simp only [Set.mem_Icc, id_eq, ne_eq] at hx ⊢
      nlinarith
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · rw [Filter.eventually_atTop]
    use 0
    intro b _
    simp only [Real.norm_eq_abs, f]
    rw [log_rpow_integral_aux n]
    · rw [log_rpow_integral' n hn]
      · set k := _
        change _ - k ≤ _
        simp only [tsub_le_iff_right, le_add_iff_nonneg_right,
          sub_nonneg, k]
        rw [div_le_div_iff₀ (by linarith) (by nlinarith), mul_assoc, mul_le_mul_iff_of_pos_left]
        · trans 0
          · rw [mul_nonpos_iff]
            right
            constructor
            · apply Real.log_nonpos
              · simp only [one_div, inv_nonneg]
                linarith
              · rw [div_le_iff₀] <;> linarith
            · positivity
          · linarith
        · apply Real.rpow_pos_of_pos
          simp only [one_div, inv_pos]
          linarith
      · constructor
        · positivity
        · rw [div_le_one] <;> linarith
    · constructor
      · positivity
      · rw [div_le_one] <;> linarith

lemma log_rpow_integral (n : ℝ) (hn : n > -1) :
    ∫ (x : ℝ) in (0)..1, -x.log * x ^ n = 1 / (n + 1) ^ 2 := by
  let F := fun (x : ℝ) => x ^ (n + 1) * (1 - (n + 1) * x.log) / (n + 1) ^ 2
  have h1 : 1 /(n + 1) ^ 2 = F 1 - F 0 := by
    simp only [F, one_div]
    rw [Real.zero_rpow (by linarith), zero_mul, zero_div, sub_zero]
    simp only [Real.log_one, mul_zero, sub_zero, Real.one_rpow]
    ring
  rw [h1]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (by norm_num) (a := 0) (b := 1)
    (f := F) (f' := fun x : ℝ => -x.log * x ^ n ) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Set.mem_Ioo] at hx
    simp only [F, mul_sub, mul_one]
    have : -Real.log x * x ^ n = -Real.log x * x ^ n * (n + 1) ^ 2 / (n + 1) ^ 2 := by
      rw [eq_div_iff]
      nlinarith
    rw [this]
    apply HasDerivAt.div_const
    rw [show -Real.log x * x ^ n * (n + 1) ^ 2 =
      (n + 1) * x ^ n - ((n + 1) * x ^ n + Real.log x * x ^ n * (n + 1) ^ 2) by ring]
    apply HasDerivAt.sub
    · rw [show (n + 1) * x ^ n = 1 * (n + 1) * x ^ (n + 1 - 1) by simp only [one_mul,
      add_sub_cancel_right]]
      apply HasDerivAt.rpow_const (hasDerivAt_id' x)
      left; linarith
    · have : (n + 1) * x ^ n + Real.log x * x ^ n * (n + 1) ^ 2 =
        (n + 1) * x ^ n * ((n + 1) * Real.log x) +  x ^ (n + 1) * ((n + 1) / x) := by
        rw [← mul_comm_div, ← Real.rpow_sub_one (by linarith)]
        ring_nf
      rw [this]
      apply HasDerivAt.mul
      · rw [show (n + 1) * x ^ n = 1 * (n + 1) * x ^ (n + 1 - 1) by simp only [one_mul,
          add_sub_cancel_right]]
        apply HasDerivAt.rpow_const (hasDerivAt_id' x)
        left; linarith
      · apply HasDerivAt.const_mul
        rw [← one_div]
        apply HasDerivAt.log (hasDerivAt_id' x) (by linarith)
  · exact log_rpow_integrable n hn
  · simp only [Real.log_zero, mul_zero, sub_zero, mul_one, F]
    rw [Real.zero_rpow (by linarith), zero_div]
    simp_rw [mul_sub, sub_div]
    nth_rw 3 [show (0 : ℝ) = 0 / (n + 1) ^ 2 - 0 / (n + 1) ^ 2 by simp]
    refine Filter.Tendsto.sub (a := 0 / (n + 1) ^ 2) (b := 0 / (n + 1) ^ 2) ?_ ?_
    · apply Filter.Tendsto.div_const
      simp_rw [mul_one]
      nth_rw 3 [show (0 : ℝ) = 0 ^ (n + 1) by rw [Real.zero_rpow (by linarith)]]
      apply Filter.Tendsto.rpow_const
      · apply tendsto_nhdsWithin_of_tendsto_nhds
        exact fun ⦃U⦄ a ↦ a
      · right; linarith
    · apply Filter.Tendsto.div_const
      rw [show (fun a : ℝ => a ^ (n + 1) * ((n + 1) * Real.log a)) =
          (fun a => Real.log a * a ^ (n + 1) * (n + 1)) by
        funext a
        ring]
      nth_rw 3 [show (0 : ℝ) = 0 * (n + 1) by simp]
      apply Filter.Tendsto.mul_const
      apply tendsto_log_mul_rpow_nhdsGT_zero
      linarith
  · apply tendsto_nhds_of_tendsto_nhdsWithin (s := ⊤)
    apply ContinuousWithinAt.tendsto_nhdsWithin
    · apply ContinuousAt.continuousWithinAt
      simp only [F]
      apply ContinuousAt.div_const
      apply ContinuousAt.mul
      · apply ContinuousAt.rpow_const continuousAt_id
        right; linarith
      · apply ContinuousAt.sub continuousAt_const
        apply ContinuousAt.mul continuousAt_const
        apply ContinuousAt.log continuousAt_id (by norm_num)
    · intro _ _
      simp

lemma ENN_log_rpow_integral (n : ℝ) (hn : n > -1) : ∫⁻ (x : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (-x.log * x ^ n) = ENNReal.ofReal (1 / (n + 1) ^ 2) := by
  calc
  _ = ∫⁻ (x : ℝ),
      ENNReal.ofReal ((Set.Ioo 0 1).indicator (fun x => -Real.log x * x ^ n) x) := by
    rw [← MeasureTheory.lintegral_indicator]
    · congr
      ext x
      rw [Set.indicator_apply, Set.indicator_apply]
      aesop
    · measurability
  _ = ENNReal.ofReal (1 / (n + 1) ^ 2) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
    · rw [MeasureTheory.integral_indicator (by measurability),
        ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num), log_rpow_integral n hn]
    · apply MeasureTheory.IntegrableOn.integrable_indicator _ (by measurability)
      rw [← integrableOn_Ioc_iff_integrableOn_Ioo, ← Set.uIoc_of_le (by norm_num),
        ← intervalIntegrable_iff]
      exact log_rpow_integrable n hn
    · refine MeasureTheory.ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite ?_ ?_
      · rintro s - -
        apply MeasureTheory.Integrable.integrableOn
        apply MeasureTheory.IntegrableOn.integrable_indicator _ (by measurability)
        rw [← integrableOn_Ioc_iff_integrableOn_Ioo, ← Set.uIoc_of_le (by norm_num),
          ← intervalIntegrable_iff]
        exact log_rpow_integrable n hn
      · rintro s hs -
        apply MeasureTheory.setIntegral_nonneg hs
        suffices  ∀ x, 0 ≤ (Set.Ioo 0 1).indicator (fun x ↦ -Real.log x * x ^ n) x by aesop
        intro x
        rw [Set.indicator_apply]
        by_cases h : x ∈ Set.Ioo 0 1
        · simp only [h, ↓reduceIte, neg_mul, Left.nonneg_neg_iff]
          simp only [Set.mem_Ioo] at h
          rw [mul_nonpos_iff]
          right
          constructor
          · apply Real.log_nonpos <;> linarith
          · apply Real.rpow_nonneg; linarith
        · simp only [h, ↓reduceIte, le_refl]

lemma ENN_log_pow_integral (n : ℕ) : ∫⁻ (x : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (-x.log * x ^ n) = ENNReal.ofReal (1 / (n + 1) ^ 2) := by
  rw [← ENN_log_rpow_integral]
  · norm_cast
  · suffices 0 ≤ n by linarith
    omega

lemma ENN_pow_integral (n : ℕ) : ∫⁻ (x : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (x ^ n) = ENNReal.ofReal (1 / (n + 1)) := by
  have h := @integral_pow 0 1 n
  rw [zero_pow, one_pow, sub_zero, intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.integral_Ioc_eq_integral_Ioo] at h
  · rw [← h, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
    · apply MeasureTheory.IntegrableOn.integrable
      rw [← integrableOn_Ioc_iff_integrableOn_Ioo, ← Set.uIoc_of_le (by norm_num),
        ← intervalIntegrable_iff]
      exact intervalIntegral.intervalIntegrable_pow n
    · apply MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
      · rw [← integrableOn_Ioc_iff_integrableOn_Ioo, ← Set.uIoc_of_le (by norm_num),
          ← intervalIntegrable_iff]
        exact intervalIntegral.intervalIntegrable_pow n
      · rintro s hs -
        apply MeasureTheory.setIntegral_nonneg (by measurability)
        intro x hs
        simp only [Set.mem_inter_iff, Set.mem_Ioo] at hs
        by_cases h : x ∈ s
        · simp only [h, true_and] at hs
          apply pow_nonneg
          linarith
        · tauto
  · omega

lemma AEMeasurable_aux : AEMeasurable (fun (x : ℝ × ℝ × ℝ) ↦
    1 / (1 - (1 - x.2.1 * x.2.2) * x.1) * x.2.1 ^ r * x.2.2 ^ s) MeasureTheory.volume := by
  measurability

lemma integral1 {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∫ (z : ℝ) in (0)..1, 1 / (1 - (1 - a) * z) = - a.log / (1 - a) := by
  rw[← sub_pos] at ha1
  have eq1 := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) (c := 1 - a)
    (f := fun z ↦ (1 - z)⁻¹) (by positivity)
  have eq2 := intervalIntegral.mul_integral_comp_sub_mul (a := 0) (b := 1 - a)
    (f := fun x ↦ (x)⁻¹)
    (c := 1) (d := 1)
  have eq3 := integral_inv_of_pos (a := a) (b := 1) ha (by norm_num)
  simp only [mul_zero, mul_one, smul_eq_mul] at eq1
  simp only [one_div]
  rw [eq1, inv_mul_eq_div]
  field_simp
  simp only [one_div]
  simp only [one_mul, intervalIntegral.integral_comp_sub_left, sub_sub_cancel, sub_zero,
    mul_zero] at eq2
  have hsub := intervalIntegral.integral_comp_sub_left
    (f := fun x : ℝ => x⁻¹) (a := 0) (b := 1 - a) 1
  simp only [sub_zero, sub_sub_cancel] at hsub
  rw [hsub, eq3, one_div, Real.log_inv]

lemma sub_mul_mul_ne_zero (y : ℝ) (x : ℝ × ℝ)
    (hy : y ∈ Set.Icc 0 1) (h1 : 0 < 1 - (1 - x.1 * x.2)) : 1 - (1 - x.1 * x.2) * y ≠ 0 := by
  suffices 1 - (1 - x.1 * x.2) * y > 0 by linarith
  simp only [gt_iff_lt, sub_pos]
  by_cases hy' : y = 0
  · rw [hy']
    simp
  · simp only [sub_pos, Set.mem_Icc] at *
    suffices (1 - x.1 * x.2) * y < y by linarith
    rwa [mul_lt_iff_lt_one_left]
    rcases hy with ⟨hy1, _⟩
    by_contra! h
    suffices y = 0 by tauto
    linarith

lemma integrableOn_aux (x : ℝ × ℝ)
    (h1 : 0 < 1 - (1 - x.1 * x.2)) (h2 : 1 - (1 - x.1 * x.2) < 1) :
    MeasureTheory.IntegrableOn (fun t ↦ 1 / (1 - (1 - x.1 * x.2) * t))
    (Set.Ioo 0 1) MeasureTheory.volume := by
  rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
  apply intervalIntegral.integrableOn_deriv_of_nonneg
    (g := fun t => -Real.log (1 - (1 - x.1 * x.2) * t) / (1 - x.1 * x.2))
  · apply ContinuousOn.div_const
    apply ContinuousOn.neg
    apply ContinuousOn.log
    · apply ContinuousOn.sub continuousOn_const
      apply ContinuousOn.mul continuousOn_const continuousOn_id
    · intro y hy
      exact sub_mul_mul_ne_zero y x hy h1
  · intro y hy
    have h : 1 / (1 - (1 - x.1 * x.2) * y) =
      -(-(1 - x.1 * x.2)) / (1 - (1 - x.1 * x.2) * y) / (1 - x.1 * x.2) := by
      rw [neg_neg, div_div, div_eq_div_iff]
      · ring
      · exact sub_mul_mul_ne_zero y x (Set.mem_Icc_of_Ioo hy) h1
      · apply mul_ne_zero (sub_mul_mul_ne_zero y x (Set.mem_Icc_of_Ioo hy) h1)
        suffices 1 - x.1 * x.2 > 0 by linarith
        linarith
    rw [h]
    apply HasDerivAt.div_const
    rw [neg_div]
    apply HasDerivAt.neg
    apply HasDerivAt.log
    · apply HasDerivAt.const_sub
      nth_rw 2 [← mul_one (a := 1 - x.1 * x.2)]
      apply HasDerivAt.const_mul _ (hasDerivAt_id' y)
    · exact sub_mul_mul_ne_zero y x (Set.mem_Icc_of_Ioo hy) h1
  · intro y hy
    simp at hy
    apply div_nonneg (by norm_num)
    simp only [sub_nonneg]
    apply mul_le_one₀ _ (by linarith) (by linarith)
    linarith

lemma JENN_eq_triple_aux' (x : ℝ × ℝ) (hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) :
    ∫⁻ (w : ℝ) in Set.Ioo 0 1, ENNReal.ofReal (1 / (1 - (1 - x.1 * x.2) * w)) =
    ENNReal.ofReal (-Real.log (1 - (1 - x.1 * x.2)) / (1 - x.1 * x.2)) := by
  have h1 : 0 < 1 - (1 - x.1 * x.2) := by
    simp only [Set.mem_prod, Set.mem_Ioo, sub_sub_cancel] at *
    apply mul_pos (by linarith) (by linarith)
  have h2 : 1 - (1 - x.1 * x.2) < 1 := by
    simp only [Set.mem_prod, Set.mem_Ioo, sub_sub_cancel] at *
    suffices x.1 * x.2 < x.2 by linarith
    aesop
  nth_rw 3 [show 1 - x.1 * x.2 = 1 - (1 - (1 - x.1 * x.2)) by simp]
  rw [←  integral1 (a := 1 - (1 - x.1 * x.2)) h1 h2,
    show 1 - (1 - (1 - x.1 * x.2)) = 1 - x.1 * x.2 by simp]
  rw [intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · apply MeasureTheory.IntegrableOn.integrable
    exact integrableOn_aux x h1 h2
  · apply MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
    · exact integrableOn_aux x h1 h2
    · rintro s hs -
      apply MeasureTheory.setIntegral_nonneg (by measurability)
      intro y hs
      simp only [Set.mem_inter_iff, Set.mem_Ioo] at hs
      by_cases h : y ∈ s
      · simp only [h, true_and] at hs
        apply div_nonneg (by norm_num)
        simp only [sub_nonneg]
        apply mul_le_one₀ _ (by linarith) (by linarith)
        linarith
      · tauto

lemma JENN_eq_triple_aux (x : ℝ × ℝ) (hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) :
    ∫⁻ (w : ℝ) in Set.Ioo 0 1,
      ENNReal.ofReal (1 / (1 - (1 - x.1 * x.2) * w) * x.1 ^ r * x.2 ^ s) =
    ENNReal.ofReal (-Real.log (x.1 * x.2) / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s) := by
  calc
  _ = ENNReal.ofReal (x.1 ^ r * x.2 ^ s) *
    ENNReal.ofReal (-Real.log (1 - (1 - x.1 * x.2)) / (1 - x.1 * x.2)) := by
    rw [← JENN_eq_triple_aux' x hx]
    rw [← MeasureTheory.lintegral_const_mul]
    · congr
      ext y
      rw [← ENNReal.ofReal_mul]
      · congr 1
        field_simp
      rcases x with ⟨x1, x2⟩
      rcases hx with ⟨⟨hx1, hx1'⟩, ⟨hx2,hx2'⟩⟩
      positivity
    · apply Measurable.ennreal_ofReal
      apply Measurable.const_div
      apply Measurable.const_sub
      apply Measurable.const_mul measurable_id
  _ = ENNReal.ofReal (-Real.log (x.1 * x.2) / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s) := by
    simp only [Set.mem_prod, Set.mem_Ioo, sub_sub_cancel] at *
    rw [mul_comm, ← ENNReal.ofReal_mul, ← mul_assoc]
    apply div_nonneg
    · simp only [Left.nonneg_neg_iff]
      apply Real.log_nonpos
      · apply mul_nonneg (by linarith) (by linarith)
      · apply mul_le_one₀ (by linarith) (by linarith) (by linarith)
    · simp only [sub_nonneg]
      apply mul_le_one₀ (by linarith) (by linarith) (by linarith)

lemma JENN_eq_triple (r s : ℕ) : JENN r s =
    ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ENNReal.ofReal (1 / (1 - (1 - x.2.1 * x.2.2) * x.1) * x.2.1 ^ r * x.2.2 ^ s) := by
  symm
  calc
  _ = ∫⁻ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1, ∫⁻ (w : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (1 / (1 - (1 - x.1 * x.2) * w) * x.1 ^ r * x.2 ^ s) := by
    rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
      MeasureTheory.lintegral_prod, MeasureTheory.lintegral_lintegral_swap]
    · simp only
      rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod,
        ← aemeasurable_indicator_iff (by measurability)]
      apply AEMeasurable.indicator _ (by measurability)
      apply AEMeasurable.ennreal_ofReal
      exact AEMeasurable_aux
    · rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod,
        ← aemeasurable_indicator_iff (by measurability)]
      apply AEMeasurable.indicator _ (by measurability)
      apply AEMeasurable.ennreal_ofReal
      exact AEMeasurable_aux
  _ = ∫⁻ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ENNReal.ofReal (- (x.1 * x.2).log / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s) := by
    apply MeasureTheory.setLIntegral_congr_fun (by measurability)
    intro x hx
    exact JENN_eq_triple_aux _ hx

lemma AEMeasurable_aux' : AEMeasurable
    (fun x ↦ ENNReal.ofReal (-Real.log (x.1 * x.2) * x.1 ^ (k + r) * x.2 ^ (k + s)))
    (MeasureTheory.volume.restrict (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1)) := by
  apply AEMeasurable.ennreal_ofReal
  apply Measurable.aemeasurable
  apply Measurable.mul _ (Measurable.pow_const measurable_snd _)
  · apply Measurable.mul _ (Measurable.pow_const measurable_fst _)
    · apply Measurable.neg
      apply Measurable.log
      apply Measurable.mul measurable_fst measurable_snd

lemma aux_lintegral1 (k r s : ℕ) (x : ℝ) (hx : 0 < x ∧ x < 1) :
    ∫⁻ (a : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (-(Real.log x * x ^ (k + r) * a ^ (k + s)))
    = ENNReal.ofReal (- x.log * x ^ (k + r) / (k + s + 1)) := by
  calc
  _ = ENNReal.ofReal (-Real.log x * x ^ (k + r)) * ∫⁻ (a : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (a ^ (k + s)) := by
    rw [← MeasureTheory.lintegral_const_mul]
    · congr
      ext y
      rw [← ENNReal.ofReal_mul]
      · field_simp
      rcases hx with ⟨hx1, hx2⟩
      simp only [neg_mul, Left.nonneg_neg_iff]
      rw [mul_nonpos_iff]
      right
      exact ⟨Real.log_nonpos (by linarith) (by linarith), by positivity⟩
    · apply Measurable.ennreal_ofReal
      apply Measurable.pow measurable_id measurable_const
  _ = ENNReal.ofReal (- x.log * x ^ (k + r) / (k + s + 1)) := by
    rw [ENN_pow_integral, ← ENNReal.ofReal_mul, mul_one_div]
    · norm_cast
    · simp only [neg_mul, Left.nonneg_neg_iff]
      rw [mul_nonpos_iff]
      right
      constructor
      · apply Real.log_nonpos (by linarith) (by nlinarith)
      · apply pow_nonneg (by linarith)

lemma aux_lintegral2 (k r s : ℕ) (x : ℝ) (hx : 0 < x ∧ x < 1) :
    ∫⁻ (a : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (-(Real.log a * x ^ (k + r) * a ^ (k + s)))
    = ENNReal.ofReal (x ^ (k + r) / (k + s + 1) ^ 2) := by
  calc
  _ = ENNReal.ofReal (x ^ (k + r)) * ∫⁻ (a : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (-a.log * a ^ (k + s)) := by
    rw [← MeasureTheory.lintegral_const_mul]
    · congr
      ext y
      cases hx
      rw [← ENNReal.ofReal_mul]
      · congr 1
        ring
      positivity
    · apply Measurable.ennreal_ofReal
      apply Measurable.mul
      · apply Measurable.neg
        apply Measurable.log measurable_id
      · apply Measurable.pow measurable_id measurable_const
  _ = ENNReal.ofReal (x ^ (k + r) / (k + s + 1) ^ 2) := by
    rw [ENN_log_pow_integral, ← ENNReal.ofReal_mul, mul_one_div]
    · norm_cast
    · apply pow_nonneg (by linarith)

lemma aux_lintegral3 (k r s : ℕ) : ∫⁻ (x : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (-x.log * x ^ (k + r) / (k + s + 1))
    = ENNReal.ofReal (1 / ((k + r + 1) ^ 2 * (k + s + 1))) := by
  calc
  _ =
      (∫⁻ (x : ℝ) in Set.Ioo 0 1, ENNReal.ofReal (-x.log * x ^ (k + r))) *
        ENNReal.ofReal (1 / (k + s + 1)) := by
    rw [← MeasureTheory.lintegral_mul_const]
    · apply MeasureTheory.setLIntegral_congr_fun (by measurability)
      rintro y ⟨hy1, hy2⟩
      change ENNReal.ofReal (-Real.log y * y ^ (k + r) / (↑k + ↑s + 1)) =
        ENNReal.ofReal (-Real.log y * y ^ (k + r)) * ENNReal.ofReal (1 / (↑k + ↑s + 1))
      rw [← ENNReal.ofReal_mul]
      · field_simp
      simp only [neg_mul, Left.nonneg_neg_iff]
      rw [mul_nonpos_iff]
      right
      refine ⟨Real.log_nonpos (by linarith) (by nlinarith), by positivity⟩
    · apply Measurable.ennreal_ofReal
      apply Measurable.mul
      · apply Measurable.neg
        apply Measurable.log measurable_id
      · apply Measurable.pow measurable_id measurable_const
  _ = ENNReal.ofReal (1 / ((k + r + 1) ^ 2 * (k + s + 1))) := by
    rw [ENN_log_pow_integral, ← ENNReal.ofReal_mul, mul_one_div, div_div]
    · norm_cast
    · positivity

lemma aux_lintegral4 (k r s : ℕ) : ∫⁻ (x : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (x ^ (k + r) / (k + s + 1) ^ 2)
    = ENNReal.ofReal (1 / ((k + r + 1) * (k + s + 1) ^ 2)) :=
  calc
  _ =
      (∫⁻ (x : ℝ) in Set.Ioo 0 1, ENNReal.ofReal (x ^ (k + r))) *
        ENNReal.ofReal (1 / (k + s + 1) ^ 2) := by
      rw [← MeasureTheory.lintegral_mul_const]
      · apply MeasureTheory.setLIntegral_congr_fun (by measurability)
        rintro y ⟨hy1, hy2⟩
        change ENNReal.ofReal (y ^ (k + r) / (↑k + ↑s + 1) ^ 2) =
          ENNReal.ofReal (y ^ (k + r)) * ENNReal.ofReal (1 / (↑k + ↑s + 1) ^ 2)
        rw [← ENNReal.ofReal_mul]
        · field_simp
        positivity
      · measurability
  _ = ENNReal.ofReal (1 / ((k + r + 1) * (k + s + 1) ^ 2)) := by
    rw [ENN_pow_integral, ← ENNReal.ofReal_mul, mul_one_div, div_div]
    · norm_cast
    · positivity

lemma J_ENN_rs_eq_tsum_aux_intergal (r s k : ℕ) :
    ∫⁻ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ENNReal.ofReal (- (x.1 * x.2).log * x.1 ^ (k + r) * x.2 ^ (k + s)) =
    ENNReal.ofReal
      (1 / ((k + r + 1) ^ 2 * (k + s + 1)) +
        1 / ((k + r + 1) * (k + s + 1) ^ 2)) := by
  rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
      MeasureTheory.lintegral_prod]
  · calc
    _ = ∫⁻ (x : ℝ) in Set.Ioo 0 1,
      ENNReal.ofReal (- x.log * x ^ (k + r) / (k + s + 1) + x ^ (k + r) / (k + s + 1) ^ 2) := by
      apply MeasureTheory.setLIntegral_congr_fun (by measurability)
      intro x hx
      simp only [neg_mul]
      have h2 :
          ∫⁻ (y : ℝ) in Set.Ioo 0 1,
            ENNReal.ofReal (-((x * y).log * x ^ (k + r) * y ^ (k + s))) =
          ∫⁻ (y : ℝ) in Set.Ioo 0 1,
            ENNReal.ofReal (-(x.log * x ^ (k + r) * y ^ (k + s))) +
              ENNReal.ofReal (-(y.log * x ^ (k + r) * y ^ (k + s))) := by
        apply MeasureTheory.setLIntegral_congr_fun (by measurability)
        intro y hy
        simp only [← neg_mul]
        simp only [Set.mem_Ioo] at hx hy
        rw [Real.log_mul (by linarith) (by linarith), neg_add, add_mul, add_mul,
          ENNReal.ofReal_add]
        · apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          simp only [Left.nonneg_neg_iff]
          apply Real.log_nonpos (by nlinarith) (by nlinarith)
        · apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          simp only [Left.nonneg_neg_iff]
          apply Real.log_nonpos (by nlinarith) (by nlinarith)
      rw [h2, MeasureTheory.lintegral_add_left']
      · simp only [Set.mem_Ioo] at hx
        rw [aux_lintegral1 k r s x hx, aux_lintegral2 k r s x hx, ENNReal.ofReal_add, neg_mul]
        · apply div_nonneg _ (by positivity)
          simp only [Left.nonneg_neg_iff]
          rw [mul_nonpos_iff]
          right
          constructor
          · apply Real.log_nonpos (by linarith) (by nlinarith)
          · apply pow_nonneg (by linarith)
        · apply div_nonneg _ (by positivity)
          apply pow_nonneg (by linarith)
      · apply AEMeasurable.ennreal_ofReal
        apply Measurable.aemeasurable
        apply Measurable.neg
        apply Measurable.const_mul
        exact Measurable.pow_const measurable_id _
    _ = ENNReal.ofReal
      (1 / ((k + r + 1) ^ 2 * (k + s + 1)) + 1 / ((k + r + 1) * (k + s + 1) ^ 2)) := by
      have h2 : ∫⁻ (x : ℝ) in Set.Ioo 0 1,
        ENNReal.ofReal
          (- x.log * x ^ (k + r) / (k + s + 1) + x ^ (k + r) / (k + s + 1) ^ 2)
        = ∫⁻ (x : ℝ) in Set.Ioo 0 1,
        ENNReal.ofReal (-x.log * x ^ (k + r) / (k + s + 1)) +
          ENNReal.ofReal (x ^ (k + r) / (k + s + 1) ^ 2) := by
        apply MeasureTheory.setLIntegral_congr_fun (by measurability)
        rintro x ⟨hx1, hx2⟩
        change ENNReal.ofReal
            (-Real.log x * x ^ (k + r) / (↑k + ↑s + 1) + x ^ (k + r) / (↑k + ↑s + 1) ^ 2) =
          ENNReal.ofReal (-Real.log x * x ^ (k + r) / (↑k + ↑s + 1)) +
            ENNReal.ofReal (x ^ (k + r) / (↑k + ↑s + 1) ^ 2)
        rw [ENNReal.ofReal_add]
        · apply div_nonneg _ (by positivity)
          apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          simp only [Left.nonneg_neg_iff]
          apply Real.log_nonpos (by nlinarith) (by nlinarith)
        · apply div_nonneg _ (by positivity)
          apply pow_nonneg (by linarith)
      rw [h2, MeasureTheory.lintegral_add_left']
      · rw [aux_lintegral3 k r s, aux_lintegral4 k r s, ENNReal.ofReal_add]
        · apply div_nonneg (by norm_num) (by positivity)
        · apply div_nonneg (by norm_num) (by positivity)
      · apply AEMeasurable.ennreal_ofReal
        apply Measurable.aemeasurable
        apply Measurable.div_const
        apply Measurable.mul
        · apply Measurable.neg
          apply Measurable.log measurable_id
        · exact Measurable.pow_const measurable_id _
  · rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
    exact AEMeasurable_aux'

lemma J_ENN_rs_eq_tsum (r s : ℕ) : JENN r s = ∑' (k : ℕ), ENNReal.ofReal
    (1 / ((k + r + 1) ^ 2 * (k + s + 1)) + 1 / ((k + r + 1) * (k + s + 1) ^ 2)) := by
  calc
  _ = ∫⁻ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ∑' (k : ℕ), ENNReal.ofReal (- (x.1 * x.2).log * x.1 ^ (k + r) * x.2 ^ (k + s)) := by
    rw [JENN, ← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
    congr
    ext y
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h1 : y ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
    · simp only [h1, ↓reduceIte, div_eq_mul_inv]
      simp only [Set.mem_prod, Set.mem_Ioo] at h1
      rw [← tsum_geometric_of_lt_one]
      · rw [← tsum_mul_left, ← tsum_mul_right, ← tsum_mul_right,
          ENNReal.ofReal_tsum_of_nonneg]
        · simp only [neg_mul, pow_add, mul_pow, ← mul_assoc]
          congr
          ext k
          nth_rw 2 [mul_assoc]
          nth_rw 4 [mul_assoc]
          nth_rw 5 [mul_comm]
        · intro n
          rw [mul_pow, ← mul_assoc]
          apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          simp only [Left.nonneg_neg_iff]
          apply Real.log_nonpos (by nlinarith) (by nlinarith)
        · simp_rw [← smul_eq_mul]
          apply Summable.smul_const (a := y.2 ^ s)
          apply Summable.smul_const (a := y.1 ^ r)
          apply Summable.const_smul (b := -(y.1 • y.2).log)
          apply summable_geometric_of_lt_one <;> rw [smul_eq_mul] <;> nlinarith
      · nlinarith
      · nlinarith
    · simp only [h1, ↓reduceIte]
  _ = ∑' (k : ℕ), ∫⁻ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ENNReal.ofReal (- (x.1 * x.2).log * x.1 ^ (k + r) * x.2 ^ (k + s)) := by
    rw [MeasureTheory.lintegral_tsum]
    intro n
    exact AEMeasurable_aux'
  _ = ∑' (k : ℕ), ENNReal.ofReal
    (1 / ((k + r + 1) ^ 2 * (k + s + 1)) + 1 / ((k + r + 1) * (k + s + 1) ^ 2)) := by
    simp_rw [J_ENN_rs_eq_tsum_aux_intergal r s]

lemma J_ENN_rr (r : ℕ) : JENN r r = ENNReal.ofReal
    (2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 -
      2 * ∑ m ∈ Finset.Icc 1 r, 1 / (m : ℝ) ^ 3) := by
  have h : JENN r r = ∑' (k : ℕ), ENNReal.ofReal (2 / ((k + r + 1) ^ 3)) := by
    rw [J_ENN_rs_eq_tsum r r]
    congr
    ext k
    rw [← pow_one (a := (k : ℝ) + r + 1), ← pow_mul, ← pow_add, ← pow_add, one_mul]
    simp only [Nat.reduceAdd, pow_one, ← two_mul, mul_one_div]
  rw [h]
  have h1 : ∑' (k : ℕ), 2 / (((k : ℝ) + r + 1) ^ 3) =
      2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 -
        2 * ∑ m ∈ Finset.Icc 1 r, 1 / (m : ℝ) ^ 3 := by
    symm
    apply sub_eq_of_eq_add
    have hsum_inv_cube : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 3) := by
      simpa [Nat.cast_add, Nat.cast_one, add_comm] using
        ((summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 3) 1).2
          ((Real.summable_one_div_nat_pow (p := 3)).2 (by norm_num)))
    rw [← hsum_inv_cube.sum_add_tsum_nat_add r, mul_add, add_comm, ← tsum_mul_left]
    · simp only [mul_one_div]
      congr 1
      · norm_cast
      · congr 1
        have h1 := Finset.sum_Ico_eq_sum_range (m := 1) (n := r + 1)
          (f := fun k => 1 / (k : ℝ) ^ 3)
        simpa [Nat_Ico_succ_right, Nat.cast_add, Nat.cast_one, add_comm] using h1.symm
  rw [← h1, ENNReal.ofReal_tsum_of_nonneg]
  · intro n
    positivity
  · norm_cast
    simp only [add_assoc, Nat.cast_pow]
    rw [summable_nat_add_iff (k := r + 1) (f := fun k => 2 / (k ^ 3 : ℝ))]
    have h2 := Real.summable_one_div_nat_pow (p := 3)
    simp only [Nat.one_lt_ofNat] at h2
    apply Iff.symm at h2
    rw [true_iff, ← summable_mul_left_iff (a := 2) (by norm_num)] at h2
    simp only [mul_one_div] at h2
    exact h2

lemma fun_of_J_nonneg (r s : ℕ) (x : ℝ × ℝ) (hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) :
    0 ≤ -Real.log (x.1 * x.2) / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s := by
  simp only [Set.mem_prod, Set.mem_Ioo] at hx
  apply mul_nonneg
  · apply mul_nonneg
    · rw [div_nonneg_iff]
      left
      constructor
      · simp only [Left.nonneg_neg_iff]
        apply Real.log_nonpos <;> nlinarith
      · nlinarith
    · apply pow_nonneg (by linarith)
  · apply pow_nonneg (by linarith)

lemma integrableOn_J_rr (r : ℕ) : MeasureTheory.IntegrableOn
    (fun x ↦ -Real.log (x.1 * x.2) / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ r)
    (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) MeasureTheory.volume := by
  have h := J_ENN_rr r
  simp only [JENN] at h
  rw [MeasureTheory.IntegrableOn, MeasureTheory.Integrable]
  constructor
  · apply AEMeasurable.aestronglyMeasurable
    apply Measurable.aemeasurable
    · apply Measurable.mul
      · apply Measurable.mul
        · apply Measurable.div
          · apply Measurable.neg (Measurable.log (Measurable.mul measurable_fst measurable_snd))
          · apply Measurable.const_sub (Measurable.mul measurable_fst measurable_snd)
        · apply Measurable.pow measurable_fst measurable_const
      · apply Measurable.pow measurable_snd measurable_const
  · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    have h1 : ∫⁻ (a : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ENNReal.ofReal ‖-Real.log (a.1 * a.2) / (1 - a.1 * a.2) * a.1 ^ r * a.2 ^ r‖ =
      ∫⁻ (a : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ENNReal.ofReal (-Real.log (a.1 * a.2) / (1 - a.1 * a.2) * a.1 ^ r * a.2 ^ r) := by
      rw [← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
      congr
      ext x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [hx, ↓reduceIte, norm_mul, norm_div, norm_neg, Real.norm_eq_abs, norm_pow]
        simp only [Set.mem_prod, Set.mem_Ioo] at hx
        rw [ENNReal.ofReal_eq_ofReal_iff]
        · congr 3
          · simp only [abs_eq_neg_self]
            apply Real.log_nonpos <;> nlinarith
          · simp only [abs_eq_self, sub_nonneg]; nlinarith
          · simp only [abs_eq_self]; nlinarith
          · simp only [abs_eq_self]; nlinarith
        · positivity
        · exact fun_of_J_nonneg r r x hx
      · simp only [hx, ↓reduceIte]
    rw [h1, h]
    simp only [one_div, ENNReal.ofReal_lt_top]

theorem J_rr (r : ℕ) :
    J r r =
      2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 -
        2 * ∑ m ∈ Finset.Icc 1 r, 1 / (m : ℝ) ^ 3 := by
  have h := J_ENN_rr r
  simp only [JENN] at h
  rw [J, MeasureTheory.integral_eq_lintegral_of_nonneg_ae, h, ENNReal.toReal_ofReal_eq_iff]
  · simp only [sub_nonneg]
    have hsum_eq : (∑ m ∈ Finset.Icc 1 r, 1 / (m : ℝ) ^ 3) =
        ∑ i ∈ Finset.range r, 1 / ((i : ℝ) + 1) ^ 3 := by
      have h := Finset.sum_Ico_eq_sum_range (m := 1) (n := r + 1)
        (f := fun k => 1 / (k : ℝ) ^ 3)
      simpa [Nat_Ico_succ_right, Nat.cast_add, Nat.cast_one, add_comm] using h
    rw [hsum_eq]
    apply mul_le_mul_of_nonneg_left
    · apply Summable.sum_le_tsum
      · intro i _
        positivity
      · norm_cast
        simp only [Nat.cast_pow]
        rw [summable_nat_add_iff (k := 1) (f := fun k => 1 / (k ^ 3 : ℝ)),
          Real.summable_one_div_nat_pow (p := 3)]
        norm_num
    · norm_num
  · apply MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
    · exact integrableOn_J_rr r
    · rintro x hx -
      apply MeasureTheory.setIntegral_nonneg (by measurability)
      intro y hy
      by_cases h : y ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · exact fun_of_J_nonneg r r y h
      · rw [Set.mem_inter_iff] at hy
        tauto
  · apply AEMeasurable.aestronglyMeasurable
    apply Measurable.aemeasurable
    · apply Measurable.mul
      · apply Measurable.mul
        · apply Measurable.div
          · apply Measurable.neg (Measurable.log (Measurable.mul measurable_fst measurable_snd))
          · apply Measurable.const_sub (Measurable.mul measurable_fst measurable_snd)
        · apply Measurable.pow measurable_fst measurable_const
      · apply Measurable.pow measurable_snd measurable_const

theorem zeta3 : J 0 0 = 2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  simp only [J_rr, one_div, zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, mul_zero,
    sub_zero]

lemma positivity_aux (r s : ℕ) (h : r > s) :
    ∀ (i : ℕ), 0 ≤ 1 / ((r : ℝ) - s) * (1 / (i + s + 1) ^ 2 - 1 / (i + r + 1) ^ 2) := by
  intro n
  apply mul_nonneg
  · simp only [one_div, inv_nonneg, sub_nonneg, Nat.cast_le]; linarith
  · simp only [sub_nonneg]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    simp only [one_mul]
    apply pow_le_pow_left₀ (by linarith)
    simp only [add_le_add_iff_right, add_le_add_iff_left, Nat.cast_le]
    linarith

lemma summable_aux (r : ℕ) : Summable fun (b : ℕ) ↦ 1 / ((b : ℝ) + r + 1) ^ 2 := by
  norm_cast
  simp only [add_assoc, Nat.cast_pow]
  rw [summable_nat_add_iff (k := r + 1) (f := fun k => 1 / (k ^ 2 : ℝ)),
    Real.summable_one_div_nat_pow (p := 2)]
  norm_num

lemma J_ENN_rs (r s : ℕ) (h : r > s) :
    JENN r s = ENNReal.ofReal ((∑ k ∈ Finset.Ioc s r, 1 / (k : ℝ) ^ 2) / (r - s)) := by
  calc
  _ = ∑' (k : ℕ),
      ENNReal.ofReal
        (1 / (r - s) * (1 / (k + s + 1) ^ 2 - 1 / (k + r + 1) ^ 2)) := by
    rw [J_ENN_rs_eq_tsum]
    congr
    ext k
    set x := (k : ℝ) + r + 1
    set y := (k : ℝ) + s + 1
    have hy : y > 0 := by positivity
    have hxy : x - y > 0 := by
      rw [show (x : ℝ) - y = r - s by ring]
      simp only [gt_iff_lt, sub_pos, Nat.cast_lt]
      linarith
    rw [show r - s = (x : ℝ) - y by ring, ENNReal.ofReal_eq_ofReal_iff]
    · rw [div_add_div]
      · rw [div_sub_div]
        · rw [div_mul_div_comm, div_eq_div_iff]
          · ring
          · suffices 0 < x ^ 2 * y * (x * y ^ 2) by linarith
            positivity
          · suffices (x - y) * (y ^ 2 * x ^ 2) > 0 by linarith
            positivity
        · positivity
        · positivity
      · suffices x ^ 2 * y > 0 by linarith
        positivity
      · suffices x * y ^ 2 > 0 by linarith
        positivity
    · positivity
    · apply mul_nonneg (by positivity)
      simp only [sub_nonneg]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      simp only [one_mul]
      apply pow_le_pow_left₀ (by linarith) (by linarith)
  _ = ENNReal.ofReal ((∑ k ∈ Finset.Ioc s r, 1 / (k : ℝ) ^ 2) / (r - s)) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg]
    · rw [ENNReal.ofReal_eq_ofReal_iff]
      · simp only [mul_sub]
        · have hsumm_s : Summable
              (fun n : ℕ => 1 / (r - s) * (1 / (n + (s : ℝ) + 1) ^ 2)) := by
            simp_rw [← smul_eq_mul]
            apply Summable.const_smul
            exact summable_aux s
          have hsumm_r : Summable
              (fun n : ℕ => 1 / (r - s) * (1 / (n + (r : ℝ) + 1) ^ 2)) := by
            simp_rw [← smul_eq_mul]
            apply Summable.const_smul
            exact summable_aux r
          rw [hsumm_s.tsum_sub hsumm_r]
          simp only [sum_div, div_div, ← one_div_mul_one_div_rev]
          apply sub_eq_of_eq_add
          rw [← hsumm_s.sum_add_tsum_nat_add (r - s)]
          congr 1
          · simp only [← Nat.cast_add, add_comm]
            rw [← Finset.sum_Ico_eq_sum_range (n := r) (m := s)
              (f := fun k => 1 / (r - s) * (1 / ((k : ℝ) + 1) ^ 2)),
              ← Nat_Ico_succ_succ s r, ← Finset.sum_Ico_add' (c := 1) (b := r) (a := s)]
            norm_cast
          · congr
            ext n
            congr 1
            norm_cast
            rw [show n + (r - s) + s + 1 = n + r + 1 by omega]
      · apply tsum_nonneg
        exact positivity_aux r s h
      · rw [sum_div]
        apply sum_nonneg
        intro i _
        rw [div_nonneg_iff]
        left
        simp only [one_div, inv_nonneg, Nat.cast_nonneg, pow_nonneg, sub_nonneg, Nat.cast_le,
          true_and]
        linarith
    · exact positivity_aux r s h
    · simp_rw [← smul_eq_mul]
      apply Summable.const_smul
      apply Summable.sub
      · exact summable_aux s
      · exact summable_aux r

lemma integrableOn_J_rs' (r s : ℕ) (h : r > s) : MeasureTheory.IntegrableOn
    (fun x ↦ -Real.log (x.1 * x.2) / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s)
    (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) MeasureTheory.volume := by
  have h₀ := J_ENN_rs r s h
  simp only [JENN] at h₀
  rw [MeasureTheory.IntegrableOn, MeasureTheory.Integrable]
  constructor
  · apply AEMeasurable.aestronglyMeasurable
    apply Measurable.aemeasurable
    · apply Measurable.mul
      · apply Measurable.mul
        · apply Measurable.div
          · apply Measurable.neg (Measurable.log (Measurable.mul measurable_fst measurable_snd))
          · apply Measurable.const_sub (Measurable.mul measurable_fst measurable_snd)
        · apply Measurable.pow measurable_fst measurable_const
      · apply Measurable.pow measurable_snd measurable_const
  · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    have h1 : ∫⁻ (a : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ENNReal.ofReal ‖-Real.log (a.1 * a.2) / (1 - a.1 * a.2) * a.1 ^ r * a.2 ^ s‖ =
      ∫⁻ (a : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ENNReal.ofReal (-Real.log (a.1 * a.2) / (1 - a.1 * a.2) * a.1 ^ r * a.2 ^ s) := by
      rw [← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
      congr
      ext x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [hx, ↓reduceIte, norm_mul, norm_div, norm_neg, Real.norm_eq_abs, norm_pow]
        simp only [Set.mem_prod, Set.mem_Ioo] at hx
        rw [ENNReal.ofReal_eq_ofReal_iff]
        · congr 3
          · simp only [abs_eq_neg_self]
            apply Real.log_nonpos <;> nlinarith
          · simp only [abs_eq_self, sub_nonneg]; nlinarith
          · simp only [abs_eq_self]; nlinarith
          · simp only [abs_eq_self]; nlinarith
        · positivity
        · exact fun_of_J_nonneg r s x hx
      · simp only [hx, ↓reduceIte]
    rw [h1, h₀]
    simp only [one_div, ENNReal.ofReal_lt_top]

lemma J_rs' (r s : ℕ) (h : r > s) :
    J r s = (∑ k ∈ Finset.Ioc s r, 1 / (k : ℝ) ^ 2) / (r - s) := by
  have h₀ := J_ENN_rs r s h
  simp only [JENN] at h₀
  rw [J, MeasureTheory.integral_eq_lintegral_of_nonneg_ae, h₀, ENNReal.toReal_ofReal_eq_iff]
  · rw [sum_div]
    apply sum_nonneg
    intro i _
    rw [div_nonneg_iff]
    left
    simp only [one_div, inv_nonneg, Nat.cast_nonneg, pow_nonneg, sub_nonneg, Nat.cast_le,
      true_and]
    linarith
  · apply MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
    · exact integrableOn_J_rs' r s h
    · rintro x hx -
      apply MeasureTheory.setIntegral_nonneg (by measurability)
      intro y hy
      by_cases h : y ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · exact fun_of_J_nonneg r s y h
      · rw [Set.mem_inter_iff] at hy
        tauto
  · apply AEMeasurable.aestronglyMeasurable
    apply Measurable.aemeasurable
    · apply Measurable.mul
      · apply Measurable.mul
        · apply Measurable.div
          · apply Measurable.neg (Measurable.log (Measurable.mul measurable_fst measurable_snd))
          · apply Measurable.const_sub (Measurable.mul measurable_fst measurable_snd)
        · apply Measurable.pow measurable_fst measurable_const
      · apply Measurable.pow measurable_snd measurable_const

lemma J_ENN_rs_symm (r s : ℕ) : JENN r s = JENN s r := by
  simp only [J_ENN_rs_eq_tsum, add_comm, mul_comm]

lemma integrableOn_J_rs (r s : ℕ) : MeasureTheory.IntegrableOn
    (fun x ↦ -Real.log (x.1 * x.2) / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s)
    (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) MeasureTheory.volume := by
  by_cases h : r > s
  · exact integrableOn_J_rs' r s h
  · by_cases h1 : s = r
    · rw [h1]
      exact integrableOn_J_rr r
    · have h2 : s > r := by
        by_contra!; apply h1; linarith
      rw [MeasureTheory.IntegrableOn, MeasureTheory.Integrable]
      constructor
      · apply AEMeasurable.aestronglyMeasurable
        apply Measurable.aemeasurable
        · apply Measurable.mul
          · apply Measurable.mul
            · apply Measurable.div
              · apply Measurable.neg
                apply Measurable.log
                apply Measurable.mul measurable_fst measurable_snd
              · apply Measurable.const_sub (Measurable.mul measurable_fst measurable_snd)
            · apply Measurable.pow measurable_fst measurable_const
          · apply Measurable.pow measurable_snd measurable_const
      · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
        have h1 : ∫⁻ (a : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
          ENNReal.ofReal ‖-Real.log (a.1 * a.2) / (1 - a.1 * a.2) * a.1 ^ r * a.2 ^ s‖ =
          ∫⁻ (a : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
          ENNReal.ofReal (-Real.log (a.1 * a.2) / (1 - a.1 * a.2) * a.1 ^ r * a.2 ^ s) := by
          rw [← MeasureTheory.lintegral_indicator (by measurability),
            ← MeasureTheory.lintegral_indicator (by measurability)]
          congr
          ext x
          rw [Set.indicator_apply, Set.indicator_apply]
          by_cases hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
          · simp only [hx, ↓reduceIte, norm_mul, norm_div, norm_neg, Real.norm_eq_abs, norm_pow]
            simp only [Set.mem_prod, Set.mem_Ioo] at hx
            rw [ENNReal.ofReal_eq_ofReal_iff]
            · congr 3
              · simp only [abs_eq_neg_self]
                apply Real.log_nonpos <;> nlinarith
              · simp only [abs_eq_self, sub_nonneg]; nlinarith
              · simp only [abs_eq_self]; nlinarith
              · simp only [abs_eq_self]; nlinarith
            · positivity
            · exact fun_of_J_nonneg r s x hx
          · simp only [hx, ↓reduceIte]
        have h₀ := J_ENN_rs s r h2
        rw [J_ENN_rs_symm s r] at h₀
        simp only [JENN] at h₀
        rw [h1, h₀]
        simp only [one_div, ENNReal.ofReal_lt_top]

lemma J_eq_toReal_J_ENN (r s : ℕ) : J r s = (JENN r s).toReal := by
  rw [J, JENN, MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
  · apply MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
    · exact integrableOn_J_rs r s
    · rintro x hx -
      apply MeasureTheory.setIntegral_nonneg (by measurability)
      intro y hy
      by_cases h : y ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · exact fun_of_J_nonneg r s y h
      · rw [Set.mem_inter_iff] at hy
        tauto
  · apply AEMeasurable.aestronglyMeasurable
    apply Measurable.aemeasurable
    · apply Measurable.mul
      · apply Measurable.mul
        · apply Measurable.div
          · apply Measurable.neg (Measurable.log (Measurable.mul measurable_fst measurable_snd))
          · apply Measurable.const_sub (Measurable.mul measurable_fst measurable_snd)
        · apply Measurable.pow measurable_fst measurable_const
      · apply Measurable.pow measurable_snd measurable_const

lemma J_rs_symm (r s : ℕ) : J r s = J s r := by
  rw [J_eq_toReal_J_ENN, J_eq_toReal_J_ENN, J_ENN_rs_symm]

theorem J_rs {r s : ℕ} (h : r ≠ s) : J r s =
    (∑ m ∈ Icc 1 r, 1 / (m : ℝ) ^ 2 - ∑ m ∈ Icc 1 s, 1 / (m : ℝ) ^ 2) / (r - s) := by
  by_cases h1 : r > s
  · simp only [J_rs' r s h1, sub_div, sum_div]
    rw [← Nat_Ico_succ_succ, Finset.sum_Ico_eq_sub]
    · congr 1
      · rw [← Finset.sum_range_add_sum_Ico (n := r + 1) (m := 1) _ (by omega)]
        simp only [range_one, one_div, sum_singleton, CharP.cast_eq_zero, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, inv_zero, zero_div, zero_add]
        rw [Nat_Ico_succ_right]
      · rw [← Finset.sum_range_add_sum_Ico (n := s + 1) (m := 1) _ (by omega)]
        simp only [range_one, one_div, sum_singleton, CharP.cast_eq_zero, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, inv_zero, zero_div, zero_add]
        rw [Nat_Ico_succ_right]
    · linarith
  · simp only [gt_iff_lt, not_lt] at h1
    have h2 : s > r := by
      by_contra!; apply h; linarith
    rw [J_rs_symm, J_rs' s r h2]
    nth_rw 2 [← neg_div_neg_eq]
    simp only [neg_sub]
    congr 1
    rw [← Nat_Ico_succ_succ, Finset.sum_Ico_eq_sub]
    · congr 1
      · rw [← Finset.sum_range_add_sum_Ico (n := s + 1) (m := 1) _ (by omega)]
        simp only [range_one, one_div, sum_singleton, CharP.cast_eq_zero, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, inv_zero, zero_add]
        rw [Nat_Ico_succ_right]
      · rw [← Finset.sum_range_add_sum_Ico (n := r + 1) (m := 1) _ (by omega)]
        simp only [range_one, one_div, sum_singleton, CharP.cast_eq_zero, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, inv_zero, zero_add]
        rw [Nat_Ico_succ_right]
    · linarith

end LeanPool.Zeta3Irrational
