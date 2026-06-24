/-
Copyright (c) 2026 Junqi Liu, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jujian Zhang
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.NormNum.BigOperators

/-!
# Chebyshev estimates needed for the ζ(3) irrationality argument

This file ports the elementary, `sorry`-free Chebyshev estimate used by the
upstream PrimeNumberTheoremAnd development. It gives an eventual bound
`ψ x ≤ 1.13 x`, enough to control the lcm denominator in Beukers' proof.
-/

namespace LeanPool.Zeta3Irrational
namespace ChebyshevAux

open Real Finsupp Finset
open ArithmeticFunction hiding log
open Asymptotics Filter
open scoped Chebyshev

attribute [local fun_prop] DifferentiableAt.differentiableWithinAt

private lemma Finset.Ioc_eq_Icc (M N : ℕ) : Finset.Ioc N M = Finset.Icc (N + 1) M := by
  ext n
  simp only [mem_Ioc, mem_Icc]
  omega

private lemma Ioc_eq_Icc (M N : ℕ) : Finset.Ioc N M = Finset.Icc (N + 1) M :=
  Finset.Ioc_eq_Icc M N

/-- The logarithm of `⌊x⌋₊!`, written as a sum of `log n` for `1 ≤ n ≤ x`. -/
noncomputable def T (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, log n

theorem T.le (x : ℝ) (hx : 1 ≤ x) : T x ≤ x * log x - x + 1 + log x := by
  rw [T, ← Ico_insert_right <| Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne',
    sum_insert right_notMem_Ico]
  have : MonotoneOn log (Set.Icc (1 : ℕ) ⌊x⌋₊) :=
    fun a ha _ _ hab ↦ log_le_log (lt_of_lt_of_le one_pos (by grind)) hab
  have : ∑ n ∈ Finset.Ico 1 ⌊x⌋₊, log n ≤ ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 :=
    calc ∑ n ∈ Finset.Ico 1 ⌊x⌋₊, log n
        ≤ ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t := this.sum_le_integral_Ico <|
          Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne'
      _ = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by simp
  have h1 : (1 : ℝ) ≤ ⌊x⌋₊ := by simp_all
  have h3 : ∀ t ∈ interior (Set.Ici 1),
      DifferentiableWithinAt ℝ (_root_.id * log - _root_.id) (interior (Set.Ici 1)) t := by
    intro t ht
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at ht
    fun_prop (disch := positivity)
  have h4 : ∀ t ∈ interior (Set.Ici 1), 0 ≤ deriv (fun t ↦ t * log t - t) t := by
    intro t ht
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at ht
    have : DifferentiableAt ℝ (fun t ↦ t * log t) t := by fun_prop (disch := positivity)
    have hderiv : deriv (fun t ↦ t * log t - t) t = log t := by
      simp [show (fun t ↦ t * log t - t) = (fun t ↦ t * log t) - _root_.id by rfl,
        deriv_sub this differentiableAt_id, deriv_mul_log (by linarith)]
    exact hderiv ▸ log_nonneg (le_of_lt ht)
  have h5 : ContinuousOn (fun t ↦ t * log t - t) (Set.Ici 1) := by fun_prop
  have h2 : MonotoneOn (fun t ↦ t * log t - t) (Set.Ici 1) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 1) h5 h3 h4
  have : (⌊x⌋₊ : ℝ) * log ⌊x⌋₊ - ⌊x⌋₊ ≤ x * log x - x := by
    exact h2 (Set.mem_Ici.mpr h1) (Set.mem_Ici.mpr hx) <| Nat.floor_le (by grind)
  linarith [log_le_log (by positivity) <| Nat.floor_le (by linarith)]

theorem T.ge (x : ℝ) (hx : 1 ≤ x) : T x ≥ x * log x - x + 1 - log x := by
  have hone_le_floor : 1 ≤ ⌊x⌋₊ := Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne'
  simp only [T, ← Ico_insert_right hone_le_floor, sum_insert right_notMem_Ico]
  have mono_log : MonotoneOn log (Set.Icc (1 : ℕ) ⌊x⌋₊) := fun a ha _ _ hab ↦
    log_le_log (lt_of_lt_of_le one_pos (by simpa using ha.1)) hab
  have h1 : ∀ n ≥ 1, ∑ i ∈ Ico 1 n, log (i + 1 : ℕ) = log n + ∑ i ∈ Ico 1 n, log i := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih => grind [Nat.Ico_succ_right_eq_insert_Ico]
  have sum_shift : ∑ i ∈ Ico 1 ⌊x⌋₊, log (i + 1 : ℕ) =
      log ⌊x⌋₊ + ∑ i ∈ Ico 1 ⌊x⌋₊, log i :=
    h1 ⌊x⌋₊ hone_le_floor
  have int_le_T :
      ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t ≤ log ⌊x⌋₊ + ∑ n ∈ Ico 1 ⌊x⌋₊, log n := by
    linarith [MonotoneOn.integral_le_sum_Ico hone_le_floor mono_log, sum_shift]
  have int_eq : ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t =
      ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by
    simp
  have h2 : ∫ t in (⌊x⌋₊ : ℝ)..x, log t ≤ (x - ⌊x⌋₊) * log x := by
    calc ∫ t in (⌊x⌋₊ : ℝ)..x, log t
      ≤ ∫ _ in (⌊x⌋₊ : ℝ)..x, log x :=
          intervalIntegral.integral_mono_on (Nat.floor_le <| by linarith)
            intervalIntegral.intervalIntegrable_log' intervalIntegrable_const fun t ht ↦
              log_le_log (lt_of_lt_of_le (by positivity) ht.1) ht.2
      _ = (x - ⌊x⌋₊) * log x := by simp
  have target_le_int : x * log x - x + 1 - log x ≤
      ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by
    calc x * log x - x + 1 - log x
        ≤ (x * log x - x + 1) - (x - ⌊x⌋₊) * log x := by
          nlinarith [log_nonneg hx, Nat.lt_floor_add_one x]
      _ ≤ (x * log x - x + 1) - ∫ t in (⌊x⌋₊ : ℝ)..x, log t := by grind
      _ = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by grind [integral_log]
  linarith

theorem T.eq_sum_Lambda (x : ℝ) : T x = ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * ⌊x / n⌋₊ := by
  unfold T
  simp_rw [← log_apply, ← vonMangoldt_mul_zeta]
  rw [← Ioc_eq_Icc, sum_Ioc_mul_zeta_eq_sum]
  simp [Nat.floor_div_natCast]

/-- The floor-sum transform associated to a finitely supported weight `ν`. -/
noncomputable def E (ν : ℕ →₀ ℝ) (x : ℝ) : ℝ :=
  ν.sum (fun m w ↦ w * ⌊x / m⌋₊)

theorem T.weighted_eq_sum (ν : ℕ →₀ ℝ) (x : ℝ) :
    ν.sum (fun m w ↦ w * T (x / m)) = ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * E ν (x / n) := by
  simp_rw [T.eq_sum_Lambda, E, Finsupp.mul_sum]
  rw [← sum_finsetSum_comm]
  apply Finsupp.sum_congr fun y hy ↦ ?_
  rw [Finset.mul_sum]
  by_cases hy : y = 0
  · simp [hy]
  have one_le_y : 1 ≤ (y : ℝ) := by grind [Nat.one_le_cast]
  by_cases hx : x < 1
  · simp [hx, show x / y < 1 from div_lt_one (by linarith) |>.mpr (by linarith)]
  apply sum_subset_zero_on_sdiff
  · apply Icc_subset_Icc_right
    gcongr
    exact div_le_self (by linarith) one_le_y
  · intro t ht
    simp only [Finset.mem_sdiff, Finset.mem_Icc, not_and, not_le] at ht
    simp only [mul_eq_zero, Nat.cast_eq_zero, Nat.floor_eq_zero]
    right
    right
    apply div_lt_one (by linarith) |>.mpr
    have := ht.2 ht.1.1
    apply div_lt_iff₀ (by simp; grind) |>.mpr
    rw [Nat.floor_lt <| div_nonneg (by linarith) (by linarith)] at this
    have := div_lt_iff₀ (by linarith) |>.mp this
    rwa [mul_comm] at this
  · grind

open Finsupp in
/-- Chebyshev's finite-difference weight used to compare `ψ x` with `ψ (x / 6)`. -/
noncomputable def ν : ℕ →₀ ℝ :=
  single 1 1 - single 2 1 - single 3 1 - single 5 1 + single 30 1

private lemma ν_support : ν.support = {1, 2, 3, 5, 30} := by
  norm_num [ν, Finset.ext_iff]
  grind

private lemma ν_sum_mul (f : ℕ → ℝ) :
    ν.sum (fun m w ↦ w * f m) = f 1 - f 2 - f 3 - f 5 + f 30 := by
  rw [ν, sum_add_index (by simp) (by intros; ring)]
  grind only [sum_single_index, sum_sub_index]

private lemma E_nu_expand (y : ℝ) :
    E ν y = ⌊y⌋₊ - ⌊y / 2⌋₊ - ⌊y / 3⌋₊ - ⌊y / 5⌋₊ + ⌊y / 30⌋₊ := by
  rw [E, ν, sum_add_index' (by grind) (by grind)]
  grind [sum_single_index, sum_sub_index]

private lemma floor_div_bounds {y : ℝ} (hy : 0 ≤ y) {k : ℕ} (hk : 1 ≤ k) :
    k * ⌊y / k⌋₊ ≤ ⌊y⌋₊ ∧ ⌊y⌋₊ < k * ⌊y / k⌋₊ + k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hdivnn : 0 ≤ y / k := div_nonneg hy hk'.le
  refine ⟨Nat.le_floor ?_, ?_⟩
  · push_cast
    have := Nat.floor_le hdivnn
    calc ((k : ℝ) * ⌊y / k⌋₊) = k * (y / k) - k * (y / k - ⌊y / k⌋₊) := by ring
      _ ≤ k * (y / k) := by nlinarith [Nat.floor_le hdivnn]
      _ = y := mul_div_cancel₀ _ hk'.ne'
  · have hlt : y / k < ⌊y / k⌋₊ + 1 := Nat.lt_floor_add_one (y / k)
    have hy_lt : y < (k : ℝ) * (⌊y / k⌋₊ + 1) := by linarith [(div_lt_iff₀ hk').mp hlt]
    have : (⌊y⌋₊ : ℝ) < (k : ℝ) * (⌊y / k⌋₊ + 1) := (Nat.floor_le hy).trans_lt hy_lt
    exact_mod_cast this

theorem nu_sum_div_eq_zero : ν.sum (fun n w ↦ w / n) = 0 := by
  norm_num [ν, add_div, sum_add_index', sub_div, sum_sub_index]

theorem E_nu_eq_one (x : ℝ) (hx : x ∈ Set.Ico 1 6) : E ν x = 1 := by
  obtain ⟨h1, h6⟩ := hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  simp only [E_nu_expand, Nat.floor_eq_zero.mpr (by linarith : x / 30 < 1)]
  have hflb : 1 ≤ ⌊x⌋₊ := by rwa [Nat.one_le_floor_iff]
  have hfub : ⌊x⌋₊ ≤ 5 := Nat.lt_succ_iff.mp (Nat.floor_lt' (by grind) |>.mpr h6)
  have h2 := floor_div_bounds hx0 (k := 2) (by norm_num)
  have h3 := floor_div_bounds hx0 (k := 3) (by norm_num)
  have h5 := floor_div_bounds hx0 (k := 5) (by norm_num)
  push_cast at h2 h3 h5
  rw [show ⌊x⌋₊ = ⌊x / 2⌋₊ + ⌊x / 3⌋₊ + ⌊x / 5⌋₊ + 1 by omega]
  grind

theorem E_nu_period (x : ℝ) (hx : x ≥ 0) : E ν (x + 30) = E ν x := by
  have h (k : ℝ) : (x + 30) / k = x / k + 30 / k := by ring
  simp_rw [E_nu_expand, h 2, h 3, h 5, h 30]
  norm_num
  repeat rw [Nat.floor_add_ofNat (by positivity)]
  rw [Nat.floor_add_one (by positivity)]
  grind

theorem E_nu_bound (x : ℝ) (hx : x ≥ 0) : 0 ≤ E ν x ∧ E ν x ≤ 1 := by
  have base (y : ℝ) (hy0 : 0 ≤ y) (hy30 : y < 30) : 0 ≤ E ν y ∧ E ν y ≤ 1 := by
    simp only [E_nu_expand, Nat.floor_eq_zero.mpr (by linarith : y / 30 < 1), Nat.cast_zero,
      add_zero]
    have h2 := floor_div_bounds hy0 (k := 2) (by norm_num)
    have h3 := floor_div_bounds hy0 (k := 3) (by norm_num)
    have h5 := floor_div_bounds hy0 (k := 5) (by norm_num)
    push_cast at h2 h3 h5
    have hfy : ⌊y⌋₊ < 30 := Nat.floor_lt' (by norm_num) |>.mpr (by exact_mod_cast hy30)
    have hlb : ⌊y / 2⌋₊ + ⌊y / 3⌋₊ + ⌊y / 5⌋₊ ≤ ⌊y⌋₊ := by omega
    have hub : ⌊y⌋₊ ≤ ⌊y / 2⌋₊ + ⌊y / 3⌋₊ + ⌊y / 5⌋₊ + 1 := by omega
    have hlb' : ((⌊y / 2⌋₊ + ⌊y / 3⌋₊ + ⌊y / 5⌋₊ : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by
      exact_mod_cast hlb
    have hub' : (⌊y⌋₊ : ℝ) ≤ ((⌊y / 2⌋₊ + ⌊y / 3⌋₊ + ⌊y / 5⌋₊ + 1 : ℕ) : ℝ) := by
      exact_mod_cast hub
    push_cast at hlb' hub'
    refine ⟨by linarith, by linarith⟩
  let y := x - ⌊x / 30⌋₊ * 30
  have hy : 0 ≤ y ∧ y < 30 := ⟨by linarith [Nat.floor_le (by positivity : 0 ≤ x / 30)], by
    linarith [Nat.lt_floor_add_one (x / 30)]⟩
  have hxy : E ν x = E ν y := by
    have : x = y + ⌊x / 30⌋₊ * 30 := by ring
    rw [this]
    induction ⌊x / 30⌋₊ with
    | zero => simp
    | succ n ih =>
        simp [add_mul, ← add_assoc, E_nu_period _ (by linarith : y + n * 30 ≥ 0), ih]
  exact hxy ▸ base y hy.1 hy.2

/-- The weighted logarithmic factorial sum used to bound increments of `ψ`. -/
noncomputable def U (x : ℝ) : ℝ :=
  ν.sum (fun m w ↦ w * T (x / m))

theorem psi_ge_weighted (x : ℝ) (hx : x > 0) : ψ x ≥ U x := by
  unfold U Chebyshev.psi
  rw [T.weighted_eq_sum, ← Ioc_eq_Icc]
  gcongr with i
  have := E_nu_bound (x / i) (div_nonneg hx.le (by simp))
  grw [this.2, mul_one]
  exact vonMangoldt_nonneg

theorem psi_diff_le_weighted (x : ℝ) (hx : x > 0) : ψ x - ψ (x / 6) ≤ U x := by
  unfold U Chebyshev.psi
  rw [T.weighted_eq_sum, ← Ioc_eq_Icc]
  have subset : Ioc 0 ⌊x / 6⌋₊ ⊆ Ioc 0 ⌊x⌋₊ := by
    apply Ioc_subset_Ioc_right
    gcongr
    exact div_le_self hx.le (by norm_num)
  rw [← sum_sdiff_eq_sub subset, ← sum_sdiff subset]
  refine le_add_of_le_of_nonneg (sum_le_sum fun n hn ↦ ?_)
    (sum_nonneg fun n hn ↦ mul_nonneg vonMangoldt_nonneg ?_)
  · rw [E_nu_eq_one, mul_one]
    simp_all only [gt_iff_lt, Finset.mem_sdiff, Finset.mem_Ioc, not_and, not_le, Set.mem_Ico]
    refine ⟨one_le_div (by simp; grind) |>.mpr <| Nat.le_floor_iff hx.le |>.mp hn.1.2, ?_⟩
    have := hn.2 hn.1.1
    apply div_lt_iff₀ (by simp; grind) |>.mpr
    rw [Nat.floor_lt <| div_nonneg (by linarith) (by linarith)] at this
    have := div_lt_iff₀ (by linarith) |>.mp this
    rwa [mul_comm] at this
  · exact E_nu_bound _ (div_nonneg hx.le (by simp)) |>.1

/-- The main linear coefficient in the Chebyshev increment estimate. -/
noncomputable def a : ℝ :=
  -ν.sum (fun m w ↦ w * log m / m)

lemma a_simpl : a = (7 / 15) * Real.log 2 + (3 / 10) * Real.log 3 + (1 / 6) * Real.log 5 := by
  norm_num [a, Finsupp.sum, single_apply, ν_support]
  norm_num [Finset.sum, ν]
  grind [show (30 : ℝ) = 2 * 3 * 5 by ring, log_mul, log_mul]

theorem a_bound : a ∈ Set.Icc 0.92129 0.92130 := by
  norm_num [ChebyshevAux.a_simpl]
  constructor <;>
    nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_three_gt_d9,
      Real.log_three_lt_d9, Real.log_five_gt_d9, Real.log_five_lt_d9]

/-- The error term in Stirling's integral approximation for `T x`. -/
noncomputable def e (x : ℝ) : ℝ :=
  T x - (x * log x - x + 1)

lemma U_bound.lemma_1 (x : ℝ) : T x = x * log x - x + 1 + e x := by
  unfold e
  ring

lemma U_bound.lemma_2 (x : ℝ) (hx : 1 ≤ x) : |e x| ≤ log x := by
  rw [abs_le]
  unfold e
  constructor <;> linarith [T.ge x hx, T.le x hx]

lemma U_bound.lemma_3 (x : ℝ) :
    U x = ν.sum (fun m w ↦ w * ((x / m) * log (x / m))) -
          ν.sum (fun m w ↦ w * (x / m)) +
          ν.sum (fun _m w ↦ w) +
          ν.sum (fun m w ↦ w * e (x / m)) := by
  simp [U, Finsupp.sum, U_bound.lemma_1, sub_eq_add_neg, add_mul, mul_comm, sum_add_distrib]

lemma U_bound.lemma_4 (x : ℝ) (hx : 0 < x) :
    ν.sum (fun m w ↦ w * ((x / m) * log (x / m))) = a * x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have ha : a = -(log 1 / 1 - log 2 / 2 - log 3 / 3 - log 5 / 5 + log 30 / 30) := by
    simp_rw [a, mul_div_assoc]
    rw [ν_sum_mul (fun m ↦ log m / m)]
    push_cast
    rfl
  rw [ν_sum_mul (fun m ↦ (x / m) * log (x / m)), ha]
  simp [Real.log_div hx0]
  ring

lemma U_bound.lemma_5 (x : ℝ) : ν.sum (fun m w ↦ w * (x / m)) = 0 := by
  rw [ν_sum_mul (fun m ↦ x / m)]
  push_cast
  ring

lemma U_bound.lemma_6 : ν.sum (fun _ w ↦ w) = (-1 : ℝ) := by
  have := ν_sum_mul (fun _ ↦ (1 : ℝ))
  simp at this
  linarith

lemma Finsupp.abs_sum_le (A : Type*) (ν : A →₀ ℝ) (g : A → ℝ → ℝ) : |ν.sum g| ≤ ν.sum |g| := by
  simp_rw [Finsupp.sum.eq_1]
  exact abs_sum_le_sum_abs (fun i ↦ g i (ν i)) ν.support

private lemma log_30_gt : (3.401197 : ℝ) < log 30 := by
  have h30 : log (30 : ℝ) = log 2 + log 3 + log 5 := by
    rw [show (30 : ℝ) = (2 * 3) * 5 by norm_num, log_mul, log_mul] <;> norm_num
  nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]

theorem U_bound (x : ℝ) (hx : 30 ≤ x) : |U x - a * x| ≤ 5 * log x - 5 := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  rw [U_bound.lemma_3, U_bound.lemma_4 x hxpos]
  ring_nf
  have hlin : ν.sum (fun m w ↦ x * w * (↑m)⁻¹) = 0 := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm] using U_bound.lemma_5 x
  rw [hlin]
  ring_nf
  rw [U_bound.lemma_6]
  grw [abs_add_le, Finsupp.abs_sum_le]
  norm_num
  have hsupp_eq : ν.support = {1, 2, 3, 5, 30} := ν_support
  have hmem_of_supp : ∀ i ∈ ν.support, 0 < i ∧ i ≤ 30 := fun i hi ↦ by
    have : i ∈ ({1, 2, 3, 5, 30} : Finset ℕ) := hsupp_eq ▸ hi
    simp only [mem_insert, mem_singleton] at this
    constructor <;> omega
  have h : ν.sum |fun m w ↦ w * e (x * (↑m)⁻¹)| ≤
      ν.sum (fun m w ↦ |w| * log (x * (↑m)⁻¹)) := by
    apply Finsupp.sum_le_sum
    intro i hi
    simp only [Pi.abs_apply, abs_mul]
    obtain ⟨hi_pos, hi_le⟩ := hmem_of_supp i hi
    have hxi : 1 ≤ x * (↑i)⁻¹ := by
      rw [le_mul_inv_iff₀ (by exact_mod_cast hi_pos)]
      linarith [show (i : ℝ) ≤ 30 from by exact_mod_cast hi_le]
    gcongr
    exact U_bound.lemma_2 _ hxi
  grw [h]
  have hlog_split : ν.sum (fun m w ↦ |w| * log (x * (m : ℝ)⁻¹)) =
      log x * ν.sum (fun m w ↦ |w|) - ν.sum (fun m w ↦ |w| * log (↑m : ℝ)) := by
    simp only [Finsupp.sum]
    conv_rhs => rw [Finset.mul_sum, ← sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast (hmem_of_supp m hm).1
    rw [← div_eq_mul_inv, Real.log_div (ne_of_gt hxpos) (ne_of_gt hm_pos)]
    ring
  rw [hlog_split]
  have expand_sum : ∀ f : ℕ → ℝ → ℝ, (∀ n, f n 0 = 0) →
      ν.sum f = f 1 1 + f 2 (-1) + f 3 (-1) + f 5 (-1) + f 30 1 := by
    intro f hf
    rw [Finsupp.sum_of_support_subset _ hsupp_eq.le _ (by intros; simp [hf])]
    simp only [sum_insert (by decide : (1 : ℕ) ∉ ({2, 3, 5, 30} : Finset ℕ)),
      sum_insert (by decide : (2 : ℕ) ∉ ({3, 5, 30} : Finset ℕ)),
      sum_insert (by decide : (3 : ℕ) ∉ ({5, 30} : Finset ℕ)),
      sum_insert (by decide : (5 : ℕ) ∉ ({30} : Finset ℕ)), sum_singleton, ν,
      Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_apply]
    norm_num
    ring
  have habs : ν.sum (fun m w ↦ |w|) = 5 := by
    rw [expand_sum _ (by intros; simp)]
    norm_num
  have hgeq6 : ν.sum (fun m w ↦ |w| * log m) ≥ 6 := by
    have hsum_eq : ν.sum (fun m w ↦ |w| * log (m : ℝ)) =
        log 2 + log 3 + log 5 + log 30 := by
      rw [expand_sum _ (by intros; simp)]
      simp [log_one]
    linarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9, log_30_gt]
  grw [hgeq6]
  rw [habs]
  linarith

theorem psi_diff_upper (x : ℝ) (hx : 30 ≤ x) : ψ x - ψ (x / 6) ≤ a * x + 5 * log x - 5 := by
  have h2 := abs_sub_le_iff.mp (U_bound x hx)
  linarith [psi_diff_le_weighted x (by linarith), h2.2]

theorem psi_upper_coarse (x : ℝ) (hx : 30 ≤ x) :
    ψ x ≤ 6 * a * x / 5 +
      (⌊log (x / 5) / log 6⌋₊ : ℝ) * (5 * log x - 5) + 180 := by
  have rpow_key : (30 : ℝ) * 6 ^ (log (x / 5) / log 6 - 1) = x := by
    rw [rpow_def_of_pos (by norm_num)]
    field_simp
    rw [exp_sub, exp_log, exp_log] <;> linarith
  have telescope (n : ℕ) : ψ x - ψ (x / 6 ^ n) =
      ∑ i ∈ Ico 0 n, (ψ (x / 6 ^ i) - ψ (x / 6 ^ (i + 1))) := by
    induction n with
    | zero => simp
    | succ n hn =>
      rw [sum_Ico_succ_top <| Nat.zero_le n, ← hn]
      ring
  have bound (n : ℕ) (h : ∀ i < n, 30 ≤ x / 6 ^ i) :
      ψ x - ψ (x / 6 ^ n) ≤
        ∑ i ∈ Ico 0 n, (a * x / 6 ^ i + 5 * log (x / 6 ^ i) - 5) := by
    rw [telescope]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    convert! psi_diff_upper (x / 6 ^ i) (by grind) using 3
    · field
    · ring
  replace bound (n : ℕ) (h : ∀ i < n, 30 ≤ x / 6 ^ i) :
      ψ x - ψ (x / 6 ^ n) ≤ ∑ i ∈ Ico 0 n, (a * x / 6 ^ i + 5 * log x - 5) := by
    grw [bound n h]
    apply Finset.sum_le_sum fun i hi ↦ ?_
    gcongr
    bound
  let n := ⌊log (x / 5) / log 6⌋₊
  specialize bound n ?_
  · intro i hi
    apply le_div_iff₀ (by simp) |>.mpr
    trans (30 * 6 ^ (n - 1))
    · gcongr <;> grind
    · trans (30 * 6 ^ (log (x / 5) / log 6 - 1))
      · rw [← rpow_natCast, Nat.cast_sub]
        · gcongr
          · norm_num
          · refine Nat.floor_le <| div_nonneg ?_ ?_ <;> apply log_nonneg <;> linarith
          · norm_cast
        · apply Nat.le_floor
          norm_cast
          apply le_div_iff₀ (log_pos (by norm_num : (1 : ℝ) < 6)) |>.mpr
          rw [one_mul]
          gcongr
          linarith
      · exact rpow_key.le
  simp_rw [← add_sub, sum_add_distrib, sum_const, Nat.Ico_zero_eq_range, Finset.card_range,
    nsmul_eq_mul, tsub_le_iff_right] at bound
  apply bound.trans
  conv => lhs; arg 1; arg 1; arg 2; ext i; rw [← mul_one_div, ← one_div_pow]
  rw [← Finset.mul_sum, geom_sum_eq (by norm_num)]
  norm_num
  have h_tail : x / 6 ^ n ≤ 30 := by
    apply div_le_iff₀ (by simp) |>.mpr
    trans 30 * 6 ^ (log (x / 5) / log 6 - 1)
    · exact rpow_key.ge
    · rw [← rpow_natCast]
      gcongr
      · norm_num
      · exact Nat.sub_one_lt_floor _ |>.le
  have h_tail_nonneg : 0 ≤ x / 6 ^ n := by positivity
  calc
    a * x * (((1 / 6 : ℝ) ^ n - 1) / -(5 / 6)) + ↑n * (5 * log x - 5) +
        ψ (x / 6 ^ n)
        = ψ (x / 6 ^ n) + (a * x * (1 - (1 / 6) ^ n) / (1 - 1 / 6) +
          ↑n * (5 * log x - 5)) := by ring
    _ ≤ 6 * (x / 6 ^ n) +
          (a * x * (1 - (1 / 6) ^ n) / (1 - 1 / 6) +
        ↑n * (5 * log x - 5)) := by
          gcongr
          exact (Chebyshev.psi_le_const_mul_self h_tail_nonneg).trans (by
            have : log 4 ≤ (2 : ℝ) := by
              rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 4)]
              have h : (4 : ℝ) < Real.exp 2 := by
                rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
                nlinarith [Real.exp_one_gt_two]
              exact h.le
            nlinarith)
    _ ≤ 6 * a * x / 5 + ↑n * (5 * log x - 5) + 180 := by
      have hnonneg : 0 ≤ a * x * (1 / 6) ^ n := by
        have ha_nonneg : 0 ≤ a := by linarith [a_bound.1]
        positivity
      have htail6 : 6 * (x / 6 ^ n) ≤ 180 := by nlinarith
      have hmain :
          a * x * (1 - (1 / 6 : ℝ) ^ n) / (1 - 1 / 6) ≤ 6 * a * x / 5 := by
        norm_num
        nlinarith
      nlinarith

theorem eventually_psi_le_mul :
    ∀ᶠ x : ℝ in atTop, ψ x ≤ (113 / 100 : ℝ) * x := by
  have h_logsq : (fun x : ℝ ↦ 5 * (log x) ^ 2 + 180) =o[atTop] (fun x : ℝ ↦ x) :=
    ((Real.isLittleO_pow_log_id_atTop (n := 2)).const_mul_left (5 : ℝ)).add
      (isLittleO_const_id_atTop (180 : ℝ))
  have hsmall := h_logsq.bound (c := 1 / 50) (by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop (30 : ℝ), eventually_ge_atTop (5 : ℝ),
    eventually_ge_atTop (3 : ℝ)] with x hxsmall hx30 hx5 hx3
  have hxpos : 0 < x := by linarith
  have hlog_nonneg : 0 ≤ log x := log_nonneg (by linarith)
  have hlog1 : 1 ≤ log x := by
    rw [le_log_iff_exp_le hxpos]
    exact le_trans Real.exp_one_lt_three.le hx3
  have hlog6 : 1 ≤ log 6 := by
    rw [le_log_iff_exp_le (by norm_num : (0 : ℝ) < 6)]
    exact le_trans Real.exp_one_lt_three.le (by norm_num)
  have hrem_small : 5 * (log x) ^ 2 + 180 ≤ (1 / 50 : ℝ) * x := by
    have hnonneg : 0 ≤ 5 * (log x) ^ 2 + 180 := by nlinarith [sq_nonneg (log x)]
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hxpos.le] using hxsmall
  have hfloor_le :
      (⌊log (x / 5) / log 6⌋₊ : ℝ) ≤ log (x / 5) / log 6 := by
    apply Nat.floor_le
    apply div_nonneg
    · apply log_nonneg
      exact one_le_div (by norm_num : (0 : ℝ) < 5) |>.mpr hx5
    · linarith
  have hlog_div_le : log (x / 5) ≤ log x := by
    apply log_le_log
    · positivity
    · exact div_le_self hxpos.le (by norm_num : (1 : ℝ) ≤ 5)
  have hmiddle :
      (⌊log (x / 5) / log 6⌋₊ : ℝ) * (5 * log x - 5) ≤ 5 * (log x) ^ 2 := by
    have hfactor_nonneg : 0 ≤ 5 * log x - 5 := by nlinarith
    have hdiv_le_log : log (x / 5) / log 6 ≤ log x :=
      div_le_of_le_mul₀ (by linarith) hlog_nonneg
        (by nlinarith [hlog_div_le, hlog6, hlog_nonneg])
    calc
      (⌊log (x / 5) / log 6⌋₊ : ℝ) * (5 * log x - 5)
          ≤ (log (x / 5) / log 6) * (5 * log x - 5) :=
            mul_le_mul_of_nonneg_right hfloor_le hfactor_nonneg
      _ ≤ log x * (5 * log x - 5) := by
        exact mul_le_mul_of_nonneg_right hdiv_le_log hfactor_nonneg
      _ ≤ 5 * (log x) ^ 2 := by nlinarith
  calc
    ψ x ≤ 6 * a * x / 5 + (⌊log (x / 5) / log 6⌋₊ : ℝ) * (5 * log x - 5) + 180 :=
      psi_upper_coarse x hx30
    _ ≤ (111 / 100 : ℝ) * x + (5 * (log x) ^ 2 + 180) := by
      have ha : 6 * a / 5 ≤ (111 / 100 : ℝ) := by nlinarith [a_bound.2]
      nlinarith
    _ ≤ (111 / 100 : ℝ) * x + (1 / 50 : ℝ) * x := by gcongr
    _ = (113 / 100 : ℝ) * x := by ring

end ChebyshevAux
end LeanPool.Zeta3Irrational
