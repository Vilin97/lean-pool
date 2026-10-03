/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Table.Intervals
import LeanPool.Zeta5Irrational.Table.Tail
import LeanPool.Zeta5Irrational.Certificates
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Int.Star
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
public import LeanPool.Zeta5Irrational.EnergyRaw
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

/-! # A variant of the configuration inequality (6.9)

From the raw inequality `energy_raw` with `ε = K⁻⁶`, the potential inequality `potential_ineq`
(Lemma 6.1), the tail bound (6.8) and the bound for the regularisation error we obtain
`energy_ineq_final`: for every configuration of `h = 37 n` positive, pairwise distinct points,

`2∑_{i<j} log|tᵢ - tⱼ| - K∑V(tᵢ) + ∑√tᵢ ≤ (λM₀ - I(ρ))K² + 5h + 6h log K`.

The paper uses `(120 + √2)h + 2h log K` for the lower-order terms and `ε = K⁻²`.
Here the different regularisation estimate and `ε = K⁻⁶` give `5h + 6h log K`.
-/

public section

open MeasureTheory Set Real Filter Topology Finset

namespace Zeta5Irrational

lemma sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- The regularisation error at one interval. -/
lemma errj_le {ε t m r : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 < t) (hm : 0 < m ∧ m < 2)
    (hr : 1 / 450 ≤ r) : errj ε t m r ≤ Real.sqrt ε * (637 * Real.sqrt t + 1457) := by
  unfold errj
  have hr0 : 0 < r := by linarith
  have hse : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hst : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hεs : ε ≤ Real.sqrt ε := by rw [Real.le_sqrt hε.le hε.le]; nlinarith
  have h1 : ε / r ≤ 450 * ε := by rw [div_le_iff₀ hr0]; nlinarith
  have habs : |t - m| ≤ t + 2 := by rw [abs_le]; constructor <;> linarith
  have h2 : ε / r * ((ε + 2 * |t - m|) / r) ≤ 450 ^ 2 * ε * (2 * t + 5) := by
    have : (ε + 2 * |t - m|) / r ≤ 450 * (2 * t + 5) := by rw [div_le_iff₀ hr0]; nlinarith
    calc
      ε / r * ((ε + 2 * |t - m|) / r) ≤ (450 * ε) * (450 * (2 * t + 5)) :=
        mul_le_mul h1 this (by positivity) (by positivity)
      _ = 450 ^ 2 * ε * (2 * t + 5) := by ring
  have hs2 : Real.sqrt 2 ≤ 14143 / 10000 := by rw [Real.sqrt_le_iff]; constructor <;> norm_num
  have hs5 : Real.sqrt 5 ≤ 22361 / 10000 := by rw [Real.sqrt_le_iff]; constructor <;> norm_num
  have h3 :
    Real.sqrt (ε / r * ((ε + 2 * |t - m|) / r)) ≤
      450 * Real.sqrt ε * (14143 / 10000 * Real.sqrt t + 22361 / 10000) := by
    calc
      Real.sqrt (ε / r * ((ε + 2 * |t - m|) / r)) ≤ Real.sqrt (450 ^ 2 * ε * (2 * t + 5)) :=
        Real.sqrt_le_sqrt h2
      _ = 450 * Real.sqrt ε * Real.sqrt (2 * t + 5) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by norm_num)]
      _ ≤ 450 * Real.sqrt ε * (Real.sqrt (2 * t) + Real.sqrt 5) := by
        apply mul_le_mul_of_nonneg_left (sqrt_add_le' (by positivity) (by norm_num))
        positivity
      _ ≤ 450 * Real.sqrt ε * (14143 / 10000 * Real.sqrt t + 22361 / 10000) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [Real.sqrt_mul (by norm_num)]
        have := mul_le_mul_of_nonneg_right hs2 hst
        linarith
  nlinarith

/-- The total mass of the sixteen weights. -/
lemma sum_cρ_fin : ∑ j : Fin 16, cρ (j + 1) = lam := by
  rw [← Sρ_sixteen, Sρ, sum_Icc_eq_sum_range', Fin.sum_univ_eq_sum_range (fun j => cρ (j + 1))]

/-- The total regularisation error. -/
lemma Err_le {ε t : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 < t) :
    Err ε t ≤ Real.sqrt ε * (590 * Real.sqrt t + 1348) := by
  unfold Err
  have hse : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hst : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  calc
    ∑ j : Fin 16, cρ (j + 1) * errj ε t (mρ (j + 1)) (rρ (j + 1)) ≤
        ∑ j : Fin 16, cρ (j + 1) * (Real.sqrt ε * (637 * Real.sqrt t + 1457)) := by
      refine Finset.sum_le_sum fun j _ => ?_
      exact
        mul_le_mul_of_nonneg_left (errj_le hε hε1 ht (mρ_bounds j) (rρ_ge j))
          (cρ_pos _ (by simp only [Finset.mem_Icc]; omega)).le
    _ = lam * (Real.sqrt ε * (637 * Real.sqrt t + 1457)) := by rw [← Finset.sum_mul, sum_cρ_fin]
    _ ≤ _ := by
      simp only [lam]
      nlinarith

/-- The tail bound with an extra `c √t`, `0 ≤ c ≤ 1/20`. -/
lemma potential_ineq_tail' {t c : ℝ} (ht : 2 ≤ t) (_hc0 : 0 ≤ c) (hc : c ≤ 1 / 20) :
    2 * Uρ t - Vfield t + c * Real.sqrt t ≤ M0 := by
  have ht0 : 0 < t := by linarith
  have h1 := Uρ_le_log ht
  have h2 := Vfield_ge_tail ht
  have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hs2 : (141 / 100 : ℝ) ≤ Real.sqrt t :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num; linarith)
  have hlog : Real.log t ≤ 2 * (Real.sqrt t - 1) := by
    have e : Real.log (Real.sqrt t ^ 2) = 2 * Real.log (Real.sqrt t) := by
      rw [Real.log_pow];
      norm_num
    rw [hs] at e
    rw [e]
    linarith [Real.log_le_sub_one_of_pos hs0]
  have hq : (3 / 40 : ℝ) ^ 2 / t ≤ (3 / 40) ^ 2 / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) ht
  have hpi := Real.pi_gt_d2
  have hprod : 314 / 100 * Real.sqrt t ≤ Real.pi * Real.sqrt t :=
    mul_le_mul_of_nonneg_right (by norm_num at hpi; linarith) hs0.le
  have hcs : c * Real.sqrt t ≤ 1 / 20 * Real.sqrt t := mul_le_mul_of_nonneg_right hc hs0.le
  unfold M0
  linarith

/-- A variant of (6.7): `2Uρ(t) - V(t) + (2/K)√t ≤ M₀ + 3/K` for `K ≥ 40`.
The paper instead uses `√t/K` and `√2/K`, and assumes `K ≥ 2`. -/
lemma pointwise_bound {K t : ℝ} (hK : 40 ≤ K) (ht : 0 < t) :
    2 * Uρ t - Vfield t + 2 / K * Real.sqrt t ≤ M0 + 3 / K := by
  have hK0 : 0 < K := by linarith
  rcases le_or_gt t 2 with h | h
  · have h1 := potential_ineq t ht
    have hs : Real.sqrt t ≤ 3 / 2 := by
      rw [Real.sqrt_le_iff];
      constructor <;> [norm_num; nlinarith]
    have : 2 / K * Real.sqrt t ≤ 3 / K := by
      rw [show 3 / K = 2 / K * (3 / 2) by ring]
      exact mul_le_mul_of_nonneg_left hs (by positivity)
    exact add_le_add h1 this
  · have h1 :=
      potential_ineq_tail' (c := 2 / K) h.le (by positivity) (by rw [div_le_iff₀ hK0]; linarith)
    have : (0 : ℝ) ≤ 3 / K := by positivity
    linarith

/-- The double sum over all ordered pairs equals twice the sum over `i < j`. -/
lemma sum_pairs_eq {h : ℕ} (t : Fin h → ℝ) :
    ∑ i, ∑ i', Real.log |t i - t i'| = ∑ i, ∑ j ∈ Finset.Ioi i, 2 * Real.log |t j - t i| := by
  have hsplit :
    ∀ i : Fin h,
      ∑ i', Real.log |t i - t i'| =
        ∑ i' ∈ Finset.Iio i, Real.log |t i - t i'| + ∑ i' ∈ Finset.Ioi i, Real.log |t i - t i'| :=
  by
    intro i
    have e1 : (Finset.univ : Finset (Fin h)).filter (fun x => x < i) = Finset.Iio i := by
      ext x;
      simp
    have e2 : (Finset.univ : Finset (Fin h)).filter (fun x => ¬x < i) = Finset.Ici i := by
      ext x;
      simp [not_lt]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => x < i), e1, e2, ←
      Finset.add_sum_Ioi_eq_sum_Ici, sub_self, abs_zero, Real.log_zero, zero_add]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  have hcomm :
    ∑ i, ∑ i' ∈ Finset.Iio i, Real.log |t i - t i'| =
      ∑ i, ∑ i' ∈ Finset.Ioi i, Real.log |t i - t i'| := by
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun i' => Finset.Ioi i')]
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
      rw [abs_sub_comm]
    · intro x y
      simp only [Finset.mem_univ, Finset.mem_Iio, Finset.mem_Ioi, true_and, and_true]
  rw [hcomm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [abs_sub_comm]; ring

/-- A variant of **(6.9)** with lower-order terms `5h + 6h log K` instead of
`(120 + √2)h + 2h log K`, for positive pairwise distinct configurations and `K = 40n`. -/
theorem energy_ineq_final (n : ℕ) (hn : 0 < n) (t : Fin (37 * n) → ℝ) (ht : ∀ i, 0 < t i)
    (hinj : Function.Injective t) :
    (∑ i, ∑ j ∈ Finset.Ioi i, 2 * Real.log |t j - t i|) - Kr n * ∑ i, Vfield (t i) +
        ∑ i, Real.sqrt (t i) ≤
      (lam * M0 - Irho) * Kr n ^ 2 + 5 * (37 * n) + 6 * (37 * n) * Real.log (Kr n) := by
  have hK : 40 ≤ Kr n := by
    simp only [Kr]; have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hK0 : 0 < Kr n := by linarith
  set K := Kr n with hKdef
  set ε : ℝ := K ^ (-6 : ℤ) with hε_def
  have hε : 0 < ε := by rw [hε_def]; positivity
  have hε1 : ε ≤ 1 := by
    rw [hε_def, zpow_neg, inv_le_one_iff₀]
    right; exact one_le_zpow₀ (by linarith) (by norm_num)
  have hsqrtε : Real.sqrt ε = K ^ (-3 : ℤ) := by
    have e : (K ^ (-3 : ℤ)) ^ 2 = ε := by rw [hε_def, ← zpow_natCast, ← zpow_mul]; norm_num
    rw [← e, Real.sqrt_sq (by positivity)]
  have hlogε : Real.log ε = -6 * Real.log K := by rw [hε_def, Real.log_zpow]; push_cast; ring
  have hraw := energy_raw n hn t hinj hε
  rw [← hKdef, sum_pairs_eq,
    hlogε] at hraw
        -- bound the error terms
  have hErr : ∀ i, Err ε (t i) ≤ 1 / K ^ 3 * (590 * Real.sqrt (t i) + 1348) := fun i =>
    by
    have := Err_le hε hε1 (ht i)
    rw [hsqrtε, zpow_neg, zpow_ofNat] at this
    rw [one_div]; exact this
  have hK2 : 1 / K ^ 2 ≤ 1 / 1600 :=
    one_div_le_one_div_of_le (by norm_num)
      (by nlinarith)
        -- pointwise
  have hpt :
    ∀ i, 2 * K * (Uρ (t i) + Err ε (t i)) - K * Vfield (t i) + Real.sqrt (t i) ≤ K * M0 + 5 := by
    intro i
    have h1 := pointwise_bound hK (ht i)
    have h2 := hErr i
    have hs := Real.sqrt_nonneg (t i)
    have e1 :
      2 * K * (1 / K ^ 3 * (590 * Real.sqrt (t i) + 1348)) =
        1 / K ^ 2 * (1180 * Real.sqrt (t i) + 2696) :=
      by field_simp; ring
    have e2 :
      1 / K ^ 2 * (1180 * Real.sqrt (t i) + 2696) ≤ 1 / 1600 * (1180 * Real.sqrt (t i) + 2696) :=
      mul_le_mul_of_nonneg_right hK2 (by positivity)
    have e3 : K * (2 / K * Real.sqrt (t i)) = 2 * Real.sqrt (t i) := by field_simp
    have e4 : K * (3 / K) = 3 := by field_simp
    have h1' := mul_le_mul_of_nonneg_left h1 hK0.le
    rw [mul_add, mul_add, mul_sub, e3, e4] at h1'
    have h2' := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * K)
    rw [e1] at h2'
    nlinarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt i
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  simp only [Finset.sum_add_distrib] at hraw
  have hlam : ((37 * n : ℕ) : ℝ) * (K * M0) = lam * M0 * K ^ 2 := by
    rw [hKdef];
    simp only [Kr, lam]; push_cast; ring
  rw [hlam] at hsum
  push_cast at hraw hsum ⊢
  linarith [hraw, hsum]

end Zeta5Irrational
