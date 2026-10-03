/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.PrimeSumStep
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Prime sums and integrals

For `f` Lipschitz on `[a, b]` (`0 < a < b`), `psum f a b K / K² ≤ ∫_a^b f(x)/x³ dx + ε` for all
large `K`; and the piecewise version for `f` given by Lipschitz pieces on `[t_i, t_{i+1})`.
-/

public section

open Finset Filter Topology Set intervalIntegral MeasureTheory

namespace Zeta5Irrational

lemma integral_inv_cube {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in a..b, x ^ (-3 : ℤ) = (1 / a ^ 2 - 1 / b ^ 2) / 2 := by
  rw [integral_zpow (Or.inr ⟨by norm_num, fun h => ?_⟩)]
  · norm_num
    field_simp
    ring
  · rcases le_total a b with hab | hab
    · rw [uIcc_of_le hab] at h; linarith [h.1]
    · rw [uIcc_of_ge hab] at h; linarith [h.1]

/-- Upper bound for `psum` by the integral, for `f` Lipschitz on `[a, b]`. -/
theorem psum_le_integral {f : ℝ → ℝ} {a b L : ℝ} (ha : 0 < a) (hab : a < b) (hL : 0 ≤ L)
    (hcont : ContinuousOn f (Icc a b))
    (hLip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |f x - f y| ≤ L * |x - y|) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ K : ℝ in atTop, psum f a b K / K ^ 2 ≤ (∫ x in a..b, f x / x ^ 3) + ε := by
  -- choose the mesh
  obtain ⟨r, hr⟩ := exists_nat_gt (2 * L * (b - a) * (1 / a ^ 2 - 1 / b ^ 2) / ε)
  have hr0 : 0 < r := by
    have : (0 : ℝ) ≤ 2 * L * (b - a) * (1 / a ^ 2 - 1 / b ^ 2) / ε := by
      have : 1 / b ^ 2 ≤ 1 / a ^ 2 := one_div_le_one_div_of_le (by positivity) (by nlinarith)
      have : 0 ≤ 1 / a ^ 2 - 1 / b ^ 2 := by linarith
      positivity
    have : (0 : ℝ) < r := lt_of_le_of_lt this hr
    exact_mod_cast this
  set δ := (b - a) / r with hδ
  have hδ0 : 0 < δ := by positivity
  set c : ℕ → ℝ := fun j => a + j * δ with hc
  have hc0 : c 0 = a := by simp [hc]
  have hcr : c r = b := by simp only [hc]; rw [hδ]; field_simp; ring
  have hmono : ∀ j < r, c j < c (j + 1) := by intro j _; simp only [hc]; push_cast; linarith
  have hcle : ∀ j, j ≤ r → a ≤ c j ∧ c j ≤ b := by
    intro j hj
    simp only [hc]
    constructor
    · have : (0 : ℝ) ≤ j * δ := by positivity
      linarith
    · have : (j : ℝ) * δ ≤ r * δ := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hδ0.le
      have : (r : ℝ) * δ = b - a := by rw [hδ]; field_simp
      linarith
  set v : ℕ → ℝ := fun j => f (c j) + L * δ with hv
  have hf : ∀ j < r, ∀ x ∈ Ico (c j) (c (j + 1)), f x ≤ v j := by
    intro j hj x hx
    have hcj := hcle j hj.le
    have hcj1 := hcle (j + 1) hj
    have hxI : x ∈ Icc a b := ⟨hcj.1.trans hx.1, hx.2.le.trans hcj1.2⟩
    have := hLip x hxI (c j) ⟨hcj.1, hcj.2⟩
    have hd : |x - c j| ≤ δ := by
      rw [abs_of_nonneg (by linarith [hx.1])]
      have : c (j + 1) = c j + δ := by simp only [hc]; push_cast; ring
      linarith [hx.2]
    simp only [hv]
    have := abs_le.mp this
    nlinarith
      -- the Darboux sum is at most the integral plus the error
  have hD :
    (∑ j ∈ range r, v j * ((1 / c j ^ 2 - 1 / c (j + 1) ^ 2) / 2)) ≤
      (∫ x in a..b, f x / x ^ 3) + 2 * L * δ * ((1 / a ^ 2 - 1 / b ^ 2) / 2) := by
    have hint :
      ∀ j < r,
        IntervalIntegrable (fun x => (f x + 2 * L * δ) * x ^ (-3 : ℤ)) volume (c j) (c (j + 1)) :=
  by
      intro j hj
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (hmono j hj).le]
      have hsub : Icc (c j) (c (j + 1)) ⊆ Icc a b :=
        Icc_subset_Icc (hcle j hj.le).1 (hcle (j + 1) hj).2
      refine ((hcont.mono hsub).add continuousOn_const).mul ?_
      exact
        continuousOn_id.zpow₀ (-3) fun x hx =>
          Or.inl (ha.trans_le ((hcle j hj.le).1.trans hx.1)).ne'
    have h1 :
      ∀ j < r,
        v j * ((1 / c j ^ 2 - 1 / c (j + 1) ^ 2) / 2) ≤
          ∫ x in c j..c (j + 1), (f x + 2 * L * δ) * x ^ (-3 : ℤ) := by
      intro j hj
      have hcj := hcle j hj.le
      have hcj1 := hcle (j + 1) hj
      rw [← integral_inv_cube (ha.trans_le hcj.1) (ha.trans_le hcj1.1), ←
        intervalIntegral.integral_const_mul]
      apply integral_mono_on (hmono j hj).le
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le (hmono j hj).le]
        exact
          continuousOn_const.mul
            (continuousOn_id.zpow₀ (-3) fun x hx => Or.inl (ha.trans_le (hcj.1.trans hx.1)).ne')
      · exact hint j hj
      intro x hx
      have hxI : x ∈ Icc a b := ⟨hcj.1.trans hx.1, hx.2.trans hcj1.2⟩
      have hx0 : 0 < x := ha.trans_le hxI.1
      have hLx := hLip (c j) ⟨hcj.1, hcj.2⟩ x hxI
      have hd : |c j - x| ≤ δ := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith [hx.1])]
        have : c (j + 1) = c j + δ := by simp only [hc]; push_cast; ring
        linarith [hx.2]
      have hvle : v j ≤ f x + 2 * L * δ := by
        simp only [hv]
        have := abs_le.mp hLx
        nlinarith
      exact mul_le_mul_of_nonneg_right hvle (by positivity)
    calc
      (∑ j ∈ range r, v j * ((1 / c j ^ 2 - 1 / c (j + 1) ^ 2) / 2)) ≤
          ∑ j ∈ range r, ∫ x in c j..c (j + 1), (f x + 2 * L * δ) * x ^ (-3 : ℤ) :=
        Finset.sum_le_sum fun j hj => h1 j (Finset.mem_range.mp hj)
      _ = ∫ x in a..b, (f x + 2 * L * δ) * x ^ (-3 : ℤ) := by
        rw [sum_integral_adjacent_intervals hint, hc0, hcr]
      _ = (∫ x in a..b, f x / x ^ 3) + 2 * L * δ * ((1 / a ^ 2 - 1 / b ^ 2) / 2) := by
        rw [← integral_inv_cube ha (ha.trans hab), ← intervalIntegral.integral_const_mul, ←
          intervalIntegral.integral_add]
        · apply integral_congr
          intro x hx
          rw [uIcc_of_le hab.le] at hx
          have hx0 : 0 < x := ha.trans_le hx.1
          simp only
          rw [zpow_neg, zpow_ofNat]
          field_simp
        · apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le hab.le]
          exact hcont.div (continuousOn_pow 3) fun x hx => by have := ha.trans_le hx.1; positivity
        · apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le hab.le]
          exact
            continuousOn_const.mul
              (continuousOn_id.zpow₀ (-3) fun x hx => Or.inl (ha.trans_le hx.1).ne')
                -- the error term is at most ε/2
  have herr : 2 * L * δ * ((1 / a ^ 2 - 1 / b ^ 2) / 2) ≤ ε / 2 := by
    rw [hδ]
    have hr' : 2 * L * (b - a) * (1 / a ^ 2 - 1 / b ^ 2) < r * ε := by rwa [div_lt_iff₀ hε] at hr
    rw [show
        2 * L * ((b - a) / r) * ((1 / a ^ 2 - 1 / b ^ 2) / 2) =
          2 * L * (b - a) * (1 / a ^ 2 - 1 / b ^ 2) / r / 2
        by field_simp]
    have : 2 * L * (b - a) * (1 / a ^ 2 - 1 / b ^ 2) / r ≤ ε := by
      rw [div_le_iff₀ (by exact_mod_cast hr0)]; linarith
    linarith
  have hev := psum_eventually_le (f := f) r (by rw [hc0]; exact ha) hmono hf (half_pos hε)
  rw [hc0, hcr] at hev
  filter_upwards [hev] with K hK
  linarith

/-- `K/k ∈ [a, b)` for `k ∈ Ioc ⌊K/b⌋₊ ⌊K/a⌋₊`. -/
lemma div_mem_Ico {a b K : ℝ} (ha : 0 < a) (hab : a ≤ b) (hK : 0 < K) {k : ℕ}
    (hk : k ∈ Finset.Ioc ⌊K / b⌋₊ ⌊K / a⌋₊) : K / k ∈ Ico a b := by
  rw [Finset.mem_Ioc] at hk
  have hb : 0 < b := ha.trans_le hab
  have hk0 : 0 < k := by have := hk.1; omega
  have hk0' : (0 : ℝ) < k := by exact_mod_cast hk0
  constructor
  · rw [le_div_iff₀ hk0']
    have h1 : (k : ℝ) ≤ K / a :=
      (Nat.floor_le (div_nonneg hK.le ha.le)).trans' (Nat.cast_le.mpr hk.2)
    rw [le_div_iff₀ ha] at h1
    linarith
  · rw [div_lt_iff₀ hk0']
    have h1 : K / b < k := by
      have := Nat.lt_floor_add_one (K / b)
      have h2 : (⌊K / b⌋₊ : ℝ) + 1 ≤ k := by exact_mod_cast hk.1
      linarith
    rw [div_lt_iff₀ hb] at h1
    linarith

lemma psum_congr {f g : ℝ → ℝ} {a b K : ℝ} (ha : 0 < a) (hab : a ≤ b) (hK : 0 < K)
    (h : ∀ x ∈ Ico a b, f x = g x) : psum f a b K = psum g a b K := by
  unfold psum
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [h _ (div_mem_Ico ha hab hK hk)]

lemma psum_sum_split (f : ℝ → ℝ) {t : ℕ → ℝ} (m : ℕ) (ht0 : 0 < t 0)
    (hmono : ∀ i < m, t i ≤ t (i + 1)) {K : ℝ} (hK : 0 ≤ K) :
    psum f (t 0) (t m) K = ∑ i ∈ range m, psum f (t i) (t (i + 1)) K := by
  induction m with
  | zero => simp [psum]
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih fun i hi => hmono i (by omega)]
    exact psum_split f ht0 (c_zero_le fun i hi => hmono i (by omega)) (hmono m (by omega)) hK

/-- The piecewise version: `f = g i` on `[t i, t (i+1))`, each `g i` Lipschitz on the closed
piece. -/
theorem psum_piecewise_le {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ} {t : ℕ → ℝ} {L : ℝ} (m : ℕ) (ht0 : 0 < t 0)
    (hmono : ∀ i < m, t i < t (i + 1)) (hL : 0 ≤ L)
    (hcont : ∀ i < m, ContinuousOn (g i) (Icc (t i) (t (i + 1))))
    (hLip :
      ∀ i < m,
        ∀ x ∈ Icc (t i) (t (i + 1)), ∀ y ∈ Icc (t i) (t (i + 1)), |g i x - g i y| ≤ L * |x - y|)
    (hfg : ∀ i < m, ∀ x ∈ Ico (t i) (t (i + 1)), f x = g i x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ K : ℝ in atTop,
      psum f (t 0) (t m) K / K ^ 2 ≤ (∑ i ∈ range m, ∫ x in t i..t (i + 1), g i x / x ^ 3) + ε := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · filter_upwards [eventually_gt_atTop 0] with K hK
    simp only [psum, Std.le_refl, Finset.Ioc_eq_empty_of_le, sum_empty, zero_div,
        Finset.range_zero, zero_add]; positivity
  have hpos : ∀ i ≤ m, 0 < t i := by
    intro i hi
    induction i with
    | zero => exact ht0
    | succ i ih => exact (ih (by omega)).trans (hmono i (by omega))
  have hε' : 0 < ε / m := by positivity
  have hev :
    ∀ i ∈ range m,
      ∀ᶠ K : ℝ in atTop,
        psum (g i) (t i) (t (i + 1)) K / K ^ 2 ≤ (∫ x in t i..t (i + 1), g i x / x ^ 3) + ε / m :=
  by
    intro i hi
    have hi := Finset.mem_range.mp hi
    exact psum_le_integral (hpos i hi.le) (hmono i hi) hL (hcont i hi) (hLip i hi) hε'
  filter_upwards [(Finset.eventually_all (range m)).mpr hev, eventually_gt_atTop 0] with K hK hK0
  rw [psum_sum_split f m ht0 (fun i hi => (hmono i hi).le) hK0.le, Finset.sum_div]
  have hcongr :
    ∀ i ∈ range m, psum f (t i) (t (i + 1)) K / K ^ 2 = psum (g i) (t i) (t (i + 1)) K / K ^ 2 := by
    intro i hi
    have hi := Finset.mem_range.mp hi
    rw [psum_congr (hpos i hi.le) (hmono i hi).le hK0 (hfg i hi)]
  rw [Finset.sum_congr rfl hcongr]
  calc
    ∑ i ∈ range m, psum (g i) (t i) (t (i + 1)) K / K ^ 2 ≤
        ∑ i ∈ range m, ((∫ x in t i..t (i + 1), g i x / x ^ 3) + ε / m) :=
      Finset.sum_le_sum fun i hi => hK i hi
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

lemma psum_mono {f g : ℝ → ℝ} {a b K : ℝ} (ha : 0 < a) (hab : a ≤ b) (hK : 0 < K)
    (h : ∀ x ∈ Ico a b, f x ≤ g x) : psum f a b K ≤ psum g a b K := by
  unfold psum
  refine Finset.sum_le_sum fun k hk => ?_
  have hk0 : (0 : ℝ) ≤ (k : ℝ) * cPrime k := mul_nonneg (Nat.cast_nonneg _) (cPrime_nonneg k)
  exact mul_le_mul_of_nonneg_left (h _ (div_mem_Ico ha hab hK hk)) hk0

/-- The piecewise version with `f ≤ g i` on the pieces. -/
theorem psum_piecewise_le' {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ} {t : ℕ → ℝ} {L : ℝ} (m : ℕ) (ht0 : 0 < t 0)
    (hmono : ∀ i < m, t i < t (i + 1)) (hL : 0 ≤ L)
    (hcont : ∀ i < m, ContinuousOn (g i) (Icc (t i) (t (i + 1))))
    (hLip :
      ∀ i < m,
        ∀ x ∈ Icc (t i) (t (i + 1)), ∀ y ∈ Icc (t i) (t (i + 1)), |g i x - g i y| ≤ L * |x - y|)
    (hfg : ∀ i < m, ∀ x ∈ Ico (t i) (t (i + 1)), f x ≤ g i x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ K : ℝ in atTop,
      psum f (t 0) (t m) K / K ^ 2 ≤ (∑ i ∈ range m, ∫ x in t i..t (i + 1), g i x / x ^ 3) + ε := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · filter_upwards [eventually_gt_atTop 0] with K hK
    simp only [psum, Std.le_refl, Finset.Ioc_eq_empty_of_le, sum_empty, zero_div,
        Finset.range_zero, zero_add]; positivity
  have hpos : ∀ i ≤ m, 0 < t i := by
    intro i hi
    induction i with
    | zero => exact ht0
    | succ i ih => exact (ih (by omega)).trans (hmono i (by omega))
  have hε' : 0 < ε / m := by positivity
  have hev :
    ∀ i ∈ range m,
      ∀ᶠ K : ℝ in atTop,
        psum (g i) (t i) (t (i + 1)) K / K ^ 2 ≤ (∫ x in t i..t (i + 1), g i x / x ^ 3) + ε / m :=
  by
    intro i hi
    have hi := Finset.mem_range.mp hi
    exact psum_le_integral (hpos i hi.le) (hmono i hi) hL (hcont i hi) (hLip i hi) hε'
  filter_upwards [(Finset.eventually_all (range m)).mpr hev, eventually_gt_atTop 0] with K hK hK0
  rw [psum_sum_split f m ht0 (fun i hi => (hmono i hi).le) hK0.le, Finset.sum_div]
  have hK2 : 0 < K ^ 2 := by positivity
  calc
    ∑ i ∈ range m, psum f (t i) (t (i + 1)) K / K ^ 2 ≤
        ∑ i ∈ range m, psum (g i) (t i) (t (i + 1)) K / K ^ 2 := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hi := Finset.mem_range.mp hi
      exact
        div_le_div_of_nonneg_right (psum_mono (hpos i hi.le) (hmono i hi).le hK0 (hfg i hi))
          hK2.le
    _ ≤ ∑ i ∈ range m, ((∫ x in t i..t (i + 1), g i x / x ^ 3) + ε / m) :=
      (Finset.sum_le_sum fun i hi => hK i hi)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

end Zeta5Irrational
