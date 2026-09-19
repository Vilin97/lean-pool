/-
Copyright (c) 2026 Arthur Champernowne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Champernowne
-/
module

public import LeanPool.Champernowne.Positions
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Asymptotic frequency of digit blocks

`champM b n` is the digit length of the number straddling position `n`.
The natural-number prefix bounds give an error that is little-o of `n`, and
therefore the frequency of each nonempty length-`k` word tends to `b⁻ᵏ`.
-/

@[expose] public section

namespace Champernowne

open Filter Asymptotics Topology

/-- Digit length of the straddling number `champIndex b n + 1`. -/
def champM (b n : ℕ) : ℕ := Nat.log b (champIndex b n + 1) + 1

theorem champM_pos (b n : ℕ) : 0 < champM b n := Nat.succ_pos _

theorem pow_champM_le (b n : ℕ) :
    b ^ (champM b n - 1) ≤ champIndex b n + 1 := by
  rw [champM, Nat.add_sub_cancel]
  exact Nat.pow_log_le_self b (Nat.succ_ne_zero _)

theorem le_pow_champM {b : ℕ} (hb : 1 < b) (n : ℕ) :
    champIndex b n + 1 ≤ b ^ champM b n :=
  le_of_lt (Nat.lt_pow_succ_log_self hb _)

/-- Length lower bound: `n` dominates the second-to-top cohort. -/
theorem cohort_le_n {b : ℕ} (hb : 1 < b) (n : ℕ) :
    (b - 1) * b ^ (champM b n - 2) * (champM b n - 1) ≤ n := by
  rcases Nat.lt_or_ge (champM b n) 2 with h2 | h2
  · rw [show champM b n - 1 = 0 by omega, Nat.mul_zero]
    exact Nat.zero_le n
  · have hN1 := pow_champM_le b n
    have hlen := length_champBlocks_champIndex_le b n
    rw [length_champBlocks] at hlen
    have hsub : Finset.Ico 1 (b ^ (champM b n - 1))
        ⊆ Finset.Ico 1 (champIndex b n + 1) :=
      Finset.Ico_subset_Ico_right hN1
    have hmono := Finset.sum_le_sum_of_subset
      (f := fun k => (bigDigits b k).length) hsub
    rw [sum_Ico_one_pow hb] at hmono
    have hsingle : (∑ k ∈ Finset.Ico (b ^ (champM b n - 1 - 1))
          (b ^ (champM b n - 1)), (bigDigits b k).length)
        ≤ ∑ m ∈ Finset.Icc 1 (champM b n - 1),
            ∑ k ∈ Finset.Ico (b ^ (m - 1)) (b ^ m),
              (bigDigits b k).length :=
      Finset.single_le_sum
        (f := fun m => ∑ k ∈ Finset.Ico (b ^ (m - 1)) (b ^ m),
          (bigDigits b k).length)
        (fun _ _ => Nat.zero_le _)
        (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
    rw [sum_length_cohort hb (champM b n - 1) (by omega),
      show champM b n - 1 - 1 = champM b n - 2 by omega] at hsingle
    omega

theorem tendsto_champIndex_atTop (b : ℕ) :
    Tendsto (champIndex b) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro K
  filter_upwards [Filter.eventually_ge_atTop ((champBlocks b K).length)]
    with n hn
  exact Nat.le_findGreatest (le_trans (le_length_champBlocks b K) hn) hn

theorem tendsto_champM_atTop {b : ℕ} (hb : 1 < b) :
    Tendsto (champM b) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro K
  have h10 : Tendsto (fun n => champIndex b n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ (champIndex b n))
      (tendsto_champIndex_atTop b)
  filter_upwards [h10.eventually_ge_atTop (b ^ K)] with n hn
  have hn' : b ^ K ≤ champIndex b n + 1 := hn
  have hlog := (Nat.le_log_iff_pow_le hb
    (show champIndex b n + 1 ≠ 0 by omega)).mpr hn'
  change K ≤ Nat.log b (champIndex b n + 1) + 1
  omega

/-! ### General-`w` packaging

Instantiates the `Positions.lean` straddle transfer at `M := champM b n`.
`w.length ≤ champM b n` holds only eventually, since `champM b n → ∞`
(`tendsto_champM_atTop`), so the transfer itself is wrapped in `∀ᶠ`. -/

theorem base_pow_count_le {b : ℕ} (hb : 1 < b) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) :
    ∀ᶠ n in atTop, b ^ w.length * countOccurrences w (champPrefix b n)
      ≤ n + 7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n := by
  filter_upwards [(tendsto_champM_atTop hb).eventually_ge_atTop w.length] with n hn
  exact base_pow_countOccurrences_champPrefix_le hb n (champM b n) hw hwne
    (champM_pos b n) hn (pow_champM_le b n) (le_pow_champM hb n)

theorem le_base_pow_count {b : ℕ} (hb : 1 < b) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) :
    ∀ᶠ n in atTop, n ≤ b ^ w.length * countOccurrences w (champPrefix b n)
      + 7 * (w.length + 1) * b ^ w.length * b ^ champM b n := by
  filter_upwards [(tendsto_champM_atTop hb).eventually_ge_atTop w.length] with n hn
  exact le_base_pow_countOccurrences_champPrefix hb n (champM b n) hw hwne
    (champM_pos b n) hn (pow_champM_le b n) (le_pow_champM hb n)

/-- The error dominates its own budget: `E(n)·(b-1)(M−1) ≤ E'·n`. -/
theorem err_mul_le_pow {b : ℕ} (hb : 1 < b) (n : ℕ) (w : List ℕ) :
    7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n * ((b - 1) * (champM b n - 1))
      ≤ (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ 2) * n := by
  rcases Nat.lt_or_ge (champM b n) 2 with h2 | h2
  · rw [show champM b n - 1 = 0 by omega]
    simp
  · have hD := cohort_le_n hb n
    have hpow : b ^ champM b n = b ^ 2 * b ^ (champM b n - 2) := by
      rw [← pow_add]; congr 1; omega
    calc 7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n
        * ((b - 1) * (champM b n - 1))
        = (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ 2)
          * ((b - 1) * b ^ (champM b n - 2) * (champM b n - 1)) := by
          rw [hpow]; ring
    _ ≤ (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ 2) * n := Nat.mul_le_mul_left _ hD

/-- Subtraction-free form for `M ≥ 2`. -/
theorem err_mul_le_pow' {b : ℕ} (hb : 1 < b) (n : ℕ) (w : List ℕ) (h2 : 2 ≤ champM b n) :
    7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n * ((b - 1) * champM b n)
      ≤ 2 * (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ 2) * n := by
  have hF := err_mul_le_pow hb n w
  have h9 : (b - 1) * champM b n ≤ 2 * ((b - 1) * (champM b n - 1)) := by
    calc (b - 1) * champM b n ≤ (b - 1) * (2 * (champM b n - 1)) :=
        Nat.mul_le_mul_left _ (by omega)
    _ = 2 * ((b - 1) * (champM b n - 1)) := by ring
  calc 7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n * ((b - 1) * champM b n)
      ≤ 7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n
        * (2 * ((b - 1) * (champM b n - 1))) := Nat.mul_le_mul_left _ h9
  _ = 2 * (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n
        * ((b - 1) * (champM b n - 1))) := by ring
  _ ≤ 2 * ((7 * (w.length + 1) * b ^ (2 * w.length) * b ^ 2) * n) :=
      Nat.mul_le_mul_left _ hF
  _ = 2 * (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ 2) * n := by ring

/-- The error sequence is negligible relative to `n`. -/
theorem tendsto_err_div_pow {b : ℕ} (hb : 1 < b) (w : List ℕ) :
    Tendsto (fun n => (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n : ℝ) / n)
      atTop (𝓝 0) := by
  have hbR : (1 : ℝ) ≤ (b : ℝ) - 1 := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hden : Tendsto (fun n => ((b : ℝ) - 1) * (champM b n : ℝ))
      atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by linarith)).mpr
      (tendsto_natCast_atTop_atTop.comp (tendsto_champM_atTop hb))
  have hg : Tendsto (fun n =>
      (2 * (7 * ((w.length : ℝ) + 1) * (b : ℝ) ^ (2 * w.length) * (b : ℝ) ^ 2))
      / (((b : ℝ) - 1) * (champM b n : ℝ))) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hden
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have h0 : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  · filter_upwards [(tendsto_champM_atTop hb).eventually_ge_atTop 2,
      Filter.eventually_ge_atTop 1] with n hM2 hn1
    have h0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hM0 : (0 : ℝ) < ((b : ℝ) - 1) * (champM b n : ℝ) := by
      have hMpos : (0 : ℝ) < (champM b n : ℝ) := by
        exact_mod_cast champM_pos b n
      nlinarith
    rw [div_le_div_iff₀ h0 hM0]
    have := err_mul_le_pow' hb n w hM2
    have hcast2 : ((7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n
        * ((b - 1) * champM b n) : ℕ) : ℝ)
        = (7 * ((w.length : ℝ) + 1) * (b : ℝ) ^ (2 * w.length) * (b : ℝ) ^ champM b n)
          * (((b : ℝ) - 1) * (champM b n : ℝ)) := by
      have hb1 : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_one]
      push_cast [hb1]
      ring
    have hcast3 : ((2 * (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ 2) * n : ℕ) : ℝ)
        = 2 * (7 * ((w.length : ℝ) + 1) * (b : ℝ) ^ (2 * w.length) * (b : ℝ) ^ 2) * n := by
      push_cast; ring
    rw [← hcast2, ← hcast3]
    exact_mod_cast this

/-- `countOccurrences w (champPrefix b n) −
n/b^k = o(n)`. -/
theorem countOccurrences_champPrefix_sub_isLittleO {b : ℕ} (hb : 1 < b) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) :
    (fun n => (countOccurrences w (champPrefix b n) : ℝ) - n / (b : ℝ) ^ w.length)
      =o[atTop] (fun n => (n : ℝ)) := by
  have hbR : (0 : ℝ) < (b : ℝ) ^ w.length := by positivity
  have hb1R : (1 : ℝ) ≤ (b : ℝ) ^ w.length := by
    have : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast le_of_lt hb
    exact one_le_pow₀ this
  have hEo : (fun n => (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n : ℝ))
      =o[atTop] (fun n => (n : ℝ)) := by
    rw [Asymptotics.isLittleO_iff_tendsto']
    · exact tendsto_err_div_pow hb w
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn h0
      have : (0 : ℝ) < n := by exact_mod_cast hn
      exact absurd h0 (ne_of_gt this)
  refine Asymptotics.IsBigO.trans_isLittleO ?_ hEo
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [base_pow_count_le hb hw hwne, le_base_pow_count hb hw hwne]
    with n h1 h2
  -- Widen the lower transfer's error b^k·… to the upper's b^(2k)·… (ℕ level).
  have h2' : n ≤ b ^ w.length * countOccurrences w (champPrefix b n)
      + 7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n := by
    have hpow : b ^ w.length ≤ b ^ (2 * w.length) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hmul := Nat.mul_le_mul_right (b ^ champM b n)
      (Nat.mul_le_mul_left (7 * (w.length + 1)) hpow)
    omega
  have e1 : (b : ℝ) ^ w.length * countOccurrences w (champPrefix b n)
      ≤ n + 7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n := by exact_mod_cast h1
  have e2 : (n : ℝ) ≤ (b : ℝ) ^ w.length * countOccurrences w (champPrefix b n)
      + 7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n := by exact_mod_cast h2'
  have hEpos : (0 : ℝ) ≤ (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n : ℝ) :=
    by positivity
  have key : |(b : ℝ) ^ w.length * countOccurrences w (champPrefix b n) - n|
      ≤ (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n : ℝ) := by
    rw [abs_le]
    constructor
    · linarith
    · linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg hEpos,
    show (countOccurrences w (champPrefix b n) : ℝ) - n / (b : ℝ) ^ w.length
      = ((b : ℝ) ^ w.length * countOccurrences w (champPrefix b n) - n) / (b : ℝ) ^ w.length by
        field_simp,
    abs_div, abs_of_pos hbR]
  calc |(b : ℝ) ^ w.length * countOccurrences w (champPrefix b n) - n| / (b : ℝ) ^ w.length
      ≤ (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n : ℝ) / (b : ℝ) ^ w.length := by
        exact div_le_div_of_nonneg_right key hbR.le
  _ ≤ (7 * (w.length + 1) * b ^ (2 * w.length) * b ^ champM b n : ℝ) := by
        rw [div_le_iff₀ hbR]
        exact le_mul_of_one_le_right hEpos hb1R

/-- Every nonempty block `w` (digits `< b`)
occurs in the base-`b` Champernowne stream with asymptotic frequency
`b⁻ᵏ`. -/
theorem tendsto_countOccurrences_champPrefix_div {b : ℕ} (hb : 1 < b) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) :
    Tendsto (fun n => (countOccurrences w (champPrefix b n) : ℝ) / n)
      atTop (𝓝 (((b : ℝ) ^ w.length)⁻¹)) := by
  have hb0 : ((b : ℝ) ^ w.length) ≠ 0 := by positivity
  have ho := countOccurrences_champPrefix_sub_isLittleO hb hw hwne
  rw [Asymptotics.isLittleO_iff_tendsto'
    (by
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn h0
      have : (0 : ℝ) < n := by exact_mod_cast hn
      exact absurd h0 (ne_of_gt this))] at ho
  have hsum := ho.add_const ((1 : ℝ) / (b : ℝ) ^ w.length)
  rw [zero_add] at hsum
  rw [← one_div]
  refine Tendsto.congr' ?_ hsum
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have h0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [one_div]
  field_simp
  ring

end Champernowne
