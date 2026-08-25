/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos132ThreeChain.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.LinearCombination

/-!
# Arithmetic of powers of three

The four-point catalogue reduces to a handful of Diophantine facts about powers of three.
This file isolates them.  Everything is stated over `ℤ`; the geometric files produce the
corresponding real equations and transfer them by `exact_mod_cast`.
-/

namespace Erdos132ThreeChain

theorem one_le_pow3 (n : ℕ) : (1 : ℤ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)

theorem pow3_pos (n : ℕ) : (0 : ℤ) < 3 ^ n := by positivity

theorem three_le_pow3 {n : ℕ} (h : n ≠ 0) : (3 : ℤ) ≤ 3 ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h3 : (3 : ℤ) ^ (m + 1) = 3 * 3 ^ m := by ring
  nlinarith [one_le_pow3 m]

theorem three_dvd_pow3 {n : ℕ} (h : n ≠ 0) : (3 : ℤ) ∣ 3 ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ⟨3 ^ m, by ring⟩

theorem nine_dvd_pow3 {n : ℕ} (h : 2 ≤ n) : (9 : ℤ) ∣ 3 ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact ⟨3 ^ m, by ring⟩

theorem pow3_inj {m n : ℕ} (h : (3 : ℤ) ^ m = 3 ^ n) : m = n := by
  have : (3 : ℕ) ^ m = 3 ^ n := by exact_mod_cast h
  exact Nat.pow_right_injective (by norm_num) this

/-- A power of three is `1`, is `3`, or is at least `9`. -/
theorem pow3_trichotomy (n : ℕ) : (3 : ℤ) ^ n = 1 ∨ (3 : ℤ) ^ n = 3 ∨ 9 ≤ (3 : ℤ) ^ n := by
  match n with
  | 0 => left; norm_num
  | 1 => right; left; norm_num
  | (m + 2) =>
    right; right
    have h : (3 : ℤ) ^ (m + 2) = 9 * 3 ^ m := by ring
    nlinarith [one_le_pow3 m]

/-- `4 * 3 ^ j - 1` is a power of three only in the trivial instance `4 - 1 = 3`. -/
theorem pow3_eq_four_mul_pow3_sub_one {j l : ℕ} (h : (3 : ℤ) ^ l = 4 * 3 ^ j - 1) :
    j = 0 ∧ l = 1 := by
  have hj : j = 0 := by
    by_contra hj
    obtain ⟨u, hu⟩ := three_dvd_pow3 hj
    rcases eq_or_ne l 0 with hl | hl
    · subst hl; rw [hu] at h; simp at h; omega
    · obtain ⟨v, hv⟩ := three_dvd_pow3 hl
      rw [hu, hv] at h; omega
  subst hj
  refine ⟨rfl, ?_⟩
  have h3 : (3 : ℤ) ^ l = 3 ^ 1 := by simpa using h
  exact pow3_inj h3


theorem one_le_pow3R (n : ℕ) : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)

theorem three_le_pow3R {n : ℕ} (h : n ≠ 0) : (3 : ℝ) ≤ 3 ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e : (3 : ℝ) ^ (m + 1) = 3 * 3 ^ m := by ring
  nlinarith [one_le_pow3R m]

theorem nine_le_pow3R {n : ℕ} (h : 2 ≤ n) : (9 : ℝ) ≤ 3 ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e : (3 : ℝ) ^ (m + 2) = 9 * 3 ^ m := by ring
  nlinarith [one_le_pow3R m]

/-- **Exponent rigidity of a chain triangle.**  If a triangle has squared sides `c * 3 ^ p`,
`c * 3 ^ q`, `c * 3 ^ r` with `p ≤ q ≤ r`, then either the two largest exponents agree, or the
two smallest agree and the largest exceeds them by exactly one. -/
theorem exp_tri {c : ℝ} (hc : 0 < c) {p q r : ℕ} (hpq : p ≤ q) (hqr : q ≤ r)
    (h : (c * 3 ^ r - c * 3 ^ p - c * 3 ^ q) ^ 2 ≤ 4 * (c * 3 ^ p) * (c * 3 ^ q)) :
    r = q ∨ (p = q ∧ r = p + 1) := by
  obtain ⟨s, rfl⟩ : ∃ s, q = p + s := ⟨q - p, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, r = p + s + t := ⟨r - (p + s), by omega⟩
  have hS := one_le_pow3R s
  have hT := one_le_pow3R t
  have hred : ((3 : ℝ) ^ s * 3 ^ t - 1 - 3 ^ s) ^ 2 ≤ 4 * 3 ^ s := by
    have hpos : (0 : ℝ) < (c * 3 ^ p) ^ 2 := by positivity
    refine le_of_mul_le_mul_left ?_ hpos
    have e1 : (c * 3 ^ p) ^ 2 * (((3 : ℝ) ^ s * 3 ^ t - 1 - 3 ^ s) ^ 2)
        = (c * 3 ^ (p + s + t) - c * 3 ^ p - c * 3 ^ (p + s)) ^ 2 := by
      rw [pow_add, pow_add]; ring
    have e2 : (c * 3 ^ p) ^ 2 * (4 * (3 : ℝ) ^ s)
        = 4 * (c * 3 ^ p) * (c * 3 ^ (p + s)) := by rw [pow_add]; ring
    rw [e1, e2]; exact h
  rcases Nat.eq_zero_or_pos t with ht | ht
  · left; omega
  have hT3 : (3 : ℝ) ≤ 3 ^ t := three_le_pow3R (by omega)
  have hs0 : s = 0 := by
    by_contra hs
    have hS3 : (3 : ℝ) ≤ 3 ^ s := three_le_pow3R hs
    have hX : 2 * (3 : ℝ) ^ s - 1 ≤ 3 ^ s * 3 ^ t - 1 - 3 ^ s := by nlinarith
    have hX0 : (0 : ℝ) ≤ 2 * (3 : ℝ) ^ s - 1 := by linarith
    nlinarith [mul_self_le_mul_self hX0 hX]
  subst hs0
  have hle : (3 : ℝ) ^ t ≤ 4 := by
    simp only [pow_zero] at hred
    nlinarith [hred, hT3]
  have ht1 : t = 1 := by
    by_contra htc
    have : (9 : ℝ) ≤ 3 ^ t := nine_le_pow3R (by omega)
    linarith
  right; omega

/-- The four-point equation for two points equidistant from the ends of the shortest edge. -/
theorem isoceles_pair_solution {j k l : ℕ} (hjk : j ≤ k)
    (hcase : j = k ∨ (l = j ∧ k = j + 1) ∨ l = k)
    (heq : (3 : ℤ) ^ j * 3 ^ j + 3 ^ k * 3 ^ k + 3 ^ l * 3 ^ l - 2 * (3 ^ j * 3 ^ k)
        - 2 * (3 ^ j * 3 ^ l) - 2 * (3 ^ k * 3 ^ l) + 3 ^ l = 0) :
    j = 0 ∧ k = 0 ∧ l = 1 := by
  have hjp := pow3_pos j
  have hkp := pow3_pos k
  have hlp := pow3_pos l
  have hj1 := one_le_pow3 j
  have hk1 := one_le_pow3 k
  have hl1 := one_le_pow3 l
  rcases hcase with hc | ⟨hlj, hkj⟩ | hlk
  · subst hc
    have hfac : (3 : ℤ) ^ l * (3 ^ l - 4 * 3 ^ j + 1) = 0 := by linear_combination heq
    have h2 : (3 : ℤ) ^ l = 4 * 3 ^ j - 1 := by
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd h (by positivity)
      · linarith
    obtain ⟨hj0, hl1'⟩ := pow3_eq_four_mul_pow3_sub_one h2
    exact ⟨hj0, hj0, hl1'⟩
  · exfalso
    rw [hlj, hkj] at heq
    have e : (3 : ℤ) ^ (j + 1) = 3 * 3 ^ j := by ring
    rw [e] at heq
    nlinarith [heq, hj1, mul_le_mul_of_nonneg_left hj1 hjp.le]
  · exfalso
    rw [hlk] at heq
    have hmono : (3 : ℤ) ^ j ≤ 3 ^ k := pow_le_pow_right₀ (by norm_num) hjk
    nlinarith [heq, mul_le_mul_of_nonneg_left hmono hjp.le,
      le_mul_of_one_le_left hkp.le hj1, mul_pos hjp hkp]

/-- The four-point equation for one point equidistant from the ends of the shortest edge and one
point spanning it. -/
theorem mixed_pair_solution {j l : ℕ} (heq : ((3 : ℤ) ^ j - 3 ^ l) ^ 2 - 3 * 3 ^ l + 3 = 0) :
    j = 0 ∧ l = 0 := by
  rcases eq_or_ne j 0 with hj | hj
  · subst hj
    rcases eq_or_ne l 0 with hl | hl
    · exact ⟨rfl, hl⟩
    · exfalso
      have h3 := three_le_pow3 hl
      rcases pow3_trichotomy l with h | h | h <;> nlinarith [heq]
  · exfalso
    have h3 := three_le_pow3 hj
    rcases eq_or_ne l 0 with hl | hl
    · subst hl; simp only [pow_zero] at heq; nlinarith [heq]
    · obtain ⟨u, hu⟩ := three_dvd_pow3 hj
      obtain ⟨v, hv⟩ := three_dvd_pow3 hl
      rw [hu, hv] at heq
      have : (1 : ℤ) = 3 * (v - (u - v) * (u - v)) := by nlinarith [heq]
      omega

theorem pow3_ne_four {l : ℕ} : (3 : ℤ) ^ l ≠ 4 := by
  rcases pow3_trichotomy l with h | h | h <;> omega

theorem pow3_ne_seven {l : ℕ} : (3 : ℤ) ^ l ≠ 7 := by
  rcases pow3_trichotomy l with h | h | h <;> omega

end Erdos132ThreeChain
