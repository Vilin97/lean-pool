/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
module

/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-! Finite analytic estimates. -/

@[expose] public section

open scoped BigOperators

namespace NonMRR

/-- A closed real walk with increments bounded by `d` has this energy bound. -/
theorem walk_square_le {L j : ℕ} (S : ℕ → ℝ) {d : ℝ}
    (hd : 0 ≤ d) (h0 : S 0 = 0) (hL : S L = 0)
    (hstep : ∀ i < L, |S (i + 1) - S i| ≤ d) (hj : j ≤ L) :
    (S j) ^ 2 ≤ 2 * d * ∑ i ∈ Finset.range L, |S i| := by
  have htel : ∑ i ∈ Finset.range j, ((S (i + 1)) ^ 2 - (S i) ^ 2) = (S j) ^ 2 := by
    induction j with
    | zero => simp [h0]
    | succ j ih =>
      rw [Finset.sum_range_succ]
      have ih' := ih (Nat.le_trans (Nat.le_succ j) hj)
      rw [ih']
      ring
  have hterm (i : ℕ) (hi : i < L) :
      (S (i + 1)) ^ 2 - (S i) ^ 2 ≤ d * (|S (i + 1)| + |S i|) := by
    calc
      _ = (S (i + 1) - S i) * (S (i + 1) + S i) := by ring
      _ ≤ |(S (i + 1) - S i) * (S (i + 1) + S i)| := le_abs_self _
      _ = |S (i + 1) - S i| * |S (i + 1) + S i| := abs_mul _ _
      _ ≤ d * (|S (i + 1)| + |S i|) :=
        mul_le_mul (hstep i hi) (abs_add_le _ _) (abs_nonneg _) hd
  have hshift : ∑ i ∈ Finset.range L, |S (i + 1)| =
      ∑ i ∈ Finset.range L, |S i| := by
    have hs := Finset.sum_range_succ' (fun i => |S i|) L
    rw [Finset.sum_range_succ, h0, hL] at hs
    simpa using hs.symm
  calc
    (S j) ^ 2 = ∑ i ∈ Finset.range j, ((S (i + 1)) ^ 2 - (S i) ^ 2) := htel.symm
    _ ≤ ∑ i ∈ Finset.range j, d * (|S (i + 1)| + |S i|) :=
      Finset.sum_le_sum fun i hi => hterm i (lt_of_lt_of_le (Finset.mem_range.mp hi) hj)
    _ ≤ ∑ i ∈ Finset.range L, d * (|S (i + 1)| + |S i|) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj)
        (fun _ _ _ => mul_nonneg hd (add_nonneg (abs_nonneg _) (abs_nonneg _)))
    _ = 2 * d * ∑ i ∈ Finset.range L, |S i| := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, hshift]
      ring

/-- A fourth-moment estimate for one closed walk. -/
theorem walk_fourth_le {L j : ℕ} (S : ℕ → ℝ) {d : ℝ}
    (hd : 0 ≤ d) (h0 : S 0 = 0) (hL : S L = 0)
    (hstep : ∀ i < L, |S (i + 1) - S i| ≤ d) (hj : j ≤ L) :
    (S j) ^ 4 ≤ 4 * d ^ 2 * (L : ℝ) * ∑ i ∈ Finset.range L, (S i) ^ 2 := by
  have hsq := walk_square_le S hd h0 hL hstep hj
  have hcs : (∑ i ∈ Finset.range L, |S i|) ^ 2 ≤
      (L : ℝ) * ∑ i ∈ Finset.range L, (S i) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.range L)
      (fun _ => (1 : ℝ)) (fun i => |S i|)
  calc
    (S j) ^ 4 = ((S j) ^ 2) ^ 2 := by ring
    _ ≤ (2 * d * ∑ i ∈ Finset.range L, |S i|) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) hsq 2
    _ = 4 * d ^ 2 * (∑ i ∈ Finset.range L, |S i|) ^ 2 := by ring
    _ ≤ 4 * d ^ 2 * ((L : ℝ) * ∑ i ∈ Finset.range L, (S i) ^ 2) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = _ := by ring

/-- The normalized version used for balanced sign vectors. -/
theorem walk_fourth_le_normalized {L j : ℕ} (hLpos : 0 < L) (S : ℕ → ℝ)
    (h0 : S 0 = 0) (hL : S L = 0)
    (hstep : ∀ i < L, |S (i + 1) - S i| ≤ 1 / (L : ℝ)) (hj : j ≤ L) :
    (S j) ^ 4 ≤ (4 / (L : ℝ)) * ∑ i ∈ Finset.range L, (S i) ^ 2 := by
  have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hLpos
  have hcoef : 4 * (1 / (L : ℝ)) ^ 2 * (L : ℝ) = 4 / (L : ℝ) := by
    field_simp
  simpa only [hcoef] using walk_fourth_le S (by positivity) h0 hL hstep hj

/-- A family with prefix-square sums at most one has total fourth moment at most four,
even when a different time is selected in each walk. -/
theorem sum_walk_fourth_le {ι : Type*} [Fintype ι] {L : ℕ} (hLpos : 0 < L)
    (S : ι → ℕ → ℝ) (h0 : ∀ k, S k 0 = 0) (hL : ∀ k, S k L = 0)
    (hstep : ∀ k i, i < L → |S k (i + 1) - S k i| ≤ 1 / (L : ℝ))
    (hprefix : ∀ i < L, ∑ k, (S k i) ^ 2 ≤ 1)
    (j : ι → ℕ) (hj : ∀ k, j k ≤ L) :
    ∑ k, (S k (j k)) ^ 4 ≤ 4 := by
  have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hLpos
  calc
    ∑ k, (S k (j k)) ^ 4 ≤
        ∑ k, (4 / (L : ℝ)) * ∑ i ∈ Finset.range L, (S k i) ^ 2 :=
      Finset.sum_le_sum fun k _ =>
        walk_fourth_le_normalized hLpos (S k) (h0 k) (hL k) (hstep k) (hj k)
    _ = (4 / (L : ℝ)) * ∑ i ∈ Finset.range L, ∑ k, (S k i) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (4 / (L : ℝ)) * ∑ _i ∈ Finset.range L, (1 : ℝ) := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun i hi => hprefix i (Finset.mem_range.mp hi)
      · positivity
    _ = 4 := by simp [hLne]

/-- The walks that at some time exceed the threshold `1/q`. -/
noncomputable def badWalks {ι : Type*} [Fintype ι]
    (S : ι → ℕ → ℝ) (L q : ℕ) : Finset ι := by
  classical
  exact Finset.univ.filter fun k => ∃ j ≤ L, 1 / (q : ℝ) < |S k j|

/-- The finite counting estimate, in terms of the prefix walks. -/
theorem card_badWalks_le {ι : Type*} [Fintype ι] {L q : ℕ}
    (hLpos : 0 < L) (hqpos : 0 < q)
    (S : ι → ℕ → ℝ) (h0 : ∀ k, S k 0 = 0) (hL : ∀ k, S k L = 0)
    (hstep : ∀ k i, i < L → |S k (i + 1) - S k i| ≤ 1 / (L : ℝ))
    (hprefix : ∀ i < L, ∑ k, (S k i) ^ 2 ≤ 1) :
    (badWalks S L q).card ≤ 4 * q ^ 4 := by
  classical
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hex (k : ι) : ∃ j, j ≤ L ∧
      (k ∈ badWalks S L q → 1 / (q : ℝ) < |S k j|) := by
    by_cases hk : k ∈ badWalks S L q
    · obtain ⟨j, hj, hlarge⟩ := (Finset.mem_filter.mp hk).2
      exact ⟨j, hj, fun _ => hlarge⟩
    · exact ⟨0, Nat.zero_le _, fun h => (hk h).elim⟩
  choose j hj hlarge using hex
  have hall := sum_walk_fourth_le hLpos S h0 hL hstep hprefix j hj
  have hterm (k : ι) (hk : k ∈ badWalks S L q) :
      1 / (q : ℝ) ^ 4 ≤ (S k (j k)) ^ 4 := by
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / (q : ℝ))
      (hlarge k hk).le 4
    simpa only [div_pow, one_pow, (by decide : Even 4).pow_abs] using hp
  have hbound : ((badWalks S L q).card : ℝ) / (q : ℝ) ^ 4 ≤ 4 := by
    calc
      ((badWalks S L q).card : ℝ) / (q : ℝ) ^ 4 =
          ∑ _k ∈ badWalks S L q, (1 : ℝ) / (q : ℝ) ^ 4 := by simp [div_eq_mul_inv]
      _ ≤ ∑ k ∈ badWalks S L q, (S k (j k)) ^ 4 := Finset.sum_le_sum hterm
      _ ≤ ∑ k, (S k (j k)) ^ 4 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => pow_nonneg (sq_nonneg _) 2 |>.trans_eq (by ring))
      _ ≤ 4 := hall
  have hreal := (div_le_iff₀ (by positivity : 0 < (q : ℝ) ^ 4)).mp hbound
  exact_mod_cast hreal

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
