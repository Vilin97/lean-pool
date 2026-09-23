/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Enumerative.Partition.GenFun
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import LeanPool.PentagonalNumberTheoremAnalytic.Franklin.Defs

/-!
# Helper lemmas for Franklin's involution

Helper lemmas about `consecutiveTopRun`, partition membership,
and properties of `αOp`/`βOp`.

## Main results

* `ctr_zero`, `ctr_succ`: defining equations for `consecutiveTopRun`
* `ctr_eq_of`: the characterisation of `consecutiveTopRun S m` as the unique `r` with
  `m - j ∈ S` for all `j < r` and `m - r ∉ S`
* `mem_DP`: membership in `distinctPartitions`
* `sum_Icc_id_mul_two`, `Icc_sum_id`: Gauss' summation formula over `Finset.Icc` in `ℕ`
* `consecutiveTopRun_Icc`, `partBase_Icc`, `partMax_Icc`, `partSlope_Icc`: the structural
  invariants of an interval, which is the shape both pentagonal families `smkSet`/`spkSet` take
-/

@[expose] public section

open Finset

namespace PentagonalNumberTheorem.Franklin

/-- Base case: `consecutiveTopRun S 0 = 1` if `0 ∈ S`, else `0`. -/
@[simp]
lemma ctr_zero (S : Finset ℕ) : consecutiveTopRun S 0 = if (0 : ℕ) ∈ S then 1 else 0 := by
  simp [consecutiveTopRun]
/-- Recurrence: `consecutiveTopRun S (m+1)` is `1 + consecutiveTopRun S m` if `m+1 ∈ S`,
else `0`. -/
@[simp]
lemma ctr_succ (S : Finset ℕ) (m : ℕ) :
    consecutiveTopRun S (m + 1) = if m + 1 ∈ S then 1 + consecutiveTopRun S m else 0 := by
  simp [consecutiveTopRun]
/-- If `m ∉ S` then `consecutiveTopRun S m = 0`. -/
lemma ctr_not_mem (S : Finset ℕ) (m : ℕ) (h : m ∉ S) : consecutiveTopRun S m = 0 := by
  cases m with
  | zero => simp [h]
  | succ m => rw [ctr_succ, ite_eq_right h]
/-- If `m ∈ S` then `consecutiveTopRun S m > 0`. -/
lemma ctr_pos_of_mem (S : Finset ℕ) (m : ℕ) (h : m ∈ S) : 0 < consecutiveTopRun S m := by
  cases m with
  | zero => simp [h]
  | succ m => rw [ctr_succ, ite_eq_left h]; omega
/-- If `0 ∉ S` then `consecutiveTopRun S m ≤ m`. -/
lemma ctr_le (S : Finset ℕ) (m : ℕ) (h : (0 : ℕ) ∉ S) : consecutiveTopRun S m ≤ m := by
  induction m with
  | zero => simp [h]
  | succ m ih => rw [ctr_succ]; split_ifs <;> omega
/-- If `j < consecutiveTopRun S m` then `m - j ∈ S`. -/
lemma ctr_mem_of_lt (S : Finset ℕ) (m j : ℕ) (hj : j < consecutiveTopRun S m) :
    m - j ∈ S := by
  induction m generalizing j with
  | zero =>
    rw [ctr_zero] at hj
    split_ifs at hj with h
    · obtain rfl : j = 0 := by omega
      simpa using h
    · omega
  | succ m ih =>
    rw [ctr_succ] at hj
    split_ifs at hj with h
    · cases j with
      | zero => simpa using h
      | succ j => simpa using ih j (by omega)
    · omega
/-- Lower bound for `consecutiveTopRun`: a run of length `r` below `m` forces
`r ≤ consecutiveTopRun S m`. -/
lemma ctr_ge_of_mem (S : Finset ℕ) (m r : ℕ) (hrm : r ≤ m) (h : ∀ j < r, m - j ∈ S) :
    r ≤ consecutiveTopRun S m := by
  induction m generalizing r with
  | zero => omega
  | succ m ih =>
    cases r with
    | zero => exact Nat.zero_le _
    | succ r =>
      rw [ctr_succ, ite_eq_left (by simpa using h 0 (Nat.succ_pos r))]
      have := ih r (by omega) fun j hj => by simpa using h (j + 1) (by omega)
      omega
/-- `consecutiveTopRun S m` is the unique `r ≤ m` with `m - j ∈ S` for every `j < r` and
`m - r ∉ S`. -/
lemma ctr_eq_of (S : Finset ℕ) (m r : ℕ) (hrm : r ≤ m) (hmem : ∀ j < r, m - j ∈ S)
    (hnot : m - r ∉ S) : consecutiveTopRun S m = r :=
  le_antisymm (by by_contra hc; exact hnot (ctr_mem_of_lt S m r (by omega)))
    (ctr_ge_of_mem S m r hrm hmem)
/-- If `0 ∉ S` and `m ∈ S` then `m - consecutiveTopRun S m ∉ S`. -/
lemma ctr_not_mem_boundary (S : Finset ℕ) (m : ℕ) (h0 : (0 : ℕ) ∉ S) (hm : m ∈ S) :
    m - consecutiveTopRun S m ∉ S := by
  induction m with
  | zero => exact absurd hm h0
  | succ m ih =>
    rw [ctr_succ, ite_eq_left hm]
    by_cases h : m ∈ S
    · rw [show m + 1 - (1 + consecutiveTopRun S m) = m - consecutiveTopRun S m by omega]
      exact ih h
    · rw [ctr_not_mem S m h]
      simpa using h
/-- `S ∈ distinctPartitions n` iff `S ⊆ Icc 1 n` and `S.sum id = n`. -/
lemma mem_DP (n : ℕ) (S : Finset ℕ) :
    S ∈ distinctPartitions n ↔ S ⊆ Icc 1 n ∧ S.sum id = n := by
  simp [distinctPartitions]
/-- Every element of a distinct partition of n is positive. -/
lemma DP_pos_mem (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitions n) {x : ℕ} (hx : x ∈ S) :
    1 ≤ x :=
  (mem_Icc.mp (mem_powerset.mp (mem_filter.mp hS).1 hx)).1
/-- Every element of `S ∈ distinctPartitions n` is at most n. -/
lemma DP_le_mem (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitions n) {x : ℕ} (hx : x ∈ S) :
    x ≤ n :=
  (mem_Icc.mp (mem_powerset.mp (mem_filter.mp hS).1 hx)).2
/-- `0` is not in any distinct partition. -/
lemma DP_zero_not_mem (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitions n) : (0 : ℕ) ∉ S :=
  fun h => absurd (DP_pos_mem n S hS h) (by omega)
/-- The sum of a distinct partition of n equals n. -/
lemma DP_sum (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitions n) : S.sum id = n :=
  (mem_filter.mp hS).2
/-- Every α-partition is a distinct partition. -/
lemma DPalpha_mem_DP (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsAlpha n) :
    S ∈ distinctPartitions n :=
  (mem_filter.mp hS).1
/-- Every β-partition is a distinct partition. -/
lemma DPbeta_mem_DP (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    S ∈ distinctPartitions n :=
  (mem_filter.mp hS).1
/-- Every α-partition is nonempty. -/
lemma DPalpha_nonempty (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsAlpha n) :
    S.Nonempty :=
  card_pos.mp (mem_filter.mp hS).2.1
/-- Every β-partition is nonempty. -/
lemma DPbeta_nonempty (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) : S.Nonempty :=
  card_pos.mp (mem_filter.mp hS).2.1
/-- `partBase S ∈ S` for nonempty S. -/
lemma partBase_mem (S : Finset ℕ) (hne : S.Nonempty) : partBase S ∈ S := by
  simp only [partBase, dite_eq_left hne]
  exact min'_mem _ hne
/-- `partMax S ∈ S` for nonempty S. -/
lemma partMax_mem (S : Finset ℕ) (hne : S.Nonempty) : partMax S ∈ S := by
  simp only [partMax, dite_eq_left hne]
  exact max'_mem _ hne
/-- `partBase S ≤ x` for any `x ∈ S`. -/
lemma partBase_le (S : Finset ℕ) (hne : S.Nonempty) {x : ℕ} (hx : x ∈ S) :
    partBase S ≤ x := by
  simp only [partBase, dite_eq_left hne]
  exact min'_le _ _ hx
/-- `x ≤ partMax S` for any `x ∈ S`. -/
lemma le_partMax (S : Finset ℕ) (hne : S.Nonempty) {x : ℕ} (hx : x ∈ S) :
    x ≤ partMax S := by
  simp only [partMax, dite_eq_left hne]
  exact le_max' _ _ hx
/-- `partBase S ≤ partMax S` for nonempty S. -/
lemma partBase_le_partMax (S : Finset ℕ) (hne : S.Nonempty) : partBase S ≤ partMax S :=
  partBase_le S hne (partMax_mem S hne)
/-- `partSlope S > 0` when `S` is nonempty. -/
lemma partSlope_pos (S : Finset ℕ) (hne : S.Nonempty) : 0 < partSlope S :=
  ctr_pos_of_mem S _ (partMax_mem S hne)
/-- `partSlope S ≤ partMax S` when `0 ∉ S`. -/
lemma partSlope_le_partMax (S : Finset ℕ) (h0 : (0 : ℕ) ∉ S) :
    partSlope S ≤ partMax S :=
  ctr_le S _ h0
/-- For S ∈ α(n), `partBase S ≤ partSlope S`. -/
lemma DPalpha_base_le_slope (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsAlpha n) :
    partBase S ≤ partSlope S := by
  have := (mem_filter.mp hS).2.2
  omega
/-- For S ∈ β(n), `partSlope S < partBase S`. -/
lemma DPbeta_slope_lt_base (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    partSlope S < partBase S := by
  have := (mem_filter.mp hS).2.2
  omega
/-- The bottom of the top run, `partMax S - partSlope S + 1`, is an element of `S`, hence is
at least `partBase S`. This is the common core of `DPalpha_max_ge_2base` and
`DPbeta_max_ge_2slope_add_1`. -/
private lemma base_le_max_sub_slope_add_one (S : Finset ℕ) (hne : S.Nonempty)
    (h0 : (0 : ℕ) ∉ S) : partBase S ≤ partMax S - partSlope S + 1 := by
  have hs := partSlope_pos S hne
  have hsm := partSlope_le_partMax S h0
  have := partBase_le S hne
    (ctr_mem_of_lt S (partMax S) (partSlope S - 1) (by change partSlope S - 1 < partSlope S; omega))
  omega
/-- For S ∈ α(n), `partMax S ≥ 2 * partBase S`. -/
lemma DPalpha_max_ge_2base (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsAlpha n) :
    2 * partBase S ≤ partMax S := by
  have hne := DPalpha_nonempty n S hS
  have h0 := DP_zero_not_mem n S (DPalpha_mem_DP n S hS)
  have := base_le_max_sub_slope_add_one S hne h0
  have := partSlope_pos S hne
  have := partSlope_le_partMax S h0
  have := (mem_filter.mp hS).2.2
  omega
/-- For S ∈ β(n), `partMax S ≥ 2 * partSlope S + 1`. -/
lemma DPbeta_max_ge_2slope_add_1 (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    2 * partSlope S + 1 ≤ partMax S := by
  have hne := DPbeta_nonempty n S hS
  have h0 := DP_zero_not_mem n S (DPbeta_mem_DP n S hS)
  have := base_le_max_sub_slope_add_one S hne h0
  have := partSlope_pos S hne
  have := partSlope_le_partMax S h0
  have := (mem_filter.mp hS).2.2
  omega

/-! ### Intervals

Both pentagonal families are intervals — `smkSet k = Icc k (2 * k - 1)` and
`spkSet k = Icc (k + 1) (2 * k)` — and a *special* partition is an interval too
(`DPspecial_*` in `Lemmas.lean`). The lemmas below compute the sum and the three structural
invariants of an arbitrary `Finset.Icc a b` once and for all. -/

/-- Gauss' summation formula over `Finset.Icc` in `ℕ`, in `* 2` form: no division and no
truncated subtraction on the left. Unconditional — both sides are `0` when `b < a`. -/
theorem sum_Icc_id_mul_two (a b : ℕ) : (∑ i ∈ Icc a b, i) * 2 = (b + 1 - a) * (a + b) := by
  rcases le_or_gt a b with h | h
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
    have hc : a + n + 1 - a = n + 1 := by omega
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, hc, sum_add_distrib, sum_const,
      card_range, smul_eq_mul, add_mul, sum_range_id_mul_two, Nat.add_sub_cancel]
    ring
  · rw [Icc_eq_empty (by omega), sum_empty, Nat.sub_eq_zero_of_le (by omega), Nat.zero_mul,
      Nat.zero_mul]

/-- Gauss' summation formula over `Finset.Icc` in `ℕ`. -/
theorem sum_Icc_id (a b : ℕ) : ∑ i ∈ Icc a b, i = (b + 1 - a) * (a + b) / 2 := by
  rw [← sum_Icc_id_mul_two, Nat.mul_div_cancel _ Nat.zero_lt_two]

/-- `sum_Icc_id_mul_two` in `Finset.sum _ id` phrasing, which is what `distinctPartitions` uses.
`rw` cannot see through `id`, so this restatement is what call sites need. -/
theorem Icc_sum_id_mul_two (a b : ℕ) : (Icc a b).sum id * 2 = (b + 1 - a) * (a + b) :=
  sum_Icc_id_mul_two a b

/-- `sum_Icc_id` in `Finset.sum _ id` phrasing. -/
theorem Icc_sum_id (a b : ℕ) : (Icc a b).sum id = (b + 1 - a) * (a + b) / 2 :=
  sum_Icc_id a b

/-- The consecutive-run function on an interval: every element of `Icc a b` continues the run
back down to `a`, and everything outside has run length `0`. -/
theorem consecutiveTopRun_Icc (a b m : ℕ) :
    consecutiveTopRun (Icc a b) m = if a ≤ m ∧ m ≤ b then m - a + 1 else 0 := by
  induction m with
  | zero => simp only [ctr_zero, mem_Icc]; split_ifs <;> omega
  | succ m ih => rw [ctr_succ, ih]; simp only [mem_Icc]; split_ifs <;> omega

/-- The base of a nonempty interval is its left endpoint. -/
theorem partBase_Icc {a b : ℕ} (hab : a ≤ b) : partBase (Icc a b) = a := by
  have hne : (Icc a b).Nonempty := nonempty_Icc.mpr hab
  simp only [partBase, dite_eq_left hne]
  exact le_antisymm (min'_le _ _ (mem_Icc.mpr ⟨le_rfl, hab⟩))
    (le_min' _ _ _ fun x hx => (mem_Icc.mp hx).1)

/-- The max of a nonempty interval is its right endpoint. -/
theorem partMax_Icc {a b : ℕ} (hab : a ≤ b) : partMax (Icc a b) = b := by
  have hne : (Icc a b).Nonempty := nonempty_Icc.mpr hab
  simp only [partMax, dite_eq_left hne]
  exact le_antisymm (max'_le _ _ _ fun x hx => (mem_Icc.mp hx).2)
    (le_max' _ _ (mem_Icc.mpr ⟨hab, le_rfl⟩))

/-- A nonempty interval is one single run, so its slope is its whole length. -/
theorem partSlope_Icc {a b : ℕ} (hab : a ≤ b) : partSlope (Icc a b) = b - a + 1 := by
  rw [partSlope, partMax_Icc hab, consecutiveTopRun_Icc, ite_eq_left ⟨hab, le_rfl⟩]

/-- For S ∈ α(n), `partMax S - partBase S + 1 ∈ S`. -/
lemma DPalpha_m_sub_b_add_1_mem (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsAlpha n) :
    partMax S - partBase S + 1 ∈ S := by
  have hne := DPalpha_nonempty n S hS
  have hb1 : 1 ≤ partBase S := DP_pos_mem n S (DPalpha_mem_DP n S hS) (partBase_mem S hne)
  have hbm := partBase_le_partMax S hne
  have hbs := DPalpha_base_le_slope n S hS
  have h := ctr_mem_of_lt S (partMax S) (partBase S - 1)
    (by change partBase S - 1 < partSlope S; omega)
  rwa [show partMax S - (partBase S - 1) = partMax S - partBase S + 1 by omega] at h
/-- For S ∈ α(n), `partBase S ≠ partMax S - partBase S + 1`. -/
lemma DPalpha_base_ne_m_sub_b_add_1 (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsAlpha n) :
    partBase S ≠ partMax S - partBase S + 1 := by
  have := DPalpha_max_ge_2base n S hS
  omega
/-- `partMax S + 1 ∉ S` for nonempty S. -/
lemma partMax_succ_not_mem (S : Finset ℕ) (hne : S.Nonempty) :
    partMax S + 1 ∉ S :=
  fun h => absurd (le_partMax S hne h) (by omega)
/-- Membership in `αOp S`, with the two `let`s of the definition unfolded. -/
lemma mem_alphaOp {S : Finset ℕ} {x : ℕ} :
    x ∈ alphaOp S ↔
      x = partMax S + 1 ∨ (x ≠ partMax S - partBase S + 1 ∧ x ≠ partBase S ∧ x ∈ S) := by
  simp only [alphaOp, mem_insert, mem_erase]
/-- The α-operation preserves the sum of parts. -/
lemma alphaOp_sum (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsAlpha n) :
    (alphaOp S).sum id = S.sum id := by
  have hne := DPalpha_nonempty n S hS
  have hbm := partBase_le_partMax S hne
  have hb : partBase S ∈ S := partBase_mem S hne
  have hm1 : partMax S - partBase S + 1 ∈ S.erase (partBase S) :=
    mem_erase.mpr ⟨(DPalpha_base_ne_m_sub_b_add_1 n S hS).symm, DPalpha_m_sub_b_add_1_mem n S hS⟩
  have hins : partMax S + 1 ∉ (S.erase (partBase S)).erase (partMax S - partBase S + 1) :=
    fun h => partMax_succ_not_mem S hne (mem_of_mem_erase (mem_of_mem_erase h))
  have key : S.sum id
      = ((S.erase (partBase S)).erase (partMax S - partBase S + 1)).sum id
        + (partMax S - partBase S + 1) + partBase S := by
    rw [← sum_erase_add S id hb, ← sum_erase_add _ id hm1]
    rfl
  rw [show alphaOp S = insert (partMax S + 1)
        ((S.erase (partBase S)).erase (partMax S - partBase S + 1)) from rfl,
    sum_insert hins, key]
  simp only [id_eq]
  omega
/-- For S ∈ α(n), `partMax (αOp S) = partMax S + 1`. -/
lemma alphaOp_partMax (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsAlpha n) :
    partMax (alphaOp S) = partMax S + 1 := by
  have hne := DPalpha_nonempty n S hS
  have hmem : partMax S + 1 ∈ alphaOp S := mem_alphaOp.mpr (Or.inl rfl)
  have hneA : (alphaOp S).Nonempty := ⟨_, hmem⟩
  have hub : ∀ x ∈ alphaOp S, x ≤ partMax S + 1 := by
    intro x hx
    rcases mem_alphaOp.mp hx with rfl | ⟨-, -, hxS⟩
    · exact le_rfl
    · exact Nat.le_succ_of_le (le_partMax S hne hxS)
  simp only [partMax, dite_eq_left hneA]
  exact le_antisymm (max'_le _ _ _ hub) (le_max' _ _ hmem)
/-- For S ∈ α(n), `partSlope (αOp S) = partBase S`. -/
lemma alphaOp_partSlope (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsAlpha n) :
    partSlope (alphaOp S) = partBase S := by
  have hne := DPalpha_nonempty n S hS
  have h0 := DP_zero_not_mem n S (DPalpha_mem_DP n S hS)
  have hb1 : 1 ≤ partBase S := DP_pos_mem n S (DPalpha_mem_DP n S hS) (partBase_mem S hne)
  have hbm := partBase_le_partMax S hne
  have h2b := DPalpha_max_ge_2base n S hS
  have hbs := DPalpha_base_le_slope n S hS
  have hsm := partSlope_le_partMax S h0
  rw [partSlope, alphaOp_partMax n S hS]
  refine ctr_eq_of _ _ _ (by omega) (fun j hj => ?_) ?_
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact mem_alphaOp.mpr (Or.inl (by omega))
    · have h := ctr_mem_of_lt S (partMax S) (j - 1) (by change j - 1 < partSlope S; omega)
      rw [show partMax S - (j - 1) = partMax S + 1 - j by omega] at h
      exact mem_alphaOp.mpr (Or.inr ⟨by omega, by omega, h⟩)
  · rw [show partMax S + 1 - partBase S = partMax S - partBase S + 1 by omega]
    intro hmem
    rcases mem_alphaOp.mp hmem with h | ⟨h, -, -⟩
    · omega
    · exact h rfl
/-- For S ∈ β(n), `partSlope S ∉ S`. -/
lemma DPbeta_slope_not_mem (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    partSlope S ∉ S := fun h =>
  absurd (partBase_le S (DPbeta_nonempty n S hS) h)
    (by have := DPbeta_slope_lt_base n S hS; omega)
/-- For S ∈ β(n), `partMax S - partSlope S ∉ S`. -/
lemma DPbeta_m_sub_s_not_mem (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    partMax S - partSlope S ∉ S :=
  ctr_not_mem_boundary S (partMax S) (DP_zero_not_mem n S (DPbeta_mem_DP n S hS))
    (partMax_mem S (DPbeta_nonempty n S hS))
/-- For S ∈ β(n), `partSlope S ≠ partMax S - partSlope S`. -/
lemma DPbeta_slope_ne_m_sub_slope (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    partSlope S ≠ partMax S - partSlope S := by
  have := DPbeta_max_ge_2slope_add_1 n S hS
  omega
/-- For S ∈ β(n), `βOp S` inserts the slope and `partMax S - partSlope S` into `S`, after
deleting the maximum. -/
lemma betaOp_eq (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    betaOp S
      = insert (partSlope S) (insert (partMax S - partSlope S) (S.erase (partMax S))) := by
  have hne := DPbeta_nonempty n S hS
  have h0 := DP_zero_not_mem n S (DPbeta_mem_DP n S hS)
  have := partSlope_pos S hne
  have := DPbeta_max_ge_2slope_add_1 n S hS
  simp only [betaOp, erase_insert_of_ne (by omega : partSlope S ≠ partMax S),
    erase_insert_of_ne (by omega : partMax S - partSlope S ≠ partMax S)]
/-- The β-operation preserves the sum of parts. -/
lemma betaOp_sum (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    (betaOp S).sum id = S.sum id := by
  have hne := DPbeta_nonempty n S hS
  have h0 := DP_zero_not_mem n S (DPbeta_mem_DP n S hS)
  have hsm := partSlope_le_partMax S h0
  have hmS : partMax S ∈ S := partMax_mem S hne
  have hsS := DPbeta_slope_not_mem n S hS
  have hmsS := DPbeta_m_sub_s_not_mem n S hS
  have hs_ne := DPbeta_slope_ne_m_sub_slope n S hS
  rw [betaOp_eq n S hS, sum_insert (by simp [hs_ne, hsS]),
    sum_insert (fun h => hmsS (mem_of_mem_erase h)), ← sum_erase_add S id hmS]
  simp only [id_eq]
  omega
/-- For S ∈ β(n), `partMax (βOp S) = partMax S - 1`. -/
lemma betaOp_partMax (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    partMax (betaOp S) = partMax S - 1 := by
  have hne := DPbeta_nonempty n S hS
  have h0 := DP_zero_not_mem n S (DPbeta_mem_DP n S hS)
  have hs0 := partSlope_pos S hne
  have h2s := DPbeta_max_ge_2slope_add_1 n S hS
  have hmem : partMax S - 1 ∈ betaOp S := by
    rw [betaOp_eq n S hS]
    by_cases h : partSlope S = 1
    · exact mem_insert_of_mem (by rw [h]; exact mem_insert_self _ _)
    · refine mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨by omega, ?_⟩))
      exact ctr_mem_of_lt S (partMax S) 1 (by change (1 : ℕ) < partSlope S; omega)
  have hneB : (betaOp S).Nonempty := ⟨_, hmem⟩
  have hub : ∀ x ∈ betaOp S, x ≤ partMax S - 1 := by
    intro x hx
    rw [betaOp_eq n S hS] at hx
    simp only [mem_insert, mem_erase] at hx
    rcases hx with rfl | rfl | ⟨hxm, hxS⟩
    · omega
    · omega
    · have := le_partMax S hne hxS; omega
  simp only [partMax, dite_eq_left hneB]
  exact le_antisymm (max'_le _ _ _ hub) (le_max' _ _ hmem)
/-- For S ∈ β(n), `partBase (βOp S) = partSlope S`. -/
lemma betaOp_partBase (n : ℕ) (S : Finset ℕ) (hS : S ∈ distinctPartitionsBeta n) :
    partBase (betaOp S) = partSlope S := by
  have hne := DPbeta_nonempty n S hS
  have h0 := DP_zero_not_mem n S (DPbeta_mem_DP n S hS)
  have h2s := DPbeta_max_ge_2slope_add_1 n S hS
  have hsb := DPbeta_slope_lt_base n S hS
  have hmem : partSlope S ∈ betaOp S := by
    rw [betaOp_eq n S hS]; exact mem_insert_self _ _
  have hneB : (betaOp S).Nonempty := ⟨_, hmem⟩
  have hlb : ∀ x ∈ betaOp S, partSlope S ≤ x := by
    intro x hx
    rw [betaOp_eq n S hS] at hx
    simp only [mem_insert, mem_erase] at hx
    rcases hx with rfl | rfl | ⟨-, hxS⟩
    · exact le_rfl
    · omega
    · have := partBase_le S hne hxS; omega
  simp only [partBase, dite_eq_left hneB]
  exact le_antisymm (min'_le _ _ hmem) (le_min' _ _ _ hlb)

end PentagonalNumberTheorem.Franklin
