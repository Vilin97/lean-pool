/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

/-!
# Rounding chips to the ends of a block of unit steps

Fix one block of `N ≥ 1` unit steps carrying integer slopes `s 0, …, s (N-1)`.
Chips sit at interior offsets `1, …, N-1` of the block, indexed by a finite set
`chips` with offsets `off` and a rounding side `side` (`true` = round the chip to
the right end of the block, `false` = round it to the left end).  The only
hypothesis on the slopes is that they may drop across an offset, by at most the
number of chips sitting there.

Moving a chip from offset `off i` to an end of the block changes the block total
by `N - off i` (right end) or by `-off i` (left end); the sum of those changes is
the correction `δ`.  The two main results bound the corrected block total between
`N` copies of the first slope (minus the number of chips rounded left) and `N`
copies of the last slope (plus the number of chips rounded right), and the third
bounds `|δ|` by the total distance the chips travel.

All of this is finite-sum integer arithmetic; no graph theory is involved.
-/

@[expose] public section

namespace Utilities.BlockSlopeRounding

open Finset

variable {ι : Type*}

/-! ### Counting the indices of `Finset.range N` on one side of a threshold -/

/-- The number of `t < N` with `a ≤ t` is `N - a`. -/
private theorem sum_range_indicator_le (a : ℕ) :
    ∀ N : ℕ, a ≤ N →
      (∑ t ∈ Finset.range N, (if a ≤ t then (1 : ℤ) else 0)) = (N : ℤ) - (a : ℤ) := by
  intro N
  induction N with
  | zero =>
    intro h
    have ha : a = 0 := by omega
    subst ha
    simp
  | succ n ih =>
    intro h
    rcases Nat.lt_or_ge n a with hlt | hge
    · have ha : a = n + 1 := by omega
      subst ha
      rw [Finset.sum_eq_zero (fun t ht => by
        rw [Finset.mem_range] at ht
        exact ite_eq_right (by omega))]
      simp
    · rw [Finset.sum_range_succ, ih (by omega), ite_eq_left hge]
      push_cast
      ring

/-- The number of `t < N` with `t < a` is `a`, provided `a ≤ N`. -/
private theorem sum_range_indicator_lt (a : ℕ) :
    ∀ N : ℕ, a ≤ N →
      (∑ t ∈ Finset.range N, (if t < a then (1 : ℤ) else 0)) = (a : ℤ) := by
  intro N
  induction N with
  | zero =>
    intro h
    have ha : a = 0 := by omega
    subst ha
    simp
  | succ n ih =>
    intro h
    rcases Nat.lt_or_ge n a with hlt | hge
    · have ha : a = n + 1 := by omega
      subst ha
      have hall : ∀ t ∈ Finset.range (n + 1), (if t < n + 1 then (1 : ℤ) else 0) = 1 := by
        intro t ht
        rw [Finset.mem_range] at ht
        exact ite_eq_left ht
      rw [Finset.sum_congr rfl hall, Finset.sum_const, Finset.card_range]
      simp
    · rw [Finset.sum_range_succ, ih (by omega), ite_eq_right (by omega)]
      ring

/-! ### Splitting a chip count off a threshold -/

/-- Raising the threshold by one adds exactly the chips at the new offset. -/
private theorem card_filter_le_succ (chips : Finset ι) (off : ι → ℕ) (t : ℕ) :
    ((chips.filter (fun i => off i ≤ t + 1)).card : ℤ)
      = ((chips.filter (fun i => off i ≤ t)).card : ℤ)
        + ((chips.filter (fun i => off i = t + 1)).card : ℤ) := by
  rw [← Nat.cast_add]
  congr 1
  simp only [Finset.card_filter, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by split_ifs <;> omega)

/-- Raising the strict threshold by one removes exactly the chips at the new offset. -/
private theorem card_filter_lt_succ (chips : Finset ι) (off : ι → ℕ) (t : ℕ) :
    ((chips.filter (fun i => t < off i)).card : ℤ)
      = ((chips.filter (fun i => t + 1 < off i)).card : ℤ)
        + ((chips.filter (fun i => off i = t + 1)).card : ℤ) := by
  rw [← Nat.cast_add]
  congr 1
  simp only [Finset.card_filter, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by split_ifs <;> omega)

/-! ### Slope bounds inside the block -/

/-- The slope at step `t` is at least the first slope minus the number of chips at
offsets `≤ t`. -/
theorem slope_ge_first (N : ℕ) (s : ℕ → ℤ) (chips : Finset ι) (off : ι → ℕ)
    (hoff : ∀ i ∈ chips, 0 < off i ∧ off i < N)
    (hslope : ∀ t, 0 < t → t < N →
      s (t - 1) - ((chips.filter (fun i => off i = t)).card : ℤ) ≤ s t) :
    ∀ t, t < N → s 0 - ((chips.filter (fun i => off i ≤ t)).card : ℤ) ≤ s t := by
  intro t
  induction t with
  | zero =>
    intro _
    have hempty : chips.filter (fun i => off i ≤ 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro i hi
      have := (hoff i hi).1
      omega
    rw [hempty]
    simp
  | succ t ih =>
    intro ht
    have ih' := ih (by omega)
    have hs := hslope (t + 1) (Nat.succ_pos t) ht
    simp only [Nat.add_sub_cancel] at hs
    rw [card_filter_le_succ chips off t]
    linarith

/-- The slope at step `t` is at most the last slope plus the number of chips at
offsets `> t`. -/
theorem slope_le_last (N : ℕ) (s : ℕ → ℤ) (chips : Finset ι) (off : ι → ℕ)
    (hoff : ∀ i ∈ chips, 0 < off i ∧ off i < N)
    (hslope : ∀ t, 0 < t → t < N →
      s (t - 1) - ((chips.filter (fun i => off i = t)).card : ℤ) ≤ s t) :
    ∀ t, t < N → s t ≤ s (N - 1) + ((chips.filter (fun i => t < off i)).card : ℤ) := by
  -- `hoff` is kept in the signature to match `slope_ge_first`, but is not needed here.
  have _ := hoff
  have key : ∀ k t, t < N → N - 1 - t ≤ k →
      s t ≤ s (N - 1) + ((chips.filter (fun i => t < off i)).card : ℤ) := by
    intro k
    induction k with
    | zero =>
      intro t ht hk
      have htN : t = N - 1 := by omega
      subst htN
      have : (0 : ℤ) ≤ ((chips.filter (fun i => N - 1 < off i)).card : ℤ) :=
        Int.natCast_nonneg _
      linarith
    | succ k ih =>
      intro t ht hk
      by_cases htN : t = N - 1
      · subst htN
        have : (0 : ℤ) ≤ ((chips.filter (fun i => N - 1 < off i)).card : ℤ) :=
          Int.natCast_nonneg _
        linarith
      · have ht1 : t + 1 < N := by omega
        have ih' := ih (t + 1) ht1 (by omega)
        have hs := hslope (t + 1) (Nat.succ_pos t) ht1
        simp only [Nat.add_sub_cancel] at hs
        rw [card_filter_lt_succ chips off t]
        linarith
  intro t ht
  exact key (N - 1 - t) t ht le_rfl

/-! ### Double counting the chip totals -/

/-- Summing the chip counts below each threshold counts, for each chip, the number of
steps strictly to its right. -/
theorem sum_card_filter_le_eq (N : ℕ) (chips : Finset ι) (off : ι → ℕ)
    (hoff : ∀ i ∈ chips, 0 < off i ∧ off i < N) :
    (∑ t ∈ Finset.range N, ((chips.filter (fun i => off i ≤ t)).card : ℤ))
      = ∑ i ∈ chips, ((N : ℤ) - (off i : ℤ)) := by
  have hcard : ∀ t : ℕ, ((chips.filter (fun i => off i ≤ t)).card : ℤ)
      = ∑ i ∈ chips, (if off i ≤ t then (1 : ℤ) else 0) := by
    intro t
    rw [Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun i _ => by split_ifs <;> simp)
  simp only [hcard]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl
    (fun i hi => sum_range_indicator_le (off i) N (le_of_lt (hoff i hi).2))

/-- Summing the chip counts above each threshold counts, for each chip, the number of
steps to its left. -/
theorem sum_card_filter_lt_eq (N : ℕ) (chips : Finset ι) (off : ι → ℕ)
    (hoff : ∀ i ∈ chips, 0 < off i ∧ off i < N) :
    (∑ t ∈ Finset.range N, ((chips.filter (fun i => t < off i)).card : ℤ))
      = ∑ i ∈ chips, (off i : ℤ) := by
  have hcard : ∀ t : ℕ, ((chips.filter (fun i => t < off i)).card : ℤ)
      = ∑ i ∈ chips, (if t < off i then (1 : ℤ) else 0) := by
    intro t
    rw [Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun i _ => by split_ifs <;> simp)
  simp only [hcard]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl
    (fun i hi => sum_range_indicator_lt (off i) N (le_of_lt (hoff i hi).2))

/-! ### The two main bounds -/

/-- Rounding every chip to an end of the block cannot push the block total below `N`
copies of the first slope, less one for each chip rounded to the left end. -/
theorem block_lower (N : ℕ) (hN : 0 < N) (s : ℕ → ℤ) (chips : Finset ι) (off : ι → ℕ)
    (side : ι → Bool)
    (hoff : ∀ i ∈ chips, 0 < off i ∧ off i < N)
    (hslope : ∀ t, 0 < t → t < N →
      s (t - 1) - ((chips.filter (fun i => off i = t)).card : ℤ) ≤ s t) :
    (N : ℤ) * (s 0 - ((chips.filter (fun i => side i = false)).card : ℤ))
      ≤ (∑ t ∈ Finset.range N, s t)
        + ∑ i ∈ chips, (if side i then ((N : ℤ) - (off i : ℤ)) else -(off i : ℤ)) := by
  -- `hN` is recorded for callers; the argument below does not need it.
  have _ := hN
  have hstep : (∑ t ∈ Finset.range N,
      (s 0 - ((chips.filter (fun i => off i ≤ t)).card : ℤ))) ≤ ∑ t ∈ Finset.range N, s t :=
    Finset.sum_le_sum (fun t ht =>
      slope_ge_first N s chips off hoff hslope t (Finset.mem_range.mp ht))
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    sum_card_filter_le_eq N chips off hoff, nsmul_eq_mul] at hstep
  have hδ := Finset.sum_filter_add_sum_filter_not chips (fun i => side i = true)
    (fun i => if side i then ((N : ℤ) - (off i : ℤ)) else -(off i : ℤ))
  have hS := Finset.sum_filter_add_sum_filter_not chips (fun i => side i = true)
    (fun i => ((N : ℤ) - (off i : ℤ)))
  simp only [Bool.not_eq_true] at hδ hS
  have hA : (∑ i ∈ chips.filter (fun i => side i = true),
      (if side i then ((N : ℤ) - (off i : ℤ)) else -(off i : ℤ)))
      = ∑ i ∈ chips.filter (fun i => side i = true), ((N : ℤ) - (off i : ℤ)) :=
    Finset.sum_congr rfl (fun i hi => ite_eq_left (Finset.mem_filter.mp hi).2)
  have hB : (∑ i ∈ chips.filter (fun i => side i = false),
      (if side i then ((N : ℤ) - (off i : ℤ)) else -(off i : ℤ)))
      = ∑ i ∈ chips.filter (fun i => side i = false), (-(off i : ℤ)) :=
    Finset.sum_congr rfl (fun i hi => by
      have h2 := (Finset.mem_filter.mp hi).2
      exact ite_eq_right (by simp [h2]))
  have hneg : (∑ i ∈ chips.filter (fun i => side i = false), (-(off i : ℤ)))
      = -(∑ i ∈ chips.filter (fun i => side i = false), (off i : ℤ)) :=
    Finset.sum_neg_distrib _
  have hBn : (∑ i ∈ chips.filter (fun i => side i = false), ((N : ℤ) - (off i : ℤ)))
      + (∑ i ∈ chips.filter (fun i => side i = false), (off i : ℤ))
      = (N : ℤ) * ((chips.filter (fun i => side i = false)).card : ℤ) := by
    rw [← Finset.sum_add_distrib]
    have hconst : ∀ i ∈ chips.filter (fun i => side i = false),
        ((N : ℤ) - (off i : ℤ)) + (off i : ℤ) = (N : ℤ) := fun i _ => by ring
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    ring
  have hexp : (N : ℤ) * (s 0 - ((chips.filter (fun i => side i = false)).card : ℤ))
      = (N : ℤ) * s 0 - (N : ℤ) * ((chips.filter (fun i => side i = false)).card : ℤ) := by
    ring
  rw [hexp]
  linarith

/-- Rounding every chip to an end of the block cannot push the block total above `N`
copies of the last slope, plus one for each chip rounded to the right end. -/
theorem block_upper (N : ℕ) (hN : 0 < N) (s : ℕ → ℤ) (chips : Finset ι) (off : ι → ℕ)
    (side : ι → Bool)
    (hoff : ∀ i ∈ chips, 0 < off i ∧ off i < N)
    (hslope : ∀ t, 0 < t → t < N →
      s (t - 1) - ((chips.filter (fun i => off i = t)).card : ℤ) ≤ s t) :
    (∑ t ∈ Finset.range N, s t)
        + ∑ i ∈ chips, (if side i then ((N : ℤ) - (off i : ℤ)) else -(off i : ℤ))
      ≤ (N : ℤ) * (s (N - 1) + ((chips.filter (fun i => side i = true)).card : ℤ)) := by
  -- `hN` is recorded for callers; the argument below does not need it.
  have _ := hN
  have hstep : (∑ t ∈ Finset.range N, s t) ≤ ∑ t ∈ Finset.range N,
      (s (N - 1) + ((chips.filter (fun i => t < off i)).card : ℤ)) :=
    Finset.sum_le_sum (fun t ht =>
      slope_le_last N s chips off hoff hslope t (Finset.mem_range.mp ht))
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    sum_card_filter_lt_eq N chips off hoff, nsmul_eq_mul] at hstep
  have hδ := Finset.sum_filter_add_sum_filter_not chips (fun i => side i = true)
    (fun i => if side i then ((N : ℤ) - (off i : ℤ)) else -(off i : ℤ))
  have hS := Finset.sum_filter_add_sum_filter_not chips (fun i => side i = true)
    (fun i => (off i : ℤ))
  simp only [Bool.not_eq_true] at hδ hS
  have hA : (∑ i ∈ chips.filter (fun i => side i = true),
      (if side i then ((N : ℤ) - (off i : ℤ)) else -(off i : ℤ)))
      = ∑ i ∈ chips.filter (fun i => side i = true), ((N : ℤ) - (off i : ℤ)) :=
    Finset.sum_congr rfl (fun i hi => ite_eq_left (Finset.mem_filter.mp hi).2)
  have hB : (∑ i ∈ chips.filter (fun i => side i = false),
      (if side i then ((N : ℤ) - (off i : ℤ)) else -(off i : ℤ)))
      = ∑ i ∈ chips.filter (fun i => side i = false), (-(off i : ℤ)) :=
    Finset.sum_congr rfl (fun i hi => by
      have h2 := (Finset.mem_filter.mp hi).2
      exact ite_eq_right (by simp [h2]))
  have hneg : (∑ i ∈ chips.filter (fun i => side i = false), (-(off i : ℤ)))
      = -(∑ i ∈ chips.filter (fun i => side i = false), (off i : ℤ)) :=
    Finset.sum_neg_distrib _
  have hAn : (∑ i ∈ chips.filter (fun i => side i = true), ((N : ℤ) - (off i : ℤ)))
      + (∑ i ∈ chips.filter (fun i => side i = true), (off i : ℤ))
      = (N : ℤ) * ((chips.filter (fun i => side i = true)).card : ℤ) := by
    rw [← Finset.sum_add_distrib]
    have hconst : ∀ i ∈ chips.filter (fun i => side i = true),
        ((N : ℤ) - (off i : ℤ)) + (off i : ℤ) = (N : ℤ) := fun i _ => by ring
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    ring
  have hexp : (N : ℤ) * (s (N - 1) + ((chips.filter (fun i => side i = true)).card : ℤ))
      = (N : ℤ) * s (N - 1) + (N : ℤ) * ((chips.filter (fun i => side i = true)).card : ℤ) := by
    ring
  rw [hexp]
  linarith

/-! ### The size of the correction -/

/-- The correction is bounded by the total distance the chips travel. -/
theorem abs_delta_le (N : ℕ) (chips : Finset ι) (off : ι → ℕ) (side : ι → Bool)
    (hoff : ∀ i ∈ chips, 0 < off i ∧ off i < N) :
    |∑ i ∈ chips, (if side i then ((N : ℤ) - (off i : ℤ)) else -(off i : ℤ))|
      ≤ ∑ i ∈ chips, ((if side i then N - off i else off i : ℕ) : ℤ) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro i hi
  obtain ⟨_, hlt⟩ := hoff i hi
  have hle : (off i : ℤ) ≤ (N : ℤ) := by exact_mod_cast le_of_lt hlt
  by_cases hs : side i = true
  · rw [ite_eq_left hs, ite_eq_left hs, Nat.cast_sub (le_of_lt hlt),
      abs_of_nonneg (by linarith)]
  · rw [ite_eq_right hs, ite_eq_right hs, abs_neg, Nat.abs_cast]

end Utilities.BlockSlopeRounding
