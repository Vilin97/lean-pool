/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Lemmas about `Nat.testBit` and bitwise folds

Statements that mention nothing from this development.  They were proved here because
something in the library needed them, and they are collected in `ForMathlib` so that they
can be contributed upstream, or deleted when Mathlib grows its own.
-/


theorem eq_of_testBit_lt {n a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (h : ∀ k, k < n → a.testBit k = b.testBit k) : a = b := by
  refine Nat.eq_of_testBit_eq fun k ↦ ?_
  by_cases hk : k < n
  · exact h k hk
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num)
      (not_lt.1 hk))), Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right
      (by norm_num) (not_lt.1 hk)))]

theorem testBit_foldl_or {α : Type} (f : α → ℕ) (p : α → Bool) (k : ℕ) (l : List α) (c : ℕ) :
    (l.foldl (fun c a ↦ if p a then c ||| 2 ^ f a else c) c).testBit k
      = (c.testBit k || l.any fun a ↦ p a && decide (f a = k)) := by
  induction l generalizing c with
  | nil => simp
  | cons a t ih =>
      simp only [List.foldl_cons, List.any_cons, ih]
      by_cases hp : p a
      · simp [hp, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_assoc]
      · simp [hp]

theorem foldl_or_lt {α : Type} (f : α → ℕ) (p : α → Bool) (m : ℕ) (l : List α)
    (hf : ∀ a ∈ l, f a < m) (c : ℕ) (hc : c < 2 ^ m) :
    l.foldl (fun c a ↦ if p a then c ||| 2 ^ f a else c) c < 2 ^ m := by
  induction l generalizing c with
  | nil => simpa using hc
  | cons a t ih =>
      simp only [List.foldl_cons]
      refine ih (fun b hb ↦ hf b (List.mem_cons_of_mem _ hb)) _ ?_
      by_cases hp : p a
      · simp only [hp, ite_true]
        exact Nat.or_lt_two_pow hc
          (Nat.pow_lt_pow_right Nat.one_lt_two (hf a List.mem_cons_self))
      · simpa [hp] using hc

theorem exists_testBit {n s : ℕ} (hs : s < 2 ^ n) (h0 : s ≠ 0) :
    ∃ i : Fin n, s.testBit i.1 = true := by
  by_contra h
  simp only [not_exists, Bool.not_eq_true] at h
  exact h0 (eq_of_testBit_lt hs (Nat.two_pow_pos n) fun k hk ↦ by
    rw [Nat.zero_testBit]; exact h ⟨k, hk⟩)

theorem le_of_testBit_imp {a b : ℕ} (h : ∀ k, a.testBit k = true → b.testBit k = true) : a ≤ b := by
  have hab : a &&& b = a := Nat.eq_of_testBit_eq fun k ↦ by
    rw [Nat.testBit_and]
    cases ha : a.testBit k with
    | false => rw [Bool.false_and]
    | true => rw [h k ha, Bool.and_self]
  exact hab ▸ Nat.and_le_right

theorem testBit_foldl_lor {α : Type} (f : α → ℕ) (p : α → Bool) (k : ℕ) (l : List α) (c : ℕ) :
    (l.foldl (fun c a ↦ if p a then c ||| f a else c) c).testBit k
      = (c.testBit k || l.any fun a ↦ p a && (f a).testBit k) := by
  induction l generalizing c with
  | nil => simp
  | cons a t ih =>
      simp only [List.foldl_cons, List.any_cons, ih]
      by_cases hp : p a
      · simp [hp, Nat.testBit_or, Bool.or_assoc]
      · simp [hp]

theorem shl_bit (acc : UInt64) (c : Bool) (t : Nat) (ht : t < 64) :
    (acc <<< 1 ||| (if c then 1 else 0)).toBitVec.getLsbD t
      = if t = 0 then c else acc.toBitVec.getLsbD (t - 1) := by
  have h : (acc <<< 1).toBitVec = acc.toBitVec <<< (1:Nat) := rfl
  simp only [UInt64.toBitVec_or, h, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · cases c <;> simp
  · cases c <;> simp [ht, Nat.not_lt.2 hpos, Nat.ne_of_gt hpos]

theorem shl_natshift (acc : UInt64) (m : Nat) (hm : m < 64) :
    (acc <<< UInt64.ofNat m).toBitVec = acc.toBitVec <<< m := by
  change acc.toBitVec <<< (((UInt64.ofNat m).toBitVec % 64).toNat) = acc.toBitVec <<< m
  congr 1
  rw [BitVec.toNat_umod]
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm,
    Nat.mod_eq_of_lt (show m < 18446744073709551616 by omega)]
