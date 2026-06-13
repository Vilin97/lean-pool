/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import LeanPool.MRiscX.Hoare.HoareCore
import Mathlib.Tactic.NthRewrite
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Mathlib.Data.Nat.ModEq

/-!
This file contains a list of theorems required during the implementation of this dsl
and the creation of the proof for the otp example.
Some of them might actually already exists in the mathlib but
i had trouble finding them.
-/

theorem excluded_middle_implication : ∀ (P Q C : Prop),
  (P ∧ Q → C) ∧ (P ∧ ¬Q → C) →
  P →
  C
  := by
  intros P Q C
  simp only [and_imp]
  intros H1 H2 HP
  tauto


theorem Nat.mod_succ_eq {a b m : ℕ} : a % m = b % m ↔ (a + 1) % m = (b + 1) % m := by
  constructor
  · exact add_mod_eq_add_mod_right 1
  · exact fun h₁ => ModEq.add_right_cancel' 1 h₁


theorem Nat.le_sub_one_le : ∀ (n m : Nat), n ≤ m → n - 1 ≤ m := by
  omega

theorem Nat.gt_zero_le_one : ∀ (n : ℕ),
  (0 < n) ↔ 1 ≤ n := by
  omega


theorem Nat.add_gt_zero_gt_zero : ∀ (n m: ℕ) ,
  0 < n →
  0 < n + m
  := by
  omega



theorem Nat.add_gt_zero : ∀ (n m : Nat),
  n > 0 →
  n + m > 0 := by
  omega



theorem Nat.gt_and_neq_succ_gt_succ : ∀ (n m : ℕ), n < m → m ≠ n + 1 → n + 1 < m := by
  intros n m h₁ h₂
  grind

theorem Nat.lt_add_cancel_right : ∀ (n m k: ℕ),
  n + k < m + k ↔ n < m
  := by
  simp


theorem Nat.lt_sub_left : ∀ (a b c : ℕ),
  b < a →
  a < b + c →
  a - b < c := by
  omega


theorem Nat.size_sub_lt_size : ∀ (x l s: Nat),
  l < s →
  x ≤ l →
  x ≥ 1 →
  l - x + 1 < s := by
  omega


theorem UInt64.gt_zero_neq_zero : ∀ (u:UInt64),
  u > 0 → u ≠ 0 := by
  intro u h neq
  rw [neq] at h
  contradiction

theorem UInt64.lt_zero : ∀ (u:UInt64), u < 0 ↔ False := by
  intro u
  simp


theorem UInt64.lt_toNat_iff : ∀ (u i : UInt64),
  u.toNat < i.toNat ↔ u < i := by
  intros u i
  exact Iff.rfl

theorem UInt64.le_toNat_iff : ∀ (u i : UInt64),
  u.toNat ≤ i.toNat ↔ u ≤ i := by
  intros u i
  exact Iff.rfl

theorem UInt64.add_lt_add : ∀ (n m k c : UInt64),
  n < m ∧ k < c →
  m.toNat + c.toNat < UInt64.size →
  n + k < m + c := by
  rintro n m k c ⟨hlt_l, hlt_r⟩ hsum
  have hfin : n.toNat + k.toNat < m.toNat + c.toNat := Nat.add_lt_add hlt_l hlt_r
  have mcNat : (m + c).toNat = m.toNat + c.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt hsum]
  have nkNat : (n + k).toNat = n.toNat + k.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (Nat.lt_trans hfin hsum)]
  rw [←UInt64.lt_toNat_iff, mcNat, nkNat]
  exact hfin



theorem UInt64.add_cancel_right_iff : ∀ (u i k : UInt64),
  u + k = i + k ↔ u = i := by
  intros u i k
  simp

theorem UInt64.add_cancel_left_iff : ∀ (u i k: UInt64),
  k + u = k + i ↔ u = i := by
  intros u i k
  simp


theorem UInt64.add_sub_assoc : ∀ (p l x : UInt64),
  x ≤ l →
  x > 0 →
  p + (l - x) + 1 = p + (l - (x - 1)) := by
  intros p l x h_xLeL h_xGtZ
  grind only


theorem UInt64.add_right_ne_of_lt : ∀ (n i l : UInt64),
  i < l →
  n + l ≠ n + i := by
  intro n i l h_iLtl neq
  rw [UInt64.add_cancel_left_iff] at neq
  rw [neq] at h_iLtl
  exact UInt64.lt_irrefl _ h_iLtl



instance instPreorderUInt64LeanPool : Preorder UInt64 where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl := by simp
  le_trans := by apply UInt64.le_trans
  lt_iff_le_not_ge := by
    intros a b
    constructor
    · intros h
      simp only [UInt64.not_le]
      constructor
      · apply UInt64.le_of_lt h
      · exact h
    · simp


instance : WellFoundedLT UInt64 where
  wf := by
    apply Subrelation.wf (r := InvImage (· < ·) UInt64.toNat)
    · intro a b h
      exact UInt64.lt_iff_toNat_lt_toNat.mp h
    · exact InvImage.wf _ wellFounded_lt
