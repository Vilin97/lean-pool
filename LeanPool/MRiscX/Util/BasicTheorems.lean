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
  specialize H1 HP
  specialize H2 HP
  have H: (Q → C) ∧ (¬Q → C) → C := by
    simp
  apply H
  constructor
  · exact H1
  · exact H2


theorem Nat.mod_succ_eq {a b m : ℕ} : a % m = b % m ↔ (a + 1) % m = (b + 1) % m := by
  constructor
  · exact add_mod_eq_add_mod_right 1
  · intro h₁
    rw[← ModEq] at *
    exact ModEq.add_right_cancel' 1 h₁


theorem Nat.le_sub_one_le : ∀ (n m : Nat), n ≤ m → n - 1 ≤ m := by
  intros n m h
  cases n with
  | zero =>
    apply Nat.zero_le
  | succ n' =>
    apply Nat.le_trans (Nat.le_succ n')
    exact h

theorem Nat.gt_zero_le_one : ∀ (n : ℕ),
  (0 < n) ↔ 1 ≤ n := by
  intros n
  apply Iff.intro
  · intros h
    apply Nat.succ_le_of_lt h
  · intros h
    apply Nat.succ_le_of_lt h


theorem Nat.add_gt_zero_gt_zero : ∀ (n m: ℕ) ,
  0 < n →
  0 < n + m
  := by
  intros n m h
  rw [Nat.add_comm]
  apply Nat.gt_of_not_le
  simp only [le_zero_eq, Nat.add_eq_zero_iff, not_and]
  intro _ neq
  rw [neq] at h
  contradiction



theorem Nat.add_gt_zero : ∀ (n m : Nat),
  n > 0 →
  n + m > 0 := by
  intros n
  cases n with
  | zero => simp
  | succ n' =>
    intros m a
    apply Nat.add_gt_zero_gt_zero
    simp



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
  intros a b c BLtA ALtBC
  rw [← Nat.lt_add_cancel_right (k := b)]
  rw [Nat.sub_add_cancel]
  · rw [Nat.add_comm]
    exact ALtBC
  · apply Nat.le_of_lt
    exact BLtA


theorem Nat.size_sub_lt_size : ∀ (x l s: Nat),
  l < s →
  x ≤ l →
  x ≥ 1 →
  l - x + 1 < s := by
  intros x l s hl hx h1
  have x_sub_l : l - x < l := by
    apply Nat.sub_lt
    · apply Nat.lt_of_lt_of_le
      · apply Nat.lt_of_succ_le h1
      · exact hx
    · apply Nat.lt_of_succ_le h1

  have s_sub_l' : l - x + 1 ≤ l := by
    rw [Nat.lt_iff_add_one_le] at x_sub_l
    exact x_sub_l
  apply Nat.lt_of_le_of_lt
  · exact s_sub_l'
  · exact hl


theorem UInt64.gt_zero_neq_zero : ∀ (u:UInt64),
  u > 0 → u ≠ 0 := by
  intro u h neq
  rw [neq] at h
  contradiction

theorem UInt64.lt_zero : ∀ (u:UInt64), u < 0 ↔ False := by
  intro u
  apply Iff.intro
  · intros h
    cases u with
    | ofBitVec s => cases h
  · intros h
    contradiction


theorem UInt64.lt_toNat_iff : ∀ (u i : UInt64),
  u.toNat < i.toNat ↔ u < i := by
  intros u i
  apply Iff.intro
  · intros h
    exact h
  · intros h
    exact h

theorem UInt64.le_toNat_iff : ∀ (u i : UInt64),
  u.toNat ≤ i.toNat ↔ u ≤ i := by
  intros u i
  apply Iff.intro
  · intros h
    exact h
  · intros h
    exact h

theorem UInt64.add_lt_add : ∀ (n m k c : UInt64),
  n < m ∧ k < c →
  m.toNat + c.toNat < UInt64.size →
  n + k < m + c := by
  rintro n m k c ⟨hlt_l, hlt_r⟩ hsum
  have hnm : n.toNat < m.toNat := hlt_l
  have hkc : k.toNat < c.toNat := hlt_r
  have hfin : n.toNat + k.toNat < m.toNat + c.toNat :=  Nat.add_lt_add hnm hkc
  have mcNat : (m + c).toNat = m.toNat + c.toNat := by
    rw [UInt64.toNat_add]
    apply Nat.mod_eq_of_lt
    exact hsum
  have nkNat : (n + k).toNat = n.toNat + k.toNat := by
    rw [UInt64.toNat_add]
    apply Nat.mod_eq_of_lt
    apply Nat.lt_trans
    · exact hfin
    · exact hsum
  rw [←UInt64.lt_toNat_iff, mcNat, nkNat]
  exact hfin



theorem UInt64.add_cancel_right_iff : ∀ (u i k : UInt64),
  u + k = i + k ↔ u = i := by
  intros u i k
  apply Iff.intro
  · intros h
    simp at h
    (repeat assumption)
  · intros h
    rw [h]

theorem UInt64.add_cancel_left_iff : ∀ (u i k: UInt64),
  k + u = k + i ↔ u = i := by
  intros u i k
  apply Iff.intro
  · intros h
    rw [←UInt64.add_cancel_right_iff (k := k), UInt64.add_comm]
    nth_rewrite 2 [UInt64.add_comm]
    exact h
  · intros h
    rw [h]


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
  apply UInt64.lt_asymm
  · assumption
  · exact h_iLtl



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
