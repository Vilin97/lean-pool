/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.NatOrdinal.Basic
public import Mathlib.SetTheory.Ordinal.Exponential

/-!
# Natural operations on `ω ^ x`

This file characterizes natural operations on powers of `ω`. In particular, we show:

- If `y < ω^ x`, then `ω^ x * n + y = of (ω ^ x.val * n + y.val)`.
- `ω^ (x + y) = ω^ x * ω^ y`.

These two results imply the validity of an algorithm to evaluate natural addition and
multiplication: write down the base `ω` Cantor Normal Forms of both ordinals, and add/multiply them
as polynomials.

## Implementation notes

Surreal exponentiation is not closed on the ordinals. Because of this, we opt against defining a
`Pow` instance on `NatOrdinal`. Instead, we implement our own custom typeclass `Wpow`, giving us
notation `ω^ x` for `of (ω ^ x.val)`. This typeclass will get reused for `IGame` and `Surreal` in
`CombinatorialGames.Surreal.Pow`.
-/

@[expose] public section

open Ordinal

theorem Ordinal.lt_mul_add_one {x y z : Ordinal} : x < y * (z + 1) ↔ ∃ w < y, x ≤ y * z + w := by
  obtain rfl | hy := eq_or_ne y 0
  · simp
  · rw [mul_add_one, lt_add_iff hy]

/-- A typeclass for the the `ω^` notation. -/
class Wpow (α : Type*) where
  /-- The `ω`-map, i.e. base `ω` exponentiation. -/
  wpow : α → α

@[inherit_doc] prefix:75 "ω^ " => Wpow.wpow
recommended_spelling "wpow" for "ω^" in [«termω^_»]

namespace NatOrdinal
variable {x y z : NatOrdinal}

noncomputable instance : Wpow NatOrdinal where
  wpow x := of (ω ^ x.val)

theorem wpow_def (x : NatOrdinal) : ω^ x = of (ω ^ x.val) := rfl
@[simp] theorem of_omega0_opow (x : Ordinal) : of (ω ^ x) = ω^ of x := rfl
@[simp] theorem val_wpow (x : NatOrdinal) : (ω^ x).val = ω ^ x.val := rfl

@[simp] theorem wpow_zero : ω^ (0 : NatOrdinal) = 1 := by simp [wpow_def]
@[simp] theorem wpow_pos (x : NatOrdinal) : 0 < ω^ x := opow_pos _ omega0_pos
@[simp] theorem wpow_ne_zero (x : NatOrdinal) : ω^ x ≠ 0 := (wpow_pos x).ne'

theorem isNormal_wpow : Order.IsNormal (ω^ · : NatOrdinal → NatOrdinal) :=
  Ordinal.isNormal_opow one_lt_omega0

@[simp] theorem wpow_lt_wpow : ω^ x < ω^ y ↔ x < y := isNormal_wpow.strictMono.lt_iff_lt
@[simp] theorem wpow_le_wpow : ω^ x ≤ ω^ y ↔ x ≤ y := isNormal_wpow.strictMono.le_iff_le
@[simp] theorem wpow_inj : ω^ x = ω^ y ↔ x = y := isNormal_wpow.strictMono.injective.eq_iff

private theorem wpow_mul_natCast_add_of_lt_aux {x y : NatOrdinal} (hy : y < ω^ x) (n : ℕ) :
    (∀ z < ω^ x, z + y < ω^ x) ∧ ω^ x * n + y = of (ω ^ x.val * n + y.val) := by
  obtain rfl | hx := eq_or_ne x 0
  · simp_all
  have H : ∀ z < ω^ x, z + y < ω^ x := by
    intro z hz
    have hm := max_lt hy hz
    rw [wpow_def, ← val_lt_iff, lt_omega0_opow (b := x.val) hx] at hm
    obtain ⟨a, ha, n, hn⟩ := hm
    have hyz (n) := (wpow_mul_natCast_add_of_lt_aux (wpow_pos (of a)) n).2
    simp_rw [val_zero, add_zero, ← val_eq_iff, val_of] at hyz
    rw [← hyz] at hn
    calc
      z + y ≤ max y z + max y z := add_le_add (le_max_right ..) (le_max_left ..)
      _ < ω^ of a * n + ω^ of a * n := add_lt_add hn hn
      _ < _ := by
        rw [← mul_add, ← Nat.cast_add, ← val.lt_iff_lt, hyz, val_wpow]
        exact opow_mul_lt_opow (natCast_lt_omega0 _) ha
  refine ⟨H, le_antisymm ?_ ?_⟩
  · refine add_le_iff.2 ⟨?_, ?_⟩ <;> intro z hz
    · match n with
      | 0 => simp at hz
      | 1 =>
        simp_rw [Nat.cast_one, mul_one] at *
        apply (H z hz).trans_le
        rw [wpow_def, of.le_iff_le]
        exact le_self_add ..
      | n + 1 + 1 =>
        rw [Nat.cast_add_one, mul_add_one] at hz
        obtain ⟨a, ha, hz⟩ : ∃ a < ω^ x, z ≤ ω^ x * ↑(n + 1) + a := by
          obtain (⟨a, ha, hz⟩ | h) := lt_add_iff.1 hz
          · have hxn := (wpow_mul_natCast_add_of_lt_aux (wpow_pos x) (n + 1)).2
            simp_rw [val_zero, add_zero] at hxn
            rw [hxn, ← val_lt_iff, Nat.cast_add_one, lt_mul_add_one] at ha
            obtain ⟨b, (hb : of b < ω^ x), hbw⟩ := ha
            rw [val_le_iff, ← val_of b, ← (wpow_mul_natCast_add_of_lt_aux hb n).2] at hbw
            refine ⟨_, hb, hz.trans <| (add_le_add_left hbw _).trans ?_⟩
            rw [add_comm, ← add_assoc, ← mul_one_add, add_comm 1, ← Nat.cast_add_one]
          · exact h
        have ha' := H a ha
        apply (add_le_add_left hz _).trans_lt
        rw [add_assoc, (wpow_mul_natCast_add_of_lt_aux ha' _).2, of.lt_iff_lt]
        apply (le_self_add ..).trans_lt'
        rw [Nat.cast_add_one (n + 1), mul_add]
        simpa
    · rw [(wpow_mul_natCast_add_of_lt_aux (hz.trans hy) n).2]
      simpa
  · exact (oadd_le_add ..).trans (add_le_add_left (omul_le_mul ..) _)
termination_by (x, n, y)

theorem add_lt_wpow (hx : x < ω^ z) (hy : y < ω^ z) : x + y < ω^ z :=
  (wpow_mul_natCast_add_of_lt_aux hy 0).1 x hx

/-- See `wpow_mul_natCast_add_of_lt` for a stronger version. -/
theorem wpow_mul_natCast_add_of_lt' (hy : y < ω^ x) (n : ℕ) :
    ω^ x * n + y = of (ω ^ x.val * n + y.val) :=
  (wpow_mul_natCast_add_of_lt_aux hy n).2

/-- See `wpow_add_of_lt` for a stronger version. -/
theorem wpow_add_of_lt' (hy : y < ω^ x) : ω^ x + y = of (ω ^ x.val + y.val) := by
  simpa using wpow_mul_natCast_add_of_lt' hy 1

theorem wpow_mul_natCast (x : NatOrdinal) (n : ℕ) : ω^ x * n = of (ω ^ x.val * n) := by
  simpa using wpow_mul_natCast_add_of_lt' (wpow_pos _) n

theorem wpow_mul_natCast_lt (h : x < y) (n : ℕ) : ω^ x * n < ω^ y := by
  rw [wpow_mul_natCast]
  exact opow_mul_lt_opow (natCast_lt_omega0 n) h

theorem lt_wpow_iff (hx : x ≠ 0) : y < ω^ x ↔ ∃ z < x, ∃ n : ℕ, y < ω^ z * n := by
  rw [wpow_def, ← val_lt_iff, lt_omega0_opow]
  · simp_rw [wpow_mul_natCast]
    rfl
  · assumption

theorem wpow_le_iff (hx : x ≠ 0) : ω^ x ≤ y ↔ ∀ z < x, ∀ n : ℕ, ω^ z * n ≤ y := by
  rw [← not_lt, lt_wpow_iff hx]
  simp

theorem lt_wpow_add_one_iff : y < ω^ (x + 1) ↔ ∃ n : ℕ, y < ω^ x * n := by
  rw [wpow_def, ← val_lt_iff, val_add_one, ← Order.succ_eq_add_one, lt_omega0_opow_succ]
  simp_rw [wpow_mul_natCast]
  rfl

theorem wpow_add_one_le_iff : ω^ (x + 1) ≤ y ↔ ∀ n : ℕ, ω^ x * n ≤ y := by
  rw [← not_lt, lt_wpow_add_one_iff]
  simp

theorem wpow_mul_natCast_add_of_lt (hy : y < ω^ (x + 1)) (n : ℕ) :
    ω^ x * n + y = of (ω ^ x.val * n + y.val) := by
  obtain ⟨z, hz, m, rfl⟩ : ∃ z < ω^ x, ∃ m : ℕ, y = ω^ x * m + z := by
    rw [wpow_def, ← val_lt_iff, val_add_one, opow_add, opow_one, Ordinal.lt_mul_iff_div_lt] at hy
    · obtain ⟨m, hm⟩ := Ordinal.lt_omega0.1 hy
      have hx : of (y.val % ω ^ x.val) < ω^ x := mod_lt _ (wpow_ne_zero _)
      use of (y.val % ω ^ x.val), hx, m
      rw [wpow_mul_natCast_add_of_lt' hx, ← hm]
      exact (div_add_mod ..).symm
    · exact wpow_ne_zero _
  simp_rw [← add_assoc, wpow_mul_natCast_add_of_lt' hz, val_of, ← add_assoc, ← mul_add,
    ← Nat.cast_add, wpow_mul_natCast_add_of_lt' hz]

theorem wpow_add_of_lt (hy : y < ω^ (x + 1)) : ω^ x + y = of (ω ^ x.val + y.val) := by
  simpa using wpow_mul_natCast_add_of_lt hy 1

theorem wpow_add_wpow (h : x ≤ y) : ω^ y + ω^ x = of (ω ^ y.val + ω ^ x.val) := by
  rw [wpow_add_of_lt, val_wpow]
  simpa using Order.lt_succ_of_le h

theorem wpow_add (x y : NatOrdinal) : ω^ (x + y) = ω^ x * ω^ y := by
  obtain rfl | hx := eq_or_ne x 0; · simp
  obtain rfl | hy := eq_or_ne y 0; · simp
  have h : x + y ≠ 0 := by simp_all
  apply le_antisymm
  · simp_rw [wpow_le_iff h, lt_add_iff]
    rintro z (⟨a, ha, hz⟩ | ⟨a, ha, hz⟩) n <;> apply (mul_le_mul_left (wpow_le_wpow.2 hz) _).trans
    · rw [wpow_add, mul_comm, ← mul_assoc, mul_comm _ (ω^ a)]
      exact mul_le_mul_left (wpow_mul_natCast_lt ha n).le _
    · rw [wpow_add, mul_assoc]
      exact mul_le_mul_right (wpow_mul_natCast_lt ha n).le _
  · simp_rw [mul_le_iff, lt_wpow_iff hx, lt_wpow_iff hy]
    rintro z ⟨a, ha, n, hz⟩ w ⟨b, hb, m, hw⟩
    apply (add_lt_wpow _ _).trans_le  (le_add_right ..)
    · apply (mul_le_mul_left hz.le _).trans_lt
      rw [← mul_comm, ← mul_assoc, mul_comm (ω^ y), ← wpow_add]
      exact wpow_mul_natCast_lt (add_lt_add_left ha y) n
    · apply (mul_le_mul_right hw.le _).trans_lt
      rw [← mul_assoc, ← wpow_add]
      exact wpow_mul_natCast_lt (add_lt_add_right hb x) m
termination_by (x, y)

end NatOrdinal
end
