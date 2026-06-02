/-
Copyright (c) 2023 Alex J. Best and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/

import LeanPool.EcTateLean.Algebra.Ring.Basic
import Mathlib.Algebra.CharP.Lemmas

/-!
# LeanPool.EcTateLean.Algebra.CharP.Basic

Imported Lean Pool material for `LeanPool.EcTateLean.Algebra.CharP.Basic`.
-/

lemma ringChar_is_zero_or_prime (R : Type _) [NonAssocSemiring R] [NoZeroDivisors R]
    [Nontrivial R] : ringChar R = 0 ∨ Nat.Prime (ringChar R) :=
  (CharP.char_is_prime_or_zero R (ringChar R)).symm

lemma add_pow_ringChar {R : Type _} [CommRing R] [IsDomain R] (a b : R) (h : ringChar R ≠ 0) :
    (a + b) ^ ringChar R =
    a ^ ringChar R +
    b ^ ringChar R := by
  have : NeZero (ringChar R) := ⟨h⟩
  have : CharP R (ringChar R) := ringChar.charP R
  have : Fact (Nat.Prime (ringChar R)) := CharP.char_is_prime_of_pos R (ringChar R)
  exact add_pow_char a b (ringChar R)

lemma sub_pow_ringChar {R : Type _} [CommRing R] [IsDomain R] (a b : R) (h : ringChar R ≠ 0) :
    (a - b) ^ ringChar R =
    a ^ ringChar R -
    b ^ ringChar R := by
  have : NeZero (ringChar R) := ⟨h⟩
  have : CharP R (ringChar R) := ringChar.charP R
  have : Fact (Nat.Prime (ringChar R)) := CharP.char_is_prime_of_pos R (ringChar R)
  exact sub_pow_char a b

lemma pow_ringChar_injective {R : Type _} [CommRing R] [IsDomain R]
    (hn : ringChar R ≠ 0) : Function.Injective (· ^ ringChar R : R → R) := by
  intros x y h
  rw [←sub_eq_zero] at *
  rw [←sub_eq_zero] at *
  simp only [sub_zero] at *
  rw [← sub_pow_ringChar _ _ hn] at h
  exact (pow_eq_zero_iff hn).mp h
