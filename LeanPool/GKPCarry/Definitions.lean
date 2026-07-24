/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.Count
import Mathlib.Data.Nat.Digits.Defs

/-!
# Ternary prefixes and doubling carries

This file gives the definitions used by the carry-language theory and its
bounded C3 corollary. Ternary digit lists are little-endian, following
`Nat.digits`.
-/

namespace GKPCarry

/-- Length of the canonical base-three expansion of `n`. -/
def ternaryLength (n : ℕ) : ℕ :=
  (Nat.digits 3 n).length

/-- The first `depth` ternary digits of `n` contain at least two `2`s. -/
def hasTwoTernaryTwosBelow (depth n : ℕ) : Prop :=
  2 ≤ ((Nat.digits 3 n).take depth).count 2

/-- One outgoing-carry step when a ternary digit is doubled. -/
def ternaryDoubleCarryStep (carry digit : ℕ) : ℕ :=
  if 3 ≤ 2 * digit + carry then 1 else 0

/-- Count outgoing carries while doubling a little-endian ternary digit list. -/
def ternaryDoubleCarryCountAux : List ℕ → ℕ → ℕ
  | [], _ => 0
  | digit :: digits, carry =>
      let next := ternaryDoubleCarryStep carry digit
      next + ternaryDoubleCarryCountAux digits next

/-- Count carries while doubling a little-endian ternary digit list. -/
def ternaryDoubleCarryCount (digits : List ℕ) : ℕ :=
  ternaryDoubleCarryCountAux digits 0

/-- Number of doubling carries visible in the first `depth` ternary digits. -/
def prefixTernaryDoubleCarryCount (depth n : ℕ) : ℕ :=
  ternaryDoubleCarryCount ((Nat.digits 3 n).take depth)

lemma count_two_le_ternaryDoubleCarryCountAux
    (digits : List ℕ) (carry : ℕ) :
    digits.count 2 ≤ ternaryDoubleCarryCountAux digits carry := by
  induction digits generalizing carry with
  | nil => simp [ternaryDoubleCarryCountAux]
  | cons digit digits ih =>
      by_cases hdigit : digit = 2
      · subst digit
        have hstep : ternaryDoubleCarryStep carry 2 = 1 := by
          simp [ternaryDoubleCarryStep, show 3 ≤ 2 * 2 + carry by omega]
        have htail := ih 1
        simp [ternaryDoubleCarryCountAux, hstep]
        omega
      · simpa [ternaryDoubleCarryCountAux, hdigit] using
          le_trans (ih (ternaryDoubleCarryStep carry digit))
            (Nat.le_add_left _ _)

/-- Two digit-`2`s in a prefix force at least two ternary doubling carries. -/
theorem two_le_prefixTernaryDoubleCarryCount_of_hasTwoTernaryTwosBelow
    {depth n : ℕ} (h : hasTwoTernaryTwosBelow depth n) :
    2 ≤ prefixTernaryDoubleCarryCount depth n := by
  exact le_trans h
    (by
      simpa [prefixTernaryDoubleCarryCount, ternaryDoubleCarryCount] using
        count_two_le_ternaryDoubleCarryCountAux
          ((Nat.digits 3 n).take depth) 0)

lemma ternaryDoubleCarryCountAux_take_le
    (depth : ℕ) (digits : List ℕ) (carry : ℕ) :
    ternaryDoubleCarryCountAux (digits.take depth) carry ≤
      ternaryDoubleCarryCountAux digits carry := by
  induction depth generalizing digits carry with
  | zero => simp [ternaryDoubleCarryCountAux]
  | succ depth ih =>
      cases digits with
      | nil => simp [ternaryDoubleCarryCountAux]
      | cons digit digits =>
          simp only [List.take_succ_cons, ternaryDoubleCarryCountAux]
          exact Nat.add_le_add_left
            (ih digits (ternaryDoubleCarryStep carry digit)) _

/-- A prefix cannot contain more doubling carries than the complete word. -/
theorem prefixTernaryDoubleCarryCount_le (depth n : ℕ) :
    prefixTernaryDoubleCarryCount depth n ≤
      ternaryDoubleCarryCount (Nat.digits 3 n) := by
  exact ternaryDoubleCarryCountAux_take_le depth (Nat.digits 3 n) 0

end GKPCarry
