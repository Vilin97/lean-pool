/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.GKPCarry.BadCarryLanguage
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Ring

/-!
# Counting deficient-carry ternary words

The automaton gives an exact enumeration theorem.  Among all ternary words of
length `m ≥ 2`, precisely `(m + 5) * 2 ^ (m - 2)` create fewer than two carries
when doubled.  The theorem below uses the subtraction-free parameterization
`m = n + 2`.
-/

namespace GKPCarry

open scoped BigOperators

/-- Convert a fixed-length word over `Fin 3` to a list of natural digits. -/
def ternaryWordDigits {length : ℕ}
    (word : List.Vector (Fin 3) length) : List ℕ :=
  word.toList.map Fin.val

/-- Peel the least significant digit off a nonempty ternary word. -/
lemma ternaryWordDigits_succ {length : ℕ}
    (word : List.Vector (Fin 3) (length + 1)) :
    ternaryWordDigits word =
      (word.head : ℕ) :: ternaryWordDigits word.tail := by
  conv_lhs => rw [← List.Vector.cons_head_tail word]
  simp only [ternaryWordDigits, List.Vector.toList_cons, List.map_cons]

/-- Fixed-length ternary words that remain outside `.good` when read from a
given automaton state. -/
abbrev BadCarryWordsFrom (state : BadCarryState) (length : ℕ) :=
  {word : List.Vector (Fin 3) length //
    badCarryStateAux (ternaryWordDigits word) state ≠ .good}

/-- Fixed-length ternary words whose doubling creates fewer than two carries. -/
abbrev BadCarryWords (length : ℕ) :=
  BadCarryWordsFrom .zeroCarry length

/-- Peeling the least significant digit gives the recursive decomposition of
deficient-carry words. -/
def badCarryWordsFromSuccEquiv (state : BadCarryState) (length : ℕ) :
    BadCarryWordsFrom state (length + 1) ≃
      Σ digit : Fin 3,
        BadCarryWordsFrom (badCarryStateStep state digit.val) length where
  toFun word :=
    ⟨word.val.head,
      ⟨word.val.tail, by
        have hproperty := word.property
        rw [ternaryWordDigits_succ] at hproperty
        simpa [badCarryStateAux] using hproperty⟩⟩
  invFun pair :=
    ⟨List.Vector.cons pair.1 pair.2.val, by
      simpa [BadCarryWordsFrom, ternaryWordDigits, badCarryStateAux] using
        pair.2.property⟩
  left_inv word := by
    apply Subtype.ext
    exact List.Vector.cons_head_tail word.val
  right_inv pair := by
    rcases pair with ⟨digit, word⟩
    rfl

/-- Recursive dynamic-programming count for words read from a given state. -/
def badCarryWordCountFrom : BadCarryState → ℕ → ℕ
  | state, 0 => if state = .good then 0 else 1
  | state, length + 1 =>
      ∑ digit : Fin 3,
        badCarryWordCountFrom (badCarryStateStep state digit.val) length

/-- The recursive count is the actual cardinality of the corresponding finite
word type. -/
theorem card_badCarryWordsFrom_eq_count
    (state : BadCarryState) (length : ℕ) :
    Fintype.card (BadCarryWordsFrom state length) =
      badCarryWordCountFrom state length := by
  induction length generalizing state with
  | zero =>
      cases state <;> decide
  | succ length ih =>
      rw [Fintype.card_congr (badCarryWordsFromSuccEquiv state length)]
      rw [Fintype.card_sigma]
      simp only [ih]
      rfl

lemma badCarryWordCountFrom_good (length : ℕ) :
    badCarryWordCountFrom .good length = 0 := by
  induction length with
  | zero => simp [badCarryWordCountFrom]
  | succ length ih =>
      simp [badCarryWordCountFrom, badCarryStateStep, ih]

lemma badCarryWordCountFrom_oneCarryNoCarry (length : ℕ) :
    badCarryWordCountFrom .oneCarryNoCarry length = 2 ^ length := by
  induction length with
  | zero => simp [badCarryWordCountFrom]
  | succ length ih =>
      rw [badCarryWordCountFrom, Fin.sum_univ_three]
      change
        badCarryWordCountFrom .oneCarryNoCarry length +
            badCarryWordCountFrom .oneCarryNoCarry length +
            badCarryWordCountFrom .good length =
          2 ^ (length + 1)
      rw [ih, badCarryWordCountFrom_good, pow_succ]
      ring

lemma badCarryWordCountFrom_oneCarryOut_succ (length : ℕ) :
    badCarryWordCountFrom .oneCarryOut (length + 1) = 2 ^ length := by
  rw [badCarryWordCountFrom, Fin.sum_univ_three]
  simp [badCarryStateStep, badCarryWordCountFrom_good,
    badCarryWordCountFrom_oneCarryNoCarry]

lemma badCarryWordCountFrom_zeroCarry_succ (length : ℕ) :
    badCarryWordCountFrom .zeroCarry (length + 1) =
      2 * badCarryWordCountFrom .zeroCarry length +
        badCarryWordCountFrom .oneCarryOut length := by
  rw [badCarryWordCountFrom, Fin.sum_univ_three]
  simp [badCarryStateStep]
  omega

/-- Exact dynamic-programming count of deficient-carry ternary words. -/
theorem badCarryWordCountFrom_zeroCarry_closed (n : ℕ) :
    badCarryWordCountFrom .zeroCarry (n + 2) =
      (n + 7) * 2 ^ n := by
  induction n with
  | zero =>
      simp [badCarryWordCountFrom, Fin.sum_univ_three, badCarryStateStep]
  | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega]
      rw [badCarryWordCountFrom_zeroCarry_succ, ih]
      rw [show n + 2 = (n + 1) + 1 by omega]
      rw [badCarryWordCountFrom_oneCarryOut_succ]
      rw [pow_succ]
      ring

/-- Headline enumeration theorem: among all ternary words of length `n + 2`,
exactly `(n + 7) * 2 ^ n` have fewer than two doubling carries. -/
theorem card_badCarryWords (n : ℕ) :
    Fintype.card (BadCarryWords (n + 2)) =
      (n + 7) * 2 ^ n := by
  rw [card_badCarryWordsFrom_eq_count]
  exact badCarryWordCountFrom_zeroCarry_closed n

/-- The ambient set contains all `3 ^ (n + 2)` ternary words. -/
theorem card_allTernaryWords (n : ℕ) :
    Fintype.card (List.Vector (Fin 3) (n + 2)) = 3 ^ (n + 2) := by
  simp

end GKPCarry
