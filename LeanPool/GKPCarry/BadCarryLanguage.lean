/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.GKPCarry.CarryArithmetic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.IntervalCases

/-!
# The regular language of deficient ternary carries

A four-state deterministic automaton recognizes the ternary words whose
doubling creates fewer than two carries.  Its language is classified as three
explicit digit patterns.  This turns the remaining GKP power-of-two condition
into an exact regular-language avoidance statement.
-/

namespace GKPCarry

open Nat

/-- State of the deficient-carry automaton while scanning little-endian ternary
digits. -/
inductive BadCarryState where
  | zeroCarry
  | oneCarryOut
  | oneCarryNoCarry
  | good
  deriving DecidableEq, Repr

/-- One transition of the deficient-carry automaton. -/
def badCarryStateStep : BadCarryState → ℕ → BadCarryState
  | .good, _ => .good
  | .zeroCarry, digit =>
      if digit = 2 then .oneCarryOut
      else if digit < 2 then .zeroCarry else .good
  | .oneCarryOut, digit =>
      if digit = 0 then .oneCarryNoCarry else .good
  | .oneCarryNoCarry, digit =>
      if digit < 2 then .oneCarryNoCarry else .good

/-- Run the automaton from an arbitrary state. -/
def badCarryStateAux : List ℕ → BadCarryState → BadCarryState
  | [], state => state
  | digit :: digits, state =>
      badCarryStateAux digits (badCarryStateStep state digit)

/-- Run the automaton from its initial state. -/
def badCarryState (digits : List ℕ) : BadCarryState :=
  badCarryStateAux digits .zeroCarry

/-- Boolean membership in the deficient-carry language. -/
def badCarryLanguage (digits : List ℕ) : Bool :=
  decide (badCarryState digits ≠ .good)

/-- Incoming arithmetic carry represented by an automaton state. -/
def BadCarryState.incomingCarry : BadCarryState → ℕ
  | .zeroCarry => 0
  | .oneCarryOut => 1
  | .oneCarryNoCarry => 0
  | .good => 0

/-- Additional carries required to reach the accepting state. -/
def BadCarryState.neededCarries : BadCarryState → ℕ
  | .zeroCarry => 2
  | .oneCarryOut => 1
  | .oneCarryNoCarry => 1
  | .good => 0

lemma badCarryStateAux_good (digits : List ℕ) :
    badCarryStateAux digits .good = .good := by
  induction digits with
  | nil => rfl
  | cons digit digits ih => simp [badCarryStateAux, badCarryStateStep, ih]

lemma badCarryStateAux_ne_good_iff_carryCount_lt_needed :
    ∀ digits : List ℕ, (∀ digit ∈ digits, digit < 3) →
      ∀ state : BadCarryState,
        badCarryStateAux digits state ≠ .good ↔
          ternaryDoubleCarryCountAux digits state.incomingCarry <
            state.neededCarries
  | [], _hdigits, state => by
      cases state <;>
        simp [badCarryStateAux, BadCarryState.neededCarries,
          ternaryDoubleCarryCountAux]
  | digit :: digits, hdigits, state => by
      have hdigit : digit < 3 := hdigits digit List.mem_cons_self
      have htail : ∀ d ∈ digits, d < 3 :=
        fun d hd => hdigits d (List.mem_cons_of_mem digit hd)
      cases state <;> interval_cases digit <;>
        simp [badCarryStateAux, badCarryStateStep,
          BadCarryState.incomingCarry, BadCarryState.neededCarries,
          ternaryDoubleCarryCountAux, ternaryDoubleCarryStep,
          badCarryStateAux_ne_good_iff_carryCount_lt_needed digits htail,
          badCarryStateAux_good]

/-- Automaton correctness: on valid ternary words, membership is equivalent to
creating fewer than two carries under doubling. -/
theorem badCarryLanguage_true_iff_carryCount_lt_two
    {digits : List ℕ} (hdigits : ∀ digit ∈ digits, digit < 3) :
    badCarryLanguage digits = true ↔
      ternaryDoubleCarryCount digits < 2 := by
  rw [badCarryLanguage, decide_eq_true_eq]
  simpa [badCarryState, ternaryDoubleCarryCount,
    BadCarryState.incomingCarry, BadCarryState.neededCarries] using
      (badCarryStateAux_ne_good_iff_carryCount_lt_needed
        digits hdigits .zeroCarry)

/-! ## Concrete classification of the language -/

/-- Every digit in the word is `0` or `1`. -/
def badCarryAllZeroOrOne (digits : List ℕ) : Prop :=
  ∀ digit ∈ digits, digit < 2

/-- The unique digit `2` is the most significant digit. -/
def badCarryExactlyOneTopTwo (digits : List ℕ) : Prop :=
  ∃ lows : List ℕ,
    badCarryAllZeroOrOne lows ∧ digits = lows ++ [2]

/-- The unique digit `2` is followed by a higher `0`, with all other digits
equal to `0` or `1`. -/
def badCarryExactlyOneTwoFollowedByZero (digits : List ℕ) : Prop :=
  ∃ lows highs : List ℕ,
    badCarryAllZeroOrOne lows ∧ badCarryAllZeroOrOne highs ∧
      digits = lows ++ 2 :: 0 :: highs

/-- The union of the three concrete deficient-carry shapes. -/
def badCarryLanguageShape (digits : List ℕ) : Prop :=
  badCarryAllZeroOrOne digits ∨
    badCarryExactlyOneTopTwo digits ∨
      badCarryExactlyOneTwoFollowedByZero digits

lemma badCarryAllZeroOrOne_cons {digit : ℕ} {digits : List ℕ} :
    badCarryAllZeroOrOne (digit :: digits) ↔
      digit < 2 ∧ badCarryAllZeroOrOne digits := by
  simp [badCarryAllZeroOrOne]

lemma badCarryAllZeroOrOne_cons_of_lt
    {digit : ℕ} {digits : List ℕ} (hdigit : digit < 2) :
    badCarryAllZeroOrOne (digit :: digits) ↔
      badCarryAllZeroOrOne digits := by
  simp [badCarryAllZeroOrOne_cons, hdigit]

lemma badCarryExactlyOneTopTwo_cons_of_lt
    {digit : ℕ} {digits : List ℕ} (hdigit : digit < 2) :
    badCarryExactlyOneTopTwo (digit :: digits) ↔
      badCarryExactlyOneTopTwo digits := by
  constructor
  · rintro ⟨lows, hlows, hshape⟩
    cases lows with
    | nil =>
        simp only [List.nil_append, List.cons.injEq] at hshape
        omega
    | cons d ds =>
        simp only [List.cons_append, List.cons.injEq] at hshape
        rcases hshape with ⟨rfl, hshape⟩
        exact ⟨ds, (badCarryAllZeroOrOne_cons.mp hlows).2, hshape⟩
  · rintro ⟨lows, hlows, rfl⟩
    exact ⟨digit :: lows,
      badCarryAllZeroOrOne_cons.mpr ⟨hdigit, hlows⟩, by simp⟩

lemma badCarryExactlyOneTwoFollowedByZero_cons_of_lt
    {digit : ℕ} {digits : List ℕ} (hdigit : digit < 2) :
    badCarryExactlyOneTwoFollowedByZero (digit :: digits) ↔
      badCarryExactlyOneTwoFollowedByZero digits := by
  constructor
  · rintro ⟨lows, highs, hlows, hhighs, hshape⟩
    cases lows with
    | nil =>
        simp only [List.nil_append, List.cons.injEq] at hshape
        omega
    | cons d ds =>
        simp only [List.cons_append, List.cons.injEq] at hshape
        rcases hshape with ⟨rfl, hshape⟩
        exact ⟨ds, highs, (badCarryAllZeroOrOne_cons.mp hlows).2,
          hhighs, hshape⟩
  · rintro ⟨lows, highs, hlows, hhighs, rfl⟩
    exact ⟨digit :: lows, highs,
      badCarryAllZeroOrOne_cons.mpr ⟨hdigit, hlows⟩,
      hhighs, by simp⟩

lemma badCarryLanguageShape_cons_of_lt
    {digit : ℕ} {digits : List ℕ} (hdigit : digit < 2) :
    badCarryLanguageShape (digit :: digits) ↔
      badCarryLanguageShape digits := by
  unfold badCarryLanguageShape
  rw [badCarryAllZeroOrOne_cons_of_lt hdigit,
    badCarryExactlyOneTopTwo_cons_of_lt hdigit,
    badCarryExactlyOneTwoFollowedByZero_cons_of_lt hdigit]

lemma badCarryStateAux_oneCarryNoCarry_ne_good_iff_allZeroOrOne :
    ∀ digits : List ℕ,
      badCarryStateAux digits .oneCarryNoCarry ≠ .good ↔
        badCarryAllZeroOrOne digits
  | [] => by simp [badCarryStateAux, badCarryAllZeroOrOne]
  | digit :: digits => by
      by_cases hdigit : digit < 2
      · simp [badCarryStateAux, badCarryStateStep, hdigit,
          badCarryAllZeroOrOne_cons_of_lt hdigit,
          badCarryStateAux_oneCarryNoCarry_ne_good_iff_allZeroOrOne digits]
      · have hshape : ¬ badCarryAllZeroOrOne (digit :: digits) := by
          intro hall
          exact hdigit ((badCarryAllZeroOrOne_cons.mp hall).1)
        simp [badCarryStateAux, badCarryStateStep, hdigit,
          badCarryStateAux_good, hshape]

lemma badCarryStateAux_oneCarryOut_ne_good_iff :
    ∀ digits : List ℕ,
      badCarryStateAux digits .oneCarryOut ≠ .good ↔
        digits = [] ∨
          ∃ highs : List ℕ,
            badCarryAllZeroOrOne highs ∧ digits = 0 :: highs
  | [] => by simp [badCarryStateAux]
  | digit :: digits => by
      by_cases hdigit : digit = 0
      · subst digit
        simp [badCarryStateAux, badCarryStateStep,
          badCarryStateAux_oneCarryNoCarry_ne_good_iff_allZeroOrOne digits]
      · simp [badCarryStateAux, badCarryStateStep, hdigit,
          badCarryStateAux_good]

lemma badCarryLanguageShape_two_cons_iff {digits : List ℕ} :
    badCarryLanguageShape (2 :: digits) ↔
      digits = [] ∨
        ∃ highs : List ℕ,
          badCarryAllZeroOrOne highs ∧ digits = 0 :: highs := by
  unfold badCarryLanguageShape badCarryExactlyOneTopTwo
    badCarryExactlyOneTwoFollowedByZero
  constructor
  · rintro (hall | htop | hzero)
    · have := hall 2 List.mem_cons_self
      omega
    · rcases htop with ⟨lows, hlows, hshape⟩
      cases lows with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at hshape
          exact Or.inl hshape.2
      | cons d ds =>
          simp only [List.cons_append, List.cons.injEq] at hshape
          have hdigit := hlows d List.mem_cons_self
          omega
    · rcases hzero with ⟨lows, highs, hlows, hhighs, hshape⟩
      cases lows with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at hshape
          exact Or.inr ⟨highs, hhighs, hshape.2⟩
      | cons d ds =>
          simp only [List.cons_append, List.cons.injEq] at hshape
          have hdigit := hlows d List.mem_cons_self
          omega
  · rintro (rfl | ⟨highs, hhighs, rfl⟩)
    · exact Or.inr (Or.inl ⟨[], by simp [badCarryAllZeroOrOne], by simp⟩)
    · exact Or.inr (Or.inr ⟨[], highs, by simp [badCarryAllZeroOrOne],
        hhighs, by simp⟩)

lemma badCarryLanguageShape_cons_of_invalid
    {digit : ℕ} {digits : List ℕ}
    (hsmall : ¬ digit < 2) (htwo : digit ≠ 2) :
    ¬ badCarryLanguageShape (digit :: digits) := by
  intro hshape
  unfold badCarryLanguageShape badCarryExactlyOneTopTwo
    badCarryExactlyOneTwoFollowedByZero at hshape
  rcases hshape with hall | htop | hzero
  · exact hsmall ((badCarryAllZeroOrOne_cons.mp hall).1)
  · rcases htop with ⟨lows, hlows, hshape⟩
    cases lows with
    | nil =>
        simp only [List.nil_append, List.cons.injEq] at hshape
        exact htwo hshape.1
    | cons d ds =>
        simp only [List.cons_append, List.cons.injEq] at hshape
        have hdigit := hlows d List.mem_cons_self
        omega
  · rcases hzero with ⟨lows, highs, hlows, hhighs, hshape⟩
    cases lows with
    | nil =>
        simp only [List.nil_append, List.cons.injEq] at hshape
        exact htwo hshape.1
    | cons d ds =>
        simp only [List.cons_append, List.cons.injEq] at hshape
        have hdigit := hlows d List.mem_cons_self
        omega

lemma badCarryStateAux_zeroCarry_ne_good_iff_shape :
    ∀ digits : List ℕ,
      badCarryStateAux digits .zeroCarry ≠ .good ↔
        badCarryLanguageShape digits
  | [] => by
      simp [badCarryStateAux, badCarryLanguageShape, badCarryAllZeroOrOne]
  | digit :: digits => by
      by_cases hsmall : digit < 2
      · have htwo : digit ≠ 2 := by omega
        simp [badCarryStateAux, badCarryStateStep, hsmall, htwo,
          badCarryStateAux_zeroCarry_ne_good_iff_shape digits,
          badCarryLanguageShape_cons_of_lt hsmall]
      · by_cases htwo : digit = 2
        · subst digit
          simp [badCarryStateAux, badCarryStateStep,
            badCarryStateAux_oneCarryOut_ne_good_iff digits,
            badCarryLanguageShape_two_cons_iff]
        · have hshape := badCarryLanguageShape_cons_of_invalid
            (digits := digits) hsmall htwo
          simp [badCarryStateAux, badCarryStateStep, hsmall, htwo,
            badCarryStateAux_good, hshape]

/-- Exact classification of the deficient-carry language into three explicit
little-endian digit shapes. -/
theorem badCarryLanguage_true_iff_shape (digits : List ℕ) :
    badCarryLanguage digits = true ↔
      badCarryLanguageShape digits := by
  rw [badCarryLanguage, decide_eq_true_eq]
  simpa [badCarryState] using
    badCarryStateAux_zeroCarry_ne_good_iff_shape digits

end GKPCarry
