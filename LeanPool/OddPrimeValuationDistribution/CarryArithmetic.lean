/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.OddPrimeValuationDistribution.Kummer
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Ring

/-!
# Doubling carries in an arbitrary odd base

Write an odd base as `2 * half + 1`.  This module defines the two-state
doubling transducer in that base and proves its arithmetic correctness.  When
the base is prime, the carry count is exactly the prime-adic valuation of the
central binomial coefficient.
-/

namespace OddPrimeValuationDistribution

open Nat

/-- The odd base represented by its lower half-size. -/
def oddBase (half : ℕ) : ℕ := 2 * half + 1

/-- Outgoing carry while doubling one digit in the odd base
`2 * half + 1`. -/
def oddDoubleCarryStep (half carry digit : ℕ) : ℕ :=
  (2 * digit + carry) / oddBase half

/-- Number of outgoing carries while doubling a little-endian word in an odd
base. -/
def oddDoubleCarryCountAux (half : ℕ) : List ℕ → ℕ → ℕ
  | [], _carry => 0
  | digit :: digits, carry =>
      let nextCarry := oddDoubleCarryStep half carry digit
      nextCarry + oddDoubleCarryCountAux half digits nextCarry

/-- Output digits while doubling in an odd base.  The final carry is retained
as the most significant output digit. -/
def oddDoubleDigitsAux (half : ℕ) : List ℕ → ℕ → List ℕ
  | [], carry => [carry]
  | digit :: digits, carry =>
      let nextCarry := oddDoubleCarryStep half carry digit
      ((2 * digit + carry) % oddBase half) ::
        oddDoubleDigitsAux half digits nextCarry

lemma oddBase_pos (half : ℕ) : 0 < oddBase half := by
  simp [oddBase]

lemma oddBase_one_lt {half : ℕ} (hhalf : 0 < half) :
    1 < oddBase half := by
  simp [oddBase]
  omega

lemma oddDoubleCarryStep_le_one
    {half carry digit : ℕ} (hcarry : carry ≤ 1)
    (hdigit : digit < oddBase half) :
    oddDoubleCarryStep half carry digit ≤ 1 := by
  have hnumerator :
      2 * digit + carry < 2 * oddBase half := by
    omega
  have hquotient :
      (2 * digit + carry) / oddBase half < 2 :=
    (Nat.div_lt_iff_lt_mul (oddBase_pos half)).2 hnumerator
  simpa [oddDoubleCarryStep] using hquotient

lemma oddDoubleCarryStep_lt_base
    {half carry digit : ℕ} (hhalf : 0 < half)
    (hcarry : carry ≤ 1) (hdigit : digit < oddBase half) :
    oddDoubleCarryStep half carry digit < oddBase half := by
  have hstep := oddDoubleCarryStep_le_one hcarry hdigit
  have hbase := oddBase_one_lt hhalf
  omega

lemma oddDoubleCarryStep_local (half carry digit : ℕ) :
    (2 * digit + carry) % oddBase half +
        oddBase half * oddDoubleCarryStep half carry digit =
      2 * digit + carry := by
  exact Nat.mod_add_div (2 * digit + carry) (oddBase half)

lemma oddDoubleCarryStep_zero_of_lt_succ
    {half digit : ℕ} (hdigit : digit < half + 1) :
    oddDoubleCarryStep half 0 digit = 0 := by
  unfold oddDoubleCarryStep
  apply Nat.div_eq_of_lt
  simp [oddBase]
  omega

lemma oddDoubleCarryStep_one_of_succ_le
    {half digit : ℕ} (hlower : half + 1 ≤ digit)
    (hupper : digit < oddBase half) :
    oddDoubleCarryStep half 0 digit = 1 := by
  unfold oddDoubleCarryStep
  apply Nat.div_eq_of_lt_le
  · simp [oddBase]
    omega
  · simp [oddBase] at hupper ⊢
    omega

lemma oddDoubleCarryStep_zero_of_lt
    {half digit : ℕ} (hdigit : digit < half) :
    oddDoubleCarryStep half 1 digit = 0 := by
  unfold oddDoubleCarryStep
  apply Nat.div_eq_of_lt
  simp [oddBase]
  omega

lemma oddDoubleCarryStep_one_of_le
    {half digit : ℕ} (hlower : half ≤ digit)
    (hupper : digit < oddBase half) :
    oddDoubleCarryStep half 1 digit = 1 := by
  unfold oddDoubleCarryStep
  apply Nat.div_eq_of_lt_le
  · simp [oddBase]
    omega
  · simp [oddBase] at hupper ⊢
    omega

lemma oddDoubleDigitsAux_length (half : ℕ) (digits : List ℕ) (carry : ℕ) :
    (oddDoubleDigitsAux half digits carry).length = digits.length + 1 := by
  induction digits generalizing carry with
  | nil => simp [oddDoubleDigitsAux]
  | cons digit digits ih => simp [oddDoubleDigitsAux, ih, Nat.add_assoc]

lemma oddDoubleDigitsAux_lt_base
    {half : ℕ} (hhalf : 0 < half) {digits : List ℕ} {carry : ℕ}
    (hcarry : carry ≤ 1)
    (hdigits : ∀ digit ∈ digits, digit < oddBase half) :
    ∀ value ∈ oddDoubleDigitsAux half digits carry,
      value < oddBase half := by
  induction digits generalizing carry with
  | nil =>
      intro value hvalue
      simp only [oddDoubleDigitsAux, List.mem_singleton] at hvalue
      subst value
      have := oddBase_one_lt hhalf
      omega
  | cons digit digits ih =>
      intro value hvalue
      rw [oddDoubleDigitsAux] at hvalue
      rcases List.mem_cons.mp hvalue with rfl | htail
      · exact Nat.mod_lt _ (oddBase_pos half)
      · have hdigit := hdigits digit List.mem_cons_self
        apply ih
          (oddDoubleCarryStep_le_one hcarry hdigit)
          (fun d hd => hdigits d (List.mem_cons_of_mem digit hd))
          value htail

lemma oddDoubleDigitsAux_ofDigits
    {half : ℕ} {digits : List ℕ} {carry : ℕ}
    (hcarry : carry ≤ 1)
    (hdigits : ∀ digit ∈ digits, digit < oddBase half) :
    Nat.ofDigits (oddBase half) (oddDoubleDigitsAux half digits carry) =
      2 * Nat.ofDigits (oddBase half) digits + carry := by
  induction digits generalizing carry with
  | nil => simp [oddDoubleDigitsAux, Nat.ofDigits]
  | cons digit digits ih =>
      have hdigit := hdigits digit List.mem_cons_self
      have htail : ∀ d ∈ digits, d < oddBase half :=
        fun d hd => hdigits d (List.mem_cons_of_mem digit hd)
      have hnext := oddDoubleCarryStep_le_one hcarry hdigit
      have hlocal := oddDoubleCarryStep_local half carry digit
      simp only [oddDoubleDigitsAux, Nat.ofDigits]
      rw [ih hnext htail]
      calc
        (2 * digit + carry) % oddBase half +
            oddBase half *
              (2 * Nat.ofDigits (oddBase half) digits +
                oddDoubleCarryStep half carry digit) =
            ((2 * digit + carry) % oddBase half +
                oddBase half * oddDoubleCarryStep half carry digit) +
              2 * (oddBase half *
                Nat.ofDigits (oddBase half) digits) := by ring
        _ = (2 * digit + carry) +
              2 * (oddBase half *
                Nat.ofDigits (oddBase half) digits) := by rw [hlocal]
        _ = 2 *
              (digit + oddBase half *
                Nat.ofDigits (oddBase half) digits) + carry := by ring

lemma oddDoubleDigitsAux_sum_add_carries
    {half : ℕ} {digits : List ℕ} {carry : ℕ}
    (hcarry : carry ≤ 1)
    (hdigits : ∀ digit ∈ digits, digit < oddBase half) :
    (oddDoubleDigitsAux half digits carry).sum +
        (oddBase half - 1) * oddDoubleCarryCountAux half digits carry =
      2 * digits.sum + carry := by
  induction digits generalizing carry with
  | nil => simp [oddDoubleDigitsAux, oddDoubleCarryCountAux]
  | cons digit digits ih =>
      have hdigit := hdigits digit List.mem_cons_self
      have htail : ∀ d ∈ digits, d < oddBase half :=
        fun d hd => hdigits d (List.mem_cons_of_mem digit hd)
      have hnext := oddDoubleCarryStep_le_one hcarry hdigit
      have hlocal := oddDoubleCarryStep_local half carry digit
      have hrec := ih hnext htail
      apply Nat.add_right_cancel
        (m := oddDoubleCarryStep half carry digit)
      simp only [oddDoubleDigitsAux, oddDoubleCarryCountAux, List.sum_cons]
      calc
        ((2 * digit + carry) % oddBase half +
              (oddDoubleDigitsAux half digits
                (oddDoubleCarryStep half carry digit)).sum +
            (oddBase half - 1) *
              (oddDoubleCarryStep half carry digit +
                oddDoubleCarryCountAux half digits
                  (oddDoubleCarryStep half carry digit))) +
            oddDoubleCarryStep half carry digit =
            ((2 * digit + carry) % oddBase half +
                oddBase half * oddDoubleCarryStep half carry digit) +
              ((oddDoubleDigitsAux half digits
                  (oddDoubleCarryStep half carry digit)).sum +
                (oddBase half - 1) *
                  oddDoubleCarryCountAux half digits
                    (oddDoubleCarryStep half carry digit)) := by
              simp [oddBase]
              ring
        _ = (2 * digit + carry) +
              (2 * digits.sum +
                oddDoubleCarryStep half carry digit) := by
              rw [hlocal, hrec]
        _ = (2 * (digit :: digits).sum + carry) +
              oddDoubleCarryStep half carry digit := by
              simp
              ring

/-- In an odd prime base, Kummer's central-binomial valuation is exactly the
number of carries produced by doubling any valid padded digit word. -/
theorem padicValNat_oddPrime_centralBinom_ofDigits_eq_carryCount
    (half : ℕ) (hhalf : 0 < half) [Fact (oddBase half).Prime]
    (digits : List ℕ)
    (hdigits : ∀ digit ∈ digits, digit < oddBase half) :
    padicValNat (oddBase half)
        (Nat.centralBinom (Nat.ofDigits (oddBase half) digits)) =
      oddDoubleCarryCountAux half digits 0 := by
  let output := oddDoubleDigitsAux half digits 0
  have hvalid : ∀ digit ∈ output, digit < oddBase half := by
    simpa [output] using
      (oddDoubleDigitsAux_lt_base hhalf (digits := digits) (carry := 0)
        (by decide) hdigits)
  have hvalue :
      Nat.ofDigits (oddBase half) output =
        2 * Nat.ofDigits (oddBase half) digits := by
    simpa [output] using
      (oddDoubleDigitsAux_ofDigits
        (half := half) (digits := digits) (carry := 0) (by decide) hdigits)
  have hinputSum :
      (Nat.digits (oddBase half)
          (Nat.ofDigits (oddBase half) digits)).sum = digits.sum :=
    Nat.sum_digits_ofDigits_eq_sum (oddBase_one_lt hhalf) ⟨rfl, hdigits⟩
  have houtputSum :
      (Nat.digits (oddBase half)
          (2 * Nat.ofDigits (oddBase half) digits)).sum = output.sum := by
    rw [← hvalue]
    exact Nat.sum_digits_ofDigits_eq_sum (oddBase_one_lt hhalf)
      ⟨rfl, hvalid⟩
  have hkummer :=
    sub_one_mul_padicValNat_centralBinom (oddBase half)
      (Nat.ofDigits (oddBase half) digits)
  rw [hinputSum, houtputSum] at hkummer
  have hcarry :
      output.sum +
          (oddBase half - 1) * oddDoubleCarryCountAux half digits 0 =
        2 * digits.sum := by
    simpa [output] using
      (oddDoubleDigitsAux_sum_add_carries
        (half := half) (digits := digits) (carry := 0) (by decide) hdigits)
  have hmul :
      (oddBase half - 1) *
          padicValNat (oddBase half)
            (Nat.centralBinom (Nat.ofDigits (oddBase half) digits)) =
        (oddBase half - 1) * oddDoubleCarryCountAux half digits 0 := by
    omega
  have hfactor : 0 < oddBase half - 1 := by
    simp [oddBase]
    omega
  exact Nat.mul_left_cancel hfactor hmul

end OddPrimeValuationDistribution
