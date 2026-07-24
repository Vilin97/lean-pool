/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.OddPrimeValuationDistribution.CarryArithmetic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Ring

/-!
# Carry polynomials in an arbitrary odd base

The coefficient of `X ^ r` in the length-`k` polynomial counts odd-base digit
words whose doubling creates exactly `r` carries.  Splitting the digit set at
the carry threshold gives a two-state transfer matrix and its scalar
second-order recurrence.
-/

namespace OddPrimeValuationDistribution

open Polynomial
open scoped BigOperators

/-- Convert an odd-base word to natural digits. -/
def oddCarryWordDigits {half length : ℕ}
    (word : List.Vector (Fin (oddBase half)) length) : List ℕ :=
  word.toList.map Fin.val

/-- Odd-base carry-count enumerator from an arbitrary incoming carry. -/
noncomputable def oddCarryPolynomialFrom
    (half carry length : ℕ) : Polynomial ℕ :=
  ∑ word : List.Vector (Fin (oddBase half)) length,
    X ^ oddDoubleCarryCountAux half (oddCarryWordDigits word) carry

/-- Odd-base carry-count enumerator from incoming carry zero. -/
noncomputable def oddCarryPolynomial (half length : ℕ) : Polynomial ℕ :=
  oddCarryPolynomialFrom half 0 length

/-- Peeling the least significant digit from an odd-base word. -/
def oddCarryWordsSuccEquiv (half length : ℕ) :
    List.Vector (Fin (oddBase half)) (length + 1) ≃
      Σ _digit : Fin (oddBase half),
        List.Vector (Fin (oddBase half)) length where
  toFun word := ⟨word.head, word.tail⟩
  invFun pair := List.Vector.cons pair.1 pair.2
  left_inv word := List.Vector.cons_head_tail word
  right_inv pair := by
    rcases pair with ⟨digit, word⟩
    rfl

lemma oddCarryPolynomialFrom_zero (half carry : ℕ) :
    oddCarryPolynomialFrom half carry 0 = 1 := by
  simp [oddCarryPolynomialFrom, oddCarryWordDigits,
    oddDoubleCarryCountAux]

lemma oddCarryPolynomialFrom_succ (half carry length : ℕ) :
    oddCarryPolynomialFrom half carry (length + 1) =
      ∑ digit : Fin (oddBase half),
        X ^ oddDoubleCarryStep half carry digit.val *
          oddCarryPolynomialFrom half
            (oddDoubleCarryStep half carry digit.val) length := by
  unfold oddCarryPolynomialFrom
  calc
    (∑ word : List.Vector (Fin (oddBase half)) (length + 1),
        X ^ oddDoubleCarryCountAux half
          (oddCarryWordDigits word) carry) =
        ∑ pair : Σ _digit : Fin (oddBase half),
            List.Vector (Fin (oddBase half)) length,
          X ^ oddDoubleCarryCountAux half
            (oddCarryWordDigits
              (List.Vector.cons pair.1 pair.2)) carry := by
          exact Fintype.sum_equiv (oddCarryWordsSuccEquiv half length) _ _
            (fun word => by
              simpa [oddCarryWordsSuccEquiv] using
                congrArg
                  (fun value => X ^ oddDoubleCarryCountAux half
                    (oddCarryWordDigits value) carry)
                  (List.Vector.cons_head_tail word).symm)
    _ = ∑ digit : Fin (oddBase half),
          X ^ oddDoubleCarryStep half carry digit.val *
            ∑ word : List.Vector (Fin (oddBase half)) length,
              X ^ oddDoubleCarryCountAux half
                (oddCarryWordDigits word)
                (oddDoubleCarryStep half carry digit.val) := by
          rw [Fintype.sum_sigma]
          simp [oddCarryWordDigits, oddDoubleCarryCountAux, pow_add,
            Finset.mul_sum]

/-- Split digits into the `half + 1` no-carry choices and `half` carry choices
when the incoming carry is zero. -/
def oddZeroCarryDigitSplitEquiv (half : ℕ) :
    Fin (oddBase half) ≃ Fin (half + 1) ⊕ Fin half :=
  (finCongr (by simp [oddBase]; omega)).trans finSumFinEquiv.symm

/-- Split digits into the `half` no-carry choices and `half + 1` carry choices
when the incoming carry is one. -/
def oddOneCarryDigitSplitEquiv (half : ℕ) :
    Fin (oddBase half) ≃ Fin half ⊕ Fin (half + 1) :=
  (finCongr (by simp [oddBase]; omega)).trans finSumFinEquiv.symm

@[simp]
lemma oddZeroCarryDigitSplitEquiv_symm_inl_val
    (half : ℕ) (digit : Fin (half + 1)) :
    ((oddZeroCarryDigitSplitEquiv half).symm (Sum.inl digit)).val =
      digit.val := by
  simp [oddZeroCarryDigitSplitEquiv]

@[simp]
lemma oddZeroCarryDigitSplitEquiv_symm_inr_val
    (half : ℕ) (digit : Fin half) :
    ((oddZeroCarryDigitSplitEquiv half).symm (Sum.inr digit)).val =
      half + 1 + digit.val := by
  simp [oddZeroCarryDigitSplitEquiv]

@[simp]
lemma oddOneCarryDigitSplitEquiv_symm_inl_val
    (half : ℕ) (digit : Fin half) :
    ((oddOneCarryDigitSplitEquiv half).symm (Sum.inl digit)).val =
      digit.val := by
  simp [oddOneCarryDigitSplitEquiv]

@[simp]
lemma oddOneCarryDigitSplitEquiv_symm_inr_val
    (half : ℕ) (digit : Fin (half + 1)) :
    ((oddOneCarryDigitSplitEquiv half).symm (Sum.inr digit)).val =
      half + digit.val := by
  simp [oddOneCarryDigitSplitEquiv]

lemma oddDoubleCarryStep_zero_split_inl
    (half : ℕ) (digit : Fin (half + 1)) :
    oddDoubleCarryStep half 0
        ((oddZeroCarryDigitSplitEquiv half).symm (Sum.inl digit)).val = 0 := by
  rw [oddZeroCarryDigitSplitEquiv_symm_inl_val]
  exact oddDoubleCarryStep_zero_of_lt_succ digit.isLt

lemma oddDoubleCarryStep_zero_split_inr
    (half : ℕ) (digit : Fin half) :
    oddDoubleCarryStep half 0
        ((oddZeroCarryDigitSplitEquiv half).symm (Sum.inr digit)).val = 1 := by
  rw [oddZeroCarryDigitSplitEquiv_symm_inr_val]
  apply oddDoubleCarryStep_one_of_succ_le
  · omega
  · simp [oddBase]
    omega

lemma oddDoubleCarryStep_one_split_inl
    (half : ℕ) (digit : Fin half) :
    oddDoubleCarryStep half 1
        ((oddOneCarryDigitSplitEquiv half).symm (Sum.inl digit)).val = 0 := by
  rw [oddOneCarryDigitSplitEquiv_symm_inl_val]
  exact oddDoubleCarryStep_zero_of_lt digit.isLt

lemma oddDoubleCarryStep_one_split_inr
    (half : ℕ) (digit : Fin (half + 1)) :
    oddDoubleCarryStep half 1
        ((oddOneCarryDigitSplitEquiv half).symm (Sum.inr digit)).val = 1 := by
  rw [oddOneCarryDigitSplitEquiv_symm_inr_val]
  apply oddDoubleCarryStep_one_of_le
  · omega
  · simp [oddBase]
    omega

lemma oddCarryPolynomialFrom_zeroCarry_succ (half length : ℕ) :
    oddCarryPolynomialFrom half 0 (length + 1) =
      ((half + 1 : ℕ) : Polynomial ℕ) *
          oddCarryPolynomialFrom half 0 length +
        (half : Polynomial ℕ) * X *
          oddCarryPolynomialFrom half 1 length := by
  rw [oddCarryPolynomialFrom_succ]
  calc
    (∑ digit : Fin (oddBase half),
        X ^ oddDoubleCarryStep half 0 digit.val *
          oddCarryPolynomialFrom half
            (oddDoubleCarryStep half 0 digit.val) length) =
        ∑ choice : Fin (half + 1) ⊕ Fin half,
          X ^ oddDoubleCarryStep half 0
              ((oddZeroCarryDigitSplitEquiv half).symm choice).val *
            oddCarryPolynomialFrom half
              (oddDoubleCarryStep half 0
                ((oddZeroCarryDigitSplitEquiv half).symm choice).val)
              length := by
          exact Fintype.sum_equiv (oddZeroCarryDigitSplitEquiv half) _ _
            (fun digit => by simp)
    _ = ((half + 1 : ℕ) : Polynomial ℕ) *
            oddCarryPolynomialFrom half 0 length +
          (half : Polynomial ℕ) * X *
            oddCarryPolynomialFrom half 1 length := by
          rw [Fintype.sum_sum_type]
          simp_rw [oddDoubleCarryStep_zero_split_inl]
          simp_rw [oddDoubleCarryStep_zero_split_inr]
          simp
          ring

lemma oddCarryPolynomialFrom_oneCarry_succ (half length : ℕ) :
    oddCarryPolynomialFrom half 1 (length + 1) =
      (half : Polynomial ℕ) * oddCarryPolynomialFrom half 0 length +
        ((half + 1 : ℕ) : Polynomial ℕ) * X *
          oddCarryPolynomialFrom half 1 length := by
  rw [oddCarryPolynomialFrom_succ]
  calc
    (∑ digit : Fin (oddBase half),
        X ^ oddDoubleCarryStep half 1 digit.val *
          oddCarryPolynomialFrom half
            (oddDoubleCarryStep half 1 digit.val) length) =
        ∑ choice : Fin half ⊕ Fin (half + 1),
          X ^ oddDoubleCarryStep half 1
              ((oddOneCarryDigitSplitEquiv half).symm choice).val *
            oddCarryPolynomialFrom half
              (oddDoubleCarryStep half 1
                ((oddOneCarryDigitSplitEquiv half).symm choice).val)
              length := by
          exact Fintype.sum_equiv (oddOneCarryDigitSplitEquiv half) _ _
            (fun digit => by simp)
    _ = (half : Polynomial ℕ) * oddCarryPolynomialFrom half 0 length +
          ((half + 1 : ℕ) : Polynomial ℕ) * X *
            oddCarryPolynomialFrom half 1 length := by
          rw [Fintype.sum_sum_type]
          simp_rw [oddDoubleCarryStep_one_split_inl]
          simp_rw [oddDoubleCarryStep_one_split_inr]
          simp
          ring

@[simp]
theorem oddCarryPolynomial_zero (half : ℕ) :
    oddCarryPolynomial half 0 = 1 := by
  simp [oddCarryPolynomial, oddCarryPolynomialFrom_zero]

@[simp]
theorem oddCarryPolynomial_one (half : ℕ) :
    oddCarryPolynomial half 1 =
      ((half + 1 : ℕ) : Polynomial ℕ) + (half : Polynomial ℕ) * X := by
  change oddCarryPolynomialFrom half 0 (0 + 1) = _
  rw [oddCarryPolynomialFrom_zeroCarry_succ]
  simp [oddCarryPolynomialFrom_zero]

/-- Headline recurrence for the full carry distribution in odd base
`2 * half + 1`. -/
theorem oddCarryPolynomial_recurrence (half length : ℕ) :
    oddCarryPolynomial half (length + 2) +
        (oddBase half : Polynomial ℕ) * X *
          oddCarryPolynomial half length =
      ((half + 1 : ℕ) : Polynomial ℕ) * (1 + X) *
        oddCarryPolynomial half (length + 1) := by
  simp only [oddCarryPolynomial]
  rw [show length + 2 = (length + 1) + 1 by omega,
    oddCarryPolynomialFrom_zeroCarry_succ]
  rw [oddCarryPolynomialFrom_oneCarry_succ]
  rw [oddCarryPolynomialFrom_zeroCarry_succ]
  simp [oddBase]
  ring

end OddPrimeValuationDistribution
