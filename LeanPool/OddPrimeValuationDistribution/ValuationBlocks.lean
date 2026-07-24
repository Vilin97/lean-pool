/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.OddPrimeValuationDistribution.CarryPolynomial
import Mathlib.Data.Fintype.EquivFin

/-!
# Exact central-binomial valuation distributions for odd primes

For the odd prime `p = 2 * half + 1`, this module identifies fixed-length
base-`p` words with the integers below `p ^ length`.  Kummer's theorem turns
the word carry count into the exact value of `ν_p (centralBinom n)`, so the
transfer recurrence becomes an arithmetic distribution theorem.
-/

namespace OddPrimeValuationDistribution

open Nat Polynomial
open scoped BigOperators

/-- Natural value of a fixed-length word in the odd base `2 * half + 1`. -/
def oddCarryWordValue {half length : ℕ}
    (word : List.Vector (Fin (oddBase half)) length) : ℕ :=
  Nat.ofDigits (oddBase half) (oddCarryWordDigits word)

lemma oddCarryWordValue_lt {half length : ℕ} (hhalf : 0 < half)
    (word : List.Vector (Fin (oddBase half)) length) :
    oddCarryWordValue word < oddBase half ^ length := by
  simpa [oddCarryWordValue, oddCarryWordDigits] using
    (Nat.ofDigits_lt_base_pow_length (b := oddBase half)
      (oddBase_one_lt hhalf)
      (by simp [oddCarryWordDigits] :
        ∀ digit ∈ oddCarryWordDigits word, digit < oddBase half))

/-- The word value packaged in the corresponding complete finite block. -/
def oddCarryWordValueFin {half length : ℕ} (hhalf : 0 < half)
    (word : List.Vector (Fin (oddBase half)) length) :
    Fin (oddBase half ^ length) :=
  ⟨oddCarryWordValue word, oddCarryWordValue_lt hhalf word⟩

lemma oddCarryWordValueFin_injective
    (half : ℕ) (hhalf : 0 < half) (length : ℕ) :
    Function.Injective
      (oddCarryWordValueFin hhalf :
        List.Vector (Fin (oddBase half)) length →
          Fin (oddBase half ^ length)) := by
  intro word₁ word₂ hvalue
  apply List.Vector.toList_injective
  apply (List.map_injective_iff.mpr Fin.val_injective)
  apply Nat.ofDigits_inj_of_len_eq
    (b := oddBase half) (oddBase_one_lt hhalf)
  · simp
  · simp
  · simp
  · exact congrArg Fin.val hvalue

/-- Positional notation is a bijection from fixed-length odd-base words to
the corresponding complete block of natural numbers. -/
noncomputable def oddCarryWordValueEquiv
    (half : ℕ) (hhalf : 0 < half) (length : ℕ) :
    List.Vector (Fin (oddBase half)) length ≃
      Fin (oddBase half ^ length) :=
  Equiv.ofBijective (oddCarryWordValueFin hhalf) <|
    (Fintype.bijective_iff_injective_and_card _).2
      ⟨oddCarryWordValueFin_injective half hhalf length, by simp⟩

lemma padicValNat_oddPrime_centralBinom_word_eq_carryCount
    (half : ℕ) (hhalf : 0 < half) [Fact (oddBase half).Prime]
    {length : ℕ} (word : List.Vector (Fin (oddBase half)) length) :
    padicValNat (oddBase half)
        (Nat.centralBinom (oddCarryWordValue word)) =
      oddDoubleCarryCountAux half (oddCarryWordDigits word) 0 := by
  exact padicValNat_oddPrime_centralBinom_ofDigits_eq_carryCount
    half hhalf _ (by simp [oddCarryWordDigits])

/-- Polynomial distribution of exact odd-prime valuations on the complete
block `0 ≤ n < p ^ length`. -/
noncomputable def oddPrimeValuationPolynomial
    (half length : ℕ) : Polynomial ℕ :=
  ∑ n : Fin (oddBase half ^ length),
    X ^ padicValNat (oddBase half) (Nat.centralBinom n.val)

/-- The odd-prime valuation distribution is exactly the doubling-carry
distribution. -/
theorem oddPrimeValuationPolynomial_eq_carryPolynomial
    (half : ℕ) (hhalf : 0 < half) [Fact (oddBase half).Prime]
    (length : ℕ) :
    oddPrimeValuationPolynomial half length =
      oddCarryPolynomial half length := by
  unfold oddPrimeValuationPolynomial oddCarryPolynomial
  symm
  exact Fintype.sum_equiv (oddCarryWordValueEquiv half hhalf length) _ _
    (fun word => by
      change
        X ^ oddDoubleCarryCountAux half (oddCarryWordDigits word) 0 =
          X ^ padicValNat (oddBase half)
            (Nat.centralBinom (oddCarryWordValue word))
      rw [padicValNat_oddPrime_centralBinom_word_eq_carryCount half hhalf])

/-- Integers in a complete odd-prime block with a prescribed exact
central-binomial valuation. -/
abbrev OddPrimeBlockWithValuation (half length value : ℕ) :=
  {n : Fin (oddBase half ^ length) //
    padicValNat (oddBase half) (Nat.centralBinom n.val) = value}

/-- Literal coefficient interpretation of the odd-prime valuation
polynomial. -/
theorem coeff_oddPrimeValuationPolynomial
    (half length value : ℕ) :
    (oddPrimeValuationPolynomial half length).coeff value =
      Fintype.card (OddPrimeBlockWithValuation half length value) := by
  classical
  simp only [oddPrimeValuationPolynomial, finsetSum_coeff, coeff_X_pow,
    Finset.sum_boole, cast_id, OddPrimeBlockWithValuation]
  rw [Fintype.card_subtype]
  congr 1
  ext n
  simp [eq_comm]

/-- Headline exact-distribution recurrence for every odd prime
`p = 2 * half + 1`. -/
theorem oddPrimeValuationPolynomial_recurrence
    (half : ℕ) (hhalf : 0 < half) [Fact (oddBase half).Prime]
    (length : ℕ) :
    oddPrimeValuationPolynomial half (length + 2) +
        (oddBase half : Polynomial ℕ) * X *
          oddPrimeValuationPolynomial half length =
      ((half + 1 : ℕ) : Polynomial ℕ) * (1 + X) *
        oddPrimeValuationPolynomial half (length + 1) := by
  simp only [oddPrimeValuationPolynomial_eq_carryPolynomial half hhalf]
  exact oddCarryPolynomial_recurrence half length

end OddPrimeValuationDistribution
