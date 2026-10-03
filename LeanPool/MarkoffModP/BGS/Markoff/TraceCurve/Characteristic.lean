/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.Geometry
public import Mathlib.Algebra.CharP.Lemmas

/-!
# The characteristic restriction in the split trace-cover lemma

The published absolute-irreducibility statement for the split trace cover does not require the
covering exponents to be prime to the characteristic.  This omission is substantive: when both
exponents equal the positive characteristic, the cleared trace polynomial is a Frobenius power.

This file records the obstruction directly on the polynomial used by the endgame.  It is kept
separate from the positive Kummer descent: the theorem below is a counterexample to an omitted
hypothesis, not another assumption on which downstream formalization may rely.
-/

@[expose] public section

namespace BGS.Markoff

open Polynomial

variable {K : Type*} [Field K]

/-- Simultaneously multiplying both covering exponents by the characteristic turns the cover
with Frobenius-powered coefficients into a Frobenius power. -/
theorem splitTraceCoverPolynomial_frobenius_pullback
    (alpha beta : K) (d e p : ℕ) [Fact p.Prime] [CharP K p] :
    splitTraceCoverPolynomial (alpha ^ p) (beta ^ p) (p * d) (p * e) =
      (splitTraceCoverPolynomial alpha beta d e) ^ p := by
  simp only [splitTraceCoverPolynomial]
  rw [sub_pow_char, sub_pow_char, add_pow_char, mul_pow, mul_pow, mul_pow, mul_pow]
  simp only [pow_mul]
  have hpd : p * d = d * p := Nat.mul_comm p d
  have hpe : p * e = e * p := Nat.mul_comm p e
  have htwoPD : 2 * p * d = 2 * d * p := by ac_rfl
  have htwoPE : 2 * p * e = 2 * e * p := by ac_rfl
  simp only [← pow_mul, hpd, hpe, htwoPD, htwoPE]
  simp only [MvPolynomial.C_pow]

/-- In characteristic `p`, the trace-cover polynomial with both exponents `p` is the `p`-th
power of its degree-one counterpart.  The parameters `(1, 0)` satisfy the published conditions
"not both zero" and `alpha * beta ≠ 1`. -/
theorem splitTraceCoverPolynomial_frobenius_factorization
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    splitTraceCoverPolynomial (1 : K) 0 p p =
      (splitTraceCoverPolynomial (1 : K) 0 1 1) ^ p := by
  simpa [zero_pow (Fact.out : p.Prime).ne_zero] using
    splitTraceCoverPolynomial_frobenius_pullback (K := K) 1 0 1 1 p

/-- Therefore the published irreducibility conclusion is false without a restriction excluding
covering exponents divisible by the characteristic.  This is reducibility over the ground field,
so in particular it also rules out absolute irreducibility. -/
theorem splitTraceCoverPolynomial_not_irreducible_when_exponents_equal_char
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    ¬ Irreducible (splitTraceCoverPolynomial (1 : K) 0 p p) := by
  rw [splitTraceCoverPolynomial_frobenius_factorization]
  exact not_irreducible_pow (Fact.out : p.Prime).ne_one

/-- A direct formal counterexample to Lemma 11 as printed: its two parameter hypotheses hold,
but the conclusion fails when both covering exponents equal the characteristic. -/
theorem publishedTraceCoverIrreducibility_requiresCharacteristicHypothesis
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (((1 : K) ≠ 0 ∨ (0 : K) ≠ 0) ∧ (1 : K) * 0 ≠ 1) ∧
      ¬ Irreducible (splitTraceCoverPolynomial (1 : K) 0 p p) := by
  exact ⟨by simp, splitTraceCoverPolynomial_not_irreducible_when_exponents_equal_char p⟩

end BGS.Markoff
