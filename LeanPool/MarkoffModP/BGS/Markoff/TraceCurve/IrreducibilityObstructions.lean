/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.Characteristic
public import Mathlib.FieldTheory.Perfect

/-!
# Exact obstructions to the published trace-cover irreducibility statement

The counterexample in `TraceCurveCharacteristic` uses a zero second weight.  That already
falsifies the published statement as written, but it does not test the normalized family used by
the current split endgame.  This file records the stronger obstruction: over a perfect field of
positive characteristic, every normalized coefficient has a Frobenius root, so simultaneously
multiplying both cover exponents by the characteristic makes the normalized cover a Frobenius
power.  This remains true when `sigma` is nonzero and different from one.
-/

@[expose] public section

namespace BGS.Markoff

open Polynomial

variable {K : Type*} [Field K]

section ZeroSecondWeight

/-- If the second trace weight is zero, denominator clearing introduces the coordinate factor
`y^e`.  Thus the polynomial displayed in the published proof is not the torus closure in this
case. -/
theorem splitTraceCoverPolynomial_zero_second_weight_factorization
    (alpha : K) (d e : ℕ) :
    splitTraceCoverPolynomial alpha 0 d e =
      MvPolynomial.X 1 ^ e *
        (MvPolynomial.C alpha * MvPolynomial.X 0 ^ d * MvPolynomial.X 1 ^ e -
          MvPolynomial.X 0 ^ (2 * d) - 1) := by
  simp only [splitTraceCoverPolynomial, MvPolynomial.C_0, zero_mul, add_zero]
  ring

lemma splitTraceCoverPolynomial_zero_second_weight_coordinateFactor_not_isUnit
    (e : ℕ) (he : 0 < e) :
    ¬ IsUnit (MvPolynomial.X (R := K) (1 : Fin 2) ^ e) := by
  intro hunit
  obtain ⟨r, _hr, heq⟩ :=
    (MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hunit)
  have hzero := congrArg
    (MvPolynomial.eval₂ (σ := Fin 2) (RingHom.id K) (![0, 0] : Fin 2 → K)) heq
  have hone := congrArg
    (MvPolynomial.eval₂ (σ := Fin 2) (RingHom.id K) (![0, 1] : Fin 2 → K)) heq
  simp [he.ne'] at hzero hone
  exact zero_ne_one (hzero.trans hone.symm)

lemma splitTraceCoverPolynomial_zero_second_weight_remainingFactor_not_isUnit
    (alpha : K) (halpha : alpha ≠ 0) (d e : ℕ) (he : 0 < e) :
    ¬ IsUnit
      (MvPolynomial.C alpha * MvPolynomial.X 0 ^ d * MvPolynomial.X 1 ^ e -
        MvPolynomial.X (0 : Fin 2) ^ (2 * d) - 1 : MvPolynomial (Fin 2) K) := by
  intro hunit
  obtain ⟨r, _hr, heq⟩ :=
    (MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hunit)
  have hzero := congrArg
    (MvPolynomial.eval₂ (σ := Fin 2) (RingHom.id K) (![1, 0] : Fin 2 → K)) heq
  have hone := congrArg
    (MvPolynomial.eval₂ (σ := Fin 2) (RingHom.id K) (![1, 1] : Fin 2 → K)) heq
  simp [he.ne'] at hzero hone
  apply halpha
  linear_combination hone - hzero

/-- The printed hypotheses "the weights are not both zero" and `alpha * beta ≠ 1` do not imply
irreducibility of the cleared polynomial: whenever `beta = 0`, `alpha ≠ 0`, and `e > 0`, both
factors above are nonunits.  This obstruction already occurs in characteristic zero. -/
theorem splitTraceCoverPolynomial_zero_second_weight_not_irreducible
    (alpha : K) (halpha : alpha ≠ 0) (d e : ℕ) (he : 0 < e) :
    ¬ Irreducible (splitTraceCoverPolynomial alpha 0 d e) := by
  intro hirreducible
  have hfactor := splitTraceCoverPolynomial_zero_second_weight_factorization alpha d e
  rcases hirreducible.isUnit_or_isUnit hfactor with hcoordinate | hremaining
  · exact splitTraceCoverPolynomial_zero_second_weight_coordinateFactor_not_isUnit e he hcoordinate
  · exact splitTraceCoverPolynomial_zero_second_weight_remainingFactor_not_isUnit
      alpha halpha d e he hremaining

/-- A direct counterexample to the published lemma in its own logical form, independent of any
positive-characteristic issue. -/
theorem publishedTraceCoverIrreducibility_requires_nonzero_secondWeight
    (alpha : K) (halpha : alpha ≠ 0) (d e : ℕ) (he : 0 < e) :
    ((alpha ≠ 0 ∨ (0 : K) ≠ 0) ∧ alpha * 0 ≠ 1) ∧
      ¬ Irreducible (splitTraceCoverPolynomial alpha 0 d e) := by
  exact ⟨⟨Or.inl halpha, by simp⟩,
    splitTraceCoverPolynomial_zero_second_weight_not_irreducible alpha halpha d e he⟩

end ZeroSecondWeight

/-- In a perfect field of characteristic `p`, the normalized cover with exponents `(p*d,p*e)`
is a `p`-th power after choosing a Frobenius root of `sigma`. -/
theorem exists_splitTraceCoverPolynomial_normalized_frobenius_factorization
    [PerfectField K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (sigma : K) (d e : ℕ) :
    ∃ tau : K,
      tau ^ p = sigma ∧
        splitTraceCoverPolynomial (1 : K) sigma (p * d) (p * e) =
          (splitTraceCoverPolynomial (1 : K) tau d e) ^ p := by
  obtain ⟨tau, htau⟩ := surjective_frobenius K p sigma
  have htauPow : tau ^ p = sigma := by
    exact htau
  refine ⟨tau, ?_, ?_⟩
  · exact htauPow
  · rw [← htauPow]
    simpa using
      (splitTraceCoverPolynomial_frobenius_pullback
        (K := K) (1 : K) tau d e p)

/-- Any normalized cover for which the characteristic divides both exponents is a nontrivial
power over a perfect field, regardless of the residual exponents. -/
theorem splitTraceCoverPolynomial_normalized_not_irreducible_when_char_mul_exponents
    [PerfectField K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (sigma : K) (d e : ℕ) :
    ¬ Irreducible
      (splitTraceCoverPolynomial (1 : K) sigma (p * d) (p * e)) := by
  obtain ⟨tau, _htau, hfactor⟩ :=
    exists_splitTraceCoverPolynomial_normalized_frobenius_factorization
      (K := K) p sigma d e
  rw [hfactor]
  exact not_irreducible_pow (Fact.out : p.Prime).ne_one

/-- Hence the normalized cover is not irreducible whenever the characteristic divides both
covering exponents.  The hypotheses `sigma ≠ 0,1` do not repair this obstruction. -/
theorem splitTraceCoverPolynomial_normalized_not_irreducible_when_exponents_equal_char
    [PerfectField K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (sigma : K) :
    ¬ Irreducible (splitTraceCoverPolynomial (1 : K) sigma p p) := by
  simpa using
    (splitTraceCoverPolynomial_normalized_not_irreducible_when_char_mul_exponents
      (K := K) p sigma 1 1)

/-- Direct logical form of the repaired counterexample: even after imposing the current
normalized nondegeneracy assumptions, the published conclusion fails if the characteristic
divides both exponents. -/
theorem normalizedTraceCoverIrreducibility_requires_commonCharacteristicExclusion
    [PerfectField K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (sigma : K) (hsigma : sigma ≠ 0) (hnondegenerate : sigma ≠ 1) :
    (sigma ≠ 0 ∧ sigma ≠ 1) ∧
      ¬ Irreducible (splitTraceCoverPolynomial (1 : K) sigma p p) := by
  exact ⟨⟨hsigma, hnondegenerate⟩,
    splitTraceCoverPolynomial_normalized_not_irreducible_when_exponents_equal_char p sigma⟩

end BGS.Markoff
