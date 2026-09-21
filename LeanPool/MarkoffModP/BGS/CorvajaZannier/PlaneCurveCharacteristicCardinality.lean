/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveSeparability
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Tactic

/-!
# Plane-curve degrees versus finite-field cardinality

This file converts the characteristic bound used in the
Corvaja--Zannier argument into the finite-field cardinality bounds required
by the local reciprocal-discriminant and canonical Euler estimates.
-/

namespace BGS.CorvajaZannier

/-- The prime characteristic of a finite field is at most its cardinality. -/
theorem prime_le_fintype_card_of_charP
    {K : Type*} [Field K] [Fintype K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    p ≤ Fintype.card K := by
  apply Nat.le_of_dvd Fintype.card_pos
  apply (prime_dvd_char_iff_dvd_card p).mp
  rw [ringChar.eq K p]

/-- If twelve times the product of the two coordinate degrees is smaller
than `p`, and both coordinate partial derivatives are nonzero, then each
coordinate degree is smaller than `p`. -/
theorem planeCurve_coordinateDegrees_lt_char_of_twelve_mul_degrees_lt_char
    {K : Type*} [Field K]
    {f : MvPolynomial (Fin 2) K} {p : ℕ}
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hbound : 12 * MvPolynomial.degreeOf 0 f *
      MvPolynomial.degreeOf 1 f < p) :
    MvPolynomial.degreeOf 0 f < p ∧
      MvPolynomial.degreeOf 1 f < p := by
  have hfirst : 0 < MvPolynomial.degreeOf 0 f :=
    degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst
  have hsecond : 0 < MvPolynomial.degreeOf 1 f :=
    degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond
  constructor <;> nlinarith

/-- Under the characteristic-size hypothesis of the Corvaja--Zannier
application, both coordinate degrees are strictly smaller than the cardinality
of the finite constant field. -/
theorem planeCurve_coordinateDegrees_lt_card_of_twelve_mul_degrees_lt_char
    {K : Type*} [Field K] [Fintype K]
    {f : MvPolynomial (Fin 2) K} {p : ℕ}
    [Fact p.Prime] [CharP K p]
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hbound : 12 * MvPolynomial.degreeOf 0 f *
      MvPolynomial.degreeOf 1 f < p) :
    MvPolynomial.degreeOf 0 f < Fintype.card K ∧
      MvPolynomial.degreeOf 1 f < Fintype.card K := by
  have hpCard : p ≤ Fintype.card K :=
    prime_le_fintype_card_of_charP (K := K) p
  exact And.imp (fun h => h.trans_le hpCard) (fun h => h.trans_le hpCard)
    (planeCurve_coordinateDegrees_lt_char_of_twelve_mul_degrees_lt_char
      hpartialFirst hpartialSecond hbound)

/-- First-coordinate specialization of
`planeCurve_coordinateDegrees_lt_card_of_twelve_mul_degrees_lt_char`. -/
theorem planeCurve_degreeOf_first_lt_card_of_twelve_mul_degrees_lt_char
    {K : Type*} [Field K] [Fintype K]
    {f : MvPolynomial (Fin 2) K} {p : ℕ}
    [Fact p.Prime] [CharP K p]
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hbound : 12 * MvPolynomial.degreeOf 0 f *
      MvPolynomial.degreeOf 1 f < p) :
    MvPolynomial.degreeOf 0 f < Fintype.card K :=
  (planeCurve_coordinateDegrees_lt_card_of_twelve_mul_degrees_lt_char
    hpartialFirst hpartialSecond hbound).1

/-- Second-coordinate specialization of
`planeCurve_coordinateDegrees_lt_card_of_twelve_mul_degrees_lt_char`. -/
theorem planeCurve_degreeOf_second_lt_card_of_twelve_mul_degrees_lt_char
    {K : Type*} [Field K] [Fintype K]
    {f : MvPolynomial (Fin 2) K} {p : ℕ}
    [Fact p.Prime] [CharP K p]
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hbound : 12 * MvPolynomial.degreeOf 0 f *
      MvPolynomial.degreeOf 1 f < p) :
    MvPolynomial.degreeOf 1 f < Fintype.card K :=
  (planeCurve_coordinateDegrees_lt_card_of_twelve_mul_degrees_lt_char
    hpartialFirst hpartialSecond hbound).2

end BGS.CorvajaZannier
