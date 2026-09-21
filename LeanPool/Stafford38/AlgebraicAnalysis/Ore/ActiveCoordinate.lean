/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Ore.Associativity

/-!
# Active-coordinate decomposition in a derivation Ore extension

This file isolates a reusable algebraic interface for one distinguished
coefficient coordinate.  The coefficient ring may be noncommutative; the
coordinate is required to be central in that ring, while the active derivation
annihilates ground scalars and sends the coordinate to `1`.

The results use only the checked normal-form construction.  They do not
postulate a PBW basis, a presented Weyl algebra, or an operator realization.
-/

namespace AlgebraicAnalysis.OreActiveCoordinate

open Polynomial
open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity

noncomputable section


/-! ## The source-relative active-coordinate data -/

/-- Hypotheses for one active differential-Ore coordinate.

The coefficient ring can be noncommutative. `coordinate_central` is the exact
hypothesis needed for coefficients of an active-variable expansion to commute
with polynomials in the coordinate. The two derivation hypotheses record that
the active derivation fixes ground scalars and differentiates the coordinate.
-/
structure ActiveCoordinateData (k C : Type*) [CommRing k] [Ring C]
    [Algebra k C] where
  /-- The coefficient derivation defining the Ore relation. -/
  derivation : OreDivisionDerivation C
  /-- The distinguished central coefficient coordinate. -/
  coordinate : C
  coordinate_central : ∀ c : C, Commute coordinate c
  derivation_smul : ∀ a : k, derivation (algebraMap k C a) = 0
  derivation_coordinate : derivation coordinate = algebraMap k C 1

namespace ActiveCoordinateData

variable {k C : Type*} [CommRing k] [Ring C] [Algebra k C]
variable (A : ActiveCoordinateData k C)

/-- The active one-variable derivation Ore ring. -/
abbrev Ore := NormalOre A.derivation

/-- The coefficient embedding into the active Ore ring. -/
def coefficient (c : C) : A.Ore := normalCoefficient A.derivation c

/-- The active Ore variable. -/
def activeVariable : A.Ore := normalVariable A.derivation

/-- The central-coordinate polynomial algebra inside the active Ore ring. -/
def coordinatePolynomial (p : Polynomial k) : A.Ore :=
  p.eval₂ ((normalCoefficient A.derivation).comp (algebraMap k C))
    (coefficient A A.coordinate)

/-- The defining differential-Ore relation at the distinguished coordinate. -/
theorem variable_mul_coordinate :
    activeVariable A * coefficient A A.coordinate =
      coefficient A A.coordinate * activeVariable A +
        coefficient A (algebraMap k C 1) := by
  unfold activeVariable coefficient
  rw [normalVariable_mul_coefficient]
  rw [A.derivation_coordinate]

/-- Ground scalars commute with the active Ore variable. -/
theorem variable_mul_smul (a : k) :
    activeVariable A * coefficient A (algebraMap k C a) =
      coefficient A (algebraMap k C a) * activeVariable A := by
  unfold activeVariable coefficient
  rw [normalVariable_mul_coefficient, A.derivation_smul, map_zero]
  simp

/-- Every coefficient commutes with the image of a ground scalar. -/
theorem coefficient_commute_smul (c : C) (a : k) :
    Commute (coefficient A c) (coefficient A (algebraMap k C a)) := by
  unfold coefficient
  rw [commute_iff_eq]
  rw [← (normalCoefficient A.derivation).map_mul,
    ← (normalCoefficient A.derivation).map_mul]
  rw [Algebra.commutes]

/-- Every coefficient commutes with the distinguished coordinate. -/
theorem coefficient_commute_coordinate (c : C) :
    Commute (coefficient A c) (coefficient A A.coordinate) := by
  unfold coefficient
  rw [commute_iff_eq]
  rw [← (normalCoefficient A.derivation).map_mul,
    ← (normalCoefficient A.derivation).map_mul]
  rw [A.coordinate_central c |>.symm.eq]

/-- Every coefficient commutes with every polynomial in the central coordinate. -/
theorem coefficient_commute_coordinatePolynomial (c : C)
    (p : Polynomial k) :
    Commute (coefficient A c) (coordinatePolynomial A p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [coordinatePolynomial, eval₂_add]
      exact hp.add_right hq
  | monomial n a =>
      rw [coordinatePolynomial, eval₂_monomial]
      exact (coefficient_commute_smul A c a).mul_right
        ((coefficient_commute_coordinate A c).pow_right n)

/-- The coefficient-left normal form is an explicit finite active-variable
expansion. -/
theorem normalForm_eq_support_sum (p : Polynomial C) :
    normalForm A.derivation p =
      ∑ j ∈ p.support,
        coefficient A (p.coeff j) * activeVariable A ^ j := by
  calc
    normalForm A.derivation p =
        normalForm A.derivation (∑ j ∈ p.support,
          Polynomial.monomial j (p.coeff j)) := by
      exact congrArg (normalForm A.derivation) p.as_sum_support
    _ = ∑ j ∈ p.support,
          normalForm A.derivation (Polynomial.monomial j (p.coeff j)) := by
      change normalFormAddHom A.derivation
          (∑ j ∈ p.support, Polynomial.monomial j (p.coeff j)) = _
      rw [map_sum]
      rfl
    _ = ∑ j ∈ p.support,
          coefficient A (p.coeff j) * activeVariable A ^ j := by
      simp only [normalForm_monomial]
      rfl

/-- Recombination using only coefficient/coordinate commutation; the active
Ore variable remains on the right throughout. -/
theorem recombine_coordinate_polynomial (p : Polynomial C)
    (b : A.Ore) (q : Polynomial k) :
    (∑ j ∈ p.support,
        (b * coefficient A (p.coeff j)) *
          (coordinatePolynomial A q * activeVariable A ^ j)) =
      b * coordinatePolynomial A q * normalForm A.derivation p := by
  calc
    (∑ j ∈ p.support,
        (b * coefficient A (p.coeff j)) *
          (coordinatePolynomial A q * activeVariable A ^ j)) =
        ∑ j ∈ p.support,
          b * coordinatePolynomial A q *
            (coefficient A (p.coeff j) * activeVariable A ^ j) := by
      apply Finset.sum_congr rfl
      intro j hj
      calc
        (b * coefficient A (p.coeff j)) *
            (coordinatePolynomial A q * activeVariable A ^ j) =
            b * (coefficient A (p.coeff j) *
              coordinatePolynomial A q) * activeVariable A ^ j := by
                simp only [mul_assoc]
        _ = b * (coordinatePolynomial A q * coefficient A (p.coeff j)) *
              activeVariable A ^ j := by
                rw [(coefficient_commute_coordinatePolynomial A
                  (p.coeff j) q).eq]
        _ = b * coordinatePolynomial A q *
              (coefficient A (p.coeff j) * activeVariable A ^ j) := by
                simp only [mul_assoc]
    _ = b * coordinatePolynomial A q *
          (∑ j ∈ p.support,
            coefficient A (p.coeff j) * activeVariable A ^ j) := by
      symm
      rw [Finset.mul_sum]
    _ = b * coordinatePolynomial A q * normalForm A.derivation p := by
      rw [normalForm_eq_support_sum]

/-- Normal-form surjectivity supplies a finite active-variable expansion and
the coefficient commutations needed to use it source-relatively. -/
theorem exists_active_expansion (d : A.Ore) :
    ∃ p : Polynomial C,
      d = ∑ j ∈ p.support,
        coefficient A (p.coeff j) * activeVariable A ^ j ∧
      ∀ n : ℕ, ∀ q : Polynomial k,
        Commute (coefficient A (p.coeff n))
          (coordinatePolynomial A q) := by
  obtain ⟨p, hp⟩ := normalForm_surjective A.derivation d
  refine ⟨p, ?_, ?_⟩
  · rw [← hp, normalForm_eq_support_sum]
  · intro n q
    exact coefficient_commute_coordinatePolynomial A (p.coeff n) q

end ActiveCoordinateData


end
end AlgebraicAnalysis.OreActiveCoordinate
