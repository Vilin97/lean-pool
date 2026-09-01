/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Nullstellensatz.GenericFiber
import LeanPool.LocalComplexGeometry.Nullstellensatz.PolynomialFibers
import LeanPool.LocalComplexGeometry.Nullstellensatz.QuotientPolynomialSpecialization

/-!
# Concrete polynomial representatives

This file relates the generic fixed-degree representative API to the two
polynomial shapes occurring in Weierstrass division and records independence
of an inessential larger degree bound.
-/

open Filter
open scoped BigOperators Topology


namespace LocalComplexGeometry

noncomputable section

/-- A constant germ polynomial specializes to the constant polynomial of its
chosen representative, independently of the displayed bound. -/
theorem eventually_germPolynomialRepresentativeAt_C
    {n m : ℕ} (f : HolomorphicGerm n) :
    ∀ᶠ z in nhds (0 : ComplexEuclidean n),
      germPolynomialRepresentativeAt m (Polynomial.C f) z =
        Polynomial.C (HolomorphicGerm.representative f z) := by
  have hdegree : (Polynomial.C f).natDegree ≤ m := by
    rw [Polynomial.natDegree_C]
    exact Nat.zero_le m
  have hbound :=
    eventually_germPolynomialRepresentativeAt_eq_of_degreeBounds
      (k := m) (m := 0) (Polynomial.C f) hdegree (by simp)
  filter_upwards [hbound] with z hz
  rw [hz]
  simp [germPolynomialRepresentativeAt,
    germPolynomialCoefficientRepresentatives, fixedDegreePolynomialAt,
    fixedDegreePolynomial]

/-- The prepared germ polynomial has exact natural degree `d`. -/
@[simp]
theorem preparedGermPolynomial_natDegree {n d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0) :
    (preparedGermPolynomial a ha).natDegree = d := by
  unfold preparedGermPolynomial
  rw [Polynomial.natDegree_add_eq_left_of_degree_lt
    (by
      simpa [Polynomial.degree_X_pow] using
        (@Polynomial.degree_sum_fin_lt (HolomorphicGerm n) _ d
          (fun i ↦ preparedCoefficientGerm a ha i))),
    Polynomial.natDegree_X_pow]

/-- Chosen coefficient representatives of the prepared germ polynomial
specialize to the original prepared polynomial family after shrinking. -/
theorem eventually_germPolynomialRepresentativeAt_preparedGermPolynomial
    {n d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0) :
    ∀ᶠ z in nhds (0 : ComplexEuclidean n),
      germPolynomialRepresentativeAt d (preparedGermPolynomial a ha) z =
        preparedPolynomialAt a z := by
  let Pg := germPolynomialRepresentativeFunctions d
    (preparedGermPolynomial a ha)
  let Pf : Polynomial (ComplexEuclidean n → ℂ) :=
    Polynomial.X ^ d + ∑ i : Fin d,
      Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)
  have hPg : Pg.map (functionToGermRingHom n) =
      (preparedGermPolynomial a ha).map
        (holomorphicGermSubring n).subtype :=
    germPolynomialRepresentativeFunctions_map_germ _
      (preparedGermPolynomial_natDegree a ha).le
  have hPf : Pf.map (functionToGermRingHom n) =
      (preparedGermPolynomial a ha).map
        (holomorphicGermSubring n).subtype := by
    simp only [Pf, preparedGermPolynomial, preparedCoefficientGerm,
      Polynomial.map_add,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
      Polynomial.map_mul, Polynomial.map_C]
    rfl
  have hevent := eventually_polynomial_map_eval_eq_of_map_germ_eq Pg Pf
    (hPg.trans hPf.symm)
  filter_upwards [hevent] with z hz
  rw [← germPolynomialRepresentativeFunctions_map_eval]
  rw [hz]
  simp only [Pf, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    preparedPolynomialAt, Pi.evalRingHom_apply]

/-- A degree-`< d` remainder germ polynomial has natural degree at most `d`. -/
theorem remainderGermPolynomial_natDegree_le {n d : ℕ}
    (r : Fin d → HolomorphicGerm n) :
    (remainderGermPolynomial r).natDegree ≤ d := by
  unfold remainderGermPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (Polynomial.natDegree_C_mul_X_pow_le (r i) (i : ℕ)).trans
    (Nat.le_of_lt i.isLt)

/-- Chosen representatives of a remainder germ polynomial specialize to the
usual displayed coefficient sum. -/
theorem eventually_germPolynomialRepresentativeAt_remainderGermPolynomial
    {n d : ℕ} (r : Fin d → HolomorphicGerm n) :
    ∀ᶠ z in nhds (0 : ComplexEuclidean n),
      germPolynomialRepresentativeAt d (remainderGermPolynomial r) z =
        remainderPolynomialAt
          (HolomorphicGerm.coefficientRepresentatives r) z := by
  let Pg := germPolynomialRepresentativeFunctions d
    (remainderGermPolynomial r)
  let Pf : Polynomial (ComplexEuclidean n → ℂ) :=
    ∑ i : Fin d,
      Polynomial.C (HolomorphicGerm.representative (r i)) *
        Polynomial.X ^ (i : ℕ)
  have hPg : Pg.map (functionToGermRingHom n) =
      (remainderGermPolynomial r).map
        (holomorphicGermSubring n).subtype :=
    germPolynomialRepresentativeFunctions_map_germ _
      (remainderGermPolynomial_natDegree_le r)
  have hPf : Pf.map (functionToGermRingHom n) =
      (remainderGermPolynomial r).map
        (holomorphicGermSubring n).subtype := by
    simp only [Pf, remainderGermPolynomial, Polynomial.map_sum,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X]
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    exact HolomorphicGerm.coe_representative (r i)
  have hevent := eventually_polynomial_map_eval_eq_of_map_germ_eq Pg Pf
    (hPg.trans hPf.symm)
  filter_upwards [hevent] with z hz
  rw [← germPolynomialRepresentativeFunctions_map_eval]
  rw [hz]
  unfold Pf remainderPolynomialAt
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X,
    HolomorphicGerm.coefficientRepresentatives]
  rfl

end

end LocalComplexGeometry
