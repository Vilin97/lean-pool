/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Nullstellensatz.IdealRepresentatives
import LeanPool.LocalComplexGeometry.Nullstellensatz.PolynomialSpecialization
import LeanPool.LocalComplexGeometry.Nullstellensatz.ResultantSpecialization

/-!
# Specializing polynomial identities modulo an analytic ideal

An equality of polynomials after reducing their germ coefficients modulo an
ideal says that every coefficient difference belongs to that ideal.  A finite
fixed-degree family of chosen representatives therefore specializes to equal
complex polynomials on the ideal's local zero set, on one common neighborhood.
-/

open Filter
open scoped Topology


namespace LocalComplexGeometry

noncomputable section

/-- Chosen representatives of all coefficients through a fixed degree bound. -/
def germPolynomialCoefficientRepresentatives {n m : ℕ}
    (p : Polynomial (HolomorphicGerm n)) :
    Fin (m + 1) → ComplexEuclidean n → ℂ :=
  fun i ↦ HolomorphicGerm.representative (p.coeff (i : ℕ))

theorem analyticAt_germPolynomialCoefficientRepresentatives {n m : ℕ}
    (p : Polynomial (HolomorphicGerm n)) (i : Fin (m + 1)) :
    AnalyticAt ℂ (germPolynomialCoefficientRepresentatives p i) 0 :=
  HolomorphicGerm.analyticAt_representative (p.coeff (i : ℕ))

/-- The fixed-degree complex polynomial obtained by specializing the chosen
coefficient representatives at a base point. -/
def germPolynomialRepresentativeAt {n : ℕ} (m : ℕ)
    (p : Polynomial (HolomorphicGerm n)) (z : ComplexEuclidean n) :
    Polynomial ℂ :=
  fixedDegreePolynomialAt
    (germPolynomialCoefficientRepresentatives (m := m) p) z

/-- The same fixed-degree representative family, before specializing its
coefficient functions at a base point. -/
def germPolynomialRepresentativeFunctions {n : ℕ} (m : ℕ)
    (p : Polynomial (HolomorphicGerm n)) :
    Polynomial (ComplexEuclidean n → ℂ) :=
  fixedDegreePolynomial
    (germPolynomialCoefficientRepresentatives (m := m) p)

@[simp]
theorem germPolynomialRepresentativeFunctions_map_eval {n : ℕ} (m : ℕ)
    (p : Polynomial (HolomorphicGerm n)) (z : ComplexEuclidean n) :
    (germPolynomialRepresentativeFunctions m p).map
        (Pi.evalRingHom (fun _ : ComplexEuclidean n ↦ ℂ) z) =
      germPolynomialRepresentativeAt m p z := by
  exact fixedDegreePolynomial_map_eval
    (germPolynomialCoefficientRepresentatives (m := m) p) z

/-- Through a valid degree bound, the polynomial of chosen representative
functions maps back to the original polynomial of raw function germs. -/
theorem germPolynomialRepresentativeFunctions_map_germ {n m : ℕ}
    (p : Polynomial (HolomorphicGerm n)) (hp : p.natDegree ≤ m) :
    (germPolynomialRepresentativeFunctions m p).map
        (functionToGermRingHom n) =
      p.map (holomorphicGermSubring n).subtype := by
  rw [germPolynomialRepresentativeFunctions, fixedDegreePolynomial_map]
  have hcoeff :
      (fun i : Fin (m + 1) ↦
        functionToGermRingHom n
          (germPolynomialCoefficientRepresentatives p i)) =
      (fun i : Fin (m + 1) ↦
        (holomorphicGermSubring n).subtype (p.coeff (i : ℕ))) := by
    funext i
    simpa [functionToGermRingHom,
      germPolynomialCoefficientRepresentatives] using
      (HolomorphicGerm.coe_representative (p.coeff (i : ℕ)))
  rw [hcoeff]
  have hdegree :
      (p.map (holomorphicGermSubring n).subtype).natDegree ≤ m :=
    (Polynomial.natDegree_map_le
      (p := p) (f := (holomorphicGermSubring n).subtype)).trans hp
  rw [← fixedDegreePolynomial_coefficients_eq
    (p.map (holomorphicGermSubring n).subtype) hdegree]
  congr 1
  funext i
  simp only [Polynomial.coeff_map]

/-- Two valid fixed-degree displays of the same germ polynomial agree after
shrinking once. -/
theorem eventually_germPolynomialRepresentativeAt_eq_of_degreeBounds
    {n k m : ℕ} (p : Polynomial (HolomorphicGerm n))
    (hk : p.natDegree ≤ k) (hm : p.natDegree ≤ m) :
    ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      germPolynomialRepresentativeAt k p z =
        germPolynomialRepresentativeAt m p z := by
  let Pk := germPolynomialRepresentativeFunctions k p
  let Pm := germPolynomialRepresentativeFunctions m p
  have hmap : Pk.map (functionToGermRingHom n) =
      Pm.map (functionToGermRingHom n) :=
    (germPolynomialRepresentativeFunctions_map_germ p hk).trans
      (germPolynomialRepresentativeFunctions_map_germ p hm).symm
  have hevent := eventually_polynomial_map_eval_eq_of_map_germ_eq Pk Pm hmap
  filter_upwards [hevent] with z hz
  simpa [Pk, Pm] using hz

/-- At bound zero, a constant germ polynomial specializes to the chosen
representative of its constant coefficient. -/
@[simp]
theorem germPolynomialRepresentativeAt_zero_C {n : ℕ}
    (f : HolomorphicGerm n) (z : ComplexEuclidean n) :
    germPolynomialRepresentativeAt 0 (Polynomial.C f) z =
      Polynomial.C (HolomorphicGerm.representative f z) := by
  ext k
  by_cases hk : k = 0
  · subst k
    simp [germPolynomialRepresentativeAt,
      germPolynomialCoefficientRepresentatives,
      fixedDegreePolynomialAt, fixedDegreePolynomial_coeff]
  · simp [germPolynomialRepresentativeAt,
      germPolynomialCoefficientRepresentatives,
      fixedDegreePolynomialAt, fixedDegreePolynomial_coeff,
      Polynomial.coeff_C, hk]

/-- Chosen fixed-degree representatives respect polynomial addition after
shrinking once, provided the displayed degree bound covers all three
polynomials. -/
theorem eventually_germPolynomialRepresentativeAt_add
    {n m : ℕ} (p q : Polynomial (HolomorphicGerm n))
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ m)
    (hpq : (p + q).natDegree ≤ m) :
    ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      germPolynomialRepresentativeAt m (p + q) z =
        germPolynomialRepresentativeAt m p z +
          germPolynomialRepresentativeAt m q z := by
  let P := germPolynomialRepresentativeFunctions m p
  let Q := germPolynomialRepresentativeFunctions m q
  let PQ := germPolynomialRepresentativeFunctions m (p + q)
  have hmap : PQ.map (functionToGermRingHom n) =
      (P + Q).map (functionToGermRingHom n) := by
    dsimp [PQ, P, Q]
    rw [Polynomial.map_add,
      germPolynomialRepresentativeFunctions_map_germ (p + q) hpq,
      germPolynomialRepresentativeFunctions_map_germ p hp,
      germPolynomialRepresentativeFunctions_map_germ q hq,
      Polynomial.map_add]
  have hevent := eventually_polynomial_map_eval_eq_of_map_germ_eq PQ (P + Q) hmap
  filter_upwards [hevent] with z hz
  simpa [PQ, P, Q, Polynomial.map_add] using hz

/-- Chosen fixed-degree representatives respect polynomial multiplication
after shrinking once, provided the displayed degree bound covers both factors
and their product. -/
theorem eventually_germPolynomialRepresentativeAt_mul
    {n m : ℕ} (p q : Polynomial (HolomorphicGerm n))
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ m)
    (hpq : (p * q).natDegree ≤ m) :
    ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      germPolynomialRepresentativeAt m (p * q) z =
        germPolynomialRepresentativeAt m p z *
          germPolynomialRepresentativeAt m q z := by
  let P := germPolynomialRepresentativeFunctions m p
  let Q := germPolynomialRepresentativeFunctions m q
  let PQ := germPolynomialRepresentativeFunctions m (p * q)
  have hmap : PQ.map (functionToGermRingHom n) =
      (P * Q).map (functionToGermRingHom n) := by
    dsimp [PQ, P, Q]
    rw [Polynomial.map_mul,
      germPolynomialRepresentativeFunctions_map_germ (p * q) hpq,
      germPolynomialRepresentativeFunctions_map_germ p hp,
      germPolynomialRepresentativeFunctions_map_germ q hq,
      Polynomial.map_mul]
  have hevent := eventually_polynomial_map_eval_eq_of_map_germ_eq PQ (P * Q) hmap
  filter_upwards [hevent] with z hz
  simpa [PQ, P, Q, Polynomial.map_mul] using hz

/-- Quotient equality gives simultaneous equality of every represented
coefficient through any prescribed finite degree bound. -/
theorem eventually_germPolynomialCoefficientRepresentatives_eq_of_map_quotient_eq
    {n m : ℕ} [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n))
    (p q : Polynomial (HolomorphicGerm n))
    (hmap : p.map (Ideal.Quotient.mk I) = q.map (Ideal.Quotient.mk I)) :
    ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      idealGeneratorZeroPredicate I z → ∀ i : Fin (m + 1),
        germPolynomialCoefficientRepresentatives p i z =
          germPolynomialCoefficientRepresentatives q i z := by
  have hcoeff (i : Fin (m + 1)) :
      Ideal.Quotient.mk I (p.coeff (i : ℕ)) =
        Ideal.Quotient.mk I (q.coeff (i : ℕ)) := by
    have h := congrArg
      (fun r : Polynomial (HolomorphicGerm n ⧸ I) ↦ r.coeff (i : ℕ)) hmap
    simpa only [Polynomial.coeff_map] using h
  have hevent (i : Fin (m + 1)) :
      ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
        idealGeneratorZeroPredicate I z →
          germPolynomialCoefficientRepresentatives p i z =
            germPolynomialCoefficientRepresentatives q i z :=
    eventually_representatives_eq_of_quotient_eq I
      (p.coeff (i : ℕ)) (q.coeff (i : ℕ)) (hcoeff i)
  have hall :
      ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n), ∀ i : Fin (m + 1),
        idealGeneratorZeroPredicate I z →
          germPolynomialCoefficientRepresentatives p i z =
            germPolynomialCoefficientRepresentatives q i z :=
    Filter.eventually_all.mpr hevent
  filter_upwards [hall] with z hz
  intro hZ i
  exact hz i hZ

/-- A polynomial identity modulo `I` specializes to a complex-polynomial
identity on `V(I)`, uniformly on one neighborhood. -/
theorem eventually_germPolynomialRepresentativeAt_eq_of_map_quotient_eq
    {n m : ℕ} [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n))
    (p q : Polynomial (HolomorphicGerm n))
    (hmap : p.map (Ideal.Quotient.mk I) = q.map (Ideal.Quotient.mk I)) :
    ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      idealGeneratorZeroPredicate I z →
        germPolynomialRepresentativeAt m p z =
          germPolynomialRepresentativeAt m q z := by
  filter_upwards
    [eventually_germPolynomialCoefficientRepresentatives_eq_of_map_quotient_eq
      (m := m) I p q hmap] with z hz
  intro hZ
  unfold germPolynomialRepresentativeAt fixedDegreePolynomialAt
  congr 1
  funext i
  exact hz hZ i

/-- Evaluation form of quotient-polynomial specialization. -/
theorem eventually_germPolynomialRepresentativeAt_eval_eq_of_map_quotient_eq
    {n m : ℕ} [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n))
    (p q : Polynomial (HolomorphicGerm n))
    (hmap : p.map (Ideal.Quotient.mk I) = q.map (Ideal.Quotient.mk I)) :
    ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      idealGeneratorZeroPredicate I z → ∀ w : ℂ,
        (germPolynomialRepresentativeAt m p z).eval w =
          (germPolynomialRepresentativeAt m q z).eval w := by
  filter_upwards
    [eventually_germPolynomialRepresentativeAt_eq_of_map_quotient_eq
      (m := m) I p q hmap] with z hz
  intro hZ w
  rw [hz hZ]

end

end LocalComplexGeometry
