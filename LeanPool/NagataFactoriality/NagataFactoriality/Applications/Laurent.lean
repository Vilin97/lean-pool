/-
Copyright (c) 2026 Arthur F. Ramos, Ruy J. G. B. de Queiroz, Anjolina G. de Oliveira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur F. Ramos, Ruy J. G. B. de Queiroz, Anjolina G. de Oliveira
-/
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import LeanPool.NagataFactoriality.NagataFactoriality.Nagata.Lemmas
import LeanPool.NagataFactoriality.NagataFactoriality.Nagata.Theorem

namespace NagataFactoriality

open scoped LaurentPolynomial
open Polynomial

theorem laurentPolynomial_isLocalization (R : Type*) [CommSemiring R] :
    IsLocalization.Away (X : R[X]) R[T;T⁻¹] :=
  LaurentPolynomial.isLocalization

theorem polynomial_prime_X {R : Type*} [CommRing R] [IsDomain R] :
    Prime (Polynomial.X : R[X]) :=
  (Polynomial.prime_X : Prime (Polynomial.X : R[X]))

theorem polynomial_toLaurent_prime_of_not_dvd_X {R : Type*} [CommRing R] [IsDomain R]
    {p : R[X]} (hp : Prime p) (hX : ¬ p ∣ X) : Prime (Polynomial.toLaurent p) := by
  let M : Submonoid R[X] := Submonoid.powers X
  have hspanPrime : (Ideal.span ({p} : Set R[X])).IsPrime :=
    (Ideal.span_singleton_prime hp.ne_zero).2 hp
  have hdisj : Disjoint (M : Set R[X]) ↑(Ideal.span ({p} : Set R[X])) := by
    rw [Set.disjoint_left]
    intro m hm hmspan
    rcases hm with ⟨n, rfl⟩
    have hmspan' : p ∣ X ^ n := by
      simpa [Ideal.mem_span_singleton] using hmspan
    exact hX (hp.dvd_of_dvd_pow hmspan')
  have hmapPrime : (Ideal.map (algebraMap R[X] R[T;T⁻¹]) (Ideal.span ({p} : Set R[X]))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M R[T;T⁻¹] _ hspanPrime hdisj
  have hspanMap : Ideal.map (algebraMap R[X] R[T;T⁻¹]) (Ideal.span ({p} : Set R[X])) =
      Ideal.span ({Polynomial.toLaurent p} : Set R[T;T⁻¹]) := by
    simpa [LaurentPolynomial.algebraMap_eq_toLaurent, Set.image_singleton] using
      (Ideal.map_span (algebraMap R[X] R[T;T⁻¹]) ({p} : Set R[X]))
  rw [hspanMap] at hmapPrime
  exact (Ideal.span_singleton_prime (Polynomial.toLaurent_ne_zero.2 hp.ne_zero)).1 hmapPrime

theorem laurentPolynomial_uniqueFactorizationMonoid {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] : UniqueFactorizationMonoid R[T;T⁻¹] := by
  letI : UniqueFactorizationMonoid R[X] := inferInstance
  rw [UniqueFactorizationMonoid.iff_exists_prime_factors]
  intro f hf
  obtain ⟨n, p, hpLaurent⟩ := LaurentPolynomial.exists_T_pow f
  have hp0 : p ≠ 0 := by
    intro hpz
    have hT0 : (LaurentPolynomial.T n : R[T;T⁻¹]) ≠ 0 := (LaurentPolynomial.isUnit_T n).ne_zero
    have : f * LaurentPolynomial.T n = 0 := by
      simpa [hpz] using hpLaurent.symm
    exact hf ((mul_eq_zero.mp this).resolve_right hT0)
  obtain ⟨q, hpq, hqX⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp0 0
  have hpq' : p = X ^ p.rootMultiplicity 0 * q := by
    simpa using hpq
  have hqX' : ¬ X ∣ q := by
    simpa using hqX
  have hq0 : q ≠ 0 := by
    intro hq0
    apply hp0
    rw [hpq', hq0, mul_zero]
  obtain ⟨w, hwprime, hwassoc⟩ := UniqueFactorizationMonoid.exists_prime_factors q hq0
  refine ⟨w.map Polynomial.toLaurent, ?_, ?_⟩
  · intro z hz
    rcases Multiset.mem_map.1 hz with ⟨r, hr, rfl⟩
    have hrdvdq : r ∣ q := hwassoc.dvd_iff_dvd_right.mp (Multiset.dvd_prod hr)
    have hrnot : ¬ r ∣ X := by
      intro hrX
      have hassoc : Associated r X :=
        (hwprime r hr).irreducible.associated_of_dvd Polynomial.irreducible_X hrX
      exact hqX' (dvd_trans hassoc.symm.dvd hrdvdq)
    exact polynomial_toLaurent_prime_of_not_dvd_X (hwprime r hr) hrnot
  · have hmapassoc : Associated (w.map Polynomial.toLaurent).prod (Polynomial.toLaurent q) := by
      rw [Multiset.prod_hom]
      exact hwassoc.map Polynomial.toLaurent
    have hfp : Associated f (Polynomial.toLaurent p) := by
      rw [hpLaurent]
      exact associated_mul_unit_right _ _ (LaurentPolynomial.isUnit_T n)
    have hpqAssoc : Associated (Polynomial.toLaurent p) (Polynomial.toLaurent q) := by
      rw [hpq', map_mul, Polynomial.toLaurent_X_pow]
      simpa [LaurentPolynomial.T_mul] using
        (associated_mul_unit_left (Polynomial.toLaurent q) (LaurentPolynomial.T (p.rootMultiplicity 0))
          (LaurentPolynomial.isUnit_T (p.rootMultiplicity 0)))
    exact hmapassoc.trans (hfp.trans hpqAssoc).symm

theorem polynomial_uniqueFactorizationMonoid_of_laurent {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [UniqueFactorizationMonoid R[T;T⁻¹]] :
    UniqueFactorizationMonoid R[X] := by
  let S : Submonoid R[X] := Submonoid.powers X
  have hS : PrimeGenerated S := by
    simpa [S] using (primeGenerated_powers (p := (X : R[X])) (polynomial_prime_X (R := R)))
  letI : _root_.IsLocalization S R[T;T⁻¹] := by
    simpa [S] using (laurentPolynomial_isLocalization R : _root_.IsLocalization.Away (X : R[X]) R[T;T⁻¹])
  exact nagata_theorem_isLocalization (R := R[X]) (T := R[T;T⁻¹]) S hS inferInstance

theorem polynomial_uniqueFactorizationMonoid_via_nagata {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [UniqueFactorizationMonoid R] : UniqueFactorizationMonoid R[X] := by
  letI : UniqueFactorizationMonoid R[T;T⁻¹] := laurentPolynomial_uniqueFactorizationMonoid (R := R)
  exact polynomial_uniqueFactorizationMonoid_of_laurent (R := R)

theorem iterated_polynomial_uniqueFactorizationMonoid_via_nagata
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [UniqueFactorizationMonoid R] : UniqueFactorizationMonoid (Polynomial (Polynomial R)) := by
  letI : UniqueFactorizationMonoid R[X] :=
    polynomial_uniqueFactorizationMonoid_via_nagata (R := R)
  simpa using polynomial_uniqueFactorizationMonoid_via_nagata (R := R[X])

end NagataFactoriality
