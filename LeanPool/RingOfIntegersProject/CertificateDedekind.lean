/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola,
Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.DedekindCriteria
import LeanPool.RingOfIntegersProject.PolynomialsAsLists

/-!

# Certificate Dedekind Criterion

We define certificates for Dedekind criterion.

## Certificates:
- `CertificateDedekindCriterion` : certifies that `T` satisifes Dedekind criterion at `p`
- `CertificateDedekindCriterionLists` : version of `CertificateDedekindCriterion` using lists.
- `CertificateDedekindAlmostAll` : certifies that `T` satisfies Dedekind criterion at all
  but a finite list of primes.
- `CertificateDedekindAlmostAllLists` : version of `CertificateDedekindAlmostAll` using lists.

-/

open Polynomial BigOperators

/-
# A CERTIFICATE FOR DEDEKIND'S CRITERION -/


/-- Certifies that a polynomial `T` satisfies Dedekind criterion at a prime `p`.
- `g` : a lift of the radical of `T mod p`
- `n` : natural such that `T mod p ∣ (g mod p) ^ n`
- `k` : equal to `(g mod p) ^ n / T mod p`
- `h` : a lift of `(T mod p) / (g mod p) `
- `f` : the polynomial `(g * h - T) / p`
- `a` and `b` : polynomials certifying `gcd (f mod p, g mod p, h mod p) = 1`
- `a'` and `b'` : polynomials certifying that `g mod p` is square-free. -/
structure CertificateDedekindCriterion (T : ℤ[X]) (p : ℕ) where
  /-- Imported declaration. -/
  n : ℕ
  /-- Imported declaration. -/
  a' : (ZMod p) [X]
  /-- Imported declaration. -/
  b' : (ZMod p) [X]
  /-- Imported declaration. -/
  k : (ZMod p) [X]
  /-- Imported declaration. -/
  f : ℤ[X]
  /-- Imported declaration. -/
  g : ℤ[X]
  /-- Imported declaration. -/
  h : ℤ[X]
  /-- Imported declaration. -/
  a : (ZMod p) [X]
  /-- Imported declaration. -/
  b : (ZMod p) [X]
  /-- Imported declaration. -/
  c : (ZMod p) [X]
  hdvdpow : (map (algebraMap ℤ (ZMod p)) T) * k = (map (algebraMap ℤ (ZMod p)) g) ^ n
  hcop : a' * (map (algebraMap ℤ (ZMod p)) g) + b' * derivative (map (algebraMap ℤ (ZMod p)) g) = 1
  hf : f * p + T = g * h
  habc : a * (map (algebraMap ℤ (ZMod p)) f) +
    b * (map (algebraMap ℤ (ZMod p)) g) + c * (map (algebraMap ℤ (ZMod p)) h) = 1

theorem satisfiesDedekindCriterion_of_certificate (T : ℤ[X]) (p : ℕ) [hp : Fact <| Nat.Prime p]
    (C : CertificateDedekindCriterion T p) : satisfiesDedekindCriterionInt T p := by
  use C.f, C.g, C.h, C.a, C.b,  C.c
  constructor
  · refine isRadicalPart_of_coprime_derivative_of_dvd_of_dvd_pow
      (map (algebraMap ℤ (ZMod p)) T) (map (algebraMap ℤ (ZMod p)) C.g) ?_ ?_ ?_
    · have : T = C.g * C.h - C.f * p := by rw [← C.hf, add_sub_cancel_left]
      simp_rw [this]
      simp only [algebraMap_int_eq, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_natCast,
        CharP.cast_eq_zero, mul_zero, sub_zero, dvd_mul_right]
    · use C.n; use C.k
      exact C.hdvdpow.symm
    · use C.a', C.b'
      exact C.hcop
  · constructor
    · rw [← C.hf, add_sub_cancel_right]
    · exact C.habc

-- We exclude these instances because pointwise addition for lists over integers is already defined.
attribute [-instance]  Lean.Omega.IntList.instMul
attribute [-instance]  Lean.Omega.IntList.instAdd

/-- Certifies that a polynomial `T` satisfies Dedekind criterion at a prime `p`
  Version of `CertificateDedekindCriterion` using lists. -/
structure CertificateDedekindCriterionLists (T : List ℤ) (p : ℕ) where
  /-- Imported declaration. -/
  n : ℕ
  /-- Imported declaration. -/
  a' : List (ZMod p)
  /-- Imported declaration. -/
  b' : List (ZMod p)
  /-- Imported declaration. -/
  k : List (ZMod p)
  /-- Imported declaration. -/
  f : List ℤ
  /-- Imported declaration. -/
  g : List ℤ
  /-- Imported declaration. -/
  h : List ℤ
  /-- Imported declaration. -/
  a : List (ZMod p)
  /-- Imported declaration. -/
  b : List (ZMod p)
  /-- Imported declaration. -/
  c : List (ZMod p)
  hdvdpow : ((List.map (algebraMap ℤ (ZMod p)) T) * k).dropTrailingZeros' =
    ((List.map (algebraMap ℤ (ZMod p)) g) ^ n).dropTrailingZeros'
  hcop : (a' * (List.map (algebraMap ℤ (ZMod p)) g) +
    b' * List.derivative (List.map (algebraMap ℤ (ZMod p)) g)).dropTrailingZeros' = 1
  hf : (f * p + T).dropTrailingZeros' = (g * h).dropTrailingZeros'
  habc : (a * (List.map (algebraMap ℤ (ZMod p)) f)+
    b * (List.map (algebraMap ℤ (ZMod p)) g) + c *
      (List.map (algebraMap ℤ (ZMod p)) h)).dropTrailingZeros' = 1

theorem satisfiesDedekindCriterion_of_certificate_lists (T : ℤ[X]) (l : List ℤ) (p : ℕ)
    [hp : Fact <| Nat.Prime p] (heq : ofList l = T)
    (C : CertificateDedekindCriterionLists l p) : satisfiesDedekindCriterionInt T p :=
  let C' : CertificateDedekindCriterion (ofList l) p :=
    { n := C.n,
      a' := ofList (C.a'), b' := ofList (C.b'),
      k := ofList (C.k), f := ofList (C.f), g := ofList (C.g),
      h := ofList (C.h), a := ofList (C.a), b := ofList (C.b), c := ofList (C.c),
      hdvdpow := by
        rw [ofList_map, ← ofList_convolve_eq_mul,
        ← ofList_dropTrailingZeros_eq_ofList, dropTrailingZeros_eq_dropTrailingZeros', C.hdvdpow,
        ← dropTrailingZeros_eq_dropTrailingZeros', ofList_dropTrailingZeros_eq_ofList,
         ofList_map, ofList_pow_eq_pow]
      hcop := by
        rw [ofList_map, ← ofList_derivative_eq_derivative,
        ← ofList_convolve_eq_mul, ← ofList_convolve_eq_mul,
        ← ofList_addPointwise_eq_add, ← ofList_dropTrailingZeros_eq_ofList,
        dropTrailingZeros_eq_dropTrailingZeros',
        C.hcop, ofList_one]
      hf := by
        rw [← ofList_convolve_eq_mul]
        nth_rw 3 [← ofList_dropTrailingZeros_eq_ofList]
        rw [dropTrailingZeros_eq_dropTrailingZeros', ← C.hf,
          ← dropTrailingZeros_eq_dropTrailingZeros',
          ofList_dropTrailingZeros_eq_ofList, ofList_addPointwise_eq_add, ofList_convolve_eq_mul]
        simp only [ofList_natCast]
      habc := by
        simp only [algebraMap_int_eq, ofList_map, Int.coe_castRingHom, ← ofList_convolve_eq_mul,
          ← ofList_addPointwise_eq_add]
        erw [← ofList_dropTrailingZeros_eq_ofList,
          dropTrailingZeros_eq_dropTrailingZeros', C.habc, ofList_one]  }
  by
  rw [← heq]
  exact satisfiesDedekindCriterion_of_certificate (ofList l) p C'


/-- Certifies that `T` satisfies Dedekind criterion for all but finitely many primes
 in the list `pb` -
- `a` and `b`: polynomials such that `a * T + b * derivative(T) = m`
- `n` : number of distinct primes dividing `m`
- `exp` : the exponents of each of the prime factors of `m`
- `pdgood` : a list of primes at which we know `T` satisfies Dedekind criterion.
-/
structure CertificateDedekindAlmostAll (T : ℤ[X]) (pb : List ℕ) where
  /-- Imported declaration. -/
  n : ℕ
  /-- Imported declaration. -/
  p : Fin n → ℕ
  /-- Imported declaration. -/
  exp : Fin n → ℕ
  /-- Imported declaration. -/
  pdgood : List ℕ
  hsub : List.ofFn p ⊆ pdgood ++ pb
  hp : ∀ i : Fin n, Nat.Prime (p i)
  /-- Imported declaration. -/
  a : ℤ[X]
  /-- Imported declaration. -/
  b : ℤ[X]
  hab : a * T + b * (derivative T) = ∏ i : Fin n, (p i) ^ (exp i)
  hd : ∀ pr ∈ pdgood, satisfiesDedekindCriterionInt T pr

theorem satisfiesDedekindAlmostAll_of_certificate (T : ℤ[X]) (pdbad : List ℕ)
    (C : CertificateDedekindAlmostAll T pdbad) :
    ∀ p, Nat.Prime p → (p ∉ pdbad) → satisfiesDedekindCriterionInt T p := by
  intro p hp hpnein
  haveI : Fact <| Nat.Prime p := fact_iff.2 hp
  by_cases hin : p  ∉ List.ofFn (C.p)
  · refine satisfiesDedekindCriterion_of_coprime_int T C.a C.b p _ C.hab ?_
    apply Prime.not_dvd_finset_prod (Nat.Prime.prime hp)
    intro i hi
    by_contra hc
    rw [(Nat.prime_dvd_prime_iff_eq hp (C.hp i)).1 (Nat.Prime.dvd_of_dvd_pow hp hc),
     List.mem_ofFn, ] at hin
    simp only [exists_apply_eq_apply, not_true_eq_false] at hin
  · push Not at hin
    have aux := (List.mem_append.1 (C.hsub hin))
    rcases aux with h1 | h2
    · exact C.hd _ h1
    · exfalso
      exact hpnein h2

/-- Certifies that `T` satisfies Dedekind criterion for all but finitely many primes
 in the list `pb`. This is a version of `CertificateDedekindAlmostAll` using lists. -/
structure CertificateDedekindAlmostAllLists (T : ℤ[X]) (l : List ℤ) (pb : List ℕ) where
  /-- Imported declaration. -/
  n : ℕ
  /-- Imported declaration. -/
  p : Fin n → ℕ
  /-- Imported declaration. -/
  exp : Fin n → ℕ
  /-- Imported declaration. -/
  pdgood : List ℕ
  hsub : List.ofFn p ⊆ pdgood ++ pb
  hp : ∀ i : Fin n, Nat.Prime (p i)
  /-- Imported declaration. -/
  a : List ℤ
  /-- Imported declaration. -/
  b : List ℤ
  hab : (a * l + b * (List.derivative l)).dropTrailingZeros' = ∏ i : Fin n, (p i) ^ (exp i)
  hd : ∀ pr ∈ pdgood, satisfiesDedekindCriterionInt T pr

theorem satisfiesDedekindAlmostAllLists_of_certificate (T : ℤ[X]) (l : List ℤ)
    (heq : ofList l = T)
    (pdbad : List ℕ)
    (C : CertificateDedekindAlmostAllLists T l pdbad) :
    ∀ p, Nat.Prime p → (p ∉ pdbad) → satisfiesDedekindCriterionInt T p :=
  let C' : CertificateDedekindAlmostAll (ofList l) pdbad :=
    { n := C.n,  p := C.p, exp := C.exp, pdgood := C.pdgood, hsub := C.hsub,
      hp := C.hp, a := ofList (C.a), b := ofList (C.b),
      hab := by
        rw [← ofList_convolve_eq_mul, ← ofList_derivative_eq_derivative, ← ofList_convolve_eq_mul,
          ← ofList_addPointwise_eq_add, ← ofList_dropTrailingZeros_eq_ofList,
           dropTrailingZeros_eq_dropTrailingZeros',
          C.hab]
        simp only [ofList_natCast, Nat.cast_prod, Nat.cast_pow]
      hd := by
        simp_rw [heq]
        exact C.hd}
  by
  rw [← heq]
  exact satisfiesDedekindAlmostAll_of_certificate _ _ C'
