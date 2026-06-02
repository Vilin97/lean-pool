/-
Copyright (c) 2026 Anne Baanen et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import Mathlib.Tactic.Cases
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Tactic.ReduceModChar

/-!
# The radical part

In this document we define what it means to be the radical part (squarefree part)
of an element in a commutative ring.

## Main definition:
- `IsRadicalPart` : predicate characterizing the radical of an element.

## Main results:
- `isRadicalPart_of_coprime_derivative_of_dvd_of_dvd_pow` : certifies the radical of a polynomial.
- `self_isRadicalPart_of_coprime'` : gives conditions that guarantee that the
  reduction of a polynomial is its own radical. -/

open Polynomial Finset

open scoped BigOperators


variable {R : Type*} [CommMonoidWithZero R]

/-- `b` is the radical part of `a` if it has the same prime divisors as `a` and is squarefree· -/
def IsRadicalPart (b : R) (a : R) : Prop :=
  (∀ p : R, Prime p → (p ∣ a ↔ p ∣ b)) ∧ Squarefree b

lemma isRadicalPart_def (b : R) (a : R) :
    IsRadicalPart b a ↔ (∀ p : R, Prime p → (p ∣ a ↔ p ∣ b)) ∧ Squarefree b :=
  Iff.rfl

/-- If `b` is a squarefree element that divides `a`, and such that `a` divides a power of `b`, then
 `b` is the radical part of `a`· -/
lemma isRadicalPart_of_dvd_pow {R : Type*} [CommMonoidWithZero R] {a b : R}
    (hg : Squarefree b) (hdvd : b ∣ a) (h : ∃ n : ℕ, a ∣ b ^ n) :
    IsRadicalPart b a := by
  obtain ⟨n, hn⟩ := h
  rw [isRadicalPart_def]
  constructor
  · intro a hap
    constructor
    · intro hadvd
      exact Prime.dvd_of_dvd_pow hap (dvd_trans hadvd hn)
    · intro hdvd2
      exact dvd_trans hdvd2 hdvd
  · exact hg

/-- The radical part of `a` is the radical part of any power of `a` -/
lemma isRadicalPart_pow_of_isRadicalPart {R : Type*} [CommMonoidWithZero R]
    {a b : R} {n : ℕ} (hn : n ≠ 0) (h : IsRadicalPart b a) :
    IsRadicalPart b (a ^ n) := by
  rw [isRadicalPart_def] at h ⊢
  refine ⟨?_, h.2⟩
  intro a hap
  constructor
  · intro hadvd
    exact (h.1 a hap).1 (Prime.dvd_of_dvd_pow hap hadvd)
  · intro hagdvd
    refine dvd_pow ?_ hn
    exact (h.1 a hap).2 hagdvd

lemma ne_dvd_of_isCoprime {R : Type*} [CommSemiring R] {a b p : R} (hp : ¬IsUnit p)
    (hgcd : IsCoprime a b) (h : p ∣ a) : ¬p ∣ b := by
  obtain ⟨t, ht⟩ := h
  by_contra hg
  obtain ⟨q, hq⟩ := hg
  rw [ht, hq, IsCoprime.mul_left_iff, IsCoprime.mul_right_iff, isCoprime_self] at hgcd
  exact hp hgcd.1.1

/-- The associate of a radical part of `a` is also a radical part· -/
lemma associated_isRadicalPart_of_isRadicalPart {R : Type*} [CommMonoidWithZero R] {a b c : R}
  (ha : Associated b c) (hr : IsRadicalPart b a) : IsRadicalPart c a := by
  rw [isRadicalPart_def] at hr ⊢
  rcases hr with ⟨h1, h2⟩
  constructor
  · simp_rw [Associated.dvd_iff_dvd_right ha] at h1
    exact h1
  · exact Squarefree.squarefree_of_dvd (Associated.dvd_dvd ha).2 h2

/-- If `b` is the radical part of `a`, then `a` divides some power of `b`. -/
lemma dvd_pow_of_isRadicalPart {R : Type*} [Nontrivial R] [CommMonoidWithZero R]
    [UniqueFactorizationMonoid R] {a b : R} (hf : a ≠ 0)
    (hr : IsRadicalPart b a) : ∃ n : ℕ, a ∣ b ^ n := by
  classical
  haveI :NormalizationMonoid R := UniqueFactorizationMonoid.normalizationMonoid
  have : b ≠ 0 := Squarefree.ne_zero hr.2
  use Multiset.card (UniqueFactorizationMonoid.normalizedFactors a)
  rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hf,
    Multiset.le_iff_count]
  · intro p
    by_cases h : Multiset.count p (UniqueFactorizationMonoid.normalizedFactors a) = 0
    · rw [h]
      simp only [zero_le]
    · simp only [Multiset.count_eq_zero, Classical.not_not] at h
      have hadvdf : p ∣ a := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors h
      have haprime : Prime p := UniqueFactorizationMonoid.prime_of_normalized_factor p h
      have hass : normalize p = p := UniqueFactorizationMonoid.normalize_normalized_factor p h
      simp only [UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul]
      have hnez : Multiset.count p (UniqueFactorizationMonoid.normalizedFactors b) ≠ 0 := by
        by_contra h1
        rw [← hass] at h1
        have :=
          UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors
            (UniqueFactorizationMonoid.irreducible_iff_prime.2 haprime) this
        rw [h1] at this
        simp only [Nat.cast_zero] at this
        rw [emultiplicity_eq_zero] at this
        exact this ((((isRadicalPart_def b a).1 hr).1 p haprime).1 hadvdf)
      have hleq :
          Multiset.count p (UniqueFactorizationMonoid.normalizedFactors a) ≤
            Multiset.card (UniqueFactorizationMonoid.normalizedFactors a) := by
        refine Multiset.count_le_card _ _
      rw [← Nat.one_le_iff_ne_zero] at hnez
      nlinarith
  · refine pow_ne_zero _ this

/-- If `b` is the radical part of `a`, and every prime that divides `a` also divides `c`,
  then `b` divides `c`. -/
lemma isRadicalPart_dvd_of_prime_dvd {R : Type*} [Nontrivial R] [CommMonoidWithZero R]
    [UniqueFactorizationMonoid R] {a b c : R}
    (hr : IsRadicalPart b a) (hpdvd : ∀ p : R, Prime p → p ∣ a → p ∣ c) : b ∣ c := by
  classical
  haveI :NormalizationMonoid R := UniqueFactorizationMonoid.normalizationMonoid
  have hgz : b ≠ 0 := Squarefree.ne_zero hr.2
  by_cases hc : c = 0
  · rw [hc]
    simp only [dvd_zero]
  · rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hgz hc,
      Multiset.le_iff_count]
    intro p
    by_cases hcc : Multiset.count p (UniqueFactorizationMonoid.normalizedFactors b) = 0
    · rw [hcc]
      simp only [zero_le]
    · simp only [Multiset.count_eq_zero, Classical.not_not] at hcc
      have hadvdg : p ∣ b := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hcc
      have haprime : Prime p := UniqueFactorizationMonoid.prime_of_normalized_factor p hcc
      have hass : normalize p = p := UniqueFactorizationMonoid.normalize_normalized_factor p hcc
      have hnez : Multiset.count p (UniqueFactorizationMonoid.normalizedFactors c) ≠ 0 := by
        by_contra h1
        rw [← hass] at h1
        have :=
          UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors
            (UniqueFactorizationMonoid.irreducible_iff_prime.2 haprime) hc
        rw [h1] at this
        simp only [Nat.cast_zero] at this
        rw [emultiplicity_eq_zero] at this
        exact this (hpdvd p haprime ((((isRadicalPart_def b a).1 hr).1 p haprime).2 hadvdg))
      have := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hgz).1 hr.2
      simp only [*, Multiset.count_eq_one_of_mem]
      rw [← Nat.one_le_iff_ne_zero] at hnez
      linarith

/-- If `b` is the radical part of `a`, then `b` divides `a`. -/
lemma isRadicalPart_dvd {R : Type*} [CommMonoidWithZero R] [Nontrivial R]
    [UniqueFactorizationMonoid R] {a b : R}
    (hr : IsRadicalPart b a) : b ∣ a :=
  isRadicalPart_dvd_of_prime_dvd hr (c := a) (fun _ _ => (fun a => a))

/-- If `b` is the radical part of `a`, and `a` divides some power of `c`, then `b` divides `c`· -/
lemma isRadicalPart_dvd_of_dvd_pow {n : ℕ} {R : Type*} [Nontrivial R] [CommMonoidWithZero R]
    [UniqueFactorizationMonoid R]
    {a b c : R} (hr : IsRadicalPart b a) (hfdvd : a ∣ c ^ n) : b ∣ c := by
  refine isRadicalPart_dvd_of_prime_dvd hr ?_
  intro a hap hadvdf
  exact Prime.dvd_of_dvd_pow hap (dvd_trans hadvdf hfdvd)

/-- The radical part of the product of two coprime elements
  is the product of the radical parts of each of these elements· -/
lemma mul_isRadicalPart_mul {R : Type*} [CommSemiring R] [IsDomain R] [DecompositionMonoid R]
    (a b c d : R) (hgcd : IsRelPrime b d) (hr1 : IsRadicalPart b a) (hr2 : IsRadicalPart d c) :
    IsRadicalPart (b * d) (a * c) := by
  constructor
  · intro a hap
    constructor
    · intro hadvd
      cases Prime.dvd_or_dvd hap hadvd
      case _ h_1 => exact dvd_mul_of_dvd_left ((hr1.1 a hap).1 h_1) d
      case _ h_1 => exact dvd_mul_of_dvd_right ((hr2.1 a hap).1 h_1) b
    · intro hadvd
      cases Prime.dvd_or_dvd hap hadvd
      case _ h_1 => apply dvd_mul_of_dvd_left; exact (hr1.1 a hap).2 h_1
      case _ h_1 => apply dvd_mul_of_dvd_right; exact (hr2.1 a hap).2 h_1
  · refine (squarefree_mul_iff (x := b) (y := d)).2 ?_
    exact ⟨hgcd, hr1.2, hr2.2⟩


/-- A certificate for the radical part of polynomials:
  `k` is the radical of `f` if `k ∣ f`, there is `n` such that `f ∣ k ^ n `,
  and `k` and the derivative of `k` are coprime. -/
lemma isRadicalPart_of_coprime_derivative_of_dvd_of_dvd_pow {K : Type*} [CommSemiring K]
    (f k : Polynomial K)
    (h : k ∣ f) (h2 : ∃ n : ℕ, f ∣ k ^ n) (h3 : ∃ a b, a * k + b * derivative k = 1) :
    IsRadicalPart k f := by
  rw [← Polynomial.separable_def'] at h3
  refine isRadicalPart_of_dvd_pow (Polynomial.Separable.squarefree h3) h h2

/-- If a polynomial is coprime with its derivative, then it is its own radical. -/
lemma self_isRadicalPart_of_gcd_unit {K : Type*} [CommSemiring K] (f : Polynomial K)
    (hgcd : IsCoprime f (derivative f)) : IsRadicalPart f f := by
  refine isRadicalPart_of_coprime_derivative_of_dvd_of_dvd_pow f f (dvd_refl f) ?_ ?_
  · use 1
    simp only [pow_one, dvd_refl]
  · exact hgcd

/-- If a polynomial has positive degree, then its radical part also has positive degree· -/
lemma degree_ne_zero_of_isRadicalPart_of_degree_ne_zero {K : Type*} [CommRing K] [IsDomain K]
    [UniqueFactorizationMonoid K] (f g : Polynomial K)
    (hdeg : f.natDegree ≠ 0) (hrad : IsRadicalPart g f) : g.natDegree ≠ 0 := by
  by_contra hc
  haveI : NormalizationMonoid K[X] := UniqueFactorizationMonoid.normalizationMonoid
  have hfz : f ≠ 0 := Ne.symm (ne_of_apply_ne natDegree fun a => hdeg (id (Eq.symm a)))
  choose n hn using (dvd_pow_of_isRadicalPart hfz hrad)
  have hgz : g ≠ 0 := by
    by_contra hcc
    rw [hcc] at hrad
    exact hfz (eq_zero_of_zero_dvd (isRadicalPart_dvd hrad))
  have := Polynomial.natDegree_le_of_dvd hn (pow_ne_zero _ hgz)
  simp only [natDegree_pow] at this
  rw [hc, mul_zero] at this
  exact hdeg (Nat.eq_zero_of_le_zero this)

/-- If the gcd of a polynomial `f` in `ZMod p` and its derivative is associated to an integer
coprime to `p`, then `f` is the radical of `f`· -/
lemma self_isRadicalPart_of_coprime {p n : ℕ}
    (f : Polynomial <| ZMod p) (hgcd : ∃ a b, a * f + b * (derivative f) = n)
    (hc : n.Coprime p) : IsRadicalPart f f := by
  have : Associated (n : Polynomial <| ZMod p) 1 := by
    rw [← C_eq_natCast, associated_one_iff_isUnit, Polynomial.isUnit_C]
    use ZMod.unitOfCoprime n hc; exact ZMod.coe_unitOfCoprime n hc
  obtain ⟨k, hk⟩:= this
  obtain ⟨a', b', hab'⟩ := hgcd
  refine isRadicalPart_of_coprime_derivative_of_dvd_of_dvd_pow f f (dvd_refl f) ?_ ?_
  · use 1
    simp only [pow_one, dvd_refl]
  · use (k * a'), (k * b')
    rw [mul_assoc, mul_assoc, ← mul_add, hab', mul_comm, hk]

/-- A more general version of `self_isRadicalPart_of_coprime` -/
lemma self_isRadicalPart_of_coprime_ideal {K R : Type*} [CommRing R] [CommRing K]
    {n : R} (g : R →+* K) (P : Ideal R) (hgker : RingHom.ker g = P)
    (f : Polynomial K) (hgcd : ∃ a b, a * f + b * (derivative f) = C (g n))
    (hc : IsCoprime (Ideal.span {n}) P) : IsRadicalPart f f := by
  have : IsUnit (g n) := by
    obtain ⟨a, ha, b, hb, hab⟩ := IsCoprime.exists hc
    replace ⟨k, hk⟩ := Ideal.mem_span_singleton.1 ha
    apply_fun g at hab
    simp only [hk, map_add, map_mul, map_one] at hab
    have : g b = 0 := by
      rw [← RingHom.mem_ker, hgker ]
      exact hb
    rw [this,  add_zero] at hab
    exact IsUnit.of_mul_eq_one _ hab
  refine self_isRadicalPart_of_gcd_unit f ?_
  obtain ⟨k, hk⟩ := (isUnit_iff_dvd_one).1 this
  obtain ⟨a', b', hab'⟩ := hgcd
  use (C k * a'), (C k * b')
  rw [mul_assoc, mul_assoc, ← mul_add, hab', mul_comm, ← C_mul, ← hk, map_one]

/-- A specialized version of `self_isRadicalPart_of_coprime_ideal` -/
lemma self_isRadicalPart_of_coprime' {K R : Type*} [CommRing R] [CommRing K]
    {π n : R}
    (g : R →+* K) (hgker : RingHom.ker g = Ideal.span {π})
    (f : Polynomial K) (hgcd : ∃ a b, a * f + b * (derivative f) = C (g n))
    (hc : IsCoprime n π) : IsRadicalPart f f := by
  refine self_isRadicalPart_of_coprime_ideal g (Ideal.span {π}) hgker f hgcd ?_
  rw [Ideal.isCoprime_span_singleton_iff]
  exact hc

/-- If `f` is a polynomial in `ZMod p` with derivative `0`,
then the radical part of `f` is the radical part of the `p`-th root of `f`· -/
lemma radical_pth_power {p : ℕ} [hp : Fact <| Nat.Prime p] (f g : Polynomial <| ZMod p)
    (h1 : derivative f = 0) (h2 : IsRadicalPart g (Polynomial.contract p f)) :
    IsRadicalPart g f := by
  rw [← Polynomial.expand_contract p h1 (Nat.Prime.ne_zero hp.out)]
  have : expand (ZMod p) p (contract p f) = contract p f ^ p := by
    rw [ZMod.expand_card (Polynomial.contract p f)]
  rw [this]
  exact isRadicalPart_pow_of_isRadicalPart (Nat.Prime.ne_zero hp.out) h2
