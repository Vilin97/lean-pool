/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.RiemannRoch.SeparableRelNorm
import Mathlib.FieldTheory.IsSepClosed

/-!
# Finite-extension norm and place-count formula

For a finite torsion-free extension of Dedekind domains, this file identifies
the exponent of the relative norm of an integral ideal at a height-one prime
with the inertia-degree-weighted sum of the ideal's exponents at all primes
above it.  The principal-integral specialization gives the corresponding
formula for `Algebra.intNorm`.

This is the finite-place norm bridge needed to pass from the rational-function
field product formula to a finite function-field extension.  The final theorem
clears a denominator to extend the identity to arbitrary elements of the
fraction field.  Places at infinity are treated separately.
-/

open scoped nonZeroDivisors
open IsDedekindDomain UniqueFactorizationMonoid

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

namespace BGS.CorvajaZannier

noncomputable section


section PrimeOver

variable {R S : Type*} [CommRing R] [IsDomain R]
  [CommRing S] [IsDomain S] [Algebra R S] [Module.IsTorsionFree R S]

/-- A prime of `S` over a height-one prime of `R`, regarded as a height-one
prime of `S`. -/
def primeOverHeightOne (p : HeightOneSpectrum R)
    (P : p.asIdeal.primesOver S) : HeightOneSpectrum S where
  asIdeal := P.1
  isPrime := P.2.1
  ne_bot := Ideal.ne_bot_of_mem_primesOver p.ne_bot P.2

@[simp]
theorem primeOverHeightOne_asIdeal (p : HeightOneSpectrum R)
    (P : p.asIdeal.primesOver S) :
    (primeOverHeightOne p P).asIdeal = P.1 := rfl

end PrimeOver

section RelativeNorm

variable {R S : Type*} [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]
  [Module.IsTorsionFree R S]
  [Algebra.IsSeparable (FractionRing R) (FractionRing S)]

local instance relativeNormFractionRingFiniteDimensional :
    FiniteDimensional (FractionRing R) (FractionRing S) :=
  Module.Finite.of_isLocalization R S R⁰

local notation3 "K" => FractionRing R
local notation3 "L" => FractionRing S

/-- The maximal-prime relative-norm formula needs separability of the actual
fraction-field extension, not perfectness of the base fraction field.  The
normal-closure proof is the same as Mathlib's
`Ideal.relNorm_eq_pow_of_isMaximal`, with that sharper hypothesis. -/
private theorem relNorm_eq_pow_of_isMaximal_of_isSeparable
    (P : Ideal S) (p : Ideal R) [P.LiesOver p]
    [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ P.inertiaDeg R := by
  exact Ideal.relNorm_eq_pow_of_isMaximal_of_isSeparable P p

private theorem count_relNorm_heightOne_of_liesOver (p : HeightOneSpectrum R)
    (Q : HeightOneSpectrum S) (hQp : Q.asIdeal.LiesOver p.asIdeal) :
    FractionalIdeal.count (FractionRing R) p
        (Ideal.relNorm R Q.asIdeal :
          FractionalIdeal R⁰ (FractionRing R)) =
      Q.asIdeal.inertiaDeg R := by
  classical
  have hpmax : p.asIdeal.IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime p.ne_bot p.isPrime
  have hQmax : Q.asIdeal.IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime Q.ne_bot Q.isPrime
  letI : Q.asIdeal.LiesOver p.asIdeal := hQp
  rw [relNorm_eq_pow_of_isMaximal_of_isSeparable Q.asIdeal p.asIdeal]
  rw [FractionalIdeal.coeIdeal_pow]
  simp [FractionalIdeal.count_pow, FractionalIdeal.count_self]

private theorem count_relNorm_heightOne_of_not_liesOver
    (p : HeightOneSpectrum R) (Q : HeightOneSpectrum S)
    (hQp : ¬ Q.asIdeal.LiesOver p.asIdeal) :
    FractionalIdeal.count (FractionRing R) p
        (Ideal.relNorm R Q.asIdeal :
          FractionalIdeal R⁰ (FractionRing R)) = 0 := by
  classical
  let q : HeightOneSpectrum R := HeightOneSpectrum.under R Q
  have hqmax : q.asIdeal.IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime q.ne_bot q.isPrime
  have hQmax : Q.asIdeal.IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime Q.ne_bot Q.isPrime
  have hQq : Q.asIdeal.LiesOver q.asIdeal := by
    change Q.asIdeal.LiesOver (Q.asIdeal.under R)
    infer_instance
  have hqp : q ≠ p := by
    intro heq
    apply hQp
    rw [← heq]
    exact hQq
  letI : Q.asIdeal.LiesOver q.asIdeal := hQq
  rw [relNorm_eq_pow_of_isMaximal_of_isSeparable Q.asIdeal q.asIdeal]
  rw [FractionalIdeal.coeIdeal_pow]
  rw [FractionalIdeal.count_pow,
    FractionalIdeal.count_maximal_coprime (FractionRing R) p hqp]
  simp

/-- The finite-prime exponent of the relative norm of an integral ideal is
the residue-degree-weighted sum of its exponents at primes above it. -/
theorem count_relNorm_eq_sum_inertiaDeg_mul_count
    (p : HeightOneSpectrum R) [Fintype (p.asIdeal.primesOver S)]
    (I : Ideal S) :
    FractionalIdeal.count (FractionRing R) p
        (Ideal.relNorm R I : FractionalIdeal R⁰ (FractionRing R)) =
      ∑ P : p.asIdeal.primesOver S,
        (P.1.inertiaDeg R : ℤ) *
          FractionalIdeal.count (FractionRing S) (primeOverHeightOne p P)
            (I : FractionalIdeal S⁰ (FractionRing S)) := by
  classical
  let property : Ideal S → Prop := fun J ↦
    FractionalIdeal.count (FractionRing R) p
        (Ideal.relNorm R J : FractionalIdeal R⁰ (FractionRing R)) =
      ∑ P : p.asIdeal.primesOver S,
        (P.1.inertiaDeg R : ℤ) *
          FractionalIdeal.count (FractionRing S) (primeOverHeightOne p P)
            (J : FractionalIdeal S⁰ (FractionRing S))
  by_cases hI : I = ⊥
  · subst hI
    simp [FractionalIdeal.count_zero]
  rw [← Ideal.prod_normalizedFactors_eq_self hI]
  refine Multiset.prod_induction property (normalizedFactors I) ?_ ?_ ?_
  · intro A B hA hB
    by_cases hA0 : A = ⊥
    · subst hA0
      simp [property, FractionalIdeal.count_zero]
    by_cases hB0 : B = ⊥
    · subst hB0
      simp [property, FractionalIdeal.count_zero]
    simp only [property, map_mul, FractionalIdeal.coeIdeal_mul]
    rw [FractionalIdeal.count_mul _ _
      (FractionalIdeal.coeIdeal_ne_zero.mpr
        (Ideal.relNorm_eq_bot_iff.not.mpr hA0))
      (FractionalIdeal.coeIdeal_ne_zero.mpr
        (Ideal.relNorm_eq_bot_iff.not.mpr hB0)), hA, hB]
    simp_rw [FractionalIdeal.count_mul _ _
      (FractionalIdeal.coeIdeal_ne_zero.mpr hA0)
      (FractionalIdeal.coeIdeal_ne_zero.mpr hB0), mul_add]
    exact Finset.sum_add_distrib.symm
  · simp [property, FractionalIdeal.count_one]
  · intro Q hQ
    have hQ0 : Q ≠ ⊥ :=
      UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hQ
    rw [Ideal.mem_normalizedFactors_iff hI] at hQ
    let q : HeightOneSpectrum S := ⟨Q, hQ.1, hQ0⟩
    dsimp only [property]
    by_cases hQp : Q.LiesOver p.asIdeal
    · rw [count_relNorm_heightOne_of_liesOver p q hQp]
      let P : p.asIdeal.primesOver S := ⟨Q, hQ.1, hQp⟩
      rw [Finset.sum_eq_single P]
      · have heq : primeOverHeightOne p P = q := by
          apply HeightOneSpectrum.ext
          rfl
        rw [heq]
        have hcount :
            FractionalIdeal.count (FractionRing S) q
                (Q : FractionalIdeal S⁰ (FractionRing S)) = 1 := by
          change FractionalIdeal.count (FractionRing S) q
              (q.asIdeal : FractionalIdeal S⁰ (FractionRing S)) = 1
          exact FractionalIdeal.count_self (FractionRing S) q
        rw [hcount, mul_one]
      · intro P' _ hP'
        have hne : primeOverHeightOne p P' ≠ q := by
          intro heq
          apply hP'
          apply Subtype.ext
          exact HeightOneSpectrum.ext_iff.mp heq
        have hcount :
            FractionalIdeal.count (FractionRing S) (primeOverHeightOne p P')
                (Q : FractionalIdeal S⁰ (FractionRing S)) = 0 := by
          change FractionalIdeal.count (FractionRing S) (primeOverHeightOne p P')
              (q.asIdeal : FractionalIdeal S⁰ (FractionRing S)) = 0
          exact FractionalIdeal.count_maximal_coprime
            (FractionRing S) (primeOverHeightOne p P') hne.symm
        rw [hcount, mul_zero]
      · intro hP
        exact (hP (Finset.mem_univ P)).elim
    · rw [count_relNorm_heightOne_of_not_liesOver p q hQp]
      symm
      apply Finset.sum_eq_zero
      intro P _
      have hne : primeOverHeightOne p P ≠ q := by
        intro heq
        apply hQp
        have hPQ : P.1 = Q := HeightOneSpectrum.ext_iff.mp heq
        rw [← hPQ]
        exact P.2.2
      have hcount :
          FractionalIdeal.count (FractionRing S) (primeOverHeightOne p P)
              (Q : FractionalIdeal S⁰ (FractionRing S)) = 0 := by
        change FractionalIdeal.count (FractionRing S) (primeOverHeightOne p P)
            (q.asIdeal : FractionalIdeal S⁰ (FractionRing S)) = 0
        exact FractionalIdeal.count_maximal_coprime
          (FractionRing S) (primeOverHeightOne p P) hne.symm
      rw [hcount, mul_zero]

/-- For an integral element, the finite-place order of its integral norm is
the residue-degree-weighted sum of the principal orders above the place. -/
theorem count_spanSingleton_intNorm_eq_sum_inertiaDeg_mul_count
    (p : HeightOneSpectrum R) [Fintype (p.asIdeal.primesOver S)]
    (x : S) :
    FractionalIdeal.count (FractionRing R) p
        (FractionalIdeal.spanSingleton R⁰
          (algebraMap R (FractionRing R) (Algebra.intNorm R S x))) =
      ∑ P : p.asIdeal.primesOver S,
        (P.1.inertiaDeg R : ℤ) *
          FractionalIdeal.count (FractionRing S) (primeOverHeightOne p P)
            (FractionalIdeal.spanSingleton S⁰
              (algebraMap S (FractionRing S) x)) := by
  simpa only [Ideal.relNorm_singleton,
    FractionalIdeal.coeIdeal_span_singleton] using
    count_relNorm_eq_sum_inertiaDeg_mul_count p (Ideal.span {x})

/-- The same principal-integral identity with the field norm written
explicitly in the fraction fields. -/
theorem count_spanSingleton_norm_algebraMap_eq_sum_inertiaDeg_mul_count
    (p : HeightOneSpectrum R) [Fintype (p.asIdeal.primesOver S)]
    (x : S) :
    FractionalIdeal.count (FractionRing R) p
        (FractionalIdeal.spanSingleton R⁰
          (Algebra.norm (FractionRing R)
            (algebraMap S (FractionRing S) x))) =
      ∑ P : p.asIdeal.primesOver S,
        (P.1.inertiaDeg R : ℤ) *
          FractionalIdeal.count (FractionRing S) (primeOverHeightOne p P)
            (FractionalIdeal.spanSingleton S⁰
              (algebraMap S (FractionRing S) x)) := by
  simpa only [Algebra.algebraMap_intNorm_fractionRing] using
    count_spanSingleton_intNorm_eq_sum_inertiaDeg_mul_count p x

/-- For an arbitrary fraction-field element, the finite-place order of its
field norm is the residue-degree-weighted sum of its principal orders at the
places above the given base place. -/
theorem count_spanSingleton_norm_eq_sum_inertiaDeg_mul_count
    (p : HeightOneSpectrum R) [Fintype (p.asIdeal.primesOver S)]
    (x : FractionRing S) :
    FractionalIdeal.count (FractionRing R) p
        (FractionalIdeal.spanSingleton R⁰
          (Algebra.norm (FractionRing R) x)) =
      ∑ P : p.asIdeal.primesOver S,
        (P.1.inertiaDeg R : ℤ) *
          FractionalIdeal.count (FractionRing S) (primeOverHeightOne p P)
            (FractionalIdeal.spanSingleton S⁰ x) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective S x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  by_cases ha0 : a = 0
  · subst a
    simp [FractionalIdeal.count_zero]
  have hma0 : algebraMap S (FractionRing S) a ≠ 0 := by simp [ha0]
  have hmb0 : algebraMap S (FractionRing S) b ≠ 0 := by simp [hb0]
  have hna0 : Algebra.norm (FractionRing R)
      (algebraMap S (FractionRing S) a) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hma0
  have hnb0 : Algebra.norm (FractionRing R)
      (algebraMap S (FractionRing S) b) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hmb0
  have hcount (q : HeightOneSpectrum S) :
      FractionalIdeal.count (FractionRing S) q
          (FractionalIdeal.spanSingleton S⁰
            (algebraMap S (FractionRing S) a *
              (algebraMap S (FractionRing S) b)⁻¹)) =
        FractionalIdeal.count (FractionRing S) q
            (FractionalIdeal.spanSingleton S⁰
              (algebraMap S (FractionRing S) a)) -
          FractionalIdeal.count (FractionRing S) q
            (FractionalIdeal.spanSingleton S⁰
              (algebraMap S (FractionRing S) b)) := by
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
      ← FractionalIdeal.spanSingleton_inv,
      FractionalIdeal.count_mul _ _
        ((FractionalIdeal.spanSingleton_ne_zero_iff).2 hma0)
        (inv_ne_zero ((FractionalIdeal.spanSingleton_ne_zero_iff).2 hmb0)),
      FractionalIdeal.count_inv]
    simp [sub_eq_add_neg]
  rw [div_eq_mul_inv, map_mul, Algebra.norm_inv,
    ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    ← FractionalIdeal.spanSingleton_inv]
  rw [FractionalIdeal.count_mul _ _
    ((FractionalIdeal.spanSingleton_ne_zero_iff).2 hna0)
    (inv_ne_zero ((FractionalIdeal.spanSingleton_ne_zero_iff).2 hnb0)),
    FractionalIdeal.count_inv]
  simp_rw [hcount, mul_sub]
  rw [count_spanSingleton_norm_algebraMap_eq_sum_inertiaDeg_mul_count p a,
    count_spanSingleton_norm_algebraMap_eq_sum_inertiaDeg_mul_count p b,
    Finset.sum_sub_distrib]
  simp [sub_eq_add_neg]

end RelativeNorm

end

end BGS.CorvajaZannier
