/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NumberField.SchurPrimeDivisors
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NumberField.IntegralPrimitiveElement
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.FiniteRamifiedPrimes
public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.ZMod.Basic

/-! # Degree One Primes -/

@[expose] public section
open scoped NumberField
open NumberField IsDedekindDomain Polynomial

namespace AlgebraicNumberTheory.PrimeSelection

/-- A good prime divisor of a primitive polynomial value gives an actual
prime ideal whose residue degree is one. -/
theorem exists_degreeOnePrime_of_dvd_minpoly_eval
    (K : Type*) [Field K] [NumberField K]
    (θ : 𝓞 K) (q : ℕ) [Fact q.Prime]
    (hGood : ¬ q ∣ RingOfIntegers.exponent θ)
    (n : ℤ) (hn : (q : ℤ) ∣ (minpoly ℤ θ).eval n) :
    ∃ P : Ideal (𝓞 K), P.IsPrime ∧
      P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) ∧
      P.inertiaDeg ℤ = 1 := by
  classical
  let f : (ZMod q)[X] := (minpoly ℤ θ).map (Int.castRingHom (ZMod q))
  have hf : f ≠ 0 := Polynomial.map_monic_ne_zero (minpoly.monic θ.isIntegral)
  have hn0 : f.eval (n : ZMod q) = 0 := by
    dsimp only [f]
    rw [Polynomial.eval_map]
    change (minpoly ℤ θ).eval₂ (Int.castRingHom (ZMod q))
      ((Int.castRingHom (ZMod q)) n) = 0
    rw [Polynomial.eval₂_at_apply]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hn
  have hFactor : X - C (n : ZMod q) ∈ RingOfIntegers.monicFactorsMod θ q := by
    change X - C (n : ZMod q) ∈ (UniqueFactorizationMonoid.normalizedFactors f).toFinset
    rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hf]
    exact ⟨Polynomial.irreducible_X_sub_C _, Polynomial.monic_X_sub_C _,
      Polynomial.dvd_iff_isRoot.mpr hn0⟩
  let P := (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hGood).symm
    ⟨X - C (n : ZMod q), hFactor⟩
  refine ⟨P, P.prop.1, P.prop.2, ?_⟩
  simpa only [Polynomial.natDegree_X_sub_C] using
    NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
      hGood hFactor

/-- Every number field has an unramified prime of residue degree one above a
new rational prime, outside an arbitrary finite set. -/
theorem exists_unramified_degreeOnePrime_not_mem
    (K : Type*) [Field K] [NumberField K] (bad : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ bad ∧
      ∃ W : HeightOneSpectrum (𝓞 K),
        W.asIdeal.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) ∧
        W.asIdeal.inertiaDeg ℤ = 1 ∧ Algebra.IsUnramifiedAt ℤ W.asIdeal := by
  classical
  obtain ⟨θ, hθ⟩ := exists_integral_primitive_element K
  have hExp : RingOfIntegers.exponent θ ≠ 0 := integralPrimitive_exponent_ne_zero K θ hθ
  let : Algebra (FractionRing ℤ) (FractionRing (𝓞 K)) :=
    FractionRing.liftAlgebra ℤ (FractionRing (𝓞 K))
  have hRam := AlgebraicNumberTheory.Ramification.finite_ramified_heightOne_primes ℤ (𝓞 K)
  have hRamFinite := hRam.image
    (fun W : HeightOneSpectrum (𝓞 K) => Ideal.absNorm (W.asIdeal.under ℤ))
  let ram : Finset ℕ := hRamFinite.toFinset
  obtain ⟨q, hq, hqBad, n, _, hqn⟩ := exists_prime_not_mem_dvd_eval
    (minpoly ℤ θ) (minpoly.natDegree_pos θ.isIntegral).ne'
    (bad ∪ (RingOfIntegers.exponent θ).divisors ∪ ram)
  have : Fact q.Prime := ⟨hq⟩
  have hGood : ¬ q ∣ RingOfIntegers.exponent θ := by
    intro hdiv
    apply hqBad
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (Nat.mem_divisors.mpr ⟨hdiv, hExp⟩))
  obtain ⟨P, hP, hOver, hf⟩ := exists_degreeOnePrime_of_dvd_minpoly_eval K θ q hGood n hqn
  have : P.IsPrime := hP
  have : P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := hOver
  have : (Ideal.span ({(q : ℤ)} : Set ℤ)).IsMaximal := Int.ideal_span_isMaximal_of_prime q
  have : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span ({(q : ℤ)} : Set ℤ))
  let W : HeightOneSpectrum (𝓞 K) := ⟨P, hP, NeZero.ne P⟩
  refine ⟨q, hq, ?_, W, hOver, hf, ?_⟩
  · intro hqb
    exact hqBad (Finset.mem_union_left _ (Finset.mem_union_left _ hqb))
  · by_contra hU
    apply hqBad
    apply Finset.mem_union_right
    apply hRamFinite.mem_toFinset.mpr
    refine ⟨W, hU, ?_⟩
    change Ideal.absNorm (P.under ℤ) = q
    rw [← Ideal.over_def P (Ideal.span ({(q : ℤ)} : Set ℤ)),
      Ideal.absNorm_span_natCast, Module.finrank_self, pow_one]

end AlgebraicNumberTheory.PrimeSelection
