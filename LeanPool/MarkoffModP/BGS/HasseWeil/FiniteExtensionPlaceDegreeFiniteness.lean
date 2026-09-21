/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionPlaceTower

/-!
# Finiteness of bounded-degree places

For a finite field `K`, there are only finitely many finite places of `K(X)`
of bounded degree: a place is represented by its normalized prime polynomial,
and a polynomial of bounded degree is determined by finitely many
coefficients.  A finite place in a finite function-field extension lies over
one of these base places, with only finitely many primes in each fiber.

This file proves the corresponding finiteness statements for base finite
places, finite places in an extension, and the exhaustive finite-plus-infinity
place type.  These are the local-finiteness inputs needed to define effective
divisor counts and Euler products without assuming zeta rationality.
-/

open scoped Polynomial

namespace BGS.HasseWeil

open BGS.CorvajaZannier

noncomputable section


/-- Finite fields have only finitely many finite rational-function places of
degree at most `n`. -/
theorem ratFuncFinitePlace_degree_le_finite
    (K : Type*) [Field K] [Fintype K] [DecidableEq K] (n : ℕ) :
    Finite {p : IsDedekindDomain.HeightOneSpectrum K[X] //
      ratFuncFinitePlaceDegree p ≤ n} := by
  let f : {p : IsDedekindDomain.HeightOneSpectrum K[X] //
      ratFuncFinitePlaceDegree p ≤ n} → Fin (n + 1) → K :=
    fun p i => (finitePlaceNormalizedPrime p.1 : K[X]).coeff i
  apply Finite.of_injective f
  intro p q hpq
  apply Subtype.ext
  have hr : finitePlaceNormalizedPrime p.1 =
      finitePlaceNormalizedPrime q.1 := by
    apply Subtype.ext
    apply Polynomial.ext
    intro m
    by_cases hm : m ≤ n
    · exact congrFun hpq ⟨m, Nat.lt_succ_iff.mpr hm⟩
    · have hnm : n < m := Nat.lt_of_not_ge hm
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt p.2 hnm),
        Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt q.2 hnm)]
  calc
    p.1 = normalizedPrimeFinitePlace (K := K)
        (finitePlaceNormalizedPrime p.1) :=
      (normalizedPrimeFinitePlace_finitePlaceNormalizedPrime p.1).symm
    _ = normalizedPrimeFinitePlace (K := K)
        (finitePlaceNormalizedPrime q.1) :=
      congrArg (normalizedPrimeFinitePlace (K := K)) hr
    _ = q.1 := normalizedPrimeFinitePlace_finitePlaceNormalizedPrime q.1

/-- A finite extension of `K(X)` has only finitely many finite places of
degree at most `n`. -/
theorem finiteExtensionFinitePlace_degree_le_finite
    (K L : Type*) [Field K] [Fintype K] [DecidableEq K]
    [DecidableEq (RatFunc K)] [Field L] [Algebra (RatFunc K) L]
    [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
    (n : ℕ) :
    Finite {q : FiniteExtensionFinitePlace K L //
      finiteExtensionPlaceDegree K L (.inl q) ≤ n} := by
  letI : Algebra K[X] L :=
    RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
      (algebraMap K[X] (RatFunc K)))
  letI : IsScalarTower K[X] (RatFunc K) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
    Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)
  letI : Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
    IsIntegralClosure.isIntegral_algebra K[X] L
  letI : Module.IsTorsionFree K[X] L :=
    Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L
  letI : Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
    IsIntegralClosure.isTorsionFree K[X] L
  let Base := {p : IsDedekindDomain.HeightOneSpectrum K[X] //
    ratFuncFinitePlaceDegree p ≤ n}
  let Fiber : Base → Type _ := fun p =>
    p.1.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L)
  letI : Finite Base := ratFuncFinitePlace_degree_le_finite K n
  letI : Fintype Base := Fintype.ofFinite Base
  letI (p : Base) : Fintype (Fiber p) := by
    dsimp only [Fiber]
    exact Set.Finite.fintype
      (IsDedekindDomain.primesOver_finite p.1.asIdeal
        (RatFuncFiniteIntegralClosure K L))
  let f : {q : FiniteExtensionFinitePlace K L //
      finiteExtensionPlaceDegree K L (.inl q) ≤ n} →
      Σ p : Base, Fiber p := fun q => by
    let p := IsDedekindDomain.HeightOneSpectrum.under K[X] q.1
    have hp : ratFuncFinitePlaceDegree p ≤ n := by
      apply (Nat.le_mul_of_pos_left _
        (Ideal.inertiaDeg_pos q.1.asIdeal K[X])).trans
      simpa only [finiteExtensionPlaceDegree, p] using q.2
    exact ⟨⟨p, hp⟩,
      (finitePlaceFiberEquivPrimesOver K L p) ⟨q.1, by simp [p]⟩⟩
  refine Finite.of_injective f ?_
  intro q r hqr
  apply Subtype.ext
  exact IsDedekindDomain.HeightOneSpectrum.ext
    (congrArg (fun z : Σ p : Base, Fiber p => z.2.1) hqr)

/-- A finite extension of `K(X)` has only finitely many exhaustive places of
degree at most `n`.  The finite branch is the preceding theorem; the branch
above the unique base infinity place is finite without a degree restriction. -/
theorem finiteExtensionPlace_degree_le_finite
    (K L : Type*) [Field K] [Fintype K] [DecidableEq K]
    [DecidableEq (RatFunc K)] [Field L] [Algebra (RatFunc K) L]
    [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
    (n : ℕ) :
    Finite {P : FiniteExtensionPlace K L //
      finiteExtensionPlaceDegree K L P ≤ n} := by
  let FinitePart := {q : FiniteExtensionFinitePlace K L //
    finiteExtensionPlaceDegree K L (.inl q) ≤ n}
  letI : Finite FinitePart :=
    finiteExtensionFinitePlace_degree_le_finite K L n
  letI : Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
    IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)
  letI : Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
    IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L
  letI : Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
    IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L
  letI : IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
    IsIntegralClosure.isDedekindDomain (RatFuncInfinityIntegers K)
      (RatFunc K) L (RatFuncInfinityIntegralClosure K L)
  letI : Fintype (FiniteExtensionInfinityPlace K L) :=
    Set.Finite.fintype
      (IsDedekindDomain.primesOver_finite
        (ratFuncInfinityPlace K).asIdeal
        (RatFuncInfinityIntegralClosure K L))
  let f : {P : FiniteExtensionPlace K L //
      finiteExtensionPlaceDegree K L P ≤ n} →
      FinitePart ⊕ FiniteExtensionInfinityPlace K L
    | ⟨.inl q, hq⟩ => .inl ⟨q, hq⟩
    | ⟨.inr Q, _⟩ => .inr Q
  refine Finite.of_injective f ?_
  intro P Q h
  apply Subtype.ext
  cases P with
  | mk P hP =>
    cases Q with
    | mk Q hQ =>
      cases P <;> cases Q <;> simp only [f, Sum.inl.injEq,
        Sum.inr.injEq, reduceCtorEq] at h ⊢
      · exact congrArg Subtype.val h
      · exact h

/-- A concrete finite type of exhaustive places of degree at most `n`. -/
@[implicit_reducible]
noncomputable def finiteExtensionPlaceDegreeLEFintype
    (K L : Type*) [Field K] [Fintype K] [DecidableEq K]
    [DecidableEq (RatFunc K)] [Field L] [Algebra (RatFunc K) L]
    [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
    (n : ℕ) :
    Fintype {P : FiniteExtensionPlace K L //
      finiteExtensionPlaceDegree K L P ≤ n} := by
  letI : Finite {P : FiniteExtensionPlace K L //
      finiteExtensionPlaceDegree K L P ≤ n} :=
    finiteExtensionPlace_degree_le_finite K L n
  exact Fintype.ofFinite _

end

end BGS.HasseWeil
