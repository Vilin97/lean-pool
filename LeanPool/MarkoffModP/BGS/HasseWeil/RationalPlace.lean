/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionPrincipalDivisor
import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Degree-one places of a finite function field

This file defines the actual degree-one place type used by the fixed-field
argument and proves that it is finite over a finite constant field.  The proof
does not assume a point-count bound: finite degree-one places inject into the
finite family of linear base primes together with their finite lying-over
fibers, while the places above infinity already form a finite lying-over
fiber.
-/

open scoped Polynomial

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier
open IsDedekindDomain

variable (K : Type*) [Field K] [DecidableEq K]

/-- Degree-one finite places of the rational function field `K(t)`. -/
abbrev RatFuncRationalFinitePlace :=
  {P : HeightOneSpectrum K[X] // ratFuncFinitePlaceDegree P = 1}

/-- Embed a degree-one rational-function-field place into the finite
coefficient space of polynomials of degree less than two. -/
def ratFuncRationalFinitePlaceToDegreeLT :
    RatFuncRationalFinitePlace K → Polynomial.degreeLT K 2 := fun P => by
  let r := finitePlaceNormalizedPrime P.1
  refine ⟨(r : K[X]), Polynomial.mem_degreeLT.mpr ?_⟩
  have hr0 : (r : K[X]) ≠ 0 := r.property.1.ne_zero
  have hrDegree : (r : K[X]).natDegree = 1 := by
    simpa only [ratFuncFinitePlaceDegree] using P.2
  rw [Polynomial.degree_eq_natDegree hr0, hrDegree]
  exact WithBot.coe_lt_coe.mpr (by omega)

theorem ratFuncRationalFinitePlaceToDegreeLT_injective :
    Function.Injective (ratFuncRationalFinitePlaceToDegreeLT K) := by
  intro P Q hPQ
  apply Subtype.ext
  have hr : finitePlaceNormalizedPrime P.1 = finitePlaceNormalizedPrime Q.1 := by
    apply Subtype.ext
    exact congrArg
      (fun r : Polynomial.degreeLT K 2 => (r.1 : K[X])) hPQ
  simpa only [normalizedPrimeFinitePlace_finitePlaceNormalizedPrime] using
    congrArg (normalizedPrimeFinitePlace (K := K)) hr

/-- There are finitely many degree-one finite places of `K(t)` when `K` is
finite. -/
noncomputable instance ratFuncRationalFinitePlace_finite [Finite K] :
    Finite (RatFuncRationalFinitePlace K) := by
  let : Finite (Fin 2 → K) := Pi.finite
  let : Finite (Polynomial.degreeLT K 2) :=
    Finite.of_equiv (Fin 2 → K) (Polynomial.degreeLTEquiv K 2).toEquiv.symm
  exact Finite.of_injective (ratFuncRationalFinitePlaceToDegreeLT K)
    (ratFuncRationalFinitePlaceToDegreeLT_injective K)

variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]
  [DecidableEq (RatFunc K)]

local instance (priority := 10) rationalPlacePolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance rationalPlacePolynomialScalarTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance rationalPlaceFiniteClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance rationalPlaceFiniteClosureIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance rationalPlacePolynomialTorsionFreeTop :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance rationalPlaceFiniteClosureTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance rationalPlaceFiniteClosureDedekind :
    IsDedekindDomain (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain K[X] (RatFunc K) L
    (RatFuncFiniteIntegralClosure K L)

local instance rationalPlaceInfinityClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance rationalPlaceInfinityClosureIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

local instance rationalPlaceInfinityClosureTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance rationalPlaceInfinityClosureDedekind :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain (RatFuncInfinityIntegers K)
    (RatFunc K) L (RatFuncInfinityIntegralClosure K L)

/-- Degree-one finite places of a finite extension of `K(t)`. -/
abbrev FiniteExtensionRationalFinitePlace :=
  {Q : FiniteExtensionFinitePlace K L //
    finiteExtensionPlaceDegree K L (.inl Q) = 1}

/-- Degree-one places above infinity of a finite extension of `K(t)`. -/
abbrev FiniteExtensionRationalInfinityPlace :=
  {Q : FiniteExtensionInfinityPlace K L //
    finiteExtensionPlaceDegree K L (.inr Q) = 1}

/-- The exhaustive type of degree-one places of a finite extension of
`K(t)`, split into the finite and above-infinity parts. -/
abbrev FiniteExtensionRationalPlace :=
  FiniteExtensionRationalFinitePlace K L ⊕
    FiniteExtensionRationalInfinityPlace K L

/-- The split rational-place type is exactly the subtype of exhaustive places
whose place degree is one. -/
def finiteExtensionRationalPlaceEquivSubtype :
    FiniteExtensionRationalPlace K L ≃
      {P : FiniteExtensionPlace K L //
        finiteExtensionPlaceDegree K L P = 1} where
  toFun
    | .inl P => ⟨.inl P.1, P.2⟩
    | .inr P => ⟨.inr P.1, P.2⟩
  invFun
    | ⟨.inl Q, hQ⟩ => .inl ⟨Q, hQ⟩
    | ⟨.inr Q, hQ⟩ => .inr ⟨Q, hQ⟩
  left_inv P := by cases P <;> rfl
  right_inv P := by rcases P with ⟨P, hP⟩; cases P <;> rfl

/-- The number of degree-one places of the finite function field. -/
def finiteExtensionRationalPlaceCount : ℕ :=
  Nat.card (FiniteExtensionRationalPlace K L)

theorem finiteExtensionRationalPlaceCount_eq_natCard_subtype :
    finiteExtensionRationalPlaceCount K L =
      Nat.card {P : FiniteExtensionPlace K L //
        finiteExtensionPlaceDegree K L P = 1} :=
  Nat.card_congr (finiteExtensionRationalPlaceEquivSubtype K L)

private theorem rationalFinitePlace_baseDegree_eq_one
    (Q : FiniteExtensionRationalFinitePlace K L) :
    ratFuncFinitePlaceDegree (HeightOneSpectrum.under K[X] Q.1) = 1 := by
  have hprod :
      Q.1.asIdeal.inertiaDeg K[X] *
          ratFuncFinitePlaceDegree (HeightOneSpectrum.under K[X] Q.1) = 1 := by
    simpa only [finiteExtensionPlaceDegree] using Q.2
  exact Nat.eq_one_of_dvd_one ⟨Q.1.asIdeal.inertiaDeg K[X], by
    simpa only [Nat.mul_comm] using hprod.symm⟩

/-- A rational finite place determines a rational base place together with a
prime in its finite lying-over fiber. -/
def rationalFinitePlaceToBaseFiber
    (Q : FiniteExtensionRationalFinitePlace K L) :
    Σ P : RatFuncRationalFinitePlace K,
      P.1.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L) :=
  ⟨⟨HeightOneSpectrum.under K[X] Q.1,
      rationalFinitePlace_baseDegree_eq_one K L Q⟩,
    ⟨Q.1.asIdeal, Q.1.isPrime, ⟨rfl⟩⟩⟩

theorem rationalFinitePlaceToBaseFiber_injective :
    Function.Injective (rationalFinitePlaceToBaseFiber K L) := by
  intro Q R hQR
  apply Subtype.ext
  apply HeightOneSpectrum.ext
  have hIdeals := congrArg
    (fun z : Σ P : RatFuncRationalFinitePlace K,
      P.1.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L) => z.2.1) hQR
  simpa only [rationalFinitePlaceToBaseFiber] using hIdeals

/-- The degree-one finite places of a finite function field are finite over a
finite constant field. -/
noncomputable instance finiteExtensionRationalFinitePlace_finite [Finite K] :
    Finite (FiniteExtensionRationalFinitePlace K L) := by
  let : Fintype (RatFuncRationalFinitePlace K) := Fintype.ofFinite _
  let (P : RatFuncRationalFinitePlace K) :
      Fintype (P.1.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L)) :=
    Set.Finite.fintype (IsDedekindDomain.primesOver_finite P.1.asIdeal
      (RatFuncFiniteIntegralClosure K L))
  exact Finite.of_injective (rationalFinitePlaceToBaseFiber K L)
    (rationalFinitePlaceToBaseFiber_injective K L)

/-- The degree-one places above infinity are finite. -/
noncomputable instance finiteExtensionRationalInfinityPlace_finite :
    Finite (FiniteExtensionRationalInfinityPlace K L) := by
  let : Fintype (FiniteExtensionInfinityPlace K L) :=
    Set.Finite.fintype (IsDedekindDomain.primesOver_finite
      (ratFuncInfinityPlace K).asIdeal
      (RatFuncInfinityIntegralClosure K L))
  infer_instance

/-- The exhaustive degree-one place type is finite over a finite constant
field. -/
noncomputable instance finiteExtensionRationalPlace_finite [Finite K] :
    Finite (FiniteExtensionRationalPlace K L) := inferInstance

end

end BGS.HasseWeil
