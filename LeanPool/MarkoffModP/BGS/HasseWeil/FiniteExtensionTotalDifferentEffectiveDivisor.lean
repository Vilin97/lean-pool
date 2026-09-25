/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionEffectiveDivisorSplit
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionCanonicalDifferentDivisor

/-!
# The total effective different divisor

This file packages the finite and above-infinity different multiplicities in
one exhaustive effective divisor, and identifies its weighted degree with the
sum of the two numerical different degrees already used by Riemann--Hurwitz.

Unlike the canonical divisor attached to `dX`, this effective divisor records
the total different itself: its infinity coefficients do not contain the
additional `-2e` correction coming from the pole of `dX`.
-/

@[expose] public section

open scoped BigOperators nonZeroDivisors Polynomial

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier IsDedekindDomain

variable (K : Type*) [Field K] [Finite K]
  [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance totalDifferentFintype : Fintype K := Fintype.ofFinite K

local instance (priority := 10) totalDifferentPolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance totalDifferentPolynomialScalarTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance totalDifferentFiniteIntegralClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance totalDifferentFiniteIntegralClosureIsIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance totalDifferentPolynomialTorsionFreeTop :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance totalDifferentFiniteIntegralClosureIsTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance totalDifferentInfinityIntegralClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance totalDifferentInfinityIntegralClosureIsIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

local instance totalDifferentInfinityTorsionFreeTop :
    Module.IsTorsionFree (RatFuncInfinityIntegers K) L :=
  Module.IsTorsionFree.trans_faithfulSMul
    (RatFuncInfinityIntegers K) (RatFunc K) L

local instance totalDifferentInfinityIntegralClosureIsTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance totalDifferentInfinityIntegralClosureIsDedekindDomain :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

local instance totalDifferentInfinityPlaceFintype :
    Fintype (FiniteExtensionInfinityPlace K L) :=
  Set.Finite.fintype
    (IsDedekindDomain.primesOver_finite
      (ratFuncInfinityPlace K).asIdeal
      (RatFuncInfinityIntegralClosure K L))

/-- The effective divisor whose coefficient at every exhaustive place is the
local multiplicity of the trace different. -/
def finiteExtensionTotalDifferentEffectiveDivisor :
    FiniteExtensionEffectiveDivisor K L :=
  (differentMultiplicityDivisor K[X]
      (RatFuncFiniteIntegralClosure K L)
      (finiteExtensionFiniteDifferentIdeal_ne_bot K L)).sumElim
    (Finsupp.equivFunOnFinite.symm fun P =>
      multiplicity P.1
        (differentIdeal (RatFuncInfinityIntegers K)
          (RatFuncInfinityIntegralClosure K L)))

omit [Finite K] [DecidableEq K] in
@[simp]
theorem finiteExtensionTotalDifferentEffectiveDivisor_inl
    (P : FiniteExtensionFinitePlace K L) :
    finiteExtensionTotalDifferentEffectiveDivisor K L (.inl P) =
      multiplicity P.asIdeal
        (differentIdeal K[X] (RatFuncFiniteIntegralClosure K L)) := by
  simp [finiteExtensionTotalDifferentEffectiveDivisor]

omit [Finite K] [DecidableEq K] in
@[simp]
theorem finiteExtensionTotalDifferentEffectiveDivisor_inr
    (P : FiniteExtensionInfinityPlace K L) :
    finiteExtensionTotalDifferentEffectiveDivisor K L (.inr P) =
      multiplicity P.1
        (differentIdeal (RatFuncInfinityIntegers K)
          (RatFuncInfinityIntegralClosure K L)) := by
  simp [finiteExtensionTotalDifferentEffectiveDivisor]

omit [Finite K] in
/-- The exhaustive effective different has degree equal to the finite
different degree plus the above-infinity different degree. -/
theorem finiteExtensionTotalDifferentEffectiveDivisor_degree :
    finiteExtensionEffectiveDivisorDegree K L
        (finiteExtensionTotalDifferentEffectiveDivisor K L) =
      finiteExtensionFiniteDifferentDegree K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L) +
        infinityDifferentDegree K L := by
  rw [finiteExtensionEffectiveDivisorDegree]
  rw [finiteExtensionTotalDifferentEffectiveDivisor, Finsupp.sum_sumElim]
  congr 1
  · rw [finiteExtensionFiniteDifferentDegree]
    apply Finsupp.sum_congr
    intro P _
    simp only [Function.comp_apply, finiteExtensionPlaceDegree]
    ac_rfl
  · rw [infinityDifferentDegree]
    rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
    apply Finset.sum_congr rfl
    intro P _
    simp only [Function.comp_apply, finiteExtensionPlaceDegree]
    simp
    ac_rfl

end

end BGS.HasseWeil
