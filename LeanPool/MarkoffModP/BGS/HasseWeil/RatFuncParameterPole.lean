/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindRamifiedDerivationScaling
import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionCanonicalDifferentDivisor
import LeanPool.MarkoffModP.BGS.HasseWeil.PoleDivisor
import Mathlib.Tactic

/-!
# The rational parameter's pole divisor in a finite extension

For a finite separable extension `L / K(X)`, the image of `RatFunc.X` is
integral at every finite place.  At a place `P` above infinity its order is
exactly `-e(P)`, because `X⁻¹` is the uniformizer of the base infinity place.
Consequently its complete pole divisor is supported exactly above infinity,
with coefficient `e(P)`, and its height is `[L : K(X)]` by the
ramification--inertia degree formula.

These statements do not require the constant field `K` to be finite.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open IsDedekindDomain
open scoped nonZeroDivisors Polynomial BigOperators

noncomputable section

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

variable (K : Type*) [Field K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance (priority := 10) ratFuncParameterPolynomialAlgebra :
    Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance ratFuncParameterPolynomialScalarTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance ratFuncParameterFiniteIntegralClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance ratFuncParameterFiniteIntegralClosureIsIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance ratFuncParameterPolynomialTorsionFreeTop :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance ratFuncParameterFiniteIntegralClosureIsTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance ratFuncParameterInfinityIntegralClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance ratFuncParameterInfinityIntegralClosureIsIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

local instance ratFuncParameterInfinityBaseTorsionFreeTop :
    Module.IsTorsionFree (RatFuncInfinityIntegers K) L :=
  Module.IsTorsionFree.trans_faithfulSMul
    (RatFuncInfinityIntegers K) (RatFunc K) L

local instance ratFuncParameterInfinityIntegralClosureIsTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance ratFuncParameterInfinityIntegralClosureIsDedekindDomain :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

local instance ratFuncParameterInfinityIntegralClosureIsFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

local instance ratFuncParameterInfinityPlaceFintype :
    Fintype (FiniteExtensionInfinityPlace K L) :=
  Set.Finite.fintype
    (IsDedekindDomain.primesOver_finite
      (ratFuncInfinityPlace K).asIdeal
      (RatFuncInfinityIntegralClosure K L))

/-- The rational parameter `X` is integral at every finite place. -/
theorem finiteExtensionPrincipalDivisor_ratFuncX_inl_nonnegative
    (q : FiniteExtensionFinitePlace K L) :
    0 ≤ finiteExtensionPrincipalDivisor K L
      (algebraMap (RatFunc K) L RatFunc.X) (.inl q) := by
  let S := RatFuncFiniteIntegralClosure K L
  let e := ratFuncFiniteIntegralClosureFractionRingEquiv K L
  let s : S := algebraMap K[X] S Polynomial.X
  have hs : s ≠ 0 := by
    have hinj : Function.Injective (algebraMap K[X] S) :=
      FunctionField.ringOfIntegers.algebraMap_injective K L
    dsimp only [s]
    exact (map_ne_zero_iff (algebraMap K[X] S) hinj).2 Polynomial.X_ne_zero
  have hrepr :
      e.symm (algebraMap (RatFunc K) L RatFunc.X) =
        algebraMap S (FractionRing S) s := by
    apply e.injective
    rw [e.apply_symm_apply, e.commutes]
    rfl
  rw [finiteExtensionPrincipalDivisor_inl, hrepr]
  exact finitePlaceOrder_algebraMap_nonnegative q s hs

private theorem finiteExtensionPrincipalDivisor_inr_eq_order
    (x : L) (P : FiniteExtensionInfinityPlace K L) :
    finiteExtensionPrincipalDivisor K L x (.inr P) =
      finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P) x := by
  rw [finiteExtensionPrincipalDivisor_inr]
  symm
  simpa [ratFuncInfinityIntegralClosureFractionRingEquiv] using
    fractionRingAlgEquiv_finitePlaceOrder_eq
      (R := RatFuncInfinityIntegralClosure K L) (L := L)
      (primeOverHeightOne (ratFuncInfinityPlace K) P)
      ((ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm x)

/-- At a place `P` above infinity, the rational parameter has order exactly
the negative ramification index. -/
theorem finiteExtensionPrincipalDivisor_ratFuncX_inr_eq_neg_ramificationIdx
    (P : FiniteExtensionInfinityPlace K L) :
    finiteExtensionPrincipalDivisor K L
        (algebraMap (RatFunc K) L RatFunc.X) (.inr P) =
      -(P.1.ramificationIdx (RatFuncInfinityIntegers K) : ℤ) := by
  let q := primeOverHeightOne (ratFuncInfinityPlace K) P
  let pi := ratFuncInfinityUniformizer K
  letI : q.asIdeal.LiesOver (ratFuncInfinityPlace K).asIdeal := by
    simpa [q] using
      (Ideal.primesOver.liesOver (ratFuncInfinityPlace K).asIdeal P)
  have hpi0 : pi ≠ 0 := by
    dsimp only [pi]
    intro hzero
    exact (ratFuncInfinityUniformizer_isUniformizer K).ne_zero
      (congrArg Subtype.val hzero)
  have hpiOrder : finitePlaceOrder q
      (algebraMap (RatFuncInfinityIntegralClosure K L) L
        (algebraMap (RatFuncInfinityIntegers K)
          (RatFuncInfinityIntegralClosure K L) pi)) =
      (P.1.ramificationIdx (RatFuncInfinityIntegers K) : ℤ) := by
    exact finitePlaceOrder_algebraMap_uniformizer_eq_ramificationIdx
      (ratFuncInfinityPlace K) q pi hpi0
        (ratFuncInfinityPlace_span_uniformizer K)
  have hpiImage : algebraMap
      (RatFuncInfinityIntegralClosure K L) L
        (algebraMap (RatFuncInfinityIntegers K)
          (RatFuncInfinityIntegralClosure K L) pi) =
        (algebraMap (RatFunc K) L RatFunc.X)⁻¹ := by
    change algebraMap (RatFunc K) L (1 / RatFunc.X) =
      (algebraMap (RatFunc K) L RatFunc.X)⁻¹
    simp
  have hX0 : algebraMap (RatFunc K) L RatFunc.X ≠ 0 := by
    simpa using (algebraMap (RatFunc K) L).injective.ne RatFunc.X_ne_zero
  have hinv := finitePlaceOrder_inv_eq_neg' q
    (algebraMap (RatFunc K) L RatFunc.X) hX0
  rw [← hpiImage, hpiOrder] at hinv
  rw [finiteExtensionPrincipalDivisor_inr_eq_order K L]
  change finitePlaceOrder q (algebraMap (RatFunc K) L RatFunc.X) = _
  omega

/-- The pole divisor of the rational parameter vanishes at finite places. -/
theorem finiteExtensionPoleDivisor_ratFuncX_inl_eq_zero
    (q : FiniteExtensionFinitePlace K L) :
    finiteExtensionPoleDivisor K L
      (algebraMap (RatFunc K) L RatFunc.X) (.inl q) = 0 := by
  simp only [finiteExtensionPoleDivisor, Finsupp.neg_apply,
    Finsupp.filter_apply]
  rw [if_neg (not_lt_of_ge
    (finiteExtensionPrincipalDivisor_ratFuncX_inl_nonnegative K L q))]
  simp

/-- Above infinity, the pole coefficient of the rational parameter is exactly
the ramification index. -/
theorem finiteExtensionPoleDivisor_ratFuncX_inr_eq_ramificationIdx
    (P : FiniteExtensionInfinityPlace K L) :
    finiteExtensionPoleDivisor K L
        (algebraMap (RatFunc K) L RatFunc.X) (.inr P) =
      (P.1.ramificationIdx (RatFuncInfinityIntegers K) : ℤ) := by
  have he : 0 < P.1.ramificationIdx (RatFuncInfinityIntegers K) :=
    P.1.ramificationIdx_pos (RatFuncInfinityIntegers K)
  simp only [finiteExtensionPoleDivisor, Finsupp.neg_apply,
    Finsupp.filter_apply,
    finiteExtensionPrincipalDivisor_ratFuncX_inr_eq_neg_ramificationIdx,
    neg_lt_zero]
  rw [if_pos (by exact_mod_cast he)]
  simp

/-- Pointwise description of the complete pole divisor of the rational
parameter: it is zero at finite places and has coefficient `e(P)` at every
place above infinity. -/
theorem finiteExtensionPoleDivisor_ratFuncX_apply
    (v : FiniteExtensionPlace K L) :
    finiteExtensionPoleDivisor K L
        (algebraMap (RatFunc K) L RatFunc.X) v =
      match v with
      | .inl _ => 0
      | .inr P => (P.1.ramificationIdx
          (RatFuncInfinityIntegers K) : ℤ) := by
  cases v with
  | inl q => exact finiteExtensionPoleDivisor_ratFuncX_inl_eq_zero K L q
  | inr P =>
      exact finiteExtensionPoleDivisor_ratFuncX_inr_eq_ramificationIdx K L P

/-- The support of the pole divisor of the rational parameter consists
exactly of the places above infinity. -/
theorem finiteExtensionPoleDivisor_ratFuncX_support :
    (finiteExtensionPoleDivisor K L
      (algebraMap (RatFunc K) L RatFunc.X)).support =
        Finset.univ.map
          (Function.Embedding.inr :
            FiniteExtensionInfinityPlace K L ↪ FiniteExtensionPlace K L) := by
  classical
  ext v
  cases v with
  | inl q => simp [finiteExtensionPoleDivisor_ratFuncX_inl_eq_zero]
  | inr P =>
      have he : 0 < P.1.ramificationIdx (RatFuncInfinityIntegers K) :=
        P.1.ramificationIdx_pos (RatFuncInfinityIntegers K)
      simp [finiteExtensionPoleDivisor_ratFuncX_inr_eq_ramificationIdx,
        Nat.ne_of_gt he]

/-- The negative support of the principal divisor of the rational parameter
consists exactly of the places above infinity. -/
theorem finiteExtensionPrincipalDivisor_ratFuncX_negativeSupport :
    (finiteExtensionPrincipalDivisor K L
      (algebraMap (RatFunc K) L RatFunc.X)).support.filter
        (fun v => finiteExtensionPrincipalDivisor K L
          (algebraMap (RatFunc K) L RatFunc.X) v < 0) =
      Finset.univ.map
        (Function.Embedding.inr :
          FiniteExtensionInfinityPlace K L ↪ FiniteExtensionPlace K L) := by
  classical
  ext v
  cases v with
  | inl q =>
      constructor
      · intro hv
        have hneg := (Finset.mem_filter.mp hv).2
        exact (not_lt_of_ge
          (finiteExtensionPrincipalDivisor_ratFuncX_inl_nonnegative K L q)
          hneg).elim
      · intro hv
        simp at hv
  | inr P =>
      have he : 0 < P.1.ramificationIdx (RatFuncInfinityIntegers K) :=
        P.1.ramificationIdx_pos (RatFuncInfinityIntegers K)
      constructor
      · intro _
        simp
      · intro _
        apply Finset.mem_filter.mpr
        constructor
        · apply Finsupp.mem_support_iff.mpr
          rw [finiteExtensionPrincipalDivisor_ratFuncX_inr_eq_neg_ramificationIdx]
          exact neg_ne_zero.mpr (Int.natCast_ne_zero.mpr (Nat.ne_of_gt he))
        · rw [finiteExtensionPrincipalDivisor_ratFuncX_inr_eq_neg_ramificationIdx]
          exact neg_lt_zero.mpr (Int.natCast_pos.mpr he)

/-- The height of the rational parameter in a finite separable extension is
the extension degree. -/
theorem finiteExtensionHeight_ratFuncX_eq_finrank :
    finiteExtensionHeight K L (algebraMap (RatFunc K) L RatFunc.X) =
      Module.finrank (RatFunc K) L := by
  rw [finiteExtensionHeight,
    finiteExtensionPrincipalDivisor_ratFuncX_negativeSupport K L]
  rw [Finset.sum_map]
  simp only [Function.Embedding.inr_apply,
    finiteExtensionPrincipalDivisor_ratFuncX_inr_eq_neg_ramificationIdx,
    neg_neg, Int.toNat_natCast, finiteExtensionPlaceDegree]
  simpa only using
    finiteExtensionInfinity_sum_ramification_inertia_eq_finrank K L

end

end BGS.HasseWeil
