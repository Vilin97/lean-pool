/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionPrincipalDivisor
import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindPlaceOrder
import Mathlib.Tactic

/-!
# Height of a polynomial in a finite rational-function extension

For a nonzero polynomial `P : K[X]`, regarded first as a rational function and
then as an element of a finite separable extension `L / K(X)`, this file proves
that the positive degree of its exhaustive principal divisor is

`Module.finrank (RatFunc K) L * P.natDegree`.

The proof is place-theoretic.  At finite places the lift is integral, hence has
nonnegative order.  Above infinity its inverse is integral, hence its order is
nonpositive.  The positive part is therefore exactly the finite-place degree
sum, which is evaluated by the norm and the rational-function product formula.
No algebraic-closedness hypothesis on the constant field is needed.
-/

open scoped nonZeroDivisors Polynomial
open IsDedekindDomain Multiplicative WithZero

namespace BGS.CorvajaZannier

noncomputable section

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance (priority := 10) polynomialHeightPolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance polynomialHeightPolynomialScalarTower :
    IsScalarTower K[X] (RatFunc K) L :=
  ⟨fun r s x => by
    simp only [Algebra.smul_def]
    rw [map_mul]
    change (algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) r) *
      algebraMap (RatFunc K) L s) * x =
      algebraMap K[X] L r * (algebraMap (RatFunc K) L s * x)
    rw [show algebraMap K[X] L r =
      algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) r) by rfl]
    ring⟩

local instance polynomialHeightFiniteIntegralClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance polynomialHeightFiniteIntegralClosureIsIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance polynomialHeightPolynomialTorsionFreeTop :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance polynomialHeightFiniteIntegralClosureIsTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance polynomialHeightInfinityIntegralClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance polynomialHeightInfinityIntegralClosureIsDedekindDomain :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

/-- The order of an inverse at a height-one place is the negative order. -/
theorem finitePlaceOrder_inv_eq_neg
    {R F : Type*} [CommRing R] [IsDedekindDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (v : HeightOneSpectrum R) (x : F) (hx : x ≠ 0) :
    finitePlaceOrder v x⁻¹ = -finitePlaceOrder v x := by
  have hone := finitePrincipalDivisor_mul (R := R)
    (1 : F) (1 : F) one_ne_zero one_ne_zero
  have hone' := congrArg (fun D => D v) hone
  simp only [one_mul, finitePrincipalDivisor_apply, Finsupp.add_apply] at hone'
  have hmul := finitePrincipalDivisor_mul (R := R)
    x⁻¹ x (inv_ne_zero hx) hx
  have hmul' := congrArg (fun D => D v) hmul
  rw [inv_mul_cancel₀ hx] at hmul'
  simp only [finitePrincipalDivisor_apply, Finsupp.add_apply] at hmul'
  omega

/-- A nonzero regular element has nonnegative finite-place order. -/
theorem finitePlaceOrder_algebraMap_nonnegative
    {R F : Type*} [CommRing R] [IsDedekindDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (v : HeightOneSpectrum R) (a : R) (ha : a ≠ 0) :
    0 ≤ finitePlaceOrder v (algebraMap R F a) := by
  have hmap : algebraMap R F a ≠ 0 := by
    intro hzero
    apply ha
    apply IsFractionRing.injective R F
    simpa using hzero
  have htop := finitePlaceOrderTop_algebraMap_nonnegative (L := F) v a
  rw [finitePlaceOrderTop_eq_coe v _ hmap] at htop
  exact_mod_cast htop

private theorem polynomial_lift_finitePlaceOrder_nonnegative
    (P : K[X]) (hP : P ≠ 0)
    (q : FiniteExtensionFinitePlace K L) :
    0 ≤ finiteExtensionPrincipalDivisor K L
      (algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) P)) (.inl q) := by
  let S := RatFuncFiniteIntegralClosure K L
  let e := ratFuncFiniteIntegralClosureFractionRingEquiv K L
  let s : S := algebraMap K[X] S P
  have hs : s ≠ 0 := by
    have hinj : Function.Injective (algebraMap K[X] S) :=
      FunctionField.ringOfIntegers.algebraMap_injective K L
    simpa [s] using hinj.ne hP
  have hrepr :
      e.symm (algebraMap (RatFunc K) L
          (algebraMap K[X] (RatFunc K) P)) =
        algebraMap S (FractionRing S) s := by
    apply e.injective
    rw [e.apply_symm_apply, e.commutes]
    rfl
  rw [finiteExtensionPrincipalDivisor_inl, hrepr]
  exact finitePlaceOrder_algebraMap_nonnegative q s hs

private theorem polynomial_lift_infinityPlaceOrder_nonpositive
    (P : K[X]) (hP : P ≠ 0)
    (q : FiniteExtensionInfinityPlace K L) :
    finiteExtensionPrincipalDivisor K L
      (algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) P)) (.inr q) ≤ 0 := by
  let f : RatFunc K := algebraMap K[X] (RatFunc K) P
  let x : L := algebraMap (RatFunc K) L f
  let S := RatFuncInfinityIntegralClosure K L
  let e := ratFuncInfinityIntegralClosureFractionRingEquiv K L
  have hf : f ≠ 0 := RatFunc.algebraMap_ne_zero hP
  have hx : x ≠ 0 := (map_ne_zero (algebraMap (RatFunc K) L)).2 hf
  let a : RatFuncInfinityIntegers K := ⟨f⁻¹, by
    change RatFunc.inftyValuation K f⁻¹ ≤ 1
    rw [RatFunc.inftyValuation_apply,
      RatFunc.inftyValuation_of_nonzero K (inv_ne_zero hf),
      ← exp_zero, exp_le_exp, RatFunc.intDegree_inv]
    have hdegree : f.intDegree = (P.natDegree : ℤ) := by
      exact RatFunc.intDegree_polynomial
    rw [hdegree]
    omega⟩
  let s : S := algebraMap (RatFuncInfinityIntegers K) S a
  have ha : a ≠ 0 := by
    intro hzero
    apply inv_ne_zero hf
    have hval := congrArg Subtype.val hzero
    simpa [a] using hval
  have hs : s ≠ 0 := by
    intro hzero
    apply ha
    apply Subtype.ext
    apply (algebraMap (RatFunc K) L).injective
    have hL := congrArg Subtype.val hzero
    change algebraMap (RatFunc K) L (a : RatFunc K) =
      algebraMap (RatFunc K) L (0 : RatFunc K)
    simpa [s] using hL
  have hrepr : (e.symm x)⁻¹ = algebraMap S (FractionRing S) s := by
    apply e.injective
    rw [map_inv₀, e.apply_symm_apply, e.commutes]
    change x⁻¹ = algebraMap (RatFunc K) L (a : RatFunc K)
    simp [x, a, f]
  have hey : e.symm x ≠ 0 := by simpa using hx
  have hinv : 0 ≤ finitePlaceOrder
      (primeOverHeightOne (ratFuncInfinityPlace K) q) ((e.symm x)⁻¹) := by
    rw [hrepr]
    exact finitePlaceOrder_algebraMap_nonnegative _ s hs
  rw [finiteExtensionPrincipalDivisor_inr]
  change finitePlaceOrder
    (primeOverHeightOne (ratFuncInfinityPlace K) q) (e.symm x) ≤ 0
  rw [finitePlaceOrder_inv_eq_neg _ _ hey] at hinv
  omega

theorem finiteExtensionPositiveDegree_polynomial_cast
    (P : K[X]) (hP : P ≠ 0) :
    (finiteExtensionPositiveDegree K L
        (algebraMap (RatFunc K) L
          (algebraMap K[X] (RatFunc K) P)) : ℤ) =
      finiteExtensionFiniteDirectDegreeSum K L
        (algebraMap (RatFunc K) L
          (algebraMap K[X] (RatFunc K) P)) := by
  let x : L := algebraMap (RatFunc K) L
    (algebraMap K[X] (RatFunc K) P)
  let D := finiteExtensionPrincipalDivisor K L x
  rw [finiteExtensionPositiveDegree_cast]
  change (∑ v ∈ D.support.filter (fun v => 0 < D v),
      D v * (finiteExtensionPlaceDegree K L v : ℤ)) = _
  have hfilter :
      (∑ v ∈ D.support.filter (fun v => 0 < D v),
        D v * (finiteExtensionPlaceDegree K L v : ℤ)) =
      D.sum (fun v n => if 0 < n then
        n * (finiteExtensionPlaceDegree K L v : ℤ) else 0) := by
    rw [Finsupp.sum]
    exact Finset.sum_filter _ _
  rw [hfilter]
  change _ = finiteExtensionFiniteDirectDegreeSum K L x
  rw [show D =
      (finiteExtensionFinitePrincipalDivisor K L x).sumElim
        (finiteExtensionInfinityPrincipalDivisor K L x) by
      rfl,
    Finsupp.sum_sumElim]
  rw [finiteExtensionFiniteDirectDegreeSum]
  have hfinite :
      (finiteExtensionFinitePrincipalDivisor K L x).sum
          (fun q n => if 0 < n then
            n * (finiteExtensionPlaceDegree K L (.inl q) : ℤ) else 0) =
        (finiteExtensionFinitePrincipalDivisor K L x).sum
          (fun q n => n * (q.asIdeal.inertiaDeg K[X] : ℤ) *
            (ratFuncFinitePlaceDegree (HeightOneSpectrum.under K[X] q) : ℤ)) := by
    apply Finsupp.sum_congr
    intro q hq
    have hnonneg := polynomial_lift_finitePlaceOrder_nonnegative K L P hP q
    have hne : finiteExtensionFinitePrincipalDivisor K L x q ≠ 0 :=
      Finsupp.mem_support_iff.mp hq
    have hpos : 0 < finiteExtensionFinitePrincipalDivisor K L x q := by
      rw [finiteExtensionFinitePrincipalDivisor_apply]
      change 0 < finiteExtensionPrincipalDivisor K L x (.inl q)
      exact lt_of_le_of_ne hnonneg (Ne.symm hne)
    rw [if_pos hpos]
    simp only [finiteExtensionPlaceDegree, Nat.cast_mul]
    ring
  have hinfinity :
      (finiteExtensionInfinityPrincipalDivisor K L x).sum
          (fun q n => if 0 < n then
            n * (finiteExtensionPlaceDegree K L (.inr q) : ℤ) else 0) = 0 := by
    rw [Finsupp.sum]
    apply Finset.sum_eq_zero
    intro q hq
    have hnonpos := polynomial_lift_infinityPlaceOrder_nonpositive K L P hP q
    have hnotpos : ¬ 0 < finiteExtensionInfinityPrincipalDivisor K L x q := by
      rw [finiteExtensionInfinityPrincipalDivisor_apply]
      change ¬ 0 < finiteExtensionPrincipalDivisor K L x (.inr q)
      exact not_lt_of_ge hnonpos
    rw [if_neg hnotpos]
  change
    (finiteExtensionFinitePrincipalDivisor K L x).sum
        (fun q n => if 0 < n then
          n * (finiteExtensionPlaceDegree K L (.inl q) : ℤ) else 0) +
      (finiteExtensionInfinityPrincipalDivisor K L x).sum
        (fun q n => if 0 < n then
          n * (finiteExtensionPlaceDegree K L (.inr q) : ℤ) else 0) =
      (finiteExtensionFinitePrincipalDivisor K L x).sum
        (fun q n => n * (q.asIdeal.inertiaDeg K[X] : ℤ) *
          (ratFuncFinitePlaceDegree (HeightOneSpectrum.under K[X] q) : ℤ))
  rw [hfinite, hinfinity, add_zero]

theorem finiteExtensionPositiveDegree_polynomial
    (P : K[X]) (hP : P ≠ 0) :
    finiteExtensionPositiveDegree K L
        (algebraMap (RatFunc K) L
          (algebraMap K[X] (RatFunc K) P)) =
      Module.finrank (RatFunc K) L * P.natDegree := by
  have hx : algebraMap (RatFunc K) L
      (algebraMap K[X] (RatFunc K) P) ≠ 0 := by
    exact (map_ne_zero (algebraMap (RatFunc K) L)).2
      (RatFunc.algebraMap_ne_zero hP)
  have hcast := finiteExtensionPositiveDegree_polynomial_cast K L P hP
  rw [finiteExtensionFiniteDirectDegreeSum_eq_grouped K L _ hx,
    finiteExtensionFinitePlaceDegreeSum_eq_normFinitePlaceDegreeSum K L _ hx,
    Algebra.norm_algebraMap,
    ratFuncExhaustiveFinitePlaceDegreeSum_eq_intDegree _
      (pow_ne_zero _ (RatFunc.algebraMap_ne_zero hP))] at hcast
  have hdegree :
      ((algebraMap K[X] (RatFunc K) P) ^ Module.finrank (RatFunc K) L).intDegree =
        (Module.finrank (RatFunc K) L * P.natDegree : ℕ) := by
    rw [← map_pow, RatFunc.intDegree_polynomial, Polynomial.natDegree_pow]
  rw [hdegree] at hcast
  exact_mod_cast hcast

end

end BGS.CorvajaZannier
