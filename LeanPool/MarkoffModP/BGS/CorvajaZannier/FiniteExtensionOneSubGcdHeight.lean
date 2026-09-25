/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionGcdOutsideHeight
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionExceptionalSupport
public import Mathlib.Tactic

/-!
# The gcd height of a function and its complement

Control the common divisor of a function and one minus that function using local orders,
exceptional places, and outside height.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

open scoped nonZeroDivisors Polynomial BigOperators
open IsDedekindDomain

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

attribute [local instance] Classical.decEq

local instance (priority := 10) oneSubGcdPolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance oneSubGcdPolynomialScalarTower :
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

local instance oneSubGcdFiniteIntegralClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance oneSubGcdFiniteIntegralClosureIsIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance oneSubGcdPolynomialTorsionFreeTop :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance oneSubGcdFiniteIntegralClosureIsTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance oneSubGcdInfinityIntegralClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance oneSubGcdInfinityIntegralClosureIsIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

local instance oneSubGcdInfinityTorsionFreeTop :
    Module.IsTorsionFree (RatFuncInfinityIntegers K) L :=
  Module.IsTorsionFree.trans_faithfulSMul
    (RatFuncInfinityIntegers K) (RatFunc K) L

local instance oneSubGcdInfinityIntegralClosureIsTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance oneSubGcdInfinityIntegralClosureIsDedekindDomain :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

omit [DecidableEq K] in
theorem finiteExtensionPrincipalDivisor_add_ge_min
    (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0)
    (w : FiniteExtensionPlace K L) :
    min (finiteExtensionPrincipalDivisor K L x w)
        (finiteExtensionPrincipalDivisor K L y w) ≤
      finiteExtensionPrincipalDivisor K L (x + y) w := by
  cases w with
  | inl q =>
      let e := ratFuncFiniteIntegralClosureFractionRingEquiv K L
      have hx' : e.symm x ≠ 0 := by simpa using e.symm.injective.ne hx
      have hy' : e.symm y ≠ 0 := by simpa using e.symm.injective.ne hy
      have hxy' : e.symm (x + y) ≠ 0 := by
        simpa using e.symm.injective.ne hxy
      simp only [finiteExtensionPrincipalDivisor_inl]
      change min (finitePlaceOrder q (e.symm x))
          (finitePlaceOrder q (e.symm y)) ≤
        finitePlaceOrder q (e.symm (x + y))
      have hadd : e.symm (x + y) = e.symm x + e.symm y :=
        e.symm.map_add x y
      rw [hadd]
      exact finitePlaceOrder_add_ge_min q (e.symm x) (e.symm y)
        hx' hy' (by rw [← hadd]; exact hxy')
  | inr P =>
      let q := primeOverHeightOne (ratFuncInfinityPlace K) P
      let e := ratFuncInfinityIntegralClosureFractionRingEquiv K L
      have hx' : e.symm x ≠ 0 := by simpa using e.symm.injective.ne hx
      have hy' : e.symm y ≠ 0 := by simpa using e.symm.injective.ne hy
      have hxy' : e.symm (x + y) ≠ 0 := by
        simpa using e.symm.injective.ne hxy
      simp only [finiteExtensionPrincipalDivisor_inr]
      change min (finitePlaceOrder q (e.symm x))
          (finitePlaceOrder q (e.symm y)) ≤
        finitePlaceOrder q (e.symm (x + y))
      have hadd : e.symm (x + y) = e.symm x + e.symm y :=
        e.symm.map_add x y
      rw [hadd]
      exact finitePlaceOrder_add_ge_min q (e.symm x) (e.symm y)
        hx' hy' (by rw [← hadd]; exact hxy')

private theorem finitePlaceOrder_neg_oneSubGcd
    {R F : Type*} [CommRing R] [IsDedekindDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (w : HeightOneSpectrum R) (x : F) (hx : x ≠ 0) :
    finitePlaceOrder w (-x) = finitePlaceOrder w x := by
  have hval : (w.valuation F) (-x) = (w.valuation F) x := by simp
  rw [valuation_eq_exp_neg_finitePlaceOrder w (-x) (neg_ne_zero.mpr hx),
    valuation_eq_exp_neg_finitePlaceOrder w x hx] at hval
  have horder := WithZero.exp_injective hval
  omega

omit [DecidableEq K] in
theorem finiteExtensionPrincipalDivisor_neg_apply
    (x : L) (hx : x ≠ 0) (w : FiniteExtensionPlace K L) :
    finiteExtensionPrincipalDivisor K L (-x) w =
      finiteExtensionPrincipalDivisor K L x w := by
  cases w with
  | inl q =>
      simp only [finiteExtensionPrincipalDivisor_inl, map_neg]
      exact finitePlaceOrder_neg_oneSubGcd q _
        (by simpa using
          (ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm.injective.ne hx)
  | inr P =>
      simp only [finiteExtensionPrincipalDivisor_inr, map_neg]
      exact finitePlaceOrder_neg_oneSubGcd
        (primeOverHeightOne (ratFuncInfinityPlace K) P) _
        (by simpa using
          (ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm.injective.ne hx)

omit [DecidableEq K] in
theorem finiteExtensionPrincipalDivisor_one_sub_nonnegative_of_eq_zero
    (x : L) (hxone : x ≠ 1)
    (w : FiniteExtensionPlace K L)
    (hzero : finiteExtensionPrincipalDivisor K L x w = 0) :
    0 ≤ finiteExtensionPrincipalDivisor K L (1 - x) w := by
  by_contra h
  have hneg : finiteExtensionPrincipalDivisor K L (1 - x) w < 0 :=
    lt_of_not_ge h
  have hsub : (1 : L) - x ≠ 0 := sub_ne_zero.mpr hxone.symm
  have heq := finiteExtensionPrincipalDivisor_one_sub_apply_of_neg
    K L (1 - x) hsub w hneg
  rw [show (1 : L) - (1 - x) = x by ring] at heq
  omega

omit [DecidableEq K] in
theorem finiteExtensionPrincipalDivisor_eq_zero_of_one_sub_pos
    (x : L) (hx : x ≠ 0) (hxone : x ≠ 1)
    (w : FiniteExtensionPlace K L)
    (hpos : 0 < finiteExtensionPrincipalDivisor K L (1 - x) w) :
    finiteExtensionPrincipalDivisor K L x w = 0 := by
  have hsub : (1 : L) - x ≠ 0 := sub_ne_zero.mpr hxone.symm
  have hlower := finiteExtensionPrincipalDivisor_add_ge_min
    K L (1 : L) (-(1 - x)) one_ne_zero (neg_ne_zero.mpr hsub)
      (by simpa using hx) w
  rw [finiteExtensionPrincipalDivisor_one K L,
    show (1 : L) + -(1 - x) = x by ring] at hlower
  simp only [Finsupp.zero_apply] at hlower
  have hnegOrder :
      finiteExtensionPrincipalDivisor K L (-(1 - x)) w =
        finiteExtensionPrincipalDivisor K L (1 - x) w :=
    finiteExtensionPrincipalDivisor_neg_apply K L (1 - x) hsub w
  rw [hnegOrder] at hlower
  have hxnonneg : 0 ≤ finiteExtensionPrincipalDivisor K L x w := by
    simpa [min_eq_left (le_of_lt hpos)] using hlower
  have hreverse := finiteExtensionPrincipalDivisor_add_ge_min
    K L x (1 - x) hx hsub (by simp) w
  rw [show x + (1 - x) = (1 : L) by ring,
    finiteExtensionPrincipalDivisor_one K L] at hreverse
  simp only [Finsupp.zero_apply] at hreverse
  rcases le_total (finiteExtensionPrincipalDivisor K L x w)
      (finiteExtensionPrincipalDivisor K L (1 - x) w) with hle | hle
  · rw [min_eq_left hle] at hreverse
    omega
  · rw [min_eq_right hle] at hreverse
    omega

/-- The exceptional places used in Proposition 2: exactly the zeroes and
poles of the two coordinates. -/
def propositionTwoExceptionalPlaces (u v : L) :
    Finset (FiniteExtensionPlace K L) := by
  classical
  exact (finiteExtensionPrincipalDivisor K L u).support ∪
    (finiteExtensionPrincipalDivisor K L v).support

/-- The divisor-theoretic gcd comparison used in Proposition 2, now on the
actual exhaustive place type used by the canonical Wronskian sum. -/
theorem finiteExtensionOneSubGcd_add_outsideHeight_le_positiveDegree
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (huone : u ≠ 1) (hvone : v ≠ 1) :
    finiteExtensionGcdWeightedDegree K L (1 - u) (1 - v) +
        finiteExtensionOutsideHeight K L ((1 - u) / (1 - v))
          (propositionTwoExceptionalPlaces K L u v) ≤
      finiteExtensionPositiveDegree K L (1 - v) := by
  apply finiteExtensionGcdWeightedDegree_add_outsideHeight_le
  · intro P
    have huSub : (1 : L) - u ≠ 0 := sub_ne_zero.mpr huone.symm
    have hvSub : (1 : L) - v ≠ 0 := sub_ne_zero.mpr hvone.symm
    have hdiv := congrArg (fun D => D P)
      (finiteExtensionPrincipalDivisor_div K L (1 - u) (1 - v)
        huSub hvSub)
    simpa using hdiv
  · intro P hP
    have hu0 : finiteExtensionPrincipalDivisor K L u P = 0 := by
      apply Finsupp.notMem_support_iff.mp
      intro huP
      exact hP (by
        rw [propositionTwoExceptionalPlaces]
        exact Finset.mem_union_left _ huP)
    have hv0 : finiteExtensionPrincipalDivisor K L v P = 0 := by
      apply Finsupp.notMem_support_iff.mp
      intro hvP
      exact hP (by
        rw [propositionTwoExceptionalPlaces]
        exact Finset.mem_union_right _ hvP)
    exact ⟨
      finiteExtensionPrincipalDivisor_one_sub_nonnegative_of_eq_zero
        K L u huone P hu0,
      finiteExtensionPrincipalDivisor_one_sub_nonnegative_of_eq_zero
        K L v hvone P hv0⟩
  · intro P hP
    by_contra hmin
    have hminpos : 0 < min
        (finiteExtensionPrincipalDivisor K L (1 - u) P)
        (finiteExtensionPrincipalDivisor K L (1 - v) P) :=
      lt_of_not_ge hmin
    have huPos : 0 < finiteExtensionPrincipalDivisor K L (1 - u) P :=
      lt_of_lt_of_le hminpos (min_le_left _ _)
    have hvPos : 0 < finiteExtensionPrincipalDivisor K L (1 - v) P :=
      lt_of_lt_of_le hminpos (min_le_right _ _)
    have hu0 := finiteExtensionPrincipalDivisor_eq_zero_of_one_sub_pos
      K L u hu huone P huPos
    have hv0 := finiteExtensionPrincipalDivisor_eq_zero_of_one_sub_pos
      K L v hv hvone P hvPos
    rw [propositionTwoExceptionalPlaces] at hP
    rcases Finset.mem_union.mp hP with huP | hvP
    · exact (Finsupp.mem_support_iff.mp huP) hu0
    · exact (Finsupp.mem_support_iff.mp hvP) hv0

/-- In the gcd comparison, the positive degree of `1-v` is exactly the
coordinate height, hence the positive degree of `v`. -/
theorem finiteExtensionOneSubGcd_add_outsideHeight_le_positiveDegree_coordinate
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (huone : u ≠ 1) (hvone : v ≠ 1) :
    finiteExtensionGcdWeightedDegree K L (1 - u) (1 - v) +
        finiteExtensionOutsideHeight K L ((1 - u) / (1 - v))
          (propositionTwoExceptionalPlaces K L u v) ≤
      finiteExtensionPositiveDegree K L v := by
  calc
    _ ≤ finiteExtensionPositiveDegree K L (1 - v) :=
      finiteExtensionOneSubGcd_add_outsideHeight_le_positiveDegree
        K L u v hu hv huone hvone
    _ = finiteExtensionPositiveDegree K L v := by
      rw [finiteExtensionPositiveDegree_eq_height K L (1 - v)
          (sub_ne_zero.mpr hvone.symm),
        finiteExtensionHeight_one_sub K L v hv hvone,
        ← finiteExtensionPositiveDegree_eq_height K L v hv]

end

end BGS.CorvajaZannier
