/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.InfinityPlace
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.RatFuncExhaustiveProductFormula
public import Mathlib.NumberTheory.FunctionField

/-!
# Exhaustive product formula in a finite extension of `K(X)`

This file combines the norm/count formula at every finite polynomial place
with the corresponding formula at infinity.  An element of a finite
separable extension is transported to the canonical fraction fields of the
two integral closures.  Naturality of the field norm shows that both models
compute the same norm in `K(X)`.

The final theorem sums the residue-degree-weighted orders at every prime
above every finite place, with the finite-place degree factor, and at every
prime above infinity.  The total is zero.
-/

@[expose] public section

open scoped nonZeroDivisors Polynomial
open IsDedekindDomain Multiplicative WithZero

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

namespace BGS.CorvajaZannier

noncomputable section

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance (priority := 10) polynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance polynomialScalarTower : IsScalarTower K[X] (RatFunc K) L :=
  ⟨fun r s x ↦ by
    simp only [Algebra.smul_def]
    rw [map_mul]
    change (algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) r) *
      algebraMap (RatFunc K) L s) * x =
      algebraMap K[X] L r * (algebraMap (RatFunc K) L s * x)
    rw [show algebraMap K[X] L r =
      algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) r) by rfl]
    ring⟩

abbrev RatFuncFiniteIntegralClosure := FunctionField.ringOfIntegers K L

noncomputable def ratFuncFiniteFractionRingEquiv :
    FractionRing K[X] ≃ₐ[K[X]] RatFunc K :=
  FractionRing.algEquiv K[X] (RatFunc K)

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
theorem ratFuncFiniteFractionRingEquiv_valuation
    (v : HeightOneSpectrum K[X]) (x : FractionRing K[X]) :
    v.valuation (RatFunc K) (ratFuncFiniteFractionRingEquiv K x) =
      v.valuation (FractionRing K[X]) x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective K[X] x
  rw [map_div₀, (ratFuncFiniteFractionRingEquiv K).commutes a,
    (ratFuncFiniteFractionRingEquiv K).commutes b,
    Valuation.map_div, Valuation.map_div,
    v.valuation_of_algebraMap, v.valuation_of_algebraMap,
    v.valuation_of_algebraMap, v.valuation_of_algebraMap]

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
theorem ratFuncFiniteFractionRing_order_eq
    (v : HeightOneSpectrum K[X]) (x : FractionRing K[X]) (hx : x ≠ 0) :
    finitePlaceOrder v x =
      ratFuncFiniteOrder v (ratFuncFiniteFractionRingEquiv K x) := by
  let e := ratFuncFiniteFractionRingEquiv K
  have hcanon := valuation_eq_exp_neg_finitePlaceOrder
    (R := K[X]) (L := FractionRing K[X]) v x hx
  have he_ne : e x ≠ 0 := by simpa using hx
  have hactual := valuation_eq_exp_neg_finitePlaceOrder
    (R := K[X]) (L := RatFunc K) v (e x) he_ne
  have hval := ratFuncFiniteFractionRingEquiv_valuation K v x
  have hexp : exp (-finitePlaceOrder v x) =
      exp (-finitePlaceOrder v (e x)) := by
    rw [← hcanon, ← hactual]
    exact hval.symm
  rw [exp_inj] at hexp
  change finitePlaceOrder v x = finitePlaceOrder v (e x)
  omega

noncomputable def ratFuncFiniteIntegralClosureFractionRingEquiv :
    FractionRing (RatFuncFiniteIntegralClosure K L) ≃ₐ[RatFuncFiniteIntegralClosure K L] L :=
  FractionRing.algEquiv (RatFuncFiniteIntegralClosure K L) L

local instance finiteIntegralClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance finiteIntegralClosureIsIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance polynomialTorsionFreeTop : Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance finiteIntegralClosureIsTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance finiteBaseFaithfulSMulExtensionFractionRing :
    FaithfulSMul K[X] (FractionRing (RatFuncFiniteIntegralClosure K L)) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y hxy
  have hS := IsFractionRing.injective (RatFuncFiniteIntegralClosure K L)
    (FractionRing (RatFuncFiniteIntegralClosure K L)) hxy
  exact FunctionField.ringOfIntegers.algebraMap_injective K L hS

local instance finiteFractionRingAlgebra :
    Algebra (FractionRing K[X])
      (FractionRing (RatFuncFiniteIntegralClosure K L)) :=
  FractionRing.liftAlgebra K[X]
    (FractionRing (RatFuncFiniteIntegralClosure K L))

local instance finiteFractionRingSeparable :
    Algebra.IsSeparable (FractionRing K[X])
      (FractionRing (RatFuncFiniteIntegralClosure K L)) := by
  refine Algebra.IsSeparable.of_equiv_equiv
    (ratFuncFiniteFractionRingEquiv K).symm.toRingEquiv
    (ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm.toRingEquiv ?_
  ext z
  exact IsFractionRing.algEquiv_commutes
    (ratFuncFiniteFractionRingEquiv K).symm
    (ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm z

local instance infinityIntegralClosureModuleFinite' :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance infinityIntegralClosureIsDedekindDomain' :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance infinityIntegralClosureIsFractionRing' :
    IsFractionRing (RatFuncInfinityIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

noncomputable def ratFuncInfinityIntegralClosureFractionRingEquiv :
    FractionRing (RatFuncInfinityIntegralClosure K L) ≃ₐ[RatFuncInfinityIntegralClosure K L] L :=
  FractionRing.algEquiv (RatFuncInfinityIntegralClosure K L) L

local instance infinityBaseFaithfulSMulExtensionFractionRing' :
    FaithfulSMul (RatFuncInfinityIntegers K)
      (FractionRing (RatFuncInfinityIntegralClosure K L)) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y hxy
  have hS := IsFractionRing.injective (RatFuncInfinityIntegralClosure K L)
    (FractionRing (RatFuncInfinityIntegralClosure K L)) hxy
  have hL := congrArg Subtype.val hS
  apply Subtype.ext
  apply (algebraMap (RatFunc K) L).injective
  change algebraMap (RatFunc K) L (x : RatFunc K) =
    algebraMap (RatFunc K) L (y : RatFunc K)
  exact hL

local instance infinityFractionRingAlgebra' :
    Algebra (FractionRing (RatFuncInfinityIntegers K))
      (FractionRing (RatFuncInfinityIntegralClosure K L)) :=
  FractionRing.liftAlgebra (RatFuncInfinityIntegers K)
    (FractionRing (RatFuncInfinityIntegralClosure K L))

local instance infinityFractionRingSeparable' :
    Algebra.IsSeparable (FractionRing (RatFuncInfinityIntegers K))
      (FractionRing (RatFuncInfinityIntegralClosure K L)) := by
  refine Algebra.IsSeparable.of_equiv_equiv
    (ratFuncInfinityFractionRingEquiv K).symm.toRingEquiv
    (ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm.toRingEquiv ?_
  ext z
  exact IsFractionRing.algEquiv_commutes
    (ratFuncInfinityFractionRingEquiv K).symm
    (ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm z

omit [DecidableEq K] [DecidableEq (RatFunc K)]
  [Algebra.IsSeparable (RatFunc K) L] in
theorem ratFuncFinite_norm_transport (x : L) :
    ratFuncFiniteFractionRingEquiv K
        (Algebra.norm (FractionRing K[X])
          ((ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm x)) =
      Algebra.norm (RatFunc K) x := by
  let eA := ratFuncFiniteFractionRingEquiv K
  let eS := ratFuncFiniteIntegralClosureFractionRingEquiv K L
  have hcompat :
      RingHom.comp (algebraMap (RatFunc K) L) eA.toRingEquiv.toRingHom =
        RingHom.comp eS.toRingEquiv.toRingHom
          (algebraMap (FractionRing K[X])
            (FractionRing (RatFuncFiniteIntegralClosure K L))) := by
    ext z
    exact IsFractionRing.algEquiv_commutes eA eS z
  have hnorm := Algebra.norm_eq_of_equiv_equiv
    eA.toRingEquiv eS.toRingEquiv hcompat (eS.symm x)
  calc
    eA (Algebra.norm (FractionRing K[X]) (eS.symm x)) =
        eA (eA.symm (Algebra.norm (RatFunc K) (eS (eS.symm x)))) :=
      congrArg eA hnorm
    _ = Algebra.norm (RatFunc K) x := by simp

omit [DecidableEq K] [Algebra.IsSeparable (RatFunc K) L]
  in
theorem ratFuncInfinity_norm_transport (x : L) :
    ratFuncInfinityFractionRingEquiv K
        (Algebra.norm (FractionRing (RatFuncInfinityIntegers K))
          ((ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm x)) =
      Algebra.norm (RatFunc K) x := by
  let eA := ratFuncInfinityFractionRingEquiv K
  let eS := ratFuncInfinityIntegralClosureFractionRingEquiv K L
  have hcompat :
      RingHom.comp (algebraMap (RatFunc K) L) eA.toRingEquiv.toRingHom =
        RingHom.comp eS.toRingEquiv.toRingHom
          (algebraMap (FractionRing (RatFuncInfinityIntegers K))
            (FractionRing (RatFuncInfinityIntegralClosure K L))) := by
    ext z
    exact IsFractionRing.algEquiv_commutes eA eS z
  have hnorm := Algebra.norm_eq_of_equiv_equiv
    eA.toRingEquiv eS.toRingEquiv hcompat (eS.symm x)
  calc
    eA (Algebra.norm (FractionRing (RatFuncInfinityIntegers K)) (eS.symm x)) =
        eA (eA.symm (Algebra.norm (RatFunc K) (eS (eS.symm x)))) :=
      congrArg eA hnorm
    _ = Algebra.norm (RatFunc K) x := by simp

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
theorem finitePrimesAbove_weightedOrder_eq_normOrder
    (p : HeightOneSpectrum K[X]) (x : L) (hx : x ≠ 0) :
    (∑ P : p.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L),
        (P.1.inertiaDeg K[X] : ℤ) *
          finitePlaceOrder (primeOverHeightOne p P)
            ((ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm x)) =
      ratFuncFiniteOrder p (Algebra.norm (RatFunc K) x) := by
  let y := (ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm x
  have hy : y ≠ 0 := by simpa [y] using hx
  have hcount := count_spanSingleton_norm_eq_sum_inertiaDeg_mul_count
    (R := K[X]) (S := RatFuncFiniteIntegralClosure K L) p y
  change finitePlaceOrder p (Algebra.norm (FractionRing K[X]) y) =
    ∑ P : p.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L),
      (P.1.inertiaDeg K[X] : ℤ) *
        finitePlaceOrder (primeOverHeightOne p P) y at hcount
  have hnorm_ne : Algebra.norm (FractionRing K[X]) y ≠ 0 := by
    intro hzero
    have hmapped := congrArg (ratFuncFiniteFractionRingEquiv K) hzero
    rw [map_zero, ratFuncFinite_norm_transport K L x] at hmapped
    exact (Algebra.norm_ne_zero_iff.mpr hx) hmapped
  calc
    _ = finitePlaceOrder p (Algebra.norm (FractionRing K[X]) y) := hcount.symm
    _ = ratFuncFiniteOrder p
        (ratFuncFiniteFractionRingEquiv K
          (Algebra.norm (FractionRing K[X]) y)) :=
      ratFuncFiniteFractionRing_order_eq K p _ hnorm_ne
    _ = ratFuncFiniteOrder p (Algebra.norm (RatFunc K) x) := by
      rw [ratFuncFinite_norm_transport K L x]

omit [DecidableEq K] in
theorem primesAboveInfinity_weightedOrder_eq_normInfinityOrder
    (x : L) (hx : x ≠ 0) :
    (∑ P : (ratFuncInfinityPlace K).asIdeal.primesOver
        (RatFuncInfinityIntegralClosure K L),
      (P.1.inertiaDeg (RatFuncInfinityIntegers K) : ℤ) *
        finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P)
          ((ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm x)) =
      ratFuncInfinityOrder (Algebra.norm (RatFunc K) x) := by
  let y := (ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm x
  have hy : y ≠ 0 := by simpa [y] using hx
  have hcount := count_spanSingleton_norm_at_infinity_eq_sum
    (K := K) (L := L) y
  change finitePlaceOrder (ratFuncInfinityPlace K)
      (Algebra.norm (FractionRing (RatFuncInfinityIntegers K)) y) =
    ∑ P : (ratFuncInfinityPlace K).asIdeal.primesOver
        (RatFuncInfinityIntegralClosure K L),
      (P.1.inertiaDeg (RatFuncInfinityIntegers K) : ℤ) *
        finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P) y at hcount
  have hnorm_ne :
      Algebra.norm (FractionRing (RatFuncInfinityIntegers K)) y ≠ 0 := by
    intro hzero
    have hmapped := congrArg (ratFuncInfinityFractionRingEquiv K) hzero
    rw [map_zero, ratFuncInfinity_norm_transport K L x] at hmapped
    exact (Algebra.norm_ne_zero_iff.mpr hx) hmapped
  calc
    _ = finitePlaceOrder (ratFuncInfinityPlace K)
        (Algebra.norm (FractionRing (RatFuncInfinityIntegers K)) y) := hcount.symm
    _ = ratFuncInfinityOrder
        (ratFuncInfinityFractionRingEquiv K
          (Algebra.norm (FractionRing (RatFuncInfinityIntegers K)) y)) :=
      ratFuncInfinityFractionRing_order_eq K _ hnorm_ne
    _ = ratFuncInfinityOrder (Algebra.norm (RatFunc K) x) := by
      rw [ratFuncInfinity_norm_transport K L x]

/-- The exhaustive finite-place contribution in `L`, grouped by the finite
places of `K(X)` supporting the divisor of the norm. -/
def finiteExtensionFinitePlaceDegreeSum (x : L) : ℤ :=
  (ratFuncFiniteDivisor (Algebra.norm (RatFunc K) x)).sum
    (fun p _ ↦
      (∑ P : p.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L),
        (P.1.inertiaDeg K[X] : ℤ) *
          finitePlaceOrder (primeOverHeightOne p P)
            ((ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm x)) *
      (ratFuncFinitePlaceDegree p : ℤ))

/-- The contribution of all primes of `L` above the place at infinity. -/
def finiteExtensionInfinityOrderSum (x : L) : ℤ :=
  ∑ P : (ratFuncInfinityPlace K).asIdeal.primesOver
      (RatFuncInfinityIntegralClosure K L),
    (P.1.inertiaDeg (RatFuncInfinityIntegers K) : ℤ) *
      finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P)
        ((ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm x)

omit [DecidableEq (RatFunc K)] in
theorem finiteExtensionFinitePlaceDegreeSum_eq_normFinitePlaceDegreeSum
    (x : L) (hx : x ≠ 0) :
    finiteExtensionFinitePlaceDegreeSum K L x =
      ratFuncExhaustiveFinitePlaceDegreeSum (Algebra.norm (RatFunc K) x) := by
  rw [finiteExtensionFinitePlaceDegreeSum,
    ratFuncExhaustiveFinitePlaceDegreeSum]
  apply Finsupp.sum_congr
  intro p _
  rw [finitePrimesAbove_weightedOrder_eq_normOrder K L p x hx,
    ratFuncFiniteDivisor_apply]

omit [DecidableEq K] in
theorem finiteExtensionInfinityOrderSum_eq_normInfinityOrder
    (x : L) (hx : x ≠ 0) :
    finiteExtensionInfinityOrderSum K L x =
      ratFuncInfinityOrder (Algebra.norm (RatFunc K) x) := by
  exact primesAboveInfinity_weightedOrder_eq_normInfinityOrder K L x hx

/-- The exhaustive weighted principal-divisor product formula in a finite
separable extension `L / K(X)`.  Every finite prime is grouped under its base
finite place and weighted by residue degree times the degree of that base
place; the second sum contains every prime above infinity. -/
theorem finiteExtension_exhaustivePrincipalDivisor_productFormula
    (x : L) (hx : x ≠ 0) :
    finiteExtensionFinitePlaceDegreeSum K L x +
      finiteExtensionInfinityOrderSum K L x = 0 := by
  rw [finiteExtensionFinitePlaceDegreeSum_eq_normFinitePlaceDegreeSum K L x hx,
    finiteExtensionInfinityOrderSum_eq_normInfinityOrder K L x hx]
  apply ratFunc_exhaustiveFinitePlace_plus_infinity_productFormula
  exact Algebra.norm_ne_zero_iff.mpr hx

end

end BGS.CorvajaZannier
