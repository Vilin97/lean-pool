/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionProductFormula
import LeanPool.MarkoffModP.BGS.CorvajaZannier.FinitePlaceCompletion
import LeanPool.MarkoffModP.BGS.CorvajaZannier.FunctionFieldProductFormula
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Valuation.Archimedean
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# The place at infinity and its primes in finite extensions

This file realizes the place at infinity of `K(X)` as an honest height-one
prime.  Its base ring is the integer ring of `RatFunc.inftyValuation`; this is
a discrete valuation ring with uniformizer `X⁻¹`.  The resulting
fractional-ideal order is proved to equal the previously defined
`ratFuncInfinityOrder = -intDegree`.

For a finite separable extension `L / K(X)`, the integral closure of the
infinity valuation ring is Dedekind and finite over the base.  The final
theorem specializes the finite-extension norm/count formula to the unique
base prime, producing the residue-degree-weighted sum over all primes above
infinity.
-/

open scoped nonZeroDivisors
open IsDedekindDomain Multiplicative WithZero

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

namespace BGS.CorvajaZannier

noncomputable section

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

/-- The valuation ring of the place at infinity of `K(X)`. -/
abbrev RatFuncInfinityIntegers := (RatFunc.inftyValuation K).integer

instance : IsDiscreteValuationRing (RatFuncInfinityIntegers K) :=
  (RatFunc.inftyValuation K).valuationSubring_isDiscreteValuationRing

instance : IsDedekindDomain (RatFuncInfinityIntegers K) := by
  let hnf : ¬ IsField (RatFuncInfinityIntegers K) :=
    IsDiscreteValuationRing.not_isField (RatFuncInfinityIntegers K)
  apply ((IsDiscreteValuationRing.TFAE (RatFuncInfinityIntegers K) hnf).out 1 3).mp
  infer_instance

/-- The unique height-one prime of the infinity valuation ring. -/
def ratFuncInfinityPlace : HeightOneSpectrum (RatFuncInfinityIntegers K) :=
  IsDiscreteValuationRing.maximalIdeal (RatFuncInfinityIntegers K)

/-- `X⁻¹` as an element of the infinity valuation ring. -/
def ratFuncInfinityUniformizer : RatFuncInfinityIntegers K :=
  ⟨1 / RatFunc.X, by
    show RatFunc.inftyValuation K (1 / RatFunc.X) ≤ 1
    rw [RatFunc.inftyValuation.X_inv]
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega⟩

theorem ratFuncInfinityUniformizer_isUniformizer :
    (RatFunc.inftyValuation K).IsUniformizer (ratFuncInfinityUniformizer K) := by
  rw [Valuation.IsUniformizer,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range]
  · simp [ratFuncInfinityUniformizer]
  · exact ⟨1 / RatFunc.X, RatFunc.inftyValuation.X_inv (F := K)⟩

theorem ratFuncInfinityPlace_span_uniformizer :
    (ratFuncInfinityPlace K).asIdeal = Ideal.span {ratFuncInfinityUniformizer K} := by
  exact Valuation.IsUniformizer.is_generator
    (ratFuncInfinityUniformizer_isUniformizer K)

/-- The canonical fraction field of the infinity valuation ring, identified
with the usual rational-function field. -/
noncomputable def ratFuncInfinityFractionRingEquiv :
    FractionRing (RatFuncInfinityIntegers K) ≃ₐ[RatFuncInfinityIntegers K] RatFunc K :=
  FractionRing.algEquiv (RatFuncInfinityIntegers K) (RatFunc K)

/-- The height-one valuation is unchanged by the canonical identification of
the fraction field of the infinity valuation ring with `K(X)`. -/
theorem ratFuncInfinityFractionRingEquiv_valuation
    (x : FractionRing (RatFuncInfinityIntegers K)) :
    (ratFuncInfinityPlace K).valuation (RatFunc K)
        (ratFuncInfinityFractionRingEquiv K x) =
      (ratFuncInfinityPlace K).valuation
        (FractionRing (RatFuncInfinityIntegers K)) x := by
  obtain ⟨a, b, hb, rfl⟩ :=
    IsFractionRing.div_surjective (RatFuncInfinityIntegers K) x
  rw [map_div₀, (ratFuncInfinityFractionRingEquiv K).commutes a,
    (ratFuncInfinityFractionRingEquiv K).commutes b,
    Valuation.map_div, Valuation.map_div,
    (ratFuncInfinityPlace K).valuation_of_algebraMap,
    (ratFuncInfinityPlace K).valuation_of_algebraMap,
    (ratFuncInfinityPlace K).valuation_of_algebraMap,
    (ratFuncInfinityPlace K).valuation_of_algebraMap]

/-- The height-one-prime order on the infinity valuation ring agrees with
the usual rational-function order `-intDegree`. -/
theorem ratFuncInfinityPlace_order_eq
    (f : RatFunc K) (hf : f ≠ 0) :
    finitePlaceOrder (ratFuncInfinityPlace K) f = ratFuncInfinityOrder f := by
  have hadic := valuation_eq_exp_neg_finitePlaceOrder
    (R := RatFuncInfinityIntegers K) (L := RatFunc K)
    (ratFuncInfinityPlace K) f hf
  have hpi_ne : ratFuncInfinityUniformizer K ≠ 0 := by
    intro h
    have hc := congrArg Subtype.val h
    exact (one_div_ne_zero RatFunc.X_ne_zero) hc
  have hadic_pi :
      (ratFuncInfinityPlace K).valuation (RatFunc K)
          (algebraMap (RatFuncInfinityIntegers K) (RatFunc K)
            (ratFuncInfinityUniformizer K)) = exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact (ratFuncInfinityPlace K).intValuation_singleton hpi_ne
      (ratFuncInfinityPlace_span_uniformizer K)
  let d : ℤ := f.intDegree
  let u0 : RatFunc K := f * RatFunc.X ^ (-d)
  have hinfty_u0 : RatFunc.inftyValuation K u0 = 1 := by
    rw [show u0 = f * RatFunc.X ^ (-d) by rfl, map_mul,
      RatFunc.inftyValuation_apply,
      RatFunc.inftyValuation_of_nonzero (F := K) hf,
      RatFunc.inftyValuation.X_zpow, ← WithZero.exp_add]
    simp [d]
  let u : RatFuncInfinityIntegers K := ⟨u0, hinfty_u0.le⟩
  have hu_unit : IsUnit u := by
    apply (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (RatFunc.inftyValuation K))).mpr
    exact hinfty_u0
  have hadic_u :
      (ratFuncInfinityPlace K).valuation (RatFunc K)
          (algebraMap (RatFuncInfinityIntegers K) (RatFunc K) u) = 1 := by
    exact Valuation.Integers.one_of_isUnit' hu_unit
      (fun x ↦ (ratFuncInfinityPlace K).valuation_le_one x)
  have hadic_invX :
      (ratFuncInfinityPlace K).valuation (RatFunc K) (1 / RatFunc.X) =
        exp (-1 : ℤ) := by
    change (ratFuncInfinityPlace K).valuation (RatFunc K) (1 / RatFunc.X) =
      exp (-1 : ℤ) at hadic_pi
    exact hadic_pi
  have hadic_X :
      (ratFuncInfinityPlace K).valuation (RatFunc K) RatFunc.X = exp (1 : ℤ) := by
    calc
      (ratFuncInfinityPlace K).valuation (RatFunc K) RatFunc.X =
          (ratFuncInfinityPlace K).valuation (RatFunc K) ((1 / RatFunc.X)⁻¹) := by
            congr 1
            simp
      _ = ((ratFuncInfinityPlace K).valuation (RatFunc K) (1 / RatFunc.X))⁻¹ := by
        rw [map_inv₀]
      _ = (exp (-1 : ℤ))⁻¹ := by rw [hadic_invX]
      _ = exp (1 : ℤ) := by simp
  have hcancel : RatFunc.X ^ d * RatFunc.X ^ (-d) = (1 : RatFunc K) := by
    rw [← zpow_add₀ RatFunc.X_ne_zero]
    simp
  have hdecomp :
      f = RatFunc.X ^ d *
        algebraMap (RatFuncInfinityIntegers K) (RatFunc K) u := by
    change f = RatFunc.X ^ d * u0
    change f = RatFunc.X ^ d * (f * RatFunc.X ^ (-d))
    symm
    rw [← mul_assoc, mul_comm (RatFunc.X ^ d) f, mul_assoc, hcancel, mul_one]
  have hadic_f :
      (ratFuncInfinityPlace K).valuation (RatFunc K) f = exp d := by
    rw [hdecomp, map_mul, map_zpow₀, hadic_X, hadic_u, mul_one]
    simp
  have hexp :
      exp (-finitePlaceOrder (ratFuncInfinityPlace K) f) = exp d :=
    hadic.symm.trans hadic_f
  rw [exp_inj] at hexp
  rw [ratFuncInfinityOrder]
  omega

/-- In the canonical `FractionRing` model used by the norm/count theorem, the
height-one-prime count still equals the ordinary rational-function order at
infinity after applying the canonical field equivalence. -/
theorem ratFuncInfinityFractionRing_order_eq
    (x : FractionRing (RatFuncInfinityIntegers K)) (hx : x ≠ 0) :
    finitePlaceOrder (ratFuncInfinityPlace K) x =
      ratFuncInfinityOrder (ratFuncInfinityFractionRingEquiv K x) := by
  let e := ratFuncInfinityFractionRingEquiv K
  have hcanon := valuation_eq_exp_neg_finitePlaceOrder
    (R := RatFuncInfinityIntegers K)
    (L := FractionRing (RatFuncInfinityIntegers K))
    (ratFuncInfinityPlace K) x hx
  have he_ne : e x ≠ 0 := by simpa using hx
  have hactual := valuation_eq_exp_neg_finitePlaceOrder
    (R := RatFuncInfinityIntegers K) (L := RatFunc K)
    (ratFuncInfinityPlace K) (e x) he_ne
  have hval := ratFuncInfinityFractionRingEquiv_valuation K x
  have hexp :
      exp (-finitePlaceOrder (ratFuncInfinityPlace K) x) =
        exp (-finitePlaceOrder (ratFuncInfinityPlace K) (e x)) := by
    rw [← hcanon, ← hactual]
    exact hval.symm
  rw [exp_inj] at hexp
  have hcount : finitePlaceOrder (ratFuncInfinityPlace K) x =
      finitePlaceOrder (ratFuncInfinityPlace K) (e x) := by omega
  rw [hcount]
  exact ratFuncInfinityPlace_order_eq K (e x) he_ne

section Extension

variable (L : Type*) [Field L] [Algebra (RatFunc K) L]

/-- The integral closure in a finite extension at the infinity valuation
ring. -/
abbrev RatFuncInfinityIntegralClosure :=
  integralClosure (RatFuncInfinityIntegers K) L

variable [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance infinityIntegralClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance infinityIntegralClosureIsDedekindDomain :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance infinityIntegralClosureIsFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance infinityBaseFaithfulSMulExtensionFractionRing :
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

local instance infinityFractionRingAlgebra :
    Algebra (FractionRing (RatFuncInfinityIntegers K))
      (FractionRing (RatFuncInfinityIntegralClosure K L)) :=
  FractionRing.liftAlgebra (RatFuncInfinityIntegers K)
    (FractionRing (RatFuncInfinityIntegralClosure K L))

local instance infinityFractionRingSeparable :
    Algebra.IsSeparable (FractionRing (RatFuncInfinityIntegers K))
      (FractionRing (RatFuncInfinityIntegralClosure K L)) := by
  refine Algebra.IsSeparable.of_equiv_equiv
    (ratFuncInfinityFractionRingEquiv K).symm.toRingEquiv
    (FractionRing.algEquiv (RatFuncInfinityIntegralClosure K L) L).symm.toRingEquiv ?_
  ext z
  exact IsFractionRing.algEquiv_commutes
    (ratFuncInfinityFractionRingEquiv K).symm
    (FractionRing.algEquiv (RatFuncInfinityIntegralClosure K L) L).symm z

/-- The norm/count identity at infinity in a finite separable extension of
`K(X)`: the order of the norm at infinity is the residue-degree-weighted sum
of the orders at all primes above infinity. -/
theorem count_spanSingleton_norm_at_infinity_eq_sum
    (x : FractionRing (RatFuncInfinityIntegralClosure K L)) :
    FractionalIdeal.count (FractionRing (RatFuncInfinityIntegers K))
        (ratFuncInfinityPlace K)
        (FractionalIdeal.spanSingleton (RatFuncInfinityIntegers K)⁰
          (Algebra.norm (FractionRing (RatFuncInfinityIntegers K)) x)) =
      ∑ P : (ratFuncInfinityPlace K).asIdeal.primesOver
          (RatFuncInfinityIntegralClosure K L),
        (P.1.inertiaDeg (RatFuncInfinityIntegers K) : ℤ) *
          FractionalIdeal.count
            (FractionRing (RatFuncInfinityIntegralClosure K L))
            (primeOverHeightOne (ratFuncInfinityPlace K) P)
            (FractionalIdeal.spanSingleton
              (RatFuncInfinityIntegralClosure K L)⁰ x) := by
  exact count_spanSingleton_norm_eq_sum_inertiaDeg_mul_count
    (ratFuncInfinityPlace K) x

end Extension

end

end BGS.CorvajaZannier
