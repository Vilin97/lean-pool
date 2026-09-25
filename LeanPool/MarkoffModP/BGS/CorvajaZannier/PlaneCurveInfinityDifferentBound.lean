/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionExhaustiveProductFormula
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.InfinityInertiaDegree
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.LocalReciprocalDiscriminant
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveDiscriminantBound
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveLocalReciprocalDiscriminant
public import Mathlib.Tactic

/-!
# The discriminant budget at infinity for a plane curve

Let `F` be a polynomial in `Y` with coefficients in `K[X]`, and suppose that
every coefficient has `X`-degree at most `a`.  On the infinity chart of the
first projection the integral normalization of the equation is obtained by
multiplying by `X⁻ᵃ`.  Its discriminant is therefore

`X⁻ᵃ⁽²ᵇ⁻²⁾ * discr(F)`.

The order of this element at infinity is exactly

`a * (2 * b - 2) - degree(discr(F))`.

This is the key complementarity needed for a Riemann--Hurwitz-free proof:
the finite discriminant contribution is at most `degree(discr(F))`, while the
above-infinity contribution is at most the displayed complementary order.
In particular, one must not bound the finite and infinity contributions
independently by `a * (2 * b - 2)`.

The module also constructs the coefficientwise integral polynomial over the
infinity valuation ring.  Identifying a reciprocal translate of that
polynomial with a primitive element of the plane-curve function field is the
remaining local normalization step.
-/

@[expose] public section

open scoped Polynomial nonZeroDivisors
open Multiplicative WithZero Polynomial IsDedekindDomain

namespace BGS.CorvajaZannier

noncomputable section

universe u

/-- A primitive polynomial over a local ring has a unit value at some center
as soon as its degree is smaller than the cardinality of a coefficient field.
The coefficient field and local ring are kept in the same universe, which is
the case needed for the infinity valuation ring of `K(X)`. -/
theorem exists_local_center_eval_isUnit_of_isPrimitive_natDegree_lt_card
    {K A : Type u} [Field K] [CommRing A] [IsLocalRing A]
    [IsBezout A] [Algebra K A]
    (F : A[X]) (hF : F.IsPrimitive)
    (hcardK : (F.natDegree : Cardinal) < Cardinal.mk K) :
    ∃ c : A, IsUnit (F.eval c) := by
  let m := IsLocalRing.maximalIdeal A
  let k := A ⧸ m
  let π : A →+* k := Ideal.Quotient.mk m
  have hFbar : F.map π ≠ 0 := by
    intro hzero
    have hcoeff : ∀ i, F.coeff i ∈ m := by
      intro i
      have hi := congrArg (fun q : k[X] => q.coeff i) hzero
      rw [Polynomial.coeff_map, Polynomial.coeff_zero] at hi
      exact Ideal.Quotient.eq_zero_iff_mem.mp hi
    have hcontent : F.contentIdeal ≤ m := by
      rw [Polynomial.contentIdeal_def, Ideal.span_le]
      intro x hx
      obtain ⟨i, _hi, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
      exact hcoeff i
    have htop : F.contentIdeal = ⊤ :=
      (Polynomial.isPrimitive_iff_contentIdeal_eq_top F).mp hF
    apply (IsLocalRing.maximalIdeal.isMaximal A).ne_top
    apply top_unique
    simpa [htop] using hcontent
  have hcard : (F.map π).natDegree < Cardinal.mk k := by
    have hdegree : ((F.map π).natDegree : Cardinal) ≤ F.natDegree := by
      exact_mod_cast Polynomial.natDegree_map_le
    exact (hdegree.trans_lt hcardK).trans_le
      (Cardinal.mk_le_of_injective
        (RingHom.injective (algebraMap K k)))
  obtain ⟨c, hc⟩ :=
    Polynomial.exists_eval_ne_zero_of_natDegree_lt_card (F.map π) hFbar hcard
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨a, IsLocalRing.notMem_maximalIdeal.mp ?_⟩
  intro hmem
  apply hc
  rw [Polynomial.eval_map_apply]
  change π (F.eval a) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]

/-! ## The normalized equation over `K(X)` -/

/-- Multiply an equation over `K[X]` by `X⁻ᵃ` on the infinity chart of the
first projection. -/
def infinityNormalizedPolynomial (a : ℕ) (F : K[X][X]) : (RatFunc K)[X] :=
  C ((RatFunc.X⁻¹) ^ a) * F.map (algebraMap K[X] (RatFunc K))

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
private theorem ratFunc_intDegree_pow (x : RatFunc K) (hx : x ≠ 0) (n : ℕ) :
    (x ^ n).intDegree = (n : ℤ) * x.intDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero n hx) hx, ih]
      push_cast
      ring

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
/-- Scaling by `X⁻ᵃ` does not change the degree in the second variable. -/
theorem infinityNormalizedPolynomial_natDegree
    (a : ℕ) (F : K[X][X]) :
    (infinityNormalizedPolynomial K a F).natDegree = F.natDegree := by
  rw [infinityNormalizedPolynomial]
  rw [natDegree_C_mul
    (pow_ne_zero a (inv_ne_zero RatFunc.X_ne_zero))]
  exact natDegree_map_eq_of_injective
    (RatFunc.algebraMap_injective K) F

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
/-- Exact discriminant formula for the infinity-normalized equation. -/
theorem infinityNormalizedPolynomial_discr
    (a : ℕ) (F : K[X][X]) :
    (infinityNormalizedPolynomial K a F).discr =
      ((RatFunc.X⁻¹) ^ a) ^ (2 * F.natDegree - 2) *
        algebraMap K[X] (RatFunc K) F.discr := by
  rw [infinityNormalizedPolynomial,
    discr_C_mul _ _ (pow_ne_zero a (inv_ne_zero RatFunc.X_ne_zero)),
    natDegree_map_eq_of_injective
      (RatFunc.algebraMap_injective K),
    discr_map_of_injective (algebraMap K[X] (RatFunc K))
      (RatFunc.algebraMap_injective K)]

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
/-- The infinity order of the normalized discriminant is the complement of
the finite polynomial discriminant degree in the full bidegree budget. -/
theorem ratFuncInfinityOrder_infinityNormalizedPolynomial_discr
    (a : ℕ) (F : K[X][X]) (hdiscr : F.discr ≠ 0) :
    ratFuncInfinityOrder (infinityNormalizedPolynomial K a F).discr =
      (a * (2 * F.natDegree - 2) : ℕ) - (F.discr.natDegree : ℤ) := by
  rw [infinityNormalizedPolynomial_discr]
  have hXinv : RatFunc.X⁻¹ ≠ (0 : RatFunc K) := inv_ne_zero RatFunc.X_ne_zero
  have hpow : ((RatFunc.X⁻¹) ^ a) ^ (2 * F.natDegree - 2) ≠
      (0 : RatFunc K) := pow_ne_zero _ (pow_ne_zero _ hXinv)
  have hmap : algebraMap K[X] (RatFunc K) F.discr ≠ 0 :=
    RatFunc.algebraMap_ne_zero hdiscr
  rw [ratFuncInfinityOrder,
    RatFunc.intDegree_mul hpow hmap,
    ratFunc_intDegree_pow K ((RatFunc.X⁻¹) ^ a)
      (pow_ne_zero _ hXinv) (2 * F.natDegree - 2),
    ratFunc_intDegree_pow K (RatFunc.X⁻¹) hXinv a,
    RatFunc.intDegree_inv, RatFunc.intDegree_X,
    RatFunc.intDegree_polynomial]
  push_cast
  ring

/-! ## The normalized equation over the infinity valuation ring -/

/-- A polynomial of degree at most `a`, multiplied by `X⁻ᵃ`, is integral at
infinity. -/
theorem infinityNormalizedCoefficient_mem
    (a : ℕ) (P : K[X]) (hdegree : P.natDegree ≤ a) :
    RatFunc.inftyValuation K
        ((RatFunc.X⁻¹) ^ a * algebraMap K[X] (RatFunc K) P) ≤ 1 := by
  by_cases hP : P = 0
  · simp [hP]
  have hXinv : RatFunc.X⁻¹ ≠ (0 : RatFunc K) := inv_ne_zero RatFunc.X_ne_zero
  have hleft : (RatFunc.X⁻¹) ^ a ≠ (0 : RatFunc K) := pow_ne_zero _ hXinv
  have hright : algebraMap K[X] (RatFunc K) P ≠ 0 :=
    RatFunc.algebraMap_ne_zero hP
  rw [RatFunc.inftyValuation_apply,
    RatFunc.inftyValuation_of_nonzero (F := K) (mul_ne_zero hleft hright),
    RatFunc.intDegree_mul hleft hright,
    ratFunc_intDegree_pow K (RatFunc.X⁻¹) hXinv a,
    RatFunc.intDegree_inv, RatFunc.intDegree_X,
    RatFunc.intDegree_polynomial]
  rw [← exp_zero, exp_le_exp]
  have hdegree' : (P.natDegree : ℤ) ≤ (a : ℤ) := by
    exact_mod_cast hdegree
  omega

/-- The coefficient `X⁻ᵃ P(X)` as an element of the infinity valuation
ring. -/
def infinityNormalizedCoefficient
    (a : ℕ) (P : K[X]) (hdegree : P.natDegree ≤ a) :
    RatFuncInfinityIntegers K :=
  ⟨(RatFunc.X⁻¹) ^ a * algebraMap K[X] (RatFunc K) P,
    infinityNormalizedCoefficient_mem K a P hdegree⟩

@[simp] theorem infinityNormalizedCoefficient_coe
    (a : ℕ) (P : K[X]) (hdegree : P.natDegree ≤ a) :
    ((infinityNormalizedCoefficient K a P hdegree :
        RatFuncInfinityIntegers K) : RatFunc K) =
      (RatFunc.X⁻¹) ^ a * algebraMap K[X] (RatFunc K) P :=
  rfl

/-- The coefficientwise integral infinity-chart equation. -/
def infinityNormalizedIntegralPolynomial
    (a : ℕ) (F : K[X][X])
    (hcoeff : ∀ i, (F.coeff i).natDegree ≤ a) :
    (RatFuncInfinityIntegers K)[X] :=
  F.sum fun i _ => monomial i
    (infinityNormalizedCoefficient K a (F.coeff i) (hcoeff i))

/-- Extending the integral infinity-chart equation to `K(X)` recovers the
field-valued normalization. -/
theorem infinityNormalizedIntegralPolynomial_map
    (a : ℕ) (F : K[X][X])
    (hcoeff : ∀ i, (F.coeff i).natDegree ≤ a) :
    (infinityNormalizedIntegralPolynomial K a F hcoeff).map
        (algebraMap (RatFuncInfinityIntegers K) (RatFunc K)) =
      infinityNormalizedPolynomial K a F := by
  ext i
  rw [coeff_map]
  simp only [infinityNormalizedIntegralPolynomial, coeff_sum,
    coeff_monomial]
  simp [Polynomial.sum]
  by_cases hzero : F.coeff i = 0
  · simp [hzero, infinityNormalizedPolynomial, coeff_C_mul]
  · rw [ite_eq_right hzero]
    have hrhs : (infinityNormalizedPolynomial K a F).coeff i =
        (RatFunc.X⁻¹) ^ a *
          algebraMap K[X] (RatFunc K) (F.coeff i) := by
      simp [infinityNormalizedPolynomial, coeff_C_mul]
    rw [hrhs]
    change algebraMap (RatFuncInfinityIntegers K) (RatFunc K)
        (infinityNormalizedCoefficient K a (F.coeff i) (hcoeff i)) =
      (RatFunc.X⁻¹) ^ a * algebraMap K[X] (RatFunc K) (F.coeff i)
    change ((infinityNormalizedCoefficient K a (F.coeff i) (hcoeff i) :
        RatFuncInfinityIntegers K) : RatFunc K) = _
    exact infinityNormalizedCoefficient_coe K a (F.coeff i) (hcoeff i)

end

end BGS.CorvajaZannier
