/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveFiniteDifferentBound
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveInfinityComplement
public import Mathlib.Tactic

/-!
# The canonical different degree of a plane function field

This module combines the sharp finite different bound with the complementary
bound above infinity.  Keeping the actual polynomial discriminant as the
intermediate budget makes its degree cancel between the two contributions.
The result is the expected first-projection canonical bound

`2 * degreeOf 0 f * degreeOf 1 f - 2 * degreeOf 0 f - 2 * degreeOf 1 f`.

No algebraic closure of the constant field is assumed.
-/

@[expose] public section

open scoped Polynomial nonZeroDivisors BigOperators
open Polynomial IsDedekindDomain

namespace BGS.CorvajaZannier

noncomputable section

variable {K : Type*} [Field K]

/-- Every bivariate polynomial has its tautological support-wise bidegree
bound given by its two `degreeOf` values. -/
theorem hasBidegreeAtMost_degreeOf
    (f : MvPolynomial (Fin 2) K) :
    BGS.External.HasBidegreeAtMost f
      (MvPolynomial.degreeOf 0 f) (MvPolynomial.degreeOf 1 f) := by
  intro m hm
  exact ⟨MvPolynomial.monomial_le_degreeOf 0 hm,
    MvPolynomial.monomial_le_degreeOf 1 hm⟩

/-- The second-coordinate equation's discriminant satisfies the sharp
bidegree estimate at the curve's actual coordinate degrees. -/
theorem planeCurvePolynomialInSecondCoordinate_discr_natDegree_le_degreeOf
    (f : MvPolynomial (Fin 2) K) :
    (planeCurvePolynomialInSecondCoordinate f).discr.natDegree ≤
      (2 * MvPolynomial.degreeOf 1 f - 2) *
        MvPolynomial.degreeOf 0 f := by
  exact planeCurvePolynomialInSecondCoordinate_discr_natDegree_le
    (hasBidegreeAtMost_degreeOf f)

variable [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)]

/-- The sharp finite-different estimate implies the usual bidegree-only
finite discriminant budget.  The canonical theorem below retains the sharper
intermediate discriminant so that it cancels against the infinity
complement. -/
theorem planeCurve_finiteDifferentDegree_le_bidegreeDiscriminantBudget
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hcardK : MvPolynomial.degreeOf 1 f < Fintype.card K) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    finiteExtensionFiniteDifferentDegree K (PlaneCurveFunctionField f)
        (finiteExtensionFiniteDifferentIdeal_ne_bot K
          (PlaneCurveFunctionField f)) ≤
      (2 * MvPolynomial.degreeOf 1 f - 2) *
        MvPolynomial.degreeOf 0 f := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  exact (planeCurve_finiteDifferentDegree_le_discrNatDegree
    hf hpartialSecond hcardK).trans
      (planeCurvePolynomialInSecondCoordinate_discr_natDegree_le_degreeOf f)

/-- The canonical different divisor of the first-coordinate plane function
field has the sharp bidegree bound. -/
theorem planeCurve_canonicalDifferentDivisor_degree_le
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hcardK : MvPolynomial.degreeOf 1 f < Fintype.card K) :
    let := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    let := planeCurveFirstCoordinateRatFuncAlgebra f hx
    let := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    let := separable_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    finiteExtensionDivisorDegree K (PlaneCurveFunctionField f)
        (finiteExtensionCanonicalDifferentDivisor K
          (PlaneCurveFunctionField f)
          (finiteExtensionFiniteDifferentIdeal_ne_bot K
            (PlaneCurveFunctionField f))) ≤
      2 * (MvPolynomial.degreeOf 0 f : ℤ) *
          (MvPolynomial.degreeOf 1 f : ℤ) -
        2 * (MvPolynomial.degreeOf 0 f : ℤ) -
          2 * (MvPolynomial.degreeOf 1 f : ℤ) := by
  intro domain hx ratFuncAlgebra finiteDimension separable
  let L := PlaneCurveFunctionField f
  let F : K[X][X] := planeCurvePolynomialInSecondCoordinate f
  let firstDegree := MvPolynomial.degreeOf 0 f
  let secondDegree := MvPolynomial.degreeOf 1 f
  have hFne : F ≠ 0 := by
    dsimp only [F]
    simpa only [map_zero] using
      (planeCurvePolynomialInSecondCoordinate (K := K)).injective.ne hf.ne_zero
  have hsupport : F.support.Nonempty :=
    Polynomial.nonempty_support_iff.mpr hFne
  let localFirstDegree : ℕ :=
    F.support.sup (fun i => (F.coeff i).natDegree)
  obtain ⟨i, hiSupport, hiMax⟩ := Finset.exists_mem_eq_sup
    F.support hsupport (fun i => (F.coeff i).natDegree)
  have hFi : F.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hiSupport
  have hiDegree : (F.coeff i).natDegree = localFirstDegree := by
    simpa only [localFirstDegree] using hiMax.symm
  have hcoeff : ∀ j, (F.coeff j).natDegree ≤ localFirstDegree := by
    intro j
    by_cases hj : F.coeff j = 0
    · simp [hj]
    · change (F.coeff j).natDegree ≤
        F.support.sup (fun i => (F.coeff i).natDegree)
      exact Finset.le_sup (s := F.support)
        (f := fun i : ℕ => (F.coeff i).natDegree)
        (Polynomial.mem_support_iff.mpr hj)
  have hlocalFirstDegree_le : localFirstDegree ≤ firstDegree := by
    rw [← hiDegree]
    exact planeCurvePolynomialInSecondCoordinate_coeff_natDegree_le_degreeOf_first
      f i
  let v : L := planeCurveFunction f 1
  have hrootF : Polynomial.aeval v
      (F.map (algebraMap K[X] (RatFunc K))) = 0 := by
    simpa only [F, v] using
      aeval_planeCurvePolynomialInSecondCoordinate_ratFunc_eq_zero
        hf hpartialSecond
  have hrootNormalized : Polynomial.aeval v
      (infinityNormalizedPolynomial K localFirstDegree F) = 0 := by
    rw [infinityNormalizedPolynomial]
    simp only [map_mul, aeval_C, hrootF, mul_zero]
  let _ : SMul (RatFunc K) L := Algebra.toSMul
  let _ : MulAction (RatFunc K) L :=
    (Algebra.toModule : Module (RatFunc K) L).toMulAction
  have hrootIntegral : Polynomial.aeval v
      (infinityNormalizedIntegralPolynomial K localFirstDegree F hcoeff) = 0 := by
    have hmap := Polynomial.aeval_map_algebraMap (RatFunc K) v
      (infinityNormalizedIntegralPolynomial K localFirstDegree F hcoeff)
    rw [← hmap]
    rw [infinityNormalizedIntegralPolynomial_map]
    exact hrootNormalized
  have hprimitive : Algebra.adjoin (RatFunc K) {v} = ⊤ := by
    exact adjoin_secondCoordinate_over_firstRatFunc_eq_top
      hf hpartialSecond
  have hFnatDegree : F.natDegree = secondDegree := by
    simp [F, secondDegree]
  have hfinrank : Module.finrank (RatFunc K) L = secondDegree :=
    finrank_planeCurveFunctionField_over_ratFunc_eq_degreeOf_second
      hf hpartialSecond
  have hFdegree : F.natDegree = Module.finrank (RatFunc K) L :=
    hFnatDegree.trans hfinrank.symm
  have hFdiscr : F.discr ≠ 0 := by
    simpa only [F] using
      planeCurvePolynomialInSecondCoordinate_discr_ne_zero
        hf hpartialSecond
  have hcard : (F.natDegree : Cardinal) < Cardinal.mk K := by
    have hdegree : F.natDegree = secondDegree := by
      simp [F, secondDegree]
    rw [hdegree]
    simpa only [secondDegree, Cardinal.mk_fintype, Nat.cast_lt] using hcardK
  have hFinite : finiteExtensionFiniteDifferentDegree K L
      (finiteExtensionFiniteDifferentIdeal_ne_bot K L) ≤ F.discr.natDegree := by
    simpa only [F] using
      planeCurve_finiteDifferentDegree_le_discrNatDegree
        hf hpartialSecond hcardK
  have hInfinity : (infinityDifferentDegree K L : ℤ) ≤
      (localFirstDegree * (2 * F.natDegree - 2) : ℕ) -
        (F.discr.natDegree : ℤ) :=
    planeCurveInfinityDifferentDegree_le_bidegreeComplement
      K L localFirstDegree F hcoeff i hFi hiDegree v
        hrootIntegral hprimitive hFdegree hFdiscr hcard
  have hCanonical := finiteExtensionCanonicalDifferentDivisor_degree_le_of_bounds
    K L F.discr.natDegree
      (localFirstDegree * (2 * F.natDegree - 2)) hFinite hInfinity
  have hsecondPos : 0 < secondDegree := by
    exact degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond
  have htwo_le : 2 ≤ 2 * secondDegree := by omega
  have hlocalFirstDegreeInt : (localFirstDegree : ℤ) ≤ firstDegree := by
    exact_mod_cast hlocalFirstDegree_le
  have hfactorNonneg : (0 : ℤ) ≤ 2 * (secondDegree : ℤ) - 2 := by
    omega
  have hmul : (localFirstDegree : ℤ) *
        (2 * (secondDegree : ℤ) - 2) ≤
      (firstDegree : ℤ) * (2 * (secondDegree : ℤ) - 2) :=
    mul_le_mul_of_nonneg_right hlocalFirstDegreeInt hfactorNonneg
  have hbudgetCast :
      ((localFirstDegree * (2 * secondDegree - 2) : ℕ) : ℤ) =
        (localFirstDegree : ℤ) * (2 * (secondDegree : ℤ) - 2) := by
    rw [Nat.cast_mul, Nat.cast_sub htwo_le]
    push_cast
    rfl
  calc
    finiteExtensionDivisorDegree K L
        (finiteExtensionCanonicalDifferentDivisor K L
          (finiteExtensionFiniteDifferentIdeal_ne_bot K L)) ≤
      ((localFirstDegree * (2 * secondDegree - 2) : ℕ) : ℤ) -
        2 * (secondDegree : ℤ) := by
          simpa only [hFnatDegree, hfinrank] using hCanonical
    _ = (localFirstDegree : ℤ) * (2 * (secondDegree : ℤ) - 2) -
        2 * (secondDegree : ℤ) := by rw [hbudgetCast]
    _ ≤ (firstDegree : ℤ) * (2 * (secondDegree : ℤ) - 2) -
        2 * (secondDegree : ℤ) := sub_le_sub_right hmul _
    _ = 2 * (MvPolynomial.degreeOf 0 f : ℤ) *
          (MvPolynomial.degreeOf 1 f : ℤ) -
        2 * (MvPolynomial.degreeOf 0 f : ℤ) -
          2 * (MvPolynomial.degreeOf 1 f : ℤ) := by
      dsimp only [firstDegree, secondDegree]
      ring

end
end BGS.CorvajaZannier
