/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveCanonicalEulerBound
import LeanPool.MarkoffModP.BGS.HasseWeil.AffinePointPlace
import Mathlib.Tactic

/-!
# Saving one boundary degree at a shared affine origin

The degree-only plane-curve estimate bounds the zero/pole support of the two
coordinate functions by adding their two support degrees.  If the curve
contains the affine origin, the finite place selected above that point lies
in both supports.  Since every place has positive degree, the union estimate
saves at least one.

This argument does not assert that a branch above an arbitrary singular
rational point has residue degree one.  Positivity of the selected place
degree is sufficient for the one-unit saving.
-/

open scoped Polynomial BigOperators

namespace BGS.CorvajaZannier

noncomputable section

private theorem sum_union_add_weight_le_sum_add_sum
    {ι : Type*} [DecidableEq ι] (s t : Finset ι) (g : ι → ℕ)
    {q : ι} (hqs : q ∈ s) (hqt : q ∈ t) :
    (∑ i ∈ s ∪ t, g i) + g q ≤
      (∑ i ∈ s, g i) + ∑ i ∈ t, g i := by
  have hdisjoint : Disjoint (t \ s) {q} := by
    rw [Finset.disjoint_singleton_right]
    intro hq
    exact (Finset.mem_sdiff.mp hq).2 hqs
  have hsubset : (t \ s) ∪ {q} ⊆ t := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (Finset.mem_sdiff.mp hi).1
    · rw [Finset.mem_singleton] at hi
      simpa [hi] using hqt
  have hremaining :
      (∑ i ∈ t \ s, g i) + g q ≤ ∑ i ∈ t, g i := by
    have hsum :
        (∑ i ∈ (t \ s) ∪ {q}, g i) ≤ ∑ i ∈ t, g i :=
      Finset.sum_le_sum_of_subset hsubset
    rw [Finset.sum_union hdisjoint] at hsum
    simpa using hsum
  calc
    (∑ i ∈ s ∪ t, g i) + g q =
        ((∑ i ∈ s, g i) + ∑ i ∈ t \ s, g i) + g q := by
      rw [show s ∪ t = s ∪ (t \ s) by ext i; simp,
        Finset.sum_union Finset.disjoint_sdiff]
    _ = (∑ i ∈ s, g i) + ((∑ i ∈ t \ s, g i) + g q) := by
      omega
    _ ≤ (∑ i ∈ s, g i) + ∑ i ∈ t, g i :=
      Nat.add_le_add_left hremaining _

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]

/-- If an irreducible plane curve contains the affine origin, then the
zero/pole boundary of positive powers of its two coordinate functions saves
one degree compared with the disjoint-support estimate. -/
theorem planeCurve_propositionTwoExceptionalPlaces_weightedDegree_add_one_le
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (origin : AffinePlaneCurvePoint f)
    (horiginFirst : origin.1.1 = 0)
    (horiginSecond : origin.1.2 = 0)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    (∑ w ∈ propositionTwoExceptionalPlaces K (PlaneCurveFunctionField f)
        ((planeCurveFunction f 0) ^ m) ((planeCurveFunction f 1) ^ n),
        finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) w) + 1 ≤
      2 * (MvPolynomial.degreeOf 0 f + MvPolynomial.degreeOf 1 f) := by
  classical
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let L := PlaneCurveFunctionField f
  let x : L := planeCurveFunction f 0
  let y : L := planeCurveFunction f 1
  have hxTrans : Transcendental K x :=
    firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  have hyTrans : Transcendental K y :=
    secondCoordinate_transcendental hf
      (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
  have hx0 : x ≠ 0 := by
    intro h
    apply hxTrans
    rw [h]
    exact isAlgebraic_zero
  have hy0 : y ≠ 0 := by
    intro h
    apply hyTrans
    rw [h]
    exact isAlgebraic_zero
  let : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hxTrans
  let : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra (Polynomial K) L :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) L).comp
        (algebraMap (Polynomial K) (RatFunc K)))
  let : IsScalarTower (Polynomial K) (RatFunc K) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let q : FiniteExtensionFinitePlace K L :=
    BGS.HasseWeil.affinePointExhaustiveFinitePlace
      hf hpartialFirst hpartialSecond origin
  have hqSpec :=
    BGS.HasseWeil.affinePointExhaustiveFinitePlace_spec
      hf hpartialFirst hpartialSecond origin
  have hqx : 0 < finitePlaceOrder q x := by
    simpa only [q, x, horiginFirst, map_zero, sub_zero] using hqSpec.2.1
  have hqy : 0 < finitePlaceOrder q y := by
    simpa only [q, y, horiginSecond, map_zero, sub_zero] using hqSpec.2.2
  have hxDegree : finiteExtensionPositiveDegree K L x =
      MvPolynomial.degreeOf 1 f := by
    have hheight := finiteExtensionPositiveDegree_polynomial
      K L Polynomial.X Polynomial.X_ne_zero
    have hmap : algebraMap (RatFunc K) L
        (algebraMap K[X] (RatFunc K) Polynomial.X) = x := by
      change ratFuncSpecialization x hxTrans RatFunc.X = x
      exact planeCurveFirstCoordinateRatFuncAlgebra_X f hxTrans
    rw [hmap,
      finrank_planeCurveFunctionField_over_ratFunc_eq_degreeOf_second
        hf hpartialSecond] at hheight
    simpa using hheight
  have hyDegree : finiteExtensionPositiveDegree K L y ≤
      MvPolynomial.degreeOf 0 f :=
    finiteExtensionPositiveDegree_planeCurveSecondCoordinate_le_degreeOf_first
      hf hpartialFirst hpartialSecond
  have hsupportX :
      (finiteExtensionPrincipalDivisor K L (x ^ m)).support =
        (finiteExtensionPrincipalDivisor K L x).support := by
    rw [finiteExtensionPrincipalDivisor_pow K L x hx0 m]
    ext w
    simp [Finsupp.mem_support_iff, hm.ne']
  have hsupportY :
      (finiteExtensionPrincipalDivisor K L (y ^ n)).support =
        (finiteExtensionPrincipalDivisor K L y).support := by
    rw [finiteExtensionPrincipalDivisor_pow K L y hy0 n]
    ext w
    simp [Finsupp.mem_support_iff, hn.ne']
  let v : FiniteExtensionPlace K L := .inl q
  let s := (finiteExtensionPrincipalDivisor K L x).support
  let t := (finiteExtensionPrincipalDivisor K L y).support
  let degree : FiniteExtensionPlace K L → ℕ :=
    finiteExtensionPlaceDegree K L
  have hvs : v ∈ s := by
    dsimp only [s, v]
    rw [Finsupp.mem_support_iff,
      finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder]
    omega
  have hvt : v ∈ t := by
    dsimp only [t, v]
    rw [Finsupp.mem_support_iff,
      finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder]
    omega
  have hvDegree : 1 ≤ degree v := by
    dsimp only [degree, v]
    exact finiteExtensionPlaceDegree_inl_pos K L q
  have hoverlap :
      (∑ w ∈ s ∪ t, degree w) + degree v ≤
        (∑ w ∈ s, degree w) + ∑ w ∈ t, degree w :=
    sum_union_add_weight_le_sum_add_sum s t degree hvs hvt
  have hsupportSum :
      (∑ w ∈ s, degree w) + ∑ w ∈ t, degree w ≤
        2 * (MvPolynomial.degreeOf 0 f + MvPolynomial.degreeOf 1 f) := by
    have hxSupport :
        (∑ w ∈ s, degree w) ≤
          2 * finiteExtensionPositiveDegree K L x := by
      exact finiteExtensionPrincipalDivisor_supportDegree_le_two_mul_height
        K L x hx0
    have hySupport :
        (∑ w ∈ t, degree w) ≤
          2 * finiteExtensionPositiveDegree K L y := by
      exact finiteExtensionPrincipalDivisor_supportDegree_le_two_mul_height
        K L y hy0
    rw [hxDegree] at hxSupport
    omega
  change
    (∑ w ∈ (finiteExtensionPrincipalDivisor K L (x ^ m)).support ∪
        (finiteExtensionPrincipalDivisor K L (y ^ n)).support,
        degree w) + 1 ≤ _
  rw [hsupportX, hsupportY]
  exact (Nat.add_le_add_left hvDegree _).trans
    (hoverlap.trans hsupportSum)

/-- Adding the canonical divisor preserves the one-unit saving from a common
affine origin. -/
theorem planeCurve_canonicalDifferent_add_propositionTwoExceptional_add_one_le
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hcardK : MvPolynomial.degreeOf 1 f < Fintype.card K)
    (origin : AffinePlaneCurvePoint f)
    (horiginFirst : origin.1.1 = 0)
    (horiginSecond : origin.1.2 = 0)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    finiteExtensionDivisorDegree K (PlaneCurveFunctionField f)
          (finiteExtensionCanonicalDifferentDivisor K
            (PlaneCurveFunctionField f)
            (finiteExtensionFiniteDifferentIdeal_ne_bot K
              (PlaneCurveFunctionField f))) +
        (∑ w ∈ propositionTwoExceptionalPlaces K
            (PlaneCurveFunctionField f)
            ((planeCurveFunction f 0) ^ m) ((planeCurveFunction f 1) ^ n),
          finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) w : ℤ) +
        1 ≤
      (2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f : ℕ) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  have hcanonical :=
    planeCurve_canonicalDifferentDivisor_degree_le
      hf hpartialSecond hcardK
  have hboundary :=
    planeCurve_propositionTwoExceptionalPlaces_weightedDegree_add_one_le
      hf hpartialFirst hpartialSecond origin
        horiginFirst horiginSecond m n hm hn
  have hboundaryInt :
      ((∑ w ∈ propositionTwoExceptionalPlaces K
          (PlaneCurveFunctionField f)
          ((planeCurveFunction f 0) ^ m) ((planeCurveFunction f 1) ^ n),
        finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) w : ℕ) : ℤ) +
        1 ≤
      2 * ((MvPolynomial.degreeOf 0 f : ℤ) +
        MvPolynomial.degreeOf 1 f) := by
    exact_mod_cast hboundary
  norm_num at hcanonical hboundaryInt ⊢
  omega

end

end BGS.CorvajaZannier
