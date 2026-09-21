/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MonoidAlgebra.SingleZeroFactors
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.AssociatedGradedDivisibility
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringMonoidAlgebra
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.GradedDivisibility
public import Mathlib.Data.Rat.Defs

import Mathlib.Tactic.NormNum

/-!
# API checks for graded divisibility

The two-component fixture has independently nonzero grades zero and one. Its trailing grade is
zero, its leading grade is one, and it is not homogeneous. This distinguishes the minimum-grade
invariant used in LM24, Proposition 6.2.1 from the existing maximum-grade invariant, and it
distinguishes `RV` from the full associated graded ring `RV̂`.

The strictly negative finite-support monomial does not divide one in the nonpositive-exponent
monoid algebra: such a quotient would require a positive exponent. Its graded image therefore
also does not divide one, exercising the reflection direction of LM24, Corollary 6.2.3 and
excluding a nearby group-algebra model with unrestricted real exponents.

Finally, a principal coefficient multiplied by that strictly negative monomial has nonzero
monoid-algebra exponent. It lies outside `P̂`, distinguishing the principal graded subring from all
of `RV̂`. The principal-one and zero-boundary checks separately certify the exact embedded image
predicate for the paper's set `P`.
-/

open scoped DirectSum HahnSeries NatOrdinal

universe v

namespace Tests

public noncomputable section

/-- The strictly negative exponent used in the finite-support divisibility separator. -/
def gradedDivisibilityNegativeExponent :
    HahnSeries.Nonpositive.exponentMonoid ℝ :=
  ⟨-1, by norm_num⟩

/-- The finite-support Hahn monomial at exponent `-1`. -/
def gradedDivisibilityNegativeMonomial :
    HahnSeries.Nonpositive.finiteSupportSubring (G := ℝ) (K := ℚ) :=
  HahnSeries.Nonpositive.finiteSupportMonomial gradedDivisibilityNegativeExponent

/-- The chosen strictly negative exponent is not zero. -/
theorem gradedDivisibilityNegativeExponent_ne_zero :
    gradedDivisibilityNegativeExponent ≠ 0 := by
  intro h
  have := congrArg Subtype.val h
  norm_num [gradedDivisibilityNegativeExponent] at this

/-- The finite-support monomial at exponent `-1` is nonzero. -/
theorem gradedDivisibilityNegativeMonomial_ne_zero :
    gradedDivisibilityNegativeMonomial ≠ 0 := by
  intro h
  have hcoeff := congrArg
    (fun p : HahnSeries.Nonpositive.finiteSupportSubring (G := ℝ) (K := ℚ) ↦
      (((p : HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧).coeff (-1))) h
  simp [gradedDivisibilityNegativeMonomial, gradedDivisibilityNegativeExponent] at hcoeff

/-- A negative monomial cannot divide one within the nonpositive-exponent finite-support ring. -/
theorem gradedDivisibilityNegativeMonomial_not_dvd_one :
    ¬ gradedDivisibilityNegativeMonomial ∣ 1 := by
  intro hDvd
  obtain ⟨r, hr⟩ := hDvd
  let e := HahnSeries.Nonpositive.finiteSupportAddMonoidAlgebraEquiv
    (G := ℝ) (K := ℚ)
  have her : e r ≠ 0 := by
    intro hzero
    have hrZero : r = 0 := by
      apply e.injective
      simpa using hzero
    rw [hrZero, mul_zero] at hr
    exact one_ne_zero hr
  have heMonomial : e gradedDivisibilityNegativeMonomial =
      AddMonoidAlgebra.single gradedDivisibilityNegativeExponent 1 := by
    exact HahnSeries.Nonpositive.finiteSupportAddMonoidAlgebraEquiv_monomial
      gradedDivisibilityNegativeExponent
  have hProduct :
      AddMonoidAlgebra.single gradedDivisibilityNegativeExponent (1 : ℚ) * e r =
        AddMonoidAlgebra.single 0 1 := by
    calc
      AddMonoidAlgebra.single gradedDivisibilityNegativeExponent (1 : ℚ) * e r =
          e gradedDivisibilityNegativeMonomial * e r :=
        congrArg (· * e r) heMonomial.symm
      _ = e (gradedDivisibilityNegativeMonomial * r) :=
        (map_mul e gradedDivisibilityNegativeMonomial r).symm
      _ = e 1 := congrArg e hr.symm
      _ = 1 := map_one e
      _ = AddMonoidAlgebra.single 0 1 := AddMonoidAlgebra.one_def
  obtain ⟨_, _, ha, _⟩ :=
    AddMonoidAlgebra.exists_eq_single_zero_of_mul_eq_single_zero
      (R := ℚ) (M := HahnSeries.Nonpositive.exponentMonoid ℝ)
      (HahnSeries.Nonpositive.exponentMonoid_top_eq_zero ℝ)
      (AddMonoidAlgebra.single_ne_zero.mpr one_ne_zero)
      her hProduct
  have hcoeff := congrArg
    (fun f : AddMonoidAlgebra ℚ (HahnSeries.Nonpositive.exponentMonoid ℝ) ↦
      f gradedDivisibilityNegativeExponent) ha
  simp [gradedDivisibilityNegativeExponent_ne_zero] at hcoeff

/-- The graded image of the negative monomial does not divide the graded image of one. -/
theorem gradedDivisibilityNegativeMonomialGraded_not_dvd_one :
    ¬ Berarducci.finiteSupportGradedEmbedding ℚ
          gradedDivisibilityNegativeMonomial ∣
        Berarducci.finiteSupportGradedEmbedding ℚ 1 := by
  intro hDvd
  exact gradedDivisibilityNegativeMonomial_not_dvd_one
    ((Berarducci.finiteSupportGradedEmbedding_dvd_iff
      gradedDivisibilityNegativeMonomial 1).mp hDvd)

variable {K : Type v} [Field K] [CharZero K]

variable (K) in
/-- The degree-RV class of one, used as a nonzero principal-image boundary case. -/
def gradedDivisibilityPrincipalOneRV : Berarducci.HahnDegreeRV K :=
  (HahnSeries.Nonpositive.degreeValuation K).rv 1

variable (K) in
/-- The degree-RV class of one is principal in the exact sense of LM24, Definition 5.2.1. -/
theorem gradedDivisibilityPrincipalOneRV_isPrincipal :
    Berarducci.IsPrincipalRV (gradedDivisibilityPrincipalOneRV K) := by
  rw [Berarducci.isPrincipalRV_iff]
  exact ⟨1, HahnSeries.Nonpositive.isPrincipal_one, rfl⟩

variable (K) in
/-- The canonical graded image of the principal RV class of one belongs to `P`. -/
theorem gradedDivisibilityPrincipalOneRV_image :
    Berarducci.IsPrincipalRVImage
      ((HahnSeries.Nonpositive.degreeValuation K).rvInitialFormHom
        (gradedDivisibilityPrincipalOneRV K)) :=
  Berarducci.isPrincipalRVImage_initialForm
    (gradedDivisibilityPrincipalOneRV K)
    (gradedDivisibilityPrincipalOneRV_isPrincipal K)

variable (K) in
/-- Zero is not in the image of principal RV classes because principal series are nonzero. -/
theorem gradedDivisibilityPrincipalRVImage_zero_false :
    ¬ Berarducci.IsPrincipalRVImage (0 : Berarducci.DegreeGraded K) := by
  intro hzero
  exact (Berarducci.isPrincipalRVImage_iff _).mp hzero |>.1 rfl

/-- A graded element supported in the two distinct grades zero and one. -/
def gradedDivisibilityTwoComponent (a₀ : (HahnSeries.Nonpositive.degreeValuation K).Component 0)
    (a₁ : (HahnSeries.Nonpositive.degreeValuation K).Component 1) :
    Berarducci.DegreeGraded K :=
  DirectSum.of _ 0 a₀ + DirectSum.of _ 1 a₁

omit [CharZero K] in
/-- The two-component fixture retains its prescribed grade-zero and grade-one components. -/
theorem gradedDivisibilityTwoComponent_components
    (a₀ : (HahnSeries.Nonpositive.degreeValuation K).Component 0)
    (a₁ : (HahnSeries.Nonpositive.degreeValuation K).Component 1) :
    gradedDivisibilityTwoComponent a₀ a₁ 0 = a₀ ∧
      gradedDivisibilityTwoComponent a₀ a₁ 1 = a₁ := by
  simp [gradedDivisibilityTwoComponent, DirectSum.of_apply]

omit [CharZero K] in
/-- With a nonzero grade-zero component, the fixture's trailing grade is zero. -/
theorem gradedDivisibilityTwoComponent_trailingValue
    (a₀ : (HahnSeries.Nonpositive.degreeValuation K).Component 0)
    (a₁ : (HahnSeries.Nonpositive.degreeValuation K).Component 1)
    (ha₀ : a₀ ≠ 0) :
    MaxAddDegree.associatedGradedTrailingValue
        (HahnSeries.Nonpositive.degreeValuation K)
        (gradedDivisibilityTwoComponent a₀ a₁) = 0 := by
  let w := HahnSeries.Nonpositive.degreeValuation K
  apply (w.associatedGradedTrailingValue_eq_coe_iff
    (gradedDivisibilityTwoComponent a₀ a₁) 0).mpr
  exact ⟨by simpa [gradedDivisibilityTwoComponent, DirectSum.of_apply] using ha₀,
    fun _ _ ↦ bot_le⟩

omit [CharZero K] in
/-- With a nonzero grade-one component, the fixture's leading grade is one. -/
theorem gradedDivisibilityTwoComponent_leadingValue
    (a₀ : (HahnSeries.Nonpositive.degreeValuation K).Component 0)
    (a₁ : (HahnSeries.Nonpositive.degreeValuation K).Component 1)
    (ha₁ : a₁ ≠ 0) :
    (HahnSeries.Nonpositive.degreeValuation K).associatedGradedValue
        (gradedDivisibilityTwoComponent a₀ a₁) = 1 := by
  let w := HahnSeries.Nonpositive.degreeValuation K
  apply (w.associatedGradedValue_eq_coe_iff
    (gradedDivisibilityTwoComponent a₀ a₁) 1).mpr
  constructor
  · simpa [gradedDivisibilityTwoComponent, DirectSum.of_apply] using ha₁
  · intro i hi
    by_cases hi₀ : i = 0
    · subst i
      exact zero_le_one
    by_cases hi₁ : i = 1
    · subst i
      exact le_rfl
    have hzero : gradedDivisibilityTwoComponent a₀ a₁ i = 0 := by
      simp [gradedDivisibilityTwoComponent, DirectSum.of_apply, Ne.symm hi₀, Ne.symm hi₁]
    exact (hi hzero).elim

omit [CharZero K] in
/-- With both displayed components nonzero, the two-component fixture is not in degree RV. -/
theorem gradedDivisibilityTwoComponent_not_homogeneous
    (a₀ : (HahnSeries.Nonpositive.degreeValuation K).Component 0)
    (a₁ : (HahnSeries.Nonpositive.degreeValuation K).Component 1)
    (ha₀ : a₀ ≠ 0) (ha₁ : a₁ ≠ 0) :
    gradedDivisibilityTwoComponent a₀ a₁ ∉
      (HahnSeries.Nonpositive.degreeValuation K).homogeneousClasses := by
  let w := HahnSeries.Nonpositive.degreeValuation K
  intro hHomogeneous
  rcases (w.mem_homogeneousClasses_iff_extremeGrades
    (gradedDivisibilityTwoComponent a₀ a₁)).mp hHomogeneous with
      hzero | ⟨m, htrail, hlead⟩
  · apply ha₀
    rw [← (gradedDivisibilityTwoComponent_components a₀ a₁).1, hzero]
    rfl
  · have htrailZero := gradedDivisibilityTwoComponent_trailingValue a₀ a₁ ha₀
    have hleadOne := gradedDivisibilityTwoComponent_leadingValue a₀ a₁ ha₁
    have hzeroM : (0 : NatOrdinal) = m :=
      WithTop.coe_injective (htrailZero.symm.trans htrail)
    have honeM : (1 : NatOrdinal) = m :=
      WithBot.coe_injective (hleadOne.symm.trans hlead)
    exact zero_ne_one (hzeroM.trans honeM.symm)

/-- The strictly negative exponent used to separate `P̂` from `RV̂`. -/
def gradedDivisibilityNonprincipalExponent :
    HahnSeries.Nonpositive.exponentMonoid ℝ :=
  ⟨-1, by norm_num⟩

variable (K) in
/-- A principal coefficient multiplied by a strictly negative finite-support monomial. -/
def gradedDivisibilityNonprincipalElement :
    Berarducci.DegreeGraded K :=
  Berarducci.principalSubringEmbedding K 1 *
    Berarducci.finiteSupportGradedEmbedding K
      (HahnSeries.Nonpositive.finiteSupportMonomial (K := K)
        gradedDivisibilityNonprincipalExponent)

variable (K) in
/-- The nonprincipal fixture has coefficient one at the strictly negative monoid exponent. -/
theorem gradedDivisibilityNonprincipalElement_coordinate :
    Berarducci.degreeGradedEquivPrincipalMonoidAlgebra K
        (gradedDivisibilityNonprincipalElement K) =
      AddMonoidAlgebra.single gradedDivisibilityNonprincipalExponent 1 := by
  exact Berarducci.degreeGradedEquivPrincipalMonoidAlgebra_principal_monomial 1
    gradedDivisibilityNonprincipalExponent

variable (K) in
/-- A nonzero monoid exponent prevents the fixture from lying in the principal graded
subalgebra. -/
theorem gradedDivisibilityNonprincipalElement_not_mem :
    gradedDivisibilityNonprincipalElement K ∉
      Berarducci.principalSubringSubalgebra K := by
  intro hmem
  let eP := Berarducci.principalSubringEquivSubalgebra K
  let z : Berarducci.principalSubringSubalgebra K :=
    ⟨gradedDivisibilityNonprincipalElement K, hmem⟩
  let x := eP.symm z
  have hx : Berarducci.principalSubringEmbedding K x =
      gradedDivisibilityNonprincipalElement K := by
    calc
      Berarducci.principalSubringEmbedding K x =
          (eP x : Berarducci.DegreeGraded K) :=
        (Berarducci.principalSubringEquivSubalgebra_apply x).symm
      _ = gradedDivisibilityNonprincipalElement K :=
        congrArg Subtype.val (eP.apply_symm_apply z)
  have hcoordinates := congrArg
    (Berarducci.degreeGradedEquivPrincipalMonoidAlgebra K) hx
  rw [Berarducci.degreeGradedEquivPrincipalMonoidAlgebra_principal,
    gradedDivisibilityNonprincipalElement_coordinate] at hcoordinates
  have hcoeff := congrArg
    (fun f : AddMonoidAlgebra (Berarducci.PrincipalSubring K)
        (HahnSeries.Nonpositive.exponentMonoid ℝ) ↦
      f gradedDivisibilityNonprincipalExponent) hcoordinates
  have hne : gradedDivisibilityNonprincipalExponent ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    norm_num [gradedDivisibilityNonprincipalExponent] at this
  rw [AddMonoidAlgebra.single_apply, ite_eq_right (Ne.symm hne),
    AddMonoidAlgebra.single_apply, ite_eq_left rfl] at hcoeff
  have hgraded :
      (0 : Berarducci.DegreeGraded K) = 1 := by
    simpa using congrArg
      (Berarducci.principalSubringEmbedding K) hcoeff
  have hfinite :
      (0 : Berarducci.FiniteSupportRing (K := K)) = 1 := by
    apply Berarducci.finiteSupportGradedEmbedding_injective K
    calc
      Berarducci.finiteSupportGradedEmbedding K 0 = 0 :=
        map_zero (Berarducci.finiteSupportGradedEmbedding K)
      _ = 1 := hgraded
      _ = Berarducci.finiteSupportGradedEmbedding K 1 :=
        (map_one (Berarducci.finiteSupportGradedEmbedding K)).symm
  exact zero_ne_one hfinite

end

end Tests
