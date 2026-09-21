/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.NormalizedSeriesMaximalFinite
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.Fixtures.ApproachZero

/-!
# API checks for series-level maximal finite-support divisors

This module formalizes the mechanism in LM24, Example 5.5.4. Put `x = t⁻¹`, let
`p₀ = 1 - x²`, let `p₁ = x + 1`, and let `a` be the principal series with support
`{-1/(n+1) | n ∈ ℕ}`. The series tested here is

`b = p₀ * a + p₁`.

The leading RV class of `b` has normalized maximal finite-support divisor `p₀`, whereas the
full series has normalized maximal finite-support divisor `p₁`. The proof also certifies that
`p₀ ≠ p₁`. Thus the client rejects the incorrect shortcut that defines the series-level
divisor solely from the leading RV class. Pairwise gcd existence and unit classification remain
explicit parameters.
-/

open scoped HahnSeries NatOrdinal

namespace Tests

public noncomputable section

/-- The finite-support monomial `x = t⁻¹` used in LM24, Example 5.5.4. -/
def seriesMaximalExampleMonomial : Berarducci.FiniteSupportRing (K := ℚ) :=
  HahnSeries.Nonpositive.finiteSupportMonomial (K := ℚ) ⟨-1, by norm_num⟩

/-- The leading-RV maximal divisor `p₀ = 1 - t⁻²` from LM24, Example 5.5.4. -/
def seriesMaximalExampleRVDivisor : Berarducci.FiniteSupportRing (K := ℚ) :=
  1 - seriesMaximalExampleMonomial * seriesMaximalExampleMonomial

/-- The full-series maximal divisor `p₁ = t⁻¹ + 1` from LM24, Example 5.5.4. -/
def seriesMaximalExampleDivisor : Berarducci.FiniteSupportRing (K := ℚ) :=
  seriesMaximalExampleMonomial + 1

/-- The Hahn series `b = (1 - t⁻²)a + (t⁻¹ + 1)` from LM24, Example 5.5.4. -/
def seriesMaximalExample : Berarducci.Series ℚ :=
  (seriesMaximalExampleRVDivisor : Berarducci.Series ℚ) *
      approachZeroNonpositive +
    (seriesMaximalExampleDivisor : Berarducci.Series ℚ)

/-- The full-series divisor `t⁻¹ + 1` is monic at its greatest support exponent. -/
theorem seriesMaximalExampleDivisor_isMonic :
    HahnSeries.Nonpositive.IsMonicFiniteSupport seriesMaximalExampleDivisor := by
  rw [HahnSeries.Nonpositive.isMonicFiniteSupport_iff]
  refine ⟨0, ⟨?_, ?_⟩, ?_⟩
  · rw [HahnSeries.mem_support]
    simp [seriesMaximalExampleDivisor, seriesMaximalExampleMonomial]
  · intro g hg
    exact HahnSeries.Nonpositive.support_subset
      (seriesMaximalExampleDivisor : HahnSeries.Nonpositive ℝ ℚ) hg
  · simp [seriesMaximalExampleDivisor, seriesMaximalExampleMonomial]

/-- The coefficient of `1 - t⁻²` at its greatest support exponent is one. -/
theorem seriesMaximalExampleRVDivisor_coeff_zero :
    (((seriesMaximalExampleRVDivisor : Berarducci.Series ℚ) : ℚ⟦ℝ⟧).coeff 0) =
      1 := by
  simp only [seriesMaximalExampleRVDivisor, seriesMaximalExampleMonomial,
    HahnSeries.Nonpositive.finiteSupportMonomial_mul, AddSubgroupClass.coe_sub,
    OneMemClass.coe_one, HahnSeries.Nonpositive.coe_finiteSupportMonomial,
    HahnSeries.coeff_sub', Pi.sub_apply, HahnSeries.coeff_one, reduceIte, sub_eq_self]
  rw [HahnSeries.coeff_single_of_ne (by norm_num)]

/-- The leading-RV divisor `1 - t⁻²` is monic at its greatest support exponent. -/
theorem seriesMaximalExampleRVDivisor_isMonic :
    HahnSeries.Nonpositive.IsMonicFiniteSupport seriesMaximalExampleRVDivisor := by
  rw [HahnSeries.Nonpositive.isMonicFiniteSupport_iff]
  refine ⟨0, ⟨?_, ?_⟩, seriesMaximalExampleRVDivisor_coeff_zero⟩
  · rw [HahnSeries.mem_support, seriesMaximalExampleRVDivisor_coeff_zero]
    norm_num
  · intro g hg
    exact HahnSeries.Nonpositive.support_subset
      (seriesMaximalExampleRVDivisor : HahnSeries.Nonpositive ℝ ℚ) hg

/-- The leading-RV divisor is nonzero. -/
theorem seriesMaximalExampleRVDivisor_ne_zero :
    seriesMaximalExampleRVDivisor ≠ 0 :=
  seriesMaximalExampleRVDivisor_isMonic.ne_zero

/-- The leading-RV and full-series divisors in LM24, Example 5.5.4 are distinct. -/
theorem seriesMaximalExample_divisors_ne :
    seriesMaximalExampleRVDivisor ≠ seriesMaximalExampleDivisor := by
  intro h
  have hcoeff := congrArg
    (fun p : Berarducci.FiniteSupportRing (K := ℚ) ↦
      (((p : Berarducci.Series ℚ) : ℚ⟦ℝ⟧).coeff (-1))) h
  simp [seriesMaximalExampleRVDivisor, seriesMaximalExampleDivisor,
    seriesMaximalExampleMonomial] at hcoeff

/-- The full-series divisor divides the leading-RV divisor:
`t⁻¹ + 1 ∣ 1 - t⁻²`. -/
theorem seriesMaximalExampleDivisor_dvd_rvDivisor :
    seriesMaximalExampleDivisor ∣ seriesMaximalExampleRVDivisor := by
  refine ⟨1 - seriesMaximalExampleMonomial, ?_⟩
  dsimp only [seriesMaximalExampleRVDivisor, seriesMaximalExampleDivisor]
  ring

/-- The associated-graded representative of the leading RV class in LM24,
Example 5.5.4. -/
def seriesMaximalExampleLeadingGraded :
    Berarducci.DegreeGraded ℚ :=
  (((HahnSeries.Nonpositive.degreeValuation ℚ).rvEquivHomogeneous
      ((HahnSeries.Nonpositive.degreeValuation ℚ).rv
        seriesMaximalExample) :
      (HahnSeries.Nonpositive.degreeValuation ℚ).HomogeneousClasses) :
    Berarducci.DegreeGraded ℚ)

/-- The leading-RV divisor has Hahn-series degree zero. -/
theorem seriesMaximalExampleRVDivisor_degree :
    ((seriesMaximalExampleRVDivisor : Berarducci.Series ℚ) : ℚ⟦ℝ⟧).degree =
      0 := by
  rw [HahnSeries.degree_eq_zero]
  exact ⟨by
      intro hzero
      apply seriesMaximalExampleRVDivisor_ne_zero
      exact Subtype.ext (Subtype.ext hzero),
    (HahnSeries.Nonpositive.mem_finiteSupportSubring_iff
      (seriesMaximalExampleRVDivisor : Berarducci.Series ℚ)).mp
        seriesMaximalExampleRVDivisor.2⟩

/-- The full-series divisor has Hahn-series degree zero. -/
theorem seriesMaximalExampleDivisor_degree :
    ((seriesMaximalExampleDivisor : Berarducci.Series ℚ) : ℚ⟦ℝ⟧).degree = 0 := by
  rw [HahnSeries.degree_eq_zero]
  exact ⟨by
      intro hzero
      apply seriesMaximalExampleDivisor_isMonic.ne_zero
      exact Subtype.ext (Subtype.ext hzero),
    (HahnSeries.Nonpositive.mem_finiteSupportSubring_iff
      (seriesMaximalExampleDivisor : Berarducci.Series ℚ)).mp
        seriesMaximalExampleDivisor.2⟩

/-- The leading term `(1 - t⁻²)a` has degree one. -/
theorem seriesMaximalExample_leading_degree :
    (((seriesMaximalExampleRVDivisor : Berarducci.Series ℚ) *
        approachZeroNonpositive : Berarducci.Series ℚ) : ℚ⟦ℝ⟧).degree = 1 := by
  rw [HahnSeries.Nonpositive.degree_mul, seriesMaximalExampleRVDivisor_degree,
    approachZero_degree_eq_one, zero_add]

/-- The series in LM24, Example 5.5.4 has degree one. -/
theorem seriesMaximalExample_degree :
    (seriesMaximalExample : ℚ⟦ℝ⟧).degree = 1 := by
  calc
    (seriesMaximalExample : ℚ⟦ℝ⟧).degree =
        (((seriesMaximalExampleRVDivisor : Berarducci.Series ℚ) *
          approachZeroNonpositive : Berarducci.Series ℚ) : ℚ⟦ℝ⟧).degree := by
      apply HahnSeries.degree_add_eq_left_of_lt
      rw [seriesMaximalExample_leading_degree,
        seriesMaximalExampleDivisor_degree]
      norm_num
    _ = 1 := seriesMaximalExample_leading_degree

/-- The leading RV class of the example is the RV class of `(1 - t⁻²)a`. -/
theorem seriesMaximalExample_rv_eq :
    (HahnSeries.Nonpositive.degreeValuation ℚ).rv
        seriesMaximalExample =
      (HahnSeries.Nonpositive.degreeValuation ℚ).rv
        ((seriesMaximalExampleRVDivisor : Berarducci.Series ℚ) *
          approachZeroNonpositive) := by
  let w := HahnSeries.Nonpositive.degreeValuation ℚ
  have hvalue : w seriesMaximalExample ≠ ⊥ := by
    rw [HahnSeries.Nonpositive.degreeValuation_apply,
      seriesMaximalExample_degree]
    norm_num
  apply (w.rv_eq_iff_of_value_ne_bot hvalue).mpr
  rw [HahnSeries.Nonpositive.degreeValuation_apply,
    HahnSeries.Nonpositive.degreeValuation_apply,
    seriesMaximalExample_degree]
  have hdiff : seriesMaximalExample -
      (seriesMaximalExampleRVDivisor : Berarducci.Series ℚ) *
        approachZeroNonpositive =
      (seriesMaximalExampleDivisor : Berarducci.Series ℚ) := by
    simp only [seriesMaximalExample]
    abel
  rw [hdiff, seriesMaximalExampleDivisor_degree]
  norm_num

/-- The associated-graded representative of the example's leading RV class is its
degree-one initial form. -/
theorem seriesMaximalExampleLeadingGraded_eq :
    seriesMaximalExampleLeadingGraded =
      DirectSum.of
        (HahnSeries.Nonpositive.degreeValuation ℚ).Component
        1
        (Berarducci.degreeLayerMk 1
          ((seriesMaximalExampleRVDivisor : Berarducci.Series ℚ) *
            approachZeroNonpositive)
          seriesMaximalExample_leading_degree.le) := by
  rw [seriesMaximalExampleLeadingGraded, seriesMaximalExample_rv_eq]
  calc
    _ = (Berarducci.degreeHomogeneousClass 1
          (Berarducci.degreeLayerMk 1
            ((seriesMaximalExampleRVDivisor : Berarducci.Series ℚ) *
              approachZeroNonpositive)
            seriesMaximalExample_leading_degree.le) :
        Berarducci.DegreeGraded ℚ) :=
      congrArg Subtype.val
        (Berarducci.rvEquivHomogeneous_rv_eq_degreeHomogeneousClass 1
            ((seriesMaximalExampleRVDivisor : Berarducci.Series ℚ) *
              approachZeroNonpositive)
            seriesMaximalExample_leading_degree)
    _ = _ := Berarducci.coe_degreeHomogeneousClass 1 _

/-- The leading RV class has maximal finite-support divisor class represented by
`1 - t⁻²`. -/
theorem seriesMaximalExample_isRVMaximalFiniteSupportDivisor :
    Berarducci.IsRVMaximalFiniteSupportDivisor
      ((HahnSeries.Nonpositive.degreeValuation ℚ).rv
        seriesMaximalExample)
      (Associates.mk seriesMaximalExampleRVDivisor) := by
  rw [seriesMaximalExample_rv_eq]
  exact Berarducci.isRVMaximalFiniteSupportDivisor_finiteSupport_mul_principal 1
    seriesMaximalExampleRVDivisor
      seriesMaximalExampleRVDivisor_ne_zero approachZeroNonpositive
      approachZero_isPrincipal approachZero_degree_eq_one

/-- The associated-graded representative of the leading RV class has maximal
finite-support divisor represented by `1 - t⁻²`. -/
theorem seriesMaximalExample_isGradedMaximalFiniteSupportDivisor :
    Berarducci.IsGradedMaximalFiniteSupportDivisor
      seriesMaximalExampleLeadingGraded
      (Associates.mk seriesMaximalExampleRVDivisor) := by
  rw [seriesMaximalExampleLeadingGraded_eq]
  exact Berarducci.isGradedMaximalFiniteSupportDivisor_finiteSupport_mul_principal 1
    seriesMaximalExampleRVDivisor approachZeroNonpositive
      approachZero_isPrincipal approachZero_degree_eq_one

/-- The full series has maximal finite-support divisor class represented by `t⁻¹ + 1`. -/
theorem seriesMaximalExample_isSeriesMaximalFiniteSupportDivisor :
    Berarducci.IsSeriesMaximalFiniteSupportDivisor seriesMaximalExample
      (Associates.mk seriesMaximalExampleDivisor) := by
  apply (Berarducci.isSeriesMaximalFiniteSupportDivisor_mk_iff
    seriesMaximalExample seriesMaximalExampleDivisor).mpr
  intro q
  rw [Berarducci.coe_dvd_iff_dvd_rvMaximal_and_residual
    seriesMaximalExample approachZeroNonpositive seriesMaximalExampleRVDivisor q
      seriesMaximalExample_isRVMaximalFiniteSupportDivisor]
  have hresidual : seriesMaximalExample -
      (seriesMaximalExampleRVDivisor : Berarducci.Series ℚ) *
        approachZeroNonpositive =
      (seriesMaximalExampleDivisor : Berarducci.Series ℚ) := by
    simp only [seriesMaximalExample]
    abel
  rw [hresidual, ← Berarducci.finiteSupport_dvd_iff_coe_dvd]
  constructor
  · exact fun h ↦ h.2
  · intro hq
    exact ⟨dvd_trans hq seriesMaximalExampleDivisor_dvd_rvDivisor, hq⟩

variable
  (hgcd : ∀ p q : Berarducci.FiniteSupportRing (K := ℚ),
    ∃ d : Berarducci.FiniteSupportRing (K := ℚ),
      ∀ e : Berarducci.FiniteSupportRing (K := ℚ), e ∣ p ∧ e ∣ q ↔ e ∣ d)
  (hunits : ∀ u : Berarducci.FiniteSupportRing (K := ℚ),
    IsUnit u ↔ ∃ k : ℚ, k ≠ 0 ∧
      u = HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k)

include hgcd hunits in
/-- The earlier normalized divisor from LM24, Notation 5.4.5 is exactly `1 - t⁻²` on
the leading class in Example 5.5.4. -/
theorem seriesMaximalExample_gradedNormalized_eq :
    Berarducci.gradedNormalizedMaximalFiniteSupportDivisor
        seriesMaximalExampleLeadingGraded =
      seriesMaximalExampleRVDivisor := by
  apply Berarducci.gradedNormalizedMaximalFiniteSupportDivisor_eq_of_is hgcd hunits
  apply (Berarducci.isNormalizedGradedMaximalFiniteSupportDivisor_iff _ _).mpr
  exact ⟨(Berarducci.isGradedMaximalFiniteSupportDivisor_mk_iff _ _).mp
        seriesMaximalExample_isGradedMaximalFiniteSupportDivisor,
    Or.inr ⟨by
      intro hzero
      have hclass :=
        seriesMaximalExample_isGradedMaximalFiniteSupportDivisor
      rw [hzero] at hclass
      have hzeroMax :
          Berarducci.IsGradedMaximalFiniteSupportDivisor
            (0 : Berarducci.DegreeGraded ℚ) 0 := by
        rw [Berarducci.isGradedMaximalFiniteSupportDivisor_iff]
        intro q
        constructor
        · intro _
          exact dvd_zero _
        · intro _
          exact Associates.mk_le_mk_of_dvd (dvd_zero q)
      have hmkZero := hclass.eq hzeroMax
      exact seriesMaximalExampleRVDivisor_ne_zero
        (Associates.mk_eq_zero.mp hmkZero),
      seriesMaximalExampleRVDivisor_isMonic⟩⟩

include hgcd hunits in
/-- The chosen normalized series-level maximal divisor of the example is `t⁻¹ + 1`, not
the normalized leading-RV divisor `1 - t⁻²`. -/
theorem seriesMaximalExample_normalized_eq :
    Berarducci.seriesNormalizedMaximalFiniteSupportDivisor seriesMaximalExample =
      seriesMaximalExampleDivisor := by
  apply Berarducci.seriesNormalizedMaximalFiniteSupportDivisor_eq_of_is hgcd hunits
  apply (Berarducci.isNormalizedSeriesMaximalFiniteSupportDivisor_iff _ _).mpr
  exact ⟨(Berarducci.isSeriesMaximalFiniteSupportDivisor_mk_iff _ _).mp
      seriesMaximalExample_isSeriesMaximalFiniteSupportDivisor,
    Or.inr ⟨by
      intro hzero
      have hHahn : (seriesMaximalExample : ℚ⟦ℝ⟧) = 0 :=
        congrArg Subtype.val hzero
      have hdegree := HahnSeries.degree_eq_bot.mpr hHahn
      rw [seriesMaximalExample_degree] at hdegree
      norm_num at hdegree,
    seriesMaximalExampleDivisor_isMonic⟩⟩

end

end Tests
