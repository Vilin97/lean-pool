/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringFiniteSupport

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Tests.PrincipalSubringFraction

/-!
# API checks for finite-support series over `Frac(P̂)`

The first fixture verifies that coefficient extension preserves both the constant term and a term
at exponent `-1`. The second fixture uses the non-scalar positive-degree fraction from the
principal graded fraction-field client. A series having that fraction as its constant coefficient
does not belong to the embedded copy of `K(ℝ^{≤0})`.

Finally, the non-scalar coefficient and its inverse are placed in opposite factors of a
nonconstant product. Multiplying the first factor by the inverse coefficient and the second by
its reciprocal puts both factors in `K(ℝ^{≤0})`. This checks the exact `B`/`B⁻¹` orientation
and the nonzero witness required in LM24, Lemma 6.3.4.
-/

open scoped HahnSeries

namespace Tests.HahnSeries.OrdinalValue.PrincipalSubringFiniteSupport

public noncomputable section

/-- A nonzero element of `Frac(P̂)` outside the coefficient-field image. -/
def outsideCoefficient : Berarducci.PrincipalSubringFractionField ℚ :=
  Tests.fractionPositiveDegreeImage

/-- The chosen coefficient outside `ℚ` is nonzero. -/
theorem outsideCoefficient_ne_zero : outsideCoefficient ≠ 0 := by
  rw [outsideCoefficient]
  exact Tests.fractionPositiveDegreeImage_ne_zero

/-- The chosen coefficient does not belong to the image of the coefficient-field embedding. -/
theorem outsideCoefficient_not_mem_coefficientMap_range :
    outsideCoefficient ∉
      Set.range (Berarducci.principalSubringFractionCoefficientMap ℚ) := by
  rintro ⟨k, hk⟩
  apply Tests.fractionPositiveDegreeImage_not_scalar
  refine ⟨k, ?_⟩
  rw [Berarducci.principalSubringFraction_algebraMap_apply]
  rw [Berarducci.principalSubringFractionCoefficientMap_apply,
    outsideCoefficient] at hk
  exact hk

/-- The nonpositive real exponent `-1`. -/
def negativeOne : HahnSeries.Nonpositive.exponentMonoid ℝ :=
  ⟨-1, show (-1 : ℝ) ≤ 0 by norm_num⟩

/-- A nonconstant finite-support series over `ℚ`, with coefficients one at `0` and `-1`. -/
def sourceBinomial :
    HahnSeries.Nonpositive.FiniteSupportRing (G := ℝ) (K := ℚ) :=
  1 + HahnSeries.Nonpositive.finiteSupportMonomial (K := ℚ) negativeOne

/-- The coefficient extension of `sourceBinomial` to `Frac(P̂)`. -/
def extendedBinomial : Berarducci.PrincipalSubringFractionFiniteSupportRing ℚ :=
  Berarducci.principalSubringFractionScalarExtension ℚ sourceBinomial

/-- The term at exponent `-1` survives coefficient extension. -/
theorem extendedBinomial_negativeOne_coeff :
    HahnSeries.Nonpositive.finiteSupportCoefficients
        extendedBinomial negativeOne = 1 := by
  rw [extendedBinomial,
    Berarducci.principalSubringFractionScalarExtension_coeff]
  simp [sourceBinomial, negativeOne, Finsupp.single_apply, Subtype.ext_iff,
    HahnSeries.Nonpositive.finiteSupportCoefficients_apply]

/-- The constant term survives coefficient extension. -/
theorem extendedBinomial_zero_coeff :
    HahnSeries.Nonpositive.finiteSupportCoefficients
        extendedBinomial 0 = 1 := by
  rw [extendedBinomial,
    Berarducci.principalSubringFractionScalarExtension_coeff]
  simp [sourceBinomial, negativeOne, Finsupp.single_apply, Subtype.ext_iff,
    HahnSeries.Nonpositive.finiteSupportCoefficients_apply]

/-- The extended binomial lies in the embedded coefficient-series subring. -/
theorem extendedBinomial_mem_coefficientSubring :
    extendedBinomial ∈
      Berarducci.principalSubringFractionCoefficientSubring ℚ :=
  (Berarducci.mem_principalGradedFractionCoefficientSubring_iff _).mpr
    ⟨sourceBinomial, rfl⟩

/-- The positive-degree fraction, regarded as a constant finite-support series. -/
def outsideConstant : Berarducci.PrincipalSubringFractionFiniteSupportRing ℚ :=
  HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ)
    outsideCoefficient

/-- The constant coefficient of `outsideConstant` is the chosen non-scalar fraction. -/
theorem outsideConstant_zero_coeff :
    HahnSeries.Nonpositive.finiteSupportCoefficients outsideConstant 0 =
      outsideCoefficient := by
  rw [outsideConstant]
  simp [HahnSeries.Nonpositive.finiteSupportCoefficients_apply]

/-- The positive-degree constant series is not in the coefficient-series subring. -/
theorem outsideConstant_not_mem_coefficientSubring :
    outsideConstant ∉
      Berarducci.principalSubringFractionCoefficientSubring ℚ := by
  rw [Berarducci.mem_principalGradedFractionCoefficientSubring_iff_coeff]
  push Not
  refine ⟨0, ?_⟩
  rw [outsideConstant_zero_coeff]
  exact outsideCoefficient_not_mem_coefficientMap_range

/-- The first redistribution factor has a non-scalar coefficient and nonconstant support. -/
def redistributionLeft : Berarducci.PrincipalSubringFractionFiniteSupportRing ℚ :=
  outsideConstant * extendedBinomial

/-- The second redistribution factor is the inverse non-scalar constant. -/
def redistributionRight : Berarducci.PrincipalSubringFractionFiniteSupportRing ℚ :=
  HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ)
    outsideCoefficient⁻¹

/-- The coefficient of the first redistribution factor at `-1` is the non-scalar coefficient. -/
theorem redistributionLeft_negativeOne_coeff :
    HahnSeries.Nonpositive.finiteSupportCoefficients
        redistributionLeft negativeOne = outsideCoefficient := by
  rw [redistributionLeft, outsideConstant,
    ← HahnSeries.Nonpositive.smul_finiteSupport_eq_scalar_mul,
    map_smul, Finsupp.smul_apply, extendedBinomial_negativeOne_coeff]
  simp

/-- The constant coefficient of the second redistribution factor is the inverse coefficient. -/
theorem redistributionRight_zero_coeff :
    HahnSeries.Nonpositive.finiteSupportCoefficients
        redistributionRight 0 = outsideCoefficient⁻¹ := by
  rw [redistributionRight]
  simp [HahnSeries.Nonpositive.finiteSupportCoefficients_apply]

private theorem finiteSupportCoefficients_zero (g : HahnSeries.Nonpositive.exponentMonoid ℝ) :
    HahnSeries.Nonpositive.finiteSupportCoefficients
        (0 : Berarducci.PrincipalSubringFractionFiniteSupportRing ℚ) g = 0 := by
  have hmap := congrArg
    (fun f : HahnSeries.Nonpositive.exponentMonoid ℝ →₀
        Berarducci.PrincipalSubringFractionField ℚ ↦ f g)
    ((HahnSeries.Nonpositive.finiteSupportCoefficients
      (G := ℝ) (K := Berarducci.PrincipalSubringFractionField ℚ)).map_zero)
  simpa only [Finsupp.zero_apply] using hmap

/-- The first redistribution factor is nonzero. -/
theorem redistributionLeft_ne_zero : redistributionLeft ≠ 0 := by
  intro hzero
  have hcoeff := congrArg
    (fun b : Berarducci.PrincipalSubringFractionFiniteSupportRing ℚ ↦
      HahnSeries.Nonpositive.finiteSupportCoefficients b negativeOne) hzero
  rw [redistributionLeft_negativeOne_coeff] at hcoeff
  rw [finiteSupportCoefficients_zero] at hcoeff
  exact outsideCoefficient_ne_zero hcoeff

/-- The second redistribution factor is nonzero. -/
theorem redistributionRight_ne_zero : redistributionRight ≠ 0 := by
  intro hzero
  have hcoeff := congrArg
    (fun b : Berarducci.PrincipalSubringFractionFiniteSupportRing ℚ ↦
      HahnSeries.Nonpositive.finiteSupportCoefficients b 0) hzero
  rw [redistributionRight_zero_coeff] at hcoeff
  rw [finiteSupportCoefficients_zero] at hcoeff
  exact inv_ne_zero outsideCoefficient_ne_zero hcoeff

/-- The two redistribution factors multiply to the extended nonconstant binomial. -/
theorem redistributionLeft_mul_right :
    redistributionLeft * redistributionRight =
      extendedBinomial := by
  rw [redistributionLeft, redistributionRight, outsideConstant]
  calc
    _ =
        (HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ)
          outsideCoefficient *
        HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ)
          outsideCoefficient⁻¹) *
          extendedBinomial := by ring
    _ = extendedBinomial := by
      rw [← (HahnSeries.Nonpositive.finiteSupportScalarHom
        (G := ℝ) (K := Berarducci.PrincipalSubringFractionField ℚ)).map_mul]
      simp [outsideCoefficient_ne_zero]

/-- The product of the redistribution factors belongs to the coefficient-series subring. -/
theorem redistributionLeft_mul_right_mem_coefficientSubring :
    redistributionLeft * redistributionRight ∈
      Berarducci.principalSubringFractionCoefficientSubring ℚ := by
  rw [redistributionLeft_mul_right]
  exact extendedBinomial_mem_coefficientSubring

/-- The non-scalar constant factor divides the first redistribution factor in the ordinary
finite-support ring sense, with the nonconstant extended binomial as quotient. -/
theorem outsideConstant_dvd_redistributionLeft :
    outsideConstant ∣ redistributionLeft := by
  exact dvd_mul_right _ _

/-- The inverse positive-degree coefficient is an explicit valid redistribution witness. -/
theorem inversePositiveDegree_is_redistributionWitness :
    let B := outsideCoefficient⁻¹
    B ≠ 0 ∧
      redistributionLeft *
          HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) B ∈
        Berarducci.principalSubringFractionCoefficientSubring ℚ ∧
      redistributionRight *
          HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) B⁻¹ ∈
        Berarducci.principalSubringFractionCoefficientSubring ℚ := by
  dsimp only
  have hX := outsideCoefficient_ne_zero
  refine ⟨inv_ne_zero hX, ?_, ?_⟩
  · rw [redistributionLeft, outsideConstant]
    have hleft :
        HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ)
            outsideCoefficient * extendedBinomial *
            HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ)
              outsideCoefficient⁻¹ =
          extendedBinomial := by
      calc
        _ =
          (HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ)
            outsideCoefficient *
          HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ)
            outsideCoefficient⁻¹) *
            extendedBinomial := by ring
        _ = extendedBinomial := by
          rw [← (HahnSeries.Nonpositive.finiteSupportScalarHom
            (G := ℝ) (K := Berarducci.PrincipalSubringFractionField ℚ)).map_mul]
          simp [hX]
    rw [hleft]
    exact extendedBinomial_mem_coefficientSubring
  · rw [redistributionRight]
    rw [inv_inv, ← (HahnSeries.Nonpositive.finiteSupportScalarHom
      (G := ℝ) (K := Berarducci.PrincipalSubringFractionField ℚ)).map_mul]
    simp [hX]

end

end Tests.HahnSeries.OrdinalValue.PrincipalSubringFiniteSupport
