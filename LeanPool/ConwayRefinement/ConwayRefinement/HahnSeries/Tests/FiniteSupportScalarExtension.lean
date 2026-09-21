/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportScalarExtension

/-!
# API checks for finite-support coefficient extension

The integer fixture has nonzero coefficients at exponents `0` and `-1`. Its scalar extension to
the rationals retains both coefficients, so it rejects maps that preserve only constants, delete
the nonconstant term, or move its exponent. The rational fixture with coefficient `1 / 2` at
exponent `-1` is not in the image of integer scalar extension; this separates the exact
coefficientwise range from the full rational finite-support ring and from a support-only test.

The diagonal map `ℚ → ℚ × ℚ` supplies a separate scalar-recovery test. Multiplying the
extended nonzero fixture by the constant `(1, 0)` leaves the image, because that coefficient is
not diagonal. This exercises the step in Remark 6.3.5 which recovers a redistributed scalar from
one nonzero coefficient. An identity-map fixture then exercises the generic divisibility-reflection
reduction with an explicit scalar-redistribution witness.
-/

open scoped HahnSeries

namespace Tests.HahnSeries.FiniteSupportScalarExtension

public noncomputable section

/-- The nonpositive exponent `-1` used by the coefficient-extension fixtures. -/
def negativeOne : HahnSeries.Nonpositive.exponentMonoid ℤ :=
  ⟨-1, show (-1 : ℤ) ≤ 0 by norm_num⟩

/-- A finite-support integer series with coefficients `3` at `0` and `2` at `-1`. -/
def integerFixture :
    HahnSeries.Nonpositive.FiniteSupportRing (G := ℤ) (K := ℤ) :=
  HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℤ) 3 +
    HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℤ) 2 *
      HahnSeries.Nonpositive.finiteSupportMonomial (K := ℤ) negativeOne

/-- The coefficientwise extension of `integerFixture` from `ℤ` to `ℚ`. -/
def rationalFixture :
    HahnSeries.Nonpositive.FiniteSupportRing (G := ℤ) (K := ℚ) :=
  HahnSeries.Nonpositive.finiteSupportScalarExtension
    (G := ℤ) (K := ℤ) (L := ℚ) integerFixture

/-- Scalar extension maps both coefficients and preserves the nonconstant exponent. -/
theorem rationalFixture_eq :
    rationalFixture =
      HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℤ) (3 : ℚ) +
        HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℤ) (2 : ℚ) *
          HahnSeries.Nonpositive.finiteSupportMonomial (K := ℚ) negativeOne := by
  rw [rationalFixture, integerFixture, map_add, map_mul,
    HahnSeries.Nonpositive.finiteSupportScalarExtension_scalar,
    HahnSeries.Nonpositive.finiteSupportScalarExtension_scalar,
    HahnSeries.Nonpositive.finiteSupportScalarExtension_monomial]
  norm_num

/-- The nonconstant coefficient survives scalar extension and is mapped to `2 : ℚ`. -/
theorem rationalFixture_negativeOne_coeff :
    HahnSeries.Nonpositive.finiteSupportCoefficients rationalFixture negativeOne = 2 := by
  rw [rationalFixture_eq,
    ← HahnSeries.Nonpositive.smul_finiteSupport_eq_scalar_mul,
    map_add, map_smul]
  simp [HahnSeries.Nonpositive.finiteSupportCoefficients_apply,
    HahnSeries.Nonpositive.coe_finiteSupportScalarHom, negativeOne, Finsupp.single_apply, Subtype.ext_iff]

/-- The constant coefficient survives scalar extension and is mapped to `3 : ℚ`. -/
theorem rationalFixture_zero_coeff :
    HahnSeries.Nonpositive.finiteSupportCoefficients rationalFixture
        (0 : HahnSeries.Nonpositive.exponentMonoid ℤ) = 3 := by
  rw [rationalFixture_eq,
    ← HahnSeries.Nonpositive.smul_finiteSupport_eq_scalar_mul,
    map_add, map_smul]
  simp [HahnSeries.Nonpositive.finiteSupportCoefficients_apply,
    HahnSeries.Nonpositive.coe_finiteSupportScalarHom, negativeOne, Finsupp.single_apply, Subtype.ext_iff]

/-- The scalar-extended integer fixture belongs to the image by construction. -/
theorem rationalFixture_mem_range :
    rationalFixture ∈ Set.range
      (HahnSeries.Nonpositive.finiteSupportScalarExtension
        (G := ℤ) (K := ℤ) (L := ℚ)) :=
  ⟨integerFixture, rfl⟩

/-- A rational finite-support series whose nonconstant coefficient is not an integer. -/
def rationalOutside :
    HahnSeries.Nonpositive.FiniteSupportRing (G := ℤ) (K := ℚ) :=
  HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℤ) 3 +
    HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℤ) (1 / 2 : ℚ) *
      HahnSeries.Nonpositive.finiteSupportMonomial (K := ℚ) negativeOne

/-- The coefficient of `rationalOutside` at exponent `-1` is `1 / 2`. -/
theorem rationalOutside_negativeOne_coeff :
    HahnSeries.Nonpositive.finiteSupportCoefficients rationalOutside negativeOne = 1 / 2 := by
  rw [rationalOutside,
    ← HahnSeries.Nonpositive.smul_finiteSupport_eq_scalar_mul,
    map_add, map_smul]
  simp [HahnSeries.Nonpositive.finiteSupportCoefficients_apply,
    HahnSeries.Nonpositive.coe_finiteSupportScalarHom, negativeOne, Finsupp.single_apply, Subtype.ext_iff]

/-- A nonintegral coefficient prevents membership in the image of integer scalar extension. -/
theorem rationalOutside_not_mem_range :
    rationalOutside ∉ Set.range
      (HahnSeries.Nonpositive.finiteSupportScalarExtension
        (G := ℤ) (K := ℤ) (L := ℚ)) := by
  rw [HahnSeries.Nonpositive.mem_range_finiteSupportScalarExtension_iff]
  push Not
  refine ⟨negativeOne, ?_⟩
  rw [rationalOutside_negativeOne_coeff]
  rintro ⟨z, hz⟩
  change (z : ℚ) = 1 / 2 at hz
  have hz' : (2 : ℚ) * (z : ℚ) = 1 := by
    rw [hz]
    norm_num
  have hzInt : 2 * z = 1 := by
    exact_mod_cast hz'
  omega

/-- Scalar extension from integer to rational finite-support series is injective. -/
theorem integer_scalarExtension_injective :
    Function.Injective
      (HahnSeries.Nonpositive.finiteSupportScalarExtension
        (G := ℤ) (K := ℤ) (L := ℚ)) :=
  HahnSeries.Nonpositive.finiteSupportScalarExtension_injective
    (Int.cast_injective : Function.Injective (algebraMap ℤ ℚ))

/-- The diagonal embedding of the rationals into the product ring. -/
def rationalDiagonal : ℚ →+* ℚ × ℚ :=
  (RingHom.id ℚ).prod (RingHom.id ℚ)

/-- The scalar `(1, 0)` does not belong to the image of the diagonal embedding. -/
theorem one_zero_not_mem_rationalDiagonal_range :
    (1, 0) ∉ Set.range rationalDiagonal := by
  rintro ⟨q, hq⟩
  have hfirst := congrArg Prod.fst hq
  have hsecond := congrArg Prod.snd hq
  change q = 1 at hfirst
  change q = 0 at hsecond
  exact zero_ne_one (hsecond.symm.trans hfirst)

/-- The rational fixture is nonzero, witnessed by its coefficient at exponent `-1`. -/
theorem rationalFixture_ne_zero : rationalFixture ≠ 0 := by
  intro hzero
  have hcoeff := congrArg
    (fun p : HahnSeries.Nonpositive.FiniteSupportRing (G := ℤ) (K := ℚ) ↦
      HahnSeries.Nonpositive.finiteSupportCoefficients p negativeOne) hzero
  rw [rationalFixture_negativeOne_coeff] at hcoeff
  simp at hcoeff

/-- Multiplication by the non-diagonal scalar `(1, 0)` takes the extended nonzero fixture out of
the diagonal coefficient image. -/
theorem diagonalFixture_mul_one_zero_not_mem_range :
    HahnSeries.Nonpositive.finiteSupportMap rationalDiagonal rationalFixture *
        HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℤ) (1, 0) ∉
      Set.range (HahnSeries.Nonpositive.finiteSupportMap (G := ℤ) rationalDiagonal) := by
  intro hmem
  have hscalar :=
    HahnSeries.Nonpositive.coefficient_mem_range_of_map_mul_scalar_mem_range
      (Field.toIsField ℚ) rationalDiagonal rationalFixture_ne_zero hmem
  exact one_zero_not_mem_rationalDiagonal_range hscalar

/-- Scalar redistribution is immediate for the identity coefficient map: choose the scalar one. -/
theorem identity_exists_scalarRedistribution :
    ∀ {p₁ p₂ : HahnSeries.Nonpositive.FiniteSupportRing (G := ℤ) (K := ℚ)},
      p₁ ≠ 0 → p₂ ≠ 0 →
        p₁ * p₂ ∈ Set.range
            (HahnSeries.Nonpositive.finiteSupportMap (G := ℤ) (RingHom.id ℚ)) →
          ∃ B : ℚ,
            B ≠ 0 ∧
              p₁ * HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℤ) B ∈
                Set.range (HahnSeries.Nonpositive.finiteSupportMap
                  (G := ℤ) (RingHom.id ℚ)) ∧
              p₂ * HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℤ) B⁻¹ ∈
                Set.range (HahnSeries.Nonpositive.finiteSupportMap
                  (G := ℤ) (RingHom.id ℚ)) := by
  intro p₁ p₂ _ _ _
  refine ⟨1, one_ne_zero, ⟨p₁, ?_⟩, ⟨p₂, ?_⟩⟩ <;>
    simp [HahnSeries.Nonpositive.finiteSupportMap_id]

/-- The generic reduction recovers a nonconstant divisibility relation from its image under the
identity coefficient map. -/
theorem identity_reflects_nonconstant_divisibility :
    rationalFixture ∣ rationalFixture * rationalOutside := by
  have hlarge :
      HahnSeries.Nonpositive.finiteSupportMap (RingHom.id ℚ) rationalFixture ∣
        HahnSeries.Nonpositive.finiteSupportMap (RingHom.id ℚ)
          (rationalFixture * rationalOutside) := by
    rw [HahnSeries.Nonpositive.finiteSupportMap_id]
    exact dvd_mul_right _ _
  exact (HahnSeries.Nonpositive.finiteSupportMap_dvd_iff_of_scalarRedistribution
    (RingHom.id ℚ) Function.injective_id identity_exists_scalarRedistribution
      rationalFixture (rationalFixture * rationalOutside)).mp hlarge

end

end Tests.HahnSeries.FiniteSupportScalarExtension
