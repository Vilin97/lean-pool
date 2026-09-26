/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.NegativeMonomialIdeal
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.NormalForm
public import Mathlib.RingTheory.Ideal.Prime
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Degree.PrincipalMultiplicativity
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Degree.SupportSupremumMultiplicativity
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.Fixtures.ApproachZero

/-!
# API checks for support-supremum multiplicativity

The first certificate distinguishes Berarducci's negative-monomial ideal from the kernel of the
constant-coefficient map. A negative monomial and the infinite `approachZero` series both have
zero constant coefficient, but only the negative monomial belongs to the ideal: `approachZero`
has support cofinal in zero and support supremum zero.

The next certificates apply the parameterized LM24, Proposition 3.5.1(2) bridge to the same
unattained boundary. One checks a normalized square, while another translates one factor to
support supremum `-1`; the latter would fail to exercise the translation-back step if both
factors remained normalized. A further certificate invokes the theorem obtained from
Berarducci, Corollary 9.8.

The final certificate invokes LM24, Proposition 3.6.1 for a nonconstant principal series whose
support does not contain zero.
-/

public noncomputable section

namespace Tests

open scoped HahnSeries

/-- The negative-monomial ideal is not the kernel of the constant-coefficient map. -/
theorem negativeMonomialIdeal_constantCoeff_separator :
    ∃ b c : HahnSeries.Nonpositive ℝ ℚ,
      HahnSeries.Nonpositive.constantCoeff b = 0 ∧
      b ∈ HahnSeries.Nonpositive.negativeMonomialIdeal ℚ ∧
      HahnSeries.Nonpositive.constantCoeff c = 0 ∧
      HahnSeries.Nonpositive.supportSup c = 0 ∧
      (c : ℚ⟦ℝ⟧).supportOrderType = Ordinal.omega0 ∧
      0 ∉ (c : ℚ⟦ℝ⟧).support ∧
      c ∉ HahnSeries.Nonpositive.negativeMonomialIdeal ℚ := by
  let b : HahnSeries.Nonpositive ℝ ℚ :=
    HahnSeries.Nonpositive.single (-1) 1 (by norm_num)
  refine ⟨b, approachZeroNonpositive, ?_, ?_, ?_, approachZero_supportSup, ?_, ?_, ?_⟩
  · simp [b, HahnSeries.Nonpositive.constantCoeff_apply]
  · exact HahnSeries.Nonpositive.single_one_mem_negativeMonomialIdeal (by norm_num)
  · rw [HahnSeries.Nonpositive.constantCoeff_apply,
      coe_approachZeroNonpositive]
    exact not_ne_iff.mp (by
      simpa [HahnSeries.mem_support] using zero_not_mem_approachZero_support)
  · simpa only [coe_approachZeroNonpositive] using
      approachZero_supportOrderType
  · simpa only [coe_approachZeroNonpositive] using
      zero_not_mem_approachZero_support
  · exact
      HahnSeries.Nonpositive.not_mem_negativeMonomialIdeal_of_supportSup_eq_zero
        approachZero_supportSup

/-- The prime-ideal form of support-supremum multiplicativity holds at an unattained normalized
boundary. -/
theorem exists_unattained_zeroSup_square_of_isPrime
    (hJ : (HahnSeries.Nonpositive.negativeMonomialIdeal ℚ).IsPrime) :
    ∃ b : HahnSeries.Nonpositive ℝ ℚ,
      HahnSeries.Nonpositive.supportSup b = 0 ∧
      0 ∉ (b : ℚ⟦ℝ⟧).support ∧
      HahnSeries.Nonpositive.supportSup (b * b) = 0 := by
  refine ⟨approachZeroNonpositive, approachZero_supportSup, ?_, ?_⟩
  · simpa only [coe_approachZeroNonpositive] using
      zero_not_mem_approachZero_support
  · rw [HahnSeries.Nonpositive.supportSup_mul_of_negativeMonomialIdeal_isPrime hJ,
      approachZero_supportSup, zero_add]

/-- Conditional support-supremum multiplicativity translates an unattained boundary correctly. -/
theorem exists_translated_unattained_product
    (hJ : (HahnSeries.Nonpositive.negativeMonomialIdeal ℚ).IsPrime) :
    ∃ b c : HahnSeries.Nonpositive ℝ ℚ,
      HahnSeries.Nonpositive.supportSup b = (-1 : ℝ) ∧
      HahnSeries.Nonpositive.supportSup c = 0 ∧
      0 ∉ (c : ℚ⟦ℝ⟧).support ∧
      HahnSeries.Nonpositive.supportSup (b * c) = (-1 : ℝ) := by
  let b : HahnSeries.Nonpositive ℝ ℚ :=
    HahnSeries.Nonpositive.single (-1) 1 (by norm_num)
  refine ⟨b, approachZeroNonpositive, ?_, approachZero_supportSup, ?_, ?_⟩
  · exact HahnSeries.Nonpositive.supportSup_single one_ne_zero (by norm_num)
  · simpa only [coe_approachZeroNonpositive] using
      zero_not_mem_approachZero_support
  · rw [HahnSeries.Nonpositive.supportSup_mul_of_negativeMonomialIdeal_isPrime hJ,
      HahnSeries.Nonpositive.supportSup_single one_ne_zero,
      approachZero_supportSup]
    norm_num

/-- Support-supremum multiplicativity holds at an unattained normalized boundary. -/
theorem exists_unattained_zeroSup_square :
    ∃ b : HahnSeries.Nonpositive ℝ ℚ,
      HahnSeries.Nonpositive.supportSup b = 0 ∧
      0 ∉ (b : ℚ⟦ℝ⟧).support ∧
      HahnSeries.Nonpositive.supportSup (b * b) = 0 := by
  refine ⟨approachZeroNonpositive, approachZero_supportSup, ?_, ?_⟩
  · simpa only [coe_approachZeroNonpositive] using
      zero_not_mem_approachZero_support
  · rw [HahnSeries.Nonpositive.supportSup_mul, approachZero_supportSup, zero_add]

/-- Nonconstant principal series are closed under squaring. -/
theorem exists_nonconstant_principal_square :
    ∃ b : HahnSeries.Nonpositive ℝ ℚ,
      HahnSeries.Nonpositive.IsPrincipal b ∧
      0 ∉ (b : ℚ⟦ℝ⟧).support ∧
      HahnSeries.Nonpositive.IsPrincipal (b * b) := by
  refine ⟨approachZeroNonpositive, approachZero_isPrincipal, ?_, ?_⟩
  · simpa only [coe_approachZeroNonpositive] using
      zero_not_mem_approachZero_support
  · exact approachZero_isPrincipal.mul approachZero_isPrincipal

end Tests
