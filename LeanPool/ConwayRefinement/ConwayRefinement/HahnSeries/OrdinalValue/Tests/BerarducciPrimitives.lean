/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValue
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Truncation

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.Fixtures.ApproachZero

/-!
# API checks for Berarducci's germs and ordinal value

The first certificates exercise all three defining branches of `Berarducci.ordinalValue`: a
nonzero strictly negative monomial has value zero, a nonconstant series in `J + K` has value one,
and a series with support cofinal in zero has value strictly greater than one. These examples
distinguish the source definition from both a two-branch function and a function whose value-one
fiber contains only literal constants.

The germ certificates distinguish the closed interval `(η, γ]` from the incorrect open interval
`(η, γ)`: zero and the constant-one series agree at every exponent strictly below zero but have
different germs at zero. A monomial supported exactly at the cutoff becomes a nonzero constant
germ, which also distinguishes weak lower truncation from strict lower truncation.
-/

public noncomputable section

namespace Tests

open scoped HahnSeries

/-- A coefficient-one monomial at a strictly negative exponent has Berarducci ordinal value zero. -/
theorem ordinalValue_negative_monomial :
    Berarducci.ordinalValue
      (HahnSeries.Nonpositive.single (-1) (1 : ℚ) (by norm_num)) = 0 := by
  apply Berarducci.ordinalValue_eq_zero_iff.mpr
  exact HahnSeries.Nonpositive.single_one_mem_negativeMonomialIdeal (by norm_num)

/-- The nonzero constant-one series has Berarducci ordinal value one. -/
theorem ordinalValue_nonzero_constant :
    Berarducci.ordinalValue (HahnSeries.Nonpositive.C (1 : ℚ)) = 1 := by
  apply Berarducci.ordinalValue_eq_one_iff.mpr
  constructor
  · apply Berarducci.mem_nearConstantSubgroup_iff.mpr
    exact ⟨0, (HahnSeries.Nonpositive.negativeMonomialIdeal ℚ).zero_mem, 1, by simp⟩
  · intro hmem
    have hcoeff := Berarducci.constantCoeff_eq_zero_of_mem_negativeMonomialIdeal hmem
    norm_num at hcoeff

private theorem one_lt_ordinalValue_approachZero :
    1 < Berarducci.ordinalValue approachZeroNonpositive := by
  apply Berarducci.one_lt_ordinalValue_of_constantCoeff_eq_zero_of_supportSup_eq_zero
  · rw [HahnSeries.Nonpositive.constantCoeff_apply, coe_approachZeroNonpositive]
    exact not_ne_iff.mp (by
      simpa [HahnSeries.mem_support] using zero_not_mem_approachZero_support)
  · exact approachZero_supportSup

private theorem ordinalValue_nonconstant_nearConstant :
    ∃ b : Berarducci.Series ℚ,
      b ∉ Berarducci.constantSubgroup ℚ ∧
        Berarducci.ordinalValue b = 1 := by
  let j : Berarducci.Series ℚ :=
    HahnSeries.Nonpositive.single (-1) 1 (by norm_num)
  let b : Berarducci.Series ℚ := j + HahnSeries.Nonpositive.C 1
  have hj : j ∈ HahnSeries.Nonpositive.negativeMonomialIdeal ℚ := by
    exact HahnSeries.Nonpositive.single_one_mem_negativeMonomialIdeal (by norm_num)
  refine ⟨b, ?_, ?_⟩
  · intro hbConstant
    obtain ⟨k, hk⟩ := Berarducci.mem_constantSubgroup_iff.mp hbConstant
    have hcoeff := congrArg
      (fun x : Berarducci.Series ℚ ↦ ((x : ℚ⟦ℝ⟧).coeff (-1))) hk
    norm_num [b, j, HahnSeries.Nonpositive.coe_C,
      HahnSeries.Nonpositive.coe_single] at hcoeff
  · apply Berarducci.ordinalValue_eq_one_iff.mpr
    constructor
    · exact Berarducci.mem_nearConstantSubgroup_iff.mpr ⟨j, hj, 1, rfl⟩
    · intro hbJ
      have hcoeff := Berarducci.constantCoeff_eq_zero_of_mem_negativeMonomialIdeal hbJ
      norm_num [b, j, HahnSeries.Nonpositive.constantCoeff_apply,
        HahnSeries.Nonpositive.coe_C, HahnSeries.Nonpositive.coe_single] at hcoeff

/-- The three disjoint branches of Berarducci's ordinal value are all nonempty. -/
theorem ordinalValue_three_branch_separator :
    ∃ b₀ b₁ b₂ : Berarducci.Series ℚ,
      b₀ ≠ 0 ∧
      Berarducci.ordinalValue b₀ = 0 ∧
      b₁ ∉ Berarducci.constantSubgroup ℚ ∧
      Berarducci.ordinalValue b₁ = 1 ∧
      1 < Berarducci.ordinalValue b₂ := by
  obtain ⟨b₁, hb₁Constant, hb₁Value⟩ := ordinalValue_nonconstant_nearConstant
  let b₀ : Berarducci.Series ℚ :=
    HahnSeries.Nonpositive.single (-1) 1 (by norm_num)
  refine ⟨b₀, b₁, approachZeroNonpositive, ?_, ordinalValue_negative_monomial,
    hb₁Constant, hb₁Value, one_lt_ordinalValue_approachZero⟩
  intro hb₀
  have hb₀' := congrArg Subtype.val hb₀
  exact HahnSeries.single_ne_zero one_ne_zero (by
    simpa only [b₀, HahnSeries.Nonpositive.coe_single, Subring.coe_zero] using hb₀')

/-- Agreement strictly below a cutoff does not determine the germ when the cutoff coefficient is
omitted. -/
theorem germAt_closed_endpoint_separator :
    ∃ b c : ℚ⟦ℝ⟧,
      (∀ δ : ℝ, δ < 0 → b.coeff δ = c.coeff δ) ∧
        Berarducci.germAt b 0 ≠ Berarducci.germAt c 0 := by
  refine ⟨0, HahnSeries.C 1, ?_, ?_⟩
  · intro δ hδ
    simp [hδ.ne]
  · intro heq
    rw [Berarducci.germAt_eq_germAt_iff_exists_coeff_eq] at heq
    obtain ⟨η, hη, hcoeff⟩ := heq
    have h := hcoeff 0 hη le_rfl
    norm_num at h

/-- A monomial at the cutoff becomes its coefficient as a constant germ. -/
theorem germAt_single_cut (k : ℚ) (γ : ℝ) :
    Berarducci.germAt (HahnSeries.single γ k) γ =
      Berarducci.toGerm (HahnSeries.Nonpositive.C k) := by
  rw [Berarducci.germAt_apply, Berarducci.translatedTruncation_single_cut]

/-- The germ at its support exponent of a coefficient-one monomial is nonzero. -/
theorem germAt_single_cut_ne_zero (γ : ℝ) :
    Berarducci.germAt (HahnSeries.single γ (1 : ℚ)) γ ≠ 0 := by
  rw [germAt_single_cut]
  intro hzero
  have hvalue := Berarducci.germOrdinalValue_eq_zero_iff.mpr hzero
  simp only [Berarducci.toGerm_apply, Berarducci.germOrdinalValue_mk,
    ordinalValue_nonzero_constant] at hvalue
  exact one_ne_zero hvalue

end Tests
