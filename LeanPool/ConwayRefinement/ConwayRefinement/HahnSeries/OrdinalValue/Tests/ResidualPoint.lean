/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPointTail
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.Fixtures.ApproachZero

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPointCofinality
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueImage

/-!
# API checks for Berarducci residual points

The approach-zero series has ordinal value `ω`, hence principal value `ω` and residual value one.
Its least support exponent is `-1`. Closed truncation at that exponent retains the coefficient-one
monomial, and translation turns it into the constant-one series, so `-1` belongs to `X(b)`.

This example separates Definition 6.6 from two nearby errors. Replacing residual value by
principal value would reject `-1`, while using strict rather than closed truncation would give the
zero series at `-1`. The endpoint zero is also excluded, but this is not a semantic separator for
the printed strict inequality: on the domain `1 < v_J(b)`, the value equation itself already
excludes zero, as proved in the definition module.

The final test uses the same residual point to distinguish the strict tail cutoff `(η, 0)` from
the nearby closed cutoff `[η, 0)`: the point `-1` lies above `-2`, but not strictly above itself.

The cofinality certificate produces a residual point strictly between `-1/1000` and zero. It
therefore distinguishes the proved conclusion of Lemma 6.8 from the nearby false assertion that
the residual-point set of this series consists only of its least exponent `-1`.
-/

open scoped HahnSeries NatOrdinal

public noncomputable section

namespace Tests

open Ordinal
open Berarducci.SeriesWithOrdinalValueAboveOne

/-- The approach-zero series in the exact domain of principal, residual, and residual-point
operations. -/
def approachZeroResidualInput :
    Berarducci.SeriesWithOrdinalValueAboveOne ℚ :=
  ⟨approachZeroNonpositive, by
    apply Berarducci.one_lt_ordinalValue_of_constantCoeff_eq_zero_of_supportSup_eq_zero
    · rw [HahnSeries.Nonpositive.constantCoeff_apply, coe_approachZeroNonpositive]
      exact not_ne_iff.mp (by
        simpa [HahnSeries.mem_support] using zero_not_mem_approachZero_support)
    · exact approachZero_supportSup⟩

/-- The packaged residual-point input has the intended underlying Hahn series. -/
@[simp]
theorem coe_approachZeroResidualInput :
    (approachZeroResidualInput : Berarducci.Series ℚ) = approachZeroNonpositive :=
  (rfl)

/-- The Berarducci ordinal value of the approach-zero series is `ω`. -/
theorem approachZero_ordinalValue_eq_omega :
    Berarducci.ordinalValue approachZeroNonpositive = NatOrdinal.of omega0 := by
  apply le_antisymm
  · simpa only [coe_approachZeroNonpositive, approachZero_supportOrderType] using
      Berarducci.ordinalValue_le_supportOrderType approachZeroNonpositive
  · apply NatOrdinal.of_le_iff.mpr
    rw [← coe_approachZeroResidualInput]
    have hprincipal :=
      Berarducci.ordinalValue_isAdditivelyPrincipal_of_one_lt
        approachZeroResidualInput.2
    have hone : (1 : Ordinal) <
        (Berarducci.ordinalValue approachZeroResidualInput.1).val :=
      NatOrdinal.of_lt_iff.mp approachZeroResidualInput.2
    exact hprincipal.omega0_le_of_one_lt hone

private theorem approachZero_ordinalValue_isMultiplicativelyPrincipal :
    Ordinal.IsMultiplicativelyPrincipal
      (Berarducci.ordinalValue approachZeroResidualInput.1).val := by
  rw [coe_approachZeroResidualInput, approachZero_ordinalValue_eq_omega]
  simp only [NatOrdinal.val_of]
  simpa [opow_zero, opow_one] using
    Ordinal.isMultiplicativelyPrincipal_omega0_opow_opow 0

/-- The approach-zero series has principal value `ω` and residual value one. -/
theorem approachZero_principalValue_eq_omega_and_residualValue_eq_one :
    approachZeroResidualInput.principalValue = NatOrdinal.of omega0 ∧
      approachZeroResidualInput.residualValue = 1 := by
  constructor
  · rw [principalValue_eq_ordinalValue_of_isMultiplicativelyPrincipal
      approachZeroResidualInput approachZero_ordinalValue_isMultiplicativelyPrincipal,
      coe_approachZeroResidualInput, approachZero_ordinalValue_eq_omega]
  · exact residualValue_eq_one_of_isMultiplicativelyPrincipal
      approachZeroResidualInput approachZero_ordinalValue_isMultiplicativelyPrincipal

private theorem approachZeroEmbedding_zero :
    approachZeroEmbedding 0 = -1 := by
  norm_num

private theorem approachZero_coeff_neg_one :
    approachZero.coeff (-1) = 1 := by
  rw [← approachZeroEmbedding_zero, approachZero_coeff_embedding]

private theorem approachZero_coeff_eq_zero_of_lt_neg_one {x : ℝ} (hx : x < -1) :
    approachZero.coeff x = 0 := by
  apply not_ne_iff.mp
  rw [← HahnSeries.mem_support, approachZero_support]
  rintro ⟨n, hn⟩
  have hmin : (-1 : ℝ) ≤ approachZeroEmbedding n := by
    rw [← approachZeroEmbedding_zero]
    exact approachZeroEmbedding.monotone (Nat.zero_le n)
  linarith

/-- Closed truncation of the approach-zero series at its least exponent, translated to zero, is
the constant-one series. -/
theorem translatedTruncation_approachZero_neg_one :
    Berarducci.translatedTruncation approachZero (-1) =
      HahnSeries.Nonpositive.C (1 : ℚ) := by
  apply Subtype.ext
  ext δ
  rw [Berarducci.coeff_translatedTruncation]
  by_cases hδ : δ = 0
  · subst δ
    simp [approachZero_coeff_neg_one]
  · by_cases hδNonpositive : δ ≤ 0
    · have hδNeg : δ < 0 := lt_of_le_of_ne hδNonpositive hδ
      have hlt : -1 + δ < -1 := by linarith
      rw [ite_eq_left hδNonpositive,
        approachZero_coeff_eq_zero_of_lt_neg_one hlt]
      simp [hδ]
    · rw [ite_eq_right hδNonpositive]
      simp [hδ]

/-- The least exponent is a residual point, whereas zero fails the value equation and is
excluded. -/
theorem approachZero_residualPointSet_boundary :
    (-1 : ℝ) ∈ Berarducci.residualPointSet approachZeroResidualInput ∧
      (0 : ℝ) ∉ Berarducci.residualPointSet approachZeroResidualInput := by
  constructor
  · rw [Berarducci.mem_residualPointSet_iff,
      approachZero_principalValue_eq_omega_and_residualValue_eq_one.2]
    constructor
    · norm_num
    · rw [coe_approachZeroResidualInput, coe_approachZeroNonpositive,
        translatedTruncation_approachZero_neg_one]
      apply Berarducci.ordinalValue_eq_one_iff.mpr
      constructor
      · apply Berarducci.mem_nearConstantSubgroup_iff.mpr
        exact ⟨0, (HahnSeries.Nonpositive.negativeMonomialIdeal ℚ).zero_mem,
          1, by simp⟩
      · intro hmem
        have hcoeff :=
          Berarducci.constantCoeff_eq_zero_of_mem_negativeMonomialIdeal hmem
        norm_num at hcoeff
  · exact Berarducci.zero_not_mem_residualPointSet approachZeroResidualInput

/-- The residual-point set contains a point strictly between `-1/1000` and zero. -/
theorem approachZero_residualPointSet_cofinal_near_zero :
    ∃ γ ∈ Berarducci.residualPointSet approachZeroResidualInput,
      -(1 : ℝ) / 1000 < γ ∧ γ < 0 := by
  have hLUB := Berarducci.residualPointSet_isLUB_zero approachZeroResidualInput
  obtain ⟨γ, hγ, hcutoff, _⟩ := hLUB.exists_between (by norm_num : -(1 : ℝ) / 1000 < 0)
  exact ⟨γ, hγ, hcutoff, Berarducci.residualPointSet_subset_Iio _ hγ⟩

/-- The least exponent belongs to the tail cut at `-2` but not to the tail cut at `-1`. This
separates the strict cutoff in `residualPointTail` from a closed cutoff. -/
theorem approachZero_residualPointTail_strict_cutoff :
    (-1 : ℝ) ∈ Berarducci.residualPointTail approachZeroResidualInput (-2) ∧
      (-1 : ℝ) ∉ Berarducci.residualPointTail approachZeroResidualInput (-1) := by
  constructor
  · rw [Berarducci.mem_residualPointTail_iff]
    exact ⟨approachZero_residualPointSet_boundary.1, by norm_num⟩
  · rw [Berarducci.mem_residualPointTail_iff]
    exact fun h ↦ (lt_irrefl (-1)) h.2

end Tests
