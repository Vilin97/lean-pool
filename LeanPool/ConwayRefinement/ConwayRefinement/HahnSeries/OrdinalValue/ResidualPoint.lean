/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalValue
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Truncation

/-!
# Berarducci residual points

For a nonpositive real Hahn series `b` with `1 < v_J(b)`, Berarducci, Definition 6.6 defines
`X(b)` to consist of the strictly negative exponents `γ` for which the translated closed
truncation `b^{|γ}` has ordinal value equal to the residual value of `b`.

The definition below uses the exact domain already imposed on principal and residual values. Its
strict inequality `γ < 0`, closed truncation at `γ`, and equality with the residual value are
all part of the carrier. In later statements, the source phrase "sufficiently close to zero" is
represented by `nhdsWithin 0 (Set.Iio 0)`, Mathlib's left-neighborhood filter; no separate
informal predicate is introduced.

When `v_J(b)` satisfies Berarducci's exact multiplicative-principality predicate, its residual
value is one. The corresponding theorem recovers the description immediately following
Definition 6.6.

-/

universe v

open scoped HahnSeries

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K]

/-- The set `X(b)` of residual points from Berarducci, Definition 6.6. -/
def residualPointSet (b : SeriesWithOrdinalValueAboveOne K) : Set ℝ :=
  {γ | γ < 0 ∧
    ordinalValue (translatedTruncation (b.1 : K⟦ℝ⟧) γ) = b.residualValue}

/-- Membership in `X(b)` is the conjunction printed in Berarducci, Definition 6.6. -/
theorem mem_residualPointSet_iff {b : SeriesWithOrdinalValueAboveOne K} {γ : ℝ} :
    γ ∈ residualPointSet b ↔
      γ < 0 ∧
        ordinalValue (translatedTruncation (b.1 : K⟦ℝ⟧) γ) = b.residualValue :=
  (Iff.rfl)

/-- Every residual point is strictly negative. -/
theorem residualPointSet_subset_Iio (b : SeriesWithOrdinalValueAboveOne K) :
    residualPointSet b ⊆ Set.Iio 0 :=
  fun _ hγ ↦ hγ.1

/-- At zero, the translated truncation has the value of the original series, which is strictly
larger than its residual value. -/
theorem ordinalValue_translatedTruncation_zero_ne_residualValue
    (b : SeriesWithOrdinalValueAboveOne K) :
    ordinalValue (translatedTruncation (b.1 : K⟦ℝ⟧) 0) ≠ b.residualValue := by
  rw [translatedTruncation_zero]
  exact ne_of_gt b.residualValue_lt_ordinalValue

/-- On the domain `1 < v_J(b)`, the value equality already excludes zero. Thus replacing the
printed condition `γ < 0` by `γ ≤ 0` gives an extensionally equal set, although the defining
characteristic theorem retains Berarducci's strict inequality. -/
theorem mem_residualPointSet_iff_le_zero
    {b : SeriesWithOrdinalValueAboveOne K} {γ : ℝ} :
    γ ∈ residualPointSet b ↔
      γ ≤ 0 ∧ ordinalValue (translatedTruncation (b.1 : K⟦ℝ⟧) γ) = b.residualValue := by
  constructor
  · rintro ⟨hγ, hvalue⟩
    exact ⟨hγ.le, hvalue⟩
  · rintro ⟨hγ, hvalue⟩
    apply mem_residualPointSet_iff.mpr
    refine ⟨lt_of_le_of_ne hγ ?_, hvalue⟩
    intro hzero
    subst γ
    exact ordinalValue_translatedTruncation_zero_ne_residualValue b hvalue

/-- Zero is not a residual point. -/
@[simp]
theorem zero_not_mem_residualPointSet (b : SeriesWithOrdinalValueAboveOne K) :
    (0 : ℝ) ∉ residualPointSet b :=
  fun hzero ↦ (mem_residualPointSet_iff.mp hzero).1.false

/-- At a residual point, the translated truncation does not belong to the negative-monomial
ideal. -/
theorem translatedTruncation_not_mem_negativeMonomialIdeal_of_mem_residualPointSet
    {b : SeriesWithOrdinalValueAboveOne K} {γ : ℝ}
    (hγ : γ ∈ residualPointSet b) :
    translatedTruncation (b.1 : K⟦ℝ⟧) γ ∉
      HahnSeries.Nonpositive.negativeMonomialIdeal K := by
  intro hmem
  have hzero := ordinalValue_of_mem_negativeMonomialIdeal hmem
  have hresidual := (mem_residualPointSet_iff.mp hγ).2
  exact b.residualValue_ne_zero (hresidual.symm.trans hzero)

/-- At a residual point, the translated truncation has support supremum zero. -/
theorem supportSup_translatedTruncation_eq_zero_of_mem_residualPointSet
    {b : SeriesWithOrdinalValueAboveOne K} {γ : ℝ}
    (hγ : γ ∈ residualPointSet b) :
    HahnSeries.Nonpositive.supportSup (translatedTruncation (b.1 : K⟦ℝ⟧) γ) = 0 := by
  apply le_antisymm
  · exact HahnSeries.Nonpositive.supportSup_le_zero _
  · apply le_of_not_gt
    intro hlt
    have hmem : translatedTruncation (b.1 : K⟦ℝ⟧) γ ∈
        HahnSeries.Nonpositive.negativeMonomialIdeal K :=
      HahnSeries.Nonpositive.mem_negativeMonomialIdeal_iff_supportSup_lt_zero.mpr hlt
    exact translatedTruncation_not_mem_negativeMonomialIdeal_of_mem_residualPointSet hγ hmem

/-- If `v_J(b)` is multiplicatively principal, `X(b)` consists exactly of the strictly negative
exponents whose translated truncations have value one. -/
theorem residualPointSet_eq_setOf_ordinalValue_eq_one_of_isMultiplicativelyPrincipal
    (b : SeriesWithOrdinalValueAboveOne K)
    (hb : Ordinal.IsMultiplicativelyPrincipal (ordinalValue b.1).val) :
    residualPointSet b =
      {γ : ℝ | γ < 0 ∧ ordinalValue (translatedTruncation (b.1 : K⟦ℝ⟧) γ) = 1} := by
  ext γ
  rw [mem_residualPointSet_iff, Set.mem_ofPred_eq,
    b.residualValue_eq_one_of_isMultiplicativelyPrincipal hb]

end Berarducci
