/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.NormSubgroup
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestriction
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CyclicValueGroup
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuation
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.SeriesValuationEstimates
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuationUniformizer
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CompleteRangeRestriction
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.UniformizerIntegerValuation
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestrictedTopology
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuationSubringUnitMap
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.LocalFieldRangeRestriction
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuedExtensionUnitMap
/-!
# Unit changes of a standard Lubin--Tate uniformizer

For a local field `F`, a chosen uniformizer `π`, and a valuation-ring unit
`u`, the product `uπ` is again a uniformizer.  Consequently all of the
standard finite-level Lubin--Tate constructions are available for `uπ`.

This file packages that elementary, characteristic-independent part of the
changed-uniformizer norm argument.  In particular, the negative primitive
generator at the changed level has norm `uπ`.  It also records the
cancellation step saying that, inside the norm subgroup of the original
`π`-level, membership of `uπ` is equivalent to membership of `u`, since `π`
is already a norm.

The remaining comparison between the `π`-level and the `uπ`-level requires
an actual finite-level intertwining equivalence; no such equivalence is
assumed here.
-/

@[expose] public section

noncomputable
section

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The unit change `uπ` of a chosen integral uniformizer. -/
def standardLubinTateChangedUniformizer
    (F : LocalField.{u, v} K) (π : F.valuationSubring)
    (u : F.valuationSubringˣ) :
    F.valuationSubring :=
  (u : F.valuationSubring) * π

/-- The changed parameter is literally the unit factor times the original
uniformizer. -/
theorem standardLubinTateChangedUniformizer_eq_unit_mul
    (F : LocalField.{u, v} K) (π : F.valuationSubring)
    (u : F.valuationSubringˣ) :
    standardLubinTateChangedUniformizer F π u =
      (u : F.valuationSubring) * π :=
  rfl

/-- Multiplication by a valuation-ring unit preserves the uniformizer
property. -/
theorem standardLubinTateChangedUniformizer_isUniformizer
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) :
    F.toCompleteDVF.valuation.IsUniformizer
      (standardLubinTateChangedUniformizer F π u : K) := by
  exact hπ.of_associated
    (associated_unit_mul_right π (u : F.valuationSubring) u.isUnit)

/-- The standard finite Lubin--Tate level attached to the changed
uniformizer `uπ`. -/
abbrev standardLubinTateChangedLevelField
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :=
  standardLubinTateLevelField
    (standardLubinTateChangedUniformizer_isUniformizer hπ u) n

/-- The chosen primitive generator of the changed standard level. -/
noncomputable abbrev standardLubinTateChangedLevelGenerator
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    standardLubinTateChangedLevelField hπ u n :=
  standardLubinTateLevelGenerator
    (standardLubinTateChangedUniformizer_isUniformizer hπ u) n

/-- The local norm subgroup of the changed standard level. -/
def standardLubinTateChangedNormSubgroup
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    Subgroup Kˣ :=
  standardLubinTateNormSubgroup
    (standardLubinTateChangedUniformizer_isUniformizer hπ u) n

/-- A valuation-ring unit regarded as a unit of the base field. -/
noncomputable def standardLubinTateUnitFactorFieldUnit
    (F : LocalField.{u, v} K) (u : F.valuationSubringˣ) :
    Kˣ :=
  CompleteDVF.valuationSubringUnitsToFieldUnits F.toCompleteDVF u

/-- The unit-factor inclusion has the expected underlying field element. -/
@[simp]
theorem standardLubinTateUnitFactorFieldUnit_coe
    (F : LocalField.{u, v} K) (u : F.valuationSubringˣ) :
    (standardLubinTateUnitFactorFieldUnit F u : K) =
      (u : F.valuationSubring) := by
  exact CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply
    F.toCompleteDVF u

/-- The changed uniformizer, regarded as a nonzero base-field unit. -/
noncomputable def standardLubinTateChangedUniformizerUnit
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) :
    Kˣ :=
  standardLubinTateBaseUniformizerUnit
    (standardLubinTateChangedUniformizer_isUniformizer hπ u)

/-- The changed uniformizer unit has underlying field element `uπ`. -/
@[simp]
theorem standardLubinTateChangedUniformizerUnit_coe
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) :
    (standardLubinTateChangedUniformizerUnit hπ u : K) =
      (standardLubinTateChangedUniformizer F π u : K) := by
  exact standardLubinTateBaseUniformizerUnit_coe
    (standardLubinTateChangedUniformizer_isUniformizer hπ u)

/-- In the base-field unit group, the changed uniformizer is the product
of the included valuation-ring unit and the original uniformizer. -/
theorem standardLubinTateChangedUniformizerUnit_eq_unit_mul
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) :
    standardLubinTateChangedUniformizerUnit hπ u =
      standardLubinTateUnitFactorFieldUnit F u *
        standardLubinTateBaseUniformizerUnit hπ := by
  apply Units.ext
  simp [standardLubinTateChangedUniformizer]

/-- Equivalently, the unit factor is the quotient of the changed and
original uniformizers. -/
theorem standardLubinTateUnitFactorFieldUnit_eq_changed_mul_uniformizer_inv
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) :
    standardLubinTateUnitFactorFieldUnit F u =
      standardLubinTateChangedUniformizerUnit hπ u *
        (standardLubinTateBaseUniformizerUnit hπ)⁻¹ := by
  rw [standardLubinTateChangedUniformizerUnit_eq_unit_mul]
  simp

/-- The negative primitive generator at the changed level has norm `uπ`. -/
theorem standardLubinTateChanged_norm_neg_levelGenerator
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    Algebra.norm K
        (-standardLubinTateChangedLevelGenerator hπ u n) =
      (standardLubinTateChangedUniformizer F π u : K) :=
  standardLubinTate_norm_neg_levelGenerator
    (standardLubinTateChangedUniformizer_isUniformizer hπ u) n

/-- The changed uniformizer is an actual norm from its own standard
finite level. -/
theorem standardLubinTateChangedUniformizerUnit_mem_changedNormSubgroup
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    standardLubinTateChangedUniformizerUnit hπ u ∈
      standardLubinTateChangedNormSubgroup hπ u n := by
  exact standardLubinTateBaseUniformizerUnit_mem_normSubgroup
    (standardLubinTateChangedUniformizer_isUniformizer hπ u) n

/-- Inside the original level's norm subgroup, the changed uniformizer
belongs exactly when its unit factor belongs.  This is the cancellation
step used after transporting the changed-level norm through a future
finite-level intertwining equivalence. -/
theorem
    standardLubinTateChangedUniformizerUnit_mem_standardNormSubgroup_iff
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    standardLubinTateChangedUniformizerUnit hπ u ∈
        standardLubinTateNormSubgroup hπ n ↔
      standardLubinTateUnitFactorFieldUnit F u ∈
        standardLubinTateNormSubgroup hπ n := by
  let N := standardLubinTateNormSubgroup hπ n
  let ϖ := standardLubinTateBaseUniformizerUnit hπ
  have hϖ : ϖ ∈ N :=
    standardLubinTateBaseUniformizerUnit_mem_normSubgroup hπ n
  have hϖinv : ϖ⁻¹ ∈ N :=
    standardLubinTateBaseUniformizerUnit_inv_mem_normSubgroup hπ n
  constructor
  · intro hchanged
    rw [standardLubinTateChangedUniformizerUnit_eq_unit_mul] at hchanged
    have hcancel := N.mul_mem hchanged hϖinv
    change standardLubinTateUnitFactorFieldUnit F u ∈ N
    simpa [ϖ, mul_assoc] using hcancel
  · intro hu
    rw [standardLubinTateChangedUniformizerUnit_eq_unit_mul]
    change standardLubinTateUnitFactorFieldUnit F u * ϖ ∈ N
    exact N.mul_mem hu hϖ

/-- The inverse changed uniformizer gives the same norm-membership test. -/
theorem
    standardLubinTateChangedUniformizerUnit_inv_mem_standardNormSubgroup_iff
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    (standardLubinTateChangedUniformizerUnit hπ u)⁻¹ ∈
        standardLubinTateNormSubgroup hπ n ↔
      standardLubinTateUnitFactorFieldUnit F u ∈
        standardLubinTateNormSubgroup hπ n := by
  let N := standardLubinTateNormSubgroup hπ n
  constructor
  · intro hinv
    apply
      (standardLubinTateChangedUniformizerUnit_mem_standardNormSubgroup_iff
        hπ u n).1
    simpa using N.inv_mem hinv
  · intro hu
    exact N.inv_mem
      ((standardLubinTateChangedUniformizerUnit_mem_standardNormSubgroup_iff
        hπ u n).2 hu)

/-- An actual equivalence from the changed level to the original level
transports the changed prime-element norm and therefore makes the unit
factor a norm from the original level.  This is the characteristic-free
terminal step of a changed-uniformizer comparison; constructing `e` is the
remaining substantive input. -/
theorem
    standardLubinTateUnitFactorFieldUnit_mem_standardNormSubgroup_of_algEquiv
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ)
    (e : standardLubinTateChangedLevelField hπ u n ≃ₐ[K]
      standardLubinTateLevelField hπ n) :
    standardLubinTateUnitFactorFieldUnit F u ∈
      standardLubinTateNormSubgroup hπ n := by
  have hchanged :
      standardLubinTateChangedUniformizerUnit hπ u ∈
        standardLubinTateChangedNormSubgroup hπ u n :=
    standardLubinTateChangedUniformizerUnit_mem_changedNormSubgroup
      hπ u n
  have htransport :
      standardLubinTateChangedUniformizerUnit hπ u ∈
        standardLubinTateNormSubgroup hπ n := by
    change standardLubinTateChangedUniformizerUnit hπ u ∈
      LocalFieldTheory.localNormSubgroup K
        (standardLubinTateChangedLevelField hπ u n) at hchanged
    rcases hchanged with ⟨y, hy⟩
    change standardLubinTateChangedUniformizerUnit hπ u ∈
      LocalFieldTheory.localNormSubgroup K
        (standardLubinTateLevelField hπ n)
    refine ⟨Units.mapEquiv e.toMulEquiv y, ?_⟩
    calc
      LocalFieldTheory.normUnits K
          (standardLubinTateLevelField hπ n)
          (Units.mapEquiv e.toMulEquiv y) =
          LocalFieldTheory.normUnits K
            (standardLubinTateChangedLevelField hπ u n) y := by
        apply Units.ext
        exact Algebra.norm_eq_of_algEquiv e
          (y : standardLubinTateChangedLevelField hπ u n)
      _ = standardLubinTateChangedUniformizerUnit hπ u := hy
  exact
    (standardLubinTateChangedUniformizerUnit_mem_standardNormSubgroup_iff
      hπ u n).1 htransport

end LubinTate

end
