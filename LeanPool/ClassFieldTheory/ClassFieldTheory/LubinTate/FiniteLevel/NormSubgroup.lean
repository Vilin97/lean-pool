/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.NormUniformizer
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient
/-!
# The norm subgroup of a standard Lubin--Tate level

This file introduces the local norm subgroup attached to a standard finite
Lubin--Tate level.  The norm identity for the negative primitive generator
shows that the chosen base uniformizer is an actual norm.  Consequently its
entire cyclic subgroup of integral powers lies in the norm subgroup.

The higher-principal-unit contribution is intentionally left to the later
norm calculation.
-/

@[expose] public section

noncomputable section

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The local norm subgroup attached to a standard finite Lubin--Tate
level. -/
def standardLubinTateNormSubgroup
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) : Subgroup Kˣ :=
  LocalFieldTheory.localNormSubgroup K
    (standardLubinTateLevelField hπ n)

/-- The chosen base uniformizer, regarded as a nonzero field unit. -/
noncomputable def standardLubinTateBaseUniformizerUnit
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    Kˣ :=
  Units.mk0 (π : K) hπ.ne_zero

/-- The chosen uniformizer unit has the expected underlying field
element. -/
@[simp]
theorem standardLubinTateBaseUniformizerUnit_coe
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    (standardLubinTateBaseUniformizerUnit hπ : K) = (π : K) :=
  rfl

/-- The chosen base uniformizer is an actual norm from every standard
finite level. -/
theorem standardLubinTateBaseUniformizerUnit_mem_normSubgroup
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    standardLubinTateBaseUniformizerUnit hπ ∈
      standardLubinTateNormSubgroup hπ n := by
  let : FiniteDimensional K (standardLubinTateLevelField hπ n) :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let y : (standardLubinTateLevelField hπ n)ˣ :=
    Units.mk0 (-standardLubinTateLevelGenerator hπ n)
      (neg_ne_zero.mpr (by
        intro hzero
        apply chosenStandardLubinTatePrimitiveRoot_ne_zero hπ n
        simpa using congrArg Subtype.val hzero))
  have hyNorm :
      LocalFieldTheory.normUnits K
          (standardLubinTateLevelField hπ n) y =
        standardLubinTateBaseUniformizerUnit hπ := by
    apply Units.ext
    exact standardLubinTate_norm_neg_levelGenerator hπ n
  have hyMem :
      LocalFieldTheory.normUnits K
          (standardLubinTateLevelField hπ n) y ∈
        LocalFieldTheory.localNormSubgroup K
          (standardLubinTateLevelField hπ n) :=
    ⟨y, rfl⟩
  rw [hyNorm] at hyMem
  exact hyMem

/-- The inverse uniformizer is also a norm, for conventions that choose the
inverse generator of the valuation factor. -/
theorem standardLubinTateBaseUniformizerUnit_inv_mem_normSubgroup
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    (standardLubinTateBaseUniformizerUnit hπ)⁻¹ ∈
      standardLubinTateNormSubgroup hπ n :=
  (standardLubinTateNormSubgroup hπ n).inv_mem
    (standardLubinTateBaseUniformizerUnit_mem_normSubgroup hπ n)

/-- Every integral power of the chosen base uniformizer is a norm. -/
theorem standardLubinTateBaseUniformizerUnit_zpowers_le_normSubgroup
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    Subgroup.zpowers (standardLubinTateBaseUniformizerUnit hπ) ≤
      standardLubinTateNormSubgroup hπ n := by
  rw [Subgroup.zpowers_le]
  exact standardLubinTateBaseUniformizerUnit_mem_normSubgroup hπ n

/-- The same cyclic norm-subgroup inclusion using the inverse-uniformizer
convention. -/
theorem standardLubinTateBaseUniformizerUnit_inv_zpowers_le_normSubgroup
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    Subgroup.zpowers ((standardLubinTateBaseUniformizerUnit hπ)⁻¹) ≤
      standardLubinTateNormSubgroup hπ n := by
  rw [Subgroup.zpowers_le]
  exact standardLubinTateBaseUniformizerUnit_inv_mem_normSubgroup hπ n

end LubinTate

end
