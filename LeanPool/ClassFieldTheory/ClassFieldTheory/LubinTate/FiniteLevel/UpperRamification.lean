/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LowerRamification
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction
/-!
# Herbrand functions and upper groups of standard Lubin--Tate levels

This file names the lower filtration, Herbrand function, inverse Herbrand
function, and genuine real upper ramification groups attached to the chosen
integral-closure valuation on a standard finite Lubin--Tate level.
-/

noncomputable section

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open RamificationTheory.HilbertRamification.Higher

variable {K : Type u} [Field K]

noncomputable local instance
    standardLubinTateLevelField_finiteDimensional_forUpperRamification
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    FiniteDimensional K (standardLubinTateLevelField hπ n) :=
  standardLubinTateLevelField_finiteDimensional hπ n

noncomputable local instance
    standardLubinTateLevelField_isGalois_forUpperRamification
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    IsGalois K (standardLubinTateLevelField hπ n) :=
  standardLubinTateLevelField_isGalois hπ n

/-- The lower ramification filtration packaged for the Herbrand API. -/
noncomputable def standardLubinTateLowerRamificationFiltration
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration
      Gal((standardLubinTateLevelField hπ n)/K) :=
  lowerRamificationFiltrationOfUniqueExtension
    (base := F.toCompleteDVF.toDVF)
    (target := (standardLubinTateLevelCompleteDVF hπ n).toDVF)
    (standardLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension hπ n)

/-- The Herbrand function of a standard finite Lubin--Tate level. -/
noncomputable def standardLubinTateHerbrandFunction
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (s : ℝ) : ℝ :=
  herbrandFunctionOfUniqueExtension
    (base := F.toCompleteDVF.toDVF)
    (target := (standardLubinTateLevelCompleteDVF hπ n).toDVF)
    (standardLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension hπ n)
    s

/-- The inverse Herbrand function of a standard finite Lubin--Tate level. -/
noncomputable def standardLubinTateInverseHerbrandFunction
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (t : ℝ) : ℝ :=
  inverseHerbrandFunctionOfUniqueExtension
    (base := F.toCompleteDVF.toDVF)
    (target := (standardLubinTateLevelCompleteDVF hπ n).toDVF)
    (standardLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension hπ n)
    t

/-- The genuine real upper ramification group of a standard finite
Lubin--Tate level. -/
noncomputable def standardLubinTateRealUpperRamificationGroup
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (t : ℝ) :
    Subgroup Gal((standardLubinTateLevelField hπ n)/K) :=
  upperRamificationGroupOfUniqueExtension
    (base := F.toCompleteDVF.toDVF)
    (target := (standardLubinTateLevelCompleteDVF hπ n).toDVF)
    (standardLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension hπ n)
    t

/-- Evaluating the upper filtration at a Herbrand value recovers the
corresponding lower group. -/
theorem standardLubinTateRealUpperRamificationGroup_herbrandFunction
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (s : ℝ) :
    standardLubinTateRealUpperRamificationGroup hπ n
        (standardLubinTateHerbrandFunction hπ n s) =
      standardLubinTateRealLowerRamificationGroup hπ n s := by
  exact
    upperRamificationGroupOfUniqueExtension_herbrandFunction
      (base := F.toCompleteDVF.toDVF)
      (target := (standardLubinTateLevelCompleteDVF hπ n).toDVF)
      (standardLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension hπ n)
      s

end LubinTate

end
