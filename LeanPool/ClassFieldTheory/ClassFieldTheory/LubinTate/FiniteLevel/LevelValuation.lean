/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LevelAutomorphisms
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.CompleteDVF
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups
/-!
# Uniqueness of the valuation on standard Lubin--Tate levels

The standard level field is finite and Galois over the local base field.
Consequently the complete discrete valuation selected from its integral
closure is the unique extension of the base valuation.  This is the bridge
needed by the genuine lower- and upper-numbering ramification groups.
-/

noncomputable section

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} [Field K]

/-- The chosen complete valuation on a standard Lubin--Tate level is the
unique extension of the base valuation. -/
theorem standardLubinTateLevelCompleteDVF_hasUniqueValuationExtension
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    ValuationTheory.DiscreteValuationField.ValuedExtension.HasUniqueValuationExtension.{u, v, u,
      0, 0}
      (base := F.toCompleteDVF)
      (target := standardLubinTateLevelCompleteDVF hπ n) := by
  let : FiniteDimensional K (standardLubinTateLevelField hπ n) :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsGalois K (standardLubinTateLevelField hπ n) :=
    standardLubinTateLevelField_isGalois hπ n
  intro Gamma' _ v'
  exact
    (hasUniqueValuationExtension_of_finite_separable.{u, v, u, 0, 0}
      F.toCompleteDVF (standardLubinTateLevelCompleteDVF hπ n)) v'

/-- The same uniqueness statement after forgetting completeness, in the form
used by the real ramification-group API. -/
theorem standardLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, u, 0, 0}
      F.toCompleteDVF.toDVF
      (standardLubinTateLevelCompleteDVF hπ n).toDVF :=
  standardLubinTateLevelCompleteDVF_hasUniqueValuationExtension hπ n

end LubinTate
