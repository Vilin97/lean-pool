/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.HerbrandFunction
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.InverseHerbrandFunction
import LeanPool.ClassFieldTheory.ClassFieldTheory.HasseArf
import Mathlib.NumberTheory.LocalField.Basic
/-! # The inverse Herbrand function is a left inverse -/

noncomputable section

namespace ClassFieldTheory

open LocalFieldTheory
open RamificationTheory.LocalField
open RamificationTheory.HilbertRamification.Higher

/-- The inverse public Herbrand function recovers every real lower index. -/
theorem inverseHerbrandFunction_herbrandFunction
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (s : ℝ) :
    inverseHerbrandFunction K L
      (ClassFieldTheory.herbrandFunction K
        (ValuativeRel.valuation L).valuationSubring s) = s := by
  have hfun :
      ClassFieldTheory.herbrandFunction K
          (ValuativeRel.valuation L).valuationSubring =
        herbrandFunctionOfUniqueExtension
          (base := (localCompleteDVF K).toDVF)
          (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
          (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension.{0} K L) := by
    funext t
    exact HasseArf.canonicalHerbrandFunction_eq_localHerbrandFunction K L t
  unfold inverseHerbrandFunction
  rw [hfun]
  change inverseHerbrandFunctionOfUniqueExtension
    (base := (localCompleteDVF K).toDVF)
    (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
    (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension.{0} K L)
    (herbrandFunctionOfUniqueExtension
      (base := (localCompleteDVF K).toDVF)
      (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
      (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension.{0} K L) s) = s
  exact inverseHerbrandFunctionOfUniqueExtension_eta
    (base := (localCompleteDVF K).toDVF)
    (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
    (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension.{0} K L) s

end ClassFieldTheory
