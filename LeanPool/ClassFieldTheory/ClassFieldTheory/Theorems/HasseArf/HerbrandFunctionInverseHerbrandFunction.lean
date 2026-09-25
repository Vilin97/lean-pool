/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.HerbrandFunction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.InverseHerbrandFunction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.HasseArf
public import Mathlib.NumberTheory.LocalField.Basic
/-! # The Herbrand function is a right inverse -/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

open LocalFieldTheory
open RamificationTheory.LocalField
open RamificationTheory.HilbertRamification.Higher

/-- The public Herbrand function takes its inverse value back to the given
upper index. -/
theorem herbrandFunction_inverseHerbrandFunction
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (t : ℝ) :
    ClassFieldTheory.herbrandFunction K
      (ValuativeRel.valuation L).valuationSubring
      (inverseHerbrandFunction K L t) = t := by
  have hfun :
      ClassFieldTheory.herbrandFunction K
          (ValuativeRel.valuation L).valuationSubring =
        herbrandFunctionOfUniqueExtension
          (base := (localCompleteDVF K).toDVF)
          (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
          (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension.{0} K L) := by
    funext s
    exact HasseArf.canonicalHerbrandFunction_eq_localHerbrandFunction K L s
  unfold inverseHerbrandFunction
  rw [hfun]
  change herbrandFunctionOfUniqueExtension
    (base := (localCompleteDVF K).toDVF)
    (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
    (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension.{0} K L)
    (inverseHerbrandFunctionOfUniqueExtension
      (base := (localCompleteDVF K).toDVF)
      (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
      (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension.{0} K L) t) = t
  exact herbrandFunctionOfUniqueExtension_psi
    (base := (localCompleteDVF K).toDVF)
    (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
    (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension.{0} K L) t

end ClassFieldTheory
