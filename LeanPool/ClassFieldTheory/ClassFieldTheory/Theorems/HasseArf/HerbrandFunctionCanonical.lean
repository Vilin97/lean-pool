/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.HerbrandFunction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.HasseArf
public import Mathlib.NumberTheory.LocalField.Basic
/-!
# Strict growth of the public Herbrand function

The piecewise function defined from the public integral lower groups agrees
with the existing Herbrand function of the local lower filtration. Its strict
growth is consequently available without exposing that filtration in the
public theorem statement.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

open LocalFieldTheory
open RamificationTheory.LocalField
open RamificationTheory.HilbertRamification.Higher

/-- For a finite Abelian extension of nonarchimedean local fields, the
Herbrand function built from the canonical lower groups is strictly
increasing on the real line. -/
theorem herbrandFunction_canonical_strictMono
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    StrictMono (ClassFieldTheory.herbrandFunction K
      (ValuativeRel.valuation L).valuationSubring) := by
  intro s t hst
  rw [← HasseArf.chosenLocalExtension_valuationSubring_eq_canonical K L]
  rw [HasseArf.chosenHerbrandFunction_eq_localHerbrandFunction K L s,
    HasseArf.chosenHerbrandFunction_eq_localHerbrandFunction K L t]
  exact
    (herbrandFunctionOfUniqueExtension_strictMono
      (base := (localCompleteDVF K).toDVF)
      (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
      (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension.{0} K L)) hst

end ClassFieldTheory
