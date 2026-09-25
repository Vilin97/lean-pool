/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.HerbrandFunction
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.Extension
/-!
# The inverse Herbrand function for a canonical local extension

The defining choice is verified to be a two-sided inverse for finite Abelian
local extensions in the theorem layer.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The inverse of the public real Herbrand function for the canonical
valuation ring of a finite Abelian local extension. -/
def inverseHerbrandFunction
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [ValuativeRel L] [TopologicalSpace L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (t : ℝ) : ℝ :=
  Function.invFun
    (herbrandFunction K (ValuativeRel.valuation L).valuationSubring) t

end ClassFieldTheory
