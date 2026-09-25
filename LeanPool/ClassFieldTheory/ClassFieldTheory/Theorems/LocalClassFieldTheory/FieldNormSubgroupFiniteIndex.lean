/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.LocalField.Basic
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.MathlibInterface
/-!
# Finite index of the local norm subgroup

Finite local reciprocity implies that the subgroup of nonzero field norms
has finite index in the multiplicative group of the base field.
-/

@[expose] public section

namespace ClassFieldTheory

/-- The norm subgroup of a finite abelian local extension has finite index. -/
theorem fieldNormSubgroup_finiteIndex
    (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    (fieldNormSubgroup K L).FiniteIndex := by
  exact LocalCFT.fieldNormSubgroup_finiteIndex K L

end ClassFieldTheory
