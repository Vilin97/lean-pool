/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.LocalField.Basic
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.MathlibInterface
/-!
# Openness of the local norm subgroup

For a finite abelian extension of a nonarchimedean local field, the subgroup
of nonzero field norms is open in the multiplicative group of the base.
-/

namespace ClassFieldTheory

/-- The norm subgroup of a finite abelian local extension is open. -/
theorem isOpen_fieldNormSubgroup
    (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    IsOpen (fieldNormSubgroup K L : Set Kˣ) := by
  exact LocalCFT.isOpen_fieldNormSubgroup K L

end ClassFieldTheory
