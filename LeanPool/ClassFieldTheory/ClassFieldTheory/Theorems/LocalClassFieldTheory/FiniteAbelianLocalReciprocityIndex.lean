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
# Index formula in finite abelian local reciprocity

The index of the norm subgroup equals the degree of the finite abelian local
extension.  This is the numerical form of the reciprocity isomorphism.
-/

namespace ClassFieldTheory

/-- The norm-subgroup index is the degree of the extension. -/
theorem fieldNormSubgroup_index_eq_finrank
    (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    (fieldNormSubgroup K L).index = Module.finrank K L := by
  exact LocalCFT.fieldNormSubgroup_index_eq_finrank K L

end ClassFieldTheory
