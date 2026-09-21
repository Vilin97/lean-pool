/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.IdeleClassConnectedQuotient
import Mathlib.FieldTheory.AbsoluteGaloisGroup
/-!
# A maximal-abelian reciprocity-map property

This predicate records surjectivity and kernel equal to the identity
component of the idèle class group. These properties alone do not determine
the normalized Artin map: finite-level Frobenius compatibility is a separate
assertion. Existence is asserted in `Theorems`.
-/

open scoped NumberField

namespace ClassFieldTheory

universe u

/-- A continuous map to the abelianized Galois group with the expected
image and kernel; normalization is not part of this predicate. -/
def IsMaximalAbelianGlobalArtin
    (K : Type u) [Field K] [NumberField K]
    (artin : NumberField.IdeleClassGroup (𝓞 K) K →ₜ*
      Field.absoluteGaloisGroupAbelianization K) : Prop :=
  Function.Surjective artin ∧
    artin.ker =
      Subgroup.connectedComponentOfOne (NumberField.IdeleClassGroup (𝓞 K) K)

end ClassFieldTheory
