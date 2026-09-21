/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Algebra.Group.Units
/-!
# The connected-component quotient of the idèle class group

For a number field `K`, Mathlib's idèle class group is the unit group of
the adele ring modulo principal idèles. Its quotient by the connected
component of `1` is the group appearing in topological global reciprocity.
-/

open scoped NumberField

namespace ClassFieldTheory

universe u

/-- The identity component is normal because the idèle class group is abelian. -/
instance instNormalIdeleClassConnectedComponent
    (K : Type u) [Field K] [NumberField K] :
    (Subgroup.connectedComponentOfOne (NumberField.IdeleClassGroup (𝓞 K) K)).Normal := by
  constructor
  intro n hn g
  have h : g * n * g⁻¹ = n := by
    rw [mul_comm g n, mul_assoc, mul_inv_cancel, mul_one]
  rw [h]
  exact hn

/-- The idèle class group modulo its identity component. -/
abbrev IdeleClassConnectedQuotient (K : Type u) [Field K] [NumberField K] :=
  NumberField.IdeleClassGroup (𝓞 K) K ⧸
    Subgroup.connectedComponentOfOne (NumberField.IdeleClassGroup (𝓞 K) K)

end ClassFieldTheory
