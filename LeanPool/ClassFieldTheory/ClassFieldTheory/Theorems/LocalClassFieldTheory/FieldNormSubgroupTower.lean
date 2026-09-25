/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup
public import Mathlib.RingTheory.Norm.Transitivity
/-!
# Norm subgroups in a tower

The norm from a larger field factors through the norm from every intermediate
field. Thus enlarging a finite extension can only shrink its subgroup of
norms in the base field. No local-field or Galois assumption is needed.
-/

@[expose] public section

noncomputable
section

namespace ClassFieldTheory

universe u v w

/-- In a finite tower `K ⊆ M ⊆ L`, every norm from `L` to `K` is a norm
from `M` to `K`. -/
theorem fieldNormSubgroup_le_of_tower
    (K : Type u) (M : Type v) (L : Type w)
    [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L] [FiniteDimensional K L] :
    fieldNormSubgroup K L ≤ fieldNormSubgroup K M := by
  rintro x ⟨y, rfl⟩
  refine ⟨fieldNormHom M L y, ?_⟩
  apply Units.ext
  exact Algebra.norm_norm

end ClassFieldTheory
