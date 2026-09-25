/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.IsFieldNorm
/-!
# Membership in the field-norm subgroup

This module gives the concrete meaning of the public predicate
`IsFieldNorm`.  For a finite-dimensional extension of fields `L / K` and a
unit `x` of `K`, it states that `x` belongs to the range of the unit-valued
field norm exactly when some unit of `L` has algebra norm equal to `x`.
No Galois, local-field, or topological assumption is required.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

universe u v

/-- Membership in the norm subgroup is equivalent to being the algebra norm
of a unit of the extension field. -/
theorem mem_fieldNormSubgroup_iff
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (x : Kˣ) :
    IsFieldNorm K L x ↔
      ∃ y : Lˣ, Algebra.norm K (y : L) = (x : K) := by
  change (∃ y : Lˣ, fieldNormHom K L y = x) ↔
    ∃ y : Lˣ, Algebra.norm K (y : L) = (x : K)
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg (fun z : Kˣ => (z : K)) hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Units.ext hy⟩

end ClassFieldTheory
