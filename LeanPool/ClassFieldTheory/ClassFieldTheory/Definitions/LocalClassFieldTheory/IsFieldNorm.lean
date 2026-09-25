/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup
/-!
# Predicate for field norms
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

universe u v

/-- A nonzero element of `K` is a field norm from `L`. -/
def IsFieldNorm
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (x : Kˣ) : Prop :=
  x ∈ fieldNormSubgroup K L

end ClassFieldTheory
