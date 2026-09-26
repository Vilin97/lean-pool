/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsEverywhereUnramified
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
/-!
# Small Hilbert class fields
-/

@[expose] public section

namespace ClassFieldTheory

universe u

/-- A small Hilbert class field is an everywhere-unramified finite abelian
extension containing every other such extension. -/
def IsSmallHilbertClassField
    {K : Type u} [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) : Prop :=
  IsEverywhereUnramified K E ∧
    ∀ F : FiniteAbelianExtension K,
      IsEverywhereUnramified K F → Nonempty (F →ₐ[K] E)

end ClassFieldTheory
