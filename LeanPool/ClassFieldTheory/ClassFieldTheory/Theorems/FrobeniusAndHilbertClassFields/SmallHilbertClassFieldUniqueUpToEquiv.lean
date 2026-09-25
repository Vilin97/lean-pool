/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.SmallHilbertClassFieldUnique
/-!
# Small Hilbert class fields are isomorphic

The intrinsic maximality condition determines a small Hilbert class field up to
an isomorphism over the base.  This asserts existence of an isomorphism, not a
distinguished or unique choice of one.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

universe u

/-- Any two small Hilbert class fields are isomorphic over the base field.
The isomorphism itself need not be unique. -/
theorem smallHilbertClassFields_equiv
    (K : Type u) [Field K] [NumberField K]
    (E F : FiniteAbelianExtension K)
    (hE : IsSmallHilbertClassField E)
    (hF : IsSmallHilbertClassField F) :
    Nonempty (E ≃ₐ[K] F) := by
  have hEF : E = F :=
    Subtype.ext (smallHilbertClassFields_eq K E F hE hF)
  cases hEF
  exact ⟨AlgEquiv.refl⟩

end ClassFieldTheory
