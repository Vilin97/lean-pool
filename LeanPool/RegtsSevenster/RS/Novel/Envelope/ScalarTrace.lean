/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.CatTheory.Trace
public import LeanPool.RegtsSevenster.RS.Classical.CatTheory.LinearCategory

/-!
# The trace as a complex number

The categorical trace lands in `End (𝟙_ C)`, the endomorphisms of
the tensor unit.  When those are exactly the scalars — the
hypothesis `HasScalarUnit` — that monoid is ℂ, and the trace becomes
a complex-valued linear functional, which is what a tower's
trace fields ask for.

Cyclicity carries across the identification unchanged.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory

universe v u

variable {C : Type u}

/-- **The unit's endomorphisms are the scalars**, as an algebra
isomorphism.  This is `HasScalarUnit` read as bijectivity of the
structure map. -/
noncomputable def unitScalarEquiv
    [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
    (h : HasScalarUnit C) :
    ℂ ≃ₐ[ℂ] End (𝟙_ C) :=
  AlgEquiv.ofBijective (Algebra.ofId ℂ (End (𝟙_ C))) h

/-- **The scalar named by an endomorphism of the unit.** -/
noncomputable def unitScalar
    [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
    (h : HasScalarUnit C) :
    End (𝟙_ C) →ₐ[ℂ] ℂ :=
  (unitScalarEquiv h).symm

/-! ## The complex-valued trace -/

/-- **The complex-valued categorical trace.** -/
noncomputable def scalarTrace
    [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
    [SymmetricCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [RigidCategory C]
    (h : HasScalarUnit C) (X : C) :
    End X →ₗ[ℂ] ℂ :=
  (unitScalar h).toLinearMap.comp (catTraceLin X)

/-- The complex-valued trace is cyclic. -/
theorem scalarTrace_comp_comm
    [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
    [SymmetricCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [RigidCategory C]
    (h : HasScalarUnit C) {X Y : C}
    (f : X ⟶ Y) (g : Y ⟶ X) :
    scalarTrace h X (f ≫ g) = scalarTrace h Y (g ≫ f) := by
  change unitScalar h (catTrace (f ≫ g)) = unitScalar h (catTrace (g ≫ f))
  rw [catTrace_comp_comm]

end RS
