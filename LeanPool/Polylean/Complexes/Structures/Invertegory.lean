/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import LeanPool.Polylean.Complexes.Structures.Category

namespace LeanPool.Polylean

/-!
`Invertegory` is an intermediate structure between a category and a groupoid:
every morphism has a formal inverse, but the inverse is not required to satisfy
the groupoid inverse laws.
-/

/-- A category equipped with formal inverses for all morphisms. -/
class Invertegory (Obj : Sort _) extends Category Obj where
  /-- Formal inverse of a morphism. -/
  inv : {X Y : Obj} → (X ⟶ Y) → (Y ⟶ X)
  invInv : ∀ e : X ⟶ Y, inv (inv e) = e

namespace Invertegory

/-- A morphism of `Invertegory`s preserving formal inverses. -/
structure Functor {C D : Sort _} (ℭ : Invertegory C) (𝔇 : Invertegory D)
    extends Category.Functor ℭ.toCategory 𝔇.toCategory where
  mapInv : {X Y : C} → {f : X ⟶ Y} → map (Invertegory.inv f) = Invertegory.inv (map f)

attribute [simp] Functor.mapInv

end Invertegory

end LeanPool.Polylean
