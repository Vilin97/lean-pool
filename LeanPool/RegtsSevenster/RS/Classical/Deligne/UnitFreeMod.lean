/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.UnitBase

/-!
# The trivial module as a free module

Over the tensor unit as base algebra the free module on `V` and
the trivial module on `V` agree, through the left unitor.

* `unitFreeIso`: the trivial module `unitMod V` is isomorphic, as
  a module over the unit, to the free module `freeMod (𝟙_ D) V`,
  by the inverse left unitor `(λ_ V).inv : V ⟶ 𝟙_ D ⊗ V`.

This is the collapse `freeModUnitBase` read in the direction that
presents a bare object as a free module; the linearity of either
leg is the coherence identity in the monoidal unit recorded by
`freeModUnitBase_linear` and `freeModUnitBase_linear_inv`.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory

universe v u

variable {D : Type u}

section UnitFree

/-- **The trivial module on `V` is the free module on `V` over
the tensor unit**, through the inverse left unitor. -/
noncomputable def unitFreeIso [Category.{v} D] [MonoidalCategory D] (V : D) :
    unitMod V ≅ freeMod (𝟙_ D) V :=
  (freeModUnitBase V).symm

@[simp] lemma unitFreeIso_hom_hom
    [Category.{v} D] [MonoidalCategory D] (V : D) :
    (unitFreeIso V).hom.hom = (λ_ V).inv := rfl

@[simp] lemma unitFreeIso_inv_hom
    [Category.{v} D] [MonoidalCategory D] (V : D) :
    (unitFreeIso V).inv.hom = (λ_ V).hom := rfl

end UnitFree

end RS
