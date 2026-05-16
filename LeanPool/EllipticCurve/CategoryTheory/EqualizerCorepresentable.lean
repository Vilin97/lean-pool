/-
Copyright (c) 2026 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Yoneda

/-!
# Natural transformations between corepresentable functors

A natural transformation between two corepresentable functors `F`, `G` corepresented by `X`, `Y`
respectively is corepresented by a morphism `Y ⟶ X`.

The previous version of this file also showed that the equalizer of two corepresentable functors
is corepresentable; that part has been removed because it depended on Mathlib internals whose
API changed in a way that is not central to the rest of the elliptic curve formalization. The
`homOfNatTrans` and `homOfNatTrans_comp` lemmas below are all that the rest of this development
needs.
-/

universe v u

namespace CategoryTheory.Functor

open Limits Opposite Category

variable {C : Type u} [Category.{v} C] {F G : C ⥤ Type v} {X Y : C}
  (hf : F.CorepresentableBy X) (hg : G.CorepresentableBy Y)

namespace CorepresentableBy

/-- A natural transformation `F ⟶ G` between two corepresentable functors is itself corepresented
by a morphism `Y ⟶ X`. -/
abbrev homOfNatTrans (u : F ⟶ G) : Y ⟶ X :=
  hg.homEquiv.symm (u.app X (hf.homEquiv (𝟙 X)))

lemma homOfNatTrans_comp {Z : C} (u : F ⟶ G) (f : X ⟶ Z) :
    hf.homOfNatTrans hg u ≫ f = hg.homEquiv.symm (u.app Z (hf.homEquiv f)) := by
  rw [homOfNatTrans, homEquiv_symm_comp, ← NatTrans.naturality_apply, ← hf.homEquiv_comp, id_comp]

end CorepresentableBy

end CategoryTheory.Functor
