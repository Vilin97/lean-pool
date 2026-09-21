/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Envelope.EnvInstances

/-!
# The Karoubi embedding is braided and linear

The canonical functor `toKaroubi C` is a braided monoidal functor
(with respect to the in-tree monoidal and braided structures on
the Karoubi envelope) and is ℂ-linear.
-/

namespace RS

open CategoryTheory CategoryTheory.Category CategoryTheory.Idempotents
open CategoryTheory.MonoidalCategory

universe v u

variable {C : Type u}

private theorem tk_mu_f [Category.{v} C] [MonoidalCategory C]
    (X Y : C) :
    (Functor.LaxMonoidal.μ (toKaroubi C) X Y).f = 𝟙 (X ⊗ Y) :=
  rfl

private theorem tk_map_f [Category.{v} C]
    {X Y : C} (g : X ⟶ Y) :
    ((toKaroubi C).map g).f = g := rfl

section Braided

private theorem tk_braiding_f
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (X Y : Karoubi C) :
    (β_ X Y).hom.f = (X.p ⊗ₘ Y.p) ≫ (β_ X.X Y.X).hom := rfl

/-- **The Karoubi embedding is braided.** -/
noncomputable instance toKaroubiBraided
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] :
    Functor.Braided (toKaroubi C) where
  braided X Y := by
    apply Karoubi.hom_ext
    show (Functor.LaxMonoidal.μ (toKaroubi C) X Y).f ≫
        ((toKaroubi C).map (β_ X Y).hom).f =
      (β_ ((toKaroubi C).obj X) ((toKaroubi C).obj Y)).hom.f ≫
        (Functor.LaxMonoidal.μ (toKaroubi C) Y X).f
    rw [tk_mu_f, tk_mu_f, tk_map_f, tk_braiding_f]
    show 𝟙 (X ⊗ Y) ≫ (β_ X Y).hom =
      ((𝟙 X ⊗ₘ 𝟙 Y) ≫ (β_ X Y).hom) ≫ 𝟙 (Y ⊗ X)
    simp

end Braided

section LinearEmb

/-- **The Karoubi embedding is ℂ-linear.** -/
instance toKaroubiLinear
    [Category.{v} C] [Preadditive C] [CategoryTheory.Linear ℂ C] :
    (toKaroubi C).Linear ℂ where
  map_smul _ _ := rfl

end LinearEmb

end RS
