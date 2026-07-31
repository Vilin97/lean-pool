/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.MonoCoprod

universe v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [MonoCoprod C]
  {J : Type u'} [Category.{v'} J]

instance [∀ (j : J), PreservesColimitsOfShape (Discrete WalkingPair) ((evaluation J C).obj j)] :
    MonoCoprod (J ⥤ C) where
  binaryCofan_inl A B c hc := by
    have (j : J) : Mono (c.inl.app j) := MonoCoprod.binaryCofan_inl _
      ((isColimitMapCoconeBinaryCofanEquiv (G := (evaluation J C).obj j) _ _ ).1
        (isColimitOfPreserves _ (IsColimit.ofIsoColimit hc (isoBinaryCofanMk c))))
    apply NatTrans.mono_of_mono_app

end CategoryTheory
