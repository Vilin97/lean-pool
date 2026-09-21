/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Monoidal functors preserve exact pairings

We show that a monoidal functor `F : C ⥤ D` sends an
exact pairing `(X, Y)` in the source to an exact pairing
`(F.obj X, F.obj Y)` in the target, with evaluation and
coevaluation obtained by conjugating through the
tensorator and unit isomorphisms of `F`.

This is the forward direction of the standard fact
"monoidal functors preserve dualizability". The reverse
direction (pulling back exact pairings along a faithful
monoidal functor) is Mathlib's
`ExactPairing.ofFaithful`.
-/

namespace RS

open CategoryTheory MonoidalCategory Category
open Functor.LaxMonoidal Functor.OplaxMonoidal
open Functor.Monoidal

variable {C D : Type*}

/-- Monoidal functors preserve exact pairings:
an `ExactPairing X Y` in `C` yields an
`ExactPairing (F.obj X) (F.obj Y)` in `D`,
with evaluation and coevaluation conjugated
through the tensorator and unit isomorphisms
of `F`. -/
@[instance_reducible]
def ExactPairing.map
    [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal]
    {X Y : C}
    [ExactPairing X Y] :
    ExactPairing (F.obj X) (F.obj Y) where
  evaluation' :=
    μ F Y X ≫ F.map (ε_ X Y) ≫ η F
  coevaluation' :=
    ε F ≫ F.map (η_ X Y) ≫ δ F X Y
  coevaluation_evaluation' := by
    simp only [whiskerLeft_comp,
      comp_whiskerRight, assoc]
    rw [map_associator_inv' F Y X Y]
    simp only [assoc, whiskerLeft_δ_μ_assoc,
      whiskerRight_δ_μ_assoc]
    rw [μ_natural_right_assoc,
      δ_natural_left_assoc,
      ← Functor.map_comp_assoc,
      ← Functor.map_comp_assoc, assoc,
      ExactPairing.coevaluation_evaluation,
      Functor.map_comp, assoc,
      map_rightUnitor_assoc F,
      μ_δ_assoc, whiskerLeft_ε_η_assoc,
      map_leftUnitor_inv F]
    simp only [assoc, μ_δ_assoc,
      whiskerRight_ε_η, comp_id]
  evaluation_coevaluation' := by
    simp only [comp_whiskerRight,
      whiskerLeft_comp, assoc]
    rw [map_associator' F X Y X]
    simp only [assoc, whiskerRight_δ_μ_assoc,
      whiskerLeft_δ_μ_assoc]
    rw [μ_natural_left_assoc,
      δ_natural_right_assoc,
      ← Functor.map_comp_assoc,
      ← Functor.map_comp_assoc, assoc,
      ExactPairing.evaluation_coevaluation,
      Functor.map_comp, assoc,
      map_leftUnitor_assoc F,
      μ_δ_assoc, whiskerRight_ε_η_assoc,
      map_rightUnitor_inv F]
    simp only [assoc, μ_δ_assoc,
      whiskerLeft_ε_η, comp_id]

end RS
