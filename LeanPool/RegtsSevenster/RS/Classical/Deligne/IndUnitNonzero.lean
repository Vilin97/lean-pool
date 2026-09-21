/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndSchur
import LeanPool.RegtsSevenster.RS.Classical.Deligne.UnitSimple

/-!
# The unit of the Ind-completion is nonzero

A scalar unit downstairs makes the identity of the tensor unit
nonzero, and the embedding is faithful, so the tensor unit of the
Ind-completion is not a zero object.  This is the side condition of
both Proposition 2.9 and Rappel 2.10 over the Ind-completion.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v

variable {C : Type v}

/-- **The tensor unit of the Ind-completion is not a zero
object.** -/
theorem not_isZero_unit_ind [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [CategoryTheory.Linear ℂ C]
    (hu : HasScalarUnit C) :
    ¬ IsZero (𝟙_ (Ind C)) := by
  intro h
  have h0 : IsZero ((indOf : C ⥤ Ind C).obj (𝟙_ C)) :=
    h.of_iso (indOfUnitIso (C := C)).symm
  have h1 : (indOf : C ⥤ Ind C).map (𝟙 (𝟙_ C)) = 0 := by
    rw [CategoryTheory.Functor.map_id]
    exact h0.eq_zero_of_src _
  exact id_unit_ne_zero hu ((indOf_map_eq_zero_iff _).mp h1)

end RS
