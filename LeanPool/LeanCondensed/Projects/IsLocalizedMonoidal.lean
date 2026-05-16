/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Localization.Monoidal.Functor
import Mathlib.CategoryTheory.Localization.Monoidal.Basic

/-!
# A localization-induced monoidal equivalence

When `L : C ⥤ D` is a monoidal localization with respect to a monoidal
morphism property `W`, the target `D` is monoidally equivalent to
`LocalizedMonoidal L W ε`.
-/

open CategoryTheory Localization.Monoidal MonoidalCategory

noncomputable section

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C)
  [MonoidalCategory C]

variable [W.IsMonoidal] [L.IsLocalization W] {unit : D} (ε : L.obj (𝟙_ C) ≅ unit)

local notation "L'" => toMonoidalCategory L W ε

instance : (L').IsLocalization W := inferInstanceAs (L.IsLocalization W)

variable [MonoidalCategory D]

namespace MonoidalCategory

/-- The trivial equivalence `D ≌ LocalizedMonoidal L W ε`: both categories
have the same underlying type, only the monoidal structure differs. -/
@[simps!]
def equivLocalizedMonoidal : D ≌ LocalizedMonoidal L W ε := CategoryTheory.Equivalence.refl

open Functor.Monoidal Functor.LaxMonoidal Functor.OplaxMonoidal

instance [L.Monoidal] : (equivLocalizedMonoidal L W ε).inverse.Monoidal :=
  letI : (L' ⋙ (equivLocalizedMonoidal L W ε).inverse).Monoidal := inferInstanceAs L.Monoidal
  letI : Localization.Lifting L W (L' ⋙ (equivLocalizedMonoidal L W ε).inverse)
    (equivLocalizedMonoidal L W ε).inverse  := ⟨Iso.refl _⟩
  functorMonoidalOfComp L' W (equivLocalizedMonoidal L W ε).inverse
    (L' ⋙ (equivLocalizedMonoidal L W ε).inverse)

instance [L.Monoidal] : (equivLocalizedMonoidal L W ε).functor.Monoidal :=
  (equivLocalizedMonoidal L W ε).symm.inverseMonoidal

end MonoidalCategory

end
