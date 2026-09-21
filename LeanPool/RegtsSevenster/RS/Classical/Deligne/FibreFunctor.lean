/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.Rappel210
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperModHom

/-!
# The fibre functor over an algebra

Deligne's `ω` of 2.11: base change to the algebra, then take the
morphisms out of the two generators.  Both steps are functorial,
so `ω` is a functor from the category to the super modules over
the Γ-algebra of the base.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v

variable {C : Type v}

/-- The base change of an object, as a module object. -/
noncomputable abbrev fibreObj
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A]
    (X : Ind C) : Ind C :=
  (freeMod A X).X

/-- **The fibre functor over an algebra** (Deligne 2.11): base
change and realize. -/
noncomputable def fibreFunctor
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [MonoidalPreadditive C] [CategoryTheory.Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)] (L : OddLine (Ind C)) (A : Ind C) [MonObj A]
    [IsCommMonObj A] :
    Ind C ⥤ (gammaAlgebra (Ind C) L A).Mod where
  obj X := gammaModule (Ind C) L A (fibreObj A X)
  map {_ _} f :=
    letI : IsModHom A (freeModMap A f).hom :=
      (freeModMap A f).isModHom
    gammaModuleMap L A (freeModMap A f).hom
  map_id X := by
    refine SuperCommAlgebra.Mod.Hom.ext ?_ ?_ <;>
      refine LinearMap.ext fun m => ?_ <;>
      · show m ≫ (freeModMap A (𝟙 X)).hom = m
        erw [show (freeModMap A (𝟙 X)).hom = 𝟙 (fibreObj A X) from
          MonoidalCategory.whiskerLeft_id A X, Category.comp_id]
  map_comp {X Y Z} f g := by
    refine SuperCommAlgebra.Mod.Hom.ext ?_ ?_ <;>
      refine LinearMap.ext fun m => ?_ <;>
      · show m ≫ (freeModMap A (f ≫ g)).hom =
          (m ≫ (freeModMap A f).hom) ≫ (freeModMap A g).hom
        erw [show (freeModMap A (f ≫ g)).hom =
            (freeModMap A f).hom ≫ (freeModMap A g).hom from
            MonoidalCategory.whiskerLeft_comp A f g,
          ← Category.assoc]

end RS
