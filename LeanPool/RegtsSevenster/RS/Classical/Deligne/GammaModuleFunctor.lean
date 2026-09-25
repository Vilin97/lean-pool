/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperModHom

/-!
# Realization as a functor on module objects

Taking the morphisms out of the two generators is functorial on
module objects over a fixed commutative monoid object: the
realization of a module map is postcomposition.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {D : Type u}

/-- **Realization, as a functor on module objects.** -/
noncomputable def gammaModuleFunctor
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (R : D)
    [MonObj R] [IsCommMonObj R] :
    Mod D R ⥤ (gammaAlgebra D L R).Mod where
  obj M := gammaModule D L R M.X
  map {_ _} f :=
    letI : IsModHom R f.hom := f.isModHom
    gammaModuleMap L R f.hom
  map_id M := by
    refine SuperCommAlgebra.Mod.Hom.ext ?_ ?_ <;>
      refine LinearMap.ext fun m => ?_ <;>
      · change m ≫ Mod.Hom.hom (𝟙 M) = m
        erw [Mod.id_hom', Category.comp_id]
  map_comp {M N P} f g := by
    refine SuperCommAlgebra.Mod.Hom.ext ?_ ?_ <;>
      refine LinearMap.ext fun m => ?_ <;>
      · change m ≫ Mod.Hom.hom (f ≫ g) = (m ≫ f.hom) ≫ g.hom
        erw [Mod.comp_hom', Category.assoc]

end RS
