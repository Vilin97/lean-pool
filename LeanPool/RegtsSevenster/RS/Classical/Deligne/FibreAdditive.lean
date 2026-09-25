/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreeModFunctor

/-!
# The fibre functor is additive

Base change followed by realization is a functor from the ambient
category to the super modules over the Γ-algebra, and it is
additive: whiskering by the algebra is additive, and realization is
composition.  Additivity is what makes the fibre functor preserve
finite biproducts, and hence what turns a mixed sum into a free
super module of the corresponding rank.

The functor is built directly rather than as a composite through
the module objects, because the category of module objects carries
no additive structure in this development.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

section

variable {D : Type u}

/-- **The fibre functor over an algebra**: base change, then
realize. -/
noncomputable def fibreFun
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] :
    D ⥤ (gammaAlgebra D L R).Mod where
  obj V := gammaModule D L R (freeMod R V).X
  map f := (gammaModuleFunctor L R).map (freeModMap R f)
  map_id V := by
    rw [freeModMap_id]
    exact CategoryTheory.Functor.map_id _ _
  map_comp f g := by
    rw [freeModMap_comp]
    exact CategoryTheory.Functor.map_comp _ _ _

@[simp] theorem fibreFun_obj
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (V : D) :
    (fibreFun L R).obj V = gammaModule D L R (freeMod R V).X := rfl

@[simp] theorem fibreFun_map
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    {V W : D} (f : V ⟶ W) :
    (fibreFun L R).map f =
      (gammaModuleFunctor L R).map (freeModMap R f) := rfl

/-- **The fibre functor is additive.** -/
instance fibreFun_additive
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] :
    (fibreFun L R).Additive where
  map_add {V W f g} := by
    rw [fibreFun_map, fibreFun_map, fibreFun_map]
    refine SuperCommAlgebra.Mod.Hom.ext ?_ ?_ <;>
      refine LinearMap.ext fun m => ?_
    · change m ≫ (R ◁ (f + g)) = m ≫ (R ◁ f) + m ≫ (R ◁ g)
      rw [MonoidalPreadditive.whiskerLeft_add]
      exact Preadditive.comp_add _ _ _ _ _ _
    · change m ≫ (R ◁ (f + g)) = m ≫ (R ◁ f) + m ≫ (R ◁ g)
      rw [MonoidalPreadditive.whiskerLeft_add]
      exact Preadditive.comp_add _ _ _ _ _ _

/-- **The fibre functor takes a finite biproduct to a finite
biproduct.** -/
noncomputable def fibreFunBiproduct
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    [HasFiniteBiproducts D]
    {ι : Type} [Fintype ι]
    (f : ι → D) :
    (fibreFun L R).obj (⨁ f) ≅ ⨁ fun i => (fibreFun L R).obj (f i) :=
  (fibreFun L R).mapBiproduct f

end

end RS
