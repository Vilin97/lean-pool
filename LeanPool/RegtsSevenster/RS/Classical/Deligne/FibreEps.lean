/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaPairNat
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreeModShuffle

/-!
# The unit comparison of the fibre functor

The free module of the tensor unit is the regular module, whose
realization is the Γ-algebra viewed over itself, that is, the unit
of the tensor product of super modules.  The unit comparison of the
fibre functor is therefore an isomorphism outright, and on the two
components it is composition with the inverse right unitor of the
algebra.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

section

variable {D : Type u}

open SuperCommAlgebra.Mod

/-- **The unit comparison of the fibre functor.** -/
noncomputable def fibreEpsIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] :
    (gammaAlgebra D L R).unitMod ≅
      gammaModule D L R (freeMod R (𝟙_ D)).X :=
  ((gammaModuleFunctor L R).mapIso (freeModUnitIso R)).symm

/-- The unit comparison, as a morphism. -/
noncomputable abbrev fibreEps
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] :
    (gammaAlgebra D L R).unitMod ⟶
      gammaModule D L R (freeMod R (𝟙_ D)).X :=
  (fibreEpsIso L R).hom

/-- The unit comparison on the even component: composition with the
inverse right unitor of the algebra. -/
@[simp] theorem fibreEps_evenMap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (x : 𝟙_ D ⟶ R) :
    (fibreEps L R).evenMap x = x ≫ (ρ_ R).inv := rfl

/-- The unit comparison on the odd component: composition with the
inverse right unitor of the algebra. -/
@[simp] theorem fibreEps_oddMap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (u : L.obj ⟶ R) :
    (fibreEps L R).oddMap u = u ≫ (ρ_ R).inv := rfl

instance [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] :
    IsIso (fibreEps L R) := (fibreEpsIso L R).isIso_hom

end

end RS
