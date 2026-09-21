/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.OddParity

/-!
# The realization of a twisted object

Deligne's `ρ(M) = (Hom(𝟙, M), Hom(1̄, M))` is computed on a twist
by one of the two generators of `⟨1, 1̄⟩`: twisting by the unit
changes nothing, and twisting by the odd line exchanges the two
components.  These four identifications are the base cases of the
computation of `ρ` on the free modules of 2.11.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {D : Type u}

/-- **The even part of a twist by the unit.** -/
noncomputable def rhoEvenUnit
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [CategoryTheory.Linear ℂ D]
    (M : D) :
    (𝟙_ D ⟶ M ⊗ 𝟙_ D) ≃ₗ[ℂ] (𝟙_ D ⟶ M) :=
  Linear.homCongr ℂ (Iso.refl (𝟙_ D)) (ρ_ M)

/-- **The odd part of a twist by the unit.** -/
noncomputable def rhoOddUnit
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [CategoryTheory.Linear ℂ D]
    (L : OddLine D) (M : D) :
    (L.obj ⟶ M ⊗ 𝟙_ D) ≃ₗ[ℂ] (L.obj ⟶ M) :=
  Linear.homCongr ℂ (Iso.refl L.obj) (ρ_ M)

/-- **The even part of a twist by the odd line** is the odd part
of the object. -/
noncomputable def rhoEvenOdd
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (M : D) :
    (𝟙_ D ⟶ M ⊗ L.obj) ≃ₗ[ℂ] (L.obj ⟶ M) :=
  oddParitySwap L M

/-- **The odd part of a twist by the odd line** is the even part
of the object. -/
noncomputable def rhoOddOdd
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (M : D) :
    (L.obj ⟶ M ⊗ L.obj) ≃ₗ[ℂ] (𝟙_ D ⟶ M) :=
  (oddParitySwap L (M ⊗ L.obj)).symm.trans
    (Linear.homCongr ℂ (Iso.refl (𝟙_ D))
      ((α_ M L.obj L.obj) ≪≫ whiskerLeftIso M L.sq ≪≫ ρ_ M))

end RS
