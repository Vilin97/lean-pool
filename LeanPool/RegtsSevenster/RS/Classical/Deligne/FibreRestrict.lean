/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.FibreStrong

/-!
# Restricting the fibre functor along a monoidal functor

A splitting algebra need not split every object of the ambient
category — after all, the ambient category here is an Ind-completion
and a filtered colimit is not a finite mixed sum.  What is needed is
only that it split the objects in the image of a chosen monoidal
functor; the composite of that functor with the fibre functor is
then strong monoidal.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v₂ u₂ v u

section

variable {D : Type u}

/-- **The algebra splits the image of a functor**: every object in
the image becomes a mixed sum of copies of the unit and of the odd
line after base change. -/
def SplitsOn [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] (L : OddLine D) (R : D)
    [MonObj R] {C : Type u₂} [Category.{v₂} C] (F : C ⥤ D) : Prop :=
  ∀ X : C, ∃ p q : ℕ,
    Nonempty (freeMod R (F.obj X) ≅ freeMod R (L.mix p q))

/-- **The restricted fibre functor is strong monoidal.** -/
@[implicit_reducible]
noncomputable def fibreRestrictMonoidal
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D] [HasFiniteBiproducts D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] {C : Type u₂}
    [Category.{v₂} C] [MonoidalCategory C] (F : C ⥤ D) [F.Monoidal]
    (hsp : SplitsOn L R F) :
    (F ⋙ fibreOver L R).Monoidal := by
  have hεF : IsIso (CategoryTheory.Functor.LaxMonoidal.ε F) :=
    ⟨CategoryTheory.Functor.OplaxMonoidal.η F,
      CategoryTheory.Functor.Monoidal.ε_η F,
      CategoryTheory.Functor.Monoidal.η_ε F⟩
  haveI : IsIso (CategoryTheory.Functor.LaxMonoidal.ε
      (F ⋙ fibreOver L R)) := by
    rw [CategoryTheory.Functor.LaxMonoidal.comp_ε]
    have h1 : IsIso (CategoryTheory.Functor.LaxMonoidal.ε
        (fibreOver L R)) := by
      rw [fibreOver_ε]; infer_instance
    exact IsIso.comp_isIso' h1
      (@CategoryTheory.Functor.map_isIso _ _ _ _ _ _
        (fibreOver L R) (CategoryTheory.Functor.LaxMonoidal.ε F)
        hεF)
  haveI : ∀ X Y : C, IsIso (CategoryTheory.Functor.LaxMonoidal.μ
      (F ⋙ fibreOver L R) X Y) := by
    intro X Y
    have hμF : IsIso (CategoryTheory.Functor.LaxMonoidal.μ F X Y) :=
      ⟨CategoryTheory.Functor.OplaxMonoidal.δ F X Y,
        CategoryTheory.Functor.Monoidal.μ_δ F X Y,
        CategoryTheory.Functor.Monoidal.δ_μ F X Y⟩
    rw [CategoryTheory.Functor.LaxMonoidal.comp_μ]
    obtain ⟨p, q, ⟨eX⟩⟩ := hsp X
    obtain ⟨p', q', ⟨eY⟩⟩ := hsp Y
    have h1 : IsIso (CategoryTheory.Functor.LaxMonoidal.μ
        (fibreOver L R) (F.obj X) (F.obj Y)) := by
      rw [fibreOver_μ]
      exact isIso_fibreMu_of_mix L R eX eY
    exact IsIso.comp_isIso' h1
      (@CategoryTheory.Functor.map_isIso _ _ _ _ _ _
        (fibreOver L R)
        (CategoryTheory.Functor.LaxMonoidal.μ F X Y) hμF)
  exact CategoryTheory.Functor.Monoidal.ofLaxMonoidal _

end

end RS
