/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.FibreMonoidal
import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaPairFreeFree

/-!
# The fibre functor is strong monoidal over a splitting algebra

Over an algebra for which every object becomes a mixed sum of
copies of the unit and of the odd line, the monoidal comparison of
Deligne's (2.11.1) is invertible at every pair of objects, and the
unit comparison is invertible outright.  The lax symmetric monoidal
structure of the fibre functor is therefore strong.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

section

variable {D : Type u}

/-- **A splitting algebra**: every object becomes a mixed sum of
copies of the unit and of the odd line after base change. -/
def Splits [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] (L : OddLine D) (R : D)
    [MonObj R] : Prop :=
  ∀ X : D, ∃ p q : ℕ,
    Nonempty (freeMod R X ≅ freeMod R (L.mix p q))

/-- Over a splitting algebra the monoidal comparison is invertible
at every pair of objects. -/
theorem isIso_fibreMu_of_splits
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D] [HasFiniteBiproducts D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (hsp : Splits L R) (V W : D) :
    IsIso (fibreMu L R V W) := by
  obtain ⟨p, q, ⟨eV⟩⟩ := hsp V
  obtain ⟨p', q', ⟨eW⟩⟩ := hsp W
  exact isIso_fibreMu_of_mix L R eV eW

/-- **Over a splitting algebra the fibre functor is strong
monoidal.** -/
@[implicit_reducible]
noncomputable def fibreOverMonoidal
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D] [HasFiniteBiproducts D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (hsp : Splits L R) :
    (fibreOver L R).Monoidal := by
  haveI : IsIso (CategoryTheory.Functor.LaxMonoidal.ε
      (fibreOver L R)) := by
    rw [fibreOver_ε]
    exact (fibreEpsIso L R).isIso_hom
  haveI : ∀ V W : D, IsIso (CategoryTheory.Functor.LaxMonoidal.μ
      (fibreOver L R) V W) := fun V W => by
    rw [fibreOver_μ]
    exact isIso_fibreMu_of_splits L R hsp V W
  exact CategoryTheory.Functor.Monoidal.ofLaxMonoidal _

end

end RS
