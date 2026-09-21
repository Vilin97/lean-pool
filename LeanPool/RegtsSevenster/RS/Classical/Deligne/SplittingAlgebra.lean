/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.UniversalAlgebra
import LeanPool.RegtsSevenster.RS.Classical.Deligne.FibreRestrict

/-!
# The splitting algebra of the embedded category

The universal algebra of `RS.exists_universal_algebra`, taken over
the family of all objects of the small category, splits the image of
the Ind-embedding in the sense of `RS.SplitsOn`, and simultaneously
splits every chosen epimorphism.  These are exactly the two
hypotheses under which the fibre functor over that algebra is strong
monoidal and exact.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v

variable {C : Type v}

/-- **The splitting algebra**: one nonzero commutative algebra that
splits every embedded object into a mixed sum and splits every
chosen epimorphism. -/
theorem exists_splitting_algebra
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [CategoryTheory.Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [RigidCategory C] [SymmetricCategory (Ind C)] [HasCoequalizers (Ind C)]
    [∀ Z : Ind C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      Z)] [HasFiniteBiproducts (Ind C)]
    (hu : HasScalarUnit C)
    (L : OddLine (Ind C)) {K : Type v} (V W : K → Ind C)
    (g : ∀ k, V k ⟶ W k)
    (hmix : ∀ X : C, L.LocallyMixed ((indOf : C ⥤ Ind C).obj X))
    (hsplit : ∀ k, ∃ (A : Ind C) (_ : MonObj A)
      (_ : IsCommMonObj A), MonObj.one (X := A) ≠ 0 ∧
      ∃ s : freeMod A (W k) ⟶ freeMod A (V k),
        s ≫ freeModMap A (g k) = 𝟙 (freeMod A (W k))) :
    ∃ (𝔸 : Ind C) (_ : MonObj 𝔸) (_ : IsCommMonObj 𝔸),
      MonObj.one (X := 𝔸) ≠ 0 ∧
      SplitsOn L 𝔸 (indOf : C ⥤ Ind C) ∧
      (∀ k, ∃ s : freeMod 𝔸 (W k) ⟶ freeMod 𝔸 (V k),
        s ≫ freeModMap 𝔸 (g k) = 𝟙 (freeMod 𝔸 (W k))) := by
  obtain ⟨𝔸, hmon, hcomm, hne, hmixed, hsec⟩ :=
    exists_universal_algebra hu L
      (fun X : C => (indOf : C ⥤ Ind C).obj X) V W g hmix hsplit
  exact ⟨𝔸, hmon, hcomm, hne, hmixed, hsec⟩

end RS
