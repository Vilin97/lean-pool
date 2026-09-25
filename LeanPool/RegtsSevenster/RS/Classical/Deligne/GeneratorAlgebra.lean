/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.CountableDescentClose
import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndLocallyMixed
import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndUnitNonzero
import LeanPool.RegtsSevenster.RS.Classical.Deligne.ScalarUnitInd

/-!
# The splitting algebra of a single object

The argument of Deligne §2.11 tensors together a splitting algebra
for every object of the category and a section for every short exact
sequence.  The index family is then as large as the category itself,
and the ring of scalars of the result has no dimension bound.

Only one object need be split.  Over a *simple* algebra the free
modules on the unit and on the odd line are simple, so a free mixed
module is semisimple of finite length and every subquotient of it is
again free mixed; the class of split objects is therefore closed
under subobjects and quotients as well as sums, tensor products and
duals, and a tensor generator drags the whole category into it.

This module supplies the entry point: for a single object, a
splitting algebra that is *countably presented*, which is what makes
its scalars a field of countable dimension over the complex numbers,
hence the complex numbers themselves.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v

variable {C : Type v}

/-- **The splitting algebra of a single object, countably
presented.**  Proposition 2.9 makes the object locally mixed, and
the countable descent replaces the witnessing algebra by a countably
presented one. -/
theorem exists_generator_algebra
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    (ψ : ℂ ≃+* End (𝟙_ C))
    (P : SchurPackage.{v}) (P₀ : SchurPackage.{0})
    (L : OddLine (Ind C)) (X₀ : C) (lam : YoungDiagram)
    (hkill : letI := linearOfScalarUnit ψ; SchurKilled P X₀ lam)
    (hlen : ∀ Z : C, ∃ N : ℕ, LengthLE Z N) :
    letI := linearOfScalarUnit ψ
    letI := monoidalLinearOfScalarUnitBraided ψ
    letI := linearOfScalarUnit (indScalarUnit ψ)
    letI := monoidalLinearOfScalarUnitBraided (indScalarUnit ψ)
    ∃ (p q : ℕ) (𝔸 : Ind C) (_ : MonObj 𝔸) (_ : IsCommMonObj 𝔸),
      η[𝔸] ≠ 0 ∧ CountablyPresented 𝔸 ∧
        Nonempty (freeMod 𝔸 ((indOf : C ⥤ Ind C).obj X₀) ≅
          freeMod 𝔸 (L.mix p q)) := by
  let := linearOfScalarUnit ψ
  let := monoidalLinearOfScalarUnitBraided ψ
  let := linearOfScalarUnit (indScalarUnit ψ)
  let := monoidalLinearOfScalarUnitBraided (indScalarUnit ψ)
  have hu : HasScalarUnit C := hasScalarUnit_of_scalarUnit ψ
  have h1 : ¬ IsZero (𝟙_ (Ind C)) := not_isZero_unit_ind hu
  exact locallyMixed_countablyPresented L
    ((indOf : C ⥤ Ind C).obj X₀) (indCompactObj_indOf X₀) hlen
    (locallyMixed_indOf ψ P P₀ X₀ lam hkill L h1)

end RS
