/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.Prop21
import LeanPool.RegtsSevenster.RS.Classical.Deligne.DoubledLine
import LeanPool.RegtsSevenster.RS.Classical.Deligne.DoubledScalar
import LeanPool.RegtsSevenster.RS.Classical.Deligne.DoubledGrowth
import LeanPool.RegtsSevenster.RS.Classical.Deligne.EvenEmbedMonoidal
import LeanPool.RegtsSevenster.RS.Classical.Deligne.OddLineMap
import LeanPool.RegtsSevenster.RS.Classical.Deligne.ScalarUnitEquiv

/-!
# Deligne's Proposition 2.1 without an odd line

`RS.exists_fibre_functor` produces the fibre algebra and its fibre
functor for a category whose ind-completion already carries an odd
line.  A tensor category need not contain such an object; Deligne's
device is to pass to the ℤ/2-graded doubling, which always does,
and to restrict along the even embedding.

This module runs that device.  The doubling of a small abelian
rigid symmetric monoidal ℂ-linear category with scalar unit
endomorphisms and moderate length growth inherits every one of those
hypotheses, and its ind-completion carries the image of the odd line
`RS.doubledOddLine` under the embedding.  Proposition 2.1 upstairs
therefore applies, and the resulting fibre functor restricts along
the even embedding `A ⥤ Doubled A`, which is strong braided
monoidal, exact and faithful; each of the four conclusions composes.

The hypothesis of 2.1 — that every object is killed by some Schur
functor — is supplied by the growth dichotomy
`RS.forall_exists_schurKilled`, applied to the doubling.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v

noncomputable section

variable {A : Type v}

/-- **The scalar unit of the doubling**, as the ring isomorphism
that Proposition 2.1 consumes: the unit of the doubling is the unit
of `A` in even degree, so its endomorphisms are the scalars. -/
def doubledScalarUnit [SmallCategory A] [MonoidalCategory A] [Abelian A]
    [MonoidalPreadditive A] [CategoryTheory.Linear ℂ A]
    (hu : HasScalarUnit A) :
    ℂ ≃+* End (𝟙_ (Doubled A)) :=
  scalarUnitEquiv (hasScalarUnit_doubled hu)

/-- **The odd line of the ind-completion of the doubling**: the
image of the odd line of the doubling under the embedding, which is
strong braided monoidal and additive. -/
def doubledIndOddLine
    [SmallCategory A] [MonoidalCategory A] [SymmetricCategory A] [Abelian A]
    [MonoidalPreadditive A] : OddLine (Ind (Doubled A)) :=
  letI := indOf_additive (C := Doubled A)
  OddLine.map (indOf : Doubled A ⥤ Ind (Doubled A)) doubledOddLine

/-- **Deligne's Proposition 2.1 in general**: no odd line is
assumed.  The category is doubled, Proposition 2.1 runs on the
doubling — whose ind-completion carries an odd line — and the fibre
functor obtained there is restricted along the even embedding.  The
composite is strong monoidal, preserves finite limits and finite
colimits, and is faithful. -/
theorem exists_fibre_functor_general
    [SmallCategory A] [MonoidalCategory A] [SymmetricCategory A] [Abelian A]
    [RigidCategory A] [MonoidalPreadditive A] [CategoryTheory.Linear ℂ A]
    (P : SchurPackage.{v})
    (P₀ : SchurPackage.{0}) (hu : HasScalarUnit A)
    (hgrow : ModerateLengthGrowth A) :
    letI := linearOfScalarUnit (doubledScalarUnit hu)
    letI := monoidalLinearOfScalarUnitBraided (doubledScalarUnit hu)
    letI := linearOfScalarUnit (indScalarUnit (doubledScalarUnit hu))
    letI := monoidalLinearOfScalarUnitBraided
      (indScalarUnit (doubledScalarUnit hu))
    ∃ (𝔸 : Ind (Doubled A)) (_ : MonObj 𝔸) (_ : IsCommMonObj 𝔸),
      MonObj.one (X := 𝔸) ≠ 0 ∧
      Nonempty ((Doubled.evenEmbed ⋙
        (indOf : Doubled A ⥤ Ind (Doubled A)) ⋙
          fibreOver doubledIndOddLine 𝔸).Monoidal) ∧
      Nonempty (Limits.PreservesFiniteLimits (Doubled.evenEmbed ⋙
        (indOf : Doubled A ⥤ Ind (Doubled A)) ⋙
          fibreFun doubledIndOddLine 𝔸)) ∧
      Nonempty (Limits.PreservesFiniteColimits (Doubled.evenEmbed ⋙
        (indOf : Doubled A ⥤ Ind (Doubled A)) ⋙
          fibreFun doubledIndOddLine 𝔸)) ∧
      (Doubled.evenEmbed ⋙ (indOf : Doubled A ⥤ Ind (Doubled A)) ⋙
        fibreFun doubledIndOddLine 𝔸).Faithful := by
  let := linearOfScalarUnit (doubledScalarUnit hu)
  let := monoidalLinearOfScalarUnitBraided (doubledScalarUnit hu)
  let := linearOfScalarUnit (indScalarUnit (doubledScalarUnit hu))
  let := monoidalLinearOfScalarUnitBraided
    (indScalarUnit (doubledScalarUnit hu))
  obtain ⟨𝔸, hmon, hcomm, hne, ⟨hM⟩, ⟨hL⟩, ⟨hCo⟩, hF⟩ :=
    exists_fibre_functor (C := Doubled A) (doubledScalarUnit hu) P P₀
      doubledIndOddLine
      (forall_exists_schurKilled P
        (hasScalarUnit_of_scalarUnit (doubledScalarUnit hu))
        (moderateLengthGrowth_doubled hgrow))
  let := hmon
  let := hcomm
  let := hM
  let := hL
  let := hCo
  let := hF
  exact ⟨𝔸, hmon, hcomm, hne, ⟨inferInstance⟩,
    ⟨comp_preservesFiniteLimits _ _⟩,
    ⟨comp_preservesFiniteColimits _ _⟩, inferInstance⟩

end

end RS
