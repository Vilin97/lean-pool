/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndSchurKilled
import LeanPool.RegtsSevenster.RS.Classical.Deligne.Rappel210Ind

/-!
# The base-change section for embedded short exact sequences

`RS.Classical.Deligne.Rappel210Ind` proves the local splitting
statement (Deligne 2.10) over `Ind C` for every short exact sequence
`S` whose quotient `S.X₃`, whose dual `S.X₃ᘁ` and whose unit-form
middle `RS.unitFormMid S` carry the duals used in the reduction.
This file discharges all four of those side conditions for the
sequences that the fibre-functor assembly actually consumes: the
images `T.map RS.indOf` of short exact sequences of `C`.

* `RS.exactPairingOfIso` — an exact pairing transports along an
  isomorphism of its left leg (Mathlib has the analogous
  `CategoryTheory.rightDualIso`/`leftDualIso` comparisons, but no
  transport of the pairing itself);
* `RS.hasRightDualIndOf` — embedded objects carry right duals,
  from `RS.exactPairingIndOf`; the dual of `RS.indOf.obj X` is
  `RS.indOf.obj (Xᘁ)` by construction, so the duals of `S.X₃ᘁ` are
  instances of the same lemma and `HasLeftDual (S.X₃ᘁ)` is
  Mathlib's `CategoryTheory.hasLeftDualRightDual`;
* `RS.unitName_indOf` — the name of the identity transports along
  the embedding, from the strong braided monoidal structure
  `RS.indOfBraided`;
* `RS.unitFormMidIndOfIso` — **the unit-form middle of an embedded
  sequence is embedded**: `RS.unitFormMid` is a pullback of maps
  between embedded objects, and `RS.indOf` preserves limits, so the
  comparison isomorphisms of the tensor and unit comparisons turn
  the cospan upstairs into the image of the cospan downstairs;
* `RS.rappel210_indOf` — **Deligne 2.10 for embedded sequences**.

The fourth side condition is the only one with content: `C` is
rigid, so the pullback taken in `C` has a right dual there, and
`RS.exactPairingOfIso` carries the embedded pairing across the
comparison isomorphism.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

section Transport

variable {D : Type u}

/-- Exact pairings transport along an isomorphism of the left leg. -/
@[implicit_reducible]
def exactPairingOfIso [Category.{v} D] [MonoidalCategory D]
    {X X' Y : D} [ExactPairing X Y] (e : X ≅ X') :
    ExactPairing X' Y where
  coevaluation' := η_ X Y ≫ (e.hom ▷ Y)
  evaluation' := (Y ◁ e.inv) ≫ ε_ X Y
  coevaluation_evaluation' := by
    simp only [MonoidalCategory.whiskerLeft_comp,
      MonoidalCategory.comp_whiskerRight, Category.assoc]
    rw [associator_inv_naturality_middle_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc,
      ← MonoidalCategory.whiskerLeft_comp, e.hom_inv_id,
      MonoidalCategory.whiskerLeft_id,
      MonoidalCategory.id_whiskerRight, Category.id_comp,
      ExactPairing.coevaluation_evaluation]
  evaluation_coevaluation' := by
    simp only [MonoidalCategory.whiskerLeft_comp,
      MonoidalCategory.comp_whiskerRight, Category.assoc]
    rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
      ← whisker_exchange, ← associator_naturality_right_assoc,
      ← whisker_exchange_assoc,
      ExactPairing.evaluation_coevaluation_assoc]
    simp

end Transport

section Embedded

variable {C : Type v}

/-- Embedded objects inherit right duals. -/
noncomputable instance hasRightDualIndOf
    [SmallCategory C] [MonoidalCategory C] [RigidCategory C]
    (X : C) :
    HasRightDual ((indOf : C ⥤ Ind C).obj X) where
  rightDual := (indOf : C ⥤ Ind C).obj (Xᘁ)

/-- The coevaluation of an embedded pairing: the unit comparison,
the image of the coevaluation, and the cotensorator. -/
theorem coevaluation_indOf
    [SmallCategory C] [MonoidalCategory C] [RigidCategory C]
    (X : C) :
    η_ ((indOf : C ⥤ Ind C).obj X)
        ((indOf : C ⥤ Ind C).obj (Xᘁ)) =
      Functor.LaxMonoidal.ε (indOf (C := C)) ≫
        indOf.map (η_ X (Xᘁ)) ≫
          Functor.OplaxMonoidal.δ (indOf (C := C)) X (Xᘁ) := rfl

/-- The cotensorator intertwines the braidings: the embedding is
braided, so the braiding upstairs is the image of the braiding
downstairs, conjugated by the tensor comparisons. -/
theorem delta_braiding_indOf
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C]
    (X Y : C) :
    Functor.OplaxMonoidal.δ (indOf (C := C)) X Y ≫
        (β_ ((indOf : C ⥤ Ind C).obj X)
          ((indOf : C ⥤ Ind C).obj Y)).hom =
      indOf.map (β_ X Y).hom ≫
        Functor.OplaxMonoidal.δ (indOf (C := C)) Y X := by
  rw [Functor.map_braiding, Category.assoc, Category.assoc,
    Functor.Monoidal.μ_δ, Category.comp_id]

/-- **The name of the identity transports along the embedding**. -/
theorem unitName_indOf
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C]
    [RigidCategory C]
    (X : C) :
    unitName ((indOf : C ⥤ Ind C).obj X) =
      Functor.LaxMonoidal.ε (indOf (C := C)) ≫
        indOf.map (unitName X) ≫
          Functor.OplaxMonoidal.δ (indOf (C := C)) (Xᘁ) X := by
  have h : unitName ((indOf : C ⥤ Ind C).obj X) =
      η_ ((indOf : C ⥤ Ind C).obj X)
          ((indOf : C ⥤ Ind C).obj (Xᘁ)) ≫
        (β_ ((indOf : C ⥤ Ind C).obj X)
          ((indOf : C ⥤ Ind C).obj (Xᘁ))).hom := rfl
  rw [h, coevaluation_indOf, Category.assoc, Category.assoc,
    delta_braiding_indOf, unitName, Functor.map_comp]
  simp only [Category.assoc]

/-- **The unit-form middle of an embedded sequence is embedded**:
the pullback displayed here is `RS.unitFormMid (T.map RS.indOf)`
with the dual instance of `RS.hasRightDualIndOf`, written out so
that the statement needs no local instance.  The embedding
preserves the pullback, and the tensor and unit comparisons carry
the cospan downstairs to the cospan upstairs. -/
noncomputable def unitFormMidIndOfIso
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C]
    (T : ShortComplex C) :
    (indOf : C ⥤ Ind C).obj (unitFormMid T) ≅
      pullback ((indOf : C ⥤ Ind C).obj ((T.X₃)ᘁ) ◁ indOf.map T.g)
        (unitName ((indOf : C ⥤ Ind C).obj T.X₃)) :=
  (PreservesPullback.iso (indOf : C ⥤ Ind C)
      (((T.X₃)ᘁ) ◁ T.g) (unitName T.X₃)).trans
    (HasLimit.isoOfNatIso (cospanExt
      (Functor.Monoidal.μIso (indOf : C ⥤ Ind C)
        ((T.X₃)ᘁ) T.X₂).symm
      (Functor.Monoidal.εIso (indOf : C ⥤ Ind C)).symm
      (Functor.Monoidal.μIso (indOf : C ⥤ Ind C)
        ((T.X₃)ᘁ) T.X₃).symm
      (by
        simp only [Iso.symm_hom, Functor.Monoidal.μIso_inv]
        exact Functor.OplaxMonoidal.δ_natural_right
          (indOf : C ⥤ Ind C) _ _)
      (by
        simp only [Iso.symm_hom, Functor.Monoidal.μIso_inv,
          Functor.Monoidal.εIso_inv]
        have hηε : Functor.OplaxMonoidal.η (indOf (C := C)) ≫
            Functor.LaxMonoidal.ε (indOf (C := C)) = 𝟙 _ :=
          Functor.Monoidal.η_ε _
        rw [unitName_indOf, ← Category.assoc, hηε,
          Category.id_comp])))

/-- **The local splitting statement for embedded short exact
sequences** (Deligne 2.10): the image in `Ind C` of a short exact
sequence of `C` splits after base change to a nonzero commutative
algebra.  The four duality side conditions of `RS.rappel210_ind` are
supplied here: the quotient and its dual are embedded, and so —
up to isomorphism — is the unit-form middle. -/
theorem rappel210_indOf
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] [Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)]
    (T : CategoryTheory.ShortComplex C)
    (hT : T.ShortExact) (h1 : ¬ IsZero (𝟙_ (Ind C))) :
    ∃ (A : Ind C) (_ : MonObj A) (_ : IsCommMonObj A), η[A] ≠ 0 ∧
      ∃ s : freeMod A ((T.map (indOf : C ⥤ Ind C)).X₃) ⟶
            freeMod A ((T.map (indOf : C ⥤ Ind C)).X₂),
        s ≫ freeModMap A ((T.map (indOf : C ⥤ Ind C)).g) =
          𝟙 (freeMod A ((T.map (indOf : C ⥤ Ind C)).X₃)) := by
  haveI := indOf_additive (C := C)
  letI i3 : HasRightDual ((T.map (indOf : C ⥤ Ind C)).X₃) :=
    hasRightDualIndOf T.X₃
  letI i3d : HasRightDual (((T.map (indOf : C ⥤ Ind C)).X₃)ᘁ) :=
    hasRightDualIndOf ((T.X₃)ᘁ)
  letI i4 : HasRightDual
      (unitFormMid (T.map (indOf : C ⥤ Ind C))) :=
    { rightDual := (indOf : C ⥤ Ind C).obj ((unitFormMid T)ᘁ)
      exact := exactPairingOfIso (unitFormMidIndOfIso T) }
  exact rappel210_ind (T.map (indOf : C ⥤ Ind C))
    (hT.map_of_exact (indOf : C ⥤ Ind C)) h1

end Embedded

end RS
