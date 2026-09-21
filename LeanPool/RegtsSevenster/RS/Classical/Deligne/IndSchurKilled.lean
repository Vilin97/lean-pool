/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndOfMonoidal

/-!
# Schur vanishing and exact pairings across `C ⥤ Ind C`

`RS.Classical.Deligne.IndSchur` transports the symmetric-group action
on tensor powers along the embedding `RS.indOf : C ⥤ Ind C` at the
level of single permutations, and `RS.Classical.Deligne.IndOfMonoidal`
packages the comparison data as a strong (braided) monoidal structure
on `indOf`.  `RS.Classical.Deligne.ScalarLinear` turns a scalar unit
`ψ : ℂ ≃+* End (𝟙_ C)` into ℂ-linear structures on `C` and on
`Ind C`.  This file joins the three.

* `RS.monoidalMap_unitConj` — a strong monoidal functor carries the
  left-unitor conjugate of a unit endomorphism to the left-unitor
  conjugate of its comparison transport;
* `RS.exactPairingMap` — a strong monoidal functor carries an exact
  pairing to an exact pairing, with the coevaluation `ε ≫ F h ≫ δ`
  and the evaluation `μ ≫ F ε_ ≫ η`; Mathlib has only the converse
  (`CategoryTheory.ExactPairing.ofFaithful`, which *reflects* a
  pairing along a faithful monoidal functor), so the two triangle
  identities are proved here from the oplax coherences;
* `RS.exactPairingIndOf` — **duals transport**: the embedding
  `C ⥤ Ind C` carries an exact pairing to an exact pairing;
* `RS.indOf_map_scalarSmul` and
  `RS.permAlg_indOf_conj_scalarUnit` — the embedding intertwines the
  scalar actions induced by `ψ` and by `RS.indScalarUnit ψ`, hence
  the whole group-algebra action;
* `RS.schurKilled_indOf` — **Schur vanishing transports**: for the
  ℂ-linear structures induced by a single scalar unit `ψ` on `C` and
  on `Ind C`, a shape kills an embedded object exactly when it kills
  the object downstairs.

Both linear structures are installed by `letI` inside the statements,
as in the acceptance section of `RS.Classical.Deligne.ScalarLinear`:
`RS.linearOfScalarUnit` is deliberately not an instance, and taking
*both* structures from the same `ψ` is what makes the two sides of
`RS.schurKilled_indOf` comparable — no compatibility hypothesis
between `ψ` and an ambient linear structure is needed.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u v' u'

noncomputable section

/-! ## Strong monoidal functors: unit conjugates and duals -/

section MonoidalFunctor

variable {A : Type u}

/-- **Transport of unit-endomorphism conjugates**: a strong monoidal
functor carries the left-unitor conjugate of a unit endomorphism `u`
to the left-unitor conjugate of the comparison transport of `u`. -/
theorem monoidalMap_unitConj
    [Category.{v} A] [MonoidalCategory A] {B : Type u'} [Category.{v'} B]
    [MonoidalCategory B] (F : A ⥤ B) [F.Monoidal]
    (X : A) (u : 𝟙_ A ⟶ 𝟙_ A) :
    F.map ((λ_ X).inv ≫ (u ▷ X) ≫ (λ_ X).hom) =
      (λ_ (F.obj X)).inv ≫
        ((Functor.LaxMonoidal.ε F ≫ F.map u ≫
          Functor.OplaxMonoidal.η F) ▷ F.obj X) ≫
        (λ_ (F.obj X)).hom := by
  rw [Functor.map_comp, Functor.map_comp,
    Functor.Monoidal.map_leftUnitor_inv,
    Functor.Monoidal.map_whiskerRight,
    Functor.Monoidal.map_leftUnitor]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc,
    Functor.Monoidal.μ_δ_assoc]

/-- **A strong monoidal functor carries an exact pairing to an exact
pairing**: the coevaluation is the unit comparison followed by the
image of the coevaluation and the cotensorator, the evaluation is the
tensorator followed by the image of the evaluation and the counit
comparison.  Both triangle identities descend from the corresponding
identities downstairs, whose image is expanded by the oplax
coherences of `CategoryTheory.Functor.Monoidal`. -/
@[implicit_reducible]
def exactPairingMap
    [Category.{v} A] [MonoidalCategory A] {B : Type u'} [Category.{v'} B]
    [MonoidalCategory B] (F : A ⥤ B) [F.Monoidal]
    {X Y : A} [ExactPairing X Y] :
    ExactPairing (F.obj X) (F.obj Y) where
  coevaluation' :=
    Functor.LaxMonoidal.ε F ≫ F.map (η_ X Y) ≫
      Functor.OplaxMonoidal.δ F X Y
  evaluation' :=
    Functor.LaxMonoidal.μ F Y X ≫ F.map (ε_ X Y) ≫
      Functor.OplaxMonoidal.η F
  evaluation_coevaluation' := by
    have h := congrArg F.map (ExactPairing.evaluation_coevaluation X Y)
    simp only [Functor.map_comp, Functor.Monoidal.map_whiskerRight,
      Functor.Monoidal.map_associator,
      Functor.Monoidal.map_whiskerLeft, Category.assoc,
      Functor.Monoidal.μ_δ_assoc, Functor.Monoidal.map_leftUnitor,
      Functor.Monoidal.map_rightUnitor_inv] at h
    have h' := Functor.LaxMonoidal.μ F (𝟙_ A) X ≫= h =≫
      Functor.OplaxMonoidal.δ F X (𝟙_ A)
    simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc,
      Functor.Monoidal.μ_δ, Category.comp_id] at h'
    simp only [MonoidalCategory.comp_whiskerRight,
      MonoidalCategory.whiskerLeft_comp, Category.assoc,
      reassoc_of% h', Functor.Monoidal.whiskerRight_ε_η_assoc,
      Functor.Monoidal.whiskerLeft_ε_η, Category.comp_id]
  coevaluation_evaluation' := by
    have h := congrArg F.map (ExactPairing.coevaluation_evaluation X Y)
    simp only [Functor.map_comp, Functor.Monoidal.map_whiskerRight,
      Functor.Monoidal.map_associator_inv,
      Functor.Monoidal.map_whiskerLeft, Category.assoc,
      Functor.Monoidal.μ_δ_assoc, Functor.Monoidal.map_rightUnitor,
      Functor.Monoidal.map_leftUnitor_inv] at h
    have h' := Functor.LaxMonoidal.μ F Y (𝟙_ A) ≫= h =≫
      Functor.OplaxMonoidal.δ F (𝟙_ A) Y
    simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc,
      Functor.Monoidal.μ_δ, Category.comp_id] at h'
    simp only [MonoidalCategory.comp_whiskerRight,
      MonoidalCategory.whiskerLeft_comp, Category.assoc,
      reassoc_of% h', Functor.Monoidal.whiskerLeft_ε_η_assoc,
      Functor.Monoidal.whiskerRight_ε_η, Category.comp_id]

end MonoidalFunctor

/-! ## Duals along the embedding -/

section Duals

variable {C : Type v}

/-- **Duals transport along the embedding `C ⥤ Ind C`**: the
embedding is strong monoidal (`RS.indOfMonoidal`), and a strong
monoidal functor preserves exact pairings. -/
instance exactPairingIndOf [SmallCategory C] [MonoidalCategory C]
    (X Y : C) [ExactPairing X Y] :
    ExactPairing ((indOf : C ⥤ Ind C).obj X)
      ((indOf : C ⥤ Ind C).obj Y) :=
  exactPairingMap indOf

end Duals

/-! ## The scalar action along the embedding -/

section Scalars

variable {C : Type v}

/-- The scalar unit of `Ind C` is the comparison transport of the
scalar unit of `C` along the strong monoidal embedding. -/
theorem scalarHom_indScalarUnit
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C]
    (ψ : ℂ ≃+* End (𝟙_ C)) (c : ℂ) :
    scalarHom (indScalarUnit ψ) c =
      Functor.LaxMonoidal.ε (indOf (C := C)) ≫ indOf.map (ψ c) ≫
        Functor.OplaxMonoidal.η (indOf (C := C)) := by
  rw [indOf_oplax_η]
  rfl

/-- **The embedding intertwines the scalar actions**: `indOf` carries
the action of `c` induced by `ψ` to the action of `c` induced by
`RS.indScalarUnit ψ`.  No compatibility with an ambient linear
structure is asked: both actions come from the same `ψ`. -/
theorem indOf_map_scalarSmul
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C]
    (ψ : ℂ ≃+* End (𝟙_ C)) (c : ℂ) {X Y : C}
    (f : X ⟶ Y) :
    indOf.map (scalarSmul ψ c f) =
      scalarSmul (indScalarUnit ψ) c (indOf.map f) := by
  have h : indOf.map ((λ_ X).inv ≫ (scalarHom ψ c ▷ X) ≫ (λ_ X).hom) =
      (λ_ (indOf.obj X)).inv ≫
        (scalarHom (indScalarUnit ψ) c ▷ indOf.obj X) ≫
        (λ_ (indOf.obj X)).hom := by
    rw [scalarHom_indScalarUnit]
    exact monoidalMap_unitConj indOf X (scalarHom ψ c)
  calc indOf.map (scalarSmul ψ c f)
      = indOf.map ((λ_ X).inv ≫ (scalarHom ψ c ▷ X) ≫ (λ_ X).hom) ≫
          indOf.map f := by
        rw [← Functor.map_comp]
        simp only [scalarSmul, Category.assoc]
    _ = scalarSmul (indScalarUnit ψ) c (indOf.map f) := by
        rw [h]
        simp only [scalarSmul, Category.assoc]

end Scalars

/-! ## The group-algebra action and Schur vanishing -/

section AlgebraTransport

variable {E : Type u}

/-- Intertwining a fixed morphism is closed under sums.  Stated at
general objects and applied by `exact`, so that the endomorphism-ring
structure never enters the rewriting. -/
private theorem sum_pass [Category.{v} E]
    [Preadditive E] {P Q : E} {a b : P ⟶ P}
    {a' b' : Q ⟶ Q} {T : P ⟶ Q} (ha : a ≫ T = T ≫ a')
    (hb : b ≫ T = T ≫ b') :
    (a + b) ≫ T = T ≫ (a' + b') := by
  rw [Preadditive.add_comp, Preadditive.comp_add, ha, hb]

/-- Intertwining a fixed morphism is closed under scalars. -/
private theorem scale_pass [Category.{v} E]
    [Preadditive E] [Linear ℂ E] {P Q : E}
    {a : P ⟶ P} {a' : Q ⟶ Q} {T : P ⟶ Q} (r : ℂ)
    (h : a ≫ T = T ≫ a') :
    (r • a) ≫ T = T ≫ (r • a') := by
  rw [Linear.smul_comp, Linear.comp_smul, h]

/-- **Transport of the group-algebra action**: for the ℂ-linear
structures induced on `C` and on `Ind C` by one scalar unit `ψ`, the
action of the symmetric-group algebra on the tensor powers of an
embedded object is conjugate, under `RS.indOfPowIso`, to the embedded
action. -/
theorem permAlg_indOf_conj_scalarUnit
    {C : Type v} [SmallCategory C] [MonoidalCategory C]
    [SymmetricCategory C] [Preadditive C] [HasFiniteColimits C]
    [MonoidalPreadditive C]
    (ψ : ℂ ≃+* End (𝟙_ C)) (X : C)
    {n : ℕ} (x : SymGroupAlgebra n) :
    letI := linearOfScalarUnit ψ
    letI := linearOfScalarUnit (indScalarUnit ψ)
    permAlg (indOf.obj X) n x ≫ (indOfPowIso X n).hom =
      (indOfPowIso X n).hom ≫ indOf.map (permAlg X n x) := by
  letI := linearOfScalarUnit ψ
  letI := linearOfScalarUnit (indScalarUnit ψ)
  haveI := indOf_additive (C := C)
  induction x using MonoidAlgebra.induction_on with
  | of σ =>
    rw [MonoidAlgebra.of_apply, permAlg_single, permAlg_single]
    exact indOfPowIso_permMor X n σ
  | add p q hp hq =>
    rw [map_add, map_add]
    exact (sum_pass hp hq).trans
      (congrArg (fun m => (indOfPowIso X n).hom ≫ m)
        (Functor.map_add (F := indOf (C := C))).symm)
  | smul c p hp =>
    rw [map_smul, map_smul]
    exact (scale_pass c hp).trans
      (congrArg (fun m => (indOfPowIso X n).hom ≫ m)
        (indOf_map_scalarSmul ψ c (permAlg X n p)).symm)

/-- **Schur vanishing transports along the embedding `C ⥤ Ind C`**:
with the ℂ-linear structures induced on `C` and on `Ind C` by one
scalar unit `ψ`, a shape kills an embedded object exactly when it
kills the object downstairs. -/
theorem schurKilled_indOf {C : Type v} [SmallCategory C] [MonoidalCategory C]
    [SymmetricCategory C] [Preadditive C] [HasFiniteColimits C]
    [MonoidalPreadditive C]
    (ψ : ℂ ≃+* End (𝟙_ C)) (P : SchurPackage.{v})
    (X : C) (μ : YoungDiagram) :
    letI := linearOfScalarUnit ψ
    letI := linearOfScalarUnit (indScalarUnit ψ)
    (SchurKilled P ((indOf : C ⥤ Ind C).obj X) μ ↔
      SchurKilled P X μ) := by
  letI := linearOfScalarUnit ψ
  letI := linearOfScalarUnit (indScalarUnit ψ)
  have hconj : permAlg (indOf.obj X) μ.card (P.e μ) =
      (indOfPowIso X μ.card).hom ≫
        indOf.map (permAlg X μ.card (P.e μ)) ≫
        (indOfPowIso X μ.card).inv := by
    rw [← reassoc_of% permAlg_indOf_conj_scalarUnit ψ X (P.e μ),
      Iso.hom_inv_id, Category.comp_id]
  have hdown : SchurKilled P X μ ↔
      permAlg X μ.card (P.e μ) =
        (0 : tensorPow C X μ.card ⟶ tensorPow C X μ.card) :=
    Iff.rfl
  constructor
  · intro h0
    have h0' : permAlg (indOf.obj X) μ.card (P.e μ) =
        (0 : tensorPow (Ind C) (indOf.obj X) μ.card ⟶
          tensorPow (Ind C) (indOf.obj X) μ.card) := h0
    rw [hconj] at h0'
    have h1 := (indOfPowIso X μ.card).inv ≫= h0' =≫
      (indOfPowIso X μ.card).hom
    have h2 : indOf.map (permAlg X μ.card (P.e μ)) = 0 := by
      simpa using h1
    exact hdown.mpr ((indOf_map_eq_zero_iff _).mp h2)
  · intro h0
    show permAlg (indOf.obj X) μ.card (P.e μ) = 0
    rw [hconj,
      (indOf_map_eq_zero_iff (permAlg X μ.card (P.e μ))).mpr
        (hdown.mp h0),
      Limits.zero_comp, Limits.comp_zero]

end AlgebraTransport

/-! ## Acceptance -/

section Acceptance

variable {C : Type v}

example
    [SmallCategory C] [MonoidalCategory C]
    (X Y : C) [ExactPairing X Y] :
    ExactPairing ((indOf : C ⥤ Ind C).obj X)
      ((indOf : C ⥤ Ind C).obj Y) :=
  inferInstance

example
    [SmallCategory C] [MonoidalCategory C]
    [RightRigidCategory C] (X : C) :
    ExactPairing ((indOf : C ⥤ Ind C).obj X)
      ((indOf : C ⥤ Ind C).obj (Xᘁ)) :=
  inferInstance

/- The embedded object of a right rigid category has a right dual in
`Ind C`, namely the embedded dual. -/
example
    [SmallCategory C] [MonoidalCategory C]
    [RightRigidCategory C] (X : C) :
    HasRightDual ((indOf : C ⥤ Ind C).obj X) where
  rightDual := (indOf : C ⥤ Ind C).obj (Xᘁ)

end Acceptance

end

end RS
