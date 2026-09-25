/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.TensorMuBraid

/-!
# The Λ coend of a pair of functors

Deligne 3.4's object `Λ(α, β)`: the coend over `X` of
`α(X)∨ ⊗ β(X)`, built here as the coend of the diagram
`(X, Y) ↦ α(Xᘁ) ⊗ β(Y)` using the *source* category's rigidity —
for tensor functors the two agree, and this form needs no duals in
the target.  This file provides the diagram, the coend with its
stage maps and dinaturality, the mapping property, and
functoriality in both arguments.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits Opposite

universe v u v' u'

variable {A : Type u}

/-- The Λ diagram of a pair of functors: `(X, Y) ↦ α(Xᘁ) ⊗ β(Y)`,
contravariant in `X` through the adjoint mate. -/
@[simps!]
def lambdaDiagram [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
    (α β : A ⥤ D) : Aᵒᵖ ⥤ A ⥤ D where
  obj X :=
    { obj := fun Y => α.obj ((unop X)ᘁ) ⊗ β.obj Y
      map := fun g => α.obj ((unop X)ᘁ) ◁ β.map g
      map_id := fun Y => by
        rw [β.map_id, MonoidalCategory.whiskerLeft_id]
      map_comp := fun g g' => by
        rw [β.map_comp, MonoidalCategory.whiskerLeft_comp] }
  map f :=
    { app := fun Y => α.map ((f.unop)ᘁ) ▷ β.obj Y
      naturality := fun Y Y' g => by
        dsimp
        exact whisker_exchange _ _ }
  map_id X := by
    ext Y
    simp
  map_comp f f' := by
    ext Y
    dsimp
    rw [comp_rightAdjointMate, α.map_comp, comp_whiskerRight]

section

/-- Existence of the Λ coend of the pair `(α, β)`. -/
abbrev HasLambda [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] (α : A ⥤ D)
    (β : A ⥤ D) : Prop := HasCoend (lambdaDiagram α β)

/-- The Λ object of a pair of functors: the coend of
`(X, Y) ↦ α(Xᘁ) ⊗ β(Y)`. -/
noncomputable def lambdaObj
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] (α : A ⥤ D)
    (β : A ⥤ D) [HasLambda α β] : D := coend (lambdaDiagram α β)

/-- The stage map of the Λ coend at an object of the source. -/
noncomputable def lambdaStage
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] (α : A ⥤ D)
    (β : A ⥤ D) [HasLambda α β]
    (X : A) :
    α.obj (Xᘁ) ⊗ β.obj X ⟶ lambdaObj α β :=
  coend.ι (lambdaDiagram α β) X

/-- Dinaturality of the stage maps. -/
@[reassoc]
theorem lambdaStage_condition
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] (α : A ⥤ D)
    (β : A ⥤ D) [HasLambda α β]
    {X Y : A} (f : X ⟶ Y) :
    (α.map (fᘁ) ▷ β.obj X) ≫ lambdaStage α β X =
      (α.obj (Yᘁ) ◁ β.map f) ≫ lambdaStage α β Y :=
  coend.condition (lambdaDiagram α β) f

/-- Maps out of the Λ object agree once they agree on stages. -/
theorem lambdaObj_hom_ext
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] (α : A ⥤ D)
    (β : A ⥤ D) [HasLambda α β]
    {W : D} {f g : lambdaObj α β ⟶ W}
    (h : ∀ X, lambdaStage α β X ≫ f = lambdaStage α β X ≫ g) :
    f = g :=
  coend.hom_ext h

/-- Descend a dinatural family of maps to the Λ object. -/
noncomputable def lambdaDesc
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] (α : A ⥤ D)
    (β : A ⥤ D) [HasLambda α β]
    {W : D}
    (f : ∀ X : A, α.obj (Xᘁ) ⊗ β.obj X ⟶ W)
    (hf : ∀ ⦃X Y : A⦄ (g : X ⟶ Y),
      (α.map (gᘁ) ▷ β.obj X) ≫ f X =
        (α.obj (Yᘁ) ◁ β.map g) ≫ f Y) :
    lambdaObj α β ⟶ W :=
  coend.desc f hf

@[reassoc (attr := simp)]
theorem lambdaStage_desc
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] (α : A ⥤ D)
    (β : A ⥤ D) [HasLambda α β]
    {W : D}
    (f : ∀ X : A, α.obj (Xᘁ) ⊗ β.obj X ⟶ W)
    (hf : ∀ ⦃X Y : A⦄ (g : X ⟶ Y),
      (α.map (gᘁ) ▷ β.obj X) ≫ f X =
        (α.obj (Yᘁ) ◁ β.map g) ≫ f Y) (X : A) :
    lambdaStage α β X ≫ lambdaDesc α β f hf = f X :=
  coend.ι_desc (F := lambdaDiagram α β) f hf X

end

section

/-- Natural transformations in both arguments induce a map of Λ
diagrams. -/
@[simps]
def lambdaDiagramMap
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {α : A ⥤ D}
    {α' : A ⥤ D} {β : A ⥤ D} {β' : A ⥤ D}
    (η : α ⟶ α') (τ : β ⟶ β') :
    lambdaDiagram α β ⟶ lambdaDiagram α' β' where
  app X :=
    { app := fun Y => η.app ((unop X)ᘁ) ⊗ₘ τ.app Y
      naturality := fun Y Y' g => by
        change α.obj ((unop X)ᘁ) ◁ β.map g ≫
            (η.app ((unop X)ᘁ) ⊗ₘ τ.app Y') =
          (η.app ((unop X)ᘁ) ⊗ₘ τ.app Y) ≫
            α'.obj ((unop X)ᘁ) ◁ β'.map g
        simp only [tensorHom_def]
        rw [whisker_exchange_assoc,
          ← MonoidalCategory.whiskerLeft_comp, Category.assoc,
          ← MonoidalCategory.whiskerLeft_comp, τ.naturality] }
  naturality f f' g := by
    ext Y
    change α.map ((g.unop)ᘁ) ▷ β.obj Y ≫
        (η.app ((unop f')ᘁ) ⊗ₘ τ.app Y) =
      (η.app ((unop f)ᘁ) ⊗ₘ τ.app Y) ≫
        α'.map ((g.unop)ᘁ) ▷ β'.obj Y
    simp only [tensorHom_def]
    rw [Category.assoc, whisker_exchange,
      ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc,
      η.naturality]

/-- Functoriality of the Λ object in both arguments. -/
noncomputable def lambdaMap
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {α : A ⥤ D}
    {α' : A ⥤ D} {β : A ⥤ D} {β' : A ⥤ D}
    [HasLambda α β] [HasLambda α' β']
    (η : α ⟶ α') (τ : β ⟶ β') :
    lambdaObj α β ⟶ lambdaObj α' β' :=
  coend.map (lambdaDiagramMap η τ)

@[reassoc (attr := simp)]
theorem lambdaStage_map
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {α : A ⥤ D}
    {α' : A ⥤ D} {β : A ⥤ D} {β' : A ⥤ D}
    [HasLambda α β] [HasLambda α' β']
    (η : α ⟶ α') (τ : β ⟶ β') (X : A) :
    lambdaStage α β X ≫ lambdaMap η τ =
      (η.app (Xᘁ) ⊗ₘ τ.app X) ≫ lambdaStage α' β' X :=
  coend.ι_map (lambdaDiagramMap η τ) X

@[simp]
theorem lambdaMap_id
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {α : A ⥤ D}
    {β : A ⥤ D}
    [HasLambda α β] :
    lambdaMap (𝟙 α) (𝟙 β) = 𝟙 (lambdaObj α β) := by
  refine lambdaObj_hom_ext α β fun X => ?_
  simp

@[reassoc]
theorem lambdaMap_comp
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {α : A ⥤ D}
    {α' : A ⥤ D} {α'' : A ⥤ D} {β : A ⥤ D} {β' : A ⥤ D} {β'' : A ⥤ D}
    [HasLambda α β] [HasLambda α' β']
    [HasLambda α'' β''] (η : α ⟶ α') (η' : α' ⟶ α'')
    (τ : β ⟶ β') (τ' : β' ⟶ β'') :
    lambdaMap η τ ≫ lambdaMap η' τ' =
      lambdaMap (η ≫ η') (τ ≫ τ') := by
  refine lambdaObj_hom_ext α β fun X => ?_
  simp

end

section Unit

open Functor.LaxMonoidal

/-- The right dual of the monoidal unit supplied by the rigid
structure — the instance the Λ stages use, which need not be the
unit-specific instance. -/
noncomputable def unitRigidDual
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A] : A :=
  @HasRightDual.rightDual A _ _ (𝟙_ A)
    (RightRigidCategory.rightDual (𝟙_ A))

/-- The rigid right dual of the monoidal unit is the unit, through
the canonical comparison of exact pairings. -/
noncomputable def unitRightDualIso
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A] :
    (unitRigidDual : A) ≅ 𝟙_ A :=
  rightDualIso
    (@HasRightDual.exact A _ _ (𝟙_ A)
      (RightRigidCategory.rightDual (𝟙_ A)))
    exactPairingUnit

/-- The unit of the Λ object of a pair of lax monoidal functors:
the units of the functors into the stage at the monoidal unit,
through the comparison of the unit with its rigid dual. -/
noncomputable def lambdaUnit
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] (α : A ⥤ D)
    (β : A ⥤ D) [α.LaxMonoidal] [β.LaxMonoidal]
    [HasLambda α β] :
    𝟙_ D ⟶ lambdaObj α β :=
  (λ_ (𝟙_ D)).inv ≫
    ((ε α ≫ α.map unitRightDualIso.inv) ⊗ₘ ε β) ≫
    lambdaStage α β (𝟙_ A)

end Unit

section TensorCoend

/-- Maps out of the image of a coend under a
colimit-preserving functor agree once they agree on the images
of the stages. -/
theorem coend_hom_ext_of_preserves
    {D : Type u'} [Category.{v'} D] {J : Type u} [Category.{v} J]
    {E : Type u'} [Category.{v'} E]
    (F : Jᵒᵖ ⥤ J ⥤ D) [HasCoend F] (G : D ⥤ E)
    [PreservesColimit (multispanIndexCoend F).multispan G]
    {Z : E} {f g : G.obj (coend F) ⟶ Z}
    (h : ∀ j, G.map (coend.ι F j) ≫ f =
      G.map (coend.ι F j) ≫ g) : f = g := by
  have hc := isColimitOfPreserves G
    (colimit.isColimit (multispanIndexCoend F).multispan)
  refine hc.hom_ext fun x => ?_
  match x with
  | .right j => exact h j
  | .left a =>
    have hw : (multispanIndexCoend F).multispan.map
          (Limits.WalkingMultispan.Hom.fst a) ≫
        colimit.ι (multispanIndexCoend F).multispan
          (.right ((multispanShapeCoend J).fst a)) =
      colimit.ι (multispanIndexCoend F).multispan (.left a) :=
      colimit.w _ _
    have hf := h ((multispanShapeCoend J).fst a)
    change G.map
        (colimit.ι (multispanIndexCoend F).multispan (.left a)) ≫
          f =
      G.map
        (colimit.ι (multispanIndexCoend F).multispan (.left a)) ≫
          g
    erw [← hw, Functor.map_comp, Category.assoc, Category.assoc]
    exact congrArg (fun t => G.map
      ((multispanIndexCoend F).multispan.map
        (Limits.WalkingMultispan.Hom.fst a)) ≫ t) hf

/-- Maps out of a tensor by a coend agree once they agree on
whiskered stages, provided tensoring preserves the coend's
colimit presentation.  The workhorse for descending
multiplications through `Λ ⊗ Λ`. -/
theorem tensorLeft_coend_hom_ext
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {J : Type u}
    [Category.{v} J]
    (F : Jᵒᵖ ⥤ J ⥤ D) [HasCoend F]
    (W : D) [PreservesColimit (multispanIndexCoend F).multispan
      (tensorLeft W)] {Z : D} {f g : W ⊗ coend F ⟶ Z}
    (h : ∀ j, (W ◁ coend.ι F j) ≫ f = (W ◁ coend.ι F j) ≫ g) :
    f = g := by
  have hc := isColimitOfPreserves (tensorLeft W)
    (colimit.isColimit (multispanIndexCoend F).multispan)
  refine hc.hom_ext fun x => ?_
  match x with
  | .right j => exact h j
  | .left a =>
    have hw : (multispanIndexCoend F).multispan.map
          (Limits.WalkingMultispan.Hom.fst a) ≫
        colimit.ι (multispanIndexCoend F).multispan
          (.right ((multispanShapeCoend J).fst a)) =
      colimit.ι (multispanIndexCoend F).multispan (.left a) :=
      colimit.w _ _
    have hf := h ((multispanShapeCoend J).fst a)
    change (tensorLeft W).map
        (colimit.ι (multispanIndexCoend F).multispan (.left a)) ≫
          f =
      (tensorLeft W).map
        (colimit.ι (multispanIndexCoend F).multispan (.left a)) ≫ g
    erw [← hw, Functor.map_comp, Category.assoc, Category.assoc]
    exact congrArg (fun t => (tensorLeft W).map
      ((multispanIndexCoend F).multispan.map
        (Limits.WalkingMultispan.Hom.fst a)) ≫ t) hf

/-- Right-hand mirror of `RS.tensorLeft_coend_hom_ext`. -/
theorem tensorRight_coend_hom_ext
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {J : Type u}
    [Category.{v} J]
    (F : Jᵒᵖ ⥤ J ⥤ D) [HasCoend F]
    (W : D) [PreservesColimit (multispanIndexCoend F).multispan
      (tensorRight W)] {Z : D} {f g : coend F ⊗ W ⟶ Z}
    (h : ∀ j, (coend.ι F j ▷ W) ≫ f = (coend.ι F j ▷ W) ≫ g) :
    f = g := by
  have hc := isColimitOfPreserves (tensorRight W)
    (colimit.isColimit (multispanIndexCoend F).multispan)
  refine hc.hom_ext fun x => ?_
  match x with
  | .right j => exact h j
  | .left a =>
    have hw : (multispanIndexCoend F).multispan.map
          (Limits.WalkingMultispan.Hom.fst a) ≫
        colimit.ι (multispanIndexCoend F).multispan
          (.right ((multispanShapeCoend J).fst a)) =
      colimit.ι (multispanIndexCoend F).multispan (.left a) :=
      colimit.w _ _
    have hf := h ((multispanShapeCoend J).fst a)
    change (tensorRight W).map
        (colimit.ι (multispanIndexCoend F).multispan (.left a)) ≫
          f =
      (tensorRight W).map
        (colimit.ι (multispanIndexCoend F).multispan (.left a)) ≫ g
    erw [← hw, Functor.map_comp, Category.assoc, Category.assoc]
    exact congrArg (fun t => (tensorRight W).map
      ((multispanIndexCoend F).multispan.map
        (Limits.WalkingMultispan.Hom.fst a)) ≫ t) hf

section

/-- The cocone under the whiskered multispan carried by a
dinatural family. -/
@[simps]
def tensorLeftCoendCocone
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {J : Type u}
    [Category.{v} J] (F : Jᵒᵖ ⥤ J ⥤ D) (W : D) {Z : D}
    (k : ∀ j : J, W ⊗ (F.obj (op j)).obj j ⟶ Z)
    (hk : ∀ ⦃i j : J⦄ (g : i ⟶ j), (W ◁ (F.map g.op).app i) ≫ k i = (W ◁
      (F.obj (op j)).map g) ≫ k j) :
    Cocone ((multispanIndexCoend F).multispan ⋙ tensorLeft W) where
  pt := Z
  ι :=
    { app := fun x =>
        match x with
        | .left a =>
            ((multispanIndexCoend F).multispan ⋙
                tensorLeft W).map
              (Limits.WalkingMultispan.Hom.fst a) ≫
              k ((multispanShapeCoend J).fst a)
        | .right j => k j
      naturality := fun x y φ => by
        match φ with
        | .id z =>
          obtain a | j := z
          · exact ((congrArg (fun t => t ≫
                (((multispanIndexCoend F).multispan ⋙
                    tensorLeft W).map
                  (Limits.WalkingMultispan.Hom.fst a) ≫
                  k ((multispanShapeCoend J).fst a)))
                (CategoryTheory.Functor.map_id _ _)).trans
              (Category.id_comp _)).trans
              (Category.comp_id _).symm
          · exact ((congrArg (fun t => t ≫ k j)
                (CategoryTheory.Functor.map_id _ _)).trans
              (Category.id_comp _)).trans
              (Category.comp_id _).symm
        | .fst a =>
          exact (Category.comp_id _).symm
        | .snd a =>
          exact ((hk (Arrow.hom a)).symm).trans
            (Category.comp_id _).symm }

/-- Descend a whiskered dinatural family through a tensor by a
coend. -/
noncomputable def tensorLeftCoendDesc
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {J : Type u}
    [Category.{v} J] (F : Jᵒᵖ ⥤ J ⥤ D) [HasCoend F] (W : D)
    [PreservesColimit (multispanIndexCoend F).multispan (tensorLeft W)]
    {Z : D} (k : ∀ j : J, W ⊗ (F.obj (op j)).obj j ⟶ Z)
    (hk : ∀ ⦃i j : J⦄ (g : i ⟶ j), (W ◁ (F.map g.op).app i) ≫ k i = (W ◁
      (F.obj (op j)).map g) ≫ k j) : W ⊗ coend F ⟶ Z :=
  (isColimitOfPreserves (tensorLeft W)
    (colimit.isColimit (multispanIndexCoend F).multispan)).desc
      (tensorLeftCoendCocone F W k hk)

@[reassoc (attr := simp)]
theorem whiskerLeft_ι_tensorLeftCoendDesc
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {J : Type u}
    [Category.{v} J] (F : Jᵒᵖ ⥤ J ⥤ D) [HasCoend F] (W : D)
    [PreservesColimit (multispanIndexCoend F).multispan (tensorLeft W)]
    {Z : D} (k : ∀ j : J, W ⊗ (F.obj (op j)).obj j ⟶ Z)
    (hk : ∀ ⦃i j : J⦄ (g : i ⟶ j), (W ◁ (F.map g.op).app i) ≫ k i = (W ◁
      (F.obj (op j)).map g) ≫ k j)
    (j : J) :
    (W ◁ coend.ι F j) ≫ tensorLeftCoendDesc F W k hk = k j :=
  (isColimitOfPreserves (tensorLeft W)
    (colimit.isColimit (multispanIndexCoend F).multispan)).fac
      (tensorLeftCoendCocone F W k hk) (.right j)

end

section

/-- The cocone under the right-whiskered multispan carried by a
dinatural family. -/
@[simps]
def tensorRightCoendCocone
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {J : Type u}
    [Category.{v} J] (F : Jᵒᵖ ⥤ J ⥤ D) (W : D) {Z : D}
    (k : ∀ j : J, (F.obj (op j)).obj j ⊗ W ⟶ Z)
    (hk : ∀ ⦃i j : J⦄ (g : i ⟶ j), ((F.map g.op).app i ▷ W) ≫ k i = ((F.obj
      (op j)).map g ▷ W) ≫ k j) :
    Cocone ((multispanIndexCoend F).multispan ⋙ tensorRight W)
    where
  pt := Z
  ι :=
    { app := fun x =>
        match x with
        | .left a =>
            ((multispanIndexCoend F).multispan ⋙
                tensorRight W).map
              (Limits.WalkingMultispan.Hom.fst a) ≫
              k ((multispanShapeCoend J).fst a)
        | .right j => k j
      naturality := fun x y φ => by
        match φ with
        | .id z =>
          obtain a | j := z
          · exact ((congrArg (fun t => t ≫
                (((multispanIndexCoend F).multispan ⋙
                    tensorRight W).map
                  (Limits.WalkingMultispan.Hom.fst a) ≫
                  k ((multispanShapeCoend J).fst a)))
                (CategoryTheory.Functor.map_id _ _)).trans
              (Category.id_comp _)).trans
              (Category.comp_id _).symm
          · exact ((congrArg (fun t => t ≫ k j)
                (CategoryTheory.Functor.map_id _ _)).trans
              (Category.id_comp _)).trans
              (Category.comp_id _).symm
        | .fst a =>
          exact (Category.comp_id _).symm
        | .snd a =>
          exact ((hk (Arrow.hom a)).symm).trans
            (Category.comp_id _).symm }

/-- Descend a right-whiskered dinatural family through a tensor by
a coend. -/
noncomputable def tensorRightCoendDesc
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {J : Type u}
    [Category.{v} J] (F : Jᵒᵖ ⥤ J ⥤ D) [HasCoend F] (W : D)
    [PreservesColimit (multispanIndexCoend F).multispan (tensorRight W)]
    {Z : D} (k : ∀ j : J, (F.obj (op j)).obj j ⊗ W ⟶ Z)
    (hk : ∀ ⦃i j : J⦄ (g : i ⟶ j), ((F.map g.op).app i ▷ W) ≫ k i = ((F.obj
      (op j)).map g ▷ W) ≫ k j) : coend F ⊗ W ⟶ Z :=
  (isColimitOfPreserves (tensorRight W)
    (colimit.isColimit (multispanIndexCoend F).multispan)).desc
      (tensorRightCoendCocone F W k hk)

@[reassoc (attr := simp)]
theorem ι_whiskerRight_tensorRightCoendDesc
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {J : Type u}
    [Category.{v} J] (F : Jᵒᵖ ⥤ J ⥤ D) [HasCoend F] (W : D)
    [PreservesColimit (multispanIndexCoend F).multispan (tensorRight W)]
    {Z : D} (k : ∀ j : J, (F.obj (op j)).obj j ⊗ W ⟶ Z)
    (hk : ∀ ⦃i j : J⦄ (g : i ⟶ j), ((F.map g.op).app i ▷ W) ≫ k i = ((F.obj
      (op j)).map g ▷ W) ≫ k j)
    (j : J) :
    (coend.ι F j ▷ W) ≫ tensorRightCoendDesc F W k hk = k j :=
  (isColimitOfPreserves (tensorRight W)
    (colimit.isColimit (multispanIndexCoend F).multispan)).fac
      (tensorRightCoendCocone F W k hk) (.right j)

end

end TensorCoend

section Multiplication

open Functor.LaxMonoidal

/-- The braid shuffle: the two ways of carrying the reversed pair
across a third object agree — the Yang–Baxter consequence behind
the associativity of the Λ multiplication. -/
theorem braid_shuffle [Category.{v} A] [MonoidalCategory A]
    {P Q R : A} [BraidedCategory A] :
    ((β_ P Q).hom ▷ R) ≫ (β_ (Q ⊗ P) R).hom ≫
        (α_ R Q P).inv =
      (α_ P Q R).hom ≫ (P ◁ (β_ Q R).hom) ≫
        (β_ P (R ⊗ Q)).hom := by
  rw [BraidedCategory.braiding_tensor_left_hom,
    BraidedCategory.braiding_tensor_right_hom]
  calc ((β_ P Q).hom ▷ R) ≫
      ((α_ Q P R).hom ≫ Q ◁ (β_ P R).hom ≫ (α_ Q R P).inv ≫
        (β_ Q R).hom ▷ P ≫ (α_ R Q P).hom) ≫ (α_ R Q P).inv
      = (α_ P Q R).hom ≫ ((α_ P Q R).inv ≫
          (β_ P Q).hom ▷ R ≫ (α_ Q P R).hom ≫
          Q ◁ (β_ P R).hom ≫ (α_ Q R P).inv ≫
          (β_ Q R).hom ▷ P ≫ (α_ R Q P).hom) ≫
          (α_ R Q P).inv := by
        monoidal
    _ = (α_ P Q R).hom ≫ (P ◁ (β_ Q R).hom ≫
          (α_ P R Q).inv ≫ (β_ P R).hom ▷ Q ≫
          (α_ R P Q).hom ≫ R ◁ (β_ P Q).hom) ≫
          (α_ R Q P).inv := by
        rw [BraidedCategory.yang_baxter]
    _ = (α_ P Q R).hom ≫ (P ◁ (β_ Q R).hom) ≫
        ((α_ P R Q).inv ≫ (β_ P R).hom ▷ Q ≫
          (α_ R P Q).hom ≫ R ◁ (β_ P Q).hom ≫
          (α_ R Q P).inv) := by
        monoidal

/-- Maps into a right dual agree once their evaluation composites
agree. -/
theorem eq_of_whiskerRight_comp_evaluation [Category.{v} A] [MonoidalCategory A]
    {P Q Z : A}
    [ExactPairing P Q] {h₁ h₂ : Z ⟶ Q}
    (H : (h₁ ▷ P) ≫ ε_ P Q = (h₂ ▷ P) ≫ ε_ P Q) : h₁ = h₂ := by
  apply_fun tensorRightHomEquiv Z P Q (𝟙_ A) at H
  have e₁ :=
    @tensorRightHomEquiv_whiskerRight_comp_evaluation A _ _ P Z
      ⟨Q⟩ h₁
  have e₂ :=
    @tensorRightHomEquiv_whiskerRight_comp_evaluation A _ _ P Z
      ⟨Q⟩ h₂
  have H' : h₁ ≫ (λ_ Q).inv = h₂ ≫ (λ_ Q).inv :=
    e₁.symm.trans (H.trans e₂)
  exact (cancel_mono _).1 H'

/-- The comparison of the dual of a product with the product of
the duals reduces the rigid evaluation to the tensor-pairing
evaluation. -/
theorem rightDualTensorIso_inv_comp_evaluation
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    (X Y : A) :
    ((rightDualTensorIso X Y).inv ▷ (X ⊗ Y)) ≫
      ε_ (X ⊗ Y) ((X ⊗ Y)ᘁ) =
        ε_ (X ⊗ Y) ((Yᘁ : A) ⊗ (Xᘁ : A)) := by
  have h := @rightAdjointMate_comp_evaluation A _ _ (X ⊗ Y)
    (X ⊗ Y) inferInstance ⟨(Yᘁ : A) ⊗ (Xᘁ : A)⟩ (𝟙 (X ⊗ Y))
  refine h.trans ?_
  rw [MonoidalCategory.whiskerLeft_id, Category.id_comp]
  rfl

/-- The mate of a left whiskering, through the comparison of the
dual of a tensor product with the tensor of the duals: the
dinaturality input of the Λ multiplication. -/
theorem whiskerLeft_mate_square
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    (X : A) {Y Y' : A} (g : Y ⟶ Y') :
    ((gᘁ) ▷ (Xᘁ : A)) ≫ (rightDualTensorIso X Y).inv =
      (rightDualTensorIso X Y').inv ≫ ((X ◁ g)ᘁ) := by
  refine eq_of_whiskerRight_comp_evaluation (P := X ⊗ Y) ?_
  rw [comp_whiskerRight, comp_whiskerRight, Category.assoc,
    Category.assoc, rightDualTensorIso_inv_comp_evaluation,
    rightAdjointMate_comp_evaluation,
    ← whisker_exchange_assoc,
    rightDualTensorIso_inv_comp_evaluation]
  calc ((gᘁ) ▷ (Xᘁ : A)) ▷ (X ⊗ Y) ≫
      ε_ (X ⊗ Y) ((Yᘁ : A) ⊗ (Xᘁ : A))
      = 𝟙 _ ⊗≫ ((gᘁ) ▷ ((Xᘁ : A) ⊗ X) ≫
          (Yᘁ : A) ◁ ε_ X (Xᘁ)) ▷ Y ⊗≫ ε_ Y (Yᘁ) := by
        rw [ExactPairing.tensor_evaluation]
        monoidal
    _ = 𝟙 _ ⊗≫ (((Y'ᘁ : A) ◁ ε_ X (Xᘁ)) ≫
          ((gᘁ) ▷ 𝟙_ A)) ▷ Y ⊗≫ ε_ Y (Yᘁ) := by
        rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ (Y'ᘁ : A) ◁ (ε_ X (Xᘁ) ▷ Y) ⊗≫
          ((gᘁ) ▷ Y ≫ ε_ Y (Yᘁ)) := by
        monoidal
    _ = 𝟙 _ ⊗≫ (Y'ᘁ : A) ◁ (ε_ X (Xᘁ) ▷ Y) ⊗≫
          ((Y'ᘁ : A) ◁ g ≫ ε_ Y' (Y'ᘁ)) := by
        rw [rightAdjointMate_comp_evaluation]
    _ = 𝟙 _ ⊗≫ (((Y'ᘁ : A) ◁ ε_ X (Xᘁ)) ▷ Y ≫
          ((Y'ᘁ : A) ⊗ 𝟙_ A) ◁ g) ⊗≫ ε_ Y' (Y'ᘁ) := by
        monoidal
    _ = 𝟙 _ ⊗≫ (((Y'ᘁ : A) ⊗ ((Xᘁ : A) ⊗ X)) ◁ g ≫
          ((Y'ᘁ : A) ◁ ε_ X (Xᘁ)) ▷ Y') ⊗≫ ε_ Y' (Y'ᘁ) := by
        rw [← whisker_exchange]
    _ = ((Y'ᘁ : A) ⊗ (Xᘁ : A)) ◁ (X ◁ g) ≫
          (𝟙 _ ⊗≫ (Y'ᘁ : A) ◁ (ε_ X (Xᘁ) ▷ Y') ⊗≫
            ε_ Y' (Y'ᘁ)) := by
        monoidal
    _ = ((Y'ᘁ : A) ⊗ (Xᘁ : A)) ◁ (X ◁ g) ≫
          ε_ (X ⊗ Y') ((Y'ᘁ : A) ⊗ (Xᘁ : A)) := by
        rw [ExactPairing.tensor_evaluation]

/-- The mate of a right whiskering: the left-slot mirror of
`RS.whiskerLeft_mate_square`. -/
theorem whiskerRight_mate_square
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {X X' : A} (f : X ⟶ X')
    (Y : A) :
    ((Yᘁ : A) ◁ (fᘁ)) ≫ (rightDualTensorIso X Y).inv =
      (rightDualTensorIso X' Y).inv ≫ ((f ▷ Y)ᘁ) := by
  refine eq_of_whiskerRight_comp_evaluation (P := X ⊗ Y) ?_
  rw [comp_whiskerRight, comp_whiskerRight, Category.assoc,
    Category.assoc, rightDualTensorIso_inv_comp_evaluation,
    rightAdjointMate_comp_evaluation,
    ← whisker_exchange_assoc,
    rightDualTensorIso_inv_comp_evaluation]
  calc ((Yᘁ : A) ◁ (fᘁ)) ▷ (X ⊗ Y) ≫
      ε_ (X ⊗ Y) ((Yᘁ : A) ⊗ (Xᘁ : A))
      = 𝟙 _ ⊗≫ (Yᘁ : A) ◁ (((fᘁ) ▷ X ≫ ε_ X (Xᘁ)) ▷ Y) ⊗≫
          ε_ Y (Yᘁ) := by
        rw [ExactPairing.tensor_evaluation]
        monoidal
    _ = 𝟙 _ ⊗≫ (Yᘁ : A) ◁ ((((X'ᘁ : A) ◁ f) ≫
          ε_ X' (X'ᘁ)) ▷ Y) ⊗≫ ε_ Y (Yᘁ) := by
        rw [rightAdjointMate_comp_evaluation]
    _ = ((Yᘁ : A) ⊗ (X'ᘁ : A)) ◁ (f ▷ Y) ≫
          ε_ (X' ⊗ Y) ((Yᘁ : A) ⊗ (X'ᘁ : A)) := by
        rw [ExactPairing.tensor_evaluation]
        monoidal

/-- The mate of the associator, through the comparisons of duals
of tensor products: the source-side kernel of the Λ
associativity. -/
theorem associator_mate_square
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    (X Y Z : A) :
    (α_ (Zᘁ : A) (Yᘁ : A) (Xᘁ : A)).hom ≫
        ((Zᘁ : A) ◁ (rightDualTensorIso X Y).inv) ≫
        (rightDualTensorIso (X ⊗ Y) Z).inv =
      ((rightDualTensorIso Y Z).inv ▷ (Xᘁ : A)) ≫
        (rightDualTensorIso X (Y ⊗ Z)).inv ≫
        (((α_ X Y Z).hom)ᘁ) := by
  refine eq_of_whiskerRight_comp_evaluation
    (P := (X ⊗ Y) ⊗ Z) ?_
  rw [comp_whiskerRight, comp_whiskerRight, comp_whiskerRight,
    comp_whiskerRight, Category.assoc, Category.assoc,
    Category.assoc, Category.assoc,
    rightDualTensorIso_inv_comp_evaluation,
    rightAdjointMate_comp_evaluation,
    ← whisker_exchange_assoc,
    rightDualTensorIso_inv_comp_evaluation]
  calc ((α_ (Zᘁ : A) (Yᘁ : A) (Xᘁ : A)).hom ▷
        ((X ⊗ Y) ⊗ Z)) ≫
      (((Zᘁ : A) ◁ (rightDualTensorIso X Y).inv) ▷
        ((X ⊗ Y) ⊗ Z)) ≫
      ε_ ((X ⊗ Y) ⊗ Z) ((Zᘁ : A) ⊗ ((X ⊗ Y)ᘁ : A))
      = ((α_ (Zᘁ : A) (Yᘁ : A) (Xᘁ : A)).hom ▷
          ((X ⊗ Y) ⊗ Z)) ≫
        (𝟙 _ ⊗≫ (Zᘁ : A) ◁
          ((((rightDualTensorIso X Y).inv ▷ (X ⊗ Y)) ≫
            ε_ (X ⊗ Y) ((X ⊗ Y)ᘁ)) ▷ Z) ⊗≫
          ε_ Z (Zᘁ)) := by
        rw [ExactPairing.tensor_evaluation]
        congr 1
        monoidal
    _ = ((α_ (Zᘁ : A) (Yᘁ : A) (Xᘁ : A)).hom ▷
          ((X ⊗ Y) ⊗ Z)) ≫
        (𝟙 _ ⊗≫ (Zᘁ : A) ◁
          ((𝟙 _ ⊗≫ (Yᘁ : A) ◁ (ε_ X (Xᘁ) ▷ Y) ⊗≫
            ε_ Y (Yᘁ)) ▷ Z) ⊗≫
          ε_ Z (Zᘁ)) := by
        rw [rightDualTensorIso_inv_comp_evaluation,
          ExactPairing.tensor_evaluation]
    _ = (((rightDualTensorIso Y Z).inv ▷ (Xᘁ : A)) ▷
          ((X ⊗ Y) ⊗ Z)) ≫
        ((((Y ⊗ Z)ᘁ : A) ⊗ (Xᘁ : A)) ◁ (α_ X Y Z).hom) ≫
        ε_ (X ⊗ (Y ⊗ Z)) (((Y ⊗ Z)ᘁ : A) ⊗ (Xᘁ : A)) := by
        symm
        calc (((rightDualTensorIso Y Z).inv ▷ (Xᘁ : A)) ▷
              ((X ⊗ Y) ⊗ Z)) ≫
            ((((Y ⊗ Z)ᘁ : A) ⊗ (Xᘁ : A)) ◁ (α_ X Y Z).hom) ≫
            ε_ (X ⊗ (Y ⊗ Z)) (((Y ⊗ Z)ᘁ : A) ⊗ (Xᘁ : A))
            = ((((Zᘁ : A) ⊗ (Yᘁ : A)) ⊗ (Xᘁ : A)) ◁
                (α_ X Y Z).hom) ≫
              (((rightDualTensorIso Y Z).inv ▷ (Xᘁ : A)) ▷
                (X ⊗ (Y ⊗ Z))) ≫
              ε_ (X ⊗ (Y ⊗ Z))
                (((Y ⊗ Z)ᘁ : A) ⊗ (Xᘁ : A)) := by
              rw [← whisker_exchange_assoc]
          _ = ((((Zᘁ : A) ⊗ (Yᘁ : A)) ⊗ (Xᘁ : A)) ◁
                (α_ X Y Z).hom) ≫
              (𝟙 _ ⊗≫
                (((rightDualTensorIso Y Z).inv ▷
                    (((Xᘁ : A) ⊗ X) ⊗ (Y ⊗ Z))) ≫
                  (((Y ⊗ Z)ᘁ : A) ◁
                    (ε_ X (Xᘁ) ▷ (Y ⊗ Z)))) ⊗≫
                ε_ (Y ⊗ Z) ((Y ⊗ Z)ᘁ)) := by
              rw [ExactPairing.tensor_evaluation]
              congr 1
              monoidal
          _ = ((((Zᘁ : A) ⊗ (Yᘁ : A)) ⊗ (Xᘁ : A)) ◁
                (α_ X Y Z).hom) ≫
              (𝟙 _ ⊗≫
                ((((Zᘁ : A) ⊗ (Yᘁ : A)) ◁
                    (ε_ X (Xᘁ) ▷ (Y ⊗ Z))) ≫
                  ((rightDualTensorIso Y Z).inv ▷
                    (𝟙_ A ⊗ (Y ⊗ Z)))) ⊗≫
                ε_ (Y ⊗ Z) ((Y ⊗ Z)ᘁ)) := by
              rw [← whisker_exchange]
          _ = ((((Zᘁ : A) ⊗ (Yᘁ : A)) ⊗ (Xᘁ : A)) ◁
                (α_ X Y Z).hom) ≫
              (𝟙 _ ⊗≫ ((Zᘁ : A) ⊗ (Yᘁ : A)) ◁
                (ε_ X (Xᘁ) ▷ (Y ⊗ Z)) ⊗≫
                (((rightDualTensorIso Y Z).inv ▷ (Y ⊗ Z)) ≫
                  ε_ (Y ⊗ Z) ((Y ⊗ Z)ᘁ))) := by
              congr 1
              monoidal
          _ = ((((Zᘁ : A) ⊗ (Yᘁ : A)) ⊗ (Xᘁ : A)) ◁
                (α_ X Y Z).hom) ≫
              (𝟙 _ ⊗≫ ((Zᘁ : A) ⊗ (Yᘁ : A)) ◁
                (ε_ X (Xᘁ) ▷ (Y ⊗ Z)) ⊗≫
                (𝟙 _ ⊗≫ (Zᘁ : A) ◁ (ε_ Y (Yᘁ) ▷ Z) ⊗≫
                  ε_ Z (Zᘁ))) := by
              rw [rightDualTensorIso_inv_comp_evaluation,
                ExactPairing.tensor_evaluation]
          _ = ((α_ (Zᘁ : A) (Yᘁ : A) (Xᘁ : A)).hom ▷
                ((X ⊗ Y) ⊗ Z)) ≫
              (𝟙 _ ⊗≫ (Zᘁ : A) ◁
                ((𝟙 _ ⊗≫ (Yᘁ : A) ◁ (ε_ X (Xᘁ) ▷ Y) ⊗≫
                  ε_ Y (Yᘁ)) ▷ Z) ⊗≫
                ε_ Z (Zᘁ)) := by
              monoidal

/-- Associativity of the composite dual comparisons: the full
source-side input of the Λ associativity, assembled from the
braid shuffle and the mate of the associator. -/
theorem cAssoc [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    [BraidedCategory A] (X Y Z : A) :
    (((β_ (Xᘁ : A) (Yᘁ : A)).hom ≫
        (rightDualTensorIso X Y).inv) ▷ (Zᘁ : A)) ≫
      (β_ ((X ⊗ Y)ᘁ : A) (Zᘁ : A)).hom ≫
      (rightDualTensorIso (X ⊗ Y) Z).inv =
    (α_ (Xᘁ : A) (Yᘁ : A) (Zᘁ : A)).hom ≫
      ((Xᘁ : A) ◁ ((β_ (Yᘁ : A) (Zᘁ : A)).hom ≫
        (rightDualTensorIso Y Z).inv)) ≫
      (β_ (Xᘁ : A) ((Y ⊗ Z)ᘁ : A)).hom ≫
      (rightDualTensorIso X (Y ⊗ Z)).inv ≫
      (((α_ X Y Z).hom)ᘁ) := by
  have hsq : ((Zᘁ : A) ◁ (rightDualTensorIso X Y).inv) ≫
      (rightDualTensorIso (X ⊗ Y) Z).inv =
        (α_ (Zᘁ : A) (Yᘁ : A) (Xᘁ : A)).inv ≫
          ((rightDualTensorIso Y Z).inv ▷ (Xᘁ : A)) ≫
          (rightDualTensorIso X (Y ⊗ Z)).inv ≫
          (((α_ X Y Z).hom)ᘁ) := by
    rw [← associator_mate_square, Iso.inv_hom_id_assoc]
  rw [comp_whiskerRight, Category.assoc,
    BraidedCategory.braiding_naturality_left_assoc, hsq,
    reassoc_of% braid_shuffle,
    ← BraidedCategory.braiding_naturality_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc]

/-- The mate of the braiding through the dual-tensor
comparisons: the source-side kernel of the Λ commutativity. -/
theorem braiding_mate_square
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    [SymmetricCategory A] (X Y : A) :
    (rightDualTensorIso Y X).inv ≫ (((β_ X Y).hom)ᘁ) =
      (β_ (Xᘁ : A) (Yᘁ : A)).hom ≫
        (rightDualTensorIso X Y).inv := by
  refine eq_of_whiskerRight_comp_evaluation (P := X ⊗ Y) ?_
  rw [comp_whiskerRight, comp_whiskerRight, Category.assoc,
    Category.assoc, rightAdjointMate_comp_evaluation,
    ← whisker_exchange_assoc,
    rightDualTensorIso_inv_comp_evaluation,
    rightDualTensorIso_inv_comp_evaluation,
    tensor_evaluation_braiding X Y (Xᘁ : A) (Yᘁ : A),
    whisker_exchange_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    SymmetricCategory.symmetry, MonoidalCategory.whiskerLeft_id,
    Category.id_comp]

/-- The tensor dual comparison at the monoidal unit, pinned to
the rigid blanket instances that the Λ stages use. -/
noncomputable def unitTensorDualIso
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    (Y : A) :
    ((𝟙_ A ⊗ Y)ᘁ : A) ≅ (Yᘁ : A) ⊗ unitRigidDual :=
  @rightDualTensorIso A _ _ (𝟙_ A) Y
    (RightRigidCategory.rightDual (𝟙_ A))
    (RightRigidCategory.rightDual Y)
    (RightRigidCategory.rightDual (𝟙_ A ⊗ Y))

/-- The rigid evaluation of the monoidal unit, at the blanket
instance. -/
noncomputable def unitRigidEvaluation
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A] :
    (unitRigidDual (A := A)) ⊗ 𝟙_ A ⟶ 𝟙_ A :=
  @ExactPairing.evaluation A _ _ (𝟙_ A) (unitRigidDual (A := A))
    (@HasRightDual.exact A _ _ (𝟙_ A)
      (RightRigidCategory.rightDual (𝟙_ A)))

/-- The unit comparison reduces the blanket evaluation of the
unit to the unit pairing. -/
theorem unitRightDualIso_inv_comp_evaluation
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A] :
    ((unitRightDualIso (A := A)).inv ▷ (𝟙_ A)) ≫
      unitRigidEvaluation (A := A) = ε_ (𝟙_ A) (𝟙_ A) := by
  have h := @rightAdjointMate_comp_evaluation A _ _ (𝟙_ A)
    (𝟙_ A) (RightRigidCategory.rightDual (𝟙_ A)) ⟨𝟙_ A⟩
    (𝟙 (𝟙_ A))
  refine h.trans ?_
  rw [MonoidalCategory.whiskerLeft_id, Category.id_comp]
  rfl

/-- The pinned tensor dual comparison at the unit reduces the
rigid evaluation to the expanded tensor evaluation. -/
theorem unitTensorDualIso_inv_comp_evaluation
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    (Y : A) :
    ((unitTensorDualIso Y).inv ▷ (𝟙_ A ⊗ Y)) ≫
      ε_ (𝟙_ A ⊗ Y) ((𝟙_ A ⊗ Y)ᘁ) =
        𝟙 _ ⊗≫ (Yᘁ : A) ◁
          (unitRigidEvaluation (A := A) ▷ Y) ⊗≫
          ε_ Y (Yᘁ) := by
  let pt : ExactPairing (𝟙_ A ⊗ Y)
      ((Yᘁ : A) ⊗ unitRigidDual) :=
    @ExactPairing.tensor A _ _ (𝟙_ A) Y (unitRigidDual (A := A))
      (Yᘁ) (@HasRightDual.exact A _ _ (𝟙_ A)
        (RightRigidCategory.rightDual (𝟙_ A))) inferInstance
  have h := @rightAdjointMate_comp_evaluation A _ _ (𝟙_ A ⊗ Y)
    (𝟙_ A ⊗ Y) inferInstance
    ⟨(Yᘁ : A) ⊗ unitRigidDual⟩ (𝟙 (𝟙_ A ⊗ Y))
  refine h.trans ?_
  rw [MonoidalCategory.whiskerLeft_id, Category.id_comp]
  rfl

/-- The tensor dual comparison with the unit on the right, pinned
to the rigid blanket instances. -/
noncomputable def tensorUnitDualIso
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    (Y : A) :
    ((Y ⊗ 𝟙_ A)ᘁ : A) ≅ unitRigidDual ⊗ (Yᘁ : A) :=
  @rightDualTensorIso A _ _ Y (𝟙_ A)
    (RightRigidCategory.rightDual Y)
    (RightRigidCategory.rightDual (𝟙_ A))
    (RightRigidCategory.rightDual (Y ⊗ 𝟙_ A))

/-- The pinned tensor dual comparison with the unit on the right
reduces the rigid evaluation to the expanded tensor
evaluation. -/
theorem tensorUnitDualIso_inv_comp_evaluation
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    (Y : A) :
    ((tensorUnitDualIso Y).inv ▷ (Y ⊗ 𝟙_ A)) ≫
      ε_ (Y ⊗ 𝟙_ A) ((Y ⊗ 𝟙_ A)ᘁ) =
        𝟙 _ ⊗≫ (unitRigidDual (A := A)) ◁
          (ε_ Y (Yᘁ) ▷ (𝟙_ A)) ⊗≫
          unitRigidEvaluation (A := A) := by
  let pt : ExactPairing (Y ⊗ 𝟙_ A)
      ((unitRigidDual (A := A)) ⊗ (Yᘁ : A)) :=
    @ExactPairing.tensor A _ _ Y (𝟙_ A) (Yᘁ)
      (unitRigidDual (A := A)) inferInstance
      (@HasRightDual.exact A _ _ (𝟙_ A)
        (RightRigidCategory.rightDual (𝟙_ A)))
  have h := @rightAdjointMate_comp_evaluation A _ _ (Y ⊗ 𝟙_ A)
    (Y ⊗ 𝟙_ A) inferInstance
    ⟨(unitRigidDual (A := A)) ⊗ (Yᘁ : A)⟩ (𝟙 (Y ⊗ 𝟙_ A))
  refine h.trans ?_
  rw [MonoidalCategory.whiskerLeft_id, Category.id_comp]
  rfl

/-- The mate of the right unitor: the mirror of
`RS.leftUnitor_mate`. -/
theorem rightUnitor_mate
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    [BraidedCategory A]
    (Y : A) :
    (ρ_ (Yᘁ : A)).inv ≫
        ((Yᘁ : A) ◁ (unitRightDualIso (A := A)).inv) ≫
        (β_ (Yᘁ : A) (unitRigidDual (A := A))).hom ≫
        (tensorUnitDualIso Y).inv =
      (((ρ_ Y).hom)ᘁ) := by
  have hβ2 : (β_ (Yᘁ : A) (𝟙_ A)).hom =
      (ρ_ (Yᘁ : A)).hom ≫ (λ_ (Yᘁ : A)).inv :=
    (Iso.eq_comp_inv _).mpr (braiding_leftUnitor _)
  have hε : ε_ (𝟙_ A) (𝟙_ A) = (ρ_ (𝟙_ A)).hom := rfl
  refine eq_of_whiskerRight_comp_evaluation
    (P := Y ⊗ 𝟙_ A) ?_
  rw [rightAdjointMate_comp_evaluation, comp_whiskerRight,
    comp_whiskerRight, comp_whiskerRight, Category.assoc,
    Category.assoc, Category.assoc,
    tensorUnitDualIso_inv_comp_evaluation]
  calc ((ρ_ (Yᘁ : A)).inv ▷ (Y ⊗ 𝟙_ A)) ≫
      (((Yᘁ : A) ◁ (unitRightDualIso (A := A)).inv) ▷
        (Y ⊗ 𝟙_ A)) ≫
      ((β_ (Yᘁ : A) (unitRigidDual (A := A))).hom ▷
        (Y ⊗ 𝟙_ A)) ≫
      (𝟙 _ ⊗≫ (unitRigidDual (A := A)) ◁
        (ε_ Y (Yᘁ) ▷ (𝟙_ A)) ⊗≫
        unitRigidEvaluation (A := A))
      = ((ρ_ (Yᘁ : A)).inv ▷ (Y ⊗ 𝟙_ A)) ≫
        (((β_ (Yᘁ : A) (𝟙_ A)).hom ≫
          ((unitRightDualIso (A := A)).inv ▷ (Yᘁ : A))) ▷
            (Y ⊗ 𝟙_ A)) ≫
        (𝟙 _ ⊗≫ (unitRigidDual (A := A)) ◁
          (ε_ Y (Yᘁ) ▷ (𝟙_ A)) ⊗≫
          unitRigidEvaluation (A := A)) := by
        rw [← comp_whiskerRight_assoc
            ((Yᘁ : A) ◁ (unitRightDualIso (A := A)).inv)
            (β_ (Yᘁ : A) (unitRigidDual (A := A))).hom,
          BraidedCategory.braiding_naturality_right,
          comp_whiskerRight_assoc]
    _ = ((ρ_ (Yᘁ : A)).inv ▷ (Y ⊗ 𝟙_ A)) ≫
        ((β_ (Yᘁ : A) (𝟙_ A)).hom ▷ (Y ⊗ 𝟙_ A)) ≫
        (𝟙 _ ⊗≫
          (((unitRightDualIso (A := A)).inv ▷
              (((Yᘁ : A) ⊗ Y) ⊗ 𝟙_ A)) ≫
            ((unitRigidDual (A := A)) ◁
              (ε_ Y (Yᘁ) ▷ (𝟙_ A)))) ⊗≫
          unitRigidEvaluation (A := A)) := by
        rw [comp_whiskerRight_assoc]
        congr 2
        monoidal
    _ = ((ρ_ (Yᘁ : A)).inv ▷ (Y ⊗ 𝟙_ A)) ≫
        ((β_ (Yᘁ : A) (𝟙_ A)).hom ▷ (Y ⊗ 𝟙_ A)) ≫
        (𝟙 _ ⊗≫
          (((𝟙_ A) ◁ (ε_ Y (Yᘁ) ▷ (𝟙_ A))) ≫
            ((unitRightDualIso (A := A)).inv ▷
              ((𝟙_ A) ⊗ (𝟙_ A)))) ⊗≫
          unitRigidEvaluation (A := A)) := by
        rw [← whisker_exchange]
    _ = ((ρ_ (Yᘁ : A)).inv ▷ (Y ⊗ 𝟙_ A)) ≫
        ((β_ (Yᘁ : A) (𝟙_ A)).hom ▷ (Y ⊗ 𝟙_ A)) ≫
        (𝟙 _ ⊗≫ (𝟙_ A) ◁ (ε_ Y (Yᘁ) ▷ (𝟙_ A)) ⊗≫
          (((unitRightDualIso (A := A)).inv ▷ (𝟙_ A)) ≫
            unitRigidEvaluation (A := A))) := by
        congr 2
        monoidal
    _ = ((ρ_ (Yᘁ : A)).inv ▷ (Y ⊗ 𝟙_ A)) ≫
        (((ρ_ (Yᘁ : A)).hom ≫ (λ_ (Yᘁ : A)).inv) ▷
          (Y ⊗ 𝟙_ A)) ≫
        (𝟙 _ ⊗≫ (𝟙_ A) ◁ (ε_ Y (Yᘁ) ▷ (𝟙_ A)) ⊗≫
          (ρ_ (𝟙_ A)).hom) := by
        rw [unitRightDualIso_inv_comp_evaluation, hε, hβ2]
    _ = ((Yᘁ : A) ◁ (ρ_ Y).hom) ≫ ε_ Y (Yᘁ) := by
        monoidal

/-- The mate of the left unitor, expressed through the unit and
tensor dual comparisons: the source-side input of the Λ unit
law. -/
theorem leftUnitor_mate
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    [BraidedCategory A]
    (Y : A) :
    (λ_ (Yᘁ : A)).inv ≫
        ((unitRightDualIso (A := A)).inv ▷ (Yᘁ : A)) ≫
        (β_ (unitRigidDual (A := A)) (Yᘁ : A)).hom ≫
        (unitTensorDualIso Y).inv =
      (((λ_ Y).hom)ᘁ) := by
  have hβ1 : (β_ (𝟙_ A) (Yᘁ : A)).hom =
      (λ_ (Yᘁ : A)).hom ≫ (ρ_ (Yᘁ : A)).inv :=
    (Iso.eq_comp_inv _).mpr (braiding_rightUnitor _)
  have hε : ε_ (𝟙_ A) (𝟙_ A) = (ρ_ (𝟙_ A)).hom := rfl
  refine eq_of_whiskerRight_comp_evaluation
    (P := 𝟙_ A ⊗ Y) ?_
  rw [rightAdjointMate_comp_evaluation, comp_whiskerRight,
    comp_whiskerRight, comp_whiskerRight, Category.assoc,
    Category.assoc, Category.assoc,
    unitTensorDualIso_inv_comp_evaluation]
  calc ((λ_ (Yᘁ : A)).inv ▷ (𝟙_ A ⊗ Y)) ≫
      (((unitRightDualIso (A := A)).inv ▷ (Yᘁ : A)) ▷
        (𝟙_ A ⊗ Y)) ≫
      ((β_ (unitRigidDual (A := A)) (Yᘁ : A)).hom ▷
        (𝟙_ A ⊗ Y)) ≫
      (𝟙 _ ⊗≫ (Yᘁ : A) ◁
        (unitRigidEvaluation (A := A) ▷ Y) ⊗≫
        ε_ Y (Yᘁ))
      = ((λ_ (Yᘁ : A)).inv ▷ (𝟙_ A ⊗ Y)) ≫
        (((β_ (𝟙_ A) (Yᘁ : A)).hom ≫
          ((Yᘁ : A) ◁ (unitRightDualIso (A := A)).inv)) ▷
            (𝟙_ A ⊗ Y)) ≫
        (𝟙 _ ⊗≫ (Yᘁ : A) ◁
          (unitRigidEvaluation (A := A) ▷ Y) ⊗≫
          ε_ Y (Yᘁ)) := by
        rw [← comp_whiskerRight_assoc
            ((unitRightDualIso (A := A)).inv ▷ (Yᘁ : A))
            (β_ (unitRigidDual (A := A)) (Yᘁ : A)).hom,
          BraidedCategory.braiding_naturality_left,
          comp_whiskerRight_assoc]
    _ = ((λ_ (Yᘁ : A)).inv ▷ (𝟙_ A ⊗ Y)) ≫
        ((β_ (𝟙_ A) (Yᘁ : A)).hom ▷ (𝟙_ A ⊗ Y)) ≫
        (𝟙 _ ⊗≫ (Yᘁ : A) ◁
          ((((unitRightDualIso (A := A)).inv ▷ (𝟙_ A)) ≫
            unitRigidEvaluation (A := A)) ▷ Y) ⊗≫
          ε_ Y (Yᘁ)) := by
        rw [comp_whiskerRight_assoc]
        congr 2
        monoidal
    _ = ((λ_ (Yᘁ : A)).inv ▷ (𝟙_ A ⊗ Y)) ≫
        (((λ_ (Yᘁ : A)).hom ≫ (ρ_ (Yᘁ : A)).inv) ▷
          (𝟙_ A ⊗ Y)) ≫
        (𝟙 _ ⊗≫ (Yᘁ : A) ◁ ((ρ_ (𝟙_ A)).hom ▷ Y) ⊗≫
          ε_ Y (Yᘁ)) := by
        rw [unitRightDualIso_inv_comp_evaluation, hε, hβ1]
    _ = ((Yᘁ : A) ◁ (λ_ Y).hom) ≫ ε_ Y (Yᘁ) := by
        monoidal

/-- The stage-level multiplication of the Λ object: middle-four
exchange, the tensorators of the two functors, and the comparison
of the dual of a product with the product of the duals. -/
noncomputable def lambdaMulStage
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory A]
    [BraidedCategory D] (α : A ⥤ D) (β : A ⥤ D) [α.LaxMonoidal]
    [β.LaxMonoidal]
    (X Y : A) :
    (α.obj (Xᘁ) ⊗ β.obj X) ⊗ (α.obj (Yᘁ) ⊗ β.obj Y) ⟶
      α.obj ((X ⊗ Y)ᘁ) ⊗ β.obj (X ⊗ Y) :=
  tensorμ (α.obj (Xᘁ)) (β.obj X) (α.obj (Yᘁ)) (β.obj Y) ≫
    (μ α (Xᘁ) (Yᘁ) ⊗ₘ μ β X Y) ≫
    (α.map ((β_ (Xᘁ : A) (Yᘁ : A)).hom ≫
      (rightDualTensorIso X Y).inv) ▷ β.obj (X ⊗ Y))

/-- The stage-level associativity of the Λ multiplication. -/
theorem lambdaMulStage_assoc
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory A]
    [BraidedCategory D] (α : A ⥤ D) (β : A ⥤ D) [α.LaxMonoidal]
    [β.LaxMonoidal]
    [HasLambda α β] (X Y Z : A) :
    (lambdaMulStage α β X Y ▷ (α.obj (Zᘁ) ⊗ β.obj Z)) ≫
      lambdaMulStage α β (X ⊗ Y) Z ≫
      lambdaStage α β ((X ⊗ Y) ⊗ Z) =
    (α_ (α.obj (Xᘁ) ⊗ β.obj X) (α.obj (Yᘁ) ⊗ β.obj Y)
        (α.obj (Zᘁ) ⊗ β.obj Z)).hom ≫
      ((α.obj (Xᘁ) ⊗ β.obj X) ◁ lambdaMulStage α β Y Z) ≫
      lambdaMulStage α β X (Y ⊗ Z) ≫
      lambdaStage α β (X ⊗ (Y ⊗ Z)) := by
  rw [lambdaMulStage, lambdaMulStage, lambdaMulStage,
    lambdaMulStage]
  simp only [Category.assoc]
  conv_lhs =>
    rw [comp_whiskerRight, comp_whiskerRight,
      ← MonoidalCategory.tensorHom_id
        (α.map ((β_ (Xᘁ : A) (Yᘁ : A)).hom ≫
          (rightDualTensorIso X Y).inv)) (β.obj (X ⊗ Y))]
    rw [Category.assoc, Category.assoc,
      tensorμ_natural_left_assoc, tensorμ_natural_left_assoc,
      tensorHom_comp_tensorHom_assoc,
      tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_left,
    MonoidalCategory.id_whiskerRight, Category.id_comp,
    reassoc_of% Functor.LaxMonoidal.μ_whiskerRight_comp_μ α
      (Xᘁ) (Yᘁ) (Zᘁ),
    Functor.LaxMonoidal.μ_whiskerRight_comp_μ β X Y Z,
    ← MonoidalCategory.tensorHom_id
      (α.map ((β_ ((X ⊗ Y)ᘁ : A) (Zᘁ : A)).hom ≫
        (rightDualTensorIso (X ⊗ Y) Z).inv))
      (β.obj ((X ⊗ Y) ⊗ Z)),
    tensorHom_comp_tensorHom_assoc, Category.comp_id]
  simp only [← Functor.map_comp, Category.assoc]
  have hA : (α_ (Xᘁ : A) (Yᘁ : A) (Zᘁ : A)).inv ≫
      (((β_ (Xᘁ : A) (Yᘁ : A)).hom ≫
        (rightDualTensorIso X Y).inv) ▷ (Zᘁ : A)) ≫
      (β_ ((X ⊗ Y)ᘁ : A) (Zᘁ : A)).hom ≫
      (rightDualTensorIso (X ⊗ Y) Z).inv =
    (((Xᘁ : A) ◁ ((β_ (Yᘁ : A) (Zᘁ : A)).hom ≫
      (rightDualTensorIso Y Z).inv)) ≫
      ((β_ (Xᘁ : A) ((Y ⊗ Z)ᘁ : A)).hom ≫
        (rightDualTensorIso X (Y ⊗ Z)).inv)) ≫
      (((α_ X Y Z).hom)ᘁ) := by
    rw [cAssoc, Iso.inv_hom_id_assoc]
    simp only [Category.assoc]
  have hstage : (α.map (((α_ X Y Z).hom)ᘁ) ⊗ₘ
      β.map ((α_ X Y Z).inv)) ≫
        lambdaStage α β ((X ⊗ Y) ⊗ Z) =
      lambdaStage α β (X ⊗ (Y ⊗ Z)) := by
    rw [tensorHom_def'_assoc, lambdaStage_condition,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp]
  rw [hA, Functor.map_comp (g := (((α_ X Y Z).hom)ᘁ)),
    ← tensorHom_comp_tensorHom_assoc,
    ← Category.id_comp (β.map ((α_ X Y Z).inv)),
    ← tensorHom_comp_tensorHom_assoc,
    ← tensorHom_comp_tensorHom_assoc,
    ← tensorHom_comp_tensorHom_assoc]
  rw [hstage, MonoidalCategory.tensorHom_id,
    reassoc_of% tensor_associativity (α.obj (Xᘁ)) (β.obj X)
      (α.obj (Yᘁ)) (β.obj Y) (α.obj (Zᘁ)) (β.obj Z)]
  rw [MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [← MonoidalCategory.tensorHom_id
      (α.map ((β_ (Yᘁ : A) (Zᘁ : A)).hom ≫
        (rightDualTensorIso Y Z).inv)) (β.obj (Y ⊗ Z)),
    MonoidalCategory.whiskerLeft_comp,
    Category.assoc, tensorμ_natural_right_assoc,
    tensorμ_natural_right_assoc,
    tensorHom_comp_tensorHom_assoc,
    tensorHom_comp_tensorHom_assoc,
    tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_right,
    MonoidalCategory.whiskerLeft_id, Category.id_comp,
    ← Category.comp_id (Functor.LaxMonoidal.μ β X (Y ⊗ Z)),
    ← tensorHom_comp_tensorHom_assoc,
    ← tensorHom_comp_tensorHom_assoc,
    ← tensorHom_comp_tensorHom_assoc,
    MonoidalCategory.tensorHom_id, Category.comp_id,
    ← comp_whiskerRight_assoc, ← Functor.map_comp]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]

/-- Dinaturality of the stage-level multiplication in the right
variable: the input of the inner coend descent of the Λ
multiplication. -/
theorem lambdaMulStage_dinat_right
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory A]
    [BraidedCategory D] (α : A ⥤ D) (β : A ⥤ D) [α.LaxMonoidal]
    [β.LaxMonoidal]
    [HasLambda α β] (X : A)
    {Y Y' : A} (g : Y ⟶ Y') :
    ((α.obj (Xᘁ) ⊗ β.obj X) ◁ (α.map (gᘁ) ▷ β.obj Y)) ≫
        lambdaMulStage α β X Y ≫ lambdaStage α β (X ⊗ Y) =
      ((α.obj (Xᘁ) ⊗ β.obj X) ◁ (α.obj (Y'ᘁ) ◁ β.map g)) ≫
        lambdaMulStage α β X Y' ≫ lambdaStage α β (X ⊗ Y') := by
  have hc : (Xᘁ : A) ◁ (gᘁ) ≫ (β_ (Xᘁ : A) (Yᘁ : A)).hom ≫
      (rightDualTensorIso X Y).inv =
        ((β_ (Xᘁ : A) (Y'ᘁ : A)).hom ≫
          (rightDualTensorIso X Y').inv) ≫ ((X ◁ g)ᘁ) := by
    rw [BraidedCategory.braiding_naturality_right_assoc,
      whiskerLeft_mate_square, Category.assoc]
  rw [lambdaMulStage, lambdaMulStage]
  simp only [Category.assoc]
  conv_lhs =>
    rw [← MonoidalCategory.tensorHom_id (α.map (gᘁ)) (β.obj Y),
      tensorμ_natural_right_assoc,
      tensorHom_comp_tensorHom_assoc,
      Functor.LaxMonoidal.μ_natural_right,
      MonoidalCategory.whiskerLeft_id, Category.id_comp,
      ← Category.comp_id (Functor.LaxMonoidal.μ β X Y),
      ← tensorHom_comp_tensorHom_assoc,
      MonoidalCategory.tensorHom_id,
      ← comp_whiskerRight_assoc,
      ← Functor.map_comp, hc,
      Functor.map_comp, comp_whiskerRight_assoc,
      lambdaStage_condition,
      ← whisker_exchange_assoc,
      ← MonoidalCategory.id_tensorHom,
      tensorHom_comp_tensorHom_assoc, Category.comp_id,
      ← Functor.LaxMonoidal.μ_natural_right,
      ← Category.id_comp (Functor.LaxMonoidal.μ α (Xᘁ) (Y'ᘁ)),
      ← tensorHom_comp_tensorHom_assoc]
  conv_rhs =>
    rw [← MonoidalCategory.id_tensorHom (α.obj (Y'ᘁ)) (β.map g),
      tensorμ_natural_right_assoc,
      MonoidalCategory.whiskerLeft_id]

/-- The stage-level left unit computation: the Λ unit composed
into the multiplication at a stage collapses to the left
unitor. -/
theorem lambdaMulStage_unit_left
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory A]
    [BraidedCategory D] (α : A ⥤ D) (β : A ⥤ D) [α.LaxMonoidal]
    [β.LaxMonoidal]
    [HasLambda α β] (Y : A) :
    ((λ_ (𝟙_ D)).inv ▷ (α.obj (Yᘁ) ⊗ β.obj Y)) ≫
      ((((ε α ≫ α.map unitRightDualIso.inv) ⊗ₘ ε β)) ▷
        (α.obj (Yᘁ) ⊗ β.obj Y)) ≫
      lambdaMulStage α β (𝟙_ A) Y ≫
      lambdaStage α β (𝟙_ A ⊗ Y) =
    (λ_ (α.obj (Yᘁ) ⊗ β.obj Y)).hom ≫ lambdaStage α β Y := by
  have hTL : ((λ_ (𝟙_ D)).inv ▷ (α.obj (Yᘁ) ⊗ β.obj Y)) ≫
      tensorμ (𝟙_ D) (𝟙_ D) (α.obj (Yᘁ)) (β.obj Y) =
        (λ_ (α.obj (Yᘁ) ⊗ β.obj Y)).hom ≫
          ((λ_ (α.obj (Yᘁ))).inv ⊗ₘ (λ_ (β.obj Y)).inv) := by
    rw [tensor_left_unitality]
    simp only [Category.assoc, tensorHom_comp_tensorHom,
      Iso.hom_inv_id, id_tensorHom_id, Category.comp_id]
  change ((λ_ (𝟙_ D)).inv ▷ (α.obj (Yᘁ) ⊗ β.obj Y)) ≫
      ((((ε α ≫ α.map unitRightDualIso.inv) ⊗ₘ ε β)) ▷
        (α.obj (Yᘁ) ⊗ β.obj Y)) ≫
      (tensorμ (α.obj (unitRigidDual (A := A))) (β.obj (𝟙_ A))
          (α.obj (Yᘁ)) (β.obj Y) ≫
        (μ α (unitRigidDual (A := A)) (Yᘁ) ⊗ₘ μ β (𝟙_ A) Y) ≫
        (α.map ((β_ (unitRigidDual (A := A)) (Yᘁ : A)).hom ≫
          (unitTensorDualIso Y).inv) ▷ β.obj (𝟙_ A ⊗ Y))) ≫
      lambdaStage α β (𝟙_ A ⊗ Y) =
    (λ_ (α.obj (Yᘁ) ⊗ β.obj Y)).hom ≫ lambdaStage α β Y
  simp only [Category.assoc]
  rw [tensorμ_natural_left_assoc, ← Category.assoc, hTL,
    Category.assoc, tensorHom_comp_tensorHom_assoc,
    tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc]
  rw [Functor.LaxMonoidal.left_unitality_inv,
    comp_whiskerRight]
  simp only [Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_left,
    reassoc_of% Functor.LaxMonoidal.left_unitality_inv,
    ← MonoidalCategory.tensorHom_id
      (α.map ((β_ (unitRigidDual (A := A)) (Yᘁ : A)).hom ≫
        (unitTensorDualIso Y).inv)) (β.obj (𝟙_ A ⊗ Y)),
    tensorHom_comp_tensorHom_assoc, Category.comp_id,
    ← Functor.map_comp, ← Functor.map_comp]
  simp only [Category.assoc]
  rw [leftUnitor_mate,
    tensorHom_def'_assoc, lambdaStage_condition,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- Dinaturality of the stage-level multiplication in the left
variable: the input of the outer coend descent of the Λ
multiplication. -/
theorem lambdaMulStage_dinat_left
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory A]
    [BraidedCategory D] (α : A ⥤ D) (β : A ⥤ D) [α.LaxMonoidal]
    [β.LaxMonoidal]
    [HasLambda α β] {X X' : A}
    (f : X ⟶ X') (Y : A) :
    ((α.map (fᘁ) ▷ β.obj X) ▷ (α.obj (Yᘁ) ⊗ β.obj Y)) ≫
        lambdaMulStage α β X Y ≫ lambdaStage α β (X ⊗ Y) =
      ((α.obj (X'ᘁ) ◁ β.map f) ▷ (α.obj (Yᘁ) ⊗ β.obj Y)) ≫
        lambdaMulStage α β X' Y ≫ lambdaStage α β (X' ⊗ Y) := by
  have hc : (fᘁ) ▷ (Yᘁ : A) ≫ (β_ (Xᘁ : A) (Yᘁ : A)).hom ≫
      (rightDualTensorIso X Y).inv =
        ((β_ (X'ᘁ : A) (Yᘁ : A)).hom ≫
          (rightDualTensorIso X' Y).inv) ≫ ((f ▷ Y)ᘁ) := by
    rw [BraidedCategory.braiding_naturality_left_assoc,
      whiskerRight_mate_square, Category.assoc]
  rw [lambdaMulStage, lambdaMulStage]
  simp only [Category.assoc]
  conv_lhs =>
    rw [← MonoidalCategory.tensorHom_id (α.map (fᘁ)) (β.obj X),
      tensorμ_natural_left_assoc,
      tensorHom_comp_tensorHom_assoc,
      Functor.LaxMonoidal.μ_natural_left,
      MonoidalCategory.id_whiskerRight, Category.id_comp,
      ← Category.comp_id (Functor.LaxMonoidal.μ β X Y),
      ← tensorHom_comp_tensorHom_assoc,
      MonoidalCategory.tensorHom_id,
      ← comp_whiskerRight_assoc,
      ← Functor.map_comp, hc,
      Functor.map_comp, comp_whiskerRight_assoc,
      lambdaStage_condition,
      ← whisker_exchange_assoc,
      ← MonoidalCategory.id_tensorHom,
      tensorHom_comp_tensorHom_assoc, Category.comp_id,
      ← Functor.LaxMonoidal.μ_natural_left,
      ← Category.id_comp
        (Functor.LaxMonoidal.μ α (X'ᘁ) (Yᘁ)),
      ← tensorHom_comp_tensorHom_assoc]
  conv_rhs =>
    rw [← MonoidalCategory.id_tensorHom (α.obj (X'ᘁ))
        (β.map f),
      tensorμ_natural_left_assoc,
      MonoidalCategory.id_whiskerRight]

/-- The inner descent of the Λ multiplication: for a fixed left
stage, the stage-level multiplication descends through the right
coend. -/
noncomputable def lambdaMulLeft
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory A]
    [BraidedCategory D] (α : A ⥤ D) (β : A ⥤ D) [α.LaxMonoidal]
    [β.LaxMonoidal]
    [HasLambda α β] (X : A)
    [PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorLeft (α.obj (Xᘁ) ⊗ β.obj X))] :
    (α.obj (Xᘁ) ⊗ β.obj X) ⊗ lambdaObj α β ⟶ lambdaObj α β :=
  tensorLeftCoendDesc (lambdaDiagram α β) _
    (fun Y => lambdaMulStage α β X Y ≫ lambdaStage α β (X ⊗ Y))
    (fun _ _ g => lambdaMulStage_dinat_right α β X g)

@[reassoc]
theorem whiskerLeft_stage_lambdaMulLeft
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory A]
    [BraidedCategory D] (α : A ⥤ D) (β : A ⥤ D) [α.LaxMonoidal]
    [β.LaxMonoidal]
    [HasLambda α β] (X : A)
    [PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorLeft (α.obj (Xᘁ) ⊗ β.obj X))] (Y : A) :
    ((α.obj (Xᘁ) ⊗ β.obj X) ◁ lambdaStage α β Y) ≫
        lambdaMulLeft α β X =
      lambdaMulStage α β X Y ≫ lambdaStage α β (X ⊗ Y) :=
  whiskerLeft_ι_tensorLeftCoendDesc (lambdaDiagram α β) _ _ _ Y

/-- Dinaturality of the inner descent in the left variable. -/
theorem lambdaMulLeft_dinat
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory A]
    [BraidedCategory D] (α : A ⥤ D) (β : A ⥤ D) [α.LaxMonoidal]
    [β.LaxMonoidal]
    [HasLambda α β]
    [∀ W : D, PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorLeft W)] {X X' : A} (f : X ⟶ X') :
    ((α.map (fᘁ) ▷ β.obj X) ▷ lambdaObj α β) ≫
        lambdaMulLeft α β X =
      ((α.obj (X'ᘁ) ◁ β.map f) ▷ lambdaObj α β) ≫
        lambdaMulLeft α β X' := by
  refine tensorLeft_coend_hom_ext (lambdaDiagram α β)
    (α.obj (X'ᘁ) ⊗ β.obj X) (fun Y => ?_)
  change ((α.obj (X'ᘁ) ⊗ β.obj X) ◁ lambdaStage α β Y) ≫
      ((α.map (fᘁ) ▷ β.obj X) ▷ lambdaObj α β) ≫
        lambdaMulLeft α β X =
    ((α.obj (X'ᘁ) ⊗ β.obj X) ◁ lambdaStage α β Y) ≫
      ((α.obj (X'ᘁ) ◁ β.map f) ▷ lambdaObj α β) ≫
        lambdaMulLeft α β X'
  rw [whisker_exchange_assoc, whisker_exchange_assoc,
    whiskerLeft_stage_lambdaMulLeft,
    whiskerLeft_stage_lambdaMulLeft,
    lambdaMulStage_dinat_left]

/-- **The Λ multiplication** (Deligne 3.7's product): the
stage-level multiplication descended through both coend
variables. -/
noncomputable def lambdaMul
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory A]
    [BraidedCategory D] (α : A ⥤ D) (β : A ⥤ D) [α.LaxMonoidal]
    [β.LaxMonoidal]
    [HasLambda α β]
    [∀ W : D, PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorLeft W)]
    [PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorRight (lambdaObj α β))] :
    lambdaObj α β ⊗ lambdaObj α β ⟶ lambdaObj α β :=
  tensorRightCoendDesc (lambdaDiagram α β) (lambdaObj α β)
    (fun X => lambdaMulLeft α β X)
    (fun _ _ f => lambdaMulLeft_dinat α β f)

@[reassoc (attr := simp)]
theorem stage_whiskerRight_lambdaMul
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory A]
    [BraidedCategory D] (α : A ⥤ D) (β : A ⥤ D) [α.LaxMonoidal]
    [β.LaxMonoidal]
    [HasLambda α β]
    [∀ W : D, PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorLeft W)]
    [PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorRight (lambdaObj α β))] (X : A) :
    (lambdaStage α β X ▷ lambdaObj α β) ≫ lambdaMul α β =
      lambdaMulLeft α β X :=
  ι_whiskerRight_tensorRightCoendDesc (lambdaDiagram α β) _ _ _ X

/-- The two-stage computation of the Λ multiplication. -/
theorem stage_tensorHom_lambdaMul
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory A]
    [BraidedCategory D] (α : A ⥤ D) (β : A ⥤ D) [α.LaxMonoidal]
    [β.LaxMonoidal]
    [HasLambda α β]
    [∀ W : D, PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorLeft W)]
    [PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorRight (lambdaObj α β))] (X Y : A) :
    (lambdaStage α β X ⊗ₘ lambdaStage α β Y) ≫ lambdaMul α β =
      lambdaMulStage α β X Y ≫ lambdaStage α β (X ⊗ Y) := by
  rw [tensorHom_def, Category.assoc, ← whisker_exchange_assoc,
    stage_whiskerRight_lambdaMul,
    whiskerLeft_stage_lambdaMulLeft]

/-- **The left unit law of the Λ algebra**: the Λ unit composed
into the Λ multiplication is the left unitor. -/
theorem lambdaMul_unit_left
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory A]
    [BraidedCategory D] (α : A ⥤ D) (β : A ⥤ D) [α.LaxMonoidal]
    [β.LaxMonoidal]
    [HasLambda α β]
    [∀ W : D, PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorLeft W)]
    [PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorRight (lambdaObj α β))] :
    (lambdaUnit α β ▷ lambdaObj α β) ≫ lambdaMul α β =
      (λ_ (lambdaObj α β)).hom := by
  refine tensorLeft_coend_hom_ext (lambdaDiagram α β) (𝟙_ D)
    (fun Y => ?_)
  change (𝟙_ D ◁ lambdaStage α β Y) ≫
      (lambdaUnit α β ▷ lambdaObj α β) ≫ lambdaMul α β =
    (𝟙_ D ◁ lambdaStage α β Y) ≫ (λ_ (lambdaObj α β)).hom
  erw [lambdaUnit, comp_whiskerRight, comp_whiskerRight]
  simp only [Category.assoc]
  change (𝟙_ D ◁ lambdaStage α β Y) ≫
      ((λ_ (𝟙_ D)).inv ▷ lambdaObj α β) ≫
      (((ε α ≫ α.map unitRightDualIso.inv) ⊗ₘ ε β) ▷
        lambdaObj α β) ≫
      (lambdaStage α β (𝟙_ A) ▷ lambdaObj α β) ≫
      lambdaMul α β =
    (𝟙_ D ◁ lambdaStage α β Y) ≫ (λ_ (lambdaObj α β)).hom
  erw [stage_whiskerRight_lambdaMul]
  erw [whisker_exchange_assoc, whisker_exchange_assoc]
  erw [whiskerLeft_stage_lambdaMulLeft]
  erw [lambdaMulStage_unit_left]
  rw [leftUnitor_naturality]

/-- The stage-level right unit computation: the mirror of
`RS.lambdaMulStage_unit_left`. -/
theorem lambdaMulStage_unit_right
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory A]
    [BraidedCategory D] (α : A ⥤ D) (β : A ⥤ D) [α.LaxMonoidal]
    [β.LaxMonoidal]
    [HasLambda α β] (Y : A) :
    ((α.obj (Yᘁ) ⊗ β.obj Y) ◁ (λ_ (𝟙_ D)).inv) ≫
      ((α.obj (Yᘁ) ⊗ β.obj Y) ◁
        ((ε α ≫ α.map unitRightDualIso.inv) ⊗ₘ ε β)) ≫
      lambdaMulStage α β Y (𝟙_ A) ≫
      lambdaStage α β (Y ⊗ 𝟙_ A) =
    (ρ_ (α.obj (Yᘁ) ⊗ β.obj Y)).hom ≫ lambdaStage α β Y := by
  have hTR : ((α.obj (Yᘁ) ⊗ β.obj Y) ◁ (λ_ (𝟙_ D)).inv) ≫
      tensorμ (α.obj (Yᘁ)) (β.obj Y) (𝟙_ D) (𝟙_ D) =
        (ρ_ (α.obj (Yᘁ) ⊗ β.obj Y)).hom ≫
          ((ρ_ (α.obj (Yᘁ))).inv ⊗ₘ (ρ_ (β.obj Y)).inv) := by
    rw [tensor_right_unitality]
    simp only [Category.assoc, tensorHom_comp_tensorHom,
      Iso.hom_inv_id, id_tensorHom_id, Category.comp_id]
  change ((α.obj (Yᘁ) ⊗ β.obj Y) ◁ (λ_ (𝟙_ D)).inv) ≫
      ((α.obj (Yᘁ) ⊗ β.obj Y) ◁
        ((ε α ≫ α.map unitRightDualIso.inv) ⊗ₘ ε β)) ≫
      (tensorμ (α.obj (Yᘁ)) (β.obj Y)
          (α.obj (unitRigidDual (A := A))) (β.obj (𝟙_ A)) ≫
        (μ α (Yᘁ) (unitRigidDual (A := A)) ⊗ₘ μ β Y (𝟙_ A)) ≫
        (α.map ((β_ (Yᘁ : A) (unitRigidDual (A := A))).hom ≫
          (tensorUnitDualIso Y).inv) ▷ β.obj (Y ⊗ 𝟙_ A))) ≫
      lambdaStage α β (Y ⊗ 𝟙_ A) =
    (ρ_ (α.obj (Yᘁ) ⊗ β.obj Y)).hom ≫ lambdaStage α β Y
  simp only [Category.assoc]
  rw [tensorμ_natural_right_assoc, ← Category.assoc, hTR,
    Category.assoc, tensorHom_comp_tensorHom_assoc,
    tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc]
  rw [Functor.LaxMonoidal.right_unitality_inv,
    MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_right,
    reassoc_of% Functor.LaxMonoidal.right_unitality_inv,
    ← MonoidalCategory.tensorHom_id
      (α.map ((β_ (Yᘁ : A) (unitRigidDual (A := A))).hom ≫
        (tensorUnitDualIso Y).inv)) (β.obj (Y ⊗ 𝟙_ A)),
    tensorHom_comp_tensorHom_assoc, Category.comp_id,
    ← Functor.map_comp, ← Functor.map_comp]
  simp only [Category.assoc]
  rw [rightUnitor_mate,
    tensorHom_def'_assoc, lambdaStage_condition,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- **The right unit law of the Λ algebra**. -/
theorem lambdaMul_unit_right
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory A]
    [BraidedCategory D] (α : A ⥤ D) (β : A ⥤ D) [α.LaxMonoidal]
    [β.LaxMonoidal]
    [HasLambda α β]
    [∀ W : D, PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorLeft W)]
    [PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorRight (lambdaObj α β))]
    [PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorRight (𝟙_ D))] :
    (lambdaObj α β ◁ lambdaUnit α β) ≫ lambdaMul α β =
      (ρ_ (lambdaObj α β)).hom := by
  refine tensorRight_coend_hom_ext (lambdaDiagram α β) (𝟙_ D)
    (fun X => ?_)
  change (lambdaStage α β X ▷ 𝟙_ D) ≫
      (lambdaObj α β ◁ lambdaUnit α β) ≫ lambdaMul α β =
    (lambdaStage α β X ▷ 𝟙_ D) ≫ (ρ_ (lambdaObj α β)).hom
  rw [← whisker_exchange_assoc]
  erw [stage_whiskerRight_lambdaMul]
  erw [lambdaUnit, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  erw [whiskerLeft_stage_lambdaMulLeft]
  erw [lambdaMulStage_unit_right]
  rw [rightUnitor_naturality]

/-- Maps out of the triple tensor of the Λ object agree once
they agree on triples of stages. -/
theorem lambda_triple_hom_ext
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
    (α : A ⥤ D) (β : A ⥤ D)
    [HasLambda α β]
    [∀ W : D, PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorLeft W)]
    [∀ W : D, PreservesColimit
      ((multispanIndexCoend (lambdaDiagram α β)).multispan ⋙
        tensorRight (lambdaObj α β)) (tensorRight W)]
    [∀ W W' : D, PreservesColimit
      ((multispanIndexCoend (lambdaDiagram α β)).multispan ⋙
        tensorLeft W) (tensorRight W')]
    {Z : D}
    {f g : (lambdaObj α β ⊗ lambdaObj α β) ⊗ lambdaObj α β ⟶ Z}
    (h : ∀ X Y W',
      ((lambdaStage α β X ⊗ₘ lambdaStage α β Y) ⊗ₘ
        lambdaStage α β W') ≫ f =
      ((lambdaStage α β X ⊗ₘ lambdaStage α β Y) ⊗ₘ
        lambdaStage α β W') ≫ g) : f = g := by
  refine tensorLeft_coend_hom_ext (lambdaDiagram α β)
    (lambdaObj α β ⊗ lambdaObj α β) (fun W' => ?_)
  refine coend_hom_ext_of_preserves (lambdaDiagram α β)
    (tensorRight (lambdaObj α β) ⋙
      tensorRight (α.obj (W'ᘁ) ⊗ β.obj W')) (fun X => ?_)
  refine coend_hom_ext_of_preserves (lambdaDiagram α β)
    (tensorLeft (α.obj (Xᘁ) ⊗ β.obj X) ⋙
      tensorRight (α.obj (W'ᘁ) ⊗ β.obj W')) (fun Y => ?_)
  change (((α.obj (Xᘁ) ⊗ β.obj X) ◁ lambdaStage α β Y) ▷
      (α.obj (W'ᘁ) ⊗ β.obj W')) ≫
      ((lambdaStage α β X ▷ lambdaObj α β) ▷
        (α.obj (W'ᘁ) ⊗ β.obj W')) ≫
      (((lambdaObj α β ⊗ lambdaObj α β) ◁
        lambdaStage α β W') ≫ f) =
    (((α.obj (Xᘁ) ⊗ β.obj X) ◁ lambdaStage α β Y) ▷
      (α.obj (W'ᘁ) ⊗ β.obj W')) ≫
      ((lambdaStage α β X ▷ lambdaObj α β) ▷
        (α.obj (W'ᘁ) ⊗ β.obj W')) ≫
      (((lambdaObj α β ⊗ lambdaObj α β) ◁
        lambdaStage α β W') ≫ g)
  have hpack : ∀ {Z' : D}
      (k : (lambdaObj α β ⊗ lambdaObj α β) ⊗ lambdaObj α β ⟶ Z'),
      (((α.obj (Xᘁ) ⊗ β.obj X) ◁ lambdaStage α β Y) ▷
        (α.obj (W'ᘁ) ⊗ β.obj W')) ≫
        ((lambdaStage α β X ▷ lambdaObj α β) ▷
          (α.obj (W'ᘁ) ⊗ β.obj W')) ≫
        (((lambdaObj α β ⊗ lambdaObj α β) ◁
          lambdaStage α β W') ≫ k) =
      ((lambdaStage α β X ⊗ₘ lambdaStage α β Y) ⊗ₘ
        lambdaStage α β W') ≫ k := by
    intro Z' k
    rw [tensorHom_def, tensorHom_def', comp_whiskerRight]
    simp only [Category.assoc]
  rw [hpack f, hpack g]
  exact h X Y W'

/-- **Associativity of the Λ multiplication** (Deligne 3.8). -/
theorem lambdaMul_assoc
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory A]
    [BraidedCategory D] (α : A ⥤ D) (β : A ⥤ D) [α.LaxMonoidal]
    [β.LaxMonoidal]
    [HasLambda α β]
    [∀ W : D, PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorLeft W)]
    [PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorRight (lambdaObj α β))]
    [∀ W : D, PreservesColimit
      ((multispanIndexCoend (lambdaDiagram α β)).multispan ⋙
        tensorRight (lambdaObj α β)) (tensorRight W)]
    [∀ W W' : D, PreservesColimit
      ((multispanIndexCoend (lambdaDiagram α β)).multispan ⋙
        tensorLeft W) (tensorRight W')] :
    (lambdaMul α β ▷ lambdaObj α β) ≫ lambdaMul α β =
      (α_ (lambdaObj α β) (lambdaObj α β)
        (lambdaObj α β)).hom ≫
        (lambdaObj α β ◁ lambdaMul α β) ≫ lambdaMul α β := by
  refine lambda_triple_hom_ext α β (fun X Y Z => ?_)
  calc ((lambdaStage α β X ⊗ₘ lambdaStage α β Y) ⊗ₘ
        lambdaStage α β Z) ≫
      (lambdaMul α β ▷ lambdaObj α β) ≫ lambdaMul α β
      = (lambdaMulStage α β X Y ▷
          (α.obj (Zᘁ) ⊗ β.obj Z)) ≫
        lambdaMulStage α β (X ⊗ Y) Z ≫
        lambdaStage α β ((X ⊗ Y) ⊗ Z) := by
        rw [← MonoidalCategory.tensorHom_id (lambdaMul α β),
          tensorHom_comp_tensorHom_assoc,
          stage_tensorHom_lambdaMul, Category.comp_id,
          ← Category.id_comp (lambdaStage α β Z),
          ← tensorHom_comp_tensorHom_assoc,
          stage_tensorHom_lambdaMul,
          MonoidalCategory.tensorHom_id]
    _ = (α_ (α.obj (Xᘁ) ⊗ β.obj X) (α.obj (Yᘁ) ⊗ β.obj Y)
          (α.obj (Zᘁ) ⊗ β.obj Z)).hom ≫
        ((α.obj (Xᘁ) ⊗ β.obj X) ◁ lambdaMulStage α β Y Z) ≫
        lambdaMulStage α β X (Y ⊗ Z) ≫
        lambdaStage α β (X ⊗ (Y ⊗ Z)) :=
      lambdaMulStage_assoc α β X Y Z
    _ = ((lambdaStage α β X ⊗ₘ lambdaStage α β Y) ⊗ₘ
          lambdaStage α β Z) ≫
        (α_ (lambdaObj α β) (lambdaObj α β)
          (lambdaObj α β)).hom ≫
        (lambdaObj α β ◁ lambdaMul α β) ≫ lambdaMul α β := by
        rw [associator_naturality_assoc,
          ← MonoidalCategory.id_tensorHom (lambdaObj α β)
            (lambdaMul α β),
          tensorHom_comp_tensorHom_assoc,
          stage_tensorHom_lambdaMul, Category.comp_id,
          ← Category.id_comp (lambdaStage α β X),
          ← tensorHom_comp_tensorHom_assoc,
          stage_tensorHom_lambdaMul,
          MonoidalCategory.id_tensorHom]

/-- Maps out of the square of the Λ object agree once they agree
on pairs of stages. -/
theorem lambda_pair_hom_ext
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] (α : A ⥤ D)
    (β : A ⥤ D)
    [HasLambda α β]
    [∀ W : D, PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorLeft W)]
    [PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorRight (lambdaObj α β))]
    {Z : D} {f g : lambdaObj α β ⊗ lambdaObj α β ⟶ Z}
    (h : ∀ X Y,
      (lambdaStage α β X ⊗ₘ lambdaStage α β Y) ≫ f =
      (lambdaStage α β X ⊗ₘ lambdaStage α β Y) ≫ g) :
    f = g := by
  refine tensorRight_coend_hom_ext (lambdaDiagram α β)
    (lambdaObj α β) (fun X => ?_)
  refine tensorLeft_coend_hom_ext (lambdaDiagram α β)
    (α.obj (Xᘁ) ⊗ β.obj X) (fun Y => ?_)
  change ((α.obj (Xᘁ) ⊗ β.obj X) ◁ lambdaStage α β Y) ≫
      ((lambdaStage α β X ▷ lambdaObj α β) ≫ f) =
    ((α.obj (Xᘁ) ⊗ β.obj X) ◁ lambdaStage α β Y) ≫
      ((lambdaStage α β X ▷ lambdaObj α β) ≫ g)
  have hpack : ∀ {Z' : D}
      (k : lambdaObj α β ⊗ lambdaObj α β ⟶ Z'),
      ((α.obj (Xᘁ) ⊗ β.obj X) ◁ lambdaStage α β Y) ≫
        ((lambdaStage α β X ▷ lambdaObj α β) ≫ k) =
      (lambdaStage α β X ⊗ₘ lambdaStage α β Y) ≫ k := by
    intro Z' k
    rw [tensorHom_def']
    simp only [Category.assoc]
  rw [hpack f, hpack g]
  exact h X Y

/-- **The Λ algebra** (Deligne 3.7): the coend of a pair of lax
monoidal functors from a braided rigid source is a monoid
object, with the stage at the unit as unit and the descended
stage-level multiplication as product. -/
@[implicit_reducible]
noncomputable def lambdaMonObj
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory A]
    [BraidedCategory D] (α : A ⥤ D) (β : A ⥤ D) [α.LaxMonoidal]
    [β.LaxMonoidal]
    [HasLambda α β]
    [∀ W : D, PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorLeft W)]
    [PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorRight (lambdaObj α β))]
    [PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorRight (𝟙_ D))]
    [∀ W : D, PreservesColimit
      ((multispanIndexCoend (lambdaDiagram α β)).multispan ⋙
        tensorRight (lambdaObj α β)) (tensorRight W)]
    [∀ W W' : D, PreservesColimit
      ((multispanIndexCoend (lambdaDiagram α β)).multispan ⋙
        tensorLeft W) (tensorRight W')] :
    MonObj (lambdaObj α β) where
  one := lambdaUnit α β
  mul := lambdaMul α β
  one_mul := lambdaMul_unit_left α β
  mul_one := lambdaMul_unit_right α β
  mul_assoc := lambdaMul_assoc α β

/-- The stage-level multiplication is natural in the pair of
monoidal transformations. -/
theorem lambdaMulStage_map
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory A]
    [BraidedCategory D] (α : A ⥤ D) (β : A ⥤ D) [α.LaxMonoidal]
    [β.LaxMonoidal]
    {α' β' : A ⥤ D} [α'.LaxMonoidal]
    [β'.LaxMonoidal] (η : α ⟶ α') (τ : β ⟶ β')
    [NatTrans.IsMonoidal η] [NatTrans.IsMonoidal τ] (X Y : A) :
    lambdaMulStage α β X Y ≫
        (η.app ((X ⊗ Y)ᘁ) ⊗ₘ τ.app (X ⊗ Y)) =
      ((η.app (Xᘁ) ⊗ₘ τ.app X) ⊗ₘ (η.app (Yᘁ) ⊗ₘ τ.app Y)) ≫
        lambdaMulStage α' β' X Y := by
  rw [lambdaMulStage, lambdaMulStage]
  simp only [Category.assoc]
  rw [tensorμ_natural_assoc, tensorHom_comp_tensorHom_assoc,
    ← NatTrans.IsMonoidal.tensor (τ := η),
    ← NatTrans.IsMonoidal.tensor (τ := τ),
    ← tensorHom_comp_tensorHom_assoc]
  congr 1
  congr 1
  rw [tensorHom_def, ← comp_whiskerRight_assoc, η.naturality,
    comp_whiskerRight_assoc, ← whisker_exchange,
    ← tensorHom_def_assoc]

end Multiplication

section Commutativity

open Functor.LaxMonoidal

/-- The stage-level commutativity of the Λ multiplication over a
symmetric source and target with braided functors. -/
theorem lambdaMulStage_comm
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
    [SymmetricCategory A] [SymmetricCategory D] (α : A ⥤ D) (β : A ⥤ D)
    [α.LaxBraided] [β.LaxBraided]
    [HasLambda α β] (X Y : A) :
    lambdaMulStage α β X Y ≫ lambdaStage α β (X ⊗ Y) =
      (β_ (α.obj (Xᘁ) ⊗ β.obj X)
          (α.obj (Yᘁ) ⊗ β.obj Y)).hom ≫
        lambdaMulStage α β Y X ≫ lambdaStage α β (Y ⊗ X) := by
  have hc : (β_ (Xᘁ : A) (Yᘁ : A)).hom ≫
      (rightDualTensorIso X Y).inv =
        (rightDualTensorIso Y X).inv ≫ (((β_ X Y).hom)ᘁ) :=
    (braiding_mate_square X Y).symm
  have hins : (rightDualTensorIso Y X).inv =
      (β_ (Xᘁ : A) (Yᘁ : A)).hom ≫
        ((β_ (Yᘁ : A) (Xᘁ : A)).hom ≫
          (rightDualTensorIso Y X).inv) := by
    rw [← Category.assoc, SymmetricCategory.symmetry,
      Category.id_comp]
  rw [lambdaMulStage, lambdaMulStage]
  simp only [Category.assoc]
  conv_lhs =>
    rw [hc, Functor.map_comp, comp_whiskerRight_assoc,
      lambdaStage_condition, ← whisker_exchange_assoc,
      hins, Functor.map_comp]
  rw [← MonoidalCategory.id_tensorHom
      (α.obj ((Xᘁ : A) ⊗ (Yᘁ : A))) (β.map (β_ X Y).hom),
    tensorHom_comp_tensorHom_assoc, Category.comp_id,
    Functor.LaxBraided.braided,
    comp_whiskerRight, Category.assoc,
    ← MonoidalCategory.tensorHom_id
      (α.map (β_ (Xᘁ : A) (Yᘁ : A)).hom) (β.obj (Y ⊗ X)),
    tensorHom_comp_tensorHom_assoc, Category.comp_id,
    Functor.LaxBraided.braided,
    ← tensorHom_comp_tensorHom_assoc,
    ← tensorμ_braiding_assoc]

/-- **Commutativity of the Λ multiplication** (Deligne 3.8). -/
theorem lambdaMul_comm
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
    [SymmetricCategory A] [SymmetricCategory D] (α : A ⥤ D) (β : A ⥤ D)
    [α.LaxBraided] [β.LaxBraided]
    [HasLambda α β]
    [∀ W : D, PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorLeft W)]
    [PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorRight (lambdaObj α β))] :
    (β_ (lambdaObj α β) (lambdaObj α β)).hom ≫ lambdaMul α β =
      lambdaMul α β := by
  refine lambda_pair_hom_ext α β (fun X Y => ?_)
  rw [reassoc_of% BraidedCategory.braiding_naturality
      (lambdaStage α β X) (lambdaStage α β Y),
    stage_tensorHom_lambdaMul α β Y X,
    ← lambdaMulStage_comm, stage_tensorHom_lambdaMul]

/-- **The Λ algebra is commutative** over symmetric data with
braided functors (Deligne 3.7–3.8 in full). -/
theorem lambdaIsCommMonObj
    [Category.{v} A] [MonoidalCategory A] [RightRigidCategory A]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
    [SymmetricCategory A] [SymmetricCategory D] (α : A ⥤ D) (β : A ⥤ D)
    [α.LaxBraided] [β.LaxBraided]
    [HasLambda α β]
    [∀ W : D, PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorLeft W)]
    [PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorRight (lambdaObj α β))]
    [PreservesColimit
      (multispanIndexCoend (lambdaDiagram α β)).multispan
      (tensorRight (𝟙_ D))]
    [∀ W : D, PreservesColimit
      ((multispanIndexCoend (lambdaDiagram α β)).multispan ⋙
        tensorRight (lambdaObj α β)) (tensorRight W)]
    [∀ W W' : D, PreservesColimit
      ((multispanIndexCoend (lambdaDiagram α β)).multispan ⋙
        tensorLeft W) (tensorRight W')] :
    letI : MonObj (lambdaObj α β) := lambdaMonObj α β
    IsCommMonObj (lambdaObj α β) := by
  let : MonObj (lambdaObj α β) := lambdaMonObj α β
  exact ⟨lambdaMul_comm α β⟩

end Commutativity

end RS
