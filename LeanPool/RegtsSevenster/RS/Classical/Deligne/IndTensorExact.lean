/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndCompact

/-!
# Right-exactness of the tensor product on ind-objects

Deligne's 2.2, exactness half: the transported tensor product of
`Ind C` preserves colimits in each variable, and the monoidal
structure is preadditive.

For a small monoidal `C` the file proves, unconditionally:

* `RS.indToDay` — the monoidal embedding of `Ind C` into the Day
  presheaf category `Cᵒᵖ ⊛⥤ Type v`, with its `Functor.Monoidal`
  instance transported from `RS.indDayEquivalence`;
* `RS.tensorLeft_ind_preservesColimitsOfShape` and the right-hand
  and packaged (`PreservesFilteredColimits`) versions — `tensorLeft
  X` and `tensorRight X` on `Ind C` preserve all small filtered
  colimits, for every `X : Ind C`;
* `RS.indOfTensorIso`/`RS.indOfTensorIsoSymm` — the embedding
  `indOf : C ⥤ Ind C` is monoidal up to isomorphism, with
  naturality in each variable
  (`RS.indOfTensorIso_hom_natural_right`/`_left`); this rests on the
  corepresentability calculus for `RS.dayCoyonedaIso`
  (`RS.eta_comp_dayCoyonedaIso_hom` and the naturality lemmas for
  `RS.dayYonedaIso`).

For `C` additionally preadditive with finite colimits and a
preadditive tensor (`[Preadditive C] [HasFiniteColimits C]
[MonoidalPreadditive C]` — Deligne's setting, where `C` is abelian
ℂ-linear with exact tensor):

* `RS.isIso_coprodComparison_tensorLeft`/`_tensorRight` — the binary
  coproduct comparisons of both tensoring functors on `Ind C` are
  invertible, by a three-stage filtered descent
  (`RS.isIso_app_of_isIso_indOf`) from the embedded case, which is
  conjugate under `indOf` to additivity of the tensor of `C`;
* `RS.isZero_tensor_left_ind`/`_right_ind` — tensoring kills zero
  objects;
* `RS.tensorLeft_ind_additive`/`RS.tensorRight_ind_additive` and
  **`MonoidalPreadditive (Ind C)`** — whiskering in `Ind C` is
  additive in each variable.

Filtered colimits are the only colimits `Ind C` possesses for
general `C`; under `[HasFiniteColimits C]` it is cocomplete, and the
finite-coproduct half of general right-exactness follows from the
additivity above (see the acceptance tests at the bottom).
Preservation of coequalizers demands genuine right-exactness of the
tensor of `C` and is left to a follow-up lane.

The `@[reducible]` marking on the small `coprodDiagram`/
`coprodCocone`/`coprodPairFunctor` helpers is deliberate: their
object fields must reduce at instance transparency for the
`show`-retyped colimit proofs below to be stateable.
-/

namespace RS

open CategoryTheory MonoidalCategory MonoidalCategory.DayFunctor Limits
open Opposite

universe v

noncomputable section

variable {C : Type v}

section Embedding

/-- The embedding of `Ind C` into the Day presheaf category: the
indization equivalence onto the full monoidal subcategory of
ind-objects, followed by the subcategory inclusion. -/
def indToDay [SmallCategory C] [MonoidalCategory C] : Ind C ⥤ (Cᵒᵖ ⊛⥤ Type v) :=
  (indDayEquivalence C).functor ⋙ ObjectProperty.ι _

/-- The forward functor of the indization equivalence is monoidal:
the monoidal structure of `Ind C` is transported across it. -/
instance [SmallCategory C] [MonoidalCategory C] :
    (indDayEquivalence C).functor.Monoidal :=
  inferInstanceAs
    (Monoidal.equivalenceTransported
      ((indDayEquivalence C).symm)).inverse.Monoidal

/-- The embedding into the Day presheaf category is monoidal. -/
instance
    [SmallCategory C] [MonoidalCategory C] : (indToDay (C := C)).Monoidal :=
  inferInstanceAs
    ((indDayEquivalence C).functor ⋙ ObjectProperty.ι _).Monoidal

instance [SmallCategory C] [MonoidalCategory C] : (indToDay (C := C)).Full :=
  inferInstanceAs
    ((indDayEquivalence C).functor ⋙ ObjectProperty.ι _).Full

instance
    [SmallCategory C] [MonoidalCategory C] : (indToDay (C := C)).Faithful :=
  inferInstanceAs
    ((indDayEquivalence C).functor ⋙ ObjectProperty.ι _).Faithful

/-- The embedding of `Ind C` into the Day presheaf category is the
inclusion into plain presheaves followed by the tautological
equivalence with the Day synonym. -/
def indToDayCompIso [SmallCategory C] [MonoidalCategory C] :
    indToDay (C := C) ≅
      Ind.inclusion C ⋙ (DayFunctor.equiv Cᵒᵖ (Type v)).inverse :=
  Iso.refl _

/-- The embedding into the Day presheaf category preserves small
filtered colimits: the inclusion into plain presheaves creates them
and the tautological Day equivalence preserves everything. -/
instance indToDay_preservesFilteredColimits
    [SmallCategory C] [MonoidalCategory C]
    (I : Type v)
    [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I (indToDay (C := C)) :=
  preservesColimitsOfShape_of_natIso (indToDayCompIso (C := C)).symm

end Embedding

section Filtered

/-- **Deligne 2.2, filtered half, left version**: tensoring on the
left in `Ind C` preserves small filtered colimits.  The embedding
into the Day presheaf category is monoidal, so it intertwines
`tensorLeft X` with the Day-convolution `tensorLeft` of the image,
which preserves all small colimits; the embedding preserves and
reflects filtered colimits, so `tensorLeft X` preserves them. -/
instance tensorLeft_ind_preservesColimitsOfShape
    [SmallCategory C] [MonoidalCategory C]
    (X : Ind C)
    (I : Type v) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I (tensorLeft X) :=
  haveI : PreservesColimitsOfShape I (tensorLeft X ⋙ indToDay) :=
    preservesColimitsOfShape_of_natIso
      (Functor.Monoidal.commTensorLeft indToDay X)
  preservesColimitsOfShape_of_reflects_of_preserves _ indToDay

/-- **Deligne 2.2, filtered half, right version**: tensoring on the
right in `Ind C` preserves small filtered colimits. -/
instance tensorRight_ind_preservesColimitsOfShape
    [SmallCategory C] [MonoidalCategory C]
    (X : Ind C)
    (I : Type v) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I (tensorRight X) :=
  haveI : PreservesColimitsOfShape I (tensorRight X ⋙ indToDay) :=
    preservesColimitsOfShape_of_natIso
      (Functor.Monoidal.commTensorRight indToDay X)
  preservesColimitsOfShape_of_reflects_of_preserves _ indToDay

/-- Filtered-colimit preservation by left tensoring, packaged. -/
instance tensorLeft_ind_preservesFilteredColimits
    [SmallCategory C] [MonoidalCategory C]
    (X : Ind C) :
    PreservesFilteredColimits (tensorLeft X) where
  preserves_filtered_colimits _ _ _ := inferInstance

/-- Filtered-colimit preservation by right tensoring, packaged. -/
instance tensorRight_ind_preservesFilteredColimits
    [SmallCategory C] [MonoidalCategory C]
    (X : Ind C) :
    PreservesFilteredColimits (tensorRight X) where
  preserves_filtered_colimits _ _ _ := inferInstance

end Filtered

section EmbeddingTensor

/-- The embedding into the Day presheaf category, restricted along
`indOf`, is the Day synonym of the Yoneda embedding. -/
def indOfDayIso [SmallCategory C] [MonoidalCategory C] :
    indOf ⋙ indToDay (C := C) ≅
      yoneda ⋙ (DayFunctor.equiv Cᵒᵖ (Type v)).inverse :=
  Functor.isoWhiskerLeft indOf (indToDayCompIso (C := C)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight Ind.yonedaCompInclusion
      (DayFunctor.equiv Cᵒᵖ (Type v)).inverse

/-- The embedding sends `indOf.obj z` to the Day representable at
`z`. -/
def indToDayIndOfIso [SmallCategory C] [MonoidalCategory C]
    (z : C) :
    (indToDay (C := C)).obj (indOf.obj z) ≅
      DayFunctor.mk (yoneda.obj z) :=
  (indOfDayIso (C := C)).app z

/-- The embedding calculus for the tensor of two embedded objects:
under `indToDay`, the tensor `indOf.obj x ⊗ indOf.obj y` is the Day
tensor of the representables at `x` and `y`, which is the
representable at `x ⊗ y` — that is, the image of
`indOf.obj (x ⊗ y)`. -/
def indToDayTensorIso [SmallCategory C] [MonoidalCategory C]
    (x y : C) :
    (indToDay (C := C)).obj (indOf.obj x ⊗ indOf.obj y) ≅
      (indToDay (C := C)).obj (indOf.obj (x ⊗ y)) :=
  (Functor.Monoidal.μIso indToDay (indOf.obj x) (indOf.obj y)).symm ≪≫
    tensorIso (indToDayIndOfIso x) (indToDayIndOfIso y) ≪≫
    dayYonedaIso x y ≪≫ (indToDayIndOfIso (x ⊗ y)).symm

/-- The fully faithful structure of the embedding into the Day
presheaf category. -/
def indToDayFullyFaithful [SmallCategory C] [MonoidalCategory C] :
    (indToDay (C := C)).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

/-- The tensor of two embedded objects of `Ind C` is the embedding
of the tensor: `indOf` is monoidal up to isomorphism. -/
def indOfTensorIso [SmallCategory C] [MonoidalCategory C]
    (x y : C) :
    indOf.obj x ⊗ indOf.obj y ≅ indOf.obj (x ⊗ y) :=
  indToDayFullyFaithful.preimageIso (indToDayTensorIso x y)

/-- **The embedding `C ⥤ Ind C` is monoidal up to isomorphism**, in
the orientation used downstream. -/
def indOfTensorIsoSymm [SmallCategory C] [MonoidalCategory C]
    (x y : C) :
    indOf.obj (x ⊗ y) ≅ indOf.obj x ⊗ indOf.obj y :=
  (indOfTensorIso x y).symm

end EmbeddingTensor

section CorepresentableCalculus

/-- Characterisation of the canonical isomorphism between two
corepresenting objects: its classification under the first
corepresentability structure is the universal element of the
second. -/
lemma corepresentableBy_homEquiv_uniqueUpToIso_hom {A : Type*}
    [Category A] {F : A ⥤ Type*} {X X' : A}
    (e : F.CorepresentableBy X) (e' : F.CorepresentableBy X') :
    e.homEquiv (e.uniqueUpToIso e').hom = e'.homEquiv (𝟙 X') := by
  simp [Functor.CorepresentableBy.uniqueUpToIso, Coyoneda.ext,
    Functor.FullyFaithful.preimageIso, Coyoneda.fullyFaithful_preimage]

end CorepresentableCalculus

section DayNaturality

attribute [local instance] dayConv

open scoped MonoidalCategory.ExternalProduct
open scoped CategoryTheory.Prod

/-- The universal transformation classified by the Day tensor of two
corepresentables: on a pair of morphisms it takes the tensor,
`(f, g) ↦ f ⊗ₘ g`. -/
def coyonedaTensorHom {D : Type v} [SmallCategory D] [MonoidalCategory D]
    (a b : D) :
    coyoneda.obj (op ((a, b) : D × D)) ⟶
      tensor D ⋙ coyoneda.obj (op (a ⊗ b)) where
  app X := TypeCat.ofHom fun (fg : (a, b) ⟶ X) => fg.1 ⊗ₘ fg.2
  naturality _ _ _ :=
    ConcreteCategory.hom_ext _ _ fun _ =>
      (tensorHom_comp_tensorHom _ _ _ _).symm

/-- `RS.dayCoyonedaIso` classifies as the universal transformation
`(f, g) ↦ f ⊗ₘ g`: composing the Day unit with its underlying
natural transformation is `RS.coyonedaTensorHom`. -/
lemma eta_comp_dayCoyonedaIso_hom
    {D : Type v} [SmallCategory D] [MonoidalCategory D]
    (a b : D) :
    η (DayFunctor.mk (coyoneda.obj (op a)))
        (DayFunctor.mk (coyoneda.obj (op b))) ≫
      Functor.whiskerLeft (tensor D) (dayCoyonedaIso a b).hom.natTrans =
    coyonedaTensorHom a b := by
  have h := corepresentableBy_homEquiv_uniqueUpToIso_hom
    (dayCoyonedaCorepresentableBy a b)
    (coyonedaDayCorepresentableBy (a ⊗ b))
  rw [show (dayCoyonedaCorepresentableBy a b).uniqueUpToIso
      (coyonedaDayCorepresentableBy (a ⊗ b)) = dayCoyonedaIso a b
    from rfl] at h
  dsimp [dayCoyonedaCorepresentableBy, coyonedaDayCorepresentableBy,
    Functor.homEquivOfIsLeftKanExtension] at h
  apply (coyonedaEquiv (C := D × D) (X := ((a, b) : D × D))
    (F := tensor D ⋙ coyoneda.obj (op (a ⊗ b)))).injective
  refine h.trans ?_
  change 𝟙 (a ⊗ b) = 𝟙 a ⊗ₘ 𝟙 b
  simp

/-- Naturality of `RS.dayCoyonedaIso` in the right variable. -/
lemma dayCoyonedaIso_hom_natural_right
    {D : Type v} [SmallCategory D] [MonoidalCategory D]
    (a : D) {b b' : D}
    (h : b ⟶ b') :
    (DayFunctor.mk (coyoneda.obj (op a)) ◁
        (⟨coyoneda.map h.op⟩ :
          DayFunctor.mk (coyoneda.obj (op b')) ⟶
            DayFunctor.mk (coyoneda.obj (op b)))) ≫
      (dayCoyonedaIso a b).hom =
    (dayCoyonedaIso a b').hom ≫ ⟨coyoneda.map ((a ◁ h).op)⟩ := by
  have h₁ : η (DayFunctor.mk (coyoneda.obj (op a)))
        (DayFunctor.mk (coyoneda.obj (op b'))) ≫
      Functor.whiskerLeft (tensor D)
        (DayFunctor.mk (coyoneda.obj (op a)) ◁
          (⟨coyoneda.map h.op⟩ :
            DayFunctor.mk (coyoneda.obj (op b')) ⟶
              DayFunctor.mk (coyoneda.obj (op b)))).natTrans =
      (externalProductBifunctor D D (Type v)).map
          (𝟙 (coyoneda.obj (op a)) ×ₘ coyoneda.map h.op) ≫
        η (DayFunctor.mk (coyoneda.obj (op a)))
          (DayFunctor.mk (coyoneda.obj (op b))) := by
    rw [natTrans_whiskerLeft]
    exact Functor.descOfIsLeftKanExtension_fac _ _ _ _
  ext1
  apply Functor.hom_ext_of_isLeftKanExtension _
    (η (DayFunctor.mk (coyoneda.obj (op a)))
      (DayFunctor.mk (coyoneda.obj (op b')))) _ _
  rw [comp_natTrans, comp_natTrans, Functor.whiskerLeft_comp,
    Functor.whiskerLeft_comp, ← Category.assoc, h₁, Category.assoc,
    eta_comp_dayCoyonedaIso_hom, ← Category.assoc,
    eta_comp_dayCoyonedaIso_hom]
  ext X : 2
  refine ConcreteCategory.hom_ext _ _ fun fg => ?_
  show fg.1 ⊗ₘ (h ≫ fg.2) = (a ◁ h) ≫ (fg.1 ⊗ₘ fg.2)
  rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]

/-- Naturality of `RS.dayCoyonedaIso` in the left variable. -/
lemma dayCoyonedaIso_hom_natural_left
    {D : Type v} [SmallCategory D] [MonoidalCategory D]
    {a a' : D} (f : a ⟶ a')
    (b : D) :
    ((⟨coyoneda.map f.op⟩ :
        DayFunctor.mk (coyoneda.obj (op a')) ⟶
          DayFunctor.mk (coyoneda.obj (op a))) ▷
        DayFunctor.mk (coyoneda.obj (op b))) ≫
      (dayCoyonedaIso a b).hom =
    (dayCoyonedaIso a' b).hom ≫ ⟨coyoneda.map ((f ▷ b).op)⟩ := by
  have h₁ : η (DayFunctor.mk (coyoneda.obj (op a')))
        (DayFunctor.mk (coyoneda.obj (op b))) ≫
      Functor.whiskerLeft (tensor D)
        ((⟨coyoneda.map f.op⟩ :
            DayFunctor.mk (coyoneda.obj (op a')) ⟶
              DayFunctor.mk (coyoneda.obj (op a))) ▷
          DayFunctor.mk (coyoneda.obj (op b))).natTrans =
      (externalProductBifunctor D D (Type v)).map
          (coyoneda.map f.op ×ₘ 𝟙 (coyoneda.obj (op b))) ≫
        η (DayFunctor.mk (coyoneda.obj (op a)))
          (DayFunctor.mk (coyoneda.obj (op b))) := by
    rw [natTrans_whiskerRight]
    exact Functor.descOfIsLeftKanExtension_fac _ _ _ _
  ext1
  apply Functor.hom_ext_of_isLeftKanExtension _
    (η (DayFunctor.mk (coyoneda.obj (op a')))
      (DayFunctor.mk (coyoneda.obj (op b)))) _ _
  rw [comp_natTrans, comp_natTrans, Functor.whiskerLeft_comp,
    Functor.whiskerLeft_comp, ← Category.assoc, h₁, Category.assoc,
    eta_comp_dayCoyonedaIso_hom, ← Category.assoc,
    eta_comp_dayCoyonedaIso_hom]
  ext X : 2
  refine ConcreteCategory.hom_ext _ _ fun fg => ?_
  show (f ≫ fg.1) ⊗ₘ fg.2 = (f ▷ b) ≫ (fg.1 ⊗ₘ fg.2)
  rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]

end DayNaturality

section YonedaNaturality

/-- Naturality of `Coyoneda.objOpOp`, inverse form. -/
lemma yoneda_map_comp_objOpOp_inv [SmallCategory C]
    {y y' : C} (g : y ⟶ y') :
    yoneda.map g ≫ (Coyoneda.objOpOp y').inv =
      (Coyoneda.objOpOp y).inv ≫ coyoneda.map (g.op.op) := by
  ext z u
  simp [Coyoneda.objOpOp, opEquiv]

/-- Naturality of `Coyoneda.objOpOp`, forward form, at a left
whiskering of `Cᵒᵖ`. -/
lemma coyoneda_map_whiskerLeft_comp_objOpOp_hom
    [SmallCategory C] [MonoidalCategory C]
    (x : C) {y y' : C}
    (g : y ⟶ y') :
    coyoneda.map ((op x ◁ g.op).op) ≫
        (Coyoneda.objOpOp (x ⊗ y')).hom =
      (Coyoneda.objOpOp (x ⊗ y)).hom ≫ yoneda.map (x ◁ g) := by
  ext z u
  simp [Coyoneda.objOpOp, opEquiv]

/-- Naturality of `Coyoneda.objOpOp`, forward form, at a right
whiskering of `Cᵒᵖ`. -/
lemma coyoneda_map_whiskerRight_comp_objOpOp_hom
    [SmallCategory C] [MonoidalCategory C]
    {x x' : C}
    (f : x ⟶ x') (y : C) :
    coyoneda.map ((f.op ▷ op y).op) ≫
        (Coyoneda.objOpOp (x' ⊗ y)).hom =
      (Coyoneda.objOpOp (x ⊗ y)).hom ≫ yoneda.map (f ▷ y) := by
  ext z u
  simp [Coyoneda.objOpOp, opEquiv]

/-- Naturality of `RS.dayYonedaIso` in the right variable. -/
lemma dayYonedaIso_hom_natural_right [SmallCategory C] [MonoidalCategory C]
    (x : C) {y y' : C}
    (g : y ⟶ y') :
    (DayFunctor.mk (yoneda.obj x) ◁
        (⟨yoneda.map g⟩ : DayFunctor.mk (yoneda.obj y) ⟶
          DayFunctor.mk (yoneda.obj y'))) ≫ (dayYonedaIso x y').hom =
      (dayYonedaIso x y).hom ≫ ⟨yoneda.map (x ◁ g)⟩ := by
  have s₁ : (⟨yoneda.map g⟩ : DayFunctor.mk (yoneda.obj y) ⟶
        DayFunctor.mk (yoneda.obj y')) ≫
        (dayMkIso (Coyoneda.objOpOp y').symm).hom =
      (dayMkIso (Coyoneda.objOpOp y).symm).hom ≫
        ⟨coyoneda.map (g.op.op)⟩ := by
    ext1
    exact yoneda_map_comp_objOpOp_inv g
  have s₂ : (⟨coyoneda.map ((op x ◁ g.op).op)⟩ :
        DayFunctor.mk (coyoneda.obj (op (op x ⊗ op y))) ⟶
          DayFunctor.mk (coyoneda.obj (op (op x ⊗ op y')))) ≫
        (dayMkIso (Coyoneda.objOpOp (x ⊗ y'))).hom =
      (dayMkIso (Coyoneda.objOpOp (x ⊗ y))).hom ≫
        ⟨yoneda.map (x ◁ g)⟩ := by
    ext1
    exact coyoneda_map_whiskerLeft_comp_objOpOp_hom x g
  have e₁ : (DayFunctor.mk (yoneda.obj x) ◁
        (⟨yoneda.map g⟩ : DayFunctor.mk (yoneda.obj y) ⟶
          DayFunctor.mk (yoneda.obj y'))) ≫
        ((dayMkIso (Coyoneda.objOpOp x).symm).hom ⊗ₘ
          (dayMkIso (Coyoneda.objOpOp y').symm).hom) =
      ((dayMkIso (Coyoneda.objOpOp x).symm).hom ⊗ₘ
          (dayMkIso (Coyoneda.objOpOp y).symm).hom) ≫
        (DayFunctor.mk (coyoneda.obj (op (op x))) ◁
          (⟨coyoneda.map (g.op.op)⟩ :
            DayFunctor.mk (coyoneda.obj (op (op y))) ⟶
              DayFunctor.mk (coyoneda.obj (op (op y'))))) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp,
      s₁, ← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
  simp only [dayYonedaIso, Iso.trans_hom, tensorIso_hom]
  rw [← Category.assoc, e₁, Category.assoc,
    reassoc_of% dayCoyonedaIso_hom_natural_right (D := Cᵒᵖ)
      (op x) (g.op), s₂]
  simp only [Category.assoc]

/-- Naturality of `RS.dayYonedaIso` in the left variable. -/
lemma dayYonedaIso_hom_natural_left [SmallCategory C] [MonoidalCategory C]
    {x x' : C} (f : x ⟶ x')
    (y : C) :
    ((⟨yoneda.map f⟩ : DayFunctor.mk (yoneda.obj x) ⟶
        DayFunctor.mk (yoneda.obj x')) ▷
        DayFunctor.mk (yoneda.obj y)) ≫ (dayYonedaIso x' y).hom =
      (dayYonedaIso x y).hom ≫ ⟨yoneda.map (f ▷ y)⟩ := by
  have s₁ : (⟨yoneda.map f⟩ : DayFunctor.mk (yoneda.obj x) ⟶
        DayFunctor.mk (yoneda.obj x')) ≫
        (dayMkIso (Coyoneda.objOpOp x').symm).hom =
      (dayMkIso (Coyoneda.objOpOp x).symm).hom ≫
        ⟨coyoneda.map (f.op.op)⟩ := by
    ext1
    exact yoneda_map_comp_objOpOp_inv f
  have s₂ : (⟨coyoneda.map ((f.op ▷ op y).op)⟩ :
        DayFunctor.mk (coyoneda.obj (op (op x ⊗ op y))) ⟶
          DayFunctor.mk (coyoneda.obj (op (op x' ⊗ op y)))) ≫
        (dayMkIso (Coyoneda.objOpOp (x' ⊗ y))).hom =
      (dayMkIso (Coyoneda.objOpOp (x ⊗ y))).hom ≫
        ⟨yoneda.map (f ▷ y)⟩ := by
    ext1
    exact coyoneda_map_whiskerRight_comp_objOpOp_hom f y
  have e₁ : ((⟨yoneda.map f⟩ : DayFunctor.mk (yoneda.obj x) ⟶
        DayFunctor.mk (yoneda.obj x')) ▷
        DayFunctor.mk (yoneda.obj y)) ≫
        ((dayMkIso (Coyoneda.objOpOp x').symm).hom ⊗ₘ
          (dayMkIso (Coyoneda.objOpOp y).symm).hom) =
      ((dayMkIso (Coyoneda.objOpOp x).symm).hom ⊗ₘ
          (dayMkIso (Coyoneda.objOpOp y).symm).hom) ≫
        ((⟨coyoneda.map (f.op.op)⟩ :
            DayFunctor.mk (coyoneda.obj (op (op x))) ⟶
              DayFunctor.mk (coyoneda.obj (op (op x')))) ▷
          DayFunctor.mk (coyoneda.obj (op (op y)))) := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp,
      s₁, ← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
  simp only [dayYonedaIso, Iso.trans_hom, tensorIso_hom]
  rw [← Category.assoc, e₁, Category.assoc,
    reassoc_of% dayCoyonedaIso_hom_natural_left (D := Cᵒᵖ)
      (f.op) (op y), s₂]
  simp only [Category.assoc]

end YonedaNaturality

section EmbeddingTensorNatural

/-- Naturality of `RS.indToDayIndOfIso` in its object. -/
lemma indToDay_map_comp_indToDayIndOfIso_hom
    [SmallCategory C] [MonoidalCategory C]
    {z z' : C} (u : z ⟶ z') :
    (indToDay (C := C)).map (indOf.map u) ≫
        (indToDayIndOfIso z').hom =
      (indToDayIndOfIso z).hom ≫ ⟨yoneda.map u⟩ :=
  (indOfDayIso (C := C)).hom.naturality u

/-- Inverse form of `RS.indToDay_map_comp_indToDayIndOfIso_hom`. -/
lemma comp_indToDayIndOfIso_inv [SmallCategory C] [MonoidalCategory C]
    {z z' : C} (u : z ⟶ z') :
    (⟨yoneda.map u⟩ : DayFunctor.mk (yoneda.obj z) ⟶
        DayFunctor.mk (yoneda.obj z')) ≫ (indToDayIndOfIso z').inv =
      (indToDayIndOfIso z).inv ≫ (indToDay (C := C)).map (indOf.map u) := by
  rw [Iso.comp_inv_eq, Category.assoc,
    indToDay_map_comp_indToDayIndOfIso_hom, Iso.inv_hom_id_assoc]

/-- Naturality of `RS.indOfTensorIso` in the right variable: the
embedding-tensor comparison intertwines whiskering by an embedded
object with the embedded whiskering. -/
lemma indOfTensorIso_hom_natural_right [SmallCategory C] [MonoidalCategory C]
    (x : C) {y y' : C}
    (g : y ⟶ y') :
    (indOf.obj x ◁ indOf.map g) ≫ (indOfTensorIso x y').hom =
      (indOfTensorIso x y).hom ≫ indOf.map (x ◁ g) := by
  apply (indToDay (C := C)).map_injective
  have hmap : ∀ (a b : C),
      (indToDay (C := C)).map (indOfTensorIso a b).hom =
        (indToDayTensorIso a b).hom := fun a b => by
    rw [indOfTensorIso, Functor.FullyFaithful.preimageIso_hom,
      Functor.FullyFaithful.map_preimage]
  have e₁ : ((indToDay (C := C)).obj (indOf.obj x) ◁
        (indToDay (C := C)).map (indOf.map g)) ≫
        ((indToDayIndOfIso x).hom ⊗ₘ (indToDayIndOfIso y').hom) =
      ((indToDayIndOfIso x).hom ⊗ₘ (indToDayIndOfIso y).hom) ≫
        (DayFunctor.mk (yoneda.obj x) ◁
          (⟨yoneda.map g⟩ : DayFunctor.mk (yoneda.obj y) ⟶
            DayFunctor.mk (yoneda.obj y'))) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp,
      indToDay_map_comp_indToDayIndOfIso_hom, ← id_tensorHom,
      tensorHom_comp_tensorHom, Category.comp_id]
  rw [Functor.map_comp, Functor.map_comp, hmap, hmap,
    Functor.Monoidal.map_whiskerLeft]
  simp only [indToDayTensorIso, Iso.trans_hom, Iso.symm_hom,
    tensorIso_hom, Functor.Monoidal.μIso_inv, Category.assoc,
    Functor.Monoidal.μ_δ_assoc]
  rw [← Category.assoc ((indToDay (C := C)).obj (indOf.obj x) ◁ _),
    e₁, Category.assoc,
    reassoc_of% dayYonedaIso_hom_natural_right x g,
    comp_indToDayIndOfIso_inv]

/-- Naturality of `RS.indOfTensorIso` in the left variable. -/
lemma indOfTensorIso_hom_natural_left [SmallCategory C] [MonoidalCategory C]
    {x x' : C} (f : x ⟶ x')
    (y : C) :
    (indOf.map f ▷ indOf.obj y) ≫ (indOfTensorIso x' y).hom =
      (indOfTensorIso x y).hom ≫ indOf.map (f ▷ y) := by
  apply (indToDay (C := C)).map_injective
  have hmap : ∀ (a b : C),
      (indToDay (C := C)).map (indOfTensorIso a b).hom =
        (indToDayTensorIso a b).hom := fun a b => by
    rw [indOfTensorIso, Functor.FullyFaithful.preimageIso_hom,
      Functor.FullyFaithful.map_preimage]
  have e₁ : ((indToDay (C := C)).map (indOf.map f) ▷
        (indToDay (C := C)).obj (indOf.obj y)) ≫
        ((indToDayIndOfIso x').hom ⊗ₘ (indToDayIndOfIso y).hom) =
      ((indToDayIndOfIso x).hom ⊗ₘ (indToDayIndOfIso y).hom) ≫
        ((⟨yoneda.map f⟩ : DayFunctor.mk (yoneda.obj x) ⟶
            DayFunctor.mk (yoneda.obj x')) ▷
          DayFunctor.mk (yoneda.obj y)) := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp,
      indToDay_map_comp_indToDayIndOfIso_hom, ← tensorHom_id,
      tensorHom_comp_tensorHom, Category.comp_id]
  rw [Functor.map_comp, Functor.map_comp, hmap, hmap,
    Functor.Monoidal.map_whiskerRight]
  simp only [indToDayTensorIso, Iso.trans_hom, Iso.symm_hom,
    tensorIso_hom, Functor.Monoidal.μIso_inv, Category.assoc,
    Functor.Monoidal.μ_δ_assoc]
  rw [← Category.assoc ((indToDay (C := C)).map (indOf.map f) ▷ _),
    e₁, Category.assoc,
    reassoc_of% dayYonedaIso_hom_natural_left f y,
    comp_indToDayIndOfIso_inv]

/-- **The unit of `Ind C` is the embedded unit**: the transported
Day unit, identified through `RS.dayUnitIso` with the representable
at `𝟙_ C` and pulled back through the fully faithful monoidal
embedding `RS.indToDay`. -/
def indOfUnitIso
    [SmallCategory C] [MonoidalCategory C] : (𝟙_ (Ind C)) ≅ indOf.obj (𝟙_ C) :=
  indToDayFullyFaithful.preimageIso
    ((Functor.Monoidal.εIso (indToDay (C := C))).symm ≪≫
      dayUnitIso Cᵒᵖ ≪≫ dayMkIso (Coyoneda.objOpOp (𝟙_ C)) ≪≫
      (indToDayIndOfIso (𝟙_ C)).symm)

end EmbeddingTensorNatural

section CoconeTools

universe v₁ v₂ v₃ u₂ u₃

/-- A cocone leg, with its type stated at the cocone point. -/
def coconeLeg {J : Type v₁} [Category.{v₁} J] {ℬ : Type u₃} [Category.{v₃} ℬ]
    {D : J ⥤ ℬ} (c : Cocone D) (j : J) : D.obj j ⟶ c.pt :=
  c.ι.app j

lemma coconeLeg_w
    {J : Type v₁} [Category.{v₁} J] {ℬ : Type u₃} [Category.{v₃} ℬ]
    {D : J ⥤ ℬ} (c : Cocone D) {j k : J} (u : j ⟶ k) :
    D.map u ≫ coconeLeg c k = coconeLeg c j :=
  c.w u

/-- The pointwise binary coproduct of two diagrams of the same
shape. -/
@[reducible, simps]
def coprodDiagram
    {J : Type v₁} [Category.{v₁} J] {ℬ : Type u₃} [Category.{v₃} ℬ]
    [HasBinaryCoproducts ℬ]
    (D₁ D₂ : J ⥤ ℬ) : J ⥤ ℬ where
  obj j := D₁.obj j ⨿ D₂.obj j
  map u := coprod.map (D₁.map u) (D₂.map u)

/-- A leg of a cocone over a pointwise coproduct, with its type
stated at the coproduct. -/
def coprodLeg {J : Type v₁} [Category.{v₁} J] {ℬ : Type u₃} [Category.{v₃} ℬ]
    [HasBinaryCoproducts ℬ]
    {D₁ D₂ : J ⥤ ℬ} (s : Cocone (coprodDiagram D₁ D₂))
    (j : J) : D₁.obj j ⨿ D₂.obj j ⟶ s.pt :=
  s.ι.app j

lemma coprodLeg_w
    {J : Type v₁} [Category.{v₁} J] {ℬ : Type u₃} [Category.{v₃} ℬ]
    [HasBinaryCoproducts ℬ]
    {D₁ D₂ : J ⥤ ℬ} (s : Cocone (coprodDiagram D₁ D₂))
    {j k : J} (u : j ⟶ k) :
    coprod.map (D₁.map u) (D₂.map u) ≫ coprodLeg s k = coprodLeg s j :=
  s.w u

/-- The coproduct of two cocones: a cocone over the pointwise
coproduct diagram, with the coproduct of the two points as its
point. -/
@[reducible, simps]
def coprodCocone {J : Type v₁} [Category.{v₁} J] {ℬ : Type u₃} [Category.{v₃} ℬ]
    [HasBinaryCoproducts ℬ]
    {D₁ D₂ : J ⥤ ℬ} (c₁ : Cocone D₁) (c₂ : Cocone D₂) :
    Cocone (coprodDiagram D₁ D₂) where
  pt := c₁.pt ⨿ c₂.pt
  ι :=
    { app := fun j => coprod.map (coconeLeg c₁ j) (coconeLeg c₂ j)
      naturality := fun j k u => by
        show coprod.map (D₁.map u) (D₂.map u) ≫
            coprod.map (coconeLeg c₁ k) (coconeLeg c₂ k) =
          coprod.map (coconeLeg c₁ j) (coconeLeg c₂ j) ≫
            𝟙 (c₁.pt ⨿ c₂.pt)
        rw [Category.comp_id, coprod.map_map, coconeLeg_w, coconeLeg_w] }

/-- A cocone over the pointwise coproduct, restricted along the
first inclusion to a cocone over the first diagram. -/
@[reducible, simps]
def coprodCoconeFst
    {J : Type v₁} [Category.{v₁} J] {ℬ : Type u₃} [Category.{v₃} ℬ]
    [HasBinaryCoproducts ℬ]
    {D₁ D₂ : J ⥤ ℬ}
    (s : Cocone (coprodDiagram D₁ D₂)) : Cocone D₁ where
  pt := s.pt
  ι :=
    { app := fun j => coprod.inl ≫ coprodLeg s j
      naturality := fun j k u => by
        show D₁.map u ≫ coprod.inl ≫ coprodLeg s k =
          (coprod.inl ≫ coprodLeg s j) ≫ 𝟙 s.pt
        rw [Category.comp_id, ← coprodLeg_w s u, coprod.inl_map_assoc] }

/-- A cocone over the pointwise coproduct, restricted along the
second inclusion to a cocone over the second diagram. -/
@[reducible, simps]
def coprodCoconeSnd
    {J : Type v₁} [Category.{v₁} J] {ℬ : Type u₃} [Category.{v₃} ℬ]
    [HasBinaryCoproducts ℬ]
    {D₁ D₂ : J ⥤ ℬ}
    (s : Cocone (coprodDiagram D₁ D₂)) : Cocone D₂ where
  pt := s.pt
  ι :=
    { app := fun j => coprod.inr ≫ coprodLeg s j
      naturality := fun j k u => by
        show D₂.map u ≫ coprod.inr ≫ coprodLeg s k =
          (coprod.inr ≫ coprodLeg s j) ≫ 𝟙 s.pt
        rw [Category.comp_id, ← coprodLeg_w s u, coprod.inr_map_assoc] }

/-- The coproduct of two colimit cocones is a colimit cocone over
the pointwise coproduct diagram: colimits commute with binary
coproducts. -/
def isColimitCoprodCocone
    {J : Type v₁} [Category.{v₁} J] {ℬ : Type u₃} [Category.{v₃} ℬ]
    [HasBinaryCoproducts ℬ]
    {D₁ D₂ : J ⥤ ℬ} {c₁ : Cocone D₁}
    {c₂ : Cocone D₂} (h₁ : IsColimit c₁) (h₂ : IsColimit c₂) :
    IsColimit (coprodCocone c₁ c₂) where
  desc s := coprod.desc (h₁.desc (coprodCoconeFst s))
    (h₂.desc (coprodCoconeSnd s))
  fac s j := by
    have f₁ : coconeLeg c₁ j ≫ h₁.desc (coprodCoconeFst s) =
        coprod.inl ≫ coprodLeg s j := h₁.fac (coprodCoconeFst s) j
    have f₂ : coconeLeg c₂ j ≫ h₂.desc (coprodCoconeSnd s) =
        coprod.inr ≫ coprodLeg s j := h₂.fac (coprodCoconeSnd s) j
    show coprod.map (coconeLeg c₁ j) (coconeLeg c₂ j) ≫
        coprod.desc (h₁.desc (coprodCoconeFst s))
          (h₂.desc (coprodCoconeSnd s)) = coprodLeg s j
    apply coprod.hom_ext
    · rw [coprod.inl_map_assoc, coprod.inl_desc]
      exact f₁
    · rw [coprod.inr_map_assoc, coprod.inr_desc]
      exact f₂
  uniq s m hm := by
    have hm' : ∀ j, coprod.map (coconeLeg c₁ j) (coconeLeg c₂ j) ≫ m =
        coprodLeg s j := hm
    show m = coprod.desc (h₁.desc (coprodCoconeFst s))
      (h₂.desc (coprodCoconeSnd s))
    apply coprod.hom_ext
    · rw [coprod.inl_desc]
      refine h₁.hom_ext fun j => ?_
      have hf : coconeLeg c₁ j ≫ h₁.desc (coprodCoconeFst s) =
          coprod.inl ≫ coprodLeg s j := h₁.fac (coprodCoconeFst s) j
      show coconeLeg c₁ j ≫ coprod.inl ≫ m =
        coconeLeg c₁ j ≫ h₁.desc (coprodCoconeFst s)
      rw [hf, ← hm' j, coprod.inl_map_assoc]
    · rw [coprod.inr_desc]
      refine h₂.hom_ext fun j => ?_
      have hf : coconeLeg c₂ j ≫ h₂.desc (coprodCoconeSnd s) =
          coprod.inr ≫ coprodLeg s j := h₂.fac (coprodCoconeSnd s) j
      show coconeLeg c₂ j ≫ coprod.inr ≫ m =
        coconeLeg c₂ j ≫ h₂.desc (coprodCoconeSnd s)
      rw [hf, ← hm' j, coprod.inr_map_assoc]

/-- The pointwise binary coproduct of two functors. -/
@[reducible, simps]
def coprodPairFunctor
    {𝒜 : Type u₂} [Category.{v₂} 𝒜] {ℬ : Type u₃} [Category.{v₃} ℬ]
    [HasBinaryCoproducts ℬ]
    (F G : 𝒜 ⥤ ℬ) : 𝒜 ⥤ ℬ where
  obj A := F.obj A ⨿ G.obj A
  map u := coprod.map (F.map u) (G.map u)

lemma preservesColimitsOfShape_coprodPairFunctor
    {J : Type v₁} [Category.{v₁} J] {𝒜 : Type u₂} [Category.{v₂} 𝒜]
    {ℬ : Type u₃} [Category.{v₃} ℬ] [HasBinaryCoproducts ℬ]
    (F G : 𝒜 ⥤ ℬ)
    [PreservesColimitsOfShape J F] [PreservesColimitsOfShape J G] :
    PreservesColimitsOfShape J (coprodPairFunctor F G) where
  preservesColimit {D} :=
    { preserves := fun {c} hc => by
        refine ⟨IsColimit.ofIsoColimit
          (isColimitCoprodCocone (isColimitOfPreserves F hc)
            (isColimitOfPreserves G hc))
          (Cocone.ext (Iso.refl _) fun j => ?_)⟩
        show coprod.map (coconeLeg (F.mapCocone c) j)
            (coconeLeg (G.mapCocone c) j) ≫
            𝟙 ((F.mapCocone c).pt ⨿ (G.mapCocone c).pt) =
          coprod.map (F.map (c.ι.app j)) (G.map (c.ι.app j))
        rw [Category.comp_id]
        rfl }

lemma preservesColimitsOfShape_const_of_isConnected
    {J : Type v₁} [Category.{v₁} J] {𝒜 : Type u₂} [Category.{v₂} 𝒜]
    {ℬ : Type u₃} [Category.{v₃} ℬ]
    [IsConnected J]
    (W : ℬ) :
    PreservesColimitsOfShape J ((Functor.const 𝒜).obj W) where
  preservesColimit {D} :=
    { preserves := fun {c} _ => by
        refine ⟨IsColimit.ofIsoColimit (isColimitConstCocone J W)
          (Cocone.ext (Iso.refl _) fun j => ?_)⟩
        show 𝟙 W ≫ 𝟙 W = 𝟙 W
        rw [Category.comp_id] }

end CoconeTools

section FilteredDescent

/-- **Filtered descent for pointwise-invertible transformations**: a
natural transformation between endofunctors of `Ind C` that both
preserve filtered colimits is invertible everywhere as soon as it is
invertible on the embedded objects, since every ind-object is a
filtered colimit of embedded objects. -/
lemma isIso_app_of_isIso_indOf [SmallCategory C]
    {L R : Ind C ⥤ Ind C}
    [PreservesFilteredColimits L] [PreservesFilteredColimits R]
    (γ : L ⟶ R) (hbase : ∀ c : C, IsIso (γ.app (indOf.obj c)))
    (A : Ind C) : IsIso (γ.app A) := by
  set D : A.presentation.I ⥤ Ind C := A.presentation.F ⋙ indOf with hD
  suffices h : IsIso (γ.app (colimit D)) by
    have e : colimit D ≅ A := Ind.colimitPresentationCompYoneda A
    have : γ.app A = L.map e.inv ≫ γ.app (colimit D) ≫ R.map e.hom := by
      rw [← γ.naturality e.hom, ← Functor.map_comp_assoc,
        e.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
    rw [this]
    infer_instance
  have hw : ∀ k, IsIso ((Functor.whiskerLeft D γ).app k) := fun k =>
    hbase (A.presentation.F.obj k)
  haveI : IsIso (Functor.whiskerLeft D γ) :=
    NatIso.isIso_of_isIso_app _
  have hL : IsColimit (L.mapCocone (colimit.cocone D)) :=
    isColimitOfPreserves L (colimit.isColimit D)
  have hR : IsColimit (R.mapCocone (colimit.cocone D)) :=
    isColimitOfPreserves R (colimit.isColimit D)
  have : γ.app (colimit D) = (IsColimit.coconePointsIsoOfNatIso hL hR
      (asIso (Functor.whiskerLeft D γ))).hom := by
    refine hL.hom_ext fun k => ?_
    refine Eq.trans ?_ (IsColimit.comp_coconePointsIsoOfNatIso_hom hL hR
      (asIso (Functor.whiskerLeft D γ)) k).symm
    exact γ.naturality (colimit.ι D k)
  rw [this]
  infer_instance

end FilteredDescent

section CoproductPreservation

open ZeroObject

/-- Abstract form of the embedded base case, left version: a
morphism satisfying the two defining equations of the binary
coproduct comparison for `tensorLeft (indOf.obj a)` at a pair of
embedded objects is invertible, provided the corresponding
comparison in `C` is. -/
lemma isIso_of_coprod_eq_whiskerLeft_indOf
    [SmallCategory C] [MonoidalCategory C] [HasFiniteColimits C]
    (a x y : C)
    (w : a ⊗ x ⨿ a ⊗ y ⟶ a ⊗ (x ⨿ y)) [IsIso w]
    (hw₁ : coprod.inl ≫ w = a ◁ coprod.inl)
    (hw₂ : coprod.inr ≫ w = a ◁ coprod.inr)
    (v : (indOf.obj a ⊗ indOf.obj x) ⨿ (indOf.obj a ⊗ indOf.obj y) ⟶
      indOf.obj a ⊗ (indOf.obj x ⨿ indOf.obj y))
    (hv₁ : coprod.inl ≫ v = indOf.obj a ◁ coprod.inl)
    (hv₂ : coprod.inr ≫ v = indOf.obj a ◁ coprod.inr) :
    IsIso v := by
  have nat₁ := indOfTensorIso_hom_natural_right a
    (coprod.inl : x ⟶ x ⨿ y)
  have nat₂ := indOfTensorIso_hom_natural_right a
    (coprod.inr : y ⟶ x ⨿ y)
  have key : v =
      coprod.map (indOfTensorIso a x).hom (indOfTensorIso a y).hom ≫
      coprodComparison indOf (a ⊗ x) (a ⊗ y) ≫
      indOf.map w ≫
      (indOfTensorIso a (x ⨿ y)).inv ≫
      (indOf.obj a ◁ inv (coprodComparison indOf x y)) := by
    apply coprod.hom_ext
    · rw [hv₁, coprod.inl_map_assoc, coprodComparison_inl_assoc,
        ← Functor.map_comp_assoc, hw₁, ← reassoc_of% nat₁,
        Iso.hom_inv_id_assoc, ← MonoidalCategory.whiskerLeft_comp,
        map_inl_inv_coprodComparison]
    · rw [hv₂, coprod.inr_map_assoc, coprodComparison_inr_assoc,
        ← Functor.map_comp_assoc, hw₂, ← reassoc_of% nat₂,
        Iso.hom_inv_id_assoc, ← MonoidalCategory.whiskerLeft_comp,
        map_inr_inv_coprodComparison]
  rw [key]
  infer_instance

/-- Abstract form of the embedded base case, right version. -/
lemma isIso_of_coprod_eq_whiskerRight_indOf
    [SmallCategory C] [MonoidalCategory C] [HasFiniteColimits C]
    (a x y : C)
    (w : x ⊗ a ⨿ y ⊗ a ⟶ (x ⨿ y) ⊗ a) [IsIso w]
    (hw₁ : coprod.inl ≫ w = coprod.inl ▷ a)
    (hw₂ : coprod.inr ≫ w = coprod.inr ▷ a)
    (v : (indOf.obj x ⊗ indOf.obj a) ⨿ (indOf.obj y ⊗ indOf.obj a) ⟶
      (indOf.obj x ⨿ indOf.obj y) ⊗ indOf.obj a)
    (hv₁ : coprod.inl ≫ v = coprod.inl ▷ indOf.obj a)
    (hv₂ : coprod.inr ≫ v = coprod.inr ▷ indOf.obj a) :
    IsIso v := by
  have nat₁ := indOfTensorIso_hom_natural_left
    (coprod.inl : x ⟶ x ⨿ y) a
  have nat₂ := indOfTensorIso_hom_natural_left
    (coprod.inr : y ⟶ x ⨿ y) a
  have key : v =
      coprod.map (indOfTensorIso x a).hom (indOfTensorIso y a).hom ≫
      coprodComparison indOf (x ⊗ a) (y ⊗ a) ≫
      indOf.map w ≫
      (indOfTensorIso (x ⨿ y) a).inv ≫
      (inv (coprodComparison indOf x y) ▷ indOf.obj a) := by
    apply coprod.hom_ext
    · rw [hv₁, coprod.inl_map_assoc, coprodComparison_inl_assoc,
        ← Functor.map_comp_assoc, hw₁, ← reassoc_of% nat₁,
        Iso.hom_inv_id_assoc, ← MonoidalCategory.comp_whiskerRight,
        map_inl_inv_coprodComparison]
    · rw [hv₂, coprod.inr_map_assoc, coprodComparison_inr_assoc,
        ← Functor.map_comp_assoc, hw₂, ← reassoc_of% nat₂,
        Iso.hom_inv_id_assoc, ← MonoidalCategory.comp_whiskerRight,
        map_inr_inv_coprodComparison]
  rw [key]
  infer_instance

-- Raised budget: the biproduct-preservation instances for
-- `tensorLeft a` are assembled by instance search through the
-- finite-biproduct hierarchy of `C`, and the two comparison maps
-- are then unified across the transported tensor of `Ind C`.
/-- The embedded base case, left version: the binary coproduct
comparison for tensoring on the left by an embedded object is
invertible at a pair of embedded objects. -/
lemma isIso_coprodComparison_tensorLeft_indOf₀
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [MonoidalPreadditive C]
    (a x y : C) :
    IsIso (coprodComparison (tensorLeft (indOf.obj a))
      (indOf.obj x) (indOf.obj y)) := by
  haveI : HasFiniteBiproducts C :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  haveI : HasBinaryBiproducts C :=
    hasBinaryBiproducts_of_finite_biproducts C
  haveI : PreservesBiproductsOfShape WalkingPair (tensorLeft a) :=
    PreservesFiniteBiproducts.preserves
  haveI := preservesBinaryBiproducts_of_preservesBiproducts
    (tensorLeft a)
  haveI := preservesBinaryCoproducts_of_preservesBinaryBiproducts
    (tensorLeft a)
  exact isIso_of_coprod_eq_whiskerLeft_indOf a x y
    (PreservesColimitPair.iso (tensorLeft a) x y).hom
    (coprodComparison_inl (tensorLeft a))
    (coprodComparison_inr (tensorLeft a))
    (coprodComparison (tensorLeft (indOf.obj a)) (indOf.obj x)
      (indOf.obj y))
    (coprodComparison_inl (tensorLeft (indOf.obj a)))
    (coprodComparison_inr (tensorLeft (indOf.obj a)))

-- Raised budget: the mirror of the left version, with the same
-- biproduct-preservation search for `tensorRight a`.
/-- The embedded base case, right version. -/
lemma isIso_coprodComparison_tensorRight_indOf₀
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [MonoidalPreadditive C]
    (a x y : C) :
    IsIso (coprodComparison (tensorRight (indOf.obj a))
      (indOf.obj x) (indOf.obj y)) := by
  haveI : HasFiniteBiproducts C :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  haveI : HasBinaryBiproducts C :=
    hasBinaryBiproducts_of_finite_biproducts C
  haveI : PreservesBiproductsOfShape WalkingPair (tensorRight a) :=
    PreservesFiniteBiproducts.preserves
  haveI := preservesBinaryBiproducts_of_preservesBiproducts
    (tensorRight a)
  haveI := preservesBinaryCoproducts_of_preservesBinaryBiproducts
    (tensorRight a)
  exact isIso_of_coprod_eq_whiskerRight_indOf a x y
    (PreservesColimitPair.iso (tensorRight a) x y).hom
    (coprodComparison_inl (tensorRight a))
    (coprodComparison_inr (tensorRight a))
    (coprodComparison (tensorRight (indOf.obj a)) (indOf.obj x)
      (indOf.obj y))
    (coprodComparison_inl (tensorRight (indOf.obj a)))
    (coprodComparison_inr (tensorRight (indOf.obj a)))

/-- Stage two, left version: the comparison for tensoring on the
left by an embedded object, at one embedded and one arbitrary
argument.  Filtered descent in the second coproduct argument. -/
lemma isIso_coprodComparison_tensorLeft_indOf₁
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [MonoidalPreadditive C]
    (a x : C)
    (Y : Ind C) :
    IsIso (coprodComparison (tensorLeft (indOf.obj a))
      (indOf.obj x) Y) := by
  haveI hL : PreservesFilteredColimits
      (coprodPairFunctor ((Functor.const (Ind C)).obj
        (indOf.obj a ⊗ indOf.obj x)) (tensorLeft (indOf.obj a))) :=
    ⟨fun I _ _ =>
      haveI := IsFiltered.isConnected (C := I)
      haveI := preservesColimitsOfShape_const_of_isConnected
        (𝒜 := Ind C) (J := I) (indOf.obj a ⊗ indOf.obj x)
      preservesColimitsOfShape_coprodPairFunctor _ _⟩
  haveI hR : PreservesFilteredColimits
      (coprodPairFunctor ((Functor.const (Ind C)).obj (indOf.obj x))
        (𝟭 (Ind C)) ⋙ tensorLeft (indOf.obj a)) :=
    ⟨fun I _ _ => by
      haveI := IsFiltered.isConnected (C := I)
      haveI := preservesColimitsOfShape_const_of_isConnected
        (𝒜 := Ind C) (J := I) (indOf.obj x)
      haveI := preservesColimitsOfShape_coprodPairFunctor
        ((Functor.const (Ind C)).obj (indOf.obj x)) (𝟭 (Ind C))
        (J := I)
      infer_instance⟩
  let γ : coprodPairFunctor ((Functor.const (Ind C)).obj
        (indOf.obj a ⊗ indOf.obj x)) (tensorLeft (indOf.obj a)) ⟶
      coprodPairFunctor ((Functor.const (Ind C)).obj (indOf.obj x))
        (𝟭 (Ind C)) ⋙ tensorLeft (indOf.obj a) :=
    { app := fun B => coprod.desc
        (indOf.obj a ◁ (coprod.inl : indOf.obj x ⟶ indOf.obj x ⨿ B))
        (indOf.obj a ◁ (coprod.inr : B ⟶ indOf.obj x ⨿ B))
      naturality := fun B B' u => by
        show coprod.map (𝟙 (indOf.obj a ⊗ indOf.obj x))
            (indOf.obj a ◁ u) ≫
            coprod.desc (indOf.obj a ◁ coprod.inl)
              (indOf.obj a ◁ coprod.inr) =
          coprod.desc (indOf.obj a ◁ coprod.inl)
              (indOf.obj a ◁ coprod.inr) ≫
            (indOf.obj a ◁ coprod.map (𝟙 (indOf.obj x)) u)
        simp only [coprod.map_desc, coprod.desc_comp, Category.id_comp,
          ← MonoidalCategory.whiskerLeft_comp, coprod.inl_map,
          coprod.inr_map] }
  have h := isIso_app_of_isIso_indOf γ
    (fun c => isIso_coprodComparison_tensorLeft_indOf₀ a x c) Y
  exact h

/-- Stage two, right version. -/
lemma isIso_coprodComparison_tensorRight_indOf₁
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [MonoidalPreadditive C]
    (a x : C)
    (Y : Ind C) :
    IsIso (coprodComparison (tensorRight (indOf.obj a))
      (indOf.obj x) Y) := by
  haveI hL : PreservesFilteredColimits
      (coprodPairFunctor ((Functor.const (Ind C)).obj
        (indOf.obj x ⊗ indOf.obj a)) (tensorRight (indOf.obj a))) :=
    ⟨fun I _ _ =>
      haveI := IsFiltered.isConnected (C := I)
      haveI := preservesColimitsOfShape_const_of_isConnected
        (𝒜 := Ind C) (J := I) (indOf.obj x ⊗ indOf.obj a)
      preservesColimitsOfShape_coprodPairFunctor _ _⟩
  haveI hR : PreservesFilteredColimits
      (coprodPairFunctor ((Functor.const (Ind C)).obj (indOf.obj x))
        (𝟭 (Ind C)) ⋙ tensorRight (indOf.obj a)) :=
    ⟨fun I _ _ => by
      haveI := IsFiltered.isConnected (C := I)
      haveI := preservesColimitsOfShape_const_of_isConnected
        (𝒜 := Ind C) (J := I) (indOf.obj x)
      haveI := preservesColimitsOfShape_coprodPairFunctor
        ((Functor.const (Ind C)).obj (indOf.obj x)) (𝟭 (Ind C))
        (J := I)
      infer_instance⟩
  let γ : coprodPairFunctor ((Functor.const (Ind C)).obj
        (indOf.obj x ⊗ indOf.obj a)) (tensorRight (indOf.obj a)) ⟶
      coprodPairFunctor ((Functor.const (Ind C)).obj (indOf.obj x))
        (𝟭 (Ind C)) ⋙ tensorRight (indOf.obj a) :=
    { app := fun B => coprod.desc
        ((coprod.inl : indOf.obj x ⟶ indOf.obj x ⨿ B) ▷ indOf.obj a)
        ((coprod.inr : B ⟶ indOf.obj x ⨿ B) ▷ indOf.obj a)
      naturality := fun B B' u => by
        show coprod.map (𝟙 (indOf.obj x ⊗ indOf.obj a))
            (u ▷ indOf.obj a) ≫
            coprod.desc (coprod.inl ▷ indOf.obj a)
              (coprod.inr ▷ indOf.obj a) =
          coprod.desc (coprod.inl ▷ indOf.obj a)
              (coprod.inr ▷ indOf.obj a) ≫
            (coprod.map (𝟙 (indOf.obj x)) u ▷ indOf.obj a)
        simp only [coprod.map_desc, coprod.desc_comp, Category.id_comp,
          ← MonoidalCategory.comp_whiskerRight, coprod.inl_map,
          coprod.inr_map] }
  have h := isIso_app_of_isIso_indOf γ
    (fun c => isIso_coprodComparison_tensorRight_indOf₀ a x c) Y
  exact h

/-- Stage three, left version: descent in the first coproduct
argument. -/
lemma isIso_coprodComparison_tensorLeft_indOf₂
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [MonoidalPreadditive C]
    (a : C)
    (X Y : Ind C) :
    IsIso (coprodComparison (tensorLeft (indOf.obj a)) X Y) := by
  haveI hL : PreservesFilteredColimits
      (coprodPairFunctor (tensorLeft (indOf.obj a))
        ((Functor.const (Ind C)).obj (indOf.obj a ⊗ Y))) :=
    ⟨fun I _ _ =>
      haveI := IsFiltered.isConnected (C := I)
      haveI := preservesColimitsOfShape_const_of_isConnected
        (𝒜 := Ind C) (J := I) (indOf.obj a ⊗ Y)
      preservesColimitsOfShape_coprodPairFunctor _ _⟩
  haveI hR : PreservesFilteredColimits
      (coprodPairFunctor (𝟭 (Ind C))
        ((Functor.const (Ind C)).obj Y) ⋙
        tensorLeft (indOf.obj a)) :=
    ⟨fun I _ _ => by
      haveI := IsFiltered.isConnected (C := I)
      haveI := preservesColimitsOfShape_const_of_isConnected
        (𝒜 := Ind C) (J := I) Y
      haveI := preservesColimitsOfShape_coprodPairFunctor
        (𝟭 (Ind C)) ((Functor.const (Ind C)).obj Y) (J := I)
      infer_instance⟩
  let γ : coprodPairFunctor (tensorLeft (indOf.obj a))
        ((Functor.const (Ind C)).obj (indOf.obj a ⊗ Y)) ⟶
      coprodPairFunctor (𝟭 (Ind C))
        ((Functor.const (Ind C)).obj Y) ⋙
        tensorLeft (indOf.obj a) :=
    { app := fun B => coprod.desc
        (indOf.obj a ◁ (coprod.inl : B ⟶ B ⨿ Y))
        (indOf.obj a ◁ (coprod.inr : Y ⟶ B ⨿ Y))
      naturality := fun B B' u => by
        show coprod.map (indOf.obj a ◁ u)
            (𝟙 (indOf.obj a ⊗ Y)) ≫
            coprod.desc (indOf.obj a ◁ coprod.inl)
              (indOf.obj a ◁ coprod.inr) =
          coprod.desc (indOf.obj a ◁ coprod.inl)
              (indOf.obj a ◁ coprod.inr) ≫
            (indOf.obj a ◁ coprod.map u (𝟙 Y))
        simp only [coprod.map_desc, coprod.desc_comp, Category.id_comp,
          ← MonoidalCategory.whiskerLeft_comp, coprod.inl_map,
          coprod.inr_map] }
  have h := isIso_app_of_isIso_indOf γ
    (fun c => isIso_coprodComparison_tensorLeft_indOf₁ a c Y) X
  exact h

/-- Stage three, right version. -/
lemma isIso_coprodComparison_tensorRight_indOf₂
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [MonoidalPreadditive C]
    (a : C)
    (X Y : Ind C) :
    IsIso (coprodComparison (tensorRight (indOf.obj a)) X Y) := by
  haveI hL : PreservesFilteredColimits
      (coprodPairFunctor (tensorRight (indOf.obj a))
        ((Functor.const (Ind C)).obj (Y ⊗ indOf.obj a))) :=
    ⟨fun I _ _ =>
      haveI := IsFiltered.isConnected (C := I)
      haveI := preservesColimitsOfShape_const_of_isConnected
        (𝒜 := Ind C) (J := I) (Y ⊗ indOf.obj a)
      preservesColimitsOfShape_coprodPairFunctor _ _⟩
  haveI hR : PreservesFilteredColimits
      (coprodPairFunctor (𝟭 (Ind C))
        ((Functor.const (Ind C)).obj Y) ⋙
        tensorRight (indOf.obj a)) :=
    ⟨fun I _ _ => by
      haveI := IsFiltered.isConnected (C := I)
      haveI := preservesColimitsOfShape_const_of_isConnected
        (𝒜 := Ind C) (J := I) Y
      haveI := preservesColimitsOfShape_coprodPairFunctor
        (𝟭 (Ind C)) ((Functor.const (Ind C)).obj Y) (J := I)
      infer_instance⟩
  let γ : coprodPairFunctor (tensorRight (indOf.obj a))
        ((Functor.const (Ind C)).obj (Y ⊗ indOf.obj a)) ⟶
      coprodPairFunctor (𝟭 (Ind C))
        ((Functor.const (Ind C)).obj Y) ⋙
        tensorRight (indOf.obj a) :=
    { app := fun B => coprod.desc
        ((coprod.inl : B ⟶ B ⨿ Y) ▷ indOf.obj a)
        ((coprod.inr : Y ⟶ B ⨿ Y) ▷ indOf.obj a)
      naturality := fun B B' u => by
        show coprod.map (u ▷ indOf.obj a)
            (𝟙 (Y ⊗ indOf.obj a)) ≫
            coprod.desc (coprod.inl ▷ indOf.obj a)
              (coprod.inr ▷ indOf.obj a) =
          coprod.desc (coprod.inl ▷ indOf.obj a)
              (coprod.inr ▷ indOf.obj a) ≫
            (coprod.map u (𝟙 Y) ▷ indOf.obj a)
        simp only [coprod.map_desc, coprod.desc_comp, Category.id_comp,
          ← MonoidalCategory.comp_whiskerRight, coprod.inl_map,
          coprod.inr_map] }
  have h := isIso_app_of_isIso_indOf γ
    (fun c => isIso_coprodComparison_tensorRight_indOf₁ a c Y) X
  exact h

/-- **The binary coproduct comparison for left tensoring in `Ind C`
is invertible**: final descent in the tensoring object. -/
lemma isIso_coprodComparison_tensorLeft
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [MonoidalPreadditive C]
    (A X Y : Ind C) :
    IsIso (coprodComparison (tensorLeft A) X Y) := by
  haveI hL : PreservesFilteredColimits
      (coprodPairFunctor (tensorRight X) (tensorRight Y)) :=
    ⟨fun I _ _ => preservesColimitsOfShape_coprodPairFunctor _ _⟩
  let γ : coprodPairFunctor (tensorRight X) (tensorRight Y) ⟶
      tensorRight (X ⨿ Y) :=
    { app := fun B => coprod.desc
        (B ◁ (coprod.inl : X ⟶ X ⨿ Y))
        (B ◁ (coprod.inr : Y ⟶ X ⨿ Y))
      naturality := fun B B' u => by
        show coprod.map (u ▷ X) (u ▷ Y) ≫
            coprod.desc (B' ◁ coprod.inl) (B' ◁ coprod.inr) =
          coprod.desc (B ◁ coprod.inl) (B ◁ coprod.inr) ≫
            (u ▷ (X ⨿ Y))
        simp only [coprod.map_desc, coprod.desc_comp,
          whisker_exchange] }
  have h := isIso_app_of_isIso_indOf γ
    (fun c => isIso_coprodComparison_tensorLeft_indOf₂ c X Y) A
  exact h

/-- **The binary coproduct comparison for right tensoring in
`Ind C` is invertible**. -/
lemma isIso_coprodComparison_tensorRight
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [MonoidalPreadditive C]
    (A X Y : Ind C) :
    IsIso (coprodComparison (tensorRight A) X Y) := by
  haveI hL : PreservesFilteredColimits
      (coprodPairFunctor (tensorLeft X) (tensorLeft Y)) :=
    ⟨fun I _ _ => preservesColimitsOfShape_coprodPairFunctor _ _⟩
  let γ : coprodPairFunctor (tensorLeft X) (tensorLeft Y) ⟶
      tensorLeft (X ⨿ Y) :=
    { app := fun B => coprod.desc
        ((coprod.inl : X ⟶ X ⨿ Y) ▷ B)
        ((coprod.inr : Y ⟶ X ⨿ Y) ▷ B)
      naturality := fun B B' u => by
        show coprod.map (X ◁ u) (Y ◁ u) ≫
            coprod.desc (coprod.inl ▷ B') (coprod.inr ▷ B') =
          coprod.desc (coprod.inl ▷ B) (coprod.inr ▷ B) ≫
            ((X ⨿ Y) ◁ u)
        simp only [coprod.map_desc, coprod.desc_comp,
          whisker_exchange] }
  have h := isIso_app_of_isIso_indOf γ
    (fun c => isIso_coprodComparison_tensorRight_indOf₂ c X Y) A
  exact h

/-- An object that is both initial and terminal is a zero object. -/
lemma isZero_of_isInitial_isTerminal {𝒜 : Type*} [Category 𝒜]
    {X : 𝒜} (hI : IsInitial X) (hT : IsTerminal X) : IsZero X :=
  ⟨fun Y => ⟨⟨⟨hI.to Y⟩, fun f => hI.hom_ext f _⟩⟩,
    fun Y => ⟨⟨⟨hT.from Y⟩, fun f => hT.hom_ext f _⟩⟩⟩

/-- The embedding `C ⥤ Ind C` carries zero objects to zero objects:
it preserves the initial and the terminal object. -/
lemma isZero_indOf [SmallCategory C]
    {W : C} (hW : IsZero W) :
    IsZero (indOf.obj W) :=
  isZero_of_isInitial_isTerminal
    (IsInitial.isInitialObj indOf W hW.isInitial)
    (IsTerminal.isTerminalObj indOf W hW.isTerminal)

/-- A colimit all of whose stages vanish vanishes. -/
lemma isZero_colimit_of_isZero
    [SmallCategory C] [Preadditive C] [HasFiniteColimits C]
    {I : Type v} [SmallCategory I]
    (K : I ⥤ Ind C) [HasColimit K] (h : ∀ i, IsZero (K.obj i)) :
    IsZero (colimit K) := by
  rw [IsZero.iff_id_eq_zero]
  apply colimit.hom_ext
  intro j
  rw [Category.comp_id, comp_zero]
  exact (h j).eq_of_src _ _

-- Raised budget: three isomorphisms of ind-objects are chained
-- through the presentation colimit, each elaborated against the
-- transported tensor of `Ind C` and the colimit-preservation
-- instance for `tensorRight`.
/-- Tensoring a vanishing ind-object on the left kills it: descend
along a presentation of the other factor and use that tensoring in
`C` is additive. -/
lemma isZero_tensor_left_ind
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [MonoidalPreadditive C]
    (A : Ind C) {Z : Ind C}
    (hZ : IsZero Z) : IsZero (A ⊗ Z) := by
  haveI : HasFiniteBiproducts C :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  have h0 : IsZero (indOf.obj (0 : C)) := isZero_indOf (isZero_zero C)
  set D : A.presentation.I ⥤ Ind C := A.presentation.F ⋙ indOf
    with hD
  have hpt : ∀ k, IsZero ((D ⋙ tensorRight (indOf.obj 0)).obj k) :=
    fun k => by
      have hz : IsZero (A.presentation.F.obj k ⊗ (0 : C)) :=
        (tensorLeft (A.presentation.F.obj k)).map_isZero
          (isZero_zero C)
      exact IsZero.of_iso (isZero_indOf hz)
        (indOfTensorIso (A.presentation.F.obj k) 0)
  have e₁ : A ⊗ Z ≅ A ⊗ indOf.obj 0 :=
    (tensorLeft A).mapIso (hZ.iso h0)
  have e₂ : A ⊗ indOf.obj (0 : C) ≅ colimit D ⊗ indOf.obj (0 : C) :=
    (tensorRight (indOf.obj (0 : C))).mapIso
      (Ind.colimitPresentationCompYoneda A).symm
  have e₃ : colimit D ⊗ indOf.obj (0 : C) ≅
      colimit (D ⋙ tensorRight (indOf.obj 0)) :=
    preservesColimitIso (tensorRight (indOf.obj (0 : C))) D
  exact IsZero.of_iso (isZero_colimit_of_isZero
    (D ⋙ tensorRight (indOf.obj 0)) hpt) (e₁ ≪≫ e₂ ≪≫ e₃)

-- Raised budget: the mirror of the left version, with the same
-- chain of three isomorphisms through the presentation colimit.
/-- Tensoring a vanishing ind-object on the right kills it. -/
lemma isZero_tensor_right_ind
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [MonoidalPreadditive C]
    (A : Ind C) {Z : Ind C}
    (hZ : IsZero Z) : IsZero (Z ⊗ A) := by
  haveI : HasFiniteBiproducts C :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  have h0 : IsZero (indOf.obj (0 : C)) := isZero_indOf (isZero_zero C)
  set D : A.presentation.I ⥤ Ind C := A.presentation.F ⋙ indOf
    with hD
  have hpt : ∀ k, IsZero ((D ⋙ tensorLeft (indOf.obj 0)).obj k) :=
    fun k => by
      have hz : IsZero ((0 : C) ⊗ A.presentation.F.obj k) :=
        (tensorRight (A.presentation.F.obj k)).map_isZero
          (isZero_zero C)
      exact IsZero.of_iso (isZero_indOf hz)
        (indOfTensorIso 0 (A.presentation.F.obj k))
  have e₁ : Z ⊗ A ≅ indOf.obj 0 ⊗ A :=
    (tensorRight A).mapIso (hZ.iso h0)
  have e₂ : indOf.obj (0 : C) ⊗ A ≅ indOf.obj (0 : C) ⊗ colimit D :=
    (tensorLeft (indOf.obj (0 : C))).mapIso
      (Ind.colimitPresentationCompYoneda A).symm
  have e₃ : indOf.obj (0 : C) ⊗ colimit D ≅
      colimit (D ⋙ tensorLeft (indOf.obj 0)) :=
    preservesColimitIso (tensorLeft (indOf.obj (0 : C))) D
  exact IsZero.of_iso (isZero_colimit_of_isZero
    (D ⋙ tensorLeft (indOf.obj 0)) hpt) (e₁ ≪≫ e₂ ≪≫ e₃)

/-- Left tensoring on `Ind C` preserves zero morphisms. -/
lemma preservesZeroMorphisms_tensorLeft_ind
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [MonoidalPreadditive C]
    (A : Ind C) :
    (tensorLeft A).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_map_zero_object
    ((isZero_tensor_left_ind A (isZero_zero (Ind C))).isoZero)

/-- Right tensoring on `Ind C` preserves zero morphisms. -/
lemma preservesZeroMorphisms_tensorRight_ind
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [MonoidalPreadditive C]
    (A : Ind C) :
    (tensorRight A).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_map_zero_object
    ((isZero_tensor_right_ind A (isZero_zero (Ind C))).isoZero)

/-- Left tensoring on `Ind C` preserves binary coproducts. -/
lemma preservesBinaryCoproducts_tensorLeft_ind
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [MonoidalPreadditive C]
    (A : Ind C) :
    PreservesColimitsOfShape (Discrete WalkingPair)
      (tensorLeft A) where
  preservesColimit {K} := by
    haveI := isIso_coprodComparison_tensorLeft A
      (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)
    haveI := PreservesColimitPair.of_iso_coprod_comparison
      (tensorLeft A) (K.obj ⟨WalkingPair.left⟩)
      (K.obj ⟨WalkingPair.right⟩)
    exact preservesColimit_of_iso_diagram _ (diagramIsoPair K).symm

/-- Right tensoring on `Ind C` preserves binary coproducts. -/
lemma preservesBinaryCoproducts_tensorRight_ind
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [MonoidalPreadditive C]
    (A : Ind C) :
    PreservesColimitsOfShape (Discrete WalkingPair)
      (tensorRight A) where
  preservesColimit {K} := by
    haveI := isIso_coprodComparison_tensorRight A
      (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)
    haveI := PreservesColimitPair.of_iso_coprod_comparison
      (tensorRight A) (K.obj ⟨WalkingPair.left⟩)
      (K.obj ⟨WalkingPair.right⟩)
    exact preservesColimit_of_iso_diagram _ (diagramIsoPair K).symm

/-- Left tensoring on `Ind C` is additive. -/
instance tensorLeft_ind_additive
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [MonoidalPreadditive C]
    (A : Ind C) :
    (tensorLeft A).Additive := by
  haveI : HasBinaryBiproducts (Ind C) :=
    hasBinaryBiproducts_of_finite_biproducts (Ind C)
  haveI := preservesZeroMorphisms_tensorLeft_ind A
  haveI := preservesBinaryCoproducts_tensorLeft_ind A
  haveI := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (tensorLeft A)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Right tensoring on `Ind C` is additive. -/
instance tensorRight_ind_additive
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [MonoidalPreadditive C]
    (A : Ind C) :
    (tensorRight A).Additive := by
  haveI : HasBinaryBiproducts (Ind C) :=
    hasBinaryBiproducts_of_finite_biproducts (Ind C)
  haveI := preservesZeroMorphisms_tensorRight_ind A
  haveI := preservesBinaryCoproducts_tensorRight_ind A
  haveI := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (tensorRight A)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- **Deligne 2.2, preadditive half**: the transported monoidal
structure on `Ind C` is preadditive — whiskering is additive in each
variable. -/
instance [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [MonoidalPreadditive C] :
    MonoidalPreadditive (Ind C) where
  whiskerLeft_zero {X Y Z} := (tensorLeft X).map_zero Y Z
  zero_whiskerRight {X Y Z} := (tensorRight X).map_zero Y Z
  whiskerLeft_add {X _ _} _ _ := (tensorLeft X).map_add
  add_whiskerRight {X _ _} _ _ := (tensorRight X).map_add

end CoproductPreservation

section AcceptanceTests

/- Instance synthesis is what is being tested; the data is chosen by
colimit machinery, hence `noncomputable`. -/

noncomputable example
    [SmallCategory C] [MonoidalCategory C]
    (X : Ind C) :
    PreservesFilteredColimits (tensorLeft X) :=
  inferInstance

noncomputable example
    [SmallCategory C] [MonoidalCategory C]
    (X : Ind C) :
    PreservesFilteredColimits (tensorRight X) :=
  inferInstance

noncomputable example
    [SmallCategory C] [MonoidalCategory C]
    [Preadditive C] [HasFiniteColimits C]
    [MonoidalPreadditive C] : MonoidalPreadditive (Ind C) :=
  inferInstance

noncomputable example
    [SmallCategory C] [MonoidalCategory C]
    [Preadditive C] [HasFiniteColimits C]
    [MonoidalPreadditive C] (X : Ind C) :
    PreservesFiniteCoproducts (tensorLeft X) :=
  inferInstance

noncomputable example
    [SmallCategory C] [MonoidalCategory C]
    [Preadditive C] [HasFiniteColimits C]
    [MonoidalPreadditive C] (X : Ind C) :
    PreservesFiniteCoproducts (tensorRight X) :=
  inferInstance

end AcceptanceTests

end

end RS
