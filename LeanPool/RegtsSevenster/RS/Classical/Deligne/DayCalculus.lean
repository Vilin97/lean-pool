/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.DayType

/-!
# The corepresentable calculus of Day convolution on `Type`

Over a small monoidal category `D`, the Day-convolution monoidal
structure on `D ⊛⥤ Type v` set up in `RS.Classical.Deligne.DayType`
interacts with corepresentables in the classical way.  This file
records:

* `RS.dayCoyonedaIso`: the Day tensor of the corepresentable functors
  at `a` and `b` is the corepresentable functor at `a ⊗ b` (the
  co-Yoneda computation for Day convolution);
* `RS.dayUnitIso`: the Day unit is the corepresentable functor at
  `𝟙_ D`;
* preservation of all `v`-small colimits by `tensorLeft F` and
  `tensorRight F` on `D ⊛⥤ Type v`, for every `F`.

The two isomorphisms follow from uniqueness of corepresenting objects:
both sides corepresent evaluation of the underlying functor at the
relevant object of `D`.  The preservation instances are obtained by
writing Day tensoring, on underlying functors, as an external-product
functor followed by the left Kan extension functor along `tensor D`;
the former preserves colimits pointwise because tensoring in `Type v`
does, and the latter is a left adjoint.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory MonoidalCategory.DayFunctor Limits
open scoped MonoidalCategory.ExternalProduct

universe v

noncomputable section

variable {D : Type v}

/-- Evaluation at `d` of the underlying functor, as a `Type`-valued
functor on `D ⊛⥤ Type v`.  Every corepresentability statement in this
file corepresents a functor of this shape. -/
def dayEvaluation [SmallCategory D] [MonoidalCategory D]
    (d : D) : (D ⊛⥤ Type v) ⥤ Type v :=
  (equiv D (Type v)).functor ⋙ (evaluation D (Type v)).obj d

/-- The corepresentable Day functor at `c` corepresents evaluation at
`c`: the Yoneda lemma, read through the `DayFunctor` synonym. -/
def coyonedaDayCorepresentableBy [SmallCategory D] [MonoidalCategory D]
    (c : D) :
    (dayEvaluation c).CorepresentableBy
      (DayFunctor.mk (coyoneda.obj (Opposite.op c))) where
  homEquiv {F} :=
    { toFun f := coyonedaEquiv (X := c) (F := F.functor) f.natTrans
      invFun x := .mk (coyonedaEquiv.symm x)
      left_inv f := by
        ext1
        exact coyonedaEquiv.symm_apply_apply f.natTrans
      right_inv x := by
        exact (coyonedaEquiv (X := c) (F := F.functor)).apply_symm_apply x }
  homEquiv_comp g f := by
    have h : coyonedaEquiv ((f ≫ g).natTrans) =
        g.natTrans.app c (coyonedaEquiv f.natTrans) := by
      rw [comp_natTrans, coyonedaEquiv_comp]
    exact h

/-- The Day tensor of the corepresentables at `a` and `b` corepresents
evaluation at `a ⊗ b`: maps out of it are transformations out of the
external product of the two corepresentables, which is definitionally
the corepresentable of the product category at `(a, b)`, so the Yoneda
lemma evaluates.  This is the co-Yoneda computation for Day
convolution. -/
def dayCoyonedaCorepresentableBy [SmallCategory D] [MonoidalCategory D]
    (a b : D) :
    (dayEvaluation (a ⊗ b)).CorepresentableBy
      (DayFunctor.mk (coyoneda.obj (Opposite.op a)) ⊗
        DayFunctor.mk (coyoneda.obj (Opposite.op b))) where
  homEquiv {F} :=
    ({ toFun := Hom.natTrans
       invFun := .mk
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl } :
        (DayFunctor.mk (coyoneda.obj (Opposite.op a)) ⊗
            DayFunctor.mk (coyoneda.obj (Opposite.op b)) ⟶ F) ≃
          ((DayFunctor.mk (coyoneda.obj (Opposite.op a)) ⊗
            DayFunctor.mk (coyoneda.obj (Opposite.op b))).functor ⟶
            F.functor)).trans <|
      (Functor.homEquivOfIsLeftKanExtension _
        (η (DayFunctor.mk (coyoneda.obj (Opposite.op a)))
          (DayFunctor.mk (coyoneda.obj (Opposite.op b))))
        F.functor).trans
        (coyonedaEquiv (C := D × D) (X := ((a, b) : D × D))
          (F := tensor D ⋙ F.functor))
  homEquiv_comp {F F'} g f := by
    change coyonedaEquiv (C := D × D) (X := ((a, b) : D × D))
      (F := tensor D ⋙ F'.functor)
      (η (DayFunctor.mk (coyoneda.obj (Opposite.op a)))
          (DayFunctor.mk (coyoneda.obj (Opposite.op b))) ≫
        Functor.whiskerLeft (tensor D) (f ≫ g).natTrans) = _
    erw [comp_natTrans, Functor.whiskerLeft_comp, ← Category.assoc,
      coyonedaEquiv_comp]

/-- Day convolution of corepresentables: the Day tensor of the
corepresentable functors at `a` and `b` is the corepresentable functor
at `a ⊗ b`. -/
def dayCoyonedaIso [SmallCategory D] [MonoidalCategory D]
    (a b : D) :
    DayFunctor.mk (coyoneda.obj (Opposite.op a)) ⊗
      DayFunctor.mk (coyoneda.obj (Opposite.op b)) ≅
    DayFunctor.mk (coyoneda.obj (Opposite.op (a ⊗ b))) :=
  (dayCoyonedaCorepresentableBy a b).uniqueUpToIso
    (coyonedaDayCorepresentableBy (a ⊗ b))

/-- The Day unit corepresents evaluation at `𝟙_ D`: a map out of it is
determined by an element of `F.functor.obj (𝟙_ D)`, via the universal
property of the unit as a left Kan extension along
`fromPUnit (𝟙_ D)`. -/
def dayUnitCorepresentableBy [SmallCategory D] [MonoidalCategory D] :
    (dayEvaluation (𝟙_ D)).CorepresentableBy (𝟙_ (D ⊛⥤ Type v)) where
  homEquiv {F} :=
    { toFun f := f.natTrans.app (𝟙_ D) (ν D (Type v) PUnit.unit)
      invFun x := unitDesc (TypeCat.ofHom fun _ => x)
      left_inv f := by
        refine unit_hom_ext ?_
        rw [ν_comp_unitDesc]
        refine ConcreteCategory.hom_ext _ _ fun u => ?_
        cases u
        rfl
      right_inv x := ConcreteCategory.congr_hom
        (ν_comp_unitDesc (TypeCat.ofHom fun _ => x)) PUnit.unit }
  homEquiv_comp g f := rfl

variable (D) in
/-- The Day unit is the corepresentable functor at the monoidal unit of
`D`. -/
def dayUnitIso [SmallCategory D] [MonoidalCategory D] :
    𝟙_ (MonoidalCategory.DayFunctor D (Type v)) ≅
      DayFunctor.mk (coyoneda.obj (Opposite.op (𝟙_ D))) :=
  dayUnitCorepresentableBy.uniqueUpToIso
    (coyonedaDayCorepresentableBy (𝟙_ D))

section Preservation

attribute [local instance] dayConv

/-- Fixing the left factor of the external product gives a functor in
the right factor. -/
def externalLeftFunctor [SmallCategory D]
    (K : D ⥤ Type v) :
    (D ⥤ Type v) ⥤ D × D ⥤ Type v :=
  Prod.sectR K (D ⥤ Type v) ⋙ externalProductBifunctor D D (Type v)

/-- Fixing the right factor of the external product gives a functor in
the left factor. -/
def externalRightFunctor [SmallCategory D]
    (K : D ⥤ Type v) :
    (D ⥤ Type v) ⥤ D × D ⥤ Type v :=
  Prod.sectL (D ⥤ Type v) K ⋙ externalProductBifunctor D D (Type v)

/-- Pointwise, the external product with a fixed left factor is
tensoring on the left in `Type v`. -/
def externalLeftFunctorEvaluationIso [SmallCategory D]
    (K : D ⥤ Type v) (p : D × D) :
    (evaluation D (Type v)).obj p.2 ⋙ tensorLeft (K.obj p.1) ≅
      externalLeftFunctor K ⋙ (evaluation (D × D) (Type v)).obj p :=
  NatIso.ofComponents (fun G => Iso.refl _) (by
    intro G G' g
    dsimp [externalLeftFunctor, Prod.sectR]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Pointwise, the external product with a fixed right factor is
tensoring on the right in `Type v`. -/
def externalRightFunctorEvaluationIso [SmallCategory D]
    (K : D ⥤ Type v) (p : D × D) :
    (evaluation D (Type v)).obj p.1 ⋙ tensorRight (K.obj p.2) ≅
      externalRightFunctor K ⋙ (evaluation (D × D) (Type v)).obj p :=
  NatIso.ofComponents (fun G => Iso.refl _) (by
    intro G G' g
    dsimp [externalRightFunctor, Prod.sectL]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The external product with a fixed left factor preserves colimits in
the right factor. -/
instance externalLeftFunctor_preservesColimits [SmallCategory D]
    (K : D ⥤ Type v) :
    PreservesColimitsOfSize.{v, v} (externalLeftFunctor K) where
  preservesColimitsOfShape {J} _ :=
    preservesColimitsOfShape_of_evaluation _ J fun p =>
      preservesColimitsOfShape_of_natIso
        (externalLeftFunctorEvaluationIso K p)

/-- The external product with a fixed right factor preserves colimits
in the left factor. -/
instance externalRightFunctor_preservesColimits [SmallCategory D]
    (K : D ⥤ Type v) :
    PreservesColimitsOfSize.{v, v} (externalRightFunctor K) where
  preservesColimitsOfShape {J} _ :=
    preservesColimitsOfShape_of_evaluation _ J fun p =>
      preservesColimitsOfShape_of_natIso
        (externalRightFunctorEvaluationIso K p)

/-- The Day tensor, on underlying functors, is the left Kan extension
of the external product along `tensor D`. -/
@[simps]
def tensorObjLanIso [SmallCategory D] [MonoidalCategory D]
    (F G : D ⊛⥤ Type v) :
    (F ⊗ G).functor ≅ (tensor D).lan.obj (F.functor ⊠ G.functor) where
  hom := Functor.descOfIsLeftKanExtension _ (η F G) _
    ((tensor D).lanUnit.app (F.functor ⊠ G.functor))
  inv := Functor.descOfIsLeftKanExtension _
    ((tensor D).lanUnit.app (F.functor ⊠ G.functor)) _ (η F G)
  hom_inv_id := Functor.hom_ext_of_isLeftKanExtension _ (η F G) _ _
    (by simp)
  inv_hom_id := Functor.hom_ext_of_isLeftKanExtension _
    ((tensor D).lanUnit.app (F.functor ⊠ G.functor)) _ _ (by simp)

open scoped CategoryTheory.Prod in
/-- Naturality in the right variable of `RS.tensorObjLanIso`. -/
lemma whiskerLeft_natTrans_tensorObjLanIso_hom
    [SmallCategory D] [MonoidalCategory D]
    (F : D ⊛⥤ Type v)
    {G G' : D ⊛⥤ Type v} (g : G ⟶ G') :
    (F ◁ g).natTrans ≫ (tensorObjLanIso F G').hom =
      (tensorObjLanIso F G).hom ≫ (tensor D).lan.map
        ((externalProductBifunctor D D (Type v)).map
          (𝟙 F.functor ×ₘ g.natTrans)) := by
  refine Functor.hom_ext_of_isLeftKanExtension _ (η F G) _ _ ?_
  have h₁ : η F G ≫ Functor.whiskerLeft (tensor D) (F ◁ g).natTrans =
      (externalProductBifunctor D D (Type v)).map
        (𝟙 F.functor ×ₘ g.natTrans) ≫ η F G' := by
    rw [natTrans_whiskerLeft]
    exact Functor.descOfIsLeftKanExtension_fac _ _ _ _
  have h₂ := (tensor D).lanUnit.naturality
    ((externalProductBifunctor D D (Type v)).map
      (𝟙 F.functor ×ₘ g.natTrans))
  simp only [Functor.id_map, Functor.comp_map,
    Functor.whiskeringLeft_obj_map] at h₂
  rw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp,
    ← Category.assoc, h₁, Category.assoc,
    tensorObjLanIso_hom, tensorObjLanIso_hom,
    Functor.descOfIsLeftKanExtension_fac,
    Functor.descOfIsLeftKanExtension_fac_assoc]
  exact h₂

open scoped CategoryTheory.Prod in
/-- Naturality in the left variable of `RS.tensorObjLanIso`. -/
lemma whiskerRight_natTrans_tensorObjLanIso_hom
    [SmallCategory D] [MonoidalCategory D]
    (F : D ⊛⥤ Type v)
    {G G' : D ⊛⥤ Type v} (g : G ⟶ G') :
    (g ▷ F).natTrans ≫ (tensorObjLanIso G' F).hom =
      (tensorObjLanIso G F).hom ≫ (tensor D).lan.map
        ((externalProductBifunctor D D (Type v)).map
          (g.natTrans ×ₘ 𝟙 F.functor)) := by
  refine Functor.hom_ext_of_isLeftKanExtension _ (η G F) _ _ ?_
  have h₁ : η G F ≫ Functor.whiskerLeft (tensor D) (g ▷ F).natTrans =
      (externalProductBifunctor D D (Type v)).map
        (g.natTrans ×ₘ 𝟙 F.functor) ≫ η G' F := by
    rw [natTrans_whiskerRight]
    exact Functor.descOfIsLeftKanExtension_fac _ _ _ _
  have h₂ := (tensor D).lanUnit.naturality
    ((externalProductBifunctor D D (Type v)).map
      (g.natTrans ×ₘ 𝟙 F.functor))
  simp only [Functor.id_map, Functor.comp_map,
    Functor.whiskeringLeft_obj_map] at h₂
  rw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp,
    ← Category.assoc, h₁, Category.assoc,
    tensorObjLanIso_hom, tensorObjLanIso_hom,
    Functor.descOfIsLeftKanExtension_fac,
    Functor.descOfIsLeftKanExtension_fac_assoc]
  exact h₂

/-- Day tensoring on the left, transported to the plain functor
category, is the external product followed by left Kan extension along
`tensor D`. -/
def tensorLeftCompIso [SmallCategory D] [MonoidalCategory D]
    (F : D ⊛⥤ Type v) :
    tensorLeft F ⋙ (equiv D (Type v)).functor ≅
      (equiv D (Type v)).functor ⋙
        externalLeftFunctor F.functor ⋙ (tensor D).lan :=
  NatIso.ofComponents (fun G => tensorObjLanIso F G)
    (fun g => whiskerLeft_natTrans_tensorObjLanIso_hom F g)

/-- Day tensoring on the right, transported to the plain functor
category, is the external product followed by left Kan extension along
`tensor D`. -/
def tensorRightCompIso [SmallCategory D] [MonoidalCategory D]
    (F : D ⊛⥤ Type v) :
    tensorRight F ⋙ (equiv D (Type v)).functor ≅
      (equiv D (Type v)).functor ⋙
        externalRightFunctor F.functor ⋙ (tensor D).lan :=
  NatIso.ofComponents (fun G => tensorObjLanIso G F)
    (fun g => whiskerRight_natTrans_tensorObjLanIso_hom F g)

/-- Day tensoring on the left preserves `v`-small colimits: through
`RS.tensorLeftCompIso` it is, up to the tautological equivalence, an
external product followed by a left Kan extension, and both preserve
colimits. -/
noncomputable instance [SmallCategory D] [MonoidalCategory D]
    (F : MonoidalCategory.DayFunctor D (Type v)) :
    Limits.PreservesColimitsOfSize.{v, v} (tensorLeft F) := by
  have : PreservesColimitsOfSize.{v, v}
      ((tensor D).lan (H := Type v)) :=
    ((tensor D).lanAdjunction (Type v)).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{v, v}
      (tensorLeft F ⋙ (equiv D (Type v)).functor) :=
    preservesColimits_of_natIso (tensorLeftCompIso F).symm
  exact preservesColimits_of_reflects_of_preserves _
    (equiv D (Type v)).functor

/-- Day tensoring on the right preserves `v`-small colimits: through
`RS.tensorRightCompIso` it is, up to the tautological equivalence, an
external product followed by a left Kan extension, and both preserve
colimits. -/
noncomputable instance [SmallCategory D] [MonoidalCategory D]
    (F : MonoidalCategory.DayFunctor D (Type v)) :
    Limits.PreservesColimitsOfSize.{v, v} (tensorRight F) := by
  have : PreservesColimitsOfSize.{v, v}
      ((tensor D).lan (H := Type v)) :=
    ((tensor D).lanAdjunction (Type v)).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{v, v}
      (tensorRight F ⋙ (equiv D (Type v)).functor) :=
    preservesColimits_of_natIso (tensorRightCompIso F).symm
  exact preservesColimits_of_reflects_of_preserves _
    (equiv D (Type v)).functor

end Preservation

end

end RS
