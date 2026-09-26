/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.SchurTransport

/-!
# The embedding `C ⥤ Ind C` as a strong braided monoidal functor

`RS.Classical.Deligne.IndSchur` assembles the comparison data of the
embedding `RS.indOf : C ⥤ Ind C` — the unit comparison
`RS.indOfUnitIso`, the tensor comparison `RS.indOfTensorIso`, and their
compatibility with the associator and the braiding.  This file supplies
the two remaining coherences, the unitalities, and packages the whole as
the Mathlib classes:

* `RS.indOfLaxMonoidal` — `indOf` is lax monoidal, with `ε` the forward
  direction of `RS.indOfUnitIso` and `μ` that of `RS.indOfTensorIso`;
* `RS.indOfMonoidal` — the comparisons are isomorphisms, so `indOf` is
  strong monoidal, with `RS.indOfMonoidal_εIso`/`RS.indOfMonoidal_μIso`
  and `RS.indOf_oplax_η`/`RS.indOf_oplax_δ` reading off the packaged
  data;
* `RS.indOfBraided` — and braided, for `C` braided.

The two coherences that `RS.Classical.Deligne.IndSchur` does not
already supply are the unitalities
`RS.indOfUnitIso_hom_leftUnitor` and
`RS.indOfUnitIso_hom_rightUnitor`.  The left one is
`RS.indOf_leftUnitor_hom` of `RS.Classical.Deligne.SchurTransport`,
which also carries the Day-level `RS.dayCoyonedaIso_hom_leftUnitor`
and its Yoneda form `RS.dayYonedaIso_hom_leftUnitor`; this file
supplies the mirror-image right-handed calculus,
`RS.dayCoyonedaIso_hom_rightUnitor` and
`RS.dayYonedaIso_hom_rightUnitor`.

The unitalities are proved the same way as the associativity: the
embedding `RS.indToDay` into the Day presheaf category is fully faithful
and monoidal, so it suffices to prove the corresponding identities for
the Day comparison `RS.dayYonedaIso` and the Day unit `RS.dayUnitIso`.
Those are decided, as everywhere in this lane, by evaluating both sides
on the canonical element `RS.dayCoyonedaUnitElt`: the Day unitors are
characterised on the Kan-extension unit by the `leftUnitor_hom_unit_app`
and `rightUnitor_hom_unit_app` fields of Mathlib's
`CategoryTheory.MonoidalCategory.LawfulDayConvolutionMonoidalCategoryStruct`.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory MonoidalCategory.DayFunctor Limits
open Opposite

universe v

noncomputable section

section DayRightUnitCalculus

attribute [local instance] dayConv dayConvPlain

variable {D : Type v}

/-- Left-whiskering the inverse of `RS.dayUnitIso` carries the canonical
element at `(a, 𝟙_ D)` to the Kan-extension unit element assembled from
the Day-unit element. -/
lemma whiskerLeft_dayUnitIso_inv_app_unitElt
    [SmallCategory D] [MonoidalCategory D]
    (a : D) :
    (DayFunctor.mk (coyoneda.obj (op a)) ◁
        (dayUnitIso D).inv).natTrans.app (a ⊗ 𝟙_ D)
      (dayCoyonedaUnitElt a (𝟙_ D)) =
    (η (DayFunctor.mk (coyoneda.obj (op a)))
      (𝟙_ (D ⊛⥤ Type v))).app (a, 𝟙_ D)
      ((𝟙 a, ν D (Type v) PUnit.unit)) := by
  have h₀ := congrArg (fun t => t.app (a ⊗ 𝟙_ D))
    (natTrans_whiskerLeft (DayFunctor.mk (coyoneda.obj (op a)))
      (dayUnitIso D).inv)
  have h₁ := ConcreteCategory.congr_hom h₀ (dayCoyonedaUnitElt a (𝟙_ D))
  have h₂' := DayConvolution.unit_app_map_app
    (f := 𝟙 ((DayFunctor.mk (coyoneda.obj (op a))).functor))
    (g := (dayUnitIso D).inv.natTrans)
    (x := a) (y := 𝟙_ D)
  have h₂ : (DayConvolution.map
        (𝟙 ((DayFunctor.mk (coyoneda.obj (op a))).functor))
        (dayUnitIso D).inv.natTrans).app
        (a ⊗ 𝟙_ D) (dayCoyonedaUnitElt a (𝟙_ D)) =
      (η (DayFunctor.mk (coyoneda.obj (op a)))
        (𝟙_ (D ⊛⥤ Type v))).app (a, 𝟙_ D)
        ((𝟙 a, (dayUnitIso D).inv.natTrans.app (𝟙_ D) (𝟙 (𝟙_ D)))) :=
    ConcreteCategory.congr_hom h₂'
      ((𝟙 a, 𝟙 (𝟙_ D)) : (a ⟶ a) × (𝟙_ D ⟶ 𝟙_ D))
  rw [h₁]
  refine h₂.trans ?_
  exact congrArg
    (fun z => (η (DayFunctor.mk (coyoneda.obj (op a)))
      (𝟙_ (D ⊛⥤ Type v))).app (a, 𝟙_ D)
      ((𝟙 a, z) :
        (a ⟶ a) × ((𝟙_ (D ⊛⥤ Type v)).functor.obj (𝟙_ D))))
    dayUnitIso_inv_app_id

/-- The Day right unitor, characterised on the Kan-extension unit. -/
lemma dayRightUnitor_hom_unit [SmallCategory D] [MonoidalCategory D]
    (K : D ⊛⥤ Type v) (y : D) :
    (K.functor.obj y ◁ ν D (Type v)) ≫
        (η K (𝟙_ (D ⊛⥤ Type v))).app (y, 𝟙_ D) ≫
        (ρ_ K).hom.natTrans.app (y ⊗ 𝟙_ D) =
      (ρ_ (K.functor.obj y)).hom ≫ K.functor.map (ρ_ y).inv :=
  LawfulDayConvolutionMonoidalCategoryStruct.rightUnitor_hom_unit_app
    (Type v) K y

/-- Evaluation of the Day right unitor on the canonical element built
from the Day-unit element. -/
lemma dayRightUnitor_hom_app_unitElt [SmallCategory D] [MonoidalCategory D]
    (a : D) :
    (ρ_ (DayFunctor.mk (coyoneda.obj (op a)) :
        D ⊛⥤ Type v)).hom.natTrans.app (a ⊗ 𝟙_ D)
      ((η (DayFunctor.mk (coyoneda.obj (op a)))
        (𝟙_ (D ⊛⥤ Type v))).app (a, 𝟙_ D)
        ((𝟙 a, ν D (Type v) PUnit.unit))) = (ρ_ a).inv := by
  have h := ConcreteCategory.congr_hom
    (dayRightUnitor_hom_unit (DayFunctor.mk (coyoneda.obj (op a))) a)
    ((𝟙 a, PUnit.unit) : (a ⟶ a) × PUnit.{v + 1})
  exact h.trans (Category.id_comp _)

/-- **Day convolution of corepresentables intertwines the right
unitor**. -/
lemma dayCoyonedaIso_hom_rightUnitor [SmallCategory D] [MonoidalCategory D]
    (a : D) :
    (dayCoyonedaIso a (𝟙_ D)).hom ≫
        (⟨coyoneda.map ((ρ_ a).inv.op)⟩ :
          DayFunctor.mk (coyoneda.obj (op (a ⊗ 𝟙_ D))) ⟶
            DayFunctor.mk (coyoneda.obj (op a))) =
      (DayFunctor.mk (coyoneda.obj (op a)) ◁ (dayUnitIso D).inv) ≫
        (ρ_ (DayFunctor.mk (coyoneda.obj (op a)) :
          D ⊛⥤ Type v)).hom := by
  apply (dayCoyonedaCorepresentableBy a (𝟙_ D)).homEquiv.injective
  change (coyoneda.map ((ρ_ a).inv.op)).app (a ⊗ 𝟙_ D)
      ((dayCoyonedaIso a (𝟙_ D)).hom.natTrans.app (a ⊗ 𝟙_ D)
        (dayCoyonedaUnitElt a (𝟙_ D))) =
    (ρ_ (DayFunctor.mk (coyoneda.obj (op a)) : D ⊛⥤ Type v)).hom.natTrans.app
      (a ⊗ 𝟙_ D)
      ((DayFunctor.mk (coyoneda.obj (op a)) ◁ (dayUnitIso D).inv).natTrans.app
        (a ⊗ 𝟙_ D) (dayCoyonedaUnitElt a (𝟙_ D)))
  rw [dayCoyonedaIso_hom_app_unitElt,
    whiskerLeft_dayUnitIso_inv_app_unitElt, dayRightUnitor_hom_app_unitElt]
  exact Category.comp_id _

end DayRightUnitCalculus

section YonedaUnitTransport

variable {C : Type v}

/-- The Day unit is the representable presheaf at the unit of `C`: the
Yoneda form of `RS.dayUnitIso`. -/
def dayYonedaUnitIso [SmallCategory C] [MonoidalCategory C] :
    𝟙_ (Cᵒᵖ ⊛⥤ Type v) ≅ DayFunctor.mk (yoneda.obj (𝟙_ C)) :=
  dayUnitIso Cᵒᵖ ≪≫ dayMkIso (Coyoneda.objOpOp (𝟙_ C))

/-- **The Day tensor of representables intertwines the right unitor**:
the Yoneda form of `RS.dayCoyonedaIso_hom_rightUnitor`. -/
lemma dayYonedaIso_hom_rightUnitor [SmallCategory C] [MonoidalCategory C]
    (x : C) :
    (DayFunctor.mk (yoneda.obj x) ◁ (dayYonedaUnitIso (C := C)).hom) ≫
        (dayYonedaIso x (𝟙_ C)).hom ≫ ⟨yoneda.map (ρ_ x).hom⟩ =
      (ρ_ (DayFunctor.mk (yoneda.obj x) : Cᵒᵖ ⊛⥤ Type v)).hom := by
  have s₂ : (⟨coyoneda.map ((ρ_ x).hom.op.op)⟩ :
        DayFunctor.mk (coyoneda.obj (op (op (x ⊗ 𝟙_ C)))) ⟶
          DayFunctor.mk (coyoneda.obj (op (op x)))) ≫
        (dayMkIso (Coyoneda.objOpOp x)).hom =
      (dayMkIso (Coyoneda.objOpOp (x ⊗ 𝟙_ C))).hom ≫
        ⟨yoneda.map (ρ_ x).hom⟩ := by
    ext1
    exact coyoneda_map_op_op_comp_objOpOp_hom (ρ_ x).hom
  have hR : (dayCoyonedaIso (op x) (op (𝟙_ C))).hom ≫
        (⟨coyoneda.map ((ρ_ x).hom.op.op)⟩ :
          DayFunctor.mk (coyoneda.obj (op (op (x ⊗ 𝟙_ C)))) ⟶
            DayFunctor.mk (coyoneda.obj (op (op x)))) =
      (DayFunctor.mk (coyoneda.obj (op (op x))) ◁
          (dayUnitIso Cᵒᵖ).inv) ≫
        (ρ_ (DayFunctor.mk (coyoneda.obj (op (op x))) :
          Cᵒᵖ ⊛⥤ Type v)).hom :=
    dayCoyonedaIso_hom_rightUnitor (D := Cᵒᵖ) (op x)
  have hcomp : ((dayUnitIso Cᵒᵖ).hom ≫
        (dayMkIso (Coyoneda.objOpOp (𝟙_ C))).hom) ≫
        (dayMkIso (Coyoneda.objOpOp (𝟙_ C)).symm).hom =
      (dayUnitIso Cᵒᵖ).hom := by
    rw [Category.assoc, dayMkIso_hom_symm_hom]
    exact Category.comp_id _
  have e₁ : (DayFunctor.mk (yoneda.obj x) ◁
          ((dayUnitIso Cᵒᵖ).hom ≫
            (dayMkIso (Coyoneda.objOpOp (𝟙_ C))).hom)) ≫
        ((dayMkIso (Coyoneda.objOpOp x).symm).hom ⊗ₘ
          (dayMkIso (Coyoneda.objOpOp (𝟙_ C)).symm).hom) =
      (dayMkIso (Coyoneda.objOpOp x).symm).hom ⊗ₘ
        (dayUnitIso Cᵒᵖ).hom := by
    rw [← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp,
      hcomp]
  have e₂ : ((dayMkIso (Coyoneda.objOpOp x).symm).hom ⊗ₘ
          (dayUnitIso Cᵒᵖ).hom) ≫
        (DayFunctor.mk (coyoneda.obj (op (op x))) ◁
          (dayUnitIso Cᵒᵖ).inv) =
      (dayMkIso (Coyoneda.objOpOp x).symm).hom ▷
        (𝟙_ (Cᵒᵖ ⊛⥤ Type v)) := by
    rw [← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom, Iso.hom_inv_id,
      Category.comp_id, MonoidalCategory.tensorHom_id]
  have e₃ : (dayMkIso (Coyoneda.objOpOp x).symm).hom ≫
      (dayMkIso (Coyoneda.objOpOp x)).hom =
      𝟙 (DayFunctor.mk (yoneda.obj x) : Cᵒᵖ ⊛⥤ Type v) :=
    dayMkIso_hom_symm_hom (Coyoneda.objOpOp x).symm
  simp only [dayYonedaUnitIso, dayYonedaIso, Iso.trans_hom, tensorIso_hom,
    Category.assoc]
  rw [← s₂, ← Category.assoc, e₁, reassoc_of% hR, ← Category.assoc, e₂,
    MonoidalCategory.rightUnitor_naturality_assoc, e₃, Category.comp_id]

end YonedaUnitTransport

section IndUnitality

variable {C : Type v}

/-- The embedding into the Day presheaf category carries the unit
comparison to the Day unit: the `RS.dayYonedaUnitIso` reading of
`RS.indToDay_map_indOfUnitIso_hom`. -/
lemma indToDay_map_indOfUnitIso_hom_dayYonedaUnitIso
    [SmallCategory C] [MonoidalCategory C] :
    (indToDay (C := C)).map indOfUnitIso.hom =
      Functor.OplaxMonoidal.η (indToDay (C := C)) ≫
        (dayYonedaUnitIso (C := C)).hom ≫
        (indToDayIndOfIso (𝟙_ C)).inv := by
  rw [indToDay_map_indOfUnitIso_hom, Functor.Monoidal.εIso_inv]
  simp only [dayYonedaUnitIso, Iso.trans_hom, Category.assoc]

/-- **The unit and tensor comparisons satisfy left unitality**: the
left-unitality axiom of the monoidal structure of `indOf`.  This is
`RS.indOf_leftUnitor_hom` read in the direction the `LaxMonoidal`
field wants. -/
lemma indOfUnitIso_hom_leftUnitor [SmallCategory C] [MonoidalCategory C]
    (x : C) :
    (indOfUnitIso.hom ▷ indOf.obj x) ≫
        (indOfTensorIso (𝟙_ C) x).hom ≫ indOf.map (λ_ x).hom =
      (λ_ (indOf.obj x)).hom :=
  (indOf_leftUnitor_hom x).symm

/-- **The unit and tensor comparisons satisfy right unitality**: the
right-unitality axiom of the monoidal structure of `indOf`. -/
lemma indOfUnitIso_hom_rightUnitor [SmallCategory C] [MonoidalCategory C]
    (x : C) :
    (indOf.obj x ◁ indOfUnitIso.hom) ≫
        (indOfTensorIso x (𝟙_ C)).hom ≫ indOf.map (ρ_ x).hom =
      (ρ_ (indOf.obj x)).hom := by
  apply (indToDay (C := C)).map_injective
  rw [Functor.map_comp, Functor.map_comp,
    Functor.Monoidal.map_whiskerLeft (F := indToDay (C := C)),
    Functor.Monoidal.map_rightUnitor (F := indToDay (C := C)),
    indToDay_map_indOfTensorIso_hom,
    indToDay_map_indOfUnitIso_hom_dayYonedaUnitIso]
  simp only [indToDayTensorIso, Iso.trans_hom, Iso.symm_hom,
    tensorIso_hom, Functor.Monoidal.μIso_inv, Category.assoc,
    Functor.Monoidal.μ_δ_assoc]
  have hq : (ρ_ ((indToDay (C := C)).obj (indOf.obj x))).hom =
      ((indToDayIndOfIso x).hom ▷ (𝟙_ (Cᵒᵖ ⊛⥤ Type v))) ≫
        (ρ_ (DayFunctor.mk (yoneda.obj x) : Cᵒᵖ ⊛⥤ Type v)).hom ≫
        (indToDayIndOfIso x).inv := by
    rw [MonoidalCategory.rightUnitor_naturality_assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hright : ((indToDay (C := C)).obj (indOf.obj x) ◁
          (Functor.OplaxMonoidal.η (indToDay (C := C)) ≫
            (dayYonedaUnitIso (C := C)).hom ≫
            (indToDayIndOfIso (𝟙_ C)).inv)) ≫
        ((indToDayIndOfIso x).hom ⊗ₘ (indToDayIndOfIso (𝟙_ C)).hom) =
      ((indToDayIndOfIso x).hom ⊗ₘ
          Functor.OplaxMonoidal.η (indToDay (C := C))) ≫
        (DayFunctor.mk (yoneda.obj x) ◁
          (dayYonedaUnitIso (C := C)).hom) := by
    rw [← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp,
      Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
  have htd : ((indToDay (C := C)).obj (indOf.obj x) ◁
        Functor.OplaxMonoidal.η (indToDay (C := C))) ≫
        ((indToDayIndOfIso x).hom ▷ (𝟙_ (Cᵒᵖ ⊛⥤ Type v))) =
      (indToDayIndOfIso x).hom ⊗ₘ
        Functor.OplaxMonoidal.η (indToDay (C := C)) :=
    (MonoidalCategory.tensorHom_def' _ _).symm
  rw [← comp_indToDayIndOfIso_inv, hq]
  rw [reassoc_of% hright, reassoc_of% htd,
    reassoc_of% dayYonedaIso_hom_rightUnitor x]

end IndUnitality

section Instances

variable {C : Type v}

/-- **The embedding `C ⥤ Ind C` is lax monoidal**: the unit comparison
`RS.indOfUnitIso` and the tensor comparison `RS.indOfTensorIso` satisfy
the five coherences. -/
noncomputable instance indOfLaxMonoidal [SmallCategory C] [MonoidalCategory C] :
    (indOf (C := C)).LaxMonoidal where
  ε := indOfUnitIso.hom
  μ x y := (indOfTensorIso x y).hom
  μ_natural_left f x' := indOfTensorIso_hom_natural_left f x'
  μ_natural_right x' f := indOfTensorIso_hom_natural_right x' f
  associativity x y z := indOfTensorIso_hom_associator x y z
  left_unitality x := (indOfUnitIso_hom_leftUnitor x).symm
  right_unitality x := (indOfUnitIso_hom_rightUnitor x).symm

/-- **The embedding `C ⥤ Ind C` is strong monoidal**: both comparisons
are isomorphisms by construction. -/
noncomputable instance indOfMonoidal
    [SmallCategory C] [MonoidalCategory C] : (indOf (C := C)).Monoidal :=
  haveI : IsIso (Functor.LaxMonoidal.ε (indOf (C := C))) :=
    (indOfUnitIso (C := C)).isIso_hom
  haveI : ∀ x y : C,
      IsIso (Functor.LaxMonoidal.μ (indOf (C := C)) x y) :=
    fun x y => (indOfTensorIso x y).isIso_hom
  Functor.Monoidal.ofLaxMonoidal _

/-- **The embedding `C ⥤ Ind C` is braided**. -/
noncomputable instance indOfBraided [SmallCategory C] [MonoidalCategory C]
    [BraidedCategory C] :
    (indOf (C := C)).Braided where
  toMonoidal := indOfMonoidal
  braided x y := (indOfTensorIso_hom_braiding x y).symm

/-- The unit comparison of the strong monoidal structure is
`RS.indOfUnitIso`. -/
lemma indOfMonoidal_εIso [SmallCategory C] [MonoidalCategory C] :
    Functor.Monoidal.εIso (indOf (C := C)) = indOfUnitIso :=
  Iso.ext rfl

/-- The tensor comparison of the strong monoidal structure is
`RS.indOfTensorIso`. -/
lemma indOfMonoidal_μIso [SmallCategory C] [MonoidalCategory C]
    (x y : C) :
    Functor.Monoidal.μIso (indOf (C := C)) x y = indOfTensorIso x y :=
  Iso.ext rfl

/-- The counit of the strong monoidal structure is the inverse of
`RS.indOfUnitIso`. -/
lemma indOf_oplax_η [SmallCategory C] [MonoidalCategory C] :
    Functor.OplaxMonoidal.η (indOf (C := C)) = indOfUnitIso.inv := by
  rw [← Functor.Monoidal.εIso_inv, indOfMonoidal_εIso]

/-- The cotensorator of the strong monoidal structure is the inverse of
`RS.indOfTensorIso`. -/
lemma indOf_oplax_δ [SmallCategory C] [MonoidalCategory C]
    (x y : C) :
    Functor.OplaxMonoidal.δ (indOf (C := C)) x y =
      (indOfTensorIso x y).inv := by
  rw [← Functor.Monoidal.μIso_inv, indOfMonoidal_μIso]

end Instances

section AcceptanceTests

/- Synthesis tests for the three instances of this file. -/

noncomputable example (C : Type v) [SmallCategory C]
    [MonoidalCategory C] : (indOf (C := C)).LaxMonoidal :=
  inferInstance

noncomputable example (C : Type v) [SmallCategory C]
    [MonoidalCategory C] : (indOf (C := C)).Monoidal :=
  inferInstance

noncomputable example (C : Type v) [SmallCategory C]
    [MonoidalCategory C] [BraidedCategory C] :
    (indOf (C := C)).Braided :=
  inferInstance

noncomputable example (C : Type v) [SmallCategory C]
    [MonoidalCategory C] [BraidedCategory C] :
    (indOf (C := C)).LaxBraided :=
  inferInstance

/- The packaged comparisons are the ones of record. -/

example (C : Type v) [SmallCategory C] [MonoidalCategory C] :
    Functor.LaxMonoidal.ε (indOf (C := C)) = indOfUnitIso.hom := rfl

example (C : Type v) [SmallCategory C] [MonoidalCategory C]
    (x y : C) :
    Functor.LaxMonoidal.μ (indOf (C := C)) x y =
      (indOfTensorIso x y).hom := rfl

end AcceptanceTests

end

end RS
