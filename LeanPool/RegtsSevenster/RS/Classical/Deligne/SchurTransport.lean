/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndSchur
import LeanPool.RegtsSevenster.RS.Classical.Deligne.ScalarLinear
import LeanPool.RegtsSevenster.RS.Novel.Envelope.ScalarTrace

/-!
# Schur-vanishing transport along the embedding `C ⥤ Ind C`

`RS.Classical.Deligne.IndSchur` transports the permutation action on
tensor powers across the embedding at the `permMor` level, and
`RS.Classical.Deligne.ScalarLinear` equips `Ind C` with the ℂ-linear
structure induced by a scalar unit `ψ : ℂ ≃+* End (𝟙_ C)`.  This file
joins the two: under `letI := linearOfScalarUnit (indScalarUnit ψ)`
the whole group-algebra action transports, and Schur vanishing on an
embedded object is Schur vanishing downstairs.

* `RS.smul_eq_unitConj` — a scalar acts by conjugating the unit
  endomorphism `c • 𝟙` through the left unitor;
* `RS.dayCoyonedaIso_hom_leftUnitor`/`RS.dayYonedaIso_hom_leftUnitor`
  — the Day tensor of (co)representables intertwines the left
  unitor, completing the coherence package of
  `RS.dayCoyonedaIso_hom_braiding`/`_associator`;
* `RS.indOf_leftUnitor_hom` — the unit comparison and the
  embedding-tensor comparison satisfy the left unitality of a
  monoidal functor up to isomorphism;
* `RS.indOf_map_smul` — the embedding carries the scalar action of
  `C` to the scalar action `RS.scalarSmul (indScalarUnit ψ)`;
* `RS.permAlg_indOf_conj` — the symmetric-group algebra action on
  the powers of an embedded object is conjugate, under
  `RS.indOfPowIso`, to the embedded action;
* **`RS.schurKilled_indOf_iff`** — Schur vanishing transports
  faithfully along `C ⥤ Ind C`, with the `HasScalarUnit`
  instantiation `RS.schurKilled_indOf_iff_of_hasScalarUnit`.
-/

namespace RS

open CategoryTheory MonoidalCategory MonoidalCategory.DayFunctor Limits
open Opposite

universe v u

noncomputable section

/-! ## The scalar action as a unitor conjugate -/

section SmulConj

variable {D : Type u}

/-- **The scalar action is a unitor conjugate**: `c • f` is
precomposition with the left-unitor conjugate of the unit
endomorphism `c • 𝟙`. -/
theorem smul_eq_unitConj
    [Category.{v} D] [MonoidalCategory D] [Preadditive D] [Linear ℂ D]
    [MonoidalPreadditive D] [MonoidalLinear ℂ D]
    (c : ℂ) {X Y : D} (f : X ⟶ Y) :
    c • f =
      (λ_ X).inv ≫ ((c • 𝟙 (𝟙_ D)) ▷ X) ≫ (λ_ X).hom ≫ f := by
  rw [MonoidalLinear.smul_whiskerRight, MonoidalCategory.id_whiskerRight,
    Linear.smul_comp, Linear.comp_smul, Category.id_comp,
    Iso.inv_hom_id_assoc]

end SmulConj

/-! ## The Day left unitor on corepresentables -/

section DayUnitCalculus

attribute [local instance] dayConv
attribute [local instance] dayConvPlain

variable {D : Type v}

/-- The Day unit comparison carries the canonical unit element to
the identity. -/
lemma dayUnitIso_hom_app_nu [SmallCategory D] [MonoidalCategory D] :
    (dayUnitIso D).hom.natTrans.app (𝟙_ D)
      (ν D (Type v) PUnit.unit) = 𝟙 (𝟙_ D) := by
  have h := corepresentableBy_homEquiv_uniqueUpToIso_hom
    (dayUnitCorepresentableBy (D := D))
    (coyonedaDayCorepresentableBy (𝟙_ D))
  rw [show (dayUnitCorepresentableBy (D := D)).uniqueUpToIso
      (coyonedaDayCorepresentableBy (𝟙_ D)) = dayUnitIso D
    from rfl] at h
  refine h.trans ?_
  dsimp [coyonedaDayCorepresentableBy]
  rw [coyonedaEquiv_apply]
  rfl

/-- The inverse of the Day unit comparison carries the identity to
the canonical unit element. -/
lemma dayUnitIso_inv_app_id [SmallCategory D] [MonoidalCategory D] :
    (dayUnitIso D).inv.natTrans.app (𝟙_ D) (𝟙 (𝟙_ D)) =
      ν D (Type v) PUnit.unit := by
  have h₀ := congrArg (fun t => t.natTrans.app (𝟙_ D))
    (dayUnitIso D).hom_inv_id
  have h₁ := ConcreteCategory.congr_hom h₀ (ν D (Type v) PUnit.unit)
  simp only [comp_natTrans, id_natTrans, NatTrans.comp_app] at h₁
  rw [← dayUnitIso_hom_app_nu]
  exact h₁.trans rfl

/-- Right-whiskering the inverse Day unit comparison carries the
canonical element of the Day tensor to the Kan-extension unit
evaluated on the canonical unit element. -/
lemma whiskerRight_dayUnitIso_inv_app_unitElt
    [SmallCategory D] [MonoidalCategory D]
    (a : D) :
    ((dayUnitIso D).inv ▷
        DayFunctor.mk (coyoneda.obj (op a))).natTrans.app (𝟙_ D ⊗ a)
      (dayCoyonedaUnitElt (𝟙_ D) a) =
    (η (𝟙_ (D ⊛⥤ Type v))
        (DayFunctor.mk (coyoneda.obj (op a)))).app (𝟙_ D, a)
      ((ν D (Type v) PUnit.unit, 𝟙 a)) := by
  have h₀ := congrArg (fun t => t.app (𝟙_ D ⊗ a))
    (natTrans_whiskerRight (dayUnitIso D).inv
      (DayFunctor.mk (coyoneda.obj (op a))))
  have h₁ := ConcreteCategory.congr_hom h₀ (dayCoyonedaUnitElt (𝟙_ D) a)
  have h₂' := DayConvolution.unit_app_map_app
    (f := (dayUnitIso D).inv.natTrans)
    (g := 𝟙 ((DayFunctor.mk (coyoneda.obj (op a))).functor))
    (x := 𝟙_ D) (y := a)
  have h₂ : (DayConvolution.map (dayUnitIso D).inv.natTrans
        (𝟙 ((DayFunctor.mk (coyoneda.obj (op a))).functor))).app
        (𝟙_ D ⊗ a) (dayCoyonedaUnitElt (𝟙_ D) a) =
      (η (𝟙_ (D ⊛⥤ Type v))
          (DayFunctor.mk (coyoneda.obj (op a)))).app (𝟙_ D, a)
        (((dayUnitIso D).inv.natTrans.app (𝟙_ D) (𝟙 (𝟙_ D)), 𝟙 a)) :=
    ConcreteCategory.congr_hom h₂'
      ((𝟙 (𝟙_ D), 𝟙 a) : ((𝟙_ D) ⟶ (𝟙_ D)) × (a ⟶ a))
  rw [h₁]
  refine h₂.trans ?_
  exact congrArg
    (fun z => (η (𝟙_ (D ⊛⥤ Type v))
      (DayFunctor.mk (coyoneda.obj (op a)))).app (𝟙_ D, a)
      ((z, 𝟙 a)))
    dayUnitIso_inv_app_id

/-- **The Day left unitor, evaluated on a Kan-extension unit
element**: it strips the canonical unit element and applies the
inverse base left unitor. -/
lemma day_leftUnitor_hom_app_eta [SmallCategory D] [MonoidalCategory D]
    (F : D ⊛⥤ Type v) (y : D)
    (x : F.functor.obj y) :
    (λ_ F).hom.natTrans.app (𝟙_ D ⊗ y)
      ((η (𝟙_ (D ⊛⥤ Type v)) F).app (𝟙_ D, y)
        ((ν D (Type v) PUnit.unit, x))) =
    F.functor.map (λ_ y).inv x := by
  have h := LawfulDayConvolutionMonoidalCategoryStruct.leftUnitor_hom_unit_app
    (C := D) (Type v) F y
  have h' := ConcreteCategory.congr_hom h
    ((PUnit.unit, x) : 𝟙_ (Type v) ⊗ F.functor.obj y)
  exact h'

/-- **The Day unit intertwines the left unitor on
corepresentables**: under the co-Yoneda identifications, the Day
left unitor at a corepresentable is precomposition with the inverse
base left unitor. -/
lemma dayCoyonedaIso_hom_leftUnitor [SmallCategory D] [MonoidalCategory D]
    (a : D) :
    ((dayUnitIso D).hom ▷ DayFunctor.mk (coyoneda.obj (op a))) ≫
        (dayCoyonedaIso (𝟙_ D) a).hom ≫
        (⟨coyoneda.map ((λ_ a).inv.op)⟩ :
          DayFunctor.mk (coyoneda.obj (op (𝟙_ D ⊗ a))) ⟶
            DayFunctor.mk (coyoneda.obj (op a))) =
      (λ_ (DayFunctor.mk (coyoneda.obj (op a)))).hom := by
  have aux : ((dayUnitIso D).inv ▷
        DayFunctor.mk (coyoneda.obj (op a))) ≫
        (λ_ (DayFunctor.mk (coyoneda.obj (op a)))).hom =
      (dayCoyonedaIso (𝟙_ D) a).hom ≫
        (⟨coyoneda.map ((λ_ a).inv.op)⟩ :
          DayFunctor.mk (coyoneda.obj (op (𝟙_ D ⊗ a))) ⟶
            DayFunctor.mk (coyoneda.obj (op a))) := by
    apply (dayCoyonedaCorepresentableBy (𝟙_ D) a).homEquiv.injective
    rw [(dayCoyonedaCorepresentableBy (𝟙_ D) a).homEquiv_comp,
      (dayCoyonedaCorepresentableBy (𝟙_ D) a).homEquiv_comp,
      dayCoyonedaCorepresentableBy_homEquiv_iso,
      dayEvaluation_map_apply, dayEvaluation_map_apply,
      dayCoyonedaCorepresentableBy_homEquiv_apply,
      whiskerRight_dayUnitIso_inv_app_unitElt,
      day_leftUnitor_hom_app_eta]
    show 𝟙 a ≫ (λ_ a).inv = (λ_ a).inv ≫ 𝟙 (𝟙_ D ⊗ a)
    rw [Category.id_comp, Category.comp_id]
  rw [← aux, ← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
    Iso.hom_inv_id, MonoidalCategory.id_whiskerRight,
    Category.id_comp]

end DayUnitCalculus

/-! ## The Yoneda form and the embedded left unitor -/

section IndUnit

variable {C : Type v}

/-- Composing the transports of an isomorphism and of its reverse
along `RS.dayMkIso`, in the reversed order. -/
lemma dayMkIso_symm_hom_hom [SmallCategory C] [MonoidalCategory C]
    {A B : Cᵒᵖ ⥤ Type v} (e : A ≅ B) :
    (dayMkIso e.symm).hom ≫ (dayMkIso e).hom =
      𝟙 (DayFunctor.mk B : Cᵒᵖ ⊛⥤ Type v) :=
  (dayMkIso e).inv_hom_id

/-- **The Day tensor of representables intertwines the left
unitor**: the Yoneda form of `RS.dayCoyonedaIso_hom_leftUnitor`.
The unit leg is the composite identification of the Day unit with
the representable at `𝟙_ C`, as in `RS.indOfUnitIso`. -/
lemma dayYonedaIso_hom_leftUnitor [SmallCategory C] [MonoidalCategory C]
    (x : C) :
    (((dayUnitIso Cᵒᵖ).hom ≫
        (dayMkIso (Coyoneda.objOpOp (𝟙_ C))).hom) ▷
        DayFunctor.mk (yoneda.obj x)) ≫
      (dayYonedaIso (𝟙_ C) x).hom ≫ ⟨yoneda.map (λ_ x).hom⟩ =
    (λ_ (DayFunctor.mk (yoneda.obj x))).hom := by
  have s₂ : (⟨coyoneda.map ((λ_ (op x)).inv.op)⟩ :
        DayFunctor.mk (coyoneda.obj (op (op (𝟙_ C) ⊗ op x))) ⟶
          DayFunctor.mk (coyoneda.obj (op (op x)))) ≫
        (dayMkIso (Coyoneda.objOpOp x)).hom =
      (dayMkIso (Coyoneda.objOpOp (𝟙_ C ⊗ x))).hom ≫
        ⟨yoneda.map (λ_ x).hom⟩ := by
    ext1
    exact coyoneda_map_op_op_comp_objOpOp_hom (λ_ x).hom
  have hcu : ((dayUnitIso Cᵒᵖ).hom ▷
        DayFunctor.mk (coyoneda.obj (op (op x)))) ≫
        (dayCoyonedaIso (op (𝟙_ C)) (op x)).hom ≫
        (⟨coyoneda.map ((λ_ (op x)).inv.op)⟩ :
          DayFunctor.mk (coyoneda.obj (op (op (𝟙_ C) ⊗ op x))) ⟶
            DayFunctor.mk (coyoneda.obj (op (op x)))) =
      (λ_ (DayFunctor.mk (coyoneda.obj (op (op x))))).hom :=
    dayCoyonedaIso_hom_leftUnitor (D := Cᵒᵖ) (op x)
  have e₁ : (((dayUnitIso Cᵒᵖ).hom ≫
        (dayMkIso (Coyoneda.objOpOp (𝟙_ C))).hom) ▷
        DayFunctor.mk (yoneda.obj x)) ≫
      ((dayMkIso (Coyoneda.objOpOp (𝟙_ C)).symm).hom ⊗ₘ
        (dayMkIso (Coyoneda.objOpOp x).symm).hom) =
      (𝟙_ (Cᵒᵖ ⊛⥤ Type v) ◁
        (dayMkIso (Coyoneda.objOpOp x).symm).hom) ≫
      ((dayUnitIso Cᵒᵖ).hom ▷
        DayFunctor.mk (coyoneda.obj (op (op x)))) := by
    rw [← MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp,
      Category.assoc, comp_dayMkIso_hom_symm_hom,
      MonoidalCategory.tensorHom_def']
  simp only [dayYonedaIso, Iso.trans_hom, tensorIso_hom,
    Category.assoc]
  rw [reassoc_of% e₁, ← s₂, reassoc_of% hcu,
    MonoidalCategory.leftUnitor_naturality_assoc,
    dayMkIso_symm_hom_hom, Category.comp_id]

/-- The embedding into the Day presheaf category carries the unit
comparison to its Day-level composite. -/
lemma indToDay_map_indOfUnitIso_hom [SmallCategory C] [MonoidalCategory C] :
    (indToDay (C := C)).map (indOfUnitIso (C := C)).hom =
      (Functor.Monoidal.εIso (indToDay (C := C))).inv ≫
        (dayUnitIso Cᵒᵖ).hom ≫
        (dayMkIso (Coyoneda.objOpOp (𝟙_ C))).hom ≫
        (indToDayIndOfIso (𝟙_ C)).inv := by
  rw [indOfUnitIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage]
  simp only [Iso.trans_hom, Iso.symm_hom]

/-- **Left unitality of the embedding comparison**: the left unitor
of an embedded object factors as the unit comparison, the
embedding-tensor comparison, and the embedded left unitor.  This is
the unit axiom of the monoidal-functor-up-to-isomorphism structure
of `indOf`. -/
lemma indOf_leftUnitor_hom [SmallCategory C] [MonoidalCategory C]
    (X : C) :
    (λ_ (indOf.obj X)).hom =
      ((indOfUnitIso (C := C)).hom ▷ indOf.obj X) ≫
        (indOfTensorIso (𝟙_ C) X).hom ≫ indOf.map (λ_ X).hom := by
  apply (indToDay (C := C)).map_injective
  rw [Functor.map_comp, Functor.map_comp,
    Functor.Monoidal.map_whiskerRight (F := indToDay (C := C)),
    Functor.Monoidal.map_leftUnitor (F := indToDay (C := C)),
    indToDay_map_indOfUnitIso_hom, indToDay_map_indOfTensorIso_hom]
  simp only [indToDayTensorIso, Iso.trans_hom, Iso.symm_hom,
    tensorIso_hom, Functor.Monoidal.μIso_inv, Category.assoc,
    Functor.Monoidal.μ_δ_assoc, MonoidalCategory.comp_whiskerRight]
  rw [← comp_indToDayIndOfIso_inv]
  have hA : ((indToDayIndOfIso (𝟙_ C)).inv ▷
        (indToDay (C := C)).obj (indOf.obj X)) ≫
        ((indToDayIndOfIso (𝟙_ C)).hom ⊗ₘ (indToDayIndOfIso X).hom) =
      DayFunctor.mk (yoneda.obj (𝟙_ C)) ◁ (indToDayIndOfIso X).hom := by
    rw [← MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_comp_tensorHom, Iso.inv_hom_id,
      Category.id_comp, MonoidalCategory.id_tensorHom]
  have hB : ((dayUnitIso Cᵒᵖ).hom ▷
        (indToDay (C := C)).obj (indOf.obj X)) ≫
        ((dayMkIso (Coyoneda.objOpOp (𝟙_ C))).hom ▷
          (indToDay (C := C)).obj (indOf.obj X)) ≫
        (DayFunctor.mk (yoneda.obj (𝟙_ C)) ◁ (indToDayIndOfIso X).hom) =
      (𝟙_ (Cᵒᵖ ⊛⥤ Type v) ◁ (indToDayIndOfIso X).hom) ≫
        (((dayUnitIso Cᵒᵖ).hom ≫
          (dayMkIso (Coyoneda.objOpOp (𝟙_ C))).hom) ▷
          DayFunctor.mk (yoneda.obj X)) := by
    rw [← MonoidalCategory.comp_whiskerRight_assoc]
    exact (MonoidalCategory.whisker_exchange _ _).symm
  rw [reassoc_of% hA, reassoc_of% hB,
    reassoc_of% dayYonedaIso_hom_leftUnitor X,
    MonoidalCategory.leftUnitor_naturality_assoc, Iso.hom_inv_id,
    Category.comp_id, Functor.Monoidal.εIso_inv]

/-- Iso form of `RS.indOf_leftUnitor_hom`. -/
lemma indOf_leftUnitorIso [SmallCategory C] [MonoidalCategory C]
    (X : C) :
    λ_ (indOf.obj X) =
      whiskerRightIso (indOfUnitIso (C := C)) (indOf.obj X) ≪≫
        indOfTensorIso (𝟙_ C) X ≪≫ indOf.mapIso (λ_ X) :=
  Iso.ext (by simpa using indOf_leftUnitor_hom X)

/-- Inverse form of `RS.indOf_leftUnitor_hom`. -/
lemma indOf_leftUnitor_inv [SmallCategory C] [MonoidalCategory C]
    (X : C) :
    (λ_ (indOf.obj X)).inv =
      indOf.map (λ_ X).inv ≫ (indOfTensorIso (𝟙_ C) X).inv ≫
        ((indOfUnitIso (C := C)).inv ▷ indOf.obj X) := by
  rw [indOf_leftUnitorIso X]
  simp

/-- **Transport of unit-endomorphism conjugates**: conjugating the
`indOfUnitIso`-transport of a unit endomorphism through the left
unitor of an embedded object is the image of the conjugate
downstairs. -/
theorem indOf_map_unitConj [SmallCategory C] [MonoidalCategory C]
    (X : C) (u : 𝟙_ C ⟶ 𝟙_ C) :
    (λ_ (indOf.obj X)).inv ≫
        (((indOfUnitIso (C := C)).hom ≫ indOf.map u ≫
          (indOfUnitIso (C := C)).inv) ▷ indOf.obj X) ≫
        (λ_ (indOf.obj X)).hom =
      indOf.map ((λ_ X).inv ≫ (u ▷ X) ≫ (λ_ X).hom) := by
  rw [indOf_leftUnitor_hom X, indOf_leftUnitor_inv X]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc,
    MonoidalCategory.inv_hom_whiskerRight_assoc]
  rw [reassoc_of% indOfTensorIso_hom_natural_left u X,
    Iso.inv_hom_id_assoc, Functor.map_comp, Functor.map_comp]

end IndUnit

/-! ## The scalar transport -/

section ScalarTransport

variable {C : Type v}

/-- The scalar unit of `Ind C`, evaluated: the
`indOfUnitIso`-conjugate of the embedded unit endomorphism. -/
lemma indScalarUnit_apply [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C]
    (ψ : ℂ ≃+* End (𝟙_ C)) (c : ℂ) :
    scalarHom (indScalarUnit ψ) c =
      (indOfUnitIso (C := C)).hom ≫ indOf.map (ψ c) ≫
        (indOfUnitIso (C := C)).inv :=
  rfl

/-- **The embedding intertwines the scalar actions**: `indOf`
carries `c • f` to the `RS.scalarSmul` action of `c` on the image,
for the scalar unit transported by `RS.indScalarUnit`. -/
theorem indOf_map_smul [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [Linear ℂ C] [MonoidalPreadditive C]
    [MonoidalLinear ℂ C]
    (ψ : ℂ ≃+* End (𝟙_ C))
    (hψ : ∀ c : ℂ, ψ c = c • 𝟙 (𝟙_ C)) (c : ℂ) {X Y : C}
    (f : X ⟶ Y) :
    indOf.map (c • f) =
      scalarSmul (indScalarUnit ψ) c (indOf.map f) := by
  rw [smul_eq_unitConj]
  simp only [scalarSmul]
  rw [indScalarUnit_apply ψ c, hψ c,
    reassoc_of% indOf_map_unitConj X (c • 𝟙 (𝟙_ C)),
    ← Functor.map_comp]
  simp only [Category.assoc]

end ScalarTransport

/-! ## The algebra transport and the summit -/

section AlgebraTransport

variable {E : Type u}

/-- Intertwining `T` is closed under sums.  Stated at general
objects and applied by `exact`, so the endomorphism-ring structure
never enters the rewriting. -/
private theorem add_pass [Category.{v} E]
    [Preadditive E] {P Q : E} {a b : P ⟶ P}
    {a' b' : Q ⟶ Q} {T : P ⟶ Q} (ha : a ≫ T = T ≫ a')
    (hb : b ≫ T = T ≫ b') :
    (a + b) ≫ T = T ≫ (a' + b') := by
  rw [Preadditive.add_comp, Preadditive.comp_add, ha, hb]

/-- Intertwining `T` is closed under scalars.  Stated at general
objects and applied by `exact`. -/
private theorem smul_pass [Category.{v} E]
    [Preadditive E] [Linear ℂ E] {P Q : E}
    {a : P ⟶ P} {a' : Q ⟶ Q} {T : P ⟶ Q} (r : ℂ)
    (h : a ≫ T = T ≫ a') :
    (r • a) ≫ T = T ≫ (r • a') := by
  rw [Linear.smul_comp, Linear.comp_smul, h]

/-- **Transport of the group-algebra action**: under the ℂ-linear
structure induced on `Ind C` by a scalar unit `ψ` for `C`, the
action of the symmetric-group algebra on the tensor powers of an
embedded object is conjugate, under `RS.indOfPowIso`, to the
embedded action. -/
theorem permAlg_indOf_conj {C : Type v} [SmallCategory C] [MonoidalCategory C]
    [SymmetricCategory C] [Preadditive C] [Linear ℂ C] [HasFiniteColimits C]
    [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    (ψ : ℂ ≃+* End (𝟙_ C))
    (hψ : ∀ c : ℂ, ψ c = c • 𝟙 (𝟙_ C)) (X : C) {n : ℕ}
    (x : SymGroupAlgebra n) :
    letI := linearOfScalarUnit (indScalarUnit ψ)
    permAlg (indOf.obj X) n x ≫ (indOfPowIso X n).hom =
      (indOfPowIso X n).hom ≫ indOf.map (permAlg X n x) := by
  letI := linearOfScalarUnit (indScalarUnit ψ)
  haveI := indOf_additive (C := C)
  induction x using MonoidAlgebra.induction_on with
  | hM σ =>
    rw [MonoidAlgebra.of_apply, permAlg_single, permAlg_single]
    exact indOfPowIso_permMor X n σ
  | hadd p q hp hq =>
    rw [map_add, map_add]
    exact (add_pass hp hq).trans
      (congrArg (fun m => (indOfPowIso X n).hom ≫ m)
        (Functor.map_add (F := indOf (C := C))).symm)
  | hsmul c p hp =>
    rw [map_smul, map_smul]
    exact (smul_pass c hp).trans
      (congrArg (fun m => (indOfPowIso X n).hom ≫ m)
        (indOf_map_smul ψ hψ c (permAlg X n p)).symm)

/-- **Schur-vanishing transport along the embedding `C ⥤ Ind C`**:
with the ℂ-linear structure induced on `Ind C` by a scalar unit for
`C`, a shape kills an embedded object precisely when it kills the
object downstairs. -/
theorem schurKilled_indOf_iff
    {C : Type v} [SmallCategory C] [MonoidalCategory C]
    [SymmetricCategory C] [Preadditive C] [Linear ℂ C] [HasFiniteColimits C]
    [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    (P : SchurPackage.{v})
    (ψ : ℂ ≃+* End (𝟙_ C)) (hψ : ∀ c : ℂ, ψ c = c • 𝟙 (𝟙_ C))
    {X : C} {μ : YoungDiagram} :
    letI := linearOfScalarUnit (indScalarUnit ψ)
    (SchurKilled P (indOf.obj X) μ ↔ SchurKilled P X μ) := by
  letI := linearOfScalarUnit (indScalarUnit ψ)
  have hconj : permAlg (indOf.obj X) μ.card (P.e μ) =
      (indOfPowIso X μ.card).hom ≫
        indOf.map (permAlg X μ.card (P.e μ)) ≫
        (indOfPowIso X μ.card).inv := by
    rw [← reassoc_of% permAlg_indOf_conj ψ hψ X (P.e μ),
      Iso.hom_inv_id, Category.comp_id]
  constructor
  · intro h0
    rw [schurKilled_iff_indOf_map_permAlg_eq_zero P X μ]
    have h0' : permAlg (indOf.obj X) μ.card (P.e μ) =
        (0 : tensorPow (Ind C) (indOf.obj X) μ.card ⟶
          tensorPow (Ind C) (indOf.obj X) μ.card) := h0
    rw [hconj] at h0'
    have h1 := (indOfPowIso X μ.card).inv ≫= h0' =≫
      (indOfPowIso X μ.card).hom
    simpa using h1
  · intro h0
    show permAlg (indOf.obj X) μ.card (P.e μ) = 0
    rw [hconj, (schurKilled_iff_indOf_map_permAlg_eq_zero P X μ).mp h0,
      zero_comp, comp_zero]
    rfl

/-- `RS.schurKilled_indOf_iff`, instantiated at the scalar unit of
a category whose unit endomorphisms are exactly the scalars. -/
theorem schurKilled_indOf_iff_of_hasScalarUnit
    {C : Type v} [SmallCategory C] [MonoidalCategory C]
    [SymmetricCategory C] [Preadditive C] [Linear ℂ C] [HasFiniteColimits C]
    [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    (P : SchurPackage.{v})
    (hu : HasScalarUnit C) {X : C} {μ : YoungDiagram} :
    letI := linearOfScalarUnit
      (indScalarUnit (unitScalarEquiv hu).toRingEquiv)
    (SchurKilled P (indOf.obj X) μ ↔ SchurKilled P X μ) :=
  schurKilled_indOf_iff P (unitScalarEquiv hu).toRingEquiv
    (fun _ => rfl)

end AlgebraTransport

end

end RS
