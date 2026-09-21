/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndTensorExact
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SchurVanishing

/-!
# Transport of tensor powers and the permutation action along
`C ⥤ Ind C`

The embedding `RS.indOf : C ⥤ Ind C` is monoidal up to isomorphism
(`RS.indOfTensorIso`, `RS.Classical.Deligne.IndTensorExact`).  This
file upgrades that comparison to the full coherent package needed to
transport the symmetric-group action on tensor powers
(`RS.Novel.Envelope.SymPerm`) across the embedding:

* `RS.dayCoyonedaIso_hom_braiding` and
  `RS.dayCoyonedaIso_hom_associator` — the co-Yoneda identifications
  of `RS.dayCoyonedaIso` intertwine the Day braiding and the Day
  associator with the braiding and associator of the base, with
  Yoneda forms `RS.dayYonedaIso_hom_braiding` and
  `RS.dayYonedaIso_hom_associator`;
* `RS.indOfUnitIso` — the unit of `Ind C` is the embedded unit;
* `RS.indOfTensorIso_hom_braiding` and
  `RS.indOfTensorIso_hom_associator` — the embedding-tensor
  comparison is compatible with braiding and associator: `indOf`
  with `indOfTensorIso` is a braided monoidal functor up to
  isomorphism;
* `RS.indOfPowIso` — the tensor powers of an embedded object are the
  embedded tensor powers, with recursion lemmas
  `RS.indOfPowIso_zero`/`RS.indOfPowIso_succ`;
* `RS.indOfPowIso_swapTop`/`RS.indOfPowIso_insertTop`/
  **`RS.indOfPowIso_permMor`** — the permutation action on the
  tensor powers of `indOf.obj X` is conjugate, under `indOfPowIso`,
  to the embedded permutation action;
* `RS.permMor_indOf_eq_zero_iff` and
  `RS.schurKilled_iff_indOf_map_permAlg_eq_zero` — vanishing of the
  action transports faithfully across the embedding.

The Mathlib pin has `Preadditive (Ind C)` (for `C` preadditive with
finite colimits) but no `Linear ℂ (Ind C)` instance, so `Ind C`
carries no `permAlg`, so Schur vanishing cannot be *stated* on
`Ind C`; the lemmas above are the `permMor`-level substrate, which is
what the group-algebra layer would rest on were `Linear ℂ (Ind C)`
available.

The single-element method used throughout the Day-level proofs: a
morphism out of a (possibly iterated) Day tensor of corepresentables
is classified, through the Kan-extension universal property and the
Yoneda lemma, by one element — its value on the canonical element
`RS.dayCoyonedaUnitElt` assembled from identities.  All coherence
comparisons are decided by evaluating both sides there.
-/

namespace RS

open CategoryTheory MonoidalCategory MonoidalCategory.DayFunctor Limits
open Opposite

universe v

noncomputable section

section DayCalculusMore

attribute [local instance] dayConv

variable {D : Type v}

/-- The Day-convolution structure of a plain presheaf pair, read
through the synonym: makes the `DayConvolution` API available on
underlying functors of the Day category. -/
@[reducible] def dayConvPlain [SmallCategory D] [MonoidalCategory D]
    (F G : D ⥤ Type v) : DayConvolution F G :=
  dayConv (DayFunctor.mk F) (DayFunctor.mk G)

attribute [local instance] dayConvPlain

/-- The canonical element of the Day tensor of two
corepresentables: the Kan-extension unit evaluated on the pair of
identities. -/
def dayCoyonedaUnitElt [SmallCategory D] [MonoidalCategory D]
    (a b : D) :
    ((DayFunctor.mk (coyoneda.obj (op a)) ⊗
      DayFunctor.mk (coyoneda.obj (op b)) : D ⊛⥤ Type v)).functor.obj
      (a ⊗ b) :=
  (η (DayFunctor.mk (coyoneda.obj (op a)))
    (DayFunctor.mk (coyoneda.obj (op b)))).app (a, b)
    ((𝟙 a, 𝟙 b) : (a ⟶ a) × (b ⟶ b))

/-- The canonical element of a left-nested triple Day tensor of
corepresentables. -/
def dayCoyonedaUnitElt₂ [SmallCategory D] [MonoidalCategory D]
    (a b c : D) :
    (((DayFunctor.mk (coyoneda.obj (op a)) ⊗
        DayFunctor.mk (coyoneda.obj (op b))) ⊗
      DayFunctor.mk (coyoneda.obj (op c)) : D ⊛⥤ Type v)).functor.obj
      ((a ⊗ b) ⊗ c) :=
  (η (DayFunctor.mk (coyoneda.obj (op a)) ⊗
      DayFunctor.mk (coyoneda.obj (op b)))
    (DayFunctor.mk (coyoneda.obj (op c)))).app (a ⊗ b, c)
    ((dayCoyonedaUnitElt a b, 𝟙 c))

/-- The canonical element of a right-nested triple Day tensor of
corepresentables. -/
def dayCoyonedaUnitElt₂' [SmallCategory D] [MonoidalCategory D]
    (a b c : D) :
    ((DayFunctor.mk (coyoneda.obj (op a)) ⊗
      (DayFunctor.mk (coyoneda.obj (op b)) ⊗
        DayFunctor.mk (coyoneda.obj (op c))) : D ⊛⥤ Type v)).functor.obj
      (a ⊗ (b ⊗ c)) :=
  (η (DayFunctor.mk (coyoneda.obj (op a)))
    (DayFunctor.mk (coyoneda.obj (op b)) ⊗
      DayFunctor.mk (coyoneda.obj (op c)))).app (a, b ⊗ c)
    ((𝟙 a, dayCoyonedaUnitElt b c))

open scoped MonoidalCategory.ExternalProduct in
/-- The left-nested triple Day tensor of corepresentables
corepresents evaluation at `(a ⊗ b) ⊗ c`: iterate the Kan-extension
universal property twice and read off the Yoneda lemma on the
external product of three corepresentables, which is definitionally
the corepresentable of the triple product category. -/
def dayCoyonedaCorepresentableBy₂ [SmallCategory D] [MonoidalCategory D]
    (a b c : D) :
    (dayEvaluation ((a ⊗ b) ⊗ c)).CorepresentableBy
      ((DayFunctor.mk (coyoneda.obj (op a)) ⊗
        DayFunctor.mk (coyoneda.obj (op b))) ⊗
        DayFunctor.mk (coyoneda.obj (op c))) where
  homEquiv {F} :=
    ({ toFun := Hom.natTrans
       invFun := .mk
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl } :
        ((DayFunctor.mk (coyoneda.obj (op a)) ⊗
            DayFunctor.mk (coyoneda.obj (op b))) ⊗
            DayFunctor.mk (coyoneda.obj (op c)) ⟶ F) ≃
          (((DayFunctor.mk (coyoneda.obj (op a)) ⊗
            DayFunctor.mk (coyoneda.obj (op b))) ⊗
            DayFunctor.mk (coyoneda.obj (op c))).functor ⟶
            F.functor)).trans <|
      (Functor.homEquivOfIsLeftKanExtension _
        (DayConvolution.unit
          ((DayFunctor.mk (coyoneda.obj (op a)) ⊗
            DayFunctor.mk (coyoneda.obj (op b))).functor)
          (coyoneda.obj (op c)))
        F.functor).trans <|
      (Functor.homEquivOfIsLeftKanExtension _
        (ExternalProduct.extensionUnitLeft _
          (DayConvolution.unit (coyoneda.obj (op a))
            (coyoneda.obj (op b)))
          (coyoneda.obj (op c)))
        (tensor D ⋙ F.functor)).trans
        (coyonedaEquiv (C := (D × D) × D)
          (X := (((a, b), c) : (D × D) × D))
          (F := (tensor D).prod (𝟭 D) ⋙ tensor D ⋙ F.functor))
  homEquiv_comp _ _ := rfl

/-- Evaluation of `RS.dayEvaluation` on a morphism of the Day
category. -/
lemma dayEvaluation_map_apply [SmallCategory D] [MonoidalCategory D]
    (d : D) {F K : D ⊛⥤ Type v} (g : F ⟶ K)
    (x : (dayEvaluation d).obj F) :
    (dayEvaluation d).map g x = g.natTrans.app d x := rfl

/-- The corepresentability of a Day tensor of two corepresentables
classifies a morphism by its value on the canonical element. -/
lemma dayCoyonedaCorepresentableBy_homEquiv_apply
    [SmallCategory D] [MonoidalCategory D]
    (a b : D)
    {K : D ⊛⥤ Type v}
    (f : DayFunctor.mk (coyoneda.obj (op a)) ⊗
      DayFunctor.mk (coyoneda.obj (op b)) ⟶ K) :
    (dayCoyonedaCorepresentableBy a b).homEquiv f =
      f.natTrans.app (a ⊗ b) (dayCoyonedaUnitElt a b) := rfl

/-- The corepresentability of a left-nested triple Day tensor of
corepresentables classifies a morphism by its value on the canonical
element. -/
lemma dayCoyonedaCorepresentableBy₂_homEquiv_apply
    [SmallCategory D] [MonoidalCategory D]
    (a b c : D)
    {K : D ⊛⥤ Type v}
    (f : (DayFunctor.mk (coyoneda.obj (op a)) ⊗
      DayFunctor.mk (coyoneda.obj (op b))) ⊗
      DayFunctor.mk (coyoneda.obj (op c)) ⟶ K) :
    (dayCoyonedaCorepresentableBy₂ a b c).homEquiv f =
      f.natTrans.app ((a ⊗ b) ⊗ c) (dayCoyonedaUnitElt₂ a b c) := rfl

/-- The classification of `RS.dayCoyonedaIso` under the
corepresentability of the Day tensor of two corepresentables: its
value is the identity of `p ⊗ q`. -/
lemma dayCoyonedaCorepresentableBy_homEquiv_iso
    [SmallCategory D] [MonoidalCategory D]
    (p q : D) :
    (dayCoyonedaCorepresentableBy p q).homEquiv
      (dayCoyonedaIso p q).hom = 𝟙 (p ⊗ q) := by
  have h := corepresentableBy_homEquiv_uniqueUpToIso_hom
    (dayCoyonedaCorepresentableBy p q)
    (coyonedaDayCorepresentableBy (p ⊗ q))
  rw [show (dayCoyonedaCorepresentableBy p q).uniqueUpToIso
      (coyonedaDayCorepresentableBy (p ⊗ q)) = dayCoyonedaIso p q
    from rfl] at h
  rw [h]
  change coyonedaEquiv (𝟙 (coyoneda.obj (op (p ⊗ q)))) = 𝟙 (p ⊗ q)
  rfl

/-- `RS.dayCoyonedaIso` sends the canonical element to the
identity. -/
lemma dayCoyonedaIso_hom_app_unitElt [SmallCategory D] [MonoidalCategory D]
    (p q : D) :
    (dayCoyonedaIso p q).hom.natTrans.app (p ⊗ q)
      (dayCoyonedaUnitElt p q) = 𝟙 (p ⊗ q) := by
  have h := dayCoyonedaCorepresentableBy_homEquiv_iso p q
  rwa [dayCoyonedaCorepresentableBy_homEquiv_apply] at h

/-- Right-whiskering `RS.dayCoyonedaIso` sends the left-nested
canonical element to the canonical element at `(a ⊗ b, c)`. -/
lemma whiskerRight_dayCoyonedaIso_app_unitElt
    [SmallCategory D] [MonoidalCategory D]
    (a b c : D) :
    ((dayCoyonedaIso a b).hom ▷
        DayFunctor.mk (coyoneda.obj (op c))).natTrans.app ((a ⊗ b) ⊗ c)
      (dayCoyonedaUnitElt₂ a b c) = dayCoyonedaUnitElt (a ⊗ b) c := by
  have h₀ := congrArg (fun t => t.app ((a ⊗ b) ⊗ c))
    (natTrans_whiskerRight (dayCoyonedaIso a b).hom
      (DayFunctor.mk (coyoneda.obj (op c))))
  have h₁ := ConcreteCategory.congr_hom h₀ (dayCoyonedaUnitElt₂ a b c)
  have h₂' := DayConvolution.unit_app_map_app
    (f := (dayCoyonedaIso a b).hom.natTrans)
    (g := 𝟙 ((DayFunctor.mk (coyoneda.obj (op c))).functor))
    (x := a ⊗ b) (y := c)
  have h₂ : (DayConvolution.map (dayCoyonedaIso a b).hom.natTrans
        (𝟙 ((DayFunctor.mk (coyoneda.obj (op c))).functor))).app
        ((a ⊗ b) ⊗ c) (dayCoyonedaUnitElt₂ a b c) =
      (η (DayFunctor.mk (coyoneda.obj (op (a ⊗ b))))
        (DayFunctor.mk (coyoneda.obj (op c)))).app (a ⊗ b, c)
        (((dayCoyonedaIso a b).hom.natTrans.app (a ⊗ b)
          (dayCoyonedaUnitElt a b), 𝟙 c)) :=
    ConcreteCategory.congr_hom h₂'
      ((dayCoyonedaUnitElt a b, 𝟙 c) :
        ((DayFunctor.mk (coyoneda.obj (op a)) ⊗
          DayFunctor.mk (coyoneda.obj (op b))).functor.obj (a ⊗ b)) ×
          (c ⟶ c))
  rw [h₁]
  refine h₂.trans ?_
  exact congrArg
    (fun z => (η (DayFunctor.mk (coyoneda.obj (op (a ⊗ b))))
      (DayFunctor.mk (coyoneda.obj (op c)))).app (a ⊗ b, c)
      ((z, 𝟙 c) :
        ((a ⊗ b) ⟶ (a ⊗ b)) × (c ⟶ c)))
    (dayCoyonedaIso_hom_app_unitElt a b)

/-- Left-whiskering `RS.dayCoyonedaIso` sends the right-nested
canonical element to the canonical element at `(a, b ⊗ c)`. -/
lemma whiskerLeft_dayCoyonedaIso_app_unitElt
    [SmallCategory D] [MonoidalCategory D]
    (a b c : D) :
    (DayFunctor.mk (coyoneda.obj (op a)) ◁
        (dayCoyonedaIso b c).hom).natTrans.app (a ⊗ (b ⊗ c))
      (dayCoyonedaUnitElt₂' a b c) = dayCoyonedaUnitElt a (b ⊗ c) := by
  have h₀ := congrArg (fun t => t.app (a ⊗ (b ⊗ c)))
    (natTrans_whiskerLeft (DayFunctor.mk (coyoneda.obj (op a)))
      (dayCoyonedaIso b c).hom)
  have h₁ := ConcreteCategory.congr_hom h₀ (dayCoyonedaUnitElt₂' a b c)
  have h₂' := DayConvolution.unit_app_map_app
    (f := 𝟙 ((DayFunctor.mk (coyoneda.obj (op a))).functor))
    (g := (dayCoyonedaIso b c).hom.natTrans) (x := a) (y := b ⊗ c)
  have h₂ : (DayConvolution.map
        (𝟙 ((DayFunctor.mk (coyoneda.obj (op a))).functor))
        (dayCoyonedaIso b c).hom.natTrans).app (a ⊗ (b ⊗ c))
        (dayCoyonedaUnitElt₂' a b c) =
      (η (DayFunctor.mk (coyoneda.obj (op a)))
        (DayFunctor.mk (coyoneda.obj (op (b ⊗ c))))).app (a, b ⊗ c)
        ((𝟙 a, (dayCoyonedaIso b c).hom.natTrans.app (b ⊗ c)
          (dayCoyonedaUnitElt b c))) :=
    ConcreteCategory.congr_hom h₂'
      ((𝟙 a, dayCoyonedaUnitElt b c) :
        (a ⟶ a) ×
          ((DayFunctor.mk (coyoneda.obj (op b)) ⊗
            DayFunctor.mk (coyoneda.obj (op c))).functor.obj (b ⊗ c)))
  rw [h₁]
  refine h₂.trans ?_
  exact congrArg
    (fun z => (η (DayFunctor.mk (coyoneda.obj (op a)))
      (DayFunctor.mk (coyoneda.obj (op (b ⊗ c))))).app (a, b ⊗ c)
      ((𝟙 a, z) :
        (a ⟶ a) × ((b ⊗ c) ⟶ (b ⊗ c))))
    (dayCoyonedaIso_hom_app_unitElt b c)

/-- The Day associator carries the left-nested canonical element to
the image of the right-nested one under the base associator. -/
lemma dayAssociator_hom_app_unitElt [SmallCategory D] [MonoidalCategory D]
    (a b c : D) :
    (α_ (DayFunctor.mk (coyoneda.obj (op a)))
        (DayFunctor.mk (coyoneda.obj (op b)))
        (DayFunctor.mk (coyoneda.obj (op c)))).hom.natTrans.app
      ((a ⊗ b) ⊗ c) (dayCoyonedaUnitElt₂ a b c) =
    (DayFunctor.mk (coyoneda.obj (op a)) ⊗
      (DayFunctor.mk (coyoneda.obj (op b)) ⊗
        DayFunctor.mk (coyoneda.obj (op c)))).functor.map (α_ a b c).inv
      (dayCoyonedaUnitElt₂' a b c) := by
  have h₀ := congrArg (fun t => t.app ((a ⊗ b) ⊗ c))
    (natTrans_associator (DayFunctor.mk (coyoneda.obj (op a)))
      (DayFunctor.mk (coyoneda.obj (op b)))
      (DayFunctor.mk (coyoneda.obj (op c))))
  have h₁ := ConcreteCategory.congr_hom h₀ (dayCoyonedaUnitElt₂ a b c)
  rw [h₁]
  exact ConcreteCategory.congr_hom
    (DayConvolution.associator_hom_unit_unit (coyoneda.obj (op a))
      (coyoneda.obj (op b)) (coyoneda.obj (op c)) a b c)
    (((𝟙 a, 𝟙 b), 𝟙 c) : ((a ⟶ a) × (b ⟶ b)) × (c ⟶ c))

/-- **Day convolution of corepresentables intertwines the
associator**: under the co-Yoneda identifications, the two
reassociation routes of a triple Day tensor of corepresentables
differ by precomposition with the associator of the base. -/
lemma dayCoyonedaIso_hom_associator [SmallCategory D] [MonoidalCategory D]
    (a b c : D) :
    ((dayCoyonedaIso a b).hom ▷ DayFunctor.mk (coyoneda.obj (op c))) ≫
        (dayCoyonedaIso (a ⊗ b) c).hom ≫
        ⟨coyoneda.map ((α_ a b c).inv.op)⟩ =
      (α_ (DayFunctor.mk (coyoneda.obj (op a)))
          (DayFunctor.mk (coyoneda.obj (op b)))
          (DayFunctor.mk (coyoneda.obj (op c)))).hom ≫
        (DayFunctor.mk (coyoneda.obj (op a)) ◁
          (dayCoyonedaIso b c).hom) ≫
        (dayCoyonedaIso a (b ⊗ c)).hom := by
  apply (dayCoyonedaCorepresentableBy₂ a b c).homEquiv.injective
  change (coyoneda.map ((α_ a b c).inv.op)).app ((a ⊗ b) ⊗ c)
      ((dayCoyonedaIso (a ⊗ b) c).hom.natTrans.app ((a ⊗ b) ⊗ c)
        (((dayCoyonedaIso a b).hom ▷ DayFunctor.mk (coyoneda.obj (op c))).natTrans.app
          ((a ⊗ b) ⊗ c) (dayCoyonedaUnitElt₂ a b c))) =
    (dayCoyonedaIso a (b ⊗ c)).hom.natTrans.app ((a ⊗ b) ⊗ c)
      ((DayFunctor.mk (coyoneda.obj (op a)) ◁ (dayCoyonedaIso b c).hom).natTrans.app
        ((a ⊗ b) ⊗ c)
        ((α_ (DayFunctor.mk (coyoneda.obj (op a)))
          (DayFunctor.mk (coyoneda.obj (op b)))
          (DayFunctor.mk (coyoneda.obj (op c)))).hom.natTrans.app
          ((a ⊗ b) ⊗ c) (dayCoyonedaUnitElt₂ a b c)))
  rw [whiskerRight_dayCoyonedaIso_app_unitElt,
    dayCoyonedaIso_hom_app_unitElt, dayAssociator_hom_app_unitElt]
  have hnatl : (DayFunctor.mk (coyoneda.obj (op a)) ◁
        (dayCoyonedaIso b c).hom).natTrans.app ((a ⊗ b) ⊗ c)
        ((DayFunctor.mk (coyoneda.obj (op a)) ⊗
          (DayFunctor.mk (coyoneda.obj (op b)) ⊗
            DayFunctor.mk (coyoneda.obj (op c)))).functor.map
          (α_ a b c).inv (dayCoyonedaUnitElt₂' a b c)) =
      (DayFunctor.mk (coyoneda.obj (op a)) ⊗
        DayFunctor.mk (coyoneda.obj (op (b ⊗ c)))).functor.map
        (α_ a b c).inv
        ((DayFunctor.mk (coyoneda.obj (op a)) ◁
          (dayCoyonedaIso b c).hom).natTrans.app (a ⊗ (b ⊗ c))
          (dayCoyonedaUnitElt₂' a b c)) :=
    ConcreteCategory.congr_hom
      ((DayFunctor.mk (coyoneda.obj (op a)) ◁
        (dayCoyonedaIso b c).hom).natTrans.naturality (α_ a b c).inv)
      (dayCoyonedaUnitElt₂' a b c)
  have hnati : (dayCoyonedaIso a (b ⊗ c)).hom.natTrans.app
        ((a ⊗ b) ⊗ c)
        ((DayFunctor.mk (coyoneda.obj (op a)) ⊗
          DayFunctor.mk (coyoneda.obj (op (b ⊗ c)))).functor.map
          (α_ a b c).inv (dayCoyonedaUnitElt a (b ⊗ c))) =
      (coyoneda.obj (op (a ⊗ (b ⊗ c)))).map (α_ a b c).inv
        ((dayCoyonedaIso a (b ⊗ c)).hom.natTrans.app (a ⊗ (b ⊗ c))
          (dayCoyonedaUnitElt a (b ⊗ c))) :=
    ConcreteCategory.congr_hom
      ((dayCoyonedaIso a (b ⊗ c)).hom.natTrans.naturality
        (α_ a b c).inv)
      (dayCoyonedaUnitElt a (b ⊗ c))
  rw [hnatl, whiskerLeft_dayCoyonedaIso_app_unitElt, hnati,
    dayCoyonedaIso_hom_app_unitElt]
  show (α_ a b c).inv ≫ 𝟙 ((a ⊗ b) ⊗ c) =
    𝟙 (a ⊗ (b ⊗ c)) ≫ (α_ a b c).inv
  rw [Category.id_comp, Category.comp_id]

section Braided

/-- **Day convolution of corepresentables intertwines the
braiding**: under the co-Yoneda identifications, the braiding of the
Day tensor of two corepresentables is precomposition with the
braiding of the base. -/
lemma dayCoyonedaIso_hom_braiding
    [SmallCategory D] [MonoidalCategory D] [BraidedCategory D]
    (a b : D) :
    (β_ (DayFunctor.mk (coyoneda.obj (op a)))
        (DayFunctor.mk (coyoneda.obj (op b)))).hom ≫
      (dayCoyonedaIso b a).hom =
    (dayCoyonedaIso a b).hom ≫ ⟨coyoneda.map ((β_ b a).hom.op)⟩ := by
  apply (dayCoyonedaCorepresentableBy a b).homEquiv.injective
  change (dayCoyonedaIso b a).hom.natTrans.app (a ⊗ b)
      ((β_ (DayFunctor.mk (coyoneda.obj (op a)))
        (DayFunctor.mk (coyoneda.obj (op b)))).hom.natTrans.app (a ⊗ b)
        (dayCoyonedaUnitElt a b)) =
    (coyoneda.map ((β_ b a).hom.op)).app (a ⊗ b)
      ((dayCoyonedaIso a b).hom.natTrans.app (a ⊗ b) (dayCoyonedaUnitElt a b))
  rw [dayCoyonedaIso_hom_app_unitElt]
  have hβ : (β_ (DayFunctor.mk (coyoneda.obj (op a)))
        (DayFunctor.mk (coyoneda.obj (op b)))).hom.natTrans.app (a ⊗ b)
        (dayCoyonedaUnitElt a b) =
      (DayFunctor.mk (coyoneda.obj (op b)) ⊗
        DayFunctor.mk (coyoneda.obj (op a))).functor.map (β_ b a).hom
        ((η (DayFunctor.mk (coyoneda.obj (op b)))
          (DayFunctor.mk (coyoneda.obj (op a)))).app (b, a)
          ((𝟙 b, 𝟙 a) : (b ⟶ b) × (a ⟶ a))) :=
    ConcreteCategory.congr_hom
      (DayConvolution.unit_app_braiding_hom_app
        (coyoneda.obj (op a)) (coyoneda.obj (op b)) a b)
      ((𝟙 a, 𝟙 b) : (a ⟶ a) × (b ⟶ b))
  have hnat : (dayCoyonedaIso b a).hom.natTrans.app (a ⊗ b)
        ((DayFunctor.mk (coyoneda.obj (op b)) ⊗
          DayFunctor.mk (coyoneda.obj (op a))).functor.map (β_ b a).hom
          ((η (DayFunctor.mk (coyoneda.obj (op b)))
            (DayFunctor.mk (coyoneda.obj (op a)))).app (b, a)
            ((𝟙 b, 𝟙 a) : (b ⟶ b) × (a ⟶ a)))) =
      (coyoneda.obj (op (b ⊗ a))).map (β_ b a).hom
        ((dayCoyonedaIso b a).hom.natTrans.app (b ⊗ a)
          ((η (DayFunctor.mk (coyoneda.obj (op b)))
            (DayFunctor.mk (coyoneda.obj (op a)))).app (b, a)
            ((𝟙 b, 𝟙 a) : (b ⟶ b) × (a ⟶ a)))) :=
    ConcreteCategory.congr_hom
      ((dayCoyonedaIso b a).hom.natTrans.naturality (β_ b a).hom)
      ((η (DayFunctor.mk (coyoneda.obj (op b)))
        (DayFunctor.mk (coyoneda.obj (op a)))).app (b, a)
        ((𝟙 b, 𝟙 a) : (b ⟶ b) × (a ⟶ a)))
  have hid : (dayCoyonedaIso b a).hom.natTrans.app (b ⊗ a)
        ((η (DayFunctor.mk (coyoneda.obj (op b)))
          (DayFunctor.mk (coyoneda.obj (op a)))).app (b, a)
          ((𝟙 b, 𝟙 a) : (b ⟶ b) × (a ⟶ a))) = 𝟙 b ⊗ₘ 𝟙 a := by
    have h := congrArg (fun t => t.app (b, a))
      (eta_comp_dayCoyonedaIso_hom b a)
    exact ConcreteCategory.congr_hom h ((𝟙 b, 𝟙 a) : (b ⟶ b) × (a ⟶ a))
  rw [hβ, hnat, hid]
  show (𝟙 b ⊗ₘ 𝟙 a) ≫ (β_ b a).hom = (β_ b a).hom ≫ 𝟙 (a ⊗ b)
  rw [MonoidalCategory.id_tensorHom_id, Category.id_comp,
    Category.comp_id]

end Braided

/-- The forward and reversed transports along `RS.dayMkIso`
compose to the identity. -/
lemma dayMkIso_hom_symm_hom [SmallCategory D] [MonoidalCategory D]
    {A B : Dᵒᵖ ⥤ Type v}
    (e : A ≅ B) :
    (dayMkIso e).hom ≫ (dayMkIso e.symm).hom =
      𝟙 (DayFunctor.mk A : Dᵒᵖ ⊛⥤ Type v) :=
  (dayMkIso e).hom_inv_id

/-- Cancellation form of `RS.dayMkIso_hom_symm_hom`, stated against
a leading morphism so that no identity is left behind. -/
lemma comp_dayMkIso_hom_symm_hom [SmallCategory D] [MonoidalCategory D]
    {A B : Dᵒᵖ ⥤ Type v} (e : A ≅ B)
    {X : Dᵒᵖ ⊛⥤ Type v} (f : X ⟶ DayFunctor.mk A) :
    f ≫ (dayMkIso e).hom ≫ (dayMkIso e.symm).hom = f := by
  rw [dayMkIso_hom_symm_hom, Category.comp_id]

end DayCalculusMore

section YonedaTransport

variable {C : Type v}

/-- Naturality of `Coyoneda.objOpOp`, forward form, at a general
double-opposite morphism. -/
lemma coyoneda_map_op_op_comp_objOpOp_hom [SmallCategory C]
    {z z' : C} (u : z ⟶ z') :
    coyoneda.map (u.op.op) ≫ (Coyoneda.objOpOp z').hom =
      (Coyoneda.objOpOp z).hom ≫ yoneda.map u := by
  ext w t
  simp [Coyoneda.objOpOp, opEquiv]

/-- **The Day tensor of representables intertwines the braiding**:
the Yoneda form of `RS.dayCoyonedaIso_hom_braiding`. -/
lemma dayYonedaIso_hom_braiding [SmallCategory C] [MonoidalCategory C]
    [BraidedCategory C] (x y : C) :
    (β_ (DayFunctor.mk (yoneda.obj x))
        (DayFunctor.mk (yoneda.obj y))).hom ≫ (dayYonedaIso y x).hom =
      (dayYonedaIso x y).hom ≫ ⟨yoneda.map (β_ x y).hom⟩ := by
  have s₂ : (⟨coyoneda.map ((β_ (op y) (op x)).hom.op)⟩ :
        DayFunctor.mk (coyoneda.obj (op (op x ⊗ op y))) ⟶
          DayFunctor.mk (coyoneda.obj (op (op y ⊗ op x)))) ≫
        (dayMkIso (Coyoneda.objOpOp (y ⊗ x))).hom =
      (dayMkIso (Coyoneda.objOpOp (x ⊗ y))).hom ≫
        ⟨yoneda.map (β_ x y).hom⟩ := by
    ext1
    exact coyoneda_map_op_op_comp_objOpOp_hom (β_ x y).hom
  have e₁ : (β_ (DayFunctor.mk (yoneda.obj x))
        (DayFunctor.mk (yoneda.obj y))).hom ≫
        ((dayMkIso (Coyoneda.objOpOp y).symm).hom ⊗ₘ
          (dayMkIso (Coyoneda.objOpOp x).symm).hom) =
      ((dayMkIso (Coyoneda.objOpOp x).symm).hom ⊗ₘ
          (dayMkIso (Coyoneda.objOpOp y).symm).hom) ≫
        (β_ (DayFunctor.mk (coyoneda.obj (op (op x))))
          (DayFunctor.mk (coyoneda.obj (op (op y))))).hom :=
    (BraidedCategory.braiding_naturality _ _).symm
  simp only [dayYonedaIso, Iso.trans_hom, tensorIso_hom]
  rw [← Category.assoc, e₁, Category.assoc,
    reassoc_of% dayCoyonedaIso_hom_braiding (D := Cᵒᵖ) (op x) (op y),
    s₂]
  simp only [Category.assoc]

/-- **The Day tensor of representables intertwines the associator**:
the Yoneda form of `RS.dayCoyonedaIso_hom_associator`. -/
lemma dayYonedaIso_hom_associator [SmallCategory C] [MonoidalCategory C]
    (x y z : C) :
    ((dayYonedaIso x y).hom ▷ DayFunctor.mk (yoneda.obj z)) ≫
        (dayYonedaIso (x ⊗ y) z).hom ≫ ⟨yoneda.map (α_ x y z).hom⟩ =
      (α_ (DayFunctor.mk (yoneda.obj x)) (DayFunctor.mk (yoneda.obj y))
          (DayFunctor.mk (yoneda.obj z))).hom ≫
        (DayFunctor.mk (yoneda.obj x) ◁ (dayYonedaIso y z).hom) ≫
        (dayYonedaIso x (y ⊗ z)).hom := by
  have s₂ : (⟨coyoneda.map ((α_ (op x) (op y) (op z)).inv.op)⟩ :
        DayFunctor.mk (coyoneda.obj (op (op ((x ⊗ y) ⊗ z)))) ⟶
          DayFunctor.mk (coyoneda.obj (op (op (x ⊗ (y ⊗ z)))))) ≫
        (dayMkIso (Coyoneda.objOpOp (x ⊗ (y ⊗ z)))).hom =
      (dayMkIso (Coyoneda.objOpOp ((x ⊗ y) ⊗ z))).hom ≫
        ⟨yoneda.map (α_ x y z).hom⟩ := by
    ext1
    exact coyoneda_map_op_op_comp_objOpOp_hom (α_ x y z).hom
  have hassoc : ((dayCoyonedaIso (op x) (op y)).hom ▷
        DayFunctor.mk (coyoneda.obj (op (op z)))) ≫
        (dayCoyonedaIso (op (x ⊗ y)) (op z)).hom ≫
        (⟨coyoneda.map ((α_ (op x) (op y) (op z)).inv.op)⟩ :
          DayFunctor.mk (coyoneda.obj (op (op ((x ⊗ y) ⊗ z)))) ⟶
            DayFunctor.mk (coyoneda.obj (op (op (x ⊗ (y ⊗ z)))))) =
      (α_ (DayFunctor.mk (coyoneda.obj (op (op x))))
          (DayFunctor.mk (coyoneda.obj (op (op y))))
          (DayFunctor.mk (coyoneda.obj (op (op z))))).hom ≫
        (DayFunctor.mk (coyoneda.obj (op (op x))) ◁
          (dayCoyonedaIso (op y) (op z)).hom) ≫
        (dayCoyonedaIso (op x) (op (y ⊗ z))).hom :=
    dayCoyonedaIso_hom_associator (D := Cᵒᵖ) (op x) (op y) (op z)
  have e_left : ((((dayMkIso (Coyoneda.objOpOp x).symm).hom ⊗ₘ
          (dayMkIso (Coyoneda.objOpOp y).symm).hom) ≫
          (dayCoyonedaIso (op x) (op y)).hom ≫
          (dayMkIso (Coyoneda.objOpOp (x ⊗ y))).hom) ▷
          DayFunctor.mk (yoneda.obj z)) ≫
        ((dayMkIso (Coyoneda.objOpOp (x ⊗ y)).symm).hom ⊗ₘ
          (dayMkIso (Coyoneda.objOpOp z).symm).hom) =
      (((dayMkIso (Coyoneda.objOpOp x).symm).hom ⊗ₘ
          (dayMkIso (Coyoneda.objOpOp y).symm).hom) ⊗ₘ
          (dayMkIso (Coyoneda.objOpOp z).symm).hom) ≫
        ((dayCoyonedaIso (op x) (op y)).hom ▷
          DayFunctor.mk (coyoneda.obj (op (op z)))) := by
    rw [← MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp,
      ← MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
    simp only [Category.assoc, comp_dayMkIso_hom_symm_hom]
  have e_right : ((dayMkIso (Coyoneda.objOpOp x).symm).hom ⊗ₘ
          ((dayMkIso (Coyoneda.objOpOp y).symm).hom ⊗ₘ
            (dayMkIso (Coyoneda.objOpOp z).symm).hom)) ≫
        (DayFunctor.mk (coyoneda.obj (op (op x))) ◁
          (dayCoyonedaIso (op y) (op z)).hom) =
      (DayFunctor.mk (yoneda.obj x) ◁
          (((dayMkIso (Coyoneda.objOpOp y).symm).hom ⊗ₘ
            (dayMkIso (Coyoneda.objOpOp z).symm).hom) ≫
            (dayCoyonedaIso (op y) (op z)).hom ≫
            (dayMkIso (Coyoneda.objOpOp (y ⊗ z))).hom)) ≫
        ((dayMkIso (Coyoneda.objOpOp x).symm).hom ⊗ₘ
          (dayMkIso (Coyoneda.objOpOp (y ⊗ z)).symm).hom) := by
    rw [← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id,
      ← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
    simp only [Category.assoc, comp_dayMkIso_hom_symm_hom]
  simp only [dayYonedaIso, Iso.trans_hom, tensorIso_hom]
  calc _ = ((((dayMkIso (Coyoneda.objOpOp x).symm).hom ⊗ₘ
          (dayMkIso (Coyoneda.objOpOp y).symm).hom) ≫
          (dayCoyonedaIso (op x) (op y)).hom ≫
          (dayMkIso (Coyoneda.objOpOp (x ⊗ y))).hom) ▷
          DayFunctor.mk (yoneda.obj z)) ≫
        ((dayMkIso (Coyoneda.objOpOp (x ⊗ y)).symm).hom ⊗ₘ
          (dayMkIso (Coyoneda.objOpOp z).symm).hom) ≫
        ((dayCoyonedaIso (op (x ⊗ y)) (op z)).hom ≫
          (dayMkIso (Coyoneda.objOpOp ((x ⊗ y) ⊗ z))).hom ≫
          ⟨yoneda.map (α_ x y z).hom⟩) := by
        simp only [Category.assoc]
    _ = (((dayMkIso (Coyoneda.objOpOp x).symm).hom ⊗ₘ
          (dayMkIso (Coyoneda.objOpOp y).symm).hom) ⊗ₘ
          (dayMkIso (Coyoneda.objOpOp z).symm).hom) ≫
        ((dayCoyonedaIso (op x) (op y)).hom ▷
          DayFunctor.mk (coyoneda.obj (op (op z)))) ≫
        (dayCoyonedaIso (op (x ⊗ y)) (op z)).hom ≫
        (⟨coyoneda.map ((α_ (op x) (op y) (op z)).inv.op)⟩ :
          DayFunctor.mk (coyoneda.obj (op (op ((x ⊗ y) ⊗ z)))) ⟶
            DayFunctor.mk (coyoneda.obj (op (op (x ⊗ (y ⊗ z)))))) ≫
        (dayMkIso (Coyoneda.objOpOp (x ⊗ (y ⊗ z)))).hom := by
        rw [← Category.assoc, e_left, ← s₂]
        simp only [Category.assoc]
    _ = (((dayMkIso (Coyoneda.objOpOp x).symm).hom ⊗ₘ
          (dayMkIso (Coyoneda.objOpOp y).symm).hom) ⊗ₘ
          (dayMkIso (Coyoneda.objOpOp z).symm).hom) ≫
        (α_ (DayFunctor.mk (coyoneda.obj (op (op x))))
          (DayFunctor.mk (coyoneda.obj (op (op y))))
          (DayFunctor.mk (coyoneda.obj (op (op z))))).hom ≫
        (DayFunctor.mk (coyoneda.obj (op (op x))) ◁
          (dayCoyonedaIso (op y) (op z)).hom) ≫
        (dayCoyonedaIso (op x) (op (y ⊗ z))).hom ≫
        (dayMkIso (Coyoneda.objOpOp (x ⊗ (y ⊗ z)))).hom := by
        rw [reassoc_of% hassoc]
    _ = _ := by
        rw [MonoidalCategory.associator_naturality_assoc,
          reassoc_of% e_right]

end YonedaTransport

section IndTransport

variable {C : Type v}

/-- The embedding into the Day presheaf category carries the
embedding-tensor comparison to the Day-level comparison. -/
lemma indToDay_map_indOfTensorIso_hom [SmallCategory C] [MonoidalCategory C]
    (x y : C) :
    (indToDay (C := C)).map (indOfTensorIso x y).hom =
      (indToDayTensorIso x y).hom := by
  rw [indOfTensorIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage]

section Braided

/-- The indization equivalence's forward functor is braided: the
braiding of `Ind C` is transported across it. -/
instance [SmallCategory C] [MonoidalCategory C] [BraidedCategory C] :
    (indDayEquivalence C).functor.Braided :=
  inferInstanceAs
    (Monoidal.equivalenceTransported
      ((indDayEquivalence C).symm)).inverse.Braided

/-- The embedding into the Day presheaf category is braided. -/
instance [SmallCategory C] [MonoidalCategory C] [BraidedCategory C] :
    (indToDay (C := C)).Braided :=
  inferInstanceAs
    ((indDayEquivalence C).functor ⋙ ObjectProperty.ι _).Braided

/-- **The embedding-tensor comparison intertwines the braiding**:
`indOf` with `indOfTensorIso` is a braided functor up to
isomorphism. -/
lemma indOfTensorIso_hom_braiding
    [SmallCategory C] [MonoidalCategory C] [BraidedCategory C]
    (x y : C) :
    (β_ (indOf.obj x) (indOf.obj y)).hom ≫ (indOfTensorIso y x).hom =
      (indOfTensorIso x y).hom ≫ indOf.map (β_ x y).hom := by
  apply (indToDay (C := C)).map_injective
  rw [Functor.map_comp, Functor.map_comp,
    indToDay_map_indOfTensorIso_hom, indToDay_map_indOfTensorIso_hom,
    Functor.map_braiding]
  simp only [indToDayTensorIso, Iso.trans_hom, Iso.symm_hom,
    tensorIso_hom, Functor.Monoidal.μIso_inv, Category.assoc,
    Functor.Monoidal.μ_δ_assoc]
  rw [← BraidedCategory.braiding_naturality_assoc,
    reassoc_of% dayYonedaIso_hom_braiding x y,
    comp_indToDayIndOfIso_inv]

end Braided

/-- **The embedding-tensor comparison intertwines the associator**:
the associativity axiom of the monoidal-functor-up-to-isomorphism
structure of `indOf`. -/
lemma indOfTensorIso_hom_associator [SmallCategory C] [MonoidalCategory C]
    (x y z : C) :
    ((indOfTensorIso x y).hom ▷ indOf.obj z) ≫
        (indOfTensorIso (x ⊗ y) z).hom ≫ indOf.map (α_ x y z).hom =
      (α_ (indOf.obj x) (indOf.obj y) (indOf.obj z)).hom ≫
        (indOf.obj x ◁ (indOfTensorIso y z).hom) ≫
        (indOfTensorIso x (y ⊗ z)).hom := by
  apply (indToDay (C := C)).map_injective
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp,
    Functor.map_comp,
    Functor.Monoidal.map_whiskerRight (F := indToDay (C := C)),
    Functor.Monoidal.map_whiskerLeft (F := indToDay (C := C)),
    Functor.Monoidal.map_associator (F := indToDay (C := C)),
    indToDay_map_indOfTensorIso_hom, indToDay_map_indOfTensorIso_hom,
    indToDay_map_indOfTensorIso_hom, indToDay_map_indOfTensorIso_hom]
  simp only [indToDayTensorIso, Iso.trans_hom, Iso.symm_hom,
    tensorIso_hom, Functor.Monoidal.μIso_inv, Category.assoc,
    Functor.Monoidal.μ_δ_assoc, MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp]
  have hA : ((indToDayIndOfIso (x ⊗ y)).inv ▷
        (indToDay (C := C)).obj (indOf.obj z)) ≫
        ((indToDayIndOfIso (x ⊗ y)).hom ⊗ₘ (indToDayIndOfIso z).hom) =
      DayFunctor.mk (yoneda.obj (x ⊗ y)) ◁ (indToDayIndOfIso z).hom := by
    rw [← MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_comp_tensorHom, Iso.inv_hom_id,
      Category.id_comp, MonoidalCategory.id_tensorHom]
  have hB : ((dayYonedaIso x y).hom ▷
        (indToDay (C := C)).obj (indOf.obj z)) ≫
        (DayFunctor.mk (yoneda.obj (x ⊗ y)) ◁ (indToDayIndOfIso z).hom) =
      ((DayFunctor.mk (yoneda.obj x) ⊗ DayFunctor.mk (yoneda.obj y)) ◁
          (indToDayIndOfIso z).hom) ≫
        ((dayYonedaIso x y).hom ▷ DayFunctor.mk (yoneda.obj z)) :=
    (MonoidalCategory.whisker_exchange _ _).symm
  have hC : (((indToDayIndOfIso x).hom ⊗ₘ (indToDayIndOfIso y).hom) ▷
        (indToDay (C := C)).obj (indOf.obj z)) ≫
        ((DayFunctor.mk (yoneda.obj x) ⊗ DayFunctor.mk (yoneda.obj y)) ◁
          (indToDayIndOfIso z).hom) =
      ((indToDayIndOfIso x).hom ⊗ₘ (indToDayIndOfIso y).hom) ⊗ₘ
        (indToDayIndOfIso z).hom :=
    (MonoidalCategory.tensorHom_def _ _).symm
  have hD : ((indToDay (C := C)).obj (indOf.obj x) ◁
        (indToDayIndOfIso (y ⊗ z)).inv) ≫
        ((indToDayIndOfIso x).hom ⊗ₘ (indToDayIndOfIso (y ⊗ z)).hom) =
      (indToDayIndOfIso x).hom ▷ DayFunctor.mk (yoneda.obj (y ⊗ z)) := by
    rw [← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom, Iso.inv_hom_id,
      Category.id_comp, MonoidalCategory.tensorHom_id]
  have hE : ((indToDay (C := C)).obj (indOf.obj x) ◁
        (dayYonedaIso y z).hom) ≫
        ((indToDayIndOfIso x).hom ▷ DayFunctor.mk (yoneda.obj (y ⊗ z))) =
      ((indToDayIndOfIso x).hom ▷
          (DayFunctor.mk (yoneda.obj y) ⊗ DayFunctor.mk (yoneda.obj z))) ≫
        (DayFunctor.mk (yoneda.obj x) ◁ (dayYonedaIso y z).hom) :=
    MonoidalCategory.whisker_exchange _ _
  have hF : ((indToDay (C := C)).obj (indOf.obj x) ◁
        ((indToDayIndOfIso y).hom ⊗ₘ (indToDayIndOfIso z).hom)) ≫
        ((indToDayIndOfIso x).hom ▷
          (DayFunctor.mk (yoneda.obj y) ⊗ DayFunctor.mk (yoneda.obj z))) =
      (indToDayIndOfIso x).hom ⊗ₘ
        ((indToDayIndOfIso y).hom ⊗ₘ (indToDayIndOfIso z).hom) :=
    (MonoidalCategory.tensorHom_def' _ _).symm
  rw [reassoc_of% hA, reassoc_of% hB, reassoc_of% hC,
    ← comp_indToDayIndOfIso_inv,
    reassoc_of% dayYonedaIso_hom_associator x y z,
    reassoc_of% hD, reassoc_of% hE, reassoc_of% hF,
    MonoidalCategory.associator_naturality_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, Functor.Monoidal.μ_δ,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

section Powers

/-- **The tensor powers of an embedded object are the embedded
tensor powers**: `n = 0` is `RS.indOfUnitIso`, and each successor
stage tensors the previous one with `indOf.obj X` and applies the
embedding-tensor comparison. -/
def indOfPowIso [SmallCategory C] [MonoidalCategory C]
    (X : C) : (n : ℕ) →
    (tensorPow (Ind C) (indOf.obj X) n ≅ indOf.obj (tensorPow C X n))
  | 0 => indOfUnitIso
  | n + 1 =>
      whiskerRightIso (indOfPowIso X n) (indOf.obj X) ≪≫
        indOfTensorIso (tensorPow C X n) X

/-- The base case of the power comparison. -/
@[simp]
theorem indOfPowIso_zero [SmallCategory C] [MonoidalCategory C]
    (X : C) :
    indOfPowIso X 0 = indOfUnitIso := rfl

/-- The defining recursion of the power comparison. -/
theorem indOfPowIso_succ [SmallCategory C] [MonoidalCategory C]
    (X : C) (n : ℕ) :
    indOfPowIso X (n + 1) =
      whiskerRightIso (indOfPowIso X n) (indOf.obj X) ≪≫
        indOfTensorIso (tensorPow C X n) X := rfl

end Powers

section Perm

/-- The braiding conjugate defining `swapTop` passes doubly
whiskered morphisms, with an arbitrary tail. -/
private lemma swap_conj_pass
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C]
    {P Q Z : Ind C} (g : P ⟶ Q) {R : Ind C}
    (h : (Q ⊗ Z) ⊗ Z ⟶ R) :
    (α_ P Z Z).hom ≫ (P ◁ (β_ Z Z).hom) ≫ (α_ P Z Z).inv ≫
        ((g ▷ Z) ▷ Z) ≫ h =
      ((g ▷ Z) ▷ Z) ≫ (α_ Q Z Z).hom ≫ (Q ◁ (β_ Z Z).hom) ≫
        (α_ Q Z Z).inv ≫ h := by
  rw [MonoidalCategory.associator_naturality_left_assoc,
    ← MonoidalCategory.whisker_exchange_assoc,
    MonoidalCategory.associator_inv_naturality_left_assoc]

/-- The embedding-tensor comparison conjugates the braiding block of
`swapTop` to its embedded form. -/
lemma indOfTensorIso_swap_conj
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C]
    (a z : C) :
    (α_ (indOf.obj a) (indOf.obj z) (indOf.obj z)).hom ≫
        (indOf.obj a ◁ (β_ (indOf.obj z) (indOf.obj z)).hom) ≫
        (α_ (indOf.obj a) (indOf.obj z) (indOf.obj z)).inv ≫
        ((indOfTensorIso a z).hom ▷ indOf.obj z) ≫
        (indOfTensorIso (a ⊗ z) z).hom =
      ((indOfTensorIso a z).hom ▷ indOf.obj z) ≫
        (indOfTensorIso (a ⊗ z) z).hom ≫
        indOf.map
          ((α_ a z z).hom ≫ (a ◁ (β_ z z).hom) ≫ (α_ a z z).inv) := by
  have hArev : (indOf.obj a ◁ (indOfTensorIso z z).hom) ≫
      (indOfTensorIso a (z ⊗ z)).hom =
      (α_ (indOf.obj a) (indOf.obj z) (indOf.obj z)).inv ≫
        ((indOfTensorIso a z).hom ▷ indOf.obj z) ≫
        (indOfTensorIso (a ⊗ z) z).hom ≫
        indOf.map (α_ a z z).hom := by
    rw [indOfTensorIso_hom_associator, Iso.inv_hom_id_assoc]
  rw [Functor.map_comp, Functor.map_comp,
    reassoc_of% indOfTensorIso_hom_associator a z z,
    ← reassoc_of% indOfTensorIso_hom_natural_right a (β_ z z).hom,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← indOfTensorIso_hom_braiding z z,
    MonoidalCategory.whiskerLeft_comp_assoc,
    reassoc_of% hArev, Iso.map_hom_inv_id, Category.comp_id]

/-- **Transport of the top braiding**: `swapTop` on the powers of an
embedded object is conjugate to the embedded `swapTop`. -/
lemma indOfPowIso_swapTop
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C]
    (X : C) (n : ℕ) :
    swapTop (indOf.obj X) n ≫ (indOfPowIso X (n + 2)).hom =
      (indOfPowIso X (n + 2)).hom ≫ indOf.map (swapTop X n) := by
  show ((α_ (tensorPow (Ind C) (indOf.obj X) n) (indOf.obj X)
        (indOf.obj X)).hom ≫
      (tensorPow (Ind C) (indOf.obj X) n ◁
        (β_ (indOf.obj X) (indOf.obj X)).hom) ≫
      (α_ (tensorPow (Ind C) (indOf.obj X) n) (indOf.obj X)
        (indOf.obj X)).inv) ≫
      ((((indOfPowIso X n).hom ▷ indOf.obj X) ≫
        (indOfTensorIso (tensorPow C X n) X).hom) ▷ indOf.obj X) ≫
      (indOfTensorIso (tensorPow C X n ⊗ X) X).hom =
    (((((indOfPowIso X n).hom ▷ indOf.obj X) ≫
        (indOfTensorIso (tensorPow C X n) X).hom) ▷ indOf.obj X) ≫
      (indOfTensorIso (tensorPow C X n ⊗ X) X).hom) ≫
      indOf.map ((α_ (tensorPow C X n) X X).hom ≫
        (tensorPow C X n ◁ (β_ X X).hom) ≫
        (α_ (tensorPow C X n) X X).inv)
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [swap_conj_pass (indOfPowIso X n).hom, indOfTensorIso_swap_conj]

/-- Whiskering by one more embedded factor preserves the transport
relation. -/
lemma indOfPowIso_whiskerRight [SmallCategory C] [MonoidalCategory C]
    (X : C) {m : ℕ}
    {f : tensorPow (Ind C) (indOf.obj X) m ⟶
      tensorPow (Ind C) (indOf.obj X) m}
    {u : tensorPow C X m ⟶ tensorPow C X m}
    (h : f ≫ (indOfPowIso X m).hom =
      (indOfPowIso X m).hom ≫ indOf.map u) :
    (f ▷ indOf.obj X) ≫ (indOfPowIso X (m + 1)).hom =
      (indOfPowIso X (m + 1)).hom ≫ indOf.map (u ▷ X) := by
  show (f ▷ indOf.obj X) ≫
      (((indOfPowIso X m).hom ▷ indOf.obj X) ≫
        (indOfTensorIso (tensorPow C X m) X).hom) =
    (((indOfPowIso X m).hom ▷ indOf.obj X) ≫
      (indOfTensorIso (tensorPow C X m) X).hom) ≫ indOf.map (u ▷ X)
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, h,
    MonoidalCategory.comp_whiskerRight, Category.assoc,
    indOfTensorIso_hom_natural_left, ← Category.assoc]

/-- Two morphisms transported across the power comparison compose to
the transported composite.  Stated at general objects, so that no
tensor-power arity enters the rewriting. -/
private lemma step_pass_map [SmallCategory C]
    {P : Ind C} {p : C} {s u : P ⟶ P}
    {T : P ⟶ indOf.obj p} {s₀ u₀ : p ⟶ p}
    (hs : s ≫ T = T ≫ indOf.map s₀)
    (hu : u ≫ T = T ≫ indOf.map u₀) :
    (s ≫ u) ≫ T = T ≫ indOf.map (s₀ ≫ u₀) := by
  rw [Functor.map_comp, Category.assoc, hu, ← Category.assoc, hs,
    Category.assoc]

/-- **Transport of the insertion cycle**: `insertTop` on the powers
of an embedded object is conjugate to the embedded `insertTop`. -/
lemma indOfPowIso_insertTop
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C]
    (X : C) : ∀ n k : ℕ,
    insertTop (indOf.obj X) n k ≫ (indOfPowIso X (n + 1)).hom =
      (indOfPowIso X (n + 1)).hom ≫ indOf.map (insertTop X n k) := by
  intro n
  induction n with
  | zero =>
    intro k
    rw [insertTop_of_zero, insertTop_of_zero, Category.id_comp,
      CategoryTheory.Functor.map_id, Category.comp_id]
  | succ n ih =>
    intro k
    cases k with
    | zero =>
      rw [insertTop_zero, insertTop_zero, Category.id_comp,
        CategoryTheory.Functor.map_id, Category.comp_id]
    | succ k =>
      exact step_pass_map (indOfPowIso_swapTop X n)
        (indOfPowIso_whiskerRight X (ih k))

/-- **Transport of the permutation action** along the embedding
`C ⥤ Ind C`: the action of a permutation on the tensor powers of an
embedded object is conjugate, under `RS.indOfPowIso`, to the
embedded action. -/
theorem indOfPowIso_permMor
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C]
    (X : C) : ∀ (n : ℕ)
    (σ : Equiv.Perm (Fin n)),
    permMor (indOf.obj X) n σ ≫ (indOfPowIso X n).hom =
      (indOfPowIso X n).hom ≫ indOf.map (permMor X n σ) := by
  intro n
  induction n with
  | zero =>
    intro σ
    show 𝟙 _ ≫ _ = _ ≫ indOf.map (𝟙 _)
    rw [Category.id_comp, CategoryTheory.Functor.map_id,
      Category.comp_id]
  | succ m ih =>
    intro σ
    exact step_pass_map
      (indOfPowIso_whiskerRight X (ih (restPerm σ)))
      (indOfPowIso_insertTop X m (m - (topImage σ : ℕ)))

/-- Conjugation form of `RS.indOfPowIso_permMor`. -/
theorem permMor_indOf_conj
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C]
    (X : C) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permMor (indOf.obj X) n σ =
      (indOfPowIso X n).hom ≫ indOf.map (permMor X n σ) ≫
        (indOfPowIso X n).inv := by
  rw [← reassoc_of% indOfPowIso_permMor X n σ, Iso.hom_inv_id,
    Category.comp_id]

end Perm

section Schur

/-- **The faithfulness bridge**: the embedding `C ⥤ Ind C` reflects
and preserves vanishing of morphisms. -/
lemma indOf_map_eq_zero_iff
    [SmallCategory C] [Preadditive C] [HasFiniteColimits C]
    {P Q : C} (f : P ⟶ Q) :
    indOf.map f = 0 ↔ f = 0 := by
  haveI : HasFiniteBiproducts C :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  haveI : indOf.PreservesZeroMorphisms (C := C) :=
    Functor.preservesZeroMorphisms_of_map_zero_object
      ((isZero_indOf (isZero_zero C)).isoZero)
  constructor
  · intro h
    apply indOf.map_injective
    rw [h, Functor.map_zero]
  · intro h
    rw [h, Functor.map_zero]

/-- Vanishing of the permutation action on an embedded object is
vanishing of the embedded action. -/
theorem permMor_indOf_eq_zero_iff_map
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [SymmetricCategory C]
    (X : C) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    permMor (indOf.obj X) n σ = 0 ↔
      indOf.map (permMor X n σ) = 0 := by
  rw [permMor_indOf_conj X n σ]
  constructor
  · intro h
    have := (indOfPowIso X n).inv ≫= h =≫ (indOfPowIso X n).hom
    simpa using this
  · intro h
    rw [h, zero_comp, comp_zero]

/-- **Vanishing of the permutation action transports faithfully
along the embedding `C ⥤ Ind C`.**  This is the `permMor`-level form
of Schur-vanishing transport: the group-algebra form waits on a
`Linear ℂ (Ind C)` instance, which the Mathlib pin does not
provide. -/
theorem permMor_indOf_eq_zero_iff
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [SymmetricCategory C]
    (X : C) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    permMor (indOf.obj X) n σ = 0 ↔ permMor X n σ = 0 := by
  rw [permMor_indOf_eq_zero_iff_map, indOf_map_eq_zero_iff]

end Schur

section SchurBridge

/-- **Schur vanishing, read through the embedding**: the shape `μ`
kills `X` precisely when the embedded action of its block idempotent
vanishes.  Together with `RS.permMor_indOf_eq_zero_iff` this is the
substrate for transporting `RS.SchurKilled` to `Ind C`; phrasing the
`Ind C` side through `permAlg` needs `Linear ℂ (Ind C)`, which is a
mainline decision. -/
theorem schurKilled_iff_indOf_map_permAlg_eq_zero
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C]
    [Preadditive C] [Linear ℂ C] [HasFiniteColimits C]
    (P : SchurPackage.{v}) (X : C) (μ : YoungDiagram) :
    SchurKilled P X μ ↔
      indOf.map (permAlg X μ.card (P.e μ)) = 0 :=
  (indOf_map_eq_zero_iff (permAlg X μ.card (P.e μ))).symm

end SchurBridge

end IndTransport

end

end RS
