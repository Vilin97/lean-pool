/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModMulti

/-!
# Crossing the monoid over a block of the multi-tensor

The endgame of `ModMulti.lean`: the braided crossing of the monoid
`A` over a whole first block of modules factors through the slot
relations of the multi-tensor.  From it, the concatenation map
descends through the binary `modTensor` of two bundled multi-tensor
modules, and the braiding of two adjacent factors descends to the
two-element multi-tensor.

* `modCrossMid`, `modCrossLegOf`: the boundary-insertion carrier —
  the monoid seated between two blocks, under a prefix — and its
  assembly of a boundary window into a prefix-whiskered leg.
* `modCrossHeadWin`/`modCrossYWin`: the two boundary windows — the
  monoid crosses the whole first block and acts on its head, or
  acts on the head of the second block.
* `modCross_rel`: **the fold-level crossing relation** — the two
  boundary legs agree after the projection, at every prefix; the
  crossing is consumed one factor at a time, one slot relation per
  factor.
* `modListCross`: the prefix-free crossing relation, in the typed
  form consumed by the `modTensor` descent.
* `modTensorMulti`: the concatenation map descended through the
  binary module tensor product of two bundled multi-tensors, with
  its defining equation `modTensorπ_multi`.
* `modWinSwap`, `modMultiSwapPair`: the braiding of the two factors
  of a two-element multi-tensor, by descent through the single slot
  relation, with its defining equation `modMultiπ_swapPair`.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## The boundary-insertion carrier

The monoid seated at the boundary between two blocks, under a
prefix.  The prefix enters by recursion, exactly as in
`modMultiMid`, so that slot-relation consumption below can match
prefixes on the nose. -/

section CrossDefs

/-- The boundary-insertion object: the monoid between the folds of
two blocks, whiskered under a prefix. -/
def modCrossMid [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (Xs Ys : List (Mod D A)) :
    List (Mod D A) → D
  | [] => (modList A Xs ⊗ A) ⊗ modList A Ys
  | P :: rest => P.X ⊗ modCrossMid A Xs Ys rest

@[simp] lemma modCrossMid_nil
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (Xs Ys : List (Mod D A)) :
    modCrossMid A Xs Ys [] = (modList A Xs ⊗ A) ⊗ modList A Ys :=
  rfl

@[simp] lemma modCrossMid_cons
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (Xs Ys : List (Mod D A))
    (P : Mod D A) (pre : List (Mod D A)) :
    modCrossMid A Xs Ys (P :: pre) =
      P.X ⊗ modCrossMid A Xs Ys pre :=
  rfl

/-- Assemble a boundary window into a prefix-whiskered leg. -/
def modCrossLegOf [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (Xs Ys : List (Mod D A))
    (w : (modList A Xs ⊗ A) ⊗ modList A Ys ⟶ modList A (Xs ++ Ys)) :
    (pre : List (Mod D A)) →
      modCrossMid A Xs Ys pre ⟶ modList A (pre ++ (Xs ++ Ys))
  | [] => w
  | P :: rest => P.X ◁ modCrossLegOf A Xs Ys w rest

@[simp] lemma modCrossLegOf_nil
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (Xs Ys : List (Mod D A))
    (w : (modList A Xs ⊗ A) ⊗ modList A Ys ⟶ modList A (Xs ++ Ys)) :
    modCrossLegOf A Xs Ys w [] = w :=
  rfl

@[simp] lemma modCrossLegOf_cons
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (Xs Ys : List (Mod D A))
    (w : (modList A Xs ⊗ A) ⊗ modList A Ys ⟶ modList A (Xs ++ Ys))
    (P : Mod D A) (pre : List (Mod D A)) :
    modCrossLegOf A Xs Ys w (P :: pre) =
      P.X ◁ modCrossLegOf A Xs Ys w pre :=
  rfl

end CrossDefs

/-! ## The two boundary windows -/

section CrossWindows

/-- The crossing window: the monoid braids over the whole first
block and acts on its head. -/
def modCrossHeadWin [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D]
    (X : Mod D A) (l Ys : List (Mod D A)) :
    (modList A (X :: l) ⊗ A) ⊗ modList A Ys ⟶
      modList A ((X :: l) ++ Ys) :=
  (((β_ (modList A (X :: l)) A).hom ≫ modListHeadAct A X l) ▷
      modList A Ys) ≫
    (modListConcat A (X :: l) Ys).hom

/-- The stationary window: the monoid acts on the head of the
second block. -/
def modCrossYWin [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (Xs : List (Mod D A)) (Y : Mod D A)
    (m : List (Mod D A)) :
    (modList A Xs ⊗ A) ⊗ modList A (Y :: m) ⟶
      modList A (Xs ++ (Y :: m)) :=
  (α_ (modList A Xs) A (modList A (Y :: m))).hom ≫
    (modList A Xs ◁ modListHeadAct A Y m) ≫
    (modListConcat A Xs (Y :: m)).hom

end CrossWindows

/-! ## The singleton first block

For a one-module first block the two boundary windows are the two
relation legs of the head slot, up to the unit seed of the fold.
The bridge below absorbs the seed and retypes the boundary carrier
at the relation object of the slot. -/

section CrossBase

/-- The base bridge: absorb the unit seed of a singleton first
block and reassociate onto the relation window of the head slot. -/
def modCrossBridge [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X Y : Mod D A) (m : List (Mod D A)) :
    (pre : List (Mod D A)) →
      modCrossMid A [X] (Y :: m) pre ⟶ modMultiMid A pre X Y m
  | [] => (((ρ_ X.X).hom ▷ A) ▷ modList A (Y :: m)) ≫
      (α_ (X.X ⊗ A) Y.X (modList A m)).inv
  | P :: rest => P.X ◁ modCrossBridge A X Y m rest

/-- **The crossing window of a singleton block is the first
relation leg** of the head slot, through the bridge. -/
lemma modCrossBridge_legM
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D]
    (X Y : Mod D A) (m : List (Mod D A)) :
    ∀ pre : List (Mod D A),
      modCrossLegOf A [X] (Y :: m)
          (modCrossHeadWin A X [] (Y :: m)) pre =
        modCrossBridge A X Y m pre ≫ modMultiLegM A pre X Y m
  | [] => by
    change (((β_ (X.X ⊗ 𝟙_ D) A).hom ≫
          ((α_ A X.X (𝟙_ D)).inv ≫
            (actLeft A X.X ▷ 𝟙_ D))) ▷ (Y.X ⊗ modList A m)) ≫
        ((α_ X.X (𝟙_ D) (Y.X ⊗ modList A m)).hom ≫
          (X.X ◁ (λ_ (Y.X ⊗ modList A m)).hom)) =
      ((((ρ_ X.X).hom ▷ A) ▷ (Y.X ⊗ modList A m)) ≫
          (α_ (X.X ⊗ A) Y.X (modList A m)).inv) ≫
        ((((β_ X.X A).hom ≫ actLeft A X.X) ▷ Y.X) ▷ modList A m ≫
          (α_ X.X Y.X (modList A m)).hom)
    have hcoh : ((α_ A X.X (𝟙_ D)).inv ▷ (Y.X ⊗ modList A m)) ≫
        (α_ (A ⊗ X.X) (𝟙_ D) (Y.X ⊗ modList A m)).hom ≫
          ((A ⊗ X.X) ◁ (λ_ (Y.X ⊗ modList A m)).hom) =
      (A ◁ (ρ_ X.X).hom) ▷ (Y.X ⊗ modList A m) := by monoidal
    simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
    conv_lhs => rw [associator_naturality_left_assoc,
      ← whisker_exchange]
    conv_rhs => rw [associator_inv_naturality_left_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc,
      ← MonoidalCategory.comp_whiskerRight,
      BraidedCategory.braiding_naturality_left]
    conv_rhs => simp only [MonoidalCategory.comp_whiskerRight,
      Category.assoc]
    conv_rhs => rw [← associator_inv_naturality_left_assoc,
      associator_naturality_left,
      associator_naturality_left_assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% hcoh]
  | P :: rest => by
    change P.X ◁ modCrossLegOf A [X] (Y :: m)
          (modCrossHeadWin A X [] (Y :: m)) rest =
      (P.X ◁ modCrossBridge A X Y m rest) ≫
        (P.X ◁ modMultiLegM A rest X Y m)
    rw [← MonoidalCategory.whiskerLeft_comp,
      modCrossBridge_legM A X Y m rest]

/-- **The stationary window of a singleton block is the second
relation leg** of the head slot, through the bridge. -/
lemma modCrossBridge_legN
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X Y : Mod D A) (m : List (Mod D A)) :
    ∀ pre : List (Mod D A),
      modCrossLegOf A [X] (Y :: m)
          (modCrossYWin A [X] Y m) pre =
        modCrossBridge A X Y m pre ≫ modMultiLegN A pre X Y m
  | [] => by
    change (α_ (X.X ⊗ 𝟙_ D) A (Y.X ⊗ modList A m)).hom ≫
        ((X.X ⊗ 𝟙_ D) ◁
          ((α_ A Y.X (modList A m)).inv ≫
            (actLeft A Y.X ▷ modList A m))) ≫
        ((α_ X.X (𝟙_ D) (Y.X ⊗ modList A m)).hom ≫
          (X.X ◁ (λ_ (Y.X ⊗ modList A m)).hom)) =
      ((((ρ_ X.X).hom ▷ A) ▷ (Y.X ⊗ modList A m)) ≫
          (α_ (X.X ⊗ A) Y.X (modList A m)).inv) ≫
        (((α_ X.X A Y.X).hom ≫ (X.X ◁ actLeft A Y.X)) ▷
            modList A m ≫
          (α_ X.X Y.X (modList A m)).hom)
    have hcoh : (α_ (X.X ⊗ 𝟙_ D) A (Y.X ⊗ modList A m)).hom ≫
        (α_ X.X (𝟙_ D) (A ⊗ (Y.X ⊗ modList A m))).hom ≫
          (X.X ◁ (λ_ (A ⊗ (Y.X ⊗ modList A m))).hom) ≫
          (X.X ◁ (α_ A Y.X (modList A m)).inv) =
      (((ρ_ X.X).hom ▷ A) ▷ (Y.X ⊗ modList A m)) ≫
        (α_ (X.X ⊗ A) Y.X (modList A m)).inv ≫
          ((α_ X.X A Y.X).hom ▷ modList A m) ≫
          (α_ X.X (A ⊗ Y.X) (modList A m)).hom := by monoidal
    simp only [MonoidalCategory.whiskerLeft_comp,
      MonoidalCategory.comp_whiskerRight, Category.assoc]
    conv_lhs => rw [associator_naturality_right_assoc,
      associator_naturality_right_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp,
      leftUnitor_naturality]
    conv_rhs => rw [associator_naturality_middle]
    simp only [MonoidalCategory.whiskerLeft_comp]
    rw [reassoc_of% hcoh]
  | P :: rest => by
    change P.X ◁ modCrossLegOf A [X] (Y :: m)
          (modCrossYWin A [X] Y m) rest =
      (P.X ◁ modCrossBridge A X Y m rest) ≫
        (P.X ◁ modMultiLegN A rest X Y m)
    rw [← MonoidalCategory.whiskerLeft_comp,
      modCrossBridge_legN A X Y m rest]

end CrossBase

/-! ## The step of the crossing

For a first block of two or more modules, the crossing decomposes
by the hexagon: the monoid braids over the tail of the block first,
reaching the relation window of the head slot; the slot relation
walks it past the head, and what remains is the crossing of the
tail block under a prefix extended by the head. -/

section CrossStep

/-- Peel the head of the first block into the prefix. -/
def modCrossPeel [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X : Mod D A) (Xs' Ys : List (Mod D A)) :
    (pre : List (Mod D A)) →
      modCrossMid A (X :: Xs') Ys pre ⟶
        modCrossMid A Xs' Ys (pre ++ [X])
  | [] => ((α_ X.X (modList A Xs') A).hom ▷ modList A Ys) ≫
      (α_ X.X (modList A Xs' ⊗ A) (modList A Ys)).hom
  | P :: rest => P.X ◁ modCrossPeel A X Xs' Ys rest

/-- **Peeling passes the stationary window**: the stationary window
of the extended block is the peel followed by the whiskered
stationary window of the tail block. -/
lemma modCrossPeel_yWin [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X : Mod D A) (Xs' : List (Mod D A))
    (Y : Mod D A) (m : List (Mod D A)) :
    ∀ (pre : List (Mod D A))
      (h : (pre ++ [X]) ++ (Xs' ++ (Y :: m)) =
        pre ++ ((X :: Xs') ++ (Y :: m))),
      modCrossPeel A X Xs' (Y :: m) pre ≫
        modCrossLegOf A Xs' (Y :: m)
          (modCrossYWin A Xs' Y m) (pre ++ [X]) ≫
        modListCast A h =
      modCrossLegOf A (X :: Xs') (Y :: m)
        (modCrossYWin A (X :: Xs') Y m) pre
  | [], h => by
    simp only [List.nil_append, List.cons_append, modListCast_rfl,
      Category.comp_id]
    change (((α_ X.X (modList A Xs') A).hom ▷ modList A (Y :: m)) ≫
        (α_ X.X (modList A Xs' ⊗ A) (modList A (Y :: m))).hom) ≫
      (X.X ◁ ((α_ (modList A Xs') A (modList A (Y :: m))).hom ≫
        (modList A Xs' ◁ modListHeadAct A Y m) ≫
        (modListConcat A Xs' (Y :: m)).hom)) =
    (α_ (X.X ⊗ modList A Xs') A (modList A (Y :: m))).hom ≫
      ((X.X ⊗ modList A Xs') ◁ modListHeadAct A Y m) ≫
      ((α_ X.X (modList A Xs') (modList A (Y :: m))).hom ≫
        (X.X ◁ (modListConcat A Xs' (Y :: m)).hom))
    have hcoh : ((α_ X.X (modList A Xs') A).hom ▷
          modList A (Y :: m)) ≫
        (α_ X.X (modList A Xs' ⊗ A) (modList A (Y :: m))).hom ≫
        (X.X ◁ (α_ (modList A Xs') A (modList A (Y :: m))).hom) =
      (α_ (X.X ⊗ modList A Xs') A (modList A (Y :: m))).hom ≫
        (α_ X.X (modList A Xs')
          (A ⊗ modList A (Y :: m))).hom := by monoidal
    rw [Category.assoc]
    simp only [MonoidalCategory.whiskerLeft_comp]
    conv_rhs => rw [associator_naturality_right_assoc]
    rw [reassoc_of% hcoh]
  | P :: rest, h => by
    change (P.X ◁ modCrossPeel A X Xs' (Y :: m) rest) ≫
        (P.X ◁ modCrossLegOf A Xs' (Y :: m)
          (modCrossYWin A Xs' Y m) (rest ++ [X])) ≫
        modListCast A h =
      P.X ◁ modCrossLegOf A (X :: Xs') (Y :: m)
        (modCrossYWin A (X :: Xs') Y m) rest
    rw [← modCrossPeel_yWin A X Xs' Y m rest (by simp)]
    simp only [MonoidalCategory.whiskerLeft_comp]
    rw [modListCast_whiskerLeft]
    rfl

/-- The step bridge: braid the monoid over the tail of the first
block and retype at the relation window of the head slot. -/
def modCrossStepBridge [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D]
    (X P : Mod D A) (l' Ys : List (Mod D A)) :
    (pre : List (Mod D A)) →
      modCrossMid A (X :: P :: l') Ys pre ⟶
        modMultiMid A pre X P (l' ++ Ys)
  | [] =>
    (((α_ X.X (P.X ⊗ modList A l') A).hom ≫
        (X.X ◁ (β_ (P.X ⊗ modList A l') A).hom) ≫
        (α_ X.X A (P.X ⊗ modList A l')).inv) ▷ modList A Ys) ≫
      (α_ (X.X ⊗ A) (P.X ⊗ modList A l') (modList A Ys)).hom ≫
      ((X.X ⊗ A) ◁
        (α_ P.X (modList A l') (modList A Ys)).hom) ≫
      ((X.X ⊗ A) ◁ (P.X ◁ (modListConcat A l' Ys).hom)) ≫
      (α_ (X.X ⊗ A) P.X (modList A (l' ++ Ys))).inv
  | Q :: rest => Q.X ◁ modCrossStepBridge A X P l' Ys rest

/-- **The crossing window decomposes over the head slot**: by the
hexagon, the full crossing is the step bridge followed by the first
relation leg of the head slot. -/
lemma modCrossStepBridge_legM
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D]
    (X P : Mod D A)
    (l' Ys : List (Mod D A)) :
    ∀ pre : List (Mod D A),
      modCrossLegOf A (X :: P :: l') Ys
          (modCrossHeadWin A X (P :: l') Ys) pre =
        modCrossStepBridge A X P l' Ys pre ≫
          modMultiLegM A pre X P (l' ++ Ys)
  | [] => by
    change (((β_ (X.X ⊗ (P.X ⊗ modList A l')) A).hom ≫
          ((α_ A X.X (P.X ⊗ modList A l')).inv ≫
            (actLeft A X.X ▷ (P.X ⊗ modList A l')))) ▷
            modList A Ys) ≫
        ((α_ X.X (P.X ⊗ modList A l') (modList A Ys)).hom ≫
          (X.X ◁ ((α_ P.X (modList A l') (modList A Ys)).hom ≫
            (P.X ◁ (modListConcat A l' Ys).hom)))) =
      ((((α_ X.X (P.X ⊗ modList A l') A).hom ≫
          (X.X ◁ (β_ (P.X ⊗ modList A l') A).hom) ≫
          (α_ X.X A (P.X ⊗ modList A l')).inv) ▷ modList A Ys) ≫
        (α_ (X.X ⊗ A) (P.X ⊗ modList A l') (modList A Ys)).hom ≫
        ((X.X ⊗ A) ◁
          (α_ P.X (modList A l') (modList A Ys)).hom) ≫
        ((X.X ⊗ A) ◁ (P.X ◁ (modListConcat A l' Ys).hom)) ≫
        (α_ (X.X ⊗ A) P.X (modList A (l' ++ Ys))).inv) ≫
        ((((β_ X.X A).hom ≫ actLeft A X.X) ▷ P.X) ▷
            modList A (l' ++ Ys) ≫
          (α_ X.X P.X (modList A (l' ++ Ys))).hom)
    rw [BraidedCategory.braiding_tensor_left_hom]
    simp only [MonoidalCategory.comp_whiskerRight, Category.assoc,
      MonoidalCategory.hom_inv_whiskerRight_assoc,
      MonoidalCategory.whiskerLeft_comp]
    conv_lhs => rw [associator_naturality_left_assoc,
      associator_naturality_left_assoc]
    conv_rhs => rw [associator_naturality_left,
      associator_naturality_left_assoc, Iso.inv_hom_id_assoc,
      whisker_exchange_assoc, whisker_exchange_assoc,
      whisker_exchange, whisker_exchange_assoc]
  | Q :: rest => by
    change Q.X ◁ modCrossLegOf A (X :: P :: l') Ys
          (modCrossHeadWin A X (P :: l') Ys) rest =
      (Q.X ◁ modCrossStepBridge A X P l' Ys rest) ≫
        (Q.X ◁ modMultiLegM A rest X P (l' ++ Ys))
    rw [← MonoidalCategory.whiskerLeft_comp,
      modCrossStepBridge_legM A X P l' Ys rest]

/-- **The step bridge against the second relation leg**: past the
head slot, what remains is the crossing of the tail block, under
the prefix extended by the head. -/
lemma modCrossStepBridge_legN
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D]
    (X P : Mod D A)
    (l' Ys : List (Mod D A)) :
    ∀ (pre : List (Mod D A))
      (h : (pre ++ [X]) ++ ((P :: l') ++ Ys) =
        pre ++ ((X :: P :: l') ++ Ys)),
      modCrossStepBridge A X P l' Ys pre ≫
          modMultiLegN A pre X P (l' ++ Ys) =
        modCrossPeel A X (P :: l') Ys pre ≫
          modCrossLegOf A (P :: l') Ys
            (modCrossHeadWin A P l' Ys) (pre ++ [X]) ≫
          modListCast A h
  | [], h => by
    simp only [List.nil_append, List.cons_append, modListCast_rfl,
      Category.comp_id]
    change ((((α_ X.X (P.X ⊗ modList A l') A).hom ≫
          (X.X ◁ (β_ (P.X ⊗ modList A l') A).hom) ≫
          (α_ X.X A (P.X ⊗ modList A l')).inv) ▷ modList A Ys) ≫
        (α_ (X.X ⊗ A) (P.X ⊗ modList A l') (modList A Ys)).hom ≫
        ((X.X ⊗ A) ◁
          (α_ P.X (modList A l') (modList A Ys)).hom) ≫
        ((X.X ⊗ A) ◁ (P.X ◁ (modListConcat A l' Ys).hom)) ≫
        (α_ (X.X ⊗ A) P.X (modList A (l' ++ Ys))).inv) ≫
        (((α_ X.X A P.X).hom ≫ (X.X ◁ actLeft A P.X)) ▷
            modList A (l' ++ Ys) ≫
          (α_ X.X P.X (modList A (l' ++ Ys))).hom) =
      (((α_ X.X (P.X ⊗ modList A l') A).hom ▷ modList A Ys) ≫
          (α_ X.X ((P.X ⊗ modList A l') ⊗ A)
            (modList A Ys)).hom) ≫
        (X.X ◁ ((((β_ (P.X ⊗ modList A l') A).hom ≫
            ((α_ A P.X (modList A l')).inv ≫
              (actLeft A P.X ▷ modList A l'))) ▷ modList A Ys) ≫
          ((α_ P.X (modList A l') (modList A Ys)).hom ≫
            (P.X ◁ (modListConcat A l' Ys).hom))))
    have hW : (((β_ (P.X ⊗ modList A l') A).hom ≫
          ((α_ A P.X (modList A l')).inv ≫
            (actLeft A P.X ▷ modList A l'))) ▷ modList A Ys) ≫
        ((α_ P.X (modList A l') (modList A Ys)).hom ≫
          (P.X ◁ (modListConcat A l' Ys).hom)) =
      ((β_ (P.X ⊗ modList A l') A).hom ▷ modList A Ys) ≫
        ((α_ A P.X (modList A l')).inv ▷ modList A Ys) ≫
        (α_ (A ⊗ P.X) (modList A l') (modList A Ys)).hom ≫
        ((A ⊗ P.X) ◁ (modListConcat A l' Ys).hom) ≫
        (actLeft A P.X ▷ modList A (l' ++ Ys)) := by
      simp only [MonoidalCategory.comp_whiskerRight,
        Category.assoc]
      rw [associator_naturality_left_assoc, ← whisker_exchange]
    have hcoh : ((α_ X.X A (P.X ⊗ modList A l')).inv ▷
          modList A Ys) ≫
        (α_ (X.X ⊗ A) (P.X ⊗ modList A l') (modList A Ys)).hom ≫
        ((X.X ⊗ A) ◁
          (α_ P.X (modList A l') (modList A Ys)).hom) ≫
        (α_ (X.X ⊗ A) P.X
          (modList A l' ⊗ modList A Ys)).inv ≫
        ((α_ X.X A P.X).hom ▷
          (modList A l' ⊗ modList A Ys)) ≫
        (α_ X.X (A ⊗ P.X)
          (modList A l' ⊗ modList A Ys)).hom =
      (α_ X.X (A ⊗ (P.X ⊗ modList A l')) (modList A Ys)).hom ≫
        (X.X ◁ ((α_ A P.X (modList A l')).inv ▷ modList A Ys)) ≫
        (X.X ◁ (α_ (A ⊗ P.X) (modList A l')
          (modList A Ys)).hom) := by
      monoidal
    rw [hW]
    simp only [MonoidalCategory.whiskerLeft_comp,
      MonoidalCategory.comp_whiskerRight, Category.assoc]
    conv_lhs => rw [associator_naturality_middle,
      associator_inv_naturality_right_assoc,
      whisker_exchange_assoc, associator_naturality_right_assoc]
    conv_rhs => rw [← associator_naturality_middle_assoc]
    rw [reassoc_of% hcoh]
  | Q :: rest, h => by
    have h' : (rest ++ [X]) ++ ((P :: l') ++ Ys) =
        rest ++ ((X :: P :: l') ++ Ys) := by simp
    have hQC : Q.X ◁ modListCast A h' = modListCast A h :=
      modListCast_whiskerLeft A Q h'
    change (Q.X ◁ modCrossStepBridge A X P l' Ys rest) ≫
        (Q.X ◁ modMultiLegN A rest X P (l' ++ Ys)) =
      (Q.X ◁ modCrossPeel A X (P :: l') Ys rest) ≫
        (Q.X ◁ modCrossLegOf A (P :: l') Ys
          (modCrossHeadWin A P l' Ys) (rest ++ [X])) ≫
        modListCast A h
    have e1 := (MonoidalCategory.whiskerLeft_comp Q.X
      (modCrossStepBridge A X P l' Ys rest)
      (modMultiLegN A rest X P (l' ++ Ys))).symm
    have e2 := congrArg (fun t => Q.X ◁ t)
      (modCrossStepBridge_legN A X P l' Ys rest h')
    have e3 := MonoidalCategory.whiskerLeft_comp Q.X
      (modCrossPeel A X (P :: l') Ys rest)
      (modCrossLegOf A (P :: l') Ys
          (modCrossHeadWin A P l' Ys) (rest ++ [X]) ≫
        modListCast A h')
    have e4 := congrArg
      (fun t => (Q.X ◁ modCrossPeel A X (P :: l') Ys rest) ≫ t)
      (MonoidalCategory.whiskerLeft_comp Q.X
        (modCrossLegOf A (P :: l') Ys
          (modCrossHeadWin A P l' Ys) (rest ++ [X]))
        (modListCast A h'))
    have e5 := congrArg (fun t =>
        (Q.X ◁ modCrossPeel A X (P :: l') Ys rest) ≫
          (Q.X ◁ modCrossLegOf A (P :: l') Ys
            (modCrossHeadWin A P l' Ys) (rest ++ [X])) ≫ t)
      hQC
    exact (((e1.trans e2).trans e3).trans e4).trans e5

end CrossStep

/-! ## The crossing relation -/

section CrossRel

/-- **The fold-level crossing relation**: after the projection of
the multi-tensor, braiding the monoid over the whole first block
and acting on its head agrees with acting on the head of the second
block, at every ambient prefix.  The crossing is consumed one
factor at a time, one slot relation per factor. -/
theorem modCross_rel [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (Y : Mod D A) (m : List (Mod D A)) :
    ∀ (l : List (Mod D A)) (X : Mod D A)
      (pr Zs : List (Mod D A))
      (h : Zs = pr ++ ((X :: l) ++ (Y :: m))),
      modCrossLegOf A (X :: l) (Y :: m)
          (modCrossHeadWin A X l (Y :: m)) pr ≫
        modListCast A h.symm ≫ modMultiπ A Zs =
      modCrossLegOf A (X :: l) (Y :: m)
          (modCrossYWin A (X :: l) Y m) pr ≫
        modListCast A h.symm ≫ modMultiπ A Zs
  | [], X, pr, Zs, h => by
    have g1 := congrArg
      (fun t => t ≫ (modListCast A h.symm ≫ modMultiπ A Zs))
      (modCrossBridge_legM A X Y m pr)
    have g2 := Category.assoc (modCrossBridge A X Y m pr)
      (modMultiLegM A pr X Y m)
      (modListCast A h.symm ≫ modMultiπ A Zs)
    have g3 := congrArg (fun t => modCrossBridge A X Y m pr ≫ t)
      (modMulti_rel A pr X Y m h)
    have g4 := (Category.assoc (modCrossBridge A X Y m pr)
      (modMultiLegN A pr X Y m)
      (modListCast A h.symm ≫ modMultiπ A Zs)).symm
    have g5 := (congrArg
      (fun t => t ≫ (modListCast A h.symm ≫ modMultiπ A Zs))
      (modCrossBridge_legN A X Y m pr)).symm
    exact g1.trans (g2.trans (g3.trans (g4.trans g5)))
  | P :: l', X, pr, Zs, h => by
    have h2 : (pr ++ [X]) ++ ((P :: l') ++ (Y :: m)) =
        pr ++ ((X :: P :: l') ++ (Y :: m)) := by simp
    have h'' : Zs = (pr ++ [X]) ++ ((P :: l') ++ (Y :: m)) :=
      h.trans h2.symm
    have b1 := congrArg
      (fun t => t ≫ (modListCast A h.symm ≫ modMultiπ A Zs))
      (modCrossStepBridge_legM A X P l' (Y :: m) pr)
    have b2 := Category.assoc
      (modCrossStepBridge A X P l' (Y :: m) pr)
      (modMultiLegM A pr X P (l' ++ (Y :: m)))
      (modListCast A h.symm ≫ modMultiπ A Zs)
    have b3 := congrArg
      (fun t => modCrossStepBridge A X P l' (Y :: m) pr ≫ t)
      (modMulti_rel A pr X P (l' ++ (Y :: m)) h)
    have b4 := (Category.assoc
      (modCrossStepBridge A X P l' (Y :: m) pr)
      (modMultiLegN A pr X P (l' ++ (Y :: m)))
      (modListCast A h.symm ≫ modMultiπ A Zs)).symm
    have b5 := congrArg
      (fun t => t ≫ (modListCast A h.symm ≫ modMultiπ A Zs))
      (modCrossStepBridge_legN A X P l' (Y :: m) pr h2)
    have b6 := Category.assoc
      (modCrossPeel A X (P :: l') (Y :: m) pr)
      (modCrossLegOf A (P :: l') (Y :: m)
          (modCrossHeadWin A P l' (Y :: m)) (pr ++ [X]) ≫
        modListCast A h2)
      (modListCast A h.symm ≫ modMultiπ A Zs)
    have b7 := congrArg
      (fun t => modCrossPeel A X (P :: l') (Y :: m) pr ≫ t)
      (Category.assoc
        (modCrossLegOf A (P :: l') (Y :: m)
          (modCrossHeadWin A P l' (Y :: m)) (pr ++ [X]))
        (modListCast A h2)
        (modListCast A h.symm ≫ modMultiπ A Zs))
    have b8 := congrArg
      (fun t => modCrossPeel A X (P :: l') (Y :: m) pr ≫
        (modCrossLegOf A (P :: l') (Y :: m)
          (modCrossHeadWin A P l' (Y :: m)) (pr ++ [X]) ≫ t))
      (modListCast_comp_assoc A h2 h.symm (modMultiπ A Zs))
    have b9 := congrArg
      (fun t => modCrossPeel A X (P :: l') (Y :: m) pr ≫ t)
      (modCross_rel A Y m l' P (pr ++ [X]) Zs h'')
    have c1 := congrArg
      (fun t => modCrossPeel A X (P :: l') (Y :: m) pr ≫
        (modCrossLegOf A (P :: l') (Y :: m)
          (modCrossYWin A (P :: l') Y m) (pr ++ [X]) ≫ t))
      (modListCast_comp_assoc A h2 h.symm (modMultiπ A Zs)).symm
    have c2 := (congrArg
      (fun t => modCrossPeel A X (P :: l') (Y :: m) pr ≫ t)
      (Category.assoc
        (modCrossLegOf A (P :: l') (Y :: m)
          (modCrossYWin A (P :: l') Y m) (pr ++ [X]))
        (modListCast A h2)
        (modListCast A h.symm ≫ modMultiπ A Zs))).symm
    have c3 := (Category.assoc
      (modCrossPeel A X (P :: l') (Y :: m) pr)
      (modCrossLegOf A (P :: l') (Y :: m)
          (modCrossYWin A (P :: l') Y m) (pr ++ [X]) ≫
        modListCast A h2)
      (modListCast A h.symm ≫ modMultiπ A Zs)).symm
    have c4 := congrArg
      (fun t => t ≫ (modListCast A h.symm ≫ modMultiπ A Zs))
      (modCrossPeel_yWin A X (P :: l') Y m pr h2)
    exact b1.trans (b2.trans (b3.trans (b4.trans (b5.trans
      (b6.trans (b7.trans (b8.trans (b9.trans (c1.trans
        (c2.trans (c3.trans c4)))))))))))

/-- **The crossing relation, prefix-free**: braiding the monoid
over the first block and acting on its head agrees, after the
projection, with acting on the head of the second block.  This is
the typed form consumed by the `modTensor` descent below. -/
theorem modListCross [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (X Y : Mod D A) (l m : List (Mod D A)) :
    (((β_ (modList A (X :: l)) A).hom ≫ modListHeadAct A X l) ▷
        modList A (Y :: m)) ≫
      (modListConcat A (X :: l) (Y :: m)).hom ≫
      modMultiπ A ((X :: l) ++ (Y :: m)) =
    (α_ (modList A (X :: l)) A (modList A (Y :: m))).hom ≫
      (modList A (X :: l) ◁ modListHeadAct A Y m) ≫
      (modListConcat A (X :: l) (Y :: m)).hom ≫
      modMultiπ A ((X :: l) ++ (Y :: m)) := by
  have h := modCross_rel A Y m l X [] ((X :: l) ++ (Y :: m)) rfl
  simp only [modCrossLegOf_nil, List.nil_append, modListCast_rfl,
    Category.id_comp] at h
  have e0 := Category.assoc
    (((β_ (modList A (X :: l)) A).hom ≫ modListHeadAct A X l) ▷
      modList A (Y :: m))
    (modListConcat A (X :: l) (Y :: m)).hom
    (modMultiπ A ((X :: l) ++ (Y :: m)))
  have e1 := Category.assoc
    (α_ (modList A (X :: l)) A (modList A (Y :: m))).hom
    ((modList A (X :: l) ◁ modListHeadAct A Y m) ≫
      (modListConcat A (X :: l) (Y :: m)).hom)
    (modMultiπ A ((X :: l) ++ (Y :: m)))
  have e2 := congrArg
    (fun t =>
      (α_ (modList A (X :: l)) A (modList A (Y :: m))).hom ≫ t)
    (Category.assoc
      (modList A (X :: l) ◁ modListHeadAct A Y m)
      (modListConcat A (X :: l) (Y :: m)).hom
      (modMultiπ A ((X :: l) ++ (Y :: m))))
  exact e0.symm.trans (h.trans (e1.trans e2))

end CrossRel

/-! ## Descent of the concatenation through the module tensor

For a commutative monoid the two bundled multi-tensor modules have
a binary `modTensor`; the concatenation map coequalizes its two
legs — by the crossing relation — and so descends. -/

section TensorMulti

/-- The concatenation coequalizes the binary module-tensor legs of
two bundled multi-tensors: the crossing relation, lifted through
the projections. -/
lemma modTensorLeg_multi
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorRight Y)]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorLeft Y)]
    (X Y : Mod D A) (l m : List (Mod D A)) :
    modTensorLegM A (modMultiMod A X l) (modMultiMod A Y m) ≫
        modMultiConcat A (X :: l) (Y :: m) =
      modTensorLegN A (modMultiMod A X l) (modMultiMod A Y m) ≫
        modMultiConcat A (X :: l) (Y :: m) := by
  have hM : (modMultiπ A (X :: l) ▷ (A ⊗ modList A (Y :: m))) ≫
      (α_ (modMulti A (X :: l)) A (modList A (Y :: m))).inv ≫
      ((modMulti A (X :: l) ⊗ A) ◁ modMultiπ A (Y :: m)) ≫
      modTensorLegM A (modMultiMod A X l) (modMultiMod A Y m) ≫
      modMultiConcat A (X :: l) (Y :: m) =
    (α_ (modList A (X :: l)) A (modList A (Y :: m))).inv ≫
      ((β_ (modList A (X :: l)) A).hom ▷ modList A (Y :: m)) ≫
      (modListHeadAct A X l ▷ modList A (Y :: m)) ≫
      (modListConcat A (X :: l) (Y :: m)).hom ≫
      modMultiπ A ((X :: l) ++ (Y :: m)) := by
    change (modMultiπ A (X :: l) ▷ (A ⊗ modList A (Y :: m))) ≫
        (α_ (modMulti A (X :: l)) A (modList A (Y :: m))).inv ≫
        ((modMulti A (X :: l) ⊗ A) ◁ modMultiπ A (Y :: m)) ≫
        (((β_ (modMulti A (X :: l)) A).hom ≫
          modMultiHeadAct A X l) ▷ modMulti A (Y :: m)) ≫
        modMultiConcat A (X :: l) (Y :: m) = _
    rw [associator_inv_naturality_left_assoc,
      ← whisker_exchange_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc,
      BraidedCategory.braiding_naturality_left_assoc,
      whiskerLeft_modMultiπ_headAct, whisker_exchange_assoc,
      whiskerLeft_modMultiπ_concat,
      MonoidalCategory.comp_whiskerRight_assoc,
      MonoidalCategory.comp_whiskerRight_assoc,
      whiskerRight_modMultiπ_concatFst]
  have hN : (modMultiπ A (X :: l) ▷ (A ⊗ modList A (Y :: m))) ≫
      (α_ (modMulti A (X :: l)) A (modList A (Y :: m))).inv ≫
      ((modMulti A (X :: l) ⊗ A) ◁ modMultiπ A (Y :: m)) ≫
      modTensorLegN A (modMultiMod A X l) (modMultiMod A Y m) ≫
      modMultiConcat A (X :: l) (Y :: m) =
    (modList A (X :: l) ◁ modListHeadAct A Y m) ≫
      (modListConcat A (X :: l) (Y :: m)).hom ≫
      modMultiπ A ((X :: l) ++ (Y :: m)) := by
    change (modMultiπ A (X :: l) ▷ (A ⊗ modList A (Y :: m))) ≫
        (α_ (modMulti A (X :: l)) A (modList A (Y :: m))).inv ≫
        ((modMulti A (X :: l) ⊗ A) ◁ modMultiπ A (Y :: m)) ≫
        ((α_ (modMulti A (X :: l)) A (modMulti A (Y :: m))).hom ≫
          (modMulti A (X :: l) ◁ modMultiHeadAct A Y m)) ≫
        modMultiConcat A (X :: l) (Y :: m) = _
    simp only [Category.assoc]
    rw [associator_naturality_right_assoc, Iso.inv_hom_id_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      whiskerLeft_modMultiπ_headAct,
      MonoidalCategory.whiskerLeft_comp_assoc,
      whiskerLeft_modMultiπ_concat, ← whisker_exchange_assoc,
      whiskerRight_modMultiπ_concatFst]
  apply modMulti_whiskerL_hom_ext A (Y :: m)
    (modMulti A (X :: l) ⊗ A)
  apply (cancel_epi
    (α_ (modMulti A (X :: l)) A (modList A (Y :: m))).inv).mp
  apply modMulti_whiskerR_hom_ext A (X :: l)
    (A ⊗ modList A (Y :: m))
  have mc := modListCross A X Y l m
  rw [MonoidalCategory.comp_whiskerRight] at mc
  simp only [Category.assoc] at mc
  change (modMultiπ A (X :: l) ▷ (A ⊗ modList A (Y :: m))) ≫
      (α_ (modMulti A (X :: l)) A (modList A (Y :: m))).inv ≫
      ((modMulti A (X :: l) ⊗ A) ◁ modMultiπ A (Y :: m)) ≫
      modTensorLegM A (modMultiMod A X l) (modMultiMod A Y m) ≫
      modMultiConcat A (X :: l) (Y :: m) =
    (modMultiπ A (X :: l) ▷ (A ⊗ modList A (Y :: m))) ≫
      (α_ (modMulti A (X :: l)) A (modList A (Y :: m))).inv ≫
      ((modMulti A (X :: l) ⊗ A) ◁ modMultiπ A (Y :: m)) ≫
      modTensorLegN A (modMultiMod A X l) (modMultiMod A Y m) ≫
      modMultiConcat A (X :: l) (Y :: m)
  rw [hM, hN, mc, Iso.inv_hom_id_assoc]

/-- **The concatenation descends to the binary module tensor
product of two multi-tensors.** -/
noncomputable def modTensorMulti
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorRight Y)]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorLeft Y)]
    (X Y : Mod D A)
    (l m : List (Mod D A)) :
    modTensor A (modMultiMod A X l) (modMultiMod A Y m) ⟶
      modMulti A ((X :: l) ++ (Y :: m)) :=
  modTensorDesc A (modMultiMod A X l) (modMultiMod A Y m)
    (modMultiConcat A (X :: l) (Y :: m))
    (modTensorLeg_multi A X Y l m)

/-- Defining equation of the descended concatenation against the
module-tensor projection. -/
@[reassoc (attr := simp)]
lemma modTensorπ_multi [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorRight Y)]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorLeft Y)]
    (X Y : Mod D A) (l m : List (Mod D A)) :
    modTensorπ A (modMultiMod A X l) (modMultiMod A Y m) ≫
        modTensorMulti A X Y l m =
      modMultiConcat A (X :: l) (Y :: m) :=
  modTensorπ_desc A _ _ _ _

/-- Defining equation of the descended concatenation against the
multi-tensor projections: on the folds it is the fold
concatenation. -/
@[reassoc]
lemma tensorHom_modTensorπ_multi
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorRight Y)]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorLeft Y)]
    (X Y : Mod D A)
    (l m : List (Mod D A)) :
    (modMultiπ A (X :: l) ⊗ₘ modMultiπ A (Y :: m)) ≫
        modTensorπ A (modMultiMod A X l) (modMultiMod A Y m) ≫
        modTensorMulti A X Y l m =
      (modListConcat A (X :: l) (Y :: m)).hom ≫
        modMultiπ A ((X :: l) ++ (Y :: m)) := by
  have e := congrArg (fun t =>
    (modMultiπ A (X :: l) ⊗ₘ modMultiπ A (Y :: m)) ≫ t)
    (modTensorπ_multi A X Y l m)
  exact e.trans (tensorHom_modMultiπ_concat A (X :: l) (Y :: m))

end TensorMulti

/-! ## The braiding at a relation window

In a symmetric category the braiding of the two module factors of
a relation window carries the monoid along; the window legs
intertwine it with the plain braiding of the factors, exchanging
the two legs.  This mirrors the treatment of the symmetric-power
slot exchange, at two distinct modules. -/

section WinSwapMod

/-- Exchange of the two module factors of a relation window,
carrying the monoid along: `(x ⊗ c) ⊗ y ↦ (y ⊗ c) ⊗ x`. -/
def modWinSwap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A]
    (M N : Mod D A) :
    (M.X ⊗ A) ⊗ N.X ⟶ (N.X ⊗ A) ⊗ M.X :=
  (β_ (M.X ⊗ A) N.X).hom ≫ (N.X ◁ (β_ M.X A).hom) ≫
    (α_ N.X A M.X).inv

/-- The window exchange is an involution. -/
@[reassoc (attr := simp)]
lemma modWinSwap_modWinSwap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A]
    (M N : Mod D A) :
    modWinSwap A M N ≫ modWinSwap A N M = 𝟙 _ := by
  simp only [modWinSwap, BraidedCategory.braiding_tensor_left_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc N.X (β_ M.X A).hom
      (β_ A M.X).hom, SymmetricCategory.symmetry,
    MonoidalCategory.whiskerLeft_id, Category.id_comp,
    Iso.hom_inv_id_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    SymmetricCategory.symmetry, MonoidalCategory.id_whiskerRight,
    Category.id_comp, Iso.inv_hom_id_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    SymmetricCategory.symmetry, MonoidalCategory.whiskerLeft_id,
    Category.id_comp, Iso.hom_inv_id]

/-- **The first leg intertwines the window exchange with the
braiding**: acting on the first factor and braiding is exchanging
and acting on the second factor. -/
@[reassoc]
lemma modWinSwap_legM
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A]
    (M N : Mod D A) :
    modTensorLegM A M N ≫ (β_ M.X N.X).hom =
      modWinSwap A M N ≫ modTensorLegN A N M := by
  rw [modTensorLegM, BraidedCategory.braiding_naturality_left,
    actRight, MonoidalCategory.whiskerLeft_comp, modWinSwap,
    modTensorLegN]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- **The second leg intertwines the window exchange with the
braiding**, by the involutivity of both. -/
@[reassoc]
lemma modWinSwap_legN
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A]
    (M N : Mod D A) :
    modTensorLegN A M N ≫ (β_ M.X N.X).hom =
      modWinSwap A M N ≫ modTensorLegM A N M := by
  have h1 : modTensorLegN A M N =
      modWinSwap A M N ≫ modTensorLegM A N M ≫
        (β_ N.X M.X).hom := by
    rw [modWinSwap_legM A N M, ← Category.assoc,
      modWinSwap_modWinSwap, Category.id_comp]
  rw [h1, Category.assoc, Category.assoc,
    SymmetricCategory.symmetry, Category.comp_id]

end WinSwapMod

/-! ## The two-element swap -/

section SwapPair

/-- **The braiding of a two-element multi-tensor**: the exchange of
the two factors descends, the single slot relation consumed through
the window exchange. -/
noncomputable def modMultiSwapPair
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    (M N : Mod D A) :
    modMulti A [M, N] ⟶ modMulti A [N, M] :=
  modMultiDesc A (pairResolve A M N ≫ (β_ M.X N.X).hom ≫
      pairResolveInv A N M ≫ modMultiπ A [N, M])
    (by
      intro pre M' N' post hd
      obtain ⟨rfl, h2, h3, rfl⟩ := pair_decomp A hd
      subst h2
      subst h3
      rw [modMultiLegM, modMultiLegN,
        modMultiLeg_pair_resolve_assoc A M N _ hd.symm,
        modMultiLeg_pair_resolve_assoc A M N _ hd.symm,
        modWinSwap_legM_assoc, modWinSwap_legN_assoc,
        modMultiLeg_pair_resolveInv_assoc A N M _
          (Eq.symm (rfl : [N, M] = [] ++ N :: M :: [])),
        modMultiLeg_pair_resolveInv_assoc A N M _
          (Eq.symm (rfl : [N, M] = [] ++ N :: M :: []))]
      have hrel := modMulti_rel A [] N M []
        (rfl : [N, M] = [] ++ N :: M :: [])
      rw [modMultiLegM, modMultiLegN] at hrel
      exact congrArg
        (fun t => pairSeed A M N ≫ modWinSwap A M N ≫
          pairSeedInv A N M ≫ t) hrel.symm)

/-- Defining equation of the two-element swap: on the fold it is
the braiding of the factors, conjugated by the unit seeds. -/
@[reassoc (attr := simp)]
lemma modMultiπ_swapPair
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    (M N : Mod D A) :
    modMultiπ A [M, N] ≫ modMultiSwapPair A M N =
      pairResolve A M N ≫ (β_ M.X N.X).hom ≫
        pairResolveInv A N M ≫ modMultiπ A [N, M] :=
  modMultiπ_desc A _ _

end SwapPair

end RS
