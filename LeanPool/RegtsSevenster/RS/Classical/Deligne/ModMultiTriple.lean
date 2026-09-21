/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModMulti
import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModAssoc

/-!
# The three-letter multi-tensor against the nested binary tensor

The comparison of the wide presentation of the multi-tensor of a
three-element list with the left-nested binary module tensor
product of `ModTensor.lean`.

* `triple_decomp`: a three-element list has exactly two adjacent
  slots.
* `tripleResolve`/`tripleResolveInv`: the resolution of the
  three-element fold onto the plain triple tensor, absorbing the
  unit seed of the fold.
* `tripleLegFst_resolve`, `tripleLegSnd_resolve`, and the inverse
  forms: the slot legs of the wide relation pair against the
  resolutions, with the window morphism quantified.
* `modMultiTripleHom`: the forward descent through the wide
  coequalizer, landing on the cover of the inverse associator of
  `ModAssoc.lean`; its slot conditions are the whiskered binary
  balance and the cover condition of the inverse associator.
* `tripleInvCover`, `tripleInvMid`, `modMultiTripleInv`: the
  backward double descent through the outer and inner binary
  coequalizers, mapping onto the wide projection.
* `modMultiTriple`: the packaged isomorphism
  `modMulti A [X, Y, Z] ≅ modTensor A (modTensorMod A X Y) Z`,
  with defining equations against the projections in both
  directions.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## The resolution of the three-element fold -/

section TripleResolve

/-- The two decompositions of a three-element list: the slot at the
head and the slot at the tail. -/
lemma triple_decomp [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    {X Y Z M N : Mod D A} {pre post : List (Mod D A)}
    (h : [X, Y, Z] = pre ++ M :: N :: post) :
    (pre = [] ∧ X = M ∧ Y = N ∧ post = [Z]) ∨
      (pre = [X] ∧ Y = M ∧ Z = N ∧ post = []) := by
  rcases pre with _ | ⟨P, pre⟩
  · injection h with h1 h
    injection h with h2 h3
    exact Or.inl ⟨rfl, h1, h2, h3.symm⟩
  · injection h with h1 h
    obtain ⟨rfl, h2, h3, rfl⟩ := pair_decomp A h
    exact Or.inr ⟨by rw [h1], h2, h3, rfl⟩

/-- The resolution of the three-element fold onto the plain triple
tensor: absorb the unit seed.  A bridge morphism with a
`modList`-typed source, so that statements through it stay
type-correct at low transparency. -/
def tripleResolve
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : Mod D A)
    (Y : Mod D A) (Z : Mod D A) : modList A [X, Y, Z] ⟶ X.X ⊗ (Y.X ⊗ Z.X) :=
  X.X ◁ (Y.X ◁ (ρ_ Z.X).hom)

/-- The inverse resolution: reinstate the unit seed. -/
def tripleResolveInv
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : Mod D A)
    (Y : Mod D A) (Z : Mod D A) : X.X ⊗ (Y.X ⊗ Z.X) ⟶ modList A [X, Y, Z] :=
  X.X ◁ (Y.X ◁ (ρ_ Z.X).inv)

@[reassoc (attr := simp)]
lemma tripleResolve_inv
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : Mod D A)
    (Y : Mod D A) (Z : Mod D A) :
    tripleResolve A X Y Z ≫ tripleResolveInv A X Y Z = 𝟙 _ := by
  show (X.X ◁ (Y.X ◁ (ρ_ Z.X).hom)) ≫
      (X.X ◁ (Y.X ◁ (ρ_ Z.X).inv)) =
    𝟙 (X.X ⊗ (Y.X ⊗ (Z.X ⊗ 𝟙_ D)))
  rw [← MonoidalCategory.whiskerLeft_comp,
    ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id]
  simp only [MonoidalCategory.whiskerLeft_id]

@[reassoc (attr := simp)]
lemma tripleResolveInv_resolve
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : Mod D A)
    (Y : Mod D A) (Z : Mod D A) :
    tripleResolveInv A X Y Z ≫ tripleResolve A X Y Z = 𝟙 _ := by
  show (X.X ◁ (Y.X ◁ (ρ_ Z.X).inv)) ≫
      (X.X ◁ (Y.X ◁ (ρ_ Z.X).hom)) =
    𝟙 (X.X ⊗ (Y.X ⊗ Z.X))
  rw [← MonoidalCategory.whiskerLeft_comp,
    ← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id]
  simp only [MonoidalCategory.whiskerLeft_id]

/-- The window seed of the head slot: absorb the unit seed of the
suffix fold, retyped at `modMultiMid`. -/
def tripleSeedFst
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : Mod D A)
    (Y : Mod D A) (Z : Mod D A) :
    modMultiMid A [] X Y [Z] ⟶ ((X.X ⊗ A) ⊗ Y.X) ⊗ Z.X :=
  ((X.X ⊗ A) ⊗ Y.X) ◁ (ρ_ Z.X).hom

/-- The inverse window seed of the head slot. -/
def tripleSeedFstInv
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : Mod D A)
    (Y : Mod D A) (Z : Mod D A) :
    ((X.X ⊗ A) ⊗ Y.X) ⊗ Z.X ⟶ modMultiMid A [] X Y [Z] :=
  ((X.X ⊗ A) ⊗ Y.X) ◁ (ρ_ Z.X).inv

/-- The head-slot leg against the resolution: the unit seed is
absorbed, the window morphism and the reassociation remain. -/
@[reassoc]
lemma tripleLegFst_resolve
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : Mod D A)
    (Y : Mod D A) (Z : Mod D A)
    (w : (X.X ⊗ A) ⊗ Y.X ⟶ X.X ⊗ Y.X)
    (h : ([] ++ X :: Y :: [Z] : List (Mod D A)) = [X, Y, Z]) :
    modMultiLegOf A X Y [Z] w [] ≫ modListCast A h ≫
        tripleResolve A X Y Z =
      tripleSeedFst A X Y Z ≫ (w ▷ Z.X) ≫
        (α_ X.X Y.X Z.X).hom := by
  show ((w ▷ (Z.X ⊗ 𝟙_ D)) ≫
        (α_ X.X Y.X (Z.X ⊗ 𝟙_ D)).hom) ≫
      𝟙 (X.X ⊗ (Y.X ⊗ (Z.X ⊗ 𝟙_ D))) ≫
        (X.X ◁ (Y.X ◁ (ρ_ Z.X).hom)) =
    (((X.X ⊗ A) ⊗ Y.X) ◁ (ρ_ Z.X).hom) ≫ (w ▷ Z.X) ≫
      (α_ X.X Y.X Z.X).hom
  rw [Category.id_comp, Category.assoc,
    ← associator_naturality_right, ← whisker_exchange_assoc]

/-- A window morphism against the inverse resolution, in head-slot
leg form. -/
@[reassoc]
lemma tripleLegFst_resolveInv
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : Mod D A)
    (Y : Mod D A) (Z : Mod D A)
    (w : (X.X ⊗ A) ⊗ Y.X ⟶ X.X ⊗ Y.X)
    (h : ([] ++ X :: Y :: [Z] : List (Mod D A)) = [X, Y, Z]) :
    (w ▷ Z.X) ≫ (α_ X.X Y.X Z.X).hom ≫
        tripleResolveInv A X Y Z =
      tripleSeedFstInv A X Y Z ≫ modMultiLegOf A X Y [Z] w [] ≫
        modListCast A h := by
  show (w ▷ Z.X) ≫ (α_ X.X Y.X Z.X).hom ≫
      (X.X ◁ (Y.X ◁ (ρ_ Z.X).inv)) =
    (((X.X ⊗ A) ⊗ Y.X) ◁ (ρ_ Z.X).inv) ≫
      ((w ▷ (Z.X ⊗ 𝟙_ D)) ≫
        (α_ X.X Y.X (Z.X ⊗ 𝟙_ D)).hom) ≫
      𝟙 (X.X ⊗ (Y.X ⊗ (Z.X ⊗ 𝟙_ D)))
  rw [Category.comp_id, whisker_exchange_assoc,
    associator_naturality_right]

/-- The window seed of the tail slot: the whiskered pair seed,
retyped at `modMultiMid` over the head prefix. -/
def tripleSeedSnd
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : Mod D A)
    (Y : Mod D A) (Z : Mod D A) :
    modMultiMid A [X] Y Z [] ⟶ X.X ⊗ ((Y.X ⊗ A) ⊗ Z.X) :=
  X.X ◁ pairSeed A Y Z

/-- The inverse window seed of the tail slot. -/
def tripleSeedSndInv
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : Mod D A)
    (Y : Mod D A) (Z : Mod D A) :
    X.X ⊗ ((Y.X ⊗ A) ⊗ Z.X) ⟶ modMultiMid A [X] Y Z [] :=
  X.X ◁ pairSeedInv A Y Z

/-- The tail-slot leg against the resolution: under the head factor
the leg is the pair leg, and the pair resolution applies. -/
@[reassoc]
lemma tripleLegSnd_resolve
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : Mod D A)
    (Y : Mod D A) (Z : Mod D A)
    (w : (Y.X ⊗ A) ⊗ Z.X ⟶ Y.X ⊗ Z.X)
    (h : ([X] ++ Y :: Z :: [] : List (Mod D A)) = [X, Y, Z]) :
    modMultiLegOf A Y Z [] w [X] ≫ modListCast A h ≫
        tripleResolve A X Y Z =
      tripleSeedSnd A X Y Z ≫ (X.X ◁ w) := by
  show (X.X ◁ ((w ▷ 𝟙_ D) ≫ (α_ Y.X Z.X (𝟙_ D)).hom)) ≫
      𝟙 (X.X ⊗ (Y.X ⊗ (Z.X ⊗ 𝟙_ D))) ≫
        (X.X ◁ (Y.X ◁ (ρ_ Z.X).hom)) =
    (X.X ◁ (ρ_ ((Y.X ⊗ A) ⊗ Z.X)).hom) ≫ (X.X ◁ w)
  rw [Category.id_comp, ← MonoidalCategory.whiskerLeft_comp,
    ← MonoidalCategory.whiskerLeft_comp]
  refine congrArg (fun t => X.X ◁ t) ?_
  have hcoh : (α_ Y.X Z.X (𝟙_ D)).hom ≫ (Y.X ◁ (ρ_ Z.X).hom) =
      (ρ_ (Y.X ⊗ Z.X)).hom := by monoidal
  rw [Category.assoc, hcoh, rightUnitor_naturality]

/-- A window morphism against the inverse resolution, in tail-slot
leg form. -/
@[reassoc]
lemma tripleLegSnd_resolveInv
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : Mod D A)
    (Y : Mod D A) (Z : Mod D A)
    (w : (Y.X ⊗ A) ⊗ Z.X ⟶ Y.X ⊗ Z.X)
    (h : ([X] ++ Y :: Z :: [] : List (Mod D A)) = [X, Y, Z]) :
    (X.X ◁ w) ≫ tripleResolveInv A X Y Z =
      tripleSeedSndInv A X Y Z ≫
        modMultiLegOf A Y Z [] w [X] ≫ modListCast A h := by
  show (X.X ◁ w) ≫ (X.X ◁ (Y.X ◁ (ρ_ Z.X).inv)) =
    (X.X ◁ (ρ_ ((Y.X ⊗ A) ⊗ Z.X)).inv) ≫
      ((X.X ◁ ((w ▷ 𝟙_ D) ≫ (α_ Y.X Z.X (𝟙_ D)).hom)) ≫
        𝟙 (X.X ⊗ (Y.X ⊗ (Z.X ⊗ 𝟙_ D))))
  rw [Category.comp_id, ← MonoidalCategory.whiskerLeft_comp,
    ← MonoidalCategory.whiskerLeft_comp]
  refine congrArg (fun t => X.X ◁ t) ?_
  have hcoh : (ρ_ (Y.X ⊗ Z.X)).inv ≫ (α_ Y.X Z.X (𝟙_ D)).hom =
      Y.X ◁ (ρ_ Z.X).inv := by monoidal
  rw [← rightUnitor_inv_naturality_assoc, hcoh]

end TripleResolve

/-! ## The comparison isomorphism -/

section TripleIso

/-- The head window against the inverse-associator cover: the two
binary legs agree after the cover, by the inner balance whiskered
by `Z`. -/
lemma tripleWindowFst_cond
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ V : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft V)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : Mod D A) (Y : Mod D A)
    (Z : Mod D A) :
    (modTensorLegM A X Y ▷ Z.X) ≫ (α_ X.X Y.X Z.X).hom ≫
        modTensorAssocInvCover A X Y Z =
      (modTensorLegN A X Y ▷ Z.X) ≫ (α_ X.X Y.X Z.X).hom ≫
        modTensorAssocInvCover A X Y Z := by
  rw [modTensorAssocInvCover]
  simp only [Iso.hom_inv_id_assoc]
  erw [← MonoidalCategory.comp_whiskerRight_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    modTensor_condition]

/-- **The forward comparison**: the wide projection descends onto
the cover of the inverse associator.  The head slot condition is
the whiskered binary balance, the tail slot condition is the cover
condition of the inverse associator. -/
noncomputable def modMultiTripleHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ V : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft V)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : Mod D A) (Y : Mod D A)
    (Z : Mod D A) :
    modMulti A [X, Y, Z] ⟶ modTensor A (modTensorMod A X Y) Z :=
  modMultiDesc A
    (tripleResolve A X Y Z ≫ modTensorAssocInvCover A X Y Z)
    (by
      intro pre M N post hd
      rcases triple_decomp A hd with ⟨rfl, h2, h3, rfl⟩ |
        ⟨rfl, h2, h3, rfl⟩
      · subst h2
        subst h3
        rw [modMultiLegM, modMultiLegN,
          tripleLegFst_resolve_assoc A X Y Z _ hd.symm,
          tripleLegFst_resolve_assoc A X Y Z _ hd.symm,
          tripleWindowFst_cond]
      · subst h2
        subst h3
        rw [modMultiLegM, modMultiLegN,
          tripleLegSnd_resolve_assoc A X Y Z _ hd.symm,
          tripleLegSnd_resolve_assoc A X Y Z _ hd.symm,
          modTensorAssocInvCover_cond])

/-- Defining equation of the forward comparison. -/
@[reassoc (attr := simp)]
lemma modMultiπ_tripleHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ V : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft V)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : Mod D A) (Y : Mod D A)
    (Z : Mod D A) :
    modMultiπ A [X, Y, Z] ≫ modMultiTripleHom A X Y Z =
      tripleResolve A X Y Z ≫ modTensorAssocInvCover A X Y Z :=
  modMultiπ_desc A _ _

/-- Defining equation of the forward comparison, with the cover
spelled out on the projections of the nested binary tensor. -/
@[reassoc]
lemma modMultiπ_tripleHom_π
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ V : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft V)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : Mod D A) (Y : Mod D A)
    (Z : Mod D A) :
    modMultiπ A [X, Y, Z] ≫ modMultiTripleHom A X Y Z =
      tripleResolve A X Y Z ≫ (α_ X.X Y.X Z.X).inv ≫
        (modTensorπ A X Y ▷ Z.X) ≫
        modTensorπ A (modTensorMod A X Y) Z := by
  rw [modMultiπ_tripleHom, modTensorAssocInvCover]

/-- The cover of the backward comparison: reassociate, reinstate
the unit seed, and project onto the multi-tensor. -/
noncomputable def tripleInvCover
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] (A : D)
    [MonObj A] (X : Mod D A) (Y : Mod D A) (Z : Mod D A) :
    (X.X ⊗ Y.X) ⊗ Z.X ⟶ modMulti A [X, Y, Z] :=
  (α_ X.X Y.X Z.X).hom ≫ tripleResolveInv A X Y Z ≫
    modMultiπ A [X, Y, Z]

/-- The cover of the backward comparison coequalizes the whiskered
inner balance: the head slot relation of the wide pair. -/
lemma tripleInvCover_cond
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] (A : D)
    [MonObj A] (X : Mod D A) (Y : Mod D A) (Z : Mod D A) :
    (modTensorLegM A X Y ▷ Z.X) ≫ tripleInvCover A X Y Z =
      (modTensorLegN A X Y ▷ Z.X) ≫ tripleInvCover A X Y Z := by
  have hrel := modMulti_rel A [] X Y [Z]
    (rfl : [X, Y, Z] = [] ++ X :: Y :: [Z])
  rw [modMultiLegM, modMultiLegN] at hrel
  rw [tripleInvCover,
    tripleLegFst_resolveInv_assoc A X Y Z _
      (Eq.symm (rfl : [X, Y, Z] = [] ++ X :: Y :: [Z])),
    tripleLegFst_resolveInv_assoc A X Y Z _
      (Eq.symm (rfl : [X, Y, Z] = [] ++ X :: Y :: [Z])),
    hrel]

/-- The tail slot relation after the inverse resolution, spelled at
the braided right action: the bridge between the outer balance of
the nested binary tensor and the wide relation pair. -/
@[reassoc]
lemma tripleResolveInv_snd_rel
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] (A : D)
    [MonObj A] (X : Mod D A) (Y : Mod D A) (Z : Mod D A) :
    (X.X ◁ (actRight A Y.X ▷ Z.X)) ≫ tripleResolveInv A X Y Z ≫
        modMultiπ A [X, Y, Z] =
      (X.X ◁ ((α_ Y.X A Z.X).hom ≫ (Y.X ◁ actLeft A Z.X))) ≫
        tripleResolveInv A X Y Z ≫ modMultiπ A [X, Y, Z] := by
  have hrel := modMulti_rel A [X] Y Z []
    (rfl : [X, Y, Z] = [X] ++ Y :: Z :: [])
  rw [modMultiLegM, modMultiLegN] at hrel
  show (X.X ◁ modTensorLegM A Y Z) ≫ tripleResolveInv A X Y Z ≫
      modMultiπ A [X, Y, Z] =
    (X.X ◁ modTensorLegN A Y Z) ≫ tripleResolveInv A X Y Z ≫
      modMultiπ A [X, Y, Z]
  rw [tripleLegSnd_resolveInv_assoc A X Y Z _
      (Eq.symm (rfl : [X, Y, Z] = [X] ++ Y :: Z :: [])),
    tripleLegSnd_resolveInv_assoc A X Y Z _
      (Eq.symm (rfl : [X, Y, Z] = [X] ++ Y :: Z :: [])),
    hrel]

/-- The half-descended backward comparison, on the cover of the
outer coequalizer of the nested binary tensor. -/
noncomputable def tripleInvMid
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ V : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight V)]
    (A : D) [MonObj A] (X : Mod D A) (Y : Mod D A) (Z : Mod D A) :
    modTensor A X Y ⊗ Z.X ⟶ modMulti A [X, Y, Z] :=
  modTensorWhiskerRDesc A X Y Z.X (tripleInvCover A X Y Z)
    (tripleInvCover_cond A X Y Z)

/-- Defining equation of the half-descended backward comparison. -/
@[reassoc (attr := simp)]
lemma whiskerRight_modTensorπ_tripleInvMid
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ V : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight V)]
    (A : D) [MonObj A] (X : Mod D A) (Y : Mod D A) (Z : Mod D A) :
    (modTensorπ A X Y ▷ Z.X) ≫ tripleInvMid A X Y Z =
      tripleInvCover A X Y Z :=
  whiskerRight_modTensorπ_whiskerRDesc A X Y Z.X _ _

/-- The half-descended backward comparison coequalizes the outer
balance: the monoid sliding between the `(X, Y)`-block and `Z`
slides into the tail slot of the wide relation pair. -/
lemma tripleInvMid_cond
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ V : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft V)]
    [∀ V : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight V)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : Mod D A) (Y : Mod D A)
    (Z : Mod D A) :
    modTensorLegM A (modTensorMod A X Y) Z ≫ tripleInvMid A X Y Z =
      modTensorLegN A (modTensorMod A X Y) Z ≫
        tripleInvMid A X Y Z := by
  refine (cancel_epi ((modTensorπ A X Y ▷ A) ▷ Z.X)).mp ?_
  show ((modTensorπ A X Y ▷ A) ▷ Z.X) ≫
      (((β_ (modTensor A X Y) A).hom ≫ modTensorAct A X Y) ▷
        Z.X) ≫
      tripleInvMid A X Y Z =
    ((modTensorπ A X Y ▷ A) ▷ Z.X) ≫
      ((α_ (modTensor A X Y) A Z.X).hom ≫
        (modTensor A X Y ◁ actLeft A Z.X)) ≫
      tripleInvMid A X Y Z
  conv_lhs => rw [← MonoidalCategory.comp_whiskerRight_assoc,
    modTensorπ_actRight]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  conv_lhs => rw [whiskerRight_modTensorπ_tripleInvMid,
    tripleInvCover, associator_naturality_middle_assoc,
    tripleResolveInv_snd_rel]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  conv_rhs => rw [associator_naturality_left_assoc,
    ← whisker_exchange_assoc, whiskerRight_modTensorπ_tripleInvMid,
    tripleInvCover, associator_naturality_right_assoc]
  rw [pentagon_assoc]

/-- **The backward comparison**: the nested binary tensor descends
onto the multi-tensor, by double descent through the outer and
inner coequalizers. -/
noncomputable def modMultiTripleInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ V : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft V)]
    [∀ V : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight V)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : Mod D A) (Y : Mod D A)
    (Z : Mod D A) :
    modTensor A (modTensorMod A X Y) Z ⟶ modMulti A [X, Y, Z] :=
  modTensorDesc A (modTensorMod A X Y) Z (tripleInvMid A X Y Z)
    (tripleInvMid_cond A X Y Z)

/-- Defining equation of the backward comparison against the outer
projection. -/
@[reassoc (attr := simp)]
lemma modTensorπ_tripleInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ V : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft V)]
    [∀ V : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight V)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : Mod D A) (Y : Mod D A)
    (Z : Mod D A) :
    modTensorπ A (modTensorMod A X Y) Z ≫
        modMultiTripleInv A X Y Z =
      tripleInvMid A X Y Z :=
  modTensorπ_desc A _ _ _ _

/-- Defining equation of the backward comparison against both
projections: reassociate, reinstate the unit seed, and project. -/
@[reassoc]
lemma whiskerRight_modTensorπ_tripleInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ V : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft V)]
    [∀ V : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight V)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : Mod D A) (Y : Mod D A)
    (Z : Mod D A) :
    (modTensorπ A X Y ▷ Z.X) ≫
        modTensorπ A (modTensorMod A X Y) Z ≫
        modMultiTripleInv A X Y Z =
      (α_ X.X Y.X Z.X).hom ≫ tripleResolveInv A X Y Z ≫
        modMultiπ A [X, Y, Z] := by
  repeat' erw [Category.assoc]
  erw [modTensorπ_tripleInv]
  erw [whiskerRight_modTensorπ_tripleInvMid, tripleInvCover]

/-- The forward comparison retracts the backward comparison. -/
@[reassoc (attr := simp)]
lemma modMultiTripleHom_tripleInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ V : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft V)]
    [∀ V : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight V)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : Mod D A) (Y : Mod D A)
    (Z : Mod D A) :
    modMultiTripleHom A X Y Z ≫ modMultiTripleInv A X Y Z =
      𝟙 (modMulti A [X, Y, Z]) := by
  apply modMulti_hom_ext
  rw [modMultiπ_tripleHom_assoc, Category.comp_id,
    modTensorAssocInvCover]
  simp only [Category.assoc]
  repeat' erw [Category.assoc]
  erw [modTensorπ_tripleInv]
  rw [whiskerRight_modTensorπ_tripleInvMid, tripleInvCover,
    Iso.inv_hom_id_assoc, tripleResolve_inv_assoc]

/-- The backward comparison retracts the forward comparison. -/
@[reassoc (attr := simp)]
lemma modMultiTripleInv_tripleHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ V : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft V)]
    [∀ V : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight V)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : Mod D A) (Y : Mod D A)
    (Z : Mod D A) :
    modMultiTripleInv A X Y Z ≫ modMultiTripleHom A X Y Z =
      𝟙 (modTensor A (modTensorMod A X Y) Z) := by
  apply modTensor_hom_ext
  rw [modTensorπ_tripleInv_assoc, Category.comp_id]
  apply modTensor_whiskerR_hom_ext A X Y Z.X
  show (modTensorπ A X Y ▷ Z.X) ≫ tripleInvMid A X Y Z ≫
      modMultiTripleHom A X Y Z =
    (modTensorπ A X Y ▷ Z.X) ≫ modTensorπ A (modTensorMod A X Y) Z
  rw [whiskerRight_modTensorπ_tripleInvMid_assoc, tripleInvCover]
  simp only [Category.assoc]
  rw [modMultiπ_tripleHom, tripleResolveInv_resolve_assoc,
    modTensorAssocInvCover, Iso.hom_inv_id_assoc]

/-- **The three-letter multi-tensor is the nested binary tensor**:
the one-step wide presentation of `modMulti A [X, Y, Z]` and the
left-nested binary module tensor product coequalize the same
relations. -/
noncomputable def modMultiTriple
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ V : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft V)]
    [∀ V : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight V)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : Mod D A) (Y : Mod D A)
    (Z : Mod D A) :
    modMulti A [X, Y, Z] ≅ modTensor A (modTensorMod A X Y) Z where
  hom := modMultiTripleHom A X Y Z
  inv := modMultiTripleInv A X Y Z
  hom_inv_id := modMultiTripleHom_tripleInv A X Y Z
  inv_hom_id := modMultiTripleInv_tripleHom A X Y Z

end TripleIso

end RS
