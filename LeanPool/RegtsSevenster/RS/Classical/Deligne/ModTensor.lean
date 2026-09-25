/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Tensor product of internal modules over a commutative monoid

Module theory over a monoid object, after Deligne (2002), §§2.2–2.3.
Throughout, `D` is a monoidal category and `A : D` a monoid object
in Mathlib's internal sense: `MonObj A`, with internal left modules
given by `ModObj A X` over the self-action of `D` and bundled as
`Mod D A`.

* `actLeft`: the action morphism of a module object, typed at the
  tensor product `A ⊗ X` rather than at the action synonym `⊙ₗ`,
  with the module laws restated in this form.
* `tensorRightModObj`: a left module tensored with an object on the
  right is again a left module; `freeModObj`/`freeMod` specialize to
  the free module `A ⊗ V`.  The regular module is Mathlib's
  `Mod.regular A`.
* `actRight`: on a left module over a commutative monoid in a
  braided category, the braiding induces a right action; the
  compatibility lemmas `actLeft_actRight` and `actRight_actRight`
  express that left and right actions commute and that `actRight`
  is associative.
* `modTensor A M N`: the tensor product of modules, the coequalizer
  of the pair `(M.X ⊗ A) ⊗ N.X ⇉ M.X ⊗ N.X` whose first leg
  `modTensorLegM` acts on `M` through `actRight` and whose second
  leg `modTensorLegN` associates and acts on `N`.
* `modTensorModObj`: the `A`-action descends to the coequalizer
  when every `tensorLeft X` preserves coequalizers; more generally
  `modTensorDescModObj` descends any monoid action on `M.X` that
  commutes with `actRight`.
* `modTensorUnitLeft`/`modTensorUnitRight`: the regular module is a
  two-sided unit, compatibly with the actions.
* `modTensorMap`: functoriality in both slots.
* `restrictRegular`/`baseChange`: base change along a morphism of
  commutative monoid objects.

The development is scoped to the structures above; associativity of
`modTensor` is outside this module's scope.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

section ActLeft

/-- The action morphism of a module object, typed at the tensor
product. -/
def actLeft [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X : D) [ModObj A X] : A ⊗ X ⟶ X :=
  γ[A, X]

/-- Unitality of the action, in tensor form. -/
@[reassoc (attr := simp)]
lemma one_actLeft [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X : D) [ModObj A X] :
    η[A] ▷ X ≫ actLeft A X = (λ_ X).hom :=
  ModObj.one_smul_self A X

/-- Associativity of the action, in tensor form. -/
@[reassoc]
lemma mul_actLeft [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X : D) [ModObj A X] :
    μ[A] ▷ X ≫ actLeft A X =
      (α_ A A X).hom ≫ A ◁ actLeft A X ≫ actLeft A X :=
  ModObj.mul_smul_self A X

/-- Associativity of the action, associator on the right. -/
@[reassoc]
lemma actLeft_actLeft [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X : D) [ModObj A X] :
    A ◁ actLeft A X ≫ actLeft A X =
      (α_ A A X).inv ≫ μ[A] ▷ X ≫ actLeft A X :=
  ModObj.mul_smul_self_flip (M := A) (X := X)

/-- `actLeft` is natural in module morphisms. -/
@[reassoc (attr := simp)]
lemma actLeft_natural [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X Y : D) [ModObj A X] [ModObj A Y]
    (f : X ⟶ Y) [IsModHom A f] :
    actLeft A X ≫ f = A ◁ f ≫ actLeft A Y :=
  IsModHom.smul_hom

/-- The regular module, with underlying object reducibly `A`; it is
definitionally Mathlib's `Mod.regular A`. -/
@[reducible]
def regularMod
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] : Mod D A :=
  letI := ModObj.regular A
  ⟨A⟩

end ActLeft

section TensorRight

/-- Unitality of an action transported to a right tensor factor. -/
lemma one_act_tensorRight
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X : D) (act : A ⊗ X ⟶ X)
    (hone : η[A] ▷ X ≫ act = (λ_ X).hom) (V : D) :
    η[A] ▷ (X ⊗ V) ≫ ((α_ A X V).inv ≫ act ▷ V) =
      (λ_ (X ⊗ V)).hom := by
  rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight,
    hone, ← leftUnitor_tensor_hom]

/-- Associativity of an action transported to a right tensor
factor. -/
lemma mul_act_tensorRight
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X : D) (act : A ⊗ X ⟶ X)
    (hmul : μ[A] ▷ X ≫ act =
      (α_ A A X).hom ≫ A ◁ act ≫ act) (V : D) :
    μ[A] ▷ (X ⊗ V) ≫ ((α_ A X V).inv ≫ act ▷ V) =
      (α_ A A (X ⊗ V)).hom ≫
        A ◁ ((α_ A X V).inv ≫ act ▷ V) ≫
          (α_ A X V).inv ≫ act ▷ V := by
  rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight,
    hmul]
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc,
    associator_inv_naturality_middle_assoc]
  monoidal

/-- A left module tensored with an object on the right: the action
of `A` on `X ⊗ V` through the left factor. -/
@[implicit_reducible]
def tensorRightModObj [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X : D) [ModObj A X] (V : D) :
    ModObj A (X ⊗ V) where
  smul := (α_ A X V).inv ≫ actLeft A X ▷ V
  one_smul := one_act_tensorRight A X (actLeft A X)
    (one_actLeft A X) V
  mul_smul := mul_act_tensorRight A X (actLeft A X)
    (mul_actLeft A X) V

@[simp] lemma tensorRightModObj_smul
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X : D) [ModObj A X] (V : D) :
    (tensorRightModObj A X V).smul =
      (α_ A X V).inv ≫ actLeft A X ▷ V :=
  rfl

/-- The free module on an object: `A ⊗ V` with the action given by
multiplication on the left factor. -/
@[implicit_reducible]
def freeModObj [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (V : D) : ModObj A (A ⊗ V) :=
  letI := ModObj.regular A
  tensorRightModObj A A V

/-- Inserting the unit of `A` and then acting on the free module
is the identity. -/
theorem whiskerLeft_one_mul
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (W : D) :
    A ◁ ((λ_ W).inv ≫ η[A] ▷ W) ≫ ((α_ A A W).inv ≫ μ[A] ▷ W) =
      𝟙 (A ⊗ W) := by
  rw [MonoidalCategory.whiskerLeft_comp, Category.assoc,
    associator_inv_naturality_middle_assoc A (η[A]) W,
    ← comp_whiskerRight, MonObj.mul_one]
  monoidal

/-- The free module on an object, bundled. -/
def freeMod [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (V : D) : Mod D A :=
  letI := freeModObj A V
  ⟨A ⊗ V⟩

/-- The carrier of the free module.  This is definitional, and is
stated for use by name: as a `simp` rule it would rewrite the type
arguments of every application of the module interface at a free
module and so stop that interface firing. -/
lemma freeMod_X [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (V : D) : (freeMod A V).X = A ⊗ V := rfl

end TensorRight

section RightAction

/-- The right action of `A` on a left module, induced by the
braiding. -/
def actRight [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D]
    (X : D) [ModObj A X] : X ⊗ A ⟶ X :=
  (β_ X A).hom ≫ actLeft A X

/-- Unitality of the braided right action. -/
@[reassoc]
lemma actRight_one [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D]
    (X : D) [ModObj A X] :
    X ◁ η[A] ≫ actRight A X = (ρ_ X).hom := by
  simp [actRight, braiding_tensorUnit_right]

/-- `actRight` is natural in module morphisms. -/
@[reassoc]
lemma actRight_natural [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D]
    (X Y : D) [ModObj A X] [ModObj A Y]
    (f : X ⟶ Y) [IsModHom A f] :
    actRight A X ≫ f = f ▷ A ≫ actRight A Y := by
  simp [actRight]

/-- `actRight` is natural in maps of module objects. -/
@[reassoc]
lemma actRight_natural_mod
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D]
    {M N : Mod D A} (f : M ⟶ N) :
    actRight A M.X ≫ f.hom = f.hom ▷ A ≫ actRight A N.X := by
  have := f.isModHom
  exact actRight_natural A M.X N.X f.hom

/-- **The shuffle of two free modules**: multiply the two algebra
factors, having carried the first generator past the second
algebra factor.  This is at once the head absorption that folds an
incoming free letter into an accumulated head. -/
def freeModShuffle [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D]
    (V W : D) : (A ⊗ V) ⊗ (A ⊗ W) ⟶ A ⊗ (V ⊗ W) :=
  tensorμ A V A W ≫ μ[A] ▷ (V ⊗ W)

/-- Two-sided compatibility for a commutative monoid: the left
action and the braided right action on a module commute. -/
@[reassoc]
lemma actLeft_actRight [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D]
    (X : D) [ModObj A X] [IsCommMonObj A] :
    A ◁ actRight A X ≫ actLeft A X =
      (α_ A X A).inv ≫ actLeft A X ▷ A ≫ actRight A X := by
  simp? [actRight, actLeft_actLeft]
  rw [← comp_whiskerRight_assoc, IsCommMonObj.mul_comm]

/-- For a commutative monoid, the braided right action is
associative. -/
@[reassoc]
lemma actRight_actRight [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D]
    (X : D) [ModObj A X] [IsCommMonObj A] :
    actRight A X ▷ A ≫ actRight A X =
      (α_ X A A).hom ≫ X ◁ μ[A] ≫ actRight A X := by
  simp? [actRight, actLeft_actLeft]
  rw [← comp_whiskerRight_assoc, IsCommMonObj.mul_comm]

end RightAction

section ModTensor

/-- First leg of the module-tensor parallel pair on
`(M.X ⊗ A) ⊗ N.X`: act on `M` through the braided right action. -/
def modTensorLegM [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (M : Mod D A) (N : Mod D A) :
    (M.X ⊗ A) ⊗ N.X ⟶ M.X ⊗ N.X :=
  actRight A M.X ▷ N.X

/-- Second leg of the module-tensor parallel pair on
`(M.X ⊗ A) ⊗ N.X`: associate and act on `N`. -/
def modTensorLegN
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (M : Mod D A)
    (N : Mod D A) : (M.X ⊗ A) ⊗ N.X ⟶ M.X ⊗ N.X :=
  (α_ M.X A N.X).hom ≫ M.X ◁ actLeft A N.X

/-- A `P`-action on `M.X` commuting with the braided right
`A`-action intertwines the first leg with the induced actions on
`(M.X ⊗ A) ⊗ N.X` and `M.X ⊗ N.X`. -/
lemma whiskerLeft_modTensorLegM_act
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (M : Mod D A) (N : Mod D A)
    (P : D)
    (act : P ⊗ M.X ⟶ M.X)
    (compat : P ◁ actRight A M.X ≫ act =
      (α_ P M.X A).inv ≫ act ▷ A ≫ actRight A M.X) :
    P ◁ modTensorLegM A M N ≫
        ((α_ P M.X N.X).inv ≫ act ▷ N.X) =
      ((α_ P (M.X ⊗ A) N.X).inv ≫
          ((α_ P M.X A).inv ≫ act ▷ A) ▷ N.X) ≫
        modTensorLegM A M N := by
  rw [modTensorLegM, associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight, compat]
  simp

/-- Any morphism `P ⊗ M.X ⟶ M.X` intertwines the second leg with
the induced maps on `(M.X ⊗ A) ⊗ N.X` and `M.X ⊗ N.X`. -/
lemma whiskerLeft_modTensorLegN_act
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (M : Mod D A)
    (N : Mod D A)
    (P : D)
    (act : P ⊗ M.X ⟶ M.X) :
    P ◁ modTensorLegN A M N ≫
        ((α_ P M.X N.X).inv ≫ act ▷ N.X) =
      ((α_ P (M.X ⊗ A) N.X).inv ≫
          ((α_ P M.X A).inv ≫ act ▷ A) ▷ N.X) ≫
        modTensorLegN A M N := by
  have hstruct :
      P ◁ (α_ M.X A N.X).hom ≫ (α_ P M.X (A ⊗ N.X)).inv =
        (α_ P (M.X ⊗ A) N.X).inv ≫ (α_ P M.X A).inv ▷ N.X ≫
          (α_ (P ⊗ M.X) A N.X).hom := by
    monoidal
  rw [modTensorLegN]
  simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  conv_lhs => rw [associator_inv_naturality_right_assoc,
    whisker_exchange]
  conv_rhs => rw [associator_naturality_left_assoc]
  rw [reassoc_of% hstruct]

section

/-- The tensor product of two modules over `A`: the coequalizer of
`modTensorLegM` and `modTensorLegN`. -/
noncomputable def modTensor
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (M : Mod D A) (N : Mod D A) [HasCoequalizers D] : D :=
  coequalizer (modTensorLegM A M N) (modTensorLegN A M N)

/-- The projection onto the tensor product of modules. -/
noncomputable def modTensorπ
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (M : Mod D A) (N : Mod D A) [HasCoequalizers D] :
    M.X ⊗ N.X ⟶ modTensor A M N :=
  coequalizer.π _ _

/-- The two legs agree after the projection. -/
@[reassoc]
lemma modTensor_condition
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (M : Mod D A) (N : Mod D A) [HasCoequalizers D] :
    modTensorLegM A M N ≫ modTensorπ A M N =
      modTensorLegN A M N ≫ modTensorπ A M N :=
  coequalizer.condition _ _

/-- Descend a morphism coequalizing the two legs to the tensor
product of modules. -/
noncomputable def modTensorDesc
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (M : Mod D A) (N : Mod D A) [HasCoequalizers D]
    {W : D} (k : M.X ⊗ N.X ⟶ W)
    (h : modTensorLegM A M N ≫ k = modTensorLegN A M N ≫ k) :
    modTensor A M N ⟶ W :=
  coequalizer.desc k h

/-- The descent factors the given morphism through the
projection. -/
@[reassoc (attr := simp)]
lemma modTensorπ_desc [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (M : Mod D A) (N : Mod D A) [HasCoequalizers D]
    {W : D} (k : M.X ⊗ N.X ⟶ W)
    (h : modTensorLegM A M N ≫ k = modTensorLegN A M N ≫ k) :
    modTensorπ A M N ≫ modTensorDesc A M N k h = k :=
  coequalizer.π_desc _ _

/-- Morphisms out of the tensor product of modules are determined
by their composite with the projection. -/
lemma modTensor_hom_ext [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (M : Mod D A) (N : Mod D A) [HasCoequalizers D]
    {W : D} {k l : modTensor A M N ⟶ W}
    (h : modTensorπ A M N ≫ k = modTensorπ A M N ≫ l) : k = l :=
  coequalizer.hom_ext h

end

section

/-- Whiskering the module-tensor coequalizer by `tensorLeft P`
yields a colimit cofork. -/
noncomputable def modTensorWhiskerIsColimit
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (M : Mod D A) (N : Mod D A) [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (P : D) :
    IsColimit (Cofork.ofπ (P ◁ modTensorπ A M N)
      (by rw [← whiskerLeft_comp, modTensor_condition,
        whiskerLeft_comp]) :
      Cofork (P ◁ modTensorLegM A M N) (P ◁ modTensorLegN A M N)) :=
  isColimitOfHasCoequalizerOfPreservesColimit (tensorLeft P) _ _

/-- Morphisms out of a whiskered tensor product of modules are
determined by their composite with the whiskered projection. -/
lemma modTensor_whisker_hom_ext
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (M : Mod D A) (N : Mod D A) [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (P : D) {W : D}
    {k l : P ⊗ modTensor A M N ⟶ W}
    (h : P ◁ modTensorπ A M N ≫ k = P ◁ modTensorπ A M N ≫ l) :
    k = l :=
  Cofork.IsColimit.hom_ext (modTensorWhiskerIsColimit A M N P) h

/-- Descend a morphism along the whiskered coequalizer. -/
noncomputable def modTensorWhiskerDesc
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (M : Mod D A) (N : Mod D A) [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (P : D) {W : D}
    (k : P ⊗ (M.X ⊗ N.X) ⟶ W)
    (h : P ◁ modTensorLegM A M N ≫ k =
      P ◁ modTensorLegN A M N ≫ k) :
    P ⊗ modTensor A M N ⟶ W :=
  Cofork.IsColimit.desc (modTensorWhiskerIsColimit A M N P) k h

/-- The whiskered descent factors the given morphism through the
whiskered projection. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_modTensorπ_whiskerDesc
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (M : Mod D A) (N : Mod D A) [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (P : D) {W : D}
    (k : P ⊗ (M.X ⊗ N.X) ⟶ W)
    (h : P ◁ modTensorLegM A M N ≫ k =
      P ◁ modTensorLegN A M N ≫ k) :
    P ◁ modTensorπ A M N ≫ modTensorWhiskerDesc A M N P k h = k :=
  Cofork.IsColimit.π_desc' (modTensorWhiskerIsColimit A M N P) k h

end

section WhiskerRKit

/-- Whiskering the module-tensor coequalizer by `tensorRight W`
yields a colimit cofork. -/
noncomputable def modTensorWhiskerRIsColimit
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (M : Mod D A) (N : Mod D A)
    [Limits.HasCoequalizers D]
    [∀ Z : D, Limits.PreservesColimitsOfShape Limits.WalkingParallelPair
      (tensorRight Z)]
    (W : D) :
    IsColimit (Cofork.ofπ (modTensorπ A M N ▷ W)
      (by rw [← comp_whiskerRight, modTensor_condition,
        comp_whiskerRight]) :
      Cofork (modTensorLegM A M N ▷ W)
        (modTensorLegN A M N ▷ W)) :=
  isColimitOfHasCoequalizerOfPreservesColimit (tensorRight W) _ _

/-- Morphisms out of a right-whiskered tensor product of modules
are determined by their composite with the whiskered
projection. -/
lemma modTensor_whiskerR_hom_ext
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (M : Mod D A) (N : Mod D A)
    [Limits.HasCoequalizers D]
    [∀ Z : D, Limits.PreservesColimitsOfShape Limits.WalkingParallelPair
      (tensorRight Z)]
    (W : D) {Z : D}
    {k l : modTensor A M N ⊗ W ⟶ Z}
    (h : (modTensorπ A M N ▷ W) ≫ k =
      (modTensorπ A M N ▷ W) ≫ l) :
    k = l :=
  Cofork.IsColimit.hom_ext
    (modTensorWhiskerRIsColimit A M N W) h

/-- Descend a morphism along the right-whiskered coequalizer. -/
noncomputable def modTensorWhiskerRDesc
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (M : Mod D A) (N : Mod D A)
    [Limits.HasCoequalizers D]
    [∀ Z : D, Limits.PreservesColimitsOfShape Limits.WalkingParallelPair
      (tensorRight Z)]
    (W : D) {Z : D}
    (k : (M.X ⊗ N.X) ⊗ W ⟶ Z)
    (h : (modTensorLegM A M N ▷ W) ≫ k =
      (modTensorLegN A M N ▷ W) ≫ k) :
    modTensor A M N ⊗ W ⟶ Z :=
  Cofork.IsColimit.desc
    (modTensorWhiskerRIsColimit A M N W) k h

/-- The right-whiskered descent factors the given morphism
through the whiskered projection. -/
@[reassoc (attr := simp)]
lemma whiskerRight_modTensorπ_whiskerRDesc
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (M : Mod D A) (N : Mod D A)
    [Limits.HasCoequalizers D]
    [∀ Z : D, Limits.PreservesColimitsOfShape Limits.WalkingParallelPair
      (tensorRight Z)]
    (W : D) {Z : D}
    (k : (M.X ⊗ N.X) ⊗ W ⟶ Z)
    (h : (modTensorLegM A M N ▷ W) ≫ k =
      (modTensorLegN A M N ▷ W) ≫ k) :
    (modTensorπ A M N ▷ W) ≫
        modTensorWhiskerRDesc A M N W k h = k :=
  Cofork.IsColimit.π_desc'
    (modTensorWhiskerRIsColimit A M N W) k h

end WhiskerRKit

end ModTensor

section DescAct

/-- Descend a compatible action along the module-tensor
projection. -/
noncomputable def modTensorDescAct
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (M : Mod D A) (N : Mod D A) [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (P : D)
    (act : P ⊗ M.X ⟶ M.X)
    (compat : P ◁ actRight A M.X ≫ act =
      (α_ P M.X A).inv ≫ act ▷ A ≫ actRight A M.X) :
    P ⊗ modTensor A M N ⟶ modTensor A M N :=
  modTensorWhiskerDesc A M N P
    (((α_ P M.X N.X).inv ≫ act ▷ N.X) ≫ modTensorπ A M N)
    (by
      conv_lhs => rw [← Category.assoc,
        whiskerLeft_modTensorLegM_act A M N P act compat,
        Category.assoc, modTensor_condition]
      conv_rhs => rw [← Category.assoc,
        whiskerLeft_modTensorLegN_act A M N P act,
        Category.assoc])

/-- Defining equation of the descended action. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_modTensorπ_descAct
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (M : Mod D A) (N : Mod D A) [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (P : D)
    (act : P ⊗ M.X ⟶ M.X)
    (compat : P ◁ actRight A M.X ≫ act =
      (α_ P M.X A).inv ≫ act ▷ A ≫ actRight A M.X) :
    P ◁ modTensorπ A M N ≫ modTensorDescAct A M N P act compat =
      ((α_ P M.X N.X).inv ≫ act ▷ N.X) ≫ modTensorπ A M N :=
  whiskerLeft_modTensorπ_whiskerDesc A M N P _ _

/-- Unitality descends to the tensor product of modules. -/
lemma modTensorDescAct_one
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (M : Mod D A) (N : Mod D A) [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (P : D) [MonObj P]
    (act : P ⊗ M.X ⟶ M.X)
    (compat : P ◁ actRight A M.X ≫ act =
      (α_ P M.X A).inv ≫ act ▷ A ≫ actRight A M.X)
    (hone : η[P] ▷ M.X ≫ act = (λ_ M.X).hom) :
    η[P] ▷ modTensor A M N ≫ modTensorDescAct A M N P act compat =
      (λ_ (modTensor A M N)).hom := by
  apply modTensor_whisker_hom_ext A M N (𝟙_ D)
  have h1 := one_act_tensorRight P M.X act hone N.X
  rw [whisker_exchange_assoc, whiskerLeft_modTensorπ_descAct]
  simp only [Category.assoc]
  rw [reassoc_of% h1]
  simp

/-- Associativity descends to the tensor product of modules. -/
lemma modTensorDescAct_mul
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (M : Mod D A) (N : Mod D A) [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (P : D) [MonObj P]
    (act : P ⊗ M.X ⟶ M.X)
    (compat : P ◁ actRight A M.X ≫ act =
      (α_ P M.X A).inv ≫ act ▷ A ≫ actRight A M.X)
    (hmul : μ[P] ▷ M.X ≫ act =
      (α_ P P M.X).hom ≫ P ◁ act ≫ act) :
    μ[P] ▷ modTensor A M N ≫ modTensorDescAct A M N P act compat =
      (α_ P P (modTensor A M N)).hom ≫
        P ◁ modTensorDescAct A M N P act compat ≫
          modTensorDescAct A M N P act compat := by
  apply modTensor_whisker_hom_ext A M N (P ⊗ P)
  have h2 := mul_act_tensorRight P M.X act hmul N.X
  conv_lhs => rw [whisker_exchange_assoc,
    whiskerLeft_modTensorπ_descAct]
  conv_rhs => rw [associator_naturality_right_assoc,
    ← whiskerLeft_comp_assoc,
    whiskerLeft_modTensorπ_descAct A M N P act compat,
    whiskerLeft_comp_assoc,
    whiskerLeft_modTensorπ_descAct A M N P act compat]
  simp only [Category.assoc]
  rw [reassoc_of% h2]

/-- The descended action intertwines descended morphisms with
actions on the target: if `k` coequalizes the legs and carries the
induced action on `M.X ⊗ N.X` to `w`, then the descent of `k` is
equivariant. -/
lemma modTensorDescAct_desc
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (M : Mod D A) (N : Mod D A) [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (P : D)
    (act : P ⊗ M.X ⟶ M.X)
    (compat : P ◁ actRight A M.X ≫ act =
      (α_ P M.X A).inv ≫ act ▷ A ≫ actRight A M.X)
    {W : D} (k : M.X ⊗ N.X ⟶ W)
    (hk : modTensorLegM A M N ≫ k = modTensorLegN A M N ≫ k)
    (w : P ⊗ W ⟶ W)
    (hw : (α_ P M.X N.X).inv ≫ act ▷ N.X ≫ k = P ◁ k ≫ w) :
    modTensorDescAct A M N P act compat ≫
        modTensorDesc A M N k hk =
      P ◁ modTensorDesc A M N k hk ≫ w := by
  apply modTensor_whisker_hom_ext A M N P
  conv_lhs => rw [whiskerLeft_modTensorπ_descAct_assoc,
    modTensorπ_desc, hw]
  conv_rhs => rw [← whiskerLeft_comp_assoc, modTensorπ_desc]

/-- Descend a compatible monoid action on `M.X` to a module
structure on the tensor product. -/
@[implicit_reducible]
noncomputable def modTensorDescModObj
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] (M : Mod D A) (N : Mod D A) [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (P : D) [MonObj P]
    (act : P ⊗ M.X ⟶ M.X)
    (compat : P ◁ actRight A M.X ≫ act =
      (α_ P M.X A).inv ≫ act ▷ A ≫ actRight A M.X)
    (hone : η[P] ▷ M.X ≫ act = (λ_ M.X).hom)
    (hmul : μ[P] ▷ M.X ≫ act =
      (α_ P P M.X).hom ≫ P ◁ act ≫ act) :
    ModObj P (modTensor A M N) where
  smul := modTensorDescAct A M N P act compat
  one_smul := modTensorDescAct_one A M N P act compat hone
  mul_smul := modTensorDescAct_mul A M N P act compat hmul

end DescAct

section TensorModule

/-- The `A`-module structure on the tensor product of modules over
a commutative monoid: the action on the `M`-factor descends. -/
@[implicit_reducible]
noncomputable def modTensorModObj
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)] :
    ModObj A (modTensor A M N) :=
  modTensorDescModObj A M N A (actLeft A M.X)
    (actLeft_actRight A M.X) (one_actLeft A M.X) (mul_actLeft A M.X)

/-- The action of `A` on the tensor product of modules. -/
noncomputable def modTensorAct
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)] :
    A ⊗ modTensor A M N ⟶ modTensor A M N :=
  (modTensorModObj A M N).smul

/-- Defining equation of the `A`-action on the tensor product of
modules. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_modTensorπ_act
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)] :
    A ◁ modTensorπ A M N ≫ modTensorAct A M N =
      ((α_ A M.X N.X).inv ≫ actLeft A M.X ▷ N.X) ≫
        modTensorπ A M N :=
  whiskerLeft_modTensorπ_descAct A M N A (actLeft A M.X)
    (actLeft_actRight A M.X)

/-- Unitality of the descended action. -/
lemma modTensorAct_one [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)] :
    η[A] ▷ modTensor A M N ≫ modTensorAct A M N =
      (λ_ (modTensor A M N)).hom :=
  modTensorDescAct_one A M N A (actLeft A M.X)
    (actLeft_actRight A M.X) (one_actLeft A M.X)

/-- Associativity of the descended action. -/
lemma modTensorAct_mul [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)] :
    μ[A] ▷ modTensor A M N ≫ modTensorAct A M N =
      (α_ A A (modTensor A M N)).hom ≫
        A ◁ modTensorAct A M N ≫ modTensorAct A M N :=
  modTensorDescAct_mul A M N A (actLeft A M.X)
    (actLeft_actRight A M.X) (mul_actLeft A M.X)

/-- The tensor product of modules, bundled as a module. -/
noncomputable def modTensorMod
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)] :
    Mod D A :=
  letI := modTensorModObj A M N
  ⟨modTensor A M N⟩

/-- The carrier of the bundled tensor product.  Definitional, and
stated for use by name, for the reason given for `freeMod_X`. -/
lemma modTensorMod_X [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)] :
    (modTensorMod A M N).X = modTensor A M N := rfl

end TensorModule

section ActSnd

/-- **The descended action through the second factor**: over a
symmetric base, the monoid braids past the first module and acts
on the second.  The balance relation of the coequalizer carries
the first-factor action across. -/
@[reassoc]
lemma whiskerLeft_modTensorπ_act_snd
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [SymmetricCategory D] [IsCommMonObj A] (M : Mod D A) (N : Mod D A)
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)] :
    A ◁ modTensorπ A M N ≫ modTensorAct A M N =
      (α_ A M.X N.X).inv ≫ ((β_ A M.X).hom ▷ N.X) ≫
        (α_ M.X A N.X).hom ≫ (M.X ◁ actLeft A N.X) ≫
        modTensorπ A M N := by
  rw [whiskerLeft_modTensorπ_act]
  simp only [Category.assoc]
  rw [cancel_epi]
  have hact : actLeft A M.X ▷ N.X =
      ((β_ A M.X).hom ▷ N.X) ≫ modTensorLegM A M N := by
    rw [modTensorLegM, actRight,
      ← MonoidalCategory.comp_whiskerRight,
      SymmetricCategory.symmetry_assoc]
  rw [hact, Category.assoc, modTensor_condition, modTensorLegN]
  simp only [Category.assoc]

end ActSnd

section Units

/-- The action of `N` coequalizes the legs at `M = A`. -/
lemma modTensorLegM_regular_actLeft
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] (N : Mod D A) :
    modTensorLegM A (regularMod A) N ≫ actLeft A N.X =
      modTensorLegN A (regularMod A) N ≫ actLeft A N.X := by
  change ((β_ A A).hom ≫ μ[A]) ▷ N.X ≫ actLeft A N.X =
    ((α_ A A N.X).hom ≫ A ◁ actLeft A N.X) ≫ actLeft A N.X
  rw [IsCommMonObj.mul_comm, mul_actLeft, Category.assoc]

/-- The right action of `M` coequalizes the legs at `N = A`. -/
lemma modTensorLegM_regular_actRight
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] (M : Mod D A) :
    modTensorLegM A M (regularMod A) ≫ actRight A M.X =
      modTensorLegN A M (regularMod A) ≫ actRight A M.X := by
  change actRight A M.X ▷ A ≫ actRight A M.X =
    ((α_ M.X A A).hom ≫ M.X ◁ μ[A]) ≫ actRight A M.X
  rw [actRight_actRight, Category.assoc]

/-- The regular module is a left unit for the module tensor
product. -/
@[simps]
noncomputable def modTensorUnitLeft
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] (N : Mod D A) [HasCoequalizers D] :
    modTensor A (regularMod A) N ≅ N.X where
  hom := modTensorDesc A (regularMod A) N (actLeft A N.X)
    (modTensorLegM_regular_actLeft A N)
  inv := (λ_ N.X).inv ≫ η[A] ▷ N.X ≫ modTensorπ A (regularMod A) N
  hom_inv_id := by
    have hM : (((λ_ A).inv ≫ η[A] ▷ A) ▷ N.X) ≫
        modTensorLegM A (regularMod A) N = 𝟙 (A ⊗ N.X) := by
      change (((λ_ A).inv ≫ η[A] ▷ A) ▷ N.X) ≫
        ((β_ A A).hom ≫ μ[A]) ▷ N.X = 𝟙 (A ⊗ N.X)
      rw [← comp_whiskerRight, IsCommMonObj.mul_comm]
      simp
    have hN : (((λ_ A).inv ≫ η[A] ▷ A) ▷ N.X) ≫
        modTensorLegN A (regularMod A) N =
          actLeft A N.X ≫ (λ_ N.X).inv ≫ η[A] ▷ N.X := by
      change (((λ_ A).inv ≫ η[A] ▷ A) ▷ N.X) ≫
        ((α_ A A N.X).hom ≫ A ◁ actLeft A N.X) =
          actLeft A N.X ≫ (λ_ N.X).inv ≫ η[A] ▷ N.X
      simp only [comp_whiskerRight, Category.assoc]
      rw [associator_naturality_left_assoc, ← whisker_exchange,
        ← leftUnitor_tensor_inv_assoc,
        ← leftUnitor_inv_naturality_assoc]
    apply modTensor_hom_ext
    rw [modTensorπ_desc_assoc, ← reassoc_of% hN,
      ← modTensor_condition, reassoc_of% hM]
    simp
  inv_hom_id := by simp

/-- The regular module is a right unit for the module tensor
product of a commutative monoid. -/
@[simps]
noncomputable def modTensorUnitRight
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] (M : Mod D A) [HasCoequalizers D] :
    modTensor A M (regularMod A) ≅ M.X where
  hom := modTensorDesc A M (regularMod A) (actRight A M.X)
    (modTensorLegM_regular_actRight A M)
  inv := (ρ_ M.X).inv ≫ M.X ◁ η[A] ≫ modTensorπ A M (regularMod A)
  hom_inv_id := by
    have hM : ((ρ_ (M.X ⊗ A)).inv ≫ (M.X ⊗ A) ◁ η[A]) ≫
        modTensorLegM A M (regularMod A) =
          actRight A M.X ≫ (ρ_ M.X).inv ≫ M.X ◁ η[A] := by
      change ((ρ_ (M.X ⊗ A)).inv ≫ (M.X ⊗ A) ◁ η[A]) ≫
        actRight A M.X ▷ A =
          actRight A M.X ≫ (ρ_ M.X).inv ≫ M.X ◁ η[A]
      rw [Category.assoc, whisker_exchange,
        ← rightUnitor_inv_naturality_assoc]
    have hN : ((ρ_ (M.X ⊗ A)).inv ≫ (M.X ⊗ A) ◁ η[A]) ≫
        modTensorLegN A M (regularMod A) = 𝟙 (M.X ⊗ A) := by
      change ((ρ_ (M.X ⊗ A)).inv ≫ (M.X ⊗ A) ◁ η[A]) ≫
        ((α_ M.X A A).hom ≫ M.X ◁ μ[A]) = 𝟙 (M.X ⊗ A)
      simp only [Category.assoc]
      rw [associator_naturality_right_assoc, ← whiskerLeft_comp,
        MonObj.mul_one, ← rightUnitor_tensor_hom]
      simp
    apply modTensor_hom_ext
    rw [modTensorπ_desc_assoc, ← reassoc_of% hM,
      modTensor_condition, reassoc_of% hN]
    simp
  inv_hom_id := by simp [actRight_one]

/-- The left unit isomorphism is a morphism of modules. -/
@[reassoc]
lemma modTensorUnitLeft_hom_actLeft
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] (N : Mod D A) [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)] :
    modTensorAct A (regularMod A) N ≫
        (modTensorUnitLeft A N).hom =
      A ◁ (modTensorUnitLeft A N).hom ≫ actLeft A N.X := by
  apply modTensor_whisker_hom_ext A (regularMod A) N A
  conv_lhs => rw [whiskerLeft_modTensorπ_act_assoc,
    modTensorUnitLeft_hom, modTensorπ_desc]
  conv_rhs => rw [modTensorUnitLeft_hom, ← whiskerLeft_comp_assoc,
    modTensorπ_desc, actLeft_actLeft]
  rfl

/-- The right unit isomorphism is a morphism of modules. -/
@[reassoc]
lemma modTensorUnitRight_hom_actLeft
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] (M : Mod D A) [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)] :
    modTensorAct A M (regularMod A) ≫
        (modTensorUnitRight A M).hom =
      A ◁ (modTensorUnitRight A M).hom ≫ actLeft A M.X := by
  apply modTensor_whisker_hom_ext A M (regularMod A) A
  conv_lhs => rw [whiskerLeft_modTensorπ_act_assoc,
    modTensorUnitRight_hom, modTensorπ_desc]
  conv_rhs => rw [modTensorUnitRight_hom, ← whiskerLeft_comp_assoc,
    modTensorπ_desc, actLeft_actRight]

end Units

section Functoriality

/-- Module morphisms intertwine the first legs. -/
lemma modTensorLegM_tensorHom
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] {M : Mod D A} {M' : Mod D A} {N : Mod D A}
    {N' : Mod D A}
    (f : M ⟶ M') (g : N ⟶ N') :
    modTensorLegM A M N ≫ (f.hom ⊗ₘ g.hom) =
      (f.hom ▷ A ⊗ₘ g.hom) ≫ modTensorLegM A M' N' := by
  rw [modTensorLegM, modTensorLegM, tensorHom_def, tensorHom_def]
  conv_lhs => rw [← comp_whiskerRight_assoc,
    actRight_natural A M.X M'.X f.hom, comp_whiskerRight_assoc]
  conv_rhs => rw [Category.assoc, whisker_exchange]

/-- Module morphisms intertwine the second legs. -/
lemma modTensorLegN_tensorHom
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] {M : Mod D A}
    {M' : Mod D A} {N : Mod D A} {N' : Mod D A}
    (f : M ⟶ M') (g : N ⟶ N') :
    modTensorLegN A M N ≫ (f.hom ⊗ₘ g.hom) =
      (f.hom ▷ A ⊗ₘ g.hom) ≫ modTensorLegN A M' N' := by
  rw [modTensorLegN, modTensorLegN, tensorHom_def, tensorHom_def]
  conv_lhs => rw [Category.assoc, whisker_exchange_assoc,
    ← whiskerLeft_comp, actLeft_natural A N.X N'.X g.hom,
    whiskerLeft_comp]
  conv_rhs => rw [Category.assoc,
    associator_naturality_right_assoc,
    associator_naturality_left_assoc]

/-- Functoriality of the module tensor product in both slots. -/
noncomputable def modTensorMap
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] {M : Mod D A} {M' : Mod D A} {N : Mod D A}
    {N' : Mod D A} [HasCoequalizers D]
    (f : M ⟶ M') (g : N ⟶ N') :
    modTensor A M N ⟶ modTensor A M' N' :=
  modTensorDesc A M N ((f.hom ⊗ₘ g.hom) ≫ modTensorπ A M' N')
    (by
      conv_lhs => rw [← Category.assoc,
        modTensorLegM_tensorHom A f g, Category.assoc,
        modTensor_condition]
      conv_rhs => rw [← Category.assoc,
        modTensorLegN_tensorHom A f g, Category.assoc])

/-- Defining equation of the functorial map. -/
@[reassoc (attr := simp)]
lemma modTensorπ_map [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] {M : Mod D A} {M' : Mod D A} {N : Mod D A}
    {N' : Mod D A} [HasCoequalizers D]
    (f : M ⟶ M') (g : N ⟶ N') :
    modTensorπ A M N ≫ modTensorMap A f g =
      (f.hom ⊗ₘ g.hom) ≫ modTensorπ A M' N' :=
  modTensorπ_desc A M N _ _

/-- The functorial map preserves identities. -/
lemma modTensorMap_id [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] {M : Mod D A} {N : Mod D A} [HasCoequalizers D] :
    modTensorMap A (𝟙 M) (𝟙 N) = 𝟙 (modTensor A M N) := by
  apply modTensor_hom_ext
  simp

/-- The functorial map preserves composition. -/
lemma modTensorMap_comp [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] {M : Mod D A} {M' : Mod D A} {M'' : Mod D A}
    {N : Mod D A} {N' : Mod D A} {N'' : Mod D A} [HasCoequalizers D]
    (f : M ⟶ M') (f' : M' ⟶ M'')
    (g : N ⟶ N') (g' : N' ⟶ N'') :
    modTensorMap A (f ≫ f') (g ≫ g') =
      modTensorMap A f g ≫ modTensorMap A f' g' := by
  apply modTensor_hom_ext
  simp

/-- `modTensorMap` is a morphism of modules. -/
@[reassoc]
lemma modTensorAct_map [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] {M : Mod D A} {M' : Mod D A} {N : Mod D A}
    {N' : Mod D A} [HasCoequalizers D] [IsCommMonObj A]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (f : M ⟶ M') (g : N ⟶ N') :
    modTensorAct A M N ≫ modTensorMap A f g =
      A ◁ modTensorMap A f g ≫ modTensorAct A M' N' := by
  have hpre : (α_ A M.X N.X).inv ≫ actLeft A M.X ▷ N.X ≫
      (f.hom ⊗ₘ g.hom) =
        A ◁ (f.hom ⊗ₘ g.hom) ≫ (α_ A M'.X N'.X).inv ≫
          actLeft A M'.X ▷ N'.X := by
    conv_rhs => rw [← id_tensorHom, associator_inv_naturality_assoc]
    simp?
    rw [← tensorHom_id (actLeft A M.X) N.X,
      ← tensorHom_id (actLeft A M'.X) N'.X,
      tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    simp
  apply modTensor_whisker_hom_ext A M N A
  conv_lhs => rw [whiskerLeft_modTensorπ_act_assoc,
    modTensorπ_map]
  conv_rhs => rw [← whiskerLeft_comp_assoc, modTensorπ_map,
    whiskerLeft_comp_assoc, whiskerLeft_modTensorπ_act]
  simp only [Category.assoc]
  rw [reassoc_of% hpre]

/-- Functoriality, as a morphism of bundled modules. -/
noncomputable def modTensorMapMod
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] {M : Mod D A} {M' : Mod D A} {N : Mod D A}
    {N' : Mod D A} [HasCoequalizers D] [IsCommMonObj A]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (f : M ⟶ M') (g : N ⟶ N') :
    modTensorMod A M N ⟶ modTensorMod A M' N' :=
  Mod.Hom.mk' (modTensorMap A f g) (modTensorAct_map A f g)

/-- The relative tensor product of two module isomorphisms. -/
noncomputable def modTensorMapIso
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] {M : Mod D A} {M' : Mod D A} {N : Mod D A}
    {N' : Mod D A} [HasCoequalizers D] [IsCommMonObj A]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (e : M ≅ M') (f : N ≅ N') :
    modTensorMod A M N ≅ modTensorMod A M' N' where
  hom := modTensorMapMod A e.hom f.hom
  inv := modTensorMapMod A e.inv f.inv
  hom_inv_id := Mod.hom_ext _ _ (by
    change modTensorMap A e.hom f.hom ≫
        modTensorMap A e.inv f.inv = 𝟙 _
    rw [← modTensorMap_comp, Iso.hom_inv_id, Iso.hom_inv_id,
      modTensorMap_id])
  inv_hom_id := Mod.hom_ext _ _ (by
    change modTensorMap A e.inv f.inv ≫
        modTensorMap A e.hom f.hom = 𝟙 _
    rw [← modTensorMap_comp, Iso.inv_hom_id, Iso.inv_hom_id,
      modTensorMap_id])

end Functoriality

section BaseChange

/-- `B` as an `A`-module by restriction along `φ`, with underlying
object reducibly `B`. -/
@[reducible]
def restrictRegular
    [Category.{v} D] [MonoidalCategory D] {A : D} {B : D} [MonObj A]
    [MonObj B] (φ : A ⟶ B) [IsMonHom φ] : Mod D A :=
  letI := ModObj.regular B
  letI := Mod.scalarRestriction φ B
  ⟨B⟩

/-- For commutative `B`, the braided right `A`-action on the
restricted module is right multiplication through `φ`. -/
lemma actRight_restrictRegular
    [Category.{v} D] [MonoidalCategory D] {A : D} {B : D} [MonObj A]
    [MonObj B] (φ : A ⟶ B) [IsMonHom φ] [BraidedCategory D]
    [IsCommMonObj B] :
    haveI := ModObj.regular B
    haveI := Mod.scalarRestriction φ B
    actRight A B = B ◁ φ ≫ μ[B] := by
  change (β_ B A).hom ≫ φ ▷ B ≫ μ[B] = B ◁ φ ≫ μ[B]
  rw [← BraidedCategory.braiding_naturality_right_assoc,
    IsCommMonObj.mul_comm]

/-- Multiplication of `B` commutes with the right `A`-action on the
restricted module. -/
lemma mul_actRight_restrictRegular
    [Category.{v} D] [MonoidalCategory D] {A : D} {B : D} [MonObj A]
    [MonObj B] (φ : A ⟶ B) [IsMonHom φ] [BraidedCategory D]
    [IsCommMonObj B] :
    haveI := ModObj.regular B
    haveI := Mod.scalarRestriction φ B
    B ◁ actRight A B ≫ μ[B] =
      (α_ B B A).inv ≫ μ[B] ▷ A ≫ actRight A B := by
  rw [actRight_restrictRegular φ]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [MonObj.mul_assoc_flip, associator_inv_naturality_right_assoc,
    whisker_exchange_assoc]

/-- Base change along `φ`: the extension `B ⊗[A] M` of an
`A`-module `M`. -/
noncomputable def baseChange
    [Category.{v} D] [MonoidalCategory D] {A : D} {B : D} [MonObj A]
    [MonObj B] (φ : A ⟶ B) [IsMonHom φ] [BraidedCategory D]
    [HasCoequalizers D]
    (M : Mod D A) : D :=
  modTensor A (restrictRegular φ) M

/-- The `B`-module structure on the base change: multiplication on
the left factor descends. -/
@[implicit_reducible]
noncomputable def baseChangeModObj
    [Category.{v} D] [MonoidalCategory D] {A : D} {B : D} [MonObj A]
    [MonObj B] (φ : A ⟶ B) [IsMonHom φ] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (M : Mod D A) [IsCommMonObj B] :
    ModObj B (baseChange φ M) :=
  modTensorDescModObj A (restrictRegular φ) M B μ[B]
    (mul_actRight_restrictRegular φ) (MonObj.one_mul B)
    (MonObj.mul_assoc B)

/-- The action of `B` on the base change. -/
noncomputable def baseChangeAct
    [Category.{v} D] [MonoidalCategory D] {A : D} {B : D} [MonObj A]
    [MonObj B] (φ : A ⟶ B) [IsMonHom φ] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (M : Mod D A) [IsCommMonObj B] :
    B ⊗ baseChange φ M ⟶ baseChange φ M :=
  (baseChangeModObj φ M).smul

/-- Defining equation of the `B`-action on the base change. -/
@[simp, reassoc]
lemma whiskerLeft_modTensorπ_baseChangeAct
    [Category.{v} D] [MonoidalCategory D] {A : D} {B : D} [MonObj A]
    [MonObj B] (φ : A ⟶ B) [IsMonHom φ] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (M : Mod D A)
    [IsCommMonObj B] :
    B ◁ modTensorπ A (restrictRegular φ) M ≫ baseChangeAct φ M =
      ((α_ B B M.X).inv ≫ μ[B] ▷ M.X) ≫
        modTensorπ A (restrictRegular φ) M :=
  whiskerLeft_modTensorπ_descAct A (restrictRegular φ) M B μ[B]
    (mul_actRight_restrictRegular φ)

/-- Base change, bundled as a `B`-module. -/
noncomputable def baseChangeMod
    [Category.{v} D] [MonoidalCategory D] {A : D} {B : D} [MonObj A]
    [MonObj B] (φ : A ⟶ B) [IsMonHom φ] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (M : Mod D A) [IsCommMonObj B] :
    Mod D B :=
  letI := baseChangeModObj φ M
  ⟨baseChange φ M⟩

@[simp] lemma baseChangeMod_X
    [Category.{v} D] [MonoidalCategory D] {A : D} {B : D} [MonObj A]
    [MonObj B] (φ : A ⟶ B) [IsMonHom φ] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (M : Mod D A) [IsCommMonObj B] :
    (baseChangeMod φ M).X = baseChange φ M := rfl

end BaseChange

end RS
