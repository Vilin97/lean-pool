/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreeModShuffle
import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaPair

/-!
# The relative tensor of two free modules

The relative tensor product of the free modules on two objects is
the free module on their tensor product.  The comparison is the
*shuffle*: multiply the two algebra factors, having carried the
first generator past the second algebra factor.

* the shuffle `RS.freeModShuffle` of
  `RS/Classical/Deligne/ModTensor.lean`, Mathlib's middle-four
  interchange `tensorμ` followed by multiplication;
* `freeModTensorIso`: the resulting isomorphism of `R`-modules
  `modTensorMod R (freeMod R V) (freeMod R W) ≅ freeMod R (V ⊗ W)`.
* `modTensorπ_freeModTensorIso` and `freeModTensorIso_gpair`: the
  isomorphism computes the projection, hence the pairing
  `RS.gpair`, as the shuffle.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

/-! ## Coherence for the shuffle -/

section Coherence

variable {D : Type u}

/-- The braided coherence morphism carrying a generator past a
scalar: `(R ⊗ V) ⊗ R ⟶ (R ⊗ R) ⊗ V`. -/
def freeModSlide
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    (V : D) : (R ⊗ V) ⊗ R ⟶ (R ⊗ R) ⊗ V :=
  (α_ R V R).hom ≫ R ◁ (β_ V R).hom ≫ (α_ R R V).inv

/-- The middle-four interchange at a free pair, cut open along the
last factor: it is the slide of the generator past the scalar,
whiskered by that factor. -/
theorem freeModSlide_whiskerRight
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    (V : D) (W : D) :
    (α_ (R ⊗ V) R W).inv ≫ freeModSlide R V ▷ W =
      tensorμ R V R W ≫ (α_ (R ⊗ R) V W).inv := by
  simp only [freeModSlide, tensorμ, comp_whiskerRight,
    Category.assoc]
  monoidal

/-- **Associativity of the shuffle**: sliding and then
interchanging against a third scalar agrees with interchanging
against the product of the last two scalars.  This is the coherence
behind the balance relation of the relative tensor product. -/
theorem freeModSlide_tensorμ
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    (V : D) (W : D) :
    freeModSlide R V ▷ (R ⊗ W) ≫ tensorμ (R ⊗ R) V R W =
      (α_ (R ⊗ V) R (R ⊗ W)).hom ≫ (R ⊗ V) ◁ (α_ R R W).inv ≫
        tensorμ R V (R ⊗ R) W ≫ (α_ R R R).inv ▷ (V ⊗ W) := by
  simp only [freeModSlide, tensorμ,
    BraidedCategory.braiding_tensor_right_hom, Category.assoc]
  monoidal

/-- **Equivariance of the shuffle**: acting on the leading scalar
and then interchanging agrees with interchanging and then acting.
This is the coherence behind the linearity of the comparison. -/
theorem tensorμ_whiskerLeft_shuffle
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    (V : D) (W : D) :
    (α_ R (R ⊗ V) (R ⊗ W)).inv ≫ (α_ R R V).inv ▷ (R ⊗ W) ≫
        tensorμ (R ⊗ R) V R W =
      R ◁ tensorμ R V R W ≫ (α_ R (R ⊗ R) (V ⊗ W)).inv ≫
        (α_ R R R).inv ▷ (V ⊗ W) := by
  simp only [tensorμ, MonoidalCategory.whiskerLeft_comp,
    Category.assoc]
  monoidal

/-- Interchanging against a unit scalar is a reassociation. -/
theorem whiskerLeft_leftUnitor_inv_tensorμ
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    (V : D) (W : D) :
    (R ⊗ V) ◁ (λ_ W).inv ≫ tensorμ R V (𝟙_ D) W ≫
        (ρ_ R).hom ▷ (V ⊗ W) = (α_ R V W).hom := by
  simp only [tensorμ, braiding_tensorUnit_right, Category.assoc]
  monoidal

end Coherence

/-! ## The shuffle -/

section Shuffle

variable {D : Type u}

/-- Multiplying the leading scalars moves through the
interchange. -/
theorem whiskerRight_mul_tensorμ
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R] (V : D) (W : D) :
    (μ[R] ▷ V) ▷ (R ⊗ W) ≫ tensorμ R V R W =
      tensorμ (R ⊗ R) V R W ≫ (μ[R] ▷ R) ▷ (V ⊗ W) := by
  simpa using tensorμ_natural_left (μ[R]) (𝟙 V) R W

/-- Multiplying the trailing scalars moves through the
interchange. -/
theorem whiskerLeft_mul_tensorμ
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R] (V : D) (W : D) :
    (R ⊗ V) ◁ (μ[R] ▷ W) ≫ tensorμ R V R W =
      tensorμ R V (R ⊗ R) W ≫ (R ◁ μ[R]) ▷ (V ⊗ W) := by
  simpa using tensorμ_natural_right R V (μ[R]) (𝟙 W)

/-- The trailing unit moves through the interchange. -/
theorem whiskerLeft_one_tensorμ
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R] (V : D) (W : D) :
    (R ⊗ V) ◁ (η[R] ▷ W) ≫ tensorμ R V R W =
      tensorμ R V (𝟙_ D) W ≫ (R ◁ η[R]) ▷ (V ⊗ W) := by
  simpa using tensorμ_natural_right R V (η[R]) (𝟙 W)

/-- Associativity of the algebra, whiskered by an object. -/
theorem whiskerRight_mul_assoc
    [Category.{v} D] [MonoidalCategory D] (R : D) [MonObj R]
    (X : D) :
    (R ◁ μ[R]) ▷ X ≫ μ[R] ▷ X =
      (α_ R R R).inv ▷ X ≫ (μ[R] ▷ R) ▷ X ≫ μ[R] ▷ X := by
  rw [← comp_whiskerRight, MonObj.mul_assoc_flip, comp_whiskerRight,
    comp_whiskerRight]

/-- **The unit inverts the shuffle**: filling the second algebra
slot with the unit turns the shuffle into a reassociation. -/
theorem whiskerLeft_one_freeModShuffle
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R] (V : D) (W : D) :
    (R ⊗ V) ◁ ((λ_ W).inv ≫ η[R] ▷ W) ≫ freeModShuffle R V W =
      (α_ R V W).hom := by
  rw [freeModShuffle, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, reassoc_of% whiskerLeft_one_tensorμ,
    ← comp_whiskerRight, MonObj.mul_one]
  exact whiskerLeft_leftUnitor_inv_tensorμ R V W

end Shuffle

/-! ## The balance and equivariance of the shuffle -/

section Balance

variable {D : Type u}

/-- **The braided right action on a free module is the slide
followed by multiplication**: the generator is carried out of the
way and the two algebra factors multiply. -/
theorem braiding_free_mul
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R] [IsCommMonObj R] (V : D) :
    (β_ (R ⊗ V) R).hom ≫ (α_ R R V).inv ≫ μ[R] ▷ V =
      freeModSlide R V ≫ μ[R] ▷ V := by
  rw [BraidedCategory.braiding_tensor_left_hom, freeModSlide]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight, IsCommMonObj.mul_comm]

/-- **The shuffle is balanced**, in raw form: the two legs of the
relative tensor product of the free modules agree after it. -/
theorem freeModShuffle_condition_raw
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R] [IsCommMonObj R] (V : D) (W : D) :
    (((β_ (R ⊗ V) R).hom ≫ (α_ R R V).inv ≫ μ[R] ▷ V) ▷
        (R ⊗ W)) ≫ freeModShuffle R V W =
      ((α_ (R ⊗ V) R (R ⊗ W)).hom ≫
          (R ⊗ V) ◁ ((α_ R R W).inv ≫ μ[R] ▷ W)) ≫
        freeModShuffle R V W := by
  rw [braiding_free_mul, freeModShuffle]
  simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp,
    Category.assoc]
  rw [reassoc_of% whiskerRight_mul_tensorμ,
    reassoc_of% whiskerLeft_mul_tensorμ, whiskerRight_mul_assoc,
    reassoc_of% freeModSlide_tensorμ]

/-- **The shuffle is equivariant**, in raw form: acting on the
leading scalar and shuffling agrees with shuffling and acting. -/
theorem freeModShuffle_act_raw
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R] (V : D) (W : D) :
    (α_ R (R ⊗ V) (R ⊗ W)).inv ≫
        ((α_ R R V).inv ≫ μ[R] ▷ V) ▷ (R ⊗ W) ≫
          freeModShuffle R V W =
      R ◁ freeModShuffle R V W ≫
        ((α_ R R (V ⊗ W)).inv ≫ μ[R] ▷ (V ⊗ W)) := by
  rw [freeModShuffle]
  simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp,
    Category.assoc]
  rw [reassoc_of% whiskerRight_mul_tensorμ,
    associator_inv_naturality_middle_assoc R (μ[R]) (V ⊗ W),
    whiskerRight_mul_assoc, reassoc_of% tensorμ_whiskerLeft_shuffle]

/-- The shuffle absorbs the reassociation of the first leg. -/
theorem freeModShuffle_associator_inv
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R] [IsCommMonObj R] (V : D) (W : D) :
    (α_ (R ⊗ V) R W).inv ≫
        ((β_ (R ⊗ V) R).hom ≫ (α_ R R V).inv ≫ μ[R] ▷ V) ▷ W =
      freeModShuffle R V W ≫ (α_ R V W).inv := by
  rw [braiding_free_mul, freeModShuffle, comp_whiskerRight,
    ← Category.assoc, freeModSlide_whiskerRight]
  simp only [Category.assoc]
  rw [associator_inv_naturality_left]

/-- **Inserting the unit is a section of the first leg**: the
shuffle followed by the insertion is the insertion followed by the
first leg. -/
theorem freeModShuffle_unit_legM
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R] [IsCommMonObj R] (V : D) (W : D) :
    freeModShuffle R V W ≫ (α_ R V W).inv ≫
        (R ⊗ V) ◁ ((λ_ W).inv ≫ η[R] ▷ W) =
      ((α_ (R ⊗ V) R W).inv ≫
          ((R ⊗ V) ⊗ R) ◁ ((λ_ W).inv ≫ η[R] ▷ W)) ≫
        (((β_ (R ⊗ V) R).hom ≫ (α_ R R V).inv ≫ μ[R] ▷ V) ▷
          (R ⊗ W)) := by
  rw [Category.assoc,
    whisker_exchange ((β_ (R ⊗ V) R).hom ≫ (α_ R R V).inv ≫
      μ[R] ▷ V) ((λ_ W).inv ≫ η[R] ▷ W),
    reassoc_of% freeModShuffle_associator_inv]

/-- **Inserting the unit is a retraction of the second leg**. -/
theorem freeModUnit_legN
    [Category.{v} D] [MonoidalCategory D] (R : D) [MonObj R] (V : D) (W : D) :
    ((α_ (R ⊗ V) R W).inv ≫
        ((R ⊗ V) ⊗ R) ◁ ((λ_ W).inv ≫ η[R] ▷ W)) ≫
      ((α_ (R ⊗ V) R (R ⊗ W)).hom ≫
        (R ⊗ V) ◁ ((α_ R R W).inv ≫ μ[R] ▷ W)) =
      𝟙 ((R ⊗ V) ⊗ (R ⊗ W)) := by
  rw [Category.assoc,
    ← Category.assoc (((R ⊗ V) ⊗ R) ◁ ((λ_ W).inv ≫ η[R] ▷ W)),
    associator_naturality_right, Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, whiskerLeft_one_mul R W,
    MonoidalCategory.whiskerLeft_id, Category.comp_id,
    Iso.inv_hom_id]

end Balance

/-! ## The isomorphism -/

section Iso

variable {D : Type u}

/-- **The shuffle is balanced**: it coequalizes the two legs of the
relative tensor product of the two free modules. -/
theorem freeModShuffle_condition
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R] [IsCommMonObj R] (V : D) (W : D) :
    modTensorLegM R (freeMod R V) (freeMod R W) ≫
        freeModShuffle R V W =
      modTensorLegN R (freeMod R V) (freeMod R W) ≫
        freeModShuffle R V W :=
  freeModShuffle_condition_raw R V W

/-- **The relative tensor of two free modules is free**, at the
level of underlying objects: the shuffle descends to an
isomorphism, inverted by filling the second algebra slot with the
unit. -/
noncomputable def freeModTensorCarrier
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D] (R : D) [MonObj R] [IsCommMonObj R] (V : D) (W : D) :
    modTensor R (freeMod R V) (freeMod R W) ≅ R ⊗ (V ⊗ W) where
  hom := modTensorDesc R (freeMod R V) (freeMod R W)
    (freeModShuffle R V W) (freeModShuffle_condition R V W)
  inv := ((α_ R V W).inv ≫
      (R ⊗ V) ◁ ((λ_ W).inv ≫ η[R] ▷ W)) ≫
    modTensorπ R (freeMod R V) (freeMod R W)
  hom_inv_id := by
    apply modTensor_hom_ext
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker (modTensorπ_desc R (freeMod R V)
      (freeMod R W) (freeModShuffle R V W)
      (freeModShuffle_condition R V W)) _) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker (freeModShuffle_unit_legM R V W) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (modTensor_condition R
      (freeMod R V) (freeMod R W))) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker (freeModUnit_legN R V W) _) ?_
    exact Eq.trans (Category.id_comp _) (Category.comp_id _).symm
  inv_hom_id := by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (modTensorπ_desc R (freeMod R V)
      (freeMod R W) (freeModShuffle R V W)
      (freeModShuffle_condition R V W))) ?_
    show ((α_ R V W).inv ≫
        (R ⊗ V) ◁ ((λ_ W).inv ≫ η[R] ▷ W)) ≫
      freeModShuffle R V W = 𝟙 (R ⊗ (V ⊗ W))
    rw [Category.assoc, whiskerLeft_one_freeModShuffle,
      Iso.inv_hom_id]

/-- The descended shuffle is `R`-linear. -/
theorem freeModTensorCarrier_linear
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (R : D) [MonObj R] [IsCommMonObj R] (V : D) (W : D) :
    modTensorAct R (freeMod R V) (freeMod R W) ≫
        (freeModTensorCarrier R V W).hom =
      R ◁ (freeModTensorCarrier R V W).hom ≫
        ((α_ R R (V ⊗ W)).inv ≫ μ[R] ▷ (V ⊗ W)) :=
  modTensorDescAct_desc R (freeMod R V) (freeMod R W) R
    (actLeft R (freeMod R V).X)
    (actLeft_actRight R (freeMod R V).X)
    (freeModShuffle R V W) (freeModShuffle_condition R V W)
    ((α_ R R (V ⊗ W)).inv ≫ μ[R] ▷ (V ⊗ W))
    (freeModShuffle_act_raw R V W)

/-- **The relative tensor of two free modules is the free module on
the tensor product.** -/
noncomputable def freeModTensorIso
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (R : D) [MonObj R] [IsCommMonObj R] (V : D) (W : D) :
    modTensorMod R (freeMod R V) (freeMod R W) ≅
      freeMod R (V ⊗ W) where
  hom := Mod.Hom.mk' (freeModTensorCarrier R V W).hom (by
    show modTensorAct R (freeMod R V) (freeMod R W) ≫
        (freeModTensorCarrier R V W).hom =
      (R ◁ (freeModTensorCarrier R V W).hom) ≫
        ((α_ R R (V ⊗ W)).inv ≫ μ[R] ▷ (V ⊗ W))
    exact freeModTensorCarrier_linear R V W)
  inv := Mod.Hom.mk' (freeModTensorCarrier R V W).inv (by
    show ((α_ R R (V ⊗ W)).inv ≫ μ[R] ▷ (V ⊗ W)) ≫
        (freeModTensorCarrier R V W).inv =
      (R ◁ (freeModTensorCarrier R V W).inv) ≫
        modTensorAct R (freeMod R V) (freeMod R W)
    exact act_inv_of_act_hom R (freeModTensorCarrier R V W)
      (freeModTensorCarrier_linear R V W))
  hom_inv_id := by
    apply Mod.Hom.ext
    exact (freeModTensorCarrier R V W).hom_inv_id
  inv_hom_id := by
    apply Mod.Hom.ext
    exact (freeModTensorCarrier R V W).inv_hom_id

/-- **The isomorphism computes the projection as the shuffle.** -/
theorem modTensorπ_freeModTensorIso
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (R : D) [MonObj R] [IsCommMonObj R] (V : D) (W : D) :
    modTensorπ R (freeMod R V) (freeMod R W) ≫
        (freeModTensorIso R V W).hom.hom = freeModShuffle R V W :=
  modTensorπ_desc R (freeMod R V) (freeMod R W)
    (freeModShuffle R V W) (freeModShuffle_condition R V W)

/-- **The isomorphism computes the pairing as the shuffle**: the
pairing `RS.gpair` of two morphisms into free modules is, after the
identification with the free module on the tensor product, the
tensor of the two morphisms followed by the shuffle. -/
theorem freeModTensorIso_gpair
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (R : D) [MonObj R] [IsCommMonObj R] (V : D) (W : D)
    {X Y : D} (m : X ⟶ R ⊗ V)
    (n : Y ⟶ R ⊗ W) :
    gpair (M := freeMod R V) (N := freeMod R W) m n ≫
        (freeModTensorIso R V W).hom.hom =
      (m ⊗ₘ n) ≫ freeModShuffle R V W := by
  rw [gpair_def, Category.assoc]
  exact whisker_eq _ (modTensorπ_freeModTensorIso R V W)

end Iso

end RS
