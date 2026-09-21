/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreeModShuffleCoh
import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreePow

/-!
# The free collapse descends to the module power

The collapse `freeCollapse A V n : (A ⊗ V) ^ ⊗ n ⟶ A ⊗ V ^ ⊗ n` of
`FreePow.lean` multiplies all the heads of a word of free letters
into a single head at the front.  Here it is shown to coequalise
the slot relations that present the module power of the free module
`A ⊗ V`, so that it descends to `freeCollapseDesc`.

The engine is head absorption `freeModShuffle A P V` viewed as the
laxity of the functor `V ↦ A ⊗ V`: it is natural, associative and
unital (`freeModShuffle_natural_left`,
`freeModShuffle_assoc_inv`, `freeModShuffle_unit`), and the collapse
is its iterate.  Generalised associativity of a laxity is
`freeCollapse_concat`, the compatibility of the collapse with
concatenation of words.

Given that, a slot relation is local: whiskering the ambient letters
away, both legs reduce to the two-letter window
`((A ⊗ V) ⊗ A) ⊗ (A ⊗ V) ⟶ A ⊗ (V ⊗ V)`, on which the left leg
multiplies the extra scalar into the first head and the right leg
into the second.  The two differ by a single crossing of the two
heads that are multiplied first — a braid identity of the ambient
symmetric structure, `freeWindow_braid` — which commutativity of `A`
absorbs.

Throughout, the module structure on `A ⊗ V` is `freeModObj A V`; the
carrier is spelt `(freeMod A V).X` so that instance synthesis finds
it.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## The laws of head absorption -/

section CollectLaws

/-- Naturality of head absorption in the accumulated block. -/
@[reassoc]
theorem freeModShuffle_natural_left
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A]
    {P P' : D} (f : P ⟶ P') (V : D) :
    ((A ◁ f) ▷ (A ⊗ V)) ≫ freeModShuffle A P' V =
      freeModShuffle A P V ≫ (A ◁ (f ▷ V)) := by
  rw [freeModShuffle, freeModShuffle,
    ← MonoidalCategory.id_tensorHom A f,
    tensorμ_natural_left_assoc, MonoidalCategory.id_whiskerRight,
    MonoidalCategory.id_tensorHom, whisker_exchange,
    Category.assoc]

/-- **Associativity of head absorption**, in inverse-associator
form: the mirror of `RS.freeModShuffle_assoc`. -/
@[reassoc]
theorem freeModShuffle_assoc_inv
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A]
    (P Q R : D) :
    (α_ (A ⊗ P) (A ⊗ Q) (A ⊗ R)).inv ≫
        (freeModShuffle A P Q ▷ (A ⊗ R)) ≫
        freeModShuffle A (P ⊗ Q) R =
      ((A ⊗ P) ◁ freeModShuffle A Q R) ≫ freeModShuffle A P (Q ⊗ R) ≫
        (A ◁ (α_ P Q R).inv) := by
  rw [← cancel_epi (α_ (A ⊗ P) (A ⊗ Q) (A ⊗ R)).hom,
    Iso.hom_inv_id_assoc,
    ← cancel_mono (A ◁ (α_ P Q R).hom)]
  simp only [Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.comp_id]
  exact freeModShuffle_assoc A P Q R

/-- **Unitality of head absorption.** -/
theorem freeModShuffle_unit
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A]
    (P : D) :
    ((A ⊗ P) ◁ ((λ_ (𝟙_ D)).inv ≫ (η[A] ▷ 𝟙_ D))) ≫
        freeModShuffle A P (𝟙_ D) ≫ (A ◁ (ρ_ P).hom) =
      (ρ_ (A ⊗ P)).hom := by
  have hunit : ((A ⊗ P) ◁ (η[A] ▷ 𝟙_ D)) ≫ freeModShuffle A P (𝟙_ D) ≫
      (A ◁ (ρ_ P).hom) =
        tensorμ A P (𝟙_ D) (𝟙_ D) ≫ ((ρ_ A).hom ⊗ₘ (ρ_ P).hom) := by
    have hmul : ((A ◁ η[A]) ▷ (P ⊗ 𝟙_ D)) ≫ (μ[A] ▷ (P ⊗ 𝟙_ D)) =
        (ρ_ A).hom ▷ (P ⊗ 𝟙_ D) := by
      rw [← MonoidalCategory.comp_whiskerRight, MonObj.mul_one]
    rw [freeModShuffle, ← MonoidalCategory.tensorHom_id η[A] (𝟙_ D)]
    simp only [Category.assoc]
    rw [tensorμ_natural_right_assoc, MonoidalCategory.whiskerLeft_id,
      MonoidalCategory.tensorHom_id, reassoc_of% hmul,
      ← MonoidalCategory.tensorHom_def]
  rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, hunit]
  exact (tensor_right_unitality A P).symm

end CollectLaws

/-! ## The collapse of a concatenation -/

section Concat

/-- The collapse of a concatenation, stated through head
absorption. -/
private theorem freeCollapse_concat_collect
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (V : D)
    (a : ℕ) : ∀ b : ℕ,
    (tensorPowConcat (A ⊗ V) a b).hom ≫ freeCollapse A V (a + b) =
      (freeCollapse A V a ⊗ₘ freeCollapse A V b) ≫
        freeModShuffle A (tensorPow D V a) (tensorPow D V b) ≫
        (A ◁ (tensorPowConcat V a b).hom)
  | 0 => by
      show (ρ_ (tensorPow D (A ⊗ V) a)).hom ≫ freeCollapse A V a =
        (freeCollapse A V a ⊗ₘ
            ((λ_ (𝟙_ D)).inv ≫ (η[A] ▷ 𝟙_ D))) ≫
          freeModShuffle A (tensorPow D V a) (𝟙_ D) ≫
          (A ◁ (ρ_ (tensorPow D V a)).hom)
      rw [MonoidalCategory.tensorHom_def, Category.assoc,
        freeModShuffle_unit, MonoidalCategory.rightUnitor_naturality]
  | b + 1 => by
      have ih := freeCollapse_concat_collect A V a b
      have hnat : (α_ (tensorPow D (A ⊗ V) a)
            (tensorPow D (A ⊗ V) b) (A ⊗ V)).inv ≫
          ((freeCollapse A V a ⊗ₘ freeCollapse A V b) ▷ (A ⊗ V)) =
            (freeCollapse A V a ⊗ₘ
                (freeCollapse A V b ▷ (A ⊗ V))) ≫
              (α_ (A ⊗ tensorPow D V a) (A ⊗ tensorPow D V b)
                (A ⊗ V)).inv := by
        rw [← MonoidalCategory.tensorHom_id
            (freeCollapse A V b) (A ⊗ V),
          ← MonoidalCategory.tensorHom_id
            (freeCollapse A V a ⊗ₘ freeCollapse A V b) (A ⊗ V),
          associator_inv_naturality]
      have hsplit : (freeCollapse A V a ⊗ₘ
            ((freeCollapse A V b ▷ (A ⊗ V)) ≫
              freeModShuffle A (tensorPow D V b) V)) =
          (freeCollapse A V a ⊗ₘ
              (freeCollapse A V b ▷ (A ⊗ V))) ≫
            ((A ⊗ tensorPow D V a) ◁
              freeModShuffle A (tensorPow D V b) V) := by
        rw [← MonoidalCategory.id_tensorHom, tensorHom_comp_tensorHom,
          Category.comp_id]
      show ((α_ (tensorPow D (A ⊗ V) a)
            (tensorPow D (A ⊗ V) b) (A ⊗ V)).inv ≫
          ((tensorPowConcat (A ⊗ V) a b).hom ▷ (A ⊗ V))) ≫
          ((freeCollapse A V (a + b) ▷ (A ⊗ V)) ≫
            freeModShuffle A (tensorPow D V (a + b)) V) =
        (freeCollapse A V a ⊗ₘ
            ((freeCollapse A V b ▷ (A ⊗ V)) ≫
              freeModShuffle A (tensorPow D V b) V)) ≫
          freeModShuffle A (tensorPow D V a) (tensorPow D V b ⊗ V) ≫
          (A ◁ ((α_ (tensorPow D V a) (tensorPow D V b) V).inv ≫
            ((tensorPowConcat V a b).hom ▷ V)))
      rw [hsplit, MonoidalCategory.whiskerLeft_comp]
      simp only [Category.assoc]
      rw [← MonoidalCategory.comp_whiskerRight_assoc, ih]
      simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
      rw [freeModShuffle_natural_left, ← Category.assoc,
        ← Category.assoc, hnat]
      simp only [Category.assoc]
      rw [freeModShuffle_assoc_inv_assoc]

/-- **The collapse of a concatenation**: collapsing a
concatenated word is collapsing each part and multiplying the two
heads. -/
theorem freeCollapse_concat
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (A : D) [MonObj A] [IsCommMonObj A]
    (V : D) (a b : ℕ) :
    (tensorPowConcat (A ⊗ V) a b).hom ≫ freeCollapse A V (a + b) =
      (freeCollapse A V a ⊗ₘ freeCollapse A V b) ≫
        tensorμ A (tensorPow D V a) A (tensorPow D V b) ≫
        (μ[A] ▷ (tensorPow D V a ⊗ tensorPow D V b)) ≫
        (A ◁ (tensorPowConcat V a b).hom) := by
  refine Eq.trans (freeCollapse_concat_collect A V a b) ?_
  rw [freeModShuffle]
  simp only [Category.assoc]

end Concat

/-! ## The window of a relation slot -/

section Window

/-- The braid identity behind the window: the two legs differ by a
single crossing of the two heads that are multiplied first. -/
private theorem freeWindow_braid
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (A V : D) :
    ((β_ (A ⊗ V) A).hom ▷ (A ⊗ V)) ≫
        ((α_ A A V).inv ▷ (A ⊗ V)) ≫ tensorμ (A ⊗ A) V A V =
      ((α_ (A ⊗ V) A (A ⊗ V)).hom ≫
        ((A ⊗ V) ◁ (α_ A A V).inv) ≫ tensorμ A V (A ⊗ A) V ≫
        ((α_ A A A).inv ▷ (V ⊗ V))) ≫
        (((β_ A A).hom ▷ A) ▷ (V ⊗ V)) := by
  calc ((β_ (A ⊗ V) A).hom ▷ (A ⊗ V)) ≫
        ((α_ A A V).inv ▷ (A ⊗ V)) ≫ tensorμ (A ⊗ A) V A V
      = 𝟙 _ ⊗≫ (A ◁ ((β_ V A).hom ▷ (A ⊗ V))) ⊗≫
          (((β_ A A).hom ▷ ((V ⊗ A) ⊗ V)) ≫
            ((A ⊗ A) ◁ ((β_ V A).hom ▷ V))) ⊗≫ 𝟙 _ := by
        dsimp only [tensorμ]
        rw [BraidedCategory.braiding_tensor_left_hom]
        monoidal
    _ = 𝟙 _ ⊗≫ (A ◁ ((β_ V A).hom ▷ (A ⊗ V))) ⊗≫
          (((A ⊗ A) ◁ ((β_ V A).hom ▷ V)) ≫
            ((β_ A A).hom ▷ ((A ⊗ V) ⊗ V))) ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]
    _ = _ := by
        dsimp only [tensorμ]
        rw [BraidedCategory.braiding_tensor_right_hom]
        monoidal

/-- The first slot leg on a window of free letters, resolved into a
braid and the product of the three heads. -/
private theorem freeWindow_legM
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (A : D) [MonObj A] (V : D) :
    winLegM A (freeMod A V).X ≫ freeModShuffle A V V =
      (((β_ (A ⊗ V) A).hom ▷ (A ⊗ V)) ≫
        ((α_ A A V).inv ▷ (A ⊗ V)) ≫ tensorμ (A ⊗ A) V A V) ≫
        (((μ[A] ▷ A) ≫ μ[A]) ▷ (V ⊗ V)) := by
  have hleft : ((μ[A] ▷ V) ▷ (A ⊗ V)) ≫ tensorμ A V A V =
      tensorμ (A ⊗ A) V A V ≫ ((μ[A] ▷ A) ▷ (V ⊗ V)) := by
    rw [← MonoidalCategory.tensorHom_id μ[A] V, tensorμ_natural_left,
      MonoidalCategory.id_whiskerRight, MonoidalCategory.tensorHom_id]
  show (((β_ (A ⊗ V) A).hom ≫ (α_ A A V).inv ≫ (μ[A] ▷ V)) ▷
      (A ⊗ V)) ≫ (tensorμ A V A V ≫ (μ[A] ▷ (V ⊗ V))) = _
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [reassoc_of% hleft]

/-- The second slot leg on a window of free letters, resolved into a
reassociation and the product of the three heads. -/
private theorem freeWindow_legN
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (A : D) [MonObj A] (V : D) :
    winLegN A (freeMod A V).X ≫ freeModShuffle A V V =
      ((α_ (A ⊗ V) A (A ⊗ V)).hom ≫
        ((A ⊗ V) ◁ (α_ A A V).inv) ≫ tensorμ A V (A ⊗ A) V) ≫
        (((A ◁ μ[A]) ≫ μ[A]) ▷ (V ⊗ V)) := by
  have hright : ((A ⊗ V) ◁ (μ[A] ▷ V)) ≫ tensorμ A V A V =
      tensorμ A V (A ⊗ A) V ≫ ((A ◁ μ[A]) ▷ (V ⊗ V)) := by
    rw [← MonoidalCategory.tensorHom_id μ[A] V, tensorμ_natural_right,
      MonoidalCategory.whiskerLeft_id, MonoidalCategory.tensorHom_id]
  show ((α_ (A ⊗ V) A (A ⊗ V)).hom ≫
      ((A ⊗ V) ◁ ((α_ A A V).inv ≫ (μ[A] ▷ V)))) ≫
      (tensorμ A V A V ≫ (μ[A] ▷ (V ⊗ V))) = _
  simp only [MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [reassoc_of% hright]

/-- **The window identity**: a scalar absorbed on either side of an
adjacent pair of free letters ends in the same head. -/
private theorem freeWindow
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (A : D) [MonObj A] [IsCommMonObj A]
    (V : D) :
    winLegM A (freeMod A V).X ≫ freeModShuffle A V V =
      winLegN A (freeMod A V).X ≫ freeModShuffle A V V := by
  have hw : (α_ A A A).inv ≫ (μ[A] ▷ A) ≫ μ[A] =
      (A ◁ μ[A]) ≫ μ[A] := by
    rw [MonObj.mul_assoc, Iso.inv_hom_id_assoc]
  have hc : (((β_ A A).hom ▷ A) ▷ (V ⊗ V)) ≫
      ((μ[A] ▷ A) ▷ (V ⊗ V)) ≫ (μ[A] ▷ (V ⊗ V)) =
        ((μ[A] ▷ A) ▷ (V ⊗ V)) ≫ (μ[A] ▷ (V ⊗ V)) := by
    simp only [← MonoidalCategory.comp_whiskerRight]
    rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
      IsCommMonObj.mul_comm]
  rw [freeWindow_legM, freeWindow_legN, freeWindow_braid, ← hw]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [hc]

end Window

/-! ## The descended collapse -/

section Descent

/-- A slot window inside a word, collapsed: only the composite of
the window with one head absorption survives. -/
private theorem freeLeg_window
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (A : D) [MonObj A] (V : D) (a b : ℕ)
    (L : ((A ⊗ V) ⊗ A) ⊗ (A ⊗ V) ⟶ (A ⊗ V) ⊗ (A ⊗ V)) :
    ((tensorPow D (A ⊗ V) a ◁ L) ▷ tensorPow D (A ⊗ V) b) ≫
        modPowGlue (A ⊗ V) a b ≫ freeCollapse A V (a + 2 + b) =
      (((freeCollapse A V a ▷ (((A ⊗ V) ⊗ A) ⊗ (A ⊗ V))) ≫
          ((A ⊗ tensorPow D V a) ◁ (L ≫ freeModShuffle A V V)) ≫
          freeModShuffle A (tensorPow D V a) (V ⊗ V) ≫
          (A ◁ (α_ (tensorPow D V a) V V).inv)) ▷
        tensorPow D (A ⊗ V) b) ≫
        ((A ⊗ tensorPow D V (a + 2)) ◁ freeCollapse A V b) ≫
        freeModShuffle A (tensorPow D V (a + 2)) (tensorPow D V b) ≫
        (A ◁ (tensorPowConcat V (a + 2) b).hom) := by
  have hA : (tensorPow D (A ⊗ V) a ◁ L) ≫
      (α_ (tensorPow D (A ⊗ V) a) (A ⊗ V) (A ⊗ V)).inv ≫
      freeCollapse A V (a + 2) =
        (freeCollapse A V a ▷ (((A ⊗ V) ⊗ A) ⊗ (A ⊗ V))) ≫
          ((A ⊗ tensorPow D V a) ◁ (L ≫ freeModShuffle A V V)) ≫
          freeModShuffle A (tensorPow D V a) (V ⊗ V) ≫
          (A ◁ (α_ (tensorPow D V a) V V).inv) := by
    show (tensorPow D (A ⊗ V) a ◁ L) ≫
        (α_ (tensorPow D (A ⊗ V) a) (A ⊗ V) (A ⊗ V)).inv ≫
        ((((freeCollapse A V a ▷ (A ⊗ V)) ≫
            freeModShuffle A (tensorPow D V a) V) ▷ (A ⊗ V)) ≫
          freeModShuffle A (tensorPow D V a ⊗ V) V) = _
    rw [MonoidalCategory.comp_whiskerRight,
      MonoidalCategory.whiskerLeft_comp]
    simp only [Category.assoc]
    rw [← MonoidalCategory.associator_inv_naturality_left_assoc,
      ← whisker_exchange_assoc, freeModShuffle_assoc_inv]
  have hglue : modPowGlue (A ⊗ V) a b ≫
      freeCollapse A V (a + 2 + b) =
        ((α_ (tensorPow D (A ⊗ V) a) (A ⊗ V) (A ⊗ V)).inv ▷
            tensorPow D (A ⊗ V) b) ≫
          ((freeCollapse A V (a + 2) ⊗ₘ freeCollapse A V b) ≫
            freeModShuffle A (tensorPow D V (a + 2))
              (tensorPow D V b) ≫
            (A ◁ (tensorPowConcat V (a + 2) b).hom)) :=
    (Category.assoc _ _ _).trans
      (whisker_eq _ (freeCollapse_concat_collect A V (a + 2) b))
  erw [hglue, MonoidalCategory.tensorHom_def]
  simp only [Category.assoc]
  erw [← MonoidalCategory.comp_whiskerRight_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc]
  erw [Category.assoc]
  erw [hA]
  rfl

/-- **The collapse coequalises the slot relations**: a scalar
absorbed on either side of a slot ends up in the same head. -/
theorem freeCollapse_leg
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (A : D) [MonObj A] [IsCommMonObj A]
    (V : D) {n : ℕ} (a b : ℕ) (hab : a + 2 + b = n) :
    modPowLegM A (freeMod A V).X a b ≫
        powCast (freeMod A V).X hab ≫ freeCollapse A V n =
      modPowLegN A (freeMod A V).X a b ≫
        powCast (freeMod A V).X hab ≫ freeCollapse A V n := by
  subst hab
  simp only [powCast_rfl, Category.id_comp, modPowLegM, modPowLegN,
    Category.assoc]
  erw [Category.id_comp]
  change ((tensorPow D (A ⊗ V) a ◁ winLegM A (freeMod A V).X) ▷
      tensorPow D (A ⊗ V) b) ≫
      modPowGlue (A ⊗ V) a b ≫ freeCollapse A V (a + 2 + b) =
    ((tensorPow D (A ⊗ V) a ◁ winLegN A (freeMod A V).X) ▷
      tensorPow D (A ⊗ V) b) ≫
      modPowGlue (A ⊗ V) a b ≫ freeCollapse A V (a + 2 + b)
  refine ((freeLeg_window A V a b
      (winLegM A (freeMod A V).X)).trans ?_).trans
    (freeLeg_window A V a b (winLegN A (freeMod A V).X)).symm
  exact congrArg
    (fun z : ((A ⊗ V) ⊗ A) ⊗ (A ⊗ V) ⟶ A ⊗ (V ⊗ V) =>
      (((freeCollapse A V a ▷ (((A ⊗ V) ⊗ A) ⊗ (A ⊗ V))) ≫
          ((A ⊗ tensorPow D V a) ◁ z) ≫
          freeModShuffle A (tensorPow D V a) (V ⊗ V) ≫
          (A ◁ (α_ (tensorPow D V a) V V).inv)) ▷
        tensorPow D (A ⊗ V) b) ≫
        ((A ⊗ tensorPow D V (a + 2)) ◁ freeCollapse A V b) ≫
        freeModShuffle A (tensorPow D V (a + 2)) (tensorPow D V b) ≫
        (A ◁ (tensorPowConcat V (a + 2) b).hom))
    (freeWindow A V)

/-- **The descended collapse.** -/
noncomputable def freeCollapseDesc
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    (A : D) [MonObj A]
    [IsCommMonObj A] (V : D) (n : ℕ) :
    modPow A (freeMod A V).X n ⟶ A ⊗ tensorPow D V n :=
  modPowDesc A (freeMod A V).X (freeCollapse A V n)
    (fun a b hab => freeCollapse_leg A V a b hab)

@[reassoc (attr := simp)]
theorem modPowπ_freeCollapseDesc
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    (A : D) [MonObj A]
    [IsCommMonObj A] (V : D) (n : ℕ) :
    modPowπ A (freeMod A V).X n ≫ freeCollapseDesc A V n =
      freeCollapse A V n :=
  modPowπ_desc A (freeMod A V).X _ _

end Descent

end RS
