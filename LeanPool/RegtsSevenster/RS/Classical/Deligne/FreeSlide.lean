/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreePow

/-!
# Sliding a head along a word of free letters

The head of a free letter splits off as a trailing scalar and
slides into the next letter.  Splitting and acting back on the
same letter is the identity, so the slot relation of the module
power says exactly that the slide is invisible after the
projection.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **Splitting the head off a free letter**: the head becomes a
trailing scalar and the letter keeps the unit. -/
noncomputable def freeSplit
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (V : D) : (A ⊗ V) ⟶ (A ⊗ V) ⊗ A :=
  (β_ A V).hom ≫ (((λ_ V).inv ≫ (η[A] ▷ V)) ▷ A)

/-- **Splitting and acting back is the identity**: the scalar
returns to the head it came from. -/
theorem freeSplit_actRight
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (V : D) :
    letI := freeModObj A V
    freeSplit A V ≫ actRight A (A ⊗ V) = 𝟙 (A ⊗ V) := by
  let := freeModObj A V
  change freeSplit A V ≫ (β_ (A ⊗ V) A).hom ≫
    ((α_ A A V).inv ≫ (μ[A] ▷ V)) = 𝟙 (A ⊗ V)
  rw [freeSplit, Category.assoc,
    BraidedCategory.braiding_naturality_left_assoc,
    ← Category.assoc ((β_ A V).hom), SymmetricCategory.symmetry,
    Category.id_comp, MonoidalCategory.whiskerLeft_comp,
    Category.assoc,
    associator_inv_naturality_middle_assoc,
    ← MonoidalCategory.comp_whiskerRight, MonObj.mul_one]
  monoidal

/-- **The slide window**: split the head off the first letter and
act with it on the second. -/
noncomputable def freeSlideWin
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (V : D) :
    (A ⊗ V) ⊗ (A ⊗ V) ⟶ (A ⊗ V) ⊗ (A ⊗ V) :=
  letI := freeModObj A V
  (freeSplit A V ▷ (A ⊗ V)) ≫ winLegN A (A ⊗ V)

/-- Splitting and acting back through the first slot leg is the
identity of the window. -/
theorem freeSplit_winLegM
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (V : D) :
    letI := freeModObj A V
    (freeSplit A V ▷ (A ⊗ V)) ≫ winLegM A (A ⊗ V) =
      𝟙 ((A ⊗ V) ⊗ (A ⊗ V)) := by
  let := freeModObj A V
  rw [winLegM, ← MonoidalCategory.comp_whiskerRight,
    freeSplit_actRight, MonoidalCategory.id_whiskerRight]

/-- **The slide is invisible in the module power**: it is the
difference of the two slot legs at a window whose first leg is the
identity. -/
theorem freeSlideWin_modPowπ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (V : D) [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    {n : ℕ} (a b : ℕ)
    (hab : a + 2 + b = n) :
    letI := freeModObj A V
    ((tensorPow D (A ⊗ V) a ◁ freeSlideWin A V) ▷
        tensorPow D (A ⊗ V) b) ≫
        modPowGlue (A ⊗ V) a b ≫ powCast (A ⊗ V) hab ≫
        modPowπ A (A ⊗ V) n =
      modPowGlue (A ⊗ V) a b ≫ powCast (A ⊗ V) hab ≫
        modPowπ A (A ⊗ V) n := by
  let := freeModObj A V
  have hsplitN : ((tensorPow D (A ⊗ V) a ◁ freeSlideWin A V) ▷
      tensorPow D (A ⊗ V) b) ≫ modPowGlue (A ⊗ V) a b =
      ((tensorPow D (A ⊗ V) a ◁ (freeSplit A V ▷ (A ⊗ V))) ▷
        tensorPow D (A ⊗ V) b) ≫ modPowLegN A (A ⊗ V) a b := by
    rw [modPowLegN, freeSlideWin,
      MonoidalCategory.whiskerLeft_comp,
      MonoidalCategory.comp_whiskerRight, Category.assoc]
  have hsplitM : ((tensorPow D (A ⊗ V) a ◁
        (freeSplit A V ▷ (A ⊗ V))) ▷ tensorPow D (A ⊗ V) b) ≫
      modPowLegM A (A ⊗ V) a b = modPowGlue (A ⊗ V) a b := by
    rw [modPowLegM, ← Category.assoc,
      ← MonoidalCategory.comp_whiskerRight,
      ← MonoidalCategory.whiskerLeft_comp, freeSplit_winLegM,
      MonoidalCategory.whiskerLeft_id,
      MonoidalCategory.id_whiskerRight, Category.id_comp]
  rw [← Category.assoc, hsplitN, Category.assoc,
    ← modPow_rel A (A ⊗ V) a b hab, ← Category.assoc, hsplitM]

/-- **The top slide**: slide the head of the penultimate letter
into the last one. -/
noncomputable def freeSlideTop
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (V : D)
    (k : ℕ) :
    tensorPow D (A ⊗ V) (k + 2) ⟶ tensorPow D (A ⊗ V) (k + 2) :=
  letI := freeModObj A V
  (α_ (tensorPow D (A ⊗ V) k) (A ⊗ V) (A ⊗ V)).hom ≫
    (tensorPow D (A ⊗ V) k ◁ freeSlideWin A V) ≫
    (α_ (tensorPow D (A ⊗ V) k) (A ⊗ V) (A ⊗ V)).inv

/-- **The top slide is invisible in the module power.** -/
theorem freeSlideTop_modPowπ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (V : D) [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (k : ℕ) :
    letI := freeModObj A V
    freeSlideTop A V k ≫ modPowπ A (A ⊗ V) (k + 2) =
      modPowπ A (A ⊗ V) (k + 2) := by
  let := freeModObj A V
  have hnat : ∀ {P Q Z : D} (f : P ⟶ Q) (m : Q ⟶ Z),
      (f ▷ tensorPow D (A ⊗ V) 0) ≫ (ρ_ Q).hom ≫ m =
        (ρ_ P).hom ≫ f ≫ m := by
    intro P Q Z f m
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker (rightUnitor_naturality f) m) ?_
    exact Category.assoc _ _ _
  have hrel :=
    freeSlideWin_modPowπ A V k 0 (rfl : k + 2 + 0 = k + 2)
  rw [modPowGlue, tensorPowConcat_zero, powCast_rfl,
    Category.id_comp] at hrel
  repeat' erw [Category.assoc] at hrel
  rw [← MonoidalCategory.comp_whiskerRight_assoc] at hrel
  have hA : ((tensorPow D (A ⊗ V) k ◁ freeSlideWin A V) ≫
      (α_ (tensorPow D (A ⊗ V) k) (A ⊗ V) (A ⊗ V)).inv) ≫
      modPowπ A (A ⊗ V) (k + 2) =
      (α_ (tensorPow D (A ⊗ V) k) (A ⊗ V) (A ⊗ V)).inv ≫
      modPowπ A (A ⊗ V) (k + 2) := by
    refine (cancel_epi (ρ_ (tensorPow D (A ⊗ V) k ⊗
      (A ⊗ V) ⊗ (A ⊗ V))).hom).mp ?_
    exact Eq.trans (hnat _ _).symm (Eq.trans hrel (hnat _ _))
  erw [freeSlideTop, Category.assoc]
  exact (whisker_eq _ hA).trans (Iso.hom_inv_id_assoc _ _)

end RS
