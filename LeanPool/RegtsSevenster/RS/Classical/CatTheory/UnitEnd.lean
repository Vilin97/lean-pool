/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# The scalars of a monoidal category commute

The endomorphisms of the tensor unit form a commutative monoid.  The
tensor product is a second unital multiplication on `End (𝟙_ C)`,
and the interchange law makes it compatible with composition, so the
Eckmann–Hilton argument applies: conjugating by the unitor writes an
endomorphism of the unit either as a right whiskering or as a left
whiskering, and whiskerings on opposite sides commute.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory

universe v u

variable {C : Type u}

/-- The two unitors of the tensor unit agree. -/
private theorem unitor_iso_eq
    [Category.{v} C] [MonoidalCategory C] : (λ_ (𝟙_ C)) = (ρ_ (𝟙_ C)) :=
  Iso.ext unitors_equal

/-- Conjugating by the right unitor recovers an endomorphism of the
unit from its right whiskering. -/
@[reassoc]
private theorem whiskerRight_unit [Category.{v} C] [MonoidalCategory C]
    (f : 𝟙_ C ⟶ 𝟙_ C) :
    (ρ_ (𝟙_ C)).inv ≫ (f ▷ 𝟙_ C) ≫ (ρ_ (𝟙_ C)).hom = f := by
  rw [rightUnitor_naturality, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

/-- Conjugating by the right unitor recovers an endomorphism of the
unit from its left whiskering. -/
@[reassoc]
private theorem whiskerLeft_unit [Category.{v} C] [MonoidalCategory C]
    (g : 𝟙_ C ⟶ 𝟙_ C) :
    (ρ_ (𝟙_ C)).inv ≫ (𝟙_ C ◁ g) ≫ (ρ_ (𝟙_ C)).hom = g := by
  rw [← unitor_iso_eq, leftUnitor_naturality, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- **Endomorphisms of the tensor unit commute.** -/
theorem unit_comp_comm [Category.{v} C] [MonoidalCategory C]
    (f g : 𝟙_ C ⟶ 𝟙_ C) : f ≫ g = g ≫ f := by
  have h1 : (ρ_ (𝟙_ C)).inv ≫ (f ▷ 𝟙_ C) ≫ (𝟙_ C ◁ g) ≫
      (ρ_ (𝟙_ C)).hom = f ≫ g := by
    rw [← unitor_iso_eq, leftUnitor_naturality, unitor_iso_eq,
      whiskerRight_unit_assoc]
  have h2 : (ρ_ (𝟙_ C)).inv ≫ (𝟙_ C ◁ g) ≫ (f ▷ 𝟙_ C) ≫
      (ρ_ (𝟙_ C)).hom = g ≫ f := by
    rw [rightUnitor_naturality, whiskerLeft_unit_assoc]
  rw [← h1, ← h2, ← whisker_exchange_assoc]

/-- The scalars form a commutative monoid. -/
instance endUnitCommMonoid
    [Category.{v} C] [MonoidalCategory C] : CommMonoid (End (𝟙_ C)) :=
  { (inferInstance : Monoid (End (𝟙_ C))) with
    mul_comm := fun f g => unit_comp_comm g f }

/-- The unit braids trivially with itself. -/
theorem braiding_unit_self [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] :
    (β_ (𝟙_ C) (𝟙_ C)).hom = 𝟙 (𝟙_ C ⊗ 𝟙_ C) := by
  have h := braiding_leftUnitor (C := C) (𝟙_ C)
  rw [unitors_equal] at h
  refine (cancel_mono (ρ_ (𝟙_ C)).hom).mp ?_
  rw [h, Category.id_comp]

end RS
