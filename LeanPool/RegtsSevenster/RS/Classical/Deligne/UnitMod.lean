/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SymAlg

/-!
# Module powers over the unit monoid

Over the trivial monoid the module relations collapse: both slot
legs are the same unitor slide, the assembled relation pair is
equal, and the module power projection is an isomorphism onto the
plain tensor power.  Symmetric powers of a bare object are thereby
the general machinery instantiated at the unit, with every
multiplication law inherited — the substrate of the local
splitting algebra.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- Over the unit monoid the action is the left unitor. -/
theorem actLeft_unit [Category.{v} D] [MonoidalCategory D]
    (X : D) :
    actLeft (𝟙_ D) X = (λ_ X).hom := rfl

/-- Over the unit monoid the braided right action is the right
unitor. -/
theorem actRight_unit [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (X : D) :
    actRight (𝟙_ D) X = (ρ_ X).hom := by
  rw [actRight, actLeft_unit]
  simp

/-- Over the unit monoid the two slot legs coincide. -/
theorem winLeg_unit [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (X : D) :
    winLegM (𝟙_ D) X = winLegN (𝟙_ D) X := by
  rw [winLegM, winLegN, actRight_unit, actLeft_unit]
  exact (MonoidalCategory.triangle X X).symm

section Pow

/-- Over the unit monoid the assembled relation legs coincide. -/
theorem modPowLeg_unit [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (X : D) (n : ℕ) :
    modPowLegFst (𝟙_ D) X n = modPowLegSnd (𝟙_ D) X n := by
  rw [modPowLegFst, modPowLegSnd]
  refine biproduct.hom_ext' _ _ fun i => ?_
  simp only [biproduct.ι_desc]
  rw [modPowLegM, modPowLegN, winLeg_unit]

/-- **The module power over the unit monoid is the plain tensor
power**: the relation pair is equal, so the coequalizer collapses
onto its target. -/
noncomputable def modPowUnitIso
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    (X : D) (n : ℕ) :
    modPow (𝟙_ D) X n ≅ tensorPow D X n where
  hom := coequalizer.desc (𝟙 _)
    (by rw [modPowLeg_unit])
  inv := modPowπ (𝟙_ D) X n
  hom_inv_id := coequalizer.hom_ext
    (((Category.assoc _ _ _).symm.trans
      ((eq_whisker (coequalizer.π_desc _ _) _).trans
        (Category.id_comp _))).trans (Category.comp_id _).symm)
  inv_hom_id := coequalizer.π_desc _ _

/-- The projection onto the module power over the unit monoid is
invertible. -/
instance [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    (X : D) (n : ℕ) : IsIso (modPowπ (𝟙_ D) X n) :=
  ⟨(modPowUnitIso X n).hom, (modPowUnitIso X n).inv_hom_id,
    (modPowUnitIso X n).hom_inv_id⟩

end Pow

end RS
