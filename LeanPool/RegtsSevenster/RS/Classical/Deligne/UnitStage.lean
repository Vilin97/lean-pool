/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ScalarLinear

/-!
# Stage detection for maps out of the unit

The monoidal unit of the ind-category is the embedded unit, so
maps out of it into filtered colimits factor through stages — the
form in which the Key Lemma's colimit algebra is probed.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v

variable {C : Type v}

/-- A map from the monoidal unit of the ind-category into a
filtered colimit factors through a stage. -/
theorem exists_factor_of_unit_hom_colimit [SmallCategory C] [MonoidalCategory C]
    {I : Type v}
    [SmallCategory I] [IsFiltered I] (D : I ⥤ Ind C)
    (f : 𝟙_ (Ind C) ⟶ colimit D) :
    ∃ (i : I) (g : 𝟙_ (Ind C) ⟶ D.obj i),
      g ≫ colimit.ι D i = f := by
  obtain ⟨i, g, hg⟩ := exists_factor_of_hom_colimit D (𝟙_ C)
    ((indOfUnitIso (C := C)).inv ≫ f)
  refine ⟨i, (indOfUnitIso (C := C)).hom ≫ g, ?_⟩
  rw [Category.assoc, hg, ← Category.assoc, Iso.hom_inv_id,
    Category.id_comp]

/-- Two maps from the unit merged in a filtered colimit merge at a
stage. -/
theorem unit_factor_eq_of_hom_colimit [SmallCategory C] [MonoidalCategory C]
    {I : Type v}
    [SmallCategory I] [IsFiltered I] (D : I ⥤ Ind C) {i j : I}
    (g₁ : 𝟙_ (Ind C) ⟶ D.obj i) (g₂ : 𝟙_ (Ind C) ⟶ D.obj j)
    (h : g₁ ≫ colimit.ι D i = g₂ ≫ colimit.ι D j) :
    ∃ (k : I) (α : i ⟶ k) (β : j ⟶ k),
      g₁ ≫ D.map α = g₂ ≫ D.map β := by
  obtain ⟨k, α, β, hk⟩ := factor_eq_of_hom_colimit D (𝟙_ C)
    ((indOfUnitIso (C := C)).inv ≫ g₁)
    ((indOfUnitIso (C := C)).inv ≫ g₂)
    (by rw [Category.assoc, Category.assoc, h])
  refine ⟨k, α, β, ?_⟩
  calc g₁ ≫ D.map α
      = ((indOfUnitIso (C := C)).hom ≫
          ((indOfUnitIso (C := C)).inv ≫ g₁)) ≫ D.map α := by
        rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    _ = (indOfUnitIso (C := C)).hom ≫
          (((indOfUnitIso (C := C)).inv ≫ g₁) ≫ D.map α) :=
        Category.assoc _ _ _
    _ = (indOfUnitIso (C := C)).hom ≫
          (((indOfUnitIso (C := C)).inv ≫ g₂) ≫ D.map β) := by
        rw [hk]
    _ = ((indOfUnitIso (C := C)).hom ≫
          ((indOfUnitIso (C := C)).inv ≫ g₂)) ≫ D.map β :=
        (Category.assoc _ _ _).symm
    _ = g₂ ≫ D.map β := by
        rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- **Vanishing at a stage**: a unit-map's image in the colimit is
zero exactly when a transition map kills it. -/
theorem unit_colimit_eq_zero_iff
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C]
    {I : Type v} [SmallCategory I]
    [IsFiltered I] (D : I ⥤ Ind C) {i : I}
    (u : 𝟙_ (Ind C) ⟶ D.obj i) :
    u ≫ colimit.ι D i = 0 ↔
      ∃ (k : I) (α : i ⟶ k), u ≫ D.map α = 0 := by
  constructor
  · intro h
    obtain ⟨k, α, β, hk⟩ := unit_factor_eq_of_hom_colimit D u
      (0 : 𝟙_ (Ind C) ⟶ D.obj i)
      (by rw [h, Limits.zero_comp])
    exact ⟨k, α, by rw [hk, Limits.zero_comp]⟩
  · rintro ⟨k, α, hk⟩
    calc u ≫ colimit.ι D i
        = u ≫ D.map α ≫ colimit.ι D k := by
          rw [colimit.w]
      _ = (u ≫ D.map α) ≫ colimit.ι D k :=
          (Category.assoc _ _ _).symm
      _ = 0 := by rw [hk, Limits.zero_comp]

end RS
