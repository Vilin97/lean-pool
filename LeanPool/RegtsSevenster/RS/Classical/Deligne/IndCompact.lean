/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndMonoidal

/-!
# Compactness of the embedded objects of the ind-completion

Objects of a small category `C` are compact in `Ind C`: the hom
functor out of an embedded object preserves filtered colimits.  This
is the finite-stage engine of Deligne 2.8 — a morphism from an
embedded object into a filtered colimit factors through a stage, and
two stage factorisations that agree in the colimit are merged by
transition maps of the diagram.

* `RS.indOf` — the canonical embedding `C ⥤ Ind C` (Mathlib's
  `Ind.yoneda`, re-exported);
* `RS.indOfCoyonedaIso` — mapping out of `indOf.obj X` in `Ind C` is
  mapping out of the representable `yoneda.obj X` after applying the
  inclusion `Ind C ⥤ Cᵒᵖ ⥤ Type v`;
* `RS.preservesColimitsOfShape_coyoneda_indOf` and the derived
  `PreservesFilteredColimits` instance — compactness itself;
* `RS.exists_factor_of_hom_colimit` — factorisation through a stage;
* `RS.factor_eq_of_hom_colimit` — merging of stage factorisations;
* `RS.comp_ι_eq_comp_ι_iff` — equality after passing to the colimit
  is equality at some later stage.

The route: the inclusion `Ind C ⥤ Cᵒᵖ ⥤ Type v` is fully faithful
and creates (hence preserves) filtered colimits, and mapping out of a
representable presheaf preserves all colimits that exist (Mathlib's
`Limits.Preserves.Yoneda`); the stage lemmas then read off elements
of a filtered colimit of types (`Types.jointly_surjective'`,
`Types.FilteredColimit.colimit_eq_iff`).
-/

namespace RS

open CategoryTheory Limits Opposite

universe v

variable {C : Type v}

/-- The canonical embedding of a small category into its
ind-completion: Mathlib's `Ind.yoneda`, re-exported under the name
used throughout the Deligne development. -/
noncomputable abbrev indOf [SmallCategory C] : C ⥤ Ind C := Ind.yoneda

/-- Mapping out of an embedded object of `Ind C` is mapping out of
its representable presheaf: the inclusion `Ind C ⥤ Cᵒᵖ ⥤ Type v` is
fully faithful and carries `indOf.obj X` to an object isomorphic to
`yoneda.obj X`. -/
noncomputable def indOfCoyonedaIso [SmallCategory C]
    (X : C) :
    coyoneda.obj (op (indOf.obj X)) ≅
      Ind.inclusion C ⋙ coyoneda.obj (op (yoneda.obj X)) :=
  NatIso.ofComponents
    (fun A => Equiv.toIso
      (Ind.inclusion.fullyFaithful.homEquiv.trans
        ((Ind.yonedaCompInclusion.app X).homCongr (Iso.refl _))))
    (fun h => by
      ext f
      show (Ind.yonedaCompInclusion.app X).inv ≫
          (Ind.inclusion C).map (f ≫ h) ≫ 𝟙 _ =
        ((Ind.yonedaCompInclusion.app X).inv ≫
          (Ind.inclusion C).map f ≫ 𝟙 _) ≫ (Ind.inclusion C).map h
      simp)

/-- **Objects of `C` are compact in `Ind C`**: the hom functor out
of an embedded object preserves filtered colimits of any given small
shape. -/
instance preservesColimitsOfShape_coyoneda_indOf [SmallCategory C]
    (X : C)
    (I : Type v) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I (coyoneda.obj (op (indOf.obj X))) :=
  haveI : PreservesColimitsOfShape I
      (coyoneda.obj (op (yoneda.obj X)) : (Cᵒᵖ ⥤ Type v) ⥤ Type v) :=
    ⟨inferInstance⟩
  preservesColimitsOfShape_of_natIso (indOfCoyonedaIso X).symm

/-- Compactness, packaged: the hom functor out of an embedded object
preserves all (small) filtered colimits. -/
instance preservesFilteredColimits_coyoneda_indOf [SmallCategory C]
    (X : C) :
    PreservesFilteredColimits (coyoneda.obj (op (indOf.obj X))) where
  preserves_filtered_colimits _ _ _ := inferInstance

/-- Stage description of an element of the hom-out-of-`indOf` functor
applied to a filtered colimit: the colimit injection of the diagram
of hom sets is postcomposition with the colimit injection of the
diagram, read through the preservation isomorphism. -/
theorem ι_comp_coyoneda_indOf [SmallCategory C]
    {I : Type v} [SmallCategory I]
    [IsFiltered I] (D : I ⥤ Ind C) (X : C) (i : I)
    (g : indOf.obj X ⟶ D.obj i) :
    colimit.ι (D ⋙ coyoneda.obj (op (indOf.obj X))) i g =
      (preservesColimitIso (coyoneda.obj (op (indOf.obj X))) D).hom
        (g ≫ colimit.ι D i) := by
  simpa using
    (ConcreteCategory.congr_hom
      (ι_preservesColimitIso_hom
        (coyoneda.obj (op (indOf.obj X))) D i) g).symm

/-- **Factorisation through a stage** (half of Kashiwara–Schapira
6.1.19, the surjectivity half of the compactness formula): a
morphism from an embedded object into a filtered colimit in `Ind C`
factors through one of the stages of the diagram. -/
theorem exists_factor_of_hom_colimit [SmallCategory C]
    {I : Type v} [SmallCategory I]
    [IsFiltered I] (D : I ⥤ Ind C) (X : C)
    (f : indOf.obj X ⟶ colimit D) :
    ∃ (i : I) (g : indOf.obj X ⟶ D.obj i),
      g ≫ colimit.ι D i = f := by
  obtain ⟨i, g, hg⟩ := Types.jointly_surjective'
    ((preservesColimitIso (coyoneda.obj (op (indOf.obj X))) D).hom f)
  refine ⟨i, g,
    (preservesColimitIso
      (coyoneda.obj (op (indOf.obj X))) D).toEquiv.injective ?_⟩
  exact (ι_comp_coyoneda_indOf D X i g).symm.trans hg

/-- **Merging of stage factorisations** (the injectivity half of the
compactness formula): two stage factorisations that agree after
passing to the filtered colimit are merged by transition maps of the
diagram. -/
theorem factor_eq_of_hom_colimit [SmallCategory C]
    {I : Type v} [SmallCategory I]
    [IsFiltered I] (D : I ⥤ Ind C) (X : C) {i j : I}
    (g₁ : indOf.obj X ⟶ D.obj i) (g₂ : indOf.obj X ⟶ D.obj j)
    (h : g₁ ≫ colimit.ι D i = g₂ ≫ colimit.ι D j) :
    ∃ (k : I) (α : i ⟶ k) (β : j ⟶ k),
      g₁ ≫ D.map α = g₂ ≫ D.map β := by
  have h' : colimit.ι (D ⋙ coyoneda.obj (op (indOf.obj X))) i g₁ =
      colimit.ι (D ⋙ coyoneda.obj (op (indOf.obj X))) j g₂ := by
    rw [ι_comp_coyoneda_indOf, ι_comp_coyoneda_indOf, h]
  obtain ⟨k, α, β, hk⟩ :=
    (Types.FilteredColimit.colimit_eq_iff _).mp h'
  exact ⟨k, α, β, hk⟩

/-- **Equality in the colimit is equality at a stage**: two parallel
morphisms from an embedded object to a stage of a filtered diagram
agree after passing to the colimit iff they agree after some
transition map.  (In an additive setting, applied with `g₂ = 0`:
a stage morphism vanishes in the colimit iff it vanishes at some
later stage.) -/
theorem comp_ι_eq_comp_ι_iff [SmallCategory C]
    {I : Type v} [SmallCategory I]
    [IsFiltered I] (D : I ⥤ Ind C) (X : C) {i : I}
    (g₁ g₂ : indOf.obj X ⟶ D.obj i) :
    g₁ ≫ colimit.ι D i = g₂ ≫ colimit.ι D i ↔
      ∃ (k : I) (α : i ⟶ k), g₁ ≫ D.map α = g₂ ≫ D.map α := by
  constructor
  · intro h
    obtain ⟨k, α, β, hk⟩ := factor_eq_of_hom_colimit D X g₁ g₂ h
    refine ⟨IsFiltered.coeq α β, α ≫ IsFiltered.coeqHom α β, ?_⟩
    rw [Functor.map_comp, ← Category.assoc, hk, Category.assoc,
      ← Functor.map_comp, ← IsFiltered.coeq_condition,
      Functor.map_comp]
  · rintro ⟨k, α, hk⟩
    rw [← colimit.w D α, ← Category.assoc, hk, Category.assoc]

end RS
