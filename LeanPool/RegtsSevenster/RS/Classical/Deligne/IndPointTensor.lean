/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndSchur
import LeanPool.RegtsSevenster.RS.Classical.Deligne.PointTensor
import LeanPool.RegtsSevenster.RS.Classical.Deligne.UnitStage

/-!
# Points tensor without vanishing in the ind-completion

`RS.Classical.Deligne.PointTensor` proves, in an abelian ℂ-linear
rigid monoidal category with scalar unit, that the tensor of two
nonzero points of the unit is nonzero.  This file carries that
statement across the embedding `C ⥤ Ind C` to the whole
ind-completion — the fact Deligne asserts in 2.11 when he says the
algebra `𝔸` is not zero, since the unit of a tensor product of
algebras is `(λ_ _).inv ≫ (η ⊗ₘ η)`.

The route is compactness, applied twice.

* `RS.indOfTensorIso_hom_natural` — the embedding-tensor comparison
  is natural in both variables at once, assembled from the two
  one-variable naturalities of `RS.Classical.Deligne.IndTensorExact`;
* `RS.exists_indOf_point` — a point of an embedded object is the
  embedding of a point downstairs, and vanishes only if that one
  does (`RS.indOfUnitIso` and `RS.indOf_map_eq_zero_iff`);
* `RS.indTensorHom_point_ne_zero_indOf` — the statement for two
  embedded objects, obtained by conjugating with the unit comparison
  `RS.indOfUnitIso` and the embedding-tensor comparison and appealing
  to `RS.tensorHom_point_ne_zero` downstairs;
* `RS.tensor_unit_point_stage_left`/`_right` — the finite-stage
  engine: if the tensor of a point with a point of a filtered
  colimit vanishes, it already vanishes at some stage of the
  diagram.  Tensoring preserves filtered colimits
  (`RS.tensorLeft_ind_preservesFilteredColimits`) and the unit of
  `Ind C` is compact (`RS.unit_colimit_eq_zero_iff`);
* `RS.indTensorHom_point_ne_zero_indOf_left` — one embedded factor
  and one arbitrary, by presenting the second factor as a filtered
  colimit of embedded objects;
* **`RS.indTensorHom_point_ne_zero`** — both factors arbitrary, by
  the same descent in the first factor.

The filtered-colimit presentations are Mathlib's: `Ind.presentation`
and `Ind.colimitPresentationCompYoneda` exhibit every ind-object as
the colimit of `X.presentation.F ⋙ Ind.yoneda` over the filtered
index category `X.presentation.I`.
-/

namespace RS

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

noncomputable section

/-! ## Transport of a vanishing composite along a preserved colimit -/

section Preserve

variable {𝒜 : Type u}

/-- If a morphism into the image of a stage dies against the image
of a colimit injection, it dies against the colimit injection of the
transported diagram.  Stated with the domain written as
`F.obj (D.obj i)` so that every composite below is type-correct
without unfolding `Functor.comp`. -/
theorem comp_ι_comp_eq_zero [Category.{v} 𝒜] [HasZeroMorphisms 𝒜]
    {I : Type v} [SmallCategory I]
    (D : I ⥤ 𝒜) [HasColimit D] (F : 𝒜 ⥤ 𝒜) [PreservesColimit D F]
    {i : I} {W : 𝒜} (w : W ⟶ F.obj (D.obj i))
    (h : w ≫ F.map (colimit.ι D i) = 0) :
    w ≫ colimit.ι (D ⋙ F) i = 0 :=
  calc w ≫ colimit.ι (D ⋙ F) i
      = w ≫ (F.map (colimit.ι D i) ≫
          (preservesColimitIso F D).hom) :=
        whisker_eq w (ι_preservesColimitIso_hom F D i).symm
    _ = (w ≫ F.map (colimit.ι D i)) ≫
          (preservesColimitIso F D).hom :=
        (Category.assoc _ _ _).symm
    _ = 0 ≫ (preservesColimitIso F D).hom := by rw [h]
    _ = 0 := Limits.zero_comp

end Preserve

/-! ## The embedding-tensor comparison in both variables -/

section Naturality

variable {C : Type v}

/-- **Naturality of the embedding-tensor comparison in both
variables at once**: `RS.indOfTensorIso` intertwines the tensor of
two embedded morphisms with the embedding of their tensor.  The
two one-variable naturalities compose along
`MonoidalCategory.tensorHom_def`. -/
theorem indOfTensorIso_hom_natural [SmallCategory C] [MonoidalCategory C]
    {x x' y y' : C} (f : x ⟶ x')
    (g : y ⟶ y') :
    (indOf.map f ⊗ₘ indOf.map g) ≫ (indOfTensorIso x' y').hom =
      (indOfTensorIso x y).hom ≫ indOf.map (f ⊗ₘ g) := by
  rw [tensorHom_def, Category.assoc, indOfTensorIso_hom_natural_right,
    ← Category.assoc, indOfTensorIso_hom_natural_left, Category.assoc,
    ← Functor.map_comp, ← tensorHom_def]

end Naturality

/-! ## Both factors embedded -/

section Embedded

variable {C : Type v}

/-- **A point of an embedded object comes from downstairs**: read
through the unit comparison `RS.indOfUnitIso`, it is the embedding of
a point of the object in `C`, and that point is nonzero whenever the
original is. -/
theorem exists_indOf_point [SmallCategory C] [MonoidalCategory C] [Abelian C]
    {X : C} (u : 𝟙_ (Ind C) ⟶ indOf.obj X) :
    ∃ u₀ : 𝟙_ C ⟶ X,
      indOf.map u₀ = (indOfUnitIso (C := C)).inv ≫ u ∧
        (u ≠ 0 → u₀ ≠ 0) :=
  ⟨Ind.yoneda.fullyFaithful.preimage _,
    Ind.yoneda.fullyFaithful.map_preimage _, fun hne h0 => hne (by
      have hz : (indOfUnitIso (C := C)).inv ≫ u = 0 := by
        rw [← Ind.yoneda.fullyFaithful.map_preimage
          ((indOfUnitIso (C := C)).inv ≫ u), h0]
        exact ((indOf_map_eq_zero_iff (0 : 𝟙_ C ⟶ X)).mpr rfl)
      exact (Preadditive.IsIso.comp_left_eq_zero _ _).mp hz)⟩

/-- **The tensor of two nonzero points of embedded objects is
nonzero**: the unit comparison and the embedding-tensor comparison
identify it with the embedding of the corresponding tensor
downstairs, which is nonzero by `RS.tensorHom_point_ne_zero`. -/
theorem indTensorHom_point_ne_zero_indOf
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [Linear ℂ C]
    [MonoidalPreadditive C] [MonoidalLinear ℂ C] [RigidCategory C]
    (hu : HasScalarUnit C)
    {X Y : C} {u : 𝟙_ (Ind C) ⟶ indOf.obj X}
    {v : 𝟙_ (Ind C) ⟶ indOf.obj Y} (hu0 : u ≠ 0) (hv0 : v ≠ 0) :
    (u ⊗ₘ v) ≠ 0 := by
  intro h0
  obtain ⟨u₀, hu₀, hu₀0⟩ := exists_indOf_point u
  obtain ⟨v₀, hv₀, hv₀0⟩ := exists_indOf_point v
  have hzero : indOf.map u₀ ⊗ₘ indOf.map v₀ = 0 := by
    rw [hu₀, hv₀, ← tensorHom_comp_tensorHom, h0]
    exact Limits.comp_zero
  have hmap : indOf.map (u₀ ⊗ₘ v₀) = 0 := by
    have h1 := indOfTensorIso_hom_natural u₀ v₀
    rw [hzero, Limits.zero_comp] at h1
    exact (Preadditive.IsIso.comp_left_eq_zero _ _).mp h1.symm
  exact tensorHom_point_ne_zero hu (hu₀0 hu0) (hv₀0 hv0)
    ((indOf_map_eq_zero_iff (u₀ ⊗ₘ v₀)).mp hmap)

end Embedded

/-! ## The finite-stage engine -/

section Stage

variable {C : Type v}

/-- **Vanishing at a stage, second factor**: if the tensor of a
point of `M` with a point of a filtered colimit that factors through
the stage `i` vanishes, then it already vanishes after some
transition map out of `i`.  Tensoring on the left preserves the
filtered colimit, and the unit of `Ind C` is compact. -/
theorem tensor_unit_point_stage_left
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    {I : Type v} [SmallCategory I]
    [IsFiltered I] (D : I ⥤ Ind C) (M : Ind C) {i : I}
    (u : 𝟙_ (Ind C) ⟶ M) (g : 𝟙_ (Ind C) ⟶ D.obj i)
    (h : u ⊗ₘ (g ≫ colimit.ι D i) = 0) :
    ∃ (k : I) (α : i ⟶ k), u ⊗ₘ (g ≫ D.map α) = 0 := by
  have hz : ((λ_ (𝟙_ (Ind C))).inv ≫ (u ⊗ₘ g)) ≫
      (tensorLeft M).map (colimit.ι D i) = 0 := by
    have h1 : (u ⊗ₘ g) ≫ (M ◁ colimit.ι D i) = 0 := by
      rw [tensorHom_comp_whiskerLeft]
      exact h
    have h2 : ((λ_ (𝟙_ (Ind C))).inv ≫ (u ⊗ₘ g)) ≫
        (M ◁ colimit.ι D i) = 0 := by
      rw [Category.assoc, h1]
      exact Limits.comp_zero
    exact h2
  have hcol := comp_ι_comp_eq_zero D (tensorLeft M)
    ((λ_ (𝟙_ (Ind C))).inv ≫ (u ⊗ₘ g)) hz
  obtain ⟨k, α, hk⟩ :=
    (unit_colimit_eq_zero_iff (D ⋙ tensorLeft M) (i := i)
      ((λ_ (𝟙_ (Ind C))).inv ≫ (u ⊗ₘ g))).mp hcol
  refine ⟨k, α, ?_⟩
  have hk1 : ((λ_ (𝟙_ (Ind C))).inv ≫ (u ⊗ₘ g)) ≫
      (M ◁ D.map α) = 0 := hk
  rw [Category.assoc] at hk1
  have hk2 : (u ⊗ₘ g) ≫ (M ◁ D.map α) = 0 :=
    (Preadditive.IsIso.comp_left_eq_zero _ _).mp hk1
  rw [tensorHom_comp_whiskerLeft] at hk2
  exact hk2

/-- **Vanishing at a stage, first factor**: the mirror image of
`RS.tensor_unit_point_stage_left`, using that tensoring on the right
preserves filtered colimits. -/
theorem tensor_unit_point_stage_right
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    {I : Type v} [SmallCategory I]
    [IsFiltered I] (D : I ⥤ Ind C) (N : Ind C) {i : I}
    (f : 𝟙_ (Ind C) ⟶ D.obj i) (v : 𝟙_ (Ind C) ⟶ N)
    (h : (f ≫ colimit.ι D i) ⊗ₘ v = 0) :
    ∃ (k : I) (α : i ⟶ k), (f ≫ D.map α) ⊗ₘ v = 0 := by
  have hz : ((λ_ (𝟙_ (Ind C))).inv ≫ (f ⊗ₘ v)) ≫
      (tensorRight N).map (colimit.ι D i) = 0 := by
    have h1 : (f ⊗ₘ v) ≫ (colimit.ι D i ▷ N) = 0 := by
      rw [tensorHom_comp_whiskerRight]
      exact h
    have h2 : ((λ_ (𝟙_ (Ind C))).inv ≫ (f ⊗ₘ v)) ≫
        (colimit.ι D i ▷ N) = 0 := by
      rw [Category.assoc, h1]
      exact Limits.comp_zero
    exact h2
  have hcol := comp_ι_comp_eq_zero D (tensorRight N)
    ((λ_ (𝟙_ (Ind C))).inv ≫ (f ⊗ₘ v)) hz
  obtain ⟨k, α, hk⟩ :=
    (unit_colimit_eq_zero_iff (D ⋙ tensorRight N) (i := i)
      ((λ_ (𝟙_ (Ind C))).inv ≫ (f ⊗ₘ v))).mp hcol
  refine ⟨k, α, ?_⟩
  have hk1 : ((λ_ (𝟙_ (Ind C))).inv ≫ (f ⊗ₘ v)) ≫
      (D.map α ▷ N) = 0 := hk
  rw [Category.assoc] at hk1
  have hk2 : (f ⊗ₘ v) ≫ (D.map α ▷ N) = 0 :=
    (Preadditive.IsIso.comp_left_eq_zero _ _).mp hk1
  rw [tensorHom_comp_whiskerRight] at hk2
  exact hk2

end Stage

/-! ## The general statement -/

section Main

variable {C : Type v}

/-- **One embedded factor**: the tensor of a nonzero point of an
embedded object with a nonzero point of an arbitrary ind-object is
nonzero.  Present the second factor as a filtered colimit of
embedded objects, factor the point through a stage, and use that a
vanishing tensor vanishes at a stage. -/
theorem indTensorHom_point_ne_zero_indOf_left
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [Linear ℂ C]
    [MonoidalPreadditive C] [MonoidalLinear ℂ C] [RigidCategory C]
    (hu : HasScalarUnit C)
    {X : C} {N : Ind C} {u : 𝟙_ (Ind C) ⟶ indOf.obj X}
    {v : 𝟙_ (Ind C) ⟶ N} (hu0 : u ≠ 0) (hv0 : v ≠ 0) :
    (u ⊗ₘ v) ≠ 0 := by
  intro h0
  set D : N.presentation.I ⥤ Ind C := N.presentation.F ⋙ indOf
    with hD
  have e : colimit D ≅ N := Ind.colimitPresentationCompYoneda N
  have hv' : v ≫ e.inv ≠ 0 := fun hz =>
    hv0 ((Preadditive.IsIso.comp_right_eq_zero _ _).mp hz)
  obtain ⟨i, g, hg⟩ := exists_factor_of_unit_hom_colimit D (v ≫ e.inv)
  have h0' : u ⊗ₘ (g ≫ colimit.ι D i) = 0 := by
    rw [hg, ← tensorHom_comp_whiskerLeft, h0]
    exact Limits.zero_comp
  obtain ⟨k, α, hk⟩ := tensor_unit_point_stage_left D _ u g h0'
  have hgα : g ≫ D.map α ≠ 0 := by
    intro hz
    refine hv' ?_
    rw [← hg, ← colimit.w D α, ← Category.assoc, hz]
    exact Limits.zero_comp
  have hgα' : (g ≫ D.map α :
      𝟙_ (Ind C) ⟶ indOf.obj (N.presentation.F.obj k)) ≠ 0 := hgα
  exact indTensorHom_point_ne_zero_indOf (X := X)
    (Y := N.presentation.F.obj k) hu hu0 hgα' hk

/-- **The tensor of two nonzero points of the ind-completion is
nonzero** (Deligne 2.11, the nonvanishing of the algebra `𝔸`).
Present the first factor as a filtered colimit of embedded objects,
factor the point through a stage, and appeal to
`RS.indTensorHom_point_ne_zero_indOf_left`. -/
theorem indTensorHom_point_ne_zero
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [Linear ℂ C]
    [MonoidalPreadditive C] [MonoidalLinear ℂ C] [RigidCategory C]
    (hu : HasScalarUnit C)
    {M N : Ind C} {u : 𝟙_ (Ind C) ⟶ M} {v : 𝟙_ (Ind C) ⟶ N}
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) : (u ⊗ₘ v) ≠ 0 := by
  intro h0
  set D : M.presentation.I ⥤ Ind C := M.presentation.F ⋙ indOf
    with hD
  have e : colimit D ≅ M := Ind.colimitPresentationCompYoneda M
  have hu' : u ≫ e.inv ≠ 0 := fun hz =>
    hu0 ((Preadditive.IsIso.comp_right_eq_zero _ _).mp hz)
  obtain ⟨i, f, hf⟩ := exists_factor_of_unit_hom_colimit D (u ≫ e.inv)
  have h0' : (f ≫ colimit.ι D i) ⊗ₘ v = 0 := by
    rw [hf, ← tensorHom_comp_whiskerRight, h0]
    exact Limits.zero_comp
  obtain ⟨k, α, hk⟩ := tensor_unit_point_stage_right D _ f v h0'
  have hfα : f ≫ D.map α ≠ 0 := by
    intro hz
    refine hu' ?_
    rw [← hf, ← colimit.w D α, ← Category.assoc, hz]
    exact Limits.zero_comp
  have hfα' : (f ≫ D.map α :
      𝟙_ (Ind C) ⟶ indOf.obj (M.presentation.F.obj k)) ≠ 0 := hfα
  exact indTensorHom_point_ne_zero_indOf_left (X := M.presentation.F.obj k)
    (N := N) hu hfα' hv0 hk

end Main

end

end RS
