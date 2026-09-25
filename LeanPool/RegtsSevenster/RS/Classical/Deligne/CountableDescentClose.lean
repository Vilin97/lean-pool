/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ImageSubalgebra
import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndImage
import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreeModAdjoint

/-!
# Closing the countable descent

`RS.Classical.Deligne.CountableDescent` builds, inside a commutative
algebra `A` of `Ind C` and above a stage of its presentation, the
countable tower `RS.imageSubalgebra` and the monomorphism
`RS.imageSubalgebraHom` of that tower into the algebra;
`RS.Classical.Deligne.ImageSubalgebra` makes the tower an algebra in
its own right.  This file uses that replacement to push the two
witnessing statements of Deligne 2.9 and 2.10 down to countably
presented algebras: `RS.locallyMixed_countablyPresented` and
`RS.section_countablyPresented`.

The data.  An algebra witnessing local mixedness carries an
isomorphism of free modules, and one witnessing a splitting carries a
section.  Neither is a datum of the ambient category, so the
free--forgetful adjunction (`RS.freeModHomEquiv`) is used first to
transpose them: an isomorphism `freeMod A X ≅ freeMod A (L.mix p q)`
becomes a pair of morphisms `X ⟶ A ⊗ L.mix p q` and
`L.mix p q ⟶ A ⊗ X` subject to two unit identities
(`RS.roundTrip_of_freeModIso`), and a section becomes a single
morphism `W ⟶ A ⊗ V` subject to one
(`RS.sectionDatum_of_section`).  Both transpositions are reversible
(`RS.freeModIsoOfRoundTrip`, `RS.exists_section_of_datum`), so the
whole descent takes place in the ambient category.

The descent.  The algebra is the filtered colimit of the stages of
its presentation (`RS.presIsColimit`), tensoring preserves filtered
colimits, and the objects carrying the data are compact
(`RS.IndCompactObj`, satisfied by the embedded objects and by the
mixed sums).  So each datum factors through a stage
(`RS.exists_presStage_whiskerRight_factor`), finitely many data are
brought to a common stage above the one carrying the unit, and there
they enter the tower generated at that stage
(`RS.exists_imageSubalgebra_pair`, `RS.exists_imageSubalgebra_single`).

The identities.  What is left is to know that the identities descend
with the data.  The inclusion of the tower into the algebra is a
monomorphism and stays one after tensoring, the tensor product of
`Ind C` being exact in each variable
(`RS.mono_imageSubalgebraHom_whiskerRight`); the inclusion carries the
unit and the multiplication of the tower to those of the algebra; so
each identity may be verified after composing with the inclusion,
where it is the identity already known
(`RS.roundTrip_descend`, `RS.sectionDatum_descend`).  Countable
presentation of the tower is
`RS.countablyPresented_imageSubalgebra`, over the embedded-image
hypothesis discharged from finite length by
`RS.indImageEmbedded_of_lengthLE`.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe w v u

/-! ## Compact objects of the ind-completion -/

section Compact

variable {C : Type v}

/-- **Compactness of an ind-object**, phrased as in
`RS.Classical.Deligne.IndCompact`: a morphism from the object into a
filtered colimit factors through a stage of the diagram. -/
def IndCompactObj [SmallCategory C]
    (Y : Ind C) : Prop :=
  ∀ {I : Type v} [SmallCategory I] [IsFiltered I] (D : I ⥤ Ind C)
    (f : Y ⟶ colimit D),
    ∃ (i : I) (g : Y ⟶ D.obj i), g ≫ colimit.ι D i = f

/-- **The embedded objects are compact.** -/
theorem indCompactObj_indOf [SmallCategory C]
    (Z : C) :
    IndCompactObj ((indOf : C ⥤ Ind C).obj Z) :=
  fun D f => exists_factor_of_hom_colimit D Z f

/-- **Compactness against an arbitrary colimit cocone**: the
factorisation of the definition does not depend on the chosen
colimit. -/
theorem IndCompactObj.factor_of_isColimit [SmallCategory C]
    {Y : Ind C}
    (hY : IndCompactObj Y) {I : Type v} [SmallCategory I]
    [IsFiltered I] {K : I ⥤ Ind C} (c : Cocone K) (hc : IsColimit c)
    (f : Y ⟶ c.pt) :
    ∃ (i : I) (g : Y ⟶ K.obj i), g ≫ c.ι.app i = f := by
  obtain ⟨i, g, hg⟩ := hY K (f ≫ (hc.coconePointUniqueUpToIso
    (colimit.isColimit K)).hom)
  refine ⟨i, g, ?_⟩
  refine (cancel_mono (hc.coconePointUniqueUpToIso
    (colimit.isColimit K)).hom).mp ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact (whisker_eq _ (hc.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit K) i)).trans hg

end Compact

/-! ## The presentation as a colimit cocone -/

section PresCocone

variable {C : Type v}

/-- The cocone of the chosen presentation of an ind-object, with the
ind-object itself as its point. -/
@[simps! pt]
noncomputable def presCocone [SmallCategory C]
    (A : Ind C) : Cocone (presDiagram A) :=
  Cocone.mk A
    { app := fun i => presStage A i
      naturality := fun _ _ α =>
        (presStage_naturality A α).trans (Category.comp_id _).symm }

@[simp] theorem presCocone_ι_app [SmallCategory C]
    (A : Ind C) (i : A.presentation.I) :
    (presCocone A).ι.app i = presStage A i := rfl

/-- **The presentation cocone is a colimit cocone.** -/
noncomputable def presIsColimit [SmallCategory C]
    (A : Ind C) :
    IsColimit (presCocone A) :=
  IsColimit.ofIsoColimit (colimit.isColimit (presDiagram A))
    (Cocone.ext (Ind.colimitPresentationCompYoneda A) (fun _ => rfl))

end PresCocone

/-! ## Descending the finite data to a stage -/

section TensorFactor

variable {C : Type v}

/-- **A map from a compact object into a base change factors through
a stage of the presentation**: tensoring preserves filtered colimits,
so the base change of the presentation cocone is again a colimit
cocone. -/
theorem exists_presStage_whiskerRight_factor
    [SmallCategory C] [MonoidalCategory C]
    (A : Ind C) {Y M : Ind C}
    (hY : IndCompactObj Y) (f : Y ⟶ A ⊗ M) :
    ∃ (i : A.presentation.I)
      (g : Y ⟶ indOf.obj (A.presentation.F.obj i) ⊗ M),
      g ≫ presStage A i ▷ M = f :=
  hY.factor_of_isColimit ((tensorRight M).mapCocone (presCocone A))
    (isColimitOfPreserves (tensorRight M) (presIsColimit A)) f

end TensorFactor

/-! ## Descending the round-trip identities along a subalgebra -/

section MonoDescend

variable {D : Type u}

/-- **The product of the subalgebra, read in the algebra**: the
left-hand free action of the subalgebra, followed by the inclusion,
is the left-hand free action of the algebra applied to the
transported datum. -/
theorem whiskerLeft_freeAct_comp_whiskerRight
    [Category.{w} D] [MonoidalCategory D] {A : D} {B : D} [MonObj A]
    [MonObj B]
    (φ : B ⟶ A)
    (hmul : μ[B] ≫ φ = (φ ⊗ₘ φ) ≫ μ[A]) {X M : D} (v : M ⟶ B ⊗ X) :
    ((B ◁ v) ≫ (α_ B B X).inv ≫ μ[B] ▷ X) ≫ φ ▷ X =
      (φ ▷ M) ≫ (A ◁ (v ≫ φ ▷ X)) ≫ (α_ A A X).inv ≫ μ[A] ▷ X := by
  have hnat : (α_ B B X).inv ≫ (φ ⊗ₘ φ) ▷ X =
      (φ ⊗ₘ φ ▷ X) ≫ (α_ A A X).inv := by
    have h := associator_inv_naturality φ φ (𝟙 X)
    simp only [tensorHom_id] at h
    exact h.symm
  calc ((B ◁ v) ≫ (α_ B B X).inv ≫ μ[B] ▷ X) ≫ φ ▷ X
      = (B ◁ v) ≫ (α_ B B X).inv ≫ (μ[B] ≫ φ) ▷ X := by
        simp only [Category.assoc, comp_whiskerRight]
    _ = (B ◁ v) ≫ ((α_ B B X).inv ≫ (φ ⊗ₘ φ) ▷ X) ≫ μ[A] ▷ X := by
        rw [hmul]
        simp only [Category.assoc, comp_whiskerRight]
    _ = ((B ◁ v) ≫ (φ ⊗ₘ φ ▷ X)) ≫ (α_ A A X).inv ≫ μ[A] ▷ X := by
        rw [hnat]
        simp only [Category.assoc]
    _ = (φ ⊗ₘ (v ≫ φ ▷ X)) ≫ (α_ A A X).inv ≫ μ[A] ▷ X := by
        rw [whiskerLeft_comp_tensorHom]
    _ = (φ ▷ M) ≫ (A ◁ (v ≫ φ ▷ X)) ≫
          (α_ A A X).inv ≫ μ[A] ▷ X := by
        rw [tensorHom_def, Category.assoc]

/-- **Descent of a round trip to a subalgebra**: the identity that
holds in the algebra for the transported data already holds in the
subalgebra, because the inclusion is a monomorphism and stays one
after tensoring. -/
theorem roundTrip_descend
    [Category.{w} D] [MonoidalCategory D] {A : D} {B : D} [MonObj A]
    [MonObj B]
    (φ : B ⟶ A) (hone : η[B] ≫ φ = η[A])
    (hmul : μ[B] ≫ φ = (φ ⊗ₘ φ) ≫ μ[A]) {X M : D}
    (u : X ⟶ B ⊗ M) (v : M ⟶ B ⊗ X) [Mono (φ ▷ X)]
    (h : (u ≫ φ ▷ M) ≫ (A ◁ (v ≫ φ ▷ X)) ≫
        (α_ A A X).inv ≫ μ[A] ▷ X = (λ_ X).inv ≫ η[A] ▷ X) :
    u ≫ (B ◁ v) ≫ (α_ B B X).inv ≫ μ[B] ▷ X =
      (λ_ X).inv ≫ η[B] ▷ X := by
  refine (cancel_mono (φ ▷ X)).mp ?_
  calc (u ≫ (B ◁ v) ≫ (α_ B B X).inv ≫ μ[B] ▷ X) ≫ φ ▷ X
      = u ≫ ((B ◁ v) ≫ (α_ B B X).inv ≫ μ[B] ▷ X) ≫ φ ▷ X := by
        simp only [Category.assoc]
    _ = u ≫ (φ ▷ M) ≫ (A ◁ (v ≫ φ ▷ X)) ≫
          (α_ A A X).inv ≫ μ[A] ▷ X := by
        rw [whiskerLeft_freeAct_comp_whiskerRight φ hmul]
    _ = (λ_ X).inv ≫ η[A] ▷ X := by
        rw [← h]
        simp only [Category.assoc]
    _ = ((λ_ X).inv ≫ η[B] ▷ X) ≫ φ ▷ X := by
        rw [Category.assoc, ← comp_whiskerRight, hone]

/-- **Descent of a splitting datum to a subalgebra.**  Only the unit
is involved: the datum is a single map, not a round trip. -/
theorem sectionDatum_descend
    [Category.{w} D] [MonoidalCategory D] {A : D} {B : D} [MonObj A]
    [MonObj B]
    (φ : B ⟶ A) (hone : η[B] ≫ φ = η[A])
    {V W : D} (g : V ⟶ W) (t : W ⟶ B ⊗ V) [Mono (φ ▷ W)]
    (h : (t ≫ φ ▷ V) ≫ (A ◁ g) = (λ_ W).inv ≫ η[A] ▷ W) :
    t ≫ (B ◁ g) = (λ_ W).inv ≫ η[B] ▷ W := by
  refine (cancel_mono (φ ▷ W)).mp ?_
  calc (t ≫ (B ◁ g)) ≫ φ ▷ W = t ≫ (B ◁ g) ≫ φ ▷ W :=
        Category.assoc _ _ _
    _ = t ≫ (φ ▷ V) ≫ (A ◁ g) := by rw [whisker_exchange]
    _ = (λ_ W).inv ≫ η[A] ▷ W := by
        rw [← h]
        simp only [Category.assoc]
    _ = ((λ_ W).inv ≫ η[B] ▷ W) ≫ φ ▷ W := by
        rw [Category.assoc, ← comp_whiskerRight, hone]

end MonoDescend

/-! ## Rebuilding the module data from the descended maps -/

section FreeRebuild

variable {D : Type u}

/-- Restricting a composite out of a free module along the unit is
postcomposition of the restriction of the first factor. -/
theorem freeModHomEquiv_symm_comp
    [Category.{w} D] [MonoidalCategory D] (R : D) [MonObj R]
    {X M : D} (N : Mod D R)
    (u : X ⟶ (freeMod R M).X) (k : freeMod R M ⟶ N) :
    freeModHomEquiv R X N
        ((freeModHomEquiv R X (freeMod R M)).symm u ≫ k) =
      u ≫ k.hom :=
  (unit_comp_assoc R X _ _ _ k.hom).trans
    (congrArg (fun z => z ≫ k.hom)
      ((freeModHomEquiv R X (freeMod R M)).apply_symm_apply u))

/-- Restricting the identity of a free module along the unit is the
unit itself. -/
theorem freeModHomEquiv_id
    [Category.{w} D] [MonoidalCategory D] (R : D) [MonObj R]
    (X : D) :
    freeModHomEquiv R X (freeMod R X) (𝟙 (freeMod R X)) =
      (λ_ X).inv ≫ η[R] ▷ X := by
  change (λ_ X).inv ≫ (η[R] ▷ X) ≫ 𝟙 _ = _
  rw [Category.comp_id]

/-- **An isomorphism of free modules from a round trip**: a pair of
maps in the ambient category satisfying the two unit identities
extends to an isomorphism of free modules, by the free--forgetful
adjunction. -/
noncomputable def freeModIsoOfRoundTrip
    [Category.{w} D] [MonoidalCategory D] (R : D) [MonObj R]
    {X M : D} (u : X ⟶ R ⊗ M)
    (v : M ⟶ R ⊗ X)
    (h₁ : u ≫ (R ◁ v) ≫ (α_ R R X).inv ≫ μ[R] ▷ X =
      (λ_ X).inv ≫ η[R] ▷ X)
    (h₂ : v ≫ (R ◁ u) ≫ (α_ R R M).inv ≫ μ[R] ▷ M =
      (λ_ M).inv ≫ η[R] ▷ M) :
    freeMod R X ≅ freeMod R M where
  hom := (freeModHomEquiv R X (freeMod R M)).symm u
  inv := (freeModHomEquiv R M (freeMod R X)).symm v
  hom_inv_id := by
    refine (freeModHomEquiv R X (freeMod R X)).injective ?_
    refine Eq.trans (freeModHomEquiv_symm_comp R _ u _) ?_
    exact h₁.trans (freeModHomEquiv_id R X).symm
  inv_hom_id := by
    refine (freeModHomEquiv R M (freeMod R M)).injective ?_
    refine Eq.trans (freeModHomEquiv_symm_comp R _ v _) ?_
    exact h₂.trans (freeModHomEquiv_id R M).symm

/-- Restriction along the unit turns composition in the category of
modules into composition in the ambient category. -/
theorem freeModHomEquiv_comp
    [Category.{w} D] [MonoidalCategory D] (R : D) [MonObj R]
    {X : D} {N P : Mod D R}
    (f : freeMod R X ⟶ N) (k : N ⟶ P) :
    freeModHomEquiv R X P (f ≫ k) =
      freeModHomEquiv R X N f ≫ k.hom :=
  unit_comp_assoc R X _ _ f.hom k.hom

/-- A module map out of a free module is the extension of its
restriction along the unit. -/
theorem freeModHom_eq_whiskerLeft
    [Category.{w} D] [MonoidalCategory D] (R : D) [MonObj R]
    {M : D} (N : Mod D R)
    (f : freeMod R M ⟶ N) :
    f.hom = R ◁ (freeModHomEquiv R M N f) ≫ actLeft R N.X :=
  congrArg (fun z : freeMod R M ⟶ N => z.hom)
    ((freeModHomEquiv R M N).symm_apply_apply f).symm

/-- **The round trip attached to an isomorphism of free modules**:
the transposes of the two directions satisfy the unit identity. -/
theorem roundTrip_of_freeModIso
    [Category.{w} D] [MonoidalCategory D] (R : D) [MonObj R]
    {X M : D}
    (Φ : freeMod R X ≅ freeMod R M) :
    freeModHomEquiv R X (freeMod R M) Φ.hom ≫
        (R ◁ freeModHomEquiv R M (freeMod R X) Φ.inv) ≫
          (α_ R R X).inv ≫ μ[R] ▷ X =
      (λ_ X).inv ≫ η[R] ▷ X := by
  have h := freeModHomEquiv_comp R Φ.hom Φ.inv
  rw [Φ.hom_inv_id, freeModHomEquiv_id,
    freeModHom_eq_whiskerLeft R (freeMod R X) Φ.inv] at h
  exact h.symm

/-- **The datum attached to a splitting**: the transpose of a section
of the free module on a morphism satisfies the unit identity. -/
theorem sectionDatum_of_section
    [Category.{w} D] [MonoidalCategory D] (R : D) [MonObj R]
    {V W : D} (g : V ⟶ W)
    (s : freeMod R W ⟶ freeMod R V)
    (hs : s ≫ freeModMap R g = 𝟙 (freeMod R W)) :
    freeModHomEquiv R W (freeMod R V) s ≫ (R ◁ g) =
      (λ_ W).inv ≫ η[R] ▷ W := by
  have h := freeModHomEquiv_comp R s (freeModMap R g)
  rw [hs, freeModHomEquiv_id] at h
  exact h.symm

/-- **A splitting from its datum**: a map satisfying the unit
identity extends to a section of the free module on a morphism. -/
theorem exists_section_of_datum
    [Category.{w} D] [MonoidalCategory D] (R : D) [MonObj R]
    {V W : D} (g : V ⟶ W)
    (t : W ⟶ R ⊗ V) (h : t ≫ (R ◁ g) = (λ_ W).inv ≫ η[R] ▷ W) :
    ∃ s : freeMod R W ⟶ freeMod R V,
      s ≫ freeModMap R g = 𝟙 (freeMod R W) := by
  refine ⟨(freeModHomEquiv R W (freeMod R V)).symm t, ?_⟩
  refine (freeModHomEquiv R W (freeMod R W)).injective ?_
  refine Eq.trans (freeModHomEquiv_symm_comp R _ t _) ?_
  exact h.trans (freeModHomEquiv_id R W).symm

end FreeRebuild

/-! ## Entering the image subalgebra -/

section IntoImage

variable {C : Type v}

/-- The generating stage, mapped into rung zero of the image tower and
on into the subalgebra it generates. -/
noncomputable def stageIntoImageSubalgebra
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I) :
    indOf.obj (A.presentation.F.obj i₀) ⟶ imageSubalgebra A i₀ :=
  stageToImage A i₀ ≫ imageRungι A i₀ 0

theorem stageIntoImageSubalgebra_comp_hom
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I) :
    stageIntoImageSubalgebra A i₀ ≫ imageSubalgebraHom A i₀ =
      presStage A i₀ :=
  (Category.assoc _ _ _).trans
    ((whisker_eq _ (imageRungι_comp_hom A i₀ 0)).trans
      (stageToImage_comp_ι A i₀))

/-- **A stage factorisation enters the image subalgebra**: a datum
factoring through a stage below the generating one factors through the
subalgebra generated there. -/
theorem exists_imageSubalgebra_factor
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I)
    {Y M : Ind C}
    {i : A.presentation.I} (α : i ⟶ i₀)
    (g : Y ⟶ indOf.obj (A.presentation.F.obj i) ⊗ M) (f : Y ⟶ A ⊗ M)
    (hg : g ≫ presStage A i ▷ M = f) :
    ∃ g' : Y ⟶ imageSubalgebra A i₀ ⊗ M,
      g' ≫ imageSubalgebraHom A i₀ ▷ M = f := by
  refine ⟨g ≫ (indOf.map (A.presentation.F.map α) ≫
    stageIntoImageSubalgebra A i₀) ▷ M, ?_⟩
  rw [Category.assoc, ← comp_whiskerRight, Category.assoc,
    stageIntoImageSubalgebra_comp_hom, presStage_naturality, hg]

/-- **Two data descend to a common image subalgebra**, generated at a
stage that also carries the unit of the algebra. -/
theorem exists_imageSubalgebra_pair
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A]
    {Y Y' M M' : Ind C}
    (hY : IndCompactObj Y) (hY' : IndCompactObj Y') (f : Y ⟶ A ⊗ M)
    (f' : Y' ⟶ A ⊗ M') :
    ∃ (j : A.presentation.I) (_ : UnitAtStage A j)
      (g : Y ⟶ imageSubalgebra A j ⊗ M)
      (g' : Y' ⟶ imageSubalgebra A j ⊗ M'),
      g ≫ imageSubalgebraHom A j ▷ M = f ∧
        g' ≫ imageSubalgebraHom A j ▷ M' = f' := by
  obtain ⟨i₁, g₁, hg₁⟩ := exists_presStage_whiskerRight_factor A hY f
  obtain ⟨i₂, g₂, hg₂⟩ := exists_presStage_whiskerRight_factor A hY' f'
  obtain ⟨g, hg⟩ := exists_imageSubalgebra_factor A
    (IsFiltered.max (IsFiltered.max i₁ i₂) (unitStage A))
    (IsFiltered.leftToMax i₁ i₂ ≫ IsFiltered.leftToMax _ _) g₁ f hg₁
  obtain ⟨g', hg'⟩ := exists_imageSubalgebra_factor A
    (IsFiltered.max (IsFiltered.max i₁ i₂) (unitStage A))
    (IsFiltered.rightToMax i₁ i₂ ≫ IsFiltered.leftToMax _ _) g₂ f' hg₂
  exact ⟨_, UnitAtStage.map (IsFiltered.rightToMax _ _), g, g', hg, hg'⟩

/-- **A single datum descends to an image subalgebra**, generated at a
stage that also carries the unit of the algebra. -/
theorem exists_imageSubalgebra_single
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A]
    {Y M : Ind C}
    (hY : IndCompactObj Y) (f : Y ⟶ A ⊗ M) :
    ∃ (j : A.presentation.I) (_ : UnitAtStage A j)
      (g : Y ⟶ imageSubalgebra A j ⊗ M),
      g ≫ imageSubalgebraHom A j ▷ M = f := by
  obtain ⟨i, g₀, hg₀⟩ := exists_presStage_whiskerRight_factor A hY f
  obtain ⟨g, hg⟩ := exists_imageSubalgebra_factor A
    (IsFiltered.max i (unitStage A)) (IsFiltered.leftToMax _ _) g₀ f hg₀
  exact ⟨_, UnitAtStage.map (IsFiltered.rightToMax _ _), g, hg⟩

end IntoImage

/-! ## The two theorems -/

section Close

variable {C : Type v}

/-- **The inclusion of the image subalgebra stays a monomorphism after
tensoring**: the tensor product of `Ind C` is exact in each
variable. -/
theorem mono_imageSubalgebraHom_whiskerRight
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    (A : Ind C) [MonObj A]
    (i₀ : A.presentation.I) (M : Ind C) :
    Mono (imageSubalgebraHom A i₀ ▷ M) :=
  haveI := mono_imageSubalgebraHom A i₀
  inferInstanceAs
    (Mono ((tensorRight M).map (imageSubalgebraHom A i₀)))

/-- **The mixed sums are compact.** -/
theorem indCompactObj_mix
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    (L : OddLine (Ind C)) (p q : ℕ) :
    IndCompactObj (L.mix p q) :=
  fun D f => exists_factor_of_mix_hom_colimit L p q D f

/-- **The countably presented form of local mixedness**: an object of
`Ind C` that becomes a mixed sum of the unit and the odd line over
some algebra with non-vanishing unit already becomes one over a
countably presented such algebra, provided the object is compact and
the objects of `C` have finite length. -/
theorem locallyMixed_countablyPresented
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    (L : OddLine (Ind C))
    (X : Ind C) (hX : IndCompactObj X)
    (hlen : ∀ Z : C, ∃ N, LengthLE Z N) (h : L.LocallyMixed X) :
    ∃ (p q : ℕ) (A : Ind C) (_ : MonObj A) (_ : IsCommMonObj A),
      η[A] ≠ 0 ∧ CountablyPresented A ∧
        Nonempty (freeMod A X ≅ freeMod A (L.mix p q)) := by
  obtain ⟨p, q, A, hmon, hcomm, hA, ⟨Φ⟩⟩ := h
  let := hmon
  let := hcomm
  obtain ⟨j, hjunit, u, v, hu, hv⟩ :=
    exists_imageSubalgebra_pair A hX (indCompactObj_mix L p q)
      (freeModHomEquiv A X (freeMod A (L.mix p q)) Φ.hom)
      (freeModHomEquiv A (L.mix p q) (freeMod A X) Φ.inv)
  have := hjunit
  have := mono_imageSubalgebraHom_whiskerRight A j X
  have := mono_imageSubalgebraHom_whiskerRight A j (L.mix p q)
  refine ⟨p, q, imageSubalgebra A j, inferInstance, inferInstance,
    one_imageSubalgebra_ne_zero A j hA,
    countablyPresented_imageSubalgebra A j
      (indImageEmbedded_of_lengthLE hlen),
    ⟨freeModIsoOfRoundTrip (imageSubalgebra A j) u v ?_ ?_⟩⟩
  · refine roundTrip_descend (imageSubalgebraHom A j)
      (imageOne_comp_hom A j) (imageMul_comp_hom A j) u v ?_
    rw [hu, hv]
    exact roundTrip_of_freeModIso A Φ
  · refine roundTrip_descend (imageSubalgebraHom A j)
      (imageOne_comp_hom A j) (imageMul_comp_hom A j) v u ?_
    rw [hu, hv]
    exact roundTrip_of_freeModIso A Φ.symm

/-- **The countably presented form of the local splitting**: a
morphism of `Ind C` whose free module acquires a section over some
algebra with non-vanishing unit already acquires one over a countably
presented such algebra, provided the two objects are compact and the
objects of `C` have finite length. -/
theorem section_countablyPresented
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    {V W : Ind C} (g : V ⟶ W)
    (_hV : IndCompactObj V) (hW : IndCompactObj W)
    (hlen : ∀ Z : C, ∃ N, LengthLE Z N)
    (h : ∃ (A : Ind C) (_ : MonObj A) (_ : IsCommMonObj A),
      η[A] ≠ 0 ∧
        ∃ s : freeMod A W ⟶ freeMod A V,
          s ≫ freeModMap A g = 𝟙 (freeMod A W)) :
    ∃ (A : Ind C) (_ : MonObj A) (_ : IsCommMonObj A),
      η[A] ≠ 0 ∧ CountablyPresented A ∧
        ∃ s : freeMod A W ⟶ freeMod A V,
          s ≫ freeModMap A g = 𝟙 (freeMod A W) := by
  obtain ⟨A, hmon, hcomm, hA, s, hs⟩ := h
  let := hmon
  let := hcomm
  obtain ⟨j, hjunit, t, ht⟩ := exists_imageSubalgebra_single A hW
    (freeModHomEquiv A W (freeMod A V) s)
  have := hjunit
  have := mono_imageSubalgebraHom_whiskerRight A j W
  refine ⟨imageSubalgebra A j, inferInstance, inferInstance,
    one_imageSubalgebra_ne_zero A j hA,
    countablyPresented_imageSubalgebra A j
      (indImageEmbedded_of_lengthLE hlen),
    exists_section_of_datum (imageSubalgebra A j) g t ?_⟩
  refine sectionDatum_descend (imageSubalgebraHom A j)
    (imageOne_comp_hom A j) g t ?_
  rw [ht]
  exact sectionDatum_of_section A g s hs

end Close

/-! ## Acceptance tests

The compactness hypothesis of the two theorems is satisfied by the
embedded objects, which is the shape in which the theorems are
consumed. -/

section AcceptanceTests

variable {C : Type v}

example
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    (L : OddLine (Ind C)) (Z : C)
    (hlen : ∀ Y : C, ∃ N, LengthLE Y N)
    (h : L.LocallyMixed ((indOf : C ⥤ Ind C).obj Z)) :
    ∃ (p q : ℕ) (A : Ind C) (_ : MonObj A) (_ : IsCommMonObj A),
      η[A] ≠ 0 ∧ CountablyPresented A ∧
        Nonempty (freeMod A ((indOf : C ⥤ Ind C).obj Z) ≅
          freeMod A (L.mix p q)) :=
  locallyMixed_countablyPresented L _ (indCompactObj_indOf Z) hlen h

example
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    {Y Z : C} (g : (indOf : C ⥤ Ind C).obj Y ⟶ indOf.obj Z)
    (hlen : ∀ W : C, ∃ N, LengthLE W N)
    (h : ∃ (A : Ind C) (_ : MonObj A) (_ : IsCommMonObj A),
      η[A] ≠ 0 ∧
        ∃ s : freeMod A (indOf.obj Z) ⟶ freeMod A (indOf.obj Y),
          s ≫ freeModMap A g = 𝟙 (freeMod A (indOf.obj Z))) :
    ∃ (A : Ind C) (_ : MonObj A) (_ : IsCommMonObj A),
      η[A] ≠ 0 ∧ CountablyPresented A ∧
        ∃ s : freeMod A (indOf.obj Z) ⟶ freeMod A (indOf.obj Y),
          s ≫ freeModMap A g = 𝟙 (freeMod A (indOf.obj Z)) :=
  section_countablyPresented g (indCompactObj_indOf Y)
    (indCompactObj_indOf Z) hlen h

end AcceptanceTests

end RS
