/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndImage

/-!
# Quotients of countably presented ind-objects

`RS.CountablyPresented` — a countable filtered colimit of embedded
objects — is the shape in which "built from countably much data"
enters the dimension count of
`RS.Classical.Deligne.GammaCountable`.  This file shows the notion
stable under quotients: an epimorphic image of a countably presented
ind-object is countably presented
(`RS.CountablyPresented.of_epi`), over the same finite length
hypothesis that discharges `RS.IndImageEmbedded`.

The argument.  Write `Z` as the colimit of a countable filtered
diagram `D` of embedded objects and let `p : Z ⟶ Q` be an
epimorphism.  The composites of the colimit inclusions with `p` form
a family `RS.quotientStage` of maps into `Q`, compatible with the
structural maps of `D`, and the images of its members assemble into a
diagram `RS.imageDiag` — functorially, because such a family is a
diagram in the arrow category and the image is a functor on the arrow
category (`CategoryTheory.Limits.im`).

The colimit of that diagram is `Q` itself
(`RS.exists_iso_colimit_imageDiag`).  It maps to `Q` by the image
inclusions; the map is a monomorphism because filtered colimits are
exact in the ind-completion, so `colim` preserves monomorphisms
(`CategoryTheory.Limits.colim.map_mono'` over the AB5 property of
`Ind C`), and an epimorphism because the members of the family are
jointly epimorphic (`RS.quotientStage_jointly_epi`) and each factors
through its image.

Finite length makes each of those images embedded
(`RS.indImageEmbedded_of_lengthLE`), and a diagram of ind-objects all
of whose values are embedded is the embedding of a diagram in the
base category (`RS.liftEmbedded`), which is what
`RS.CountablyPresented` asks for.

The dimension counts the descent consumes follow: the even component
of a countably presented ind-object is of at most countable dimension
(`RS.rank_hom_unit_le_aleph0_of_presented`), and hence so is that of
any of its quotients (`RS.rank_hom_unit_le_aleph0_of_epi`).
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

attribute [local instance] IsFiltered.isConnected

/-! ## Lifting a diagram of embedded objects

A diagram of ind-objects whose values are all embedded is the
embedding of a diagram in the base category: the structural maps are
transported through the full faithfulness of `RS.indOf`. -/

section Lift

variable {C : Type v}

/-- **A diagram of embedded objects comes from the base category**:
the chosen isomorphisms transport the structural maps down through
the full faithfulness of the embedding. -/
noncomputable def liftEmbedded [SmallCategory C]
    {I : Type v} [SmallCategory I]
    (F : I ⥤ Ind C) (W : I → C) (θ : ∀ i, F.obj i ≅ indOf.obj (W i)) :
    I ⥤ C where
  obj := W
  map {i j} α := Ind.yoneda.fullyFaithful.preimage
    ((θ i).inv ≫ F.map α ≫ (θ j).hom)
  map_id i := by
    refine indOf.map_injective ?_
    rw [Ind.yoneda.fullyFaithful.map_preimage]
    simp
  map_comp {i j k} α β := by
    refine indOf.map_injective ?_
    simp

/-- The lifted diagram embeds back to the diagram it was lifted
from. -/
noncomputable def liftEmbeddedIso [SmallCategory C]
    {I : Type v} [SmallCategory I]
    (F : I ⥤ Ind C) (W : I → C) (θ : ∀ i, F.obj i ≅ indOf.obj (W i)) :
    liftEmbedded F W θ ⋙ indOf ≅ F :=
  NatIso.ofComponents (fun i => (θ i).symm) (by
    intro i j α
    show indOf.map (Ind.yoneda.fullyFaithful.preimage
      ((θ i).inv ≫ F.map α ≫ (θ j).hom)) ≫ (θ j).inv =
      (θ i).inv ≫ F.map α
    rw [Ind.yoneda.fullyFaithful.map_preimage]
    simp)

end Lift

/-! ## The diagram of images

A compatible family of maps into a fixed object is a diagram in the
arrow category, and the image is a functor on the arrow category
(`CategoryTheory.Limits.im`), so the images of the members of the
family form a diagram again. -/

section ImageDiagram

variable {C : Type v}

/-- A compatible family of maps into a fixed object, read as a
diagram in the arrow category. -/
noncomputable def arrowDiagram
    [SmallCategory C] {I : Type v} [SmallCategory I] {D : I ⥤ Ind C}
    {Q : Ind C}
    (f : ∀ i, D.obj i ⟶ Q)
    (hf : ∀ (i j : I) (α : i ⟶ j), D.map α ≫ f j = f i) :
    I ⥤ Arrow (Ind C) where
  obj i := Arrow.mk (f i)
  map {i j} α := Arrow.homMk' (D.map α) (𝟙 Q)
    (by rw [hf i j α, Category.comp_id])
  map_id i := by
    ext
    · exact D.map_id i
    · rfl
  map_comp α β := by
    ext
    · exact D.map_comp α β
    · exact (Category.comp_id (𝟙 Q)).symm

/-- **The diagram of images** of a compatible family of maps into a
fixed object. -/
noncomputable def imageDiag
    [SmallCategory C] [Abelian C] {I : Type v} [SmallCategory I]
    {D : I ⥤ Ind C} {Q : Ind C}
    (f : ∀ i, D.obj i ⟶ Q)
    (hf : ∀ (i j : I) (α : i ⟶ j), D.map α ≫ f j = f i) : I ⥤ Ind C :=
  arrowDiagram f hf ⋙ Limits.im

/-- The image inclusions, as a map into the constant diagram. -/
noncomputable def imageDiagHom
    [SmallCategory C] [Abelian C] {I : Type v} [SmallCategory I]
    {D : I ⥤ Ind C} {Q : Ind C}
    (f : ∀ i, D.obj i ⟶ Q)
    (hf : ∀ (i j : I) (α : i ⟶ j), D.map α ≫ f j = f i) :
    imageDiag f hf ⟶ (Functor.const I).obj Q where
  app i := image.ι (f i)
  naturality _ _ α := image.map_ι ((arrowDiagram f hf).map α)

/-- The map from the colimit of the images to the common target. -/
noncomputable def imageColimitDesc
    [SmallCategory C] [Abelian C] {I : Type v} [SmallCategory I]
    {D : I ⥤ Ind C} {Q : Ind C}
    [IsFiltered I]
    (f : ∀ i, D.obj i ⟶ Q)
    (hf : ∀ (i j : I) (α : i ⟶ j), D.map α ≫ f j = f i) :
    colimit (imageDiag f hf) ⟶ Q :=
  colimit.desc (imageDiag f hf) (Cocone.mk Q (imageDiagHom f hf))

theorem ι_imageColimitDesc
    [SmallCategory C] [Abelian C] {I : Type v} [SmallCategory I]
    {D : I ⥤ Ind C} {Q : Ind C}
    [IsFiltered I] (f : ∀ i, D.obj i ⟶ Q)
    (hf : ∀ (i j : I) (α : i ⟶ j), D.map α ≫ f j = f i) (i : I) :
    colimit.ι (imageDiag f hf) i ≫ imageColimitDesc f hf =
      image.ι (f i) :=
  colimit.ι_desc _ i

/-- **The images of a jointly epimorphic filtered family exhaust
their target.**  The map from the colimit of the images is a
monomorphism because filtered colimits are exact in the
ind-completion, and an epimorphism because every member of the family
factors through its image. -/
theorem exists_iso_colimit_imageDiag
    [SmallCategory C] [Abelian C] {I : Type v} [SmallCategory I]
    {D : I ⥤ Ind C} {Q : Ind C}
    [IsFiltered I]
    (f : ∀ i, D.obj i ⟶ Q)
    (hf : ∀ (i j : I) (α : i ⟶ j), D.map α ≫ f j = f i)
    (hepi : ∀ {T : Ind C} (a b : Q ⟶ T),
      (∀ i, f i ≫ a = f i ≫ b) → a = b) :
    Nonempty (Q ≅ colimit (imageDiag f hf)) := by
  haveI : ∀ i : I, Mono ((imageDiagHom f hf).app i) := fun i =>
    inferInstanceAs (Mono (image.ι (f i)))
  haveI : Mono (imageDiagHom f hf) := NatTrans.mono_of_mono_app _
  haveI : Mono (imageColimitDesc f hf) :=
    colim.map_mono' (imageDiagHom f hf) (colimit.isColimit _)
      (isColimitConstCocone I Q) (imageColimitDesc f hf)
      (fun j => (ι_imageColimitDesc f hf j).trans
        (Category.comp_id _).symm)
  haveI : Epi (imageColimitDesc f hf) := by
    refine ⟨fun a b hab => hepi a b (fun i => ?_)⟩
    have h1 : (colimit.ι (imageDiag f hf) i ≫
          imageColimitDesc f hf) ≫ a =
        (colimit.ι (imageDiag f hf) i ≫
          imageColimitDesc f hf) ≫ b :=
      (Category.assoc _ _ _).trans
        ((whisker_eq _ hab).trans (Category.assoc _ _ _).symm)
    have h2 : image.ι (f i) ≫ a = image.ι (f i) ≫ b :=
      ((eq_whisker (ι_imageColimitDesc f hf i).symm a).trans h1).trans
        (eq_whisker (ι_imageColimitDesc f hf i) b)
    exact ((eq_whisker (image.fac (f i)).symm a).trans
      ((Category.assoc _ _ _).trans ((whisker_eq _ h2).trans
        (Category.assoc _ _ _).symm))).trans
      (eq_whisker (image.fac (f i)) b)
  haveI : IsIso (imageColimitDesc f hf) := isIso_of_mono_of_epi _
  exact ⟨(asIso (imageColimitDesc f hf)).symm⟩

end ImageDiagram

/-! ## The quotient of a countably presented ind-object -/

section Quotient

variable {C : Type v}

/-- The stages of a presentation of `Z`, followed by a map out of
`Z`. -/
noncomputable def quotientStage
    [SmallCategory C] {I : Type v} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ Ind C} {Z : Ind C} {Q : Ind C}
    (e : Z ≅ colimit D) (p : Z ⟶ Q)
    (i : I) : D.obj i ⟶ Q :=
  colimit.ι D i ≫ e.inv ≫ p

/-- The stages are compatible with the structural maps of the
presentation. -/
theorem quotientStage_comp
    [SmallCategory C] {I : Type v} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ Ind C} {Z : Ind C} {Q : Ind C}
    (e : Z ≅ colimit D) (p : Z ⟶ Q) (i j : I)
    (α : i ⟶ j) :
    D.map α ≫ quotientStage e p j = quotientStage e p i := by
  show D.map α ≫ colimit.ι D j ≫ e.inv ≫ p =
    colimit.ι D i ≫ e.inv ≫ p
  rw [← Category.assoc, colimit.w]

/-- **The stages of a presentation, followed by an epimorphism, are
jointly epimorphic.** -/
theorem quotientStage_jointly_epi
    [SmallCategory C] {I : Type v} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ Ind C} {Z : Ind C} {Q : Ind C}
    (e : Z ≅ colimit D) (p : Z ⟶ Q)
    [Epi p] {T : Ind C} (a b : Q ⟶ T)
    (h : ∀ i, quotientStage e p i ≫ a = quotientStage e p i ≫ b) :
    a = b := by
  refine (cancel_epi p).mp ((cancel_epi e.inv).mp
    (colimit.hom_ext (fun i => ?_)))
  calc colimit.ι D i ≫ e.inv ≫ p ≫ a
      = colimit.ι D i ≫ (e.inv ≫ p) ≫ a :=
        whisker_eq _ (Category.assoc _ _ _).symm
    _ = (colimit.ι D i ≫ e.inv ≫ p) ≫ a := (Category.assoc _ _ _).symm
    _ = (colimit.ι D i ≫ e.inv ≫ p) ≫ b := h i
    _ = colimit.ι D i ≫ (e.inv ≫ p) ≫ b := Category.assoc _ _ _
    _ = colimit.ι D i ≫ e.inv ≫ p ≫ b :=
        whisker_eq _ (Category.assoc _ _ _)

/-- **A quotient of a countably presented ind-object is countably
presented.**  Finite length makes the images of the stages embedded,
and those images exhaust the quotient. -/
theorem CountablyPresented.of_epi [SmallCategory C] [Abelian C]
    (hlen : ∀ Z : C, ∃ N, LengthLE Z N) {Z Q : Ind C} (p : Z ⟶ Q)
    [Epi p] (h : CountablyPresented Z) : CountablyPresented Q := by
  classical
  obtain ⟨I, hcat, hfil, hcnt, G, ⟨e⟩⟩ := h
  letI := hcat
  letI := hfil
  letI := hcnt
  have hcomp := quotientStage_comp e p
  obtain ⟨eQ⟩ := exists_iso_colimit_imageDiag (quotientStage e p)
    hcomp (fun a b hab => quotientStage_jointly_epi e p a b hab)
  have hemb : ∀ i : I, ∃ V : C,
      Nonempty ((imageDiag (quotientStage e p) hcomp).obj i ≅
        indOf.obj V) := fun i =>
    indImageEmbedded_of_lengthLE hlen (G.obj i) Q (quotientStage e p i)
  choose W hW using hemb
  refine ⟨I, hcat, hfil, hcnt,
    liftEmbedded (imageDiag (quotientStage e p) hcomp) W
      (fun i => (hW i).some), ⟨eQ ≪≫ ?_⟩⟩
  exact (HasColimit.isoOfNatIso (liftEmbeddedIso
    (imageDiag (quotientStage e p) hcomp) W
    (fun i => (hW i).some))).symm

end Quotient

/-! ## The dimension counts

The even component of a countably presented ind-object is a countable
union of even components of embedded objects, hence of at most
countable dimension; the same then holds for every quotient. -/

section Rank

variable {C : Type v}

/-- **A countably presented ind-object has countable even
component**: it is a countable filtered colimit of embedded objects,
each of which has finite dimensional even component by finite
length. -/
theorem rank_hom_unit_le_aleph0_of_presented
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [CategoryTheory.Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [RigidCategory C] [CategoryTheory.Linear ℂ (Ind C)]
    (hu : HasScalarUnit C)
    (hsmul : IndOfLinear C) (hlen : ∀ Z : C, ∃ N : ℕ, LengthLE Z N)
    {Z : Ind C} (h : CountablyPresented Z) :
    Module.rank ℂ (𝟙_ (Ind C) ⟶ Z) ≤ Cardinal.aleph0 := by
  obtain ⟨I, hcat, hfil, hcnt, G, ⟨e⟩⟩ := h
  letI := hcat
  letI := hfil
  letI := hcnt
  refine rank_hom_unit_le_aleph0_of_iso e ?_
  exact rank_hom_unit_colimit_le_aleph0 _ (fun i =>
    rank_hom_unit_indOf_le_aleph0 hu hsmul (hlen (G.obj i)))

/-- **A quotient of a countably presented ind-object has countable
even component.**  This is the form in which the countable descent
consumes `RS.CountablyPresented.of_epi`. -/
theorem rank_hom_unit_le_aleph0_of_epi
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [CategoryTheory.Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [RigidCategory C] [CategoryTheory.Linear ℂ (Ind C)]
    (hu : HasScalarUnit C)
    (hsmul : IndOfLinear C) (hlen : ∀ Z : C, ∃ N : ℕ, LengthLE Z N)
    {Z Q : Ind C} (p : Z ⟶ Q) [Epi p] (h : CountablyPresented Z) :
    Module.rank ℂ (𝟙_ (Ind C) ⟶ Q) ≤ Cardinal.aleph0 :=
  rank_hom_unit_le_aleph0_of_presented hu hsmul hlen
    (CountablyPresented.of_epi hlen p h)

end Rank

end RS
