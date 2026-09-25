/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndTensorExact
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.TensorExact

/-!
# Exactness of the tensor product on ind-objects, (co)equalizer half

Deligne's 2.2, finite-(co)limit half: for a small rigid abelian
monoidal `C` with preadditive tensor, the transported tensor product
of `Ind C` preserves finite colimits *and* finite limits in each
variable.  This closes the gap documented in
`RS.Classical.Deligne.IndTensorExact`, whose additivity results
cover the finite-(co)product halves; what remains, and is proved
here, is preservation of coequalizers and of equalizers.

The route is a two-stage descent from the exactness of the tensor of
`C` itself (`RS.Classical.Deligne.TensorExact`):

* *Embedded stage* (`RS.preservesColimit_parallelPair_tensorLeft_indOf`
  and its limit and right-hand twins): a parallel pair of `Ind C` is
  presented as a filtered colimit of parallel pairs of `C`
  (Mathlib's `IndParallelPairPresentation`), i.e. the pair is
  isomorphic to `parallelPair φ ψ ⋙ Ind.lim I`.  Tensoring by an
  embedded object commutes with `Ind.lim` up to the natural
  isomorphism `RS.indLimCompTensorLeftIso`, built from
  `RS.indOfTensorIso` and its naturality; on the functor category
  side the whiskered `tensorLeft a` preserves (co)equalizers
  pointwise because `tensorLeft a` preserves all (co)limits in the
  rigid `C`, and `Ind.lim` preserves finite limits and colimits.
  Preservation transports along the presentation.
* *Descent stage* (`RS.isIso_post_parallelPair_tensorLeft`,
  `RS.isIso_limitPost_parallelPair_tensorLeft` and twins): for a
  fixed parallel pair, the (co)limit comparison of `tensorLeft A` is
  natural in the tensoring object `A`
  (`RS.whiskerLeftCoeqComparison`/`RS.whiskerLeftEqComparison`),
  between endofunctor-composites that preserve filtered colimits.
  The filtered-descent lemma `RS.isIso_app_of_isIso_indOf` of
  `IndTensorExact` then propagates invertibility from the embedded
  stage to every `A : Ind C`.  For coequalizers the required
  filtered preservation of `colim`-composites is formal; for
  equalizers it is the exactness of filtered colimits in `Ind C`,
  derived here as `RS.preservesColimitsOfShape_parallelPairLim_ind`
  from the type-level commutation of filtered colimits with finite
  limits through the interchange transpose
  `RS.preservesColimitsOfShape_lim` and the inclusion into
  presheaves.

Deliverables, for every `A : Ind C`:

* `RS.tensorLeft_ind_preservesCoequalizers` /
  `RS.tensorRight_ind_preservesCoequalizers` and
  `RS.tensorLeft_ind_preservesEqualizers` /
  `RS.tensorRight_ind_preservesEqualizers` — preservation of
  `WalkingParallelPair` colimits and limits for both tensoring
  functors;
* `RS.tensorLeft_ind_preservesFiniteColimits` /
  `RS.tensorRight_ind_preservesFiniteColimits` — **the tensor of
  `Ind C` is right exact in each variable**;
* `RS.tensorLeft_ind_preservesFiniteLimits` /
  `RS.tensorRight_ind_preservesFiniteLimits` — **and left exact**,
  combining with the additivity of `IndTensorExact`.

The acceptance tests confirm that the cokernel and kernel comparison
isomorphisms of both tensoring functors synthesize.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v

noncomputable section

section CompositeDiagram

universe w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀

variable {J : Type w₁}

/-- Preservation of the colimit of a composed diagram `K ⋙ F` by
`T`, given that `F` preserves the colimit of `K` and the composite
functor `F ⋙ T` does: the colimit cocone of `K ⋙ F` may be taken to
be the image under `F` of the colimit cocone of `K`. -/
lemma preservesColimit_comp_diagram
    [Category.{w₂} J] {𝒜 : Type w₃} [Category.{w₄} 𝒜] {ℬ : Type w₅}
    [Category.{w₆} ℬ] {𝒞 : Type w₇} [Category.{w₈} 𝒞]
    (K : J ⥤ 𝒜) (F : 𝒜 ⥤ ℬ)
    (T : ℬ ⥤ 𝒞) [HasColimit K] [PreservesColimit K F]
    [PreservesColimit K (F ⋙ T)] : PreservesColimit (K ⋙ F) T :=
  preservesColimit_of_preserves_colimit_cocone
    (isColimitOfPreserves F (colimit.isColimit K))
    (isColimitOfPreserves (F ⋙ T) (colimit.isColimit K))

/-- Dual of `RS.preservesColimit_comp_diagram`. -/
lemma preservesLimit_comp_diagram
    [Category.{w₂} J] {𝒜 : Type w₃} [Category.{w₄} 𝒜] {ℬ : Type w₅}
    [Category.{w₆} ℬ] {𝒞 : Type w₇} [Category.{w₈} 𝒞]
    (K : J ⥤ 𝒜) (F : 𝒜 ⥤ ℬ)
    (T : ℬ ⥤ 𝒞) [HasLimit K] [PreservesLimit K F]
    [PreservesLimit K (F ⋙ T)] : PreservesLimit (K ⋙ F) T :=
  preservesLimit_of_preserves_limit_cone
    (isLimitOfPreserves F (limit.isLimit K))
    (isLimitOfPreserves (F ⋙ T) (limit.isLimit K))

end CompositeDiagram

section InterchangeBridge

universe x₁ x₂ x₃ x₄ x₅ x₆

variable {J : Type x₁}

/-- Transpose of the interchange property, flipped-diagram form: if
`K`-indexed colimits preserve `J`-limits, the `J`-limit functor
preserves the colimit of `G.flip` for any bifunctor `G`.  The
colimit comparison is identified with the canonical interchange
isomorphism `Limits.colimitLimitIso`. -/
lemma preservesColimit_flip_lim
    [Category.{x₂} J] {K : Type x₃} [Category.{x₄} K] {𝒟 : Type x₅}
    [Category.{x₆} 𝒟] [HasLimitsOfShape J 𝒟] [HasColimitsOfShape K 𝒟]
    [PreservesLimitsOfShape J (colim : (K ⥤ 𝒟) ⥤ 𝒟)]
    (G : J ⥤ K ⥤ 𝒟) :
    PreservesColimit G.flip (lim : (J ⥤ 𝒟) ⥤ 𝒟) := by
  have key : colimit.post G.flip lim =
      (HasColimit.isoOfNatIso (limitIsoFlipCompLim G).symm).hom ≫
        (colimitLimitIso G).hom := by
    apply colimit.hom_ext
    intro a
    apply limit.hom_ext
    intro b
    have hL :
        (colimit.ι (G.flip ⋙ lim) a ≫ colimit.post G.flip lim) ≫
            limit.π (colimit G.flip) b =
          limit.π (G.flip.obj a) b ≫ (colimit.ι G.flip a).app b :=
      (congrArg (fun t => t ≫ limit.π (colimit G.flip) b)
          (colimit.ι_post G.flip lim a)).trans
        (limMap_π (colimit.ι G.flip a) b)
    have hR :
        (colimit.ι (G.flip ⋙ lim) a ≫
            (HasColimit.isoOfNatIso (limitIsoFlipCompLim G).symm).hom ≫
              (colimitLimitIso G).hom) ≫ limit.π (colimit G.flip) b =
          limit.π (G.flip.obj a) b ≫
            (colimit.ι G.flip a).app b := by
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun t => colimit.ι (G.flip ⋙ lim) a ≫ t)
        (Category.assoc _ _ _)).trans ?_
      refine (HasColimit.ι_isoOfNatIso_hom_assoc
        (limitIsoFlipCompLim G).symm a _).trans ?_
      refine (congrArg
        (fun t => (limitIsoFlipCompLim G).symm.hom.app a ≫ t)
        (ι_colimitLimitIso_limit_π G a b)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      apply congrArg (fun t => t ≫ (colimit.ι G.flip a).app b)
      simp [limitIsoFlipCompLim, Category.assoc]
    exact hL.trans hR.symm
  have : IsIso (colimit.post G.flip lim) := by
    rw [key]
    exact IsIso.comp_isIso
  exact preservesColimit_of_isIso_post _ _

/-- Transpose of the interchange property: if `K`-indexed colimits
preserve `J`-limits, then the `J`-limit functor preserves
`K`-colimits. -/
lemma preservesColimitsOfShape_lim
    [Category.{x₂} J] {K : Type x₃} [Category.{x₄} K] {𝒟 : Type x₅}
    [Category.{x₆} 𝒟] [HasLimitsOfShape J 𝒟] [HasColimitsOfShape K 𝒟]
    [PreservesLimitsOfShape J (colim : (K ⥤ 𝒟) ⥤ 𝒟)] :
    PreservesColimitsOfShape K (lim : (J ⥤ 𝒟) ⥤ 𝒟) where
  preservesColimit {D} := preservesColimit_flip_lim D.flip

end InterchangeBridge

variable {C : Type v}

section IndLimTensor

/-- The embedding-tensor comparison as a natural isomorphism, left
version: composing the embedding with left tensoring by an embedded
object is left tensoring in `C` followed by the embedding. -/
def indOfCompTensorLeftIso [SmallCategory C] [MonoidalCategory C]
    (a : C) :
    indOf ⋙ tensorLeft (indOf.obj a) ≅
      tensorLeft a ⋙ (indOf : C ⥤ Ind C) :=
  NatIso.ofComponents (fun x => indOfTensorIso a x)
    (fun {_ _} g => indOfTensorIso_hom_natural_right a g)

/-- The embedding-tensor comparison as a natural isomorphism, right
version. -/
def indOfCompTensorRightIso [SmallCategory C] [MonoidalCategory C]
    (a : C) :
    indOf ⋙ tensorRight (indOf.obj a) ≅
      tensorRight a ⋙ (indOf : C ⥤ Ind C) :=
  NatIso.ofComponents (fun x => indOfTensorIso x a)
    (fun {_ _} g => indOfTensorIso_hom_natural_left g a)

/-- Left tensoring by an embedded object commutes with `Ind.lim`:
the composite `Ind.lim I ⋙ tensorLeft (indOf.obj a)` is the
whiskering of `tensorLeft a` followed by `Ind.lim I`.  The chain
mirrors Mathlib's `Ind.limCompInclusion`, with the embedded-tensor
isomorphism in place of `Ind.yonedaCompInclusion`. -/
def indLimCompTensorLeftIso [SmallCategory C] [MonoidalCategory C]
    (a : C) (I : Type v) [SmallCategory I]
    [IsFiltered I] :
    Ind.lim I ⋙ tensorLeft (indOf.obj a) ≅
      (Functor.whiskeringRight I C C).obj (tensorLeft a) ⋙
        Ind.lim I := calc
  Ind.lim I ⋙ tensorLeft (indOf.obj a)
      ≅ (Functor.whiskeringRight I C (Ind C)).obj indOf ⋙
          (colim ⋙ tensorLeft (indOf.obj a)) :=
      Functor.associator _ _ _
  _ ≅ (Functor.whiskeringRight I C (Ind C)).obj indOf ⋙
        ((Functor.whiskeringRight I (Ind C) (Ind C)).obj
            (tensorLeft (indOf.obj a)) ⋙ colim) :=
      Functor.isoWhiskerLeft _ (preservesColimitNatIso _)
  _ ≅ ((Functor.whiskeringRight I C (Ind C)).obj indOf ⋙
        (Functor.whiskeringRight I (Ind C) (Ind C)).obj
          (tensorLeft (indOf.obj a))) ⋙ colim :=
      (Functor.associator _ _ _).symm
  _ ≅ (Functor.whiskeringRight I C (Ind C)).obj
        (indOf ⋙ tensorLeft (indOf.obj a)) ⋙ colim :=
      Functor.isoWhiskerRight
        (Functor.whiskeringRightObjCompIso _ _) colim
  _ ≅ (Functor.whiskeringRight I C (Ind C)).obj
        (tensorLeft a ⋙ indOf) ⋙ colim :=
      Functor.isoWhiskerRight
        ((Functor.whiskeringRight I C (Ind C)).mapIso
          (indOfCompTensorLeftIso a)) colim
  _ ≅ ((Functor.whiskeringRight I C C).obj (tensorLeft a) ⋙
        (Functor.whiskeringRight I C (Ind C)).obj indOf) ⋙ colim :=
      Functor.isoWhiskerRight
        (Functor.whiskeringRightObjCompIso _ _).symm colim
  _ ≅ (Functor.whiskeringRight I C C).obj (tensorLeft a) ⋙
        Ind.lim I :=
      Functor.associator _ _ _

/-- Right tensoring by an embedded object commutes with
`Ind.lim`. -/
def indLimCompTensorRightIso [SmallCategory C] [MonoidalCategory C]
    (a : C) (I : Type v) [SmallCategory I]
    [IsFiltered I] :
    Ind.lim I ⋙ tensorRight (indOf.obj a) ≅
      (Functor.whiskeringRight I C C).obj (tensorRight a) ⋙
        Ind.lim I := calc
  Ind.lim I ⋙ tensorRight (indOf.obj a)
      ≅ (Functor.whiskeringRight I C (Ind C)).obj indOf ⋙
          (colim ⋙ tensorRight (indOf.obj a)) :=
      Functor.associator _ _ _
  _ ≅ (Functor.whiskeringRight I C (Ind C)).obj indOf ⋙
        ((Functor.whiskeringRight I (Ind C) (Ind C)).obj
            (tensorRight (indOf.obj a)) ⋙ colim) :=
      Functor.isoWhiskerLeft _ (preservesColimitNatIso _)
  _ ≅ ((Functor.whiskeringRight I C (Ind C)).obj indOf ⋙
        (Functor.whiskeringRight I (Ind C) (Ind C)).obj
          (tensorRight (indOf.obj a))) ⋙ colim :=
      (Functor.associator _ _ _).symm
  _ ≅ (Functor.whiskeringRight I C (Ind C)).obj
        (indOf ⋙ tensorRight (indOf.obj a)) ⋙ colim :=
      Functor.isoWhiskerRight
        (Functor.whiskeringRightObjCompIso _ _) colim
  _ ≅ (Functor.whiskeringRight I C (Ind C)).obj
        (tensorRight a ⋙ indOf) ⋙ colim :=
      Functor.isoWhiskerRight
        ((Functor.whiskeringRight I C (Ind C)).mapIso
          (indOfCompTensorRightIso a)) colim
  _ ≅ ((Functor.whiskeringRight I C C).obj (tensorRight a) ⋙
        (Functor.whiskeringRight I C (Ind C)).obj indOf) ⋙ colim :=
      Functor.isoWhiskerRight
        (Functor.whiskeringRightObjCompIso _ _).symm colim
  _ ≅ (Functor.whiskeringRight I C C).obj (tensorRight a) ⋙
        Ind.lim I :=
      Functor.associator _ _ _

end IndLimTensor

section EmbeddedBase

/-- Embedded stage, left version: left tensoring by an embedded
object preserves the colimit of every parallel pair of `Ind C`.  The
pair is presented as a filtered colimit of parallel pairs of `C`;
tensoring commutes with the presentation by
`RS.indLimCompTensorLeftIso`, and on the functor-category side the
whiskered `tensorLeft a` preserves coequalizers pointwise since the
tensor of the rigid `C` is exact. -/
lemma preservesColimit_parallelPair_tensorLeft_indOf
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    (a : C)
    {X Y : Ind C} (f g : X ⟶ Y) :
    PreservesColimit (parallelPair f g) (tensorLeft (indOf.obj a)) := by
  obtain ⟨P⟩ := nonempty_indParallelPairPresentation
    (Ind.isIndObject_inclusion_obj X) (Ind.isIndObject_inclusion_obj Y)
    ((Ind.inclusion C).map f) ((Ind.inclusion C).map g)
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft a) :=
    preservesSmallestColimits_of_preservesColimits _
  have : PreservesColimit (parallelPair P.φ P.ψ)
      (Ind.lim P.I ⋙ tensorLeft (indOf.obj a)) :=
    preservesColimit_of_natIso _ (indLimCompTensorLeftIso a P.I).symm
  have : PreservesColimit (parallelPair P.φ P.ψ ⋙ Ind.lim P.I)
      (tensorLeft (indOf.obj a)) :=
    preservesColimit_comp_diagram _ _ _
  exact preservesColimit_of_iso_diagram _
    P.parallelPairIsoParallelPairCompIndYoneda.symm

/-- Embedded stage for limits, left version: left tensoring by an
embedded object preserves the limit of every parallel pair of
`Ind C` — the dual of the coequalizer argument, using that
`Ind.lim` preserves finite limits and that the tensor of the rigid
`C` is left exact. -/
lemma preservesLimit_parallelPair_tensorLeft_indOf
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    (a : C)
    {X Y : Ind C} (f g : X ⟶ Y) :
    PreservesLimit (parallelPair f g) (tensorLeft (indOf.obj a)) := by
  obtain ⟨P⟩ := nonempty_indParallelPairPresentation
    (Ind.isIndObject_inclusion_obj X) (Ind.isIndObject_inclusion_obj Y)
    ((Ind.inclusion C).map f) ((Ind.inclusion C).map g)
  have : PreservesLimitsOfSize.{0, 0} (tensorLeft a) :=
    preservesSmallestLimits_of_preservesLimits _
  have : PreservesLimit (parallelPair P.φ P.ψ)
      (Ind.lim P.I ⋙ tensorLeft (indOf.obj a)) :=
    preservesLimit_of_natIso _ (indLimCompTensorLeftIso a P.I).symm
  have : PreservesLimit (parallelPair P.φ P.ψ ⋙ Ind.lim P.I)
      (tensorLeft (indOf.obj a)) :=
    preservesLimit_comp_diagram _ _ _
  exact preservesLimit_of_iso_diagram _
    P.parallelPairIsoParallelPairCompIndYoneda.symm

/-- Embedded stage for limits, right version. -/
lemma preservesLimit_parallelPair_tensorRight_indOf
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    (a : C)
    {X Y : Ind C} (f g : X ⟶ Y) :
    PreservesLimit (parallelPair f g) (tensorRight (indOf.obj a)) := by
  obtain ⟨P⟩ := nonempty_indParallelPairPresentation
    (Ind.isIndObject_inclusion_obj X) (Ind.isIndObject_inclusion_obj Y)
    ((Ind.inclusion C).map f) ((Ind.inclusion C).map g)
  have : PreservesLimitsOfSize.{0, 0} (tensorRight a) :=
    preservesSmallestLimits_of_preservesLimits _
  have : PreservesLimit (parallelPair P.φ P.ψ)
      (Ind.lim P.I ⋙ tensorRight (indOf.obj a)) :=
    preservesLimit_of_natIso _ (indLimCompTensorRightIso a P.I).symm
  have : PreservesLimit (parallelPair P.φ P.ψ ⋙ Ind.lim P.I)
      (tensorRight (indOf.obj a)) :=
    preservesLimit_comp_diagram _ _ _
  exact preservesLimit_of_iso_diagram _
    P.parallelPairIsoParallelPairCompIndYoneda.symm

/-- Embedded stage, right version. -/
lemma preservesColimit_parallelPair_tensorRight_indOf
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    (a : C)
    {X Y : Ind C} (f g : X ⟶ Y) :
    PreservesColimit (parallelPair f g) (tensorRight (indOf.obj a)) := by
  obtain ⟨P⟩ := nonempty_indParallelPairPresentation
    (Ind.isIndObject_inclusion_obj X) (Ind.isIndObject_inclusion_obj Y)
    ((Ind.inclusion C).map f) ((Ind.inclusion C).map g)
  have : PreservesColimitsOfSize.{0, 0} (tensorRight a) :=
    preservesSmallestColimits_of_preservesColimits _
  have : PreservesColimit (parallelPair P.φ P.ψ)
      (Ind.lim P.I ⋙ tensorRight (indOf.obj a)) :=
    preservesColimit_of_natIso _ (indLimCompTensorRightIso a P.I).symm
  have : PreservesColimit (parallelPair P.φ P.ψ ⋙ Ind.lim P.I)
      (tensorRight (indOf.obj a)) :=
    preservesColimit_comp_diagram _ _ _
  exact preservesColimit_of_iso_diagram _
    P.parallelPairIsoParallelPairCompIndYoneda.symm

end EmbeddedBase

section CoequalizerDescent

/-- The parallel pair `(A ◁ f, A ◁ g)` as a functor of the tensoring
object `A`.  The `@[reducible]` marking is deliberate: the object
field must reduce at instance transparency for the `show`-retyped
colimit proofs below to be stateable. -/
@[reducible]
def whiskerLeftPairFunctor
    [SmallCategory C] [MonoidalCategory C] {X : Ind C} {Y : Ind C}
    (f g : X ⟶ Y) :
    Ind C ⥤ WalkingParallelPair ⥤ Ind C where
  obj A := parallelPair f g ⋙ tensorLeft A
  map {A B} u :=
    { app := fun k => u ▷ (parallelPair f g).obj k
      naturality := fun _ _ h =>
        whisker_exchange u ((parallelPair f g).map h) }
  map_id A := by
    ext k
    exact MonoidalCategory.id_whiskerRight A ((parallelPair f g).obj k)
  map_comp {A B D} u v := by
    ext k
    exact MonoidalCategory.comp_whiskerRight u v
      ((parallelPair f g).obj k)

/-- The parallel pair `(f ▷ A, g ▷ A)` as a functor of the tensoring
object `A`. -/
@[reducible]
def whiskerRightPairFunctor
    [SmallCategory C] [MonoidalCategory C] {X : Ind C} {Y : Ind C}
    (f g : X ⟶ Y) :
    Ind C ⥤ WalkingParallelPair ⥤ Ind C where
  obj A := parallelPair f g ⋙ tensorRight A
  map {A B} u :=
    { app := fun k => (parallelPair f g).obj k ◁ u
      naturality := fun _ _ h =>
        (whisker_exchange ((parallelPair f g).map h) u).symm }
  map_id A := by
    ext k
    exact MonoidalCategory.whiskerLeft_id ((parallelPair f g).obj k) A
  map_comp {A B D} u v := by
    ext k
    exact MonoidalCategory.whiskerLeft_comp
      ((parallelPair f g).obj k) u v

/-- Evaluating `RS.whiskerLeftPairFunctor` at a stage of the walking
parallel pair gives right tensoring by the corresponding object. -/
def whiskerLeftPairFunctorEvalIso
    [SmallCategory C] [MonoidalCategory C] {X : Ind C} {Y : Ind C}
    (f g : X ⟶ Y)
    (k : WalkingParallelPair) :
    whiskerLeftPairFunctor f g ⋙ (evaluation _ _).obj k ≅
      tensorRight ((parallelPair f g).obj k) :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun u => by
      change u ▷ (parallelPair f g).obj k ≫ 𝟙 _ =
        𝟙 _ ≫ u ▷ (parallelPair f g).obj k
      rw [Category.comp_id, Category.id_comp])

/-- Evaluating `RS.whiskerRightPairFunctor` at a stage gives left
tensoring by the corresponding object. -/
def whiskerRightPairFunctorEvalIso
    [SmallCategory C] [MonoidalCategory C] {X : Ind C} {Y : Ind C}
    (f g : X ⟶ Y)
    (k : WalkingParallelPair) :
    whiskerRightPairFunctor f g ⋙ (evaluation _ _).obj k ≅
      tensorLeft ((parallelPair f g).obj k) :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun u => by
      change (parallelPair f g).obj k ◁ u ≫ 𝟙 _ =
        𝟙 _ ≫ (parallelPair f g).obj k ◁ u
      rw [Category.comp_id, Category.id_comp])

/-- The pair functor preserves filtered colimits, pointwise. -/
lemma preservesFilteredColimits_whiskerLeftPairFunctor
    [SmallCategory C] [MonoidalCategory C] {X : Ind C} {Y : Ind C}
    (f g : X ⟶ Y) :
    PreservesFilteredColimits (whiskerLeftPairFunctor f g) where
  preserves_filtered_colimits _ _ _ :=
    preservesColimitsOfShape_of_evaluation _ _ fun k =>
      preservesColimitsOfShape_of_natIso
        (whiskerLeftPairFunctorEvalIso f g k).symm

/-- The right-hand pair functor preserves filtered colimits. -/
lemma preservesFilteredColimits_whiskerRightPairFunctor
    [SmallCategory C] [MonoidalCategory C] {X : Ind C} {Y : Ind C}
    (f g : X ⟶ Y) :
    PreservesFilteredColimits (whiskerRightPairFunctor f g) where
  preserves_filtered_colimits _ _ _ :=
    preservesColimitsOfShape_of_evaluation _ _ fun k =>
      preservesColimitsOfShape_of_natIso
        (whiskerRightPairFunctorEvalIso f g k).symm

/-- The coequalizer comparison for left tensoring, naturally in the
tensoring object: at `A` it is the canonical morphism from the
colimit of the pair `(A ◁ f, A ◁ g)` to `A ⊗ coeq (f, g)`. -/
def whiskerLeftCoeqComparison
    [SmallCategory C] [MonoidalCategory C] [Abelian C] {X : Ind C}
    {Y : Ind C}
    (f g : X ⟶ Y) :
    whiskerLeftPairFunctor f g ⋙ colim ⟶
      tensorRight (colimit (parallelPair f g)) where
  app A := colimit.post (parallelPair f g) (tensorLeft A)
  naturality {A B} u := by
    change colimMap ((whiskerLeftPairFunctor f g).map u) ≫
        colimit.post (parallelPair f g) (tensorLeft B) =
      colimit.post (parallelPair f g) (tensorLeft A) ≫
        u ▷ colimit (parallelPair f g)
    apply colimit.hom_ext
    intro k
    rw [ι_colimMap_assoc]
    change ((whiskerLeftPairFunctor f g).map u).app k ≫
        colimit.ι (parallelPair f g ⋙ tensorLeft B) k ≫
          colimit.post (parallelPair f g) (tensorLeft B) =
      colimit.ι (parallelPair f g ⋙ tensorLeft A) k ≫
        colimit.post (parallelPair f g) (tensorLeft A) ≫
          u ▷ colimit (parallelPair f g)
    rw [colimit.ι_post, colimit.ι_post_assoc]
    change u ▷ (parallelPair f g).obj k ≫
        (B ◁ colimit.ι (parallelPair f g) k) =
      (A ◁ colimit.ι (parallelPair f g) k) ≫
        u ▷ colimit (parallelPair f g)
    exact (whisker_exchange u (colimit.ι (parallelPair f g) k)).symm

/-- The coequalizer comparison for right tensoring, naturally in the
tensoring object. -/
def whiskerRightCoeqComparison
    [SmallCategory C] [MonoidalCategory C] [Abelian C] {X : Ind C}
    {Y : Ind C}
    (f g : X ⟶ Y) :
    whiskerRightPairFunctor f g ⋙ colim ⟶
      tensorLeft (colimit (parallelPair f g)) where
  app A := colimit.post (parallelPair f g) (tensorRight A)
  naturality {A B} u := by
    change colimMap ((whiskerRightPairFunctor f g).map u) ≫
        colimit.post (parallelPair f g) (tensorRight B) =
      colimit.post (parallelPair f g) (tensorRight A) ≫
        colimit (parallelPair f g) ◁ u
    apply colimit.hom_ext
    intro k
    rw [ι_colimMap_assoc]
    change ((whiskerRightPairFunctor f g).map u).app k ≫
        colimit.ι (parallelPair f g ⋙ tensorRight B) k ≫
          colimit.post (parallelPair f g) (tensorRight B) =
      colimit.ι (parallelPair f g ⋙ tensorRight A) k ≫
        colimit.post (parallelPair f g) (tensorRight A) ≫
          colimit (parallelPair f g) ◁ u
    rw [colimit.ι_post, colimit.ι_post_assoc]
    change (parallelPair f g).obj k ◁ u ≫
        (colimit.ι (parallelPair f g) k ▷ B) =
      (colimit.ι (parallelPair f g) k ▷ A) ≫
        colimit (parallelPair f g) ◁ u
    exact whisker_exchange (colimit.ι (parallelPair f g) k) u

/-- Descent stage, left version: the colimit comparison of any
parallel pair under left tensoring is invertible, for every
tensoring ind-object.  Filtered descent from the embedded stage. -/
lemma isIso_post_parallelPair_tensorLeft
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    {X : Ind C} {Y : Ind C}
    (A : Ind C) (f g : X ⟶ Y) :
    IsIso (colimit.post (parallelPair f g) (tensorLeft A)) := by
  have : PreservesFilteredColimits (whiskerLeftPairFunctor f g) :=
    preservesFilteredColimits_whiskerLeftPairFunctor f g
  have : PreservesColimitsOfSize.{v, v}
      (colim : (WalkingParallelPair ⥤ Ind C) ⥤ Ind C) :=
    colimConstAdj.leftAdjoint_preservesColimits
  have : PreservesFilteredColimits
      (whiskerLeftPairFunctor f g ⋙ colim) :=
    ⟨fun _ _ _ => inferInstance⟩
  have h := isIso_app_of_isIso_indOf (whiskerLeftCoeqComparison f g)
    (fun c => by
      have := preservesColimit_parallelPair_tensorLeft_indOf c f g
      exact inferInstanceAs (IsIso (colimit.post (parallelPair f g)
        (tensorLeft (indOf.obj c))))) A
  exact h

/-- Descent stage, right version. -/
lemma isIso_post_parallelPair_tensorRight
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    {X : Ind C} {Y : Ind C}
    (A : Ind C) (f g : X ⟶ Y) :
    IsIso (colimit.post (parallelPair f g) (tensorRight A)) := by
  have : PreservesFilteredColimits (whiskerRightPairFunctor f g) :=
    preservesFilteredColimits_whiskerRightPairFunctor f g
  have : PreservesColimitsOfSize.{v, v}
      (colim : (WalkingParallelPair ⥤ Ind C) ⥤ Ind C) :=
    colimConstAdj.leftAdjoint_preservesColimits
  have : PreservesFilteredColimits
      (whiskerRightPairFunctor f g ⋙ colim) :=
    ⟨fun _ _ _ => inferInstance⟩
  have h := isIso_app_of_isIso_indOf (whiskerRightCoeqComparison f g)
    (fun c => by
      have := preservesColimit_parallelPair_tensorRight_indOf c f g
      exact inferInstanceAs (IsIso (colimit.post (parallelPair f g)
        (tensorRight (indOf.obj c))))) A
  exact h

end CoequalizerDescent

section Coequalizers

/-- **Left tensoring on `Ind C` preserves coequalizers.** -/
instance tensorLeft_ind_preservesCoequalizers
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    (A : Ind C) :
    PreservesColimitsOfShape WalkingParallelPair (tensorLeft A) where
  preservesColimit {K} := by
    have := isIso_post_parallelPair_tensorLeft A
      (K.map WalkingParallelPairHom.left)
      (K.map WalkingParallelPairHom.right)
    have : PreservesColimit
        (parallelPair (K.map WalkingParallelPairHom.left)
          (K.map WalkingParallelPairHom.right)) (tensorLeft A) :=
      preservesColimit_of_isIso_post _ _
    exact preservesColimit_of_iso_diagram _
      (diagramIsoParallelPair K).symm

/-- **Right tensoring on `Ind C` preserves coequalizers.** -/
instance tensorRight_ind_preservesCoequalizers
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    (A : Ind C) :
    PreservesColimitsOfShape WalkingParallelPair (tensorRight A) where
  preservesColimit {K} := by
    have := isIso_post_parallelPair_tensorRight A
      (K.map WalkingParallelPairHom.left)
      (K.map WalkingParallelPairHom.right)
    have : PreservesColimit
        (parallelPair (K.map WalkingParallelPairHom.left)
          (K.map WalkingParallelPairHom.right)) (tensorRight A) :=
      preservesColimit_of_isIso_post _ _
    exact preservesColimit_of_iso_diagram _
      (diagramIsoParallelPair K).symm

end Coequalizers

section EqualizerDescent

/-- Filtered colimits commute with `WalkingParallelPair`-limits in
`Ind C`: the parallel-pair limit functor preserves filtered
colimits.  The property holds for types, lifts to presheaves
pointwise, transposes through `RS.preservesColimitsOfShape_lim`,
and transports to `Ind C` along the inclusion, which creates the
limits and preserves the filtered colimits involved. -/
lemma preservesColimitsOfShape_parallelPairLim_ind [SmallCategory C] [Abelian C]
    (I : Type v) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I
      (lim : (WalkingParallelPair ⥤ Ind C) ⥤ Ind C) := by
  have hlim : PreservesColimitsOfShape I
      (lim : (WalkingParallelPair ⥤ (Cᵒᵖ ⥤ Type v)) ⥤ _) :=
    preservesColimitsOfShape_lim
  have h₁ : PreservesColimitsOfShape I
      ((lim : (WalkingParallelPair ⥤ Ind C) ⥤ Ind C) ⋙
        Ind.inclusion C) := by
    exact preservesColimitsOfShape_of_natIso
      (preservesLimitNatIso (Ind.inclusion C)).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves _
    (Ind.inclusion C)

/-- The equalizer comparison for left tensoring, naturally in the
tensoring object: at `A` it is the canonical morphism from
`A ⊗ lim (f, g)` to the limit of the pair `(A ◁ f, A ◁ g)`. -/
def whiskerLeftEqComparison
    [SmallCategory C] [MonoidalCategory C] [Abelian C] {X : Ind C}
    {Y : Ind C}
    (f g : X ⟶ Y) :
    tensorRight (limit (parallelPair f g)) ⟶
      whiskerLeftPairFunctor f g ⋙ lim where
  app A := limit.post (parallelPair f g) (tensorLeft A)
  naturality {A B} u := by
    apply limit.hom_ext
    intro k
    have hL :
        ((u ▷ limit (parallelPair f g)) ≫
            limit.post (parallelPair f g) (tensorLeft B)) ≫
          limit.π (parallelPair f g ⋙ tensorLeft B) k =
        (A ◁ limit.π (parallelPair f g) k) ≫
          u ▷ (parallelPair f g).obj k := by
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun t => (u ▷ limit (parallelPair f g)) ≫ t)
        (limit.post_π (parallelPair f g) (tensorLeft B) k)).trans ?_
      exact (whisker_exchange u (limit.π (parallelPair f g) k)).symm
    have hR :
        (limit.post (parallelPair f g) (tensorLeft A) ≫
            limMap ((whiskerLeftPairFunctor f g).map u)) ≫
          limit.π (parallelPair f g ⋙ tensorLeft B) k =
        (A ◁ limit.π (parallelPair f g) k) ≫
          u ▷ (parallelPair f g).obj k := by
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg
        (fun t => limit.post (parallelPair f g) (tensorLeft A) ≫ t)
        (limMap_π ((whiskerLeftPairFunctor f g).map u) k)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      exact congrArg
        (fun t => t ≫ ((whiskerLeftPairFunctor f g).map u).app k)
        (limit.post_π (parallelPair f g) (tensorLeft A) k)
    exact hL.trans hR.symm

/-- The equalizer comparison for right tensoring, naturally in the
tensoring object. -/
def whiskerRightEqComparison
    [SmallCategory C] [MonoidalCategory C] [Abelian C] {X : Ind C}
    {Y : Ind C}
    (f g : X ⟶ Y) :
    tensorLeft (limit (parallelPair f g)) ⟶
      whiskerRightPairFunctor f g ⋙ lim where
  app A := limit.post (parallelPair f g) (tensorRight A)
  naturality {A B} u := by
    apply limit.hom_ext
    intro k
    have hL :
        ((limit (parallelPair f g) ◁ u) ≫
            limit.post (parallelPair f g) (tensorRight B)) ≫
          limit.π (parallelPair f g ⋙ tensorRight B) k =
        (limit.π (parallelPair f g) k ▷ A) ≫
          (parallelPair f g).obj k ◁ u := by
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun t => (limit (parallelPair f g) ◁ u) ≫ t)
        (limit.post_π (parallelPair f g) (tensorRight B) k)).trans ?_
      exact whisker_exchange (limit.π (parallelPair f g) k) u
    have hR :
        (limit.post (parallelPair f g) (tensorRight A) ≫
            limMap ((whiskerRightPairFunctor f g).map u)) ≫
          limit.π (parallelPair f g ⋙ tensorRight B) k =
        (limit.π (parallelPair f g) k ▷ A) ≫
          (parallelPair f g).obj k ◁ u := by
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg
        (fun t => limit.post (parallelPair f g) (tensorRight A) ≫ t)
        (limMap_π ((whiskerRightPairFunctor f g).map u) k)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      exact congrArg
        (fun t => t ≫ ((whiskerRightPairFunctor f g).map u).app k)
        (limit.post_π (parallelPair f g) (tensorRight A) k)
    exact hL.trans hR.symm

/-- Descent stage for limits, left version: the limit comparison of
any parallel pair under left tensoring is invertible, for every
tensoring ind-object. -/
lemma isIso_limitPost_parallelPair_tensorLeft
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    {X : Ind C} {Y : Ind C}
    (A : Ind C)
    (f g : X ⟶ Y) :
    IsIso (limit.post (parallelPair f g) (tensorLeft A)) := by
  have : PreservesFilteredColimits (whiskerLeftPairFunctor f g) :=
    preservesFilteredColimits_whiskerLeftPairFunctor f g
  have : PreservesFilteredColimits
      (whiskerLeftPairFunctor f g ⋙ lim) :=
    ⟨fun I _ _ => by
      have := preservesColimitsOfShape_parallelPairLim_ind (C := C) I
      infer_instance⟩
  have h := isIso_app_of_isIso_indOf (whiskerLeftEqComparison f g)
    (fun c => by
      have := preservesLimit_parallelPair_tensorLeft_indOf c f g
      exact inferInstanceAs (IsIso (limit.post (parallelPair f g)
        (tensorLeft (indOf.obj c))))) A
  exact h

/-- Descent stage for limits, right version. -/
lemma isIso_limitPost_parallelPair_tensorRight
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    {X : Ind C} {Y : Ind C}
    (A : Ind C)
    (f g : X ⟶ Y) :
    IsIso (limit.post (parallelPair f g) (tensorRight A)) := by
  have : PreservesFilteredColimits (whiskerRightPairFunctor f g) :=
    preservesFilteredColimits_whiskerRightPairFunctor f g
  have : PreservesFilteredColimits
      (whiskerRightPairFunctor f g ⋙ lim) :=
    ⟨fun I _ _ => by
      have := preservesColimitsOfShape_parallelPairLim_ind (C := C) I
      infer_instance⟩
  have h := isIso_app_of_isIso_indOf (whiskerRightEqComparison f g)
    (fun c => by
      have := preservesLimit_parallelPair_tensorRight_indOf c f g
      exact inferInstanceAs (IsIso (limit.post (parallelPair f g)
        (tensorRight (indOf.obj c))))) A
  exact h

end EqualizerDescent

section Equalizers

/-- **Left tensoring on `Ind C` preserves equalizers.** -/
instance tensorLeft_ind_preservesEqualizers
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    (A : Ind C) :
    PreservesLimitsOfShape WalkingParallelPair (tensorLeft A) where
  preservesLimit {K} := by
    have := isIso_limitPost_parallelPair_tensorLeft A
      (K.map WalkingParallelPairHom.left)
      (K.map WalkingParallelPairHom.right)
    have : PreservesLimit
        (parallelPair (K.map WalkingParallelPairHom.left)
          (K.map WalkingParallelPairHom.right)) (tensorLeft A) :=
      preservesLimit_of_isIso_post _ _
    exact preservesLimit_of_iso_diagram _
      (diagramIsoParallelPair K).symm

/-- **Right tensoring on `Ind C` preserves equalizers.** -/
instance tensorRight_ind_preservesEqualizers
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    (A : Ind C) :
    PreservesLimitsOfShape WalkingParallelPair (tensorRight A) where
  preservesLimit {K} := by
    have := isIso_limitPost_parallelPair_tensorRight A
      (K.map WalkingParallelPairHom.left)
      (K.map WalkingParallelPairHom.right)
    have : PreservesLimit
        (parallelPair (K.map WalkingParallelPairHom.left)
          (K.map WalkingParallelPairHom.right)) (tensorRight A) :=
      preservesLimit_of_isIso_post _ _
    exact preservesLimit_of_iso_diagram _
      (diagramIsoParallelPair K).symm

end Equalizers

section RightExact

/-- **Deligne 2.2, right-exactness, left version**: left tensoring
on `Ind C` preserves finite colimits — coequalizers by the descent
above, finite coproducts by the additivity of
`RS.Classical.Deligne.IndTensorExact`. -/
instance tensorLeft_ind_preservesFiniteColimits
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    (A : Ind C) :
    PreservesFiniteColimits (tensorLeft A) :=
  preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts
    _

/-- **Deligne 2.2, right-exactness, right version**. -/
instance tensorRight_ind_preservesFiniteColimits
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    (A : Ind C) :
    PreservesFiniteColimits (tensorRight A) :=
  preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts
    _

/-- **Left-exactness, left version**: left tensoring on `Ind C`
preserves finite limits — equalizers by the dual descent, finite
products by additivity.  With the right-exactness above, the tensor
of `Ind C` is exact in each variable. -/
instance tensorLeft_ind_preservesFiniteLimits
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    (A : Ind C) :
    PreservesFiniteLimits (tensorLeft A) :=
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts _

/-- **Left-exactness, right version**. -/
instance tensorRight_ind_preservesFiniteLimits
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    (A : Ind C) :
    PreservesFiniteLimits (tensorRight A) :=
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts _

end RightExact

section AcceptanceTests

/- Instance synthesis is what is being tested; the data is chosen by
colimit machinery, hence `noncomputable`. -/

noncomputable example
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    (A : Ind C) :
    PreservesColimitsOfShape WalkingParallelPair (tensorLeft A) :=
  inferInstance

noncomputable example
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    (A : Ind C) :
    PreservesColimitsOfShape WalkingParallelPair (tensorRight A) :=
  inferInstance

noncomputable example
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    (A : Ind C) :
    PreservesFiniteColimits (tensorLeft A) :=
  inferInstance

noncomputable example
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    (A : Ind C) :
    PreservesFiniteColimits (tensorRight A) :=
  inferInstance

noncomputable example
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    {X Y : Ind C} (h : X ⟶ Y) (A : Ind C) :
    IsIso (cokernelComparison h (tensorLeft A)) :=
  inferInstance

noncomputable example
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    {X Y : Ind C} (h : X ⟶ Y) (A : Ind C) :
    IsIso (cokernelComparison h (tensorRight A)) :=
  inferInstance

noncomputable example
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    (A : Ind C) :
    PreservesFiniteLimits (tensorLeft A) :=
  inferInstance

noncomputable example
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    (A : Ind C) :
    PreservesFiniteLimits (tensorRight A) :=
  inferInstance

noncomputable example
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    {X Y : Ind C} (h : X ⟶ Y) (A : Ind C) :
    IsIso (kernelComparison h (tensorLeft A)) :=
  inferInstance

noncomputable example
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    {X Y : Ind C} (h : X ⟶ Y) (A : Ind C) :
    IsIso (kernelComparison h (tensorRight A)) :=
  inferInstance

end AcceptanceTests

end

end RS
