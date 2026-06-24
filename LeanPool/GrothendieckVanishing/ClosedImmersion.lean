/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent
-/

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Topology.Sheaves.Stalks

/-!
# Closed immersions

This module packages the `TopCat` API for the closed inclusion `closedIncl : TopCat.of s ⟶ X`
and the stalk comparisons needed in the closed-immersion step of Grothendieck vanishing.

Main results:
- `closedIncl_isClosedEmbedding` and `closedIncl_isInducing` record the basic topology of
  the closed inclusion.
- `closedIncl_map_eq_bot_of_le_compl` shows that opens contained in the complement pull back
  to `⊥` on the closed subspace.
- `pushforward_closedIncl_stalk_eq_zero` identifies stalks of a closed-immersion
  pushforward away from the closed subset with zero.
- `closedIncl_pushforward_preservesEpis/Monos` and
  `closedIncl_pushforward_shortExact` package exactness of pushforward along the
  closed inclusion for `AddCommGrpCat`-valued sheaves.
- `stalkFunctor_map_iso_toSheafify` identifies the stalk of sheafification with an isomorphism.
- `closedIncl_counit_isIso` identifies the pushforward-pullback counit for
  presheaves on the closed subspace carrying a sheaf condition.
- `stalkPullbackHom_naturality` is the stalk-level naturality needed to compare the unit with
  the counit isomorphism.
- `closedIncl_unit_stalk_isIso` shows that the adjunction unit is an isomorphism on stalks at
  points of the closed subset.
- `epi_unit_of_closedImmersion` upgrades the adjunction unit to an epi of sheaves.
- `closedImmersionSES` and `closedImmersionSES_shortExact` package the short exact sequence
  `0 → ker(η) → F → i_*(i^*F) → 0` associated to a closed immersion.
-/

open CategoryTheory TopologicalSpace Opposite Limits

universe u

noncomputable section

instance sheafAbelianAddCommGrp (X : TopCat.{u}) :
    Abelian (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (Abelian (CategoryTheory.Sheaf _ _))

namespace TopCat

/-- Closed inclusion `s ↪ X` as a morphism in `TopCat`. -/
def closedIncl {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) : TopCat.of s ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, hs.isClosedEmbedding_subtypeVal.continuous⟩

lemma set_range_closedIncl {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) :
    Set.range (closedIncl hs : s → X) = s := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

lemma closedIncl_isClosedEmbedding {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) :
    Topology.IsClosedEmbedding (closedIncl hs) :=
  hs.isClosedEmbedding_subtypeVal

lemma closedIncl_isInducing {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) :
    Topology.IsInducing (closedIncl hs) :=
  (closedIncl_isClosedEmbedding hs).isInducing

theorem closedIncl_map_eq_bot_of_le_compl {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {U : Opens X} (hU : U ≤ ⟨sᶜ, hs.isOpen_compl⟩) :
    (Opens.map (closedIncl hs)).obj U = ⊥ := by
  apply Opens.ext
  change (closedIncl hs : s → X) ⁻¹' (U : Set X) = (⊥ : Opens (TopCat.of s))
  have hdisj : Disjoint (U : Set X) (Set.range (closedIncl hs : s → X)) := by
    rw [set_range_closedIncl hs]
    exact Set.disjoint_left.mpr fun x hxU hxS ↦ hU hxU hxS
  simpa using (Set.preimage_eq_empty hdisj)

instance closedIncl_stalkPushforward_isIso {X : TopCat.{u}} {s : Set X} {hs : IsClosed s}
    {C : Type*} [Category.{u} C] [HasColimits C]
    {F : (TopCat.of s).Presheaf C} {x : TopCat.of s} :
    IsIso (Presheaf.stalkPushforward C (closedIncl hs) F x) :=
  Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
    C (closedIncl_isInducing hs) F x

lemma opensMap_range_isBasis_of_isInducing {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : Topology.IsInducing f) :
    Opens.IsBasis (Set.range (Opens.map f).obj) := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  refine ⟨U, ?_, hx, le_rfl⟩
  refine ⟨hf.functorObj U, ?_⟩
  simpa using hf.map_functorObj U

lemma opensMap_isCoverDense_of_isInducing {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : Topology.IsInducing f) :
    (Opens.map f).IsCoverDense (Opens.grothendieckTopology X) := by
  rw [TopCat.Opens.coverDense_iff_isBasis]
  exact opensMap_range_isBasis_of_isInducing hf

instance opensMap_isLocallyFull {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (Opens.map f).IsLocallyFull (Opens.grothendieckTopology X) where
  functorPushforward_imageSieve_mem := by
    intro U V i
    rw [Opens.grothendieckTopology]
    intro x hx
    refine ⟨(Opens.map f).obj (U ⊓ V), (Opens.map f).map (Opens.infLELeft U V), ?_, ?_⟩
    · refine ⟨U ⊓ V, Opens.infLELeft U V, 𝟙 _, ?_, by simp⟩
      refine ⟨Opens.infLERight U V, ?_⟩
      exact Subsingleton.elim _ _
    · exact ⟨hx, i.le hx⟩

theorem locallyInjective_stalkFunctor_map_injective
    {C : Type*} [Category.{u} C] [HasColimits C]
    {FC : C → C → Type*} {CC : C → Type u}
    [∀ (X Y : C), FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [PreservesFilteredColimits (forget C)]
    {X : TopCat.{u}} {F G : X.Presheaf C} (T : F ⟶ G)
    [CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) T] :
  ∀ x : X, Function.Injective ((TopCat.Presheaf.stalkFunctor C x).map T) := by
  intro x s t hst
  obtain ⟨U, hxU, sU, rfl⟩ := F.exists_germ_eq s
  obtain ⟨V, hxV, sV, hsV⟩ := F.exists_germ_eq t
  rw [← hsV] at hst ⊢
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hst
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hst
  obtain ⟨W, hxW, iWU, iWV, hEq⟩ := G.germ_eq x hxU hxV _ _ hst
  have hnat (Y : Opens X) (iWY : W ⟶ Y) (sY : CC (F.obj (op Y))) :
      T.app (op W) (F.map iWY.op sY) = G.map iWY.op (T.app (op Y) sY) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, T.naturality]
  have hEq' : T.app (op W) (F.map iWU.op sU) =
      T.app (op W) (F.map iWV.op sV) := by rw [hnat _ iWU, hnat _ iWV]; exact hEq
  have hloc := CategoryTheory.Presheaf.equalizerSieve_mem
    (J := Opens.grothendieckTopology X) (φ := T)
    (x := F.map iWU.op sU) (y := F.map iWV.op sV) hEq'
  rw [Opens.grothendieckTopology] at hloc
  rcases hloc x hxW with ⟨Z, iZW, hEqZ, hxZ⟩
  apply F.germ_ext Z hxZ (iZW ≫ iWU) (iZW ≫ iWV)
  simpa using hEqZ

theorem stalkFunctor_map_iso_toSheafify
    {C : Type*} [Category.{u} C] [HasColimits C]
    {FC : C → C → Type*} {CC : C → Type u}
    [∀ (X Y : C), FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [PreservesFilteredColimits (forget C)]
    [(forget C).ReflectsIsomorphisms]
    {X : TopCat.{u}} [HasWeakSheafify (Opens.grothendieckTopology X) C]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective C]
    (P : X.Presheaf C) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor C x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · exact locallyInjective_stalkFunctor_map_injective
      (T := CategoryTheory.toSheafify (Opens.grothendieckTopology X) P) x
  · have hls : TopCat.Presheaf.IsLocallySurjective
          (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P) := by
        dsimp [TopCat.Presheaf.IsLocallySurjective]; infer_instance
    exact
      ((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
        (T := CategoryTheory.toSheafify (Opens.grothendieckTopology X) P)).mp hls) x

theorem closedIncl_counit_isIso
    {C : Type*} [Category.{u} C]
    {FC : C → C → Type*} {CC : C → Type u}
    [∀ (X Y : C), FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (forget C)]
    [PreservesFilteredColimits (forget C)]
    [(forget C).ReflectsIsomorphisms]
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    (F : TopCat.Sheaf C (TopCat.of s)) :
    IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction C (closedIncl hs)).counit.app
      F) := by
  letI : (Opens.map (closedIncl hs)).IsCoverDense
      (Opens.grothendieckTopology (TopCat.of s)) :=
    opensMap_isCoverDense_of_isInducing (closedIncl_isInducing hs)
  letI : (Opens.map (closedIncl hs)).IsLocallyFull
      (Opens.grothendieckTopology (TopCat.of s)) :=
    opensMap_isLocallyFull (closedIncl hs)
  letI : (Opens.map (closedIncl hs)).IsContinuous
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology (TopCat.of s)) :=
    CategoryTheory.Functor.IsCoverDense.isContinuous
      (J := Opens.grothendieckTopology X)
      (K := Opens.grothendieckTopology (TopCat.of s))
      (G := Opens.map (closedIncl hs))
      (coverPreserving_opens_map (closedIncl hs))
  haveI : (TopCat.Sheaf.pushforward C (closedIncl hs)).Full := by
    change ((Opens.map (closedIncl hs)).sheafPushforwardContinuous C
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology (TopCat.of s))).Full
    infer_instance
  haveI : (TopCat.Sheaf.pushforward C (closedIncl hs)).Faithful := by
    change ((Opens.map (closedIncl hs)).sheafPushforwardContinuous C
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology (TopCat.of s))).Faithful
    infer_instance
  infer_instance

end TopCat

/-- Stalks of a pushforward along a closed inclusion vanish outside the closed set:
    if `x ∉ s`, every element of `stalk(i_*(G), x)` is zero. -/
theorem pushforward_closedIncl_stalk_eq_zero
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {G : TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of s)} (hG : G.IsSheaf)
    {x : X} (hx : x ∉ s)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).obj G)) :
    a = 0 := by
  let Gsh : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s) := ⟨G, hG⟩
  let F' := (TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).obj G
  obtain ⟨U, hxU, sU, rfl⟩ := F'.exists_germ_eq a
  let W : Opens X := U ⊓ ⟨sᶜ, hs.isOpen_compl⟩
  have hW_map : (Opens.map (TopCat.closedIncl hs)).obj W = ⊥ :=
    TopCat.closedIncl_map_eq_bot_of_le_compl (hs := hs) (U := W) inf_le_right
  haveI : Subsingleton (F'.obj (op W)) := AddCommGrpCat.subsingleton_of_isZero (by
    change IsZero (G.obj (op ((Opens.map (TopCat.closedIncl hs)).obj W)))
    rw [hW_map]
    exact Gsh.isTerminalOfEmpty.isZero)
  rw [← TopCat.Presheaf.germ_res_apply F'
    (homOfLE (show W ≤ U from inf_le_left)) x ⟨hxU, hx⟩ sU]
  rw [Subsingleton.eq_zero (ConcreteCategory.hom (F'.map (homOfLE (show W ≤ U from
    inf_le_left)).op) sU)]
  exact map_zero _

/-- Pushforward along a closed immersion preserves epis: if `f : F ⟶ G` is epi in
    presheaves on the closed subspace, then `i_*(f)` is epi in sheaves on the ambient
    space whenever `f` is locally surjective.
    Proof: stalkwise surjectivity (identity on the closed set, zero outside). -/
theorem epi_pushforward_map_closedIncl_of_locallySurjective
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {F G : TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of s)}
    (hF : F.IsSheaf) (hG : G.IsSheaf)
    (f : F ⟶ G)
    (hf_loc : TopCat.Presheaf.IsLocallySurjective f) :
    Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map (show
        (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) ⟶
          (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) from
            ObjectProperty.homMk f)) := by
  let fsh : (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) ⟶
      (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) := ObjectProperty.homMk f
  letI : Balanced (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    balanced_of_strongEpiCategory
  change Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map fsh)
  rw [← TopCat.Sheaf.isLocallySurjective_iff_epi
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map fsh)]
  rw [TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro x; by_cases hx : (x : X) ∈ s
  · let z : TopCat.of s := ⟨x, hx⟩
    haveI hEpiF : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map f) :=
      (AddCommGrpCat.epi_iff_surjective _).mpr
        (((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
            (T := f)).mp hf_loc) z)
    have hnat : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        ((TopCat.closedIncl hs) z)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).map f) ≫
      TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (TopCat.closedIncl hs) G z =
    TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (TopCat.closedIncl hs) F z ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map f := by
      apply TopCat.Presheaf.stalk_hom_ext; intro U hU
      erw [← Category.assoc]
      rw [TopCat.Presheaf.stalkFunctor_map_germ U ((TopCat.closedIncl hs) z) hU
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).map f)]
      erw [Category.assoc]
      erw [TopCat.Presheaf.stalkPushforward_germ]
      erw [TopCat.Presheaf.stalkPushforward_germ_assoc]
      erw [TopCat.Presheaf.stalkFunctor_map_germ]
      rfl
    apply (AddCommGrpCat.epi_iff_surjective _).mp
    change Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        ((TopCat.closedIncl hs) z)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).map f))
    haveI : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs) F z) :=
      TopCat.closedIncl_stalkPushforward_isIso (hs := hs)
    haveI : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs) G z) :=
      TopCat.closedIncl_stalkPushforward_isIso (hs := hs)
    have hcomp : Epi (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs) F z ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map f) :=
      @epi_comp _ _ _ _ _
        (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (TopCat.closedIncl hs) F z)
        (inferInstance : Epi (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
          (TopCat.closedIncl hs) F z))
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map f)
        hEpiF
    have hcomp' : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        ((TopCat.closedIncl hs) z)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).map f) ≫
      TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (TopCat.closedIncl hs) G z) := by
      rw [hnat]; exact hcomp
    exact (epi_comp_iff_of_isIso _
      (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (TopCat.closedIncl hs) G z)).mp hcomp'
  · intro b
    rw [pushforward_closedIncl_stalk_eq_zero (hs := hs) (G := G) hG hx b]
    exact ⟨0, AddMonoidHom.map_zero _⟩

instance closedIncl_pushforward_preservesEpis
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).PreservesEpimorphisms where
  preserves {F G} f hf := by
    letI : Epi f := hf
    letI : Balanced (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
      balanced_of_strongEpiCategory
    have hf_loc : TopCat.Presheaf.IsLocallySurjective f.hom :=
      (TopCat.Sheaf.isLocallySurjective_iff_epi f).mpr inferInstance
    change Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map (ObjectProperty.homMk f.hom))
    exact epi_pushforward_map_closedIncl_of_locallySurjective
      (hs := hs) (F := F.obj) (G := G.obj) F.property G.property f.hom hf_loc

instance closedIncl_pushforward_preservesMonos
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).PreservesMonomorphisms := inferInstance

/-- Pushforward along a closed immersion preserves short exact sequences. -/
theorem closedIncl_pushforward_shortExact
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s))}
    (hSE : S.ShortExact) :
    (S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs))).ShortExact := by
  let F := TopCat.Sheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)
  haveI := hSE.mono_f
  haveI := hSE.epi_g
  haveI : Mono (F.map S.f) := inferInstance
  haveI : Epi (F.map S.g) := inferInstance
  exact ShortComplex.ShortExact.mk'
    (hSE.exact.map_of_mono_of_preservesKernel _ hSE.mono_f inferInstance) ‹_› ‹_›

namespace TopCat

-- Stalk pullback hom naturality
lemma stalkPullbackHom_naturality
    {C : Type*} [Category C] [HasColimits C]
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    {F G : Y.Presheaf C} (α : F ⟶ G) (x : ↑X) :
    (Presheaf.stalkFunctor C (ConcreteCategory.hom f x)).map α ≫
      Presheaf.stalkPullbackHom C f G x =
    Presheaf.stalkPullbackHom C f F x ≫
      (Presheaf.stalkFunctor C x).map
        ((Presheaf.pullback C f).map α) := by
  apply Presheaf.stalk_hom_ext; intro U hU
  have key : α.app (Opposite.op U) ≫
      ((Presheaf.pullbackPushforwardAdjunction C f).unit.app G).app (Opposite.op U) =
    ((Presheaf.pullbackPushforwardAdjunction C f).unit.app F).app (Opposite.op U) ≫
      ((Presheaf.pullback C f).map α).app
        (Opposite.op ((TopologicalSpace.Opens.map f).obj U)) := by
    have h := congr_arg (fun β ↦ NatTrans.app β (Opposite.op U))
      ((Presheaf.pullbackPushforwardAdjunction C f).unit.naturality α)
    dsimp at h ⊢
    exact h
  erw [← Category.assoc]
  rw [Presheaf.stalkFunctor_map_germ U ((ConcreteCategory.hom f) x) hU α]
  erw [Category.assoc]
  erw [Presheaf.germ_stalkPullbackHom]
  erw [Presheaf.germ_stalkPullbackHom_assoc]
  erw [← Category.assoc]
  rw [key]
  erw [Presheaf.stalkFunctor_map_germ]
  exact Category.assoc _ _ _

-- Unit stalk is iso for closed immersions.
-- Proof chain: triangle identity → pullback.map(η) iso → pullbackIso naturality
-- → toSheafify naturality → stalkPullbackHom_naturality → η stalk iso
theorem closedIncl_unit_stalk_isIso
    {C : Type*} [Category.{u} C]
    {FC : C → C → Type*} {CC : C → Type u}
    [∀ (X Y : C), FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (forget C)]
    [PreservesFilteredColimits (forget C)]
    [(forget C).ReflectsIsomorphisms]
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    (F : TopCat.Sheaf C X) (x : TopCat.of s) :
    IsIso ((Presheaf.stalkFunctor C ((closedIncl hs) x)).map
      ((Sheaf.pullbackPushforwardAdjunction C (closedIncl hs)).unit.app
        F).hom) := by
  -- Use the triangle identity + counit iso
  let i := closedIncl hs
  let adj := Sheaf.pullbackPushforwardAdjunction C i
  let pb := Sheaf.pullback C i
  let η := adj.unit.app F
  haveI hCounit : IsIso (adj.counit.app (pb.obj F)) :=
    closedIncl_counit_isIso (C := C) (hs := hs) (pb.obj F)
  haveI hId : IsIso (𝟙 (pb.obj F)) := IsIso.id _
  haveI hEta : IsIso (pb.map η) :=
    @IsIso.of_isIso_fac_right (TopCat.Sheaf C (TopCat.of s)) _ _ _ _
      (adj.counit.app (pb.obj F)) (pb.map η) (𝟙 (pb.obj F))
      hCounit hId (adj.left_triangle_components F)
  -- Step 2: val stalk of pb.map(η) is iso
  haveI hEtaHom : IsIso (pb.map η).hom :=
    @Functor.map_isIso _ _ _ _ _ _ (sheafToPresheaf _ _) (pb.map η) hEta
  let Tz := Presheaf.stalkFunctor C x
  let K := Opens.grothendieckTopology (TopCat.of s)
  let pull := Presheaf.pullback C i
  -- Step 3: pullbackIso naturality
  let pi := Sheaf.pullbackIso C i
  let piF := pi.hom.app F
  let piT := pi.hom.app ((pb ⋙ Sheaf.pushforward C i).obj F)
  haveI hPiFHom : IsIso piF.hom :=
    @Functor.map_isIso _ _ _ _ _ _ (sheafToPresheaf _ _) piF inferInstance
  haveI hPiTHom : IsIso piT.hom :=
    @Functor.map_isIso _ _ _ _ _ _ (sheafToPresheaf _ _) piT inferInstance
  have hnat : (pb.map η).hom ≫ piT.hom = piF.hom ≫ sheafifyMap K (pull.map η.hom) :=
    congr_arg InducedCategory.Hom.hom (pi.hom.naturality η)
  have hnat_stalk : Tz.map (pb.map η).hom ≫ Tz.map piT.hom =
      Tz.map piF.hom ≫ Tz.map (sheafifyMap K (pull.map η.hom)) := by
    rw [← Tz.map_comp, ← Tz.map_comp]
    exact congr_arg Tz.map hnat
  -- Step 4: presheafToSheaf.map(pull.map(η.hom)) stalk is iso
  haveI hStalkEtaHom : IsIso (Tz.map (pb.map η).hom) :=
    @Functor.map_isIso _ _ _ _ _ _ Tz _ hEtaHom
  haveI hStalkPiFHom : IsIso (Tz.map piF.hom) :=
    @Functor.map_isIso _ _ _ _ _ _ Tz _ hPiFHom
  haveI hStalkPiTHom : IsIso (Tz.map piT.hom) :=
    @Functor.map_isIso _ _ _ _ _ _ Tz _ hPiTHom
  haveI hSheafifyComp : IsIso (Tz.map piF.hom ≫ Tz.map (sheafifyMap K (pull.map η.hom))) := by
    rw [← hnat_stalk]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hStalkEtaHom hStalkPiTHom
  haveI hSheafifyMap : IsIso (Tz.map (sheafifyMap K (pull.map η.hom))) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _ (Tz.map piF.hom)
      (Tz.map (sheafifyMap K (pull.map η.hom))) hStalkPiFHom hSheafifyComp
  -- Step 5: toSheafify naturality → pull.map(η.hom) stalk is iso
  let P₁ := pull.obj F.obj
  let P₂ := pull.obj ((pb ⋙ Sheaf.pushforward C i).obj F).obj
  have hts : Tz.map (pull.map η.hom) ≫ Tz.map (CategoryTheory.toSheafify K P₂) =
      Tz.map (CategoryTheory.toSheafify K P₁) ≫ Tz.map (sheafifyMap K (pull.map η.hom)) := by
    rw [← Tz.map_comp, ← Tz.map_comp]
    exact congr_arg Tz.map (CategoryTheory.toSheafify_naturality K (pull.map η.hom))
  have hToSheafifyIso (P : (TopCat.of s).Presheaf C) :
      IsIso (Tz.map (toSheafify K P)) :=
    stalkFunctor_map_iso_toSheafify P x
  haveI hPullComp :
      IsIso (Tz.map (pull.map η.hom) ≫ Tz.map (CategoryTheory.toSheafify K P₂)) := by
    rw [hts]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (hToSheafifyIso P₁) hSheafifyMap
  haveI hPullMap : IsIso (Tz.map (pull.map η.hom)) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ (Tz.map (pull.map η.hom))
      (Tz.map (CategoryTheory.toSheafify K P₂)) (hToSheafifyIso P₂) hPullComp
  -- Step 6: stalkPull_nat → η.hom stalk is iso
  haveI hStalkPullbackF : IsIso (Presheaf.stalkPullbackHom C i F.obj x) :=
    (Presheaf.stalkPullbackIso C i F.obj x).isIso_hom
  haveI hStalkPullbackTarget : IsIso (Presheaf.stalkPullbackHom C i
      ((pb ⋙ Sheaf.pushforward C i).obj F).obj x) :=
    (Presheaf.stalkPullbackIso C i _ x).isIso_hom
  haveI hStalkPullbackComp :
      IsIso (Presheaf.stalkPullbackHom C i F.obj x ≫ Tz.map (pull.map η.hom)) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ hStalkPullbackF hPullMap
  exact @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _
    hStalkPullbackTarget hStalkPullbackComp
    (stalkPullbackHom_naturality i η.hom x)

end TopCat

-- The adjunction unit `F → i_*(i^*F)` is epi for closed immersions.
theorem epi_unit_of_closedImmersion
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Epi ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
      (TopCat.closedIncl hZ)).unit.app F) := by
  let closedIncl := TopCat.closedIncl hZ
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} closedIncl
  letI : Balanced (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    balanced_of_strongEpiCategory
  rw [← TopCat.Sheaf.isLocallySurjective_iff_epi (adj.unit.app F),
    TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro x
  by_cases hxZ : (x : X) ∈ Z
  · haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        ((TopCat.closedIncl hZ) ⟨x, hxZ⟩)).map (adj.unit.app F).hom) := by
      simpa using
        (TopCat.closedIncl_unit_stalk_isIso (C := AddCommGrpCat.{u})
          (hs := hZ) F ⟨x, hxZ⟩)
    exact (ConcreteCategory.bijective_of_isIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} ((TopCat.closedIncl hZ) ⟨x, hxZ⟩)).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
          (TopCat.closedIncl hZ)).unit.app F).hom)).2
  · exact fun b ↦ ⟨0, by
      rw [pushforward_closedIncl_stalk_eq_zero
        (hs := hZ)
        (G := ((TopCat.Sheaf.pullback AddCommGrpCat.{u} closedIncl).obj F).obj)
        (((TopCat.Sheaf.pullback AddCommGrpCat.{u} closedIncl).obj F).property)
        hxZ b]
      exact map_zero _⟩

/-- The short exact sequence `0 → ker(η) → F → i_*(i^*F) → 0` from a closed immersion,
    where `η` is the pullback-pushforward adjunction unit and `i : Z ↪ X` is the
    inclusion of a closed subset. -/
noncomputable def closedImmersionSES
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  let closedIncl := TopCat.closedIncl hZ
  let η := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} closedIncl).unit.app F
  ShortComplex.mk (kernel.ι η) η (kernel.condition η)

theorem closedImmersionSES_shortExact
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (closedImmersionSES (Z := Z) (hZ := hZ) F).ShortExact := by
  unfold closedImmersionSES
  haveI := epi_unit_of_closedImmersion (Z := Z) (hZ := hZ) F
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)) inferInstance inferInstance
