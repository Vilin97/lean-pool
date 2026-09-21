/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arnaud Mayeux
-/
module

public import LeanPool.Dilatations.Basic

/-!
# Restriction, composition, and union of centers

From Arnaud Mayeux, *Dilatations of categories, via their Lean formalization*,
https://arxiv.org/abs/2608.09305, and `rndmx/DilCat` at commit
`604559654c948566675da3f7709b8ad3126bd487` (Apache-2.0).
-/

@[expose] public section

noncomputable section

open CategoryTheory Finset
open CategoryTheory.Localization.Construction

universe v u v' pu pv u₁ v₁ u₂ v₂ u₃ v₃

namespace CategoryTheory.Dilatations

variable {C : Type u} [Category.{v} C]
variable (Z : Center C)
variable {D : Type u} [Category.{v'} D]
variable (F : C ⥤ D)

/-- **Proposition 3.14, setup.** The restriction of `Z` to a subcollection `K ⊂ Z.I`. -/
def Center.restrict (Z : Center C) (K : Set Z.I) (hK : K.Nonempty) : Center C where
  I := K
  nonempty := ⟨⟨hK.choose, hK.choose_spec⟩⟩
  dom := fun k => Z.dom k.1
  cod := fun k => Z.cod k.1
  mor := fun k => Z.mor k.1
  N := fun k => Z.N k.1

/-- `Γ := {d_i}_{i ∈ K}` is a subcollection of `Σ := {d_i}_{i ∈ I}` as `MorphismProperty`s. -/
lemma CenterMorphismProperty_restrict_le
    (Z : Center C) (K : Set Z.I) (hK : K.Nonempty) :
    CenterMorphismProperty (Z.restrict K hK) ≤ CenterMorphismProperty Z := by
  rintro X Y f ⟨k, hk⟩
  exact ⟨k.1, hk⟩

/-- The localization functor induced by inclusion of a restricted set of denominators. -/
def baseRestrictFunctor (Z : Center C) (K : Set Z.I) (hK : K.Nonempty) :
    (CenterMorphismProperty (Z.restrict K hK)).Localization ⥤
      (CenterMorphismProperty Z).Localization :=
  Localization.Construction.lift
    (W := CenterMorphismProperty (Z.restrict K hK))
    (CenterMorphismProperty Z).Q
    (fun X Y f hf => by
      show IsIso ((CenterMorphismProperty Z).Q.map f)
      apply CategoryTheory.MorphismProperty.Q_inverts
      exact CenterMorphismProperty_restrict_le Z K hK f hf)

lemma ImageCenterMorphismProperty_restrict_le
    (Z : Center C) (K : Set Z.I) (hK : K.Nonempty) :
    ImageCenterMorphismProperty (Z.restrict K hK) (CatToDila Z) ≤
      ImageCenterMorphismProperty Z (CatToDila Z) := by
  rintro X Y f ⟨k, hk⟩
  exact ⟨k.1, hk⟩

/-- Inverting fewer morphisms preserves faithfulness of the localization functor. -/
private theorem localizationFaithful_of_le {E : Type*} [Category* E]
    {W V : MorphismProperty E} (hWV : W ≤ V) (hV : V.Q.Faithful) : W.Q.Faithful := by
  let L := Localization.Construction.lift (W := W) V.Q
    (fun _ _ f hf => MorphismProperty.Q_inverts V f (hWV f hf))
  have hcomp : (W.Q ⋙ L).Faithful := by
    dsimp [L]
    erw [Localization.Construction.fac]
    exact hV
  exact { map_injective := fun h => hcomp.map_injective (congrArg L.map h) }

lemma CatToDila_isSigmaRegular_restrict
    (Z : Center C) (K : Set Z.I) (hK : K.Nonempty) :
    IsSigmaRegular (Z.restrict K hK) (CatToDila Z) := by
  exact localizationFaithful_of_le (ImageCenterMorphismProperty_restrict_le Z K hK)
    (CatToDila_isSigmaRegular Z)

lemma CatToDila_restrict_hsieve (Z : Center C) (K : Set Z.I) (hK : K.Nonempty) :
    ∀ k : (Z.restrict K hK).I,
      Sieve.functorPushforward (CatToDila Z) ((Z.restrict K hK).N k) ≤
        Sieve.generate (Presieve.singleton ((CatToDila Z).map ((Z.restrict K hK).mor k))) :=
  fun k => CatToDila_image_sieve_le_singleton Z k.1

/-- **Proposition 3.14.** The canonical functor `Φ : C[{dᵢ}_{i∈K}] ⥤ C[{dᵢ}_{i∈I}]`. -/
noncomputable def restrictPhi (Z : Center C) (K : Set Z.I) (hK : K.Nonempty) :
    Dila (Z.restrict K hK) ⥤ Dila Z :=
  DilaLift (Z.restrict K hK) (CatToDila Z)
    (by show (ImageCenterLocalizationFunctor (Z.restrict K hK) (CatToDila Z)).Faithful
        exact CatToDila_isSigmaRegular_restrict Z K hK)
    (CatToDila_restrict_hsieve Z K hK)

lemma restrictPhi_spec (Z : Center C) (K : Set Z.I) (hK : K.Nonempty) :
    CatToDila (Z.restrict K hK) ⋙ restrictPhi Z K hK = CatToDila Z :=
  DilaLift_fac (Z.restrict K hK) (CatToDila Z)
    (by show (ImageCenterLocalizationFunctor (Z.restrict K hK) (CatToDila Z)).Faithful
        exact CatToDila_isSigmaRegular_restrict Z K hK)
    (CatToDila_restrict_hsieve Z K hK)

/-- Universe-polymorphic version of `faithful_of_comp_faithful`, with independent universes for
each of the three categories. -/
theorem faithful_of_comp_faithful_gen
    {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
    {C₃ : Type u₃} [Category.{v₃} C₃]
    (p : C₁ ⥤ C₂) (e : C₂ ⥤ C₃) (hfaith : (p ⋙ e).Faithful) :
    p.Faithful := by
  constructor
  intro X Y f g h
  apply hfaith.map_injective
  simp only [Functor.comp_map, h]

lemma isoMorphismProperty_Q_faithful
    {E : Type u} [Category.{v'} E] (W : MorphismProperty E)
    (hW : ∀ ⦃X Y⦄ (f : X ⟶ Y), W f → IsIso f) :
    W.Q.Faithful := by
  have hinv : W.IsInvertedBy (𝟭 E) := fun X Y f hf => by simpa using hW f hf
  apply faithful_of_comp_faithful_gen W.Q (Localization.Construction.lift (W := W) (𝟭 E) hinv)
  rw [Localization.Construction.fac]
  infer_instance

/-- `Z`'s own raw localization functor is always `Z`-regular — every `Z`-generator is already
inverted by `.Q` (`Q_inverts`), so `isoMorphismProperty_Q_faithful` applies directly. -/
lemma LocalizationFunctor_isSigmaRegular (Z : Center C) :
    IsSigmaRegular Z (LocalizationFunctor Z) := by
  change (ImageCenterMorphismProperty Z (LocalizationFunctor Z)).Q.Faithful
  apply isoMorphismProperty_Q_faithful
  rintro X Y f ⟨i, hi⟩
  have hX : X = (LocalizationFunctor Z).obj (Z.dom i) := congrArg Sigma.fst hi
  have hY : Y = (LocalizationFunctor Z).obj (Z.cod i) := congrArg (fun s => s.2.1) hi
  subst hX
  subst hY
  have hf : f = (LocalizationFunctor Z).map (Z.mor i) := by cases hi; rfl
  rw [hf]
  exact CategoryTheory.MorphismProperty.Q_inverts _ (Z.mor i) ⟨i, rfl⟩

lemma LocalizationFunctor_isSigmaRegular_restrict
    (Z : Center C) (K : Set Z.I) (hK : K.Nonempty) :
    IsSigmaRegular (Z.restrict K hK) (LocalizationFunctor Z) := by
  change (ImageCenterMorphismProperty (Z.restrict K hK) (LocalizationFunctor Z)).Q.Faithful
  apply isoMorphismProperty_Q_faithful
  rintro X Y f ⟨k, hk⟩
  have hX : X = (LocalizationFunctor Z).obj ((Z.restrict K hK).dom k) := congrArg Sigma.fst hk
  have hY : Y = (LocalizationFunctor Z).obj ((Z.restrict K hK).cod k) :=
    congrArg (fun s => s.2.1) hk
  subst X
  subst Y
  have hf : f = (LocalizationFunctor Z).map ((Z.restrict K hK).mor k) := by cases hk; rfl
  rw [hf]
  change IsIso ((CenterMorphismProperty Z).Q.map (Z.mor k.1))
  apply CategoryTheory.MorphismProperty.Q_inverts
  exact ⟨k.1, rfl⟩

lemma restrictPhi_comp_DilaToLoc
    (Z : Center C) (K : Set Z.I) (hK : K.Nonempty) :
    restrictPhi Z K hK ⋙ DilaToLoc Z =
      DilaToLoc (Z.restrict K hK) ⋙ baseRestrictFunctor Z K hK :=
  Dila_factor_unique (Z.restrict K hK) (LocalizationFunctor Z)
    (restrictPhi Z K hK ⋙ DilaToLoc Z)
    (DilaToLoc (Z.restrict K hK) ⋙ baseRestrictFunctor Z K hK)
    (by
      change CatToDila (Z.restrict K hK) ⋙ restrictPhi Z K hK ⋙ DilaToLoc Z = LocalizationFunctor Z
      rw [show CatToDila (Z.restrict K hK) ⋙ restrictPhi Z K hK ⋙ DilaToLoc Z =
            (CatToDila (Z.restrict K hK) ⋙ restrictPhi Z K hK) ⋙ DilaToLoc Z from rfl,
          restrictPhi_spec, CatToDila_comp_DilaToLoc])
    (by
      change CatToDila (Z.restrict K hK) ⋙
          (DilaToLoc (Z.restrict K hK) ⋙ baseRestrictFunctor Z K hK) = LocalizationFunctor Z
      rw [show CatToDila (Z.restrict K hK) ⋙
              (DilaToLoc (Z.restrict K hK) ⋙ baseRestrictFunctor Z K hK) =
            (CatToDila (Z.restrict K hK) ⋙ DilaToLoc (Z.restrict K hK)) ⋙
              baseRestrictFunctor Z K hK from rfl,
          CatToDila_comp_DilaToLoc]
      change (CenterMorphismProperty (Z.restrict K hK)).Q ⋙ baseRestrictFunctor Z K hK =
        LocalizationFunctor Z
      exact Localization.Construction.fac _ _)
    (by
      show (ImageCenterLocalizationFunctor (Z.restrict K hK) (LocalizationFunctor Z)).Faithful
      exact LocalizationFunctor_isSigmaRegular_restrict Z K hK)

/-- **Proposition 3.14 (ii).** If `C[Γ⁻¹] → C[Σ⁻¹]` is faithful, then `Φ` is faithful. -/
theorem restrictPhi_faithful
    (Z : Center C) (K : Set Z.I) (hK : K.Nonempty)
    (hbase : (baseRestrictFunctor Z K hK).Faithful) :
    (restrictPhi Z K hK).Faithful := by
  have := DilaToLoc_faithful (Z.restrict K hK)
  have := hbase
  apply faithful_of_comp_faithful (restrictPhi Z K hK) (DilaToLoc Z)
  rw [restrictPhi_comp_DilaToLoc]
  infer_instance

/-- A fraction whose numerator already factors through its denominator is an original morphism. -/
lemma fractionInDilatation_eq_of_factors
    (i : Z.I) (X : C) (q : X ⟶ Z.dom i) (m : X ⟶ Z.cod i) (hm : Z.N i m)
    (hfactor : m = q ≫ Z.mor i) :
    fractionInDilatation Z ⟨i, ⟨X, ⟨m, hm⟩⟩⟩ = (CatToDila Z).map q := by
      apply unique_factor_D Z (CatToDila Z)
        (by show (ImageCenterLocalizationFunctor Z (CatToDila Z)).Faithful
            exact CatToDila_isSigmaRegular Z)
        i ((CatToDila Z).obj X)
      rw [fraction_in_dila_comp_mor Z i X m hm, ← Functor.map_comp, ← hfactor]

/-- The basic object-identification : `Φ` sends the `Z.restrict K hK`-image of `Y` to the
`Z`-image of `Y`, on the nose, via `restrictPhi_spec`. -/
lemma restrictPhi_obj_eq (Z : Center C) (K : Set Z.I) (hK : K.Nonempty) (Y : C) :
    (restrictPhi Z K hK).obj ((CatToDila (Z.restrict K hK)).obj Y) = (CatToDila Z).obj Y :=
  congrArg (fun H : C ⥤ Dila Z => H.obj Y) (restrictPhi_spec Z K hK)

/-- `hobj`, restated in terms of `restrictPhi_obj_eq` via the object-equivalence `objEquiv`. -/
lemma restrictPhi_full_hobj (Z : Center C) (K : Set Z.I) (hK : K.Nonempty)
    (X' : GeneratedCategory Z) :
    (restrictPhi Z K hK).obj
        ((CatToDila (Z.restrict K hK)).obj ((objEquiv (CenterMorphismProperty Z)).symm X')) =
      (CatToDila Z).obj ((objEquiv (CenterMorphismProperty Z)).symm X') :=
  restrictPhi_obj_eq Z K hK ((objEquiv (CenterMorphismProperty Z)).symm X')

/-- The `Φ`-preimage predicate used in the induction : `p : A' ⟶ B'` (in `GeneratedCategory Z`)
has a `Φ`-preimage among morphisms of `Dila (Z.restrict K hK)`, up to the object-identification
`restrictPhi_full_hobj`. -/
def PhiPreimage (Z : Center C) (K : Set Z.I) (hK : K.Nonempty)
    {A' B' : GeneratedCategory Z} (p : A' ⟶ B') : Prop :=
  ∃ f :
      (CatToDila (Z.restrict K hK)).obj ((objEquiv (CenterMorphismProperty Z)).symm A') ⟶
      (CatToDila (Z.restrict K hK)).obj ((objEquiv (CenterMorphismProperty Z)).symm B'),
    (restrictPhi Z K hK).map f =
      eqToHom (restrictPhi_full_hobj Z K hK A') ≫ (GeneratedToDila Z).map p ≫
        eqToHom (restrictPhi_full_hobj Z K hK B').symm

/-- Base case : the identity generator has a `Φ`-preimage (namely the identity). -/
lemma PhiPreimage_id (Z : Center C) (K : Set Z.I) (hK : K.Nonempty) (X' : GeneratedCategory Z) :
    PhiPreimage Z K hK (𝟙 X') := by
  refine ⟨𝟙 _, ?_⟩
  rw [Functor.map_id]
  erw [Functor.map_id]
  -- `restrictPhi` is now a structural `DilaLift`, so both `eqToHom`s flanking the identity
  -- are definitionally `𝟙`; strip the two compositions and close by `rfl`.
  erw [Category.id_comp]
  erw [Category.id_comp]
  rfl

/-- Inductive step : `Φ`-preimages compose. -/
lemma PhiPreimage_comp (Z : Center C) (K : Set Z.I) (hK : K.Nonempty)
    {X' Y' W' : GeneratedCategory Z} (p : X' ⟶ Y') (q : Y' ⟶ W')
    (hp : PhiPreimage Z K hK p) (hq : PhiPreimage Z K hK q) :
    PhiPreimage Z K hK (p ≫ q) := by
  obtain ⟨f, hf⟩ := hp
  obtain ⟨f', hf'⟩ := hq
  refine ⟨f ≫ f', ?_⟩
  change (restrictPhi Z K hK).map (f ≫ f') =
      eqToHom (restrictPhi_full_hobj Z K hK X') ≫ (GeneratedToDila Z).map (p ≫ q) ≫
        eqToHom (restrictPhi_full_hobj Z K hK W').symm
  rw [Functor.map_comp, hf, hf']
  erw [Functor.map_comp]
  exact transported_comp (restrictPhi_full_hobj Z K hK X')
    (restrictPhi_full_hobj Z K hK Y') (restrictPhi_full_hobj Z K hK W') _ _

/-- `DilaToLoc` sends a fraction generator back down to the corresponding fraction morphism
of the localization. -/
lemma DilaToLoc_map_fraction (Z : Center C) (p : CenterSievePair Z) :
    (DilaToLoc Z).map (fractionInDilatation Z p) = fractionInLocalization Z p := by
  rfl

lemma fractionInLocalization_eq (Z : Center C) (p : CenterSievePair Z) :
    fractionInLocalization Z p =
      (CenterMorphismProperty Z).Q.map p.2.2.1 ≫
        Localization.Construction.wInv (Z.mor p.1) ⟨p.1, rfl⟩ := by
  rfl

lemma baseRestrictFunctor_map_Q (Z : Center C) (K : Set Z.I) (hK : K.Nonempty)
    {X Y : C} (f : X ⟶ Y) :
    (baseRestrictFunctor Z K hK).map ((CenterMorphismProperty (Z.restrict K hK)).Q.map f) =
      (CenterMorphismProperty Z).Q.map f := by
  rfl

lemma baseRestrictFunctor_map_wInv (Z : Center C) (K : Set Z.I) (hK : K.Nonempty)
    {X Y : C} (w : X ⟶ Y) (hw : CenterMorphismProperty (Z.restrict K hK) w) :
    (baseRestrictFunctor Z K hK).map (Localization.Construction.wInv w hw) =
      Localization.Construction.wInv w (CenterMorphismProperty_restrict_le Z K hK w hw) := by
  have := MorphismProperty.Q_inverts (CenterMorphismProperty (Z.restrict K hK)) w hw
  have : IsIso ((CenterMorphismProperty Z).Q.map w) :=
    MorphismProperty.Q_inverts (CenterMorphismProperty Z) w
    (CenterMorphismProperty_restrict_le Z K hK w hw)
  have h1 : Localization.Construction.wInv w hw =
      CategoryTheory.inv ((CenterMorphismProperty (Z.restrict K hK)).Q.map w) :=
    (IsIso.Iso.inv_hom (Localization.Construction.wIso w hw)).symm
  have h2 : Localization.Construction.wInv w (CenterMorphismProperty_restrict_le Z K hK w hw) =
      CategoryTheory.inv ((CenterMorphismProperty Z).Q.map w) :=
    (IsIso.Iso.inv_hom
      (Localization.Construction.wIso w (CenterMorphismProperty_restrict_le Z K hK w hw))).symm
  rw [h1, h2, Functor.map_inv]
  change inv ((CenterMorphismProperty Z).Q.map w) = inv ((CenterMorphismProperty Z).Q.map w)
  rfl

lemma baseRestrictFunctor_map_fraction (Z : Center C) (K : Set Z.I) (hK : K.Nonempty)
    (i : Z.I) (hiK : i ∈ K) (X0 : C) (n : X0 ⟶ Z.cod i) (hn : Z.N i n) :
    (baseRestrictFunctor Z K hK).map
        (fractionInLocalization (Z.restrict K hK) ⟨⟨i, hiK⟩, ⟨X0, ⟨n, hn⟩⟩⟩) =
      fractionInLocalization Z ⟨i, ⟨X0, ⟨n, hn⟩⟩⟩ := by
  erw [fractionInLocalization_eq, Functor.map_comp,
    baseRestrictFunctor_map_Q, baseRestrictFunctor_map_wInv, fractionInLocalization_eq]
  rfl

/-- `restrictPhi` sends the fraction generator of `Z.restrict K hK` at an index `i ∈ K` to the
corresponding fraction generator of `Z` at `i`, up to the object-identification
`restrictPhi_obj_eq`. -/
lemma restrictPhi_map_fraction (Z : Center C) (K : Set Z.I) (hK : K.Nonempty)
    (i : Z.I) (hiK : i ∈ K) (X0 : C) (n : X0 ⟶ Z.cod i) (hn : Z.N i n) :
    (restrictPhi Z K hK).map
        (fractionInDilatation (Z.restrict K hK) ⟨⟨i, hiK⟩, ⟨X0, ⟨n, hn⟩⟩⟩) =
      eqToHom (restrictPhi_obj_eq Z K hK X0) ≫ fractionInDilatation Z ⟨i, ⟨X0, ⟨n, hn⟩⟩⟩ ≫
        eqToHom (restrictPhi_obj_eq Z K hK (Z.dom i)).symm := by
  have := DilaToLoc_faithful Z
  apply (DilaToLoc Z).map_injective
  have hcomp := Functor.congr_hom (restrictPhi_comp_DilaToLoc Z K hK)
      (fractionInDilatation (Z.restrict K hK) ⟨⟨i, hiK⟩, ⟨X0, ⟨n, hn⟩⟩⟩)
  erw [Functor.comp_map, Functor.comp_map, DilaToLoc_map_fraction,
    baseRestrictFunctor_map_fraction] at hcomp
  erw [hcomp, Functor.map_comp, Functor.map_comp]
  erw [eqToHom_map, eqToHom_map, DilaToLoc_map_fraction]
  rfl

/-- Generator case, `i ∈ K`: a fraction generator indexed by `i ∈ K` has a `Φ`-preimage — the
corresponding fraction generator of `Z.restrict K hK`, via `restrictPhi_map_fraction`. -/
lemma PhiPreimage_fraction_mem (Z : Center C) (K : Set Z.I) (hK : K.Nonempty)
    (i : Z.I) (hiK : i ∈ K) (X0 : C) (n : X0 ⟶ Z.cod i) (hn : Z.N i n) :
    PhiPreimage Z K hK
      (Quiver.Hom.toPath
        (⟨fractionInLocalization Z ⟨i, ⟨X0, ⟨n, hn⟩⟩⟩,
          GeneratorMorphismData.fraction ⟨⟨i, ⟨X0, ⟨n, hn⟩⟩⟩, rfl⟩⟩ :
          (GeneratorQuiver Z).Hom
            (objEquiv (CenterMorphismProperty Z) X0)
            (objEquiv (CenterMorphismProperty Z) (Z.dom i)))) := by
  refine ⟨eqToHom (by rw [Equiv.symm_apply_apply]) ≫
      fractionInDilatation (Z.restrict K hK) ⟨⟨i, hiK⟩, ⟨X0, ⟨n, hn⟩⟩⟩ ≫
      eqToHom rfl, ?_⟩
  change (restrictPhi Z K hK).map
      (eqToHom (by rw [Equiv.symm_apply_apply]) ≫
        fractionInDilatation (Z.restrict K hK) ⟨⟨i, hiK⟩, ⟨X0, ⟨n, hn⟩⟩⟩ ≫
        eqToHom rfl) =
      eqToHom (restrictPhi_full_hobj Z K hK (objEquiv (CenterMorphismProperty Z) X0)) ≫
        (GeneratedToDila Z).map
          (Quiver.Hom.toPath
            (⟨fractionInLocalization Z ⟨i, ⟨X0, ⟨n, hn⟩⟩⟩,
              GeneratorMorphismData.fraction ⟨⟨i, ⟨X0, ⟨n, hn⟩⟩⟩, rfl⟩⟩ :
              (GeneratorQuiver Z).Hom _ _)) ≫
        eqToHom
          (restrictPhi_full_hobj Z K hK
            (objEquiv (CenterMorphismProperty Z) (Z.dom i))).symm
  rw [Functor.map_comp, Functor.map_comp,
    restrictPhi_map_fraction Z K hK i hiK X0 n hn]
  simp only [eqToHom_map]
  rfl

/-- Generator case, original morphisms : always has a `Φ`-preimage. -/
lemma PhiPreimage_original (Z : Center C) (K : Set Z.I) (hK : K.Nonempty)
    {X0 Y0 : C} (c : X0 ⟶ Y0) :
    PhiPreimage Z K hK
      (Quiver.Hom.toPath
        (⟨(CenterMorphismProperty Z).Q.map c, GeneratorMorphismData.original ⟨c, rfl⟩⟩ :
          (GeneratorQuiver Z).Hom
            (objEquiv (CenterMorphismProperty Z) X0)
            (objEquiv (CenterMorphismProperty Z) Y0))) := by
  refine ⟨(CatToDila (Z.restrict K hK)).map c, ?_⟩
  change (restrictPhi Z K hK).map ((CatToDila (Z.restrict K hK)).map c) =
      eqToHom (restrictPhi_full_hobj Z K hK (objEquiv (CenterMorphismProperty Z) X0)) ≫
        (GeneratedToDila Z).map
          (Quiver.Hom.toPath
            (⟨(CenterMorphismProperty Z).Q.map c, GeneratorMorphismData.original ⟨c, rfl⟩⟩ :
              (GeneratorQuiver Z).Hom _ _)) ≫
        eqToHom (restrictPhi_full_hobj Z K hK (objEquiv (CenterMorphismProperty Z) Y0)).symm
  have hcomp := Functor.congr_hom (restrictPhi_spec Z K hK) c
  rw [Functor.comp_map] at hcomp
  rw [hcomp]
  rfl

/-- Generator case, `i ∉ K`: under `hI`, a fraction generator indexed by `i ∉ K` reduces to an
ordinary morphism, which already has a `Φ`-preimage. -/
lemma PhiPreimage_fraction_notmem (Z : Center C) (K : Set Z.I) (hK : K.Nonempty)
    (hI : ∀ i : Z.I, i ∉ K → Z.N i = Sieve.generate (Presieve.singleton (Z.mor i)))
    (i : Z.I) (hiK : i ∉ K) (X0 : C) (n : X0 ⟶ Z.cod i) (hn : Z.N i n) :
    PhiPreimage Z K hK
      (Quiver.Hom.toPath
        (⟨fractionInLocalization Z ⟨i, ⟨X0, ⟨n, hn⟩⟩⟩,
          GeneratorMorphismData.fraction ⟨⟨i, ⟨X0, ⟨n, hn⟩⟩⟩, rfl⟩⟩ :
          (GeneratorQuiver Z).Hom
            (objEquiv (CenterMorphismProperty Z) X0)
            (objEquiv (CenterMorphismProperty Z) (Z.dom i)))) := by
  have hn' : (Sieve.generate (Presieve.singleton (Z.mor i))).arrows n := (hI i hiK) ▸ hn
  obtain ⟨X1, q, e, he, hq⟩ := hn'
  rcases he with ⟨-, rfl⟩
  have := MorphismProperty.Q_inverts (CenterMorphismProperty Z) (Z.mor i) ⟨i, rfl⟩
  have hfrac : fractionInLocalization Z ⟨i, ⟨X0, ⟨n, hn⟩⟩⟩ = (CenterMorphismProperty Z).Q.map
    q := by
    apply (cancel_mono ((CenterMorphismProperty Z).Q.map (Z.mor i))).1
    erw [fraction_comp_mor, ← Functor.map_comp]
    exact congrArg (CenterMorphismProperty Z).Q.map hq.symm
  have hEq :
      (GeneratedToDila Z).map
          (Quiver.Hom.toPath
            (⟨fractionInLocalization Z ⟨i, ⟨X0, ⟨n, hn⟩⟩⟩,
              GeneratorMorphismData.fraction ⟨⟨i, ⟨X0, ⟨n, hn⟩⟩⟩, rfl⟩⟩ :
              (GeneratorQuiver Z).Hom
                (objEquiv (CenterMorphismProperty Z) X0)
                (objEquiv (CenterMorphismProperty Z) (Z.dom i)))) =
        (GeneratedToDila Z).map
          (Quiver.Hom.toPath
            (⟨(CenterMorphismProperty Z).Q.map q, GeneratorMorphismData.original ⟨q, rfl⟩⟩ :
              (GeneratorQuiver Z).Hom
                (objEquiv (CenterMorphismProperty Z) X0)
                (objEquiv (CenterMorphismProperty Z) (Z.dom i)))) :=
    Quotient.sound (r := DilaRel Z) hfrac
  obtain ⟨f, hf⟩ := PhiPreimage_original Z K hK q
  refine ⟨f, ?_⟩
  erw [hEq]
  exact hf

/-- Every object of `Dila Z` is the `CatToDila`-image of some object of `C`. -/
lemma CatToDila_obj_surjective (Z : Center C) (A : Dila Z) :
    ∃ X : C, (CatToDila Z).obj X = A := by
  refine ⟨(objEquiv (CenterMorphismProperty Z)).symm A.as, ?_⟩
  apply CategoryTheory.Quotient.ext
  change objEquiv (CenterMorphismProperty Z)
      ((objEquiv (CenterMorphismProperty Z)).symm A.as) = A.as
  erw [Equiv.apply_symm_apply]

/-- A single generator edge always has a `Φ`-preimage. -/
lemma PhiPreimage_edge (Z : Center C) (K : Set Z.I) (hK : K.Nonempty)
    (hI : ∀ i : Z.I, i ∉ K → Z.N i = Sieve.generate (Presieve.singleton (Z.mor i)))
    {X Y : (CenterMorphismProperty Z).Localization} (e : (GeneratorQuiver Z).Hom X Y) :
    PhiPreimage Z K hK (Quiver.Hom.toPath e) := by
  obtain ⟨f, d⟩ := e
  cases d with
  | fraction w =>
    obtain ⟨cp, heq⟩ := w
    obtain ⟨i, X0, n, hn⟩ := cp
    cases heq
    by_cases hiK : i ∈ K
    · exact PhiPreimage_fraction_mem Z K hK i hiK X0 n hn
    · exact PhiPreimage_fraction_notmem Z K hK hI i hiK X0 n hn
  | original w =>
    obtain ⟨g, heq⟩ := w
    cases heq
    exact PhiPreimage_original Z K hK g

/-- Every morphism of `GeneratedCategory Z` has a `Φ`-preimage : induction on the underlying
path, using `PhiPreimage_id`, `PhiPreimage_comp`, and `PhiPreimage_edge`. -/
lemma PhiPreimage_all (Z : Center C) (K : Set Z.I) (hK : K.Nonempty)
    (hI : ∀ i : Z.I, i ∉ K → Z.N i = Sieve.generate (Presieve.singleton (Z.mor i)))
    {A' B' : GeneratedCategory Z} (p : A' ⟶ B') :
    PhiPreimage Z K hK p := by
  induction p with
  | nil => exact PhiPreimage_id Z K hK A'
  | cons p e ih =>
    exact PhiPreimage_comp Z K hK p (Quiver.Hom.toPath e) ih (PhiPreimage_edge Z K hK hI e)

theorem restrictPhi_full
    (Z : Center C) (K : Set Z.I) (hK : K.Nonempty)
    (hI : ∀ i : Z.I, i ∉ K → Z.N i = Sieve.generate (Presieve.singleton (Z.mor i))) :
    (restrictPhi Z K hK).Full := by
  refine ⟨fun {X1 Y1} g => ?_⟩
  obtain ⟨X0, hX0⟩ := CatToDila_obj_surjective (Z.restrict K hK) X1
  obtain ⟨Y0, hY0⟩ := CatToDila_obj_surjective (Z.restrict K hK) Y1
  subst hX0
  subst hY0
  set g' : (CatToDila Z).obj X0 ⟶ (CatToDila Z).obj Y0 :=
    eqToHom (restrictPhi_full_hobj Z K hK (objEquiv (CenterMorphismProperty Z) X0)).symm ≫ g ≫
      eqToHom (restrictPhi_full_hobj Z K hK (objEquiv (CenterMorphismProperty Z) Y0)) with hg'
  obtain ⟨p, hp⟩ := (GeneratedToDila Z).map_surjective
    (show (GeneratedToDila Z).obj (objEquiv (CenterMorphismProperty Z) X0) ⟶
        (GeneratedToDila Z).obj (objEquiv (CenterMorphismProperty Z) Y0) from g')
  obtain ⟨f, hf⟩ := PhiPreimage_all Z K hK hI p
  refine ⟨f, ?_⟩
  erw [hf, hp, hg']
  erw [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-! ### Proposition 3.15 -/
/-- Pushing a center `W` on `C` forward along a functor `F : C ⥤ D` gives a center on `D`,
namely `{[F(N_j), F(d_j)]}_j`. -/
def Center.pushforward (W : Center C) (F : C ⥤ D) : Center D where
  I := W.I
  nonempty := W.nonempty
  dom := fun i => F.obj (W.dom i)
  cod := fun i => F.obj (W.cod i)
  mor := fun i => F.map (W.mor i)
  N := fun i => Sieve.functorPushforward F (W.N i)

/-- Combining two centers `Z` and `W` on the same category `C` into one center indexed by
`Z.I ⊕ W.I`. -/
def Center.sum (Z W : Center C) : Center C where
  I := Z.I ⊕ W.I
  nonempty := ⟨Sum.inl Z.nonempty.some⟩
  dom := Sum.elim Z.dom W.dom
  cod := Sum.elim Z.cod W.cod
  mor := fun i => match i with
    | Sum.inl i => Z.mor i
    | Sum.inr j => W.mor j
  N := fun i => match i with
    | Sum.inl i => Z.N i
    | Sum.inr j => W.N j

lemma CenterMorphismProperty_sum_inl_le (Z W : Center C) :
    CenterMorphismProperty Z ≤ CenterMorphismProperty (Z.sum W) := by
  rintro X Y f ⟨i, hi⟩
  exact ⟨Sum.inl i, hi⟩

lemma CenterMorphismProperty_sum_inr_le (Z W : Center C) :
    CenterMorphismProperty W ≤ CenterMorphismProperty (Z.sum W) := by
  rintro X Y f ⟨j, hj⟩
  exact ⟨Sum.inr j, hj⟩

lemma ImageCenterMorphismProperty_sum_inl_le (Z W : Center C) (F : C ⥤ D) :
    ImageCenterMorphismProperty Z F ≤ ImageCenterMorphismProperty (Z.sum W) F := by
  rintro X Y f ⟨i, hi⟩
  exact ⟨Sum.inl i, hi⟩

lemma ImageCenterMorphismProperty_sum_inr_le (Z W : Center C) (F : C ⥤ D) :
    ImageCenterMorphismProperty W F ≤ ImageCenterMorphismProperty (Z.sum W) F := by
  rintro X Y f ⟨j, hj⟩
  exact ⟨Sum.inr j, hj⟩

/-- The dilatation of the `Z`-part of `Z.sum W` is regular for `CatToDila (Z.sum W)`: analogous
to `CatToDila_isSigmaRegular_restrict`, but for the `Sum.inl`-inclusion into `Z.sum W` instead of
a `Center.restrict`. -/
lemma CatToDila_isSigmaRegular_sum_inl (Z W : Center C) :
    IsSigmaRegular Z (CatToDila (Z.sum W)) := by
  exact localizationFaithful_of_le
    (ImageCenterMorphismProperty_sum_inl_le Z W (CatToDila (Z.sum W)))
    (CatToDila_isSigmaRegular (Z.sum W))

lemma CatToDila_isSigmaRegular_sum_inr (Z W : Center C) :
    IsSigmaRegular W (CatToDila (Z.sum W)) := by
  exact localizationFaithful_of_le
    (ImageCenterMorphismProperty_sum_inr_le Z W (CatToDila (Z.sum W)))
    (CatToDila_isSigmaRegular (Z.sum W))

/-- The sieve condition needed to extend `CatToDila (Z.sum W)` along `CatToDila Z`. -/
lemma CatToDila_sum_hsieve_inl (Z W : Center C) :
    ∀ i : Z.I,
      Sieve.functorPushforward (CatToDila (Z.sum W)) (Z.N i) ≤
        Sieve.generate (Presieve.singleton ((CatToDila (Z.sum W)).map (Z.mor i))) :=
  fun i => CatToDila_image_sieve_le_singleton (Z.sum W) (Sum.inl i)

lemma CatToDila_sum_hsieve_inr (Z W : Center C) :
    ∀ j : W.I,
      Sieve.functorPushforward (CatToDila (Z.sum W)) (W.N j) ≤
        Sieve.generate (Presieve.singleton ((CatToDila (Z.sum W)).map (W.mor j))) :=
  fun j => CatToDila_image_sieve_le_singleton (Z.sum W) (Sum.inr j)

/-- **Proposition 3.15, setup.** The canonical functor `Φ : Dila Z ⥤ Dila (Z.sum W)`, obtained
directly from the universal property of `Dila Z` (Theorem 3.10 / `Dila_universal_property`)
applied to `CatToDila (Z.sum W)`, rather than through `Center.restrict`/`restrictPhi` — this
avoids having to reindex `Z.sum W` restricted to its `Z`-part back to `Z`, since the two
constructions agree by the uniqueness clause of the universal property. -/
noncomputable def Phi315 (Z W : Center C) : Dila Z ⥤ Dila (Z.sum W) :=
  DilaLift Z (CatToDila (Z.sum W))
    (CatToDila_isSigmaRegular_sum_inl Z W) (CatToDila_sum_hsieve_inl Z W)

lemma Phi315_spec (Z W : Center C) :
    CatToDila Z ⋙ Phi315 Z W = CatToDila (Z.sum W) :=
  DilaLift_fac Z (CatToDila (Z.sum W))
    (CatToDila_isSigmaRegular_sum_inl Z W) (CatToDila_sum_hsieve_inl Z W)

/-- The pushed-forward center `{[Θ(Nj), Θ(dj)]}_{j∈J}` living in `Dila Z`. -/
def CenterZW (Z W : Center C) : Center (Dila Z) := W.pushforward (CatToDila Z)

/-- **β.** The dilatation functor for `CenterZW`. -/
def Beta315 (Z W : Center C) : Dila Z ⥤ Dila (CenterZW Z W) := CatToDila (CenterZW Z W)

/-- A helper for comparing two elements of `Σ X Y : D, X ⟶ Y` whose objects agree via a
(possibly non-trivial) `eqToHom`-transport of the morphism. -/
lemma sigma_hom_eq {A A' B B' : D} (hA : A = A') (hB : B = B') (m : A ⟶ B) (m' : A' ⟶ B')
    (hm : m' = eqToHom hA.symm ≫ m ≫ eqToHom hB) :
    (⟨A, B, m⟩ : Σ X Y : D, X ⟶ Y) = ⟨A', B', m'⟩ := by
  subst hA; subst hB; simpa using hm.symm

lemma ImageCenterMorphismProperty_ZW_Phi_eq (Z W : Center C) :
    ImageCenterMorphismProperty (CenterZW Z W) (Phi315 Z W) =
      ImageCenterMorphismProperty W (CatToDila (Z.sum W)) := by
  have hobj : ∀ X : C, (Phi315 Z W).obj ((CatToDila Z).obj X) = (CatToDila (Z.sum W)).obj X :=
    fun X => congrArg (fun H : C ⥤ Dila (Z.sum W) => H.obj X) (Phi315_spec Z W)
  have hmap : ∀ {X Y : C} (f : X ⟶ Y),
      (CatToDila (Z.sum W)).map f =
        eqToHom (hobj X).symm ≫ (Phi315 Z W).map ((CatToDila Z).map f) ≫ eqToHom (hobj Y) := by
    intro X Y f
    have h := Functor.congr_hom (Phi315_spec Z W) f
    rw [Functor.comp_map] at h
    rw [h]
    simp
  funext X Y f
  apply propext
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, hj.trans (sigma_hom_eq (hobj (W.dom j)) (hobj (W.cod j))
      ((Phi315 Z W).map ((CatToDila Z).map (W.mor j))) ((CatToDila (Z.sum W)).map (W.mor j))
      (hmap (W.mor j)))⟩
  · rintro ⟨j, hj⟩
    refine ⟨j, hj.trans (sigma_hom_eq (hobj (W.dom j)).symm (hobj (W.cod j)).symm
      ((CatToDila (Z.sum W)).map (W.mor j)) ((Phi315 Z W).map ((CatToDila Z).map (W.mor j)))
      (by simp [hmap]))⟩

/-- **Fact 2.14.** `C[(dᵢ)⁻¹∘Nᵢ] → C[{dᵢ}⁻¹]` is faithful. -/
theorem Fact_2_14 (Z : Center C) : (DilaToLoc Z).Faithful :=
  DilaToLoc_faithful Z

/-- **Proposition 3.15 (i).** `Φ` belongs to `Cat ^ {Θ(dj)}_j-reg_{Dila Z}`. -/
theorem Phi315_isSigmaRegular (Z W : Center C) :
    IsSigmaRegular (CenterZW Z W) (Phi315 Z W) := by
  change (ImageCenterMorphismProperty (CenterZW Z W) (Phi315 Z W)).Q.Faithful
  rw [ImageCenterMorphismProperty_ZW_Phi_eq]
  exact CatToDila_isSigmaRegular_sum_inr Z W

lemma functorPushforward_singleton_congr {F G : C ⥤ D} (h : F = G) {X Y : C} (S : Sieve X)
    (f : Y ⟶ X) (hle : Sieve.functorPushforward G S ≤ Sieve.generate (Presieve.singleton
      (G.map f))) :
    Sieve.functorPushforward F S ≤ Sieve.generate (Presieve.singleton (F.map f)) := by
  subst h; exact hle

theorem Phi315_hsieve (Z W : Center C) :
    ∀ j : (CenterZW Z W).I,
      Sieve.functorPushforward (Phi315 Z W) ((CenterZW Z W).N j) ≤
        Sieve.generate (Presieve.singleton ((Phi315 Z W).map ((CenterZW Z W).mor j))) := by
  intro j
  change Sieve.functorPushforward (Phi315 Z W) (Sieve.functorPushforward (CatToDila Z) (W.N j)) ≤
      Sieve.generate (Presieve.singleton ((Phi315 Z W).map ((CatToDila Z).map (W.mor j))))
  rw [← Sieve.functorPushforward_comp]
  exact functorPushforward_singleton_congr (Phi315_spec Z W) (W.N j) (W.mor j)
    (CatToDila_image_sieve_le_singleton (Z.sum W) (Sum.inr j))

/-- **Proposition 3.15 (iv), setup.** The unique functor `α'` with `Φ = α' ∘ β`. Built ahead of
Part (ii)/(iii) since Part (ii) depends on `Alpha'315_spec`. -/
noncomputable def Alpha'315 (Z W : Center C) : Dila (CenterZW Z W) ⥤ Dila (Z.sum W) :=
  DilaLift (CenterZW Z W) (Phi315 Z W)
    (Phi315_isSigmaRegular Z W) (Phi315_hsieve Z W)

theorem Alpha'315_spec (Z W : Center C) :
    Beta315 Z W ⋙ Alpha'315 Z W = Phi315 Z W :=
  DilaLift_fac (CenterZW Z W) (Phi315 Z W)
    (Phi315_isSigmaRegular Z W) (Phi315_hsieve Z W)

theorem Alpha'315_unique (Z W : Center C) (G : Dila (CenterZW Z W) ⥤ Dila (Z.sum W))
    (hG : Beta315 Z W ⋙ G = Phi315 Z W) :
    G = Alpha'315 Z W :=
  DilaLift_unique (CenterZW Z W) (Phi315 Z W)
    (Phi315_isSigmaRegular Z W) (Phi315_hsieve Z W) G hG

/-- `Φ` sends the `Θ`-image of a `C`-object to the `Θ'`-image, on the nose (both `Θ ⋙ Φ` and
`Θ'` are functors `C ⥤ Dila (Z.sum W)`, so the object part of `Phi315_spec` needs no `eqToHom`). -/
theorem Phi315_obj_eq (Z W : Center C) (X : C) :
    (Phi315 Z W).obj ((CatToDila Z).obj X) = (CatToDila (Z.sum W)).obj X :=
  congrArg (fun H : C ⥤ Dila (Z.sum W) => H.obj X) (Phi315_spec Z W)

/-- The map-level companion of `Phi315_obj_eq`: since `Φ` is opaque (built via `.choose`), this
needs the `eqToHom`-sandwiched form, exactly as in `restrictPhi`'s own object/map lemmas. -/
theorem Phi315_map_eq (Z W : Center C) {X Y : C} (f : X ⟶ Y) :
    (Phi315 Z W).map ((CatToDila Z).map f) =
      eqToHom (Phi315_obj_eq Z W X) ≫ (CatToDila (Z.sum W)).map f ≫
        eqToHom (Phi315_obj_eq Z W Y).symm := by
  have h := Functor.congr_hom (Phi315_spec Z W) f
  rw [Functor.comp_map] at h
  rw [h]

/-- The "flattened" comparison functor `Dila Z → C[{dᵢ}_{I'}⁻¹]`, obtained by composing `Φ`
with `DilaToLoc (Z.sum W)`. -/
def comparisonToLocalization (Z W : Center C) : Dila Z ⥤ (CenterMorphismProperty (Z.sum
    W)).Localization :=
  Phi315 Z W ⋙ DilaToLoc (Z.sum W)

theorem comparisonToLocalization_obj (Z W : Center C) (X : C) :
    (comparisonToLocalization Z W).obj ((CatToDila Z).obj X) = (CenterMorphismProperty (Z.sum
      W)).Q.obj X := by
  change (DilaToLoc (Z.sum W)).obj ((Phi315 Z W).obj ((CatToDila Z).obj X)) = _
  rw [Phi315_obj_eq]
  exact congrArg (fun H : C ⥤ (CenterMorphismProperty (Z.sum W)).Localization => H.obj X)
    (CatToDila_comp_DilaToLoc (Z.sum W))

/-- `comparisonToLocalization` sends the `Θ`-image of a `C`-morphism to its direct image under
`(CenterMorphismProperty (Z.sum W)).Q`, up to the object-identification
    `comparisonToLocalization_obj`. -/
theorem comparisonToLocalization_map (Z W : Center C) {X Y : C} (f : X ⟶ Y) :
    (comparisonToLocalization Z W).map ((CatToDila Z).map f) =
      eqToHom (comparisonToLocalization_obj Z W X) ≫ (CenterMorphismProperty (Z.sum W)).Q.map f ≫
        eqToHom (comparisonToLocalization_obj Z W Y).symm := by
  change (DilaToLoc (Z.sum W)).map ((Phi315 Z W).map ((CatToDila Z).map f)) = _
  rw [Phi315_map_eq]
  have h := Functor.congr_hom (CatToDila_comp_DilaToLoc (Z.sum W)) f
  rw [Functor.comp_map] at h
  simp only [Functor.map_comp, eqToHom_map]
  rw [h]
  rfl

/-- **Part of "Fact 2.14 applied a third time".** `comparisonToLocalization` is regular for
    `CenterZW Z W`: its
image-center morphism property is exactly the `Sum.inr`-image of `(CenterMorphismProperty
(Z.sum W)).Q`'s own generators (via `comparisonToLocalization_map`), which are already invertible by
`MorphismProperty.Q_inverts`, so `isoMorphismProperty_Q_faithful` applies directly — no
appeal to `Φ`'s own faithfulness (which is not known) is needed. -/
theorem comparisonToLocalization_isSigmaRegular (Z W : Center C) :
    IsSigmaRegular (CenterZW Z W) (comparisonToLocalization Z W) := by
  change (ImageCenterMorphismProperty (CenterZW Z W) (comparisonToLocalization Z W)).Q.Faithful
  apply isoMorphismProperty_Q_faithful
  rintro X Y f ⟨j, hj⟩
  have hX : X = (comparisonToLocalization Z W).obj ((CatToDila Z).obj (W.dom j)) := congrArg
    Sigma.fst hj
  have hY : Y = (comparisonToLocalization Z W).obj ((CatToDila Z).obj (W.cod j)) := congrArg
    (fun s => s.2.1) hj
  subst X
  subst Y
  have hf : f = (comparisonToLocalization Z W).map ((CatToDila Z).map (W.mor j)) := by cases hj; rfl
  rw [hf, comparisonToLocalization_map]
  have : IsIso ((CenterMorphismProperty (Z.sum W)).Q.map (W.mor j)) :=
    CategoryTheory.MorphismProperty.Q_inverts _ (W.mor j) ⟨Sum.inr j, rfl⟩
  infer_instance

/-- `comparisonToLocalization` precomposed with `Θ` is *literally* `(CenterMorphismProperty
    (Z.sum W)).Q`, as a
functor equality (both sides `C ⥤ (CenterMorphismProperty (Z.sum W)).Localization`) — combining
`Phi315_spec` (`Θ ⋙ Φ = Θ'`) with `CatToDila_comp_DilaToLoc (Z.sum W)`. -/
theorem comparisonToLocalization_comp (Z W : Center C) :
    CatToDila Z ⋙ comparisonToLocalization Z W = (CenterMorphismProperty (Z.sum W)).Q := by
  change CatToDila Z ⋙ (Phi315 Z W ⋙ DilaToLoc (Z.sum W)) = _
  rw [← Functor.assoc, Phi315_spec, CatToDila_comp_DilaToLoc]
  rfl

/-- The sieve condition needed to extend `comparisonToLocalization` along `CatToDila (CenterZW
    Z W)`: `(CatToDila Z
⋙ comparisonToLocalization Z W).map (W.mor j)` is already an isomorphism, so its generated
    sieve is the top sieve. -/
theorem comparisonToLocalization_hsieve (Z W : Center C) :
    ∀ j : (CenterZW Z W).I,
      Sieve.functorPushforward (comparisonToLocalization Z W) ((CenterZW Z W).N j) ≤
        Sieve.generate (Presieve.singleton ((comparisonToLocalization Z W).map ((CenterZW Z
          W).mor j))) := by
  intro j
  change Sieve.functorPushforward (comparisonToLocalization Z W) (Sieve.functorPushforward
    (CatToDila Z) (W.N j)) ≤
      Sieve.generate (Presieve.singleton ((comparisonToLocalization Z W).map ((CatToDila
        Z).map (W.mor j))))
  rw [← Sieve.functorPushforward_comp]
  have hiso : IsIso ((CatToDila Z ⋙ comparisonToLocalization Z W).map (W.mor j)) := by
    rw [comparisonToLocalization_comp]
    exact CategoryTheory.MorphismProperty.Q_inverts _ (W.mor j) ⟨Sum.inr j, rfl⟩
  intro Y f _
  refine ⟨(CatToDila Z ⋙ comparisonToLocalization Z W).obj (W.dom j),
    f ≫ inv ((CatToDila Z ⋙ comparisonToLocalization Z W).map (W.mor j)),
    (CatToDila Z ⋙ comparisonToLocalization Z W).map (W.mor j), Presieve.singleton_self _, ?_⟩
  simp

/-- **The unique extension of `comparisonToLocalization` along `β`.** By
    `Dila_universal_property (CenterZW Z W)
(comparisonToLocalization Z W) comparisonToLocalization_isSigmaRegular
    comparisonToLocalization_hsieve`. -/
noncomputable def H315 (Z W : Center C) :
    Dila (CenterZW Z W) ⥤ (CenterMorphismProperty (Z.sum W)).Localization :=
  (Dila_universal_property (CenterZW Z W) (comparisonToLocalization Z W)
      (comparisonToLocalization_isSigmaRegular Z W) (comparisonToLocalization_hsieve Z W)).choose

theorem H315_spec (Z W : Center C) :
    Beta315 Z W ⋙ H315 Z W = comparisonToLocalization Z W :=
  (Dila_universal_property (CenterZW Z W) (comparisonToLocalization Z W)
      (comparisonToLocalization_isSigmaRegular Z W) (comparisonToLocalization_hsieve Z
        W)).choose_spec.1

/-- `H315` agrees with `α' ⋙ DilaToLoc (Z.sum W)`: both extend `comparisonToLocalization` along `β`
(`β ⋙ (α' ⋙ DilaToLoc (Z.sum W)) = (β ⋙ α') ⋙ DilaToLoc (Z.sum W) = Φ ⋙ DilaToLoc (Z.sum W)
= comparisonToLocalization`, using `Alpha'315_spec`), so by the uniqueness half of the same
    universal property used
to build `H315`, they coincide. `Alpha'315` only needs Part (i), so this holds unconditionally. -/
theorem H315_eq (Z W : Center C) :
    H315 Z W = Alpha'315 Z W ⋙ DilaToLoc (Z.sum W) :=
  ((Dila_universal_property (CenterZW Z W) (comparisonToLocalization Z W)
      (comparisonToLocalization_isSigmaRegular Z W) (comparisonToLocalization_hsieve Z
        W)).choose_spec.2
    (Alpha'315 Z W ⋙ DilaToLoc (Z.sum W))
    (show Beta315 Z W ⋙ (Alpha'315 Z W ⋙ DilaToLoc (Z.sum W)) = comparisonToLocalization Z W by
      rw [← Functor.assoc, Alpha'315_spec]; rfl)).symm

theorem BetaComp315_hsieve (Z W : Center C) :
    ∀ k : (Z.sum W).I,
      Sieve.functorPushforward (CatToDila Z ⋙ Beta315 Z W) ((Z.sum W).N k) ≤
        Sieve.generate
          (Presieve.singleton ((CatToDila Z ⋙ Beta315 Z W).map ((Z.sum W).mor k))) := by
  rintro (i | j)
  · exact CatToDila_comp_image_sieve_le_singleton Z (Beta315 Z W) i
  · change Sieve.functorPushforward (CatToDila Z ⋙ Beta315 Z W) (W.N j) ≤
        Sieve.generate (Presieve.singleton ((CatToDila Z ⋙ Beta315 Z W).map (W.mor j)))
    rw [Sieve.functorPushforward_comp]
    exact CatToDila_image_sieve_le_singleton (CenterZW Z W) j

/-- **Proposition 3.15 (iii), setup.** -/
noncomputable def Alpha315 (Z W : Center C)
    (hreg : IsSigmaRegular (Z.sum W) (CatToDila Z ⋙ Beta315 Z W)) :
    Dila (Z.sum W) ⥤ Dila (CenterZW Z W) :=
  (Dila_universal_property (Z.sum W) (CatToDila Z ⋙ Beta315 Z W)
      hreg (BetaComp315_hsieve Z W)).choose

theorem Alpha315_spec (Z W : Center C)
    (hreg : IsSigmaRegular (Z.sum W) (CatToDila Z ⋙ Beta315 Z W)) :
    CatToDila (Z.sum W) ⋙ Alpha315 Z W hreg = CatToDila Z ⋙ Beta315 Z W :=
  (Dila_universal_property (Z.sum W) (CatToDila Z ⋙ Beta315 Z W)
      hreg (BetaComp315_hsieve Z W)).choose_spec.1

theorem Alpha315_unique (Z W : Center C)
    (hreg : IsSigmaRegular (Z.sum W) (CatToDila Z ⋙ Beta315 Z W))
    (G : Dila (Z.sum W) ⥤ Dila (CenterZW Z W))
    (hG : CatToDila (Z.sum W) ⋙ G = CatToDila Z ⋙ Beta315 Z W) :
    G = Alpha315 Z W hreg :=
  (Dila_universal_property (Z.sum W) (CatToDila Z ⋙ Beta315 Z W)
      hreg (BetaComp315_hsieve Z W)).choose_spec.2 G hG

/-- General form of `CatToDila_isSigmaRegular_sum_inl`: regularity for the `Z`-part transfers
from regularity of `Z.sum W` for *any* target functor `F`, not just `CatToDila (Z.sum W)`. -/
lemma IsSigmaRegular_sum_inl_of (Z W : Center C) (F : C ⥤ D) (hF : IsSigmaRegular (Z.sum W) F) :
    IsSigmaRegular Z F := by
  exact localizationFaithful_of_le (ImageCenterMorphismProperty_sum_inl_le Z W F) hF

/-- **Proposition 3.15 (v), part 1.** `Φ ∘ α = β` (equivalently `Φ ⋙ α = β` in Lean's
left-to-right composition). Conditional on item 2 (`hreg`). -/
theorem Phi315_comp_Alpha315 (Z W : Center C)
    (hreg : IsSigmaRegular (Z.sum W) (CatToDila Z ⋙ Beta315 Z W)) :
    Phi315 Z W ⋙ Alpha315 Z W hreg = Beta315 Z W := by
  apply Dila_factor_unique Z (CatToDila Z ⋙ Beta315 Z W) (Phi315 Z W ⋙ Alpha315 Z W hreg)
    (Beta315 Z W)
  · change CatToDila Z ⋙ Phi315 Z W ⋙ Alpha315 Z W hreg = CatToDila Z ⋙ Beta315 Z W
    rw [← Functor.assoc, Phi315_spec, Alpha315_spec]
  · rfl
  · exact IsSigmaRegular_sum_inl_of Z W (CatToDila Z ⋙ Beta315 Z W) hreg

/-- **Proposition 3.15 (v), part 2 / `α ∘ α' = id`.** `Alpha315 Z W ⋙ Alpha'315 Z W = 𝟭 _`
(i.e. `α' ∘ α = 𝟭` in the paper's right-to-left composition). Conditional on item 2 (`hreg`). -/
theorem Alpha315_comp_Alpha'315 (Z W : Center C)
    (hreg : IsSigmaRegular (Z.sum W) (CatToDila Z ⋙ Beta315 Z W)) :
    Alpha315 Z W hreg ⋙ Alpha'315 Z W = 𝟭 (Dila (Z.sum W)) := by
  apply Dila_factor_unique (Z.sum W) (CatToDila (Z.sum W)) (Alpha315 Z W hreg ⋙ Alpha'315 Z W)
    (𝟭 (Dila (Z.sum W)))
  · change CatToDila (Z.sum W) ⋙ Alpha315 Z W hreg ⋙ Alpha'315 Z W = CatToDila (Z.sum W)
    rw [← Functor.assoc, Alpha315_spec, Functor.assoc, Alpha'315_spec, Phi315_spec]
  · exact Functor.comp_id _
  · exact CatToDila_isSigmaRegular (Z.sum W)

/-- **Proposition 3.15 (v), part 3 / `α' ∘ α = id`.** `Alpha'315 Z W ⋙ Alpha315 Z W = 𝟭 _`
(i.e. `α ∘ α' = 𝟭` in the paper's right-to-left composition). Conditional on item 2 (`hreg`). -/
theorem Alpha'315_comp_Alpha315 (Z W : Center C)
    (hreg : IsSigmaRegular (Z.sum W) (CatToDila Z ⋙ Beta315 Z W)) :
    Alpha'315 Z W ⋙ Alpha315 Z W hreg = 𝟭 (Dila (CenterZW Z W)) := by
  apply Dila_factor_unique (CenterZW Z W) (Beta315 Z W) (Alpha'315 Z W ⋙ Alpha315 Z W hreg)
    (𝟭 (Dila (CenterZW Z W)))
  · change Beta315 Z W ⋙ Alpha'315 Z W ⋙ Alpha315 Z W hreg = Beta315 Z W
    rw [← Functor.assoc, Alpha'315_spec, Phi315_comp_Alpha315]
  · exact Functor.comp_id _
  · exact CatToDila_isSigmaRegular (CenterZW Z W)

/-- **Proposition 3.15 (vi).** The mutually-inverse `Alpha315 Z W` and `Alpha'315 Z W` assemble
into an isomorphism of categories `Dila (CenterZW Z W) ≅ Dila (Z.sum W)` (as objects of `Cat`,
i.e. a pair of mutually-inverse functors — this needs only `hom_inv_id`/`inv_hom_id`, not the
fuller coherence of a `CategoryTheory.Equivalence`). Conditional on item 2 (`hreg`). -/
noncomputable def Iso315 (Z W : Center C)
    (hreg : IsSigmaRegular (Z.sum W) (CatToDila Z ⋙ Beta315 Z W)) :
    Cat.of (Dila (CenterZW Z W)) ≅ Cat.of (Dila (Z.sum W)) where
  hom := (Alpha'315 Z W).toCatHom
  inv := (Alpha315 Z W hreg).toCatHom
  hom_inv_id := Cat.ext (Alpha'315_comp_Alpha315 Z W hreg)
  inv_hom_id := Cat.ext (Alpha315_comp_Alpha'315 Z W hreg)

/-! ### Proposition 3.18

For a fixed center `{[Nᵢ,dᵢ]}_{i∈I}` on `C` and an alternative choice of sieves `{N'ᵢ}_{i∈I}`
(same generators `dᵢ`), the dilatation for the *combined* two-copy center
`{[Nᵢ,dᵢ]}_{i∈I}, {[N'ᵢ,dᵢ]}_{i∈I}` identifies with the dilatation for the single center with
sieves `Nᵢ ∪ N'ᵢ`. -/
/-- Same generators `{dᵢ}` as `Z`, with an alternative choice of sieves `N'`. Represents
`{[N'ᵢ,dᵢ]}_{i∈I}`. -/
def Center.altSieve (Z : Center C) (N' : ∀ i : Z.I, Sieve (C := C) (Z.cod i)) : Center C :=
  { Z with N := N' }

/-- Same generators as `Z`, with sieves `Nᵢ ∪ N'ᵢ`. Represents `{[N''ᵢ,dᵢ]}_{i∈I}` from
Proposition 3.18. -/
def Center.sieveUnion (Z : Center C) (N' : ∀ i : Z.I, Sieve (C := C) (Z.cod i)) : Center C :=
  { Z with N := fun i => Z.N i ⊔ N' i }

variable {D : Type u} [Category.{v'} D]

lemma ImageCenterMorphismProperty_altSieve (Z : Center C)
    (N' : ∀ i : Z.I, Sieve (C := C) (Z.cod i)) (F : C ⥤ D) :
    ImageCenterMorphismProperty (Z.altSieve N') F = ImageCenterMorphismProperty Z F := rfl

lemma ImageCenterMorphismProperty_sieveUnion (Z : Center C)
    (N' : ∀ i : Z.I, Sieve (C := C) (Z.cod i)) (F : C ⥤ D) :
    ImageCenterMorphismProperty (Z.sieveUnion N') F = ImageCenterMorphismProperty Z F := rfl

/-- The combined two-copy center `Z.sum (Z.altSieve N')` shares its `ImageCenterMorphismProperty`
with `Z` alone : both `Sum.inl` and `Sum.inr` witnesses reduce to the *same* underlying generator
data, since `Z.altSieve N'` shares `dom`/`cod`/`mor` with `Z`. -/
lemma ImageCenterMorphismProperty_sum_altSieve_self (Z : Center C)
    (N' : ∀ i : Z.I, Sieve (C := C) (Z.cod i)) (F : C ⥤ D) :
    ImageCenterMorphismProperty (Z.sum (Z.altSieve N')) F = ImageCenterMorphismProperty Z F := by
  funext X Y f
  apply propext
  constructor
  · rintro ⟨i | i, hi⟩ <;> exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨Sum.inl i, hi⟩

lemma IsSigmaRegular_altSieve (Z : Center C) (N' : ∀ i : Z.I, Sieve (C := C) (Z.cod i))
    (F : C ⥤ D) :
    IsSigmaRegular (Z.altSieve N') F ↔ IsSigmaRegular Z F := by
  unfold IsSigmaRegular
  rw [ImageCenterMorphismProperty_altSieve]

lemma CenterMorphismProperty_altSieve (Z : Center C) (N' : ∀ i : Z.I, Sieve (C := C) (Z.cod i)) :
    CenterMorphismProperty (Z.altSieve N') = CenterMorphismProperty Z := rfl

/-- **Fact 3.13.** For a family of subsieves `Mᵢ ⊆ Nᵢ`, the canonical comparison functor
`φ : C[{(dᵢ)⁻¹∘Mᵢ}] ⥤ C[{(dᵢ)⁻¹∘Nᵢ}]`. -/
noncomputable def Fact313Phi (Z : Center C) (M : ∀ i : Z.I, Sieve (C := C) (Z.cod i))
    (hM : ∀ i, M i ≤ Z.N i) :
    Dila (Z.altSieve M) ⥤ Dila Z :=
  (Dila_universal_property (Z.altSieve M) (CatToDila Z)
    ((IsSigmaRegular_altSieve Z M (CatToDila Z)).2 (CatToDila_isSigmaRegular Z))
    (fun i => by
      change Sieve.functorPushforward (CatToDila Z) (M i) ≤
        Sieve.generate (Presieve.singleton ((CatToDila Z).map (Z.mor i)))
      exact le_trans (Sieve.functorPushforward_monotone (CatToDila Z) (Z.cod i) (hM i))
        (CatToDila_image_sieve_le_singleton Z i))).choose

theorem Fact313Phi_spec (Z : Center C) (M : ∀ i : Z.I, Sieve (C := C) (Z.cod i))
    (hM : ∀ i, M i ≤ Z.N i) :
    CatToDila (Z.altSieve M) ⋙ Fact313Phi Z M hM = CatToDila Z :=
  (Dila_universal_property (Z.altSieve M) (CatToDila Z)
    ((IsSigmaRegular_altSieve Z M (CatToDila Z)).2 (CatToDila_isSigmaRegular Z))
    (fun i => by
      change Sieve.functorPushforward (CatToDila Z) (M i) ≤
        Sieve.generate (Presieve.singleton ((CatToDila Z).map (Z.mor i)))
      exact le_trans (Sieve.functorPushforward_monotone (CatToDila Z) (Z.cod i) (hM i))
        (CatToDila_image_sieve_le_singleton Z i))).choose_spec.1

/-- **Fact 3.13.** `φ` is faithful : `Dila_factor_unique` identifies `φ ⋙ DilaToLoc Z` with
`DilaToLoc (Z.altSieve M)` (both are the unique factorization of the *same* raw localization
functor, since `CenterMorphismProperty` doesn't see the sieve component at all), and the latter
is always faithful (Fact 2.14). -/
theorem Fact313Phi_faithful (Z : Center C) (M : ∀ i : Z.I, Sieve (C := C) (Z.cod i))
    (hM : ∀ i, M i ≤ Z.N i) :
    (Fact313Phi Z M hM).Faithful := by
  apply faithful_of_comp_faithful (Fact313Phi Z M hM) (DilaToLoc Z)
  have heq : Fact313Phi Z M hM ⋙ DilaToLoc Z = DilaToLoc (Z.altSieve M) := by
    apply Dila_factor_unique (Z.altSieve M) (LocalizationFunctor Z)
    · change CatToDila (Z.altSieve M) ⋙ Fact313Phi Z M hM ⋙ DilaToLoc Z = LocalizationFunctor Z
      rw [← Functor.assoc, Fact313Phi_spec, CatToDila_comp_DilaToLoc]
    · change CatToDila (Z.altSieve M) ⋙ DilaToLoc (Z.altSieve M) = LocalizationFunctor Z
      rw [CatToDila_comp_DilaToLoc]
      rfl
    · exact (IsSigmaRegular_altSieve Z M (LocalizationFunctor Z)).2
        (LocalizationFunctor_isSigmaRegular Z)
  rw [heq]
  exact DilaToLoc_faithful (Z.altSieve M)

lemma IsSigmaRegular_sieveUnion (Z : Center C) (N' : ∀ i : Z.I, Sieve (C := C) (Z.cod i))
    (F : C ⥤ D) :
    IsSigmaRegular (Z.sieveUnion N') F ↔ IsSigmaRegular Z F := by
  unfold IsSigmaRegular
  rw [ImageCenterMorphismProperty_sieveUnion]

lemma IsSigmaRegular_sum_altSieve_self (Z : Center C) (N' : ∀ i : Z.I, Sieve (C := C) (Z.cod i))
    (F : C ⥤ D) :
    IsSigmaRegular (Z.sum (Z.altSieve N')) F ↔ IsSigmaRegular Z F := by
  unfold IsSigmaRegular
  rw [ImageCenterMorphismProperty_sum_altSieve_self]

/-- The sieve condition needed to extend `CatToDila (Z.sieveUnion N')` along
`CatToDila (Z.sum (Z.altSieve N'))` (Fact 3.17, via `Sieve.functorPushforward_union`, combined
with Proposition 3.5 applied to both `Z` and `Z.altSieve N'` inside the sum). -/
theorem CatToDila_sieveUnion_hsieve (Z : Center C) (N' : ∀ i : Z.I, Sieve (C := C) (Z.cod i)) :
    ∀ i : Z.I,
      Sieve.functorPushforward (CatToDila (Z.sum (Z.altSieve N'))) ((Z.sieveUnion N').N i) ≤
        Sieve.generate
          (Presieve.singleton
            ((CatToDila (Z.sum (Z.altSieve N'))).map ((Z.sieveUnion N').mor i))) := by
  intro i
  change Sieve.functorPushforward (CatToDila (Z.sum (Z.altSieve N'))) (Z.N i ⊔ N' i) ≤ _
  rw [Sieve.functorPushforward_union]
  exact sup_le (CatToDila_sum_hsieve_inl Z (Z.altSieve N') i)
    (CatToDila_sum_hsieve_inr Z (Z.altSieve N') i)

/-- **Proposition 3.18, direction one.** The unique functor
`α : Dila (Z.sieveUnion N') ⥤ Dila (Z.sum (Z.altSieve N'))` extending
`CatToDila (Z.sum (Z.altSieve N'))` along `CatToDila (Z.sieveUnion N')`. -/
noncomputable def Alpha318 (Z : Center C) (N' : ∀ i : Z.I, Sieve (C := C) (Z.cod i)) :
    Dila (Z.sieveUnion N') ⥤ Dila (Z.sum (Z.altSieve N')) :=
  (Dila_universal_property (Z.sieveUnion N') (CatToDila (Z.sum (Z.altSieve N')))
      ((IsSigmaRegular_sieveUnion Z N' _).2 (CatToDila_isSigmaRegular_sum_inl Z (Z.altSieve N')))
      (CatToDila_sieveUnion_hsieve Z N')).choose

theorem Alpha318_spec (Z : Center C) (N' : ∀ i : Z.I, Sieve (C := C) (Z.cod i)) :
    CatToDila (Z.sieveUnion N') ⋙ Alpha318 Z N' = CatToDila (Z.sum (Z.altSieve N')) :=
  (Dila_universal_property (Z.sieveUnion N') (CatToDila (Z.sum (Z.altSieve N')))
      ((IsSigmaRegular_sieveUnion Z N' _).2 (CatToDila_isSigmaRegular_sum_inl Z (Z.altSieve N')))
      (CatToDila_sieveUnion_hsieve Z N')).choose_spec.1

/-- The sieve condition needed to extend `CatToDila (Z.sieveUnion N')` along
`CatToDila (Z.sum (Z.altSieve N'))`. -/
theorem CatToDila_sum_altSieve_hsieve (Z : Center C) (N' : ∀ i : Z.I, Sieve (C := C) (Z.cod i)) :
    ∀ k : Z.I ⊕ Z.I,
      Sieve.functorPushforward (CatToDila (Z.sieveUnion N')) ((Z.sum (Z.altSieve N')).N k) ≤
        Sieve.generate
          (Presieve.singleton
            ((CatToDila (Z.sieveUnion N')).map ((Z.sum (Z.altSieve N')).mor k))) := by
  rintro (i | i)
  · apply le_trans _ (CatToDila_image_sieve_le_singleton (Z.sieveUnion N') i)
    apply Sieve.functorPushforward_monotone
    exact le_sup_left
  · apply le_trans _ (CatToDila_image_sieve_le_singleton (Z.sieveUnion N') i)
    apply Sieve.functorPushforward_monotone
    exact le_sup_right

/-- **Proposition 3.18, direction two.** The unique functor
`α' : Dila (Z.sum (Z.altSieve N')) ⥤ Dila (Z.sieveUnion N')` extending
`CatToDila (Z.sieveUnion N')` along `CatToDila (Z.sum (Z.altSieve N'))`. -/
noncomputable def Alpha'318 (Z : Center C) (N' : ∀ i : Z.I, Sieve (C := C) (Z.cod i)) :
    Dila (Z.sum (Z.altSieve N')) ⥤ Dila (Z.sieveUnion N') :=
  (Dila_universal_property (Z.sum (Z.altSieve N')) (CatToDila (Z.sieveUnion N'))
      ((IsSigmaRegular_sum_altSieve_self Z N' _).2
        ((IsSigmaRegular_sieveUnion Z N' _).2 (CatToDila_isSigmaRegular (Z.sieveUnion N'))))
      (CatToDila_sum_altSieve_hsieve Z N')).choose

theorem Alpha'318_spec (Z : Center C) (N' : ∀ i : Z.I, Sieve (C := C) (Z.cod i)) :
    CatToDila (Z.sum (Z.altSieve N')) ⋙ Alpha'318 Z N' = CatToDila (Z.sieveUnion N') :=
  (Dila_universal_property (Z.sum (Z.altSieve N')) (CatToDila (Z.sieveUnion N'))
      ((IsSigmaRegular_sum_altSieve_self Z N' _).2
        ((IsSigmaRegular_sieveUnion Z N' _).2 (CatToDila_isSigmaRegular (Z.sieveUnion N'))))
      (CatToDila_sum_altSieve_hsieve Z N')).choose_spec.1

theorem Alpha318_comp_Alpha'318 (Z : Center C) (N' : ∀ i : Z.I, Sieve (C := C) (Z.cod i)) :
    Alpha318 Z N' ⋙ Alpha'318 Z N' = 𝟭 (Dila (Z.sieveUnion N')) := by
  apply Dila_factor_unique (Z.sieveUnion N') (CatToDila (Z.sieveUnion N'))
    (Alpha318 Z N' ⋙ Alpha'318 Z N') (𝟭 (Dila (Z.sieveUnion N')))
  · change CatToDila (Z.sieveUnion N') ⋙ Alpha318 Z N' ⋙ Alpha'318 Z N' =
        CatToDila (Z.sieveUnion N')
    rw [← Functor.assoc, Alpha318_spec, Alpha'318_spec]
  · exact Functor.comp_id _
  · exact CatToDila_isSigmaRegular (Z.sieveUnion N')

theorem Alpha'318_comp_Alpha318 (Z : Center C) (N' : ∀ i : Z.I, Sieve (C := C) (Z.cod i)) :
    Alpha'318 Z N' ⋙ Alpha318 Z N' = 𝟭 (Dila (Z.sum (Z.altSieve N'))) := by
  apply Dila_factor_unique (Z.sum (Z.altSieve N')) (CatToDila (Z.sum (Z.altSieve N')))
    (Alpha'318 Z N' ⋙ Alpha318 Z N') (𝟭 (Dila (Z.sum (Z.altSieve N'))))
  · change CatToDila (Z.sum (Z.altSieve N')) ⋙ Alpha'318 Z N' ⋙ Alpha318 Z N' =
        CatToDila (Z.sum (Z.altSieve N'))
    rw [← Functor.assoc, Alpha'318_spec, Alpha318_spec]
  · exact Functor.comp_id _
  · exact CatToDila_isSigmaRegular (Z.sum (Z.altSieve N'))

/-- **Proposition 3.18.** `Dila (Z.sum (Z.altSieve N'))` (i.e.
`C[{(dᵢ)⁻¹∘Nᵢ}, {(dᵢ)⁻¹∘N'ᵢ}]`) is isomorphic to `Dila (Z.sieveUnion N')` (i.e.
`C[{(dᵢ)⁻¹∘(Nᵢ∪N'ᵢ)}]`). -/
noncomputable def Iso318 (Z : Center C) (N' : ∀ i : Z.I, Sieve (C := C) (Z.cod i)) :
    Cat.of (Dila (Z.sum (Z.altSieve N'))) ≅ Cat.of (Dila (Z.sieveUnion N')) where
  hom := (Alpha'318 Z N').toCatHom
  inv := (Alpha318 Z N').toCatHom
  hom_inv_id := Cat.ext (Alpha'318_comp_Alpha318 Z N')
  inv_hom_id := Cat.ext (Alpha318_comp_Alpha'318 Z N')

end CategoryTheory.Dilatations
