/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arnaud Mayeux
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Sites.Sieves.Basic
import Mathlib.CategoryTheory.Sites.Sieves.Functoriality
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Setoid.Basic
import Mathlib.CategoryTheory.Quotient
import Mathlib.CategoryTheory.ComposableArrows.Basic
import Mathlib.Tactic.Linarith
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Init.Data.Nat.Basic
import Init.Data.Int.Order
import Mathlib.Data.Nat.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.CategoryTheory.Widesubcategory
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Combinatorics.Quiver.Covering
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.LinearCombination
noncomputable section


open CategoryTheory
open Finset
open CategoryTheory ComposableArrows
open CategoryTheory.Localization.Construction
universe v u v' pu pv
namespace CategoryTheory

/-- **Definition 2.9.** A center `{[Nᵢ,dᵢ]}ᵢ∈I` in `C`. -/
structure Center (C : Type u) [Category.{v} C] where
  I : Type u
  (nonempty : Nonempty I)
  dom : I → C
  cod : I → C
  mor : ∀ i : I, dom i ⟶ cod i
  N   : ∀ i : I, Sieve (C := C) (cod i)



variable {C : Type u} [Category.{v} C]
variable (Z : Center C)


def IsCenterMor (f : Σ X Y : C, X ⟶ Y) : Prop :=
  ∃ i : Z.I, f = ⟨Z.dom i, Z.cod i, Z.mor i⟩


/-- The MorphismProperty corresponding to IsCenterMor. -/

def CenterMorphismProperty : MorphismProperty C := fun X Y f => IsCenterMor Z ⟨X, Y, f⟩

/-- The localized category obtained by formally inverting the morphisms in CenterMorphismProperty. -/

def CenterLocalization : Type u := (CenterMorphismProperty Z).Localization

/-- The canonical functor from C to the localization. -/


def LocalizationFunctor : C ⥤ (CenterMorphismProperty Z).Localization := (CenterMorphismProperty Z).Q

def CenterSievePair : Type (max u v) :=
  Σ i : Z.I, Σ X : C, { f : X ⟶ Z.cod i // Z.N i f }

def Quv := LocQuiver (CenterMorphismProperty Z)

def inv_in_path (p : CenterSievePair Z) :
    ιPaths (CenterMorphismProperty Z) (Z.cod p.1) ⟶
    ιPaths (CenterMorphismProperty Z) (Z.dom p.1) :=
  Localization.Construction.ψ₂ (CenterMorphismProperty Z)
    (Z.mor p.1) ⟨p.1, rfl⟩

def fraction_in_path_single (p : CenterSievePair Z) :
    ιPaths (CenterMorphismProperty Z) (p.2.1) ⟶
    ιPaths (CenterMorphismProperty Z) (Z.dom p.1) :=
  Localization.Construction.ψ₁ (CenterMorphismProperty Z) p.2.2.1 ≫
    inv_in_path Z p

def fraction_in_loc_single (p : CenterSievePair Z) :
objEquiv (CenterMorphismProperty Z) (p.2.1) ⟶
objEquiv (CenterMorphismProperty Z) (Z.dom p.1) :=
 (CategoryTheory.Quotient.functor
   (relations (CenterMorphismProperty Z))).map
      (fraction_in_path_single Z p)

def IsPairMor
    (f : Σ X Y : (CenterMorphismProperty Z).Localization, X ⟶ Y) : Prop :=
  ∃ p : CenterSievePair Z,
    f =
      ⟨objEquiv (CenterMorphismProperty Z) (p.2.1),
       objEquiv (CenterMorphismProperty Z) (Z.dom p.1),
       (CategoryTheory.Quotient.functor
          (relations (CenterMorphismProperty Z))).map
             (fraction_in_path_single Z p)⟩

structure PairMorWitness
    (Z : Center C)
    {X Y : (CenterMorphismProperty Z).Localization}
    (f : X ⟶ Y) where
  p : CenterSievePair Z
  eq :
    (⟨X,Y,f⟩ :
      Σ A B : (CenterMorphismProperty Z).Localization, A ⟶ B)
      =
    ⟨objEquiv (CenterMorphismProperty Z) (p.2.1),
     objEquiv (CenterMorphismProperty Z) (Z.dom p.1),
     (CategoryTheory.Quotient.functor
        (relations (CenterMorphismProperty Z))).map
       (fraction_in_path_single Z p)⟩

def FractionMorphismProperty :
       MorphismProperty (CenterMorphismProperty Z).Localization  :=
          fun X Y f => IsPairMor Z ⟨X, Y, f⟩


structure OriginalWitness
    (Z : Center C)
    {X Y : (CenterMorphismProperty Z).Localization}
    (f : X ⟶ Y) where
  g :
    (objEquiv (CenterMorphismProperty Z)).symm X ⟶
      (objEquiv (CenterMorphismProperty Z)).symm Y

  eq :
    f =
      (CenterMorphismProperty Z).Q.map g


inductive GeneratorMorphismData
    (Z : Center C)
    {X Y : (CenterMorphismProperty Z).Localization}
    (f : X ⟶ Y)
    : Type (max u v)

| fraction :
    PairMorWitness Z f →
    GeneratorMorphismData Z f

| original :
    OriginalWitness Z f →
    GeneratorMorphismData Z f

@[instance_reducible]
def GeneratorQuiver : Quiver (CenterMorphismProperty Z).Localization where
  Hom X Y :=
    Σ f : X ⟶ Y, GeneratorMorphismData Z f


def GeneratorObjects :=
  (CenterMorphismProperty Z).Localization

instance : Quiver (GeneratorObjects Z) :=
  GeneratorQuiver Z

def GeneratedCategory :=
  CategoryTheory.Paths (GeneratorObjects Z)

instance : Category (GeneratedCategory Z) :=
  Paths.categoryPaths _

def forgetGenerator : GeneratorObjects Z ⥤q (CenterMorphismProperty Z).Localization :=
  { obj := id,
    map := fun {_ _} f => f.1 }

def GeneratedToLocalization :
    GeneratedCategory Z ⥤ (CenterMorphismProperty Z).Localization :=
         CategoryTheory.Paths.lift (forgetGenerator Z)



def originalFactor
    {X Y : (CenterMorphismProperty Z).Localization}
    (f : X ⟶ Y)
    (h : OriginalWitness Z f) :
    (objEquiv (CenterMorphismProperty Z)).symm X ⟶
      (objEquiv (CenterMorphismProperty Z)).symm Y :=
  h.g



def DilaRel :
    HomRel (GeneratedCategory Z) :=
  fun {_ _} f g =>
    (GeneratedToLocalization Z).map f =
      (GeneratedToLocalization Z).map g

/-- **Definition 2.13 / Fact 2.11.** The dilatation `C[{(dᵢ)⁻¹∘Nᵢ}ᵢ∈I]`: objects are `C`'s
objects, morphisms are `{[Nᵢ,dᵢ]}`-fractions, composed via `Quotient` (Fact 2.11's associativity
of fraction composition is `Quotient.category`'s own well-definedness). -/
def Dila :=
  CategoryTheory.Quotient (DilaRel Z)

instance : Category (Dila Z) :=
  CategoryTheory.Quotient.category _

def DilaToLoc :
    Dila Z ⥤ (CenterMorphismProperty Z).Localization :=
  CategoryTheory.Quotient.lift
    (DilaRel Z)
    (GeneratedToLocalization Z)
    (by
      intro X Y f g h
      exact h)


instance : Congruence (DilaRel Z) where
  equivalence := by
    intro X Y
    constructor
    · intro f
      rfl
    · intro f₁ f₂ h
      exact h.symm
    · intro f₁ f₂ f₃ h₁ h₂
      dsimp [DilaRel] at h₁ h₂ ⊢
      exact h₁.trans h₂
  comp_left := by
    intro X Y Z f g g' h
    dsimp [DilaRel] at h ⊢
    rw [Functor.map_comp, Functor.map_comp, h]

  comp_right := by
    intro X Y Z f f' g h
    dsimp [DilaRel] at h ⊢
    rw [Functor.map_comp, Functor.map_comp, h]



lemma DilaToLoc_faithful :
    (DilaToLoc Z).Faithful := by
  constructor
  intro X Y f g
  change CategoryTheory.Quotient.Hom (DilaRel Z) X Y at f
  unfold CategoryTheory.Quotient.Hom at f
  change CategoryTheory.Quotient.Hom (DilaRel Z) X Y at g
  unfold CategoryTheory.Quotient.Hom at g
  intro h
  revert h
  refine Quot.inductionOn f ?_
  intro p
  refine Quot.inductionOn g ?_
  intro q h
  apply Quot.sound
  change
    (GeneratedToLocalization Z).map p =
    (GeneratedToLocalization Z).map q at h
  simpa using
    (CategoryTheory.HomRel.CompClosure.intro _ _
      (r := DilaRel Z)
      (𝟙 X.as)
      p
      q
      (𝟙 Y.as)
      h)



def GeneratedToDila :
    GeneratedCategory Z ⥤ Dila Z :=
  CategoryTheory.Quotient.functor (DilaRel Z)

instance GeneratedToDila_full :
    (GeneratedToDila Z).Full := by
  change (CategoryTheory.Quotient.functor (DilaRel Z)).Full
  infer_instance


def CToGeneratorQuiver :
    C ⥤q GeneratorObjects Z where
  obj X := objEquiv (CenterMorphismProperty Z) X
  map { _ _ } f :=
  ⟨(CenterMorphismProperty Z).Q.map f,
    GeneratorMorphismData.original
      {
        g := f
        eq := rfl
      }⟩


/-- **Proposition 3.1 (1).** The canonical functor `Θ : C ⥤ C'`. -/
def CatToDila :
    C ⥤ Dila Z where
  obj X :=
    Quotient.mk ((CToGeneratorQuiver Z).obj X)

  map {X Y} f :=
    (Quotient.functor (DilaRel Z)).map
      (Quiver.Hom.toPath ((CToGeneratorQuiver Z).map f))

  map_id X := by
    apply Quotient.sound
    change
      (GeneratedToLocalization Z).map
          (Quiver.Hom.toPath
            ⟨(CenterMorphismProperty Z).Q.map (𝟙 X), _⟩)
        =
      𝟙 _
    change (CenterMorphismProperty Z).Q.map (𝟙 X) = 𝟙 _
    exact Functor.map_id _ _

  map_comp f g := by

    apply Quotient.sound
    change
      (CenterMorphismProperty Z).Q.map (f ≫ g) =
        (CenterMorphismProperty Z).Q.map f ≫
        (CenterMorphismProperty Z).Q.map g
    simp

lemma CatToDila_comp_DilaToLoc :
    CatToDila Z ⋙ DilaToLoc Z = LocalizationFunctor Z := by
  refine Functor.ext (fun _ => rfl) ?_
  intro X Y f
  change (CenterMorphismProperty Z).Q.map f = 𝟙 _ ≫ (CenterMorphismProperty Z).Q.map f ≫ 𝟙 _
  simp

/-- **Fact 3.2.** A morphism whose image under a faithful functor is a bimorphism (mono and epi)
is itself a bimorphism. -/
theorem Fact_3_2 {A : Type*} [Category A] {B : Type*} [Category B] (F : A ⥤ B) [F.Faithful]
    {X Y : A} (f : X ⟶ Y) [Mono (F.map f)] [Epi (F.map f)] : Mono f ∧ Epi f :=
  ⟨F.mono_of_mono_map ‹_›, F.epi_of_epi_map ‹_›⟩

/-- **Proposition 3.3.** For `i : Z.I`, `Θ(dᵢ) = (CatToDila Z).map (Z.mor i)` is a bimorphism in
`Dila Z`. -/
theorem Prop_3_3 (i : Z.I) :
    Mono ((CatToDila Z).map (Z.mor i)) ∧ Epi ((CatToDila Z).map (Z.mor i)) := by
  haveI : IsIso ((DilaToLoc Z).map ((CatToDila Z).map (Z.mor i))) := by
    have hkey := Functor.congr_hom (CatToDila_comp_DilaToLoc Z) (Z.mor i)
    simp only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] at hkey
    rw [hkey]
    exact CategoryTheory.MorphismProperty.Q_inverts _ (Z.mor i) ⟨i, rfl⟩
  haveI := DilaToLoc_faithful Z
  exact Fact_3_2 (DilaToLoc Z) ((CatToDila Z).map (Z.mor i))

def CatToDilaSieve
    {X : C} (N : Sieve (C := C) X) :
    Sieve (C := Dila Z) ((CatToDila Z).obj X) :=
  Sieve.functorPushforward (CatToDila Z) N

lemma fraction_comp_mor (i : Z.I) (X : C)
    (m : X ⟶ Z.cod i)
    (hm : Z.N i m) :
    (fraction_in_loc_single Z ⟨i, ⟨X, ⟨m, hm⟩⟩⟩) ≫
      (CenterMorphismProperty Z).Q.map (Z.mor i)
    =
      (CenterMorphismProperty Z).Q.map m := by
  change (Quotient.functor (relations (CenterMorphismProperty Z))).map
      (fraction_in_path_single Z ⟨i, ⟨X, ⟨m, hm⟩⟩⟩) ≫
      (Quotient.functor (relations (CenterMorphismProperty Z))).map
        (ψ₁ (CenterMorphismProperty Z) (Z.mor i)) =
      (Quotient.functor (relations (CenterMorphismProperty Z))).map
        (ψ₁ (CenterMorphismProperty Z) m)
  rw [← Functor.map_comp]
  apply Quot.sound
  simpa only [fraction_in_path_single, inv_in_path, Category.assoc, Category.comp_id] using
    (relations.Winv₂ (Z.mor i) ⟨i, rfl⟩ |>
    HomRel.CompClosure.intro _ _ (ψ₁ (CenterMorphismProperty Z) m) _ _ (𝟙 _))


def fraction_in_generated (p : CenterSievePair Z) :
    (CToGeneratorQuiver Z).obj p.2.1 ⟶
    (CToGeneratorQuiver Z).obj (Z.dom p.1) :=
  ⟨
  fraction_in_loc_single Z p,
  GeneratorMorphismData.fraction ⟨p, rfl⟩
⟩

/-- **Proposition 3.1 (2), existence.** The fraction `b = dᵢ\n = [n∘l_{dᵢ}]` witnessing the
unique factorization `[n] = Θ(dᵢ) ∘ b`. -/
def fraction_in_dila_single (p : CenterSievePair Z) :
    (CatToDila Z).obj p.2.1 ⟶
    (CatToDila Z).obj (Z.dom p.1) :=
  (GeneratedToDila Z).map
    (Quiver.Hom.toPath (fraction_in_generated Z p))

/-- **Proposition 3.5.** `S^C'_Θ(Nᵢ) ⊂ S^C'_Θ(dᵢ)`. -/
theorem CatToDila_image_sieve_le_singleton (i : Z.I) :
    CatToDilaSieve Z (Z.N i) ≤
      Sieve.generate (Presieve.singleton ((CatToDila Z).map (Z.mor i))) := by

  intro X f hf
  dsimp [CatToDilaSieve, Sieve.functorPushforward] at hf

  rcases hf with ⟨Y, h, g, hg, rfl⟩

  have hfrac :
      fraction_in_dila_single Z ⟨i, ⟨Y, ⟨h, hg⟩⟩⟩ ≫
          (CatToDila Z).map (Z.mor i)
      =
      (CatToDila Z).map h := by
    apply Quotient.sound
    simp [DilaRel,
      CatToDila,
      GeneratedToLocalization,
      forgetGenerator,
      ]
    change
      fraction_in_loc_single Z ⟨i, ⟨Y, ⟨h, hg⟩⟩⟩ ≫
          (CenterMorphismProperty Z).Q.map (Z.mor i)
        =
      (CenterMorphismProperty Z).Q.map h

    exact fraction_comp_mor Z i Y h hg


  refine ⟨
      (CatToDila Z).obj (Z.dom i),
      g ≫ fraction_in_dila_single Z ⟨i, ⟨Y, ⟨h, hg⟩⟩⟩,
      (CatToDila Z).map (Z.mor i),
      Presieve.singleton_self _,
      ?_
    ⟩

  calc
    (g ≫ fraction_in_dila_single Z ⟨i, ⟨Y, ⟨h, hg⟩⟩⟩) ≫
        (CatToDila Z).map (Z.mor i)
        =
        g ≫
          (fraction_in_dila_single Z ⟨i, ⟨Y, ⟨h, hg⟩⟩⟩ ≫
            (CatToDila Z).map (Z.mor i)) := by
              rw [Category.assoc]

    _ = g ≫ (CatToDila Z).map h := by
          rw [hfrac]


lemma GeneratedCategory_morphism_induction
    (P :
      ∀ {X Y : GeneratedCategory Z},
        (f : X ⟶ Y) → Prop)
    (h_id :
      ∀ X, P (𝟙 X))
    (h_comp :
      ∀ {X Y W}
        (f : X ⟶ Y) (g : Y ⟶ W),
        P f → P g → P (f ≫ g))
        (h_gen :
  ∀ {A B : GeneratorObjects Z}
    (g : (GeneratorQuiver Z).Hom A B),
    P (Quiver.Hom.toPath g)) :
    ∀ {X Y : GeneratedCategory Z}
      (f : X ⟶ Y), P f := by

  intro X Y f
  apply CategoryTheory.Paths.induction
  · intro X
    exact h_id X
  · intro u v w p q hp
    exact h_comp p
      ((Paths.of (GeneratorObjects Z)).map q)
      hp
      (h_gen q)

variable {D : Type u} [Category.{v'} D]
variable (F : C ⥤ D)



/-- Morphisms in D obtained as images of the chosen central morphisms of C. -/
def IsImageCenterMor
    (F : C ⥤ D)
    (f : Σ X Y : D, X ⟶ Y) : Prop :=
  ∃ i : Z.I,
    f =
      ⟨F.obj (Z.dom i),
       F.obj (Z.cod i),
       F.map (Z.mor i)⟩

def ImageCenterMorphismProperty :
    MorphismProperty D :=
  fun X Y f =>
    IsImageCenterMor Z F ⟨X, Y, f⟩

/-- The localization of D obtained by formally inverting
    the images of the central morphisms. -/
def ImageCenterLocalization : Type u :=
  (ImageCenterMorphismProperty Z F).Localization

instance instCategoryImageCenterLocalization :
    Category (ImageCenterLocalization Z F) := by
  dsimp [ImageCenterLocalization]
  infer_instance

/-- The canonical functor from D to the localization. -/
def ImageCenterLocalizationFunctor :
    D ⥤ ImageCenterLocalization Z F :=
  (ImageCenterMorphismProperty Z F).Q

lemma exists_factor_D
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate (Presieve.singleton (F.map (Z.mor i)))) :
    ∀ (i : Z.I) (Y : D) (n : Y ⟶ F.obj (Z.cod i)),
      (Sieve.functorPushforward F (Z.N i)).arrows n →
      ∃ q : Y ⟶ F.obj (Z.dom i),
        q ≫ F.map (Z.mor i) = n := by

  intro i Y n hn

  have hgen :
      (Sieve.generate
        (Presieve.singleton (F.map (Z.mor i)))).arrows n :=
    hsieve i n hn

  rcases hgen with ⟨X, q, g, hg, hq⟩

  rcases hg with ⟨h, rfl⟩

  exact ⟨q, hq⟩
lemma unique_factor_D
    (hfaith :
      (ImageCenterLocalizationFunctor Z F).Faithful) :
    ∀ (i : Z.I) (Y : D)
      (q₁ q₂ : Y ⟶ F.obj (Z.dom i)),
      q₁ ≫ F.map (Z.mor i) =
        q₂ ≫ F.map (Z.mor i) →
      q₁ = q₂ := by
  intro i Y q₁ q₂ hq

  apply hfaith.map_injective

  haveI :
      IsIso ((ImageCenterLocalizationFunctor Z F).map
        (F.map (Z.mor i))) := by
    apply CategoryTheory.MorphismProperty.Q_inverts
    exact ⟨i, rfl⟩
  apply (cancel_mono
    ((ImageCenterLocalizationFunctor Z F).map
      (F.map (Z.mor i)))).1

  simpa only [Functor.map_comp] using
    congrArg
      (fun f => (ImageCenterLocalizationFunctor Z F).map f)
      hq


lemma exists_unique_factor_D
    (hfaith :
      (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate
            (Presieve.singleton (F.map (Z.mor i)))) :
    ∀ (i : Z.I) (Y : D) (n : Y ⟶ F.obj (Z.cod i)),
      (Sieve.functorPushforward F (Z.N i)).arrows n →
      ∃! q : Y ⟶ F.obj (Z.dom i),
        q ≫ F.map (Z.mor i) = n := by
  intro i Y n hn

  obtain ⟨q, hq⟩ := exists_factor_D Z F hsieve i Y n hn

  refine ⟨q, hq, ?_⟩

  intro q' hq'

  exact unique_factor_D Z F hfaith i Y q' q (by
    rw [hq', hq])

def uniqueFactor_D
    (hfaith :
      (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate
            (Presieve.singleton (F.map (Z.mor i))))
    (i : Z.I) (Y : C)
    (n : Y ⟶ Z.cod i)
    (hn : Z.N i n) :
    F.obj Y ⟶ F.obj (Z.dom i) := by

  have hn' :
      (Sieve.functorPushforward F (Z.N i)).arrows (F.map n) := by
    refine ⟨Y, n, 𝟙 _, hn, ?_⟩
    simp

  exact Classical.choose
    (exists_unique_factor_D Z F hfaith hsieve
      i (F.obj Y) (F.map n) hn')

def mapGenerator
    (hfaith :
      (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate
            (Presieve.singleton (F.map (Z.mor i))))
    {X Y : GeneratorObjects Z}
    (g : (GeneratorQuiver Z).Hom X Y) :
    F.obj ((objEquiv (CenterMorphismProperty Z)).symm X) ⟶
    F.obj ((objEquiv (CenterMorphismProperty Z)).symm Y) :=
by
  classical

  rcases g with ⟨f, hdata⟩

  cases hdata with

  | fraction hw =>
    have hX :
        (objEquiv (CenterMorphismProperty Z)).symm X = hw.p.2.1 := by
      exact congrArg (fun s => (objEquiv (CenterMorphismProperty Z)).symm s.1) hw.eq

    have hY :
        (objEquiv (CenterMorphismProperty Z)).symm Y = Z.dom hw.p.1 := by
      exact congrArg (fun s => (objEquiv (CenterMorphismProperty Z)).symm s.2.1) hw.eq

    rw [hX, hY]

    exact
      uniqueFactor_D Z F hfaith hsieve
        hw.p.1
        hw.p.2.1
        hw.p.2.2.1
        hw.p.2.2.2

  | original hw =>
      exact F.map hw.g

def localizationMap :
    (CenterMorphismProperty Z).Localization ⥤
      ImageCenterLocalization Z F := by

  apply Localization.Construction.lift
    (W := CenterMorphismProperty Z)
    (F ⋙ ImageCenterLocalizationFunctor Z F)

  intro X Y f hf

  rcases hf with ⟨i, hi⟩

  have hX : X = Z.dom i := by
    exact congrArg Sigma.fst hi

  have hY : Y = Z.cod i := by
    exact congrArg (fun s => s.2.1) hi

  subst X
  subst Y


  apply CategoryTheory.MorphismProperty.Q_inverts
  refine ⟨i, ?_⟩
  simp
  cases hi
  rfl





theorem localizationMap_comp_Q :
    (CenterMorphismProperty Z).Q ⋙ localizationMap Z F =
      F ⋙ ImageCenterLocalizationFunctor Z F := by
  apply Localization.Construction.fac


def Gq
    (hfaith :
      (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate
            (Presieve.singleton (F.map (Z.mor i)))) :
    GeneratorObjects Z ⥤q D :=
{
  obj := fun X =>
    F.obj ((objEquiv (CenterMorphismProperty Z)).symm X)

  map := by
    intro X Y g
    exact mapGenerator Z F hfaith hsieve g
}

def H
    (hfaith :
      (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate
            (Presieve.singleton (F.map (Z.mor i)))) :
    GeneratedCategory Z ⥤ D :=
  Paths.lift (Gq Z F hfaith hsieve)


lemma mapGenerator_original
    (hfaith :
      (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate
            (Presieve.singleton (F.map (Z.mor i))))
    {X Y : C} (f : X ⟶ Y) :
    mapGenerator Z F hfaith hsieve
      ⟨(CenterMorphismProperty Z).Q.map f,
        GeneratorMorphismData.original
          {
            g := f
            eq := rfl
          }⟩ =
      F.map f := by

  classical

  unfold mapGenerator
  rfl




lemma H_map_original
    (hfaith :
      (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate (Presieve.singleton (F.map (Z.mor i))))
    {X Y : C} (f : X ⟶ Y) :
    (H Z F hfaith hsieve).map
      ((CToGeneratorQuiver Z).map f).toPath =
      F.map f := by
      dsimp [H, Paths.lift]
      rw [show ((CToGeneratorQuiver Z).map f).toPath =
          Quiver.Path.nil.cons ((CToGeneratorQuiver Z).map f) by rfl]
      simp
      exact mapGenerator_original Z F hfaith hsieve f



lemma uniqueFactor_D_spec
    (hfaith : (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve : ∀ (i : Z.I),
      Sieve.functorPushforward F (Z.N i) ≤
        Sieve.generate (Presieve.singleton (F.map (Z.mor i))))
    (i : Z.I) (Y : C) (n : Y ⟶ Z.cod i) (hn : Z.N i n) :
    uniqueFactor_D Z F hfaith hsieve i Y n hn ≫ F.map (Z.mor i) = F.map n := by
  unfold uniqueFactor_D
  exact (Classical.choose_spec
    (exists_unique_factor_D Z F hfaith hsieve i (F.obj Y) (F.map n) ⟨Y, n, 𝟙 _, hn, by simp⟩)).1

lemma generatedLocalization_commutes_obj
    (hfaith : (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve : ∀ (i : Z.I),
      Sieve.functorPushforward F (Z.N i) ≤
        Sieve.generate (Presieve.singleton (F.map (Z.mor i)))) :
    ∀ A : GeneratedCategory Z,
      (H Z F hfaith hsieve ⋙ ImageCenterLocalizationFunctor Z F).obj A =
        (GeneratedToLocalization Z ⋙ localizationMap Z F).obj A := by
  intro A
  change
    (ImageCenterLocalizationFunctor Z F).obj
        (F.obj ((objEquiv (CenterMorphismProperty Z)).symm A)) =
      (localizationMap Z F).obj A
  have hA :
      (CenterMorphismProperty Z).Q.obj
          ((objEquiv (CenterMorphismProperty Z)).symm A) = A :=
    Equiv.apply_symm_apply (objEquiv (CenterMorphismProperty Z)) A
  rw [← hA]
  exact (congrArg (fun G => G.obj ((objEquiv (CenterMorphismProperty Z)).symm A))
    (localizationMap_comp_Q Z F)).symm

lemma H_map_fraction
    (hfaith : (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve : ∀ (i : Z.I),
      Sieve.functorPushforward F (Z.N i) ≤
        Sieve.generate (Presieve.singleton (F.map (Z.mor i))))
    (p : CenterSievePair Z)
    {gf :
      objEquiv (CenterMorphismProperty Z) p.2.1 ⟶
        objEquiv (CenterMorphismProperty Z) (Z.dom p.1)}
    (heq :
      (⟨objEquiv (CenterMorphismProperty Z) p.2.1,
        objEquiv (CenterMorphismProperty Z) (Z.dom p.1), gf⟩ :
          Σ A B : (CenterMorphismProperty Z).Localization, A ⟶ B) =
      ⟨objEquiv (CenterMorphismProperty Z) p.2.1,
        objEquiv (CenterMorphismProperty Z) (Z.dom p.1),
        (Quotient.functor (relations (CenterMorphismProperty Z))).map
          (fraction_in_path_single Z p)⟩)
    (hgf : gf = fraction_in_loc_single Z p) :
    (H Z F hfaith hsieve).map
        (Quiver.Hom.toPath
          (⟨gf, GeneratorMorphismData.fraction ⟨p, heq⟩⟩ :
            (GeneratorQuiver Z).Hom _ _)) =
      eqToHom (congrArg F.obj (Equiv.symm_apply_apply (objEquiv (CenterMorphismProperty Z)) p.2.1)) ≫
        uniqueFactor_D Z F hfaith hsieve p.1 p.2.1 p.2.2.1 p.2.2.2 ≫
        eqToHom (congrArg F.obj
          (Equiv.symm_apply_apply (objEquiv (CenterMorphismProperty Z)) (Z.dom p.1))).symm := by
  subst hgf
  apply (conj_eqToHom_iff_heq _ _ _ _).2
  · show HEq ((Paths.lift (Gq Z F hfaith hsieve)).map
        (Quiver.Hom.toPath
          (⟨fraction_in_loc_single Z p, GeneratorMorphismData.fraction ⟨p, heq⟩⟩ :
            (GeneratorQuiver Z).Hom _ _)))
      (uniqueFactor_D Z F hfaith hsieve p.1 p.2.1 p.2.2.1 p.2.2.2)
    rw [Paths.lift_toPath (Gq Z F hfaith hsieve)
      (⟨fraction_in_loc_single Z p, GeneratorMorphismData.fraction ⟨p, heq⟩⟩ :
        (GeneratorQuiver Z).Hom _ _)]
    show HEq (mapGenerator Z F hfaith hsieve
        (⟨fraction_in_loc_single Z p, GeneratorMorphismData.fraction ⟨p, heq⟩⟩ :
          (GeneratorQuiver Z).Hom _ _))
      (uniqueFactor_D Z F hfaith hsieve p.1 p.2.1 p.2.2.1 p.2.2.2)
    unfold mapGenerator
    simp
  all_goals
    dsimp only [H, Gq, Paths.lift]
    rw [Equiv.symm_apply_apply]


/-- `GeneratedToLocalization` sends a `fraction` generator to `fraction_in_loc_single`. -/
lemma GeneratedToLocalization_map_fraction
    (p : CenterSievePair Z)
    {gf :
      objEquiv (CenterMorphismProperty Z) p.2.1 ⟶
        objEquiv (CenterMorphismProperty Z) (Z.dom p.1)}
    (heq :
      (⟨objEquiv (CenterMorphismProperty Z) p.2.1,
        objEquiv (CenterMorphismProperty Z) (Z.dom p.1), gf⟩ :
          Σ A B : (CenterMorphismProperty Z).Localization, A ⟶ B) =
      ⟨objEquiv (CenterMorphismProperty Z) p.2.1,
        objEquiv (CenterMorphismProperty Z) (Z.dom p.1),
        (Quotient.functor (relations (CenterMorphismProperty Z))).map
          (fraction_in_path_single Z p)⟩)
    (hgf : gf = fraction_in_loc_single Z p) :
    (GeneratedToLocalization Z).map
        (Quiver.Hom.toPath
          (⟨gf, GeneratorMorphismData.fraction ⟨p, heq⟩⟩ :
            (GeneratorQuiver Z).Hom _ _)) =
      fraction_in_loc_single Z p := by
  simp [GeneratedToLocalization, forgetGenerator, Paths.lift]
  subst hgf
  rfl




lemma mapGenerator_original'
    (hfaith : (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve : ∀ (i : Z.I),
      Sieve.functorPushforward F (Z.N i) ≤
        Sieve.generate (Presieve.singleton (F.map (Z.mor i))))
    {A B : (CenterMorphismProperty Z).Localization} {gf : A ⟶ B}
    (h : OriginalWitness Z gf) :
    mapGenerator Z F hfaith hsieve
      (⟨gf, GeneratorMorphismData.original h⟩ : (GeneratorQuiver Z).Hom A B) =
      F.map h.g := by
  classical
  unfold mapGenerator
  rfl

lemma H_map_original_generator
    (hfaith : (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve : ∀ (i : Z.I),
      Sieve.functorPushforward F (Z.N i) ≤
        Sieve.generate (Presieve.singleton (F.map (Z.mor i))))
    {A B : (CenterMorphismProperty Z).Localization} {gf : A ⟶ B}
    (h : OriginalWitness Z gf) :
    (H Z F hfaith hsieve).map
        (Quiver.Hom.toPath
          (⟨gf, GeneratorMorphismData.original h⟩ :
            (GeneratorQuiver Z).Hom A B)) =
      F.map h.g := by
  exact (Paths.lift_toPath (Gq Z F hfaith hsieve)
    (⟨gf, GeneratorMorphismData.original h⟩ : (GeneratorQuiver Z).Hom A B)).trans
    (mapGenerator_original' Z F hfaith hsieve h)


/-- `GeneratedToLocalization` sends an `original` generator to itself. -/
lemma GeneratedToLocalization_map_original
    {A B : (CenterMorphismProperty Z).Localization} {gf : A ⟶ B}
    (h : OriginalWitness Z gf) :
    (GeneratedToLocalization Z).map
        (Quiver.Hom.toPath
          (⟨gf, GeneratorMorphismData.original h⟩ :
            (GeneratorQuiver Z).Hom A B)) =
      gf := by
  exact Paths.lift_toPath (forgetGenerator Z)
    (⟨gf, GeneratorMorphismData.original h⟩ : (GeneratorQuiver Z).Hom A B)



/-- Core cancellation step for the `fraction` case: matching the two sides of
`generatedLocalization_commutes` after both have been rewritten via `H_map_fraction` /
`GeneratedToLocalization_map_fraction`, using that `L(F(d_i))` is (tautologically)
invertible in the image-center localization. -/
lemma generatedLocalization_commutes_fraction_core
    (hfaith : (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve : ∀ (i : Z.I),
      Sieve.functorPushforward F (Z.N i) ≤
        Sieve.generate (Presieve.singleton (F.map (Z.mor i))))
    (hobj : ∀ A : GeneratedCategory Z,
      (H Z F hfaith hsieve ⋙ ImageCenterLocalizationFunctor Z F).obj A =
        (GeneratedToLocalization Z ⋙ localizationMap Z F).obj A)
    (i : Z.I) (X : C) (n : X ⟶ Z.cod i) (hn : Z.N i n) :
    (ImageCenterLocalizationFunctor Z F).map
        (uniqueFactor_D Z F hfaith hsieve i X n hn) =
      eqToHom (hobj (objEquiv (CenterMorphismProperty Z) X)) ≫
        (localizationMap Z F).map (fraction_in_loc_single Z ⟨i, ⟨X, ⟨n, hn⟩⟩⟩) ≫
        eqToHom (hobj (objEquiv (CenterMorphismProperty Z) (Z.dom i))).symm := by
  have : IsIso ((ImageCenterLocalizationFunctor Z F).map (F.map (Z.mor i))) :=
    MorphismProperty.Q_inverts _ _ ⟨i, rfl⟩
  change (ImageCenterLocalizationFunctor Z F).map
      (uniqueFactor_D Z F hfaith hsieve i X n hn) =
    𝟙 _ ≫ (localizationMap Z F).map (fraction_in_loc_single Z ⟨i, X, n, hn⟩) ≫ 𝟙 _
  erw [Category.id_comp, Category.comp_id]
  have hmap {A B : C} (g : A ⟶ B) :
      (localizationMap Z F).map ((CenterMorphismProperty Z).Q.map g) =
        (ImageCenterLocalizationFunctor Z F).map (F.map g) := by
    have h := Functor.congr_hom (localizationMap_comp_Q Z F) g
    simpa only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] using! h
  apply (cancel_mono ((ImageCenterLocalizationFunctor Z F).map (F.map (Z.mor i)))).mp
  rw [← Functor.map_comp, uniqueFactor_D_spec]
  erw [← hmap (Z.mor i), ← Functor.map_comp, fraction_comp_mor, hmap]

lemma generatedLocalization_commutes
    (hfaith : (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve : ∀ (i : Z.I),
      Sieve.functorPushforward F (Z.N i) ≤
        Sieve.generate (Presieve.singleton (F.map (Z.mor i)))) :
    H Z F hfaith hsieve ⋙ ImageCenterLocalizationFunctor Z F =
      GeneratedToLocalization Z ⋙ localizationMap Z F := by
  have hobj := generatedLocalization_commutes_obj Z F hfaith hsieve
  apply Functor.ext
  · intro A B f
    apply GeneratedCategory_morphism_induction Z
      (fun {A B} (k : A ⟶ B) =>
        (H Z F hfaith hsieve ⋙ ImageCenterLocalizationFunctor Z F).map k =
          eqToHom (hobj A) ≫
            (GeneratedToLocalization Z ⋙ localizationMap Z F).map k ≫
            eqToHom (hobj B).symm)
    · intro A
      change (H Z F hfaith hsieve ⋙ ImageCenterLocalizationFunctor Z F).map (𝟙 A) =
        𝟙 _ ≫ (GeneratedToLocalization Z ⋙ localizationMap Z F).map (𝟙 A) ≫ 𝟙 _
      simp
      rfl
    · intro X Y W f g hf hg
      rw [Functor.map_comp, hf, hg]
      simp
    · intro A B g
      erw [Functor.comp_map, Functor.comp_map]
      obtain ⟨gf, gdata⟩ := g
      cases gdata with
      | fraction h =>
        obtain ⟨p, heq⟩ := h
        obtain ⟨i, X, n, hn⟩ := p
        have hA' : A = objEquiv (CenterMorphismProperty Z) X :=
          congrArg Sigma.fst heq
        have hB' : B = objEquiv (CenterMorphismProperty Z) (Z.dom i) := by
          exact congrArg (fun s => s.2.1) heq
        subst hA'; subst hB'
        have hgf : gf = fraction_in_loc_single Z ⟨i, ⟨X, ⟨n, hn⟩⟩⟩ := by
          simp only [Sigma.mk.injEq, heq_eq_eq] at heq
          exact eq_of_heq (Sigma.mk.inj heq.2).2
        rw [H_map_fraction Z F hfaith hsieve ⟨i, ⟨X, ⟨n, hn⟩⟩⟩ heq hgf,
            GeneratedToLocalization_map_fraction Z ⟨i, ⟨X, ⟨n, hn⟩⟩⟩ heq hgf]
        erw [Category.id_comp, Category.comp_id]
        erw [generatedLocalization_commutes_fraction_core Z F hfaith hsieve hobj i X n hn]
        rfl
      | original h =>
        obtain ⟨g, heq⟩ := h
        rw [H_map_original_generator Z F hfaith hsieve ⟨g, heq⟩,
            GeneratedToLocalization_map_original Z ⟨g, heq⟩]
        dsimp only
        rw [heq]
        have hc := Functor.congr_hom (localizationMap_comp_Q Z F) g
        simp only [Functor.comp_map] at hc
        erw [hc]
        erw [Category.id_comp, Category.comp_id]

/-- `H` sends `DilaRel`-related paths to equal morphisms of `D`: the second, global use of
`Σ`-regularity, by injectivity after post-composing with `ImageCenterLocalizationFunctor Z F`. -/
lemma H_descends
    (hfaith :
      (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate
            (Presieve.singleton (F.map (Z.mor i)))) :
    ∀ {X Y : GeneratedCategory Z}
      (f g : X ⟶ Y),
      DilaRel Z f g →
      (H Z F hfaith hsieve).map f =
      (H Z F hfaith hsieve).map g := by
  intro X Y f g hfg

  apply (ImageCenterLocalizationFunctor Z F).map_injective

  have hcomm :=
    generatedLocalization_commutes Z F hfaith hsieve

  change
    (H Z F hfaith hsieve ⋙ ImageCenterLocalizationFunctor Z F).map f =
    (H Z F hfaith hsieve ⋙ ImageCenterLocalizationFunctor Z F).map g

  rw [hcomm]

  simpa only [Functor.comp_map] using
    congrArg
      (fun k => (localizationMap Z F).map k)
      hfg


/-- **Theorem 3.10, the functor `F'`.** The functor `Dila Z ⥤ D` factoring `F` through
`Θ = CatToDila Z`, built structurally: the generator-by-generator choice `Gq`, lifted to the
free category as `H`, descends along the quotient by `DilaRel` via `H_descends`. Its defining
equation `F' ∘ Θ = F` is `DilaLift_fac`; its uniqueness is `DilaLift_unique`. -/
def DilaLift
    (hfaith :
      (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate
            (Presieve.singleton (F.map (Z.mor i)))) :
    Dila Z ⥤ D :=
  CategoryTheory.Quotient.lift
    (DilaRel Z)
    (H Z F hfaith hsieve)
    (fun _ _ f g hfg => H_descends Z F hfaith hsieve f g hfg)


/-- **Theorem 3.10, existence half.** `F' ∘ Θ = F`. -/
theorem DilaLift_fac
    (hfaith :
      (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate
            (Presieve.singleton (F.map (Z.mor i)))) :
    CatToDila Z ⋙ DilaLift Z F hfaith hsieve = F := by
  refine Functor.ext (fun _ => rfl) ?_
  intro X Y f
  change (H Z F hfaith hsieve).map ((CToGeneratorQuiver Z).map f).toPath =
    𝟙 _ ≫ F.map f ≫ 𝟙 _
  simpa using H_map_original Z F hfaith hsieve f


theorem exists_Dila_factor
    (hfaith :
      (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate
            (Presieve.singleton (F.map (Z.mor i)))) :
    ∃ (G : Dila Z ⥤ D),
      CatToDila Z ⋙ G = F :=
  ⟨DilaLift Z F hfaith hsieve, DilaLift_fac Z F hfaith hsieve⟩




lemma Dila_factor_unique_on_C
    (G₁ G₂ : Dila Z ⥤ D)
    (h₁ : CatToDila Z ⋙ G₁ = F)
    (h₂ : CatToDila Z ⋙ G₂ = F) :
    CatToDila Z ⋙ G₁ = CatToDila Z ⋙ G₂ := by
  exact h₁.trans h₂.symm

lemma map_eq_of_agree_on_C
    {X Y : C}
    (G₁ G₂ : Dila Z ⥤ D)
    (h₁ : CatToDila Z ⋙ G₁ = F)
    (h₂ : CatToDila Z ⋙ G₂ = F)
    (f : X ⟶ Y) :
    G₁.map ((CatToDila Z).map f) =
      eqToHom
        (congrArg (fun H => H.obj X)
          (h₁.trans h₂.symm)) ≫
        G₂.map ((CatToDila Z).map f) ≫
      eqToHom
        (congrArg (fun H => H.obj Y)
          (h₁.trans h₂.symm)).symm := by

  apply Functor.congr_hom (h₁.trans h₂.symm)


lemma Dila_factor_unique_fraction
    (G₁ G₂ : Dila Z ⥤ D)
    (hfaith :
    (ImageCenterLocalizationFunctor Z F).Faithful)
    (h₁ : CatToDila Z ⋙ G₁ = F)
    (h₂ : CatToDila Z ⋙ G₂ = F) :
    ∀ (i : Z.I) (X : C)
      (n : X ⟶ Z.cod i)
      (hn : Z.N i n),
      G₁.map
        (fraction_in_dila_single Z
          ⟨i, ⟨X, ⟨n, hn⟩⟩⟩)
      =
      eqToHom (by
        have := congrArg (fun H => H.obj X)
          (Dila_factor_unique_on_C Z F G₁ G₂ h₁ h₂)
        exact this)
      ≫
      G₂.map
        (fraction_in_dila_single Z ⟨i, ⟨X, ⟨n, hn⟩⟩⟩)
      ≫
      eqToHom (by
        have := congrArg (fun H => H.obj (Z.dom i))
          (Dila_factor_unique_on_C Z F G₁ G₂ h₁ h₂)
        exact this.symm) :=  by
  intro i X n hn

  let b :=
    fraction_in_dila_single Z ⟨i, ⟨X, ⟨n, hn⟩⟩⟩

  have hb :
      b ≫ (CatToDila Z).map (Z.mor i) =
        (CatToDila Z).map n := by
    apply Quotient.sound
    change
      (GeneratedToLocalization Z).map
          (Quiver.Hom.toPath
            (fraction_in_generated Z
              ⟨i, ⟨X, ⟨n, hn⟩⟩⟩)) ≫
        (GeneratedToLocalization Z).map
          (Quiver.Hom.toPath
            ((CToGeneratorQuiver Z).map (Z.mor i)))
      =
      (GeneratedToLocalization Z).map
          (Quiver.Hom.toPath
            ((CToGeneratorQuiver Z).map n))

    change
      fraction_in_loc_single Z ⟨i, ⟨X, ⟨n, hn⟩⟩⟩ ≫
          (CenterMorphismProperty Z).Q.map (Z.mor i)
        =
      (CenterMorphismProperty Z).Q.map n

    exact fraction_comp_mor Z i X n hn

  have h₁b :
      G₁.map b ≫
          G₁.map ((CatToDila Z).map (Z.mor i))
        =
      G₁.map ((CatToDila Z).map n) := by
    rw [← Functor.map_comp]
    rw [hb]

  have h₂b :
      G₂.map b ≫
          G₂.map ((CatToDila Z).map (Z.mor i))
        =
      G₂.map ((CatToDila Z).map n) := by
    rw [← Functor.map_comp]
    rw [hb]

  have hmono :
      Mono (F.map (Z.mor i)) := by
    constructor
    intro W u v huv

    apply hfaith.map_injective

    haveI :
        IsIso ((ImageCenterLocalizationFunctor Z F).map
          (F.map (Z.mor i))) := by
      apply CategoryTheory.MorphismProperty.Q_inverts
        (ImageCenterMorphismProperty Z F)
      exact ⟨i, rfl⟩

    apply (cancel_mono
      ((ImageCenterLocalizationFunctor Z F).map
        (F.map (Z.mor i)))).1

    simpa only [Functor.map_comp] using
      congrArg
        (fun f =>
          (ImageCenterLocalizationFunctor Z F).map f)
        huv


  have hcancel :
      ∀ {u v :
        G₁.obj ((CatToDila Z).obj X) ⟶
          G₁.obj ((CatToDila Z).obj (Z.dom i))},
      u ≫ G₁.map ((CatToDila Z).map (Z.mor i)) =
        v ≫ G₁.map ((CatToDila Z).map (Z.mor i)) →
      u = v := by

    intro u v huv

    haveI :
        Mono ((CatToDila Z ⋙ G₁).map (Z.mor i)) := by
      rw [h₁]
      exact hmono

    haveI :
        Mono (G₁.map ((CatToDila Z).map (Z.mor i))) := by
      change Mono ((CatToDila Z ⋙ G₁).map (Z.mor i))
      infer_instance

    exact
      (cancel_mono
        (G₁.map ((CatToDila Z).map (Z.mor i)))).1 huv

  apply hcancel


  rw [h₁b]

  have hn_map :
      G₁.map ((CatToDila Z).map n) =
        eqToHom
          (congrArg (fun H => H.obj X)
            (h₁.trans h₂.symm)) ≫
        G₂.map ((CatToDila Z).map n) ≫
        eqToHom
          (congrArg (fun H => H.obj (Z.cod i))
            (h₁.trans h₂.symm)).symm :=
    map_eq_of_agree_on_C (Z := Z) (F := F)
      G₁ G₂ h₁ h₂ n

  rw [hn_map]

  rw [← h₂b]

  have hdi :
    G₁.map ((CatToDila Z).map (Z.mor i)) =
      eqToHom
        (congrArg (fun H => H.obj (Z.dom i))
          (h₁.trans h₂.symm)) ≫
      G₂.map ((CatToDila Z).map (Z.mor i)) ≫
      eqToHom
        (congrArg (fun H => H.obj (Z.cod i))
          (h₁.trans h₂.symm)).symm :=
  map_eq_of_agree_on_C (Z := Z) (F := F)
    G₁ G₂ h₁ h₂ (Z.mor i)

  rw [hdi]
  simp only [Category.assoc]
  subst b
  simp


lemma Subtype.ext_val
    {α : Type*} {p : α → Prop} {a b : Subtype p}
    (h : a.val = b.val) : a = b :=
by
  exact Subtype.ext h

lemma Subtype.val_eq_of_eq
    {α : Type*} {p : α → Prop} {a b : Subtype p}
    (h : a = b) : a.val = b.val :=
by
  simpa using congrArg Subtype.val h


lemma GeneratorQuiver_Hom_ext
    {X Y : GeneratorObjects Z}
    (g₁ g₂ : (GeneratorQuiver Z).Hom X Y)
    (h : g₁.1 = g₂.1) :
    (GeneratedToDila Z).map
        (Quiver.Hom.toPath g₁)
      =
    (GeneratedToDila Z).map
        (Quiver.Hom.toPath g₂) := by
  apply Quotient.sound
  dsimp [DilaRel]
  cases g₁ with
  | mk f₁ d₁ =>
    cases g₂ with
    | mk f₂ d₂ =>
      dsimp at h
      subst h
      rfl



lemma Generated_factor_unique_map
    (G₁ G₂ :
      Dila Z ⥤ D)
    (h_obj :
      ∀ X : Dila Z, G₁.obj X = G₂.obj X)
    (h_mor :
      ∀ {X Y : C} (f : X ⟶ Y),
        G₁.map ((CatToDila Z).map f) =
          eqToHom (h_obj ((CatToDila Z).obj X)) ≫
          G₂.map ((CatToDila Z).map f) ≫
          eqToHom (h_obj ((CatToDila Z).obj Y)).symm)
    (h_fraction :
      ∀ (i : Z.I) (X : C)
        (n : X ⟶ Z.cod i)
        (hn : Z.N i n),
        G₁.map
          (fraction_in_dila_single Z ⟨i, ⟨X, ⟨n, hn⟩⟩⟩)
        =
        eqToHom (h_obj ((CatToDila Z).obj X)) ≫
          G₂.map
            (fraction_in_dila_single Z ⟨i, ⟨X, ⟨n, hn⟩⟩⟩) ≫
          eqToHom (h_obj ((CatToDila Z).obj (Z.dom i))).symm)
    {X Y : Dila Z}
    (f : X ⟶ Y) :
    G₁.map f =
      eqToHom (h_obj X) ≫
        G₂.map f ≫
        eqToHom (h_obj Y).symm := by

  letI : (GeneratedToDila Z).Full := GeneratedToDila_full Z

  obtain ⟨g, rfl⟩ := (GeneratedToDila Z).map_surjective f

  let P :=
    fun {A B : GeneratedCategory Z} (k : A ⟶ B) =>
      G₁.map ((GeneratedToDila Z).map k) =
        eqToHom (h_obj ((GeneratedToDila Z).obj A)) ≫
          G₂.map ((GeneratedToDila Z).map k) ≫
          eqToHom (h_obj ((GeneratedToDila Z).obj B)).symm

  show P g

  apply GeneratedCategory_morphism_induction Z P

  · intro A
    simp [P]

  · intro A B C f g hf hg
    dsimp [P] at *
    simp [Functor.map_comp, hf, hg, Category.assoc]

  · intro A B g
    dsimp [P]
    rcases g.2 with h | h
    · -- fraction case: h : PairMorWitness Z g.fst
      obtain ⟨p, heq⟩ := h
      have hA : A = objEquiv (CenterMorphismProperty Z) p.2.1 :=
        congrArg Sigma.fst heq
      have hB : B = objEquiv (CenterMorphismProperty Z) (Z.dom p.1) := by
        exact congrArg (fun s => s.2.1) heq
      subst hA
      subst hB
      have hg1 : g.1 = fraction_in_loc_single Z p := by
        simp only [Sigma.mk.injEq, heq_eq_eq] at heq
        exact eq_of_heq (Sigma.mk.inj heq.2).2
      have hgg :
          (GeneratedToDila Z).map (Quiver.Hom.toPath g) =
            fraction_in_dila_single Z p :=
        GeneratorQuiver_Hom_ext Z g (fraction_in_generated Z p) hg1
      rw [hgg]
      obtain ⟨i, X, n, hn⟩ := p
      exact h_fraction i X n hn
    · -- original case: h : OriginalWitness Z g.fst
      have hgg :
          (GeneratedToDila Z).map (Quiver.Hom.toPath g) =
            (CatToDila Z).map h.g :=
        GeneratorQuiver_Hom_ext Z g ((CToGeneratorQuiver Z).map h.g) h.eq
      rw [hgg]
      exact h_mor h.g






lemma localization_obj_eq_Q_obj
    (X : (CenterMorphismProperty Z).Localization) :
    ∃ Y : C, (CenterMorphismProperty Z).Q.obj Y = X := by
  let e := (CategoryTheory.Localization.Construction.objEquiv
      (CenterMorphismProperty Z))
  refine ⟨e.invFun X, ?_⟩
  exact e.apply_symm_apply X

lemma Dila_obj_eq_C_obj :
    ∀ (X : Dila Z), ∃ Y : C, (CatToDila Z).obj Y = X := by
  intro X
  obtain ⟨Y, hY⟩ :=
    localization_obj_eq_Q_obj Z X.1
  refine ⟨Y, ?_⟩
  cases X
  dsimp [CatToDila]
  cases hY
  rfl

theorem Dila_factor_unique
    (G₁ G₂ :
        Dila Z ⥤ D)
    (h₁ :
      CatToDila Z ⋙ G₁ =
        F)
    (h₂ :
      CatToDila Z ⋙ G₂ =
        F)
    (hfaith :
       (ImageCenterLocalizationFunctor Z F).Faithful)
     :
    G₁ = G₂ := by
  have h_obj :
      ∀ X : Dila Z, G₁.obj X = G₂.obj X := by
      intro X
      obtain ⟨Y, hY⟩ := Dila_obj_eq_C_obj Z X
      rw [← hY]
      have h1Y := congrArg (fun H : C ⥤ D => H.obj Y) h₁
      have h2Y := congrArg (fun H : C ⥤ D => H.obj Y) h₂
      exact h1Y.trans h2Y.symm

  apply CategoryTheory.Functor.ext
  · intro X Y f
    exact Generated_factor_unique_map
      Z G₁ G₂
     (by

        assumption)
     (   by
                intro X Y f

                have H :
                    CatToDila Z ⋙ G₁ = CatToDila Z ⋙ G₂ :=
                  Dila_factor_unique_on_C Z F G₁ G₂ h₁ h₂

                have hm :
                    G₁.map ((CatToDila Z).map f) ≍
                    G₂.map ((CatToDila Z).map f) := by
                  have hm' :
                      (CatToDila Z ⋙ G₁).map f ≍
                      (CatToDila Z ⋙ G₂).map f := by
                    rw [H]
                  exact hm'

                exact (conj_eqToHom_iff_heq
                          (G₁.map ((CatToDila Z).map f))
                          (G₂.map ((CatToDila Z).map f))
                          (h_obj ((CatToDila Z).obj X))
                          (h_obj ((CatToDila Z).obj Y))).2 hm )
       (by
        intro i X n hn
        exact Dila_factor_unique_fraction
          Z F G₁ G₂ (by assumption) h₁ h₂ i X n hn)
        f




/-- **Theorem 3.10, uniqueness half.** Any `G` with `G ∘ Θ = F` equals `DilaLift`. -/
theorem DilaLift_unique
    (hfaith :
      (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate
            (Presieve.singleton (F.map (Z.mor i))))
    (G : Dila Z ⥤ D)
    (hG : CatToDila Z ⋙ G = F) :
    G = DilaLift Z F hfaith hsieve :=
  Dila_factor_unique
    Z
    F
    G
    (DilaLift Z F hfaith hsieve)
    hG
    (DilaLift_fac Z F hfaith hsieve)
    hfaith


theorem Dila_universal_property
    (F : C ⥤ D)
    (hfaith :
       (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate
            (Presieve.singleton (F.map (Z.mor i)))) :
    ∃! (G : Dila Z ⥤ D),
      CatToDila Z ⋙ G =
        F :=
  ⟨DilaLift Z F hfaith hsieve,
    DilaLift_fac Z F hfaith hsieve,
    fun G' hG' => DilaLift_unique Z F hfaith hsieve G' hG'⟩



/-- **Definition 3.6.** `F : C ⥤ D` is `Σ`-regular (`F ∈ Cat^Σ-reg_C`) if `D → D[F(Σ)⁻¹]` is
faithful. -/
def IsSigmaRegular : Prop :=
  Functor.Faithful (ImageCenterMorphismProperty Z F).Q


/-- If `p ⋙ e` is faithful, then `p` is faithful. This is the elementary categorical fact behind
both Fact 3.7 and Fact 3.8: a functor that factors (on the target side) through a faithful
functor is itself faithful. -/
theorem faithful_of_comp_faithful
    {C₁ : Type u} [Category.{v} C₁] {C₂ : Type u} [Category.{v} C₂] {C₃ : Type u} [Category.{v} C₃]
    (p : C₁ ⥤ C₂) (e : C₂ ⥤ C₃) (hfaith : (p ⋙ e).Faithful) :
    p.Faithful := by
  constructor
  intro X Y f g h
  apply hfaith.map_injective
  simp only [Functor.comp_map, h]




/-- **Fact 3.7.** `Θ : C ⥤ C'` is `Σ`-regular. -/
theorem CatToDila_isSigmaRegular : IsSigmaRegular Z (CatToDila Z) := by
  show (ImageCenterLocalizationFunctor Z (CatToDila Z)).Faithful
  have hex :
    ∃ l : ImageCenterLocalization Z (CatToDila Z) ⥤ (CenterMorphismProperty Z).Localization,
      ImageCenterLocalizationFunctor Z (CatToDila Z) ⋙ l = DilaToLoc Z :=
  ⟨Localization.Construction.lift
      (W := ImageCenterMorphismProperty Z (CatToDila Z))
      (DilaToLoc Z)
      (by
        intro X Y f hf
        rcases hf with ⟨i, hi⟩
        have hX : X = (CatToDila Z).obj (Z.dom i) := congrArg Sigma.fst hi
        have hY : Y = (CatToDila Z).obj (Z.cod i) := congrArg (fun s => s.2.1) hi
        subst X
        subst Y
        have hf' : f = (CatToDila Z).map (Z.mor i) := by cases hi; rfl
        rw [hf']
        have hkey := Functor.congr_hom (CatToDila_comp_DilaToLoc Z) (Z.mor i)
        simp only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] at hkey
        rw [hkey]
        apply CategoryTheory.MorphismProperty.Q_inverts
        exact ⟨i, rfl⟩),
  Localization.Construction.fac _ _⟩
  obtain ⟨l, hl⟩ := hex
  apply faithful_of_comp_faithful (ImageCenterLocalizationFunctor Z (CatToDila Z)) l
  rw [hl]
  exact DilaToLoc_faithful Z

/-- **Fact 3.11.** If `G : Dila Z ⥤ D` and `i : Z.I`, then the pushforward of `Z.N i` along
`CatToDila Z ⋙ G` is contained in the singleton sieve generated by
`(CatToDila Z ⋙ G).map (Z.mor i)`. This is `CatToDila_image_sieve_le_singleton` pushed forward
one further step through `G`. -/
lemma CatToDila_comp_image_sieve_le_singleton
    (G : Dila Z ⥤ D) (i : Z.I) :
    Sieve.functorPushforward (CatToDila Z ⋙ G) (Z.N i) ≤
      Sieve.generate (Presieve.singleton ((CatToDila Z ⋙ G).map (Z.mor i))) := by
  intro X f hf
  dsimp [Sieve.functorPushforward] at hf
  rcases hf with ⟨Y₀, h, g, hg, rfl⟩
  have hmem : (CatToDilaSieve Z (Z.N i)).arrows ((CatToDila Z).map h) :=
    ⟨Y₀, h, 𝟙 _, hg, by simp⟩
  obtain ⟨Y, q, g₀, hg₀, hq⟩ :=
    CatToDila_image_sieve_le_singleton Z i ((CatToDila Z).map h) hmem
  obtain ⟨rfl, rfl⟩ := hg₀
  refine ⟨G.obj ((CatToDila Z).obj (Z.dom i)), g ≫ G.map q,
    (CatToDila Z ⋙ G).map (Z.mor i), Presieve.singleton_self _, ?_⟩
  show (g ≫ G.map q) ≫ (CatToDila Z ⋙ G).map (Z.mor i) = g ≫ (CatToDila Z ⋙ G).map h
  simp only [Functor.comp_map]
  rw [Category.assoc, ← Functor.map_comp, hq]



theorem CatToDila_represents
    (F : C ⥤ D) (hfaith : IsSigmaRegular Z F) :
    (∃! G : Dila Z ⥤ D, CatToDila Z ⋙ G = F) ↔
      ∀ i : Z.I,
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate (Presieve.singleton (F.map (Z.mor i))) := by
  constructor
  · -- if a (necessarily unique) factorization exists, the sieve condition holds for every i
    rintro ⟨G, hG, -⟩
    intro i
    have h := CatToDila_comp_image_sieve_le_singleton Z G i
    rw [hG] at h
    exact h
  · -- conversely, the sieve condition for every i gives existence and uniqueness
    intro hsieve
    exact Dila_universal_property Z F
      (by
        show (ImageCenterLocalizationFunctor Z F).Faithful
        exact hfaith)
      hsieve



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

lemma CatToDila_isSigmaRegular_restrict
    (Z : Center C) (K : Set Z.I) (hK : K.Nonempty) :
    IsSigmaRegular (Z.restrict K hK) (CatToDila Z) := by
  show (ImageCenterMorphismProperty (Z.restrict K hK) (CatToDila Z)).Q.Faithful
  apply faithful_of_comp_faithful
    (ImageCenterMorphismProperty (Z.restrict K hK) (CatToDila Z)).Q
    (Localization.Construction.lift
      (W := ImageCenterMorphismProperty (Z.restrict K hK) (CatToDila Z))
      (ImageCenterMorphismProperty Z (CatToDila Z)).Q
      (fun X Y f hf => by
        show IsIso ((ImageCenterMorphismProperty Z (CatToDila Z)).Q.map f)
        apply CategoryTheory.MorphismProperty.Q_inverts
        exact ImageCenterMorphismProperty_restrict_le Z K hK f hf))
  erw [Localization.Construction.fac]
  exact CatToDila_isSigmaRegular Z


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


universe u₁ v₁ u₂ v₂ u₃ v₃

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
  show (ImageCenterMorphismProperty Z (LocalizationFunctor Z)).Q.Faithful
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
  show (ImageCenterMorphismProperty (Z.restrict K hK) (LocalizationFunctor Z)).Q.Faithful
  apply isoMorphismProperty_Q_faithful
  rintro X Y f ⟨k, hk⟩
  have hX : X = (LocalizationFunctor Z).obj ((Z.restrict K hK).dom k) := congrArg Sigma.fst hk
  have hY : Y = (LocalizationFunctor Z).obj ((Z.restrict K hK).cod k) :=
    congrArg (fun s => s.2.1) hk
  subst X
  subst Y
  have hf : f = (LocalizationFunctor Z).map ((Z.restrict K hK).mor k) := by cases hk; rfl
  rw [hf]
  show IsIso ((CenterMorphismProperty Z).Q.map (Z.mor k.1))
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
      show CatToDila (Z.restrict K hK) ⋙ restrictPhi Z K hK ⋙ DilaToLoc Z = LocalizationFunctor Z
      rw [show CatToDila (Z.restrict K hK) ⋙ restrictPhi Z K hK ⋙ DilaToLoc Z =
            (CatToDila (Z.restrict K hK) ⋙ restrictPhi Z K hK) ⋙ DilaToLoc Z from rfl,
          restrictPhi_spec, CatToDila_comp_DilaToLoc])
    (by
      show CatToDila (Z.restrict K hK) ⋙
          (DilaToLoc (Z.restrict K hK) ⋙ baseRestrictFunctor Z K hK) = LocalizationFunctor Z
      rw [show CatToDila (Z.restrict K hK) ⋙
              (DilaToLoc (Z.restrict K hK) ⋙ baseRestrictFunctor Z K hK) =
            (CatToDila (Z.restrict K hK) ⋙ DilaToLoc (Z.restrict K hK)) ⋙
              baseRestrictFunctor Z K hK from rfl,
          CatToDila_comp_DilaToLoc]
      show (CenterMorphismProperty (Z.restrict K hK)).Q ⋙ baseRestrictFunctor Z K hK =
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
  haveI := DilaToLoc_faithful (Z.restrict K hK)
  haveI := hbase
  apply faithful_of_comp_faithful (restrictPhi Z K hK) (DilaToLoc Z)
  rw [restrictPhi_comp_DilaToLoc]
  infer_instance


/-- **Proposition 3.1 (2), defining property.** `b ≫ Θ(dᵢ) = Θ(n)`, i.e. the triangle
`[n] = Θ(dᵢ) ∘ b` commutes. -/
lemma fraction_in_dila_comp_mor (Z : Center C) (i : Z.I) (X : C) (m : X ⟶ Z.cod i) (hm : Z.N i m) :
    fraction_in_dila_single Z ⟨i, ⟨X, ⟨m, hm⟩⟩⟩ ≫ (CatToDila Z).map (Z.mor i) =
      (CatToDila Z).map m := by
  apply Quotient.sound
  simp [DilaRel, CatToDila, GeneratedToLocalization, forgetGenerator]
  change
    fraction_in_loc_single Z ⟨i, ⟨X, ⟨m, hm⟩⟩⟩ ≫ (CenterMorphismProperty Z).Q.map (Z.mor i) =
      (CenterMorphismProperty Z).Q.map m
  exact fraction_comp_mor Z i X m hm

lemma fraction_in_dila_single_eq_of_factors
    (i : Z.I) (X : C) (q : X ⟶ Z.dom i) (m : X ⟶ Z.cod i) (hm : Z.N i m)
    (hfactor : m = q ≫ Z.mor i) :
    fraction_in_dila_single Z ⟨i, ⟨X, ⟨m, hm⟩⟩⟩ = (CatToDila Z).map q := by
      apply unique_factor_D Z (CatToDila Z)
        (by show (ImageCenterLocalizationFunctor Z (CatToDila Z)).Faithful
            exact CatToDila_isSigmaRegular Z)
        i ((CatToDila Z).obj X)
      rw [fraction_in_dila_comp_mor Z i X m hm, ← Functor.map_comp, ← hfactor]

/-- The basic object-identification: `Φ` sends the `Z.restrict K hK`-image of `Y` to the
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

/-- The `Φ`-preimage predicate used in the induction: `p : A' ⟶ B'` (in `GeneratedCategory Z`)
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

/-- Base case: the identity generator has a `Φ`-preimage (namely the identity). -/
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



/-- Inductive step: `Φ`-preimages compose. -/
lemma PhiPreimage_comp (Z : Center C) (K : Set Z.I) (hK : K.Nonempty)
    {X' Y' W' : GeneratedCategory Z} (p : X' ⟶ Y') (q : Y' ⟶ W')
    (hp : PhiPreimage Z K hK p) (hq : PhiPreimage Z K hK q) :
    PhiPreimage Z K hK (p ≫ q) := by
  obtain ⟨f, hf⟩ := hp
  obtain ⟨f', hf'⟩ := hq
  refine ⟨f ≫ f', ?_⟩
  show (restrictPhi Z K hK).map (f ≫ f') =
      eqToHom (restrictPhi_full_hobj Z K hK X') ≫ (GeneratedToDila Z).map (p ≫ q) ≫
        eqToHom (restrictPhi_full_hobj Z K hK W').symm
  rw [Functor.map_comp, hf, hf']
  erw [Functor.map_comp, Category.assoc, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp, Category.assoc]
  erw [Category.id_comp, Category.id_comp]
  rfl

/-- `DilaToLoc` sends a fraction generator back down to the corresponding fraction morphism
of the localization. -/
lemma DilaToLoc_map_fraction (Z : Center C) (p : CenterSievePair Z) :
    (DilaToLoc Z).map (fraction_in_dila_single Z p) = fraction_in_loc_single Z p := by
  rfl

lemma fraction_in_loc_single_eq (Z : Center C) (p : CenterSievePair Z) :
    fraction_in_loc_single Z p =
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
  haveI := MorphismProperty.Q_inverts (CenterMorphismProperty (Z.restrict K hK)) w hw
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
        (fraction_in_loc_single (Z.restrict K hK) ⟨⟨i, hiK⟩, ⟨X0, ⟨n, hn⟩⟩⟩) =
      fraction_in_loc_single Z ⟨i, ⟨X0, ⟨n, hn⟩⟩⟩ := by
  erw [fraction_in_loc_single_eq, Functor.map_comp,
    baseRestrictFunctor_map_Q, baseRestrictFunctor_map_wInv, fraction_in_loc_single_eq]
  rfl

/-- `restrictPhi` sends the fraction generator of `Z.restrict K hK` at an index `i ∈ K` to the
corresponding fraction generator of `Z` at `i`, up to the object-identification
`restrictPhi_obj_eq`. -/
lemma restrictPhi_map_fraction (Z : Center C) (K : Set Z.I) (hK : K.Nonempty)
    (i : Z.I) (hiK : i ∈ K) (X0 : C) (n : X0 ⟶ Z.cod i) (hn : Z.N i n) :
    (restrictPhi Z K hK).map
        (fraction_in_dila_single (Z.restrict K hK) ⟨⟨i, hiK⟩, ⟨X0, ⟨n, hn⟩⟩⟩) =
      eqToHom (restrictPhi_obj_eq Z K hK X0) ≫ fraction_in_dila_single Z ⟨i, ⟨X0, ⟨n, hn⟩⟩⟩ ≫
        eqToHom (restrictPhi_obj_eq Z K hK (Z.dom i)).symm := by
  haveI := DilaToLoc_faithful Z
  apply (DilaToLoc Z).map_injective
  have hcomp := Functor.congr_hom (restrictPhi_comp_DilaToLoc Z K hK)
      (fraction_in_dila_single (Z.restrict K hK) ⟨⟨i, hiK⟩, ⟨X0, ⟨n, hn⟩⟩⟩)
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
        (⟨fraction_in_loc_single Z ⟨i, ⟨X0, ⟨n, hn⟩⟩⟩,
          GeneratorMorphismData.fraction ⟨⟨i, ⟨X0, ⟨n, hn⟩⟩⟩, rfl⟩⟩ :
          (GeneratorQuiver Z).Hom
            (objEquiv (CenterMorphismProperty Z) X0)
            (objEquiv (CenterMorphismProperty Z) (Z.dom i)))) := by
  refine ⟨eqToHom (by rw [Equiv.symm_apply_apply]) ≫
      fraction_in_dila_single (Z.restrict K hK) ⟨⟨i, hiK⟩, ⟨X0, ⟨n, hn⟩⟩⟩ ≫
      eqToHom rfl, ?_⟩
  show (restrictPhi Z K hK).map
      (eqToHom (by rw [Equiv.symm_apply_apply]) ≫
        fraction_in_dila_single (Z.restrict K hK) ⟨⟨i, hiK⟩, ⟨X0, ⟨n, hn⟩⟩⟩ ≫
        eqToHom rfl) =
      eqToHom (restrictPhi_full_hobj Z K hK (objEquiv (CenterMorphismProperty Z) X0)) ≫
        (GeneratedToDila Z).map
          (Quiver.Hom.toPath
            (⟨fraction_in_loc_single Z ⟨i, ⟨X0, ⟨n, hn⟩⟩⟩,
              GeneratorMorphismData.fraction ⟨⟨i, ⟨X0, ⟨n, hn⟩⟩⟩, rfl⟩⟩ :
              (GeneratorQuiver Z).Hom _ _)) ≫
        eqToHom
          (restrictPhi_full_hobj Z K hK
            (objEquiv (CenterMorphismProperty Z) (Z.dom i))).symm
  rw [Functor.map_comp, Functor.map_comp,
    restrictPhi_map_fraction Z K hK i hiK X0 n hn]
  simp only [eqToHom_map, Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rfl

/-- Generator case, original morphisms: always has a `Φ`-preimage. -/
lemma PhiPreimage_original (Z : Center C) (K : Set Z.I) (hK : K.Nonempty)
    {X0 Y0 : C} (c : X0 ⟶ Y0) :
    PhiPreimage Z K hK
      (Quiver.Hom.toPath
        (⟨(CenterMorphismProperty Z).Q.map c, GeneratorMorphismData.original ⟨c, rfl⟩⟩ :
          (GeneratorQuiver Z).Hom
            (objEquiv (CenterMorphismProperty Z) X0)
            (objEquiv (CenterMorphismProperty Z) Y0))) := by
  refine ⟨(CatToDila (Z.restrict K hK)).map c, ?_⟩
  show (restrictPhi Z K hK).map ((CatToDila (Z.restrict K hK)).map c) =
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
        (⟨fraction_in_loc_single Z ⟨i, ⟨X0, ⟨n, hn⟩⟩⟩,
          GeneratorMorphismData.fraction ⟨⟨i, ⟨X0, ⟨n, hn⟩⟩⟩, rfl⟩⟩ :
          (GeneratorQuiver Z).Hom
            (objEquiv (CenterMorphismProperty Z) X0)
            (objEquiv (CenterMorphismProperty Z) (Z.dom i)))) := by
  have hn' : (Sieve.generate (Presieve.singleton (Z.mor i))).arrows n := (hI i hiK) ▸ hn
  obtain ⟨X1, q, e, he, hq⟩ := hn'
  rcases he with ⟨-, rfl⟩
  haveI := MorphismProperty.Q_inverts (CenterMorphismProperty Z) (Z.mor i) ⟨i, rfl⟩
  have hfrac : fraction_in_loc_single Z ⟨i, ⟨X0, ⟨n, hn⟩⟩⟩ = (CenterMorphismProperty Z).Q.map q := by
    apply (cancel_mono ((CenterMorphismProperty Z).Q.map (Z.mor i))).1
    erw [fraction_comp_mor, ← Functor.map_comp]
    exact congrArg (CenterMorphismProperty Z).Q.map hq.symm
  have hEq :
      (GeneratedToDila Z).map
          (Quiver.Hom.toPath
            (⟨fraction_in_loc_single Z ⟨i, ⟨X0, ⟨n, hn⟩⟩⟩,
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
  show objEquiv (CenterMorphismProperty Z)
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

/-- Every morphism of `GeneratedCategory Z` has a `Φ`-preimage: induction on the underlying
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
  show (ImageCenterMorphismProperty Z (CatToDila (Z.sum W))).Q.Faithful
  apply faithful_of_comp_faithful
    (ImageCenterMorphismProperty Z (CatToDila (Z.sum W))).Q
    (Localization.Construction.lift
      (W := ImageCenterMorphismProperty Z (CatToDila (Z.sum W)))
      (ImageCenterMorphismProperty (Z.sum W) (CatToDila (Z.sum W))).Q
      (fun X Y f hf => by
        show IsIso ((ImageCenterMorphismProperty (Z.sum W) (CatToDila (Z.sum W))).Q.map f)
        apply CategoryTheory.MorphismProperty.Q_inverts
        exact ImageCenterMorphismProperty_sum_inl_le Z W (CatToDila (Z.sum W)) f hf))
  erw [Localization.Construction.fac]
  exact CatToDila_isSigmaRegular (Z.sum W)

lemma CatToDila_isSigmaRegular_sum_inr (Z W : Center C) :
    IsSigmaRegular W (CatToDila (Z.sum W)) := by
  show (ImageCenterMorphismProperty W (CatToDila (Z.sum W))).Q.Faithful
  apply faithful_of_comp_faithful
    (ImageCenterMorphismProperty W (CatToDila (Z.sum W))).Q
    (Localization.Construction.lift
      (W := ImageCenterMorphismProperty W (CatToDila (Z.sum W)))
      (ImageCenterMorphismProperty (Z.sum W) (CatToDila (Z.sum W))).Q
      (fun X Y f hf => by
        show IsIso ((ImageCenterMorphismProperty (Z.sum W) (CatToDila (Z.sum W))).Q.map f)
        apply CategoryTheory.MorphismProperty.Q_inverts
        exact ImageCenterMorphismProperty_sum_inr_le Z W (CatToDila (Z.sum W)) f hf))
  erw [Localization.Construction.fac]
  exact CatToDila_isSigmaRegular (Z.sum W)

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

/-- **Proposition 3.15 (i).** `Φ` belongs to `Cat^{Θ(dj)}_j-reg_{Dila Z}`. -/
theorem Phi315_isSigmaRegular (Z W : Center C) :
    IsSigmaRegular (CenterZW Z W) (Phi315 Z W) := by
  show (ImageCenterMorphismProperty (CenterZW Z W) (Phi315 Z W)).Q.Faithful
  rw [ImageCenterMorphismProperty_ZW_Phi_eq]
  exact CatToDila_isSigmaRegular_sum_inr Z W

lemma functorPushforward_singleton_congr {F G : C ⥤ D} (h : F = G) {X Y : C} (S : Sieve X)
    (f : Y ⟶ X) (hle : Sieve.functorPushforward G S ≤ Sieve.generate (Presieve.singleton (G.map f))) :
    Sieve.functorPushforward F S ≤ Sieve.generate (Presieve.singleton (F.map f)) := by
  subst h; exact hle

theorem Phi315_hsieve (Z W : Center C) :
    ∀ j : (CenterZW Z W).I,
      Sieve.functorPushforward (Phi315 Z W) ((CenterZW Z W).N j) ≤
        Sieve.generate (Presieve.singleton ((Phi315 Z W).map ((CenterZW Z W).mor j))) := by
  intro j
  show Sieve.functorPushforward (Phi315 Z W) (Sieve.functorPushforward (CatToDila Z) (W.N j)) ≤
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
def H0_315 (Z W : Center C) : Dila Z ⥤ (CenterMorphismProperty (Z.sum W)).Localization :=
  Phi315 Z W ⋙ DilaToLoc (Z.sum W)

theorem H0_315_obj (Z W : Center C) (X : C) :
    (H0_315 Z W).obj ((CatToDila Z).obj X) = (CenterMorphismProperty (Z.sum W)).Q.obj X := by
  show (DilaToLoc (Z.sum W)).obj ((Phi315 Z W).obj ((CatToDila Z).obj X)) = _
  rw [Phi315_obj_eq]
  exact congrArg (fun H : C ⥤ (CenterMorphismProperty (Z.sum W)).Localization => H.obj X)
    (CatToDila_comp_DilaToLoc (Z.sum W))

/-- `H0_315` sends the `Θ`-image of a `C`-morphism to its direct image under
`(CenterMorphismProperty (Z.sum W)).Q`, up to the object-identification `H0_315_obj`. -/
theorem H0_315_map (Z W : Center C) {X Y : C} (f : X ⟶ Y) :
    (H0_315 Z W).map ((CatToDila Z).map f) =
      eqToHom (H0_315_obj Z W X) ≫ (CenterMorphismProperty (Z.sum W)).Q.map f ≫
        eqToHom (H0_315_obj Z W Y).symm := by
  show (DilaToLoc (Z.sum W)).map ((Phi315 Z W).map ((CatToDila Z).map f)) = _
  rw [Phi315_map_eq]
  have h := Functor.congr_hom (CatToDila_comp_DilaToLoc (Z.sum W)) f
  rw [Functor.comp_map] at h
  simp only [Functor.map_comp, eqToHom_map]
  rw [h]
  rfl

/-- **Part of "Fact 2.14 applied a third time".** `H0_315` is regular for `CenterZW Z W`: its
image-center morphism property is exactly the `Sum.inr`-image of `(CenterMorphismProperty
(Z.sum W)).Q`'s own generators (via `H0_315_map`), which are already invertible by
`MorphismProperty.Q_inverts`, so `isoMorphismProperty_Q_faithful` applies directly — no
appeal to `Φ`'s own faithfulness (which is not known) is needed. -/
theorem H0_315_isSigmaRegular (Z W : Center C) :
    IsSigmaRegular (CenterZW Z W) (H0_315 Z W) := by
  show (ImageCenterMorphismProperty (CenterZW Z W) (H0_315 Z W)).Q.Faithful
  apply isoMorphismProperty_Q_faithful
  rintro X Y f ⟨j, hj⟩
  have hX : X = (H0_315 Z W).obj ((CatToDila Z).obj (W.dom j)) := congrArg Sigma.fst hj
  have hY : Y = (H0_315 Z W).obj ((CatToDila Z).obj (W.cod j)) := congrArg (fun s => s.2.1) hj
  subst X
  subst Y
  have hf : f = (H0_315 Z W).map ((CatToDila Z).map (W.mor j)) := by cases hj; rfl
  rw [hf, H0_315_map]
  haveI : IsIso ((CenterMorphismProperty (Z.sum W)).Q.map (W.mor j)) :=
    CategoryTheory.MorphismProperty.Q_inverts _ (W.mor j) ⟨Sum.inr j, rfl⟩
  infer_instance

/-- `H0_315` precomposed with `Θ` is *literally* `(CenterMorphismProperty (Z.sum W)).Q`, as a
functor equality (both sides `C ⥤ (CenterMorphismProperty (Z.sum W)).Localization`) — combining
`Phi315_spec` (`Θ ⋙ Φ = Θ'`) with `CatToDila_comp_DilaToLoc (Z.sum W)`. -/
theorem H0_315_comp (Z W : Center C) :
    CatToDila Z ⋙ H0_315 Z W = (CenterMorphismProperty (Z.sum W)).Q := by
  show CatToDila Z ⋙ (Phi315 Z W ⋙ DilaToLoc (Z.sum W)) = _
  rw [← Functor.assoc, Phi315_spec, CatToDila_comp_DilaToLoc]
  rfl

/-- The sieve condition needed to extend `H0_315` along `CatToDila (CenterZW Z W)`: `(CatToDila Z
⋙ H0_315 Z W).map (W.mor j)` is already an isomorphism, so its generated sieve is the top sieve. -/
theorem H0_315_hsieve (Z W : Center C) :
    ∀ j : (CenterZW Z W).I,
      Sieve.functorPushforward (H0_315 Z W) ((CenterZW Z W).N j) ≤
        Sieve.generate (Presieve.singleton ((H0_315 Z W).map ((CenterZW Z W).mor j))) := by
  intro j
  show Sieve.functorPushforward (H0_315 Z W) (Sieve.functorPushforward (CatToDila Z) (W.N j)) ≤
      Sieve.generate (Presieve.singleton ((H0_315 Z W).map ((CatToDila Z).map (W.mor j))))
  rw [← Sieve.functorPushforward_comp]
  have hiso : IsIso ((CatToDila Z ⋙ H0_315 Z W).map (W.mor j)) := by
    rw [H0_315_comp]
    exact CategoryTheory.MorphismProperty.Q_inverts _ (W.mor j) ⟨Sum.inr j, rfl⟩
  intro Y f _
  refine ⟨(CatToDila Z ⋙ H0_315 Z W).obj (W.dom j),
    f ≫ inv ((CatToDila Z ⋙ H0_315 Z W).map (W.mor j)),
    (CatToDila Z ⋙ H0_315 Z W).map (W.mor j), Presieve.singleton_self _, ?_⟩
  simp

/-- **The unique extension of `H0_315` along `β`.** By `Dila_universal_property (CenterZW Z W)
(H0_315 Z W) H0_315_isSigmaRegular H0_315_hsieve`. -/
noncomputable def H315 (Z W : Center C) :
    Dila (CenterZW Z W) ⥤ (CenterMorphismProperty (Z.sum W)).Localization :=
  (Dila_universal_property (CenterZW Z W) (H0_315 Z W)
      (H0_315_isSigmaRegular Z W) (H0_315_hsieve Z W)).choose

theorem H315_spec (Z W : Center C) :
    Beta315 Z W ⋙ H315 Z W = H0_315 Z W :=
  (Dila_universal_property (CenterZW Z W) (H0_315 Z W)
      (H0_315_isSigmaRegular Z W) (H0_315_hsieve Z W)).choose_spec.1

/-- `H315` agrees with `α' ⋙ DilaToLoc (Z.sum W)`: both extend `H0_315` along `β`
(`β ⋙ (α' ⋙ DilaToLoc (Z.sum W)) = (β ⋙ α') ⋙ DilaToLoc (Z.sum W) = Φ ⋙ DilaToLoc (Z.sum W)
= H0_315`, using `Alpha'315_spec`), so by the uniqueness half of the same universal property used
to build `H315`, they coincide. `Alpha'315` only needs Part (i), so this holds unconditionally. -/
theorem H315_eq (Z W : Center C) :
    H315 Z W = Alpha'315 Z W ⋙ DilaToLoc (Z.sum W) :=
  ((Dila_universal_property (CenterZW Z W) (H0_315 Z W)
      (H0_315_isSigmaRegular Z W) (H0_315_hsieve Z W)).choose_spec.2
    (Alpha'315 Z W ⋙ DilaToLoc (Z.sum W))
    (show Beta315 Z W ⋙ (Alpha'315 Z W ⋙ DilaToLoc (Z.sum W)) = H0_315 Z W by
      rw [← Functor.assoc, Alpha'315_spec]; rfl)).symm

theorem BetaComp315_hsieve (Z W : Center C) :
    ∀ k : (Z.sum W).I,
      Sieve.functorPushforward (CatToDila Z ⋙ Beta315 Z W) ((Z.sum W).N k) ≤
        Sieve.generate
          (Presieve.singleton ((CatToDila Z ⋙ Beta315 Z W).map ((Z.sum W).mor k))) := by
  rintro (i | j)
  · exact CatToDila_comp_image_sieve_le_singleton Z (Beta315 Z W) i
  · show Sieve.functorPushforward (CatToDila Z ⋙ Beta315 Z W) (W.N j) ≤
        Sieve.generate (Presieve.singleton ((CatToDila Z ⋙ Beta315 Z W).map (W.mor j)))
    rw [Sieve.functorPushforward_comp]
    exact CatToDila_image_sieve_le_singleton (CenterZW Z W) j

/-- **Proposition 3.15 (iii), setup.**  -/
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
  show (ImageCenterMorphismProperty Z F).Q.Faithful
  apply faithful_of_comp_faithful_gen
    (ImageCenterMorphismProperty Z F).Q
    (Localization.Construction.lift
      (W := ImageCenterMorphismProperty Z F)
      (ImageCenterMorphismProperty (Z.sum W) F).Q
      (fun X Y f hf => by
        show IsIso ((ImageCenterMorphismProperty (Z.sum W) F).Q.map f)
        apply CategoryTheory.MorphismProperty.Q_inverts
        exact ImageCenterMorphismProperty_sum_inl_le Z W F f hf))
  erw [Localization.Construction.fac]
  exact hF

/-- **Proposition 3.15 (v), part 1.** `Φ ∘ α = β` (equivalently `Φ ⋙ α = β` in Lean's
left-to-right composition). Conditional on item 2 (`hreg`). -/
theorem Phi315_comp_Alpha315 (Z W : Center C)
    (hreg : IsSigmaRegular (Z.sum W) (CatToDila Z ⋙ Beta315 Z W)) :
    Phi315 Z W ⋙ Alpha315 Z W hreg = Beta315 Z W := by
  apply Dila_factor_unique Z (CatToDila Z ⋙ Beta315 Z W) (Phi315 Z W ⋙ Alpha315 Z W hreg)
    (Beta315 Z W)
  · show CatToDila Z ⋙ Phi315 Z W ⋙ Alpha315 Z W hreg = CatToDila Z ⋙ Beta315 Z W
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
  · show CatToDila (Z.sum W) ⋙ Alpha315 Z W hreg ⋙ Alpha'315 Z W = CatToDila (Z.sum W)
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
  · show Beta315 Z W ⋙ Alpha'315 Z W ⋙ Alpha315 Z W hreg = Beta315 Z W
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
with `Z` alone: both `Sum.inl` and `Sum.inr` witnesses reduce to the *same* underlying generator
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
      show Sieve.functorPushforward (CatToDila Z) (M i) ≤
        Sieve.generate (Presieve.singleton ((CatToDila Z).map (Z.mor i)))
      exact le_trans (Sieve.functorPushforward_monotone (CatToDila Z) (Z.cod i) (hM i))
        (CatToDila_image_sieve_le_singleton Z i))).choose

theorem Fact313Phi_spec (Z : Center C) (M : ∀ i : Z.I, Sieve (C := C) (Z.cod i))
    (hM : ∀ i, M i ≤ Z.N i) :
    CatToDila (Z.altSieve M) ⋙ Fact313Phi Z M hM = CatToDila Z :=
  (Dila_universal_property (Z.altSieve M) (CatToDila Z)
    ((IsSigmaRegular_altSieve Z M (CatToDila Z)).2 (CatToDila_isSigmaRegular Z))
    (fun i => by
      show Sieve.functorPushforward (CatToDila Z) (M i) ≤
        Sieve.generate (Presieve.singleton ((CatToDila Z).map (Z.mor i)))
      exact le_trans (Sieve.functorPushforward_monotone (CatToDila Z) (Z.cod i) (hM i))
        (CatToDila_image_sieve_le_singleton Z i))).choose_spec.1

/-- **Fact 3.13.** `φ` is faithful: `Dila_factor_unique` identifies `φ ⋙ DilaToLoc Z` with
`DilaToLoc (Z.altSieve M)` (both are the unique factorization of the *same* raw localization
functor, since `CenterMorphismProperty` doesn't see the sieve component at all), and the latter
is always faithful (Fact 2.14). -/
theorem Fact313Phi_faithful (Z : Center C) (M : ∀ i : Z.I, Sieve (C := C) (Z.cod i))
    (hM : ∀ i, M i ≤ Z.N i) :
    (Fact313Phi Z M hM).Faithful := by
  apply faithful_of_comp_faithful (Fact313Phi Z M hM) (DilaToLoc Z)
  have heq : Fact313Phi Z M hM ⋙ DilaToLoc Z = DilaToLoc (Z.altSieve M) := by
    apply Dila_factor_unique (Z.altSieve M) (LocalizationFunctor Z)
    · show CatToDila (Z.altSieve M) ⋙ Fact313Phi Z M hM ⋙ DilaToLoc Z = LocalizationFunctor Z
      rw [← Functor.assoc, Fact313Phi_spec, CatToDila_comp_DilaToLoc]
    · show CatToDila (Z.altSieve M) ⋙ DilaToLoc (Z.altSieve M) = LocalizationFunctor Z
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
  show Sieve.functorPushforward (CatToDila (Z.sum (Z.altSieve N'))) (Z.N i ⊔ N' i) ≤ _
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
  · show CatToDila (Z.sieveUnion N') ⋙ Alpha318 Z N' ⋙ Alpha'318 Z N' =
        CatToDila (Z.sieveUnion N')
    rw [← Functor.assoc, Alpha318_spec, Alpha'318_spec]
  · exact Functor.comp_id _
  · exact CatToDila_isSigmaRegular (Z.sieveUnion N')

theorem Alpha'318_comp_Alpha318 (Z : Center C) (N' : ∀ i : Z.I, Sieve (C := C) (Z.cod i)) :
    Alpha'318 Z N' ⋙ Alpha318 Z N' = 𝟭 (Dila (Z.sum (Z.altSieve N'))) := by
  apply Dila_factor_unique (Z.sum (Z.altSieve N')) (CatToDila (Z.sum (Z.altSieve N')))
    (Alpha'318 Z N' ⋙ Alpha318 Z N') (𝟭 (Dila (Z.sum (Z.altSieve N'))))
  · show CatToDila (Z.sum (Z.altSieve N')) ⋙ Alpha'318 Z N' ⋙ Alpha318 Z N' =
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

/-! ### Section 4: Codilatations of categories

Codilatations are defined via dilatations and opposite categories, exactly as in the paper. -/

/-- **Definition 2.1 (dual notion).** A cosieve from `X`: a collection of morphisms out of `X`,
stable under postcomposition. -/
structure Cosieve {C : Type u₁} [Category.{v₁} C] (X : C) where
  /-- the underlying collection of morphisms out of `X` -/
  arrows : ∀ ⦃Y⦄, (X ⟶ Y) → Prop
  /-- stability by postcomposition -/
  upward_closed : ∀ {Y Z} {f : X ⟶ Y} (_ : arrows f) (g : Y ⟶ Z), arrows (f ≫ g)

/-- **Definition 2.1.** The cosieve generated by a collection `E` of morphisms out of `X`
(denoted `CoSC_E` in the paper): `f` is generated iff `f = e ≫ h` for some `e ∈ E`. -/
def Cosieve.generate {C : Type u₁} [Category.{v₁} C] {X : C} (E : ∀ ⦃Y⦄, (X ⟶ Y) → Prop) :
    Cosieve X where
  arrows Z f := ∃ (Y : C) (e : X ⟶ Y) (h : Y ⟶ Z), E e ∧ e ≫ h = f
  upward_closed := by
    rintro Y Z _ ⟨W, e, h, he, rfl⟩ k
    exact ⟨W, e, h ≫ k, he, by simp⟩

/-- **Fact 4.2.** A cosieve from `X` is *the same data* as a sieve over `op X` in `Cᵒᵖ`. -/
def Cosieve.toSieveOp {C : Type u₁} [Category.{v₁} C] {X : C} (V : Cosieve X) :
    Sieve (Opposite.op X : Cᵒᵖ) where
  arrows {Y} f := V.arrows f.unop
  downward_closed {Y Z f} hf g := V.upward_closed hf g.unop

/-- **Fact 4.2**, converse direction. -/
def Sieve.toCosieveUnop {C : Type u₁} [Category.{v₁} C] {X : C}
    (S : Sieve (Opposite.op X : Cᵒᵖ)) : Cosieve X where
  arrows {Y} f := S.arrows f.op
  upward_closed {Y Z f} hf g := S.downward_closed hf g.op

/-- **Fact 4.2**, as an explicit equivalence: a cosieve from `X` *is* a sieve over `op X`. -/
def Cosieve.equivSieveOp {C : Type u₁} [Category.{v₁} C] (X : C) :
    Cosieve X ≃ Sieve (Opposite.op X : Cᵒᵖ) where
  toFun := Cosieve.toSieveOp
  invFun := Sieve.toCosieveUnop
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Fact 4.4.** `CoSC_E = SCᵒᵖ_E`: the cosieve generated by `E` equals (under Fact 4.2's
identification) the sieve generated by `E`'s image under `.op` in `Cᵒᵖ`. -/
theorem Cosieve.generate_toSieveOp {C : Type u₁} [Category.{v₁} C] {X : C}
    (E : ∀ ⦃Y⦄, (X ⟶ Y) → Prop) :
    (Cosieve.generate E).toSieveOp =
      Sieve.generate (fun {Y'} (g : Y' ⟶ (Opposite.op X : Cᵒᵖ)) => E g.unop) := by
  apply Sieve.ext
  intro Y f
  constructor
  · rintro ⟨W, e, h, he, heq⟩
    refine ⟨Opposite.op W, h.op, e.op, he, ?_⟩
    show h.op ≫ e.op = f
    rw [← CategoryTheory.op_comp, heq, Quiver.Hom.op_unop]
  · rintro ⟨W, h, e, he, heq⟩
    refine ⟨W.unop, e.unop, h.unop, he, ?_⟩
    show e.unop ≫ h.unop = f.unop
    rw [← CategoryTheory.unop_comp, heq]

/-- A cocenter `{[Vᵢ,dᵢ]}_{i∈I}` in `C` (Definition 4.1): `dᵢ` a morphism, `Vᵢ` a cosieve from
`dom(dᵢ)`. Following Fact 4.2 (a cosieve from `X` is *the same data* as a sieve over `op X` in
`Cᵒᵖ`), `Vᵢ` is recorded directly as a `Sieve` in `Cᵒᵖ` over `op (dom dᵢ)`. -/
structure Cocenter (C : Type u) [Category.{v} C] where
  I : Type u
  nonempty : Nonempty I
  dom : I → C
  cod : I → C
  mor : ∀ i : I, dom i ⟶ cod i
  V : ∀ i : I, Sieve (C := Cᵒᵖ) (Opposite.op (dom i))

/-- The center on `Cᵒᵖ` obtained by regarding `{[Vᵢ,dᵢ]}_{i∈I}` as `{[Vᵢ,(dᵢ)ᵒᵖ]}_{i∈I}`
(Fact 4.2). -/
def Cocenter.toCenterOp (co : Cocenter C) : Center Cᵒᵖ where
  I := co.I
  nonempty := co.nonempty
  dom := fun i => Opposite.op (co.cod i)
  cod := fun i => Opposite.op (co.dom i)
  mor := fun i => (co.mor i).op
  N := co.V

/-- The underlying `{dᵢ}`-only center on `C`. `IsSigmaRegular`/`ImageCenterMorphismProperty` only
depend on `I`/`dom`/`cod`/`mor` (never on the sieve component), so any placeholder sieve works
here. -/
def Cocenter.toCenter (co : Cocenter C) : Center C where
  I := co.I
  nonempty := co.nonempty
  dom := co.dom
  cod := co.cod
  mor := co.mor
  N := fun _ => ⊤

/-- **Definition 4.3.** The codilatation of `C` with cocenter `{[Vᵢ,dᵢ]}_{i∈I}`:
`C[{Vᵢ∘(dᵢ)⁻¹}_{i∈I}] := (Cᵒᵖ[{(dᵢ)⁻¹∘Vᵢ}_{i∈I}])ᵒᵖ`. -/
def Codila (co : Cocenter C) : Type u := (Dila (co.toCenterOp))ᵒᵖ

instance instCategoryCodila (co : Cocenter C) : Category (Codila co) := by
  unfold Codila; infer_instance

/-- General fact used to transport faithfulness of `.Q` across `Cᵒᵖ`: if `W.Q` is faithful, so is
`(W.op).Q`. Proved via the universal property of `(W.op).Localization` (`Prop 2.8` /
`Localization.Construction.lift`), *not* via raw combinatorics — `(W.Q).op` is faithful for free
(`.op` preserves faithfulness), it inverts `W.op` (since `.op` preserves isomorphisms), so it
factors uniquely through `(W.op).Q`, and `faithful_of_comp_faithful` finishes it. -/
lemma MorphismProperty.op_Q_faithful {D : Type u} [Category.{v} D] (W : MorphismProperty D)
    (hW : W.Q.Faithful) : W.op.Q.Faithful := by
  haveI := hW
  apply faithful_of_comp_faithful_gen
    W.op.Q
    (Localization.Construction.lift (W := W.op) W.Q.op
      (fun X Y f hf => by
        show IsIso (W.Q.map f.unop).op
        haveI : IsIso (W.Q.map f.unop) := CategoryTheory.MorphismProperty.Q_inverts W f.unop hf
        infer_instance))
  erw [Localization.Construction.fac]
  infer_instance

/-- **Proposition 4.5 (i).** The canonical functor `Υ : C ⥤ Codila co`, obtained by taking the
`rightOp` of `Θ : Cᵒᵖ ⥤ Dila (co.toCenterOp)` (Proposition 3.1). -/
def Cocenter.Upsilon (co : Cocenter C) : C ⥤ Codila co :=
  (CatToDila (co.toCenterOp)).rightOp

/-- **Proposition 4.5 (ii).** The canonical faithful functor
`Codila co ⥤ (Cᵒᵖ[{(dᵢ)⁻¹}])ᵒᵖ` (which identifies with `C[{dᵢ}⁻¹]`, e.g. via the explicit
description of fractions — Fact 4.4 — matching the paper's own aside). -/
instance Codila.faithful_to_loc_op (co : Cocenter C) :
    ((DilaToLoc (co.toCenterOp)).op :
      Codila co ⥤ ((CenterMorphismProperty (co.toCenterOp)).Localization)ᵒᵖ).Faithful := by
  haveI := Fact_2_14 (co.toCenterOp)
  infer_instance

/-- `Cocenter.Upsilon`'s `ImageCenterMorphismProperty` (relative to `co.toCenter`) is exactly the
`.op` of `Θ`'s (relative to `co.toCenterOp`), matching how `Upsilon = (CatToDila
(co.toCenterOp)).rightOp` is built. -/
lemma ImageCenterMorphismProperty_toCenter_Upsilon (co : Cocenter C) :
    ImageCenterMorphismProperty co.toCenter co.Upsilon =
      (ImageCenterMorphismProperty (co.toCenterOp) (CatToDila (co.toCenterOp))).op := by
  funext X Y f
  apply propext
  constructor
  · rintro ⟨i, hi⟩
    have hX : X = co.Upsilon.obj (co.dom i) := congrArg Sigma.fst hi
    have hY : Y = co.Upsilon.obj (co.cod i) := congrArg (fun s => s.2.1) hi
    subst hX
    subst hY
    have hf : f = co.Upsilon.map (co.mor i) := by cases hi; rfl
    subst hf
    exact ⟨i, rfl⟩
  · rintro ⟨i, hi⟩
    have hX : Opposite.unop Y = (CatToDila co.toCenterOp).obj (co.toCenterOp.dom i) :=
      congrArg Sigma.fst hi
    have hY : Opposite.unop X = (CatToDila co.toCenterOp).obj (co.toCenterOp.cod i) :=
      congrArg (fun s => s.2.1) hi
    refine ⟨i, ?_⟩
    have hXeq : X = Opposite.op ((CatToDila co.toCenterOp).obj (co.toCenterOp.cod i)) := by
      rw [← hY]; exact (Opposite.op_unop X).symm
    have hYeq : Y = Opposite.op ((CatToDila co.toCenterOp).obj (co.toCenterOp.dom i)) := by
      rw [← hX]; exact (Opposite.op_unop Y).symm
    subst hXeq
    subst hYeq
    injection hi with h1 h2
    injection h2 with h3 hf
    have hfeq : f = ((CatToDila co.toCenterOp).map (co.toCenterOp.mor i)).op := by
      rw [← hf]; exact (Quiver.Hom.op_unop f).symm
    subst hfeq
    rfl

/-- **Proposition 4.5 (iii).** `Υ` belongs to `Cat^{{dᵢ}-reg}_C` (i.e. is `{dᵢ}`-regular). -/
theorem Cocenter.Upsilon_isSigmaRegular (co : Cocenter C) :
    IsSigmaRegular co.toCenter co.Upsilon := by
  show (ImageCenterMorphismProperty co.toCenter co.Upsilon).Q.Faithful
  rw [ImageCenterMorphismProperty_toCenter_Upsilon]
  exact MorphismProperty.op_Q_faithful _ (CatToDila_isSigmaRegular (co.toCenterOp))

/-- `Cocenter.Upsilon` post-composed with any `G` corresponds, on the nose after taking `.op`, to
`Θ` post-composed with `G.rightOp`. This is the key bridge letting factorizations through
`Codila co` be transported to (and from) factorizations through `Dila (co.toCenterOp)`. -/
lemma Cocenter.comp_Upsilon_op (co : Cocenter C) (G : Codila co ⥤ D) :
    (co.Upsilon ⋙ G).op = CatToDila (co.toCenterOp) ⋙ G.rightOp := rfl

/-- `ImageCenterMorphismProperty` for `(co.toCenterOp, F.op)` is exactly the `.op` of
`ImageCenterMorphismProperty` for `(co.toCenter, F)`. -/
lemma ImageCenterMorphismProperty_toCenterOp_op (co : Cocenter C) (F : C ⥤ D) :
    ImageCenterMorphismProperty (co.toCenterOp) F.op =
      (ImageCenterMorphismProperty co.toCenter F).op := by
  funext X Y f
  apply propext
  constructor
  · rintro ⟨i, hi⟩
    have hX : X = Opposite.op (F.obj (co.cod i)) := congrArg Sigma.fst hi
    have hY : Y = Opposite.op (F.obj (co.dom i)) := congrArg (fun s => s.2.1) hi
    subst hX
    subst hY
    have hf : f = (F.map (co.mor i)).op := by cases hi; rfl
    subst hf
    exact ⟨i, rfl⟩
  · rintro ⟨i, hi⟩
    have hX : Opposite.unop Y = F.obj (co.dom i) := congrArg Sigma.fst hi
    have hY : Opposite.unop X = F.obj (co.cod i) := congrArg (fun s => s.2.1) hi
    refine ⟨i, ?_⟩
    have hXeq : X = Opposite.op (F.obj (co.cod i)) := by rw [← hY]
    have hYeq : Y = Opposite.op (F.obj (co.dom i)) := by rw [← hX]
    subst hXeq
    subst hYeq
    injection hi with h1 h2
    injection h2 with h3 hf
    have hf' : f.unop = F.map (co.mor i) := hf
    have hfeq : f = (F.map (co.mor i)).op := by
      rw [← hf']; exact (Quiver.Hom.op_unop f).symm
    subst hfeq
    rfl

/-- If `F : C ⥤ D` is `{dᵢ}`-regular, so is `F.op : Cᵒᵖ ⥤ Dᵒᵖ` (relative to `co.toCenterOp`). -/
lemma IsSigmaRegular_toCenterOp_op (co : Cocenter C) (F : C ⥤ D)
    (hF : IsSigmaRegular co.toCenter F) : IsSigmaRegular (co.toCenterOp) F.op := by
  show (ImageCenterMorphismProperty (co.toCenterOp) F.op).Q.Faithful
  rw [ImageCenterMorphismProperty_toCenterOp_op]
  exact MorphismProperty.op_Q_faithful _ hF

/-- **Proposition 4.5 (iv).** `Υ` represents the covariant functor `Cat^{{dᵢ}-reg}_C → Set`,
`(C --F--> D) ↦ {∗}` if `CoS^D_{F(Vᵢ)} ⊂ CoS^D_{F(dᵢ)}` for all `i`, else `∅`. -/
theorem Cocenter.represents (co : Cocenter C) (F : C ⥤ D) (hfaith : IsSigmaRegular co.toCenter F) :
    (∃! G : Codila co ⥤ D, co.Upsilon ⋙ G = F) ↔
      ∀ i : co.I, Sieve.functorPushforward F.op (co.V i) ≤
        Sieve.generate (Presieve.singleton (F.op.map (co.toCenterOp.mor i))) := by
  show (∃! G : Codila co ⥤ D, co.Upsilon ⋙ G = F) ↔
      ∀ i : co.toCenterOp.I, Sieve.functorPushforward F.op (co.toCenterOp.N i) ≤
        Sieve.generate (Presieve.singleton (F.op.map (co.toCenterOp.mor i)))
  rw [← CatToDila_represents (co.toCenterOp) F.op (IsSigmaRegular_toCenterOp_op co F hfaith)]
  constructor
  · rintro ⟨G, hG, hU⟩
    refine ⟨G.rightOp, by
      show CatToDila co.toCenterOp ⋙ G.rightOp = F.op
      rw [← Cocenter.comp_Upsilon_op, hG], ?_⟩
    intro G'' hG''
    have hop : (co.Upsilon ⋙ G''.leftOp).op = F.op := by
      erw [Cocenter.comp_Upsilon_op]
      simpa only using! hG''
    have heq : co.Upsilon ⋙ G''.leftOp = F := by
      have := congrArg Functor.unop hop
      simpa only using! this
    have := hU G''.leftOp heq
    have := congrArg Functor.rightOp this
    simpa only using! this
  · rintro ⟨G', hG', hU'⟩
    refine ⟨G'.leftOp, ?_, ?_⟩
    · have hop : (co.Upsilon ⋙ G'.leftOp).op = F.op := by
        erw [Cocenter.comp_Upsilon_op]
        simpa only using! hG'
      have := congrArg Functor.unop hop
      simpa only using! this
    · intro G'' hG''
      have hop : CatToDila (co.toCenterOp) ⋙ G''.rightOp = F.op := by
        rw [← Cocenter.comp_Upsilon_op, hG'']
      have := hU' G''.rightOp hop
      have := congrArg Functor.leftOp this
      simpa only using! this

/-! ### §5.1: Universal property of localizations, recovered from the universal property of
dilatations

By Fact 2.15, the dilatation for a center whose sieves are all the trivial one
`Nᵢ = S^C_{Idcod(dᵢ)} = ⊤` is the plain localization `C[{dᵢ}⁻¹]`. Given that identification, this
section shows `Dila_universal_property` (Theorem 3.10) recovers `Proposition 2.8` (the universal
property of plain localizations) as a special case: a functor inverting every `dᵢ` factors
uniquely through this dilatation. -/

/-- The sieve generated by a single isomorphism is the top sieve. -/
lemma Sieve.generate_singleton_eq_top_of_isIso {D : Type*} [Category D] {X Y : D} (g : X ⟶ Y)
    [IsIso g] : Sieve.generate (Presieve.singleton g) = ⊤ := by
  refine le_antisymm le_top (fun Z f _ => ?_)
  exact ⟨X, f ≫ inv g, g, Presieve.singleton_self _, by simp⟩

/-- The center built from an arbitrary indexed family of morphisms `{dᵢ}_{i∈I}`, using the
trivial choice of sieves `Nᵢ = S^C_{Idcod(dᵢ)} = ⊤` — matching the hypothesis of Fact 2.15. -/
def Center.ofMorphisms {I : Type u} (hI : Nonempty I) (dom cod : I → C)
    (mor : ∀ i, dom i ⟶ cod i) : Center C where
  I := I
  nonempty := hI
  dom := dom
  cod := cod
  mor := mor
  N := fun _ => ⊤

/-- **§5.1.** The universal property of dilatations recovers the universal property of
localizations (Proposition 2.8, matching `Fact 2.15`'s identification of this dilatation with
`C[{dᵢ}⁻¹]`): any `F : C ⥤ D` inverting every generator `dᵢ = mor i` factors uniquely through
`Dila (Center.ofMorphisms hI dom cod mor)`. -/
theorem Center.ofMorphisms_universal_property {I : Type u} (hI : Nonempty I) (dom cod : I → C)
    (mor : ∀ i, dom i ⟶ cod i) (F : C ⥤ D) (hF : ∀ i, IsIso (F.map (mor i))) :
    ∃! G : Dila (Center.ofMorphisms hI dom cod mor) ⥤ D,
      CatToDila (Center.ofMorphisms hI dom cod mor) ⋙ G = F := by
  set Z := Center.ofMorphisms hI dom cod mor with hZ
  apply Dila_universal_property Z F
  · show (ImageCenterMorphismProperty Z F).Q.Faithful
    apply isoMorphismProperty_Q_faithful
    rintro X Y f ⟨i, hi⟩
    have hX : X = F.obj (Z.dom i) := congrArg Sigma.fst hi
    have hY : Y = F.obj (Z.cod i) := congrArg (fun s => s.2.1) hi
    subst hX
    subst hY
    have hf : f = F.map (Z.mor i) := by cases hi; rfl
    subst hf
    exact hF i
  · intro i
    show Sieve.functorPushforward F (⊤ : Sieve (Z.cod i)) ≤
      Sieve.generate (Presieve.singleton (F.map (Z.mor i)))
    haveI : IsIso (F.map (Z.mor i)) := hF i
    rw [Sieve.generate_singleton_eq_top_of_isIso (F.map (Z.mor i))]
    exact le_top

/-- **Fact 2.15, isomorphism-witness.** With all sieves trivial, `Θ(dᵢ)` already has an explicit
inverse fraction inside the dilatation: `n/dᵢ` at `n := 𝟙 (cod i)` (valid since `N i = ⊤`), with
`Prop_3_3`'s epi-ness closing the other triangle identity. -/
theorem CatToDila_ofMorphisms_isIso {I : Type u} (hI : Nonempty I) (dom cod : I → C)
    (mor : ∀ i, dom i ⟶ cod i) (i : I) :
    IsIso ((CatToDila (Center.ofMorphisms hI dom cod mor)).map (mor i)) := by
  set Z := Center.ofMorphisms hI dom cod mor with hZ
  set inv := fraction_in_dila_single Z ⟨i, ⟨cod i, ⟨𝟙 (cod i), trivial⟩⟩⟩ with hinv
  have hri : inv ≫ (CatToDila Z).map (mor i) = 𝟙 _ := by
    have h := fraction_in_dila_comp_mor Z i (cod i) (𝟙 (cod i)) trivial
    erw [Functor.map_id] at h
    exact h
  haveI : Mono ((CatToDila Z).map (mor i)) := (Prop_3_3 Z i).1
  have hli : (CatToDila Z).map (mor i) ≫ inv = 𝟙 _ :=
    (cancel_mono ((CatToDila Z).map (mor i))).mp (by
      erw [Category.assoc, hri, Category.comp_id])
  exact ⟨inv, hli, hri⟩

theorem CatToDila_ofMorphisms_isInvertedBy {I : Type u} (hI : Nonempty I) (dom cod : I → C)
    (mor : ∀ i, dom i ⟶ cod i) :
    (CenterMorphismProperty (Center.ofMorphisms hI dom cod mor)).IsInvertedBy
      (CatToDila (Center.ofMorphisms hI dom cod mor)) := by
  intro X Y f hf
  rcases hf with ⟨i, hi⟩
  have hX : X = (Center.ofMorphisms hI dom cod mor).dom i := congrArg Sigma.fst hi
  have hY : Y = (Center.ofMorphisms hI dom cod mor).cod i := congrArg (fun s => s.2.1) hi
  subst hX; subst hY
  have hf' : f = (Center.ofMorphisms hI dom cod mor).mor i := by cases hi; rfl
  rw [hf']
  exact CatToDila_ofMorphisms_isIso hI dom cod mor i

/-- The inverse to `DilaToLoc (Center.ofMorphisms ...)`, built via the raw localization's own
universal property (`Localization.Construction.lift`), now that `CatToDila` inverts every
generator (`CatToDila_ofMorphisms_isInvertedBy`). -/
noncomputable def Fact215Inv {I : Type u} (hI : Nonempty I) (dom cod : I → C)
    (mor : ∀ i, dom i ⟶ cod i) :
    (CenterMorphismProperty (Center.ofMorphisms hI dom cod mor)).Localization ⥤
      Dila (Center.ofMorphisms hI dom cod mor) :=
  Localization.Construction.lift (CatToDila (Center.ofMorphisms hI dom cod mor))
    (CatToDila_ofMorphisms_isInvertedBy hI dom cod mor)

theorem Fact215Inv_fac {I : Type u} (hI : Nonempty I) (dom cod : I → C)
    (mor : ∀ i, dom i ⟶ cod i) :
    (CenterMorphismProperty (Center.ofMorphisms hI dom cod mor)).Q ⋙
        Fact215Inv hI dom cod mor = CatToDila (Center.ofMorphisms hI dom cod mor) :=
  Localization.Construction.fac _ _

/-- **Fact 2.15.** `Dila (Center.ofMorphisms hI dom cod mor)` (dilatation with all sieves
trivial) is isomorphic to the plain localization `C[{morᵢ}⁻¹]`. -/
noncomputable def Fact_2_15 {I : Type u} (hI : Nonempty I) (dom cod : I → C)
    (mor : ∀ i, dom i ⟶ cod i) :
    Cat.of (Dila (Center.ofMorphisms hI dom cod mor)) ≅
      Cat.of (CenterMorphismProperty (Center.ofMorphisms hI dom cod mor)).Localization where
  hom := (DilaToLoc (Center.ofMorphisms hI dom cod mor)).toCatHom
  inv := (Fact215Inv hI dom cod mor).toCatHom
  hom_inv_id := by
    apply Cat.ext
    apply Dila_factor_unique (Center.ofMorphisms hI dom cod mor)
      (CatToDila (Center.ofMorphisms hI dom cod mor))
    · show CatToDila (Center.ofMorphisms hI dom cod mor) ⋙
          DilaToLoc (Center.ofMorphisms hI dom cod mor) ⋙ Fact215Inv hI dom cod mor =
        CatToDila (Center.ofMorphisms hI dom cod mor)
      rw [← Functor.assoc, CatToDila_comp_DilaToLoc]
      show (CenterMorphismProperty (Center.ofMorphisms hI dom cod mor)).Q ⋙
          Fact215Inv hI dom cod mor = CatToDila (Center.ofMorphisms hI dom cod mor)
      exact Fact215Inv_fac hI dom cod mor
    · exact Functor.comp_id _
    · exact CatToDila_isSigmaRegular (Center.ofMorphisms hI dom cod mor)
  inv_hom_id := by
    apply Cat.ext
    apply Localization.Construction.uniq
    show (CenterMorphismProperty (Center.ofMorphisms hI dom cod mor)).Q ⋙
        Fact215Inv hI dom cod mor ⋙ DilaToLoc (Center.ofMorphisms hI dom cod mor) =
      (CenterMorphismProperty (Center.ofMorphisms hI dom cod mor)).Q ⋙ 𝟭 _
    rw [← Functor.assoc, Fact215Inv_fac]
    show CatToDila (Center.ofMorphisms hI dom cod mor) ⋙
        DilaToLoc (Center.ofMorphisms hI dom cod mor) =
      (CenterMorphismProperty (Center.ofMorphisms hI dom cod mor)).Q ⋙ 𝟭 _
    rw [CatToDila_comp_DilaToLoc, Functor.comp_id]
    rfl

/-! ### §5.0.2: Dilatations of commutative rings and semirings

The ring-theoretic dilatation `A[{Mᵢ/aᵢ}]` from [M], matching `Multicenter A` below to the
paper's `{[Mᵢ, aᵢ]}ᵢ∈I` (ported from `ProjConstruction/Proj`). -/

section RingDilatation

/-! #### Vendored from `Project/Dilatation/lemma.lean` -/

variable {ι A' B' F' : Type*} [CommSemiring A'] [CommSemiring B'] [FunLike F' A' B']
  [RingHomClass F' A' B']

namespace Ideal

lemma prod_span' (f : ι → A') (s : Finset ι) :
    Ideal.span {∏ i ∈ s, f i} = ∏ i ∈ s, Ideal.span {f i} := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, ← Ideal.span_singleton_mul_span_singleton, ih,
      Finset.prod_insert hi]

lemma prod_map (f : ι → Ideal A') (s : Finset ι) (χ : F') :
    Ideal.map χ (∏ i ∈ s, f i) = ∏ i ∈ s, Ideal.map χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Ideal.map_top]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Ideal.map_mul, Finset.prod_insert hi, ih]

end Ideal

/-! #### Vendored from `Project/Dilatation/Family.lean` -/

section

variable {A' G : Type*} [CommMonoid A'] [Zero G] [Pow A' G]
variable {ι : Type*}
def familyPow (f : ι → A') (v : ι →₀ G) : A' := v.prod fun i k ↦ f i ^ k

def instFamilyPow : HPow (ι → A') (ι →₀ G) A' where
  hPow f v := familyPow f v

scoped[Family] attribute [instance] instFamilyPow

open Family

lemma familyPow_def (f : ι → A') (v : ι →₀ G) : f^v = v.prod fun i k ↦ f i ^ k := rfl

lemma familyPow_add (f : ι → A') (v w : ι →₀ ℕ) : f^(v + w) = f^v * f^w := by
  classical
  simp only [familyPow_def]
  rw [Finsupp.prod_add_index (by simp) (by simp [pow_add])]

@[simp]
lemma familyPow_zero (f : ι → A') : f^(0 : ι →₀ ℕ) = (1 : A') := by
  simp only [familyPow_def]
  rw [Finsupp.prod_zero_index]

/-- A family-power raised to an ordinary `ℕ`-power is the family-power at the scaled exponent:
`(f^ν)^k = f^(k•ν)`. Used to relate a "power of a power" to a single flattened exponent. -/
lemma familyPow_nsmul (f : ι → A') (ν : ι →₀ ℕ) (k : ℕ) : (f^ν)^k = f^(k • ν) := by
  induction k with
  | zero => simp
  | succ n ih => rw [succ_nsmul, familyPow_add, pow_succ, ih]

/-- Flattening a finite `ℕ`-combination `μ` of exponent profiles and taking a single family-power
agrees with taking the family-power at each profile first and combining: `μ.prod (fun ν k ↦
(f^ν)^k) = f^(μ.sum fun ν k ↦ k•ν)`. This is the key identity behind reindexing a multi-center by
exponent profiles (`Multicenter.reindex_LargeIdeal_pow`, `Multicenter.reindex_elem_pow` below). -/
lemma family_pow_flatten (f : ι → A') (μ : (ι →₀ ℕ) →₀ ℕ) :
    μ.prod (fun ν k => (f^ν)^k) = f ^ (μ.sum fun ν k => k • ν) := by
  induction μ using Finsupp.induction with
  | zero => simp
  | single_add ν0 k0 μ' hν0 hk0 ih =>
    rw [Finsupp.prod_add_index' (by simp) (fun ν k k' => by rw [pow_add]),
        Finsupp.sum_add_index' (by simp) (fun ν k k' => by rw [add_smul]),
        Finsupp.prod_single_index (by simp), Finsupp.sum_single_index (by simp),
        familyPow_add, ih, familyPow_nsmul]

end

namespace Ideal

variable {A' : Type*} [CommSemiring A']
variable {ι : Type*} (M : ι → Ideal A') (a : ι → A')

open Family

lemma familyPow_def (v : ι →₀ ℕ) : M^v = v.prod fun i k ↦ M i ^ k := rfl

variable {M} in
lemma mem_familyPow_add {v w : ι →₀ ℕ} {x y : A'} (hx : x ∈ M^v) (hy : y ∈ M^w) :
  x * y ∈ M^(v+w) := by
  classical
  rw [familyPow_add]
  exact Ideal.mul_mem_mul hx hy

variable {M a} in
lemma mem_familyPow_of_mem {v : ι →₀ ℕ} (mem : ∀ i ∈ v.support, a i ∈ M i) : a^v ∈ M^v :=
  Ideal.prod_mem_prod fun _ hi ↦ Ideal.pow_mem_pow (mem _ hi) _

end Ideal

/-! #### Vendored from `Project/Dilatation/Multicenter.lean` (live, non-commented-out part only) -/

open DirectSum Family

section defs

variable (A' : Type*) [CommSemiring A']

structure Multicenter where
  (index : Type*)
  (ideal : index → Ideal A')
  (elem : index → A')
end defs

namespace Multicenter

section semiring

variable {A' : Type*} [CommSemiring A'] (M : Multicenter A')

scoped notation: max M"^ℕ"  => Multicenter.index M  →₀ ℕ

def LargeIdeal (i : M.index) : Ideal A' := M.ideal i + Ideal.span {M.elem i}

lemma elem_mem_LargeIdeal (i: M.index) : M.elem i ∈ M.LargeIdeal i := by
  suffices inequality : Ideal.span {M.elem i} ≤ M.LargeIdeal i by
   apply inequality
   exact Ideal.mem_span_singleton_self (M.elem i)
  simp only [LargeIdeal, Submodule.add_eq_sup, le_sup_right]

abbrev prodLargeIdealPower (v : M^ℕ) : Ideal A' :=
  v.prod fun i k ↦ M.LargeIdeal i ^ k

lemma elem_pow_mem_LargeIdealPow (ν : M^ℕ) : M.elem^ν ∈ M.LargeIdeal^ν :=
  Ideal.mem_familyPow_of_mem fun i _ => elem_mem_LargeIdeal M i

/-- The `ν`-indexed reindexing of `M`: index type `M^ℕ` (exponent profiles), ideal `L^ν` at `ν`,
element `a^ν` at `ν`. Dilating by this center gives back the same ring as dilating by `M`
directly (`reindexRingEquiv` below, inside `Dilatation`). -/
@[reducible] def reindex : Multicenter A' where
  index := M^ℕ
  ideal := M.prodLargeIdealPower
  elem := fun ν => M.elem^ν

/-- `reindex`'s large ideal at `ν` is just `L^ν` itself: the `+span{a^ν}` correction is already
absorbed, since `a^ν ∈ L^ν` (`elem_pow_mem_LargeIdealPow`). -/
lemma reindex_LargeIdeal (ν : M^ℕ) : (M.reindex).LargeIdeal ν = M.LargeIdeal^ν := by
  show M.prodLargeIdealPower ν + Ideal.span {M.elem^ν} = M.prodLargeIdealPower ν
  rw [Submodule.add_eq_sup, sup_eq_left, Ideal.span_le, Set.singleton_subset_iff]
  exact elem_pow_mem_LargeIdealPow M ν

/-- Flatten a finite `ℕ`-combination of exponent profiles into a single exponent profile:
`μ ↦ Σ_ν μ(ν)•ν`. This is the comparison map between `reindex`'s own exponent profiles
(`(M^ℕ) →₀ ℕ`) and `M`'s (`M^ℕ`). -/
noncomputable def flatten (μ : (M^ℕ) →₀ ℕ) : M^ℕ := μ.sum (fun ν k => k • ν)

lemma flatten_add (μ μ' : (M^ℕ) →₀ ℕ) : M.flatten (μ + μ') = M.flatten μ + M.flatten μ' := by
  unfold flatten
  refine Finsupp.sum_add_index' (fun ν => ?_) (fun ν k k' => ?_)
  · simp
  · rw [add_smul]

lemma flatten_zero : M.flatten 0 = 0 := by
  unfold flatten
  exact Finsupp.sum_zero_index

lemma flatten_single (ν0 : M^ℕ) : M.flatten (Finsupp.single ν0 1) = ν0 := by
  unfold flatten
  rw [Finsupp.sum_single_index (by simp), one_smul]

lemma flatten_surjective : Function.Surjective (M.flatten) :=
  fun ν0 => ⟨Finsupp.single ν0 1, flatten_single M ν0⟩

lemma reindex_LargeIdeal_pow (μ : (M^ℕ) →₀ ℕ) :
    (M.reindex).LargeIdeal^μ = M.LargeIdeal^(M.flatten μ) := by
  show μ.prod (fun ν k => ((M.reindex).LargeIdeal ν)^k) = _
  simp_rw [reindex_LargeIdeal]
  exact family_pow_flatten M.LargeIdeal μ

lemma reindex_elem_pow (μ : (M^ℕ) →₀ ℕ) :
    (M.reindex).elem^μ = M.elem^(M.flatten μ) :=
  family_pow_flatten M.elem μ

structure PreDil where
  pow : M^ℕ
  num : A'
  num_mem : num ∈ M.LargeIdeal ^pow

def r : M.PreDil → M.PreDil → Prop := fun x y =>
  ∃ β : M^ℕ, x.num * M.elem^(β + y.pow) = y.num * M.elem^(β + x.pow)

variable {M}

lemma r_refl (x : M.PreDil) : M.r x x := by simp[r]

lemma r_symm (x y : M.PreDil) : M.r x y → M.r y x := by
  intro h
  rcases h with ⟨β , hβ⟩
  use β
  rw[hβ.symm]

lemma r_trans (x y z : M.PreDil) : M.r x y → M.r y z → M.r x z := by
  intro h g
  rcases h with ⟨β , hβ⟩
  rcases g with ⟨γ , gγ⟩
  have eq' := congr($hβ * M.elem^(γ+z.pow))
  have eq'' := congr($gγ * M.elem^(β+x.pow))
  use β+γ+y.pow

  rw [show β + γ + y.pow + z.pow = (β + y.pow) + (γ + z.pow) by abel,
    familyPow_add, ← mul_assoc, hβ, mul_assoc, mul_comm (M.elem^(_ : M^ℕ)), ← mul_assoc, gγ,
    mul_assoc, ← familyPow_add]
  congr 2
  abel

def setoid : Setoid (M.PreDil) where
  r := M.r
  iseqv :=
  { refl := r_refl
    symm {x y} := r_symm x y
    trans {x y z} := r_trans x y z }

variable (M) in
def Dilatation := _root_.Quotient M.setoid

scoped notation:max ring"["multicenter"]" => Dilatation (A' := ring) multicenter
namespace Dilatation

def mk (x : M.PreDil) : A'[M] := _root_.Quotient.mk _ x

lemma mk_eq_mk (x y : M.PreDil) : mk x = mk y ↔ M.r x y := by
  erw [_root_.Quotient.eq]
  rfl

@[elab_as_elim]
lemma induction_on {P : A'[M] → Prop} (x : A'[M]) (h : ∀ x : M.PreDil, P (mk x)) : P x := by
  induction x using _root_.Quotient.inductionOn with | h a =>
  exact h a

def descFun {B' : Type*} (f : M.PreDil → B') (hf : ∀ x y, M.r x y → f x = f y) : A'[M] → B' :=
  _root_.Quotient.lift f hf

def descFun₂ {B' : Type*} (f : M.PreDil → M.PreDil → B')
    (hf : ∀ a b x y, M.r a b → M.r x y → f a x = f b y) :
    A'[M] → A'[M] → B' :=
  _root_.Quotient.lift₂ f <| fun a x b y ↦ hf a b x y

@[simp]
lemma descFun_mk {B' : Type*} (f : M.PreDil → B') (hf : ∀ x y, M.r x y → f x = f y)
    (x : M.PreDil) :
    descFun f hf (mk x) = f x := rfl

@[simp]
lemma descFun₂_mk_mk {B' : Type*} (f : M.PreDil → M.PreDil → B')
    (hf : ∀ a b x y, M.r a b → M.r x y → f a x = f b y) (x y : M.PreDil) :
    descFun₂ f hf (mk x) (mk y) = f x y := rfl

@[simps]
def add' (x y : M.PreDil) : M.PreDil where
 pow := x.pow + y.pow
 num := M.elem ^ y.pow * x.num + M.elem ^ x.pow * y.num
 num_mem := Ideal.add_mem _
  (by
    rw [add_comm, familyPow_add]
    exact Ideal.mul_mem_mul (Ideal.mem_familyPow_of_mem fun i _ ↦ elem_mem_LargeIdeal M i)
      x.num_mem)
  (by
    rw [familyPow_add]
    exact Ideal.mul_mem_mul (Ideal.mem_familyPow_of_mem fun i _ ↦ elem_mem_LargeIdeal M i)
      y.num_mem)

instance : Add A'[M] where
  add := descFun₂ (fun x y ↦ mk (add' x y))  <| by
   rintro x y x' y' ⟨α, hα⟩ ⟨β, hβ⟩
   have eq := congr($hβ * M.elem^(x.pow + y.pow + α))
   have eq' := congr($hα * M.elem^(x'.pow + y'.pow + β))
   have eq'' := congr($eq + $eq')

   rw [mk_eq_mk]
   use α + β
   simp only [mul_assoc, ← familyPow_add] at eq''
   simp only [add'_num, add'_pow, add_mul]
   rw [mul_comm _ x.num, mul_comm _ x'.num, mul_assoc, ← familyPow_add,
    mul_assoc, ← familyPow_add]
   rw [mul_comm _ y.num, mul_comm _ y'.num, mul_assoc, ← familyPow_add,
    mul_assoc, ← familyPow_add]
   convert eq'' using 1 <;>
   · rw [add_comm]
     congr 3 <;> abel

lemma mk_add_mk (x y : M.PreDil) : mk x + mk y = mk (add' x y) := rfl

@[simps]
def mul' (x y : M.PreDil) : M.PreDil where
  pow := x.pow + y.pow
  num := x.num * y.num
  num_mem := Ideal.mem_familyPow_add x.num_mem y.num_mem

lemma dist' (x y z : M.PreDil) : M.r (mul' x (add' y z))
                                (add' (mul' x y) (mul' x z))  := by
  use 0
  simp [familyPow_add]
  ring

instance : Mul A'[M] where
  mul := descFun₂ (fun x y ↦ mk <| mul' x y) <| by
    rintro a b x y ⟨α, hα⟩ ⟨β, hβ⟩
    rw [mk_eq_mk]
    use α + β
    simp only [mul'_num, mul'_pow]
    rw [show α + β + (b.pow + y.pow) = (α + b.pow) + (β + y.pow) by abel, familyPow_add,
      show a.num * x.num * (M.elem^(α + b.pow) * M.elem^(β + y.pow)) =
        (a.num * M.elem^(α + b.pow)) * (x.num * M.elem^(β + y.pow)) by ring, hα, hβ,
      show b.num * M.elem^(α + a.pow) * (y.num * M.elem^(β + x.pow)) =
        b.num * y.num * (M.elem^(α + a.pow) * M.elem^(β + x.pow)) by ring, ← familyPow_add]
    congr 2
    abel

lemma mk_mul_mk (x y : M.PreDil) : mk x * mk y = mk (mul' x y) := rfl

instance : Zero A'[M] where
  zero := mk {
    pow := 0
    num := 0
    num_mem := by exact Submodule.zero_mem (M.prodLargeIdealPower 0)
  }

lemma zero_def :  (0 :A'[M]) =  (mk {
    pow := 0
    num := 0
    num_mem := by simp only [Finsupp.prod_zero_index, Ideal.one_eq_top, Submodule.zero_mem]
  } :A'[M]):= rfl

instance : One A'[M] where
  one := mk {
    pow := 0
    num := 1
    num_mem := by exact Submodule.one_le.mp fun ⦃x⦄ a ↦ a
  }

lemma one_def :  (1 :A'[M]) =  (mk {
  pow := 0
  num := 1
  num_mem := by simp
} :A'[M]):= rfl

instance : AddCommMonoid A'[M] where
  add_assoc := by
   intro a b c
   induction a using induction_on with |h x =>
   induction b using induction_on with |h y =>
   induction c using induction_on with |h z =>
    simp only [mk_add_mk, mk_eq_mk]
    use 0
    simp only [add'_num, add'_pow, familyPow_add, zero_add]
    ring
  zero_add := by
   intro a
   induction a using induction_on with |h x=>
    simp only [zero_def, mk_add_mk, mk_eq_mk]
    use 0
    simp [familyPow_add]
  add_zero := by
   intro a
   induction a using induction_on with |h x=>
    simp only [zero_def, mk_add_mk, mk_eq_mk]
    use 0
    simp [familyPow_add]
  add_comm := by
   intro a b
   induction a using induction_on with |h x =>
   induction b using induction_on with |h y =>
    simp only [mk_add_mk, mk_eq_mk]
    use 0
    simp [familyPow_add]
    ring
  nsmul := nsmulRec

instance monoid : Monoid A'[M] where
  mul_assoc := by
   intro a b c
   induction a using induction_on with |h x =>
   induction b using induction_on with |h y =>
   induction c using induction_on with |h z =>
    simp only [mk_mul_mk, mk_eq_mk]
    use 0
    simp only [mul'_num, mul'_pow, zero_add, familyPow_add]
    ring
  one_mul := by
   intro a
   induction a using induction_on with |h x =>
    simp only [one_def, mk_mul_mk, mk_eq_mk]
    use 0
    simp [familyPow_add]
  mul_one := by
   intro a
   induction a using induction_on with |h x =>
    simp only [one_def, mk_mul_mk, mk_eq_mk]
    use 0
    simp [familyPow_add]

instance instCommSemiring : CommSemiring A'[M] where
  __ := monoid
  left_distrib := by
   rintro a b c
   induction a using induction_on with |h x =>
   induction b using induction_on with |h y =>
   induction c using induction_on with |h z =>
    simp only [mk_add_mk, mk_mul_mk, mk_eq_mk]
    use 0
    simp only [mul'_num, add'_num, add'_pow, mul'_pow, zero_add, familyPow_add]
    ring
  right_distrib := by
   rintro a b c
   induction a using induction_on with |h x =>
   induction b using induction_on with |h y =>
   induction c using induction_on with |h z =>
    simp only [mk_add_mk, mk_mul_mk, mk_eq_mk]
    use 0
    simp only [mul'_num, add'_num, add'_pow, mul'_pow, zero_add, familyPow_add]
    ring
  zero_mul := by
   rintro a
   induction a using induction_on with |h x =>
    simp only [zero_def, mk_mul_mk, mk_eq_mk]
    use 0
    simp [familyPow_add]
  mul_zero := by
   rintro a
   induction a using induction_on with |h x =>
    simp only [zero_def, mk_mul_mk, mk_eq_mk]
    use 0
    simp [familyPow_add]

  mul_comm := by
   intro a b
   induction a using induction_on with |h x =>
   induction b using induction_on with |h y =>
    simp only [mk_mul_mk, mk_eq_mk]
    use 0
    simp only [mul'_num, mul'_pow, zero_add, familyPow_add]
    ring

variable (M) in
@[simps]
def fromBaseRing : A' →+* A'[M] where
  toFun x := .mk
        { pow := 0
          num := x
          num_mem := by simp }
  map_one' := by simp [one_def]
  map_mul' _ _ := by simp only [mk_mul_mk, mk_eq_mk]; use 0; simp
  map_zero' := by simp [zero_def]
  map_add' _ _ := by simp [mk_add_mk, mk_eq_mk]; use 0; simp

instance : Algebra A' A'[M] := RingHom.toAlgebra (fromBaseRing M)

lemma algebraMap_eq : (algebraMap A' A'[M]) = fromBaseRing M := rfl

lemma algebraMap_apply (x : A') : algebraMap A' A'[M] x = mk {
  pow := 0
  num := x
  num_mem := by simp
} := rfl

lemma smul_mk (x : A') (y : M.PreDil) : x • mk y = mk {
    pow := y.pow
    num := x * y.num
    num_mem := Ideal.mul_mem_left _ _ y.num_mem } := by
  simp only [Algebra.smul_def, algebraMap_apply, mk_mul_mk, mk_eq_mk]
  use 0
  simp

abbrev frac (ν : M^ℕ)  (m: M.LargeIdeal^ν) : A'[M]:=
  mk {
    pow := ν
    num := m
    num_mem := by simp
    }

scoped notation:max m"/.[" M"]"ν => frac (M := M) ν m

scoped notation:max m"/."ν => frac ν m

lemma frac_add_frac (v w : M^ℕ) (m : M.LargeIdeal^v) (n : M.LargeIdeal^w) :
    (m/.v) + (n/.w) =
    (⟨(m : A') * M.elem^w + (n : A') * M.elem^v, Ideal.add_mem _
      (Ideal.mem_familyPow_add m.2 (Ideal.mem_familyPow_of_mem fun i _ ↦ elem_mem_LargeIdeal M i))
      (add_comm v w ▸
        Ideal.mem_familyPow_add n.2 (Ideal.mem_familyPow_of_mem fun i _ ↦ elem_mem_LargeIdeal M i))⟩) /. (v + w) := by
  simp only [frac, mk_add_mk, mk_eq_mk]
  use 0
  simp only [add'_num, zero_add, familyPow_add, add'_pow]
  ring


lemma frac_mul_frac (v w : M^ℕ) (m : M.LargeIdeal^v) (n : M.LargeIdeal^w) :
    (m/.v) * (n/.w) =
    (⟨m * n, Ideal.mem_familyPow_add m.2 n.2⟩)/.(v + w) := by
  simp only [frac, mk_mul_mk, mk_eq_mk]
  use 0
  simp

lemma smul_frac (a : A') (v : M^ℕ) (m : M.LargeIdeal^v) : a • (m/.v) = (a • m)/.v := by
  simp only [frac, smul_mk, mk_eq_mk]
  use 0
  simp

lemma nonzerodiv_image (v :M^ℕ) :
   algebraMap A' A'[M] (M.elem^v) ∈ nonZeroDivisors A'[M] := by
    have key : ∀ x : A'[M], x * algebraMap A' A'[M] (M.elem^v) = 0 → x = 0 := by
      intro x h
      induction x using induction_on with |h x =>
      simp only [algebraMap_apply, mk_mul_mk, zero_def, mk_eq_mk] at h
      rcases h with ⟨ α, hα ⟩
      simp only [mul'_num, add_zero, mul'_pow, zero_mul] at hα
      simp only [zero_def, mk_eq_mk]
      use v + α
      simp [familyPow_add, ← mul_assoc, hα]
    rw [mem_nonZeroDivisors_iff]
    exact ⟨fun x hx => key x (by rw [mul_comm]; exact hx), key⟩

lemma image_elem_LargeIdeal_equal  (v : M^ℕ) :
 Ideal.span ({algebraMap A' A'[M] (M.elem^v)}) =
    Ideal.map (algebraMap A' A'[M]) (M.LargeIdeal^v):= by
    refine le_antisymm ?_  ?_
    · rw [Ideal.span_le]
      simp only [Set.singleton_subset_iff, SetLike.mem_coe]
      apply Ideal.mem_map_of_mem
      apply Ideal.mem_familyPow_of_mem
      intros
      exact elem_mem_LargeIdeal M _
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have eq: algebraMap A' A'[M] x =
       algebraMap A' A'[M] (M.elem^v) * ⟨ x , hx⟩  /.v := by
       simp  [algebraMap_apply, frac, mk_mul_mk, mk_eq_mk]
       use 0
       simp [mul_comm]
      simp only [Ideal.mem_comap]
      rw [eq]
      apply Ideal.mul_mem_right
      apply Ideal.subset_span
      simp only [Set.mem_singleton_iff]

/-! ##### Reindexing invariance: `A'[M.reindex] ≃+* A'[M]`

A purely ring-theoretic fact, independent of the comparison with categories: dilating by the
`ν`-indexed reindexing of `M` (`Multicenter.reindex`) gives back the same ring as dilating by `M`
directly. The forward map sends a `ν`-indexed generator `⟨μ,m,hm⟩` to `⟨flatten μ, m,_⟩`; the
backward map sends `⟨ν,m,hm⟩` to the singleton-profile generator `⟨single ν 1, m,_⟩`. -/

/-- The forward direction on representatives: `⟨μ,m,hm⟩ ↦ ⟨flatten μ, m, _⟩`. -/
noncomputable def toPreDil (x : (M.reindex).PreDil) : M.PreDil where
  pow := M.flatten x.pow
  num := x.num
  num_mem := reindex_LargeIdeal_pow M x.pow ▸ x.num_mem

lemma toPreDil_respects {x y : (M.reindex).PreDil} (h : (M.reindex).r x y) :
    M.r (toPreDil x) (toPreDil y) := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨M.flatten β, ?_⟩
  show x.num * M.elem^(M.flatten β + M.flatten y.pow) =
    y.num * M.elem^(M.flatten β + M.flatten x.pow)
  rw [← flatten_add, ← flatten_add, ← reindex_elem_pow, ← reindex_elem_pow]
  exact hβ

noncomputable def toDilatation : A'[M.reindex] → A'[M] :=
  descFun (M := M.reindex) (fun x => mk (toPreDil x))
    (fun x y hxy => (mk_eq_mk _ _).mpr (toPreDil_respects hxy))

/-- The backward direction on representatives: `⟨ν,m,hm⟩ ↦ ⟨single ν 1, m, _⟩`. -/
noncomputable def toPreDil' (x : M.PreDil) : (M.reindex).PreDil where
  pow := Finsupp.single x.pow 1
  num := x.num
  num_mem := by
    rw [reindex_LargeIdeal_pow, flatten_single]
    exact x.num_mem

lemma toPreDil'_respects {x y : M.PreDil} (h : M.r x y) :
    (M.reindex).r (toPreDil' x) (toPreDil' y) := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨Finsupp.single β 1, ?_⟩
  show x.num * (M.reindex).elem^(Finsupp.single β 1 + Finsupp.single y.pow 1) =
    y.num * (M.reindex).elem^(Finsupp.single β 1 + Finsupp.single x.pow 1)
  rw [reindex_elem_pow, reindex_elem_pow]
  simp only [flatten_add, flatten_single]
  exact hβ

noncomputable def toDilatation' : A'[M] → A'[M.reindex] :=
  descFun (M := M) (fun x => mk (toPreDil' x))
    (fun x y hxy => (mk_eq_mk _ _).mpr (toPreDil'_respects hxy))

lemma toPreDil_toPreDil' (x : M.PreDil) : toPreDil (toPreDil' x) = x := by
  unfold toPreDil toPreDil'
  simp only [flatten_single]

lemma toPreDil'_toPreDil (y : (M.reindex).PreDil) :
    (M.reindex).r (toPreDil' (toPreDil y)) y := by
  refine ⟨0, ?_⟩
  show y.num * (M.reindex).elem^(0 + y.pow) =
    y.num * (M.reindex).elem^(0 + Finsupp.single (M.flatten y.pow) 1)
  rw [zero_add, zero_add, reindex_elem_pow, reindex_elem_pow, flatten_single]

lemma toDilatation_toDilatation' (x : A'[M]) :
    toDilatation (toDilatation' x) = x := by
  induction x using induction_on with
  | h x => show mk (toPreDil (toPreDil' x)) = mk x; rw [toPreDil_toPreDil']

lemma toDilatation'_toDilatation (y : A'[M.reindex]) :
    toDilatation' (toDilatation y) = y := by
  induction y using induction_on with
  | h y =>
    show mk (toPreDil' (toPreDil y)) = mk y
    exact (mk_eq_mk _ _).mpr (toPreDil'_toPreDil y)

lemma toPreDil_add' (x y : (M.reindex).PreDil) :
    toPreDil (add' x y) = add' (toPreDil x) (toPreDil y) := by
  refine PreDil.mk.injEq .. |>.mpr ⟨?_, ?_⟩
  · exact flatten_add M x.pow y.pow
  · show (M.reindex).elem^y.pow * x.num + (M.reindex).elem^x.pow * y.num =
      M.elem^(M.flatten y.pow) * x.num + M.elem^(M.flatten x.pow) * y.num
    rw [reindex_elem_pow, reindex_elem_pow]

lemma toPreDil_mul' (x y : (M.reindex).PreDil) :
    toPreDil (mul' x y) = mul' (toPreDil x) (toPreDil y) := by
  refine PreDil.mk.injEq .. |>.mpr ⟨?_, ?_⟩
  · exact flatten_add M x.pow y.pow
  · rfl

lemma toDilatation_zero : toDilatation (0 : A'[M.reindex]) = 0 := by
  show mk (toPreDil _) = _
  congr 1

lemma toDilatation_one : toDilatation (1 : A'[M.reindex]) = 1 := by
  show mk (toPreDil _) = _
  congr 1

lemma toDilatation_add (x y : A'[M.reindex]) :
    toDilatation (x + y) = toDilatation x + toDilatation y := by
  induction x using induction_on with
  | h x =>
    induction y using induction_on with
    | h y =>
      show mk (toPreDil (add' x y)) = mk (toPreDil x) + mk (toPreDil y)
      rw [mk_add_mk, toPreDil_add']

lemma toDilatation_mul (x y : A'[M.reindex]) :
    toDilatation (x * y) = toDilatation x * toDilatation y := by
  induction x using induction_on with
  | h x =>
    induction y using induction_on with
    | h y =>
      show mk (toPreDil (mul' x y)) = mk (toPreDil x) * mk (toPreDil y)
      rw [mk_mul_mk, toPreDil_mul']

/-- **Ring-theoretic reindexing invariance.** Dilating by the `ν`-indexed reindexing of `M`
(`Multicenter.reindex`) gives back the same ring as dilating by `M` directly. -/
noncomputable def reindexRingEquiv : A'[M.reindex] ≃+* A'[M] where
  toFun := toDilatation
  invFun := toDilatation'
  left_inv := toDilatation'_toDilatation
  right_inv := toDilatation_toDilatation'
  map_add' := toDilatation_add
  map_mul' := toDilatation_mul

end Dilatation

end semiring

section ring

namespace Dilatation

variable {A' : Type*} [CommRing A'] {M : Multicenter A'}

@[simps]
def neg' (x : M.PreDil) : M.PreDil where
  pow := x.pow
  num := -x.num
  num_mem := neg_mem x.num_mem

instance : Neg A'[M] where
  neg := descFun (mk ∘ neg') <| by
    rintro x y ⟨α, hα⟩
    simp only [Function.comp_apply, mk_eq_mk]
    use α
    simp [hα]

lemma mk_neg (x : M.PreDil) : -mk x = mk (neg' x) := rfl

instance : CommRing A'[M] where
  __ := instCommSemiring
  zsmul := zsmulRec
  neg_add_cancel := by
    intro a
    induction a using induction_on with |h x =>
    simp only [mk_neg, mk_add_mk, zero_def, mk_eq_mk]
    use 0
    simp

lemma neg_frac (v : M^ℕ) (m : M.LargeIdeal^v) : -(m/.v) = (-m)/.v := by
  simp only [frac, mk_neg, mk_eq_mk]
  use 0
  simp

end Dilatation

end ring

section universal_property

variable {A' B' : Type*} [CommRing A'] [CommRing B'] (M : Multicenter A')

lemma  cond_univ_implies_large_cond [Algebra A' B']
    (gen : ∀ i, Ideal.span {(algebraMap A' B') (M.elem i)} = Ideal.map (algebraMap A' B') (M.LargeIdeal i)):
    (∀ (ν : M^ℕ) , (Ideal.span {(algebraMap A' B') (M.elem^ν)} = Ideal.map (algebraMap A' B') (M.LargeIdeal^ν))) :=by
     classical
     intro v
     simp only [familyPow_def, Finsupp.prod, map_prod, map_pow]
     rw [Ideal.prod_span']
     simp [← Ideal.span_singleton_pow, gen]
     simp [Ideal.prod_map, Ideal.map_pow]

lemma equ_trivial_image_divisor_ring  [Algebra A' B']  :
 ∀ i, Ideal.map (algebraMap A' B') (Ideal.span {M.elem i})=
      Ideal.span {(algebraMap A' B') (M.elem i)} := by
      intro i
      rw [Ideal.map_span, Set.image_singleton]

lemma equiv_small_big_cond [Algebra A' B']  :
( ∀ i, Ideal.map (algebraMap A' B') (Ideal.span {M.elem i}) = Ideal.map (algebraMap A' B') (M.LargeIdeal i)) ↔
( ∀ i, Ideal.map (algebraMap A' B') (Ideal.span {M.elem i}) ≥  Ideal.map (algebraMap A' B') (M.ideal i)) := by
  constructor
  · intro h i
    have eq1 : (M.LargeIdeal i) ≥ (M.ideal i)  := by
      simp [LargeIdeal]
    have eq2 : Ideal.map (algebraMap A' B') (M.LargeIdeal i) ≥
               Ideal.map (algebraMap A' B') (M.ideal i) := by
                simp[Ideal.map_mono, eq1]
    simp[eq2, h]

  · intro h i
    have eq1: Ideal.map (algebraMap A' B') (M.LargeIdeal i)=
               Ideal.map (algebraMap A' B') (M.ideal i)+
               Ideal.map (algebraMap A' B') (Ideal.span {M.elem i}):= by
               simp[LargeIdeal]
               rw [Ideal.map_sup]
    have eq2: Ideal.map (algebraMap A' B') (Ideal.span {M.elem i})
             ≥  Ideal.map (algebraMap A' B') (M.LargeIdeal i) := by
             simp[eq1, h]
    have eq3: Ideal.map (algebraMap A' B') (Ideal.span {M.elem i})
             ≤   Ideal.map (algebraMap A' B') (M.LargeIdeal i) := by
             simp[LargeIdeal, eq1, Ideal.map_sup]
    have eq4: Ideal.map (algebraMap A' B') (Ideal.span {M.elem i})
             = Ideal.map (algebraMap A' B') (M.LargeIdeal i) := by
             exact LE.le.antisymm' eq2 eq3
    exact eq4

lemma  lemma_exists_in_image [Algebra A' B']
    (non_zero_divisor : ∀ i : M.index, (algebraMap A' B') (M.elem i) ∈ nonZeroDivisors B')
    (gen : ∀ i, Ideal.span {(algebraMap A' B') (M.elem i)} = Ideal.map (algebraMap A' B') (M.LargeIdeal i)):
    (∀(ν : M^ℕ) (m : M.LargeIdeal^ν) ,  (∃! bm : B' ,  (algebraMap A' B') (M.elem^ν) *bm=(algebraMap A' B') (m) )):= by
      intro v m
      have mem : (algebraMap A' B') m ∈  (M.LargeIdeal^v).map (algebraMap A' B') := by
          apply Ideal.mem_map_of_mem
          exact m.2
      rw[← cond_univ_implies_large_cond] at mem
      rw[Ideal.mem_span_singleton'] at mem
      rcases mem with ⟨bm, eq_bm⟩
      use bm
      rw[mul_comm] at eq_bm
      use eq_bm
      intro bm' eq
      rw[← eq_bm] at eq
      rw[mul_cancel_left_mem_nonZeroDivisors] at eq
      · exact eq
      · simp only [familyPow_def, Finsupp.prod, map_prod, map_pow]
        apply prod_mem
        intro i hi
        apply pow_mem
        apply non_zero_divisor
      · exact gen

def def_unique_elem [Algebra A' B'] (v : M^ℕ) (m : M.LargeIdeal^v)
    (non_zero_divisor : ∀ i : M.index, (algebraMap A' B') (M.elem i) ∈ nonZeroDivisors B')
    (gen : ∀ i, Ideal.span {(algebraMap A' B') (M.elem i)} = Ideal.map (algebraMap A' B') (M.LargeIdeal i)): B' :=
     (lemma_exists_in_image  M  non_zero_divisor gen v m).choose

lemma def_unique_elem_spec [Algebra A' B'] (v : M^ℕ) (m : M.LargeIdeal^v)
    (non_zero_divisor : ∀ i : M.index, (algebraMap A' B') (M.elem i) ∈ nonZeroDivisors B')
    (gen : ∀ i, Ideal.span {(algebraMap A' B') (M.elem i)} = Ideal.map (algebraMap A' B') (M.LargeIdeal i)):
    (algebraMap A' B') (M.elem^v) * def_unique_elem M v m non_zero_divisor gen = (algebraMap A' B') m := by
    apply (lemma_exists_in_image M non_zero_divisor gen v m).choose_spec.1

lemma def_unique_elem_unique  [Algebra A' B'] (v : M^ℕ) (m : M.LargeIdeal^v)
    (non_zero_divisor : ∀ i : M.index, (algebraMap A' B') (M.elem i) ∈ nonZeroDivisors B')
    (gen : ∀ i, Ideal.span {(algebraMap A' B') (M.elem i)} = Ideal.map (algebraMap A' B') (M.LargeIdeal i)):
    ∀ bm : B', (algebraMap A' B') (M.elem^v) * bm = (algebraMap A' B') m →  def_unique_elem M v m non_zero_divisor gen =bm:= by
    intro bm hbm
    apply ((lemma_exists_in_image M  non_zero_divisor gen v m).choose_spec.2 bm hbm).symm

def desc [Algebra A' B']
    (non_zero_divisor : ∀ i : M.index, (algebraMap A' B') (M.elem i) ∈ nonZeroDivisors B')
    (gen : ∀ i, Ideal.span {(algebraMap A' B') (M.elem i)} = Ideal.map (algebraMap A' B') (M.LargeIdeal i)) :
     A'[M] →ₐ[A'] B' where
  toFun := Dilatation.descFun (fun x ↦ def_unique_elem M  x.pow ⟨ x.num, x.num_mem⟩  non_zero_divisor gen )
                            ( by
                              intro x y h
                              rcases h with ⟨β, hβ⟩

                              apply def_unique_elem_unique
                              apply_fun (fun z => (algebraMap A' B') (M.elem^ (β + y.pow)) * z)
                              · simp only [mul_assoc, hβ]
                                rw[← map_mul, mul_comm _ x.num]
                                rw [hβ]
                                simp only [map_mul]
                                rw[← def_unique_elem_spec M y.pow ⟨y.num, y.num_mem⟩ non_zero_divisor gen]
                                simp only [familyPow_add, map_mul]
                                ring
                              · intro x y hx
                                simp only at hx
                                rwa [mul_cancel_left_mem_nonZeroDivisors] at hx
                                simp only [familyPow_def, Finsupp.prod, Finsupp.coe_add,
                                  Pi.add_apply, map_prod, map_pow]
                                apply prod_mem
                                intro i hi
                                apply pow_mem
                                apply non_zero_divisor)
  map_one' := by
    simp only [Dilatation.descFun, Dilatation.one_def]
    apply def_unique_elem_unique
    simp
  map_mul' := by
    intro x y
    induction x using Dilatation.induction_on with |h x =>
    induction y using Dilatation.induction_on with |h y =>
    simp only [Dilatation.descFun₂_mk_mk, Dilatation.mk_mul_mk]
    apply def_unique_elem_unique
    · exact non_zero_divisor
    · exact gen
    · simp only [Dilatation.mul'_pow, Dilatation.descFun_mk, Dilatation.mul'_num, map_mul]
      rw [familyPow_add]
      rw[← def_unique_elem_spec M  y.pow ⟨y.num, y.num_mem⟩ non_zero_divisor gen]
      rw[← def_unique_elem_spec M x.pow ⟨x.num, x.num_mem⟩ non_zero_divisor gen]
      simp only [map_mul]
      ring
  map_zero' := by
    simp only [Dilatation.descFun, Dilatation.one_def]
    apply def_unique_elem_unique
    simp
  map_add' :=  by
    intro x y
    induction x using Dilatation.induction_on with |h x =>
    induction y using Dilatation.induction_on with |h y =>
    simp only [Dilatation.descFun₂_mk_mk, Dilatation.mk_add_mk]
    apply def_unique_elem_unique
    · exact non_zero_divisor
    · exact gen
    · simp only [Dilatation.add'_pow, Dilatation.descFun_mk, Dilatation.add'_num, map_add, map_mul]
      rw [familyPow_add]
      rw[← def_unique_elem_spec M  y.pow ⟨y.num, y.num_mem⟩ non_zero_divisor gen]
      rw[← def_unique_elem_spec M x.pow ⟨x.num, x.num_mem⟩ non_zero_divisor gen]
      simp only [map_mul]
      ring
  commutes' := by
    intro x
    simp only [Dilatation.descFun, Dilatation.one_def]
    apply def_unique_elem_unique
    simp

open Multicenter
open Dilatation
lemma dsc_spec [Algebra A' B'] (v : M^ℕ) (m : M.LargeIdeal^v)
    (non_zero_divisor : ∀ i : M.index, (algebraMap A' B') (M.elem i) ∈ nonZeroDivisors B')
    (gen : ∀ i, Ideal.span {(algebraMap A' B') (M.elem i)} = Ideal.map (algebraMap A' B') (M.LargeIdeal i)):
    (algebraMap A' B') (M.elem^v) * desc M non_zero_divisor gen (m/.v)  = (algebraMap A' B') m := by
    apply (lemma_exists_in_image M non_zero_divisor gen v m).choose_spec.1

lemma  lemma_exists_unique_morphism [Algebra A' B']
    (non_zero_divisor : ∀ i : M.index, (algebraMap A' B') (M.elem i) ∈ nonZeroDivisors B')
    (gen : ∀ i, Ideal.span {(algebraMap A' B') (M.elem i)} = Ideal.map (algebraMap A' B') (M.LargeIdeal i))
    (χ':A'[M]→ₐ[A'] B')  : χ' = desc M non_zero_divisor gen := by
      ext x
      induction x using induction_on with |h x =>
      have eq1 : ((algebraMap A' B') (M.elem^x.pow)) *(χ' ⟨x.num, x.num_mem⟩/.x.pow) =
       (χ' (algebraMap A' A'[M] (M.elem^x.pow))) *(χ' ⟨x.num, x.num_mem⟩/.x.pow) := by rw[AlgHom.commutes]
      have eq2 : ((algebraMap A' B') (M.elem^x.pow)) *(χ' ⟨x.num, x.num_mem⟩/.x.pow) =
       ((algebraMap A' B') x.num) := by
         rw[eq1, ← map_mul]
         simp only [algebraMap_apply, mk_mul_mk, mul']
         rw[← AlgHom.commutes (χ' : A'[M] →ₐ[A'] B')]
         congr 1
         simp[algebraMap_apply]
         simp[mk_eq_mk]
         use 0
         simp
         simp[mul_comm]
      have eq3:  def_unique_elem M  x.pow ⟨x.num, x.num_mem⟩ non_zero_divisor gen =
         (χ' ⟨x.num, x.num_mem⟩/.x.pow) := by
          apply def_unique_elem_unique
          exact eq2
      rw[← eq3]
      rfl

open Dilatation
open Multicenter
lemma reciprocal_for_univ [Algebra A' B'] (M : Multicenter A')
   (χ':A'[M] →ₐ[A'] B') : ∀ i, Ideal.span {(algebraMap A' B') (M.elem i)}
         = Ideal.map (algebraMap A' B') (M.LargeIdeal i):= by
          intro i
          let v : M^ℕ := Finsupp.single i 1
          have eq1:  Ideal.span {(algebraMap A' A'[M]) (M.elem^v)}
             = Ideal.map (algebraMap A' A'[M]) (M.LargeIdeal^v):= by
             rw [image_elem_LargeIdeal_equal v]
          have eq2: M.elem^v = M.elem i := by
            simp [familyPow_def, v]
          have eq3 : M.LargeIdeal^v = M.LargeIdeal i := by
            simp [familyPow_def, v]
          have eq4: Ideal.span {(algebraMap A' A'[M]) (M.elem i)}
             = Ideal.map (algebraMap A' A'[M]) (M.LargeIdeal i):= by
                   have eq41: Ideal.span {(algebraMap A' A'[M]) (M.elem i)}=
                      Ideal.span {(algebraMap A' A'[M]) (M.elem^v)} := by
                      rw[eq2]
                   have eq42: Ideal.map (algebraMap A' A'[M]) (M.LargeIdeal i)=
                      Ideal.map (algebraMap A' A'[M]) (M.LargeIdeal^v) := by
                      rw[eq3]
                   rw[eq41, eq42, eq1]
          have eqA:  Ideal.map (algebraMap A' B') (Ideal.span {M.elem i})
           = Ideal.map (algebraMap A' B') (M.LargeIdeal i) := by
               have eq6: Ideal.map (algebraMap A' A'[M]) (Ideal.span {(M.elem i)})
                       = Ideal.span {(algebraMap A' A'[M]) (M.elem i)} := by
                  rw [equ_trivial_image_divisor_ring  ]
               have eq7: Ideal.map (algebraMap A' A'[M]) (Ideal.span {(M.elem i)})
                        =Ideal.map (algebraMap A' A'[M]) (M.LargeIdeal i) := by
                        rw[ eq6, ← eq4]
               have eq8: Ideal.map (χ'.toRingHom)
                          (Ideal.map (algebraMap A' A'[M]) (Ideal.span {(M.elem i)}))
                        =Ideal.map (χ'.toRingHom )
                          (Ideal.map (algebraMap A' A'[M]) (M.LargeIdeal i)) := by
                          rw[eq7]
               have eqcomp: (algebraMap A' B') = (RingHom.comp χ'.toRingHom (algebraMap A' A'[M])) := by
                  simp
               have eq9: Ideal.map (algebraMap A' B') (Ideal.span {M.elem i})
                        =Ideal.map (algebraMap A' B') (M.LargeIdeal i) := by
                        rw [Ideal.map_map (algebraMap A' A'[M]) χ'.toRingHom] at eq8
                        rw [Ideal.map_map (algebraMap A' A'[M]) χ'.toRingHom] at eq8
                        simp[Function.comp_apply, Function.comp_apply] at eq8
                        exact eq8
               exact eq9

          have eqB: Ideal.map (algebraMap A' B') (Ideal.span {M.elem i})=
            Ideal.span {(algebraMap A' B') (M.elem i)}:= by
                rw [equ_trivial_image_divisor_ring  ]

          rw[←eqB, eqA]

end universal_property

end Multicenter

/-! #### Proposition 5.1: identifying the categorical and ring-theoretic dilatations

`C := SingleObj A'` is "the category attached to `A'`" from §5.0.2: a single object `•`, with
`Hom(•,•) = A'` and composition = multiplication (`CategoryTheory.SingleObj`, already used above
for Fact 5.2). A `Multicenter A'` (`{[Mᵢ,aᵢ]}ᵢ∈I`) corresponds exactly to a `Center (SingleObj A')`:
`aᵢ` becomes the morphism `M.elem i : star ⟶ star`, and `Mᵢ` — an ideal, hence automatically
closed under multiplication by *arbitrary* ring elements — becomes a sieve (`Sieve.ofIdeal`
below), matching the paper's own identification `ObC = {•}` (§5.0.2). -/

namespace Prop51

open CategoryTheory Multicenter Multicenter.Dilatation

variable {A' : Type u} [CommRing A']

/-- An ideal of `A'`, regarded as a sieve over the unique object of `SingleObj A'`: ideals absorb
multiplication by arbitrary ring elements, which is exactly a sieve's stability under
precomposition, since composition in `SingleObj A'` *is* ring multiplication. -/
def Sieve.ofIdeal (I : Ideal A') : Sieve (CategoryTheory.SingleObj.star A') where
  arrows {_} f := (f : A') ∈ I
  downward_closed {_ _ f} hf g := by
    show (f * g : A') ∈ I
    exact I.mul_mem_right g hf

/-- A `Multicenter A'` as a `Center (SingleObj A')`, indexed by exponent profiles `ν : M^ℕ`: the
generator at `ν` divides by `aᵢ^ν := M.elem^ν` with numerator ranging over `M.LargeIdeal^ν`,
matching `Dilatation.frac` exactly (needed for `Phi51` to be surjective — a single-index
generator only reaches products, not sums, of `LargeIdeal` elements). -/
def centerOfMulticenter (M : Multicenter A') :
    Center (CategoryTheory.SingleObj A') where
  I := M^ℕ
  nonempty := ⟨0⟩
  dom _ := CategoryTheory.SingleObj.star A'
  cod _ := CategoryTheory.SingleObj.star A'
  mor ν := M.elem^ν
  N ν := Sieve.ofIdeal (M.LargeIdeal^ν)

variable (M : Multicenter A')

/-- The functor `SingleObj A' ⥤ SingleObj A'[M]` induced by the canonical ring map `A' → A'[M]`
(`CategoryTheory.SingleObj.mapHom` turns any monoid hom into a functor between the attached
one-object categories). This plays the role of `Θ` on the "attached-to-a-ring" side. -/
def toDilatationFunctor : CategoryTheory.SingleObj A' ⥤ CategoryTheory.SingleObj A'[M] :=
  CategoryTheory.SingleObj.mapHom A' A'[M] (algebraMap A' A'[M]).toMonoidHom

/-- **General fact**: in the one-object category `SingleObj R` attached to a monoid `R`, a
morphism is an isomorphism iff it is a unit of `R` — composition unwinds to multiplication
(`SingleObj.comp_as_mul`), so a two-sided categorical inverse is exactly a two-sided
multiplicative inverse. -/
lemma isIso_iff_isUnit {R : Type*} [Monoid R]
    (x : CategoryTheory.SingleObj.star R ⟶ CategoryTheory.SingleObj.star R) :
    CategoryTheory.IsIso x ↔ IsUnit x := by
  constructor
  · intro h
    haveI := h
    refine ⟨⟨x, CategoryTheory.inv x, ?_, ?_⟩, rfl⟩
    · show x * CategoryTheory.inv x = (1 : R)
      have := CategoryTheory.IsIso.inv_hom_id x
      rwa [CategoryTheory.SingleObj.comp_as_mul, CategoryTheory.SingleObj.id_as_one] at this
    · show CategoryTheory.inv x * x = (1 : R)
      have := CategoryTheory.IsIso.hom_inv_id x
      rwa [CategoryTheory.SingleObj.comp_as_mul, CategoryTheory.SingleObj.id_as_one] at this
  · rintro ⟨u, rfl⟩
    refine ⟨⟨(↑u⁻¹ : R), ?_, ?_⟩⟩
    · show (↑u⁻¹ : R) * (↑u : R) = (1 : R)
      exact u.inv_mul
    · show (↑u : R) * (↑u⁻¹ : R) = (1 : R)
      exact u.mul_inv

/-- **General fact**: if `W.IsInvertedBy e` for some *faithful* `e`, then `W.Q` is faithful —
`e` factors as `W.Q ⋙ (lift of e)` (universal property of the localization), and a functor whose
composite with something else is faithful is itself faithful (`faithful_of_comp_faithful_gen`,
applied to the *lift*, not `e` itself: here we need the reverse composition order, so we go via
`e`'s own factorization instead). -/
lemma faithful_Q_of_isInvertedBy_of_faithful {E : Type u} [Category.{v'} E] (W : MorphismProperty E)
    {E' : Type u} [Category.{v'} E'] (e : E ⥤ E') (he : W.IsInvertedBy e) (hefaith : e.Faithful) :
    W.Q.Faithful := by
  apply faithful_of_comp_faithful_gen W.Q (Localization.Construction.lift e he)
  rw [Localization.Construction.fac]
  exact hefaith

/-- The images of `M`'s generators in `A'[M]` are non-zero-divisors — an unconditional structural
fact about dilatations (`Multicenter.Dilatation.nonzerodiv_image`, specialized to a single
generator). -/
lemma nonzerodiv_image_single (i : M.index) :
    algebraMap A' A'[M] (M.elem i) ∈ nonZeroDivisors A'[M] := by
  have h := Multicenter.Dilatation.nonzerodiv_image (M := M) (Finsupp.single i 1)
  simpa [familyPow_def] using h

/-- **Proposition 5.1, universal-property half.** `Dila (centerOfMulticenter M)` is the unique
factorization of `toDilatationFunctor M` through `CatToDila (centerOfMulticenter M)`. -/
theorem prop_5_1 :
    ∃! (Φ : Dila (centerOfMulticenter M) ⥤ CategoryTheory.SingleObj A'[M]),
      CatToDila (centerOfMulticenter M) ⋙ Φ = toDilatationFunctor M := by
  apply Dila_universal_property
  · show (ImageCenterMorphismProperty (centerOfMulticenter M) (toDilatationFunctor M)).Q.Faithful
    set Sgen : Submonoid A'[M] :=
      Submonoid.closure (Set.range (fun i => algebraMap A' A'[M] (M.elem i))) with hSgendef
    have hSgennzd : Sgen ≤ nonZeroDivisors A'[M] := by
      rw [hSgendef, Submonoid.closure_le]
      rintro x ⟨i, rfl⟩
      exact nonzerodiv_image_single M i
    let e0 : CategoryTheory.SingleObj A'[M] ⥤ CategoryTheory.SingleObj (Localization Sgen) :=
      CategoryTheory.SingleObj.mapHom _ _ (algebraMap A'[M] (Localization Sgen)).toMonoidHom
    have he0faith : e0.Faithful := by
      constructor
      intro _ _ f g h
      exact IsLocalization.injective (M := Sgen) (Localization Sgen) hSgennzd h
    have he0inv :
        (ImageCenterMorphismProperty (centerOfMulticenter M)
          (toDilatationFunctor M)).IsInvertedBy e0 := by
      rintro X Y f ⟨ν0, hi⟩
      set ν : M^ℕ := ν0 with hνdef
      have hX : X = (toDilatationFunctor M).obj ((centerOfMulticenter M).dom ν) :=
        congrArg Sigma.fst hi
      have hY : Y = (toDilatationFunctor M).obj ((centerOfMulticenter M).cod ν) :=
        congrArg (fun s => s.2.1) hi
      subst hX
      subst hY
      have hf : f = (toDilatationFunctor M).map ((centerOfMulticenter M).mor ν) := by
        cases hi; rfl
      have hmem : algebraMap A' A'[M] (M.elem^ν) ∈ Sgen := by
        rw [familyPow_def, Finsupp.prod, map_prod]
        refine Submonoid.prod_mem Sgen (fun i _ => ?_)
        rw [map_pow]
        refine Submonoid.pow_mem Sgen ?_ _
        rw [hSgendef]
        exact Submonoid.subset_closure ⟨i, rfl⟩
      rw [hf, isIso_iff_isUnit]
      exact IsLocalization.map_units (Localization Sgen)
        (⟨algebraMap A' A'[M] (M.elem^ν), hmem⟩ : Sgen)
    exact faithful_Q_of_isInvertedBy_of_faithful _ e0 he0inv he0faith
  · intro ν0
    set ν : M^ℕ := ν0 with hνdef
    rintro Y f ⟨Z, g, h, hg, rfl⟩
    obtain rfl : Y = CategoryTheory.SingleObj.star A'[M] := Subsingleton.elim _ _
    obtain rfl : Z = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
    let h' : A'[M] := h
    let d : A'[M] :=
      @CategoryTheory.Functor.map (CategoryTheory.SingleObj A') _ (CategoryTheory.SingleObj A'[M]) _
        (toDilatationFunctor M) (CategoryTheory.SingleObj.star A') (CategoryTheory.SingleObj.star A')
        (M.elem^ν)
    have hd : d = algebraMap A' A'[M] (M.elem^ν) := by
      show (@CategoryTheory.Functor.map (CategoryTheory.SingleObj A') _
        (CategoryTheory.SingleObj A'[M]) _ (toDilatationFunctor M)
        (CategoryTheory.SingleObj.star A') (CategoryTheory.SingleObj.star A') (M.elem^ν)) = _
      simp [toDilatationFunctor, CategoryTheory.SingleObj.mapHom]
    have hgeq : @CategoryTheory.Functor.map (CategoryTheory.SingleObj A') _
        (CategoryTheory.SingleObj A'[M]) _ (toDilatationFunctor M)
        (CategoryTheory.SingleObj.star A') (CategoryTheory.SingleObj.star A') g
        = algebraMap A' A'[M] g := by
      simp [toDilatationFunctor, CategoryTheory.SingleObj.mapHom]
    have hmem : algebraMap A' A'[M] g ∈ Ideal.span {algebraMap A' A'[M] (M.elem^ν)} := by
      rw [Multicenter.Dilatation.image_elem_LargeIdeal_equal (M := M) ν]
      exact Ideal.mem_map_of_mem _ hg
    rw [Ideal.mem_span_singleton'] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨CategoryTheory.SingleObj.star A'[M], c * h', d, Presieve.singleton_self _, ?_⟩
    rw [CategoryTheory.SingleObj.comp_as_mul, CategoryTheory.SingleObj.comp_as_mul, hd, hgeq, ← hc]
    show algebraMap A' A'[M] (M.elem^ν) * (c * h') = c * algebraMap A' A'[M] (M.elem^ν) * h'
    ring

/-- The functor `Φ` from Proposition 5.1 (the functor produced by `prop_5_1`'s existence claim),
matching the paper's own naming (cf. `Alpha315` for the analogous functor in Proposition 3.15). -/
noncomputable def Phi51 : Dila (centerOfMulticenter M) ⥤ CategoryTheory.SingleObj A'[M] :=
  (prop_5_1 M).choose

theorem Phi51_spec :
    CatToDila (centerOfMulticenter M) ⋙ Phi51 M = toDilatationFunctor M :=
  (prop_5_1 M).choose_spec.1

theorem Phi51_unique (G : Dila (centerOfMulticenter M) ⥤ CategoryTheory.SingleObj A'[M])
    (hG : CatToDila (centerOfMulticenter M) ⋙ G = toDilatationFunctor M) :
    G = Phi51 M :=
  (prop_5_1 M).choose_spec.2 G hG

/-! ##### Injectivity of `Φ`

Compare both `Φ` and the (unconditionally faithful) raw-localization comparison `DilaToLoc`
against a common target: the categorical localization `(CenterMorphismProperty
(centerOfMulticenter M)).Localization`, reached from `SingleObj A'[M]` via the *ring-theoretic*
localization of `A'` at `M`'s generators (using the monoid-level universal property of
`Localization`, since the target's endomorphism monoid need not be a ring). -/

/-- `M`'s generators, viewed as a submonoid of `A'` itself (not of `A'[M]`). -/
def genSubmonoid : Submonoid A' :=
  Submonoid.closure (Set.range M.elem)

lemma genSubmonoid_nonZeroDivisors (i : M.index) :
    algebraMap A' (Localization (genSubmonoid M)) (M.elem i) ∈
      nonZeroDivisors (Localization (genSubmonoid M)) :=
  (IsLocalization.map_units (Localization (genSubmonoid M))
    (⟨M.elem i, Submonoid.subset_closure ⟨i, rfl⟩⟩ : genSubmonoid M)).mem_nonZeroDivisors

lemma genSubmonoid_gen (i : M.index) :
    Ideal.span {algebraMap A' (Localization (genSubmonoid M)) (M.elem i)} =
      Ideal.map (algebraMap A' (Localization (genSubmonoid M))) (M.LargeIdeal i) := by
  have hunit : IsUnit (algebraMap A' (Localization (genSubmonoid M)) (M.elem i)) :=
    IsLocalization.map_units (Localization (genSubmonoid M))
      (⟨M.elem i, Submonoid.subset_closure ⟨i, rfl⟩⟩ : genSubmonoid M)
  have hspan_top : Ideal.span {algebraMap A' (Localization (genSubmonoid M)) (M.elem i)} = ⊤ :=
    Ideal.span_singleton_eq_top.mpr hunit
  have hmap_top :
      Ideal.map (algebraMap A' (Localization (genSubmonoid M))) (M.LargeIdeal i) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (M.elem_mem_LargeIdeal i)) hunit
  rw [hspan_top, hmap_top]

/-- The canonical map from `A'[M]` into the *full* localization of `A'` at the generators —
trivial to build via `desc`, since generators become units there. -/
noncomputable def descToLoc : A'[M] →ₐ[A'] Localization (genSubmonoid M) :=
  Multicenter.desc M (genSubmonoid_nonZeroDivisors M) (genSubmonoid_gen M)

/-- `A'`, as a monoid hom into the endomorphism monoid of the raw localization
`(CenterMorphismProperty (centerOfMulticenter M)).Localization`, matching
`LocalizationFunctor (centerOfMulticenter M)`. -/
def toLocEnd : A' →* CategoryTheory.End
    ((LocalizationFunctor (centerOfMulticenter M)).obj (CategoryTheory.SingleObj.star A')) where
  toFun a := (LocalizationFunctor (centerOfMulticenter M)).map
    (a : CategoryTheory.SingleObj.star A' ⟶ CategoryTheory.SingleObj.star A')
  map_one' := by
    change (LocalizationFunctor (centerOfMulticenter M)).map
        (𝟙 (CategoryTheory.SingleObj.star A')) =
      𝟙 ((LocalizationFunctor (centerOfMulticenter M)).obj (CategoryTheory.SingleObj.star A'))
    rw [CategoryTheory.Functor.map_id]
  map_mul' a b := by
    change (LocalizationFunctor (centerOfMulticenter M)).map
        ((a * b : A') : CategoryTheory.SingleObj.star A' ⟶ CategoryTheory.SingleObj.star A') =
      (LocalizationFunctor (centerOfMulticenter M)).map
          (b : CategoryTheory.SingleObj.star A' ⟶ CategoryTheory.SingleObj.star A') ≫
        (LocalizationFunctor (centerOfMulticenter M)).map
          (a : CategoryTheory.SingleObj.star A' ⟶ CategoryTheory.SingleObj.star A')
    rw [← CategoryTheory.SingleObj.comp_as_mul, CategoryTheory.Functor.map_comp]

lemma toLocEnd_inverts_gen : ∀ y : genSubmonoid M, IsUnit (toLocEnd M (y : A')) := by
  rintro ⟨y, hy⟩
  induction hy using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [CategoryTheory.isUnit_iff_isIso]
    show CategoryTheory.IsIso (toLocEnd M (M.elem i))
    exact CategoryTheory.MorphismProperty.Q_inverts (CenterMorphismProperty (centerOfMulticenter M))
      (M.elem i : CategoryTheory.SingleObj.star A' ⟶ CategoryTheory.SingleObj.star A')
      ⟨Finsupp.single i 1, by
        have heq : M.elem i = M.elem^(Finsupp.single i 1) := by simp [familyPow_def]
        exact congrArg
          (fun x => (⟨CategoryTheory.SingleObj.star A', CategoryTheory.SingleObj.star A', x⟩ :
            Σ X Y : CategoryTheory.SingleObj A', X ⟶ Y)) heq⟩
  | one =>
    rw [CategoryTheory.isUnit_iff_isIso]
    show CategoryTheory.IsIso (toLocEnd M (1 : A'))
    rw [map_one, CategoryTheory.End.one_def]
    infer_instance
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy

/-- General fact: if `u` commutes with `v₁` and with `v₂`, it commutes with `v₁ ≫ v₂`. -/
private lemma commutesComp {E : Type*} [CategoryTheory.Category E] {X : E} {u v₁ v₂ : X ⟶ X}
    (h₁ : u ≫ v₁ = v₁ ≫ u) (h₂ : u ≫ v₂ = v₂ ≫ u) : u ≫ (v₁ ≫ v₂) = (v₁ ≫ v₂) ≫ u := by
  rw [← CategoryTheory.Category.assoc, h₁, CategoryTheory.Category.assoc, h₂,
    ← CategoryTheory.Category.assoc]

/-- General fact: if `u` commutes with the `hom` of an iso `α : X ≅ X`, it commutes with
`α.inv` too. Stated for an explicit `Iso` (rather than `[IsIso _]`) so that it applies directly
to `Localization.Construction.wIso`, without worrying about which `IsIso` witness is in scope. -/
private lemma commutesInv {E : Type*} [CategoryTheory.Category E] {X : E} {u : X ⟶ X}
    (α : X ≅ X) (h : u ≫ α.hom = α.hom ≫ u) : u ≫ α.inv = α.inv ≫ u := by
  rw [CategoryTheory.Iso.comp_inv_eq, CategoryTheory.Category.assoc, h,
    ← CategoryTheory.Category.assoc, α.inv_hom_id, CategoryTheory.Category.id_comp]

/-- **Key structural fact**: since `A'` is commutative, every image `toLocEnd M a` is *central*
in the raw localization's endomorphism monoid — it commutes with everything. Proved via
`Localization.Construction.morphismProperty_eq_top`: a `MorphismProperty` stable under
composition, containing every generator-image and every formal inverse, is everything. -/
lemma genImage_central (a : A') :
    ∀ ⦃X Y : (CenterMorphismProperty (centerOfMulticenter M)).Localization⦄ (v : X ⟶ Y),
      (toLocEnd M a) ≫ v = v ≫ (toLocEnd M a) := by
  let P : CategoryTheory.MorphismProperty
      (CenterMorphismProperty (centerOfMulticenter M)).Localization :=
    fun _ _ v => (toLocEnd M a) ≫ v = v ≫ (toLocEnd M a)
  haveI : P.IsStableUnderComposition := ⟨fun _ _ hf hg => commutesComp hf hg⟩
  have hP : P = ⊤ := by
    apply Localization.Construction.morphismProperty_eq_top P
    · intro X Y f
      show toLocEnd M a ≫ toLocEnd M (f : A') = toLocEnd M (f : A') ≫ toLocEnd M a
      rw [← CategoryTheory.End.mul_def, ← CategoryTheory.End.mul_def, ← map_mul, ← map_mul,
        mul_comm]
    · intro X Y w hw
      show toLocEnd M a ≫ (Localization.Construction.wIso w hw).inv =
        (Localization.Construction.wIso w hw).inv ≫ toLocEnd M a
      apply commutesInv (Localization.Construction.wIso w hw)
      show toLocEnd M a ≫ toLocEnd M (w : A') = toLocEnd M (w : A') ≫ toLocEnd M a
      rw [← CategoryTheory.End.mul_def, ← CategoryTheory.End.mul_def, ← map_mul, ← map_mul,
        mul_comm]
  intro X Y v
  simpa only [← hP] using CategoryTheory.MorphismProperty.top_apply v

/-- The single object of the raw localization, viewed as an object of
`(CenterMorphismProperty (centerOfMulticenter M)).Localization`. -/
private noncomputable abbrev ptLoc : (CenterMorphismProperty (centerOfMulticenter M)).Localization :=
  (LocalizationFunctor (centerOfMulticenter M)).obj (CategoryTheory.SingleObj.star A')

/-- Every object of the raw localization is (canonically, but non-computably) equal to `ptLoc`,
since the localization of a single-object category is again single-object. -/
private lemma isoObj_eq_ptLoc :
    ∀ X : (CenterMorphismProperty (centerOfMulticenter M)).Localization, X = ptLoc M := by
  haveI : Subsingleton (CenterMorphismProperty (centerOfMulticenter M)).Localization :=
    Equiv.subsingleton.symm (CategoryTheory.Localization.Construction.objEquiv
      (CenterMorphismProperty (centerOfMulticenter M)))
  intro X
  exact Subsingleton.elim _ _

/-- Cast a morphism between arbitrary objects of the raw localization into an endomorphism of
`ptLoc`, using that the localization has (up to equality) a single object. -/
private noncomputable def castE ⦃X Y : (CenterMorphismProperty (centerOfMulticenter M)).Localization⦄
    (u : X ⟶ Y) : CategoryTheory.End (ptLoc M) :=
  CategoryTheory.eqToHom (isoObj_eq_ptLoc M X).symm ≫ u ≫
    CategoryTheory.eqToHom (isoObj_eq_ptLoc M Y)

private lemma castE_comp ⦃X Y Z : (CenterMorphismProperty (centerOfMulticenter M)).Localization⦄
    (f : X ⟶ Y) (g : Y ⟶ Z) : castE M (f ≫ g) = castE M f ≫ castE M g := by
  show CategoryTheory.eqToHom _ ≫ (f ≫ g) ≫ CategoryTheory.eqToHom _ =
    (CategoryTheory.eqToHom _ ≫ f ≫ CategoryTheory.eqToHom _) ≫
      (CategoryTheory.eqToHom _ ≫ g ≫ CategoryTheory.eqToHom _)
  simp only [CategoryTheory.Category.assoc, eqToHom_trans_assoc, CategoryTheory.eqToHom_refl,
    CategoryTheory.Category.id_comp]

private lemma castE_eq_self (u : CategoryTheory.End (ptLoc M)) : castE M u = u := by
  show CategoryTheory.eqToHom _ ≫ u ≫ CategoryTheory.eqToHom _ = u
  simp only [CategoryTheory.eqToHom_refl, CategoryTheory.Category.id_comp,
    CategoryTheory.Category.comp_id]

/-- **Key structural fact, part 2**: *every* endomorphism of the raw localization is central
(commutes with everything) — same argument as `genImage_central`, one level up: generator-images
are central by `genImage_central`, and formal inverses of central elements are central too. -/
lemma allCentral (v : CategoryTheory.End (ptLoc M)) :
    ∀ ⦃X Y : (CenterMorphismProperty (centerOfMulticenter M)).Localization⦄ (u : X ⟶ Y),
      castE M u ≫ v = v ≫ castE M u := by
  let P : CategoryTheory.MorphismProperty
      (CenterMorphismProperty (centerOfMulticenter M)).Localization :=
    fun _ _ u => castE M u ≫ v = v ≫ castE M u
  have hcomp : ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z), P f → P g → P (f ≫ g) := by
    intro X Y Z f g hf hg
    show castE M (f ≫ g) ≫ v = v ≫ castE M (f ≫ g)
    rw [castE_comp, CategoryTheory.Category.assoc, hg, ← CategoryTheory.Category.assoc, hf,
      CategoryTheory.Category.assoc]
  haveI : P.IsStableUnderComposition := ⟨hcomp⟩
  have hP : P = ⊤ := by
    apply Localization.Construction.morphismProperty_eq_top P
    · intro X Y f
      show castE M ((LocalizationFunctor (centerOfMulticenter M)).map f) ≫ v =
        v ≫ castE M ((LocalizationFunctor (centerOfMulticenter M)).map f)
      obtain rfl : X = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
      obtain rfl : Y = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
      rw [castE_eq_self]
      exact genImage_central M (f : A') v
    · intro X Y w hw
      obtain rfl : X = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
      obtain rfl : Y = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
      show castE M (Localization.Construction.wIso w hw).inv ≫ v =
        v ≫ castE M (Localization.Construction.wIso w hw).inv
      erw [castE_eq_self]
      apply Eq.symm
      apply commutesInv (Localization.Construction.wIso w hw)
      show v ≫ (LocalizationFunctor (centerOfMulticenter M)).map w =
        (LocalizationFunctor (centerOfMulticenter M)).map w ≫ v
      exact (genImage_central M (w : A') v).symm
  intro X Y u
  simpa only [← hP] using CategoryTheory.MorphismProperty.top_apply u

/-- The endomorphism monoid of the raw localization's single object is commutative: this is
what makes `LocEndLift` (a monoid-localization universal-property construction) type-check. -/
noncomputable instance commEnd : CommMonoid (CategoryTheory.End (ptLoc M)) where
  __ := CategoryTheory.End.monoid
  mul_comm u v := by
    show v ≫ u = u ≫ v
    have h := allCentral M v u
    rw [castE_eq_self] at h
    exact h.symm

/-- The universal monoid-level extension of `toLocEnd` along `A' → Localization (genSubmonoid M)`
(the generators already become units under `toLocEnd`, so the monoid-localization universal
property applies unconditionally). -/
noncomputable def LocEndLift :
    Localization (genSubmonoid M) →* CategoryTheory.End
      ((LocalizationFunctor (centerOfMulticenter M)).obj (CategoryTheory.SingleObj.star A')) :=
  (IsLocalization.toLocalizationMap (genSubmonoid M) (Localization (genSubmonoid M))).lift
    (g := toLocEnd M) (toLocEnd_inverts_gen M)

/-- The comparison map `A'[M] → (CenterMorphismProperty (centerOfMulticenter M)).Localization`,
as a monoid hom on the (single) Hom-set. -/
noncomputable def kappaHom : A'[M] →* CategoryTheory.End
    ((LocalizationFunctor (centerOfMulticenter M)).obj (CategoryTheory.SingleObj.star A')) :=
  (LocEndLift M).comp (descToLoc M).toRingHom.toMonoidHom

/-- `kappaHom` as a functor `SingleObj A'[M] ⥤ (CenterMorphismProperty
(centerOfMulticenter M)).Localization`. -/
noncomputable def kappaFunctor :
    CategoryTheory.SingleObj A'[M] ⥤
      (CenterMorphismProperty (centerOfMulticenter M)).Localization :=
  CategoryTheory.SingleObj.functor (kappaHom M)

theorem toDilatationFunctor_comp_kappaFunctor :
    toDilatationFunctor M ⋙ kappaFunctor M = LocalizationFunctor (centerOfMulticenter M) := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro X Y a
  refine heq_of_eq ?_
  show kappaHom M ((toDilatationFunctor M).map a) =
      (LocalizationFunctor (centerOfMulticenter M)).map a
  show kappaHom M (algebraMap A' A'[M] a) = toLocEnd M a
  show (LocEndLift M) ((descToLoc M) (algebraMap A' A'[M] a)) = toLocEnd M a
  rw [AlgHom.commutes]
  exact (IsLocalization.toLocalizationMap (genSubmonoid M)
    (Localization (genSubmonoid M))).lift_eq (toLocEnd_inverts_gen M) a

theorem Phi51_comp_kappaFunctor :
    Phi51 M ⋙ kappaFunctor M = DilaToLoc (centerOfMulticenter M) := by
  apply Dila_factor_unique (centerOfMulticenter M)
    (LocalizationFunctor (centerOfMulticenter M))
  · show CatToDila (centerOfMulticenter M) ⋙ Phi51 M ⋙ kappaFunctor M =
      LocalizationFunctor (centerOfMulticenter M)
    rw [← CategoryTheory.Functor.assoc, Phi51_spec, toDilatationFunctor_comp_kappaFunctor]
  · exact CatToDila_comp_DilaToLoc (centerOfMulticenter M)
  · exact LocalizationFunctor_isSigmaRegular (centerOfMulticenter M)

theorem Phi51_faithful : (Phi51 M).Faithful := by
  apply faithful_of_comp_faithful (Phi51 M) (kappaFunctor M)
  rw [Phi51_comp_kappaFunctor]
  exact DilaToLoc_faithful (centerOfMulticenter M)

/-! ##### Surjectivity of `Φ`

With the `ν`-indexed sieve, a *single* fraction-generator edge at profile `ν` already reaches an
*arbitrary* element of `LargeIdeal^ν` (the whole ideal, not just a product of simpler pieces), so
every `Dilatation.frac` fraction — hence every element of `A'[M]`, by `induction_on` — is directly
the `Φ`-image of one such generator. No path/product induction is needed at all. -/

/-- The defining fraction identity `aᵢ^ν · (num/aᵢ^ν) = num` inside `A'[M]` itself (as opposed to
`Multicenter.Dilatation.image_elem_LargeIdeal_equal`'s span/map statement) — the same computation,
extracted as a reusable equation. -/
lemma algebraMap_elem_pow_mul_frac (ν : M^ℕ) (num : A') (hnum : num ∈ M.LargeIdeal^ν) :
    algebraMap A' A'[M] (M.elem^ν) * frac ν ⟨num, hnum⟩ = algebraMap A' A'[M] num := by
  simp only [algebraMap_apply, frac, mk_mul_mk, mk_eq_mk]
  exact ⟨0, by simp [mul_comm]⟩

theorem Phi51_full : (Phi51 M).Full := by
  refine ⟨fun {X Y} g => ?_⟩
  obtain ⟨X0, hX0⟩ := CatToDila_obj_surjective (centerOfMulticenter M) X
  obtain ⟨Y0, hY0⟩ := CatToDila_obj_surjective (centerOfMulticenter M) Y
  obtain rfl : X0 = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
  obtain rfl : Y0 = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
  subst hX0
  subst hY0
  set a : A'[M] := g with hadef
  induction a using Multicenter.Dilatation.induction_on with
  | h x =>
    obtain ⟨ν, num, hnum⟩ := x
    refine ⟨fraction_in_dila_single (centerOfMulticenter M)
      ⟨ν, CategoryTheory.SingleObj.star A', num, hnum⟩, ?_⟩
    have hcomp := fraction_in_dila_comp_mor (centerOfMulticenter M) ν
      (CategoryTheory.SingleObj.star A') num hnum
    have hmap := congrArg (Phi51 M).map hcomp
    rw [CategoryTheory.Functor.map_comp] at hmap
    have hspec1 : (Phi51 M).map
        ((CatToDila (centerOfMulticenter M)).map ((centerOfMulticenter M).mor ν)) =
        algebraMap A' A'[M] (M.elem^ν) := by
      have h := CategoryTheory.Functor.congr_hom (Phi51_spec M) ((centerOfMulticenter M).mor ν)
      simpa [toDilatationFunctor, CategoryTheory.SingleObj.mapHom,
        CategoryTheory.Functor.comp_map, centerOfMulticenter] using! h
    set numMor : CategoryTheory.SingleObj.star A' ⟶ CategoryTheory.SingleObj.star A' :=
      num with hnumMor
    have hspec2 : (Phi51 M).map ((CatToDila (centerOfMulticenter M)).map numMor) =
        algebraMap A' A'[M] num := by
      have h := CategoryTheory.Functor.congr_hom (Phi51_spec M) numMor
      simpa [toDilatationFunctor, CategoryTheory.SingleObj.mapHom,
        CategoryTheory.Functor.comp_map, centerOfMulticenter] using! h
    rw [hspec1, hspec2] at hmap
    rw [← CategoryTheory.End.mul_def] at hmap
    have hnzd : algebraMap A' A'[M] (M.elem^ν) ∈ nonZeroDivisors A'[M] :=
      Multicenter.Dilatation.nonzerodiv_image (M := M) ν
    exact (mul_cancel_left_mem_nonZeroDivisors hnzd).mp
      (hmap.trans (algebraMap_elem_pow_mul_frac M ν num hnum).symm)

/-! ##### Packaging `Φ` into an isomorphism of categories

`Phi51` is full and faithful, and both `Dila (centerOfMulticenter M)` and `SingleObj A'[M]` have a
single object, so `Φ` restricts to a bijection on the (unique) Hom-set — a `MonoidHom` inverse to
`Phi51.map` builds the inverse functor `Psi51` directly, mirroring `Iso315` in Proposition 3.15. -/

/-- `Φ`, restricted to the single Hom-set, as a bijection (using that `Phi51` is full and
faithful). -/
noncomputable def Phi51Equiv :
    CategoryTheory.End
      ((CatToDila (centerOfMulticenter M)).obj (CategoryTheory.SingleObj.star A')) ≃ A'[M] := by
  haveI := Phi51_faithful M
  haveI := Phi51_full M
  exact Equiv.ofBijective (Phi51 M).map
    ⟨fun _ _ h => (Phi51 M).map_injective h, fun a => (Phi51 M).map_surjective a⟩

lemma Phi51Equiv_apply (x : CategoryTheory.End
    ((CatToDila (centerOfMulticenter M)).obj (CategoryTheory.SingleObj.star A'))) :
    Phi51Equiv M x = (Phi51 M).map x := rfl

lemma Phi51Equiv_one : Phi51Equiv M 1 = 1 := by
  show (Phi51 M).map (1 : CategoryTheory.End _) = (1 : A'[M])
  rw [CategoryTheory.End.one_def, CategoryTheory.Functor.map_id,
    CategoryTheory.SingleObj.id_as_one]

lemma Phi51Equiv_mul (x y : CategoryTheory.End
    ((CatToDila (centerOfMulticenter M)).obj (CategoryTheory.SingleObj.star A'))) :
    Phi51Equiv M (x * y) = Phi51Equiv M x * Phi51Equiv M y := by
  simp only [Phi51Equiv_apply]
  rw [CategoryTheory.End.mul_def, CategoryTheory.Functor.map_comp, CategoryTheory.End.mul_def]

/-- The inverse of `Phi51Equiv`, as a `MonoidHom` — the data needed to build `Psi51`. -/
noncomputable def psi51Hom : A'[M] →* CategoryTheory.End
    ((CatToDila (centerOfMulticenter M)).obj (CategoryTheory.SingleObj.star A')) where
  toFun := (Phi51Equiv M).symm
  map_one' := by rw [← Phi51Equiv_one, Equiv.symm_apply_apply]
  map_mul' x y := by
    apply (Phi51Equiv M).injective
    rw [Phi51Equiv_mul, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The inverse functor to `Phi51`. -/
noncomputable def Psi51 : CategoryTheory.SingleObj A'[M] ⥤ Dila (centerOfMulticenter M) :=
  CategoryTheory.SingleObj.functor (psi51Hom M)

/-- `Dila (centerOfMulticenter M)` has a single object, since `C = SingleObj A'` does
(`CatToDila_obj_surjective` and `Subsingleton.elim` on `C`). -/
instance dila51_subsingleton : Subsingleton (Dila (centerOfMulticenter M)) := by
  constructor
  intro X Y
  obtain ⟨X0, hX0⟩ := CatToDila_obj_surjective (centerOfMulticenter M) X
  obtain ⟨Y0, hY0⟩ := CatToDila_obj_surjective (centerOfMulticenter M) Y
  obtain rfl : X0 = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
  obtain rfl : Y0 = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
  rw [← hX0, ← hY0]

theorem Phi51_comp_Psi51 : Phi51 M ⋙ Psi51 M = 𝟭 (Dila (centerOfMulticenter M)) := by
  refine CategoryTheory.Functor.hext (fun _ => Subsingleton.elim _ _) ?_
  intro X Y f
  refine heq_of_eq ?_
  obtain ⟨X0, hX0⟩ := CatToDila_obj_surjective (centerOfMulticenter M) X
  obtain ⟨Y0, hY0⟩ := CatToDila_obj_surjective (centerOfMulticenter M) Y
  obtain rfl : X0 = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
  obtain rfl : Y0 = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
  subst hX0
  subst hY0
  show (Psi51 M).map ((Phi51 M).map f) = f
  show psi51Hom M (Phi51Equiv M f) = f
  show (Phi51Equiv M).symm (Phi51Equiv M f) = f
  rw [Equiv.symm_apply_apply]

theorem Psi51_comp_Phi51 : Psi51 M ⋙ Phi51 M = 𝟭 (CategoryTheory.SingleObj A'[M]) := by
  refine CategoryTheory.Functor.hext (fun _ => Subsingleton.elim _ _) ?_
  intro X Y g
  refine heq_of_eq ?_
  obtain rfl : X = CategoryTheory.SingleObj.star A'[M] := Subsingleton.elim _ _
  obtain rfl : Y = CategoryTheory.SingleObj.star A'[M] := Subsingleton.elim _ _
  show (Phi51 M).map ((Psi51 M).map g) = g
  show Phi51Equiv M (psi51Hom M g) = g
  show Phi51Equiv M ((Phi51Equiv M).symm g) = g
  rw [Equiv.apply_symm_apply]

/-- **Proposition 5.1, full statement.** `Φ` assembles `Phi51`/`Psi51` into an isomorphism of
categories `Dila (centerOfMulticenter M) ≅ SingleObj A'[M]`, matching the paper's "provides the
desired identification." -/
noncomputable def Iso51 :
    Cat.of (Dila (centerOfMulticenter M)) ≅ Cat.of (CategoryTheory.SingleObj A'[M]) where
  hom := (Phi51 M).toCatHom
  inv := (Psi51 M).toCatHom
  hom_inv_id := Cat.ext (Phi51_comp_Psi51 M)
  inv_hom_id := Cat.ext (Psi51_comp_Phi51 M)

end Prop51

end RingDilatation

/-! ### Erratum to Proposition 5.1: the naive `I`-indexed center is *not* the right one

The printed `\citep[Proposition~5.1]{Mayeux}` identifies `𝒞[{(aᵢ)⁻¹∘Mᵢ}ᵢ∈I]` (dilating by the
center indexed directly by `i ∈ I`, one generator per index) with `A[M]`. This identification is
false: composition in `SingleObj A'` is multiplication, so the image of every morphism of this
naive center's dilatation is a product `c·∏ⱼ(mⱼ/aᵢⱼ)`, and not every element of `A[M]` has this
form. The concrete witness below: `A = ℤ[X]`, `a = 2`, `M = (X)`, and `(X+2)/2 ∈ A[M]` is not
reachable. See `\S`10.2 of the paper for the informal argument this formalizes. -/

namespace NaiveCenterCounterexample

open Family Polynomial Multicenter

abbrev CEx : Multicenter (Polynomial ℤ) where
  index := Unit
  ideal _ := Ideal.span {X}
  elem _ := 2

abbrev Target := Localization (Submonoid.powers (2:ℤ))

open Family in
lemma CEx_elem_pow_eval (ν : CEx^ℕ) : (CEx.elem^ν).eval 0 = 2 ^ (ν ()) := by
  have hν : ν = Finsupp.single () (ν ()) := by
    apply Finsupp.ext; intro i; cases i; simp
  erw [hν, familyPow_def, Finsupp.prod_single_index (by simp)]
  simp [CEx]

def psiPreDil (x : CEx.PreDil) : Target :=
  IsLocalization.mk' Target (x.num.eval 0) (⟨2 ^ (x.pow ()), x.pow (), rfl⟩ : Submonoid.powers (2:ℤ))

lemma psiPreDil_respects {x y : CEx.PreDil} (h : CEx.r x y) : psiPreDil x = psiPreDil y := by
  obtain ⟨β, hβ⟩ := h
  have hβ' := congrArg (Polynomial.eval 0) hβ
  simp only [eval_mul] at hβ'
  change x.num.eval 0 * (CEx.elem^(β + y.pow)).eval 0 =
    y.num.eval 0 * (CEx.elem^(β + x.pow)).eval 0 at hβ'
  rw [CEx_elem_pow_eval, CEx_elem_pow_eval] at hβ'
  simp only [Finsupp.add_apply] at hβ'
  refine IsLocalization.eq.mpr ⟨⟨2 ^ (β ()), β (), rfl⟩, ?_⟩
  show (2:ℤ) ^ (β ()) * (2 ^ (y.pow ()) * x.num.eval 0) =
    2 ^ (β ()) * (2 ^ (x.pow ()) * y.num.eval 0)
  calc (2:ℤ) ^ (β ()) * (2 ^ (y.pow ()) * x.num.eval 0)
      = (2 ^ (β ()) * 2 ^ (y.pow ())) * x.num.eval 0 := by ring
    _ = 2 ^ (β () + y.pow ()) * x.num.eval 0 := by rw [pow_add]
    _ = x.num.eval 0 * 2 ^ (β () + y.pow ()) := by ring
    _ = y.num.eval 0 * 2 ^ (β () + x.pow ()) := hβ'
    _ = 2 ^ (β () + x.pow ()) * y.num.eval 0 := by ring
    _ = (2 ^ (β ()) * 2 ^ (x.pow ())) * y.num.eval 0 := by rw [pow_add]
    _ = 2 ^ (β ()) * (2 ^ (x.pow ()) * y.num.eval 0) := by ring

/-- **The evaluation-at-`X=0` invariant `ψ`.** Descends to the dilatation ring because it kills
exactly what fraction-composition can produce from `(X)`-numerators. -/
def psi : (Polynomial ℤ)[CEx] → Target :=
  Multicenter.Dilatation.descFun psiPreDil (fun _ _ h => psiPreDil_respects h)

open Multicenter.Dilatation in
lemma psi_algebraMap (c : Polynomial ℤ) : psi (algebraMap _ _ c) = algebraMap ℤ Target (c.eval 0) := by
  rw [algebraMap_apply]
  show psiPreDil ⟨0, c, _⟩ = _
  unfold psiPreDil
  simp only [Finsupp.zero_apply, pow_zero]
  erw [show (⟨1, 0, rfl⟩ : Submonoid.powers (2:ℤ)) = 1 from rfl, IsLocalization.mk'_one]

open Multicenter.Dilatation in
lemma psi_mul (x y : (Polynomial ℤ)[CEx]) : psi (x * y) = psi x * psi y := by
  induction x using induction_on with
  | h x =>
    induction y using induction_on with
    | h y =>
      show psi (mk (Dilatation.mul' x y)) = psi (mk x) * psi (mk y)
      show psiPreDil (Dilatation.mul' x y) = psiPreDil x * psiPreDil y
      unfold psiPreDil Dilatation.mul'
      simp only [Finsupp.add_apply, eval_mul, pow_add]
      rw [← IsLocalization.mk'_mul]
      congr 1

open Multicenter.Dilatation in
lemma X_add_two_mem :
    (X + 2 : Polynomial ℤ) ∈ CEx.LargeIdeal^(Finsupp.single () 1 : CEx^ℕ) := by
  erw [familyPow_def, Finsupp.prod_single_index (by simp)]
  simp only [pow_one]
  show (X + 2 : Polynomial ℤ) ∈ Ideal.span {X} + Ideal.span {(2:Polynomial ℤ)}
  apply Submodule.add_mem_sup
  · exact Ideal.mem_span_singleton_self X
  · exact Ideal.mem_span_singleton_self 2

open Multicenter.Dilatation in
/-- The target element `(X+2)/2 ∈ A[M]`, which we show is unreachable. -/
noncomputable def target_elt : (Polynomial ℤ)[CEx] :=
  Dilatation.frac (Finsupp.single () 1 : CEx^ℕ) ⟨X + 2, X_add_two_mem⟩

open Multicenter.Dilatation in
lemma psi_target : psi target_elt = 1 := by
  show psiPreDil ⟨_, _, _⟩ = 1
  unfold psiPreDil
  simp only [eval_add, eval_X, eval_ofNat, Finsupp.single_eq_same]
  norm_num

open Multicenter.Dilatation in
lemma psi_frac_eq_zero (m : Polynomial ℤ) (hm : m ∈ Ideal.span ({X} : Set (Polynomial ℤ)))
    (hL : m ∈ CEx.LargeIdeal^(Finsupp.single () 1 : CEx^ℕ)) :
    psi (Dilatation.frac (Finsupp.single () 1 : CEx^ℕ) ⟨m, hL⟩) = 0 := by
  show psiPreDil ⟨_, _, _⟩ = 0
  unfold psiPreDil
  have : m.eval 0 = 0 := by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hm
    simp
  simp only [this]
  exact IsLocalization.mk'_zero _

/-- The naive `I`-indexed center `{(a_i, M_i)}` (here a single index): index `Unit`, morphism
`2`, sieve generated by `(X)` directly (not the large ideal). -/
def centerNaive : Center (CategoryTheory.SingleObj (Polynomial ℤ)) where
  I := Unit
  nonempty := ⟨()⟩
  dom _ := CategoryTheory.SingleObj.star (Polynomial ℤ)
  cod _ := CategoryTheory.SingleObj.star (Polynomial ℤ)
  mor _ := (2 : Polynomial ℤ)
  N _ := CategoryTheory.Prop51.Sieve.ofIdeal (Ideal.span {X})

open CategoryTheory Prop51 in
/-- **The comparison functor for the naive center**, built directly from the universal property
(`Dila_universal_property`), exactly as the printed proof's `Φ` is meant to be. -/
theorem prop_naive :
    ∃! (Φ : Dila centerNaive ⥤ CategoryTheory.SingleObj (Polynomial ℤ)[CEx]),
      CatToDila centerNaive ⋙ Φ = toDilatationFunctor CEx := by
  apply Dila_universal_property
  · show (ImageCenterMorphismProperty centerNaive (toDilatationFunctor CEx)).Q.Faithful
    set Sgen : Submonoid (Polynomial ℤ)[CEx] :=
      Submonoid.closure (Set.range (fun _ : Unit => algebraMap (Polynomial ℤ) _ (CEx.elem ())))
      with hSgendef
    have hSgennzd : Sgen ≤ nonZeroDivisors (Polynomial ℤ)[CEx] := by
      rw [hSgendef, Submonoid.closure_le]
      rintro x ⟨i, rfl⟩
      exact nonzerodiv_image_single CEx ()
    let e0 : CategoryTheory.SingleObj (Polynomial ℤ)[CEx] ⥤ CategoryTheory.SingleObj (Localization Sgen) :=
      CategoryTheory.SingleObj.mapHom _ _ (algebraMap (Polynomial ℤ)[CEx] (Localization Sgen)).toMonoidHom
    have he0faith : e0.Faithful := by
      constructor
      intro _ _ f g h
      exact IsLocalization.injective (M := Sgen) (Localization Sgen) hSgennzd h
    have he0inv :
        (ImageCenterMorphismProperty centerNaive (toDilatationFunctor CEx)).IsInvertedBy e0 := by
      rintro X Y f ⟨i0, hi⟩
      have hX : X = (toDilatationFunctor CEx).obj (centerNaive.dom i0) :=
        congrArg Sigma.fst hi
      have hY : Y = (toDilatationFunctor CEx).obj (centerNaive.cod i0) :=
        congrArg (fun s => s.2.1) hi
      subst hX
      subst hY
      have hf : f = (toDilatationFunctor CEx).map (centerNaive.mor i0) := by
        cases hi; rfl
      have hmem : algebraMap (Polynomial ℤ) _ (centerNaive.mor i0) ∈ Sgen := by
        show algebraMap (Polynomial ℤ) _ (CEx.elem ()) ∈ Sgen
        rw [hSgendef]
        exact Submonoid.subset_closure ⟨(), rfl⟩
      rw [hf, isIso_iff_isUnit]
      exact IsLocalization.map_units (Localization Sgen)
        (⟨algebraMap (Polynomial ℤ) _ (centerNaive.mor i0), hmem⟩ : Sgen)
    exact faithful_Q_of_isInvertedBy_of_faithful _ e0 he0inv he0faith
  · intro i0
    rintro Y f ⟨Z, g, h, hg, rfl⟩
    obtain rfl : Y = CategoryTheory.SingleObj.star (Polynomial ℤ)[CEx] := Subsingleton.elim _ _
    obtain rfl : Z = CategoryTheory.SingleObj.star (Polynomial ℤ) := Subsingleton.elim _ _
    let h' : (Polynomial ℤ)[CEx] := h
    let d : (Polynomial ℤ)[CEx] :=
      @CategoryTheory.Functor.map (CategoryTheory.SingleObj (Polynomial ℤ)) _
        (CategoryTheory.SingleObj (Polynomial ℤ)[CEx]) _
        (toDilatationFunctor CEx) (CategoryTheory.SingleObj.star (Polynomial ℤ))
        (CategoryTheory.SingleObj.star (Polynomial ℤ)) (centerNaive.mor i0)
    have hd : d = algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] (centerNaive.mor i0) := by
      show (@CategoryTheory.Functor.map (CategoryTheory.SingleObj (Polynomial ℤ)) _
        (CategoryTheory.SingleObj (Polynomial ℤ)[CEx]) _ (toDilatationFunctor CEx)
        (CategoryTheory.SingleObj.star (Polynomial ℤ)) (CategoryTheory.SingleObj.star (Polynomial ℤ))
        (centerNaive.mor i0)) = _
      simp [toDilatationFunctor, CategoryTheory.SingleObj.mapHom]
    have hgeq : @CategoryTheory.Functor.map (CategoryTheory.SingleObj (Polynomial ℤ)) _
        (CategoryTheory.SingleObj (Polynomial ℤ)[CEx]) _ (toDilatationFunctor CEx)
        (CategoryTheory.SingleObj.star (Polynomial ℤ)) (CategoryTheory.SingleObj.star (Polynomial ℤ)) g
        = algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] g := by
      simp [toDilatationFunctor, CategoryTheory.SingleObj.mapHom]
    have hgmem : g ∈ Ideal.span ({X} : Set (Polynomial ℤ)) := hg
    have hgL : g ∈ CEx.LargeIdeal^(Finsupp.single () 1 : CEx^ℕ) := by
      erw [familyPow_def, Finsupp.prod_single_index (by simp)]
      simp only [pow_one, Multicenter.LargeIdeal, Submodule.add_eq_sup]
      exact Submodule.mem_sup_left (M := Polynomial ℤ) hgmem
    have hmem : algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] g ∈
        Ideal.span {algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] (centerNaive.mor i0)} := by
      show algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] g ∈
        Ideal.span {algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] (CEx.elem ())}
      have heq := Multicenter.Dilatation.image_elem_LargeIdeal_equal (M := CEx)
        (Finsupp.single () 1 : CEx^ℕ)
      rw [show CEx.elem^(Finsupp.single () 1 : CEx^ℕ) = CEx.elem () by
        erw [familyPow_def, Finsupp.prod_single_index (by simp)]; simp] at heq
      rw [heq]
      exact Ideal.mem_map_of_mem _ hgL
    rw [Ideal.mem_span_singleton'] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨CategoryTheory.SingleObj.star (Polynomial ℤ)[CEx], c * h', d, Presieve.singleton_self _, ?_⟩
    rw [CategoryTheory.SingleObj.comp_as_mul, CategoryTheory.SingleObj.comp_as_mul, hd, hgeq, ← hc]
    show algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] (centerNaive.mor i0) * (c * h') =
      c * algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] (centerNaive.mor i0) * h'
    ring

/-- The functor `Φ_naive` produced by `prop_naive`, matching the printed paper's `Φ`. -/
noncomputable def PhiNaive : Dila centerNaive ⥤ CategoryTheory.SingleObj (Polynomial ℤ)[CEx] :=
  prop_naive.choose

open CategoryTheory.Prop51 in
lemma PhiNaive_spec : CatToDila centerNaive ⋙ PhiNaive = toDilatationFunctor CEx :=
  prop_naive.choose_spec.1

open CategoryTheory.Prop51 in
lemma PhiNaive_unique (G' : Dila centerNaive ⥤ CategoryTheory.SingleObj (Polynomial ℤ)[CEx])
    (hG' : CatToDila centerNaive ⋙ G' = toDilatationFunctor CEx) : G' = PhiNaive :=
  prop_naive.choose_spec.2 G' hG'

/-- `CEx.elem^ν = 2^(ν ())` as a polynomial identity (no evaluation), for arbitrary `ν`. -/
lemma CEx_elem_pow (ν : CEx^ℕ) : CEx.elem^ν = (2 : Polynomial ℤ)^(ν ()) := by
  have hν : ν = Finsupp.single () (ν ()) := by apply Finsupp.ext; intro i; cases i; simp
  erw [hν, familyPow_def, Finsupp.prod_single_index (by simp)]
  simp [CEx]

/-- `c·Xᵏ` always lies in the `k`-th large-ideal power, for every `c` and every `k`. -/
lemma cXk_mem (c : Polynomial ℤ) (k : ℕ) :
    c * X^k ∈ CEx.LargeIdeal^(Finsupp.single () k : CEx^ℕ) := by
  erw [familyPow_def, Finsupp.prod_single_index (by simp)]
  have hXmem : (X : Polynomial ℤ) ∈ CEx.LargeIdeal () := by
    simp only [Multicenter.LargeIdeal, Submodule.add_eq_sup]
    exact Submodule.mem_sup_left (Ideal.mem_span_singleton_self X)
  exact Ideal.mul_mem_left _ c (Ideal.pow_mem_pow hXmem k)

/-- `ψ` kills every fraction `(c·Xᵏ)/2ᵏ` with `k ≥ 1` (numerator divisible by `X`). -/
lemma psi_cXk_eq_zero (c : Polynomial ℤ) (k : ℕ) (hk : 1 ≤ k) :
    psi (Multicenter.Dilatation.frac (Finsupp.single () k : CEx^ℕ) ⟨c * X^k, cXk_mem c k⟩) = 0 := by
  show psiPreDil ⟨_, _, _⟩ = 0
  unfold psiPreDil
  have : (c * X^k).eval 0 = 0 := by
    have : (0:ℤ)^k = 0 := zero_pow (by omega)
    simp [this]
  simp only [this]
  exact IsLocalization.mk'_zero _

open Multicenter.Dilatation in
/-- **The key non-surjectivity fact.** `target_elt = (X+2)/2` is never `algebraMap c` for any
`c : ℤ[X]`: cross-multiplying gives `2c = X+2` (up to a harmless common power of `2`), and evaluating
at `X = 1` turns this into `2·c(1) = 3` in `ℤ`, which is false (2 does not divide 3). -/
lemma target_elt_ne_algebraMap (c : Polynomial ℤ) :
    algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] c ≠ target_elt := by
  intro heq
  rw [algebraMap_apply, target_elt, Multicenter.Dilatation.mk_eq_mk] at heq
  obtain ⟨β, hβ⟩ := heq
  simp only [add_zero] at hβ
  rw [CEx_elem_pow, CEx_elem_pow] at hβ
  simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hβ
  rw [pow_succ] at hβ
  have hne : (2:Polynomial ℤ)^(β ()) ≠ 0 := by
    apply pow_ne_zero
    intro h
    have := congrArg (Polynomial.eval 0) h
    simp at this
  have hrearranged : (2:Polynomial ℤ)^(β ()) * (c * 2) = (2:Polynomial ℤ)^(β ()) * (X + 2) := by
    linear_combination hβ
  have h2 : c * (2:Polynomial ℤ) = X + 2 := mul_left_cancel₀ hne hrearranged
  have hmap := congrArg (Polynomial.eval 1) h2
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat] at hmap
  omega

lemma mem_LargeIdeal_single1_of_mem_ideal {m : Polynomial ℤ}
    (hm : m ∈ Ideal.span ({X} : Set (Polynomial ℤ))) :
    m ∈ CEx.LargeIdeal^(Finsupp.single () 1 : CEx^ℕ) := by
  erw [familyPow_def, Finsupp.prod_single_index (by simp)]
  simp only [pow_one, Multicenter.LargeIdeal, Submodule.add_eq_sup]
  exact Submodule.mem_sup_left (M := Polynomial ℤ) hm

open Multicenter.Dilatation CategoryTheory.Prop51 in
/-- The defining identity for our specific `[X,2]` fraction, specialized from
`algebraMap_elem_pow_mul_frac`. -/
lemma algebraMap_two_mul_frac (m : Polynomial ℤ) (hm : m ∈ CEx.LargeIdeal^(Finsupp.single () 1 : CEx^ℕ)) :
    algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] 2 * frac (Finsupp.single () 1 : CEx^ℕ) ⟨m, hm⟩ =
    algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] m := by
  have h := algebraMap_elem_pow_mul_frac CEx (Finsupp.single () 1) m hm
  erw [CEx_elem_pow, Finsupp.single_eq_same, pow_one] at h
  exact h

open CategoryTheory.Prop51 Multicenter.Dilatation in
/-- **The image of a fraction generator.** `Φ_naive` sends the "`m`-over-`2`" generator (for
`m ∈ (X)`) to the honest dilatation fraction `m/2` — no more, no less. This is forced: composing
with `Θ(2)` on both sides and cancelling the nonzerodivisor `algebraMap 2` pins the value down
uniquely (cf. `Phi51_full`, the analogous computation for the `ν`-indexed center). -/
lemma PhiNaive_map_fraction (X' : CategoryTheory.SingleObj (Polynomial ℤ)) (m : Polynomial ℤ)
    (hm : m ∈ Ideal.span ({X} : Set (Polynomial ℤ))) :
    PhiNaive.map (fraction_in_dila_single centerNaive ⟨(), X', m, hm⟩) =
      frac (Finsupp.single () 1 : CEx^ℕ) ⟨m, mem_LargeIdeal_single1_of_mem_ideal hm⟩ := by
  have hcomp := fraction_in_dila_comp_mor centerNaive () X' m hm
  have hmap := congrArg PhiNaive.map hcomp
  rw [CategoryTheory.Functor.map_comp] at hmap
  have hspec1 : PhiNaive.map ((CatToDila centerNaive).map (centerNaive.mor ())) =
      algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] (centerNaive.mor ()) := by
    have h := CategoryTheory.Functor.congr_hom PhiNaive_spec (centerNaive.mor ())
    simpa [toDilatationFunctor, CategoryTheory.SingleObj.mapHom,
      CategoryTheory.Functor.comp_map] using h
  set mMor : CategoryTheory.SingleObj.star (Polynomial ℤ) ⟶ CategoryTheory.SingleObj.star (Polynomial ℤ) :=
    m with hmMor
  have hspec2 : PhiNaive.map ((CatToDila centerNaive).map mMor) =
      algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] m := by
    have h := CategoryTheory.Functor.congr_hom PhiNaive_spec mMor
    simpa [toDilatationFunctor, CategoryTheory.SingleObj.mapHom,
      CategoryTheory.Functor.comp_map] using h
  rw [hspec1, hspec2] at hmap
  rw [← CategoryTheory.End.mul_def] at hmap
  have hnzd : algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] (centerNaive.mor ()) ∈
      nonZeroDivisors (Polynomial ℤ)[CEx] := nonzerodiv_image_single CEx ()
  exact (mul_cancel_left_mem_nonZeroDivisors hnzd).mp
    (hmap.trans (algebraMap_two_mul_frac m (mem_LargeIdeal_single1_of_mem_ideal hm)).symm)

open CategoryTheory.Prop51 Multicenter.Dilatation in
/-- **Every reachable morphism is `c·Xᵏ/2ᵏ`.** Since `Dila centerNaive`'s only generators are
`C`'s original morphisms (ring elements) and the single fraction generator `X/2` (from the sieve
`(X)`), and composition is multiplication, every morphism's `Φ_naive`-image is a product of these,
hence of the stated shape. -/
lemma exists_c_k : ∀ {A B : GeneratedCategory centerNaive} (f : A ⟶ B),
    ∃ (c : Polynomial ℤ) (k : ℕ) (hmem : c * X^k ∈ CEx.LargeIdeal^(Finsupp.single () k : CEx^ℕ)),
      (PhiNaive.map ((GeneratedToDila centerNaive).map f) : (Polynomial ℤ)[CEx]) =
        frac (Finsupp.single () k : CEx^ℕ) ⟨c * X^k, hmem⟩ := by
  apply GeneratedCategory_morphism_induction centerNaive
    (P := fun {A B} (f : A ⟶ B) =>
      ∃ (c : Polynomial ℤ) (k : ℕ) (hmem : c * X^k ∈ CEx.LargeIdeal^(Finsupp.single () k : CEx^ℕ)),
        (PhiNaive.map ((GeneratedToDila centerNaive).map f) : (Polynomial ℤ)[CEx]) =
          frac (Finsupp.single () k : CEx^ℕ) ⟨c * X^k, hmem⟩)
  · -- identity
    intro A
    refine ⟨1, 0, by simpa using cXk_mem 1 0, ?_⟩
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    show (𝟙 (PhiNaive.obj ((GeneratedToDila centerNaive).obj A)) : (Polynomial ℤ)[CEx]) = _
    rw [CategoryTheory.SingleObj.id_as_one, ← map_one (algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx])]
    simp [algebraMap_apply, frac, mk_eq_mk]
  · -- composition
    rintro X Y W f g ⟨c1, k1, hmem1, heq1⟩ ⟨c2, k2, hmem2, heq2⟩
    refine ⟨c1 * c2, k1 + k2, by
      have := cXk_mem (c1 * c2) (k1 + k2)
      rw [pow_add] at this ⊢
      exact this, ?_⟩
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    set a : (Polynomial ℤ)[CEx] := PhiNaive.map ((GeneratedToDila centerNaive).map f) with ha
    set b : (Polynomial ℤ)[CEx] := PhiNaive.map ((GeneratedToDila centerNaive).map g) with hb
    rw [CategoryTheory.SingleObj.comp_as_mul, heq1, heq2, frac_mul_frac]
    show Multicenter.Dilatation.mk (M := CEx) _ = Multicenter.Dilatation.mk (M := CEx) _
    rw [mk_eq_mk]
    refine ⟨0, ?_⟩
    simp only [zero_add]
    rw [CEx_elem_pow, CEx_elem_pow]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    rw [pow_add]
    ring
  · -- generator
    intro A B g
    obtain ⟨f0, data⟩ := g
    cases data with
    | original h =>
        obtain ⟨g0, heq⟩ := h
        subst heq
        refine ⟨g0, 0, by simpa using cXk_mem g0 0, ?_⟩
        show (PhiNaive.map ((CatToDila centerNaive).map g0) : (Polynomial ℤ)[CEx]) = _
        have hh := CategoryTheory.Functor.congr_hom PhiNaive_spec g0
        have heq2 : PhiNaive.map ((CatToDila centerNaive).map g0) =
            algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] g0 := by
          simpa [toDilatationFunctor, CategoryTheory.SingleObj.mapHom,
            CategoryTheory.Functor.comp_map] using hh
        rw [heq2]
        simp [algebraMap_apply, frac, mk_eq_mk]
    | fraction h =>
        obtain ⟨p, heq⟩ := h
        cases heq
        obtain ⟨i0, X0, m, hm⟩ := p
        obtain rfl : i0 = () := rfl
        let m2 : Polynomial ℤ := m
        have hm2 : m2 ∈ Ideal.span ({X} : Set (Polynomial ℤ)) := hm
        obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp hm2
        refine ⟨c', 1, ?_, ?_⟩
        · rw [pow_one, hc']; exact mem_LargeIdeal_single1_of_mem_ideal hm2
        · show (PhiNaive.map (fraction_in_dila_single centerNaive ⟨(), X0, m, hm⟩) :
            (Polynomial ℤ)[CEx]) = _
          rw [PhiNaive_map_fraction X0 m hm]
          congr 1
          apply Subtype.ext
          show (m : Polynomial ℤ) = c' * X ^ 1
          rw [pow_one]
          exact hc'.symm

open CategoryTheory.Prop51 Multicenter.Dilatation in
/-- **`target_elt = (X+2)/2` is not in the image of `Φ_naive`.** Every morphism of `Dila
centerNaive` lifts (via `GeneratedToDila_full`) to a path of generators, whose image under
`Φ_naive` is `c·Xᵏ/2ᵏ` by `exists_c_k`. If `k = 0` this is `algebraMap c`, ruled out by
`target_elt_ne_algebraMap`; if `k ≥ 1` the numerator `c·Xᵏ` is divisible by `X`, so `ψ` kills it
(`psi_cXk_eq_zero`), while `ψ (target_elt) = 1 ≠ 0`. -/
theorem target_elt_not_in_range :
    ∀ {A B : Dila centerNaive} (φ : A ⟶ B), (PhiNaive.map φ : (Polynomial ℤ)[CEx]) ≠ target_elt := by
  intro A B φ hφ
  obtain ⟨ψ, hψ⟩ := (GeneratedToDila centerNaive).map_surjective φ
  obtain ⟨c, k, hmem, heq⟩ := exists_c_k ψ
  erw [← hψ, heq] at hφ
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0
    have hrw : frac (Finsupp.single () 0 : CEx^ℕ) ⟨c * X ^ 0, hmem⟩ =
        algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] c := by
      rw [algebraMap_apply]
      simp only [frac, mk_eq_mk]
      exact ⟨0, by simp⟩
    rw [hrw] at hφ
    exact target_elt_ne_algebraMap c hφ
  · have h0 := congrArg psi hφ
    rw [psi_target, psi_cXk_eq_zero c k hk1] at h0
    have hpow_nzd : Submonoid.powers (2:ℤ) ≤ nonZeroDivisors ℤ := by
      rw [Submonoid.powers_le]
      simp
    have hinj : Function.Injective (algebraMap ℤ Target) := IsLocalization.injective Target hpow_nzd
    have : (0:ℤ) = 1 := hinj (by rw [map_zero, map_one]; exact h0)
    exact absurd this (by norm_num)

open CategoryTheory.Prop51 Multicenter.Dilatation in
/-- `Φ_naive` itself is not full (its image on the relevant `End` misses `target_elt`). -/
theorem PhiNaive_not_full : ¬ PhiNaive.Full := by
  intro hfull
  haveI := hfull
  obtain ⟨φ, hφ⟩ := PhiNaive.map_surjective
    (X := (CatToDila centerNaive).obj (CategoryTheory.SingleObj.star (Polynomial ℤ)))
    (Y := (CatToDila centerNaive).obj (CategoryTheory.SingleObj.star (Polynomial ℤ)))
    (target_elt :
      PhiNaive.obj ((CatToDila centerNaive).obj (CategoryTheory.SingleObj.star (Polynomial ℤ))) ⟶
      PhiNaive.obj ((CatToDila centerNaive).obj (CategoryTheory.SingleObj.star (Polynomial ℤ))))
  exact target_elt_not_in_range φ hφ

open CategoryTheory.Prop51 in
/-- **The main theorem.** No functor `Dila centerNaive ⥤ SingleObj ℤ[X][CEx]` compatible with the
two canonical inclusion functors (i.e. matching the printed paper's comparison functor `Φ`) can be
part of an equivalence of categories: by `prop_naive`'s uniqueness clause any such functor equals
`Φ_naive`, and `Φ_naive` is not full (`PhiNaive_not_full`), while every equivalence functor is
full. This refutes Proposition 5.1's claimed identification `𝒞[(aᵢ)⁻¹∘Mᵢ] ≅ A[M]` for the naive
`I`-indexed center. -/
theorem no_C_compatible_equiv :
    ¬ ∃ (Φ' : Dila centerNaive ≌ CategoryTheory.SingleObj (Polynomial ℤ)[CEx]),
      CatToDila centerNaive ⋙ Φ'.functor = toDilatationFunctor CEx := by
  rintro ⟨Φ', hΦ'⟩
  have heq : Φ'.functor = PhiNaive := PhiNaive_unique Φ'.functor hΦ'
  have hfull : Φ'.functor.Full := inferInstance
  rw [heq] at hfull
  exact PhiNaive_not_full hfull

end NaiveCenterCounterexample

/-! ### Fact 5.2: the "sub-algebra" characterization of ring dilatations fails for categories

A concrete counterexample: a category `C` with two objects `X, Y` and two parallel non-identity
arrows `a, b : X ⟶ Y` (else trivial/empty Hom-sets), `Γ := {b}`, and a category `D` (with
`Hom_D(X,Y) = {b, a, a ∘ b⁻¹ ∘ a}`, finite) through which `C → C[Γ⁻¹]` factors faithfully — such
that `D` is *not* isomorphic (as a `C`-category) to any dilatation of `C`. -/

namespace Fact52

/-- The two objects of `C`. -/
inductive Obj : Type
  | X | Y

/-- `Hom_C(X,X) = {id}`, `Hom_C(Y,Y) = {id}`, `Hom_C(Y,X) = ∅`, `Hom_C(X,Y) = {a, b}`. -/
inductive CHom : Obj → Obj → Type
  | idX : CHom .X .X
  | idY : CHom .Y .Y
  | a : CHom .X .Y
  | b : CHom .X .Y

/-- Composition in `C` — well-defined since `Hom_C(Y,X) = ∅` leaves nothing nontrivial to
compose beyond identities. -/
def CHom.comp : ∀ {P Q R : Obj}, CHom P Q → CHom Q R → CHom P R := by
  intro P Q R f g
  match f, g with
  | .idX, g => exact g
  | .idY, .idY => exact .idY
  | .a, .idY => exact .a
  | .b, .idY => exact .b

instance : CategoryStruct Obj where
  Hom := CHom
  id P := match P with | .X => .idX | .Y => .idY
  comp f g := CHom.comp f g

instance : Category Obj where
  id_comp f := by cases f <;> rfl
  comp_id f := by cases f <;> rfl
  assoc f g h := by cases f <;> cases g <;> cases h <;> rfl

/-- The target groupoid for separating `a`, `b`, `a ∘ b⁻¹ ∘ a` in `C[Γ⁻¹]`: the one-object
groupoid on `Multiplicative ℤ` (`Quiver.SingleObj`, already fully instanced in mathlib). -/
abbrev D0 := CategoryTheory.SingleObj (Multiplicative ℤ)

/-- The morphism part of `FSep`, sending `a ↦ 1`, `b ↦ 0` (as elements of `Multiplicative ℤ`,
i.e. `ofAdd 1`/`ofAdd 0`). -/
def FSepMap : ∀ {P Q : Obj}, CHom P Q →
    ((CategoryTheory.SingleObj.star (Multiplicative ℤ)) ⟶
      (CategoryTheory.SingleObj.star (Multiplicative ℤ)))
  | _, _, .idX => (1 : Multiplicative ℤ)
  | _, _, .idY => (1 : Multiplicative ℤ)
  | _, _, .a => Multiplicative.ofAdd (1 : ℤ)
  | _, _, .b => (1 : Multiplicative ℤ)

/-- The functor `F : C ⥤ D0` sending `a ↦ ofAdd 1`, `b ↦ 1` (both automatically invertible,
since `D0` is a groupoid). -/
def FSep : Obj ⥤ D0 where
  obj _ := CategoryTheory.SingleObj.star (Multiplicative ℤ)
  map := FSepMap
  map_id P := by cases P <;> rfl
  map_comp f g := by cases f <;> cases g <;> rfl

/-- `Γ = {b}` as a `MorphismProperty Obj`. -/
def Gamma : MorphismProperty Obj := fun P Q f => (⟨P, Q, f⟩ : Σ P Q : Obj, CHom P Q) = ⟨.X, .Y, .b⟩

lemma Gamma_b : Gamma (CHom.b) := rfl

/-- `F` inverts `Γ`, trivially — `D0` is a groupoid, so *every* morphism is invertible. -/
lemma FSep_inverts_Gamma : Gamma.IsInvertedBy FSep := by
  rintro P Q f -
  infer_instance

/-- The unique extension of `FSep` along `Γ.Q` (universal property of localization). -/
noncomputable def FSep' : Gamma.Localization ⥤ D0 :=
  Localization.Construction.lift FSep FSep_inverts_Gamma

lemma FSep'_fac : Gamma.Q ⋙ FSep' = FSep :=
  Localization.Construction.fac FSep FSep_inverts_Gamma

instance : IsIso (Gamma.Q.map (CHom.b : CHom .X .Y)) :=
  CategoryTheory.MorphismProperty.Q_inverts Gamma CHom.b Gamma_b

/-- The composite `a ∘ b⁻¹ ∘ a` in `C[Γ⁻¹]`. -/
noncomputable def cMor : Gamma.Q.obj .X ⟶ Gamma.Q.obj .Y :=
  Gamma.Q.map CHom.a ≫ inv (Gamma.Q.map CHom.b) ≫ Gamma.Q.map CHom.a

lemma FSep'_map_b : FSep'.map (Gamma.Q.map CHom.b) = Multiplicative.ofAdd (0 : ℤ) := by
  have := Functor.congr_hom FSep'_fac (CHom.b : CHom .X .Y)
  simpa [FSep, FSepMap] using this

lemma FSep'_map_a : FSep'.map (Gamma.Q.map CHom.a) = Multiplicative.ofAdd (1 : ℤ) := by
  have := Functor.congr_hom FSep'_fac (CHom.a : CHom .X .Y)
  simpa [FSep, FSepMap] using this

lemma FSep'_map_cMor : FSep'.map cMor = Multiplicative.ofAdd (2 : ℤ) := by
  show FSep'.map (Gamma.Q.map CHom.a ≫ inv (Gamma.Q.map CHom.b) ≫ Gamma.Q.map CHom.a) = _
  simp only [Functor.map_comp, Functor.map_inv, FSep'_map_a, FSep'_map_b,
    CategoryTheory.SingleObj.comp_as_mul, CategoryTheory.SingleObj.inv_as_inv]
  rfl

/-- `b`, `a`, `a ∘ b⁻¹ ∘ a` are pairwise distinct morphisms `X ⟶ Y` in `C[Γ⁻¹]`. -/
lemma pairwise_distinct :
    Gamma.Q.map CHom.b ≠ Gamma.Q.map CHom.a ∧
      Gamma.Q.map CHom.b ≠ cMor ∧ Gamma.Q.map CHom.a ≠ cMor := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have h2 := congrArg (Multiplicative.toAdd ∘ FSep'.map) h
    simp only [Function.comp_apply, FSep'_map_a, FSep'_map_b] at h2
    simp at h2
  · have h2 := congrArg (Multiplicative.toAdd ∘ FSep'.map) h
    simp only [Function.comp_apply, FSep'_map_cMor, FSep'_map_b] at h2
    simp at h2
  · have h2 := congrArg (Multiplicative.toAdd ∘ FSep'.map) h
    simp only [Function.comp_apply, FSep'_map_cMor, FSep'_map_a] at h2
    simp at h2

/-- The two objects of `D`. -/
inductive DObj : Type
  | X | Y

/-- `Hom_D(X,X)={id}`, `Hom_D(Y,Y)={id}`, `Hom_D(Y,X)=∅`, `Hom_D(X,Y)={b,a,c}`. -/
inductive DHom : DObj → DObj → Type
  | idX : DHom .X .X
  | idY : DHom .Y .Y
  | b : DHom .X .Y
  | a : DHom .X .Y
  | c : DHom .X .Y

def DHom.comp : ∀ {P Q R : DObj}, DHom P Q → DHom Q R → DHom P R := by
  intro P Q R f g
  match f, g with
  | .idX, g => exact g
  | .idY, .idY => exact .idY
  | .b, .idY => exact .b
  | .a, .idY => exact .a
  | .c, .idY => exact .c

instance : CategoryStruct DObj where
  Hom := DHom
  id P := match P with | .X => .idX | .Y => .idY
  comp f g := DHom.comp f g

instance : Category DObj where
  id_comp f := by cases f <;> rfl
  comp_id f := by cases f <;> rfl
  assoc f g h := by cases f <;> cases g <;> cases h <;> rfl

/-- The object part of `C → D`. -/
def CtoDObj : Obj → DObj
  | .X => .X
  | .Y => .Y

/-- The morphism part of `C → D` (identity-on-objects, `a ↦ a`, `b ↦ b`). -/
def CtoDMap : ∀ {P Q : Obj}, CHom P Q → DHom (CtoDObj P) (CtoDObj Q)
  | _, _, .idX => .idX
  | _, _, .idY => .idY
  | _, _, .a => .a
  | _, _, .b => .b

/-- **Fact 5.2, setup.** The canonical (identity-on-objects) functor `C → D`. -/
def CtoD : Obj ⥤ DObj where
  obj := CtoDObj
  map := CtoDMap
  map_id P := by cases P <;> rfl
  map_comp f g := by cases f <;> cases g <;> rfl

/-- The object part of `D → C[Γ⁻¹]`. -/
def DtoLocObj : DObj → Gamma.Localization
  | .X => Gamma.Q.obj .X
  | .Y => Gamma.Q.obj .Y

/-- The morphism part of `D → C[Γ⁻¹]`, sending `b ↦ Γ.Q(b)`, `a ↦ Γ.Q(a)`, `c ↦ a ∘ b⁻¹ ∘ a`. -/
def DtoLocMap : ∀ {P Q : DObj}, DHom P Q → (DtoLocObj P ⟶ DtoLocObj Q)
  | _, _, .idX => 𝟙 _
  | _, _, .idY => 𝟙 _
  | _, _, .a => Gamma.Q.map CHom.a
  | _, _, .b => Gamma.Q.map CHom.b
  | _, _, .c => cMor

/-- **Fact 5.2, setup.** The canonical functor `D → C[Γ⁻¹]`. -/
def DtoLoc : DObj ⥤ Gamma.Localization where
  obj := DtoLocObj
  map := DtoLocMap
  map_id P := by cases P <;> rfl
  map_comp f g := by
    cases f <;> cases g <;>
      first
        | rfl
        | (show DtoLocMap DHom.c = 𝟙 _ ≫ DtoLocMap DHom.c
           rw [Category.id_comp])
        | (show DtoLocMap DHom.c = DtoLocMap DHom.c ≫ 𝟙 _
           rw [Category.comp_id])

lemma CHom.idX_eq : (CHom.idX : CHom .X .X) = 𝟙 Obj.X := rfl
lemma CHom.idY_eq : (CHom.idY : CHom .Y .Y) = 𝟙 Obj.Y := rfl

/-- The triangle `C → D → C[Γ⁻¹]` commutes with `C → C[Γ⁻¹]`. -/
theorem CtoD_comp_DtoLoc : CtoD ⋙ DtoLoc = Gamma.Q := by
  refine Functor.ext (fun P => by cases P <;> rfl) ?_
  intro P Q f
  cases f <;>
    change _ = 𝟙 _ ≫ _ ≫ 𝟙 _ <;>
    simp only [Category.id_comp, Category.comp_id]
  · exact (Gamma.Q.map_id Obj.X).symm
  · exact (Gamma.Q.map_id Obj.Y).symm
  · rfl
  · rfl

/-- **Fact 5.2, (ii).** `D → C[Γ⁻¹]` is faithful. -/
theorem DtoLoc_faithful : DtoLoc.Faithful := by
  constructor
  intro P Q f g h
  cases P <;> cases Q
  · cases f; cases g; rfl
  · cases f <;> cases g <;>
      first
        | rfl
        | exact absurd h pairwise_distinct.1
        | exact absurd h.symm pairwise_distinct.1
        | exact absurd h pairwise_distinct.2.1
        | exact absurd h.symm pairwise_distinct.2.1
        | exact absurd h pairwise_distinct.2.2
        | exact absurd h.symm pairwise_distinct.2.2
  · cases f
  · cases f; cases g; rfl

/-- **General separation fact.** For *any* `W : MorphismProperty Obj`, `a` and `b` remain
distinct after localizing at `W` — via the same `FSep`/groupoid-separation trick as
`pairwise_distinct`, since `FSep` (landing in a groupoid) inverts *every* `W`, not just `Γ`. -/
lemma Q_map_a_ne_map_b (W : MorphismProperty Obj) : W.Q.map CHom.a ≠ W.Q.map CHom.b := by
  intro h
  have hW : W.IsInvertedBy FSep := fun _ _ _ _ => inferInstance
  have hfac : W.Q ⋙ Localization.Construction.lift FSep hW = FSep :=
    Localization.Construction.fac FSep hW
  have ha : (Localization.Construction.lift FSep hW).map (W.Q.map CHom.a) =
      Multiplicative.ofAdd (1 : ℤ) := by
    have := Functor.congr_hom hfac (CHom.a : CHom .X .Y)
    simpa [FSep, FSepMap] using this
  have hb : (Localization.Construction.lift FSep hW).map (W.Q.map CHom.b) =
      Multiplicative.ofAdd (0 : ℤ) := by
    have := Functor.congr_hom hfac (CHom.b : CHom .X .Y)
    simpa [FSep, FSepMap] using this
  have hcontra := congrArg (Localization.Construction.lift FSep hW).map h
  rw [ha, hb] at hcontra
  have := congrArg Multiplicative.toAdd hcontra
  simp at this

/-- `Θ(a) ≠ Θ(b)` in *any* dilatation `Dila Z`, unconditionally — via `Fact_2_14`/
`CatToDila_comp_DilaToLoc` transporting `Q_map_a_ne_map_b` back along `DilaToLoc Z`. -/
lemma CatToDila_a_ne_b (Z : Center Obj) :
    (CatToDila Z).map CHom.a ≠ (CatToDila Z).map CHom.b := by
  intro h
  apply Q_map_a_ne_map_b (CenterMorphismProperty Z)
  have hDa : (DilaToLoc Z).map ((CatToDila Z).map CHom.a) =
      (CenterMorphismProperty Z).Q.map CHom.a := by
    have := Functor.congr_hom (CatToDila_comp_DilaToLoc Z) (CHom.a : CHom .X .Y)
    simpa only [Functor.comp_map, LocalizationFunctor, eqToHom_refl,
      Category.id_comp, Category.comp_id] using! this
  have hDb : (DilaToLoc Z).map ((CatToDila Z).map CHom.b) =
      (CenterMorphismProperty Z).Q.map CHom.b := by
    have := Functor.congr_hom (CatToDila_comp_DilaToLoc Z) (CHom.b : CHom .X .Y)
    simpa only [Functor.comp_map, LocalizationFunctor, eqToHom_refl,
      Category.id_comp, Category.comp_id] using! this
  rw [← hDa, ← hDb, h]

/-- Every generator index of a center on `Obj` has domain/codomain `(X,X)`, `(Y,Y)`, or `(X,Y)`
(the `(Y,X)` case is vacuous, `Hom_C(Y,X) = ∅`). -/
lemma Center.dom_cod_cases (Z : Center Obj) (i : Z.I) :
    (Z.dom i = .X ∧ Z.cod i = .X) ∨ (Z.dom i = .Y ∧ Z.cod i = .Y) ∨
      (Z.dom i = .X ∧ Z.cod i = .Y) := by
  match Z.dom i, Z.cod i, Z.mor i with
  | .X, .X, .idX => exact Or.inl ⟨rfl, rfl⟩
  | .Y, .Y, .idY => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | .X, .Y, .a => exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  | .X, .Y, .b => exact Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- The only endomorphism of any object in `Obj` is the identity. -/
lemma CHom.eq_id : ∀ {P : Obj} (f : CHom P P), f = 𝟙 P := by
  intro P f
  cases P <;> cases f <;> rfl

/-- `Hom_Obj(X,Y) = {a, b}`. -/
lemma CHom.eq_a_or_b (f : CHom Obj.X Obj.Y) : f = CHom.a ∨ f = CHom.b := by
  cases f <;> simp

/-- If `Z.dom i = Z.cod i` (an identity-shaped generator), every witness trivially factors
through `Z.mor i`, so such a generator index can never witness `¬ GoodCenter`. All objects here
are free variables of the lemma (not the compound `Z.dom i`/`Z.cod i`), so the `subst` below is
unproblematic; the caller instantiates `P, Q` at `Z.dom i, Z.cod i` directly. -/
lemma false_of_hnq_selfmor {P Q X' : Obj} (hPQ : P = Q) (m : X' ⟶ Q) (f : P ⟶ Q)
    (hnq : ∀ x : X' ⟶ P, m ≠ x ≫ f) : False := by
  subst hPQ
  exact hnq m (by rw [CHom.eq_id f, Category.comp_id])

/-- A witness `m` in the sieve `N` that doesn't factor through `gen` forces a contradiction.
Parametrized over free objects `P, Q` so `cases m` needs no dependent-elimination gymnastics. -/
lemma false_of_hnq_case3 {P Q X' : Obj} (hP : P = Obj.X) (hQ : Q = Obj.Y)
    {D : Type*} [Category D] (Θ : Obj ⥤ D)
    (N : Sieve Q) (gen : P ⟶ Q) (m : X' ⟶ Q) (hm : N m)
    (hnq : ∀ x : X' ⟶ P, m ≠ x ≫ gen)
    (frac : ∀ {X'' : Obj} (m' : X'' ⟶ Q), N m' → (Θ.obj X'' ⟶ Θ.obj P))
    (hfrac_comp : ∀ {X'' : Obj} (m' : X'' ⟶ Q) (hm' : N m'),
      frac m' hm' ≫ Θ.map gen = Θ.map m')
    (hYX : (Θ.obj Obj.Y ⟶ Θ.obj Obj.X) → False)
    (hendX : ∀ (e' : Θ.obj Obj.X ⟶ Θ.obj Obj.X), e' ≠ 𝟙 _ → False)
    (hab_ne : Θ.map CHom.a ≠ Θ.map CHom.b) : False := by
  subst hP; subst hQ
  cases m with
  | idY => exact hYX (frac CHom.idY hm)
  | a =>
      by_cases hg : gen = CHom.a
      · exact hnq CHom.idX (by rw [hg]; rfl)
      · have hgb : gen = CHom.b := (CHom.eq_a_or_b gen).resolve_left hg
        apply hendX (frac CHom.a hm)
        intro hid
        apply hab_ne
        have hcomp := hfrac_comp CHom.a hm
        rw [hgb, hid, Category.id_comp] at hcomp
        exact hcomp.symm
  | b =>
      by_cases hg : gen = CHom.b
      · exact hnq CHom.idX (by rw [hg]; rfl)
      · have hga : gen = CHom.a := (CHom.eq_a_or_b gen).resolve_right hg
        apply hendX (frac CHom.b hm)
        intro hid
        apply hab_ne
        have hcomp := hfrac_comp CHom.b hm
        rw [hga, hid, Category.id_comp] at hcomp
        exact hcomp

/-- The case-(ii) hypothesis, phrased directly as the factorization property needed by
`fraction_in_dila_single_eq_of_factors`: every sieve-witness `m ∈ Z.N i` factors through the
generator `Z.mor i` itself. For `Z.mor i = a` this forces (given `Hom_C`'s rigidity) `N_a ⊆ {a}`;
for `Z.mor i = b`, `N_b ⊆ {b}`; for `Z.mor i ∈ {idX, idY}` it holds unconditionally (composing
with an identity is free), matching the paper's case (ii) exactly. -/
def GoodCenter (Z : Center Obj) : Prop :=
  ∀ (i : Z.I) (X' : Obj) (m : X' ⟶ Z.cod i), Z.N i m → ∃ q : X' ⟶ Z.dom i, m = q ≫ Z.mor i

/-- **Case (i).** If `Z` is not "good", `CtoD` cannot be equivalent to `CatToDila Z` compatibly
with the maps from `C`. -/
lemma false_of_not_good {Z : Center Obj} (e : DObj ≌ Dila Z)
    (heq : CtoD ⋙ e.functor = CatToDila Z) (hbad : ¬ GoodCenter Z) : False := by
  have hobj : ∀ P : Obj, e.functor.obj (CtoDObj P) = (CatToDila Z).obj P := fun P =>
    congrArg (fun H : Obj ⥤ Dila Z => H.obj P) heq
  have hF := e.fullyFaithfulFunctor
  -- Both `Y ⟶ X` nonempty and `X ⟶ X` nontrivial in `Dila Z` are impossible under `e`.
  have false_of_hom_YX : ∀ (_w : (CatToDila Z).obj .Y ⟶ (CatToDila Z).obj .X), False := by
    intro w
    have w' : e.functor.obj (CtoDObj .Y) ⟶ e.functor.obj (CtoDObj .X) :=
      eqToHom (hobj .Y) ≫ w ≫ eqToHom (hobj .X).symm
    exact nomatch hF.preimage w'
  have false_of_endX_ne_id : ∀ (e' : (CatToDila Z).obj .X ⟶ (CatToDila Z).obj .X),
      e' ≠ 𝟙 _ → False := by
    intro e' he'
    apply he'
    set w' : e.functor.obj (CtoDObj .X) ⟶ e.functor.obj (CtoDObj .X) :=
      eqToHom (hobj .X) ≫ e' ≫ eqToHom (hobj .X).symm with hw'
    have hpre : hF.preimage w' = (DHom.idX : DHom .X .X) := by
      generalize hF.preimage w' = z
      cases z
      rfl
    have hmap := hF.map_preimage w'
    rw [hpre] at hmap
    have hidx : (DHom.idX : DHom .X .X) = 𝟙 (CtoDObj .X) := rfl
    rw [hidx, e.functor.map_id] at hmap
    rw [hw'] at hmap
    have := congrArg (fun f => eqToHom (hobj .X).symm ≫ f ≫ eqToHom (hobj .X)) hmap
    simpa using this.symm
  obtain ⟨i, X', m, hm, hnq⟩ := by
    unfold GoodCenter at hbad; push_neg at hbad; exact hbad
  rcases Center.dom_cod_cases Z i with ⟨hd, hc⟩ | ⟨hd, hc⟩ | ⟨hd, hc⟩
  · exact false_of_hnq_selfmor (hd.trans hc.symm) m (Z.mor i) hnq
  · exact false_of_hnq_selfmor (hd.trans hc.symm) m (Z.mor i) hnq
  · exact false_of_hnq_case3 hd hc (CatToDila Z) (Z.N i) (Z.mor i) m hm hnq
      (fun {X''} m' hm' => fraction_in_dila_single Z ⟨i, ⟨X'', ⟨m', hm'⟩⟩⟩)
      (fun {X''} m' hm' => fraction_in_dila_comp_mor Z i X'' m' hm')
      false_of_hom_YX false_of_endX_ne_id (CatToDila_a_ne_b Z)

/-- **Case (ii), core step.** Under `GoodCenter Z`, every morphism of the generated category
(hence, via `GeneratedToDila_full`, every morphism of `Dila Z`) between the images of two objects
of `Obj` is `Θ` applied to some morphism of `Obj`. This collapses every `fraction` edge back to an
`original` edge using `fraction_in_dila_single_eq_of_factors`, driven by the factorization
`GoodCenter Z` supplies. -/
lemma exists_C_mor_of_good {Z : Center Obj} (hGood : GoodCenter Z) :
    ∀ {X Y : GeneratedCategory Z} (f : X ⟶ Y),
      ∃ c : (objEquiv (CenterMorphismProperty Z)).symm X ⟶
          (objEquiv (CenterMorphismProperty Z)).symm Y,
        (GeneratedToDila Z).map f = (CatToDila Z).map c := by
  apply GeneratedCategory_morphism_induction Z
    (P := fun {X Y} f => ∃ c : (objEquiv (CenterMorphismProperty Z)).symm X ⟶
        (objEquiv (CenterMorphismProperty Z)).symm Y,
        (GeneratedToDila Z).map f = (CatToDila Z).map c)
  · intro X0
    have hEq : (GeneratedToDila Z).obj X0 =
        (CatToDila Z).obj ((objEquiv (CenterMorphismProperty Z)).symm X0) :=
      congrArg Quotient.mk (Equiv.apply_symm_apply (objEquiv (CenterMorphismProperty Z)) X0).symm
    exact ⟨𝟙 _, by rw [Functor.map_id, Functor.map_id]; exact hEq ▸ rfl⟩
  · rintro X0 Y0 W0 f0 g0 ⟨c1, hc1⟩ ⟨c2, hc2⟩
    exact ⟨c1 ≫ c2, by rw [Functor.map_comp, hc1, hc2, Functor.map_comp]; rfl⟩
  · intro A B g
    obtain ⟨f0, data⟩ := g
    cases data with
    | original h =>
        obtain ⟨g0, heq⟩ := h
        subst heq
        exact ⟨g0, rfl⟩
    | fraction h =>
        obtain ⟨p, heq⟩ := h
        cases heq
        obtain ⟨q, hq⟩ := hGood p.1 p.2.1 p.2.2.1 p.2.2.2
        exact ⟨q, fraction_in_dila_single_eq_of_factors Z p.1 p.2.1 q p.2.2.1 p.2.2.2 hq⟩

/-- **Case (ii).** Under `GoodCenter Z`, `CatToDila Z` is "full onto its generators": every
morphism `(CatToDila Z).obj P ⟶ (CatToDila Z).obj Q` is `Θ` of an actual morphism of `Obj`. -/
lemma CatToDila_full_of_good {Z : Center Obj} (hGood : GoodCenter Z) (P Q : Obj)
    (φ : (CatToDila Z).obj P ⟶ (CatToDila Z).obj Q) :
    ∃ c : P ⟶ Q, φ = (CatToDila Z).map c := by
  obtain ⟨p, hp⟩ := (GeneratedToDila Z).map_surjective
    (show (GeneratedToDila Z).obj (objEquiv (CenterMorphismProperty Z) P) ⟶
        (GeneratedToDila Z).obj (objEquiv (CenterMorphismProperty Z) Q) from φ)
  obtain ⟨c, hc⟩ := exists_C_mor_of_good hGood p
  have hP : (objEquiv (CenterMorphismProperty Z)).symm
      (objEquiv (CenterMorphismProperty Z) P) = P :=
    Equiv.symm_apply_apply (objEquiv (CenterMorphismProperty Z)) P
  have hQ : (objEquiv (CenterMorphismProperty Z)).symm
      (objEquiv (CenterMorphismProperty Z) Q) = Q :=
    Equiv.symm_apply_apply (objEquiv (CenterMorphismProperty Z)) Q
  refine ⟨hP ▸ hQ ▸ c, ?_⟩
  rw [← hp, hc]
  rfl

theorem no_realizing_center :
    ¬ ∃ (Z : Center Obj) (e : DObj ≌ Dila Z), CtoD ⋙ e.functor = CatToDila Z := by
  rintro ⟨Z, e, heq⟩
  by_cases hGood : GoodCenter Z
  · have hobj : ∀ P : Obj, e.functor.obj (CtoDObj P) = (CatToDila Z).obj P := fun P =>
      congrArg (fun H : Obj ⥤ Dila Z => H.obj P) heq
    have hF := e.fullyFaithfulFunctor
    set ψ : DHom .X .Y → ((CatToDila Z).obj .X ⟶ (CatToDila Z).obj .Y) := fun x =>
      eqToHom (hobj .X).symm ≫ e.functor.map x ≫ eqToHom (hobj .Y) with hψ_def
    have hψinj : Function.Injective ψ := by
      intro x y hxy
      apply hF.map_injective
      apply (cancel_mono (eqToHom (hobj .Y))).mp
      apply (cancel_epi (eqToHom (hobj .X).symm)).mp
      exact hxy
    obtain ⟨cb, hcb⟩ := CatToDila_full_of_good hGood .X .Y (ψ DHom.b)
    obtain ⟨ca, hca⟩ := CatToDila_full_of_good hGood .X .Y (ψ DHom.a)
    obtain ⟨cc, hcc⟩ := CatToDila_full_of_good hGood .X .Y (ψ DHom.c)
    have hcoll : cb = ca ∨ cb = cc ∨ ca = cc := by
      rcases CHom.eq_a_or_b cb with h1 | h1 <;> rcases CHom.eq_a_or_b ca with h2 | h2 <;>
        rcases CHom.eq_a_or_b cc with h3 | h3 <;> simp_all
    rcases hcoll with h | h | h
    · exact nomatch hψinj (hcb.trans ((congrArg (CatToDila Z).map h).trans hca.symm))
    · exact nomatch hψinj (hcb.trans ((congrArg (CatToDila Z).map h).trans hcc.symm))
    · exact nomatch hψinj (hca.trans ((congrArg (CatToDila Z).map h).trans hcc.symm))
  · exact false_of_not_good e heq hGood

end Fact52



/-! ## Appendix C: Elementary Properties of Dilatations of Rings

Formalizing statements of A. Mayeux, *Multi-centered Dilatations, Congruent Isomorphisms and
Rost Double Deformation Space*, Transformation Groups **31** (2026), 1801-1850, SS2.2
("Elementary Properties of Dilatations"), on top of the `Multicenter`/`Dilatation` API above.
-/

section AppendixC

open Family

namespace Multicenter

section restrict

variable {A' : Type*} [CommRing A'] (M : Multicenter A') (K : Set M.index)

/-- **Restriction of a multicenter to a subset `K ⊆ I` of the index set**, matching the notation
`{[Mᵢ,aᵢ]}_{i∈K}` of §2.2 of the printed paper. -/
def restrict : Multicenter A' where
  index := K
  ideal := fun i => M.ideal i.1
  elem  := fun i => M.elem i.1

@[simp] lemma restrict_ideal (i : K) : (M.restrict K).ideal i = M.ideal i.1 := rfl
@[simp] lemma restrict_elem (i : K) : (M.restrict K).elem i = M.elem i.1 := rfl
@[simp] lemma restrict_LargeIdeal (i : K) :
    (M.restrict K).LargeIdeal i = M.LargeIdeal i.1 := rfl

/-- **The second-stage multicenter of Proposition 2.24.** Over `B := A'[M.restrict K]`, the
complementary indices `j ∈ I ∖ K` carry the ideal `B·(Mⱼ)` (the image of `M.ideal j`) and the
element `aⱼ/1` (the image of `M.elem j`). -/
def complement : Multicenter (A'[M.restrict K]) where
  index := (Kᶜ : Set M.index)
  ideal := fun j => Ideal.map (algebraMap A' A'[M.restrict K]) (M.ideal j.1)
  elem  := fun j => algebraMap A' A'[M.restrict K] (M.elem j.1)

@[simp] lemma complement_ideal (j : (Kᶜ : Set M.index)) :
    (M.complement K).ideal j = Ideal.map (algebraMap A' A'[M.restrict K]) (M.ideal j.1) := rfl

@[simp] lemma complement_elem (j : (Kᶜ : Set M.index)) :
    (M.complement K).elem j = algebraMap A' A'[M.restrict K] (M.elem j.1) := rfl

end restrict

/-- **Reformulation of the `gen` hypothesis of the universal property.** For an `A'`-algebra `B'`,
the condition `span {φ(aᵢ)} = map φ (Lᵢ)` appearing in `Multicenter.desc` is equivalent to the
plain containment `map φ (Mᵢ) ≤ span {φ(aᵢ)}`, since `Lᵢ = Mᵢ + (aᵢ)`. This is the working form
used throughout Appendix C. -/
lemma gen_iff_le {A' B' : Type*} [CommRing A'] [CommRing B'] [Algebra A' B']
    (M : Multicenter A') (i : M.index) :
    Ideal.span {(algebraMap A' B') (M.elem i)} =
        Ideal.map (algebraMap A' B') (M.LargeIdeal i) ↔
      Ideal.map (algebraMap A' B') (M.ideal i) ≤
        Ideal.span {(algebraMap A' B') (M.elem i)} := by
  rw [LargeIdeal, Submodule.add_eq_sup, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  constructor
  · intro h; rw [h]; exact le_sup_left
  · intro h; exact (sup_eq_right.mpr h).symm

namespace Dilatation

/-- **The canonical map of a dilatation preserves non-zero-divisors of the base ring**: if `c ∈ A'`
is a non-zero-divisor, so is its image in `A'[M]`. (Unlike Proposition 2.20's injectivity, which
genuinely needs an extra hypothesis, this direction always holds; it is what makes the `i ∈ K`
branch of Proposition 2.24 unconditional.) -/
lemma nonzerodiv_algebraMap_of_mem_nonZeroDivisors {A' : Type*} [CommRing A']
    {M : Multicenter A'} {c : A'} (hc : c ∈ nonZeroDivisors A') :
    algebraMap A' A'[M] c ∈ nonZeroDivisors A'[M] := by
  have key : ∀ x : A'[M], x * algebraMap A' A'[M] c = 0 → x = 0 := by
    intro x h
    induction x using induction_on with
    | h x =>
      simp only [algebraMap_apply, mk_mul_mk, zero_def, mk_eq_mk] at h
      obtain ⟨β, hβ⟩ := h
      simp only [mul'_num, mul'_pow, add_zero, zero_mul] at hβ
      have hβ' : c * (x.num * M.elem ^ β) = 0 := by rw [← hβ]; ring
      have hx0 : x.num * M.elem ^ β = 0 := (mem_nonZeroDivisors_iff.mp hc).1 _ hβ'
      simp only [zero_def, mk_eq_mk]
      exact ⟨β, by simp [hx0]⟩
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun x hx => key x (by rw [mul_comm]; exact hx), key⟩

end Dilatation

end Multicenter

section Prop224

open Multicenter Multicenter.Dilatation Prop51

variable {A' : Type*} [CommRing A'] (M : Multicenter A') (K : Set M.index)

local notation "B224" => A'[Multicenter.restrict M K]
local notation "C224" => (A'[Multicenter.restrict M K])[Multicenter.complement M K]

/-- **First stage of Proposition 2.24**: the canonical `A'`-algebra map `A'[M|_K] → A'[M]`. -/
def psi224 : B224 →ₐ[A'] A'[M] :=
  Multicenter.desc (M.restrict K)
    (fun i => nonzerodiv_image_single M i.1)
    (fun i => reciprocal_for_univ M (AlgHom.id A' A'[M]) i.1)

instance algebra224 : Algebra B224 A'[M] := (psi224 M K).toRingHom.toAlgebra

lemma algebraMap224_eq : (algebraMap B224 A'[M]) = (psi224 M K).toRingHom := rfl

instance scalarTower224 : IsScalarTower A' B224 A'[M] :=
  IsScalarTower.of_algebraMap_eq fun a => ((psi224 M K).commutes a).symm

/-- The `A'`-algebra structure on the second stage `C224`, obtained by composing `A' → B224` with
`B224 → C224`. -/
instance algebra224' : Algebra A' C224 :=
  ((algebraMap B224 C224).comp (algebraMap A' B224)).toAlgebra

instance scalarTower224' : IsScalarTower A' B224 C224 :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-! #### The four hypotheses feeding the universal property. -/

lemma hnzd_chi (j : (Multicenter.complement M K).index) :
    (algebraMap B224 A'[M]) ((Multicenter.complement M K).elem j) ∈ nonZeroDivisors A'[M] := by
  erw [algebraMap224_eq, complement_elem]
  show psi224 M K (algebraMap A' B224 (M.elem j.1)) ∈ nonZeroDivisors A'[M]
  rw [(psi224 M K).commutes]
  exact nonzerodiv_image_single M j.1

lemma hgen_chi (j : (Multicenter.complement M K).index) :
    Ideal.span {(algebraMap B224 A'[M]) ((Multicenter.complement M K).elem j)} =
      Ideal.map (algebraMap B224 A'[M]) ((Multicenter.complement M K).LargeIdeal j) := by
  erw [gen_iff_le, complement_ideal, complement_elem, Ideal.map_map]
  have hcomm : (algebraMap B224 A'[M]).comp (algebraMap A' B224) = algebraMap A' A'[M] :=
    RingHom.ext fun a => (IsScalarTower.algebraMap_apply A' B224 A'[M] a).symm
  rw [hcomm, show (algebraMap B224 A'[M]) (algebraMap A' B224 (M.elem j.1)) =
      algebraMap A' A'[M] (M.elem j.1) from
    (IsScalarTower.algebraMap_apply A' B224 A'[M] (M.elem j.1)).symm]
  exact (gen_iff_le M j.1).mp (reciprocal_for_univ M (AlgHom.id A' A'[M]) j.1)

lemma hnzd_rho (i : M.index) :
    (algebraMap A' C224) (M.elem i) ∈ nonZeroDivisors C224 := by
  rw [IsScalarTower.algebraMap_apply A' B224 C224]
  by_cases hi : i ∈ K
  · -- `aᵢ/1` is already a non-zero-divisor in `B224`; lift it along the second dilatation.
    exact nonzerodiv_algebraMap_of_mem_nonZeroDivisors
      (nonzerodiv_image_single (M.restrict K) (⟨i, hi⟩ : K))
  · -- `aᵢ/1` is literally one of `complement M K`'s own generators.
    exact nonzerodiv_image_single (Multicenter.complement M K) (⟨i, hi⟩ : (Kᶜ : Set M.index))

lemma hgen_rho (i : M.index) :
    Ideal.span {(algebraMap A' C224) (M.elem i)} =
      Ideal.map (algebraMap A' C224) (M.LargeIdeal i) := by
  rw [gen_iff_le, IsScalarTower.algebraMap_eq A' B224 C224, ← Ideal.map_map, RingHom.comp_apply]
  by_cases hi : i ∈ K
  · have h : Ideal.map (algebraMap A' B224) (M.ideal i) ≤
        Ideal.span {(algebraMap A' B224) (M.elem i)} :=
      (gen_iff_le (M.restrict K) (⟨i, hi⟩ : K)).mp
        (reciprocal_for_univ (M.restrict K) (AlgHom.id A' B224) (⟨i, hi⟩ : K))
    calc Ideal.map (algebraMap B224 C224) (Ideal.map (algebraMap A' B224) (M.ideal i))
        ≤ Ideal.map (algebraMap B224 C224) (Ideal.span {(algebraMap A' B224) (M.elem i)}) :=
          Ideal.map_mono h
      _ = Ideal.span {(algebraMap B224 C224) ((algebraMap A' B224) (M.elem i))} := by
          rw [Ideal.map_span, Set.image_singleton]
  · have h : Ideal.map (algebraMap B224 C224)
        ((Multicenter.complement M K).ideal (⟨i, hi⟩ : (Kᶜ : Set M.index))) ≤
          Ideal.span {(algebraMap B224 C224)
            ((Multicenter.complement M K).elem (⟨i, hi⟩ : (Kᶜ : Set M.index)))} :=
      (gen_iff_le (Multicenter.complement M K) (⟨i, hi⟩ : (Kᶜ : Set M.index))).mp
        (reciprocal_for_univ (Multicenter.complement M K) (AlgHom.id B224 C224)
          (⟨i, hi⟩ : (Kᶜ : Set M.index)))
    exact h

/-! #### The two comparison maps and the isomorphism. -/

/-- **Second stage of Proposition 2.24**: the canonical `B224`-algebra map `C224 →ₐ A'[M]`. -/
def chi224 : C224 →ₐ[B224] A'[M] :=
  Multicenter.desc (Multicenter.complement M K) (hnzd_chi M K) (hgen_chi M K)

/-- **Reverse direction of Proposition 2.24**: the canonical `A'`-algebra map `A'[M] →ₐ C224`. -/
def rho224 : A'[M] →ₐ[A'] C224 :=
  Multicenter.desc M (hnzd_rho M K) (hgen_rho M K)

lemma rho224_psi224 (b : B224) : rho224 M K (psi224 M K b) = algebraMap B224 C224 b := by
  have h1 := Multicenter.lemma_exists_unique_morphism (M.restrict K)
    (fun i => hnzd_rho M K i.1) (fun i => hgen_rho M K i.1)
    ((rho224 M K).comp (psi224 M K))
  have h2 := Multicenter.lemma_exists_unique_morphism (M.restrict K)
    (fun i => hnzd_rho M K i.1) (fun i => hgen_rho M K i.1)
    (IsScalarTower.toAlgHom A' B224 C224)
  exact AlgHom.congr_fun (h1.trans h2.symm) b

/-- **Proposition 2.24.** The full dilatation `A'[M]` is canonically isomorphic, as an
`A'[M|_K]`-algebra, to the second-stage dilatation `(A'[M|_K])[complement M K]`. -/
def prop_2_24 : C224 ≃ₐ[B224] A'[M] where
  toFun := chi224 M K
  invFun := rho224 M K
  left_inv := by
    have hcommutes : ∀ b : B224,
        (rho224 M K) ((chi224 M K) (algebraMap B224 C224 b)) = algebraMap B224 C224 b := by
      intro b
      rw [(chi224 M K).commutes b, algebraMap224_eq]
      exact rho224_psi224 M K b
    let composite : C224 →ₐ[B224] C224 :=
      { toFun := fun y => rho224 M K (chi224 M K y)
        map_one' := by simp
        map_mul' := by intro x y; simp
        map_zero' := by simp
        map_add' := by intro x y; simp
        commutes' := hcommutes }
    have h1 := Multicenter.lemma_exists_unique_morphism (Multicenter.complement M K)
      (fun j => nonzerodiv_image_single (Multicenter.complement M K) j)
      (fun j => reciprocal_for_univ (Multicenter.complement M K) (AlgHom.id B224 C224) j)
      composite
    have h2 := Multicenter.lemma_exists_unique_morphism (Multicenter.complement M K)
      (fun j => nonzerodiv_image_single (Multicenter.complement M K) j)
      (fun j => reciprocal_for_univ (Multicenter.complement M K) (AlgHom.id B224 C224) j)
      (AlgHom.id B224 C224)
    intro y
    exact AlgHom.congr_fun (h1.trans h2.symm) y
  right_inv := by
    have h1 := Multicenter.lemma_exists_unique_morphism M
      (fun i => nonzerodiv_image_single M i)
      (fun i => reciprocal_for_univ M (AlgHom.id A' A'[M]) i)
      (((chi224 M K).restrictScalars A').comp (rho224 M K))
    have h2 := Multicenter.lemma_exists_unique_morphism M
      (fun i => nonzerodiv_image_single M i)
      (fun i => reciprocal_for_univ M (AlgHom.id A' A'[M]) i)
      (AlgHom.id A' A'[M])
    intro x
    exact AlgHom.congr_fun (h1.trans h2.symm) x
  map_mul' := map_mul (chi224 M K)
  map_add' := map_add (chi224 M K)
  commutes' := (chi224 M K).commutes

/-! #### Uniqueness in Proposition 2.24 -/

/-- **Uniqueness of the comparison map of Proposition 2.24.** Any `A[M|_K]`-algebra map from
the two-stage dilatation to `A[M]` equals `chi224`. This is the uniqueness half of the
universal property of dilatations of rings, applied to the multicenter `complement M K`. -/
theorem chi224_unique (f : C224 →ₐ[B224] A'[M]) : f = chi224 M K :=
  Multicenter.lemma_exists_unique_morphism _ (hnzd_chi M K) (hgen_chi M K) f

/-- **The isomorphism of Proposition 2.24 is unique.** Any isomorphism of
`A[M|_K]`-algebras between the two-stage dilatation and `A[M]` equals `prop_2_24`. -/
theorem prop_2_24_unique (e : C224 ≃ₐ[B224] A'[M]) : e = prop_2_24 M K := by
  apply AlgEquiv.ext
  intro x
  exact AlgHom.congr_fun (chi224_unique M K e.toAlgHom) x

/-- **Proposition 2.24, existence and uniqueness together.** There is exactly one
isomorphism from the two-stage dilatation to `A[M]` compatible with the canonical maps out
of the first-stage ring `A[M|_K]`. -/
theorem prop_2_24_existsUnique :
    ∃! e : C224 ≃ₐ[B224] A'[M],
      ∀ b : B224, e (algebraMap B224 C224 b) = algebraMap B224 A'[M] b :=
  ⟨prop_2_24 M K, (prop_2_24 M K).commutes, fun e _ => prop_2_24_unique M K e⟩

end Prop224

end AppendixC

end CategoryTheory
