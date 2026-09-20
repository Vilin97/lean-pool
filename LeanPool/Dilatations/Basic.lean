/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arnaud Mayeux
-/
module

public import Mathlib.CategoryTheory.Sites.Sieves.Functoriality
public import Mathlib.CategoryTheory.Localization.Construction

/-!
# Construction and universal property of categorical dilatations

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

/-- Transporting the endpoints of two composable morphisms respects composition. -/
lemma transported_comp {C : Type u} [Category.{v} C] {X Y Z X' Y' Z' : C}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') (f : X' ⟶ Y') (g : Y' ⟶ Z') :
    (eqToHom hX ≫ f ≫ eqToHom hY.symm) ≫ (eqToHom hY ≫ g ≫ eqToHom hZ.symm) =
      eqToHom hX ≫ (f ≫ g) ≫ eqToHom hZ.symm := by
  subst X' Y' Z'
  simp

/-- **Definition 2.9.** A center `{[Nᵢ,dᵢ]}ᵢ∈I` in `C`. -/
structure Center (C : Type u) [Category.{v} C] where
  /-- Indices of the denominator morphisms and their numerator sieves. -/
  I : Type u
  (nonempty : Nonempty I)
  /-- Domain of each denominator morphism. -/
  dom : I → C
  /-- Codomain of each denominator morphism. -/
  cod : I → C
  /-- Morphisms by which the corresponding numerators may be divided. -/
  mor : ∀ i : I, dom i ⟶ cod i
  /-- Permitted numerators, stable under precomposition. -/
  N   : ∀ i : I, Sieve (C := C) (cod i)

variable {C : Type u} [Category.{v} C]
variable (Z : Center C)

/-- Whether a dependent morphism is one of the chosen denominators. -/
def IsCenterMor (f : Σ X Y : C, X ⟶ Y) : Prop :=
  ∃ i : Z.I, f = ⟨Z.dom i, Z.cod i, Z.mor i⟩

/-- The MorphismProperty corresponding to IsCenterMor. -/
def CenterMorphismProperty : MorphismProperty C := fun X Y f => IsCenterMor Z ⟨X, Y, f⟩

/-- The localized category obtained by formally inverting the morphisms in
    CenterMorphismProperty. -/
def CenterLocalization : Type u := (CenterMorphismProperty Z).Localization

/-- The canonical functor from C to the localization. -/
def LocalizationFunctor : C ⥤ (CenterMorphismProperty Z).Localization :=
    (CenterMorphismProperty Z).Q

/-- A chosen denominator together with a permitted numerator. -/
def CenterSievePair : Type (max u v) :=
  Σ i : Z.I, Σ X : C, { f : X ⟶ Z.cod i // Z.N i f }

/-- The quiver obtained by adjoining formal inverses of the chosen denominators. -/
def localizationQuiver := LocQuiver (CenterMorphismProperty Z)

/-- The formal inverse of the denominator attached to a numerator. -/
def inverseInPath (p : CenterSievePair Z) :
    ιPaths (CenterMorphismProperty Z) (Z.cod p.1) ⟶
    ιPaths (CenterMorphismProperty Z) (Z.dom p.1) :=
  Localization.Construction.ψ₂ (CenterMorphismProperty Z)
    (Z.mor p.1) ⟨p.1, rfl⟩

/-- The path consisting of a numerator followed by its formal denominator inverse. -/
def fractionInPath (p : CenterSievePair Z) :
    ιPaths (CenterMorphismProperty Z) (p.2.1) ⟶
    ιPaths (CenterMorphismProperty Z) (Z.dom p.1) :=
  Localization.Construction.ψ₁ (CenterMorphismProperty Z) p.2.2.1 ≫
    inverseInPath Z p

/-- A permitted fraction evaluated in the ambient localization. -/
def fractionInLocalization (p : CenterSievePair Z) :
objEquiv (CenterMorphismProperty Z) (p.2.1) ⟶
objEquiv (CenterMorphismProperty Z) (Z.dom p.1) :=
 (CategoryTheory.Quotient.functor
   (relations (CenterMorphismProperty Z))).map
      (fractionInPath Z p)

/-- Whether a localization morphism is represented by one permitted fraction. -/
def IsPairMor
    (f : Σ X Y : (CenterMorphismProperty Z).Localization, X ⟶ Y) : Prop :=
  ∃ p : CenterSievePair Z,
    f =
      ⟨objEquiv (CenterMorphismProperty Z) (p.2.1),
       objEquiv (CenterMorphismProperty Z) (Z.dom p.1),
       (CategoryTheory.Quotient.functor
          (relations (CenterMorphismProperty Z))).map
             (fractionInPath Z p)⟩

/-- Data exhibiting a localization morphism as a permitted fraction. -/
structure PairMorWitness
    (Z : Center C)
    {X Y : (CenterMorphismProperty Z).Localization}
    (f : X ⟶ Y) where
  /-- The chosen denominator and numerator representing the morphism. -/
  p : CenterSievePair Z
  eq :
    (⟨X,Y,f⟩ :
      Σ A B : (CenterMorphismProperty Z).Localization, A ⟶ B)
      =
    ⟨objEquiv (CenterMorphismProperty Z) (p.2.1),
     objEquiv (CenterMorphismProperty Z) (Z.dom p.1),
     (CategoryTheory.Quotient.functor
        (relations (CenterMorphismProperty Z))).map
       (fractionInPath Z p)⟩

/-- The localization morphisms represented by single permitted fractions. -/
def FractionMorphismProperty :
       MorphismProperty (CenterMorphismProperty Z).Localization  :=
          fun X Y f => IsPairMor Z ⟨X, Y, f⟩

/-- Data exhibiting a localization morphism as the image of a base morphism. -/
structure OriginalWitness
    (Z : Center C)
    {X Y : (CenterMorphismProperty Z).Localization}
    (f : X ⟶ Y) where
  /-- The base morphism whose localization image is the given morphism. -/
  g :
    (objEquiv (CenterMorphismProperty Z)).symm X ⟶
      (objEquiv (CenterMorphismProperty Z)).symm Y
  eq :
    f =
      (CenterMorphismProperty Z).Q.map g

/-- A generator is either a permitted fraction or the image of a base morphism. -/
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

/-- The quiver of witnessed original and fraction morphisms. -/
@[instance_reducible]
def GeneratorQuiver : Quiver (CenterMorphismProperty Z).Localization where
  Hom X Y :=
    Σ f : X ⟶ Y, GeneratorMorphismData Z f

/-- Objects of the ambient localization, used to build the generator category. -/
def GeneratorObjects :=
  (CenterMorphismProperty Z).Localization

instance : Quiver (GeneratorObjects Z) :=
  GeneratorQuiver Z

/-- The free category on the original and fraction generators. -/
def GeneratedCategory :=
  CategoryTheory.Paths (GeneratorObjects Z)

instance : Category (GeneratedCategory Z) :=
  Paths.categoryPaths _

/-- Forget the witness distinguishing original and fraction generators. -/
def forgetGenerator : GeneratorObjects Z ⥤q (CenterMorphismProperty Z).Localization :=
  { obj := id,
    map := fun {_ _} f => f.1 }

/-- Evaluate a path of generators by composition in the localization. -/
def GeneratedToLocalization :
    GeneratedCategory Z ⥤ (CenterMorphismProperty Z).Localization :=
         CategoryTheory.Paths.lift (forgetGenerator Z)

/-- Recover the base morphism from its original-morphism witness. -/
def originalFactor
    {X Y : (CenterMorphismProperty Z).Localization}
    (f : X ⟶ Y)
    (h : OriginalWitness Z f) :
    (objEquiv (CenterMorphismProperty Z)).symm X ⟶
      (objEquiv (CenterMorphismProperty Z)).symm Y :=
  h.g

/-- Two paths are identified exactly when they evaluate equally in the localization. -/
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

/-- The canonical faithful functor from the dilatation to the ambient localization. -/
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

/-- The quotient functor from generator paths to the dilatation. -/
def GeneratedToDila :
    GeneratedCategory Z ⥤ Dila Z :=
  CategoryTheory.Quotient.functor (DilaRel Z)

instance GeneratedToDila_full :
    (GeneratedToDila Z).Full := by
  change (CategoryTheory.Quotient.functor (DilaRel Z)).Full
  infer_instance

/-- The base-category prefunctor sending morphisms to original generators. -/
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
  have : IsIso ((DilaToLoc Z).map ((CatToDila Z).map (Z.mor i))) := by
    have hkey := Functor.congr_hom (CatToDila_comp_DilaToLoc Z) (Z.mor i)
    simp only [Functor.comp_map] at hkey
    rw [hkey]
    exact CategoryTheory.MorphismProperty.Q_inverts _ (Z.mor i) ⟨i, rfl⟩
  have := DilaToLoc_faithful Z
  exact Fact_3_2 (DilaToLoc Z) ((CatToDila Z).map (Z.mor i))

/-- Push a sieve forward along the canonical dilatation functor. -/
def CatToDilaSieve
    {X : C} (N : Sieve (C := C) X) :
    Sieve (C := Dila Z) ((CatToDila Z).obj X) :=
  Sieve.functorPushforward (CatToDila Z) N

lemma fraction_comp_mor (i : Z.I) (X : C)
    (m : X ⟶ Z.cod i)
    (hm : Z.N i m) :
    (fractionInLocalization Z ⟨i, ⟨X, ⟨m, hm⟩⟩⟩) ≫
      (CenterMorphismProperty Z).Q.map (Z.mor i)
    =
      (CenterMorphismProperty Z).Q.map m := by
  change (Quotient.functor (relations (CenterMorphismProperty Z))).map
      (fractionInPath Z ⟨i, ⟨X, ⟨m, hm⟩⟩⟩) ≫
      (Quotient.functor (relations (CenterMorphismProperty Z))).map
        (ψ₁ (CenterMorphismProperty Z) (Z.mor i)) =
      (Quotient.functor (relations (CenterMorphismProperty Z))).map
        (ψ₁ (CenterMorphismProperty Z) m)
  rw [← Functor.map_comp]
  apply Quot.sound
  simpa only [fractionInPath, inverseInPath, Category.assoc, Category.comp_id] using
    (relations.Winv₂ (Z.mor i) ⟨i, rfl⟩ |>
    HomRel.CompClosure.intro _ _ (ψ₁ (CenterMorphismProperty Z) m) _ _ (𝟙 _))

/-- The generator corresponding to a single permitted fraction. -/
def fractionGenerator (p : CenterSievePair Z) :
    (CToGeneratorQuiver Z).obj p.2.1 ⟶
    (CToGeneratorQuiver Z).obj (Z.dom p.1) :=
  ⟨
  fractionInLocalization Z p,
  GeneratorMorphismData.fraction ⟨p, rfl⟩
⟩

/-- **Proposition 3.1 (2), existence.** The fraction `b = dᵢ\n = [n∘l_{dᵢ}]` witnessing the
unique factorization `[n] = Θ(dᵢ) ∘ b`. -/
def fractionInDilatation (p : CenterSievePair Z) :
    (CatToDila Z).obj p.2.1 ⟶
    (CatToDila Z).obj (Z.dom p.1) :=
  (GeneratedToDila Z).map
    (Quiver.Hom.toPath (fractionGenerator Z p))

/-- **Proposition 3.1 (2), defining property.** `b ≫ Θ(dᵢ) = Θ(n)`, i.e. the triangle
`[n] = Θ(dᵢ) ∘ b` commutes. -/
lemma fraction_in_dila_comp_mor (Z : Center C) (i : Z.I) (X : C) (m : X ⟶ Z.cod i) (hm : Z.N i m) :
    fractionInDilatation Z ⟨i, ⟨X, ⟨m, hm⟩⟩⟩ ≫ (CatToDila Z).map (Z.mor i) =
      (CatToDila Z).map m := by
  apply Quotient.sound
  change
    fractionInLocalization Z ⟨i, ⟨X, ⟨m, hm⟩⟩⟩ ≫ (CenterMorphismProperty Z).Q.map (Z.mor i) =
      (CenterMorphismProperty Z).Q.map m
  exact fraction_comp_mor Z i X m hm

/-- **Proposition 3.5.** `S ^ C'_Θ(Nᵢ) ⊂ S ^ C'_Θ(dᵢ)`. -/
theorem CatToDila_image_sieve_le_singleton (i : Z.I) :
    CatToDilaSieve Z (Z.N i) ≤
      Sieve.generate (Presieve.singleton ((CatToDila Z).map (Z.mor i))) := by
  intro X f hf
  dsimp [CatToDilaSieve, Sieve.functorPushforward] at hf
  rcases hf with ⟨Y, h, g, hg, rfl⟩
  have hfrac :
      fractionInDilatation Z ⟨i, ⟨Y, ⟨h, hg⟩⟩⟩ ≫
          (CatToDila Z).map (Z.mor i)
      =
      (CatToDila Z).map h := by
    apply Quotient.sound
    simp only [DilaRel,
      CatToDila,
      GeneratedToLocalization,
      forgetGenerator,
      ]
    change
      fractionInLocalization Z ⟨i, ⟨Y, ⟨h, hg⟩⟩⟩ ≫
          (CenterMorphismProperty Z).Q.map (Z.mor i)
        =
      (CenterMorphismProperty Z).Q.map h
    exact fraction_comp_mor Z i Y h hg
  refine ⟨
      (CatToDila Z).obj (Z.dom i),
      g ≫ fractionInDilatation Z ⟨i, ⟨Y, ⟨h, hg⟩⟩⟩,
      (CatToDila Z).map (Z.mor i),
      Presieve.singleton_self _,
      ?_
    ⟩
  calc
    (g ≫ fractionInDilatation Z ⟨i, ⟨Y, ⟨h, hg⟩⟩⟩) ≫
        (CatToDila Z).map (Z.mor i)
        =
        g ≫
          (fractionInDilatation Z ⟨i, ⟨Y, ⟨h, hg⟩⟩⟩ ≫
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

end CategoryTheory.Dilatations

/-! ## The universal property -/

namespace CategoryTheory.Dilatations

variable {C : Type u} [Category.{v} C]
variable (Z : Center C)
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

/-- The morphism property consisting of the images of the chosen denominators. -/
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
  have :
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

/-- The unique factor of a mapped numerator through its mapped denominator. -/
def uniqueFactor
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

/-- Interpret each original or fraction generator in a sieve-compatible target category. -/
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
      uniqueFactor Z F hfaith hsieve
        hw.p.1
        hw.p.2.1
        hw.p.2.2.1
        hw.p.2.2.2
  | original hw =>
      exact F.map hw.g

/-- The functor between localizations induced by the original functor. -/
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

/-- The prefunctor interpreting dilatation generators in the target category. -/
def generatorImage
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

/-- Extend the generator interpretation to paths by the free-category universal property. -/
def H
    (hfaith :
      (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate
            (Presieve.singleton (F.map (Z.mor i)))) :
    GeneratedCategory Z ⥤ D :=
  Paths.lift (generatorImage Z F hfaith hsieve)

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
  exact (Paths.lift_toPath (generatorImage Z F hfaith hsieve) ((CToGeneratorQuiver Z).map f)).trans
    (mapGenerator_original Z F hfaith hsieve f)

lemma uniqueFactor_spec
    (hfaith : (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve : ∀ (i : Z.I),
      Sieve.functorPushforward F (Z.N i) ≤
        Sieve.generate (Presieve.singleton (F.map (Z.mor i))))
    (i : Z.I) (Y : C) (n : Y ⟶ Z.cod i) (hn : Z.N i n) :
    uniqueFactor Z F hfaith hsieve i Y n hn ≫ F.map (Z.mor i) = F.map n := by
  unfold uniqueFactor
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
          (fractionInPath Z p)⟩)
    (hgf : gf = fractionInLocalization Z p) :
    (H Z F hfaith hsieve).map
        (Quiver.Hom.toPath
          (⟨gf, GeneratorMorphismData.fraction ⟨p, heq⟩⟩ :
            (GeneratorQuiver Z).Hom _ _)) =
      eqToHom (congrArg F.obj (Equiv.symm_apply_apply (objEquiv (CenterMorphismProperty Z))
        p.2.1)) ≫
        uniqueFactor Z F hfaith hsieve p.1 p.2.1 p.2.2.1 p.2.2.2 ≫
        eqToHom (congrArg F.obj
          (Equiv.symm_apply_apply (objEquiv (CenterMorphismProperty Z)) (Z.dom p.1))).symm := by
  subst hgf
  apply (conj_eqToHom_iff_heq _ _ _ _).2
  · change HEq ((Paths.lift (generatorImage Z F hfaith hsieve)).map
        (Quiver.Hom.toPath
          (⟨fractionInLocalization Z p, GeneratorMorphismData.fraction ⟨p, heq⟩⟩ :
            (GeneratorQuiver Z).Hom _ _)))
      (uniqueFactor Z F hfaith hsieve p.1 p.2.1 p.2.2.1 p.2.2.2)
    rw [Paths.lift_toPath (generatorImage Z F hfaith hsieve)
      (⟨fractionInLocalization Z p, GeneratorMorphismData.fraction ⟨p, heq⟩⟩ :
        (GeneratorQuiver Z).Hom _ _)]
    change HEq (mapGenerator Z F hfaith hsieve
        (⟨fractionInLocalization Z p, GeneratorMorphismData.fraction ⟨p, heq⟩⟩ :
          (GeneratorQuiver Z).Hom _ _))
      (uniqueFactor Z F hfaith hsieve p.1 p.2.1 p.2.2.1 p.2.2.2)
    unfold mapGenerator
    simp
  all_goals
    dsimp only [H, generatorImage, Paths.lift]
    rw [Equiv.symm_apply_apply]

/-- `GeneratedToLocalization` sends a `fraction` generator to `fractionInLocalization`. -/
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
          (fractionInPath Z p)⟩)
    (hgf : gf = fractionInLocalization Z p) :
    (GeneratedToLocalization Z).map
        (Quiver.Hom.toPath
          (⟨gf, GeneratorMorphismData.fraction ⟨p, heq⟩⟩ :
            (GeneratorQuiver Z).Hom _ _)) =
      fractionInLocalization Z p := by
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
  exact (Paths.lift_toPath (generatorImage Z F hfaith hsieve)
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

/-- Core cancellation step for the `fraction` case : matching the two sides of
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
        (uniqueFactor Z F hfaith hsieve i X n hn) =
      eqToHom (hobj (objEquiv (CenterMorphismProperty Z) X)) ≫
        (localizationMap Z F).map (fractionInLocalization Z ⟨i, ⟨X, ⟨n, hn⟩⟩⟩) ≫
        eqToHom (hobj (objEquiv (CenterMorphismProperty Z) (Z.dom i))).symm := by
  have : IsIso ((ImageCenterLocalizationFunctor Z F).map (F.map (Z.mor i))) :=
    MorphismProperty.Q_inverts _ _ ⟨i, rfl⟩
  change (ImageCenterLocalizationFunctor Z F).map
      (uniqueFactor Z F hfaith hsieve i X n hn) =
    𝟙 _ ≫ (localizationMap Z F).map (fractionInLocalization Z ⟨i, X, n, hn⟩) ≫ 𝟙 _
  erw [Category.id_comp, Category.comp_id]
  have hmap {A B : C} (g : A ⟶ B) :
      (localizationMap Z F).map ((CenterMorphismProperty Z).Q.map g) =
        (ImageCenterLocalizationFunctor Z F).map (F.map g) := by
    have h := Functor.congr_hom (localizationMap_comp_Q Z F) g
    simpa only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] using! h
  apply (cancel_mono ((ImageCenterLocalizationFunctor Z F).map (F.map (Z.mor i)))).mp
  rw [← Functor.map_comp, uniqueFactor_spec]
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
        have hgf : gf = fractionInLocalization Z ⟨i, ⟨X, ⟨n, hn⟩⟩⟩ := by
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
`Θ = CatToDila Z`, built structurally : the generator-by-generator choice `generatorImage`,
    lifted to the
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

/-- Sigma-regularity makes every mapped denominator a monomorphism. -/
lemma imageCenter_mono
    (hfaith : (ImageCenterLocalizationFunctor Z F).Faithful) (i : Z.I) :
    Mono (F.map (Z.mor i)) := by
  have := hfaith
  have : IsIso ((ImageCenterLocalizationFunctor Z F).map (F.map (Z.mor i))) :=
    MorphismProperty.Q_inverts (ImageCenterMorphismProperty Z F) _ ⟨i, rfl⟩
  exact (ImageCenterLocalizationFunctor Z F).mono_of_mono_map inferInstance

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
        (fractionInDilatation Z
          ⟨i, ⟨X, ⟨n, hn⟩⟩⟩)
      =
      eqToHom (by
        have := congrArg (fun H => H.obj X)
          (Dila_factor_unique_on_C Z F G₁ G₂ h₁ h₂)
        exact this)
      ≫
      G₂.map
        (fractionInDilatation Z ⟨i, ⟨X, ⟨n, hn⟩⟩⟩)
      ≫
      eqToHom (by
        have := congrArg (fun H => H.obj (Z.dom i))
          (Dila_factor_unique_on_C Z F G₁ G₂ h₁ h₂)
        exact this.symm) :=  by
  intro i X n hn
  have : Mono (G₁.map ((CatToDila Z).map (Z.mor i))) := by
    change Mono ((CatToDila Z ⋙ G₁).map (Z.mor i))
    rw [h₁]
    exact imageCenter_mono Z F hfaith i
  apply (cancel_mono (G₁.map ((CatToDila Z).map (Z.mor i)))).mp
  rw [← Functor.map_comp, fraction_in_dila_comp_mor]
  rw [map_eq_of_agree_on_C Z F G₁ G₂ h₁ h₂ n,
    map_eq_of_agree_on_C Z F G₁ G₂ h₁ h₂ (Z.mor i)]
  have hfactor := congrArg G₂.map (fraction_in_dila_comp_mor Z i X n hn)
  simp only [Functor.map_comp] at hfactor
  rw [← hfactor]
  simp [Category.assoc]


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

lemma Generated_factor_unique_generator
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
          (fractionInDilatation Z ⟨i, ⟨X, ⟨n, hn⟩⟩⟩)
        =
        eqToHom (h_obj ((CatToDila Z).obj X)) ≫
          G₂.map
            (fractionInDilatation Z ⟨i, ⟨X, ⟨n, hn⟩⟩⟩) ≫
          eqToHom (h_obj ((CatToDila Z).obj (Z.dom i))).symm)
    {A B : GeneratorObjects Z} (g : (GeneratorQuiver Z).Hom A B) :
    G₁.map ((GeneratedToDila Z).map (Quiver.Hom.toPath g)) =
      eqToHom (h_obj ((GeneratedToDila Z).obj A)) ≫
        G₂.map ((GeneratedToDila Z).map (Quiver.Hom.toPath g)) ≫
        eqToHom (h_obj ((GeneratedToDila Z).obj B)).symm := by
  rcases g.2 with h | h
  · -- fraction case : h : PairMorWitness Z g.fst
    obtain ⟨p, heq⟩ := h
    have hA : A = objEquiv (CenterMorphismProperty Z) p.2.1 :=
      congrArg Sigma.fst heq
    have hB : B = objEquiv (CenterMorphismProperty Z) (Z.dom p.1) := by
      exact congrArg (fun s => s.2.1) heq
    subst hA
    subst hB
    have hg1 : g.1 = fractionInLocalization Z p := by
      simp only [Sigma.mk.injEq, heq_eq_eq] at heq
      exact eq_of_heq (Sigma.mk.inj heq.2).2
    have hgg :
        (GeneratedToDila Z).map (Quiver.Hom.toPath g) =
          fractionInDilatation Z p :=
      GeneratorQuiver_Hom_ext Z g (fractionGenerator Z p) hg1
    rw [hgg]
    obtain ⟨i, X, n, hn⟩ := p
    exact h_fraction i X n hn
  · -- original case : h : OriginalWitness Z g.fst
    have hgg :
        (GeneratedToDila Z).map (Quiver.Hom.toPath g) =
          (CatToDila Z).map h.g :=
      GeneratorQuiver_Hom_ext Z g ((CToGeneratorQuiver Z).map h.g) h.eq
    rw [hgg]
    exact h_mor h.g

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
          (fractionInDilatation Z ⟨i, ⟨X, ⟨n, hn⟩⟩⟩)
        =
        eqToHom (h_obj ((CatToDila Z).obj X)) ≫
          G₂.map
            (fractionInDilatation Z ⟨i, ⟨X, ⟨n, hn⟩⟩⟩) ≫
          eqToHom (h_obj ((CatToDila Z).obj (Z.dom i))).symm)
    {X Y : Dila Z}
    (f : X ⟶ Y) :
    G₁.map f =
      eqToHom (h_obj X) ≫
        G₂.map f ≫
        eqToHom (h_obj Y).symm := by
  let : (GeneratedToDila Z).Full := GeneratedToDila_full Z
  obtain ⟨g, rfl⟩ := (GeneratedToDila Z).map_surjective f
  let P :=
    fun {A B : GeneratedCategory Z} (k : A ⟶ B) =>
      G₁.map ((GeneratedToDila Z).map k) =
        eqToHom (h_obj ((GeneratedToDila Z).obj A)) ≫
          G₂.map ((GeneratedToDila Z).map k) ≫
          eqToHom (h_obj ((GeneratedToDila Z).obj B)).symm
  change P g
  apply GeneratedCategory_morphism_induction Z P
  · intro A
    simp [P]
  · intro A B C f g hf hg
    dsimp [P] at *
    simp [Functor.map_comp, hf, hg, Category.assoc]
  · intro A B g
    dsimp [P]
    exact Generated_factor_unique_generator Z G₁ G₂ h_obj h_mor h_fraction g

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
  have h_obj : ∀ X : Dila Z, G₁.obj X = G₂.obj X := by
    intro X
    obtain ⟨Y, rfl⟩ := Dila_obj_eq_C_obj Z X
    exact congrArg (fun H : C ⥤ D => H.obj Y) (h₁.trans h₂.symm)
  refine Functor.ext h_obj ?_
  intro X Y f
  exact Generated_factor_unique_map Z G₁ G₂ h_obj
    (fun g => map_eq_of_agree_on_C Z F G₁ G₂ h₁ h₂ g)
    (fun i X n hn => Dila_factor_unique_fraction Z F G₁ G₂ hfaith h₁ h₂ i X n hn) f

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

/-- **Definition 3.6.** `F : C ⥤ D` is `Σ`-regular (`F ∈ Cat ^ Σ-reg_C`) if `D → D[F(Σ)⁻¹]` is
faithful. -/
def IsSigmaRegular : Prop :=
  Functor.Faithful (ImageCenterMorphismProperty Z F).Q

/-- If `p ⋙ e` is faithful, then `p` is faithful. This is the elementary categorical fact behind
both Fact 3.7 and Fact 3.8 : a functor that factors (on the target side) through a faithful
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
  change (ImageCenterLocalizationFunctor Z (CatToDila Z)).Faithful
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
        simp only [Functor.comp_map] at hkey
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

end CategoryTheory.Dilatations
