/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ExactFromShort

/-!
# Exactness of the fibre functor from a base-change section

A short exact sequence of an abelian category does not split, so
the splitting hypothesis of `RS.fibreFun_shortExact` is never
available as stated.  What Deligne's 2.10 supplies — in the form
recorded by `RS.Rappel210Statement` — is weaker and is exactly what
is needed: a section of the epimorphism *after base change*, that
is, a morphism of module objects
`s : freeMod R S.X₃ ⟶ freeMod R S.X₂` splitting `freeModMap R S.g`.

This module derives short exactness of the realised sequence from
that hypothesis alone.  The route is:

* base change is exact, so `S.map (tensorLeft R)` is short exact
  whenever `S` is (`RS.shortExact_map_tensorLeft`);
* a section of a short exact sequence produces a retraction
  (Mathlib's `ShortComplex.Splitting.ofExactOfSection`), and that
  retraction is again a morphism of module objects — the content of
  `RS.baseChangeRetraction_lin`, proved by cancelling the
  monomorphism `R ◁ S.f`, past which the intertwining law of the
  retraction becomes the intertwining law of the complement of
  `(R ◁ S.g) ≫ s`, a composite of module maps;
* realisation is a functor and turns sums of module morphisms into
  sums, so the three splitting identities transport to the super
  modules, where a split short complex is short exact.

The category of module objects carries no additive structure, so
the transported splitting is assembled by hand rather than through
`ShortComplex.Splitting.map`; `RS.gammaModuleFunctor_map_add` is
the one additivity statement this needs, phrased on underlying
morphisms.

Exactness of base change is assumed as an instance hypothesis on
the ambient category; for `Ind C` it is supplied by
`RS.tensorLeft_ind_preservesFiniteLimits` and its colimit
counterpart.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

/-! ## Intertwining laws in raw tensor form -/

section Raw

variable {D : Type u}

/-- **The underlying morphism of a map of free modules intertwines
the free actions**, in raw tensor form. -/
theorem freeMod_hom_lin [Category.{v} D] [MonoidalCategory D] (R : D) [MonObj R]
    {V W : D} (f : freeMod R V ⟶ freeMod R W) :
    ((α_ R R V).inv ≫ (μ[R] ▷ V)) ≫ Mod.Hom.hom f =
      (R ◁ Mod.Hom.hom f) ≫ ((α_ R R W).inv ≫ (μ[R] ▷ W)) :=
  (Mod.Hom.isModHom f).smul_hom

section Complement

/-- **The complement of a module endomorphism is a module map.**
Let `f` be a monomorphism intertwining the free actions, let `c` be
an endomorphism intertwining them, and let `u` satisfy
`u ≫ f + c = 𝟙`.  Then `u` intertwines the free actions as well:
the law for `u` is checked after `f`, where it becomes the law for
`𝟙 - c`.  This is the crux of the whole module. -/
theorem lin_of_complement
    [Category.{v} D] [MonoidalCategory D] (R : D) [MonObj R] [Preadditive D]
    [MonoidalPreadditive D]
    {V W : D} (f : R ⊗ V ⟶ R ⊗ W) [Mono f]
    (hf : ((α_ R R V).inv ≫ (μ[R] ▷ V)) ≫ f =
      (R ◁ f) ≫ ((α_ R R W).inv ≫ (μ[R] ▷ W)))
    (u : R ⊗ W ⟶ R ⊗ V) (c : R ⊗ W ⟶ R ⊗ W)
    (hc : ((α_ R R W).inv ≫ (μ[R] ▷ W)) ≫ c =
      (R ◁ c) ≫ ((α_ R R W).inv ≫ (μ[R] ▷ W)))
    (hid : u ≫ f + c = 𝟙 (R ⊗ W)) :
    ((α_ R R W).inv ≫ (μ[R] ▷ W)) ≫ u =
      (R ◁ u) ≫ ((α_ R R V).inv ≫ (μ[R] ▷ V)) := by
  rw [← cancel_mono f]
  have hR : ((R ◁ u) ≫ ((α_ R R V).inv ≫ (μ[R] ▷ V))) ≫ f =
      (R ◁ (u ≫ f)) ≫ ((α_ R R W).inv ≫ (μ[R] ▷ W)) := by
    rw [Category.assoc, hf, ← Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp]
  rw [Category.assoc, hR]
  have hsum : ((α_ R R W).inv ≫ (μ[R] ▷ W)) ≫ (u ≫ f) +
        ((α_ R R W).inv ≫ (μ[R] ▷ W)) ≫ c =
      (R ◁ (u ≫ f)) ≫ ((α_ R R W).inv ≫ (μ[R] ▷ W)) +
        (R ◁ c) ≫ ((α_ R R W).inv ≫ (μ[R] ▷ W)) := by
    rw [← Preadditive.comp_add, ← Preadditive.add_comp,
      ← MonoidalPreadditive.whiskerLeft_add, hid,
      MonoidalCategory.whiskerLeft_id, Category.comp_id,
      Category.id_comp]
  rw [hc] at hsum
  exact add_right_cancel hsum

end Complement

end Raw

/-! ## The retraction produced by a base-change section -/

section BaseChange

variable {D : Type u}

/-- **Base change of a short exact sequence is short exact.**
Tensoring is exact, so the whiskered sequence is again short
exact. -/
theorem shortExact_map_tensorLeft
    [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D] [∀ Z : D, PreservesFiniteLimits (tensorLeft Z)]
    [∀ Z : D, PreservesFiniteColimits (tensorLeft Z)] (R : D)
    {S : CategoryTheory.ShortComplex D} (hS : S.ShortExact) :
    (S.map (tensorLeft R)).ShortExact :=
  hS.map_of_exact (tensorLeft R)

/-- The underlying morphism of a module-level section, in raw
tensor form. -/
def baseChangeSectionHom
    [Category.{v} D] [MonoidalCategory D] [Abelian D] (R : D) [MonObj R]
    {S : CategoryTheory.ShortComplex D}
    (s : freeMod R S.X₃ ⟶ freeMod R S.X₂) :
    R ⊗ S.X₃ ⟶ R ⊗ S.X₂ :=
  Mod.Hom.hom s

/-- A module-level section splits the base-changed epimorphism. -/
theorem baseChangeSectionHom_g
    [Category.{v} D] [MonoidalCategory D] [Abelian D] (R : D) [MonObj R]
    {S : CategoryTheory.ShortComplex D}
    (s : freeMod R S.X₃ ⟶ freeMod R S.X₂)
    (hs : s ≫ freeModMap R S.g = 𝟙 (freeMod R S.X₃)) :
    baseChangeSectionHom R s ≫ (R ◁ S.g) = 𝟙 (R ⊗ S.X₃) :=
  congrArg Mod.Hom.hom hs

/-- The splitting of the base-changed sequence determined by a
module-level section of the epimorphism. -/
noncomputable def baseChangeSplitting
    [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D] [∀ Z : D, PreservesFiniteLimits (tensorLeft Z)]
    [∀ Z : D, PreservesFiniteColimits (tensorLeft Z)] (R : D) [MonObj R]
    {S : CategoryTheory.ShortComplex D}
    (hS : S.ShortExact)
    (s : freeMod R S.X₃ ⟶ freeMod R S.X₂)
    (hs : s ≫ freeModMap R S.g = 𝟙 (freeMod R S.X₃)) :
    (S.map (tensorLeft R)).Splitting :=
  CategoryTheory.ShortComplex.Splitting.ofExactOfSection
    (S.map (tensorLeft R)) (shortExact_map_tensorLeft R hS).exact
    (baseChangeSectionHom R s) (baseChangeSectionHom_g R s hs)
    (shortExact_map_tensorLeft R hS).mono_f

/-- The retraction of the base-changed sequence, in raw tensor
form. -/
noncomputable def baseChangeRetractionHom
    [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D] [∀ Z : D, PreservesFiniteLimits (tensorLeft Z)]
    [∀ Z : D, PreservesFiniteColimits (tensorLeft Z)] (R : D) [MonObj R]
    {S : CategoryTheory.ShortComplex D}
    (hS : S.ShortExact)
    (s : freeMod R S.X₃ ⟶ freeMod R S.X₂)
    (hs : s ≫ freeModMap R S.g = 𝟙 (freeMod R S.X₃)) :
    R ⊗ S.X₂ ⟶ R ⊗ S.X₁ :=
  (baseChangeSplitting R hS s hs).r

/-- The retraction retracts the base-changed monomorphism. -/
theorem baseChangeRetractionHom_f
    [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D] [∀ Z : D, PreservesFiniteLimits (tensorLeft Z)]
    [∀ Z : D, PreservesFiniteColimits (tensorLeft Z)] (R : D) [MonObj R]
    {S : CategoryTheory.ShortComplex D}
    (hS : S.ShortExact)
    (s : freeMod R S.X₃ ⟶ freeMod R S.X₂)
    (hs : s ≫ freeModMap R S.g = 𝟙 (freeMod R S.X₃)) :
    (R ◁ S.f) ≫ baseChangeRetractionHom R hS s hs =
      𝟙 (R ⊗ S.X₁) :=
  (baseChangeSplitting R hS s hs).f_r

/-- The retraction and the section are complementary. -/
theorem baseChangeRetractionHom_id
    [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D] [∀ Z : D, PreservesFiniteLimits (tensorLeft Z)]
    [∀ Z : D, PreservesFiniteColimits (tensorLeft Z)] (R : D) [MonObj R]
    {S : CategoryTheory.ShortComplex D}
    (hS : S.ShortExact)
    (s : freeMod R S.X₃ ⟶ freeMod R S.X₂)
    (hs : s ≫ freeModMap R S.g = 𝟙 (freeMod R S.X₃)) :
    baseChangeRetractionHom R hS s hs ≫ (R ◁ S.f) +
        (R ◁ S.g) ≫ baseChangeSectionHom R s =
      𝟙 (R ⊗ S.X₂) :=
  (baseChangeSplitting R hS s hs).id

/-- **The retraction is a morphism of module objects.** -/
theorem baseChangeRetraction_lin
    [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D] [∀ Z : D, PreservesFiniteLimits (tensorLeft Z)]
    [∀ Z : D, PreservesFiniteColimits (tensorLeft Z)] (R : D) [MonObj R]
    {S : CategoryTheory.ShortComplex D}
    (hS : S.ShortExact)
    (s : freeMod R S.X₃ ⟶ freeMod R S.X₂)
    (hs : s ≫ freeModMap R S.g = 𝟙 (freeMod R S.X₃)) :
    ((α_ R R S.X₂).inv ≫ (μ[R] ▷ S.X₂)) ≫
        baseChangeRetractionHom R hS s hs =
      (R ◁ baseChangeRetractionHom R hS s hs) ≫
        ((α_ R R S.X₁).inv ≫ (μ[R] ▷ S.X₁)) := by
  have : Mono (R ◁ S.f) := (shortExact_map_tensorLeft R hS).mono_f
  exact lin_of_complement R (R ◁ S.f) (freeModMap_lin R S.f)
    (baseChangeRetractionHom R hS s hs)
    ((R ◁ S.g) ≫ baseChangeSectionHom R s)
    (freeMod_hom_lin R (freeModMap R S.g ≫ s))
    (baseChangeRetractionHom_id R hS s hs)

/-- **The retraction, as a morphism of module objects.** -/
noncomputable def baseChangeRetraction
    [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D] [∀ Z : D, PreservesFiniteLimits (tensorLeft Z)]
    [∀ Z : D, PreservesFiniteColimits (tensorLeft Z)] (R : D) [MonObj R]
    {S : CategoryTheory.ShortComplex D}
    (hS : S.ShortExact)
    (s : freeMod R S.X₃ ⟶ freeMod R S.X₂)
    (hs : s ≫ freeModMap R S.g = 𝟙 (freeMod R S.X₃)) :
    freeMod R S.X₂ ⟶ freeMod R S.X₁ :=
  Mod.Hom.mk' (baseChangeRetractionHom R hS s hs)
    (baseChangeRetraction_lin R hS s hs)

/-- The module retraction retracts the base change of the
monomorphism. -/
theorem freeModMap_baseChangeRetraction
    [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D] [∀ Z : D, PreservesFiniteLimits (tensorLeft Z)]
    [∀ Z : D, PreservesFiniteColimits (tensorLeft Z)] (R : D) [MonObj R]
    {S : CategoryTheory.ShortComplex D}
    (hS : S.ShortExact)
    (s : freeMod R S.X₃ ⟶ freeMod R S.X₂)
    (hs : s ≫ freeModMap R S.g = 𝟙 (freeMod R S.X₃)) :
    freeModMap R S.f ≫ baseChangeRetraction R hS s hs =
      𝟙 (freeMod R S.X₁) :=
  Mod.hom_ext _ _ (baseChangeRetractionHom_f R hS s hs)

/-- The module retraction and the module section are
complementary, read on underlying morphisms. -/
theorem baseChangeRetraction_id
    [Category.{v} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D] [∀ Z : D, PreservesFiniteLimits (tensorLeft Z)]
    [∀ Z : D, PreservesFiniteColimits (tensorLeft Z)] (R : D) [MonObj R]
    {S : CategoryTheory.ShortComplex D}
    (hS : S.ShortExact)
    (s : freeMod R S.X₃ ⟶ freeMod R S.X₂)
    (hs : s ≫ freeModMap R S.g = 𝟙 (freeMod R S.X₃)) :
    Mod.Hom.hom (baseChangeRetraction R hS s hs ≫ freeModMap R S.f)
        + Mod.Hom.hom (freeModMap R S.g ≫ s) =
      Mod.Hom.hom (𝟙 (freeMod R S.X₂)) :=
  baseChangeRetractionHom_id R hS s hs

end BaseChange

/-! ## Transport to the super modules -/

section Fibre

variable {D : Type u}

/-- **Realisation turns a sum of module morphisms into a sum.**
The category of module objects has no additive structure, so the
hypothesis is stated on underlying morphisms. -/
theorem gammaModuleFunctor_map_add
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    [MonoidalPreadditive D] [Linear ℂ D] [MonoidalLinear ℂ D]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    {M N : Mod D R} (f g h : M ⟶ N)
    (hfg : Mod.Hom.hom f + Mod.Hom.hom g = Mod.Hom.hom h) :
    (gammaModuleFunctor L R).map f +
        (gammaModuleFunctor L R).map g =
      (gammaModuleFunctor L R).map h := by
  refine SuperCommAlgebra.Mod.Hom.ext ?_ ?_ <;>
    refine LinearMap.ext fun m => ?_ <;>
    · change m ≫ Mod.Hom.hom f + m ≫ Mod.Hom.hom g =
        m ≫ Mod.Hom.hom h
      erw [← Preadditive.comp_add, hfg]

section Splitting

/-- **The splitting of the realised sequence.**  Its retraction and
section are the realisations of the module retraction and of the
given module section; the three identities are the images of the
corresponding identities in the category of module objects. -/
noncomputable def fibreFunSplitting
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    [MonoidalPreadditive D] [Linear ℂ D] [MonoidalLinear ℂ D]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    [∀ Z : D, PreservesFiniteLimits (tensorLeft Z)]
    [∀ Z : D, PreservesFiniteColimits (tensorLeft Z)]
    {S : CategoryTheory.ShortComplex D}
    (hS : S.ShortExact)
    (s : freeMod R S.X₃ ⟶ freeMod R S.X₂)
    (hs : s ≫ freeModMap R S.g = 𝟙 (freeMod R S.X₃)) :
    (S.map (fibreFun L R)).Splitting where
  r := (gammaModuleFunctor L R).map (baseChangeRetraction R hS s hs)
  s := (gammaModuleFunctor L R).map s
  f_r := by
    change (gammaModuleFunctor L R).map (freeModMap R S.f) ≫
        (gammaModuleFunctor L R).map
          (baseChangeRetraction R hS s hs) = _
    rw [← CategoryTheory.Functor.map_comp,
      freeModMap_baseChangeRetraction R hS s hs]
    exact CategoryTheory.Functor.map_id _ _
  s_g := by
    change (gammaModuleFunctor L R).map s ≫
        (gammaModuleFunctor L R).map (freeModMap R S.g) = _
    rw [← CategoryTheory.Functor.map_comp, hs]
    exact CategoryTheory.Functor.map_id _ _
  id := by
    change (gammaModuleFunctor L R).map
          (baseChangeRetraction R hS s hs) ≫
          (gammaModuleFunctor L R).map (freeModMap R S.f) +
        (gammaModuleFunctor L R).map (freeModMap R S.g) ≫
          (gammaModuleFunctor L R).map s = _
    rw [← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp]
    refine Eq.trans (gammaModuleFunctor_map_add L R _ _
      (𝟙 (freeMod R S.X₂)) (baseChangeRetraction_id R hS s hs)) ?_
    exact CategoryTheory.Functor.map_id _ _

/-- **The fibre functor carries a short exact sequence with a
base-change section to a short exact sequence of super modules.**
No section in the ambient category is required: a section of the
base-changed epimorphism as a map of module objects suffices. -/
theorem fibreFun_shortExact_of_baseChangeSection
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    [MonoidalPreadditive D] [Linear ℂ D] [MonoidalLinear ℂ D]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    [∀ Z : D, PreservesFiniteLimits (tensorLeft Z)]
    [∀ Z : D, PreservesFiniteColimits (tensorLeft Z)]
    {S : CategoryTheory.ShortComplex D} (hS : S.ShortExact)
    (s : freeMod R S.X₃ ⟶ freeMod R S.X₂)
    (hs : s ≫ freeModMap R S.g = 𝟙 (freeMod R S.X₃)) :
    (S.map (fibreFun L R)).ShortExact :=
  (fibreFunSplitting L R hS s hs).shortExact

end Splitting

end Fibre

end RS
