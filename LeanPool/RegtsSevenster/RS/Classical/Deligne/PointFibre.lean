/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.FibreOverComplex
import LeanPool.RegtsSevenster.RS.Classical.Deligne.FibreOverSplitting

/-!
# The fibre functor into super vector spaces

Base change along a ℂ-point of the Γ-algebra turns each super
module into a finite-dimensional super vector space
(`RS.toSuperVect` of
[PointBaseChange.lean](PointBaseChange.lean)).  This module
upgrades that assignment to a functor, records its exactness, and
assembles the fibre functor of Deligne's theorem out of the fibre
functor over a splitting algebra and a ℂ-point of its Γ-algebra.

Three things are needed for the assembly and are established here.

* *Super vector spaces are an abelian category.*  A super vector
  space is a `Bool`-indexed family of finite-dimensional complex
  vector spaces, and a morphism is a family of linear maps, so
  `RS.SuperVect` is equivalent to the category of functors from the
  discrete category on `Bool` to `FGModuleCat ℂ`.  That functor
  category is abelian, and abelianness transports along an
  equivalence.  This is what lets the exactness criterion
  `RS.preservesFiniteLimits_of_shortExact` be applied to a functor
  landing in `RS.SuperVect`.

* *Base change is functorial.*  Tensoring with the residue module
  of the point is a functor, and `RS.toSuperVect` replaces the two
  components of the result by coordinate spaces of the same
  dimensions; conjugating by the coordinate equivalences turns the
  first into a functor to `RS.SuperVect`.  The conjugation cancels
  in a composite, which is functoriality, and is additive
  componentwise, which is additivity.

* *Exactness comes from freeness.*  Every module in the image of
  the fibre functor over a splitting algebra is free, so a short
  exact sequence of them splits, and base change carries the
  splitting across; a split short complex is short exact.

Faithfulness is then automatic: the functor is exact, so it carries
the image factorisation of a morphism to an image factorisation,
and an object whose fibre vanishes has both mixed ranks zero, hence
zero fibre already over the algebra, hence — the unit of the
algebra being a monomorphism — vanishes itself.

## Contents

* `RS.superVectComponents`, `RS.superVectAbelian`: the equivalence
  with the diagram category, and the abelian structure it
  transports.
* `RS.SuperCommAlgebra.Mod.instLinear`,
  `RS.SuperCommAlgebra.Mod.tensorHom_smul_left`: the ℂ-linear
  structure of the super modules, and ℂ-linearity of the tensor
  product in the left variable.
* `RS.superVectHom`: base change of a morphism of super modules,
  with `RS.superVectHom_id`, `superVectHom_comp`, `superVectHom_add`
  and `superVectHom_smul`.
* `RS.superVectFunctor`: the base-change functor at a ℂ-point, with
  `RS.superVectFunctor_additive` and
  `RS.superVectFunctor_linear`.
* `RS.finrank_superVectFunctor_even`, `finrank_superVectFunctor_odd`:
  the two dimensions of the base change of a free value.
* `RS.superVectSplitting`, `RS.superVectFunctor_shortExact`,
  `RS.superVectFunctor_preservesFiniteLimits`,
  `RS.superVectFunctor_preservesFiniteColimits`,
  `RS.superVectFunctor_preservesHomology`: exactness.
* `RS.deligneFibre`: the fibre functor of a splitting algebra at a
  point, with its additivity, exactness
  (`RS.deligneFibre_preservesFiniteLimits`,
  `deligneFibre_preservesFiniteColimits`) and faithfulness
  (`RS.deligneFibre_faithful`).
* `RS.exists_deligneFibre_of_point`: the four properties packaged.
-/
namespace RS

open CategoryTheory Limits
open SuperCommAlgebra (pointMod)
open SuperCommAlgebra.Mod

universe u v₂ u₂

/-! ## Super vector spaces form an abelian category

A super vector space is a `Bool`-indexed family of
finite-dimensional complex vector spaces, and a morphism is a
family of linear maps: the category is equivalent to the category
of functors from the discrete category on `Bool` to the
finite-dimensional complex vector spaces.  That functor category is
abelian, so `RS.SuperVect` is abelian too. -/

section SuperVectAbelian

/-- **The components of a super vector space**, as a functor to the
`Bool`-indexed diagrams of finite-dimensional complex vector
spaces. -/
noncomputable def superVectComponents :
    SuperVect ⥤ (Discrete Bool ⥤ FGModuleCat.{0} ℂ) where
  obj V := Discrete.functor fun b =>
    cond b (FGModuleCat.of ℂ V.odd) (FGModuleCat.of ℂ V.even)
  map f := Discrete.natTrans fun i =>
    match i with
    | ⟨true⟩ => FGModuleCat.ofHom f.oddMap
    | ⟨false⟩ => FGModuleCat.ofHom f.evenMap
  map_id V := by
    refine NatTrans.ext (funext fun i => ?_)
    obtain ⟨b⟩ := i
    cases b <;> rfl
  map_comp f g := by
    refine NatTrans.ext (funext fun i => ?_)
    obtain ⟨b⟩ := i
    cases b <;> rfl

instance superVectComponents_faithful : superVectComponents.Faithful where
  map_injective {_ _ f g} h := by
    refine SuperVect.hom_ext ?_ ?_
    · exact congrArg (fun α => (α.app ⟨false⟩).hom.hom) h
    · exact congrArg (fun α => (α.app ⟨true⟩).hom.hom) h

instance superVectComponents_full : superVectComponents.Full where
  map_surjective {_ _} α :=
    ⟨{ evenMap := (α.app ⟨false⟩).hom.hom
       oddMap := (α.app ⟨true⟩).hom.hom }, by
      refine NatTrans.ext (funext fun i => ?_)
      obtain ⟨b⟩ := i
      cases b <;> rfl⟩

instance superVectComponents_essSurj : superVectComponents.EssSurj where
  mem_essImage Φ :=
    ⟨{ even := Φ.obj ⟨false⟩
       odd := Φ.obj ⟨true⟩ },
      ⟨Discrete.natIso fun i =>
        match i with
        | ⟨true⟩ => Iso.refl _
        | ⟨false⟩ => Iso.refl _⟩⟩

instance superVectComponents_isEquivalence :
    superVectComponents.IsEquivalence :=
  ⟨superVectComponents_faithful, superVectComponents_full,
    superVectComponents_essSurj⟩

/-- Super vector spaces have finite products, transported along the
equivalence with the diagram category. -/
noncomputable instance : Limits.HasFiniteProducts SuperVect :=
  ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence
    superVectComponents⟩

/-- **Super vector spaces form an abelian category.** -/
noncomputable instance superVectAbelian : Abelian SuperVect :=
  abelianOfEquivalence superVectComponents

end SuperVectAbelian

/-! ## ℂ-linearity of the super modules over a super algebra

Morphisms of super modules already carry a scaling by complex
numbers; the module axioms and the bilinearity of composition hold
componentwise, so the category is ℂ-linear.  The tensor product is
ℂ-linear in each variable for the same reason. -/

namespace SuperCommAlgebra.Mod

variable {S : SuperCommAlgebra.{u, u}}

/-- Morphisms of super modules form a ℂ-module. -/
instance homModule (M N : S.Mod.{u, u, u, u}) : Module ℂ (M ⟶ N) where
  one_smul _ := Hom.ext (one_smul _ _) (one_smul _ _)
  mul_smul _ _ _ := Hom.ext (mul_smul _ _ _) (mul_smul _ _ _)
  smul_zero _ := Hom.ext (smul_zero _) (smul_zero _)
  smul_add _ _ _ := Hom.ext (smul_add _ _ _) (smul_add _ _ _)
  add_smul _ _ _ := Hom.ext (add_smul _ _ _) (add_smul _ _ _)
  zero_smul _ := Hom.ext (zero_smul _ _) (zero_smul _ _)

/-- **Super modules over a super algebra form a ℂ-linear
category.** -/
instance instLinear : CategoryTheory.Linear ℂ S.Mod.{u, u, u, u} where
  smul_comp _ _ _ c f g :=
    Hom.ext (LinearMap.comp_smul _ _ _) (LinearMap.comp_smul _ _ _)
  comp_smul _ _ _ f c g :=
    Hom.ext (LinearMap.smul_comp _ _ _) (LinearMap.smul_comp _ _ _)

variable {M N P Q : S.Mod.{u, u, u, u}}

/-- **The tensor product of super modules is ℂ-linear in the left
variable.** -/
theorem tensorHom_smul_left (c : ℂ) (f : M ⟶ P) (g : N ⟶ Q) :
    tensorHom (c • f) g = c • tensorHom f g := by
  refine hom_ext (fun m n => ?_) (fun m n => ?_) (fun m n => ?_)
    (fun m n => ?_) <;>
    simp only [tensorHom_evenMap_tmulEE, tensorHom_evenMap_tmulOO,
      tensorHom_oddMap_tmulEO, tensorHom_oddMap_tmulOE,
      smul_evenMap, smul_oddMap, LinearMap.smul_apply, map_smul]

/-- Tensoring on the right by a fixed module is ℂ-linear. -/
instance tensorRightFunctor_linear (N : S.Mod.{u, u, u, u}) :
    (tensorRightFunctor N).Linear ℂ where
  map_smul {_ _} f c := tensorHom_smul_left c f (𝟙 N)

end SuperCommAlgebra.Mod

section Transport

variable {S : SuperCommAlgebra.{u, u}} (P : SuperPoint S)
variable {M N Q : S.Mod.{u, u, u, u}}

/-- **Base change of a morphism of super modules along a ℂ-point.**
The morphism is tensored with the residue module and the result is
read in the coordinates that `RS.toSuperVect` installs on the two
components. -/
noncomputable def superVectHom
    [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).odd]
    (u : M ⟶ N) :
    toSuperVect P M ⟶ toSuperVect P N where
  evenMap := (toSuperVectEvenEquiv P N).toLinearMap ∘ₗ
    ((tensorRightFunctor (pointMod P)).map u).evenMap ∘ₗ
    (toSuperVectEvenEquiv P M).symm.toLinearMap
  oddMap := (toSuperVectOddEquiv P N).toLinearMap ∘ₗ
    ((tensorRightFunctor (pointMod P)).map u).oddMap ∘ₗ
    (toSuperVectOddEquiv P M).symm.toLinearMap

/-- Base change fixes the identity. -/
theorem superVectHom_id [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd] :
    superVectHom P (𝟙 M) = 𝟙 (toSuperVect P M) := by
  refine SuperVect.hom_ext ?_ ?_ <;> refine LinearMap.ext fun x => ?_
  · show (toSuperVectEvenEquiv P M)
      (((tensorRightFunctor (pointMod P)).map (𝟙 M)).evenMap
        ((toSuperVectEvenEquiv P M).symm x)) = x
    rw [CategoryTheory.Functor.map_id]
    exact (toSuperVectEvenEquiv P M).apply_symm_apply x
  · show (toSuperVectOddEquiv P M)
      (((tensorRightFunctor (pointMod P)).map (𝟙 M)).oddMap
        ((toSuperVectOddEquiv P M).symm x)) = x
    rw [CategoryTheory.Functor.map_id]
    exact (toSuperVectOddEquiv P M).apply_symm_apply x

/-- Base change respects composition: the conjugating equivalences
cancel. -/
theorem superVectHom_comp [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (Q.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (Q.tensor (pointMod P)).odd]
    (u : M ⟶ N) (v : N ⟶ Q) :
    superVectHom P (u ≫ v) = superVectHom P u ≫ superVectHom P v := by
  refine SuperVect.hom_ext ?_ ?_ <;> refine LinearMap.ext fun x => ?_
  · show (toSuperVectEvenEquiv P Q)
      (((tensorRightFunctor (pointMod P)).map (u ≫ v)).evenMap
        ((toSuperVectEvenEquiv P M).symm x)) = _
    rw [CategoryTheory.Functor.map_comp]
    show _ = (toSuperVectEvenEquiv P Q)
      (((tensorRightFunctor (pointMod P)).map v).evenMap
        ((toSuperVectEvenEquiv P N).symm ((toSuperVectEvenEquiv P N)
          (((tensorRightFunctor (pointMod P)).map u).evenMap
            ((toSuperVectEvenEquiv P M).symm x)))))
    rw [LinearEquiv.symm_apply_apply]
    rfl
  · show (toSuperVectOddEquiv P Q)
      (((tensorRightFunctor (pointMod P)).map (u ≫ v)).oddMap
        ((toSuperVectOddEquiv P M).symm x)) = _
    rw [CategoryTheory.Functor.map_comp]
    show _ = (toSuperVectOddEquiv P Q)
      (((tensorRightFunctor (pointMod P)).map v).oddMap
        ((toSuperVectOddEquiv P N).symm ((toSuperVectOddEquiv P N)
          (((tensorRightFunctor (pointMod P)).map u).oddMap
            ((toSuperVectOddEquiv P M).symm x)))))
    rw [LinearEquiv.symm_apply_apply]
    rfl

/-- Base change is additive. -/
theorem superVectHom_add [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).odd]
    (u v : M ⟶ N) :
    superVectHom P (u + v) = superVectHom P u + superVectHom P v := by
  refine SuperVect.hom_ext ?_ ?_ <;> refine LinearMap.ext fun x => ?_
  · show (toSuperVectEvenEquiv P N)
      (((tensorRightFunctor (pointMod P)).map (u + v)).evenMap
        ((toSuperVectEvenEquiv P M).symm x)) = _
    rw [CategoryTheory.Functor.map_add]
    show (toSuperVectEvenEquiv P N)
      ((((tensorRightFunctor (pointMod P)).map u).evenMap +
        ((tensorRightFunctor (pointMod P)).map v).evenMap)
        ((toSuperVectEvenEquiv P M).symm x)) = _
    exact map_add _ _ _
  · show (toSuperVectOddEquiv P N)
      (((tensorRightFunctor (pointMod P)).map (u + v)).oddMap
        ((toSuperVectOddEquiv P M).symm x)) = _
    rw [CategoryTheory.Functor.map_add]
    show (toSuperVectOddEquiv P N)
      ((((tensorRightFunctor (pointMod P)).map u).oddMap +
        ((tensorRightFunctor (pointMod P)).map v).oddMap)
        ((toSuperVectOddEquiv P M).symm x)) = _
    exact map_add _ _ _

/-- Base change is ℂ-linear. -/
theorem superVectHom_smul [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).odd]
    (c : ℂ) (u : M ⟶ N) :
    superVectHom P (c • u) = c • superVectHom P u := by
  refine SuperVect.hom_ext ?_ ?_ <;> refine LinearMap.ext fun x => ?_
  · show (toSuperVectEvenEquiv P N)
      (((tensorRightFunctor (pointMod P)).map (c • u)).evenMap
        ((toSuperVectEvenEquiv P M).symm x)) = _
    rw [CategoryTheory.Functor.map_smul]
    show (toSuperVectEvenEquiv P N)
      ((c • ((tensorRightFunctor (pointMod P)).map u).evenMap)
        ((toSuperVectEvenEquiv P M).symm x)) = _
    exact map_smul (toSuperVectEvenEquiv P N) c _
  · show (toSuperVectOddEquiv P N)
      (((tensorRightFunctor (pointMod P)).map (c • u)).oddMap
        ((toSuperVectOddEquiv P M).symm x)) = _
    rw [CategoryTheory.Functor.map_smul]
    show (toSuperVectOddEquiv P N)
      ((c • ((tensorRightFunctor (pointMod P)).map u).oddMap)
        ((toSuperVectOddEquiv P M).symm x)) = _
    exact map_smul (toSuperVectOddEquiv P N) c _

end Transport

section PointFunctor

variable {S : SuperCommAlgebra.{u, u}} (P : SuperPoint S) {E : Type u₂}

/-- **The base-change functor at a ℂ-point.**  Each value of `G` is
tensored with the residue module of the point and packaged as a
super vector space; each morphism is conjugated through the
coordinate equivalences. -/
noncomputable def superVectFunctor
    [Category.{v₂} E] (G : E ⥤ S.Mod.{u, u, u, u})
    (hE : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).even)
    (hO : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).odd) :
    E ⥤ SuperVect where
  obj X := @toSuperVect _ P (G.obj X) (hE X) (hO X)
  map {X Y} f :=
    @superVectHom _ P _ _ (hE X) (hO X) (hE Y) (hO Y) (G.map f)
  map_id X := by
    show @superVectHom _ P _ _ (hE X) (hO X) (hE X) (hO X)
      (G.map (𝟙 X)) = _
    rw [CategoryTheory.Functor.map_id]
    exact superVectHom_id P
  map_comp {X Y Z} f g := by
    show @superVectHom _ P _ _ (hE X) (hO X) (hE Z) (hO Z)
      (G.map (f ≫ g)) = _
    rw [CategoryTheory.Functor.map_comp]
    exact superVectHom_comp P _ _

@[simp] theorem superVectFunctor_obj
    [Category.{v₂} E] (G : E ⥤ S.Mod.{u, u, u, u})
    (hE : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).even)
    (hO : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).odd)
    (X : E) :
    (superVectFunctor P G hE hO).obj X =
      @toSuperVect _ P (G.obj X) (hE X) (hO X) := rfl

@[simp] theorem superVectFunctor_map
    [Category.{v₂} E] (G : E ⥤ S.Mod.{u, u, u, u})
    (hE : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).even)
    (hO : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).odd)
    {X Y : E} (f : X ⟶ Y) :
    (superVectFunctor P G hE hO).map f =
      @superVectHom _ P _ _ (hE X) (hO X) (hE Y) (hO Y)
        (G.map f) := rfl

/-! ## Additivity -/

/-- **The base-change functor is additive.** -/
instance superVectFunctor_additive
    [Category.{v₂} E] (G : E ⥤ S.Mod.{u, u, u, u})
    (hE : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).even)
    (hO : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).odd)
    [Preadditive E] [G.Additive] :
    (superVectFunctor P G hE hO).Additive where
  map_add {X Y f g} := by
    show @superVectHom _ P _ _ (hE X) (hO X) (hE Y) (hO Y)
      (G.map (f + g)) = _
    rw [CategoryTheory.Functor.map_add]
    exact superVectHom_add P _ _

/-- **The base-change functor is ℂ-linear.** -/
instance superVectFunctor_linear [Category.{v₂} E] (G : E ⥤ S.Mod.{u, u, u, u})
    (hE : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).even)
    (hO : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).odd)
    [Preadditive E]
    [CategoryTheory.Linear ℂ E] [G.Additive] [G.Linear ℂ] :
    (superVectFunctor P G hE hO).Linear ℂ where
  map_smul {X Y} f c := by
    show @superVectHom _ P _ _ (hE X) (hO X) (hE Y) (hO Y)
      (G.map (c • f)) = _
    rw [CategoryTheory.Functor.map_smul]
    exact superVectHom_smul P _ _

/-! ## Dimensions -/

/-- **The even dimension of the base change of a free value.**  If
`G` takes `X` to a free super module of rank `(p | q)` then the
even part of its base change has dimension `p`. -/
theorem finrank_superVectFunctor_even
    [Category.{v₂} E] (G : E ⥤ S.Mod.{u, u, u, u})
    (hE : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).even)
    (hO : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).odd)
    (X : E) (p q : ℕ)
    (e : G.obj X ≅ ⨁ fun i : Fin p ⊕ Fin q =>
      Sum.elim (fun _ => S.unitMod) (fun _ => shift S.unitMod) i) :
    Module.finrank ℂ ((superVectFunctor P G hE hO).obj X).even = p :=
  @finrank_toSuperVect_even_of_free _ P p q (G.obj X) e (hE X) (hO X)

/-- **The odd dimension of the base change of a free value.** -/
theorem finrank_superVectFunctor_odd
    [Category.{v₂} E] (G : E ⥤ S.Mod.{u, u, u, u})
    (hE : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).even)
    (hO : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).odd)
    (X : E) (p q : ℕ)
    (e : G.obj X ≅ ⨁ fun i : Fin p ⊕ Fin q =>
      Sum.elim (fun _ => S.unitMod) (fun _ => shift S.unitMod) i) :
    Module.finrank ℂ ((superVectFunctor P G hE hO).obj X).odd = q :=
  @finrank_toSuperVect_odd_of_free _ P p q (G.obj X) e (hE X) (hO X)

/-! ## Exactness -/

section Exact

/-- **A splitting of the image under `G` gives a splitting after
base change.**  All three terms are free over the Γ-algebra, so the
sequence splits before base change, and base change carries the
splitting across. -/
noncomputable def superVectSplitting
    [Category.{v₂} E] (G : E ⥤ S.Mod.{u, u, u, u})
    (hE : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).even)
    (hO : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).odd)
    [Abelian E] [G.Additive]
    (T : CategoryTheory.ShortComplex E) (σ : (T.map G).Splitting) :
    (T.map (superVectFunctor P G hE hO)).Splitting :=
  haveI : FiniteDimensional ℂ
    (((T.map G).X₁).tensor (pointMod P)).even := hE T.X₁
  haveI : FiniteDimensional ℂ
    (((T.map G).X₁).tensor (pointMod P)).odd := hO T.X₁
  haveI : FiniteDimensional ℂ
    (((T.map G).X₂).tensor (pointMod P)).even := hE T.X₂
  haveI : FiniteDimensional ℂ
    (((T.map G).X₂).tensor (pointMod P)).odd := hO T.X₂
  haveI : FiniteDimensional ℂ
    (((T.map G).X₃).tensor (pointMod P)).even := hE T.X₃
  haveI : FiniteDimensional ℂ
    (((T.map G).X₃).tensor (pointMod P)).odd := hO T.X₃
  { r := superVectHom P σ.r
    s := superVectHom P σ.s
    f_r :=
      Eq.trans (superVectHom_comp P (G.map T.f) σ.r).symm
        (Eq.trans (congrArg (superVectHom P) σ.f_r)
          (superVectHom_id P))
    s_g :=
      Eq.trans (superVectHom_comp P σ.s (G.map T.g)).symm
        (Eq.trans (congrArg (superVectHom P) σ.s_g)
          (superVectHom_id P))
    id := by
      refine Eq.trans (congrArg₂ (· + ·)
        (superVectHom_comp P σ.r (G.map T.f)).symm
        (superVectHom_comp P (G.map T.g) σ.s).symm) ?_
      exact Eq.trans (superVectHom_add P _ _).symm
        (Eq.trans (congrArg (superVectHom P) σ.id)
          (superVectHom_id P)) }

/-- **The base-change functor carries a split short exact sequence
to a short exact sequence.** -/
theorem superVectFunctor_shortExact
    [Category.{v₂} E] (G : E ⥤ S.Mod.{u, u, u, u})
    (hE : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).even)
    (hO : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).odd)
    [Abelian E] [G.Additive]
    (T : CategoryTheory.ShortComplex E) (σ : (T.map G).Splitting) :
    (T.map (superVectFunctor P G hE hO)).ShortExact :=
  (superVectSplitting P G hE hO T σ).shortExact

/-- **The base-change functor preserves finite limits** as soon as
every short exact sequence splits after `G`. -/
theorem superVectFunctor_preservesFiniteLimits
    [Category.{v₂} E] (G : E ⥤ S.Mod.{u, u, u, u})
    (hE : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).even)
    (hO : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).odd)
    [Abelian E] [G.Additive]
    (hsec : ∀ T : CategoryTheory.ShortComplex E, T.ShortExact →
      Nonempty ((T.map G).Splitting)) :
    Limits.PreservesFiniteLimits (superVectFunctor P G hE hO) :=
  preservesFiniteLimits_of_shortExact _ fun T hT =>
    superVectFunctor_shortExact P G hE hO T (hsec T hT).some

/-- **The base-change functor preserves finite colimits** under the
same hypothesis; with the previous statement it is exact. -/
theorem superVectFunctor_preservesFiniteColimits
    [Category.{v₂} E] (G : E ⥤ S.Mod.{u, u, u, u})
    (hE : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).even)
    (hO : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).odd)
    [Abelian E] [G.Additive]
    (hsec : ∀ T : CategoryTheory.ShortComplex E, T.ShortExact →
      Nonempty ((T.map G).Splitting)) :
    Limits.PreservesFiniteColimits (superVectFunctor P G hE hO) :=
  preservesFiniteColimits_of_shortExact _ fun T hT =>
    superVectFunctor_shortExact P G hE hO T (hsec T hT).some

/-- **The base-change functor preserves homology**, hence
monomorphisms and epimorphisms. -/
theorem superVectFunctor_preservesHomology
    [Category.{v₂} E] (G : E ⥤ S.Mod.{u, u, u, u})
    (hE : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).even)
    (hO : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).odd)
    [Abelian E] [G.Additive]
    (hsec : ∀ T : CategoryTheory.ShortComplex E, T.ShortExact →
      Nonempty ((T.map G).Splitting)) :
    (superVectFunctor P G hE hO).PreservesHomology :=
  preservesHomology_of_shortExact _ fun T hT =>
    superVectFunctor_shortExact P G hE hO T (hsec T hT).some

end Exact

end PointFunctor

/-! ## The fibre functor of a splitting algebra at a point -/

section Fibre

open MonoidalCategory
open scoped MonObj

universe v

variable {C : Type v}

/-- The restricted fibre functor is additive. -/
instance indFibre_additive
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [MonoidalPreadditive C] [CategoryTheory.Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)] (L : OddLine (Ind C)) (𝔸 : Ind C) [MonObj 𝔸]
    [IsCommMonObj 𝔸] :
    ((indOf : C ⥤ Ind C) ⋙ fibreFun L 𝔸).Additive :=
  haveI : (indOf (C := C)).Additive := indOf_additive
  inferInstance

/-- **The even part of the fibre of an embedded object at a point is
finite dimensional**, for an algebra splitting the embedding. -/
theorem finiteDimensional_indFibre_even
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [MonoidalPreadditive C] [CategoryTheory.Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)] (L : OddLine (Ind C)) (𝔸 : Ind C) [MonObj 𝔸]
    [IsCommMonObj 𝔸]
    (hsp : SplitsOn L 𝔸 (indOf : C ⥤ Ind C))
    (P : SuperPoint (gammaAlgebra (Ind C) L 𝔸)) (X : C) :
    FiniteDimensional ℂ
      ((((indOf : C ⥤ Ind C) ⋙ fibreFun L 𝔸).obj X).tensor
        (pointMod P)).even := by
  obtain ⟨p, q, ⟨e⟩⟩ := hsp X
  exact finiteDimensional_fibre_tensor_point_even L 𝔸 P e

/-- **The odd part of the fibre of an embedded object at a point is
finite dimensional.** -/
theorem finiteDimensional_indFibre_odd
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [MonoidalPreadditive C] [CategoryTheory.Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)] (L : OddLine (Ind C)) (𝔸 : Ind C) [MonObj 𝔸]
    [IsCommMonObj 𝔸]
    (hsp : SplitsOn L 𝔸 (indOf : C ⥤ Ind C))
    (P : SuperPoint (gammaAlgebra (Ind C) L 𝔸)) (X : C) :
    FiniteDimensional ℂ
      ((((indOf : C ⥤ Ind C) ⋙ fibreFun L 𝔸).obj X).tensor
        (pointMod P)).odd := by
  obtain ⟨p, q, ⟨e⟩⟩ := hsp X
  exact finiteDimensional_fibre_tensor_point_odd L 𝔸 P e

/-- **The fibre functor into super vector spaces**: embed, take the
fibre over the splitting algebra, and base change to the ℂ-point. -/
noncomputable def deligneFibre
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [MonoidalPreadditive C] [CategoryTheory.Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)] (L : OddLine (Ind C)) (𝔸 : Ind C) [MonObj 𝔸]
    [IsCommMonObj 𝔸]
    (hsp : SplitsOn L 𝔸 (indOf : C ⥤ Ind C))
    (P : SuperPoint (gammaAlgebra (Ind C) L 𝔸)) : C ⥤ SuperVect :=
  superVectFunctor P ((indOf : C ⥤ Ind C) ⋙ fibreFun L 𝔸)
    (finiteDimensional_indFibre_even L 𝔸 hsp P)
    (finiteDimensional_indFibre_odd L 𝔸 hsp P)

/-- **The fibre functor is additive.** -/
instance deligneFibre_additive
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [MonoidalPreadditive C] [CategoryTheory.Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)] (L : OddLine (Ind C)) (𝔸 : Ind C) [MonObj 𝔸]
    [IsCommMonObj 𝔸]
    (hsp : SplitsOn L 𝔸 (indOf : C ⥤ Ind C))
    (P : SuperPoint (gammaAlgebra (Ind C) L 𝔸)) :
    (deligneFibre L 𝔸 hsp P).Additive :=
  superVectFunctor_additive _ _ _ _

/-! ### Exactness -/

/-- The base-change hypothesis of `RS.exists_fibre_algebra`, as a
splitting of each embedded short exact sequence after the fibre
functor. -/
theorem indFibre_nonempty_splitting
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    [CategoryTheory.Linear ℂ (Ind C)] [MonoidalLinear ℂ (Ind C)]
    (L : OddLine (Ind C)) (𝔸 : Ind C) [MonObj 𝔸] [IsCommMonObj 𝔸]
    (hsec : ∀ T : CategoryTheory.ShortComplex C, T.ShortExact →
      ∃ s : freeMod 𝔸 ((T.map (indOf : C ⥤ Ind C)).X₃) ⟶
          freeMod 𝔸 ((T.map (indOf : C ⥤ Ind C)).X₂),
        s ≫ freeModMap 𝔸 ((T.map (indOf : C ⥤ Ind C)).g) =
          𝟙 (freeMod 𝔸 ((T.map (indOf : C ⥤ Ind C)).X₃)))
    (T : CategoryTheory.ShortComplex C) (hT : T.ShortExact) :
    Nonempty
      ((T.map ((indOf : C ⥤ Ind C) ⋙ fibreFun L 𝔸)).Splitting) := by
  obtain ⟨s, hs⟩ := hsec T hT
  rw [CategoryTheory.ShortComplex.map_comp]
  exact ⟨fibreFunSplitting L 𝔸 (indOf_shortExact hT) s hs⟩

/-- **The fibre functor preserves finite limits.** -/
theorem deligneFibre_preservesFiniteLimits
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    [CategoryTheory.Linear ℂ (Ind C)] [MonoidalLinear ℂ (Ind C)]
    (L : OddLine (Ind C)) (𝔸 : Ind C) [MonObj 𝔸] [IsCommMonObj 𝔸]
    (hsp : SplitsOn L 𝔸 (indOf : C ⥤ Ind C))
    (hsec : ∀ T : CategoryTheory.ShortComplex C, T.ShortExact →
      ∃ s : freeMod 𝔸 ((T.map (indOf : C ⥤ Ind C)).X₃) ⟶
          freeMod 𝔸 ((T.map (indOf : C ⥤ Ind C)).X₂),
        s ≫ freeModMap 𝔸 ((T.map (indOf : C ⥤ Ind C)).g) =
          𝟙 (freeMod 𝔸 ((T.map (indOf : C ⥤ Ind C)).X₃)))
    (P : SuperPoint (gammaAlgebra (Ind C) L 𝔸)) :
    Limits.PreservesFiniteLimits (deligneFibre L 𝔸 hsp P) :=
  superVectFunctor_preservesFiniteLimits P _ _ _
    (indFibre_nonempty_splitting L 𝔸 hsec)

/-- **The fibre functor preserves finite colimits**; with the
previous statement it is exact. -/
theorem deligneFibre_preservesFiniteColimits
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    [CategoryTheory.Linear ℂ (Ind C)] [MonoidalLinear ℂ (Ind C)]
    (L : OddLine (Ind C)) (𝔸 : Ind C) [MonObj 𝔸] [IsCommMonObj 𝔸]
    (hsp : SplitsOn L 𝔸 (indOf : C ⥤ Ind C))
    (hsec : ∀ T : CategoryTheory.ShortComplex C, T.ShortExact →
      ∃ s : freeMod 𝔸 ((T.map (indOf : C ⥤ Ind C)).X₃) ⟶
          freeMod 𝔸 ((T.map (indOf : C ⥤ Ind C)).X₂),
        s ≫ freeModMap 𝔸 ((T.map (indOf : C ⥤ Ind C)).g) =
          𝟙 (freeMod 𝔸 ((T.map (indOf : C ⥤ Ind C)).X₃)))
    (P : SuperPoint (gammaAlgebra (Ind C) L 𝔸)) :
    Limits.PreservesFiniteColimits (deligneFibre L 𝔸 hsp P) :=
  superVectFunctor_preservesFiniteColimits P _ _ _
    (indFibre_nonempty_splitting L 𝔸 hsec)

/-! ### Dimensions and faithfulness -/

/-- **The fibre functor detects the zero object.**  If the fibre of
an object is a zero super vector space then both ranks of its mixed
sum vanish, so its fibre over the algebra is already zero, and the
unit of the algebra being a monomorphism forces the object to
vanish. -/
theorem id_eq_zero_of_deligneFibre_id_eq_zero
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [MonoidalPreadditive C] [CategoryTheory.Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)] (L : OddLine (Ind C)) (𝔸 : Ind C) [MonObj 𝔸]
    [IsCommMonObj 𝔸] [∀ Z : Ind C, (tensorRight Z).PreservesMonomorphisms]
    (hmono : Mono η[𝔸])
    (hsp : SplitsOn L 𝔸 (indOf : C ⥤ Ind C))
    (P : SuperPoint (gammaAlgebra (Ind C) L 𝔸)) (Z : C)
    (hz : 𝟙 ((deligneFibre L 𝔸 hsp P).obj Z) = 0) : 𝟙 Z = 0 := by
  haveI : (indOf (C := C)).Additive := indOf_additive
  obtain ⟨p, q, ⟨e⟩⟩ := hsp Z
  have hide : (LinearMap.id :
      ((deligneFibre L 𝔸 hsp P).obj Z).even →ₗ[ℂ]
        ((deligneFibre L 𝔸 hsp P).obj Z).even) = 0 :=
    congrArg SuperVect.Hom.evenMap hz
  have hido : (LinearMap.id :
      ((deligneFibre L 𝔸 hsp P).obj Z).odd →ₗ[ℂ]
        ((deligneFibre L 𝔸 hsp P).obj Z).odd) = 0 :=
    congrArg SuperVect.Hom.oddMap hz
  haveI : Subsingleton ((deligneFibre L 𝔸 hsp P).obj Z).even :=
    ⟨fun a b => by
      have ha : a = 0 := by simpa using DFunLike.congr_fun hide a
      have hb : b = 0 := by simpa using DFunLike.congr_fun hide b
      rw [ha, hb]⟩
  haveI : Subsingleton ((deligneFibre L 𝔸 hsp P).obj Z).odd :=
    ⟨fun a b => by
      have ha : a = 0 := by simpa using DFunLike.congr_fun hido a
      have hb : b = 0 := by simpa using DFunLike.congr_fun hido b
      rw [ha, hb]⟩
  have hp : p = 0 := by
    refine Eq.trans ?_ (Module.finrank_eq_zero_of_subsingleton (R := ℂ)
      (M := ((deligneFibre L 𝔸 hsp P).obj Z).even))
    exact (finrank_superVectFunctor_even P _
      (finiteDimensional_indFibre_even L 𝔸 hsp P)
      (finiteDimensional_indFibre_odd L 𝔸 hsp P) Z p q
      (fibreFreeIso L 𝔸 e)).symm
  have hq : q = 0 := by
    refine Eq.trans ?_ (Module.finrank_eq_zero_of_subsingleton (R := ℂ)
      (M := ((deligneFibre L 𝔸 hsp P).obj Z).odd))
    exact (finrank_superVectFunctor_odd P _
      (finiteDimensional_indFibre_even L 𝔸 hsp P)
      (finiteDimensional_indFibre_odd L 𝔸 hsp P) Z p q
      (fibreFreeIso L 𝔸 e)).symm
  subst hp
  subst hq
  have hB : 𝟙 (⨁ fun i : Fin 0 ⊕ Fin 0 =>
      Sum.elim (fun _ => (gammaAlgebra (Ind C) L 𝔸).unitMod)
        (fun _ => SuperCommAlgebra.Mod.shift
          (gammaAlgebra (Ind C) L 𝔸).unitMod) i) = 0 := by
    refine Limits.biproduct.hom_ext _ _ ?_
    rintro (i | i)
    exacts [i.elim0, i.elim0]
  have hW : 𝟙 ((fibreFun L 𝔸).obj ((indOf : C ⥤ Ind C).obj Z)) = 0 := by
    have h1 := (fibreFreeIso L 𝔸 e).hom_inv_id
    rw [← Category.id_comp (fibreFreeIso L 𝔸 e).inv, hB,
      Limits.zero_comp, Limits.comp_zero] at h1
    exact h1.symm
  have h0 : (fibreFun L 𝔸).map
      (𝟙 ((indOf : C ⥤ Ind C).obj Z)) = 0 := by
    rw [CategoryTheory.Functor.map_id]
    exact hW
  have h1 : 𝟙 ((indOf : C ⥤ Ind C).obj Z) = 0 :=
    fibreFun_map_eq_zero L 𝔸 hmono _ e h0
  have h2 : (indOf : C ⥤ Ind C).map (𝟙 Z) =
      (indOf : C ⥤ Ind C).map (0 : Z ⟶ Z) := by
    rw [CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_zero]
    exact h1
  exact (indOf (C := C)).map_injective h2

/-- **The fibre functor is faithful.**  It is exact, so it carries
the image factorisation of a morphism to an image factorisation;
a morphism killed by the functor therefore has zero image, and an
object with zero fibre is zero. -/
theorem deligneFibre_faithful
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    [CategoryTheory.Linear ℂ (Ind C)] [MonoidalLinear ℂ (Ind C)]
    (L : OddLine (Ind C)) (𝔸 : Ind C) [MonObj 𝔸] [IsCommMonObj 𝔸]
    [∀ Z : Ind C, (tensorRight Z).PreservesMonomorphisms]
    (hmono : Mono η[𝔸])
    (hsp : SplitsOn L 𝔸 (indOf : C ⥤ Ind C))
    (hsec : ∀ T : CategoryTheory.ShortComplex C, T.ShortExact →
      ∃ s : freeMod 𝔸 ((T.map (indOf : C ⥤ Ind C)).X₃) ⟶
          freeMod 𝔸 ((T.map (indOf : C ⥤ Ind C)).X₂),
        s ≫ freeModMap 𝔸 ((T.map (indOf : C ⥤ Ind C)).g) =
          𝟙 (freeMod 𝔸 ((T.map (indOf : C ⥤ Ind C)).X₃)))
    (P : SuperPoint (gammaAlgebra (Ind C) L 𝔸)) :
    (deligneFibre L 𝔸 hsp P).Faithful := by
  haveI : (deligneFibre L 𝔸 hsp P).PreservesHomology :=
    superVectFunctor_preservesHomology P _ _ _
      (indFibre_nonempty_splitting L 𝔸 hsec)
  refine ⟨fun {X Y} f g hfg => ?_⟩
  have hd : (deligneFibre L 𝔸 hsp P).map (f - g) = 0 := by
    rw [CategoryTheory.Functor.map_sub, hfg, sub_self]
  have hfac : Abelian.factorThruImage (f - g) ≫
      Abelian.image.ι (f - g) = f - g := Abelian.image.fac (f - g)
  have h1 : (deligneFibre L 𝔸 hsp P).map
        (Abelian.factorThruImage (f - g)) ≫
      (deligneFibre L 𝔸 hsp P).map (Abelian.image.ι (f - g)) = 0 := by
    rw [← CategoryTheory.Functor.map_comp, hfac, hd]
  have h2 : (deligneFibre L 𝔸 hsp P).map
      (Abelian.image.ι (f - g)) = 0 :=
    zero_of_epi_comp _ h1
  have h3 : 𝟙 ((deligneFibre L 𝔸 hsp P).obj
      (Abelian.image (f - g))) = 0 :=
    (cancel_mono ((deligneFibre L 𝔸 hsp P).map
      (Abelian.image.ι (f - g)))).mp
      (by rw [Category.id_comp, h2, Limits.zero_comp])
  have h4 : 𝟙 (Abelian.image (f - g)) = 0 :=
    id_eq_zero_of_deligneFibre_id_eq_zero L 𝔸 hmono hsp P _ h3
  have h5 : Abelian.image.ι (f - g) = 0 := by
    rw [← Category.id_comp (Abelian.image.ι (f - g)), h4,
      Limits.zero_comp]
  have h6 : f - g = 0 := by
    rw [← hfac, h5, Limits.comp_zero]
  exact sub_eq_zero.mp h6

/-! ### The packaged statement -/

/-- **A fibre functor into super vector spaces from a splitting
algebra with a ℂ-point.**  Over an algebra whose unit is a nonzero
monomorphism, which splits every embedded object into a mixed sum
and every embedded short exact sequence after base change, the
composite of the embedding, the fibre functor over the algebra and
base change along the point is an additive, exact and faithful
functor to finite-dimensional super vector spaces. -/
theorem exists_deligneFibre_of_point
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    [CategoryTheory.Linear ℂ (Ind C)] [MonoidalLinear ℂ (Ind C)]
    (L : OddLine (Ind C)) (𝔸 : Ind C) [MonObj 𝔸] [IsCommMonObj 𝔸]
    [∀ Z : Ind C, (tensorRight Z).PreservesMonomorphisms]
    (hmono : Mono η[𝔸])
    (hsp : SplitsOn L 𝔸 (indOf : C ⥤ Ind C))
    (hsec : ∀ T : CategoryTheory.ShortComplex C, T.ShortExact →
      ∃ s : freeMod 𝔸 ((T.map (indOf : C ⥤ Ind C)).X₃) ⟶
          freeMod 𝔸 ((T.map (indOf : C ⥤ Ind C)).X₂),
        s ≫ freeModMap 𝔸 ((T.map (indOf : C ⥤ Ind C)).g) =
          𝟙 (freeMod 𝔸 ((T.map (indOf : C ⥤ Ind C)).X₃)))
    (P : SuperPoint (gammaAlgebra (Ind C) L 𝔸)) :
    ∃ ω : C ⥤ SuperVect, ω.Additive ∧
      Nonempty (Limits.PreservesFiniteLimits ω) ∧
      Nonempty (Limits.PreservesFiniteColimits ω) ∧ ω.Faithful :=
  ⟨deligneFibre L 𝔸 hsp P, deligneFibre_additive L 𝔸 hsp P,
    ⟨deligneFibre_preservesFiniteLimits L 𝔸 hsp hsec P⟩,
    ⟨deligneFibre_preservesFiniteColimits L 𝔸 hsp hsec P⟩,
    deligneFibre_faithful L 𝔸 hmono hsp hsec P⟩

end Fibre

end RS
