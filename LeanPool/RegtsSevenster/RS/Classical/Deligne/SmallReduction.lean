/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Interfaces.DeligneTheorem

/-!
# Deligne's theorem reduced to a genuinely small category

`RS.DeligneTheoremStatement` quantifies over a category `A : Type u`
with `Category.{v} A` that is only *essentially* small, whereas the
constructions of the development live over a `SmallCategory`.  This
module supplies the bridge: `RS.deligneTheoremStatement_of_small`
derives the statement in its stated generality from the special case
of a small category.

The route is Mathlib's `CategoryTheory.SmallModel`, carrying the
monoidal structure transported along `CategoryTheory.equivSmallModel`
(`CategoryTheory.Monoidal.Transported`).  Along that equivalence:

* the abelian, preadditive, ℂ-linear, monoidal preadditive, monoidal
  ℂ-linear and rigid structures are transported to the small model
  (`RS.SmallDeligne`), the ℂ-linear one by `RS.linearOfFullyFaithful`
  and the rest by Mathlib's transfer lemmas;
* Deligne's three hypotheses are transported —
  `RS.hasScalarUnit_of_fullyFaithful`, `RS.tensorGeneratedBy_map` and
  `RS.moderateLengthGrowth_map` — using the comparison isomorphisms
  `RS.tensorPowMapIso`, `RS.rightDualMapIso` and `RS.mixedPowMapIso`
  of a monoidal equivalence, together with the behaviour of
  subquotients and of bounded length under a fully faithful functor
  (`RS.isSubquotientOf_map`, `RS.lengthLE_of_map`);
* the fibre functor comes back by precomposition,
  `RS.DeligneFibreFunctor.precompose`.
-/

@[expose] public section

namespace RS

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v₁ u₁ v₂ u₂ v u

/-! ## A linear structure pulled back along a fully faithful functor -/

section LinearTransfer

/-- The `R`-linear structure that a fully faithful additive functor
into an `R`-linear category induces on its source: a morphism is
rescaled by rescaling its image and taking the preimage. -/
@[implicit_reducible]
def linearOfFullyFaithful (R : Type*) [Semiring R] {B : Type u₁}
    [Category.{v₁} B] [Preadditive B] {A : Type u₂} [Category.{v₂} A]
    [Preadditive A] [Linear R A] {G : B ⥤ A} (hG : G.FullyFaithful)
    [G.Additive] : Linear R B where
  homModule X Y := by
    letI : SMul R (X ⟶ Y) := ⟨fun r f => hG.preimage (r • G.map f)⟩
    exact Function.Injective.module R (G.mapAddHom (X := X) (Y := Y))
      (fun _ _ h => hG.map_injective h) (fun _ _ => hG.map_preimage _)
  smul_comp X Y Z r f g := hG.map_injective (by
    change G.map ((hG.preimage (r • G.map f)) ≫ g) = _
    rw [Functor.map_comp, hG.map_preimage]
    change _ = G.map (hG.preimage (r • G.map (f ≫ g)))
    rw [hG.map_preimage, Functor.map_comp, Linear.smul_comp])
  comp_smul X Y Z f r g := hG.map_injective (by
    change G.map (f ≫ (hG.preimage (r • G.map g))) = _
    rw [Functor.map_comp, hG.map_preimage]
    change _ = G.map (hG.preimage (r • G.map (f ≫ g)))
    rw [hG.map_preimage, Functor.map_comp, Linear.comp_smul])

/-- The inducing functor is linear for the induced structure: that
structure is defined so that it is. -/
theorem functorLinearOfFullyFaithful (R : Type*) [Semiring R]
    {B : Type u₁} [Category.{v₁} B] [Preadditive B] {A : Type u₂}
    [Category.{v₂} A] [Preadditive A] [Linear R A] {G : B ⥤ A}
    (hG : G.FullyFaithful) [G.Additive] :
    letI := linearOfFullyFaithful R hG
    G.Linear R :=
  letI := linearOfFullyFaithful R hG
  { map_smul := fun _ _ => hG.map_preimage _ }

end LinearTransfer

/-! ## Comparison isomorphisms of a monoidal functor -/

section MonoidalComparison

/-- A monoidal functor carries a tensor power to the tensor power of
the image: the comparison isomorphisms assembled by induction on the
exponent. -/
noncomputable def tensorPowMapIso {A : Type u₁} [Category.{v₁} A]
    [MonoidalCategory A] {B : Type u₂} [Category.{v₂} B]
    [MonoidalCategory B] (G : A ⥤ B) [G.Monoidal] (X : A) :
    ∀ n : ℕ, G.obj (tensorPow A X n) ≅ tensorPow B (G.obj X) n
  | 0 => (Functor.Monoidal.εIso G).symm
  | n + 1 => (Functor.Monoidal.μIso G (tensorPow A X n) X).symm ≪≫
      tensorIso (tensorPowMapIso G X n) (Iso.refl (G.obj X))

/-- Tensor powers respect isomorphisms of the base object. -/
noncomputable def tensorPowCongrIso {B : Type u₂} [Category.{v₂} B]
    [MonoidalCategory B] {X Y : B} (i : X ≅ Y) :
    ∀ n : ℕ, tensorPow B X n ≅ tensorPow B Y n
  | 0 => Iso.refl _
  | n + 1 => tensorIso (tensorPowCongrIso i n) i

/-- A monoidal equivalence of rigid categories carries right duals to
right duals: the image of a dualising pair is a dualising pair
because the inverse functor reflects one, and right duals are unique
up to isomorphism. -/
noncomputable def rightDualMapIso {A : Type u₁} [Category.{v₁} A]
    [MonoidalCategory A] [RigidCategory A] {B : Type u₂}
    [Category.{v₂} B] [MonoidalCategory B] [RigidCategory B]
    (e : A ≌ B) [e.inverse.Monoidal] (X : A) :
    e.functor.obj (Xᘁ) ≅ (e.functor.obj X)ᘁ := by
  have u : ∀ Z : A, Z ≅ e.inverse.obj (e.functor.obj Z) := fun Z =>
    e.unitIso.app Z
  haveI : ExactPairing (e.inverse.obj (e.functor.obj X))
      (e.inverse.obj (e.functor.obj (Xᘁ))) :=
    exactPairingCongr (u X).symm (u (Xᘁ)).symm
  haveI hpair : ExactPairing (e.functor.obj X) (e.functor.obj (Xᘁ)) :=
    ExactPairing.ofFullyFaithful e.inverse _ _
  exact rightDualIso hpair HasRightDual.exact

/-- A monoidal equivalence of rigid categories carries mixed tensor
powers to mixed tensor powers. -/
noncomputable def mixedPowMapIso {A : Type u₁} [Category.{v₁} A]
    [MonoidalCategory A] [RigidCategory A] {B : Type u₂}
    [Category.{v₂} B] [MonoidalCategory B] [RigidCategory B]
    (e : A ≌ B) [e.functor.Monoidal] [e.inverse.Monoidal] (X : A)
    (a b : ℕ) :
    e.functor.obj (mixedPow A X a b) ≅ mixedPow B (e.functor.obj X) a b :=
  (Functor.Monoidal.μIso e.functor (tensorPow A X a)
      (tensorPow A (Xᘁ) b)).symm ≪≫
    tensorIso (tensorPowMapIso e.functor X a)
      (tensorPowMapIso e.functor (Xᘁ) b ≪≫
        tensorPowCongrIso (rightDualMapIso e X) b)

end MonoidalComparison

/-! ## Subquotients and bounded length along a functor -/

section SubquotientLength

/-- A functor preserving monomorphisms and epimorphisms carries
subquotients to subquotients. -/
theorem isSubquotientOf_map {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B] (G : A ⥤ B)
    [G.PreservesMonomorphisms] [G.PreservesEpimorphisms] {Y Z : A}
    (h : IsSubquotientOf Y Z) :
    IsSubquotientOf (G.obj Y) (G.obj Z) := by
  obtain ⟨S, i, p, hi, hp⟩ := h
  have := hi
  have := hp
  exact ⟨G.obj S, G.map i, G.map p, inferInstance, inferInstance⟩

/-- The subquotient relation transfers along isomorphisms of both
arguments. -/
theorem IsSubquotientOf.congr {A : Type u₁} [Category.{v₁} A]
    {Y Y' Z Z' : A} (h : IsSubquotientOf Y Z) (iY : Y ≅ Y')
    (iZ : Z ≅ Z') : IsSubquotientOf Y' Z' := by
  obtain ⟨S, i, p, hi, hp⟩ := h
  have := hi
  have := hp
  exact ⟨S, i ≫ iZ.hom, p ≫ iY.hom, inferInstance, inferInstance⟩

/-- A fully faithful functor preserving monomorphisms reflects the
length bound: it embeds the subobject order of `Z` in that of
`G.obj Z`, so a strictly increasing chain over `Z` gives one over
`G.obj Z`. -/
theorem lengthLE_of_map {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B] (G : B ⥤ A) (hG : G.FullyFaithful)
    [G.PreservesMonomorphisms] {Z : B} {k : ℕ}
    (h : LengthLE (G.obj Z) k) : LengthLE Z k := by
  intro f hf
  have hmono : ∀ {S T : Subobject Z}, S ≤ T →
      Subobject.mk (G.map S.arrow) ≤ Subobject.mk (G.map T.arrow) := by
    intro S T hST
    refine Subobject.mk_le_mk_of_comm (G.map (Subobject.ofLE S T hST)) ?_
    rw [← G.map_comp, Subobject.ofLE_arrow]
  have hrefl : ∀ {S T : Subobject Z},
      Subobject.mk (G.map S.arrow) ≤ Subobject.mk (G.map T.arrow) →
        S ≤ T := by
    intro S T hle
    refine Subobject.le_of_comm
      (hG.preimage
        (Subobject.ofMkLEMk (G.map S.arrow) (G.map T.arrow) hle)) ?_
    refine hG.map_injective ?_
    rw [G.map_comp, hG.map_preimage, Subobject.ofMkLEMk_comp]
  refine h (fun i => Subobject.mk (G.map (f i).arrow)) ?_
  intro i j hij
  have hlt : f i < f j := hf hij
  exact lt_of_le_of_ne (hmono hlt.le) fun heq =>
    hlt.ne (le_antisymm hlt.le (hrefl (le_of_eq heq.symm)))

end SubquotientLength

/-! ## Deligne's hypotheses along an equivalence -/

section Hypotheses

/-- Scalar unit endomorphisms transfer along a fully faithful
ℂ-linear monoidal functor: the map `c ↦ c • 𝟙` on the source is
carried onto the one on the target by the functor followed by
conjugation with the unit comparison, and both of those are
bijective. -/
theorem hasScalarUnit_of_fullyFaithful {A : Type u₁} [Category.{v₁} A]
    [Preadditive A] [Linear ℂ A] [MonoidalCategory A] {B : Type u₂}
    [Category.{v₂} B] [Preadditive B] [Linear ℂ B] [MonoidalCategory B]
    (G : B ⥤ A) (hG : G.FullyFaithful) [G.Linear ℂ]
    [G.Monoidal] (h : HasScalarUnit A) : HasScalarUnit B := by
  have h' : Function.Bijective
      (fun c : ℂ => (c • 𝟙 (𝟙_ A) : 𝟙_ A ⟶ 𝟙_ A)) := h
  change Function.Bijective (fun c : ℂ => (c • 𝟙 (𝟙_ B) : 𝟙_ B ⟶ 𝟙_ B))
  set α : G.obj (𝟙_ B) ≅ 𝟙_ A := (Functor.Monoidal.εIso G).symm
  have hcomp : (fun c : ℂ => (c • 𝟙 (𝟙_ A) : 𝟙_ A ⟶ 𝟙_ A)) =
      (fun g : G.obj (𝟙_ B) ⟶ G.obj (𝟙_ B) => α.conj g) ∘
        (fun f : 𝟙_ B ⟶ 𝟙_ B => G.map f) ∘
          (fun c : ℂ => (c • 𝟙 (𝟙_ B) : 𝟙_ B ⟶ 𝟙_ B)) := by
    funext c
    simp [Iso.conj_apply, Functor.map_smul]
  have hbij : Function.Bijective
      ((fun g : G.obj (𝟙_ B) ⟶ G.obj (𝟙_ B) => α.conj g) ∘
        (fun f : 𝟙_ B ⟶ 𝟙_ B => G.map f)) :=
    Function.Bijective.comp α.conj.bijective hG.homEquiv.bijective
  rw [hcomp] at h'
  exact (Function.Bijective.of_comp_iff' hbij _).mp h'

/-- Finite tensor generation transfers along a monoidal equivalence:
the image of a generator generates, because the equivalence carries
the subquotient witness of the preimage of an object to one for the
object, biproducts to biproducts and mixed powers to mixed powers. -/
theorem tensorGeneratedBy_map {A : Type u₁} [Category.{v₁} A]
    [Preadditive A] [HasFiniteBiproducts A] [MonoidalCategory A]
    [RigidCategory A] {B : Type u₂} [Category.{v₂} B] [Preadditive B]
    [HasFiniteBiproducts B] [MonoidalCategory B] [RigidCategory B]
    (e : A ≌ B) [e.functor.Monoidal] [e.inverse.Monoidal]
    [e.functor.Additive] {X : A} (h : TensorGeneratedBy A X) :
    TensorGeneratedBy B (e.functor.obj X) := by
  have cu : ∀ Z : B, e.functor.obj (e.inverse.obj Z) ≅ Z := fun Z =>
    e.counitIso.app Z
  intro Y
  obtain ⟨k, ab, hsub⟩ := h (e.inverse.obj Y)
  refine ⟨k, ab, (isSubquotientOf_map e.functor hsub).congr (cu Y) ?_⟩
  exact e.functor.mapBiproduct _ ≪≫
    biproduct.mapIso fun t => mixedPowMapIso e X (ab t).1 (ab t).2

/-- Moderate length growth transfers along a monoidal equivalence:
the inverse functor carries a tensor power to the tensor power of the
preimage, and reflects the length bound. -/
theorem moderateLengthGrowth_map {A : Type u₁} [Category.{v₁} A]
    [MonoidalCategory A] {B : Type u₂} [Category.{v₂} B]
    [MonoidalCategory B] (e : A ≌ B) [e.inverse.Monoidal]
    (h : ModerateLengthGrowth A) : ModerateLengthGrowth B := by
  intro Y
  obtain ⟨c₀, c₁, hc⟩ := h (e.inverse.obj Y)
  exact ⟨c₀, c₁, fun N => lengthLE_of_map e.inverse
    e.fullyFaithfulInverse
    ((hc N).of_iso (tensorPowMapIso e.inverse Y N).symm)⟩

end Hypotheses

/-! ## The fibre functor along a functor -/

section Fibre

/-- Precomposing a Deligne fibre functor with an exact, faithful,
ℂ-linear symmetric monoidal functor gives a Deligne fibre functor:
every clause of the conclusion is stable under composition. -/
noncomputable def DeligneFibreFunctor.precompose {A : Type u₁}
    [Category.{v₁} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] {B : Type u₂} [Category.{v₂} B]
    [MonoidalCategory B] [SymmetricCategory B] [Preadditive B]
    [Linear ℂ B] (F : DeligneFibreFunctor B) (G : A ⥤ B) [G.Braided]
    [G.Additive] [G.Linear ℂ] [G.Faithful] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] : DeligneFibreFunctor A :=
  letI := F.braided
  letI := F.additive
  letI := F.linear
  letI := F.faithful
  letI := F.preservesFiniteLimits
  letI := F.preservesFiniteColimits
  { ω := G ⋙ F.ω
    braided := inferInstance
    additive := inferInstance
    linear := inferInstance
    faithful := inferInstance
    preservesFiniteLimits := comp_preservesFiniteLimits G F.ω
    preservesFiniteColimits := comp_preservesFiniteColimits G F.ω }

end Fibre

/-! ## The small model of a candidate tensor category -/

section SmallModel

variable (A : Type u)

/-- The small model of an essentially small monoidal category,
carrying the monoidal structure transported along
`CategoryTheory.equivSmallModel`. -/
@[reducible] noncomputable def SmallDeligne
    [Category.{v} A] [EssentiallySmall.{v} A] : Type v :=
  Monoidal.Transported (equivSmallModel.{v} A)

/-- The transporting equivalence onto the small model, monoidal by
construction. -/
@[reducible] noncomputable def smallDeligneEquiv
    [Category.{v} A] [EssentiallySmall.{v} A] : A ≌ SmallDeligne A :=
  Monoidal.equivalenceTransported (equivSmallModel.{v} A)

/-- The preadditive structure of the small model. -/
@[implicit_reducible]
noncomputable def smallDelignePreadditive
    [Category.{v} A] [Abelian A] [EssentiallySmall.{v} A] :
    Preadditive (SmallDeligne A) :=
  Preadditive.ofFullyFaithful (smallDeligneEquiv A).fullyFaithfulInverse

attribute [local instance] smallDelignePreadditive

/-- The inverse of the transporting equivalence is additive. -/
theorem smallDeligneInverseAdditive
    [Category.{v} A] [Abelian A] [EssentiallySmall.{v} A] :
    (smallDeligneEquiv A).inverse.Additive :=
  (smallDeligneEquiv A).fullyFaithfulInverse.additive_ofFullyFaithful

attribute [local instance] smallDeligneInverseAdditive

/-- The transporting equivalence is additive. -/
theorem smallDeligneFunctorAdditive
    [Category.{v} A] [Abelian A] [EssentiallySmall.{v} A] :
    (smallDeligneEquiv A).functor.Additive :=
  haveI : (smallDeligneEquiv A).symm.functor.Additive :=
    smallDeligneInverseAdditive A
  Equivalence.inverse_additive (smallDeligneEquiv A).symm

attribute [local instance] smallDeligneFunctorAdditive

/-- The ℂ-linear structure of the small model. -/
@[implicit_reducible]
noncomputable def smallDeligneLinear
    [Category.{v} A] [Abelian A] [Linear ℂ A] [EssentiallySmall.{v} A] :
    Linear ℂ (SmallDeligne A) :=
  linearOfFullyFaithful ℂ (smallDeligneEquiv A).fullyFaithfulInverse

attribute [local instance] smallDeligneLinear

/-- The inverse of the transporting equivalence is ℂ-linear. -/
theorem smallDeligneInverseLinear
    [Category.{v} A] [Abelian A] [Linear ℂ A] [EssentiallySmall.{v} A] :
    (smallDeligneEquiv A).inverse.Linear ℂ :=
  functorLinearOfFullyFaithful ℂ
    (smallDeligneEquiv A).fullyFaithfulInverse

attribute [local instance] smallDeligneInverseLinear

/-- The transporting equivalence is ℂ-linear. -/
theorem smallDeligneFunctorLinear
    [Category.{v} A] [Abelian A] [Linear ℂ A] [EssentiallySmall.{v} A] :
    (smallDeligneEquiv A).functor.Linear ℂ :=
  haveI : (smallDeligneEquiv A).symm.functor.Linear ℂ :=
    smallDeligneInverseLinear A
  Equivalence.inverseLinear (R := ℂ) (smallDeligneEquiv A).symm

attribute [local instance] smallDeligneFunctorLinear

/-- The small model has finite limits. -/
theorem smallDeligneFiniteLimits
    [Category.{v} A] [Abelian A] [EssentiallySmall.{v} A] :
    HasFiniteLimits (SmallDeligne A) :=
  ⟨fun _ _ _ =>
    Adjunction.hasLimitsOfShape_of_equivalence (smallDeligneEquiv A).inverse⟩

attribute [local instance] smallDeligneFiniteLimits

/-- The small model is abelian. -/
@[implicit_reducible]
noncomputable def smallDeligneAbelian
    [Category.{v} A] [Abelian A] [EssentiallySmall.{v} A] :
    Abelian (SmallDeligne A) :=
  abelianOfEquivalence (smallDeligneEquiv A).inverse

attribute [local instance] smallDeligneAbelian

/-- The small model has finite biproducts. -/
theorem smallDeligneBiproducts
    [Category.{v} A] [Abelian A] [EssentiallySmall.{v} A] :
    HasFiniteBiproducts (SmallDeligne A) :=
  HasFiniteBiproducts.of_hasFiniteProducts

attribute [local instance] smallDeligneBiproducts

/-- The tensor product of the small model is biadditive. -/
theorem smallDeligneMonoidalPreadditive
    [Category.{v} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [EssentiallySmall.{v} A] :
    MonoidalPreadditive (SmallDeligne A) :=
  monoidalPreadditive_of_faithful (smallDeligneEquiv A).inverse

attribute [local instance] smallDeligneMonoidalPreadditive

/-- The tensor product of the small model is ℂ-bilinear. -/
theorem smallDeligneMonoidalLinear
    [Category.{v} A] [Abelian A] [Linear ℂ A] [MonoidalCategory A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A] [EssentiallySmall.{v} A] :
    MonoidalLinear ℂ (SmallDeligne A) :=
  MonoidalLinear.ofFaithful ℂ (smallDeligneEquiv A).inverse

attribute [local instance] smallDeligneMonoidalLinear

/-- The small model is rigid. -/
@[implicit_reducible]
noncomputable def smallDeligneRigid
    [Category.{v} A] [MonoidalCategory A] [RigidCategory A]
    [EssentiallySmall.{v} A] : RigidCategory (SmallDeligne A) :=
  rigidCategoryOfEquivalence (smallDeligneEquiv A).symm.toAdjunction

attribute [local instance] smallDeligneRigid

/-- **Deligne's theorem reduces to the small case.**  Given the
conclusion of Théorème 0.6 for every small category carrying the
hypotheses, it holds for every essentially small one: transport the
structure and the hypotheses to the small model, apply the small
case, and precompose the resulting fibre functor with the
transporting equivalence. -/
theorem deligneTheoremStatement_of_small
    (h : ∀ (B : Type v) [SmallCategory B] [Abelian B] [Linear ℂ B]
        [MonoidalCategory B] [SymmetricCategory B] [MonoidalPreadditive B]
        [MonoidalLinear ℂ B] [HasFiniteBiproducts B] [RigidCategory B],
      HasScalarUnit B → (∃ X : B, TensorGeneratedBy B X) →
        ModerateLengthGrowth B → Nonempty (DeligneFibreFunctor B)) :
    DeligneTheoremStatement.{u, v} := by
  intro A _ _ _ _ _ _ _ _ _ _ hunit hgen hgrow
  obtain ⟨X, hX⟩ := hgen
  obtain ⟨F⟩ := h (SmallDeligne A)
    (hasScalarUnit_of_fullyFaithful (smallDeligneEquiv A).inverse
      (smallDeligneEquiv A).fullyFaithfulInverse hunit)
    ⟨(smallDeligneEquiv A).functor.obj X,
      tensorGeneratedBy_map (smallDeligneEquiv A) hX⟩
    (moderateLengthGrowth_map (smallDeligneEquiv A) hgrow)
  exact ⟨F.precompose (smallDeligneEquiv A).functor⟩

end SmallModel

end RS
