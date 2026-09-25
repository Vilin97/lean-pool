/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.DoubledAbelian

/-!
# The even embedding is strong braided monoidal

`RS/Classical/Deligne/Doubling.lean` builds the even embedding
`evenEmbed : A ⥤ Doubled A`, `X ↦ (X, 0)`, together with its
tensor comparison `evenEmbedTensorIso`, its unit comparison
`evenEmbedUnitIso` and the compatibility of the comparison with the
two braidings.  This module packages that data as a lax monoidal
structure, upgrades it to a strong monoidal structure — both
comparisons are isomorphisms by construction — and records that the
result is braided.

Every coherence reduces, by `Doubled.hom_ext`, to a pair of
component identities.  The odd component of each target is the zero
object, so the odd half is automatic; the even half is a biproduct
calculation in which the mixed parity blocks are killed because one
of their two factors is the zero object.

The module also records the exactness of the even embedding.  The
even embedding is simultaneously left and right adjoint to the
even-component functor `evenFunctor` of
`RS/Classical/Deligne/DoubledAbelian.lean`, because a morphism into
or out of the zero object is unique; so it preserves all limits and
all colimits, in particular the finite ones.
-/

namespace RS

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

noncomputable section

namespace Doubled

section Monoidal

open ZeroObject

variable {A : Type u}

/-- The even component of the unit comparison is the identity. -/
@[simp]
theorem evenHom_evenEmbedUnitIso_hom
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A] :
    evenHom (evenEmbedUnitIso (A := A)).hom = 𝟙 (𝟙_ A) :=
  rfl

/-- The even embedding is lax monoidal: the unit comparison is the
identity, because the unit of `Doubled A` *is* the even embedding
of the unit of `A`, and the tensor comparison is
`evenEmbedTensorIso`. -/
instance evenEmbedLaxMonoidal
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A] :
    (evenEmbed (A := A)).LaxMonoidal where
  ε := evenEmbedUnitIso.hom
  μ X Y := (evenEmbedTensorIso X Y).hom
  μ_natural_left := by
    intro X Y f X'
    ext
    · simp [evenEmbedTensorIso, isoBiprodZero]
  μ_natural_right := by
    intro X Y X' f
    ext
    · simp [evenEmbedTensorIso, isoBiprodZero]
  associativity := by
    intro X Y Z
    ext
    · apply biprod.hom_ext' <;> apply tensorRight_ext <;>
        simp [evenEmbedTensorIso, isoBiprodZero, assocEven,
          -comp_whiskerRight, -MonoidalCategory.whiskerLeft_comp,
          ← comp_whiskerRight_assoc,
          ← MonoidalCategory.whiskerLeft_comp]
  left_unitality := by
    intro X
    ext
    · apply biprod.hom_ext' <;>
        simp [evenEmbedTensorIso, isoBiprodZero, leftUnitorComp]
  right_unitality := by
    intro X
    ext
    · apply biprod.hom_ext' <;>
        simp [evenEmbedTensorIso, isoBiprodZero, rightUnitorComp]

/-- The even embedding is strong monoidal: both comparisons are
isomorphisms by construction. -/
noncomputable instance evenEmbedMonoidal
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A] :
    (evenEmbed (A := A)).Monoidal := by
  haveI hε : IsIso (Functor.LaxMonoidal.ε (evenEmbed (A := A))) :=
    inferInstanceAs (IsIso (evenEmbedUnitIso (A := A)).hom)
  haveI hμ : ∀ X Y : A,
      IsIso (Functor.LaxMonoidal.μ (evenEmbed (A := A)) X Y) :=
    fun X Y => inferInstanceAs (IsIso (evenEmbedTensorIso X Y).hom)
  exact CategoryTheory.Functor.Monoidal.ofLaxMonoidal _

/-! ### The four structure morphisms

These are stated after the strong monoidal structure has been
installed, so that their left-hand sides use the instance that a
downstream file resolves. -/

@[simp]
theorem evenEmbed_ε [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A] :
    Functor.LaxMonoidal.ε (evenEmbed (A := A)) =
      (evenEmbedUnitIso (A := A)).hom :=
  rfl

@[simp]
theorem evenEmbed_μ [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (X Y : A) :
    Functor.LaxMonoidal.μ (evenEmbed (A := A)) X Y =
      (evenEmbedTensorIso X Y).hom :=
  rfl

@[simp]
theorem evenEmbed_η [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A] :
    Functor.OplaxMonoidal.η (evenEmbed (A := A)) =
      (evenEmbedUnitIso (A := A)).inv := by
  have h : Functor.LaxMonoidal.ε (evenEmbed (A := A)) ≫
      Functor.OplaxMonoidal.η (evenEmbed (A := A)) = 𝟙 _ :=
    Functor.Monoidal.ε_η _
  calc Functor.OplaxMonoidal.η (evenEmbed (A := A))
      = ((evenEmbedUnitIso (A := A)).inv ≫
          Functor.LaxMonoidal.ε (evenEmbed (A := A))) ≫
          Functor.OplaxMonoidal.η (evenEmbed (A := A)) := by
        rw [evenEmbed_ε, Iso.inv_hom_id, Category.id_comp]
    _ = (evenEmbedUnitIso (A := A)).inv := by
        rw [Category.assoc, h, Category.comp_id]

@[simp]
theorem evenEmbed_δ [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (X Y : A) :
    Functor.OplaxMonoidal.δ (evenEmbed (A := A)) X Y =
      (evenEmbedTensorIso X Y).inv := by
  have h : Functor.LaxMonoidal.μ (evenEmbed (A := A)) X Y ≫
      Functor.OplaxMonoidal.δ (evenEmbed (A := A)) X Y = 𝟙 _ :=
    Functor.Monoidal.μ_δ _ X Y
  calc Functor.OplaxMonoidal.δ (evenEmbed (A := A)) X Y
      = ((evenEmbedTensorIso X Y).inv ≫
          Functor.LaxMonoidal.μ (evenEmbed (A := A)) X Y) ≫
          Functor.OplaxMonoidal.δ (evenEmbed (A := A)) X Y := by
        rw [evenEmbed_μ, Iso.inv_hom_id, Category.id_comp]
    _ = (evenEmbedTensorIso X Y).inv := by
        rw [Category.assoc, h, Category.comp_id]

end Monoidal

section Braided

open ZeroObject

variable {A : Type u}

/-- The even embedding is braided: the Koszul sign is invisible on
purely even objects, so the tensor comparison intertwines the two
braidings. -/
noncomputable instance evenEmbedBraided
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    [SymmetricCategory A] :
    (evenEmbed (A := A)).Braided where
  braided X Y := (evenEmbedTensorIso_braided X Y).symm

end Braided

section Exactness

open ZeroObject

variable {A : Type u}

/-- The even embedding is left adjoint to the even-component
functor: a morphism out of the zero object is unique. -/
def evenEmbedAdjEvenFunctor [Category.{v} A] [Preadditive A] [HasZeroObject A] :
    evenEmbed (A := A) ⊣ evenFunctor :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ Y =>
        { toFun := fun f => evenHom f
          invFun := fun g => homMk g ((isZero_zero A).to_ Y.odd)
          left_inv := fun _ =>
            hom_ext rfl ((isZero_zero A).eq_of_src _ _)
          right_inv := fun _ => rfl }
      homEquiv_naturality_left_symm := fun _ _ =>
        hom_ext rfl ((isZero_zero A).eq_of_src _ _)
      homEquiv_naturality_right := fun _ _ => rfl }

/-- The even embedding is right adjoint to the even-component
functor: a morphism into the zero object is unique. -/
def evenFunctorAdjEvenEmbed [Category.{v} A] [Preadditive A] [HasZeroObject A] :
    evenFunctor ⊣ evenEmbed (A := A) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun Y _ =>
        { toFun := fun g => homMk g ((isZero_zero A).from_ Y.odd)
          invFun := fun f => evenHom f
          left_inv := fun _ => rfl
          right_inv := fun _ =>
            hom_ext rfl ((isZero_zero A).eq_of_tgt _ _) }
      homEquiv_naturality_left_symm := fun _ _ => rfl
      homEquiv_naturality_right := fun _ _ =>
        hom_ext rfl ((isZero_zero A).eq_of_tgt _ _) }

/-- Being a right adjoint, the even embedding is left exact. -/
instance evenEmbedPreservesFiniteLimits
    [Category.{v} A] [Preadditive A] [HasZeroObject A] :
    PreservesFiniteLimits (evenEmbed (A := A)) := by
  have : PreservesLimitsOfSize.{0, 0} (evenEmbed (A := A)) :=
    (evenFunctorAdjEvenEmbed (A := A)).rightAdjoint_preservesLimits
  infer_instance

/-- Being a left adjoint, the even embedding is right exact. -/
instance evenEmbedPreservesFiniteColimits
    [Category.{v} A] [Preadditive A] [HasZeroObject A] :
    PreservesFiniteColimits (evenEmbed (A := A)) := by
  have : PreservesColimitsOfSize.{0, 0} (evenEmbed (A := A)) :=
    (evenEmbedAdjEvenFunctor (A := A)).leftAdjoint_preservesColimits
  infer_instance

end Exactness

end Doubled

end

end RS
