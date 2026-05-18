/-
Copyright (c) 2026 Joseph Eremondi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Eremondi
-/

import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Logic.Unique
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types.Basic



import LeanPool.LeanCwf.Fam
import LeanPool.LeanCwf.Basics
import LeanPool.LeanCwf.Util

namespace LeanPool.LeanCwf

open CategoryTheory
open NatTrans Category Functor
open Fam

namespace CwF

open TmTy
open CwFExt

universe u



/-- A bundled category equipped with a category-with-families structure. -/
structure CwFCat : Type (u + 1) where
  /-- The category of contexts. -/
  Ctx : Type u
  /-- The category structure on contexts. -/
  [exCat : Category.{u} Ctx]
  /-- The category-with-families structure on the context category. -/
  [exCwF : Structure Ctx]


instance : Coe CwFCat (Type _) where
  coe C := C.Ctx

attribute [instance] CwFCat.exCat CwFCat.exCwF

/-- A morphism of the type-and-term presheaves underlying two CwFs. -/
structure TmTyMorphism (C D : CwFCat) : Type _ where
  /-- The functor on context categories. -/
  CtxF : CategoryTheory.Functor C.Ctx D.Ctx
  /-- The natural transformation preserving type-and-term presheaves. -/
  transSubst :
    NatTrans
      (tmTyFam (Ctx := C)) --C's functor
      (Functor.comp (CtxF.op) (tmTyFam (Ctx := D)) ) -- D's functor






/-- Applies a CwF morphism to a context. -/
def MapCtx {C D : CwFCat} (F : TmTyMorphism C D) (Γ : C.Ctx) : D.Ctx :=
  F.CtxF.obj Γ

/-- Applies a CwF morphism to a substitution. -/
def MapSub {C D : CwFCat} (F : TmTyMorphism C D) {Γ Δ : C.Ctx}
  (θ : Δ ⟶ Γ) :
  (MapCtx F Δ) ⟶ (MapCtx F Γ) :=
  F.CtxF.map θ

@[simp]
theorem MapSubComp {C D : CwFCat} (F : TmTyMorphism C D) {Γ Δ Ξ : C.Ctx}
  (f : Ξ ⟶ Δ) (g : Δ ⟶ Γ) :
  (MapSub F f) ≫ (MapSub F g) = MapSub F (f ≫ g) :=
    Eq.symm (F.CtxF.map_comp f g)

theorem MapSubId {C D : CwFCat} (F : TmTyMorphism C D) {Γ : C.Ctx} :
  MapSub F (𝟙 Γ) = 𝟙 (MapCtx F Γ) :=
    F.CtxF.map_id Γ

/-- Applies a CwF morphism to a type. -/
def MapTy {C D : CwFCat} (F : TmTyMorphism C D)
  {Γ : C.Ctx}
  (T : Ty Γ) :
  Ty (MapCtx F Γ) := mapIx (F.transSubst.app (Opposite.op Γ)) T


/-- Applies a CwF morphism to a term. -/
def MapTm {C D : CwFCat} (F : TmTyMorphism C D)
 {Γ : C.Ctx}
  {T : Ty Γ}
  (t : Tm T) :
  Tm (MapTy F T) := mapFam (F.transSubst.app (Opposite.op Γ)) t

@[simp]
theorem MapTyCommut {C D : CwFCat} (F : TmTyMorphism C D)
  {Δ Γ : C.Ctx}
  {T : Ty Γ}
  {θ : Δ ⟶ Γ} :
  MapTy F (T⦃θ⦄) = (MapTy F T)⦃MapSub F θ⦄ :=
    congrFun (congrArg mapIx (F.transSubst.naturality (Opposite.op θ))) T

@[simp]
theorem MapTmCommut {C D : CwFCat} {F : TmTyMorphism C D}
  {Δ Γ : C.Ctx}
  {T : Ty Γ}
  {t : Tm T}
  {θ : Δ ⟶ Γ} :
  MapTm F (t⦃θ⦄) = castTm ((MapTm F t)⦃MapSub F θ⦄) (by rw [MapTyCommut]) := by
    symm
    refine eq_cast_of_heq ?_
    apply Subtype_HExt
    · exact
        (by
          simpa [MapTm, tmSub, MapTy, tySub, mapFam, Arrow.comp_left,
            ConcreteCategory.comp_apply, MapSub] using
            (congrFun
              (congrArg (fun h => h.left) (F.transSubst.naturality (Opposite.op θ)))
              t.val).symm)
    · aesop

@[simp]
theorem CastMapTmCommut {C D : CwFCat} {F : TmTyMorphism C D}
  {Γ : C.Ctx}
  {S T : Ty Γ}
  {eq : S = T}
  {t : Tm T} :
  MapTm F (castTm (S := S) t (by rw [eq])) =ₜ MapTm F t := by aesop


/-- Preservation of CwF context extension up to isomorphism. -/
class IsoPreserveCwF {C D : CwFCat} (F : TmTyMorphism C D) : Type _ where
  /-- The comparison isomorphism for extended contexts. -/
  snocIso :
    {Γ : C.Ctx}
    → {T : Ty Γ}
    → MapCtx F (Γ ▹ T) ≅ (MapCtx F Γ) ▹ (MapTy F T) := by aesop_cat
  /-- The projection map is preserved through the comparison isomorphism. -/
  pPreserve :
    {Γ : C.Ctx}
    → {T : Ty Γ}
    → MapSub F (p_ T)
      = snocIso.hom ≫ p
      := by aesop_cat
  /-- The variable term is preserved through the comparison isomorphism. -/
  vPreserve :
    {Γ : C.Ctx}
    → {T : Ty Γ}
    → MapTm F (v_ T) =ₜ (v_ (MapTy F T))⦃snocIso.hom⦄ := by aesop_cat

open IsoPreserveCwF

-- attribute [simp] IsoPreserveCwF.snocIso
-- attribute [simp] IsoPreserveCwF.pPreserve
attribute [simp] IsoPreserveCwF.vPreserve



@[aesop safe apply]
theorem pPreserve' {C D : CwFCat} {F : TmTyMorphism C D} [IsoPreserveCwF F]
    {Γ : C.Ctx}
    {T : Ty Γ}
    : p_ (MapTy F T) =
        (IsoPreserveCwF.snocIso (F := F) (Γ := Γ) (T := T)).inv ≫ MapSub F (p_ T) := by
      rw [IsoPreserveCwF.pPreserve (F := F) (Γ := Γ) (T := T)]
      simp

/-- Strict preservation of CwF context extension by a morphism. -/
class StrictPreserveCwF {C D : CwFCat} (F : TmTyMorphism C D) : Prop where
  /-- Extended contexts are preserved definitionally up to equality. -/
  snocPreserve:
    {Γ : C.Ctx}
    → {T : Ty Γ}
    → MapCtx F (Γ ▹ T) = (MapCtx F Γ) ▹ (MapTy F T) := by aesop_cat
  /-- Projections are preserved strictly. -/
  pPreserveStrict :
    {Γ : C.Ctx}
    → {T : Ty Γ}
    → MapSub F (p_ T)
      = eqToHom snocPreserve ≫ p := by aesop_cat
  /-- Variables are preserved strictly. -/
  vPreserveStrict :
    {Γ : C.Ctx}
    → {T : Ty Γ}
    → MapTm F (v_ T) =ₜ (v_ (MapTy F T))⦃eqToHom snocPreserve⦄ := by aesop_cat

open StrictPreserveCwF

instance strictIsoPreserve {C D : CwFCat} (F : TmTyMorphism C D) [StrictPreserveCwF F] :
    IsoPreserveCwF F where
  snocIso := eqToIso snocPreserve
  pPreserve := pPreserveStrict
  vPreserve := vPreserveStrict

theorem preserveId {C : CwFCat} : StrictPreserveCwF ⟨Functor.id C, NatTrans.id _⟩ where
  snocPreserve := by
    intros
    rfl
  pPreserveStrict := by
    intro Γ T
    change MapSub { CtxF := 𝟭 C.Ctx, transSubst := NatTrans.id tmTyFam } (p_ T) =
      eqToHom rfl ≫ p_ T
    simp [MapSub]
  vPreserveStrict := by
    intro Γ T
    change v_ T = castTm ((v_ T)⦃𝟙 (Γ ▹ T)⦄) (by simp)
    aesop_cat

/-- Composition of morphisms of type-and-term presheaves. -/
def tmTyComp {C D E : CwFCat} (F : TmTyMorphism C D) (G : TmTyMorphism D E) : TmTyMorphism C E := by
  fconstructor
  · apply Functor.comp F.CtxF G.CtxF
  · fconstructor
    · intros Γ
      apply CategoryStruct.comp
      · apply F.transSubst.app
      · apply G.transSubst.app
    · intro X Y f
      rw [← Category.assoc, F.transSubst.naturality f]
      exact congrArg (fun h => F.transSubst.app X ≫ h)
        (G.transSubst.naturality (F.CtxF.op.map f))

theorem MapCtxComp {C D E : CwFCat} (F : TmTyMorphism C D) (G : TmTyMorphism D E)
    {Γ : C.Ctx} :
    MapCtx (tmTyComp F G) Γ = MapCtx G (MapCtx F Γ) := by aesop


theorem MapSubTmTyComp {C D E : CwFCat} (F : TmTyMorphism C D) (G : TmTyMorphism D E)
    {Γ Δ : C.Ctx} {θ : Δ ⟶ Γ} :
    MapSub (tmTyComp F G) θ = MapSub G (MapSub F θ) := by aesop

theorem MapTm_TmTyComp {C D E : CwFCat} (F : TmTyMorphism C D) (G : TmTyMorphism D E)
    {Γ : C.Ctx} {T : Ty Γ} {t : Tm T} :
    MapTm (tmTyComp F G) t = MapTm G (MapTm F t) := by aesop

end CwF

end LeanPool.LeanCwf
