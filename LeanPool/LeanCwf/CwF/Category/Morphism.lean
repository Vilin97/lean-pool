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



import LeanPool.LeanCwf.CwF.Fam
import LeanPool.LeanCwf.CwF.Basics
import LeanPool.LeanCwf.CwF.Properties
import LeanPool.LeanCwf.CwF.Util

/-!
# CwF morphisms

Defines type-term morphisms, strict preservation of CwF structure, and the
category of bundled CwFs.
-/

namespace LeanPool.LeanCwf

open CategoryTheory
open NatTrans Category Functor

namespace CwF

open TmTy
open Fam
open CwFExt

universe u

/-- A bundled category with families: a category of contexts together with its
CwF structure. -/
structure CwFCat : Type _ where
  /-- The underlying category of contexts. -/
  Ctx : Type u
  /-- The category structure on the contexts. -/
  [exCat : Category.{u} Ctx]
  /-- The category-with-families structure on the contexts. -/
  [exCwF : CwFStruct Ctx]


/-- A bundled CwF is coerced to its underlying type of contexts. -/
instance : Coe CwFCat (Type _) where
  coe C := C.Ctx

attribute [instance] CwFCat.exCat CwFCat.exCwF

/-- A morphism of type-term structures: a functor on contexts together with a
natural transformation of the type-term presheaves. -/
structure TmTyMorphism (C D : CwFCat) : Type _ where
  /-- The action on contexts. -/
  CtxF : CategoryTheory.Functor.{u,u,u,u} C.Ctx D.Ctx
  /-- The natural transformation relating the type-term presheaves of `C` and `D`. -/
  transSubst :
    NatTrans
      (tmTyFam (Ctx := C)) --C's functor
      (Functor.comp (CtxF.op) (tmTyFam (Ctx := D)) ) -- D's functor






/-- The action of a type-term morphism on contexts. -/
def MapCtx {C D : CwFCat} (F : TmTyMorphism C D) (Γ : C.Ctx) : D.Ctx :=
  F.CtxF.obj Γ

/-- The action of a type-term morphism on context substitutions. -/
def MapSub {C D : CwFCat} (F : TmTyMorphism C D) {Γ Δ : C.Ctx}
  (θ : Δ ⟶ Γ)
  : (MapCtx F Δ) ⟶ (MapCtx F Γ) :=
  F.CtxF.map θ

@[simp]
theorem MapSubComp {C D : CwFCat} (F : TmTyMorphism C D) {Γ Δ Ξ : C.Ctx}
  (f : Ξ ⟶ Δ) (g : Δ ⟶ Γ)
  : (MapSub F f) ≫ (MapSub F g) = MapSub F (f ≫ g) :=
    Eq.symm (F.CtxF.map_comp f g)

theorem MapSubId {C D : CwFCat} (F : TmTyMorphism C D) {Γ : C.Ctx}
  : MapSub F (𝟙 Γ) = 𝟙 (MapCtx F Γ) :=
    F.CtxF.map_id Γ

/-- The action of a type-term morphism on types. -/
def MapTy {C D : CwFCat} (F : TmTyMorphism C D)
  {Γ : C.Ctx}
  (T : Ty Γ)
  : Ty (MapCtx F Γ) := mapIx (F.transSubst.app (Opposite.op Γ )) T


/-- The action of a type-term morphism on terms. -/
def MapTm {C D : CwFCat} (F : TmTyMorphism C D)
 {Γ : C.Ctx}
  {T : Ty Γ}
  (t : Tm T)
  : Tm (MapTy F T) := mapFam (F.transSubst.app (Opposite.op Γ )) t

/-- The action on types commutes with substitution. -/
@[simp]
theorem MapTyCommut {C D : CwFCat} (F : TmTyMorphism C D)
  {Δ Γ : C.Ctx}
  {T : Ty Γ}
  {θ : Δ ⟶ Γ}
  : MapTy F (T⦃θ⦄) = (MapTy F T)⦃MapSub F θ⦄ :=
    congrFun (congrArg mapIx (F.transSubst.naturality (Opposite.op θ))) T

/-- The action on terms commutes with substitution (up to cast). -/
@[simp]
theorem MapTmCommut {C D : CwFCat} {F : TmTyMorphism C D}
  {Δ Γ : C.Ctx}
  {T : Ty Γ}
  {t : Tm T}
  {θ : Δ ⟶ Γ}
  : (MapTm F (t⦃θ⦄)) = castTm  ((MapTm F t)⦃MapSub F θ⦄) (by rw [MapTyCommut]) := by
    -- let tyEq := MapTyCommut F (T := T) (θ := θ)
    -- let ceq
    --   := castSub (t := MapTm F t) (eq := by aesop) (f := MapSub F θ)
    let nat := F.transSubst.naturality (Opposite.op θ)
    let mapnat :=  (HEq.symm (hCong (refl mapFam) nat))
    let mapnat_T := hCongFunImplicit T (by rw [nat]) mapnat
    let mapnat_Tt := hCongFun t (by rw [nat]) mapnat_T
    let mapnat_eq := Eq.symm (eq_cast_of_heq mapnat_Tt)
    eapply Eq.trans mapnat_eq
    simp only [Functor.comp_map, mapFamComp]
    apply Subtype.ext
    aesop_cat

/-- The action on terms is invariant (up to cast) under casting the input term. -/
@[simp]
theorem CastMapTmCommut {C D : CwFCat} {F : TmTyMorphism C D}
  {Γ : C.Ctx}
  {S T : Ty Γ}
  {eq : S = T}
  {t : Tm T}
  : MapTm F (castTm (S := S) t (by rw [eq])) =ₜ MapTm F t  := by aesop


/-- A type-term morphism preserves context comprehension up to isomorphism: the
image of an extended context is isomorphic to the extension of the image. -/
class IsoPreserveCwF {C D : CwFCat} (F : TmTyMorphism C D) : Type _ where
  /-- The isomorphism between the image of an extended context and the extension
  of the image. -/
  snocIso :
    {Γ : C.Ctx}
    → {T : Ty Γ}
    → MapCtx F (Γ ▹ T) ≅ (MapCtx F Γ) ▹ (MapTy F T) := by aesop_cat
  /-- The projection is preserved through `snocIso`. -/
  pPreserve :
    {Γ : C.Ctx}
    → {T : Ty Γ}
    → MapSub F ((p_ T))
      = snocIso.hom ≫ p
      := by aesop_cat
  /-- The introduced variable is preserved through `snocIso`. -/
  vPreserve :
    {Γ : C.Ctx}
    → {T : Ty Γ}
    → (MapTm F ((v_ T)))
     =ₜ ((v_ (MapTy F T)))⦃snocIso.hom⦄  := by aesop_cat

open IsoPreserveCwF

-- attribute [simp] IsoPreserveCwF.snocIso
-- attribute [simp] IsoPreserveCwF.pPreserve
attribute [simp] IsoPreserveCwF.vPreserve



/-- The reversed form of `pPreserve`, expressing the image projection via the
inverse isomorphism. -/
@[aesop safe apply]
theorem pPreserve' {C D : CwFCat} {F : TmTyMorphism C D} [IsoPreserveCwF F]
    {Γ : C.Ctx}
    {T : Ty Γ}
    : (p_ (MapTy F T)) = snocIso.inv ≫ MapSub F ((p_ T)) := by
      simp_all only [pPreserve, Iso.inv_hom_id_assoc]

/-- The image variable, transported by the inverse isomorphism, equals the
introduced variable of the image extension (up to cast). -/
theorem vPreserve' {C D : CwFCat} {F : TmTyMorphism C D} [IsoPreserveCwF F]
    {Γ : C.Ctx}
    {T : Ty Γ}
    : ((v_ (MapTy F T))) =
       castTm (MapTm F ((v_ T)))⦃snocIso.inv⦄ (by simp [pPreserve']) := by
      simp only [vPreserve, castSub, tmSubComp]
      apply Subtype.ext
      simp only [castTm_val, tmSub_val, Iso.inv_hom_id, CategoryTheory.op_id, Functor.map_id,
        Arrow.id_left]
      rfl



/-- A type-term morphism preserving comprehension transports extension morphisms
through `snocIso`. -/
theorem extPreserve' (C D : CwFCat) {F : TmTyMorphism C D} [pres : IsoPreserveCwF F]
  {Γ Δ : C.Ctx} {T : Ty Γ} {f : Δ ⟶ Γ} {t : Tm (T⦃f⦄)}
  : MapSub F ⟪f, t⟫ ≫ snocIso.hom
    = ⟪MapSub F f, ↑ₜ (MapTm F t) ⟫  := by
    have vid : v⦃⟪f,t⟫⦄ = castTm t (by rw [tySubComp, CwFProp.ext_p])
       := CwFProp.ext_v (f := f) (t := t)
    have vCongr := Eq.symm (congrArg (MapTm F) vid)
    rw [MapTmCommut, ← castSymm] at vCongr <;> try simp only [vPreserve]
    rotate_left
    · rw [← MapTyCommut, tySubComp]
    simp only [vPreserve, castSub, tmSubComp, cast_cast, tySubComp, CwFProp.ext_p,
      CastMapTmCommut, castCastGen] at vCongr
    fapply CwFProp.ext_unique
    · rw [Category.assoc, ← pPreserve, MapSubComp, CwFProp.ext_p]
    · simp only [castTm, cast_cast]
      exact vCongr

/-- The form of `extPreserve'` solved for the image extension morphism. -/
@[simp]
theorem extPreserve (C D : CwFCat) {F : TmTyMorphism C D} [pres : IsoPreserveCwF F]
  {Γ Δ : C.Ctx} {T : Ty Γ} {f : Δ ⟶ Γ} {t : Tm (T⦃f⦄)}
  : MapSub F ⟪f,t⟫
    =  ⟪MapSub F f, ↑ₜ (MapTm F t) ⟫ ≫ snocIso.inv  := by
    symm
    rw [CategoryTheory.Iso.comp_inv_eq]
    symm
    apply extPreserve'


/-- A type-term morphism that preserves context comprehension strictly (on the
nose), as needed to organize CwFs into a category. -/
class StrictPreserveCwF {C D : CwFCat} (F : TmTyMorphism C D) : Prop where
  /-- The empty context is preserved on the nose. -/
  emptyPreserve :
    MapCtx F (CwFStruct.empty (C := C.Ctx)) = CwFStruct.empty (C := D.Ctx) := by aesop_cat
  /-- The image of an extended context equals the extension of the image. -/
  snocPreserve:
    {Γ : C.Ctx}
    → {T : Ty Γ}
    → MapCtx F (Γ ▹ T) = (MapCtx F Γ) ▹ (MapTy F T) := by aesop_cat
  /-- The projection is preserved on the nose. -/
  pPreserveStrict :
    {Γ : C.Ctx}
    → {T : Ty Γ}
    → MapSub F ((p_ T))
      = eqToHom snocPreserve ≫ p := by aesop_cat
  /-- The introduced variable is preserved on the nose. -/
  vPreserveStrict :
    {Γ : C.Ctx}
    → {T : Ty Γ}
    → (MapTm F ((v_ T)))
     =ₜ ((v_ (MapTy F T)))⦃eqToHom snocPreserve⦄  := by aesop_cat

open StrictPreserveCwF

instance strictIsoPreserve {C D : CwFCat} (F : TmTyMorphism C D) [StrictPreserveCwF F] :
    IsoPreserveCwF F where
  snocIso := eqToIso snocPreserve
  pPreserve := pPreserveStrict
  vPreserve := vPreserveStrict

theorem preserveId {C : CwFCat} : StrictPreserveCwF ⟨Functor.id C, NatTrans.id _⟩ where
  emptyPreserve := rfl
  snocPreserve := rfl
  pPreserveStrict := by
    intro Γ T
    simp only [MapSub, MapTy, MapCtx, CategoryTheory.Functor.id_obj,
      CategoryTheory.Functor.id_map, NatTrans.id_app', mapIxId, eqToHom_refl, Category.id_comp]
  vPreserveStrict := by
    intro Γ T
    apply Subtype.ext
    simp only [MapTm, MapTy, MapCtx, CategoryTheory.Functor.id_obj,
      NatTrans.id_app', castTm_val, tmSub_val, mapIxId, eqToHom_refl,
      CategoryTheory.op_id, Functor.map_id, Arrow.id_left]
    rfl

/-- The composite of two type-term morphisms. -/
def tmTyComp {C D E : CwFCat} (F : TmTyMorphism C D) (G : TmTyMorphism D E) : TmTyMorphism C E where
  CtxF := Functor.comp F.CtxF G.CtxF
  transSubst :=
    F.transSubst ≫ whiskerLeft F.CtxF.op G.transSubst
      ≫ (Functor.associator F.CtxF.op G.CtxF.op tmTyFam).inv

theorem MapCtxComp {C D E : CwFCat} (F : TmTyMorphism C D) (G : TmTyMorphism D E) {Γ : C.Ctx} :
    MapCtx (tmTyComp F G) Γ = MapCtx G (MapCtx F Γ)
  := by aesop


theorem MapSubTmTyComp {C D E : CwFCat} (F : TmTyMorphism C D) (G : TmTyMorphism D E)
    {Γ Δ : C.Ctx} {θ : Δ ⟶ Γ}
  : MapSub (tmTyComp F G) θ = MapSub G (MapSub F θ)
  := by aesop

theorem MapTm_TmTyComp {C D E : CwFCat} (F : TmTyMorphism C D) (G : TmTyMorphism D E)
    {Γ : C.Ctx} {T : Ty Γ} {t : Tm T}
  : MapTm (tmTyComp F G) t = MapTm G (MapTm F t)
  := by aesop


theorem preserveComp {C D E : CwFCat} {F : TmTyMorphism C D} {G : TmTyMorphism D E}
    [Fpres : StrictPreserveCwF F] [Gpres : StrictPreserveCwF G]
  : StrictPreserveCwF (tmTyComp F G) where
  emptyPreserve := by
    simp only [MapCtxComp]
    rw [Fpres.emptyPreserve, Gpres.emptyPreserve]

  snocPreserve := by
    intros
    simp only [MapCtxComp]
    simp [Fpres.snocPreserve, Gpres.snocPreserve]
    rfl

  pPreserveStrict := by
    intros Γ T
    rw [MapSubTmTyComp, Fpres.pPreserveStrict, ← MapSubComp, Gpres.pPreserveStrict]
    simp only [MapSub]
    rw [eqToHom_map G.CtxF Fpres.snocPreserve]
    dsimp only [MapCtx, MapTy]
    rw [← Category.assoc, eqToHom_trans]
    rfl

  vPreserveStrict := by
    intros Γ T
    rw [MapTm_TmTyComp]
    rw [Fpres.vPreserveStrict]
    let eq : MapTy F T⦃p⦄ = (MapTy F T)⦃p⦄⦃eqToHom (snocPreserve (T := T))⦄ := by
      simp [pPreserveStrict]
    rw [CastMapTmCommut (eq := eq)]
    rw [MapTmCommut]
    rw [Gpres.vPreserveStrict]
    simp only [castSub, castCast]
    apply Subtype.ext
    simp only [castTm_val, tmSub_val, MapSub]
    rw [eqToHom_map G.CtxF, ← types_comp_apply, ← Arrow.comp_left, ← Functor.map_comp,
      ← CategoryTheory.op_comp]
    dsimp only [MapCtx, MapTy]
    rw [eqToHom_trans]
    rfl




instance : Category CwFCat where
  Hom C D := {F : TmTyMorphism C D // StrictPreserveCwF F}
  id C := ⟨ ⟨Functor.id C, NatTrans.id _⟩, preserveId⟩
  comp F G := ⟨ tmTyComp F.val G.val , preserveComp (Fpres := F.prop) (Gpres := G.prop)⟩

end CwF

end LeanPool.LeanCwf
