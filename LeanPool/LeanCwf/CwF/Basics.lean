/-
Copyright (c) 2026 Joseph Eremondi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Eremondi
-/

import LeanPool.LeanCwf.CwF.Fam
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Logic.Unique

import LeanPool.LeanCwf.CwF.Util

namespace LeanPool.LeanCwf

open CategoryTheory
open Fam

namespace CwF

universe u v'

/-- Terms and types in a CwF, without the comprehension structure. A CwF over a
category of contexts has a `Fam`-valued presheaf assigning to each context the
family of its types and terms. We use `Fam.{u}`, so contexts, types and terms
all live in `Type u`, while hom-sets may have a different size `v'`. -/
class TmTy (Ctx : Type u) [Category.{v'} Ctx] : Type (max (u + 1) v') where
  /-- The `Fam`-valued presheaf assigning types and terms to each context. -/
  tmTyFam : CategoryTheory.Functor Ctxᵒᵖ Fam.{u}

open TmTy

variable {C : Type u} [cat : Category.{v'} C] [tmTy : TmTy.{u, v'} C]

/-- The index set of the presheaf gives the types over a given context. -/
def Ty (Γ : C) : Type u := ixSet (tmTyFam.obj (Opposite.op Γ))

/-- `Ty` packaged as a contravariant functor into `Type u`. -/
def TyFunctor : CategoryTheory.Functor Cᵒᵖ (Type u) :=
  Functor.comp tmTyFam projIx

/-- The family for a given context and type gives the set of terms of that type. -/
def Tm {Γ : C} (T : Ty Γ) : Type u := famFor (tmTyFam.obj (Opposite.op Γ)) T

/-- Substitution on types: any context morphism lifts to a function on types via
the functorial structure of the presheaf. -/
def tySub {Δ Γ : C} (T : Ty Δ) (θ : Γ ⟶ Δ) : Ty Γ :=
  mapIx (tmTyFam.map θ.op) T

/-- Notation for substitution on types. -/
notation:max T "⦃" θ "⦄" => tySub T θ

/-- Substitution on terms: like substitution on types, but the resulting term
also carries the substitution in its type. -/
def tmSub {Γ Δ : C} {T : Ty Δ} (t : Tm T) (θ : Γ ⟶ Δ) : Tm (T⦃θ⦄) :=
  mapFam (tmTyFam.map θ.op) t

/-- Notation for substitution on terms. -/
notation:max t "⦃" θ "⦄" => tmSub t θ

/-- The underlying value of a substituted term is the image of the original
value under the presheaf action. -/
@[simp]
theorem tmSub_val {Γ Δ : C} {T : Ty Δ} (t : Tm T) (θ : Γ ⟶ Δ) :
    (t⦃θ⦄).val = ((tmTyFam.map θ.op).left) t.val :=
  rfl

/-- Cast a term along an equality of its type. -/
abbrev castTm {Γ : C} {S T : Ty Γ} (t : Tm T) (eq : S = T) : Tm S :=
  cast (by aesop) t

/-- Casting a term along a type equality leaves its underlying value unchanged. -/
@[simp]
theorem castTm_val {Γ : C} {S T : Ty Γ} (t : Tm T) (eq : S = T) :
    (castTm t eq).val = t.val := by
  subst eq
  rfl

/-- Cast a substituted term along an equality of the substituting morphism. -/
abbrev castTmSub {Γ Δ : C} {f g : Δ ⟶ Γ} {T : Ty Γ} (t : Tm (T⦃f⦄)) (eq : f = g) :
    Tm (T⦃g⦄) :=
  cast (by aesop) t

/-- Two terms of types known to be equal are equal modulo the corresponding cast. -/
abbrev eqModCast {Γ : C} {S T : Ty Γ} (s : Tm S) (t : Tm T) (eq : S = T) : Prop :=
  s = castTm t (by aesop)

/-- Notation for casting a term up along an automatically-derived type equality. -/
notation:500 "↑ₜ" t => castTm t (by aesop)
/-- Notation for equality of terms modulo a cast. -/
notation:50 s "=ₜ" t => s = (↑ₜ t)

/-- Equality of terms modulo cast is symmetric. -/
theorem castSymm {Γ : C} {S T : Ty Γ} {s : Tm S} {t : Tm T} {eq : S = T} :
    (s =ₜ t) ↔ (t =ₜ s) := by
  constructor <;> aesop

/-- A cast commutes with substitution on terms. -/
@[simp]
theorem castSub {Γ Δ : C} {S T : Ty Γ} {t : Tm T} {eq : S = T} {f : Δ ⟶ Γ} :
    (castTm t eq)⦃f⦄ = castTm (t⦃f⦄) (by aesop) := by aesop

/-- Two successive casts compose into a single cast. -/
theorem castCast {Γ : C} {S T U : Ty Γ} {t : Tm U} {eq : S = T} {eq2 : T = U} :
    (castTm (castTm t eq2) eq) = castTm t (Eq.trans eq eq2) := by aesop

/-- Casting two terms along `rfl` preserves equality. -/
@[simp]
theorem castEq {Γ : C} {T : Ty Γ} {s t : Tm T} :
    castTm s rfl = castTm t rfl ↔ s = t := by aesop

/-- Equality of terms modulo cast is transitive. -/
theorem castTrans {Γ : C} {S T U : Ty Γ} {s : Tm S} {t : Tm T} {u : Tm U}
    {eq1 : S = T} {eq2 : T = U}
    (eqst : s=ₜt) (eqtu : t=ₜu) : s=ₜu := by aesop

/-- Two `cast`s into a common type are equal iff one is a cast of the other. -/
@[simp]
theorem castCastGen {X Y Z : Type u} {x : X} {y : Y}
    {eq1 : X = Z} {eq2 : Y = Z} :
    cast eq1 x = cast eq2 y ↔ x = cast (by aesop) y := by aesop

/-- Substitution distributes over a cast applied to the type being substituted. -/
theorem castTyOutOfSub {Γ1 Γ2 : C} {θ : Δ ⟶ Γ1} {T : Ty Γ2}
    {eq : Γ1 = Γ2} :
    T⦃cast (α := Δ ⟶ Γ1) (β := Δ ⟶ Γ2) (by rw [eq]) θ⦄
      = tySub (cast (by aesop) T) θ := by aesop

/-- Substitution distributes over a cast applied to the morphism being substituted. -/
@[simp]
theorem castOutOfSub {Δ Γ1 Γ2 : C} {θ : Δ ⟶ Γ1} {T : Ty Γ2} {t : Tm T}
    {eq : Γ1 = Γ2} :
    t⦃cast (α := Δ ⟶ Γ1) (β := Δ ⟶ Γ2) (by rw [eq]) θ⦄
      =ₜ castTm
        (S := tySub T (cast (by rw [eq]) θ)) (T := tySub (cast (by rw [eq]) T) θ)
        ((cast (by aesop) t)⦃θ⦄)
        (by aesop) := by aesop

/-- Substitution by the identity has no effect on types. -/
@[simp]
theorem tySubId {Γ : C} {T : Ty Γ} : T⦃𝟙 Γ⦄ = T := by
  simp only [tySub, op_id, Functor.map_id, mapIxId]

/-- Substitution by a composite is the composition of substitutions on types. -/
@[simp]
theorem tySubComp {Γ Δ Ξ : C} {T : Ty Γ} {g : Δ ⟶ Γ} {f : Ξ ⟶ Δ} :
    (T⦃g⦄)⦃f⦄ = T⦃f ≫ g⦄ := by
  simp only [tySub, op_comp, Functor.map_comp, mapIxComp, Function.comp_apply]

/-- Substitution by the identity has no effect on terms (up to cast). -/
@[simp]
theorem tmSubId {Γ : C} {T : Ty Γ} (t : Tm T) : (t⦃𝟙 Γ⦄) =ₜ t := by
  have eq := mapCast t (symm (tmTyFam.map_id (Opposite.op Γ)))
  simp only [tmSub, mapFamId] at eq ⊢
  apply Subtype.ext
  exact congrArg Subtype.val eq

/-- Substitution by a composite is the composition of substitutions on terms (up to cast). -/
@[simp]
theorem tmSubComp {Γ Δ Ξ : C} {T : Ty Γ} {f : Δ ⟶ Γ} {g : Ξ ⟶ Δ} {t : Tm T} :
    ((t⦃f⦄)⦃g⦄) =ₜ (t⦃g ≫ f⦄) := by
  apply Subtype.ext
  rw [castTm_val]
  change ((tmTyFam.map g.op).left) (((tmTyFam.map f.op).left) t.val)
    = (mapFam (tmTyFam.map (g ≫ f).op) t).val
  rw [show (g ≫ f).op = f.op ≫ g.op from rfl, tmTyFam.map_comp]
  rfl

/-- The reversed form of `tmSubComp`, convenient for rewriting. -/
theorem tmSubComp' {Γ Δ Ξ : C} {T : Ty Γ} {f : Δ ⟶ Γ} {g : Ξ ⟶ Δ} {t : Tm T} :
    (t⦃g ≫ f⦄) =ₜ ((t⦃f⦄)⦃g⦄) := by simp

/-- Substitution on types respects heterogeneous equality of morphisms. -/
theorem tySubExt {Γ Δ Ξ : C} {f : Δ ⟶ Γ} {g : Ξ ⟶ Γ} {T : Ty Γ} (ctxEq : Δ = Ξ)
    (eq : HEq f g) :
    HEq T⦃f⦄ T⦃g⦄ := by aesop

/-- Substituting along equal morphisms agrees up to cast. -/
theorem tmSubCast {Γ Δ : C} {T : Ty Γ} {f g : Δ ⟶ Γ} {t : Tm T} (eq : f = g) :
    t⦃f⦄ = ↑ₜ t⦃g⦄ := by aesop

/-- Heterogeneously equal types over equal contexts have equal term sets. -/
theorem tmHeq {Γ Δ : C} {S : Ty Γ} {T : Ty Δ} (eq : Γ = Δ) (heq : HEq S T) :
    Tm (Γ := Γ) S = Tm T := by aesop

/-- Isomorphic contexts have isomorphic sets of types. -/
def ctxIsoToType {Γ Δ : C} (iso : Γ ≅ Δ) : Ty Γ ≅ Ty Δ := by
  simp only [Ty]
  apply Functor.mapIso TyFunctor
  apply Iso.op
  exact iso.symm

/-- The forward map of `ctxIsoToType` is substitution along the inverse. -/
@[simp]
theorem ctxIsoTypeSubHom {Γ Δ : C} (iso : Γ ≅ Δ) {T : Ty Γ} :
    (ctxIsoToType iso).hom T = T⦃iso.inv⦄ := by aesop

/-- The backward map of `ctxIsoToType` is substitution along the forward map. -/
@[simp]
theorem ctxIsoTypeSubInv {Γ Δ : C} (iso : Γ ≅ Δ) {T : Ty Δ} :
    (ctxIsoToType iso).inv T = T⦃iso.hom⦄ := by aesop

/-- Context isomorphisms can be transported over term sets. -/
def ctxIsoToTm {Γ Δ : C} (iso : Γ ≅ Δ) {T : Ty Γ} :
    Tm T ≅ Tm ((ctxIsoToType iso).hom T) where
  hom := TypeCat.ofHom fun (t : Tm T) =>
    castTm (t⦃iso.inv⦄) (S := (ctxIsoToType iso).hom T) (ctxIsoTypeSubHom iso)
  inv := TypeCat.ofHom fun (t : Tm ((ctxIsoToType iso).hom T)) =>
    castTm ((castTm t (ctxIsoTypeSubHom iso).symm)⦃iso.hom⦄) (S := T) (by simp)
  hom_inv_id := by
    apply ConcreteCategory.hom_ext
    intro t
    apply Subtype.ext
    rw [ConcreteCategory.comp_apply, TypeCat.ofHom_apply, TypeCat.ofHom_apply,
      ConcreteCategory.id_apply]
    simp only [castTm_val, tmSub_val]
    rw [← types_comp_apply ((tmTyFam.map iso.inv.op).left) ((tmTyFam.map iso.hom.op).left),
      ← Arrow.comp_left, ← Functor.map_comp, ← op_comp, Iso.hom_inv_id, op_id,
      Functor.map_id, Arrow.id_left]
    rfl
  inv_hom_id := by
    apply ConcreteCategory.hom_ext
    intro t
    apply Subtype.ext
    rw [ConcreteCategory.comp_apply, TypeCat.ofHom_apply, TypeCat.ofHom_apply,
      ConcreteCategory.id_apply]
    simp only [castTm_val, tmSub_val]
    rw [← types_comp_apply ((tmTyFam.map iso.hom.op).left) ((tmTyFam.map iso.inv.op).left),
      ← Arrow.comp_left, ← Functor.map_comp, ← op_comp, Iso.inv_hom_id, op_id,
      Functor.map_id, Arrow.id_left]
    rfl

/-- Context comprehension: extending a context by a type, with a projection
substitution that weakens by introducing an unused variable, the variable
introduced by the extension, and the operation extending a morphism into the
extended context. -/
class CwFExt (C : Type u) [Category.{v'} C] [tmTy : TmTy C] : Type _ where
  /-- Context extension: extend a context `Γ` by a type over `Γ`. -/
  snoc : (Γ : C) → Ty Γ → C
  /-- The projection substitution weakening a type/term by introducing an unused
  variable. -/
  p_ : {Γ : C} → (T : Ty Γ) → snoc Γ T ⟶ Γ
  /-- The variable introduced by extending a context. -/
  v_ : {Γ : C} → (T : Ty Γ) → Tm (T⦃p_ T⦄ : Ty (snoc Γ T))
  /-- Extend a morphism into the extended context: do whatever `f` does, and map
  the newly introduced variable to `t`. -/
  ext : {Γ Δ : C} → {T : Ty Γ} → (f : Δ ⟶ Γ) → (t : Tm (T⦃f⦄)) → Δ ⟶ snoc Γ T

open CwFExt
/-- Notation for context extension. -/
notation:max Γ:1000 "▹" T:max => snoc Γ T
/-- Notation for an extended morphism. -/
notation:max "⟪" θ "," t "⟫" => ext θ t

/-- Notation for the projection substitution. -/
notation:max "p" => p_ _
/-- Notation for the introduced variable. -/
notation:max "v" => v_ _

/-- Bind the variable of an extended context to produce a type over it. -/
def bindTy {C : Type u} [Category.{v'} C] [tmTy : TmTy C] [CwFExt C]
    {Γ : C} {S : Ty Γ}
    (f : Tm S⦃p_ S⦄ → Ty (Γ▹S)) :
    Ty (Γ▹S) := f (v_ S)

/-- Bind the variable of an extended context to produce a term over it. -/
def bindTm {C : Type u} [Category.{v'} C] [tmTy : TmTy C] [CwFExt C]
    {Γ : C} {S : Ty Γ} {T : Ty (Γ▹S)}
    (f : Tm S⦃p_ S⦄ → Tm T) :
    Tm T := f (v_ S)

/-- Bind the variable of an extended context to produce a dependent type-term pair. -/
def bindTmTy {C : Type u} [Category.{v'} C] [tmTy : TmTy C] [CwFExt C]
    {Γ : C} {S : Ty Γ}
    (f : Tm S⦃p_ S⦄ → ((T : Ty (Γ▹S)) × Tm T)) :
    Tm (f v).fst := (f v).snd

/-- The laws governing context comprehension: the projection cancels an
extension, the introduced variable picks out the term used to extend, and the
extension morphism is the unique one satisfying these laws. -/
class CwFProp (C : Type u) [catInst : Category.{v'} C] [tmTy : TmTy C] [cwf : CwFExt C] :
    Prop where
  /-- Extending and then projecting recovers the original substitution. -/
  ext_p : {Γ Δ : C} → {T : Ty Γ}
    → {f : Δ ⟶ Γ} → {t : Tm (T⦃f⦄)}
    → ⟪f , t⟫ ≫ p = f := by aesop_cat

  /-- A derived equality, stated explicitly so the type of later fields is
  easier to express. -/
  ext_pHelper : {Γ Δ : C} → {S : Ty Γ}
    → {f : Δ ⟶ Γ} → {t : Tm (S⦃f⦄)} → {T : Ty _}
    → (T⦃p⦄⦃ext f t⦄) = T⦃f⦄ :=
    fun {_ _} {_} {f} {_} {T} =>
      of_eq_true ((congrArg (fun x => x = T⦃f⦄)
        (tySubComp.trans (congrArg (tySub T) ext_p))).trans (eq_self T⦃f⦄))

  /-- An extended substitution maps the introduced variable to the extending term. -/
  ext_v : {Γ Δ : C} → {T : Ty Γ} → (f : Δ ⟶ Γ) → (t : Tm (T⦃f⦄))
    → v⦃⟪f,t⟫⦄ = castTm t ext_pHelper := by aesop_cat

  /-- The extension morphism is unique. -/
  ext_unique : {Γ Δ : C} → {T : Ty Γ} → (f : Δ ⟶ Γ)
    → (t : Tm T⦃f⦄) → (g : _)
    → (peq : g ≫ p = f)
    → (v⦃g⦄ = castTm t (by rw [tySubComp, peq]))
    → g = ⟪f,t⟫ := by aesop_cat

attribute [simp] CwFProp.ext_p CwFProp.ext_v

open CwFProp

/-- A category with families: a type-term structure together with context
comprehension, its laws, and a terminal (empty) context. -/
class CwFStruct (C : Type u) [cat : Category.{v'} C] : Type _ where
  /-- The empty context. -/
  empty : C
  /-- The empty context is terminal. -/
  emptyTerminal : Limits.IsTerminal empty
  /-- The underlying type-term structure. -/
  [tmTy : TmTy C]
  /-- The context comprehension structure. -/
  [cwfExt : CwFExt C]
  /-- The laws governing context comprehension. -/
  [cwfProp : CwFProp C]

/-- The unique weakening substitution from any context into the empty context. -/
def wkAll {C : Type u} [Category.{v'} C] [cwf : CwFStruct C] (Γ : C) : Γ ⟶ cwf.empty :=
  Limits.IsTerminal.from cwf.emptyTerminal Γ

/-- Notation for the empty context. -/
notation:max "⬝" => CwFStruct.empty
/-- Notation for the weakening substitution into the empty context, with explicit context. -/
notation:max "⟨⟩" T => wkAll T
/-- Notation for the weakening substitution into the empty context. -/
notation:max "‼" => wkAll _

attribute [reducible, instance] CwFStruct.tmTy CwFStruct.cwfExt
attribute [instance] CwFStruct.cwfProp

/-- A reassociated form of `CwFProp.ext_p`, convenient for `simp`. -/
@[simp]
theorem ext_p_comp {C : Type u} [Category.{v'} C] [cwf : CwFStruct C] {Γ Δ Ξ : C} {T : Ty Γ}
    {f : Δ ⟶ Γ} {g : Γ ⟶ Ξ} {t : Tm (T⦃f⦄)} :
    ⟪f , t⟫ ≫ (p ≫ g) = f ≫ g := by simp only [← Category.assoc, CwFProp.ext_p]

/-- Any CwF has a terminal object, namely the empty context. -/
instance hasTerminalOfCwF (C : Type u) [Category.{v'} C] [CwFStruct C] : Limits.HasTerminal C :=
  Limits.IsTerminal.hasTerminal CwFStruct.emptyTerminal

/-- Every morphism into the empty context is the canonical one. -/
theorem toEmptyUnique {C : Type u} [cat : Category.{v'} C] [cwf : CwFStruct C] {Γ : C} {θ : Γ ⟶ ⬝} :
    θ = ‼ := (Limits.IsTerminal.hom_ext cwf.emptyTerminal ‼ θ).symm

/-- The morphisms into the empty context form a singleton. -/
instance uniqueToEmpty {C : Type u} [cat : Category.{v'} C] [cwf : CwFStruct C] {Γ : C} :
    Unique (Γ ⟶ ⬝) where
  default := ‼
  uniq _ := toEmptyUnique

/-- Composing with the weakening into the empty context yields that weakening. -/
theorem toEmptyComp {C : Type u} [cat : Category.{v'} C] [cwf : CwFStruct C] {Γ Δ : C} {θ : Δ ⟶ Γ} :
    θ ≫ ‼ = ‼ := by
  simp only [toEmptyUnique]

/-- A reassociated form of `toEmptyComp`. -/
@[simp]
theorem toEmptyCompComp {C : Type u} [cat : Category.{v'} C] [cwf : CwFStruct C] {Γ Δ Ξ : C}
    {θ : Δ ⟶ Γ} {g : ⬝ ⟶ Ξ} :
    θ ≫ (‼ ≫ g) = ‼ ≫ g := by
  simp only [← Category.assoc, toEmptyComp]

/-- The unique self-morphism of the empty context is the identity. -/
theorem emptySelfUnique {C : Type u} [cat : Category.{v'} C] [cwf : CwFStruct C] :
    ‼ = 𝟙 cwf.empty := toEmptyUnique.symm

/-- The weakening into the empty context is a left identity for composition. -/
@[simp]
theorem emptySelfComp {C : Type u} [cat : Category.{v'} C] [cwf : CwFStruct C] {Γ : C} {f : ⬝ ⟶ Γ} :
    ‼ ≫ f = f := by
  rw [emptySelfUnique]
  simp only [Category.id_comp]

attribute [simp] CwFProp.ext_p CwFProp.ext_v

end CwF

end LeanPool.LeanCwf
