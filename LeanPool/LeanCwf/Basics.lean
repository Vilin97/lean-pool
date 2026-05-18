/-
Copyright (c) 2026 Joseph Eremondi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Eremondi
-/

import LeanPool.LeanCwf.Fam
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Logic.Unique

import LeanPool.LeanCwf.Util

namespace LeanPool.LeanCwf

open CategoryTheory
open Fam



namespace CwF

universe u v'


/--
The type-and-term presheaf of a category with families, before adding comprehension structure.

Objects of `Ctx` are contexts. The presheaf is valued in `Fam`, so its indices are types over
a context and its fibers are terms of those types.
-/
class TmTy (Ctx : Type u) [Category.{v'} Ctx] : Type (max (u+1) v') where
  /-- The family-valued presheaf of types and terms. -/
  tmTyFam : CategoryTheory.Functor Ctxᵒᵖ Fam.{u}

open TmTy

variable {C : Type u} [cat : Category.{v'} C] [tmTy : TmTy.{u, v'} C]

/-- Types over a context. -/
def Ty (Γ : C) : Type u := ixSet (tmTyFam.obj (Opposite.op Γ))

/-- The contravariant functor of types over contexts. -/
def TyFunctor : CategoryTheory.Functor Cᵒᵖ (Type u) :=
  Functor.comp tmTyFam projIx

/-- Terms of a type over a context. -/
def Tm {Γ : C} (T : Ty Γ) : Type u :=
  famFor (tmTyFam.obj (Opposite.op Γ)) T

/-- Substitution of a type along a context morphism. -/
def tySub {Δ Γ : C} (T : Ty Δ) (θ : Γ ⟶ Δ) : Ty Γ :=
  mapIx (tmTyFam.map θ.op) T

/-- Notation for substitution of a type along a context morphism. -/
notation:max T "⦃" θ "⦄" => tySub T θ

/-- Substitution of a term along a context morphism. -/
def tmSub {Γ Δ : C} {T : Ty Δ} (t : Tm T) (θ : Γ ⟶ Δ) : Tm (T⦃θ⦄) :=
  mapFam (tmTyFam.map θ.op) t

/-- Notation for substitution of a term along a context morphism. -/
notation:max t "⦃" θ "⦄" => tmSub t θ

/-- Casts a term across an equality of types over the same context. -/
abbrev castTm {Γ : C} {S T : Ty Γ} (t : Tm T) (eq : S = T) : Tm S :=
  cast (by aesop) t

/-- Casts a substituted term across an equality of substitutions. -/
abbrev castTmSub {Γ Δ : C} {f g : Δ ⟶ Γ} {T : Ty Γ} (t : Tm (T⦃f⦄))
    (eq : f = g) : Tm (T⦃g⦄) :=
  cast (by aesop) t

/-- Equality of terms modulo the canonical cast between their types. -/
abbrev eqModCast {Γ : C} {S T : Ty Γ} (s : Tm S) (t : Tm T) (eq : S = T) :
    Prop :=
  s = castTm t (by aesop)

/-- Notation for inserting the canonical term cast. -/
notation:500 "↑ₜ" t => castTm t (by aesop)
/-- Notation for equality of terms modulo the canonical term cast. -/
notation:50 s "=ₜ" t => s = (↑ₜ t)

theorem castSymm {Γ : C} {S T : Ty Γ} {s : Tm S} {t : Tm T} {eq : S = T} :
    (s =ₜ t) ↔ (t =ₜ s) := by
  constructor <;> aesop

@[simp]
theorem castSub {Γ Δ : C} {S T : Ty Γ} {t : Tm T} {eq : S = T} {f : Δ ⟶ Γ} :
    (castTm t eq)⦃f⦄ = castTm (t⦃f⦄) (by aesop) := by aesop

theorem castCast {Γ : C} {S T U : Ty Γ} {t : Tm U} {eq : S = T} {eq2 : T = U} :
    castTm (castTm t eq2) eq = castTm t (Eq.trans eq eq2) := by aesop

@[simp]
theorem castEq {Γ : C} {T : Ty Γ} {s t : Tm T} :
    castTm s rfl = castTm t rfl ↔ s = t := by aesop

theorem castTrans {Γ : C} {S T U : Ty Γ} {s : Tm S} {t : Tm T} {u : Tm U}
    {eq1 : S = T} {eq2 : T = U} (eqst : s=ₜt) (eqtu : t=ₜu) : s=ₜu := by
  aesop

@[simp]
theorem castCastGen {X Y Z : Type u} {x : X} {y : Y} {eq1 : X = Z} {eq2 : Y = Z} :
    cast eq1 x = cast eq2 y ↔ x = cast (by aesop) y := by aesop

theorem castTyOutOfSub {Γ1 Γ2 : C} {θ : Δ ⟶ Γ1} {T : Ty Γ2} {eq : Γ1 = Γ2} :
    T⦃cast (α := Δ ⟶ Γ1) (β := Δ ⟶ Γ2) (by rw [eq]) θ⦄ =
      tySub (cast (by aesop) T) θ := by aesop

@[simp]
theorem castOutOfSub {Δ Γ1 Γ2 : C} {θ : Δ ⟶ Γ1} {T : Ty Γ2} {t : Tm T}
    {eq : Γ1 = Γ2} :
    t⦃cast (α := Δ ⟶ Γ1) (β := Δ ⟶ Γ2) (by rw [eq]) θ⦄ =ₜ
      castTm
        (S := tySub T (cast (by rw [eq]) θ)) (T := tySub (cast (by rw [eq]) T) θ)
        ((cast (by aesop) t)⦃θ⦄)
        (by aesop) := by aesop

@[simp]
theorem tySubId {Γ : C} {T : Ty Γ} : T⦃𝟙 Γ⦄ = T := by
  simp [tySub]

@[simp]
theorem tySubComp {Γ Δ Ξ : C} {T : Ty Γ} {g : Δ ⟶ Γ} {f : Ξ ⟶ Δ} :
    (T⦃g⦄)⦃f⦄ = T⦃f ≫ g⦄ := by
  simp [tySub]

@[simp]
theorem tmSubId {Γ : C} {T : Ty Γ} (t : Tm T) : (t⦃𝟙 Γ⦄)=ₜt := by
  simp only [tySub, tmSub]
  have eq := mapCast t (symm (tmTyFam.map_id (Opposite.op Γ)))
  aesop_cat

@[simp]
theorem tmSubComp {Γ Δ Ξ : C} {T : Ty Γ} {f : Δ ⟶ Γ} {g : Ξ ⟶ Δ} {t : Tm T} :
    ((t⦃f⦄)⦃g⦄)=ₜ(t⦃g ≫ f⦄) := by
  simp only [tySub, tmSub]
  have eq := mapCast t (tmTyFam.map_comp f.op g.op)
  aesop_cat

@[aesop safe apply]
theorem tmSubComp' {Γ Δ Ξ : C} {T : Ty Γ} {f : Δ ⟶ Γ} {g : Ξ ⟶ Δ} {t : Tm T} :
    (t⦃g ≫ f⦄)=ₜ((t⦃f⦄)⦃g⦄) := by simp

theorem tySubExt {Γ Δ Ξ : C} {f : Δ ⟶ Γ} {g : Ξ ⟶ Γ} {T : Ty Γ}
    (ctxEq : Δ = Ξ) (eq : HEq f g) : HEq T⦃f⦄ T⦃g⦄ := by aesop

theorem tmSubCast {Γ Δ : C} {T : Ty Γ} {f g : Δ ⟶ Γ} {t : Tm T} (eq : f = g) :
    t⦃f⦄ = ↑ₜ t⦃g⦄ := by aesop

theorem tmHeq {Γ Δ : C} {S : Ty Γ} {T : Ty Δ} (eq : Γ = Δ) (heq : HEq S T) :
    Tm (Γ := Γ) S = Tm T := by aesop

/-- A context isomorphism induces an isomorphism between the corresponding type fibers. -/
def ctxIsoToType {Γ Δ : C} (iso : Γ ≅ Δ) : Ty Γ ≅ Ty Δ :=
  Functor.mapIso TyFunctor iso.symm.op

@[simp]
theorem ctxIsoTypeSubHom {Γ Δ : C} (iso : Γ ≅ Δ) {T : Ty Γ} :
    (ctxIsoToType iso).hom T = T⦃iso.inv⦄ := by aesop

@[simp]
theorem ctxIsoTypeSubInv {Γ Δ : C} (iso : Γ ≅ Δ) {T : Ty Δ} :
    (ctxIsoToType iso).inv T = T⦃iso.hom⦄ := by aesop


/-- Context extension operations for a category with families. -/
class CwFExt (C : Type u) [Category.{v'} C] [tmTy : TmTy C] : Type _ where
  /-- Extends a context by a type. -/
  snoc : (Γ : C) → Ty Γ → C
  /-- The projection from an extended context to its base context. -/
  p_ : {Γ : C} → (T : Ty Γ) → snoc Γ T ⟶ Γ
  /-- The variable introduced by extending a context. -/
  v_ : {Γ : C} → (T : Ty Γ) → Tm (T⦃p_ T⦄ : Ty (snoc Γ T))
  /-- Extends a substitution with a term for the newly introduced variable. -/
  ext : {Γ Δ : C} → {T : Ty Γ} → (f : Δ ⟶ Γ) → (t : Tm (T⦃f⦄)) → Δ ⟶ snoc Γ T


open CwFExt
/-- Notation for extending a context by a type. -/
notation:max Γ:1000 "▹" T:max => snoc Γ T
/-- Notation for extending a substitution by a term. -/
notation:max "⟪" θ "," t "⟫" => ext θ t


/-- Notation for the projection from an extended context. -/
notation:max "p" => p_ _
/-- Notation for the variable of an extended context. -/
notation:max "v" => v_ _


/-- Binds the variable of an extended context into a type expression. -/
def bindTy {C : Type u} [Category.{v'} C] [tmTy : TmTy C] [CwFExt C]
  {Γ : C} {S : Ty Γ}
  (f : Tm S⦃p_ S⦄ → Ty (Γ▹S))
  : Ty (Γ▹S) := f (v_ S)

/-- Binds the variable of an extended context into a term expression. -/
def bindTm {C : Type u} [Category.{v'} C] [tmTy : TmTy C] [CwFExt C]
  {Γ : C} {S : Ty Γ} {T : Ty (Γ▹S)}
  (f : Tm S⦃p_ S⦄ → Tm T)
  : Tm T := f (v_ S)

/-- Binds the variable of an extended context into a dependent pair of type and term. -/
def bindTmTy {C : Type u} [Category.{v'} C] [tmTy : TmTy C] [CwFExt C]
  {Γ : C} {S : Ty Γ}
  (f : Tm S⦃p_ S⦄ → ((T : Ty (Γ▹S)) × Tm T)) :
  Tm (f v).fst := (f v).snd

-- abbrev p (C : Type u) [Category.{v'} C]  [tmTy : TmTy C] [CwFExt C]
--   {Γ : C} {T : Ty Γ} : snoc Γ T ⟶ Γ := p_ T

-- abbrev v (C : Type u) [Category.{v'} C]  [tmTy : TmTy C] [CwFExt C]
--   {Γ : C} {T : Ty Γ} : Tm (T⦃p_ T⦄ : Ty (snoc Γ T)) := v_ T

/-- The defining equations for context extension in a category with families. -/
class CwFProp (C : Type u) [catInst : Category.{v'} C] [tmTy : TmTy C] [cwf : CwFExt C] :
    Prop where
  /-- Extending a substitution and then projecting recovers the original substitution. -/
  ext_p : {Γ Δ : C} → {T : Ty Γ}
    → {f : Δ ⟶ Γ} → {t : Tm (T⦃f⦄)}
    → ⟪f , t⟫ ≫ p = f

  /-- A transport helper derived from the projection law. -/
  ext_pHelper : {Γ Δ : C} → {S : Ty Γ}
    → {f : Δ ⟶ Γ} → {t : Tm (S⦃f⦄)} → {T : Ty _}
    → (T⦃p⦄⦃ext f t⦄) = T⦃f⦄ :=
    fun {_ _} {_} {f} {_} {T} =>
      of_eq_true
        ((congrArg (fun x => x = T⦃f⦄)
          (tySubComp.trans (congrArg (tySub T) ext_p))).trans (eq_self T⦃f⦄))

  /-- Substituting along an extended substitution sends the new variable to the extension term. -/
  ext_v : {Γ Δ : C} → {T : Ty Γ} → (f : Δ ⟶ Γ) → (t : Tm (T⦃f⦄))
    → v⦃⟪f,t⟫⦄ = castTm t (ext_pHelper)

  /-- The extension operation is uniquely determined by the projection and variable laws. -/
  ext_unique : {Γ Δ : C} → {T : Ty Γ} → (f : Δ ⟶ Γ)
    → (t : Tm T⦃f⦄) → (g : _)
    → (peq : g ≫ p = f)
    → (v⦃g⦄ = castTm t (by rw [tySubComp, peq]))
    → g = ⟪f,t⟫

attribute [simp] CwFProp.ext_p CwFProp.ext_v

open CwFProp

/-- A category with families, including an empty context and context extension. -/
class Structure (C : Type u) [cat : Category.{v'} C] : Type _ where
  /-- The empty context. -/
  empty : C
  /-- The empty context is terminal. -/
  emptyTerminal : Limits.IsTerminal empty
  /-- The type-and-term presheaf. -/
  [tmTy : TmTy C]
  /-- Context extension operations. -/
  [cwfExt : CwFExt C]
  /-- Context extension equations. -/
  [cwfProp : CwFProp C]


/-- The unique substitution from a context to the empty context. -/
def wkAll {C : Type u} [Category.{v'} C] [cwf : Structure C] (Γ : C) : Γ ⟶ cwf.empty :=
  Limits.IsTerminal.from cwf.emptyTerminal Γ

/-- Notation for the empty context. -/
notation:max "⬝" => Structure.empty
/-- Notation for the unique substitution to the empty context. -/
notation:max "⟨⟩" T => wkAll T
/-- Notation for the inferred unique substitution to the empty context. -/
notation:max "‼" => wkAll _

attribute [reducible, instance] Structure.tmTy Structure.cwfExt
attribute [instance] Structure.cwfProp



-- Version of ext_p that works better with reassociating
@[simp]
theorem ext_p_comp {C : Type u} [Category.{v'} C] [cwf : Structure C] {Γ Δ Ξ : C}
    {T : Ty Γ} {f : Δ ⟶ Γ} {g : Γ ⟶ Ξ} {t : Tm (T⦃f⦄)} :
    ⟪f , t⟫ ≫ (p ≫ g) = f ≫ g := by simp [<- Category.assoc]

-- Any CwF is a terminal category
instance (C : Type u) [Category.{v'} C] [Structure C] : Limits.HasTerminal C :=
  Limits.IsTerminal.hasTerminal Structure.emptyTerminal

--Not sure why this isn't in mathlib

-- All arrows into ⬝ are equal
theorem toEmptyUnique {C : Type u} [cat : Category.{v'} C] [cwf : Structure C] {Γ : C}
    {θ : Γ ⟶ ⬝} :
    θ = ‼ := (Limits.IsTerminal.hom_ext cwf.emptyTerminal ‼ θ).symm

instance {C : Type u} [cat : Category.{v'} C] [cwf : Structure C] {Γ : C}
  : Unique (Γ ⟶ ⬝) where
  default := ‼
  uniq _ := toEmptyUnique

-- Version of the above that works better with simp
-- Composing with ‼ produces ‼
theorem toEmptyComp {C : Type u} [cat : Category.{v'} C] [cwf : Structure C] {Γ Δ : C}
    {θ : Δ ⟶ Γ} :
    θ ≫ ‼ = ‼ := by
  exact toEmptyUnique (θ := θ ≫ (‼ : Γ ⟶ ⬝))


@[simp]
theorem toEmptyCompComp {C : Type u} [cat : Category.{v'} C] [cwf : Structure C] {Γ Δ Ξ : C}
    {θ : Δ ⟶ Γ} {g : ⬝ ⟶ Ξ} :
    θ ≫ (‼ ≫ g) = ‼ ≫ g := by
  rw [← Category.assoc, toEmptyComp]

-- Only one self-arrow into empty
theorem emptySelfUnique {C : Type u} [cat : Category.{v'} C] [cwf : Structure C]
  : ‼ = 𝟙 (cwf.empty) := by
  exact (toEmptyUnique (θ := 𝟙 (cwf.empty))).symm

@[simp]
theorem emptySelfComp {C : Type u} [cat : Category.{v'} C] [cwf : Structure C] {Γ : C} {f : ⬝ ⟶ Γ}
  : ‼ ≫ f = f := by
    rw [emptySelfUnique]
    simp only [Category.id_comp]

attribute [simp] ext_p ext_v


end CwF

end LeanPool.LeanCwf
