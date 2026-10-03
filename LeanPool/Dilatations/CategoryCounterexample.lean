/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arnaud Mayeux
-/
module

public import LeanPool.Dilatations.Centers
public import Mathlib.CategoryTheory.SingleObj

/-!
# A category extension that is not a dilatation

From Arnaud Mayeux, *Dilatations of categories, via their Lean formalization*,
https://arxiv.org/abs/2608.09305, and `rndmx/DilCat` at commit
`604559654c948566675da3f7709b8ad3126bd487` (Apache-2.0).
-/

public section

noncomputable section

open CategoryTheory Finset
open CategoryTheory.Localization.Construction

universe v u v' pu pv u₁ v₁ u₂ v₂ u₃ v₃

namespace CategoryTheory.Dilatations

variable {C : Type u} [Category.{v} C]
variable (Z : Center C)
variable {D : Type u} [Category.{v'} D]
variable (F : C ⥤ D)

/-! ### Fact 5.2 : the "sub-algebra" characterization of ring dilatations fails for categories

A concrete counterexample : a category `C` with two objects `X, Y` and two parallel non-identity
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

lemma Gamma_b : Gamma (CHom.b) := by rfl

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
  change FSep'.map (Gamma.Q.map CHom.a ≫ inv (Gamma.Q.map CHom.b) ≫ Gamma.Q.map CHom.a) = _
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

/-- Composition in the three-arrow counterexample category. -/
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
        | (change DtoLocMap DHom.c = 𝟙 _ ≫ DtoLocMap DHom.c
           rw [Category.id_comp])
        | (change DtoLocMap DHom.c = DtoLocMap DHom.c ≫ 𝟙 _
           rw [Category.comp_id])

lemma CHom.idX_eq : (CHom.idX : CHom .X .X) = 𝟙 Obj.X := rfl
lemma CHom.idY_eq : (CHom.idY : CHom .Y .Y) = 𝟙 Obj.Y := rfl

/-- The triangle `C → D → C[Γ⁻¹]` commutes with `C → C[Γ⁻¹]`. -/
theorem CtoD_comp_DtoLoc : CtoD ⋙ DtoLoc = Gamma.Q := by
  refine Functor.ext (fun P => by cases P <;> rfl) ?_
  intro P Q f
  cases f <;>
    change _ = 𝟙 _ ≫ _ ≫ 𝟙 _ <;>
    simp only [Category.id_comp]
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
`fractionInDilatation_eq_of_factors`: every sieve-witness `m ∈ Z.N i` factors through the
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
    unfold GoodCenter at hbad; push Not at hbad; exact hbad
  rcases Center.dom_cod_cases Z i with ⟨hd, hc⟩ | ⟨hd, hc⟩ | ⟨hd, hc⟩
  · exact false_of_hnq_selfmor (hd.trans hc.symm) m (Z.mor i) hnq
  · exact false_of_hnq_selfmor (hd.trans hc.symm) m (Z.mor i) hnq
  · exact false_of_hnq_case3 hd hc (CatToDila Z) (Z.N i) (Z.mor i) m hm hnq
      (fun {X''} m' hm' => fractionInDilatation Z ⟨i, ⟨X'', ⟨m', hm'⟩⟩⟩)
      (fun {X''} m' hm' => fraction_in_dila_comp_mor Z i X'' m' hm')
      false_of_hom_YX false_of_endX_ne_id (CatToDila_a_ne_b Z)

/-- **Case (ii), core step.** Under `GoodCenter Z`, every morphism of the generated category
(hence, via `GeneratedToDila_full`, every morphism of `Dila Z`) between the images of two objects
of `Obj` is `Θ` applied to some morphism of `Obj`. This collapses every `fraction` edge back to an
`original` edge using `fractionInDilatation_eq_of_factors`, driven by the factorization
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
        exact ⟨q, fractionInDilatation_eq_of_factors Z p.1 p.2.1 q p.2.2.1 p.2.2.2 hq⟩

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

end CategoryTheory.Dilatations
