/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Logic.LogicSymbol
import LeanPool.Incompleteness.Foundation.Logic.Semantics
import LeanPool.Incompleteness.Foundation.Vorspiel.Collection

/-!
# Basic definitions and properties of proof system related notions

This file defines a characterization of the system/proof/provability/calculus of formulae.
Also defines soundness and completeness.

## Main Definitions
* `LO.Entailment F S`: a general framework of deductive system `S` for formulae `F`.
* `LO.Entailment.Inconsistent 𝓢`: a proposition that states that all formulae in `F` is provable
* from `𝓢`.
* `LO.Entailment.Consistent 𝓢`: a proposition that states that `𝓢` is not inconsistent.
* `LO.Entailment.Sound 𝓢 𝓜`: provability from `𝓢` implies satisfiability on `𝓜`.
* `LO.Entailment.Complete 𝓢 𝓜`: satisfiability on `𝓜` implies provability from `𝓢`.

## Notation
* `𝓢 ⊢ φ`: a type of formalized proofs of `φ : F` from deductive system `𝓢 : S`.
* `𝓢 ⊢! φ`: a proposition that states there is a proof of `φ` from `𝓢`, i.e. `φ` is provable from
* `𝓢`.
* `𝓢 ⊬ φ`: a proposition that states `φ` is not provable from `𝓢`.
* `𝓢 ⊢* T`: a type of formalized proofs for each formulae in a set `T` from `𝓢`.
* `𝓢 ⊢!* T`: a proposition that states each formulae in `T` is provable from `𝓢`.

-/

namespace LO

/-- Imported declaration from the Incompleteness formalization. -/
class Entailment (F : outParam Type*) (S : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Prf : S → F → Type*

/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊢ " => Entailment.Prf

namespace Entailment

variable {F : Type*} {S T U : Type*} [Entailment F S] [Entailment F T] [Entailment F U]

section «lp_section_1»

variable (𝓢 : S)

/-- Imported declaration from the Incompleteness formalization. -/
def Provable (f : F) : Prop := Nonempty (𝓢 ⊢ f)

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Unprovable (f : F) : Prop := ¬Provable 𝓢 f

/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊢! " => Provable

/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊬ " => Unprovable

/-- Imported declaration from the Incompleteness formalization. -/
def PrfSet (s : Set F) : Type _ := {f : F} → f ∈ s → 𝓢 ⊢ f

/-- Imported declaration from the Incompleteness formalization. -/
def ProvableSet (s : Set F) : Prop := ∀ {f}, f ∈ s → 𝓢 ⊢! f

/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊢* " => PrfSet

/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊢!* " => ProvableSet

/-- Imported declaration from the Incompleteness formalization. -/
def theory : Set F := {f | 𝓢 ⊢! f}

end «lp_section_1»

lemma unprovable_iff_isEmpty {𝓢 : S} {f : F} :
    𝓢 ⊬ f ↔ IsEmpty (𝓢 ⊢ f) := by simp [Provable, Unprovable]

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def _root_.LO.Entailment.Provable.get {𝓢 : S} {f : F} (h : 𝓢 ⊢! f) : 𝓢 ⊢ f :=
  Classical.choice h

lemma provableSet_iff {𝓢 : S} {s : Set F} :
    𝓢 ⊢!* s ↔ Nonempty (𝓢 ⊢* s) := by
  simp [ProvableSet, PrfSet, Provable, Classical.nonempty_pi, ←imp_iff_not_or]

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def _root_.LO.Entailment.ProvableSet.get {𝓢 : S} {s : Set F} (h : 𝓢 ⊢!* s) : 𝓢 ⊢* s :=
  Classical.choice (α := 𝓢 ⊢* s) (provableSet_iff.mp h : Nonempty (𝓢 ⊢* s))

/-- Imported declaration from the Incompleteness formalization. -/
class WeakerThan (𝓢 : S) (𝓣 : T) : Prop where
  subset : theory 𝓢 ⊆ theory 𝓣

/-- Imported declaration from the Incompleteness formalization. -/
infix:40 " wkn " => WeakerThan

/-- Imported declaration from the Incompleteness formalization. -/
class StrictlyWeakerThan (𝓢 : S) (𝓣 : T) : Prop where
   weakerThan : 𝓢 wkn 𝓣
   notWT : ¬𝓣 wkn 𝓢

/-- Imported declaration from the Incompleteness formalization. -/
infix:40 " swkn " => StrictlyWeakerThan

/-- Imported declaration from the Incompleteness formalization. -/
class Equiv (𝓢 : S) (𝓣 : T) : Prop where
  eq : theory 𝓢 = theory 𝓣

/-- Imported declaration from the Incompleteness formalization. -/
infix:40 " ≊ " => Equiv

section «lp_section_2»

variable {𝓢 : S} {𝓣 : T} {𝓤 : U}

@[instance, simp, refl] protected lemma _root_.LO.Entailment.WeakerThan.refl (𝓢 : S) :
    𝓢 wkn 𝓢 :=
  ⟨Set.Subset.refl _⟩

lemma _root_.LO.Entailment.WeakerThan.wk (h : 𝓢 wkn 𝓣) {φ} : 𝓢 ⊢! φ → 𝓣 ⊢! φ := @h.subset φ

lemma _root_.LO.Entailment.WeakerThan.pbl [h : 𝓢 wkn 𝓣] {φ} : 𝓢 ⊢! φ → 𝓣 ⊢! φ := @h.subset φ

@[trans] lemma _root_.LO.Entailment.WeakerThan.trans :
    𝓢 wkn 𝓣 → 𝓣 wkn 𝓤 → 𝓢 wkn 𝓤 :=
  fun w₁ w₂ ↦ ⟨Set.Subset.trans w₁.subset w₂.subset⟩

lemma weakerThan_iff : 𝓢 wkn 𝓣 ↔ (∀ {f}, 𝓢 ⊢! f → 𝓣 ⊢! f) :=
  ⟨fun h _ hf ↦ h.subset hf, fun h ↦ ⟨fun _ hf ↦ h hf⟩⟩

lemma not_weakerThan_iff : ¬𝓢 wkn 𝓣 ↔ (∃ f, 𝓢 ⊢! f ∧ 𝓣 ⊬ f) := by simp [weakerThan_iff, Unprovable];

lemma strictlyWeakerThan_iff : 𝓢 swkn 𝓣 ↔ (∀ {f}, 𝓢 ⊢! f → 𝓣 ⊢! f) ∧ (∃ f, 𝓢 ⊬ f ∧ 𝓣 ⊢! f) := by
  constructor
  · rintro ⟨wt, nwt⟩
    exact ⟨weakerThan_iff.mp wt, by rcases not_weakerThan_iff.mp nwt with ⟨φ, ht, hs⟩; exact ⟨φ,
      hs, ht⟩⟩
  · rintro ⟨h, φ, hs, ht⟩
    exact ⟨weakerThan_iff.mpr h, not_weakerThan_iff.mpr ⟨φ, ht, hs⟩⟩

@[trans]
lemma _root_.LO.Entailment.strictlyWeakerThan.trans : 𝓢 swkn 𝓣 → 𝓣 swkn 𝓤 → 𝓢 swkn 𝓤 := by
  rintro ⟨h₁, nh₁⟩ ⟨h₂, _⟩
  refine ⟨WeakerThan.trans h₁ h₂, not_weakerThan_iff.mpr ?_⟩
  obtain ⟨f, hf₁, hf₂⟩ := not_weakerThan_iff.mp nh₁
  exact ⟨f, weakerThan_iff.mp h₂ hf₁, hf₂⟩

lemma weakening (h : 𝓢 wkn 𝓣) {f} : 𝓢 ⊢! f → 𝓣 ⊢! f := weakerThan_iff.mp h

lemma _root_.LO.Entailment.StrictlyWeakerThan.of_unprovable_provable {𝓢 : S} {𝓣 : T} [𝓢 wkn 𝓣] {φ :
    F}
    (hS : 𝓢 ⊬ φ) (hT : 𝓣 ⊢! φ) : 𝓢 swkn 𝓣 := ⟨inferInstance, fun h ↦ hS (h.wk hT)⟩

lemma _root_.LO.Entailment.Equiv.iff : 𝓢 ≊ 𝓣 ↔ (∀ f, 𝓢 ⊢! f ↔ 𝓣 ⊢! f) :=
  ⟨fun e ↦ by simpa [Set.ext_iff, theory] using e.eq, fun e ↦ ⟨by simpa [Set.ext_iff,
    theory] using e⟩⟩

@[instance, simp, refl] protected lemma _root_.LO.Entailment.Equiv.refl (𝓢 : S) : 𝓢 ≊ 𝓢 := ⟨rfl⟩

@[symm] lemma _root_.LO.Entailment.Equiv.symm : 𝓢 ≊ 𝓣 → 𝓣 ≊ 𝓢 := fun e ↦ ⟨Eq.symm e.eq⟩

@[trans] lemma _root_.LO.Entailment.Equiv.trans :
    𝓢 ≊ 𝓣 → 𝓣 ≊ 𝓤 → 𝓢 ≊ 𝓤 :=
  fun e₁ e₂ ↦ ⟨Eq.trans e₁.eq e₂.eq⟩

lemma _root_.LO.Entailment.Equiv.antisymm_iff : 𝓢 ≊ 𝓣 ↔ 𝓢 wkn 𝓣 ∧ 𝓣 wkn 𝓢 := by
  refine ⟨fun e ↦ ⟨⟨Set.Subset.antisymm_iff.mp e.eq |>.1⟩, ⟨Set.Subset.antisymm_iff.mp e.eq |>.2⟩⟩,
    ?_⟩
  rintro ⟨w₁, w₂⟩
  exact ⟨Set.Subset.antisymm w₁.subset w₂.subset⟩

alias ⟨_, Equiv.antisymm⟩ := Equiv.antisymm_iff

lemma _root_.LO.Entailment.Equiv.le : 𝓢 ≊ 𝓣 → 𝓢 wkn 𝓣 := fun e ↦ ⟨by rw [e.eq]⟩

end «lp_section_2»

@[simp] lemma provableSet_theory (𝓢 : S) : 𝓢 ⊢!* theory 𝓢 := fun hf ↦ hf

/-- Imported declaration from the Incompleteness formalization. -/
def Inconsistent (𝓢 : S) : Prop := ∀ f, 𝓢 ⊢! f

/-- Imported declaration from the Incompleteness formalization. -/
class Consistent (𝓢 : S) : Prop where
  not_inconsistent : ¬Inconsistent 𝓢

lemma inconsistent_def {𝓢 : S} :
    Inconsistent 𝓢 ↔ ∀ f, 𝓢 ⊢! f := by simp [Inconsistent]

lemma inconsistent_iff_theory_eq {𝓢 : S} :
    Inconsistent 𝓢 ↔ theory 𝓢 = Set.univ := by
  simp [Inconsistent, Set.ext_iff, theory]

lemma not_inconsistent_iff_consistent {𝓢 : S} :
    ¬Inconsistent 𝓢 ↔ Consistent 𝓢 :=
  ⟨fun h ↦ ⟨h⟩, by rintro ⟨h⟩; exact h⟩

alias ⟨_, Consistent.not_inc⟩ := not_inconsistent_iff_consistent

lemma not_consistent_iff_inconsistent {𝓢 : S} :
    ¬Consistent 𝓢 ↔ Inconsistent 𝓢 := by simp [←not_inconsistent_iff_consistent]

alias ⟨_, Inconsistent.not_con⟩ := not_consistent_iff_inconsistent

lemma consistent_iff_exists_unprovable {𝓢 : S} :
    Consistent 𝓢 ↔ ∃ f, 𝓢 ⊬ f := by
  simp [←not_inconsistent_iff_consistent, inconsistent_def]

alias ⟨Consistent.exists_unprovable, _⟩ := consistent_iff_exists_unprovable

lemma _root_.LO.Entailment.Consistent.of_unprovable {𝓢 : S} {f} (h : 𝓢 ⊬ f) : Consistent 𝓢 :=
  ⟨fun hp ↦ h (hp f)⟩

lemma inconsistent_iff_theory_eq_univ {𝓢 : S} :
    Inconsistent 𝓢 ↔ theory 𝓢 = Set.univ := by simp [inconsistent_def, theory, Set.ext_iff]

alias ⟨Inconsistent.theory_eq, _⟩ := inconsistent_iff_theory_eq_univ

lemma _root_.LO.Entailment.Inconsistent.of_ge {𝓢 : S} {𝓣 : T} (h𝓢 : Inconsistent 𝓢) (h : 𝓢 wkn 𝓣) :
    Inconsistent 𝓣 :=
  fun f ↦ h.subset (h𝓢 f)

lemma _root_.LO.Entailment.Consistent.of_le {𝓢 : S} {𝓣 : T} (h𝓢 : Consistent 𝓢) (h : 𝓣 wkn 𝓢) :
    Consistent 𝓣 :=
  ⟨fun H ↦ not_consistent_iff_inconsistent.mpr (H.of_ge h) h𝓢⟩

/-- Imported declaration from the Incompleteness formalization. -/
@[ext] structure Translation {S S' F F'} [Entailment F S] [Entailment F' S'] (𝓢 : S) (𝓣 : S') where
  /-- Imported declaration from the Incompleteness formalization. -/
  toFun : F → F'
  /-- Imported declaration from the Incompleteness formalization. -/
  prf {f} : 𝓢 ⊢ f → 𝓣 ⊢ toFun f

/-- Imported declaration from the Incompleteness formalization. -/
infix:40 " ↝ " => Translation

/-- Imported declaration from the Incompleteness formalization. -/
@[ext] structure Bitranslation {S S' F F'} [Entailment F S] [Entailment F' S'] (𝓢 : S) (𝓣 :
    S') where
  /-- Imported declaration from the Incompleteness formalization. -/
  r : 𝓢 ↝ 𝓣
  /-- Imported declaration from the Incompleteness formalization. -/
  l : 𝓣 ↝ 𝓢
  /-- Imported declaration from the Incompleteness formalization. -/
  r_l : r.toFun ∘ l.toFun = id
  /-- Imported declaration from the Incompleteness formalization. -/
  l_r : l.toFun ∘ r.toFun = id

/-- Imported declaration from the Incompleteness formalization. -/
infix:40 " ↭ " => Bitranslation

/-- Imported declaration from the Incompleteness formalization. -/
@[ext] structure FaithfulTranslation {S S' F F'} [Entailment F S] [Entailment F' S'] (𝓢 : S) (𝓣 :
    S') extends 𝓢 ↝ 𝓣 where
  /-- Imported declaration from the Incompleteness formalization. -/
  prfInv {f} : 𝓣 ⊢ toFun f → 𝓢 ⊢ f

/-- Imported declaration from the Incompleteness formalization. -/
infix:40 " ↝¹ " => FaithfulTranslation

namespace Translation

variable {S S' S'' : Type*} {F F' F'' : Type*} [Entailment F S] [Entailment F' S']
variable [Entailment F'' S'']

/-- Imported declaration from the Incompleteness formalization. -/
instance (𝓢 : S) (𝓣 : S') : CoeFun (𝓢 ↝ 𝓣) (fun _ ↦ F → F') := ⟨Translation.toFun⟩

/-- Imported declaration from the Incompleteness formalization. -/
protected def id (𝓢 : S) : 𝓢 ↝ 𝓢 where
  toFun := id
  prf := id

@[simp] lemma id_app (𝓢 : S) (f : F) : Translation.id 𝓢 f = f := rfl

/-- Imported declaration from the Incompleteness formalization. -/
def comp {𝓢 : S} {𝓣 : S'} {𝓤 : S''} (φ : 𝓣 ↝ 𝓤) (ψ : 𝓢 ↝ 𝓣) : 𝓢 ↝ 𝓤 where
  toFun := φ.toFun ∘ ψ.toFun
  prf := φ.prf ∘ ψ.prf

@[simp] lemma comp_app {𝓢 : S} {𝓣 : S'} {𝓤 : S''} (φ : 𝓣 ↝ 𝓤) (ψ : 𝓢 ↝ 𝓣) (f : F) :
    φ.comp ψ f = φ (ψ f) := rfl

lemma provable {𝓢 : S} {𝓣 : S'} (f : 𝓢 ↝ 𝓣) {φ} (h : 𝓢 ⊢! φ) : 𝓣 ⊢! f φ := ⟨f.prf h.get⟩

end Translation

namespace Bitranslation

variable {S S' S'' : Type*} {F F' F'' : Type*} [Entailment F S] [Entailment F' S']
variable [Entailment F'' S'']

@[simp] lemma r_l_app {𝓢 : S} {𝓣 : S'} (f : 𝓢 ↭ 𝓣) (φ : F') : f.r (f.l φ) = φ := congr_fun f.r_l φ

@[simp] lemma l_r_app {𝓢 : S} {𝓣 : S'} (f : 𝓢 ↭ 𝓣) (φ : F) : f.l (f.r φ) = φ := congr_fun f.l_r φ

/-- Imported declaration from the Incompleteness formalization. -/
protected def id (𝓢 : S) : 𝓢 ↭ 𝓢 where
  r := Translation.id 𝓢
  l := Translation.id 𝓢
  r_l := by ext; simp
  l_r := by ext; simp

/-- Imported declaration from the Incompleteness formalization. -/
protected def symm {𝓢 : S} {𝓣 : S'} (φ : 𝓢 ↭ 𝓣) : 𝓣 ↭ 𝓢 where
  r := φ.l
  l := φ.r
  r_l := φ.l_r
  l_r := φ.r_l

/-- Imported declaration from the Incompleteness formalization. -/
def comp {𝓢 : S} {𝓣 : S'} {𝓤 : S''} (φ : 𝓣 ↭ 𝓤) (ψ : 𝓢 ↭ 𝓣) : 𝓢 ↭ 𝓤 where
  r := φ.r.comp ψ.r
  l := ψ.l.comp φ.l
  r_l := by ext; simp
  l_r := by ext; simp

end Bitranslation

namespace FaithfulTranslation

variable {S S' S'' : Type*} {F F' F'' : Type*} [Entailment F S] [Entailment F' S']
variable [Entailment F'' S'']

instance (𝓢 : S) (𝓣 : S') : CoeFun (𝓢 ↝¹ 𝓣) (fun _ ↦ F → F') := ⟨fun t ↦ t.toFun⟩

/-- Imported declaration from the Incompleteness formalization. -/
protected def id (𝓢 : S) : 𝓢 ↝¹ 𝓢 where
  toFun := id
  prf := id
  prfInv := id

@[simp] lemma id_app (𝓢 : S) (f : F) : FaithfulTranslation.id 𝓢 f = f := rfl

/-- Imported declaration from the Incompleteness formalization. -/
def comp {𝓢 : S} {𝓣 : S'} {𝓤 : S''} (φ : 𝓣 ↝¹ 𝓤) (ψ : 𝓢 ↝¹ 𝓣) : 𝓢 ↝¹ 𝓤 where
  toFun := φ.toFun ∘ ψ.toFun
  prf := φ.prf ∘ ψ.prf
  prfInv := ψ.prfInv ∘ φ.prfInv

@[simp] lemma comp_app {𝓢 : S} {𝓣 : S'} {𝓤 : S''} (φ : 𝓣 ↝¹ 𝓤) (ψ : 𝓢 ↝¹ 𝓣) (f : F) :
    φ.comp ψ f = φ (ψ f) := rfl

lemma provable {𝓢 : S} {𝓣 : S'} (f : 𝓢 ↝¹ 𝓣) {φ} (h : 𝓢 ⊢! φ) : 𝓣 ⊢! f φ := ⟨f.prf h.get⟩

lemma provable_iff {𝓢 : S} {𝓣 : S'} (f : 𝓢 ↝¹ 𝓣) {φ} : 𝓣 ⊢! f φ ↔ 𝓢 ⊢! φ :=
  ⟨fun h ↦ ⟨f.prfInv h.get⟩, fun h ↦ ⟨f.prf h.get⟩⟩

end FaithfulTranslation

section «lp_section_3»

variable [LogicalConnective F]

variable (𝓢 : S)

/-- Imported declaration from the Incompleteness formalization. -/
def Complete : Prop := ∀ f, 𝓢 ⊢! f ∨ 𝓢 ⊢! ∼f

/-- Imported declaration from the Incompleteness formalization. -/
def Undecidable (f : F) : Prop := 𝓢 ⊬ f ∧ 𝓢 ⊬ ∼f

end «lp_section_3»

lemma incomplete_iff_exists_undecidable [LogicalConnective F] {𝓢 : S} :
    ¬Entailment.Complete 𝓢 ↔ ∃ f, Undecidable 𝓢 f := by simp [Complete, Undecidable, not_or]

variable (S T)

/-- Imported declaration from the Incompleteness formalization. -/
class Axiomatized [Collection F S] where
  /-- Imported declaration from the Incompleteness formalization. -/
  prfAxm {𝓢 : S} : 𝓢 ⊢* Collection.set 𝓢
  /-- Imported declaration from the Incompleteness formalization. -/
  weakening {𝓢 𝓣 : S} : 𝓢 ⊆ 𝓣 → 𝓢 ⊢ f → 𝓣 ⊢ f

alias byAxm := Axiomatized.prfAxm
alias wk := Axiomatized.weakening

/-- Imported declaration from the Incompleteness formalization. -/
class StrongCut [Collection F T] where
  /-- Imported declaration from the Incompleteness formalization. -/
  cut {𝓢 : S} {𝓣 : T} {φ} : 𝓢 ⊢* Collection.set 𝓣 → 𝓣 ⊢ φ → 𝓢 ⊢ φ

variable {S T}

section «lp_section_4»

namespace Axiomatized

variable [Collection F S] [Axiomatized S] {𝓢 𝓣 : S}

@[simp] lemma provable_axm (𝓢 : S) : 𝓢 ⊢!* Collection.set 𝓢 := fun hf ↦ ⟨prfAxm hf⟩

lemma axm_subset (𝓢 : S) : Collection.set 𝓢 ⊆ theory 𝓢 := fun _ hp ↦ provable_axm 𝓢 hp

lemma le_of_subset (h : 𝓢 ⊆ 𝓣) : 𝓢 wkn 𝓣 := ⟨by rintro f ⟨b⟩; exact ⟨weakening h b⟩⟩

lemma «weakening!» (h : 𝓢 ⊆ 𝓣) {f} : 𝓢 ⊢! f → 𝓣 ⊢! f := by rintro ⟨b⟩; exact ⟨weakening h b⟩

/-- Imported declaration from the Incompleteness formalization. -/
lemma weakerThanOfSubset (h : 𝓢 ⊆ 𝓣) : 𝓢 wkn 𝓣 := ⟨fun _ ↦ weakening! h⟩

/-- Imported declaration from the Incompleteness formalization. -/
def translation (h : 𝓢 ⊆ 𝓣) : 𝓢 ↝ 𝓣 where
  toFun := id
  prf := weakening h

end Axiomatized

alias by_axm := Axiomatized.provable_axm
alias wk! := Axiomatized.weakening!

section «lp_section_5»

variable [Collection F S] [Collection F T] [Axiomatized S]

/-- Imported declaration from the Incompleteness formalization. -/
def FiniteAxiomatizable (𝓢 : S) : Prop := ∃ 𝓕 : S, Collection.Finite 𝓕 ∧ 𝓕 ≊ 𝓢

lemma _root_.LO.Entailment.Consistent.of_subset {𝓢 𝓣 : S} (h𝓢 : Consistent 𝓢) (h : 𝓣 ⊆ 𝓢) :
    Consistent 𝓣 :=
  h𝓢.of_le (Axiomatized.le_of_subset h)

lemma _root_.LO.Entailment.Inconsistent.of_supset {𝓢 𝓣 : S} (h𝓢 : Inconsistent 𝓢) (h : 𝓢 ⊆ 𝓣) :
    Inconsistent 𝓣 :=
  h𝓢.of_ge (Axiomatized.le_of_subset h)

end «lp_section_5»

namespace StrongCut

variable [Collection F T] [StrongCut S T]

lemma «cut!» {𝓢 : S} {𝓣 : T} {φ : F} (H : 𝓢 ⊢!* Collection.set 𝓣) (hp : 𝓣 ⊢! φ) : 𝓢 ⊢! φ := by
  rcases hp with ⟨b⟩; exact ⟨StrongCut.cut H.get b⟩

/-- Imported declaration from the Incompleteness formalization. -/
def translation {𝓢 : S} {𝓣 : T} (B : 𝓢 ⊢* Collection.set 𝓣) : 𝓣 ↝ 𝓢 where
  toFun := id
  prf := StrongCut.cut B

end StrongCut

namespace WeakerThan

/-- Imported declaration from the Incompleteness formalization. -/
lemma «ofAxm!» [Collection F S] [StrongCut S S] {𝓢₁ 𝓢₂ : S} (B : 𝓢₂ ⊢!* Collection.set 𝓢₁) :
    𝓢₁ wkn 𝓢₂ := ⟨fun _ b ↦ StrongCut.cut! B b⟩

end WeakerThan

/-- Imported declaration from the Incompleteness formalization. -/
lemma _root_.LO.Entailment.WeakerThan.ofSubset [Collection F S] [Axiomatized S] {𝓢 𝓣 : S} (h :
    𝓢 ⊆ 𝓣) :
    𝓢 wkn 𝓣 :=
  ⟨fun _ ↦ wk! h⟩

variable (S)

/-- Imported declaration from the Incompleteness formalization. -/
class Compact [Collection F S] where
  /-- Imported declaration from the Incompleteness formalization. -/
  φ {𝓢 : S} {f : F} : 𝓢 ⊢ f → S
  /-- Imported declaration from the Incompleteness formalization. -/
  φPrf {𝓢 : S} {f : F} (b : 𝓢 ⊢ f) : φ b ⊢ f
  φ_subset {𝓢 : S} {f : F} (b : 𝓢 ⊢ f) : φ b ⊆ 𝓢
  φ_finite {𝓢 : S} {f : F} (b : 𝓢 ⊢ f) : Collection.Finite (φ b)

variable {S}

namespace Compact

variable [Collection F S] [Compact S]

lemma finite_provable {𝓢 : S} (h : 𝓢 ⊢! f) : ∃ 𝓕 : S, 𝓕 ⊆ 𝓢 ∧ Collection.Finite 𝓕 ∧ 𝓕 ⊢! f := by
  rcases h with ⟨b⟩
  exact ⟨φ b, φ_subset b, φ_finite b, ⟨φPrf b⟩⟩

end Compact

end «lp_section_4»

end Entailment

namespace Entailment

variable {S : Type*} {F : Type*} [LogicalConnective F] [Entailment F S]

variable (S)

/-- Imported declaration from the Incompleteness formalization. -/
class DeductiveExplosion where
  /-- Imported declaration from the Incompleteness formalization. -/
  dexp {𝓢 : S} : 𝓢 ⊢ ⊥ → (φ : F) → 𝓢 ⊢ φ

variable {S}

section «lp_section_6»

variable [DeductiveExplosion S]

namespace DeductiveExplosion

/-- Imported declaration from the Incompleteness formalization. -/
lemma «dexp!» {𝓢 : S} (h : 𝓢 ⊢! ⊥) (f : F) : 𝓢 ⊢! f := by
  rcases h with ⟨b⟩; exact ⟨DeductiveExplosion.dexp b f⟩

end DeductiveExplosion

lemma inconsistent_iff_provable_bot {𝓢 : S} :
    Inconsistent 𝓢 ↔ 𝓢 ⊢! ⊥ := ⟨fun h ↦ h ⊥, fun h f ↦ DeductiveExplosion.dexp! h f⟩

alias ⟨_, inconsistent_of_provable⟩ := inconsistent_iff_provable_bot

lemma consistent_iff_unprovable_bot {𝓢 : S} :
    Consistent 𝓢 ↔ 𝓢 ⊬ ⊥ := by
  simp [inconsistent_iff_provable_bot, ←not_inconsistent_iff_consistent]

alias ⟨Consistent.not_bot, _⟩ := consistent_iff_unprovable_bot

variable [Collection F S] [Axiomatized S] [Compact S]

lemma inconsistent_compact {𝓢 : S} :
    Inconsistent 𝓢 ↔ ∃ 𝓕 : S, 𝓕 ⊆ 𝓢 ∧ Collection.Finite 𝓕 ∧ Inconsistent 𝓕 :=
  ⟨fun H ↦ by rcases Compact.finite_provable (H ⊥) with ⟨𝓕, h𝓕, fin, h⟩; exact ⟨𝓕, h𝓕, fin,
    inconsistent_of_provable h⟩, by
    rintro ⟨𝓕, h𝓕, _, H⟩; exact H.of_supset h𝓕⟩

lemma consistent_compact {𝓢 : S} :
    Consistent 𝓢 ↔ ∀ 𝓕 : S, 𝓕 ⊆ 𝓢 → Collection.Finite 𝓕 → Consistent 𝓕 := by
  simp [←not_inconsistent_iff_consistent, inconsistent_compact (𝓢 := 𝓢)]

end «lp_section_6»

variable (S)

/-- Imported declaration from the Incompleteness formalization. -/
class Deduction [Cons F S] where
  /-- Imported declaration from the Incompleteness formalization. -/
  ofInsert {φ ψ : F} {𝓢 : S} : cons φ 𝓢 ⊢ ψ → 𝓢 ⊢ φ ==> ψ
  /-- Imported declaration from the Incompleteness formalization. -/
  inv {φ ψ : F} {𝓢 : S} : 𝓢 ⊢ φ ==> ψ → cons φ 𝓢 ⊢ ψ

variable {S}

section «lp_section_7»

variable [Cons F S] [Deduction S] {𝓢 : S} {φ ψ : F}

alias deduction := Deduction.ofInsert

namespace Deduction

lemma «of_insert!» (h : cons φ 𝓢 ⊢! ψ) : 𝓢 ⊢! φ ==> ψ := by
  rcases h with ⟨b⟩; exact ⟨Deduction.ofInsert b⟩

alias deduction! := Deduction.of_insert!

lemma «inv!» (h : 𝓢 ⊢! φ ==> ψ) : cons φ 𝓢 ⊢! ψ := by
  rcases h with ⟨b⟩; exact ⟨Deduction.inv b⟩

end Deduction

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Entailment.Deduction.translation (φ : F) (𝓢 : S) : cons φ 𝓢 ↝ 𝓢 where
  toFun := fun ψ ↦ φ ==> ψ
  prf := deduction

lemma deduction_iff : cons φ 𝓢 ⊢! ψ ↔ 𝓢 ⊢! φ ==> ψ :=
  ⟨Deduction.of_insert!, Deduction.inv!⟩

end «lp_section_7»

end Entailment

section «lp_section_8»

variable {S : Type*} {F : Type*} [Entailment F S] {M : Type*} [Semantics F M]

/-- Imported declaration from the Incompleteness formalization. -/
class Sound (𝓢 : S) (𝓜 : M) : Prop where
  sound : ∀ {f : F}, 𝓢 ⊢! f → 𝓜 ⊧ f

/-- Imported declaration from the Incompleteness formalization. -/
class Complete (𝓢 : S) (𝓜 : M) : Prop where
  complete : ∀ {f : F}, 𝓜 ⊧ f → 𝓢 ⊢! f

namespace Sound

section «lp_section_9»

variable {𝓢 𝓣 : S} {𝓜 𝓝 : M} [Sound 𝓢 𝓜] [Sound 𝓣 𝓝]

lemma not_provable_of_countermodel {φ : F} (hp : ¬𝓜 ⊧ φ) : 𝓢 ⊬ φ :=
  fun b ↦ hp (Sound.sound b)

lemma consistent_of_meaningful : Semantics.Meaningful 𝓜 → Entailment.Consistent 𝓢 :=
  fun H ↦ ⟨fun h ↦ by rcases H with ⟨f, hf⟩; exact hf (Sound.sound (h f))⟩

lemma consistent_of_model [LogicalConnective F] [Semantics.Bot M] (𝓜 : M) [Sound 𝓢 𝓜] :
    Entailment.Consistent 𝓢 :=
  consistent_of_meaningful (𝓜 := 𝓜) inferInstance

lemma realizeSet_of_prfSet {T : Set F} (b : 𝓢 ⊢!* T) : 𝓜 ⊧* T :=
  ⟨fun _ hf => sound (b hf)⟩

end «lp_section_9»

section «lp_section_10»

variable {𝓢 : S} {T : Set F} [Sound 𝓢 (Semantics.models M T)]

lemma consequence_of_provable {f : F} : 𝓢 ⊢! f → T ⊨[M] f := sound

lemma consistent_of_satisfiable [LogicalConnective F] [∀ 𝓜 : M, Semantics.Meaningful 𝓜] :
    Semantics.Satisfiable M T → Entailment.Consistent 𝓢 :=
  fun H ↦ consistent_of_meaningful (Semantics.meaningful_iff_satisfiableSet.mp H)

end «lp_section_10»

end Sound

namespace Complete

section «lp_section_11»

variable {𝓢 : S} {𝓜 : M} [Complete 𝓢 𝓜]

lemma meaningful_of_consistent : Entailment.Consistent 𝓢 → Semantics.Meaningful 𝓜 := by
  contrapose
  suffices (∀ (f : F), 𝓜 ⊧ f) → Entailment.Inconsistent 𝓢 by
    simpa [Semantics.not_meaningful_iff, Entailment.not_consistent_iff_inconsistent]
  exact fun h f ↦ Complete.complete (h f)

end «lp_section_11»

section «lp_section_12»

variable {𝓢 : S} {s : Set F} [Complete 𝓢 (Semantics.models M s)]

lemma provable_of_consequence {f : F} : s ⊨[M] f → 𝓢 ⊢! f := complete

lemma provable_iff_consequence [Sound 𝓢 (Semantics.models M s)] {f : F} :
    s ⊨[M] f ↔ 𝓢 ⊢! f :=
  ⟨complete, Sound.sound⟩


section «lp_section_13»

variable [LogicalConnective F] [∀ 𝓜 : M, Semantics.Meaningful 𝓜]

lemma satisfiable_of_consistent :
    Entailment.Consistent 𝓢 → Semantics.Satisfiable M s :=
  fun H ↦ Semantics.meaningful_iff_satisfiableSet.mpr (meaningful_of_consistent H)

lemma inconsistent_of_unsatisfiable :
    ¬Semantics.Satisfiable M s → Entailment.Inconsistent 𝓢 := by
  contrapose; simpa [←Entailment.not_consistent_iff_inconsistent] using satisfiable_of_consistent

lemma consistent_iff_satisfiable [Sound 𝓢 (Semantics.models M s)] :
    Entailment.Consistent 𝓢 ↔ Semantics.Satisfiable M s :=
  ⟨satisfiable_of_consistent, Sound.consistent_of_satisfiable⟩

end «lp_section_13»

lemma weakerthan_of_models {𝓣 : S} {t : Set F} [Sound 𝓣 (Semantics.models M t)]
    (H : ∀ 𝓜 : M, 𝓜 ⊧* s → 𝓜 ⊧* t) : 𝓣 wkn 𝓢 :=
  Entailment.weakerThan_iff.mpr <| fun h ↦ provable_of_consequence <|
      fun 𝓜 h𝓜 ↦ Sound.consequence_of_provable (M :=
    M) (T := t) h (H 𝓜 h𝓜)

end «lp_section_12»

end Complete

end «lp_section_8»

end LO
