/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Logic.Entailment
import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Supplemental

/-!
# Sequent calculus and variants

This file defines a characterization of Tait style calculus and Gentzen style calculus.

## Main Definitions
* `LO.Tait`
* `LO.Gentzen`

-/

namespace LO

/-- Imported declaration from the Incompleteness formalization. -/
class OneSided (F : outParam Type*) (K : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Derivation : K → List F → Type*

/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⟹ " => OneSided.Derivation

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.OneSided.Derivation₁ [OneSided F K] (𝓚 : K) (φ : F) : Type _ := 𝓚 ⟹ [φ]

/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⟹. " => OneSided.Derivation₁

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.OneSided.Derivable [OneSided F K] (𝓚 : K) (Δ : List F) : Prop := Nonempty (𝓚 ⟹ Δ)

/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⟹! " => OneSided.Derivable

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.OneSided.Derivable₁ [OneSided F K] (𝓚 : K) (φ : F) : Prop := Nonempty (𝓚 ⟹. φ)

/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⟹!. " => OneSided.Derivable₁

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def _root_.LO.OneSided.Derivable.get [OneSided F K] (𝓚 : K) (Δ : List F) (h :
    𝓚 ⟹! Δ) :
    𝓚 ⟹ Δ :=
  Classical.choice h

/-- Imported declaration from the Incompleteness formalization. -/
class Tait
    (F K : Type*) [LogicalConnective F] [DeMorgan F] [Collection F K] extends OneSided F K where
  /-- Imported declaration from the Incompleteness formalization. -/
  verum (𝓚 : K) (Δ : List F) : 𝓚 ⟹ ⊤ :: Δ
  /-- Imported declaration from the Incompleteness formalization. -/
  and {𝓚 : K} {φ ψ : F} {Δ : List F} : 𝓚 ⟹ φ :: Δ → 𝓚 ⟹ ψ :: Δ → 𝓚 ⟹ φ ⋏ ψ :: Δ
  /-- Imported declaration from the Incompleteness formalization. -/
  or {𝓚 : K} {φ ψ : F} {Δ : List F}  : 𝓚 ⟹ φ :: ψ :: Δ → 𝓚 ⟹ φ ⋎ ψ :: Δ
  /-- Imported declaration from the Incompleteness formalization. -/
  wk {𝓚 : K} {Δ Δ' : List F}         : 𝓚 ⟹ Δ → Δ ⊆ Δ' → 𝓚 ⟹ Δ'
  /-- Imported declaration from the Incompleteness formalization. -/
  em {𝓚 : K} {φ} {Δ : List F}        : φ ∈ Δ → ∼φ ∈ Δ → 𝓚 ⟹ Δ

/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.Tait.Cut (F K :
    Type*) [LogicalConnective F] [DeMorgan F] [Collection F K] [Tait F K] where
  /-- Imported declaration from the Incompleteness formalization. -/
  cut {𝓚 : K} {Δ : List F} {φ} : 𝓚 ⟹ φ :: Δ → 𝓚 ⟹ ∼φ :: Δ → 𝓚 ⟹ Δ

/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.Tait.Axiomatized (F K :
    Type*) [LogicalConnective F] [DeMorgan F] [Collection F K] [Tait F K] where
  /-- Imported declaration from the Incompleteness formalization. -/
  root {𝓚 : K} {φ} : φ ∈ 𝓚 → 𝓚 ⟹. φ
  /-- Imported declaration from the Incompleteness formalization. -/
  trans {𝓚 𝓛 : K} {Γ} : ((ψ : F) → ψ ∈ 𝓚 → 𝓛 ⟹. ψ) → 𝓚 ⟹ Γ → 𝓛 ⟹ Γ

variable {F S K : Type*} [LogicalConnective F] [Collection F K]

namespace OneSided

variable [OneSided F K] {𝓚 : K} {Γ Δ : List F}

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev cast (d : 𝓚 ⟹ Δ) (e : Δ = Γ) : 𝓚 ⟹ Γ := cast (congrArg _ e) d

end OneSided

namespace Tait

open Entailment

variable [DeMorgan F] [Tait F K]

variable {𝓚 : K} {Γ Δ : List F} {φ ψ φ₁ φ₂ φ₃ φ₄ : F}

/-- Imported declaration from the Incompleteness formalization. -/
def ofEq (b : 𝓚 ⟹ Γ) (h : Γ = Δ) : 𝓚 ⟹ Δ := h ▸ b

lemma of_eq (b : 𝓚 ⟹! Γ) (h : Γ = Δ) : 𝓚 ⟹! Δ := h ▸ b

/-- Imported declaration from the Incompleteness formalization. -/
def verum' (h : ⊤ ∈ Γ := by simp) : 𝓚 ⟹ Γ := wk (verum 𝓚 Γ) (by simp [h])

lemma «verum!» (𝓚 : K) (Γ : List F) : 𝓚 ⟹! ⊤ :: Γ := ⟨verum _ _⟩

lemma «verum'!» (h : ⊤ ∈ Γ) : 𝓚 ⟹! Γ := ⟨verum' h⟩

lemma «and!» (hp : 𝓚 ⟹! φ :: Γ) (hq : 𝓚 ⟹! ψ :: Γ) : 𝓚 ⟹! φ ⋏ ψ :: Γ := ⟨and hp.get hq.get⟩

lemma «or!» (h : 𝓚 ⟹! φ :: ψ :: Γ) : 𝓚 ⟹! φ ⋎ ψ :: Γ := ⟨or h.get⟩

lemma «wk!» (h : 𝓚 ⟹! Γ) (ss : Γ ⊆ Δ) : 𝓚 ⟹! Δ := ⟨wk h.get ss⟩

lemma «em!» (hp : φ ∈ Γ) (hn : ∼φ ∈ Γ) : 𝓚 ⟹! Γ := ⟨em hp hn⟩

/-- Imported declaration from the Incompleteness formalization. -/
def close (φ : F) (hp : φ ∈ Γ := by simp) (hn : ∼φ ∈ Γ := by simp) : 𝓚 ⟹ Γ := em hp hn

lemma «close!» (φ : F) (hp : φ ∈ Γ := by simp) (hn : ∼φ ∈ Γ := by simp) : 𝓚 ⟹! Γ := em! hp hn

/-- Imported declaration from the Incompleteness formalization. -/
def and' {φ ψ : F} (h : φ ⋏ ψ ∈ Γ) (dp : 𝓚 ⟹ φ :: Γ) (dq : 𝓚 ⟹ ψ :: Γ) : 𝓚 ⟹ Γ :=
  wk (and dp dq) (by simp [h])

/-- Imported declaration from the Incompleteness formalization. -/
def or' {φ ψ : F} (h : φ ⋎ ψ ∈ Γ) (dpq : 𝓚 ⟹ φ :: ψ :: Γ) : 𝓚 ⟹ Γ :=
  wk (or dpq) (by simp [h])

/-- Imported declaration from the Incompleteness formalization. -/
def wkTail (d : 𝓚 ⟹ Γ) : 𝓚 ⟹ φ :: Γ := wk d (by simp)

/-- Imported declaration from the Incompleteness formalization. -/
def rotate₁ (d : 𝓚 ⟹ φ₂ :: φ₁ :: Γ) : 𝓚 ⟹ φ₁ :: φ₂ :: Γ := wk d (by simp)

/-- Imported declaration from the Incompleteness formalization. -/
def rotate₂ (d : 𝓚 ⟹ φ₃ :: φ₁ :: φ₂ :: Γ) : 𝓚 ⟹ φ₁ :: φ₂ :: φ₃ :: Γ :=
  wk d (by
    simp only [List.cons_subset, List.mem_cons, true_or, or_true, true_and]
    apply List.subset_cons_of_subset _ (List.subset_cons_of_subset _ <| by simp))

/-- Imported declaration from the Incompleteness formalization. -/
def rotate₃ (d : 𝓚 ⟹ φ₄ :: φ₁ :: φ₂ :: φ₃ :: Γ) : 𝓚 ⟹ φ₁ :: φ₂ :: φ₃ :: φ₄ :: Γ :=
  wk d (by
    simp only [List.cons_subset, List.mem_cons, true_or, or_true, true_and]
    apply List.subset_cons_of_subset _ (List.subset_cons_of_subset _ <|
      List.subset_cons_of_subset _ <| by simp))

variable {𝓚 𝓛 : K} {Γ : List F}

alias cut := Tait.Cut.cut

alias root := Tait.Axiomatized.root

lemma «cut!» [Tait.Cut F K] (hp : 𝓚 ⟹! φ :: Δ) (hn : 𝓚 ⟹! ∼φ :: Δ) : 𝓚 ⟹! Δ := ⟨cut hp.get hn.get⟩

lemma «root!» [Tait.Axiomatized F K] {φ} (h : φ ∈ 𝓚) : 𝓚 ⟹!. φ := ⟨root h⟩

/-- Imported declaration from the Incompleteness formalization. -/
def byAxm [Tait.Axiomatized F K] (φ) (h : φ ∈ 𝓚) (hΓ : φ ∈ Γ := by simp) :
    𝓚 ⟹ Γ :=
  wk (root h) (by simp_all)

lemma «byAxm!» [Tait.Axiomatized F K] (φ) (h : φ ∈ 𝓚) (hΓ : φ ∈ Γ := by simp) :
    𝓚 ⟹! Γ :=
  ⟨byAxm φ h hΓ⟩

/-- Imported declaration from the Incompleteness formalization. -/
def ofAxiomSubset [Tait.Axiomatized F K] (h : 𝓚 ⊆ 𝓛) : 𝓚 ⟹ Γ → 𝓛 ⟹ Γ :=
  Tait.Axiomatized.trans fun _ hq ↦ Tait.Axiomatized.root (Collection.subset_iff.mp h _ hq)

lemma of_axiom_subset [Tait.Axiomatized F K] (h : 𝓚 ⊆ 𝓛) :
    𝓚 ⟹! Γ → 𝓛 ⟹! Γ :=
  fun b ↦ ⟨ofAxiomSubset h b.get⟩

instance system : Entailment F K := ⟨(· ⟹. ·)⟩

instance [Tait.Axiomatized F K] : Entailment.Axiomatized K where
  prfAxm := fun hf ↦ Tait.Axiomatized.root <| hf
  weakening := Tait.ofAxiomSubset

lemma provable_bot_iff_derivable_nil [Tait.Cut F K] : 𝓚 ⟹! [] ↔ 𝓚 ⊢! ⊥ :=
  ⟨fun b ↦ wk! b (by simp), fun b ↦ cut! b (by simpa using verum! _ _)⟩

lemma waekerThan_of_subset [Tait.Axiomatized F K] (h : 𝓚 ⊆ 𝓛) :
    𝓚 wkn 𝓛 :=
  ⟨fun _ ↦ Entailment.Axiomatized.weakening! h⟩

instance [Tait.Axiomatized F K] : Entailment.StrongCut K K where
  cut {_ _ _ bs b} := Tait.Axiomatized.trans (fun _ hq ↦ bs hq) b

instance [Tait.Cut F K] : DeductiveExplosion K where
  dexp {𝓚 b φ} := wk (Tait.Cut.cut b (by simpa using verum _ _)) (by simp)

/-
instance : Entailment.Deduction K where
  ofInsert {φ ψ 𝓚 b} := by {  }
  inv {φ ψ 𝓚 b} :=
    let h : cons φ 𝓚 ⟹ [∼φ ⋎ ψ, ψ] :=
      wk (show cons φ 𝓚 ⟹ [∼φ ⋎ ψ] from ofEq (ofAxiomSubset (by simp) b) (by simp [DeMorgan.imply]))
      (by simp)
    let n : cons φ 𝓚 ⟹ [∼(∼φ ⋎ ψ), ψ] :=
      let hp : cons φ 𝓚 ⟹ [φ, ψ] := wk (show cons φ 𝓚 ⊢ φ from byAxm (by simp)) (by simp)
      let hq : cons φ 𝓚 ⟹ [∼ψ, ψ] := em (φ := ψ) (by simp) (by simp)
      ofEq (and hp hq) (by simp)
    cut h n
-/

lemma inconsistent_iff_provable [Tait.Cut F K] :
    Inconsistent 𝓚 ↔ 𝓚 ⟹! [] :=
  ⟨fun b ↦ ⟨cut (inconsistent_iff_provable_bot.mp b).get (by simpa using verum _ _)⟩,
   fun h ↦ inconsistent_iff_provable_bot.mpr (wk! h (by simp))⟩

lemma consistent_iff_unprovable [Tait.Axiomatized F K] [Tait.Cut F K] :
    Consistent 𝓚 ↔ IsEmpty (𝓚 ⟹ []) :=
  not_iff_not.mp <| by simp [not_consistent_iff_inconsistent, inconsistent_iff_provable]

/-
lemma provable_iff_inconsistent {φ} :
    𝓚 ⊢! φ ↔ Inconsistent (cons (∼φ) 𝓚) := by
  simp [inconsistent_iff_provable, deduction_iff, DeMorgan.imply]
  constructor
  · intro h; exact cut! (of_axiom_subset (by simp) h) (root! <| by simp)
  · rintro ⟨b⟩
    exact ⟨by simpa using Tait.Axiomatized.proofOfContra b⟩

lemma refutable_iff_inconsistent {φ} :
    𝓚 ⊢! ∼φ ↔ Inconsistent (cons φ 𝓚) := by simpa using provable_iff_inconsistent (𝓚 := 𝓚) (φ := ∼φ)

lemma consistent_insert_iff_not_refutable {φ}  :
    Entailment.Consistent (cons φ 𝓚) ↔ 𝓚 ⊬ ∼φ := by
  simp [Entailment.Unprovable, refutable_iff_inconsistent,
    Entailment.not_inconsistent_iff_consistent]

lemma inconsistent_of_provable_and_refutable {φ} (bp : 𝓚 ⊢! φ) (br : 𝓚 ⊢! ∼φ) : Inconsistent 𝓚 :=
  inconsistent_iff_provable.mpr <| cut! bp br
-/

instance [Tait.Cut F K] : Entailment.Classical 𝓚 where
  mdp {φ ψ dpq dp} :=
    let dpq : 𝓚 ⟹ [∼φ ⋎ ψ, ψ] := wk dpq (by simp [DeMorgan.imply])
    let dnq : 𝓚 ⟹ [∼(∼φ ⋎ ψ), ψ] :=
      let d : 𝓚 ⟹ [φ ⋏ ∼ψ, ψ] := and (wk dp <| by simp) (close ψ)
      ofEq d (by simp)
    cut dpq dnq
  negEquiv φ := ofEq
    (show 𝓚 ⊢ (φ ⋎ ∼φ ⋎ ⊥) ⋏ (φ ⋏ ⊤ ⋎ ∼φ) from
      and (or <| rotate₁ <| or <| close φ) (or <| and (close φ) verum'))
    (by simp [Axioms.NegEquiv, DeMorgan.imply, LogicalConnective.iff])
  verum := verum _ _
  imply₁ φ ψ :=
    have : 𝓚 ⊢ ∼φ ⋎ ∼ψ ⋎ φ := or <| rotate₁ <| or <| close φ
    ofEq this (by simp [DeMorgan.imply])
  imply₂ φ ψ χ :=
    have : 𝓚 ⊢ φ ⋏ ψ ⋏ ∼χ ⋎ φ ⋏ ∼ψ ⋎ ∼φ ⋎ χ :=
      or <| rotate₁ <| or <| rotate₁ <| or <| rotate₃ <| and
        (close φ)
        (and (rotate₃ <| and (close φ) (close ψ)) (close χ))
    ofEq this (by simp [DeMorgan.imply])
  and₁ φ ψ :=
    have : 𝓚 ⊢ (∼φ ⋎ ∼ψ) ⋎ φ := or <| or <| close φ
    ofEq this (by simp [DeMorgan.imply])
  and₂ φ ψ :=
    have : 𝓚 ⊢ (∼φ ⋎ ∼ψ) ⋎ ψ := or <| or <| close ψ
    ofEq this (by simp [DeMorgan.imply])
  and₃ φ ψ :=
    have : 𝓚 ⊢ ∼φ ⋎ ∼ψ ⋎ φ ⋏ ψ := or <| rotate₁ <| or <| rotate₁ <| and (close φ) (close ψ)
    ofEq this (by simp [DeMorgan.imply])
  or₁ φ ψ :=
    have : 𝓚 ⊢ ∼φ ⋎ φ ⋎ ψ := or <| rotate₁ <| or <| close φ
    ofEq this (by simp [DeMorgan.imply])
  or₂ φ ψ :=
    have : 𝓚 ⊢ ∼ψ ⋎ φ ⋎ ψ := or <| rotate₁ <| or <| close ψ
    ofEq this (by simp [DeMorgan.imply])
  or₃ φ ψ χ :=
    have : 𝓚 ⊢ φ ⋏ ∼χ ⋎ ψ ⋏ ∼ χ ⋎ ∼φ ⋏ ∼ψ ⋎ χ :=
      or <| rotate₁ <| or <| rotate₁ <| or <| and
        (rotate₃ <| and (close φ) (close χ))
        (rotate₂ <| and (close ψ) (close χ))
    ofEq this (by simp [DeMorgan.imply])
  dne φ :=
    have : 𝓚 ⊢ ∼φ ⋎ φ := or <| close φ
    ofEq this (by simp [DeMorgan.imply])

end Tait

end LO
