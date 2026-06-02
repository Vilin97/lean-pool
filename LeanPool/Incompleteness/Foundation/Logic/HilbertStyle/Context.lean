/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Logic.Entailment
import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Basic

/-! # Context -/


namespace LO

namespace Entailment

variable (F : Type*) {S : Type*}

/-- Imported declaration from the Incompleteness formalization. -/
structure FiniteContext (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  ctx : List F

variable {F}

namespace FiniteContext

variable {𝓢 : S}

instance : Coe (List F) (FiniteContext F 𝓢) := ⟨mk⟩

/-- Imported declaration from the Incompleteness formalization. -/
abbrev conj [LogicalConnective F] (Γ : FiniteContext F 𝓢) : F := ⋀Γ.ctx

/-- Imported declaration from the Incompleteness formalization. -/
abbrev disj [LogicalConnective F] (Γ : FiniteContext F 𝓢) : F := ⋁Γ.ctx

instance : EmptyCollection (FiniteContext F 𝓢) := ⟨⟨[]⟩⟩

instance : Membership F (FiniteContext F 𝓢) := ⟨fun Γ x => (x ∈ Γ.ctx)⟩

instance : HasSubset (FiniteContext F 𝓢) := ⟨(·.ctx ⊆ ·.ctx)⟩

instance : Cons F (FiniteContext F 𝓢) := ⟨(· :: ·.ctx)⟩

lemma mem_def {φ : F} {Γ : FiniteContext F 𝓢} : φ ∈ Γ ↔ φ ∈ Γ.ctx := iff_of_eq rfl

@[simp 1100] lemma coe_subset_coe_iff {Γ Δ : List F} : (Γ :
    FiniteContext F 𝓢) ⊆ Δ ↔ Γ ⊆ Δ :=
  iff_of_eq rfl

@[simp] lemma mem_coe_iff {φ : F} {Γ : List F} : φ ∈ (Γ :
    FiniteContext F 𝓢) ↔ φ ∈ Γ :=
  iff_of_eq rfl

@[simp 1100] lemma not_mem_empty (φ : F) : ¬φ ∈ (∅ :
    FiniteContext F 𝓢) := by
  simp [EmptyCollection.emptyCollection]

instance : Collection F (FiniteContext F 𝓢) where
  subset_iff := List.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Cons.cons, mem_def]

variable [Entailment F S] [LogicalConnective F]

instance (𝓢 : S) : Entailment F (FiniteContext F 𝓢) := ⟨(𝓢 ⊢ ·.conj ==> ·)⟩

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Prf (𝓢 : S) (Γ : List F) (φ : F) : Type _ := (Γ : FiniteContext F 𝓢) ⊢ φ

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Provable (𝓢 : S) (Γ : List F) (φ : F) : Prop := (Γ : FiniteContext F 𝓢) ⊢! φ

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Unprovable (𝓢 : S) (Γ : List F) (φ : F) : Prop := (Γ : FiniteContext F 𝓢) ⊬ φ

/-- Imported declaration from the Incompleteness formalization. -/
abbrev PrfSet (𝓢 : S) (Γ : List F) (s : Set F) : Type _ := (Γ : FiniteContext F 𝓢) ⊢* s

/-- Imported declaration from the Incompleteness formalization. -/
abbrev ProvableSet (𝓢 : S) (Γ : List F) (s : Set F) : Prop := (Γ : FiniteContext F 𝓢) ⊢!* s

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ:45 " ⊢[" 𝓢 "] " φ:46 => Prf 𝓢 Γ φ

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ:45 " ⊢[" 𝓢 "]! " φ:46 => Provable 𝓢 Γ φ

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ:45 " ⊬[" 𝓢 "] " φ:46 => Unprovable 𝓢 Γ φ

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ:45 " ⊢[" 𝓢 "]* " s:46 => PrfSet 𝓢 Γ s

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ:45 " ⊢[" 𝓢 "]*! " s:46 => ProvableSet 𝓢 Γ s

lemma entailment_def (Γ : FiniteContext F 𝓢) (φ : F) : (Γ ⊢ φ) = (𝓢 ⊢ Γ.conj ==> φ) := rfl

/-- Imported declaration from the Incompleteness formalization. -/
def ofDef {Γ : List F} {φ : F} (b : 𝓢 ⊢ ⋀Γ ==> φ) : Γ ⊢[𝓢] φ := b

/-- Imported declaration from the Incompleteness formalization. -/
def toDef {Γ : List F} {φ : F} (b : Γ ⊢[𝓢] φ) : 𝓢 ⊢ ⋀Γ ==> φ := b

lemma «toₛ!» (b : Γ ⊢[𝓢]! φ) : 𝓢 ⊢! ⋀Γ ==> φ := b

lemma provable_iff {φ : F} : Γ ⊢[𝓢]! φ ↔ 𝓢 ⊢! ⋀Γ ==> φ := iff_of_eq rfl

/-- Imported declaration from the Incompleteness formalization. -/
def cast {Γ φ} (d : Γ ⊢[𝓢] φ) (eΓ : Γ = Γ') (eφ : φ = φ') : Γ' ⊢[𝓢] φ' := eΓ ▸ eφ ▸ d

section «lp_section_1»

variable {Γ Δ E : List F}
variable [Entailment.Minimal 𝓢]

instance [DecidableEq F] : Axiomatized (FiniteContext F 𝓢) where
  prfAxm := fun hp ↦ generalConj' hp
  weakening := fun H b ↦ impTrans'' (conjImplyConj' H) b

instance : Compact (FiniteContext F 𝓢) where
  φ := fun {Γ} _ _ ↦ Γ
  φPrf := id
  φ_subset := by simp
  φ_finite := by rintro ⟨Γ⟩; simp [Collection.Finite, Collection.set]

/-- Imported declaration from the Incompleteness formalization. -/
def nthAxm {Γ} (n : ℕ) (h : n < Γ.length := by simp) : Γ ⊢[𝓢] Γ[n] := conj₂Nth Γ n h
lemma «nth_axm!» {Γ} (n : ℕ) (h : n < Γ.length := by simp) : Γ ⊢[𝓢]! Γ[n] := ⟨nthAxm n h⟩

/-- Imported declaration from the Incompleteness formalization. -/
def byAxm [DecidableEq F] {φ} (h : φ ∈ Γ := by simp) : Γ ⊢[𝓢] φ := Axiomatized.prfAxm (by simpa)

lemma «by_axm!» {φ} (h : φ ∈ Γ := by simp) :
    Γ ⊢[𝓢]! φ := by
  classical
  exact Axiomatized.provable_axm _ (by simpa)

/-- Imported declaration from the Incompleteness formalization. -/
def weakening [DecidableEq F] (h : Γ ⊆ Δ) {φ} :
    Γ ⊢[𝓢] φ → Δ ⊢[𝓢] φ :=
  Axiomatized.weakening (by simpa)

lemma «weakening!» (h : Γ ⊆ Δ) {φ} : Γ ⊢[𝓢]! φ → Δ ⊢[𝓢]! φ := by
  classical
  exact fun h ↦ (Axiomatized.le_of_subset (by simpa)).subset h

/-- Imported declaration from the Incompleteness formalization. -/
def of {φ : F} (b : 𝓢 ⊢ φ) : Γ ⊢[𝓢] φ := imply₁' (ψ := ⋀Γ) b

/-- Imported declaration from the Incompleteness formalization. -/
def emptyPrf {φ : F} : [] ⊢[𝓢] φ → 𝓢 ⊢ φ := fun b ↦ b ⨀ verum

/-- Imported declaration from the Incompleteness formalization. -/
lemma provable_iff_provable {φ : F} : 𝓢 ⊢! φ ↔ [] ⊢[𝓢]! φ :=
  ⟨fun b ↦ ⟨of b.some⟩, fun b ↦ ⟨emptyPrf b.some⟩⟩

lemma «of'!» (h : 𝓢 ⊢! φ) :
    Γ ⊢[𝓢]! φ :=
  weakening! (by simp) <| provable_iff_provable.mp h

/-- Imported declaration from the Incompleteness formalization. -/
def id : [φ] ⊢[𝓢] φ := nthAxm 0
@[simp] lemma «id!» : [φ] ⊢[𝓢]! φ := nth_axm! 0

/-- Imported declaration from the Incompleteness formalization. -/
def byAxm₀ : (φ :: Γ) ⊢[𝓢] φ := nthAxm 0
lemma «by_axm₀!» : (φ :: Γ) ⊢[𝓢]! φ := nth_axm! 0

/-- Imported declaration from the Incompleteness formalization. -/
def byAxm₁ : (φ :: ψ :: Γ) ⊢[𝓢] ψ := nthAxm 1
lemma «by_axm₁!» : (φ :: ψ :: Γ) ⊢[𝓢]! ψ := nth_axm! 1

/-- Imported declaration from the Incompleteness formalization. -/
def byAxm₂ : (φ :: ψ :: χ :: Γ) ⊢[𝓢] χ := nthAxm 2
lemma «by_axm₂!» : (φ :: ψ :: χ :: Γ) ⊢[𝓢]! χ := nth_axm! 2

instance (Γ : FiniteContext F 𝓢) : Entailment.ModusPonens Γ := ⟨mdp₁⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomVerum Γ := ⟨of verum⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomImply₁ Γ := ⟨fun _ _ ↦ of imply₁⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomImply₂ Γ := ⟨fun _ _ _ ↦ of imply₂⟩

instance (Γ : FiniteContext F 𝓢) :
    Entailment.HasAxiomAndElim Γ :=
  ⟨fun _ _ ↦ of and₁, fun _ _ ↦ of and₂⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomAndInst Γ := ⟨fun _ _ ↦ of and₃⟩

instance (Γ : FiniteContext F 𝓢) :
    Entailment.HasAxiomOrInst Γ :=
  ⟨fun _ _ ↦ of or₁, fun _ _ ↦ of or₂⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomOrElim Γ := ⟨fun _ _ _ ↦ of or₃⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.NegationEquiv Γ := ⟨fun _ ↦ of negEquiv⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.Minimal Γ where


/-- Imported declaration from the Incompleteness formalization. -/
def mdp' [DecidableEq F] (bΓ : Γ ⊢[𝓢] φ ==> ψ) (bΔ : Δ ⊢[𝓢] φ) :
    (Γ ++ Δ) ⊢[𝓢] ψ :=
  wk (by simp) bΓ ⨀ wk (by simp) bΔ

/-- Imported declaration from the Incompleteness formalization. -/
def deduct {φ ψ : F} : {Γ : List F} → (φ :: Γ) ⊢[𝓢] ψ → Γ ⊢[𝓢] φ ==> ψ
  | .nil => fun b ↦ ofDef <| imply₁' (toDef b)
  | .cons _ _ => fun b ↦ ofDef <| andImplyIffImplyImply'.mp (impTrans'' (andComm _ _) (toDef b))

lemma «deduct!» (h : (φ :: Γ) ⊢[𝓢]! ψ) :  Γ ⊢[𝓢]! φ ==> ψ  := ⟨FiniteContext.deduct h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def deductInv {φ ψ : F} : {Γ : List F} → Γ ⊢[𝓢] φ ==> ψ → (φ :: Γ) ⊢[𝓢] ψ
  | .nil => fun b => ofDef <| (toDef b) ⨀ verum
  | .cons _ _ => fun b => ofDef <| (impTrans'' (andComm _ _) (andImplyIffImplyImply'.mpr (toDef b)))

lemma «deductInv!» (h : Γ ⊢[𝓢]! φ ==> ψ) : (φ :: Γ) ⊢[𝓢]! ψ := ⟨FiniteContext.deductInv h.some⟩

lemma deduct_iff {φ ψ : F} {Γ : List F} : Γ ⊢[𝓢]! φ ==> ψ ↔ (φ :: Γ) ⊢[𝓢]! ψ :=
  ⟨fun h ↦ ⟨deductInv h.some⟩, fun h ↦ ⟨deduct h.some⟩⟩

/-- Imported declaration from the Incompleteness formalization. -/
def deduct' : [φ] ⊢[𝓢] ψ → 𝓢 ⊢ φ ==> ψ := fun b ↦ emptyPrf <| deduct b

lemma «deduct'!» (h : [φ] ⊢[𝓢]! ψ) : 𝓢 ⊢! φ ==> ψ := ⟨FiniteContext.deduct' h.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
def deductInv' : 𝓢 ⊢ φ ==> ψ → [φ] ⊢[𝓢] ψ := fun b ↦ deductInv <| of b

lemma «deductInv'!» (h : 𝓢 ⊢! φ ==> ψ) : [φ] ⊢[𝓢]! ψ := ⟨FiniteContext.deductInv' h.some⟩


instance deduction : Deduction (FiniteContext F 𝓢) where
  ofInsert := deduct
  inv := deductInv

instance : StrongCut (FiniteContext F 𝓢) (FiniteContext F 𝓢) :=
  ⟨fun {Γ Δ _} bΓ bΔ ↦
    have : Γ ⊢ Δ.conj := conjIntro' _ (fun _ hp ↦ bΓ hp)
    ofDef <| impTrans'' (toDef this) (toDef bΔ)⟩

instance [HasAxiomEFQ 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomEFQ Γ := ⟨fun _ ↦ of efq⟩

instance [HasAxiomEFQ 𝓢] : DeductiveExplosion (FiniteContext F 𝓢) := inferInstance

instance [HasAxiomDNE 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomDNE Γ := ⟨fun φ ↦ of (HasAxiomDNE.dne φ)⟩

end «lp_section_1»

instance [Entailment.Intuitionistic 𝓢] (Γ : FiniteContext F 𝓢) : Entailment.Intuitionistic Γ where

instance [Entailment.Classical 𝓢] (Γ : FiniteContext F 𝓢) : Entailment.Classical Γ where

end FiniteContext


variable (F)

/-- Imported declaration from the Incompleteness formalization. -/
structure Context (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  ctx : Set F

variable {F}


namespace Context

variable {𝓢 : S}

instance : Coe (Set F) (Context F 𝓢) := ⟨mk⟩

instance : EmptyCollection (Context F 𝓢) := ⟨⟨∅⟩⟩

instance : Membership F (Context F 𝓢) := ⟨fun Γ x => (x ∈ Γ.ctx)⟩

instance : HasSubset (Context F 𝓢) := ⟨(·.ctx ⊆ ·.ctx)⟩

instance : Cons F (Context F 𝓢) := ⟨(⟨insert · ·.ctx⟩)⟩

lemma mem_def {φ : F} {Γ : Context F 𝓢} : φ ∈ Γ ↔ φ ∈ Γ.ctx := iff_of_eq rfl

@[simp 1100] lemma coe_subset_coe_iff {Γ Δ : Set F} : (Γ : Context F 𝓢) ⊆ Δ ↔ Γ ⊆ Δ := iff_of_eq rfl

@[simp] lemma mem_coe_iff {φ : F} {Γ : Set F} : φ ∈ (Γ : Context F 𝓢) ↔ φ ∈ Γ := iff_of_eq rfl

@[simp 1100] lemma not_mem_empty (φ : F) : ¬φ ∈ (∅ : Context F 𝓢) := by
  intro h
  exact h

instance : Collection F (Context F 𝓢) where
  subset_iff := by rintro ⟨s⟩ ⟨u⟩; simp [Set.subset_def]
  not_mem_empty := by simp
  mem_cons_iff := by simp [Cons.cons, mem_def]

variable [LogicalConnective F] [Entailment F S]

/-- Imported declaration from the Incompleteness formalization. -/
structure Proof (Γ : Context F 𝓢) (φ : F) where
  /-- Imported declaration from the Incompleteness formalization. -/
  ctx : List F
  subset : ∀ ψ ∈ ctx, ψ ∈ Γ
  /-- Imported declaration from the Incompleteness formalization. -/
  prf : ctx ⊢[𝓢] φ

instance (𝓢 : S) : Entailment F (Context F 𝓢) := ⟨Proof⟩

variable (𝓢)

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Prf (Γ : Set F) (φ : F) : Type _ := (Γ : Context F 𝓢) ⊢ φ

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Provable (Γ : Set F) (φ : F) : Prop := (Γ : Context F 𝓢) ⊢! φ

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Unprovable (Γ : Set F) (φ : F) : Prop := (Γ : Context F 𝓢) ⊬ φ

/-- Imported declaration from the Incompleteness formalization. -/
abbrev PrfSet (Γ : Set F) (s : Set F) : Type _ := (Γ : Context F 𝓢) ⊢* s

/-- Imported declaration from the Incompleteness formalization. -/
abbrev ProvableSet (Γ : Set F) (s : Set F) : Prop := (Γ : Context F 𝓢) ⊢!* s

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ:45 " *⊢[" 𝓢 "] " φ:46 => Prf 𝓢 Γ φ

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ:45 " *⊢[" 𝓢 "]! " φ:46 => Provable 𝓢 Γ φ

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ:45 " *⊬[" 𝓢 "] " φ:46 => Unprovable 𝓢 Γ φ

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ:45 " *⊢[" 𝓢 "]* " s:46 => PrfSet 𝓢 Γ s

/-- Imported declaration from the Incompleteness formalization. -/
notation Γ:45 " *⊢[" 𝓢 "]*! " s:46 => ProvableSet 𝓢 Γ s

section «lp_section_2»

variable {𝓢}

lemma provable_iff {φ : F} : Γ *⊢[𝓢]! φ ↔ ∃ Δ : List F, (∀ ψ ∈ Δ, ψ ∈ Γ) ∧ Δ ⊢[𝓢]! φ :=
  ⟨by rintro ⟨⟨Δ, h, b⟩⟩; exact ⟨Δ, h, ⟨b⟩⟩, by rintro ⟨Δ, h, ⟨d⟩⟩; exact ⟨⟨Δ, h, d⟩⟩⟩

section «lp_section_3»

variable [Entailment.Minimal 𝓢]

instance [DecidableEq F] : Axiomatized (Context F 𝓢) where
  prfAxm := fun {Γ φ} hp ↦ ⟨[φ], by simpa using hp, byAxm (by simp [Collection.set])⟩
  weakening := fun h b ↦ ⟨b.ctx, fun φ hp ↦ Collection.subset_iff.mp h φ (b.subset φ hp), b.prf⟩

instance : Compact (Context F 𝓢) where
  φ := fun b ↦ Collection.set b.ctx
  φPrf := fun b ↦ ⟨b.ctx, by simp [Collection.set], b.prf⟩
  φ_subset := by rintro ⟨Γ⟩ φ b; exact b.subset
  φ_finite := by rintro ⟨Γ⟩; simp [Collection.Finite, Collection.set]

/-- Imported declaration from the Incompleteness formalization. -/
def deduct [DecidableEq F] {φ ψ : F} {Γ : Set F} : (insert φ Γ) *⊢[𝓢] ψ → Γ *⊢[𝓢] φ ==> ψ
  | ⟨Δ, h, b⟩ =>
    have h : ∀ ψ ∈ Δ, ψ = φ ∨ ψ ∈ Γ := by simpa using h
    let b' : (φ :: Δ.filter (· ≠ φ)) ⊢[𝓢] ψ :=
      FiniteContext.weakening
        (by simp only [ne_eq, decide_not]; rintro χ hr; simp [hr]; tauto)
        b
    ⟨ Δ.filter (· ≠ φ), by
      intro ψ; simp only [ne_eq, decide_not, List.mem_filter, Bool.not_eq_eq_eq_not,
        Bool.not_true, decide_eq_false_iff_not, mem_coe_iff, and_imp]
      intro hq ne
      rcases h ψ hq
      · contradiction
      · assumption,
      FiniteContext.deduct b' ⟩

/-- Imported declaration from the Incompleteness formalization. -/
def deductInv {φ ψ : F} {Γ : Set F} : Γ *⊢[𝓢] φ ==> ψ → (insert φ Γ) *⊢[𝓢] ψ
  | ⟨Δ, h, b⟩ => ⟨φ :: Δ, by
      simp only [List.mem_cons, mem_coe_iff, Set.mem_insert_iff, forall_eq_or_imp, true_or,
        true_and]
      intro χ hr; exact Or.inr (h χ hr), FiniteContext.deductInv b⟩

instance deduction [DecidableEq F] : Deduction (Context F 𝓢) where
  ofInsert := deduct
  inv := deductInv

/-- Imported declaration from the Incompleteness formalization. -/
def of {φ : F} (b : 𝓢 ⊢ φ) : Γ *⊢[𝓢] φ := ⟨[], by simp, FiniteContext.of b⟩

lemma «of!» (b : 𝓢 ⊢! φ) : Γ *⊢[𝓢]! φ := ⟨Context.of b.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def mdp [DecidableEq F] {Γ : Set F} (bpq : Γ *⊢[𝓢] φ ==> ψ) (bp : Γ *⊢[𝓢] φ) : Γ *⊢[𝓢] ψ :=
  ⟨ bpq.ctx ++ bp.ctx, by
    simp only [List.mem_append, mem_coe_iff]; rintro χ (hr | hr)
    · exact bpq.subset χ hr
    · exact bp.subset χ hr,
    FiniteContext.mdp' bpq.prf bp.prf ⟩

lemma «by_axm!» (h : φ ∈ Γ) : Γ *⊢[𝓢]! φ := by
  classical
  exact Entailment.by_axm _ (by simpa)

/-- Imported declaration from the Incompleteness formalization. -/
def emptyPrf {φ : F} : ∅ *⊢[𝓢] φ → 𝓢 ⊢ φ := by
  rintro ⟨Γ, hΓ, h⟩;
  have := List.eq_nil_iff_forall_not_mem.mpr hΓ;
  subst this;
  exact FiniteContext.emptyPrf h;

lemma «emptyPrf!» {φ : F} : ∅ *⊢[𝓢]! φ → 𝓢 ⊢! φ := fun h ↦ ⟨emptyPrf h.some⟩

lemma provable_iff_provable {φ : F} : 𝓢 ⊢! φ ↔ ∅ *⊢[𝓢]! φ := ⟨of!, emptyPrf!⟩

instance minimal [DecidableEq F] (Γ : Context F 𝓢) : Entailment.Minimal Γ where
  mdp := mdp
  verum := of verum
  imply₁ := fun _ _ ↦ of imply₁
  imply₂ := fun _ _ _ ↦ of imply₂
  and₁ := fun _ _ ↦ of and₁
  and₂ := fun _ _ ↦ of and₂
  and₃ := fun _ _ ↦ of and₃
  or₁ := fun _ _ ↦ of or₁
  or₂ := fun _ _ ↦ of or₂
  or₃ := fun _ _ _ ↦ of or₃
  negEquiv := fun _ ↦ of negEquiv

instance [HasAxiomEFQ 𝓢] (Γ : Context F 𝓢) : HasAxiomEFQ Γ := ⟨fun _ ↦ of efq⟩

instance [HasAxiomDNE 𝓢] (Γ : Context F 𝓢) : HasAxiomDNE Γ := ⟨fun φ ↦ of (HasAxiomDNE.dne φ)⟩

instance [HasAxiomEFQ 𝓢] : DeductiveExplosion (FiniteContext F 𝓢) := inferInstance

end «lp_section_3»

instance [DecidableEq F] [Entailment.Intuitionistic 𝓢] (Γ : Context F 𝓢) :
    Entailment.Intuitionistic Γ where

instance [DecidableEq F] [Entailment.Classical 𝓢] (Γ : Context F 𝓢) : Entailment.Classical Γ where

end «lp_section_2»

end Context

end Entailment

end LO
