/-
Copyright (c) 2026 Vikraman Choudhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vikraman Choudhury
-/
import Mathlib.Order.Basic

/-!
# Event structures

This module defines `EventStructure`: a set of events equipped with a causal
partial order and an irreflexive, symmetric binary conflict relation, together
with the derived consistency, concurrency, minimal-conflict and past/future
notions used throughout the development, and decidability data for events.
-/

namespace EventStructures

/-- An event structure with binary conflict. -/
structure EventStructure where
  /-- The type of events. -/
  Event : Type*
  /-- The causal partial order on events. -/
  [poEvent : PartialOrder Event]
  /-- The binary conflict relation on events. -/
  conflict : Event → Event → Prop
  conflict_irrefl : ∀ e, ¬ conflict e e
  conflict_symm : ∀ ⦃e₁ e₂⦄, conflict e₁ e₂ → conflict e₂ e₁
  conflict_hereditary : ∀ {e₁ e₂ e₃}, conflict e₁ e₂ → e₂ ≤ e₃ → conflict e₁ e₃

namespace EventStructure

variable (es : EventStructure)

instance : PartialOrder es.Event := es.poEvent

/-- Notation for the conflict relation. -/
local infixl:50 " # " => es.conflict

/-- Consistency relation: two events are consistent if they are not in conflict. -/
@[simp]
def consistent (e₁ e₂ : es.Event) : Prop := ¬ (e₁ # e₂)

/-- Consistency is reflexive. -/
lemma consistent_refl : ∀ e, es.consistent e e := es.conflict_irrefl

/-- Consistency is symmetric. -/
lemma consistent_symm : ∀ ⦃e₁ e₂⦄, es.consistent e₁ e₂ → es.consistent e₂ e₁ :=
  fun _ _ h h' => h (es.conflict_symm h')

/-- Concurrency relation: two events are concurrent if they are
    consistent and causally independent. -/
@[simp]
def concurrent (e₁ e₂ : es.Event) : Prop :=
  es.consistent e₁ e₂ ∧ ¬ (e₁ ≤ e₂) ∧ ¬ (e₂ ≤ e₁)
local infixl:50 " ⋈ " => es.concurrent

/-- Concurrency is irreflexive. -/
lemma concurrent_irrefl : ∀ e, ¬ es.concurrent e e :=
  fun _ ⟨_, hNotLe, _⟩ => hNotLe le_rfl

/-- Concurrency is symmetric. -/
lemma concurrent_symm : ∀ ⦃e₁ e₂⦄, es.concurrent e₁ e₂ → es.concurrent e₂ e₁ := by
  intro e₁ e₂ h
  rcases h with ⟨hCons, hNotLe12, hNotLe21⟩
  refine ⟨?_, hNotLe21, hNotLe12⟩
  exact (consistent_symm es) hCons

/-- Minimal conflict relation: (e₁, e₂) is a minimal conflicting pair if they conflict
    and there is no proper reduction of either that still produces a conflict.
    Formally: e₁ # e₂ and for all e₁' ≤ e₁, e₂' ≤ e₂, if e₁' # e₂' then e₁' = e₁ ∧ e₂' = e₂ -/
@[simp]
def minimalConflict (e₁ e₂ : es.Event) : Prop :=
  es.conflict e₁ e₂ ∧
  ∀ e₁' e₂', e₁' ≤ e₁ → e₂' ≤ e₂ → es.conflict e₁' e₂' → e₁' = e₁ ∧ e₂' = e₂

/-- Notation for minimal conflict. -/
local infixl:50 " ## " => es.minimalConflict

/-- Minimal conflict is symmetric. -/
lemma minimalConflict_symm : ∀ ⦃e₁ e₂⦄, es.minimalConflict e₁ e₂ → es.minimalConflict e₂ e₁ := by
  intro e₁ e₂ ⟨hConf, hMin⟩
  refine ⟨es.conflict_symm hConf, ?_⟩
  intro e₂' e₁' he₂ he₁ hConf'
  have := hMin e₁' e₂' he₁ he₂ (es.conflict_symm hConf')
  exact ⟨this.2, this.1⟩

/-- If (e₁, e₂) is a minimal conflict, then e₁ and e₂ conflict. -/
lemma minimalConflict_conflict {e₁ e₂ : es.Event} (h : es.minimalConflict e₁ e₂) :
    es.conflict e₁ e₂ :=
  h.1

/-- If (e₁, e₂) is a minimal conflict and e₁' ≤ e₁, e₂' ≤ e₂ with e₁' ## e₂',
    then e₁' = e₁ and e₂' = e₂. -/
lemma minimalConflict_minimal {e₁ e₂ e₁' e₂' : es.Event} (h : es.minimalConflict e₁ e₂)
    (he₁ : e₁' ≤ e₁) (he₂ : e₂' ≤ e₂) (hConf : es.conflict e₁' e₂') :
    e₁' = e₁ ∧ e₂' = e₂ :=
  h.2 e₁' e₂' he₁ he₂ hConf

/-- The strict past of an event: all events strictly preceding it. -/
@[simp] def past (e : es.Event) : Set es.Event := {x | x < e}

/-- The future (upset) of an event: all events causally succeeding it. -/
@[simp] def future (e : es.Event) : Set es.Event := {x | e ≤ x}

end EventStructure

/-- Decidability data for an event structure: decidable equality on events and
    decidable strict order. Together these yield decidable causality. -/
class DecidableEventStructure (es : EventStructure) where
  decEq : DecidableEq es.Event
  decLt : DecidableRel ((· < ·) : es.Event → es.Event → Prop)

attribute [reducible, instance] DecidableEventStructure.decEq DecidableEventStructure.decLt

instance EventStructure.decLe (es : EventStructure) [DecidableEventStructure es] :
    DecidableRel ((· ≤ ·) : es.Event → es.Event → Prop) := fun a b =>
  if hab : a = b then isTrue (hab ▸ le_refl a)
  else if hlt : a < b then isTrue (le_of_lt hlt)
  else isFalse fun h => (lt_or_eq_of_le h).elim hlt hab

end EventStructures
