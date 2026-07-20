/-
Copyright (c) 2026 Vikraman Choudhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vikraman Choudhury
-/
import LeanPool.EventStructures.Basic
import Mathlib.Data.Finset.Basic

/-!
# Configurations

A configuration of an event structure is a conflict-free, downward-closed set of
events. This module defines configurations (and their finite variant), the
enabling relation between a configuration and an event, and proves that enabling
an event extends a configuration.
-/

namespace EventStructures

variable (es : EventStructure)

/-- A set of events is a configuration if it is conflict-free and downward closed. -/
@[simp] def isConf (X : Set es.Event) : Prop :=
  (∀ {e₁ e₂}, e₁ ∈ X → e₂ ∈ X → ¬ es.conflict e₁ e₂) ∧
  (∀ {e e'}, e ∈ X → e' ≤ e → e' ∈ X)

/-- Type of all configurations of an event structure. -/
def Conf : Type := {X : Set es.Event // isConf es X}

/-- Type of all finite configurations of an event structure. -/
def FinConf : Type := {X : Finset es.Event // isConf es (X : Set es.Event)}

namespace Configuration

/-- A configuration c enables an event e if e is fresh (not already in c),
    e is consistent with all events in c, and the past of e is contained in c.
    Freshness rules out self-loop edges in the configuration graph. -/
def enables (c : Set es.Event) (e : es.Event) : Prop :=
  isConf es c ∧
  e ∉ c ∧
  (∀ e' ∈ c, es.consistent e e') ∧
  es.past e ⊆ c

/-- Notation for the enabling relation. -/
local infix:50 " ⊢ " => enables es

/-- An enabled event is not already in the configuration. -/
lemma enables_not_mem {c : Set es.Event} {e : es.Event} (h : c ⊢ e) : e ∉ c :=
  h.2.1

/-- If a configuration c enables an event e, then c ∪ {e} is also a configuration. -/
lemma enables_extension {c : Set es.Event} {e : es.Event} (h : c ⊢ e) :
    isConf es (c ∪ {e}) := by
  obtain ⟨⟨hConflictFree, hDownClosed⟩, -, hConsistent, hPast⟩ := h
  constructor
  · -- Conflict-free
    intro e₁ e₂ h₁ h₂
    obtain h₁ | h₁ := h₁
    · obtain h₂ | h₂ := h₂
      · exact hConflictFree h₁ h₂
      · rw [Set.mem_singleton_iff] at h₂
        exact h₂ ▸ fun hConf => hConsistent e₁ h₁ (es.conflict_symm hConf)
    · rw [Set.mem_singleton_iff] at h₁
      obtain h₂ | h₂ := h₂
      · exact h₁ ▸ fun hConf => hConsistent e₂ h₂ hConf
      · rw [Set.mem_singleton_iff] at h₂
        rw [h₁, h₂]
        exact es.conflict_irrefl e
  · -- Downward closed
    intro e' e'' h' h''
    obtain h' | h' := h'
    · exact Set.mem_union_left _ (hDownClosed h' h'')
    · rw [Set.mem_singleton_iff] at h'
      subst h'
      rcases lt_or_eq_of_le h'' with hlt | rfl
      · exact Set.mem_union_left _ (hPast hlt)
      · exact Set.mem_union_right _ rfl

end Configuration

end EventStructures
