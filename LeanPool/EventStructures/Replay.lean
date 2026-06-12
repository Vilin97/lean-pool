/-
Copyright (c) 2026 Vikraman Choudhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vikraman Choudhury
-/
import LeanPool.EventStructures.Basic
import LeanPool.EventStructures.Configuration
import LeanPool.EventStructures.Computation
import LeanPool.EventStructures.Log
import LeanPool.EventStructures.Trace

/-!
# Replay

This module defines minimal and maximal replays of a log, the minimum and
maximum replay sets, and proves that the minimum (resp. maximum) replay set is
the smallest (resp. largest) configuration compatible with a log, together with
uniqueness of minimal and maximal replays and *conditional* existence lemmas:
existence is established relative to a computation compatible with the log that
reaches the corresponding replay set, not unconditionally.
-/

namespace EventStructures

variable (es : EventStructure)
open EventStructure
open Configuration
open Log

/-- Notation for computation compatible with log. -/
local infixl:50 " ⊨ " => compatibleWithLog es

namespace Replay

/-- Extract the configuration from a computation. -/
def conf (σ : Computations es) : Conf es := σ.1

/-- A computation is a minimal replay of a log if it's compatible (σ ⊨ l) and
    its configuration is a subset of all other compatible computations. -/
def isMinReplay (l : Set es.Event) (σ : Computations es) : Prop :=
  σ ⊨ l ∧ ∀ σ' : Computations es, σ' ⊨ l → (conf es σ).1 ⊆ (conf es σ').1

/-- A computation is a maximal replay of a log if it's compatible (σ ⊨ l) and
    all other compatible computations' configurations are subsets of it. -/
def isMaxReplay (l : Set es.Event) (σ : Computations es) : Prop :=
  σ ⊨ l ∧ ∀ σ' : Computations es, σ' ⊨ l → (conf es σ').1 ⊆ (conf es σ).1

/-- The downset (or principal ideal) of an event e: all predecessors including e. -/
def downset (e : es.Event) : Set es.Event :=
  {x | x ≤ e}

/-- Notation for minimal conflict. -/
local infixl:50 " ## " => es.minimalConflict

/-- Notation for conflict. -/
local infixl:50 " # " => es.conflict

/-- The minimum replay set of a log l: union of all downsets of events in l. -/
def minReplaySet (l : Set es.Event) : Set es.Event :=
  ⋃ e ∈ l, downset es e

/-- The maximum replay set of a log l: the minimum replay set plus all events
    that are causally forced if any of their minimal conflicts (e₁ ## e₂) are in the log. -/
def maxReplaySet (l : Set es.Event) : Set es.Event :=
  minReplaySet es l ∪ {e : es.Event | ∀ e₁ e₂ : es.Event, e₁ ## e₂ ∧ e₁ ≤ e → e₁ ∈ l}

/-- The downset is closed under taking predecessors. -/
lemma downset_closed {e x y : es.Event} (hxy : x ≤ y) (hy : y ∈ downset es e) :
    x ∈ downset es e :=
  le_trans hxy hy

/-- The minimum replay set contains the log. -/
lemma minReplaySet_contains_log {l : Set es.Event} : l ⊆ minReplaySet es l := by
  intro e he
  simp only [minReplaySet, downset, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  exact ⟨e, he, le_rfl⟩

/-- The minimum replay set is closed under predecessors. -/
lemma minReplaySet_closed {l : Set es.Event} {x y : es.Event}
    (hy : y ≤ x) (hx : x ∈ minReplaySet es l) : y ∈ minReplaySet es l := by
  simp only [minReplaySet, downset, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hx ⊢
  obtain ⟨e, he, hxe⟩ := hx
  exact ⟨e, he, le_trans hy hxe⟩

/-- The maximum replay set contains the minimum replay set. -/
lemma minReplaySet_subset_maxReplaySet {l : Set es.Event} :
    minReplaySet es l ⊆ maxReplaySet es l :=
  Set.subset_union_left

/-- If e is in l and x ≤ e, and l is conflict-free,
    then x is compatible with all events in l. -/
lemma downset_compatible_with_log {l : Set es.Event} {e x : es.Event}
    (he : e ∈ l) (hxe : x ≤ e)
    (hl_conflict_free : ∀ {e₁ e₂}, e₁ ∈ l → e₂ ∈ l → ¬(e₁ # e₂)) :
    ∀ e' ∈ l, ¬(x # e') := by
  intro e' he' hconf
  have hconf_symm := es.conflict_symm hconf
  have : e' # e := es.conflict_hereditary hconf_symm hxe
  have : e # e' := es.conflict_symm this
  exact hl_conflict_free he he' this

/-- The minimum replay set is compatible with the log. -/
lemma minReplaySet_compatible_with_log {l : Set es.Event}
    (hl_conflict_free : ∀ {e₁ e₂}, e₁ ∈ l → e₂ ∈ l → ¬(e₁ # e₂)) :
    ∀ x ∈ minReplaySet es l, ∀ e ∈ l, ¬(x # e) := by
  intro x hx e he
  simp only [minReplaySet, downset, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hx
  obtain ⟨e', he', hxe'⟩ := hx
  exact downset_compatible_with_log es he' hxe' hl_conflict_free e he

/-- The minimum replay set is the smallest configuration compatible with a log.
    Any computation with configuration equal to minReplaySet is a minimal replay. -/
lemma minReplaySet_is_minimal_replay {l : Set es.Event} {σ : Computations es}
    (h_conf : (conf es σ).1 = minReplaySet es l)
    (h_compat : σ ⊨ l) :
    isMinReplay es l σ := by
  constructor
  · exact h_compat
  · intro σ' h'_compat
    rw [h_conf]
    intro x hx
    simp only [minReplaySet, downset, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hx
    obtain ⟨e, he, hxe⟩ := hx
    -- x ≤ e and e ∈ l
    -- σ' ⊨ l means all events in l are in σ'
    have : e ∈ (conf es σ').1 := h'_compat.1 e he
    exact (conf es σ').2.2 this hxe

/-- The maximum replay set is the largest configuration compatible with a log.
    Any computation with configuration equal to maxReplaySet is a maximal replay. -/
lemma maxReplaySet_is_maximal_replay {l : Set es.Event} {σ : Computations es}
    (h_conf : (conf es σ).1 = maxReplaySet es l)
    (h_compat : σ ⊨ l) :
    isMaxReplay es l σ := by
  constructor
  · exact h_compat
  · intro σ' h'_compat
    rw [h_conf]
    intro x hx
    -- hx : x ∈ (conf es σ').1, need to show: x ∈ maxReplaySet es l
    by_cases hconflict : ∃ e', x # e'
    · -- Case 1: x conflicts with something, so by compatibility x ∈ l ⊆ minReplaySet
      obtain ⟨e', hc⟩ := hconflict
      have x_in_l : x ∈ l := h'_compat.2.2 x hx e' hc
      left
      exact minReplaySet_contains_log es x_in_l
    · -- Case 2: x has no conflicts, show it's in the forced set
      right
      intro e₁ e₂ ⟨hmc, hle⟩
      -- e₁ ## e₂ and e₁ ≤ x
      -- Since x ∈ conf(σ') and configurations are downward-closed, e₁ ∈ conf(σ')
      have he₁_in : e₁ ∈ (conf es σ').1 := (conf es σ').2.2 hx hle
      -- From e₁ ## e₂, we have e₁ # e₂ (minimalConflict.1)
      have hconf_e₁_e₂ : e₁ # e₂ := hmc.1
      -- By compatibility of σ': e₁ ∈ conf(σ') and e₁ # e₂ implies e₁ ∈ l
      exact h'_compat.2.2 e₁ he₁_in e₂ hconf_e₁_e₂

/-- Any two minimal replays of a log have equal configurations.
    Since both are minimal, each configuration is a subset of the other by definition. -/
lemma minReplay_unique_config {l : Set es.Event} {σ₁ σ₂ : Computations es}
    (h₁ : isMinReplay es l σ₁) (h₂ : isMinReplay es l σ₂) :
    (conf es σ₁).1 = (conf es σ₂).1 := by
  ext x
  constructor
  · intro hx
    -- By minimality of σ₁: (conf es σ₁).1 ⊆ (conf es σ₂).1 (since σ₂ ⊨ l)
    exact h₁.2 σ₂ h₂.1 hx
  · intro hx
    -- By minimality of σ₂: (conf es σ₂).1 ⊆ (conf es σ₁).1 (since σ₁ ⊨ l)
    exact h₂.2 σ₁ h₁.1 hx

/-- Any two maximal replays of a log have equal configurations.
    Since both are maximal, each configuration is a superset of the other by definition. -/
lemma maxReplay_unique_config {l : Set es.Event} {σ₁ σ₂ : Computations es}
    (h₁ : isMaxReplay es l σ₁) (h₂ : isMaxReplay es l σ₂) :
    (conf es σ₁).1 = (conf es σ₂).1 := by
  ext x
  constructor
  · intro hx
    -- hx : x ∈ (conf es σ₁).1, need: x ∈ (conf es σ₂).1
    -- By maximality of σ₂: (conf es σ₁).1 ⊆ (conf es σ₂).1 (since σ₁ ⊨ l)
    exact h₂.2 σ₁ h₁.1 hx
  · intro hx
    -- hx : x ∈ (conf es σ₂).1, need: x ∈ (conf es σ₁).1
    -- By maximality of σ₁: (conf es σ₂).1 ⊆ (conf es σ₁).1 (since σ₂ ⊨ l)
    exact h₁.2 σ₂ h₂.1 hx

/-- Conditional existence of the minimal replay: *if* some computation
    compatible with the log reaches the minimum replay set, then a minimal
    replay exists. This is a characterization lemma, not an unconditional
    existence theorem; minimality follows from minReplaySet_is_minimal_replay. -/
lemma minReplay_exists (l : Set es.Event)
    (hexists : ∃ σ : Computations es, (conf es σ).1 = minReplaySet es l ∧ σ ⊨ l) :
    ∃ σ : Computations es, isMinReplay es l σ := by
  obtain ⟨σ, h_conf, h_compat⟩ := hexists
  exact ⟨σ, minReplaySet_is_minimal_replay es h_conf h_compat⟩

/-- Conditional existence of the maximal replay: *if* some computation
    compatible with the log reaches the maximum replay set, then a maximal
    replay exists. This is a characterization lemma, not an unconditional
    existence theorem; maximality follows from maxReplaySet_is_maximal_replay. -/
lemma maxReplay_exists (l : Set es.Event)
    (hexists : ∃ σ : Computations es, (conf es σ).1 = maxReplaySet es l ∧ σ ⊨ l) :
    ∃ σ : Computations es, isMaxReplay es l σ := by
  obtain ⟨σ, h_conf, h_compat⟩ := hexists
  exact ⟨σ, maxReplaySet_is_maximal_replay es h_conf h_compat⟩

/-- Uniqueness of the minimal replay: any two minimal replays of a log reach
    the same configuration. -/
lemma minReplay_unique {l : Set es.Event} {σ₁ σ₂ : Computations es}
    (h₁ : isMinReplay es l σ₁) (h₂ : isMinReplay es l σ₂) :
    conf es σ₁ = conf es σ₂ := by
  apply Subtype.ext
  exact minReplay_unique_config es h₁ h₂

/-- Uniqueness of the maximal replay: any two maximal replays of a log reach
    the same configuration. -/
lemma maxReplay_unique {l : Set es.Event} {σ₁ σ₂ : Computations es}
    (h₁ : isMaxReplay es l σ₁) (h₂ : isMaxReplay es l σ₂) :
    conf es σ₁ = conf es σ₂ := by
  apply Subtype.ext
  exact maxReplay_unique_config es h₁ h₂

end Replay

end EventStructures
