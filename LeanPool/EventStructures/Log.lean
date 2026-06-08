/-
Copyright (c) 2026 Vikraman Choudhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vikraman Choudhury
-/
import LeanPool.EventStructures.Basic
import LeanPool.EventStructures.Configuration
import LeanPool.EventStructures.Computation

/-!
# Logs and compatibility

This module defines logged events and the log of a configuration (events that
have a minimal conflict with some event outside the configuration), and the
notion of a computation being compatible with a log.
-/

namespace EventStructures

variable (es : EventStructure)
open EventStructure
open Configuration

/-- Notation for minimal conflict. -/
local infixl:50 " ## " => es.minimalConflict

/-- An event e is logged if there exists some event e' with which it has minimal conflict. -/
@[simp]
def logged (e : es.Event) : Prop := ∃ e', e ## e'

/-- The log of a configuration c is the set of events in c that are logged
    and have a minimal conflict with some event outside c. -/
@[simp]
def log (c : Conf es) : Set es.Event :=
  {e ∈ c.1 | ∃ e' ∉ c.1, e ## e'}

namespace Log

/-- If e is in the log of c, then e is in c. -/
lemma log_subset {c : Conf es} : log es c ⊆ c.1 := fun _ ⟨h, _⟩ => h

/-- If e is in the log of c, then e is logged. -/
lemma log_logged {c : Conf es} {e : es.Event} (h : e ∈ log es c) : logged es e := by
  simp only [log, Set.mem_setOf_eq] at h
  exact ⟨h.2.choose, h.2.choose_spec.2⟩

/-- The log is a subset of the configuration. -/
lemma log_mem_iff {c : Conf es} {e : es.Event} :
    e ∈ log es c ↔ e ∈ c.1 ∧ ∃ e' ∉ c.1, e ## e' :=
  Iff.rfl

/-- e is logged if it has minimal conflict with some event. -/
lemma logged_iff {e : es.Event} : logged es e ↔ ∃ e', e ## e' :=
  Iff.rfl

/-- By symmetry of minimal conflict, if e is logged, then any e' with e ## e'
    also has minimal conflict with some event. -/
lemma logged_symm {e e' : es.Event} (h : e ## e') :
    logged es e' := by
  exact ⟨e, es.minimalConflict_symm h⟩

/-- Notation for the conflict relation. -/
local infixl:50 " # " => es.conflict

/-- If e is in the log of c and e' has minimal conflict with e,
    then either e' is not in c, or there exists another e'' not in c with e ## e''. -/
lemma log_has_conflict_outside {c : Conf es} {e : es.Event} (he : e ∈ log es c) :
    ∃ e' ∉ c.1, e ## e' := by
  simp only [log, Set.mem_setOf_eq] at he
  exact he.2

/-- A computation σ is compatible with a log l if:
    1. All events in l are in σ's target configuration
    2. Events in σ are consistent with events in l
    3. If an event in σ conflicts with any event, it must be in l -/
@[simp]
def compatibleWithLog (σ : Computations es) (l : Set es.Event) : Prop :=
  (∀ e ∈ l, e ∈ σ.1.1) ∧
  (∀ e ∈ σ.1.1, ∀ e' ∈ l, ¬ (e # e')) ∧
  (∀ e ∈ σ.1.1, ∀ e' : es.Event, e # e' → e ∈ l)

/-- Notation for computation compatible with log. -/
local infixl:50 " ⊨ " => compatibleWithLog es

/-- Extract the first condition: all events in the log are in the computation. -/
lemma compatibleWithLog_log_subset {σ : Computations es} {l : Set es.Event}
    (h : σ ⊨ l) : l ⊆ σ.1.1 :=
  h.1

/-- Extract the second condition: events in the computation are consistent with the log. -/
lemma compatibleWithLog_consistent {σ : Computations es} {l : Set es.Event}
    (h : σ ⊨ l) {e e' : es.Event} (he : e ∈ σ.1.1) (he' : e' ∈ l) : ¬ (e # e') :=
  h.2.1 e he e' he'

/-- Extract the third condition: conflicting events in the computation are in the log. -/
lemma compatibleWithLog_conflict_in_log {σ : Computations es} {l : Set es.Event}
    (h : σ ⊨ l) {e e' : es.Event} (he : e ∈ σ.1.1) (hconf : e # e') : e ∈ l :=
  h.2.2 e he e' hconf

/-- The type of all computations compatible with a given log. -/
def CompatibleComputations (l : Set es.Event) : Type _ :=
  {σ : Computations es // σ ⊨ l}

/-- Extract the underlying computation from a compatible computation. -/
def CompatibleComputations.val {l : Set es.Event} (σ : CompatibleComputations es l) :
    Computations es :=
  σ.1

/-- Extract the compatibility proof. -/
lemma CompatibleComputations.compatible {l : Set es.Event} (σ : CompatibleComputations es l) :
    σ.val ⊨ l :=
  σ.2

/-- A computation is compatible with the log of a configuration. -/
def compatibleWithConfigLog (c : Conf es) (σ : Computations es) : Prop :=
  σ ⊨ (log es c)

/-- The type of all computations compatible with the log of a configuration. -/
def CompatibleWithConfigLog (c : Conf es) : Type _ :=
  CompatibleComputations es (log es c)

end Log

end EventStructures
