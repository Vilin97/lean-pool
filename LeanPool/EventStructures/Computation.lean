/-
Copyright (c) 2026 Vikraman Choudhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vikraman Choudhury
-/
import LeanPool.EventStructures.Configuration
import LeanPool.EventStructures.Path
import LeanPool.EventStructures.Trace
import Mathlib.Logic.Function.Basic

/-!
# Computations

A computation to a configuration is an asynchronous path from the empty
configuration to it. This module defines computations, the type of reachable
configurations, and linearisations, and relates computations to the
configurations they reach.
-/

namespace EventStructures

variable (es : EventStructure)
open EventStructure
open Configuration
open Path
open Trace

/-- Notation for trace equivalence. -/
local infixr:60 " ≈ₜ " => TraceEquiv es

/-- The empty configuration is a valid configuration. -/
def emptyConf : Conf es :=
  ⟨(∅ : Set es.Event), by
    constructor
    · intro e₁ e₂ h₁ h₂
      exact False.elim (by simp at h₁)
    · intro e e' hmem hle
      exact False.elim (by simp at hmem)
  ⟩

/-- A computation to a configuration `c` is an asynchronous path
  starting at the empty configuration and ending at `c`.
  Equivalently, a computation records a causal execution up to
  trace equivalence of the underlying path. -/
def Computation (c : Conf es) : Type _ :=
  Path.Async es (emptyConf es) c

/-- The type of all computations, paired with their target configuration. -/
def Computations : Type _ := Σ c : Conf es, Computation es c

/-- A list of events `t` is a linearisation of configuration `c`
  if it is trace-equivalent to the trace of some path from the
  empty configuration to `c`. Equivalently, `t` enumerates
  the events of `c` in some order compatible with causality. -/
def isLinearisation (c : Conf es) (t : List es.Event) : Prop :=
  ∃ p : Path es (emptyConf es) c, Path.trace es p ≈ₜ t

/-- Every computation determines a linearisation of its target configuration. -/
lemma computation_is_linearisation {c : Conf es} (comp : Computation es c) :
    ∃ t : List es.Event, isLinearisation es c t := by
  obtain ⟨p, rfl⟩ := Quotient.exists_rep comp
  refine ⟨Path.trace es p, ⟨p, TraceEquiv.refl _⟩⟩

/-- Configurations that are reachable by a computation. -/
def ReachableConf : Type _ := {c : Conf es // Nonempty (Computation es c)}

/-- Every computation targets a reachable configuration. -/
def computationToReachable : Computations es → ReachableConf es :=
  fun p => ⟨p.1, ⟨p.2⟩⟩

/-- The map from computations to reachable configurations is surjective. -/
lemma computation_to_reachable_surjective :
    Function.Surjective (computationToReachable es) :=
  fun ⟨c, ⟨comp⟩⟩ => ⟨⟨c, comp⟩, rfl⟩

end EventStructures
