/-
Copyright (c) 2026 György Kurucz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: György Kurucz
-/
import Mathlib.Data.Set.Basic

/-!
# Alternating Büchi automata

We define positive Boolean formulas (`PositiveBool`), alternating Büchi automata
(`ABW`), their run DAGs (`RunDAG`), and the language they accept.
-/

namespace LeanModelChecking

/-- A positive Boolean formula over a set of atoms `Q`: a formula built from
atoms, `true`, `false`, conjunction, and disjunction (no negation). -/
inductive PositiveBool (Q : Type) where
| atom (q : Q)
| true
| false
| and (ψ₁ ψ₂ : PositiveBool Q)
| or (ψ₁ ψ₂ : PositiveBool Q)

/-- `PositiveBool.Sat Y f` holds when the set `Y` of atoms satisfies the positive
Boolean formula `f` (reading atoms as "is a member of `Y`"). -/
def PositiveBool.Sat {Q} (Y : Set Q) : PositiveBool Q → Prop
| atom q => q ∈ Y
| true => True
| false => False
| and ψ₁ ψ₂ => Sat Y ψ₁ ∧ Sat Y ψ₂
| or ψ₁ ψ₂ => Sat Y ψ₁ ∨ Sat Y ψ₂

theorem PositiveBool.Sat.monotone {Q} {f : PositiveBool Q} {A B : Set Q} :
    A ⊆ B → PositiveBool.Sat A f → PositiveBool.Sat B f := by
  induction f <;> grind [Sat]

/-- An alternating Büchi automaton over input alphabet `S` and state space `Q`. -/
structure ABW (S Q : Type) where
  /-- The initial state. -/
  q₀ : Q
  /-- The transition function, mapping a state and a letter to a positive Boolean
  formula over the successor states. -/
  δ : Q → S → PositiveBool Q
  /-- The set of accepting (final) states. -/
  F : Set Q

/-- The underlying data of a directed acyclic graph whose vertices are
state/level pairs: a vertex set `V` and an edge set `E`. -/
structure DAG.Base Q where
  /-- The set of vertices, each a state paired with a level. -/
  V : Set (Q × ℕ)
  /-- The set of edges, each from a state/level pair to a successor state. -/
  E : Set ((Q × ℕ) × Q)
/-- A directed acyclic graph of state/level pairs in which every edge connects a
vertex on level `i` to a vertex on level `i + 1`. -/
structure DAG Q extends DAG.Base Q where
  /-- Every edge starts at a vertex of `V` and ends at a vertex on the next level. -/
  edge_closure : ∀ e ∈ E, e.1 ∈ V ∧ (e.2, e.1.2 + 1) ∈ V

/-- Infinite path, with an arbitrary starting level. -/
def DAG.path {Q} (G : DAG Q) (p : ℕ → Q) :=
  ∃ n, ∀ i, ((p i, n + i), p (i + 1)) ∈ G.E

/-- A run DAG of the automaton `A` on the word `w`: a `DAG` rooted at the initial
state in which every vertex's successors satisfy the relevant transition formula. -/
structure RunDAG {S Q} (A : ABW S Q) (w : ℕ → S) extends DAG Q where
  /-- The initial state sits at the root (level `0`). -/
  p_root : (A.q₀, 0) ∈ V
  /-- Each vertex has a set of successors satisfying its transition formula. -/
  p_sat :
    ∀ v ∈ V, let (q, i) := v;
    ∃ Y,
    PositiveBool.Sat Y (A.δ q (w i)) ∧
    {(q, i)} ×ˢ Y ⊆ E

/-- A run DAG is accepting when every infinite path through it visits an
accepting state infinitely often. -/
def RunDAG.accepting {S Q} {A : ABW S Q} {w : ℕ → S} (G : RunDAG A w) :=
  ∀ p, G.path p → ∀ i, ∃ j ≥ i, p j ∈ A.F

/-- The automaton `A` accepts the word `w` when it admits an accepting run DAG. -/
def ABW.language {S Q} (A : ABW S Q) (w : Nat → S) :=
  ∃ (G : RunDAG A w), G.accepting

end LeanModelChecking
