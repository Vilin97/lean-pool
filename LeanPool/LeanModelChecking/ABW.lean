/-
Copyright (c) 2026 György Kurucz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: György Kurucz
-/
import Mathlib.Data.Set.Basic

inductive PositiveBool (Q : Type) where
| atom (q : Q)
| true
| false
| and (ψ₁ ψ₂ : PositiveBool Q)
| or (ψ₁ ψ₂ : PositiveBool Q)

def PositiveBool.Sat {Q} (Y : Set Q) : PositiveBool Q → Prop
| atom q => q ∈ Y
| true => True
| false => False
| and ψ₁ ψ₂ => Sat Y ψ₁ ∧ Sat Y ψ₂
| or ψ₁ ψ₂ => Sat Y ψ₁ ∨ Sat Y ψ₂

theorem PositiveBool.Sat.monotone {Q} {f : PositiveBool Q} {A B : Set Q} : A ⊆ B → PositiveBool.Sat A f → PositiveBool.Sat B f := by
  induction f <;> grind [Sat]

structure ABW (S Q : Type) where
  q₀ : Q
  δ : Q → S → PositiveBool Q
  F : Set Q

structure DAG.Base Q where
  V : Set (Q × ℕ)
  E : Set ((Q × ℕ) × Q)
structure DAG Q extends DAG.Base Q where
  edge_closure: ∀ e ∈ E, e.1 ∈ V ∧ (e.2, e.1.2 + 1) ∈ V

/-- Infinite path, with an arbitrary starting level. -/
def DAG.path {Q} (G : DAG Q) (p : ℕ → Q) :=
  ∃ n, ∀ i, ((p i, n + i), p (i + 1)) ∈ G.E

structure RunDAG {S Q} (A : ABW S Q) (w : ℕ → S) extends DAG Q where
  p_root : (A.q₀, 0) ∈ V
  p_sat :
    ∀ v ∈ V, let (q, i) := v;
    ∃ Y,
    PositiveBool.Sat Y (A.δ q (w i)) ∧
    {(q, i)} ×ˢ Y ⊆ E

def RunDAG.accepting {S Q} {A : ABW S Q} {w : ℕ → S} (G : RunDAG A w) :=
  ∀ p, G.path p → ∀ i, ∃ j ≥ i, p j ∈ A.F

def ABW.language {S Q} (A : ABW S Q) (w : Nat → S) :=
  ∃ (G : RunDAG A w), G.accepting
