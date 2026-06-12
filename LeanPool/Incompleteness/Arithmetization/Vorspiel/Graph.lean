/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Arithmetization.Vorspiel.Vorspiel

/-! # Graph -/


namespace Function

variable {σ α β : Sort*}

/-- Imported declaration from the Incompleteness formalization. -/
def Graphᵥ (f : (Fin k → α) → α) : (Fin (k + 1) → α) → Prop := fun v ↦ v 0 = f (v ·.succ)

/-- Imported declaration from the Incompleteness formalization. -/
def Graph (f : α → σ) : σ → α → Prop := fun y x ↦ y = f x

/-- Imported declaration from the Incompleteness formalization. -/
def Graph₂ (f : α → β → σ) : σ → α → β → Prop := fun y x₁ x₂ ↦ y = f x₁ x₂

/-- Imported declaration from the Incompleteness formalization. -/
def Graph₃ (f : α → β → γ → σ) : σ → α → β → γ → Prop := fun y x₁ x₂ x₃ ↦ y = f x₁ x₂ x₃

/-- Imported declaration from the Incompleteness formalization. -/
def Graph₄ (f : α → β → γ → δ → σ) :
    σ → α → β → γ → δ → Prop :=
  fun y x₁ x₂ x₃ x₄ ↦ y = f x₁ x₂ x₃ x₄

/-- Imported declaration from the Incompleteness formalization. -/
def Graph₅ (f : α → β → γ → δ → ε → σ) :
    σ → α → β → γ → δ → ε → Prop :=
  fun y x₁ x₂ x₃ x₄ x₅ ↦ y = f x₁ x₂ x₃ x₄ x₅

lemma _root_.Function.Graph.eq {f : α → σ} {y x} (h : Graph f y x) : f x = y := h.symm

lemma _root_.Function.Graph.iff_left (f : α → σ) {y x} :
    f x = y ↔ Graph f y x := by
  simp [Graph, eq_comm]

lemma _root_.Function.Graph.iff_right (f : α → σ) {y x} : y = f x ↔ Graph f y x := by simp [Graph]

lemma _root_.Function.Graph₂.eq {f : α → β → σ} {y x₁ x₂} (h : Graph₂ f y x₁ x₂) :
    f x₁ x₂ = y :=
  h.symm

lemma _root_.Function.Graph₂.iff_left (f : α → β → σ) {y x₁ x₂} :
    f x₁ x₂ = y ↔ Graph₂ f y x₁ x₂ := by
  simp [Graph₂, eq_comm]

lemma _root_.Function.Graph₂.iff_right (f : α → β → σ) {y x₁ x₂} :
    y = f x₁ x₂ ↔ Graph₂ f y x₁ x₂ := by
  simp [Graph₂]

lemma _root_.Function.Graph₃.eq {f : α → β → γ → σ} {y x₁ x₂ x₃} (h : Graph₃ f y x₁ x₂ x₃) :
    f x₁ x₂ x₃ = y :=
  h.symm

lemma _root_.Function.Graph₃.iff_left (f : α → β → γ → σ) {y x₁ x₂ x₃} :
    f x₁ x₂ x₃ = y ↔ Graph₃ f y x₁ x₂ x₃ := by
  simp [Graph₃, eq_comm]

lemma _root_.Function.Graph₃.iff_right (f : α → β → γ → σ) {y x₁ x₂ x₃} :
    y = f x₁ x₂ x₃ ↔ Graph₃ f y x₁ x₂ x₃ := by
  simp [Graph₃]

end Function
