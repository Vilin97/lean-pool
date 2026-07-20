/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.FirstOrder.Arith.PeanoMinus

/-! # StrictHierarchy -/


namespace LO

namespace FirstOrder

namespace Arith

section «lp_section_1»

variable {L : Language} [L.LT]

/-- Imported declaration from the Incompleteness formalization. -/
inductive StrictHierarchy : Polarity → ℕ → {n : ℕ} → Semiformula L μ n → Prop
  | zero {Γ φ}                                : DeltaZero φ → StrictHierarchy Γ s φ
  | sigma {s n} {φ : Semiformula L μ (n + 1)} : StrictHierarchy Pg s φ →
    StrictHierarchy Sg (s + 1) (∃' φ)
  | pi {s n} {φ : Semiformula L μ (n + 1)}    : StrictHierarchy Sg s φ →
    StrictHierarchy Pg (s + 1) (∀' φ)
  | ex {s n} {φ : Semiformula L μ (n + 1)}    : StrictHierarchy Sg (s + 1) φ →
    StrictHierarchy Sg (s + 1) (∃' φ)
  | all {s n} {φ : Semiformula L μ (n + 1)}   : StrictHierarchy Pg (s + 1) φ →
    StrictHierarchy Pg (s + 1) (∀' φ)

lemma _root_.LO.FirstOrder.Arith.DeltaZero.of_open {φ : Semiformula L μ n} :
    φ.Open → DeltaZero φ := Hierarchy.of_open

namespace StrictHierarchy

lemma rew {φ : Semiformula L μ₁ n₁} (h : StrictHierarchy Γ s φ) (ω : Rew L μ₁ n₁ μ₂ n₂) :
    StrictHierarchy Γ s (ω ▹ φ) := by
  induction h generalizing μ₂ n₂ <;> try simp only [Rewriting.app_ex, Rewriting.app_all]
  case zero h => exact zero <| (Hierarchy.rew_iff (ω := ω)).mpr h
  case sigma ih => exact (ih ω.q).sigma
  case pi ih => exact (ih ω.q).pi
  case ex ih => exact (ih ω.q).ex
  case all ih => exact (ih ω.q).all

lemma rew_iff {φ : Semiformula L μ₁ n₁} (ω : Rew L μ₁ n₁ μ₂ n₂) :
    StrictHierarchy Γ s (ω ▹ φ) ↔ StrictHierarchy Γ s φ :=
  ⟨by
    generalize hq : ω ▹ φ = ψ
    intro h;
    induction h generalizing n₁ <;> try
      simp only [Semiformula.eq_all_iff, Semiformula.eq_ex_iff] at hq ⊢
    case zero ψ h =>
      rcases hq; exact zero (Hierarchy.rew_iff.mp h)
    case sigma h ih =>
      rcases hq with ⟨_, rfl, rfl⟩
      exact (ih ω.q rfl).sigma
    case pi h ih =>
      rcases hq with ⟨_, rfl, rfl⟩
      exact (ih ω.q rfl).pi
    case ex h ih =>
      rcases hq with ⟨_, rfl, rfl⟩
      exact (ih ω.q rfl).ex
    case all ih =>
      rcases hq with ⟨_, rfl, rfl⟩
      exact (ih ω.q rfl).all,
  fun h ↦ h.rew ω⟩

lemma succ {Γ} {φ : Semiformula L μ₁ n₁} (h : StrictHierarchy Γ s φ) :
    StrictHierarchy Γ (s + 1) φ := by
  induction h
  case zero h => exact zero h
  case sigma ih => exact ih.sigma
  case pi ih => exact ih.pi
  case ex ih => exact ih.ex
  case all ih => exact ih.all

lemma zero_iff_delta_zero {Γ} {φ : Semiformula L μ n} :
    StrictHierarchy Γ 0 φ ↔ DeltaZero φ := by
  constructor
  · rintro ⟨h⟩; exact h
  · intro h; exact zero h

end StrictHierarchy

end «lp_section_1»

end Arith
end FirstOrder
end LO
