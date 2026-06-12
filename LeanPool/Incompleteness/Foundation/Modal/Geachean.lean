/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Vorspiel.RelItr
import LeanPool.Incompleteness.Foundation.Vorspiel.BinaryRelations

/-! # Geachean -/


/-- Imported declaration from the Incompleteness formalization. -/
structure Geachean.Taple where
  /-- Imported declaration from the Incompleteness formalization. -/
  i : ℕ
  /-- Imported declaration from the Incompleteness formalization. -/
  j : ℕ
  /-- Imported declaration from the Incompleteness formalization. -/
  m : ℕ
  /-- Imported declaration from the Incompleteness formalization. -/
  n : ℕ

/-- Imported declaration from the Incompleteness formalization. -/
def Geachean (t : Geachean.Taple) (R : Rel α α) := ∀ {x y z :
    α}, (R.iterate t.i x y) ∧ (R.iterate t.j x z) → ∃ u, (R.iterate t.m y u) ∧ (R.iterate t.n z u)


namespace Geachean

variable {rel : Rel α α}

lemma serial_def : Serial rel ↔ (Geachean ⟨0, 0, 1, 1⟩ rel) := by simp [Geachean, Serial];

lemma reflexive_def : Std.Refl rel ↔ (Geachean ⟨0, 0, 1, 0⟩ rel) := by
  constructor
  · intro h
    simp only [Geachean, Rel.iterate.iff_zero, Rel.iterate.iff_succ, exists_eq_right,
      exists_eq_right', and_imp, forall_apply_eq_imp_iff, forall_eq']
    intro x
    exact h.refl x
  · intro h
    simp only [Geachean, Rel.iterate.iff_zero, Rel.iterate.iff_succ, exists_eq_right,
      exists_eq_right', and_imp, forall_apply_eq_imp_iff, forall_eq'] at h
    exact ⟨fun x => h (x := x)⟩

lemma symmetric_def : Symmetric rel ↔ (Geachean ⟨0, 1, 0, 1⟩ rel) := by
  simp only [Symmetric, Geachean, Rel.iterate.iff_zero, Rel.iterate.iff_succ,
    exists_eq_right, exists_eq_left', and_imp];
  constructor;
  · rintro h x y z rfl Rxz; exact h Rxz;
  · intro h x y Rxy; exact h rfl Rxy;

lemma transitive_def : IsTrans α rel ↔ (Geachean ⟨0, 2, 1, 0⟩ rel) := by
  simp only [Geachean, Rel.iterate.iff_zero, Rel.iterate.iff_succ, exists_eq_right,
    exists_eq_right', and_imp, forall_exists_index]
  constructor;
  · rintro h x y z rfl w Rxw Rwz
    exact h.trans _ _ _ Rxw Rwz
  · intro h
    exact ⟨fun x y z Rxy Ryz => h rfl y Rxy Ryz⟩

lemma euclidean_def : Euclidean rel ↔ (Geachean ⟨1, 1, 0, 1⟩ rel) := by simp [Geachean, Euclidean];

lemma confluent_def : Confluent rel ↔ (Geachean ⟨1, 1, 1, 1⟩ rel) := by simp [Geachean, Confluent];

lemma coreflexive_def : Coreflexive rel ↔ (Geachean ⟨0, 1, 0, 0⟩ rel) := by
  simp only [Coreflexive, Geachean, Rel.iterate.iff_zero, Rel.iterate.iff_succ,
    exists_eq_right, exists_eq_left', and_imp];
  constructor;
  · rintro h x y z rfl Rxz; have := h Rxz; tauto;
  · intro h x y Rxy; have := h rfl Rxy; tauto;

lemma functional_def : Functional rel ↔ (Geachean ⟨1, 1, 0, 0⟩ rel) := by
  simp [Geachean, Functional];
  constructor <;> tauto;

lemma dense_def : RelDense rel ↔ (Geachean ⟨0, 1, 2, 0⟩ rel) := by
  simp only [RelDense, Geachean, Rel.iterate.iff_zero, Rel.iterate.iff_succ,
    exists_eq_right, exists_eq_right', and_imp];
  constructor;
  · rintro h x y z rfl Rxz; exact h Rxz;
  · intro h x y Rxy; exact h rfl Rxy;

@[simp]
lemma satisfies_eq : Geachean (α := α) t (· = ·) := by simp [Geachean];

end Geachean


/-- Imported declaration from the Incompleteness formalization. -/
def MultiGeachean (G : Set Geachean.Taple) (R : Rel α α) := ∀ g ∈ G, Geachean g R
