/-
Copyright (c) 2026 Vikraman Choudhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vikraman Choudhury
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Order.WellFounded

/-!
# Minimal elements of finite posets

Auxiliary lemmas used by the rollback development: every nonempty finite subset
of a partial order with well-founded strict order (or, constructively, of any
partial order) has a minimal element.
-/

namespace EventStructures

/-- Classical: A non-empty finite subset of a well-founded partial order has a minimal element. -/
lemma Finset.exists_minimal_of_nonempty {α : Type*} [PartialOrder α] [WellFoundedLT α]
    (T : Finset α) (hne : T.Nonempty) :
    ∃ x ∈ T, ∀ y ∈ T, y < x → False := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  suffices ∀ x, x ∈ T → ∃ m ∈ T, (∀ y ∈ T, y < m → False) ∧ m ≤ x by
    obtain ⟨m, hmT, hmmin, _⟩ := this x₀ hx₀
    exact ⟨m, hmT, hmmin⟩
  intro x
  apply (IsWellFounded.wf (r := (· < ·))).induction x
  intro z ih hz
  by_cases hmin : ∀ y ∈ T, y < z → False
  · exact ⟨z, hz, hmin, le_rfl⟩
  · push Not at hmin
    obtain ⟨y, hyT, hy_lt, _⟩ := hmin
    obtain ⟨m, hmT, hmmin, hm_le⟩ := ih y hy_lt hyT
    exact ⟨m, hmT, hmmin, le_trans hm_le (le_of_lt hy_lt)⟩

/-- Constructive: every nonempty finite subset of a
    decidable strict order has a minimal element (no well-foundedness needed). -/
lemma Finset.exists_minimal_dec {α : Type*} [PartialOrder α]
    (T : Finset α) (hne : T.Nonempty) :
    ∃ x ∈ T, ∀ y ∈ T, ¬ y < x := by
  classical
  induction T using Finset.induction_on with
  | empty => exact absurd rfl hne.ne_empty
  | @insert a S haS ih =>
    by_cases hS : S.Nonempty
    · obtain ⟨m, hmS, hmmin⟩ := ih hS
      by_cases hlt : a < m
      · refine ⟨a, Finset.mem_insert_self a S, ?_⟩
        intro y hyT hya
        rcases Finset.mem_insert.mp hyT with rfl | hyS
        · exact lt_irrefl _ hya
        · exact hmmin y hyS (lt_trans hya hlt)
      · refine ⟨m, Finset.mem_insert_of_mem hmS, ?_⟩
        intro y hyT hym
        rcases Finset.mem_insert.mp hyT with rfl | hyS
        · exact hlt hym
        · exact hmmin y hyS hym
    · have hSe : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst hSe
      refine ⟨a, Finset.mem_insert_self a ∅, ?_⟩
      intro y hyT hya
      rcases Finset.mem_insert.mp hyT with rfl | hy
      · exact lt_irrefl _ hya
      · exact (Finset.notMem_empty y) hy

end EventStructures
