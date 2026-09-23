/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
module

public import LeanPool.LanguageGeneration.FiniteWitness.Histories
public import Mathlib.Logic.Equiv.List
public import Mathlib.Data.Finset.Preimage
public import Mathlib.Order.WellFounded
public import Mathlib.Tactic.Push

/-!
# Universal normalization by finite priorities

The checkpoints here are target elements whose ambient codes are below the
stage number. They replace the paper's first-k-target-element checkpoints;
both exhaust each target and agree between a sufficiently confirmed sample
and that target. The sample search retains the `2 * S.card` length cutoff.
-/

@[expose] public section

namespace GenLimit.FiniteWitness

variable {α : Type*}

/-- The finite set of elements whose encoding is strictly below the given bound. -/
noncomputable def belowCodes (β : Type*) [Encodable β] (n : ℕ) : Finset β :=
  (Finset.range n).preimage Encodable.encode Encodable.encode_injective.injOn

@[simp] theorem mem_belowCodes {β : Type*} [Encodable β] {n : ℕ} {x : β} :
    x ∈ belowCodes β n ↔ Encodable.encode x < n := by
  simp [belowCodes]

/-- Select the element of least encoding satisfying an inhabited predicate. -/
noncomputable def leastCode {β : Type*} [Encodable β]
    (P : β → Prop) (h : ∃ x, P x) : β :=
  (measure Encodable.encode).wf.min {x | P x} h

theorem leastCode_spec {β : Type*} [Encodable β]
    (P : β → Prop) (h : ∃ x, P x) : P (leastCode P h) :=
  (measure Encodable.encode).wf.min_mem {x | P x} h

theorem leastCode_le {β : Type*} [Encodable β]
    (P : β → Prop) (h : ∃ x, P x) {x : β} (hx : P x) :
    Encodable.encode (leastCode P h) ≤ Encodable.encode x := by
  apply Nat.le_of_not_lt
  exact (measure Encodable.encode).wf.not_lt_min {x | P x} hx

section Encoded

variable [Encodable α] [DecidableEq α]

/-- The elements of a target language whose codes are below the checkpoint bound. -/
noncomputable def checkpoint (L : Set α) (k : ℕ) : Finset α := by
  classical
  exact (belowCodes α k).filter (fun x => x ∈ L)

omit [DecidableEq α] in
@[simp] theorem mem_checkpoint {L : Set α} {k : ℕ} {x : α} :
    x ∈ checkpoint L k ↔ Encodable.encode x < k ∧ x ∈ L := by
  classical
  simp [checkpoint]

omit [DecidableEq α] in
theorem checkpoint_subset (L : Set α) (k : ℕ) :
    (↑(checkpoint L k) : Set α) ⊆ L := fun _ hx => (mem_checkpoint.mp hx).2

omit [DecidableEq α] in
theorem checkpoint_mono {L : Set α} {j k : ℕ} (hjk : j ≤ k) :
    checkpoint L j ⊆ checkpoint L k := by
  intro x hx
  exact mem_checkpoint.mpr ⟨(mem_checkpoint.mp hx).1.trans_le hjk,
    (mem_checkpoint.mp hx).2⟩

omit [DecidableEq α] in
theorem checkpoint_agrees {L : Set α} {S : Finset α} {j k : ℕ}
    (hSL : (↑S : Set α) ⊆ L) (hseen : checkpoint L k ⊆ S) (hjk : j ≤ k) :
    checkpoint (↑S : Set α) j = checkpoint L j := by
  ext x
  simp only [mem_checkpoint, Finset.mem_coe]
  constructor
  · rintro ⟨hx, hS⟩
    exact ⟨hx, hSL hS⟩
  · rintro ⟨hx, hL⟩
    exact ⟨hx, hseen (mem_checkpoint.mpr ⟨hx.trans_le hjk, hL⟩)⟩

omit [Encodable α] in
theorem content_mono {p q : List α} (hpq : p <+: q) : p.toFinset ⊆ q.toFinset := by
  obtain ⟨tail, rfl⟩ := hpq
  simp

/-- The target-dependent genuine errors used only in the proof. -/
def BadExtension (F : List α → α) (L : Set α) (p : List α) (k : ℕ)
    (q : List α) : Prop :=
  p <+: q ∧ p.length < q.length ∧ (↑q.toFinset : Set α) ⊆ L ∧
    checkpoint L (k + 1) ⊆ q.toFinset ∧ F q ∉ L

/-- The canonical sequence of least-code bad extensions for a fixed target language. -/
noncomputable def trueRun (F : List α → α) (L : Set α) : ℕ → List α
  | 0 => []
  | k + 1 => by
      classical
      exact if h : ∃ q, BadExtension F L (trueRun F L k) k q then
        leastCode _ h else trueRun F L k

theorem trueRun_next {F : List α → α} {L : Set α} {k : ℕ}
    (h : ∃ q, BadExtension F L (trueRun F L k) k q) :
    BadExtension F L (trueRun F L k) k (trueRun F L (k + 1)) := by
  classical
  simp only [trueRun, dite_eq_left h]
  exact leastCode_spec _ h

theorem trueRun_prefix (F : List α → α) (L : Set α) (k : ℕ) :
    trueRun F L k <+: trueRun F L (k + 1) := by
  classical
  by_cases h : ∃ q, BadExtension F L (trueRun F L k) k q
  · exact (trueRun_next h).1
  · simp only [trueRun, dite_eq_right h]
    exact List.prefix_refl _

theorem trueRun_legal (F : List α → α) (L : Set α) (k : ℕ) :
    (↑(trueRun F L k).toFinset : Set α) ⊆ L := by
  classical
  induction k with
  | zero => simp [trueRun]
  | succ k ih =>
      by_cases h : ∃ q, BadExtension F L (trueRun F L k) k q
      · exact (trueRun_next h).2.2.1
      · simpa only [trueRun, dite_eq_right h] using ih

/-- Exhaustiveness rules out a genuine error at every stage. -/
theorem trueRun_stops {F : List α → α} {L : Set α}
    (hvalid : EventuallyValid F L) :
    ∃ m, ¬∃ q, BadExtension F L (trueRun F L m) m q := by
  classical
  by_contra h
  push Not at h
  have hs : ∀ k, BadExtension F L (trueRun F L k) k (trueRun F L (k + 1)) :=
    fun k => trueRun_next (h k)
  have hlen : ∀ n, n ≤ (trueRun F L n).length := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => have := (hs n).2.1; omega
  apply no_exhaustive_bad_chain hvalid (trueRun F L) (trueRun_prefix F L) hlen
  · intro n x hx
    exact trueRun_legal F L n (List.mem_toFinset.mpr hx)
  · intro x hx
    refine ⟨Encodable.encode x + 1, ?_⟩
    apply List.mem_toFinset.mp
    exact (hs (Encodable.encode x)).2.2.2.1
      (mem_checkpoint.mpr ⟨Nat.lt_succ_self _, hx⟩)
  · intro n
    exact (hs n).2.2.2.2

end Encoded

end GenLimit.FiniteWitness
