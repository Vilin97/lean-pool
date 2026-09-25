/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
module

public import LeanPool.LanguageGeneration.FiniteWitness.Simplified.Checkpoints
public import Mathlib.Tactic.Push

/-!
# Canonical candidate searches and target error sequences
-/

@[expose] public section

namespace GenLimit.FiniteWitness.Simplified
variable {α : Type*} [Encodable α] [DecidableEq α]

/-- No word-length cutoff; freshness concerns the entire observed sample. -/
def Candidate (M : Checkpoints α) (F : List α → α) (S : Finset α)
    (p : List α) (k : ℕ) (q : List α) : Prop :=
  p <+: q ∧ p.length < q.length ∧ q.toFinset ⊆ S ∧
    M.points (↑S : Set α) (k + 1) ⊆ q.toFinset ∧ F q ∉ S

/-- Iterate least-code candidate extensions relative to a finite observed sample. -/
noncomputable def sampleRun (M : Checkpoints α) (F : List α → α) (S : Finset α) :
    ℕ → List α
  | 0 => []
  | k + 1 => by
      classical
      exact if h : ∃ q, Candidate M F S (sampleRun M F S k) k q then
        leastCode _ h else sampleRun M F S k

theorem sampleRun_next {M : Checkpoints α} {F : List α → α} {S : Finset α} {k : ℕ}
    (h : ∃ q, Candidate M F S (sampleRun M F S k) k q) :
    Candidate M F S (sampleRun M F S k) k (sampleRun M F S (k + 1)) := by
  classical
  simp only [sampleRun, dite_eq_left h]
  exact leastCode_spec _ h

theorem sampleRun_prefix (M : Checkpoints α) (F : List α → α) (S : Finset α) (k : ℕ) :
    sampleRun M F S k <+: sampleRun M F S (k + 1) := by
  classical
  by_cases h : ∃ q, Candidate M F S (sampleRun M F S k) k q
  · exact (sampleRun_next h).1
  · simp only [sampleRun, dite_eq_right h]
    exact List.prefix_refl _

theorem sampleRun_content (M : Checkpoints α) (F : List α → α) (S : Finset α) (k : ℕ) :
    (sampleRun M F S k).toFinset ⊆ S := by
  classical
  induction k with
  | zero => simp [sampleRun]
  | succ k ih =>
      by_cases h : ∃ q, Candidate M F S (sampleRun M F S k) k q
      · exact (sampleRun_next h).2.2.1
      · simpa only [sampleRun, dite_eq_right h] using ih

omit [Encodable α] in
/-- Appending all observed points supplies a candidate at every round. -/
theorem append_candidate (M : Checkpoints α) {F : List α → α} (hF : Fresh F)
    {S : Finset α} (hS : S.Nonempty) {p : List α} (hp : p.toFinset ⊆ S) (k : ℕ) :
    Candidate M F S p k (p ++ S.toList) := by
  have hcontent : (p ++ S.toList).toFinset = S := by
    simp [Finset.union_eq_right.mpr hp]
  refine ⟨List.prefix_append _ _, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, Finset.length_toList]
    have := Finset.card_pos.mpr hS
    omega
  · rw [hcontent]
  · rw [hcontent]
    exact M.subset _ _
  · simpa only [← List.mem_toFinset, hcontent] using hF (p ++ S.toList)

theorem candidate_exists (M : Checkpoints α) {F : List α → α} (hF : Fresh F)
    {S : Finset α} (hS : S.Nonempty) (k : ℕ) :
    ∃ q, Candidate M F S (sampleRun M F S k) k q :=
  ⟨_, append_candidate M hF hS (sampleRun_content M F S k) k⟩

/-- Evaluate the canonical history after a number of steps equal to the sample size. -/
noncomputable def normalized (M : Checkpoints α) (F : List α → α) (S : Finset α) : α :=
  F (sampleRun M F S S.card)

/-- A strict target-valid extension covering the next checkpoint whose output misses the target.
-/
def BadExtension (M : Checkpoints α) (F : List α → α) (L : Set α)
    (p : List α) (k : ℕ) (q : List α) : Prop :=
  p <+: q ∧ p.length < q.length ∧ (↑q.toFinset : Set α) ⊆ L ∧
    M.points L (k + 1) ⊆ q.toFinset ∧ F q ∉ L

/-- The canonical sequence of least-code target errors using the checkpoint interface. -/
noncomputable def trueRun (M : Checkpoints α) (F : List α → α) (L : Set α) : ℕ → List α
  | 0 => []
  | k + 1 => by
      classical
      exact if h : ∃ q, BadExtension M F L (trueRun M F L k) k q then
        leastCode _ h else trueRun M F L k

theorem trueRun_next {M : Checkpoints α} {F : List α → α} {L : Set α} {k : ℕ}
    (h : ∃ q, BadExtension M F L (trueRun M F L k) k q) :
    BadExtension M F L (trueRun M F L k) k (trueRun M F L (k + 1)) := by
  classical
  simp only [trueRun, dite_eq_left h]
  exact leastCode_spec _ h

theorem trueRun_prefix (M : Checkpoints α) (F : List α → α) (L : Set α) (k : ℕ) :
    trueRun M F L k <+: trueRun M F L (k + 1) := by
  classical
  by_cases h : ∃ q, BadExtension M F L (trueRun M F L k) k q
  · exact (trueRun_next h).1
  · simp only [trueRun, dite_eq_right h]
    exact List.prefix_refl _

theorem trueRun_legal (M : Checkpoints α) (F : List α → α) (L : Set α) (k : ℕ) :
    (↑(trueRun M F L k).toFinset : Set α) ⊆ L := by
  classical
  induction k with
  | zero => simp [trueRun]
  | succ k ih =>
      by_cases h : ∃ q, BadExtension M F L (trueRun M F L k) k q
      · exact (trueRun_next h).2.2.1
      · simpa only [trueRun, dite_eq_right h] using ih

theorem trueRun_stops (M : Checkpoints α) {F : List α → α} {L : Set α}
    (hvalid : EventuallyValid F L) :
    ∃ m, ¬∃ q, BadExtension M F L (trueRun M F L m) m q := by
  classical
  by_contra h
  push Not at h
  have hs := fun k => trueRun_next (h k)
  have hlen : ∀ n, n ≤ (trueRun M F L n).length := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => have := (hs n).2.1; omega
  apply no_exhaustive_bad_chain hvalid (trueRun M F L) (trueRun_prefix M F L) hlen
  · intro n x hx
    exact trueRun_legal M F L n (List.mem_toFinset.mpr hx)
  · intro x hx
    obtain ⟨k, hk⟩ := M.exhaust L x hx
    exact ⟨k + 1, List.mem_toFinset.mp ((hs k).2.2.2.1 hk)⟩
  · intro n
    exact (hs n).2.2.2.2

end GenLimit.FiniteWitness.Simplified
