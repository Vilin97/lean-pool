/-
Copyright (c) 2026 Weighted Horn Cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weighted Horn Cores contributors
-/
module

public import LeanPool.WeightedHornCores.CoreBound

/-!
# Unary chains

With no branching clauses, the size of a smallest core can grow linearly in the total
unit weight. Each cut of a chain falsifies just the clause crossing the cut.
-/

@[expose] public section

namespace WeightedHornCores

/-- The positive unit at the start of a chain. -/
def fact : Clause ℕ := ⟨∅, some 0⟩

/-- A single directed implication between consecutive atoms. -/
def step (i : ℕ) : Clause ℕ := ⟨{i}, some (i + 1)⟩

/-- The negative unit at the end of a chain. -/
def denial (n : ℕ) : Clause ℕ := ⟨{n}, none⟩

/-- A fact at zero, `n` successive implications, and a denial at `n`. -/
def unaryChain (n : ℕ) : Finset (Clause ℕ) :=
  insert fact (insert (denial n) ((Finset.range n).image step))

private theorem mem_chain {n : ℕ} {c : Clause ℕ} :
    c ∈ unaryChain n ↔ c = fact ∨ c = denial n ∨ ∃ i < n, step i = c := by
  simp [unaryChain]

/-- The chain has one more clause at each end than its number of implications. -/
theorem card_unaryChain (n : ℕ) : (unaryChain n).card = n + 2 := by
  have hi : Function.Injective step := fun _ _ h => by
    simpa [step] using congrArg Clause.head h
  have hd : denial n ∉ (Finset.range n).image step := by
    simp [Finset.mem_image, step, denial]
  have hf : fact ∉ insert (denial n) ((Finset.range n).image step) := by
    simp [Finset.mem_image, fact, step, denial]
  rw [unaryChain, Finset.card_insert_of_notMem hf, Finset.card_insert_of_notMem hd,
    Finset.card_image_of_injective _ hi, Finset.card_range]

private theorem holds_fact (s : Set ℕ) : fact.Holds s ↔ 0 ∈ s := by
  simp [fact, Clause.Holds]

private theorem holds_step (i : ℕ) (s : Set ℕ) : (step i).Holds s ↔ (i ∈ s → i + 1 ∈ s) := by
  simp [step, Clause.Holds]

private theorem holds_denial (n : ℕ) (s : Set ℕ) : (denial n).Holds s ↔ n ∉ s := by
  simp [denial, Clause.Holds]

/-- Forward propagation reaches the forbidden final atom. -/
theorem unaryChain_unsatisfiable (n : ℕ) : ¬ ∃ s, Models (unaryChain n) s := by
  rintro ⟨s, hs⟩
  have reach (i : ℕ) (hi : i ≤ n) : i ∈ s := by
    induction i with
    | zero => exact (holds_fact s).mp (hs _ (mem_chain.mpr (Or.inl rfl)))
    | succ i ih =>
      have h := hs _ (mem_chain.mpr (Or.inr (Or.inr ⟨i, by omega, rfl⟩)))
      exact (holds_step i s).mp h (ih (by omega))
  exact (holds_denial n s).mp (hs _ (mem_chain.mpr (Or.inr (Or.inl rfl)))) (reach n le_rfl)

/-- Removing any one clause opens a cut, yielding a model of all remaining clauses. -/
theorem unaryChain_erase_models {n : ℕ} {c : Clause ℕ} (hc : c ∈ unaryChain n) :
    ∃ s, Models ((unaryChain n).erase c) s := by
  rcases mem_chain.mp hc with rfl | rfl | ⟨i, hi, rfl⟩
  · refine ⟨∅, fun d hd => ?_⟩
    obtain ⟨hne, hd⟩ := Finset.mem_erase.mp hd
    rcases mem_chain.mp hd with h | rfl | ⟨j, _, rfl⟩
    · exact (hne h).elim
    · simp [holds_denial]
    · simp [holds_step]
  · refine ⟨Set.univ, fun d hd => ?_⟩
    obtain ⟨hne, hd⟩ := Finset.mem_erase.mp hd
    rcases mem_chain.mp hd with rfl | h | ⟨j, _, rfl⟩
    · simp [holds_fact]
    · exact (hne h).elim
    · simp [holds_step]
  · refine ⟨{x | x ≤ i}, fun d hd => ?_⟩
    obtain ⟨hne, hd⟩ := Finset.mem_erase.mp hd
    rcases mem_chain.mp hd with rfl | rfl | ⟨j, _, rfl⟩
    · simp [holds_fact]
    · exact (holds_denial _ _).mpr (Nat.not_le_of_lt hi)
    · have hij : j ≠ i := fun h => hne (congrArg step h)
      apply (holds_step _ _).mpr
      change j ≤ i → j + 1 ≤ i
      omega

/-- No proper subformula of a unary chain is unsatisfiable. -/
theorem eq_unaryChain_of_unsatisfiable {n : ℕ} {K : Finset (Clause ℕ)}
    (hK : K ⊆ unaryChain n) (hu : ¬ ∃ s, Models K s) : K = unaryChain n := by
  apply Finset.Subset.antisymm hK
  intro c hc
  by_contra h
  obtain ⟨s, hs⟩ := unaryChain_erase_models hc
  exact hu ⟨s, hs.mono fun d hd => Finset.mem_erase.mpr
    ⟨fun he => h (he ▸ hd), hK hd⟩⟩

/-- All rules are unary or nullary, irrespective of weights. -/
theorem branchingWeight_unaryChain (n : ℕ) (w : Clause ℕ → ℝ) :
    branchingWeight (unaryChain n) w = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro c hc
  rcases mem_chain.mp hc with rfl | rfl | ⟨i, _, rfl⟩ <;>
    simp [Clause.Branches, fact, denial, step]

/-- The least weight falsified by an assignment is exactly one under unit weights. -/
theorem unaryChain_isLeast_violationWeight (n : ℕ) :
    IsLeast (Set.range (violationWeight (unaryChain n) (fun _ => 1))) 1 := by
  classical
  constructor
  · refine ⟨∅, ?_⟩
    unfold violationWeight
    rw [Finset.sum_eq_single fact]
    · simp [holds_fact]
    · intro c hc hne
      rcases mem_chain.mp hc with h | rfl | ⟨i, _, rfl⟩
      · exact (hne h).elim
      · simp [holds_denial]
      · simp [holds_step]
    · intro h
      exact (h (mem_chain.mpr (Or.inl rfl))).elim
  · rintro _ ⟨s, rfl⟩
    have hn : ¬ Models (unaryChain n) s := fun h => unaryChain_unsatisfiable n ⟨s, h⟩
    unfold Models at hn
    push Not at hn
    obtain ⟨c, hc, h⟩ := hn
    unfold violationWeight
    have bound := Finset.single_le_sum (s := unaryChain n)
      (f := fun d => if ¬ d.Holds s then (1 : ℝ) else 0) (fun d _ => by split <;> norm_num) hc
    simpa [h] using bound

end WeightedHornCores
