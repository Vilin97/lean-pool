/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
module

public import LeanPool.LanguageGeneration.FiniteWitness.Simplified.Normalization
public import LeanPool.LanguageGeneration.FiniteWitness.Width.Executable

/-!
# Finite-search implementation of the revised normalization
-/

public section

namespace GenLimit.FiniteWitness.Simplified

/-- Executable first-k selection from the observed finite set. -/
def samplePoints (S : Finset ℕ) (k : ℕ) : Finset ℕ :=
  S.filter (fun x => (S.filter (fun y => y < x)).card < k)

theorem samplePoints_eq (S : Finset ℕ) (k : ℕ) :
    samplePoints S k = firstPoints (↑S : Set ℕ) k := by
  classical
  ext x
  have he : S.filter (fun y => y < x) =
      (Finset.range x).filter (fun y => y ∈ S) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_range]
    exact and_comm
  simp only [samplePoints, Finset.mem_filter, mem_firstPoints, Finset.mem_coe,
    Nat.count_eq_card_filter_range, he]

/-- Decode a finite initial segment of the fixed word codes. -/
def codeWords (b : ℕ) : Finset (List ℕ) :=
  (Finset.range (b + 1)).image (fun i => (Encodable.decode (α := List ℕ) i).getD [])

theorem mem_codeWords {q : List ℕ} {b : ℕ} (h : Encodable.encode q ≤ b) :
    q ∈ codeWords b := by
  refine Finset.mem_image.mpr ⟨Encodable.encode q, Finset.mem_range.mpr (by omega), ?_⟩
  simp

/-- Test a strict history extension that covers the next checkpoint and outputs outside the
sample. -/
@[expose]
def testCandidate (F : List ℕ → ℕ) (S : Finset ℕ) (p : List ℕ) (k : ℕ)
    (q : List ℕ) : Prop :=
  p <+: q ∧ p.length < q.length ∧ q.toFinset ⊆ S ∧
    samplePoints S (k + 1) ⊆ q.toFinset ∧ F q ∉ S

instance (F : List ℕ → ℕ) (S : Finset ℕ) (p : List ℕ) (k : ℕ) (q : List ℕ) :
    Decidable (testCandidate F S p k q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

theorem testCandidate_iff (F : List ℕ → ℕ) (S : Finset ℕ) (p : List ℕ) (k : ℕ)
    (q : List ℕ) :
    testCandidate F S p k q ↔ Candidate naturalCheckpoints F S p k q := by
  simp only [testCandidate, Candidate, samplePoints_eq, naturalCheckpoints_points]

/-- Search the bounded code interval for candidates extending the current history. -/
def candidateCodes (F : List ℕ → ℕ) (S : Finset ℕ) (p : List ℕ) (k : ℕ) :
    Finset (List ℕ) :=
  (codeWords (Encodable.encode (p ++ S.sort (· ≤ ·)))).filter (testCandidate F S p k)

theorem pick_candidate_eq {F : List ℕ → ℕ} (hF : Fresh F) {S : Finset ℕ}
    (hS : S.Nonempty) {p : List ℕ} (hp : p.toFinset ⊆ S) (k : ℕ)
    (hex : ∃ q, Candidate naturalCheckpoints F S p k q) :
    pickWord (candidateCodes F S p k) = leastCode _ hex := by
  classical
  have hcontent : (p ++ S.sort (· ≤ ·)).toFinset = S := by
    simp [Finset.union_eq_right.mpr hp]
  have happ : Candidate naturalCheckpoints F S p k (p ++ S.sort (· ≤ ·)) := by
    refine ⟨List.prefix_append _ _, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, Finset.length_sort]
      have := Finset.card_pos.mpr hS
      omega
    · rw [hcontent]
    · rw [hcontent]
      exact naturalCheckpoints.subset _ _
    · simpa only [← List.mem_toFinset, hcontent] using hF (p ++ S.sort (· ≤ ·))
  have hmem : p ++ S.sort (· ≤ ·) ∈ candidateCodes F S p k :=
    Finset.mem_filter.mpr ⟨mem_codeWords le_rfl, (testCandidate_iff _ _ _ _ _).mpr happ⟩
  have hC : (candidateCodes F S p k).Nonempty := ⟨_, hmem⟩
  have hmin := leastCode_spec _ hex
  have hmin_bound := leastCode_le _ hex happ
  have hmin_mem : leastCode _ hex ∈ candidateCodes F S p k :=
    Finset.mem_filter.mpr ⟨mem_codeWords hmin_bound, (testCandidate_iff _ _ _ _ _).mpr hmin⟩
  apply Encodable.encode_injective
  exact le_antisymm ((pickWord_spec hC).2 _ hmin_mem)
    (leastCode_le _ hex ((testCandidate_iff _ _ _ _ _).mp
      (Finset.mem_filter.mp (pickWord_spec hC).1).2))

/-- Iterate finite candidate selection for the revised normalization. -/
def executableRun (F : List ℕ → ℕ) (S : Finset ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => pickWord (candidateCodes F S (executableRun F S k) k)

theorem executableRun_eq {F : List ℕ → ℕ} (hF : Fresh F) {S : Finset ℕ}
    (hS : S.Nonempty) (k : ℕ) : executableRun F S k = sampleRun naturalCheckpoints F S k := by
  classical
  induction k with
  | zero => rfl
  | succ k ih =>
      have hex := candidate_exists naturalCheckpoints hF hS k
      rw [executableRun, ih, sampleRun, dite_eq_left hex]
      exact pick_candidate_eq hF hS (sampleRun_content naturalCheckpoints F S k) k hex

/-- Evaluate the history function after as many search steps as sample elements. -/
def executableNormalized (F : List ℕ → ℕ) (S : Finset ℕ) : ℕ :=
  F (executableRun F S S.card)

theorem executableNormalized_eq {F : List ℕ → ℕ} (hF : Fresh F) (S : Finset ℕ) :
    executableNormalized F S = normalized naturalCheckpoints F S := by
  by_cases hS : S.Nonempty
  · simp only [executableNormalized, executableRun_eq hF hS, normalized]
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    rfl

/-- Apply the revised finite-search normalization after repairing repeated outputs. -/
def executableNormalization (G : Generic.Generator ℕ) (S : Finset ℕ) : ℕ :=
  executableNormalized (maxRepair G) S

/-- A terminating executable program for the new construction, not the old bounded one. -/
theorem executable_universal_normalization (G : Generic.Generator ℕ) :
    ∀ L : Set ℕ, L.Infinite →
      (∀ stream : Generic.Stream ℕ, Generic.Presents stream L →
        ∃ N, ∀ n ≥ N, Generic.CorrectAt G L stream n) →
      Locks (executableNormalization G) L := by
  intro L hL hG
  have he : executableNormalization G = normalized naturalCheckpoints (maxRepair G) :=
    funext (executableNormalized_eq (maxRepair_fresh G))
  rw [he]
  exact normalized_locks naturalCheckpoints (maxRepair G) (maxRepair_fresh G) hL
    (maxRepair_eventuallyValid hG)

end GenLimit.FiniteWitness.Simplified
