/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
module

public import LeanPool.LanguageGeneration.FiniteWitness.Width.FiniteQueries
public import Mathlib.Data.Finset.Max

/-!
# Finite-search implementation of the bounded normalization
-/

public section

namespace GenLimit.FiniteWitness

variable {α : Type*} [DecidableEq α] [Encodable α]

/-- The decidable candidate test with bounded history length and observed checkpoints. -/
@[expose]
def finiteCandidate (F : List α → α) (S : Finset α) (n : ℕ)
    (p : List α) (k : ℕ) (q : List α) : Prop :=
  p <+: q ∧ p.length < q.length ∧ q.toFinset ⊆ S ∧ q.length ≤ 2 * n ∧
    S.filter (fun x => Encodable.encode x < k + 1) ⊆ q.toFinset ∧ F q ∉ S

instance (F : List α → α) (S : Finset α) (n : ℕ) (p : List α) (k : ℕ) (q : List α) :
    Decidable (finiteCandidate F S n p k q) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

theorem finiteCandidate_iff (F : List α → α) (S : Finset α) (n : ℕ)
    (p : List α) (k : ℕ) (q : List α) :
    finiteCandidate F S n p k q ↔ Candidate F S n p k q := by
  have he : S.filter (fun x => Encodable.encode x < k + 1) = checkpoint (↑S : Set α) (k + 1) := by
    ext x
    simp [and_comm]
  simp only [finiteCandidate, Candidate, he]

/-- The finite set of candidate histories within the fixed length bound. -/
def candidateWords (F : List α → α) (S : Finset α) (n : ℕ) (p : List α) (k : ℕ) :
    Finset (List α) := (boundedWords S (2 * n)).filter (finiteCandidate F S n p k)

theorem mem_candidateWords (F : List α → α) (S : Finset α) (n : ℕ)
    (p : List α) (k : ℕ) (q : List α) :
    q ∈ candidateWords F S n p k ↔ Candidate F S n p k q := by
  rw [candidateWords, Finset.mem_filter, finiteCandidate_iff]
  exact ⟨And.right, fun h => ⟨mem_boundedWords.mpr ⟨h.2.2.1, h.2.2.2.1⟩, h⟩⟩

/-- Decode the smallest code in a finite candidate set. This definition is executable. -/
def pickWord (C : Finset (List α)) : List α :=
  if h : C.Nonempty then
    (Encodable.decode (α := List α) ((C.image Encodable.encode).min' (h.image _))).getD []
  else []

omit [DecidableEq α] in
theorem pickWord_spec {C : Finset (List α)} (hC : C.Nonempty) :
    pickWord C ∈ C ∧ ∀ q ∈ C, Encodable.encode (pickWord C) ≤ Encodable.encode q := by
  obtain ⟨q, hq, he⟩ := Finset.mem_image.mp
    (Finset.min'_mem (C.image Encodable.encode) (hC.image _))
  have heq : pickWord C = q := by
    simp only [pickWord, dite_eq_left hC, ← he]
    simp
  refine ⟨heq.symm ▸ hq, ?_⟩
  intro r hr
  rw [heq, he]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem Encodable.encode hr)

omit [DecidableEq α] in
theorem pickWord_eq_leastCode {C : Finset (List α)} {P : List α → Prop}
    (hP : ∃ q, P q) (hC : ∀ q, q ∈ C ↔ P q) : pickWord C = leastCode P hP := by
  have hc : C.Nonempty := by obtain ⟨q, hq⟩ := hP; exact ⟨q, (hC q).mpr hq⟩
  apply Encodable.encode_injective
  exact le_antisymm ((pickWord_spec hc).2 _ ((hC _).mpr (leastCode_spec P hP)))
    (leastCode_le P hP ((hC _).mp (pickWord_spec hc).1))

/-- Iterate bounded finite candidate searches, retaining the history when no candidate exists. -/
def executableRun (F : List α → α) (S : Finset α) (n : ℕ) : ℕ → List α
  | 0 => []
  | k + 1 =>
    let p := executableRun F S n k
    let C := candidateWords F S n p k
    if C.Nonempty then pickWord C else p

theorem executableRun_eq (F : List α → α) (S : Finset α) (n k : ℕ) :
    executableRun F S n k = sampleRun F S n k := by
  classical
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [executableRun, ih]
    by_cases h : ∃ q, Candidate F S n (sampleRun F S n k) k q
    · have hc : (candidateWords F S n (sampleRun F S n k) k).Nonempty := by
        obtain ⟨q, hq⟩ := h
        exact ⟨q, (mem_candidateWords _ _ _ _ _ _).mpr hq⟩
      rw [ite_eq_left hc, sampleRun, dite_eq_left h]
      exact pickWord_eq_leastCode h (mem_candidateWords _ _ _ _ _)
    · have hc : ¬ (candidateWords F S n (sampleRun F S n k) k).Nonempty := by
        rintro ⟨q, hq⟩
        exact h ⟨q, (mem_candidateWords _ _ _ _ _ _).mp hq⟩
      rw [ite_eq_right hc, sampleRun, dite_eq_right h]

/-- Evaluate the finite-search history at the sample-size bound. -/
def executableNormalized (F : List α → α) (S : Finset α) : α :=
  F (executableRun F S S.card S.card)

theorem executableNormalized_eq (F : List α → α) (S : Finset α) :
    executableNormalized F S = normalized F S := by
  simp [executableNormalized, executableRun_eq, normalized]

theorem executableNormalized_locks (F : List α → α) (hF : Fresh F) {L : Set α}
    (hL : L.Infinite) (hvalid : EventuallyValid F L) : Locks (executableNormalized F) L := by
  have he : executableNormalized F = normalized F := funext (executableNormalized_eq F)
  rw [he]
  exact normalized_locks F hF hL hvalid

/-- A computable fresh repair on the concrete natural-number universe. -/
def maxRepair (G : Generic.Generator ℕ) (xs : List ℕ) : ℕ :=
  if listOutput G xs ∈ xs then xs.toFinset.sup id + 1 else listOutput G xs

theorem maxRepair_fresh (G : Generic.Generator ℕ) : Fresh (maxRepair G) := by
  intro xs
  by_cases h : listOutput G xs ∈ xs
  · rw [maxRepair, ite_eq_left h]
    intro hm
    have hh : xs.toFinset.sup id + 1 ≤ xs.toFinset.sup id :=
      Finset.le_sup (f := id) (List.mem_toFinset.mpr hm)
    omega
  · simp [maxRepair, h]

theorem maxRepair_eventuallyValid {G : Generic.Generator ℕ} {L : Set ℕ}
    (hG : ∀ stream : Generic.Stream ℕ, Generic.Presents stream L →
      ∃ N, ∀ n ≥ N, Generic.CorrectAt G L stream n) : EventuallyValid (maxRepair G) L := by
  intro stream hp
  obtain ⟨N, hN⟩ := hG stream hp
  refine ⟨N, ?_⟩
  intro n hn
  have hg := hN n hn
  have hf : listOutput G (GenLimit.textPrefix stream n) ∉ GenLimit.textPrefix stream n := by
    simpa [← List.mem_toFinset, Generic.CorrectAt] using hg.2
  rw [maxRepair, ite_eq_right hf]
  simpa only [listOutput_prefix] using hg.1

/-- An executable, target-independent normalization, with the whole input set as its argument. -/
def executableNormalization (G : Generic.Generator ℕ) (S : Finset ℕ) : ℕ :=
  executableNormalized (maxRepair G) S

theorem executableNormalization_finite_queries {G G' : Generic.Generator ℕ} (S : Finset ℕ)
    (h : ∀ q ∈ boundedWords S (2 * S.card), listOutput G q = listOutput G' q) :
    executableNormalization G S = executableNormalization G' S := by
  unfold executableNormalization
  simp only [executableNormalized_eq]
  apply normalized_finite_query_bound S
  intro q hq
  simp only [maxRepair, h q hq]

theorem executable_universal_normalization (G : Generic.Generator ℕ) :
    ∀ L : Set ℕ, L.Infinite →
      (∀ stream : Generic.Stream ℕ, Generic.Presents stream L →
        ∃ N, ∀ n ≥ N, Generic.CorrectAt G L stream n) →
      Locks (executableNormalization G) L := by
  intro L hL hG
  exact executableNormalized_locks (maxRepair G) (maxRepair_fresh G) hL
    (maxRepair_eventuallyValid hG)

end GenLimit.FiniteWitness
