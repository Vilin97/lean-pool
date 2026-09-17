/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
import LeanPool.LanguageGeneration.FiniteWitness.SampleSearch

/-! # Finite positive confirmation of the canonical error priorities -/

namespace GenLimit.FiniteWitness

variable {α : Type*} [Encodable α] [DecidableEq α]

omit [Encodable α] [DecidableEq α] in
theorem extend_inside_infinite {L : Set α} {B : Finset α}
    (hL : L.Infinite) (hBL : (↑B : Set α) ⊆ L) (n : ℕ) :
    ∃ T : Finset α, (↑T : Set α) ⊆ L ∧ B ⊆ T ∧ n ≤ T.card := by
  classical
  obtain ⟨P, hPL, hcard⟩ := hL.exists_subset_card_eq n
  refine ⟨B ∪ P, ?_, Finset.subset_union_left, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hBL hx
    · exact hPL hx
  · rw [← hcard]
    exact Finset.card_le_card Finset.subset_union_right

/-- Finitely many earlier codes and their target-valid outputs can be confirmed. -/
theorem exists_confirming_witness (F : List α → α) {L : Set α}
    (hL : L.Infinite) (m : ℕ) :
    ∃ T : Finset α,
      (↑T : Set α) ⊆ L ∧
      checkpoint L (m + 1) ⊆ T ∧
      (trueRun F L m).toFinset ⊆ T ∧
      (trueRun F L m).length + m + 1 ≤ T.card ∧
      ∀ k < m, ∀ q : List α,
        Encodable.encode q < Encodable.encode (trueRun F L (k + 1)) →
        F q ∈ L → F q ∈ T := by
  classical
  let b := (Finset.range (m + 1)).sup (fun j => Encodable.encode (trueRun F L j))
  let confirmations := ((belowCodes (List α) (b + 1)).image F).filter (fun x => x ∈ L)
  let B := (checkpoint L (m + 1) ∪ (trueRun F L m).toFinset) ∪ confirmations
  have hBL : (↑B : Set α) ⊆ L := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · exact checkpoint_subset L (m + 1) hx
      · exact trueRun_legal F L m hx
    · exact (Finset.mem_filter.mp hx).2
  obtain ⟨T, hTL, hBT, hsize⟩ :=
    extend_inside_infinite hL hBL ((trueRun F L m).length + m + 1)
  refine ⟨T, hTL, ?_, ?_, hsize, ?_⟩
  · intro x hx
    apply hBT
    simp [B, hx]
  · intro x hx
    apply hBT
    simp [B, hx]
  · intro k hk q hq hqL
    have hb : Encodable.encode (trueRun F L (k + 1)) ≤ b :=
      Finset.le_sup (f := fun j => Encodable.encode (trueRun F L j))
        (Finset.mem_range.mpr (by omega))
    have hqB : q ∈ belowCodes (List α) (b + 1) :=
      mem_belowCodes.mpr (by omega)
    have hconf : F q ∈ confirmations :=
      Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨q, hqB, rfl⟩, hqL⟩
    exact hBT (Finset.mem_union_right _ hconf)

/-- Every sample above the confirming witness reproduces the genuine errors. -/
theorem sampleRun_matches_true {F : List α → α} {L : Set α}
    {S : Finset α} {n m : ℕ}
    (hSL : (↑S : Set α) ⊆ L)
    (hseen : checkpoint L (m + 1) ⊆ S)
    (hcontents : (trueRun F L m).toFinset ⊆ S)
    (hlength : (trueRun F L m).length ≤ n)
    (hbefore : ∀ k < m, ∃ q, BadExtension F L (trueRun F L k) k q)
    (hconfirm : ∀ k < m, ∀ q : List α,
      Encodable.encode q < Encodable.encode (trueRun F L (k + 1)) →
      F q ∈ L → F q ∈ S) :
    ∀ k ≤ m, sampleRun F S n k = trueRun F L k := by
  classical
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hkm
      have hk : k < m := by omega
      have heq := ih (by omega)
      have hbad := trueRun_next (hbefore k hk)
      have hp := history_prefix_mono (trueRun_prefix F L) hkm
      have hcp := checkpoint_agrees hSL hseen (j := k + 1) (by omega)
      have hcand : Candidate F S n (sampleRun F S n k) k (trueRun F L (k + 1)) := by
        rw [heq]
        refine ⟨hbad.1, hbad.2.1, (content_mono hp).trans hcontents, ?_, ?_, ?_⟩
        · have := hp.length_le; omega
        · rw [hcp]
          exact hbad.2.2.2.1
        · exact fun hx => hbad.2.2.2.2 (hSL hx)
      have hex : ∃ q, Candidate F S n (sampleRun F S n k) k q := ⟨_, hcand⟩
      have hselected := sampleRun_next hex
      have hupper : Encodable.encode (sampleRun F S n (k + 1)) ≤
          Encodable.encode (trueRun F L (k + 1)) := by
        simp only [sampleRun, dite_eq_left hex]
        exact leastCode_le _ hex hcand
      have hnotlower : ¬ Encodable.encode (sampleRun F S n (k + 1)) <
          Encodable.encode (trueRun F L (k + 1)) := by
        intro hlow
        have hnotL : F (sampleRun F S n (k + 1)) ∉ L := by
          intro hgood
          exact hselected.2.2.2.2.2 (hconfirm k hk _ hlow hgood)
        have htrue : BadExtension F L (trueRun F L k) k
            (sampleRun F S n (k + 1)) := by
          rw [heq] at hselected
          refine ⟨hselected.1, hselected.2.1, ?_, ?_, hnotL⟩
          · intro x hx
            exact hSL (hselected.2.2.1 hx)
          · rw [← hcp]
            exact hselected.2.2.2.2.1
        have hminimal : Encodable.encode (trueRun F L (k + 1)) ≤
            Encodable.encode (sampleRun F S n (k + 1)) := by
          rw [trueRun, dite_eq_left (hbefore k hk)]
          exact leastCode_le _ (hbefore k hk) htrue
        omega
      exact Encodable.encode_injective (Nat.le_antisymm hupper (Nat.le_of_not_lt hnotlower))

end GenLimit.FiniteWitness
