/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
module

public import LeanPool.LanguageGeneration.FiniteWitness.Confirmation
public import Mathlib.Basic.Denumerable

/-! # The complete ordinary-generation finite-witness characterization -/

@[expose] public section

namespace GenLimit.FiniteWitness

variable {α : Type*}

/-- A single target-free bounded search locks on every successful infinite target. -/
theorem normalized_locks [Encodable α] [DecidableEq α]
    (F : List α → α) (hF : Fresh F) {L : Set α}
    (hL : L.Infinite) (hvalid : EventuallyValid F L) : Locks (normalized F) L := by
  classical
  let hexstop := trueRun_stops hvalid
  let m := Nat.find hexstop
  have hstop : ¬∃ q, BadExtension F L (trueRun F L m) m q := Nat.find_spec hexstop
  have hbefore : ∀ k < m, ∃ q, BadExtension F L (trueRun F L k) k q := by
    intro k hk
    by_contra hbad
    exact Nat.find_min hexstop hk hbad
  obtain ⟨T, hTL, hcpT, hcontentT, hsizeT, hconfT⟩ := exists_confirming_witness F hL m
  refine ⟨T, hTL, ?_⟩
  intro S hTS hSL
  let n := S.card
  have hsize : (trueRun F L m).length + m + 1 ≤ n :=
    hsizeT.trans (Finset.card_le_card hTS)
  have hmn : m + 1 ≤ n := by omega
  have hlength : (trueRun F L m).length ≤ n := by omega
  have hseen : checkpoint L (m + 1) ⊆ S := hcpT.trans hTS
  have hcontents : (trueRun F L m).toFinset ⊆ S := hcontentT.trans hTS
  have hconfirm : ∀ k < m, ∀ q : List α,
      Encodable.encode q < Encodable.encode (trueRun F L (k + 1)) →
      F q ∈ L → F q ∈ S := by
    intro k hk q hq hqL
    exact hTS (hconfT k hk q hq hqL)
  have hmatches := sampleRun_matches_true hSL hseen hcontents hlength hbefore hconfirm
  have hm : sampleRun F S n m = trueRun F L m := hmatches m le_rfl
  -- Appending the entire actual sample forces a step past the last genuine error.
  let q := trueRun F L m ++ S.toList
  have hqcontent : q.toFinset = S := by
    simp [q, Finset.union_eq_right.mpr hcontents]
  have hqfresh : F q ∉ S := by
    rw [← hqcontent, List.mem_toFinset]
    exact hF q
  have hcand : Candidate F S n (sampleRun F S n m) m q := by
    rw [hm]
    refine ⟨List.prefix_append _ _, ?_, ?_, ?_, ?_, hqfresh⟩
    · simp only [q, List.length_append, Finset.length_toList]
      dsimp [n] at hmn
      omega
    · rw [hqcontent]
    · simp only [q, List.length_append, Finset.length_toList]
      dsimp [n] at hlength ⊢
      omega
    · rw [hqcontent]
      intro x hx
      exact (mem_checkpoint.mp hx).2
  have hex : ∃ q, Candidate F S n (sampleRun F S n m) m q := ⟨q, hcand⟩
  have hnext := sampleRun_next hex
  have hp := history_prefix_mono (sampleRun_prefix F S n) hmn
  have hprefix : trueRun F L m <+: sampleRun F S n n := by
    rw [← hm]
    exact hnext.1.trans hp
  have hstrict : (trueRun F L m).length < (sampleRun F S n n).length := by
    have hs := hnext.2.1
    rw [hm] at hs
    exact hs.trans_le hp.length_le
  have hlegal : (↑(sampleRun F S n n).toFinset : Set α) ⊆ L := by
    intro x hx
    exact hSL (sampleRun_content F S n n hx)
  have hcheckpoint : checkpoint L (m + 1) ⊆ (sampleRun F S n n).toFinset := by
    have hc := hnext.2.2.2.2.1
    rw [checkpoint_agrees hSL hseen le_rfl] at hc
    exact hc.trans (content_mono hp)
  have hcorrect : F (sampleRun F S n n) ∈ L := by
    by_contra hbad
    exact hstop ⟨_, hprefix, hstrict, hlegal, hcheckpoint, hbad⟩
  have hfresh : F (sampleRun F S n n) ∉ S :=
    sampleRun_preserves_fresh hnext.2.2.2.2.2 hmn
  exact ⟨hcorrect, hfresh⟩

/-- The normalization is selected before the target; the target may range over
all infinite sets on which the original ordered-history generator succeeds. -/
theorem universal_normalization [Countable α] [Infinite α]
    (G : Generic.Generator α) :
    ∃ g : Finset α → α, ∀ L : Set α, L.Infinite →
      (∀ stream : Generic.Stream α, Generic.Presents stream L →
        ∃ t₀, ∀ t, t₀ ≤ t → Generic.CorrectAt G L stream t) → Locks g L := by
  classical
  let : Encodable α := Encodable.ofCountable α
  refine ⟨normalized (freshRepair G), ?_⟩
  intro L hL hG
  apply normalized_locks (freshRepair G) (freshRepair_fresh G) hL
  have hsingleton : Generic.IsLimitGenerator G ({L} : Generic.LanguageClass α) := by
    intro K hK
    have hKL : K = L := Set.mem_singleton_iff.mp hK
    subst K
    exact hG
  exact freshRepair_eventuallyValid hsingleton (by simp)

theorem ordinary_implies_locks [Countable α] [Infinite α]
    {H : Generic.LanguageClass α} (hUUS : Generic.UUS H)
    (h : Generic.GeneratableInLimit H) :
    ∃ g : Finset α → α, ∀ L, L ∈ H → Locks g L := by
  obtain ⟨G, hG⟩ := h
  obtain ⟨g, hg⟩ := universal_normalization G
  exact ⟨g, fun L hL => hg L (hUUS L hL) (hG L hL)⟩

/-- Main theorem: the upstream ordinary notion equals the finite-witness condition. -/
theorem ordinary_iff_finiteWitnesses [Countable α] [Infinite α]
    (H : Generic.LanguageClass α) (hUUS : Generic.UUS H) :
    Generic.GeneratableInLimit H ↔ HasFiniteWitnesses H := by
  constructor
  · intro h
    exact locks_imply_finiteWitnesses (ordinary_implies_locks hUUS h)
  · exact finiteWitnesses_imply_ordinary

/-- All three conditions from the paper, using the original ordered-history API. -/
theorem full_characterization [Countable α] [Infinite α]
    (H : Generic.LanguageClass α) (hUUS : Generic.UUS H) :
    (Generic.GeneratableInLimit H ↔ SetDrivenGeneratable H) ∧
    (SetDrivenGeneratable H ↔ HasFiniteWitnesses H) := by
  constructor
  · exact ⟨fun h => locks_imply_setDriven (ordinary_implies_locks hUUS h),
      setDriven_implies_ordinary⟩
  · constructor
    · intro h
      exact (ordinary_iff_finiteWitnesses H hUUS).mp (setDriven_implies_ordinary h)
    · intro h
      exact locks_imply_setDriven (finiteWitnesses_imply_locks h)

end GenLimit.FiniteWitness
