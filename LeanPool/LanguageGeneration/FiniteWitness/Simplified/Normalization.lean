/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
module

public import LeanPool.LanguageGeneration.FiniteWitness.Simplified.Search
public import LeanPool.LanguageGeneration.FiniteWitness.Characterization

/-!
# Locking and characterization through fixed-size checkpoints
-/

@[expose] public section

namespace GenLimit.FiniteWitness.Simplified
variable {α : Type*} [Encodable α] [DecidableEq α]

/-- A sufficient finite confirming witness: markers, terminal history, and valid outputs.
No enlargement to meet a word-length bound is needed. -/
theorem exists_confirming_witness (M : Checkpoints α) (F : List α → α)
    (L : Set α) (m : ℕ) :
    ∃ T : Finset α, (↑T : Set α) ⊆ L ∧ M.points L (m + 1) ⊆ T ∧
      (trueRun M F L m).toFinset ⊆ T ∧
      ∀ k < m, ∀ q : List α,
        Encodable.encode q < Encodable.encode (trueRun M F L (k + 1)) →
        F q ∈ L → F q ∈ T := by
  classical
  let b := (Finset.range (m + 1)).sup (fun j => Encodable.encode (trueRun M F L j))
  let confirmations := ((belowCodes (List α) (b + 1)).image F).filter (fun x => x ∈ L)
  let T := (M.points L (m + 1) ∪ (trueRun M F L m).toFinset) ∪ confirmations
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · exact M.subset L (m + 1) hx
      · exact trueRun_legal M F L m hx
    · exact (Finset.mem_filter.mp hx).2
  · intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  · intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  · intro k hk q hq hqL
    have hb : Encodable.encode (trueRun M F L (k + 1)) ≤ b :=
      Finset.le_sup (f := fun j => Encodable.encode (trueRun M F L j))
        (Finset.mem_range.mpr (by omega))
    have hqB : q ∈ belowCodes (List α) (b + 1) := mem_belowCodes.mpr (by omega)
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨q, hqB, rfl⟩, hqL⟩)

theorem sampleRun_matches_true (M : Checkpoints α) {F : List α → α}
    {L : Set α} (hL : L.Infinite) {S : Finset α} {m : ℕ}
    (hSL : (↑S : Set α) ⊆ L) (hseen : M.points L (m + 1) ⊆ S)
    (hcontents : (trueRun M F L m).toFinset ⊆ S)
    (hbefore : ∀ k < m, ∃ q, BadExtension M F L (trueRun M F L k) k q)
    (hconfirm : ∀ k < m, ∀ q : List α,
      Encodable.encode q < Encodable.encode (trueRun M F L (k + 1)) →
      F q ∈ L → F q ∈ S) :
    ∀ k ≤ m, sampleRun M F S k = trueRun M F L k := by
  classical
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hkm
      have hk : k < m := by omega
      have heq := ih (by omega)
      have hbad := trueRun_next (hbefore k hk)
      have hp := history_prefix_mono (trueRun_prefix M F L) hkm
      have hcp := M.agree hL hSL hseen (j := k + 1) (by omega)
      have hcand : Candidate M F S (sampleRun M F S k) k (trueRun M F L (k + 1)) := by
        rw [heq]
        refine ⟨hbad.1, hbad.2.1, (content_mono hp).trans hcontents, ?_, ?_⟩
        · rw [hcp]
          exact hbad.2.2.2.1
        · exact fun hx => hbad.2.2.2.2 (hSL hx)
      have hex : ∃ q, Candidate M F S (sampleRun M F S k) k q := ⟨_, hcand⟩
      have hselected := sampleRun_next hex
      have hupper : Encodable.encode (sampleRun M F S (k + 1)) ≤
          Encodable.encode (trueRun M F L (k + 1)) := by
        simp only [sampleRun, dite_eq_left hex]
        exact leastCode_le _ hex hcand
      have hnotlower : ¬ Encodable.encode (sampleRun M F S (k + 1)) <
          Encodable.encode (trueRun M F L (k + 1)) := by
        intro hlow
        have hnotL : F (sampleRun M F S (k + 1)) ∉ L := by
          intro hgood
          exact hselected.2.2.2.2 (hconfirm k hk _ hlow hgood)
        have htrue : BadExtension M F L (trueRun M F L k) k
            (sampleRun M F S (k + 1)) := by
          rw [heq] at hselected
          refine ⟨hselected.1, hselected.2.1, ?_, ?_, hnotL⟩
          · intro x hx
            exact hSL (hselected.2.2.1 hx)
          · rw [← hcp]
            exact hselected.2.2.2.1
        have hminimal : Encodable.encode (trueRun M F L (k + 1)) ≤
            Encodable.encode (sampleRun M F S (k + 1)) := by
          rw [trueRun, dite_eq_left (hbefore k hk)]
          exact leastCode_le _ (hbefore k hk) htrue
        omega
      exact Encodable.encode_injective (Nat.le_antisymm hupper (Nat.le_of_not_lt hnotlower))

/-- The cutoff-free search locks on every successful infinite target. -/
theorem normalized_locks (M : Checkpoints α) (F : List α → α) (hF : Fresh F)
    {L : Set α} (hL : L.Infinite) (hvalid : EventuallyValid F L) :
    Locks (normalized M F) L := by
  classical
  let hexstop := trueRun_stops M hvalid
  let m := Nat.find hexstop
  have hstop := Nat.find_spec hexstop
  have hbefore : ∀ k < m, ∃ q, BadExtension M F L (trueRun M F L k) k q := by
    intro k hk
    by_contra hbad
    exact Nat.find_min hexstop hk hbad
  obtain ⟨T, hTL, hcpT, hcontentT, hconfT⟩ := exists_confirming_witness M F L m
  refine ⟨T, hTL, ?_⟩
  intro S hTS hSL
  have hseen := hcpT.trans hTS
  have hmn : m + 1 ≤ S.card := by
    rw [← M.card hL (m + 1)]
    exact Finset.card_le_card hseen
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have hm : sampleRun M F S m = trueRun M F L m :=
    sampleRun_matches_true M hL hSL hseen (hcontentT.trans hTS) hbefore
      (fun k hk q hq hqL => hTS (hconfT k hk q hq hqL)) m le_rfl
  have hnext := sampleRun_next (candidate_exists M hF hS m)
  have hp := history_prefix_mono (sampleRun_prefix M F S) hmn
  have hprefix : trueRun M F L m <+: sampleRun M F S S.card := by
    rw [← hm]
    exact hnext.1.trans hp
  have hstrict : (trueRun M F L m).length < (sampleRun M F S S.card).length := by
    have hs := hnext.2.1
    rw [hm] at hs
    exact hs.trans_le hp.length_le
  have hlegal : (↑(sampleRun M F S S.card).toFinset : Set α) ⊆ L :=
    fun x hx => hSL (sampleRun_content M F S S.card hx)
  have hcheckpoint : M.points L (m + 1) ⊆ (sampleRun M F S S.card).toFinset := by
    have hc := hnext.2.2.2.1
    rw [M.agree hL hSL hseen le_rfl] at hc
    exact hc.trans (content_mono hp)
  have hcorrect : F (sampleRun M F S S.card) ∈ L := by
    by_contra hbad
    exact hstop ⟨_, hprefix, hstrict, hlegal, hcheckpoint, hbad⟩
  have hlast := (sampleRun_next (candidate_exists M hF hS (S.card - 1))).2.2.2.2
  have he : S.card - 1 + 1 = S.card := by omega
  rw [he] at hlast
  exact ⟨hcorrect, hlast⟩

omit [Encodable α] [DecidableEq α] in
/-- Same universal quantifiers as the manuscript, for any countably infinite universe. -/
theorem universal_normalization [Countable α] [Infinite α] (G : Generic.Generator α) :
    ∃ g : Finset α → α, ∀ L : Set α, L.Infinite →
      (∀ stream : Generic.Stream α, Generic.Presents stream L →
        ∃ t₀, ∀ t, t₀ ≤ t → Generic.CorrectAt G L stream t) → Locks g L := by
  classical
  let : Encodable α := Encodable.ofCountable α
  let e : α ≃ ℕ := Classical.choice (inferInstance : Nonempty (α ≃ ℕ))
  refine ⟨normalized (orderedCheckpoints e) (freshRepair G), ?_⟩
  intro L hL hG
  apply normalized_locks (orderedCheckpoints e) (freshRepair G) (freshRepair_fresh G) hL
  have hsingle : Generic.IsLimitGenerator G ({L} : Generic.LanguageClass α) := by
    intro K hK
    have hKL : K = L := Set.mem_singleton_iff.mp hK
    subst K
    exact hG
  exact freshRepair_eventuallyValid hsingle (by simp)

omit [Encodable α] [DecidableEq α] in
/-- The revised proof of the characterization goes directly through locking witnesses. -/
theorem ordinary_iff_finiteWitnesses [Countable α] [Infinite α]
    (H : Generic.LanguageClass α) (hUUS : Generic.UUS H) :
    Generic.GeneratableInLimit H ↔ HasFiniteWitnesses H := by
  constructor
  · rintro ⟨G, hG⟩
    obtain ⟨g, hg⟩ := universal_normalization G
    exact locks_imply_finiteWitnesses ⟨g, fun L hL => hg L (hUUS L hL) (hG L hL)⟩
  · exact finiteWitnesses_imply_ordinary

omit [Encodable α] [DecidableEq α] in
theorem full_characterization [Countable α] [Infinite α]
    (H : Generic.LanguageClass α) (hUUS : Generic.UUS H) :
    (Generic.GeneratableInLimit H ↔ SetDrivenGeneratable H) ∧
    (SetDrivenGeneratable H ↔ HasFiniteWitnesses H) := by
  have ho := ordinary_iff_finiteWitnesses H hUUS
  refine ⟨⟨?_, setDriven_implies_ordinary⟩, ⟨?_, ?_⟩⟩
  · intro h
    exact locks_imply_setDriven (finiteWitnesses_imply_locks (ho.mp h))
  · intro h
    exact ho.mp (setDriven_implies_ordinary h)
  · intro h
    exact locks_imply_setDriven (finiteWitnesses_imply_locks h)

end GenLimit.FiniteWitness.Simplified
