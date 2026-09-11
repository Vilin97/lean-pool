/-
Copyright (c) 2026 Yann Pequignot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Pequignot
-/
import Mathlib.Order.WellFoundedSet

/-!
# Regular sequences in a well quasi-order

A sequence `f : ℕ → Q` in a quasi-order `(Q, r)` is *regular* if every term dominates infinitely
many later terms. This file shows that in a WQO every sequence has a regular tail
(`WellQuasiOrdered.eventuallyRegular`), and draws two consequences that are the backbone of the
2-BQO closure theorems in `TwoBQO.lean`:

* an antitone sequence in a WQO eventually stabilizes
  (`WellQuasiOrdered.exists_forall_le_of_antitone`);
* `List.SublistForall₂ r` (Higman's order) is a WQO on all of `List Q`, not just on a
  `PartiallyWellOrderedOn` subset (`WellQuasiOrdered.sublistForall₂`), a direct corollary of
  Higman's lemma already in Mathlib
  (`Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂`).

## Main definitions

* `Preorder.IsRegularSeq r f`: every term of `f` dominates infinitely many later terms.

## Main results

* `WellQuasiOrdered.eventuallyRegular`: every sequence in a WQO has a regular tail.
* `WellQuasiOrdered.exists_forall_le_of_antitone`: an antitone sequence in a WQO stabilizes.
* `WellQuasiOrdered.sublistForall₂`: Higman's order is a WQO on `List Q` when `r` is a WQO on `Q`.
-/

open Set Preorder

noncomputable section

/-!
## Regular sequences
A sequence `(f i)_{i ∈ ℕ}` in a quasi-order `(Q, ≤)` is **regular**
if for every `i : ℕ`, the set `{j : ℕ | f i ≤ f j}` is infinite. -/
namespace Preorder

/-- A sequence is *regular* if every term dominates infinitely many later terms. -/
def IsRegularSeq {Q : Type*} (r : Q → Q → Prop) (f : ℕ → Q) : Prop :=
  ∀ i : ℕ, {j : ℕ | r (f i) (f j)}.Infinite

/-- A regular sequence has arbitrarily large indices dominating any given index:
for every `i` and threshold `N` there is `j ≥ N` with `f i ≤ f j`. -/
theorem IsRegularSeq.exists_ge {Q : Type*} {r : Q → Q → Prop}
    {f : ℕ → Q} (hf : IsRegularSeq r f) (i N : ℕ) :
    ∃ j, N ≤ j ∧ r (f i) (f j) := by
  obtain ⟨j, hj_mem, hj_gt⟩ := (hf i).exists_gt N
  exact ⟨j, hj_gt.le, hj_mem⟩

/-- A tail of a regular sequence is regular. -/
theorem IsRegularSeq.tail {Q : Type*} {r : Q → Q → Prop}
    {f : ℕ → Q} (hf : IsRegularSeq r f) (k : ℕ) :
    IsRegularSeq r fun i => f (i + k) := by
  intro i
  have h_infinite : {j | r (f (i + k)) (f j)}.Infinite := hf (i + k)
  refine Set.infinite_of_forall_exists_gt fun n => ?_
  obtain ⟨j, hj₁, hj₂⟩ := h_infinite.exists_gt (n + k)
  exact ⟨j - k, by simpa [Nat.sub_add_cancel (show k ≤ j from by omega)] using hj₁,
    by omega⟩

end Preorder

private theorem key_reformulation {Q : Type*} (r : Q → Q → Prop) (f : ℕ → Q)
    (hcon : ∀ n, ∃ i, {j : ℕ | r (f (i + n)) (f (j + n))}.Finite) :
    ∀ m : ℕ, ∃ i, m ≤ i ∧ {j : ℕ | r (f i) (f j)}.Finite := by
  intro m
  obtain ⟨i, hfin⟩ := hcon m
  refine ⟨i + m, by omega, ?_⟩
  have hsplit : {j : ℕ | r (f (i + m)) (f j)}
      = {j : ℕ | j < m ∧ r (f (i + m)) (f j)}
        ∪ (fun k => k + m) '' {k : ℕ | r (f (i + m)) (f (k + m))} := by
    ext j
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro hj
      rcases lt_or_ge j m with h | h
      · exact Or.inl ⟨h, hj⟩
      · exact Or.inr ⟨j - m, by simpa [Nat.sub_add_cancel h] using hj, Nat.sub_add_cancel h⟩
    · rintro (⟨_, hj⟩ | ⟨k, hk, rfl⟩)
      · exact hj
      · exact hk
  rw [hsplit]
  exact Set.Finite.union ((Set.finite_Iio m).subset fun j ⟨hj, _⟩ => hj) (hfin.image _)

private theorem exists_bad_seq {Q : Type*} (r : Q → Q → Prop) (f : ℕ → Q)
    (key : ∀ m : ℕ, ∃ i, m ≤ i ∧ {j : ℕ | r (f i) (f j)}.Finite) :
    ∃ idx : ℕ → ℕ, StrictMono idx ∧ ∀ m n, m < n → ¬ r (f (idx m)) (f (idx n)) := by
  let S := {p : ℕ × ℕ // ∀ j, r (f p.1) (f j) → j ≤ p.2}
  have succ_step : ∀ p : S, ∃ q : S, p.1.1 < q.1.1 ∧ p.1.2 < q.1.1 := by
    rintro ⟨⟨i, B⟩, hB⟩
    obtain ⟨i', hi'_ge, hfin'⟩ := key (max (i + 1) (B + 1))
    obtain ⟨B', hB'⟩ := hfin'.bddAbove
    refine ⟨⟨(i', max B' i'), fun j hj => le_trans (hB' hj) (le_max_left _ _)⟩, ?_, ?_⟩
    · change i < i'; have h := le_trans (le_max_left (i + 1) (B + 1)) hi'_ge; omega
    · change B < i'; have h := le_trans (le_max_right (i + 1) (B + 1)) hi'_ge; omega
  obtain ⟨i₀, _, hfin₀⟩ := key 0
  obtain ⟨B₀, hB₀⟩ := hfin₀.bddAbove
  let p0 : S := ⟨(i₀, B₀), hB₀⟩
  let nextOf : S → S := fun p => (succ_step p).choose
  let seq : ℕ → S := fun k => Nat.rec p0 (fun _ q => nextOf q) k
  have hseq_succ : ∀ k, seq (k + 1) = nextOf (seq k) := fun k => rfl
  have hstep : ∀ p : S, p.1.1 < (nextOf p).1.1 ∧ p.1.2 < (nextOf p).1.1 :=
    fun p => (succ_step p).choose_spec
  set idx : ℕ → ℕ := fun k => (seq k).1.1 with hidx
  set bd : ℕ → ℕ := fun k => (seq k).1.2 with hbd
  have hidx_lt : ∀ k, idx k < idx (k + 1) := fun k => by
    change (seq k).1.1 < (seq (k + 1)).1.1
    rw [hseq_succ k]; exact (hstep (seq k)).1
  have hbd_lt_idx : ∀ k, bd k < idx (k + 1) := fun k => by
    change (seq k).1.2 < (seq (k + 1)).1.1
    rw [hseq_succ k]; exact (hstep (seq k)).2
  have hidx_mono : StrictMono idx := strictMono_nat_of_lt_succ hidx_lt
  refine ⟨idx, hidx_mono, ?_⟩
  intro m n hmn hle
  have hbound := (seq m).2
  have h1 : idx n ≤ bd m := hbound (idx n) hle
  have h2 : bd m < idx (m + 1) := hbd_lt_idx m
  have h3 : idx (m + 1) ≤ idx n := hidx_mono.le_iff_le.mpr hmn
  omega

/-- **In a WQO every sequence is eventually regular.** In fact this is an equivalent
characterization of WQO, since any bad sequence admits no regular tail. -/
theorem WellQuasiOrdered.eventuallyRegular {Q : Type*} (r : Q → Q → Prop)
    (hwqo : WellQuasiOrdered r) (f : ℕ → Q) :
    ∃ n : ℕ, IsRegularSeq r fun i => f (i + n) := by
  by_contra hcon
  push Not at hcon
  simp only [IsRegularSeq, not_forall, Set.not_infinite] at hcon
  obtain ⟨idx, _, hbad⟩ := exists_bad_seq r f (key_reformulation r f hcon)
  obtain ⟨m, n, hmn, hrel⟩ := hwqo fun k => f (idx k)
  exact hbad m n hmn hrel

/-- In a WQO, an antitone sequence stabilizes from above: there is an index `m` from
which the sequence becomes `r`-dominated by `a m` (so, together with antitonicity,
`a m` is `r`-equivalent to every later term). -/
theorem WellQuasiOrdered.exists_forall_le_of_antitone {β : Type*} {r : β → β → Prop}
    [IsPreorder β r] (hwqo : WellQuasiOrdered r) (a : ℕ → β)
    (hanti : ∀ m n : ℕ, m ≤ n → r (a n) (a m)) :
    ∃ m : ℕ, ∀ n : ℕ, m ≤ n → r (a m) (a n) := by
  by_contra h_contra
  obtain ⟨idx, hidx⟩ : ∃ idx : ℕ → ℕ, StrictMono idx ∧ ∀ k, ¬ r (a (idx k)) (a (idx (k + 1))) := by
    have h_seq : ∀ k, ∃ n > k, ¬ r (a k) (a n) := fun k => by
      push Not at h_contra
      obtain ⟨n, hn₁, hn₂⟩ := h_contra k
      exact ⟨n, lt_of_le_of_ne hn₁ (by rintro rfl; exact hn₂ (refl_of r _)), hn₂⟩
    choose f hf using h_seq
    exact ⟨fun k => Nat.recOn k 0 fun k ih => f ih,
      strictMono_nat_of_lt_succ fun k => (hf _).1, fun k => (hf _).2⟩
  obtain ⟨k, l, hkl, h⟩ := hwqo fun n => a (idx n)
  exact hidx.2 k (trans_of r h (hanti _ _ (hidx.1.monotone (Nat.succ_le_of_lt hkl))))

/-- `List.SublistForall₂ r` is a preorder on `List Q` whenever `r` is a preorder on `Q`. -/
instance List.SublistForall₂.instIsPreorder {Q : Type*} (r : Q → Q → Prop) [IsPreorder Q r] :
    IsPreorder (List Q) (List.SublistForall₂ r) where
  refl := (List.SublistForall₂.is_refl (Rₐ := r)).refl
  trans := (List.SublistForall₂.is_trans (Rₐ := r)).trans

/-- **Higman's Lemma, unrestricted.** If `r` is a WQO on `Q`, then `List.SublistForall₂ r` is a
WQO on all of `List Q` (not just on a `PartiallyWellOrderedOn` subset). A direct restatement of
`Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂` via
`partiallyWellOrderedOn_univ_iff`. -/
theorem WellQuasiOrdered.sublistForall₂ {Q : Type*} {r : Q → Q → Prop} [IsPreorder Q r]
    (h : WellQuasiOrdered r) : WellQuasiOrdered (List.SublistForall₂ r) := by
  rw [← partiallyWellOrderedOn_univ_iff] at h ⊢
  simpa [Set.eq_univ_iff_forall] using h.partiallyWellOrderedOn_sublistForall₂ r

end
