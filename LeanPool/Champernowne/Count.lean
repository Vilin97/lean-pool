/-
Copyright (c) 2026 Arthur Champernowne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Champernowne
-/
module

public import LeanPool.Champernowne.Defs
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Finset.Powerset

/-!
# Occurrence-counting inequalities

This file gives the lower append bound, a characterization by starting positions,
and the `allWords` enumeration of length-`k` digit strings. Summing occurrences
over `allWords` bounds the number of windows, allowing upper frequency estimates
to be derived from lower ones by complement.

The window convention is documented at `countOccurrences`. Statements assume
`w ≠ []` when the empty word needs to be excluded. Further append, take, drop,
and exact digit-counting results are in `LeanPool.Champernowne.CountExtras`.
-/

@[expose] public section

namespace Champernowne

theorem countOccurrences_cons (w l : List ℕ) (x : ℕ) :
    countOccurrences w (x :: l)
      = countOccurrences w l + (if w.isPrefixOf (x :: l) then 1 else 0) := by
  simp [countOccurrences, List.countP_cons]

theorem countOccurrences_nil' (w : List ℕ) :
    countOccurrences w [] = if w.isPrefixOf [] then 1 else 0 := by
  simp [countOccurrences]

theorem countOccurrences_nil {w : List ℕ} (hw : w ≠ []) :
    countOccurrences w [] = 0 := by
  obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hw
  simp [countOccurrences, List.isPrefixOf]

/-- Extending the list to the right preserves window hits. -/
theorem isPrefixOf_append_of_isPrefixOf {w a : List ℕ} (b : List ℕ)
    (h : w.isPrefixOf a) : w.isPrefixOf (a ++ b) := by
  rw [List.isPrefixOf_iff_prefix] at h ⊢
  exact h.trans (List.prefix_append a b)

/-! ### The append lower bound -/

/-- Lower bound: occurrences inside `a` and inside `b` survive in `a ++ b`.
Fails for `w = []` (window counts overlap at the seam). -/
theorem add_countOccurrences_le_append {w : List ℕ} (hw : w ≠ [])
    (a b : List ℕ) :
    countOccurrences w a + countOccurrences w b
      ≤ countOccurrences w (a ++ b) := by
  induction a with
  | nil => simp [countOccurrences_nil hw]
  | cons x a' ih =>
    rw [List.cons_append, countOccurrences_cons, countOccurrences_cons]
    have hmono : (if w.isPrefixOf (x :: a') then 1 else 0)
        ≤ if w.isPrefixOf (x :: (a' ++ b)) then 1 else 0 := by
      by_cases h : w.isPrefixOf (x :: a')
      · have h2 : w.isPrefixOf (x :: (a' ++ b)) := by
          rw [← List.cons_append]
          exact isPrefixOf_append_of_isPrefixOf b h
        simp [h, h2]
      · simp [h]
    omega

/-! ### Occurrences in `champBlocks` -/

/-- Per-number occurrences survive in the stream. -/
theorem sum_le_countOccurrences_champBlocks {b : ℕ} {w : List ℕ}
    (hw : w ≠ []) (N : ℕ) :
    ∑ n ∈ Finset.Ico 1 (N + 1), countOccurrences w (bigDigits b n)
      ≤ countOccurrences w (champBlocks b N) := by
  induction N with
  | zero => simp [champBlocks, countOccurrences_nil hw]
  | succ n ih =>
    rw [champBlocks_succ, Finset.sum_Ico_succ_top (by omega)]
    calc (∑ k ∈ Finset.Ico 1 (n + 1), countOccurrences w (bigDigits b k))
          + countOccurrences w (bigDigits b (n + 1))
        ≤ countOccurrences w (champBlocks b n)
          + countOccurrences w (bigDigits b (n + 1)) :=
          Nat.add_le_add_right ih _
    _ ≤ _ := add_countOccurrences_le_append hw _ _

/-! ### Position characterization -/

/-- `countOccurrences` counts window start positions. -/
theorem countOccurrences_eq_card_filter_range (w l : List ℕ) :
    countOccurrences w l
      = ((Finset.range (l.length + 1)).filter
          (fun j => w.isPrefixOf (l.drop j))).card := by
  induction l with
  | nil =>
    by_cases h : w.isPrefixOf []
    · simp [countOccurrences_nil', h]
    · simp [countOccurrences_nil', h]
  | cons x xs ih =>
    rw [List.length_cons, Finset.card_filter, Finset.sum_range_succ',
      countOccurrences_cons, ih, Finset.card_filter]
    simp only [List.drop_succ_cons, List.drop_zero]

/-! ### Word enumeration and the window pigeonhole

`allWords b k` enumerates all length-`k` digit strings over `{0, …, b−1}`
(leading zeros allowed) — the complement machinery that lets the upper
occurrence bound be *derived* from the lower one: a window matching no
`v ≠ w` must match `w`. -/

/-- All length-`k` digit strings over `{0, …, b−1}`, leading zeros allowed. -/
def allWords (b : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | k + 1 => (Finset.range b).biUnion fun d => (allWords b k).image (d :: ·)

theorem mem_allWords {b k : ℕ} {l : List ℕ} :
    l ∈ allWords b k ↔ l.length = k ∧ ∀ d ∈ l, d < b := by
  induction k generalizing l with
  | zero => cases l <;> simp [allWords]
  | succ k ih =>
    simp only [allWords, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨d, hd, v, hv, rfl⟩
      obtain ⟨hlen, hlt⟩ := ih.mp hv
      refine ⟨by simp [hlen], ?_⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he'
      · exact hd
      · exact hlt e he'
    · rintro ⟨hlen, hlt⟩
      cases l with
      | nil => simp at hlen
      | cons d v =>
        exact ⟨d, hlt d (List.mem_cons_self ..), v,
          ih.mpr ⟨by simpa using hlen, fun e he => hlt e (List.mem_cons_of_mem d he)⟩,
          rfl⟩

theorem card_allWords (b k : ℕ) : (allWords b k).card = b ^ k := by
  induction k with
  | zero => simp [allWords]
  | succ k ih =>
    have hdisj : ∀ d₁ ∈ Finset.range b, ∀ d₂ ∈ Finset.range b, d₁ ≠ d₂ →
        Disjoint ((allWords b k).image (d₁ :: ·))
          ((allWords b k).image (d₂ :: ·)) := by
      intro d₁ _ d₂ _ hne
      rw [Finset.disjoint_left]
      rintro l hl₁ hl₂
      obtain ⟨v₁, -, rfl⟩ := Finset.mem_image.mp hl₁
      obtain ⟨v₂, -, heq⟩ := Finset.mem_image.mp hl₂
      injection heq with h1 _
      exact hne h1.symm
    calc (allWords b (k + 1)).card
        = ∑ d ∈ Finset.range b, ((allWords b k).image (d :: ·)).card :=
          Finset.card_biUnion hdisj
    _ = ∑ _d ∈ Finset.range b, (allWords b k).card :=
          Finset.sum_congr rfl fun d _ =>
            Finset.card_image_of_injective _ fun v₁ v₂ h => by injection h
    _ = b ^ (k + 1) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul, ih, pow_succ']

/-- Window pigeonhole: a window position matches at most one length-`k`
word, so over ALL length-`k` words the occurrence counts total at most the
number of window start positions. This single inequality replaces the
entire upper-bound counting chain. -/
theorem sum_countOccurrences_allWords_le (b k : ℕ) (l : List ℕ) :
    ∑ v ∈ allWords b k, countOccurrences v l ≤ l.length + 1 := by
  have hdisj : ∀ v₁ ∈ allWords b k, ∀ v₂ ∈ allWords b k, v₁ ≠ v₂ →
      Disjoint
        ((Finset.range (l.length + 1)).filter (fun j => v₁.isPrefixOf (l.drop j)))
        ((Finset.range (l.length + 1)).filter (fun j => v₂.isPrefixOf (l.drop j))) := by
    intro v₁ h₁ v₂ h₂ hne
    rw [Finset.disjoint_left]
    rintro j hj₁ hj₂
    have hp₁ := List.isPrefixOf_iff_prefix.mp (Finset.mem_filter.mp hj₁).2
    have hp₂ := List.isPrefixOf_iff_prefix.mp (Finset.mem_filter.mp hj₂).2
    have hlen₁ := (mem_allWords.mp h₁).1
    have hlen₂ := (mem_allWords.mp h₂).1
    apply hne
    calc v₁ = (l.drop j).take v₁.length := List.prefix_iff_eq_take.mp hp₁
    _ = (l.drop j).take v₂.length := by rw [hlen₁, hlen₂]
    _ = v₂ := (List.prefix_iff_eq_take.mp hp₂).symm
  calc ∑ v ∈ allWords b k, countOccurrences v l
      = ∑ v ∈ allWords b k,
          ((Finset.range (l.length + 1)).filter
            (fun j => v.isPrefixOf (l.drop j))).card :=
        Finset.sum_congr rfl fun v _ => countOccurrences_eq_card_filter_range v l
  _ = ((allWords b k).biUnion fun v =>
        (Finset.range (l.length + 1)).filter
          (fun j => v.isPrefixOf (l.drop j))).card :=
        (Finset.card_biUnion hdisj).symm
  _ ≤ (Finset.range (l.length + 1)).card :=
        Finset.card_le_card
          (Finset.biUnion_subset.mpr fun v _ => Finset.filter_subset _ _)
  _ = l.length + 1 := Finset.card_range _

end Champernowne
