/-
Copyright (c) 2026 Shuangping Li, Peng Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuangping Li, Peng Zhang
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Set.Finite.Basic

/-!
# A generic countable-universe interface

The original core fixes the universe to `ℕ`, as in the finite-query
Kleinberg--Mullainathan construction. Many later papers state their results
over an arbitrary countable example space. This file supplies that generic
paper-facing layer without changing the existing API.

A finite history of length `t` is represented by `Fin t → α`. Thus a
`Generator α` is literally a function on finite sequences, while
`output G stream t` exposes only the prefix strictly before time `t`.
-/

public section

namespace GenLimit.Generic

/-- A language over an arbitrary example type. -/
abbrev Language (α : Type*) := Set α

/-- A possibly uncountable class of languages. -/
abbrev LanguageClass (α : Type*) := Set (Language α)

/-- An enumerated countable family of languages.  Unlike `LanguageClass`,
this representation preserves the paper's index order and repetitions. -/
abbrev LanguageFamily (α : Type*) := ℕ → Language α

/-- An infinite stream of examples. -/
abbrev Stream (α : Type*) := ℕ → α

/-- A generator is a map from each finite sequence to one new example. -/
abbrev Generator (α : Type*) := ∀ t : ℕ, (Fin t → α) → α

/-- Exact presentation: repetitions are allowed, and every target element
must eventually occur. -/
@[expose]
def Presents (stream : Stream α) (L : Language α) : Prop :=
  Set.range stream = L

/-- Every element ever shown by the stream belongs to `L`. -/
def StreamIn (stream : Stream α) (L : Language α) : Prop :=
  Set.range stream ⊆ L

/-- The distinct values in a finite sequence. -/
noncomputable def sequenceSample {t : ℕ} (xs : Fin t → α) : Finset α := by
  classical
  exact Finset.univ.image xs

/-- The distinct observations strictly before time `t`. -/
@[expose]
noncomputable def sample (stream : Stream α) (t : ℕ) : Finset α := by
  classical
  exact (Finset.range t).image stream

/-- The stream that follows a finite history and then repeats a fallback
value forever. -/
def historyThenFallback (history : List α) (fallback : α) : Stream α :=
  fun n => if h : n < history.length then history.get ⟨n, h⟩ else fallback

/-- A finite history followed by a fallback stays in a language when both
the history and fallback do. -/
theorem streamIn_historyThenFallback
    {history : List α} {fallback : α} {L : Language α}
    (hhistory : ∀ x ∈ history, x ∈ L)
    (hfallback : fallback ∈ L) :
    StreamIn (historyThenFallback history fallback) L := by
  rintro _ ⟨n, rfl⟩
  by_cases hn : n < history.length
  · rw [historyThenFallback, dite_eq_left hn]
    exact hhistory _ (List.get_mem history ⟨n, hn⟩)
  · rw [historyThenFallback, dite_eq_right hn]
    exact hfallback

/-- Run `G` on the prefix of `stream` strictly before time `t`. -/
@[expose] def output (G : Generator α) (stream : Stream α) (t : ℕ) : α :=
  G t (fun i => stream i)

theorem mem_sequenceSample_iff {t : ℕ} {xs : Fin t → α} {x : α} :
    x ∈ sequenceSample xs ↔ ∃ i : Fin t, xs i = x := by
  classical
  simp [sequenceSample]

/-- Passing a list through its canonical `Fin`-indexed input recovers its
underlying finite set of values. -/
theorem sequenceSample_list_get [DecidableEq α] (xs : List α) :
    sequenceSample xs.get = xs.toFinset := by
  classical
  ext x
  rw [mem_sequenceSample_iff, List.mem_toFinset, List.mem_iff_get]

/-- An injective finite history has as many distinct observations as
positions. -/
theorem sequenceSample_card_of_injective
    {t : ℕ} (xs : Fin t → α) (hxs : Function.Injective xs) :
    (sequenceSample xs).card = t := by
  classical
  rw [sequenceSample, Finset.card_image_iff.mpr]
  · simp
  · intro i _ j _ hij
    exact hxs hij

/-- Pointwise membership of a finite history implies membership of every
element in its underlying sample. -/
theorem sequenceSample_subset_of_pointwise
    {t : ℕ} {xs : Fin t → α} {S : Set α}
    (hxs : ∀ k, xs k ∈ S) :
    (↑(sequenceSample xs) : Set α) ⊆ S := by
  intro x hx
  have hx' : x ∈ sequenceSample xs := hx
  rw [mem_sequenceSample_iff] at hx'
  obtain ⟨k, rfl⟩ := hx'
  exact hxs k

/-- Enumerating a finset through its canonical equivalence with `Fin`
recovers exactly that finset as the distinct sample. -/
theorem sequenceSample_equivFin_symm (S : Finset α) :
    sequenceSample (fun i : Fin S.card => (S.equivFin.symm i).1) = S := by
  classical
  ext x
  rw [mem_sequenceSample_iff]
  constructor
  · rintro ⟨i, rfl⟩
    exact (S.equivFin.symm i).2
  · intro hx
    let z : S := ⟨x, hx⟩
    refine ⟨S.equivFin z, ?_⟩
    simp [z]

/-- The value map of a finset's canonical `Fin` enumeration is injective. -/
theorem equivFin_symm_value_injective (S : Finset α) :
    Function.Injective (fun i : Fin S.card => (S.equivFin.symm i).1) := by
  intro i j hij
  apply S.equivFin.symm.injective
  apply Subtype.ext
  exact hij

theorem mem_sample_iff {stream : Stream α} {t : ℕ} {x : α} :
    x ∈ sample stream t ↔ ∃ s < t, stream s = x := by
  classical
  simp [sample]

/-- An injective stream has exactly `t` distinct observations before round
`t`. -/
theorem sample_card_of_injective
    (stream : Stream α) (hstream : Function.Injective stream) (t : ℕ) :
    (sample stream t).card = t := by
  classical
  rw [sample, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    exact hstream hab

/-- Samples depend only on the corresponding finite stream prefix. -/
theorem sample_eq_of_eq_on_prefix
    {stream₁ stream₂ : Stream α} {t : ℕ}
    (h : ∀ n, n < t → stream₁ n = stream₂ n) :
    sample stream₁ t = sample stream₂ t := by
  classical
  ext x
  simp only [mem_sample_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, (h n hn).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, h n hn⟩

/-- Sampling a finite-history stream at the end of the history recovers
exactly the history's distinct values. -/
theorem sample_historyThenFallback_length [DecidableEq α]
    (history : List α) (fallback : α) :
    sample (historyThenFallback history fallback) history.length =
      history.toFinset := by
  classical
  ext x
  simp only [mem_sample_iff, List.mem_toFinset]
  constructor
  · rintro ⟨n, hn, hnx⟩
    apply List.mem_iff_get.mpr
    refine ⟨⟨n, hn⟩, ?_⟩
    simpa [historyThenFallback, hn] using hnx
  · intro hx
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
    refine ⟨i, i.isLt, ?_⟩
    simpa [historyThenFallback, i.isLt] using hi

theorem sequenceSample_prefix (stream : Stream α) (t : ℕ) :
    sequenceSample (fun i : Fin t => stream i) = sample stream t := by
  classical
  ext x
  simp only [mem_sequenceSample_iff, mem_sample_iff]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, i.isLt, hi⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

theorem sample_mono {stream : Stream α} {s t : ℕ} (hst : s ≤ t) :
    sample stream s ⊆ sample stream t := by
  intro x hx
  rw [mem_sample_iff] at hx ⊢
  obtain ⟨i, his, rfl⟩ := hx
  exact ⟨i, lt_of_lt_of_le his hst, rfl⟩

theorem value_mem_sample {stream : Stream α} {s t : ℕ} (hst : s < t) :
    stream s ∈ sample stream t := by
  rw [mem_sample_iff]
  exact ⟨s, hst, rfl⟩

theorem sample_card_step (stream : Stream α) (t : ℕ) :
    (sample stream (t + 1)).card ≤ (sample stream t).card + 1 := by
  classical
  have hsub : sample stream (t + 1) ⊆ insert (stream t) (sample stream t) := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_sample_iff.mp hx
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hst
    · exact Finset.mem_insert_of_mem (mem_sample_iff.mpr ⟨s, hs, hxs⟩)
    · subst s
      subst x
      exact @Finset.mem_insert_self α (Classical.decEq α) (stream t) (sample stream t)
  exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)

/-- If a finite prefix contains at least `k` distinct observations, some
earlier prefix contains exactly `k`. -/
theorem exists_sample_card_eq_of_le
    {stream : Stream α} {t k : ℕ}
    (hk : k ≤ (sample stream t).card) :
    ∃ r ≤ t, (sample stream r).card = k := by
  classical
  let hex : ∃ r, k ≤ (sample stream r).card := ⟨t, hk⟩
  let r := Nat.find hex
  have hrLower : k ≤ (sample stream r).card := Nat.find_spec hex
  have hrt : r ≤ t := Nat.find_min' hex hk
  by_cases hr0 : r = 0
  · have hk0 : k = 0 := by
      rw [hr0] at hrLower
      simpa [sample] using hrLower
    exact ⟨0, by simp, by simp [sample, hk0]⟩
  · obtain ⟨s, hrs⟩ := Nat.exists_eq_succ_of_ne_zero hr0
    have hprevNot : ¬ k ≤ (sample stream s).card :=
      Nat.find_min hex (by
        change s < r
        rw [hrs]
        exact Nat.lt_succ_self s)
    have hprev : (sample stream s).card < k :=
      Nat.lt_of_not_ge hprevNot
    have hupper : (sample stream (s + 1)).card ≤ k :=
      (sample_card_step stream s).trans (Nat.succ_le_iff.mpr hprev)
    rw [hrs] at hrLower hrt
    exact ⟨s + 1, hrt, Nat.le_antisymm hupper hrLower⟩

/-- If every reached size can be crossed exactly, a property that holds
eventually after reaching exact size `d` also holds after reaching any larger
exact size. -/
theorem eventualAtExactSize_mono
    {size : ℕ → ℕ} {good : ℕ → Prop} {d n : ℕ}
    (hcross : ∀ {t k}, k ≤ size t → ∃ r ≤ t, size r = k)
    (hdn : d ≤ n)
    (hgood : ∀ t, size t = d → ∀ s, t ≤ s → good s) :
    ∀ t, size t = n → ∀ s, t ≤ s → good s := by
  intro t ht s hts
  have hdAtT : d ≤ size t := by
    rw [ht]
    exact hdn
  obtain ⟨r, hrt, hr⟩ := hcross hdAtT
  exact hgood r hr s (hrt.trans hts)

theorem sample_card_le (stream : Stream α) (t : ℕ) :
    (sample stream t).card ≤ t := by
  classical
  simpa [sample] using
    (Finset.card_image_le (s := Finset.range t) (f := stream))

theorem mem_language_of_mem_sample_of_presents
    {stream : Stream α} {L : Language α} (hP : Presents stream L)
    {t : ℕ} {x : α} (hx : x ∈ sample stream t) : x ∈ L := by
  rw [← hP]
  obtain ⟨s, -, rfl⟩ := mem_sample_iff.mp hx
  exact ⟨s, rfl⟩

theorem streamIn_of_presents
    {stream : Stream α} {L : Language α} (hP : Presents stream L) :
    StreamIn stream L := by
  intro x hx
  rw [← hP]
  exact hx

theorem eventually_mem_sample_of_presents
    {stream : Stream α} {L : Language α} (hP : Presents stream L)
    {x : α} (hx : x ∈ L) :
    ∃ T, ∀ t, T ≤ t → x ∈ sample stream t := by
  rw [← hP] at hx
  obtain ⟨s, rfl⟩ := hx
  refine ⟨s + 1, ?_⟩
  intro t ht
  exact value_mem_sample (lt_of_lt_of_le (Nat.lt_succ_self s) ht)

theorem finset_eventually_subset_sample
    {stream : Stream α} {L : Language α} (hP : Presents stream L)
    (S : Finset α) (hS : ↑S ⊆ L) :
    ∃ T, S ⊆ sample stream T := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert x S hxS ih =>
      have hxL : x ∈ L := hS (by simp)
      have hSL : (↑S : Set α) ⊆ L := by
        intro y hy
        exact hS (by simp [hy])
      obtain ⟨Tx, hTx⟩ := eventually_mem_sample_of_presents hP hxL
      obtain ⟨TS, hTS⟩ := ih hSL
      refine ⟨max Tx TS, ?_⟩
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact hTx _ (Nat.le_max_left _ _)
      · exact sample_mono (Nat.le_max_right _ _) (hTS hy)

theorem exists_sample_card_ge_of_presents_infinite
    {stream : Stream α} {L : Language α}
    (hP : Presents stream L) (hL : L.Infinite) (d : ℕ) :
    ∃ t, d ≤ (sample stream t).card := by
  classical
  obtain ⟨S, hSL, hcard⟩ := hL.exists_subset_card_eq d
  obtain ⟨T, hST⟩ := finset_eventually_subset_sample hP S hSL
  refine ⟨T, ?_⟩
  rw [← hcard]
  exact Finset.card_le_card hST

/-- An exact presentation of an infinite language passes through every finite
number of distinct observations. -/
theorem exists_sample_card_eq_of_presents_infinite
    {stream : Stream α} {L : Language α}
    (hP : Presents stream L) (hL : L.Infinite) (d : ℕ) :
    ∃ t, (sample stream t).card = d := by
  obtain ⟨t, ht⟩ := exists_sample_card_ge_of_presents_infinite hP hL d
  obtain ⟨r, _, hr⟩ := exists_sample_card_eq_of_le ht
  exact ⟨r, hr⟩

/-- The generated value is a fresh member of `L` at time `t`. -/
@[expose] def CorrectAt
    (G : Generator α) (L : Language α) (stream : Stream α) (t : ℕ) : Prop :=
  output G stream t ∈ L ∧ output G stream t ∉ sample stream t

end GenLimit.Generic
