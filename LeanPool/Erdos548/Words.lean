/-
Copyright (c) 2026 Tom Adamczewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Adamczewski
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.Finset.Prod
import Mathlib.Data.List.Permutation
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Find

/-!
# Marked words, permutation words and the gluing inequalities

This file is the pure word combinatorics behind the Erdős–Sós theorem; no graph appears in it.

A *marked* word is one whose last letter satisfies a predicate `N`. For families `A`, `B`, `C`
of letter sets with `C ⊆ A` and `A R → B X → C (R ∪ X)` for disjoint `R`, `X`, the exact counting
inequality `marked_word_gluing_count` bounds the marked cuts qualifying for `A` plus those
qualifying for `B` by the ambient allowed cuts plus those qualifying for `C`. It is proved by
rotating the first `A`-and-not-`C` prefix of a cut past the rest of the prefix, an injective
operation into the allowed cuts that do not qualify for `B`.

`permutationWords l` is the finite set of permutations of a repetition-free word `l`, of
cardinality `l.length !`; the marked cuts of `l` are counted by its marked letters
(`marked_prefix_card`), and the allowed cuts are the marked ones plus one empty cut per word
(`allowedWordCuts_card`).

A *full* word `b :: q` has a distinguished first letter `b` (the root image) and a cut in the
remaining word `q`. `fullWordCount` counts the qualifying cuts of all permutation words of a
fixed word `l₀`; `fullWordCount_eq_sum` decomposes it by root, `full_word_gluing_count` lifts
the gluing inequality to full words, and `full_word_transfer_count` bounds one family by another
through the cut-reversal involution `reverseCutPair`, losing at most one first cut per word.
-/

namespace Erdos548

/-! Reversible prefix-block rotation for finite marked-word counting. -/

/-- A nonempty marked last letter. -/
def MarkedEnd {α : Type*} (N : α → Prop) (l : List α) : Prop :=
  ∃ a, l.getLast? = some a ∧ N a

lemma markedEnd_not_nil {α : Type*} {N : α → Prop} {l : List α}
    (h : MarkedEnd N l) : l ≠ [] := by
  rintro rfl
  obtain ⟨a, ha, _⟩ := h
  simp at ha

lemma markedEnd_append_right {α : Type*} {N : α → Prop} {r x : List α}
    (h : MarkedEnd N (r ++ x)) (hx : x ≠ []) : MarkedEnd N x := by
  obtain ⟨a, ha, hN⟩ := h
  have hn : x.getLast? ≠ none := fun he => hx (List.getLast?_eq_none_iff.mp he)
  cases he : x.getLast? with
  | none => exact (hn he).elim
  | some b =>
    rw [List.getLast?_append, he] at ha
    change some b = some a at ha
    have hba := Option.some.inj ha
    subst b
    exact ⟨a, he, hN⟩

/-- The displayed word is the first qualifying prefix of any extension. -/
def FirstPrefix {α : Type*} (P : List α → Prop) (r : List α) : Prop :=
  P r ∧ ∀ j < r.length, ¬P (r.take j)

lemma firstPrefix_unique {α : Type*} {P : List α → Prop} {r y r' y' : List α}
    (hr : FirstPrefix P r) (hr' : FirstPrefix P r') (he : r ++ y = r' ++ y') :
    r = r' ∧ y = y' := by
  have hlen : r.length = r'.length := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · have hh := congrArg (List.take r.length) he
      rw [List.take_left, List.take_append_of_le_length h.le] at hh
      exact hr'.2 r.length h (hh ▸ hr.1)
    · have hh := congrArg (List.take r'.length) he
      rw [List.take_append_of_le_length h.le, List.take_left] at hh
      exact hr.2 r'.length h (hh.symm ▸ hr'.1)
  exact ⟨List.append_inj_left he hlen, List.append_inj_right he hlen⟩

lemma firstPrefix_rotation_injective {α : Type*} {P : List α → Prop}
    {r x y r' x' y' : List α} (hr : FirstPrefix P r) (hr' : FirstPrefix P r')
    (he : (x ++ (r ++ y), x.length) = (x' ++ (r' ++ y'), x'.length)) :
    ((r ++ x) ++ y, r.length + x.length) = ((r' ++ x') ++ y', r'.length + x'.length) := by
  have hword := congrArg Prod.fst he
  have hlen := congrArg Prod.snd he
  have hx : x = x' := List.append_inj_left hword hlen
  have hs : r ++ y = r' ++ y' := List.append_inj_right hword hlen
  obtain ⟨hrEq, hyEq⟩ := firstPrefix_unique hr hr' hs
  subst x'
  subst r'
  subst y'
  rfl

/-- Cut at the first qualifying marked prefix and rotate it past the rest of
an input prefix. Its new prefix is a disjoint difference and hence cannot
belong to the second family. -/
lemma marked_prefix_rotation_exists {α : Type*} [DecidableEq α]
    (N : α → Prop) (A B C : Finset α → Prop)
    (hglue : ∀ R X, Disjoint R X → A R → B X → C (R ∪ X))
    (l : List α) (hl : l.Nodup) (k : ℕ) (hk : k ≤ l.length)
    (hm : MarkedEnd N (l.take k)) (hA : A (l.take k).toFinset)
    (hC : ¬C (l.take k).toFinset) :
    ∃ r x y : List α,
      l = (r ++ x) ++ y ∧ k = r.length + x.length ∧
      FirstPrefix (fun q => MarkedEnd N q ∧ A q.toFinset ∧ ¬C q.toFinset) r ∧
      (x = [] ∨ MarkedEnd N x) ∧ ¬B x.toFinset := by
  classical
  let P : List α → Prop := fun q => MarkedEnd N q ∧ A q.toFinset ∧ ¬C q.toFinset
  have hex : ∃ j, j ≤ k ∧ P (l.take j) := ⟨k, le_rfl, hm, hA, hC⟩
  let j := Nat.find hex
  have hjk : j ≤ k := (Nat.find_spec hex).1
  have hjP : P (l.take j) := (Nat.find_spec hex).2
  let r := l.take j
  let x := (l.drop j).take (k - j)
  let y := l.drop k
  have hrlen : r.length = j := by simp only [r, List.length_take]; omega
  have hxlen : x.length = k - j := by
    simp only [x, List.length_take, List.length_drop]
    omega
  have hrx : r ++ x = l.take k := by
    dsimp only [r, x]
    rw [← List.take_add]
    congr 1
    omega
  have hword : (r ++ x) ++ y = l := by
    rw [hrx]
    exact List.take_append_drop k l
  refine ⟨r, x, y, hword.symm, by omega, ⟨hjP, ?_⟩, ?_, ?_⟩
  · intro i hi hPi
    have hij : i < j := by omega
    have hp : P (l.take i) := by
      simpa only [r, List.take_take, Nat.min_eq_left hij.le] using hPi
    exact Nat.find_min hex hij ⟨by omega, hp⟩
  · by_cases hx : x = []
    · exact Or.inl hx
    · exact Or.inr (markedEnd_append_right (hrx.symm ▸ hm) hx)
  · intro hB
    have hnr : (r ++ x).Nodup := hrx.symm ▸ hl.sublist (List.take_sublist k l)
    have hd : Disjoint r.toFinset x.toFinset := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (List.disjoint_left.mp hnr.disjoint) (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb)
    have hh := hglue r.toFinset x.toFinset hd hjP.2.1 hB
    apply hC
    rwa [← List.toFinset_append, hrx] at hh

/-- The relation records the reversible block rotation, without choosing a
particular implementation of the first-prefix search. -/
def PrefixRotation {α : Type*} (P : List α → Prop)
    (u v : List α × ℕ) : Prop :=
  ∃ r x y : List α, u = ((r ++ x) ++ y, r.length + x.length) ∧
    v = (x ++ (r ++ y), x.length) ∧ FirstPrefix P r

lemma prefixRotation_left_unique {α : Type*} {P : List α → Prop}
    {u u' v : List α × ℕ} (h : PrefixRotation P u v) (h' : PrefixRotation P u' v) : u = u' := by
  obtain ⟨r, x, y, rfl, hv, hr⟩ := h
  obtain ⟨r', x', y', rfl, hv', hr'⟩ := h'
  exact firstPrefix_rotation_injective hr hr' (hv.symm.trans hv')

/-- All cuts `(l, k)` of words `l ∈ W` with `k ≤ m`, where the cut is either empty or ends at a
marked letter. This is the ambient family the gluing inequality is counted against. -/
noncomputable def allowedWordCuts {α : Type*} (W : Finset (List α)) (m : ℕ)
    (N : α → Prop) : Finset (List α × ℕ) := by
  classical
  exact (W ×ˢ Finset.range (m + 1)).filter (fun p => p.2 = 0 ∨ MarkedEnd N (p.1.take p.2))

/-- Cuts `(l, k)` of words `l ∈ W` with `k ≤ m` whose prefix ends at a marked letter and whose
letter set satisfies `A`. -/
noncomputable def goodWordCuts {α : Type*} [DecidableEq α]
    (W : Finset (List α)) (m : ℕ) (N : α → Prop) (A : Finset α → Prop) :
    Finset (List α × ℕ) := by
  classical
  exact (W ×ˢ Finset.range (m + 1)).filter
    (fun p => MarkedEnd N (p.1.take p.2) ∧ A (p.1.take p.2).toFinset)

lemma goodWordCuts_subset_allowed {α : Type*} [DecidableEq α]
    (W : Finset (List α)) (m : ℕ) (N : α → Prop) (A : Finset α → Prop) :
    goodWordCuts W m N A ⊆ allowedWordCuts W m N := by
  classical
  intro p hp
  obtain ⟨hp, hm, _⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hp, Or.inr hm⟩

lemma goodWordCuts_mono {α : Type*} [DecidableEq α]
    (W : Finset (List α)) (m : ℕ) (N : α → Prop) (A C : Finset α → Prop)
    (hCA : ∀ X, C X → A X) : goodWordCuts W m N C ⊆ goodWordCuts W m N A := by
  classical
  intro p hp
  obtain ⟨hp, hm, hC⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hp, hm, hCA _ hC⟩

/-- The exact finite marked-word gluing inequality. The ambient word family
must be closed under permutation; every word is repetition-free. -/
lemma marked_word_gluing_count {α : Type*} [DecidableEq α]
    (W : Finset (List α)) (m : ℕ) (N : α → Prop) (A B C : Finset α → Prop)
    (hlen : ∀ l ∈ W, l.length = m) (hnodup : ∀ l ∈ W, l.Nodup)
    (hperm : ∀ l ∈ W, ∀ l', l'.Perm l → l' ∈ W)
    (hCA : ∀ X, C X → A X)
    (hglue : ∀ R X, Disjoint R X → A R → B X → C (R ∪ X)) :
    (goodWordCuts W m N A).card + (goodWordCuts W m N B).card ≤
      (allowedWordCuts W m N).card + (goodWordCuts W m N C).card := by
  classical
  let D := goodWordCuts W m N A \ goodWordCuts W m N C
  let E := allowedWordCuts W m N \ goodWordCuts W m N B
  let P : List α → Prop := fun q => MarkedEnd N q ∧ A q.toFinset ∧ ¬C q.toFinset
  have hex : ∀ u : ↥D, ∃ v : ↥E, PrefixRotation P u.val v.val := by
    rintro ⟨⟨l, k⟩, hu⟩
    obtain ⟨huA, huC⟩ := Finset.mem_sdiff.mp hu
    obtain ⟨hbase, hm, hA⟩ := Finset.mem_filter.mp huA
    obtain ⟨hlW, hkr⟩ := Finset.mem_product.mp hbase
    have hlm := hlen l hlW
    have hk : k ≤ l.length := by have := Finset.mem_range.mp hkr; omega
    have hC : ¬C (l.take k).toFinset := by
      intro hc
      exact huC (Finset.mem_filter.mpr ⟨hbase, hm, hc⟩)
    obtain ⟨r, x, y, hword, hcut, hr, hx, hBx⟩ :=
      marked_prefix_rotation_exists N A B C hglue l (hnodup l hlW) k hk hm hA hC
    let q := x ++ (r ++ y)
    have hqperm : q.Perm l := by
      rw [hword]
      simpa only [q, List.append_assoc] using
        (List.perm_append_comm (l₁:=x) (l₂:=r)).append_right y
    have hqW : q ∈ W := hperm l hlW q hqperm
    have hqLen : q.length = m := (List.Perm.length_eq hqperm).trans hlm
    have hxle : x.length ≤ m := by simp only [q, List.length_append] at hqLen; omega
    have htake : q.take x.length = x := List.take_left
    have hqBase : (q, x.length) ∈ W ×ˢ Finset.range (m + 1) :=
      Finset.mem_product.mpr ⟨hqW, Finset.mem_range.mpr (by omega)⟩
    have hqAllowed : (q, x.length) ∈ allowedWordCuts W m N := by
      apply Finset.mem_filter.mpr
      refine ⟨hqBase, ?_⟩
      rcases hx with hx | hx
      · exact Or.inl (hx ▸ rfl)
      · exact Or.inr (htake.symm ▸ hx)
    have hqNot : (q, x.length) ∉ goodWordCuts W m N B := by
      intro hh
      have hb := (Finset.mem_filter.mp hh).2.2
      rw [htake] at hb
      exact hBx hb
    refine ⟨⟨(q, x.length), Finset.mem_sdiff.mpr ⟨hqAllowed, hqNot⟩⟩, r, x, y, ?_, rfl, hr⟩
    exact Prod.ext hword hcut
  choose f hf using hex
  have hi : Function.Injective f := by
    intro u u' he
    apply Subtype.ext
    apply prefixRotation_left_unique (hf u)
    rw [he]
    exact hf u'
  have hcard : D.card ≤ E.card := Finset.card_le_card_of_injective hi
  have hAC := Finset.card_sdiff_add_card_eq_card (goodWordCuts_mono W m N A C hCA)
  have hBE := Finset.card_sdiff_add_card_eq_card (goodWordCuts_subset_allowed W m N B)
  change (goodWordCuts W m N A \ goodWordCuts W m N C).card ≤
    (allowedWordCuts W m N \ goodWordCuts W m N B).card at hcard
  omega

/-! Exact cardinalities of permutation words and marked prefixes. -/

section

attribute [local instance] Classical.propDecidable

/-- The finite set of all words that are permutations of `l`. -/
noncomputable def permutationWords {α : Type*} [DecidableEq α] (l : List α) :
    Finset (List α) := l.permutations.toFinset

lemma mem_permutationWords {α : Type*} [DecidableEq α] (l q : List α) :
    q ∈ permutationWords l ↔ q.Perm l := by
  simp only [permutationWords, List.mem_toFinset, List.mem_permutations]

lemma permutationWords_card {α : Type*} [DecidableEq α] (l : List α) (hl : l.Nodup) :
    (permutationWords l).card = l.length.factorial := by
  rw [permutationWords, List.toFinset_card_of_nodup (List.nodup_permutations l hl),
    List.length_permutations]

lemma markedEnd_take_succ {α : Type*} (N : α → Prop) (l : List α) (i : ℕ)
    (hi : i < l.length) : MarkedEnd N (l.take (i + 1)) ↔ N l[i] := by
  rw [List.take_succ_eq_append_getElem hi]
  simp only [MarkedEnd, List.getLast?_concat, Option.some.injEq]
  constructor
  · rintro ⟨a, he, ha⟩
    exact he.symm ▸ ha
  · intro h
    exact ⟨l[i], rfl, h⟩

lemma markedEnd_take_pos {α : Type*} {N : α → Prop} {l : List α} {k : ℕ}
    (h : MarkedEnd N (l.take k)) : 0 < k := by
  by_contra hn
  have hk : k = 0 := by omega
  rw [hk, List.take_zero] at h
  exact markedEnd_not_nil h rfl

lemma markedEnd_take_iff {α : Type*} (N : α → Prop) (l : List α) (k : ℕ)
    (hk : k ≤ l.length) :
    MarkedEnd N (l.take k) ↔ ∃ h : 0 < k, N (l[k - 1]'(by omega)) := by
  constructor
  · intro h
    have hp := markedEnd_take_pos h
    refine ⟨hp, ?_⟩
    have hh := (markedEnd_take_succ N l (k - 1) (by omega)).mp
      (show MarkedEnd N (l.take ((k - 1) + 1)) from by simpa only [Nat.sub_add_cancel hp] using h)
    exact hh
  · rintro ⟨hp, h⟩
    have hh := (markedEnd_take_succ N l (k - 1) (by omega)).mpr h
    simpa only [Nat.sub_add_cancel hp] using hh

lemma marked_prefix_card {α : Type*} [DecidableEq α] (N : α → Prop)
    (l : List α) (hl : l.Nodup) :
    (Finset.filter (fun k => MarkedEnd N (l.take k)) (Finset.range (l.length + 1))).card =
      (l.toFinset.filter N).card := by
  classical
  let F := Finset.filter (fun k => MarkedEnd N (l.take k)) (Finset.range (l.length + 1))
  have hk : ∀ k ∈ F, k ≤ l.length := by
    intro k hk
    exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
  have hp : ∀ k ∈ F, 0 < k := fun k hk => markedEnd_take_pos (Finset.mem_filter.mp hk).2
  let f : (k : ℕ) → k ∈ F → α := fun k h => l[k - 1]'(by have := hk k h; have := hp k h; omega)
  apply Finset.card_bij f
  · intro k h
    refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (List.getElem_mem _), ?_⟩
    exact ((markedEnd_take_iff N l k (hk k h)).mp (Finset.mem_filter.mp h).2).2
  · intro k h j hj he
    have hh : k - 1 = j - 1 := hl.getElem_inj_iff.mp he
    have := hp k h
    have := hp j hj
    omega
  · intro a ha
    obtain ⟨haL, haN⟩ := Finset.mem_filter.mp ha
    obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp haL)
    have hm : MarkedEnd N (l.take (i + 1)) := (markedEnd_take_succ N l i hi).mpr (hia.symm ▸ haN)
    have hF : i + 1 ∈ F := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), hm⟩
    refine ⟨i + 1, hF, ?_⟩
    simpa only [f, Nat.add_sub_cancel] using hia

lemma goodWordCuts_true_card {α : Type*} [DecidableEq α]
    (W : Finset (List α)) (m : ℕ) (N : α → Prop)
    (hlen : ∀ l ∈ W, l.length = m) (hnodup : ∀ l ∈ W, l.Nodup) :
    (goodWordCuts W m N (fun _ => True)).card =
      ∑ l ∈ W, (l.toFinset.filter N).card := by
  classical
  unfold goodWordCuts
  rw [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [and_true]
  rw [← Finset.card_filter, ← hlen l hl, marked_prefix_card N l (hnodup l hl)]

lemma allowedWordCuts_card {α : Type*} [DecidableEq α]
    (W : Finset (List α)) (m : ℕ) (N : α → Prop) :
    (allowedWordCuts W m N).card = W.card + (goodWordCuts W m N (fun _ => True)).card := by
  classical
  let E := W.image (fun l => (l, 0))
  have hdis : Disjoint E (goodWordCuts W m N (fun _ => True)) := by
    apply Finset.disjoint_left.mpr
    rintro p hp hgood
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hp
    simp only [goodWordCuts, Finset.mem_filter] at hgood
    have hm := hgood.2.1
    simp only [List.take_zero] at hm
    exact markedEnd_not_nil hm rfl
  have he : allowedWordCuts W m N = E ∪ goodWordCuts W m N (fun _ => True) := by
    ext p
    simp only [allowedWordCuts, goodWordCuts, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range, Finset.mem_union, and_true]
    constructor
    · rintro ⟨⟨hl, hk⟩, he | hm⟩
      · exact Or.inl (Finset.mem_image.mpr ⟨p.1, hl, Prod.ext rfl he.symm⟩)
      · exact Or.inr ⟨⟨hl, hk⟩, hm⟩
    · rintro (hp | hp)
      · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
        exact ⟨⟨hl, by omega⟩, Or.inl rfl⟩
      · exact ⟨hp.1, Or.inr hp.2⟩
  rw [he, Finset.card_union_of_disjoint hdis]
  congr 1
  exact Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)

end

/-! Full permutation words, grouped by their first letter, and the cut-reversal involution. -/

section

attribute [local instance] Classical.propDecidable

/-- The first letter is a distinguished root, and a marked cut is taken in
the remaining word. The family is allowed to depend on that root. -/
def FullWordQualifies {α : Type*} [DecidableEq α]
    (N : α → α → Prop) (A : α → Finset α → Prop) (l : List α) (k : ℕ) : Prop :=
  ∃ b q, l = b::q ∧ MarkedEnd (N b) (q.take k) ∧ A b (q.take k).toFinset

lemma fullWordQualifies_cons {α : Type*} [DecidableEq α]
    (N : α → α → Prop) (A : α → Finset α → Prop) (b : α) (q : List α) (k : ℕ) :
    FullWordQualifies N A (b::q) k ↔
      MarkedEnd (N b) (q.take k) ∧ A b (q.take k).toFinset := by
  constructor
  · rintro ⟨b', q', he, hm, hA⟩
    obtain ⟨rfl, rfl⟩ := List.cons.inj he
    exact ⟨hm, hA⟩
  · rintro ⟨hm, hA⟩
    exact ⟨b, q, rfl, hm, hA⟩

/-- Full permutation words of `l₀` with a cut position, restricted to the qualifying ones. -/
noncomputable def fullGoodWordCuts {α : Type*} [DecidableEq α]
    (l₀ : List α) (N : α → α → Prop) (A : α → Finset α → Prop) : Finset (List α × ℕ) :=
  (permutationWords l₀ ×ˢ Finset.range l₀.length).filter
    (fun p => FullWordQualifies N A p.1 p.2)

/-- The number of qualifying cut permutation words of `l₀`. -/
noncomputable def fullWordCount {α : Type*} [DecidableEq α]
    (l₀ : List α) (N : α → α → Prop) (A : α → Finset α → Prop) : ℕ :=
  (fullGoodWordCuts l₀ N A).card

lemma mem_fullGoodWordCuts {α : Type*} [DecidableEq α]
    (l₀ : List α) (N : α → α → Prop) (A : α → Finset α → Prop) (l : List α) (k : ℕ) :
    (l, k) ∈ fullGoodWordCuts l₀ N A ↔ l.Perm l₀ ∧ k < l₀.length ∧ FullWordQualifies N A l k := by
  simp only [fullGoodWordCuts, Finset.mem_filter, Finset.mem_product, mem_permutationWords,
    Finset.mem_range, and_assoc]

lemma fullWordCount_eq_sum {α : Type*} [DecidableEq α]
    (l₀ : List α) (N : α → α → Prop) (A : α → Finset α → Prop) :
    fullWordCount l₀ N A = ∑ b ∈ l₀.toFinset,
      (goodWordCuts (permutationWords (l₀.erase b)) (l₀.length - 1) (N b) (A b)).card := by
  classical
  let F := fun b => goodWordCuts (permutationWords (l₀.erase b)) (l₀.length - 1) (N b) (A b)
  let E := fun b => (F b).image (fun p => (b::p.1, p.2))
  have he : fullGoodWordCuts l₀ N A = l₀.toFinset.biUnion E := by
    ext p
    rcases p with ⟨l, k⟩
    rw [mem_fullGoodWordCuts, Finset.mem_biUnion]
    constructor
    · rintro ⟨hl, hk, b, q, rfl, hm, hA⟩
      obtain ⟨hb, hq⟩ := List.cons_perm_iff_perm_erase.mp hl
      refine ⟨b, List.mem_toFinset.mpr hb, Finset.mem_image.mpr ⟨(q, k), ?_, rfl⟩⟩
      have hn : 0 < l₀.length := by have := List.length_pos_of_mem hb; omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨(mem_permutationWords _ _).mpr hq, Finset.mem_range.mpr (by omega)⟩, hm, hA⟩
    · rintro ⟨b, hb, hp⟩
      obtain ⟨⟨q, j⟩, hq, heq⟩ := Finset.mem_image.mp hp
      have hword : b::q = l := congrArg Prod.fst heq
      have hj : j = k := congrArg Prod.snd heq
      subst l
      subst j
      obtain ⟨hbase, hm, hA⟩ := Finset.mem_filter.mp hq
      obtain ⟨hq, hk⟩ := Finset.mem_product.mp hbase
      have hbL := List.mem_toFinset.mp hb
      have hn := List.length_pos_of_mem hbL
      refine ⟨List.cons_perm_iff_perm_erase.mpr ⟨hbL, (mem_permutationWords _ _).mp hq⟩,
        by have := Finset.mem_range.mp hk; omega, b, q, rfl, hm, hA⟩
  have hd : (l₀.toFinset : Set α).PairwiseDisjoint E := by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    rintro p hp hq
    obtain ⟨⟨q, k⟩, _, he₁⟩ := Finset.mem_image.mp hp
    obtain ⟨⟨r, j⟩, _, he₂⟩ := Finset.mem_image.mp hq
    have hword := congrArg Prod.fst (he₁.trans he₂.symm)
    exact hbc (List.cons.inj hword).1
  unfold fullWordCount
  rw [he, Finset.card_biUnion hd]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.card_image_of_injective
  rintro ⟨q, k⟩ ⟨r, j⟩ h
  have hq := (List.cons.inj (congrArg Prod.fst h)).2
  have hk : k = j := congrArg Prod.snd h
  exact Prod.ext hq hk

/-- Sum of the numbers of outer words: exactly one full word for every
choice of its head and its outer permutation. -/
lemma sum_outer_words_card {α : Type*} [DecidableEq α] (l₀ : List α) (hl : l₀.Nodup)
    (hne : l₀ ≠ []) :
    (∑ b ∈ l₀.toFinset, (permutationWords (l₀.erase b)).card) = (permutationWords l₀).card := by
  classical
  have hn : 0 < l₀.length := List.length_pos_iff.mpr hne
  have he : ∀ b ∈ l₀.toFinset,
      (permutationWords (l₀.erase b)).card = (l₀.length - 1).factorial := by
    intro b hb
    rw [permutationWords_card _ (hl.erase b), List.length_erase_of_mem (List.mem_toFinset.mp hb)]
  rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_const, nsmul_eq_mul, List.toFinset_card_of_nodup hl,
    permutationWords_card l₀ hl, Nat.cast_id]
  simpa only [Nat.sub_add_cancel hn] using (Nat.factorial_succ (l₀.length - 1)).symm

/-- Root-dependent gluing, summed over ALL full permutation words. -/
lemma full_word_gluing_count {α : Type*} [DecidableEq α]
    (l₀ : List α) (hl : l₀.Nodup) (hne : l₀ ≠ [])
    (N : α → α → Prop) (A B C : α → Finset α → Prop)
    (hCA : ∀ b X, C b X → A b X)
    (hglue : ∀ b R X, Disjoint R X → A b R → B b X → C b (R ∪ X)) :
    fullWordCount l₀ N A + fullWordCount l₀ N B ≤
      fullWordCount l₀ N (fun _ _ => True) + (permutationWords l₀).card + fullWordCount l₀ N C := by
  classical
  have hh : ∀ b ∈ l₀.toFinset,
      (goodWordCuts (permutationWords (l₀.erase b)) (l₀.length - 1) (N b) (A b)).card +
        (goodWordCuts (permutationWords (l₀.erase b)) (l₀.length - 1) (N b) (B b)).card ≤
      (goodWordCuts (permutationWords (l₀.erase b)) (l₀.length - 1) (N b) (fun _ => True)).card +
        (permutationWords (l₀.erase b)).card +
        (goodWordCuts (permutationWords (l₀.erase b)) (l₀.length - 1) (N b) (C b)).card := by
    intro b hb
    have he := marked_word_gluing_count (permutationWords (l₀.erase b)) (l₀.length - 1) (N b)
      (A b) (B b) (C b)
      (fun q hq => ((mem_permutationWords _ _).mp hq).length_eq.trans
        (List.length_erase_of_mem (List.mem_toFinset.mp hb)))
      (fun q hq => ((mem_permutationWords _ _).mp hq).nodup_iff.mpr (hl.erase b))
      (fun q hq q' hp => (mem_permutationWords _ _).mpr
        (hp.trans ((mem_permutationWords _ _).mp hq))) (hCA b) (hglue b)
    rw [allowedWordCuts_card] at he
    omega
  have hs := Finset.sum_le_sum hh
  simp only [Finset.sum_add_distrib] at hs
  rw [sum_outer_words_card l₀ hl hne] at hs
  simpa only [fullWordCount_eq_sum] using hs

/-- Reverse the first `c` letters of a word and, separately, the remaining letters. -/
def reverseWordAt {α : Type*} (l : List α) (c : ℕ) : List α :=
  (l.take c).reverse ++ (l.drop c).reverse

lemma reverseWordAt_perm {α : Type*} (l : List α) (c : ℕ) : (reverseWordAt l c).Perm l := by
  have h := (List.reverse_perm (l.take c)).append (List.reverse_perm (l.drop c))
  simpa only [reverseWordAt, List.take_append_drop] using h

lemma reverseWordAt_involutive {α : Type*} (l : List α) (c : ℕ) :
    reverseWordAt (reverseWordAt l c) c = l := by
  by_cases hc : c ≤ l.length
  · have hrlen : (l.take c).reverse.length = c := by
      simp only [List.length_reverse, List.length_take]; omega
    have ht : (reverseWordAt l c).take c = (l.take c).reverse := by
      simpa only [reverseWordAt, hrlen] using
        (List.take_left (l₁:=(l.take c).reverse) (l₂:=(l.drop c).reverse))
    have hd : (reverseWordAt l c).drop c = (l.drop c).reverse := by
      simpa only [reverseWordAt, hrlen] using
        (List.drop_left (l₁:=(l.take c).reverse) (l₂:=(l.drop c).reverse))
    rw [reverseWordAt, ht, hd, List.reverse_reverse, List.reverse_reverse, List.take_append_drop]
  · have hlc : l.length ≤ c := by omega
    have he : reverseWordAt l c = l.reverse := by
      simp [reverseWordAt, List.take_of_length_le hlc, List.drop_eq_nil_of_le hlc]
    have hrc : l.reverse.length ≤ c := by simpa using hlc
    rw [he]
    simp [reverseWordAt, List.take_of_length_le hrc, List.drop_eq_nil_of_le hrc]

/-- The cut-reversal involution on words with a cut position. -/
def reverseCutPair {α : Type*} (p : List α × ℕ) : List α × ℕ :=
  (reverseWordAt p.1 (p.2 + 1), p.2)

lemma reverseCutPair_involutive {α : Type*} : Function.Involutive (@reverseCutPair α) := by
  rintro ⟨l, k⟩
  exact Prod.ext (reverseWordAt_involutive l (k + 1)) rfl

lemma reverseCutPair_injective {α : Type*} : Function.Injective (@reverseCutPair α) :=
  reverseCutPair_involutive.injective

lemma reverseWordAt_decomposition {α : Type*} (b w : α) (p q : List α) :
    reverseWordAt (b::(p ++ w::q)) (p.length + 2) = w::(p.reverse ++ b::q.reverse) := by
  have he : b::(p ++ w::q) = (b::(p ++ [w])) ++ q := by
    simp only [List.cons_append, List.append_assoc, List.nil_append]
  have hlen : (b::(p ++ [w])).length = p.length + 2 := by simp
  rw [he, ← hlen, reverseWordAt, List.take_left, List.drop_left]
  simp only [List.reverse_cons, List.reverse_append, List.cons_append,
    List.nil_append, List.append_assoc, List.reverse_nil]

/-- A first-state loss of at most one per full word, followed by the cut
reversal involution. This is purely finite counting. -/
lemma full_word_transfer_count {α : Type*} [DecidableEq α]
    (l₀ : List α) (N N' : α → α → Prop) (A B : α → Finset α → Prop)
    (hstep : ∀ l, l.Perm l₀ → ∀ k, k < l₀.length → FullWordQualifies N A l k →
      ∀ j, j < k → FullWordQualifies N A l j →
        FullWordQualifies N' B (reverseWordAt l (k + 1)) k) :
    fullWordCount l₀ N A ≤ fullWordCount l₀ N' B + (permutationWords l₀).card := by
  classical
  let D := fullGoodWordCuts l₀ N A
  let M := D.filter (fun p => ∃ j, j < p.2 ∧ FullWordQualifies N A p.1 j)
  have hMD : M ⊆ D := Finset.filter_subset _ _
  have hfirst : (D \ M).card ≤ (permutationWords l₀).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      have hpD := (Finset.mem_sdiff.mp hp).1
      exact (mem_permutationWords _ _).mpr ((mem_fullGoodWordCuts l₀ N A p.1 p.2).mp hpD).1
    · intro p hp q hq he
      have hpD := (mem_fullGoodWordCuts l₀ N A p.1 p.2).mp (Finset.mem_sdiff.mp hp).1
      have hqD := (mem_fullGoodWordCuts l₀ N A q.1 q.2).mp (Finset.mem_sdiff.mp hq).1
      apply Prod.ext he
      by_contra hn
      rcases lt_or_gt_of_ne hn with h | h
      · apply (Finset.mem_sdiff.mp hq).2
        exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hq).1,
          p.2, h, he ▸ hpD.2.2⟩
      · apply (Finset.mem_sdiff.mp hp).2
        exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hp).1,
          q.2, h, he.symm ▸ hqD.2.2⟩
  have hmove : M.card ≤ (fullGoodWordCuts l₀ N' B).card := by
    apply Finset.card_le_card_of_injOn reverseCutPair
    · rintro ⟨l, k⟩ hp
      obtain ⟨hpD, j, hjk, hj⟩ := Finset.mem_filter.mp hp
      obtain ⟨hl, hk, hs⟩ := (mem_fullGoodWordCuts l₀ N A l k).mp hpD
      exact (mem_fullGoodWordCuts l₀ N' B _ _).mpr
        ⟨(reverseWordAt_perm l (k + 1)).trans hl, hk, hstep l hl k hk hs j hjk hj⟩
    · exact fun _ _ _ _ h => reverseCutPair_injective h
  have he := Finset.card_sdiff_add_card_eq_card hMD
  change D.card ≤ (fullGoodWordCuts l₀ N' B).card + (permutationWords l₀).card
  omega

end

end Erdos548
