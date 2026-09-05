/-
Copyright (c) 2026 Yann Pequignot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Pequignot
-/
import LeanPool.NashWilliams.Data.Nat.Nth

/-!
# Nash-Williams Fronts

Fronts are families of finite sets of natural numbers which generalize the families `[M]^k` of
subsets of size `k ∈ ℕ` for infinite subsets `M ⊆ ℕ`. They enjoy a similar combinatorial
property, an infinite Ramsey theorem, which is the main result of this file.

The explicit definition of a front is relative to an infinite set `M ⊆ ℕ`. A family `F` of
finite subsets of `M` is a front if it satisfies:

1. (Base) Either `F = {∅}` or `⋃ F = M`.
2. (Incomparability) For all `s, t ∈ F`, if `s ⊑ t` then `s = t`.
3. (Density) For all `N ∈ [M]^∞` there exists `t ∈ F` such that `t ⊑ N`.

Here `s ⊑ t` is the *initial-segment* (prefix) relation.

## Encoding (enumeration-first)

Everything is represented through increasing enumerations, so a subset of `ℕ` is its strictly
monotone enumeration and the underlying set is recovered as a `range`.

* An infinite subset of `ℕ` is a `StrictMono` map `N : ℕ → ℕ`; its set is `Set.range N`.
* A finite subset is a sorted list `s : List ℕ`; its set is `{x | x ∈ s}`.
* `IsInit s N` says `s` is the initial segment of the sequence `N`, i.e.
  `s = [N 0, N 1, …, N (s.length - 1)]`. This is `⊑` between (the increasing enumeration of) a
  finite set and an infinite set.
* `⊑` between two finite sets is plain `List.IsPrefix` (`<+:`).
* `[M]^∞`, the infinite subsets of `M`, is exactly the subsequences `M ∘ g` for `StrictMono g`.

### Why increasing lists rather than `Finset ℕ`

Front elements are finite subsets, but the whole theory — incomparability, density, the tree of
prefixes and its rank — is phrased in the *initial-segment (prefix) order*, not just in terms of
membership. `List.IsPrefix` carries that order natively, with the full Mathlib API (and matching
`Mathlib.SetTheory.Descriptive.Tree`, whose nodes are likewise `List`s). A `Finset ℕ` has no
intrinsic order, so an initial-segment relation on finsets would have to be reintroduced by
sorting and its API rebuilt from scratch. We therefore encode a finite subset by its strictly
increasing enumeration (a sorted `List ℕ`) and bridge to `Finset ℕ` only at the boundary with
`Finset`-based (e.g. Ramsey) statements, via `Finset.sort` / `List.toFinset`.
-/

open Set List

noncomputable section

namespace List

/-- A prefix keeps the first entry. -/
theorem IsPrefix.head_eq {α : Type*} {s t : List α} (h : s <+: t) (hne : s ≠ []) :
    t.head? = s.head? := by
  obtain ⟨u, rfl⟩ := h
  cases s with
  | nil => exact absurd rfl hne
  | cons a s' => simp

end List

namespace Front

/-- `IsInit s N` : the sorted list `s` is the initial segment of the increasing enumeration
`N : ℕ → ℕ`, i.e. `s = [N 0, N 1, …, N (s.length - 1)]`. This is the prefix relation `⊑`
between a finite set and an infinite set. -/
def IsInit (s : List ℕ) (N : ℕ → ℕ) : Prop :=
  s = (List.range s.length).map N

/-- `List.range` is monotone for the prefix order. -/
theorem range_prefix_range {m n : ℕ} (h : m ≤ n) : List.range m <+: List.range n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.range_add]
  exact List.prefix_append _ _

@[simp] theorem isInit_nil (N : ℕ → ℕ) : IsInit [] N := by simp [IsInit]

/-- The length-`n` initial segment of `N` is an initial segment of `N`. -/
theorem isInit_take (N : ℕ → ℕ) (n : ℕ) : IsInit ((List.range n).map N) N := by
  simp [IsInit]

/-- The `i`-th entry of an initial segment of `N` is `N i`. -/
theorem IsInit.getElem {s : List ℕ} {N : ℕ → ℕ} (hs : IsInit s N)
    {i : ℕ} (h : i < s.length) : s[i] = N i := by
  have hq : s[i]? = some (N i) := by
    conv_lhs => rw [hs]
    simp [h]
  simpa [List.getElem?_eq_getElem h] using hq

/-- The first entry of a nonempty initial segment of `N` is `N 0`. -/
theorem IsInit.head_eq {s : List ℕ} {N : ℕ → ℕ} (hs : IsInit s N) (hne : s ≠ []) :
    s.head? = some (N 0) := by
  have hlen : 0 < s.length := List.length_pos_iff.mpr hne
  obtain ⟨m, hm⟩ : ∃ m, s.length = m + 1 := ⟨s.length - 1, by omega⟩
  rw [hs, hm, List.head?_map, List.range_succ_eq_map]
  simp

/-- An initial segment is determined by its length: two initial segments of `N` of equal length
are equal. -/
theorem IsInit.eq_of_length {s t : List ℕ} {N : ℕ → ℕ}
    (hs : IsInit s N) (ht : IsInit t N) (h : s.length = t.length) : s = t := by
  rw [hs, ht, h]

/-- A prefix of an initial segment of `N` is again an initial segment of `N`. -/
theorem IsInit.isPrefix {s t : List ℕ} {N : ℕ → ℕ} (ht : IsInit t N) (h : s <+: t) :
    IsInit s N := by
  change s = (List.range s.length).map N
  calc s = t.take s.length := List.prefix_iff_eq_take.mp h
    _ = ((List.range t.length).map N).take s.length := by rw [← ht]
    _ = (List.range s.length).map N := by
        rw [← List.map_take, List.take_range, Nat.min_eq_left (by simpa using h.length_le)]

/-- Two initial segments of the same sequence are prefix-comparable. -/
theorem IsInit.prefix_or_prefix {s t : List ℕ} {N : ℕ → ℕ}
    (hs : IsInit s N) (ht : IsInit t N) : s <+: t ∨ t <+: s := by
  rcases le_total s.length t.length with h | h
  · left;  rw [hs, ht]; exact (range_prefix_range h).map N
  · right; rw [hs, ht]; exact (range_prefix_range h).map N

/-- A front relative to an infinite set `M`, given by its increasing enumeration
`M : ℕ → ℕ` (a `StrictMono` map, so `range M` is infinite). `F` is a family of finite sets
(sorted lists) satisfying Base, Incomparability and Density. -/
structure IsFront (F : Set (List ℕ)) (M : ℕ → ℕ) : Prop where
  /-- `M` is the increasing enumeration of an infinite subset of `ℕ`; in particular `range M`
  is infinite. Without this a degenerate `M` (e.g. constant) would vacuously admit "fronts". -/
  mono : StrictMono M
  /-- Every element of `F` is the strictly increasing enumeration of a finite set. -/
  sorted : ∀ s ∈ F, s.Pairwise (· < ·)
  /-- Every element of `F` is a subset of `M`. -/
  subM : ∀ s ∈ F, ∀ x ∈ s, x ∈ Set.range M
  /-- Base: `F = {∅}` or the elements of `F` cover `M`. -/
  base : F = {[]} ∨ (⋃ s ∈ F, {x | x ∈ s}) = Set.range M
  /-- Incomparability: `F` is an antichain for the prefix order. -/
  incomp : ∀ s ∈ F, ∀ t ∈ F, s <+: t → s = t
  /-- Density: every subsequence `M ∘ g` of `M` has an initial segment in `F`. -/
  dense : ∀ g : ℕ → ℕ, StrictMono g → ∃ t ∈ F, IsInit t (M ∘ g)

/-!
## The uniform fronts `[M]^k`

The prototypical fronts: `[M]^k` is the family of size-`k` subsets of `M`, i.e. the strictly
increasing lists of length `k` whose entries lie in `M`.
-/

/-- `[M]^k` : the strictly increasing lists of length `k` contained in `M`. -/
def powK (M : ℕ → ℕ) (k : ℕ) : Set (List ℕ) :=
  {s | s.length = k ∧ s.Pairwise (· < ·) ∧ ∀ x ∈ s, x ∈ Set.range M}

/-- The first `k` values of `M ∘ e` forms a size-`k` subset of `M`, for `e` strictly
monotone. This is the generic member of `[M]^k` used to witness Base and Density. -/
theorem rangeMap_mem_powK {M : ℕ → ℕ} (hM : StrictMono M) {e : ℕ → ℕ}
    (he : StrictMono e) (k : ℕ) : (List.range k).map (M ∘ e) ∈ powK M k := by
  refine ⟨by simp, ?_, ?_⟩
  · rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp fun hab => (hM.comp he) hab
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact ⟨e i, rfl⟩

/-- **`[M]^k` the family of subsets of `M` of size `k` is a front on `M`.** -/
theorem isFront_powK {M : ℕ → ℕ} (hM : StrictMono M) (k : ℕ) : IsFront (powK M k) M where
  mono := hM
  sorted _ hs := hs.2.1
  subM _ hs := hs.2.2
  incomp _ hs _ ht hst := hst.eq_of_length (by rw [hs.1, ht.1])
  dense g hg :=
    ⟨(List.range k).map (M ∘ g), rangeMap_mem_powK hM hg k, isInit_take (M ∘ g) k⟩
  base := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · -- `[M]^0 = {∅}`
      left
      subst hk
      ext s
      simp only [powK, Set.mem_ofPred_eq, Set.mem_singleton_iff, List.length_eq_zero_iff]
      constructor
      · rintro ⟨h, -, -⟩; exact h
      · rintro rfl; exact ⟨rfl, List.Pairwise.nil, by simp⟩
    · -- `k ≥ 1`: the elements of `[M]^k` cover `M`
      right
      ext x
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
      constructor
      · rintro ⟨s, hs, hxs⟩
        exact hs.2.2 x hxs
      · rintro ⟨i, rfl⟩
        refine ⟨(List.range k).map (M ∘ (i + ·)),
          rangeMap_mem_powK hM (add_right_strictMono) k, ?_⟩
        rw [List.mem_map]
        exact ⟨0, List.mem_range.mpr hk, by simp⟩

/-!
## The Schreier front

The Schreier front on `M` consists of the non-empty finite subsets `s ⊆ M` whose size is one
more than the minimal (first) element: `∃ a, s.head? = some a ∧ s.length = a + 1`. It is the
first genuinely non-uniform front — the lists' length varies with where the list starts.
-/

/-- The Schreier front on `M`: increasing lists `s ⊆ M` whose length is one more than their first
element. -/
def schreier (M : ℕ → ℕ) : Set (List ℕ) :=
  {s | (∃ a, s.head? = some a ∧ s.length = a + 1) ∧
    s.Pairwise (· < ·) ∧ ∀ x ∈ s, x ∈ Set.range M}

/-- **The Schreier front is a front on `M`.** -/
theorem isFront_schreier {M : ℕ → ℕ} (hM : StrictMono M) : IsFront (schreier M) M where
  mono := hM
  sorted _ hs := hs.2.1
  subM _ hs := hs.2.2
  incomp s hs t ht hst := by
    obtain ⟨a, hsa, hslen⟩ := hs.1
    obtain ⟨b, htb, htlen⟩ := ht.1
    have hsne : s ≠ [] := by rintro rfl; simp at hsa
    have hth : t.head? = some a := by rw [hst.head_eq hsne]; exact hsa
    have hab : a = b := Option.some.inj (hth.symm.trans htb)
    exact hst.eq_of_length (by rw [hslen, htlen, hab])
  dense g hg := by
    -- the initial segment of `M ∘ g` whose length is `(M ∘ g) 0 + 1`
    refine ⟨(List.range ((M ∘ g) 0 + 1)).map (M ∘ g), ⟨?_, ?_, ?_⟩,
      isInit_take (M ∘ g) _⟩
    · exact ⟨(M ∘ g) 0, (isInit_take (M ∘ g) ((M ∘ g) 0 + 1)).head_eq (by simp), by simp⟩
    · exact (rangeMap_mem_powK hM hg _).2.1
    · exact (rangeMap_mem_powK hM hg _).2.2
  base := by
    right
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨s, hs, hxs⟩
      exact hs.2.2 x hxs
    · rintro ⟨i, rfl⟩
      have he : StrictMono (i + ·) := add_right_strictMono
      refine ⟨(List.range (M i + 1)).map (M ∘ (i + ·)), ⟨?_, ?_, ?_⟩, ?_⟩
      · exact ⟨M i, (isInit_take (M ∘ (i + ·)) (M i + 1)).head_eq (by simp), by simp⟩
      · exact (rangeMap_mem_powK hM he _).2.1
      · exact (rangeMap_mem_powK hM he _).2.2
      · rw [List.mem_map]
        exact ⟨0, List.mem_range.mpr (by omega), by simp⟩

end Front
