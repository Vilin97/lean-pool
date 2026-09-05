/-
Copyright (c) 2026 Yann Pequignot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Pequignot
-/
import LeanPool.NashWilliams.Combinatorics.Front.Rank

/-!
# Restricting a front to an infinite subset

Given a front `F` on `M` and an infinite subset `N ⊆ M`, the restriction `F ↾ N`
(`Front.shrink F N`) keeps the elements of `F` all of whose entries lie in `N`. When `N = M ∘ E`
is an infinite subset of `M` (`E : ℕ → ℕ` strictly monotone), `shrink F N` is a front on `N`.
This is one of the two operations (with the ray, see `Fronts.Ray`) needed for the Nash-Williams
theorem.

`shrink F N` is in fact *the* subfront of `F` living on `N`: every subfront arises this way, i.e.
if `F' ⊆ F` is itself a front on `N`, then `F' = shrink F N`. (This characterization is not
formalized here.)

## Main definitions

* `Front.shrink F N` : the elements of `F` whose entries lie in `range N`.

## Main results

* `Front.shrink_isFront` : `shrink F (M ∘ E)` is a front on `M ∘ E`.
-/

open Set List

noncomputable section

namespace Front

variable {F : Set (List ℕ)} {M : ℕ → ℕ}

/-- The restriction of `F` to the infinite subset enumerated by `N`: the elements of `F` whose
entries all lie in `range N`. -/
def shrink (F : Set (List ℕ)) (N : ℕ → ℕ) : Set (List ℕ) :=
  {s | s ∈ F ∧ ∀ x ∈ s, x ∈ Set.range N}

/-- The restriction of `F` to a set `X` (the survey's `F ↾ X`): the elements of `F` whose entries
all lie in `X`. Definitionally `shrink F N = shrinkOn F (Set.range N)`, so the enumeration-based
`shrink` and this set-based restriction agree on `X = Set.range N`. -/
def shrinkOn (F : Set (List ℕ)) (X : Set ℕ) : Set (List ℕ) :=
  {s | s ∈ F ∧ ∀ x ∈ s, x ∈ X}

theorem shrink_eq_shrinkOn_range (F : Set (List ℕ)) (N : ℕ → ℕ) :
    shrink F N = shrinkOn F (Set.range N) := rfl

/-- **The restriction of a front to an infinite subset is a front on that subset.** For a front
`F` on `M` and the infinite subset `N = M ∘ E` (`E` strictly monotone), `shrink F N` is a front
on `N`. -/
theorem shrink_isFront (hF : IsFront F M) {E : ℕ → ℕ} (hE : StrictMono E) :
    IsFront (shrink F (M ∘ E)) (M ∘ E) where
  mono := hF.mono.comp hE
  sorted s hs := hF.sorted s hs.1
  subM s hs := hs.2
  incomp s hs t ht hst := hF.incomp s hs.1 t ht.1 hst
  dense g hg := by
    obtain ⟨u, hu, hInit⟩ := hF.dense (E ∘ g) (hE.comp hg)
    refine ⟨u, ⟨hu, ?_⟩, hInit⟩
    intro x hx
    rw [hInit, List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact ⟨g i, rfl⟩
  base := by
    by_cases h0 : [] ∈ F
    · -- `F = {[]}`, so `shrink F N = {[]}`
      left
      ext s
      simp only [shrink, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hsF, -⟩
        exact (hF.incomp [] h0 s hsF List.nil_prefix).symm
      · rintro rfl
        exact ⟨h0, by simp⟩
    · -- nontrivial: the elements of `shrink F N` cover `N`
      right
      ext x
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
      constructor
      · rintro ⟨s, hs, hxs⟩
        exact hs.2 x hxs
      · rintro ⟨k, rfl⟩
        have hg : StrictMono (fun x => k + x) := add_right_strictMono
        obtain ⟨u, hu, hInit⟩ := hF.dense (E ∘ (fun x => k + x)) (hE.comp hg)
        have hune : u ≠ [] := fun h => h0 (h ▸ hu)
        have huN : ∀ y ∈ u, y ∈ Set.range (M ∘ E) := by
          intro y hy
          rw [hInit, List.mem_map] at hy
          obtain ⟨i, _, rfl⟩ := hy
          exact ⟨k + i, rfl⟩
        refine ⟨u, ⟨hu, huN⟩, ?_⟩
        have hhead : u.head? = some ((M ∘ E) k) := by rw [hInit.head_eq hune]; simp
        obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp hhead
        rw [hys]; simp

/-! ### Restriction: further lemmas -/

/-- Restricting twice to nested subsets collapses to the inner restriction. -/
theorem shrink_shrink {N N' : ℕ → ℕ} (h : Set.range N' ⊆ Set.range N) :
    shrink (shrink F N) N' = shrink F N' := by
  ext s
  simp only [shrink, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hsF, _⟩, hN'⟩; exact ⟨hsF, hN'⟩
  · rintro ⟨hsF, hN'⟩; exact ⟨⟨hsF, fun x hx => h (hN' x hx)⟩, hN'⟩

/-- The restriction of the uniform front `[M]^k` to an infinite subset `M ∘ e` is the uniform
front `[M ∘ e]^k` on that subset. -/
theorem shrink_powK {e : ℕ → ℕ} (k : ℕ) :
    shrink (powK M k) (M ∘ e) = powK (M ∘ e) k := by
  ext s
  simp only [shrink, powK, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hlen, hp, _⟩, hMe⟩; exact ⟨hlen, hp, hMe⟩
  · rintro ⟨hlen, hp, hMe⟩
    refine ⟨⟨hlen, hp, fun x hx => ?_⟩, hMe⟩
    obtain ⟨i, rfl⟩ := hMe x hx
    exact ⟨e i, rfl⟩

/-- The tree of a restriction is contained in the tree of the front. -/
theorem tree_shrink_subset {N : ℕ → ℕ} : tree (shrink F N) ⊆ tree F := by
  rintro s ⟨u, hu, hpre⟩
  exact ⟨u, hu.1, hpre⟩

/-- **Restriction does not increase rank.** The restriction of a front to an infinite subset has
rank at most that of the front. -/
theorem IsFront.shrink_rank_le (hF : IsFront F M) {E : ℕ → ℕ} (hE : StrictMono E) :
    (shrink_isFront hF hE).rank ≤ hF.rank := by
  have iF : IsWellFounded (List ℕ) (treeExt F) := ⟨hF.wellFounded_treeExt⟩
  have iS : IsWellFounded (List ℕ) (treeExt (shrink F (M ∘ E))) :=
    ⟨(shrink_isFront hF hE).wellFounded_treeExt⟩
  -- The identity is a relation homomorphism `treeExt (shrink F N) →r treeExt F`.
  let φ : treeExt (shrink F (M ∘ E)) →r treeExt F :=
    ⟨id, by
      rintro x y ⟨hx, hy, hyx, hne⟩
      exact ⟨tree_shrink_subset hx, tree_shrink_subset hy, hyx, hne⟩⟩
  change IsWellFounded.rank (treeExt (shrink F (M ∘ E))) [] ≤ IsWellFounded.rank (treeExt F) []
  exact φ.rank_le []

end Front
