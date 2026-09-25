/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ChainLists

/-!
# Concatenation sign factorisation

The global key-sortSign of the concatenated pair enumeration equals
the product of the per-block key-sortSigns: key ranges of distinct
blocks are disjoint and ordered, so concatenation adds no inversions.
-/

namespace RS

open Finset

variable {k ℓ : ℕ}

/-! ## Cross-block key monotonicity -/

/-- Keys from an earlier block are strictly less than keys from a
later block. -/
theorem blockSigmaEquiv_lt_of_block_lt :
    ∀ {ds : List ℕ} {v₁ v₂ : Fin ds.length}
      (_ : v₁ < v₂) (j₁ : Fin (ds.get v₁)) (j₂ : Fin (ds.get v₂)),
      blockSigmaEquiv ds ⟨v₁, j₁⟩ < blockSigmaEquiv ds ⟨v₂, j₂⟩
  | [], v₁, _, _, _, _ => v₁.elim0
  | d :: ds, v₁, v₂, hlt, j₁, j₂ => by
    match v₁, v₂ with
    | ⟨0, hv₁⟩, ⟨0, hv₂⟩ =>
      exact absurd hlt (lt_irrefl _)
    | ⟨0, hv₁⟩, ⟨w₂ + 1, hv₂⟩ =>
      rw [Fin.lt_def]
      have h1 : (blockSigmaEquiv (d :: ds) ⟨⟨0, hv₁⟩, j₁⟩).val =
          j₁.val := rfl
      have hw₂ : w₂ < ds.length := by
        simp only [List.length_cons] at hv₂; omega
      have h2 : (blockSigmaEquiv (d :: ds) ⟨⟨w₂ + 1, hv₂⟩, j₂⟩).val =
          d + (blockSigmaEquiv ds ⟨⟨w₂, hw₂⟩, j₂⟩).val := rfl
      rw [h1, h2]
      have hj₁ : j₁.val < d := j₁.isLt
      omega
    | ⟨w₁ + 1, hv₁⟩, ⟨0, hv₂⟩ =>
      simp only [Fin.lt_def] at hlt
      omega
    | ⟨w₁ + 1, hv₁⟩, ⟨w₂ + 1, hv₂⟩ =>
      have hw₁ : w₁ < ds.length := by
        simp only [List.length_cons] at hv₁; omega
      have hw₂ : w₂ < ds.length := by
        simp only [List.length_cons] at hv₂; omega
      have hlt' : (⟨w₁, hw₁⟩ : Fin ds.length) < ⟨w₂, hw₂⟩ := by
        simp only [Fin.lt_def] at hlt ⊢; omega
      have hrec := blockSigmaEquiv_lt_of_block_lt hlt' j₁ j₂
      rw [Fin.lt_def]
      have h1 : (blockSigmaEquiv (d :: ds) ⟨⟨w₁ + 1, hv₁⟩, j₁⟩).val =
          d + (blockSigmaEquiv ds ⟨⟨w₁, hw₁⟩, j₁⟩).val := rfl
      have h2 : (blockSigmaEquiv (d :: ds) ⟨⟨w₂ + 1, hv₂⟩, j₂⟩).val =
          d + (blockSigmaEquiv ds ⟨⟨w₂, hw₂⟩, j₂⟩).val := rfl
      rw [h1, h2]
      rw [Fin.lt_def] at hrec
      omega

/-! ## Inversions under ordered append -/

/-- Appending two lists whose elements are in order adds no
inversions. -/
theorem inversions_append_of_le {α : Type} [LinearOrder α] :
    ∀ (l₁ l₂ : List α)
      (_ : ∀ x ∈ l₁, ∀ y ∈ l₂, x ≤ y),
      inversions (l₁ ++ l₂) = inversions l₁ + inversions l₂
  | [], l₂, _ => by simp [inversions]
  | a :: l₁, l₂, h => by
    rw [List.cons_append, inversions, inversions]
    have hrec := inversions_append_of_le l₁ l₂ (fun x hx y hy =>
      h x (List.mem_cons_of_mem a hx) y hy)
    rw [hrec]
    -- the filter over l₁ ++ l₂ splits as filter over l₁ + filter over l₂
    have hfilt : (l₁ ++ l₂).filter (fun b => decide (b < a)) =
        l₁.filter (fun b => decide (b < a)) ++
        l₂.filter (fun b => decide (b < a)) := by
      exact List.filter_append l₁ l₂
    rw [hfilt, List.length_append]
    -- the l₂ part of the filter is empty
    have hempty : l₂.filter (fun b => decide (b < a)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b hb
      simp only [decide_eq_true_eq]
      exact not_lt.mpr (h a (List.mem_cons.mpr (Or.inl rfl)) b hb)
    rw [hempty, List.length_nil]
    omega

/-- The sortSign is multiplicative under ordered append. -/
theorem sortSign_append_of_le {α : Type} [LinearOrder α]
    (l₁ l₂ : List α)
    (h : ∀ x ∈ l₁, ∀ y ∈ l₂, x ≤ y) :
    sortSign (l₁ ++ l₂) = sortSign l₁ * sortSign l₂ := by
  rw [sortSign, inversions_append_of_le l₁ l₂ h, pow_add]
  rfl

/-! ## Key membership in blocks -/

/-- A pair-flag at block v has its key in that block's sigma range. -/
theorem sortKey_mem_block (W : ClosedFragment) (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (v : Fin (ds W).length)
    (f : {f : W.Flag // f ∈ F.flags})
    (hf : f ∈ pairFlagList (F := F) o (blockVertex W v)) :
    ∃ j : Fin ((ds W).get v),
      sortKey W f.val = blockSigmaEquiv (ds W) ⟨v, j⟩ := by
  classical
  have hatt := (mem_pairFlagList o (blockVertex W v) f).mp hf
  have hvtx : ClosedFragment.vertexOf W f.val = blockVertex W v :=
    Sum.inl.inj
      ((ClosedFragment.attach_eq_vertexOf W f.val).symm.trans hatt)
  have hmem : f.val ∈ Finset.univ.filter (fun g =>
      ClosedFragment.vertexOf W g = blockVertex W v) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hvtx⟩
  rw [← image_blockFlag] at hmem
  rw [Finset.mem_image] at hmem
  obtain ⟨j, _, hj⟩ := hmem
  exact ⟨j, by rw [← hj, sortKey_blockFlag]⟩

/-! ## Global list properties -/

/-- The global pair list is duplicate-free. -/
theorem globalPairList_nodup (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) :
    (globalPairList W F o).Nodup := by
  rw [globalPairList, List.nodup_flatMap]
  constructor
  · intro v _
    exact pairFlagList_nodup o (blockVertex W v)
  · have hpw : (List.finRange (ds W).length).Pairwise (· < ·) :=
      (List.sortedLT_finRange _).pairwise
    exact hpw.imp (fun {v₁ v₂} hlt => by
      change List.Disjoint _ _
      intro x hx₁ hx₂
      have h₁ := (mem_pairFlagList o (blockVertex W v₁) x).mp hx₁
      have h₂ := (mem_pairFlagList o (blockVertex W v₂) x).mp hx₂
      have : blockVertex W v₁ = blockVertex W v₂ :=
        Sum.inl.inj (h₁.symm.trans h₂)
      exact absurd (blockVertex_injective' W this) (ne_of_lt hlt))

/-- Every participating flag appears in the global pair list. -/
theorem mem_globalPairList (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation)
    (x : {f : W.Flag // f ∈ F.flags}) :
    x ∈ globalPairList W F o := by
  rw [globalPairList, List.mem_flatMap]
  have hatt := ClosedFragment.attach_eq_vertexOf W x.val
  obtain ⟨v, hv⟩ := blockVertex_surjective' W (ClosedFragment.vertexOf W x.val)
  refine ⟨v, List.mem_finRange v, ?_⟩
  rw [mem_pairFlagList]
  rw [hatt, hv]

/-! ## Main theorem -/

/-- The sortSign of the flatMap over a pairwise-ordered list of block
indices equals the list product of per-block sortSigns. -/
private theorem sortSign_flatMap_aux (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) :
    ∀ (L : List (Fin (ds W).length)),
      L.Pairwise (· < ·) →
      (sortSign ((L.flatMap (fun v =>
          pairFlagList (F := F) o (blockVertex W v))).map
        (fun f => sortKey W f.val)) : ℤ) =
      (L.map (fun v =>
          sortSign ((pairFlagList (F := F) o (blockVertex W v)).map
            (fun f => sortKey W f.val)))).prod
  | [], _ => by simp [sortSign, inversions]
  | v₀ :: L, hpw => by
    rw [List.flatMap_cons, List.map_append,
      sortSign_append_of_le _ _ ?_, List.map_cons, List.prod_cons]
    · congr 1
      exact sortSign_flatMap_aux W F o L hpw.of_cons
    · intro x hx y hy
      rw [List.mem_map] at hx hy
      obtain ⟨fx, hfx, rfl⟩ := hx
      obtain ⟨fy, hfy, rfl⟩ := hy
      -- fy is in the flatMap tail, so it belongs to some block v' with v₀ < v'
      rw [List.mem_flatMap] at hfy
      obtain ⟨v', hv'L, hfy'⟩ := hfy
      obtain ⟨jx, hjx⟩ := sortKey_mem_block W F o v₀ fx hfx
      obtain ⟨jy, hjy⟩ := sortKey_mem_block W F o v' fy hfy'
      rw [hjx, hjy]
      have hlt : v₀ < v' := List.rel_of_pairwise_cons hpw hv'L
      exact le_of_lt (blockSigmaEquiv_lt_of_block_lt hlt jx jy)

/-- **The global key-sortSign is the product of the per-block
key-sortSigns.** -/
theorem sortSign_globalPairList (W : ClosedFragment) (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation) :
    (sortSign ((globalPairList W F o).map (fun f => sortKey W f.val)) : ℂ) =
    ∏ v : Fin (ds W).length,
      (sortSign ((pairFlagList (F := F) o (blockVertex W v)).map
        (fun f => sortKey W f.val)) : ℂ) := by
  -- Work in ℤ first, then cast
  have hint : (sortSign ((globalPairList W F o).map
        (fun f => sortKey W f.val)) : ℤ) =
      ∏ v : Fin (ds W).length,
        sortSign ((pairFlagList (F := F) o (blockVertex W v)).map
          (fun f => sortKey W f.val)) := by
    rw [globalPairList]
    rw [sortSign_flatMap_aux W F o (List.finRange (ds W).length)
      (List.sortedLT_finRange _).pairwise]
    rw [Fin.prod_univ_def]
  rw [show (sortSign ((globalPairList W F o).map
      (fun f => sortKey W f.val)) : ℂ) =
    ((sortSign ((globalPairList W F o).map
      (fun f => sortKey W f.val)) : ℤ) : ℂ) from rfl]
  rw [hint, Int.cast_prod]

end RS
