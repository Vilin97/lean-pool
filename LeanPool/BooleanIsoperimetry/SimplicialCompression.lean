/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import LeanPool.BooleanIsoperimetry.Cube

/-!
# Simplicial coordinate compression

This file defines coordinate up/down compression operations on Boolean-cube
families and proves basic neighborhood monotonicity and slice-pair facts.
-/

open scoped BigOperators
open Finset

namespace BooleanIsoperimetry

/-- A faithful relation for the Up compression of a family along a coordinate `i`.
It pushes elements missing `i` to have `i`, provided the target is not already present. -/
def IsCoordinateUp {N : ℕ} (i : Fin N) (A A' : Finset (Cube N)) : Prop :=
  A'.card = A.card ∧
  ∀ x, x ∈ A' ↔ (x ∈ A ∧ (i ∈ x ∨ insert i x ∈ A)) ∨ (i ∈ x ∧ x ∉ A ∧ x.erase i ∈ A)

/-- A faithful relation for the Down compression of a family along a coordinate `i`.
It pushes elements containing `i` to miss `i`, provided the target is not already present. -/
def IsCoordinateDown {N : ℕ} (i : Fin N) (B B' : Finset (Cube N)) : Prop :=
  B'.card = B.card ∧
  ∀ x, x ∈ B' ↔ (x ∈ B ∧ (i ∉ x ∨ x.erase i ∈ B)) ∨ (i ∉ x ∧ x ∉ B ∧ insert i x ∈ B)

/-- Coordinate-up compression along `i`. -/
noncomputable def coordinateUp {N : ℕ} (i : Fin N) (A : Finset (Cube N)) : Finset (Cube N) :=
  let A_kept := A.filter (fun x => i ∈ x ∨ insert i x ∈ A)
  let A_moved := (A.filter (fun x => i ∉ x ∧ insert i x ∉ A)).image (fun x => insert i x)
  A_kept ∪ A_moved

/-- Coordinate-down compression along `i`. -/
noncomputable def coordinateDown {N : ℕ} (i : Fin N) (A : Finset (Cube N)) : Finset (Cube N) :=
  let A_kept := A.filter (fun x => i ∉ x ∨ erase x i ∈ A)
  let A_moved := (A.filter (fun x => i ∈ x ∧ erase x i ∉ A)).image (fun x => erase x i)
  A_kept ∪ A_moved

lemma coordinateUp_spec {N : ℕ} (i : Fin N) (A : Finset (Cube N)) :
    IsCoordinateUp i A (coordinateUp i A) := by
  unfold IsCoordinateUp coordinateUp
  constructor
  · let A_kept := A.filter (fun x => i ∈ x ∨ insert i x ∈ A)
    let A_tomove := A.filter (fun x => i ∉ x ∧ insert i x ∉ A)
    have h_disj1 : Disjoint A_kept A_tomove := by
      rw [disjoint_iff_ne]
      intro x hx y hy hxy
      rw [mem_filter] at hx hy
      subst hxy
      rcases hx.2 with h1 | h2
      · exact hy.2.1 h1
      · exact hy.2.2 h2
    have h_union : A_kept ∪ A_tomove = A := by
      ext x
      simp only [mem_union]
      by_cases h1 : i ∈ x
      · aesop
      · by_cases h2 : insert i x ∈ A
        · aesop
        · aesop
    have h_inj : Set.InjOn (fun x => insert i x) (A_tomove : Set (Cube N)) := by
      intro x hx y hy eq
      rw [mem_coe, mem_filter] at hx hy
      have eq2 := congrArg (fun z => erase z i) eq
      simp only [erase_insert hx.2.1, erase_insert hy.2.1] at eq2
      exact eq2
    have h_card1 : (A_tomove.image (fun x => insert i x)).card = A_tomove.card :=
      card_image_of_injOn h_inj
    have h_disj2 : Disjoint A_kept (A_tomove.image (fun x => insert i x)) := by
      rw [disjoint_iff_ne]
      intro x hx y hy hxy
      rw [mem_filter] at hx
      rw [mem_image] at hy
      rcases hy with ⟨z, hz, rfl⟩
      subst hxy
      rw [mem_filter] at hz
      exact hz.2.2 hx.1
    rw [card_union_of_disjoint h_disj2, h_card1, ←card_union_of_disjoint h_disj1, h_union]
  · intro x
    simp only [mem_union, mem_image, mem_filter]
    constructor
    · rintro (⟨hxA, hxcond⟩ | ⟨y, ⟨hyA, hycond1, hycond2⟩, rfl⟩)
      · left; exact ⟨hxA, hxcond⟩
      · right
        exact ⟨mem_insert_self i y, hycond2, by rwa [erase_insert hycond1]⟩
    · rintro (⟨hxA, hxcond⟩ | ⟨hxi, hxA, hyA⟩)
      · left; exact ⟨hxA, hxcond⟩
      · right
        refine ⟨erase x i, ⟨hyA, by simp, ?_⟩, insert_erase hxi⟩
        · rwa [insert_erase hxi]

lemma coordinateDown_spec {N : ℕ} (i : Fin N) (A : Finset (Cube N)) :
    IsCoordinateDown i A (coordinateDown i A) := by
  unfold IsCoordinateDown coordinateDown
  constructor
  · let A_kept := A.filter (fun x => i ∉ x ∨ erase x i ∈ A)
    let A_tomove := A.filter (fun x => i ∈ x ∧ erase x i ∉ A)
    have h_disj1 : Disjoint A_kept A_tomove := by
      rw [disjoint_iff_ne]
      intro x hx y hy hxy
      rw [mem_filter] at hx hy
      subst hxy
      rcases hx.2 with h1 | h2
      · exact h1 hy.2.1
      · exact hy.2.2 h2
    have h_union : A_kept ∪ A_tomove = A := by
      ext x
      simp only [mem_union]
      by_cases h1 : i ∈ x
      · by_cases h2 : erase x i ∈ A
        · aesop
        · aesop
      · aesop
    have h_inj : Set.InjOn (fun x => erase x i) (A_tomove : Set (Cube N)) := by
      intro x hx y hy eq
      rw [mem_coe, mem_filter] at hx hy
      have eq2 := congrArg (fun z => insert i z) eq
      simp only [insert_erase hx.2.1, insert_erase hy.2.1] at eq2
      exact eq2
    have h_card1 : (A_tomove.image (fun x => erase x i)).card = A_tomove.card :=
      card_image_of_injOn h_inj
    have h_disj2 : Disjoint A_kept (A_tomove.image (fun x => erase x i)) := by
      rw [disjoint_iff_ne]
      intro x hx y hy hxy
      rw [mem_filter] at hx
      rw [mem_image] at hy
      rcases hy with ⟨z, hz, rfl⟩
      subst hxy
      rw [mem_filter] at hz
      exact hz.2.2 hx.1
    rw [card_union_of_disjoint h_disj2, h_card1, ←card_union_of_disjoint h_disj1, h_union]
  · intro x
    simp only [mem_union, mem_image, mem_filter]
    constructor
    · rintro (⟨hxA, hxcond⟩ | ⟨y, ⟨hyA, hycond1, hycond2⟩, rfl⟩)
      · left; exact ⟨hxA, hxcond⟩
      · right
        exact ⟨by simp, hycond2, by rwa [insert_erase hycond1]⟩
    · rintro (⟨hxA, hxcond⟩ | ⟨hxi, hxA, hyA⟩)
      · left; exact ⟨hxA, hxcond⟩
      · right
        refine ⟨insert i x, ⟨hyA, by simp, ?_⟩, erase_insert hxi⟩
        · rwa [erase_insert hxi]

lemma IsCoordinateUp_unique {N : ℕ} {i : Fin N} {A A' A'' : Finset (Cube N)}
    (h1 : IsCoordinateUp i A A') (h2 : IsCoordinateUp i A A'') : A' = A'' := by
  ext x
  rw [h1.2, h2.2]

lemma coordinateUp_eq {N : ℕ} {i : Fin N} {A A' : Finset (Cube N)}
    (hA : IsCoordinateUp i A A') : A' = coordinateUp i A :=
  IsCoordinateUp_unique hA (coordinateUp_spec i A)

lemma IsCoordinateDown_unique {N : ℕ} {i : Fin N} {A A' A'' : Finset (Cube N)}
    (h1 : IsCoordinateDown i A A') (h2 : IsCoordinateDown i A A'') : A' = A'' := by
  ext x
  rw [h1.2, h2.2]

lemma coordinateDown_eq {N : ℕ} {i : Fin N} {A A' : Finset (Cube N)}
    (hA : IsCoordinateDown i A A') : A' = coordinateDown i A :=
  IsCoordinateDown_unique hA (coordinateDown_spec i A)

/-- Membership characterization of the explicit Up compression, read off directly
from `coordinateUp_spec`. -/
lemma mem_coordinateUp_iff {N : ℕ} (i : Fin N) (A : Finset (Cube N)) (x : Cube N) :
    x ∈ coordinateUp i A ↔
      (x ∈ A ∧ (i ∈ x ∨ insert i x ∈ A)) ∨ (i ∈ x ∧ x ∉ A ∧ x.erase i ∈ A) :=
  (coordinateUp_spec i A).2 x

lemma coordinateUp_mem_of_not_mem {N : ℕ} (i : Fin N) (A : Finset (Cube N)) (x : Cube N)
    (hix : i ∉ x) : x ∈ coordinateUp i A ↔ x ∈ A ∧ insert i x ∈ A := by
  rw [mem_coordinateUp_iff]; simp [hix]

lemma coordinateUp_mem_of_mem {N : ℕ} (i : Fin N) (A : Finset (Cube N)) (x : Cube N)
    (hix : i ∈ x) : x ∈ coordinateUp i A ↔ x ∈ A ∨ x.erase i ∈ A := by
  rw [mem_coordinateUp_iff]; simp [hix]; tauto

/-- Membership characterization of the explicit Down compression, read off directly
from `coordinateDown_spec`. -/
lemma mem_coordinateDown_iff {N : ℕ} (i : Fin N) (A : Finset (Cube N)) (x : Cube N) :
    x ∈ coordinateDown i A ↔
      (x ∈ A ∧ (i ∉ x ∨ x.erase i ∈ A)) ∨ (i ∉ x ∧ x ∉ A ∧ insert i x ∈ A) :=
  (coordinateDown_spec i A).2 x

lemma coordinateDown_mem_of_mem {N : ℕ} (i : Fin N) (B : Finset (Cube N)) (x : Cube N)
    (hix : i ∈ x) : x ∈ coordinateDown i B ↔ x ∈ B ∧ x.erase i ∈ B := by
  rw [mem_coordinateDown_iff]; simp [hix]

lemma coordinateDown_mem_of_not_mem {N : ℕ} (i : Fin N) (B : Finset (Cube N)) (x : Cube N)
    (hix : i ∉ x) : x ∈ coordinateDown i B ↔ x ∈ B ∨ insert i x ∈ B := by
  rw [mem_coordinateDown_iff]; simp [hix]; tauto

/-! ### Hamming-distance helpers for the coordinate shadow inclusions -/

lemma hDist_comm {N : ℕ} (x y : Cube N) : hDist x y = hDist y x := by
  unfold hDist; rw [symmDiff_comm]

lemma hDist_self_le_one {N : ℕ} (x : Cube N) : hDist x x ≤ 1 := by
  unfold hDist; simp [symmDiff_self]

lemma hDist_erase_le_hDist {N : ℕ} (i : Fin N) (x y : Cube N) (h : hDist x y ≤ 1) :
    hDist (x.erase i) (y.erase i) ≤ 1 := by
  unfold hDist at h ⊢
  have : symmDiff (x.erase i) (y.erase i) ⊆ symmDiff x y := by
    intro j hj
    simp only [mem_symmDiff, mem_erase] at hj ⊢
    tauto
  exact le_trans (card_le_card this) h

lemma hDist_insert_le_hDist {N : ℕ} (i : Fin N) (x y : Cube N) (h : hDist x y ≤ 1) :
    hDist (insert i x) (insert i y) ≤ 1 := by
  unfold hDist at h ⊢
  have : symmDiff (insert i x) (insert i y) ⊆ symmDiff x y := by
    intro j hj
    simp only [mem_symmDiff, mem_insert] at hj ⊢
    tauto
  exact le_trans (card_le_card this) h

lemma hDist_insert_self_le_one {N : ℕ} (i : Fin N) (x : Cube N) : hDist (insert i x) x ≤ 1 := by
  unfold hDist
  have : symmDiff (insert i x) x ⊆ {i} := by
    intro j hj
    simp only [mem_symmDiff, mem_insert] at hj
    rw [mem_singleton]; tauto
  have hcard : (symmDiff (insert i x) x).card ≤ ({i} : Finset (Fin N)).card := card_le_card this
  rwa [card_singleton] at hcard

lemma hDist_self_insert_le_one {N : ℕ} (i : Fin N) (x : Cube N) : hDist x (insert i x) ≤ 1 := by
  rw [hDist_comm]; exact hDist_insert_self_le_one i x

lemma hDist_erase_self_le_one {N : ℕ} (i : Fin N) (x : Cube N) : hDist (x.erase i) x ≤ 1 := by
  unfold hDist
  have : symmDiff (x.erase i) x ⊆ {i} := by
    intro j hj
    simp only [mem_symmDiff, mem_erase] at hj
    rw [mem_singleton]; tauto
  have hcard : (symmDiff (x.erase i) x).card ≤ ({i} : Finset (Fin N)).card := card_le_card this
  rwa [card_singleton] at hcard

lemma hDist_self_erase_le_one {N : ℕ} (i : Fin N) (x : Cube N) : hDist x (x.erase i) ≤ 1 := by
  unfold hDist
  have : symmDiff x (x.erase i) ⊆ {i} := by
    intro j hj
    simp only [mem_symmDiff, mem_erase] at hj
    rw [mem_singleton]; tauto
  have hcard : (symmDiff x (x.erase i)).card ≤ ({i} : Finset (Fin N)).card := card_le_card this
  rwa [card_singleton] at hcard

lemma eq_insert_of_hDist_le_one_of_not_mem_of_mem {N : ℕ} {x y : Cube N} {i : Fin N}
    (h : hDist x y ≤ 1) (hix : i ∉ x) (hiy : i ∈ y) : y = insert i x := by
  unfold hDist at h
  have hi : i ∈ symmDiff x y := by rw [mem_symmDiff]; tauto
  have heq : symmDiff x y = {i} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hi, fun j hj => ?_⟩
    by_contra h_ne
    have h_sub : {i, j} ⊆ symmDiff x y := by
      intro k hk
      rw [mem_insert, mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hi
      · exact hj
    have h_card : 2 ≤ (symmDiff x y).card := by
      have : ({i, j} : Finset (Fin N)).card = 2 := card_pair (ne_comm.mp h_ne)
      rw [← this]; exact card_le_card h_sub
    omega
  ext j
  by_cases hj : j = i
  · subst hj; simp [hix, hiy]
  · have hdiff : j ∉ symmDiff x y := by
      rw [heq]; exact fun h => hj (mem_singleton.mp h)
    simp only [mem_symmDiff] at hdiff
    have : j ∈ y ↔ j ∈ x := by tauto
    simp [hj, this]

lemma eq_erase_of_hDist_le_one_of_mem_of_not_mem {N : ℕ} {x y : Cube N} {i : Fin N}
    (h : hDist x y ≤ 1) (hix : i ∈ x) (hiy : i ∉ y) : y = x.erase i := by
  unfold hDist at h
  have hi : i ∈ symmDiff x y := by rw [mem_symmDiff]; tauto
  have heq : symmDiff x y = {i} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hi, fun j hj => ?_⟩
    by_contra h_ne
    have h_sub : {i, j} ⊆ symmDiff x y := by
      intro k hk
      rw [mem_insert, mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hi
      · exact hj
    have h_card : 2 ≤ (symmDiff x y).card := by
      have : ({i, j} : Finset (Fin N)).card = 2 := card_pair (ne_comm.mp h_ne)
      rw [← this]; exact card_le_card h_sub
    omega
  ext j
  by_cases hj : j = i
  · subst hj; simp [hix, hiy]
  · have hdiff : j ∉ symmDiff x y := by
      rw [heq]; exact fun h => hj (mem_singleton.mp h)
    simp only [mem_symmDiff] at hdiff
    have : j ∈ y ↔ j ∈ x := by tauto
    simp [hj, this]

/-- **Coordinate Up shadow inclusion (PDF Frankl-Füredi).**  The closed unit
neighborhood of an Up-compressed family is contained in the Up-compression of the
neighborhood.  This is the classical "compression does not expand the shadow" fact. -/
lemma neighborhood_coordinateUp_subset {N : ℕ} {i : Fin N} {A : Finset (Cube N)} :
    neighborhood 1 (coordinateUp i A) ⊆ coordinateUp i (neighborhood 1 A) := by
  intro y hy
  rw [mem_neighborhood_iff] at hy
  rcases hy with ⟨x, hx, hdist⟩
  by_cases hiy : i ∈ y
  · rw [coordinateUp_mem_of_mem i _ y hiy]
    by_cases hix : i ∈ x
    · rw [coordinateUp_mem_of_mem i A x hix] at hx
      rcases hx with hxA | hx_erase
      · exact Or.inl (mem_neighborhood_iff.mpr ⟨x, hxA, hdist⟩)
      · exact Or.inr (mem_neighborhood_iff.mpr
          ⟨x.erase i, hx_erase, hDist_erase_le_hDist i x y hdist⟩)
    · rw [coordinateUp_mem_of_not_mem i A x hix] at hx
      have hxy : y = insert i x := eq_insert_of_hDist_le_one_of_not_mem_of_mem hdist hix hiy
      subst hxy
      exact Or.inl (mem_neighborhood_iff.mpr ⟨insert i x, hx.2, hDist_self_le_one (insert i x)⟩)
  · rw [coordinateUp_mem_of_not_mem i _ y hiy]
    by_cases hix : i ∈ x
    · have hdist2 : hDist y x ≤ 1 := by rwa [hDist_comm]
      have hyx : x = insert i y := eq_insert_of_hDist_le_one_of_not_mem_of_mem hdist2 hiy hix
      subst hyx
      rw [coordinateUp_mem_of_mem i A _ (mem_insert_self _ _)] at hx
      rcases hx with hxA | hx_erase
      · exact ⟨mem_neighborhood_iff.mpr ⟨insert i y, hxA, hDist_insert_self_le_one i y⟩,
               mem_neighborhood_iff.mpr ⟨insert i y, hxA, hDist_self_le_one (insert i y)⟩⟩
      · rw [erase_insert hiy] at hx_erase
        exact ⟨mem_neighborhood_iff.mpr ⟨y, hx_erase, hDist_self_le_one y⟩,
               mem_neighborhood_iff.mpr ⟨y, hx_erase, hDist_self_insert_le_one i y⟩⟩
    · rw [coordinateUp_mem_of_not_mem i A x hix] at hx
      exact ⟨mem_neighborhood_iff.mpr ⟨x, hx.1, hdist⟩,
             mem_neighborhood_iff.mpr ⟨insert i x, hx.2, hDist_insert_le_hDist i x y hdist⟩⟩

/-- **Coordinate Down shadow inclusion (PDF Frankl-Füredi).**  The mirror of
`neighborhood_coordinateUp_subset` for Down compression. -/
lemma neighborhood_coordinateDown_subset {N : ℕ} {i : Fin N} {A : Finset (Cube N)} :
    neighborhood 1 (coordinateDown i A) ⊆ coordinateDown i (neighborhood 1 A) := by
  intro y hy
  rw [mem_neighborhood_iff] at hy
  rcases hy with ⟨x, hx, hdist⟩
  by_cases hiy : i ∉ y
  · rw [coordinateDown_mem_of_not_mem i _ y hiy]
    by_cases hix : i ∉ x
    · rw [coordinateDown_mem_of_not_mem i A x hix] at hx
      rcases hx with hxB | hx_insert
      · exact Or.inl (mem_neighborhood_iff.mpr ⟨x, hxB, hdist⟩)
      · exact Or.inr (mem_neighborhood_iff.mpr
          ⟨insert i x, hx_insert, hDist_insert_le_hDist i x y hdist⟩)
    · rw [coordinateDown_mem_of_mem i A x (by rwa [not_not] at hix)] at hx
      have hxy : y = x.erase i :=
        eq_erase_of_hDist_le_one_of_mem_of_not_mem hdist (by rwa [not_not] at hix) hiy
      subst hxy
      exact Or.inl (mem_neighborhood_iff.mpr ⟨x.erase i, hx.2, hDist_self_le_one (x.erase i)⟩)
  · rw [coordinateDown_mem_of_mem i _ y (by rwa [not_not] at hiy)]
    by_cases hix : i ∉ x
    · have hdist2 : hDist y x ≤ 1 := by unfold hDist at hdist ⊢; rw [symmDiff_comm]; exact hdist
      have hyx : x = y.erase i :=
        eq_erase_of_hDist_le_one_of_mem_of_not_mem hdist2 (by rwa [not_not] at hiy) hix
      subst hyx
      rw [coordinateDown_mem_of_not_mem i A _ (by simp)] at hx
      rcases hx with hxB | hx_insert
      · exact ⟨mem_neighborhood_iff.mpr ⟨y.erase i, hxB, hDist_erase_self_le_one i y⟩,
               mem_neighborhood_iff.mpr ⟨y.erase i, hxB, hDist_self_le_one (y.erase i)⟩⟩
      · rw [insert_erase (by rwa [not_not] at hiy)] at hx_insert
        exact ⟨mem_neighborhood_iff.mpr ⟨y, hx_insert, hDist_self_le_one y⟩,
               mem_neighborhood_iff.mpr ⟨y, hx_insert, hDist_self_erase_le_one i y⟩⟩
    · rw [coordinateDown_mem_of_mem i A x (by rwa [not_not] at hix)] at hx
      exact ⟨mem_neighborhood_iff.mpr ⟨x, hx.1, hdist⟩,
             mem_neighborhood_iff.mpr ⟨x.erase i, hx.2, hDist_erase_le_hDist i x y hdist⟩⟩


/-- The Frankl-Füredi compression potential used for well-founded descent:
the sum of simplicial ranks of all vertices in the family.  Coordinate and
within-layer shifts are expected to strictly reduce this potential unless they
are already fixed points. -/
noncomputable def compressionPotential {N : ℕ} (A : Finset (Cube N)) : ℕ :=
  ∑ x ∈ A, rank x

/-- The paired version of `compressionPotential`, matching the two-slice
Frankl-Füredi compression process. -/
noncomputable def pairCompressionPotential {N : ℕ} (A B : Finset (Cube N)) : ℕ :=
  compressionPotential A + compressionPotential B

/-- A family is fixed by all currently formalized Up-compressions.  This is only
the coordinate part of the PDF terminal condition; the within-layer/colex shifts
still have to be added before fixed points can be identified with simplicial
initial segments. -/
def IsCoordinateUpFixed {N : ℕ} (A : Finset (Cube N)) : Prop :=
  ∀ i : Fin N, IsCoordinateUp i A A

/-- A family is fixed by all currently formalized Down-compressions. -/
def IsCoordinateDownFixed {N : ℕ} (A : Finset (Cube N)) : Prop :=
  ∀ i : Fin N, IsCoordinateDown i A A

lemma coordinateUp_card_eq {N : ℕ} {i : Fin N} {A A' : Finset (Cube N)}
    (hA : IsCoordinateUp i A A') :
    A'.card = A.card :=
  hA.1

lemma coordinateDown_card_eq {N : ℕ} {i : Fin N} {B B' : Finset (Cube N)}
    (hB : IsCoordinateDown i B B') :
    B'.card = B.card :=
  hB.1


/-- **PDF compression lemma (Up move).**  An Up-compression along coordinate `i`
does not increase the closed unit neighborhood (vertex boundary) of a family.
This is the classical Frankl–Füredi / Harper statement "the `i`-compression does
not increase the shadow", here in the closed-neighborhood form
`|N(C_i^↑ A)| ≤ |N(A)|`.  It is a genuine combinatorial obligation about the
concrete `IsCoordinateUp` relation, *not* a missing definition: every object in
the statement is already formalized.  It is proved in the PDF by the inclusion
`N(C_i^↑ A) ⊆ C_i^↑(N A)` together with cardinality-preservation of `C_i^↑`. -/
lemma coordinateUp_neighborhood_card_le {N : ℕ} {i : Fin N} {A A' : Finset (Cube N)}
    (hA : IsCoordinateUp i A A') :
    (neighborhood 1 A').card ≤ (neighborhood 1 A).card := by
  rw [coordinateUp_eq hA]
  have h_sub := neighborhood_coordinateUp_subset (A := A) (i := i)
  have h_card := coordinateUp_card_eq (coordinateUp_spec i (neighborhood 1 A))
  exact le_trans (card_le_card h_sub) (le_of_eq h_card)

/-- **PDF compression lemma (Down move).**  The mirror of
`coordinateUp_neighborhood_card_le`: a Down-compression along coordinate `i` does
not increase the closed unit neighborhood, `|N(C_i^↓ B)| ≤ |N(B)|`.  Symmetric to
the Up case under the coordinate-`i` flip isometry of the cube. -/
lemma coordinateDown_neighborhood_card_le {N : ℕ} {i : Fin N} {B B' : Finset (Cube N)}
    (hB : IsCoordinateDown i B B') :
    (neighborhood 1 B').card ≤ (neighborhood 1 B).card := by
  rw [coordinateDown_eq hB]
  have h_sub := neighborhood_coordinateDown_subset (A := B) (i := i)
  have h_card := coordinateDown_card_eq (coordinateDown_spec i (neighborhood 1 B))
  exact le_trans (card_le_card h_sub) (le_of_eq h_card)



-- ============================================================================
-- Coordinate Down-compression strictly decreases the rank potential when it
-- actually moves something.  This is the missing ingredient that lets the
-- single honest Phase-1 leaf be restricted from *all* non-terminal families to
-- the strictly smaller class of coordinate-Down-*fixed* non-terminal families:
-- a family that is not Down-fixed admits a coordinate Down-compression, which
-- (a) preserves size (`coordinateDown_card_eq`), (b) does not increase the
-- boundary (`coordinateDown_neighborhood_card_le`), and (c) strictly lowers
-- `compressionPotential = ∑ rank` (proved here), hence is itself a descent
-- witness.  All sorry-free.
-- ============================================================================

/-- The explicit single-vertex Down map underlying `coordinateDown`: a vertex
containing `i` whose `i`-erasure is not already present is pushed down to that
erasure; every other vertex is fixed. -/
noncomputable def downMap {N : ℕ} (i : Fin N) (A : Finset (Cube N)) (x : Cube N) : Cube N :=
  if i ∈ x ∧ x.erase i ∉ A then x.erase i else x

/-- Erasing a present coordinate is a strictly earlier simplicial vertex. -/
lemma simplicialLt_erase_self {N : ℕ} {i : Fin N} {x : Cube N} (hi : i ∈ x) :
    simplicialLt (x.erase i) x := by
  have hpos : 0 < x.card := Finset.card_pos.mpr ⟨i, hi⟩
  have hcard : (x.erase i).card = x.card - 1 := Finset.card_erase_of_mem hi
  refine ⟨Or.inl ?_, ?_⟩
  · rw [hcard]; omega
  · rintro (h | ⟨h, _⟩) <;> · rw [hcard] at h; omega

/-- The Down map never increases simplicial rank. -/
lemma downMap_rank_le {N : ℕ} (i : Fin N) (A : Finset (Cube N)) (x : Cube N) :
    rank (downMap i A x) ≤ rank x := by
  unfold downMap
  split
  · next h => exact le_of_lt (rank_strictMono (simplicialLt_erase_self h.1))
  · exact le_rfl

/-- The Down map is injective on its family. -/
lemma downMap_injOn {N : ℕ} (i : Fin N) (A : Finset (Cube N)) :
    Set.InjOn (downMap i A) ↑A := by
  intro x hx y hy h
  rw [Finset.mem_coe] at hx hy
  unfold downMap at h
  by_cases hcx : i ∈ x ∧ x.erase i ∉ A
  · by_cases hcy : i ∈ y ∧ y.erase i ∉ A
    · rw [if_pos hcx, if_pos hcy] at h
      have := congrArg (insert i) h
      rwa [Finset.insert_erase hcx.1, Finset.insert_erase hcy.1] at this
    · rw [if_pos hcx, if_neg hcy] at h
      rw [← h] at hy; exact (hcx.2 hy).elim
  · by_cases hcy : i ∈ y ∧ y.erase i ∉ A
    · rw [if_neg hcx, if_pos hcy] at h
      rw [h] at hx; exact (hcy.2 hx).elim
    · rw [if_neg hcx, if_neg hcy] at h
      exact h

/-- `coordinateDown` is the image of the family under `downMap`. -/
lemma coordinateDown_eq_image {N : ℕ} (i : Fin N) (A : Finset (Cube N)) :
    coordinateDown i A = A.image (downMap i A) := by
  unfold coordinateDown downMap
  ext y
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro (⟨hyA, hcond⟩ | ⟨z, hz, rfl⟩)
    · refine ⟨y, hyA, ?_⟩
      rw [if_neg]
      rintro ⟨hiy, hey⟩
      rcases hcond with h | h
      · exact h hiy
      · exact hey h
    · exact ⟨z, hz.1, by rw [if_pos hz.2]⟩
  · rintro ⟨z, hz, rfl⟩
    by_cases hcond : i ∈ z ∧ z.erase i ∉ A
    · right
      rw [if_pos hcond]
      exact ⟨z, ⟨hz, hcond⟩, rfl⟩
    · left
      rw [if_neg hcond]
      refine ⟨hz, ?_⟩
      rw [not_and_or, not_not] at hcond
      exact hcond

/-- `coordinateDown` never increases the rank potential. -/
lemma coordinateDown_potential_le {N : ℕ} (i : Fin N) (A : Finset (Cube N)) :
    compressionPotential (coordinateDown i A) ≤ compressionPotential A := by
  unfold compressionPotential
  rw [coordinateDown_eq_image, Finset.sum_image (fun x hx y hy h => downMap_injOn i A hx hy h)]
  exact Finset.sum_le_sum (fun x _ => downMap_rank_le i A x)

/-- If a coordinate Down-compression actually changes the family, it strictly
moves at least one vertex down. -/
lemma exists_downMap_ne_of_ne {N : ℕ} (i : Fin N) (A : Finset (Cube N))
    (hne : coordinateDown i A ≠ A) : ∃ x ∈ A, downMap i A x ≠ x := by
  by_contra hcon
  push Not at hcon
  apply hne
  rw [coordinateDown_eq_image, Finset.image_congr (g := id) (fun x hx => hcon x hx),
    Finset.image_id]

/-- **Coordinate Down-compression strictly decreases the rank potential when it
moves something.**  Combined with the proven size- and boundary-control
(`coordinateDown_card_eq`, `coordinateDown_neighborhood_card_le`) this gives any
non-Down-fixed family an explicit Frankl–Füredi compression descent witness. -/
lemma coordinateDown_potential_lt_of_ne {N : ℕ} (i : Fin N) (A : Finset (Cube N))
    (hne : coordinateDown i A ≠ A) :
    compressionPotential (coordinateDown i A) < compressionPotential A := by
  unfold compressionPotential
  rw [coordinateDown_eq_image, Finset.sum_image (fun x hx y hy h => downMap_injOn i A hx hy h)]
  obtain ⟨x, hx, hxne⟩ := exists_downMap_ne_of_ne i A hne
  refine Finset.sum_lt_sum (fun x _ => downMap_rank_le i A x) ⟨x, hx, ?_⟩
  unfold downMap at hxne ⊢
  split at hxne
  · next hc => rw [if_pos hc]; exact rank_strictMono (simplicialLt_erase_self hc.1)
  · next => exact absurd rfl hxne

/-- Within-layer colexicographic shift. It moves an element to a strictly earlier
element in the same layer (same cardinality), provided the target is not already in the family. -/
def IsColexShift {N : ℕ} (A A' : Finset (Cube N)) : Prop :=
  A'.card = A.card ∧
  ∃ (x y : Cube N), x ∈ A ∧ y ∉ A ∧ x.card = y.card ∧ simplicialLt y x ∧
    A' = insert y (A.erase x)

/-- A family is stable under all within-layer colex shifts. -/
def IsColexShiftFixed {N : ℕ} (A : Finset (Cube N)) : Prop :=
  ∀ A', ¬IsColexShift A A'

/-- The missing level-saturation condition in the PDF compression route: once
the compression process keeps a vertex of a given Hamming level, every lower
Hamming level is already completely filled.  Coordinate Down-compressions alone
only fill coordinate subfaces of a present vertex; they do not imply this global
saturation across a whole level. -/
def IsLowerLevelSaturated {N : ℕ} (A : Finset (Cube N)) : Prop :=
  ∀ ⦃x y : Cube N⦄, x.card < y.card → y ∈ A → x ∈ A

lemma lowerLevelSaturated_colexFixed_is_downClosed {N : ℕ} (A : Finset (Cube N))
    (hLower : IsLowerLevelSaturated A)
    (hColex : IsColexShiftFixed A) :
    ∀ x y, simplicialLe x y → y ∈ A → x ∈ A := by
  intro x y hxy hyA
  unfold simplicialLe at hxy
  rcases hxy with hcard | ⟨hcard, hnat⟩
  · exact hLower hcard hyA
  · by_cases hxA : x ∈ A
    · exact hxA
    · have hlt : simplicialLt x y := by
        refine ⟨?_, ?_⟩
        · unfold simplicialLe
          exact Or.inr ⟨hcard, hnat⟩
        · intro hyx
          exact hxA ((simplicialLe_antisymm x y
            (by unfold simplicialLe; exact Or.inr ⟨hcard, hnat⟩) hyx).symm ▸ hyA)
      have hshift : IsColexShift A (insert x (A.erase y)) := by
        refine ⟨?_, ⟨y, x, hyA, hxA, hcard.symm, hlt, rfl⟩⟩
        rw [card_insert_of_notMem]
        · rw [card_erase_of_mem hyA]
          have hpos : 0 < A.card := Finset.card_pos.mpr ⟨y, hyA⟩
          omega
        · simp [hxA]
      exact (hColex (insert x (A.erase y)) hshift).elim

lemma coordinate_compressed_is_downClosed {N : ℕ} (A : Finset (Cube N))
    (_hDown : IsCoordinateDownFixed A)
    (hLower : IsLowerLevelSaturated A)
    (hColex : IsColexShiftFixed A) :
    ∀ x y, simplicialLe x y → y ∈ A → x ∈ A :=
  lowerLevelSaturated_colexFixed_is_downClosed A hLower hColex

/-- The embedded two-slice family whose lower slice is the initial segment of
size `a` and whose upper slice is the initial segment of size `b`.  This is the
PDF-language object behind the scalar Macaulay split step. -/
noncomputable def initialSlicePair (N a b : ℕ) : Finset (Cube (N + 1)) :=
  (simplicialInitSeg N a).image embed0 ∪ (simplicialInitSeg N b).image embed1

lemma initialSlicePair_embed0_injective {N : ℕ} : Function.Injective (@embed0 N) :=
  Finset.image_injective (Fin.castSucc_injective N)

lemma initialSlicePair_last_not_mem_embed0 {N : ℕ} (x : Cube N) :
    Fin.last N ∉ embed0 x := by
  simp [embed0]

lemma initialSlicePair_embed1_injective {N : ℕ} : Function.Injective (@embed1 N) := by
  intro x y h
  unfold embed1 at h
  have key : x.image Fin.castSucc = y.image Fin.castSucc := by
    have := congrArg (·.erase (Fin.last N)) h
    simpa [Finset.erase_insert, initialSlicePair_last_not_mem_embed0] using this
  exact Finset.image_injective (Fin.castSucc_injective N) key

lemma slice0_initialSlicePair {N a b : ℕ} :
    slice0 (initialSlicePair N a b) = simplicialInitSeg N a := by
  ext x
  simp only [slice0, initialSlicePair, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨y, hy, hxy⟩ | ⟨y, _hy, hxy⟩)
    · have hyx : y = x := initialSlicePair_embed0_injective hxy
      simpa [← hyx] using hy
    · have hlast : Fin.last N ∈ embed1 y := by simp [embed1]
      rw [hxy] at hlast
      exact (initialSlicePair_last_not_mem_embed0 x hlast).elim
  · intro hx
    exact Or.inl ⟨x, hx, rfl⟩

lemma slice1_initialSlicePair {N a b : ℕ} :
    slice1 (initialSlicePair N a b) = simplicialInitSeg N b := by
  ext x
  simp only [slice1, initialSlicePair, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨y, _hy, hxy⟩ | ⟨y, hy, hxy⟩)
    · have hlast : Fin.last N ∈ embed1 x := by simp [embed1]
      rw [← hxy] at hlast
      exact (initialSlicePair_last_not_mem_embed0 y hlast).elim
    · have hyx : y = x := initialSlicePair_embed1_injective hxy
      simpa [← hyx] using hy
  · intro hx
    exact Or.inr ⟨x, hx, rfl⟩

lemma neighborhood_initialSlicePair_card {N a b : ℕ}
    (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    (neighborhood 1 (initialSlicePair N a b)).card =
      max (H N a) b + max (H N b) a := by
  rw [neighborhood_succ, slice0_initialSlicePair, slice1_initialSlicePair]
  rw [neighborhood_initSeg_eq, neighborhood_initSeg_eq]
  rw [card_initSeg_union (H_le_cube N a) hb, card_initSeg_union (H_le_cube N b) ha]


/-- Every family on the `N`-cube has cardinality at most `2 ^ N`. -/
lemma card_le_two_pow {N : ℕ} (S : Finset (Cube N)) : S.card ≤ 2 ^ N := by
  have h1 : S.card ≤ Fintype.card (Cube N) := Finset.card_le_univ S
  have h2 : Fintype.card (Cube N) = 2 ^ N := by
    simp [Cube, Fintype.card_finset, Fintype.card_fin]
  omega

end BooleanIsoperimetry
