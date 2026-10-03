/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.MaximumPrinciple
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.ProductCoordinates
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Stability.Neighborhoods

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Compact neighborhoods for the maximum-principle proof

This file contains product-neighborhood localization lemmas used in the
finite-dimensional maximum-principle proof.
-/

@[expose] public noncomputable section

namespace ViscositySolns

variable {n : Nat}

/--
A relative neighborhood of a point in `C × D` contains a translated compact
product neighborhood.

In quantified mathematical form, assume `x0 ∈ C`, `y0 ∈ D`, the relative
topologies on `C` and `D` are locally compact, and
`P ∈ nhdsWithin (x0, y0) (C × D)`. Then there exist compact nonempty sets
`K, L ⊆ R^n`, both containing `0`, such that

* `x0 + K ⊆ C`;
* `y0 + L ⊆ D`;
* for every `x ∈ K` and `y ∈ L`, `(x0 + x, y0 + y) ∈ P`.

The sets are obtained by choosing compact relative closed-ball neighborhoods
of `x0` and `y0` inside the product neighborhood and then translating the
base point to the origin.
-/
theorem exists_compact_translated_product_subset_of_mem_nhdsWithin_prod
    {C D : Set (Point n)} [LocallyCompactSpace C] [LocallyCompactSpace D]
    {P : Set (DoubledPoint n)} {x0 y0 : Point n}
    (hx0C : x0 ∈ C) (hy0D : y0 ∈ D)
    (hP : P ∈ nhdsWithin (x0, y0) (C ×ˢ D)) :
    ∃ K L : Set (Point n),
      K.Nonempty ∧ L.Nonempty ∧
      IsCompact K ∧ IsCompact L ∧
      (0 : Point n) ∈ K ∧ (0 : Point n) ∈ L ∧
      ((fun x : Point n => x0 + x) '' K ∈ nhdsWithin x0 C) ∧
      ((fun y : Point n => y0 + y) '' L ∈ nhdsWithin y0 D) ∧
      ((fun x : Point n => x0 + x) '' K ⊆ C) ∧
      ((fun y : Point n => y0 + y) '' L ⊆ D) ∧
      (∀ x : Point n, x ∈ K -> ∀ y : Point n, y ∈ L -> (x0 + x, y0 + y) ∈ P) ∧
      {q : DoubledPoint n | q.1 - x0 ∈ K ∧ q.2 - y0 ∈ L} ⊆ P := by
  rcases mem_nhdsWithin_prod_iff.1 hP with ⟨U, hU, V, hV, hUV⟩
  rcases exists_inter_closedBall_compactRelativeNeighborhood_subset_of_mem_nhdsWithin
      (C := C) (P := U) hx0C hU with
    ⟨r, _hr, hK0, hK0U⟩
  rcases exists_inter_closedBall_compactRelativeNeighborhood_subset_of_mem_nhdsWithin
      (C := D) (P := V) hy0D hV with
    ⟨s, _hs, hL0, hL0V⟩
  let K0 : Set (Point n) := C ∩ Metric.closedBall x0 r
  let L0 : Set (Point n) := D ∩ Metric.closedBall y0 s
  let K : Set (Point n) := (fun z : Point n => z - x0) '' K0
  let L : Set (Point n) := (fun z : Point n => z - y0) '' L0
  have hKcompact : IsCompact K :=
    hK0.isCompact.image (continuous_id.sub continuous_const)
  have hLcompact : IsCompact L :=
    hL0.isCompact.image (continuous_id.sub continuous_const)
  have h0K : (0 : Point n) ∈ K := by
    refine ⟨x0, hK0.point_mem, ?_⟩
    simp
  have h0L : (0 : Point n) ∈ L := by
    refine ⟨y0, hL0.point_mem, ?_⟩
    simp
  have hK_nonempty : K.Nonempty := ⟨0, h0K⟩
  have hL_nonempty : L.Nonempty := ⟨0, h0L⟩
  have hK_to_K0 : ∀ x : Point n, x ∈ K -> x0 + x ∈ K0 := by
    intro x hx
    rcases hx with ⟨z, hz, rfl⟩
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hz
  have hL_to_L0 : ∀ y : Point n, y ∈ L -> y0 + y ∈ L0 := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hz
  have hK_image_eq : ((fun x : Point n => x0 + x) '' K) = K0 := by
    ext w
    constructor
    · rintro ⟨x, hxK, rfl⟩
      exact hK_to_K0 x hxK
    · intro hw
      refine ⟨w - x0, ⟨w, hw, rfl⟩, ?_⟩
      simp [sub_eq_add_neg]
  have hL_image_eq : ((fun y : Point n => y0 + y) '' L) = L0 := by
    ext w
    constructor
    · rintro ⟨y, hyL, rfl⟩
      exact hL_to_L0 y hyL
    · intro hw
      refine ⟨w - y0, ⟨w, hw, rfl⟩, ?_⟩
      simp [sub_eq_add_neg]
  have hKnhds : ((fun x : Point n => x0 + x) '' K) ∈ nhdsWithin x0 C := by
    rw [hK_image_eq]
    exact hK0.mem_nhdsWithin
  have hLnhds : ((fun y : Point n => y0 + y) '' L) ∈ nhdsWithin y0 D := by
    rw [hL_image_eq]
    exact hL0.mem_nhdsWithin
  have hKsubsetC : ((fun x : Point n => x0 + x) '' K ⊆ C) := by
    rintro _ ⟨x, hxK, rfl⟩
    exact hK0.subset (hK_to_K0 x hxK)
  have hLsubsetD : ((fun y : Point n => y0 + y) '' L ⊆ D) := by
    rintro _ ⟨y, hyL, rfl⟩
    exact hL0.subset (hL_to_L0 y hyL)
  have htranslated :
      ∀ x : Point n, x ∈ K -> ∀ y : Point n, y ∈ L -> (x0 + x, y0 + y) ∈ P := by
    intro x hxK y hyL
    exact hUV ⟨hK0U (hK_to_K0 x hxK), hL0V (hL_to_L0 y hyL)⟩
  have hproduct :
      {q : DoubledPoint n | q.1 - x0 ∈ K ∧ q.2 - y0 ∈ L} ⊆ P := by
    intro q hq
    have hxK0 : q.1 ∈ K0 := by
      have hx := hK_to_K0 (q.1 - x0) hq.1
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hx
    have hyL0 : q.2 ∈ L0 := by
      have hy := hL_to_L0 (q.2 - y0) hq.2
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hy
    exact hUV ⟨hK0U hxK0, hL0V hyL0⟩
  exact ⟨K, L, hK_nonempty, hL_nonempty, hKcompact, hLcompact,
    h0K, h0L, hKnhds, hLnhds, hKsubsetC, hLsubsetD, htranslated, hproduct⟩

/--
A doubled local maximum supplies compact translated neighborhoods on which the
same inequality is a genuine maximum inequality.

In quantified mathematical form, assume `x0 ∈ C`, `y0 ∈ D`, and `(x0, y0)`
is a local maximum point of

`(x, y) ↦ u(x) - v(y) - φ(x, y)`

relative to `C × D`. If the relative topologies on `C` and `D` are locally
compact, then there exist compact nonempty sets `K, L ⊆ R^n`, both
containing `0`, such that `x0 + K ⊆ C`, `y0 + L ⊆ D`, and `(x0, y0)` is a
maximum point of the same doubled objective on the translated product set

`{(x, y) | x - x0 ∈ K and y - y0 ∈ L}`.
-/
theorem exists_compact_translated_product_isMaxOn_of_hasDoubledLocalMaximumOn
    {C D : Set (Point n)} [LocallyCompactSpace C] [LocallyCompactSpace D]
    {u v : Point n -> Real} {φ : DoubledPoint n -> Real} {x0 y0 : Point n}
    (hlocal : HasDoubledLocalMaximumOn C D u v φ x0 y0) :
    ∃ K L : Set (Point n),
      K.Nonempty ∧ L.Nonempty ∧
      IsCompact K ∧ IsCompact L ∧
      (0 : Point n) ∈ K ∧ (0 : Point n) ∈ L ∧
      ((fun x : Point n => x0 + x) '' K ∈ nhdsWithin x0 C) ∧
      ((fun y : Point n => y0 + y) '' L ∈ nhdsWithin y0 D) ∧
      ((fun x : Point n => x0 + x) '' K ⊆ C) ∧
      ((fun y : Point n => y0 + y) '' L ⊆ D) ∧
      IsMaxOn
        (fun q : DoubledPoint n => u q.1 - v q.2 - φ q)
        {q : DoubledPoint n | q.1 - x0 ∈ K ∧ q.2 - y0 ∈ L}
        (x0, y0) := by
  rcases hlocal with ⟨hxy, hlocmax⟩
  rcases exists_isMaxOn_mem_nhdsWithin_of_isLocalMaxOn hxy hlocmax with
    ⟨P, hPnhds, _hxyP, _hPsubset, hmaxP⟩
  rcases exists_compact_translated_product_subset_of_mem_nhdsWithin_prod
      (C := C) (D := D) (P := P) hxy.1 hxy.2 hPnhds with
    ⟨K, L, hKne, hLne, hKcompact, hLcompact, h0K, h0L,
      hKnhds, hLnhds, hKsubsetC, hLsubsetD, _htranslated, hproduct⟩
  exact ⟨K, L, hKne, hLne, hKcompact, hLcompact, h0K, h0L,
    hKnhds, hLnhds, hKsubsetC, hLsubsetD,
    isMaxOn_translated_product_of_isMaxOn_superset hmaxP hproduct⟩

end ViscositySolns
