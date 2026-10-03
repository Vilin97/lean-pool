/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the vertex-pair rectangle of a sub-triple

The deterministic grid construction produces its sub-triples `(A, B, C)` as blocks inside the
clusters of a good triple, and the design asks for the tripartite graphs to be pairwise
edge-disjoint.  The natural — and strictly stronger — property the construction actually has is
that the *rectangles of vertex pairs* `A × B`, `A × C`, `B × C` (and their transposes) of different
sub-triples are disjoint.  This file records that notion and its two consequences.

* `Nibble.AX1.tripleRect` — the (symmetric) set of vertex pairs covered by a sub-triple;
* `Nibble.AX1.tripleGraph_edgeDisjoint_of_rect_disjoint` — disjoint rectangles give edge-disjoint
  tripartite graphs;
* `Nibble.AX1.card_tripleRect`, `Nibble.AX1.sum_area_le_of_rect_disjoint` — the areas of pairwise
  disjoint rectangles add up to at most `|V|²`, which is what bounds the total error of a design.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapTripleDegrees

/-! # CoreGapRectPack -/

public section

open Finset SimpleGraph

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The vertex-pair rectangle of a sub-triple**: all ordered pairs joining two different parts
of `(A, B, C)`. -/
@[expose] def tripleRect (A B C : Finset V) : Finset (V × V) :=
  ((A ×ˢ B) ∪ (B ×ˢ A)) ∪ ((A ×ˢ C) ∪ (C ×ˢ A)) ∪ ((B ×ˢ C) ∪ (C ×ˢ B))

omit [Fintype V] in
theorem mem_tripleRect_iff {A B C : Finset V} {x y : V} :
    (x, y) ∈ tripleRect A B C ↔ crossAdj A B C x y := by
  simp only [tripleRect, Finset.mem_union, Finset.mem_product, crossAdj]
  tauto

omit [Fintype V] in
/-- **Disjoint rectangles give edge-disjoint tripartite graphs.** -/
theorem tripleGraph_edgeDisjoint_of_rect_disjoint (G : SimpleGraph V) {A B C A' B' C' : Finset V}
    (h : Disjoint (tripleRect A B C) (tripleRect A' B' C')) (x y : V)
    (hxy : (tripleGraph G A B C).Adj x y) : ¬ (tripleGraph G A' B' C').Adj x y := by
  intro hxy'
  have h1 : (x, y) ∈ tripleRect A B C := mem_tripleRect_iff.mpr hxy.2
  have h2 : (x, y) ∈ tripleRect A' B' C' := mem_tripleRect_iff.mpr hxy'.2
  exact (Finset.disjoint_left.mp h h1) h2

omit [Fintype V] [DecidableEq V] in
/-- Two rectangles with disjoint first sides are disjoint. -/
private theorem disjoint_product_left {S T S' T' : Finset V} (h : Disjoint S S') :
    Disjoint (S ×ˢ T) (S' ×ˢ T') := by
  rw [Finset.disjoint_left]
  rintro ⟨x, y⟩ h1 h2
  rw [Finset.mem_product] at h1 h2
  exact (Finset.disjoint_left.mp h h1.1) h2.1

omit [Fintype V] [DecidableEq V] in
/-- Two rectangles with disjoint second sides are disjoint. -/
private theorem disjoint_product_right {S T S' T' : Finset V} (h : Disjoint T T') :
    Disjoint (S ×ˢ T) (S' ×ˢ T') := by
  rw [Finset.disjoint_left]
  rintro ⟨x, y⟩ h1 h2
  rw [Finset.mem_product] at h1 h2
  exact (Finset.disjoint_left.mp h h1.2) h2.2

omit [Fintype V] in
/-- The area of the rectangle of a sub-triple with pairwise disjoint parts. -/
theorem card_tripleRect {A B C : Finset V} (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C) :
    #(tripleRect A B C) = 2 * (#A * #B + #A * #C + #B * #C) := by
  classical
  have hd1 : Disjoint (A ×ˢ B) (B ×ˢ A) := disjoint_product_left hAB
  have hd2 : Disjoint (A ×ˢ C) (C ×ˢ A) := disjoint_product_left hAC
  have hd3 : Disjoint (B ×ˢ C) (C ×ˢ B) := disjoint_product_left hBC
  have nAB := Finset.disjoint_left.mp hAB
  have nAC := Finset.disjoint_left.mp hAC
  have nBC := Finset.disjoint_left.mp hBC
  have hd12 : Disjoint ((A ×ˢ B) ∪ (B ×ˢ A)) ((A ×ˢ C) ∪ (C ×ˢ A)) := by
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    simp only [Finset.mem_union, Finset.mem_product] at h1 h2
    rcases h1 with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rcases h2 with ⟨hx', hy'⟩ | ⟨hx', hy'⟩ <;>
      first
        | exact nAB hx hx' | exact nAB hx' hx | exact nAC hx hx' | exact nAC hx' hx
        | exact nBC hx hx' | exact nBC hx' hx
        | exact nAB hy hy' | exact nAB hy' hy | exact nAC hy hy' | exact nAC hy' hy
        | exact nBC hy hy'
  have hd123 : Disjoint (((A ×ˢ B) ∪ (B ×ˢ A)) ∪ ((A ×ˢ C) ∪ (C ×ˢ A)))
      ((B ×ˢ C) ∪ (C ×ˢ B)) := by
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    simp only [Finset.mem_union, Finset.mem_product] at h1 h2
    rcases h1 with (⟨hx, hy⟩ | ⟨hx, hy⟩) | (⟨hx, hy⟩ | ⟨hx, hy⟩) <;>
      rcases h2 with ⟨hx', hy'⟩ | ⟨hx', hy'⟩ <;>
      first
        | exact nAB hx hx' | exact nAB hx' hx | exact nAC hx hx' | exact nAC hx' hx
        | exact nBC hx hx' | exact nBC hx' hx
        | exact nAB hy hy' | exact nAB hy' hy | exact nAC hy hy'
  rw [tripleRect, Finset.card_union_of_disjoint hd123, Finset.card_union_of_disjoint hd12,
    Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2,
    Finset.card_union_of_disjoint hd3]
  simp only [Finset.card_product]
  ring

/-- **The areas of pairwise disjoint rectangles add up to at most `|V|²`** (natural-number form). -/
theorem sum_area_le_of_rect_disjoint_nat {k : ℕ} (A B C : ℕ → Finset V)
    (hAB : ∀ i < k, Disjoint (A i) (B i)) (hAC : ∀ i < k, Disjoint (A i) (C i))
    (hBC : ∀ i < k, Disjoint (B i) (C i))
    (hdisj : ∀ i < k, ∀ j < k, i ≠ j →
      Disjoint (tripleRect (A i) (B i) (C i)) (tripleRect (A j) (B j) (C j))) :
    2 * ∑ i ∈ Finset.range k, (#(A i) * #(B i) + #(A i) * #(C i) + #(B i) * #(C i))
      ≤ Fintype.card V ^ 2 := by
  classical
  have hpair : ((Finset.range k : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun i => tripleRect (A i) (B i) (C i)) := by
    intro i hi j hj hij
    exact hdisj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij
  have hsum : ∑ i ∈ Finset.range k, #(tripleRect (A i) (B i) (C i))
      = #((Finset.range k).biUnion (fun i => tripleRect (A i) (B i) (C i))) :=
    (Finset.card_biUnion hpair).symm
  have hle : #((Finset.range k).biUnion (fun i => tripleRect (A i) (B i) (C i)))
      ≤ Fintype.card (V × V) := by
    simpa using Finset.card_le_univ
      ((Finset.range k).biUnion (fun i => tripleRect (A i) (B i) (C i)))
  have hcard : Fintype.card (V × V) = Fintype.card V ^ 2 := by
    rw [Fintype.card_prod]; ring
  have hterm : ∀ i ∈ Finset.range k, #(tripleRect (A i) (B i) (C i))
      = 2 * (#(A i) * #(B i) + #(A i) * #(C i) + #(B i) * #(C i)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact card_tripleRect (hAB i hi') (hAC i hi') (hBC i hi')
  calc 2 * ∑ i ∈ Finset.range k, (#(A i) * #(B i) + #(A i) * #(C i) + #(B i) * #(C i))
      = ∑ i ∈ Finset.range k, #(tripleRect (A i) (B i) (C i)) := by
        rw [Finset.mul_sum]
        exact (Finset.sum_congr rfl hterm).symm
    _ = #((Finset.range k).biUnion (fun i => tripleRect (A i) (B i) (C i))) := hsum
    _ ≤ Fintype.card (V × V) := hle
    _ = Fintype.card V ^ 2 := hcard

/-- **The areas of pairwise disjoint rectangles add up to at most `|V|²`.** -/
theorem sum_area_le_of_rect_disjoint {k : ℕ} (A B C : ℕ → Finset V)
    (hAB : ∀ i < k, Disjoint (A i) (B i)) (hAC : ∀ i < k, Disjoint (A i) (C i))
    (hBC : ∀ i < k, Disjoint (B i) (C i))
    (hdisj : ∀ i < k, ∀ j < k, i ≠ j →
      Disjoint (tripleRect (A i) (B i) (C i)) (tripleRect (A j) (B j) (C j))) :
    ∑ i ∈ Finset.range k,
        ((#(A i) : ℝ) * (#(B i) : ℝ) + (#(A i) : ℝ) * (#(C i) : ℝ)
          + (#(B i) : ℝ) * (#(C i) : ℝ))
      ≤ (Fintype.card V : ℝ) ^ 2 / 2 := by
  have h := sum_area_le_of_rect_disjoint_nat A B C hAB hAC hBC hdisj
  have hcast : ((2 * ∑ i ∈ Finset.range k,
      (#(A i) * #(B i) + #(A i) * #(C i) + #(B i) * #(C i)) : ℕ) : ℝ)
      ≤ ((Fintype.card V ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hcast
  linarith

end Nibble.AX1
