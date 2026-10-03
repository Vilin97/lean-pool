/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the **small-box allocation residual** of the coarse-cell route

`Nibble.AX1.BlockCoverResidualCoupled` (`Nibble.CoreGapBlockCoverCoupled`) is reduced, in
`Nibble.CoarseCellCoupled`, to a purely combinatorial *allocation* statement about a grid of coarse
cells, stated here.

The picture.  Every cluster is cut into `P` coarse cells.  A *copy* `c` (one member of the family to
be built) lives on a triple of distinct clusters `cl c 0, cl c 1, cl c 2` and has to occupy, in the
cluster `cl c a`, a set `I c a` of exactly `sz c a` coarse cells — the prescribed size, `sz c a`
being dictated by the density of the pair *opposite* to `a`.  The *same* set `I c a` is seen by both
cluster pairs through `cl c a`, which is the three-way coherence of the allocation.  Two copies
sharing a cluster pair must occupy disjoint rectangles of the cell grid of that pair; by
`Nibble.AX1.boxCompat_iff_disjoint_product` that is the disjunction

    Disjoint (I c a) (I c' a')  ∨  Disjoint (I c b) (I c' b')

for the two positions `a, b` of `c` and `a', b'` of `c'` carrying the shared pair.

`Nibble.AX1.boxDemand` is the total area demanded in one ordered cluster pair, and the hypothesis of
the residual is that it is below a `(1 - ε)` fraction of the capacity `P²` of the grid of the pair.
The conclusion allows a set `bad` of copies to be left unplaced, of total area at most
`ε·(#clusters)²·P²` — the loss this produces in the covering sum of the residual.

The restriction `s₀ ≤ θ·P` to **small boxes** is essential and is what the reduction supplies:
`Nibble.AX1.box_allocation_infeasible` (`Nibble.CellBoxAllocation`) shows that a `P × 1` box and a
`1 × P` box can never be placed compatibly, so no allocation statement without a smallness
restriction can hold.  In the reduction the prescribed sizes are `⌈K·d/δ⌉ ≤ ⌈K/δ⌉`, a
constant, while
the number `P` of cells per cluster grows with the accuracy, so the restriction is met.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Bound
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Finset.Prod
public import Mathlib.Tactic.NormNum


/-! # CellBoxAllocation -/

public section

open Finset

namespace Nibble.AX1

/-- **Compatibility of two boxes in the grid of one cluster pair**: the two rectangles
`I ×ˢ J` and `I' ×ˢ J'` are disjoint exactly when the boxes are disjoint in one of the two
clusters. -/
def BoxCompat {P : ℕ} (I I' J J' : Finset (Fin P)) : Prop := Disjoint I I' ∨ Disjoint J J'

theorem boxCompat_iff_disjoint_product {P : ℕ} (I I' J J' : Finset (Fin P))
    (_hI : I.Nonempty) (_hI' : I'.Nonempty) (_hJ : J.Nonempty) (_hJ' : J'.Nonempty) :
    BoxCompat I I' J J' ↔ Disjoint (I ×ˢ J) (I' ×ˢ J') := by
  constructor
  · rintro (h | h)
    · rw [Finset.disjoint_left]
      rintro ⟨x, y⟩ hx hy
      exact (Finset.disjoint_left.mp h) (Finset.mem_product.mp hx).1
        (Finset.mem_product.mp hy).1
    · rw [Finset.disjoint_left]
      rintro ⟨x, y⟩ hx hy
      exact (Finset.disjoint_left.mp h) (Finset.mem_product.mp hx).2
        (Finset.mem_product.mp hy).2
  · intro h
    by_contra hc
    simp only [BoxCompat, not_or] at hc
    obtain ⟨h1, h2⟩ := hc
    rw [Finset.not_disjoint_iff] at h1 h2
    obtain ⟨x, hx, hx'⟩ := h1
    obtain ⟨y, hy, hy'⟩ := h2
    refine (Finset.disjoint_left.mp h) (a := (x, y)) (Finset.mem_product.mpr ⟨hx, hy⟩) ?_
    exact Finset.mem_product.mpr ⟨hx', hy'⟩

/-- **The box allocation is infeasible at general densities.**  A `P × 1` box and a `1 × P` box in
the same cluster-pair grid — the shapes forced by two cluster triples through the pair whose two
other densities are opposite extremes — cannot be placed compatibly, although their total area
`2·P` is a `2/P` fraction of the capacity `P²`. -/
theorem box_allocation_infeasible {P : ℕ} (I I' J J' : Finset (Fin P))
    (hI : #I = P) (hJ : #J = 1) (hI' : #I' = 1) (hJ' : #J' = P) :
    ¬ BoxCompat I I' J J' := by
  have hcard : Fintype.card (Fin P) = P := Fintype.card_fin P
  have hIu : I = univ := by
    apply Finset.eq_univ_of_card
    rw [hI, hcard]
  have hJ'u : J' = univ := by
    apply Finset.eq_univ_of_card
    rw [hJ', hcard]
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [hI']; norm_num : 0 < #I')
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by rw [hJ]; norm_num : 0 < #J)
  rintro (h | h)
  · exact (Finset.disjoint_left.mp h) (hIu ▸ Finset.mem_univ x) hx
  · exact (Finset.disjoint_left.mp h) hy (hJ'u ▸ Finset.mem_univ y)

/-! ### Axiom check -/

section AxCheck




end AxCheck

end Nibble.AX1

end


/-! # BoxAllocationSpec -/

public section

open Finset

namespace Nibble.AX1

/-- **The area demanded in the ordered cluster pair `(S, T)`**: every copy through both clusters
contributes the product of its two prescribed sizes there. -/
@[expose] def boxDemand {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (cl : κ → ZMod 3 → ι) (sz : κ → ZMod 3 → ℕ) (S T : ι) : ℝ :=
  ∑ c : κ, ∑ a : ZMod 3, ∑ b : ZMod 3,
    if cl c a = S ∧ cl c b = T then (sz c a : ℝ) * (sz c b : ℝ) else 0

/-- **The small-box allocation residual.**  For every accuracy `ε` and every box bound `s₀` there is
a smallness threshold `θ` such that, whenever the prescribed sizes are at most `s₀ ≤ θ·P` and the
demand of every cluster pair is at most `(1 - ε)·P²`, all copies can be given cell sets of the
prescribed sizes, three-way coherent by construction, so that any two copies sharing a cluster pair
occupy disjoint rectangles of the cell grid of that pair — apart from a set `bad` of copies of total
area at most `ε·(#clusters)²·P²`.

The threshold `θ` is allowed to depend on the box bound `s₀` as well as on `ε`.  This is what the
reduction of `Nibble.CoarseCellCoupled` supplies (there `s₀ = ⌈K/δ⌉` is fixed by the accuracy of the
block-cover residual, while the number `P` of cells per cluster is driven to infinity afterwards),
and it is what a nibble proof needs: the placement hypergraph has uniformity of order `s₀²`, and the
codegree threshold of `Nibble.fracNibbleWeighted_nearPerfect` degrades with the uniformity, so `θ`
cannot be chosen before `s₀` is known. -/
@[expose] def BoxAllocationResidual : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ s₀ : ℕ, ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
    ∀ P : ℕ, 0 < P → (s₀ : ℝ) ≤ θ * (P : ℝ) →
    ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      (cl : κ → ZMod 3 → ι) (sz : κ → ZMod 3 → ℕ),
      (∀ c, Function.Injective (cl c)) →
      (∀ c a, 1 ≤ sz c a) → (∀ c a, sz c a ≤ s₀) →
      (∀ S T : ι, S ≠ T → boxDemand cl sz S T ≤ (1 - ε) * (P : ℝ) ^ 2) →
      ∃ (bad : Finset κ) (I : κ → ZMod 3 → Finset (Fin P)),
        (∀ c a, #(I c a) = sz c a) ∧
        (∀ c ∉ bad, ∀ c' ∉ bad, c ≠ c' → ∀ a b a' b' : ZMod 3, a ≠ b → a' ≠ b' →
          cl c a = cl c' a' → cl c b = cl c' b' →
          Disjoint (I c a) (I c' a') ∨ Disjoint (I c b) (I c' b')) ∧
        (∑ c ∈ bad, ∑ a : ZMod 3, (sz c a : ℝ) * (sz c (a + 1) : ℝ))
          ≤ ε * (Fintype.card ι : ℝ) ^ 2 * (P : ℝ) ^ 2

end Nibble.AX1
