/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.ParitySplitting

/-!
# Theorem 2.8: two-sided polygonal crosscuts

A crosscut `P` of a simple closed polygon `C` cuts one of the two regions of `ℝ² ∖ C` into
exactly two, bounded by the two curves `Jᵢ = Aᵢ ∪ P`; and `ℝ² ∖ (C ∪ P)` then has exactly three
regions, with boundaries `C, J₁, J₂`.

## One theorem, not two

The blueprint splits the statement into case (a), the crosscut inside `C`, and case (b), the
crosscut outside. The two cases differ only in *which* region of `ℝ² ∖ Jᵢ` is the new cell: in
case (a) it is `Int(Jᵢ)` for both `i`, while in case (b) it is `Ext(J₁)` for one index and
`Int(J₂)` for the other, and which is which is not determined by the data. What *is* uniform is
the description "the region of `ℝ² ∖ Jᵢ` on the far side from a point `y` of the region of
`ℝ² ∖ C` that the crosscut does not enter". So the whole theorem is proved once, for

    farRegion J y  =  the region of `ℝ² ∖ J` that does not contain `y`,

and the two cases of the blueprint are then read off by identifying `farRegion` with `inside`
or with `outside` (`IsSeparating.farRegion_eq_inside`, `…_eq_outside`). A reference point `y`
in the untouched region is the one extra datum this costs, and it is exactly the datum the
blueprint hides in the phrase "let `Ω` be the region containing `P ∖ {p, q}`".

## Exhaustion is pure parity, in both cases at once

Lemma 2.6 (`Schoenflies.crosscut_cells`) already exhibits the two cells as components of
`Ω ∖ P`. All that Theorem 2.8 adds is that there are no others, and the blueprint reads this
off Lemma 2.7. Here the reading is uniform. Write `πJ` for the crossing count of a curve `J`.
For points `x, y` off `J` — Theorem 2.3 —

    `x` and `y` lie in different regions of `ℝ² ∖ J`  ↔  `πJ(x) ≠ πJ(y)`,

which is `ClosedPolygon.parity_ne_iff_mem_farRegion`. Lemma 2.7 gives
`πJ₁ + πJ₂ = πC` at every point, so subtracting the identity at `y` from the identity at `x`
turns "`x` is separated from `y` by `C`" into "`x` is separated from `y` by exactly one of
`J₁, J₂`" — `IsPolygonalCrosscut.separates_xor`, whose entire proof is sixteen cases of `ZMod 2`
arithmetic. No case distinction on inside/outside is made anywhere.

## The hypotheses, bundled

`IsPolygonalCrosscut C J₁ J₂ K a k y` collects the seven hypotheses of the theorem: the two
curves of the split carry the right edges (`Schoenflies.SameEdges`, from Lemma 2.7), the
crosscut meets `C` only in points common to both arcs, and the reference point `y` lies off `C`
in a region the crosscut does not enter. It is closed under swapping the two arcs
(`IsPolygonalCrosscut.symm`), which is why every statement below is proved for index `1` only.

Realizing `J₁` and `J₂` as `ClosedPolygon`s is the consumer's job, exactly as in Lemma 2.7 —
see the note there about the `corner` field. Nothing in this file inspects `corner`.

## Blueprint

* `farRegion`, `IsSeparating.isRegionPair_farRegion`, `IsSeparating.farRegion_eq_inside`,
  `IsSeparating.farRegion_eq_outside` — the blueprint's `Ω`, `Ω†`, `Vᵢ` and `Wᵢ` named as
  functions of a reference point instead of by an existential.
* `ClosedPolygon.arc` — the arcs `A₁, A₂` of Theorem 2.8, as sets; `…vertex_mem_arc`,
  `…vertex_add_mem_arc`, `…endpoints_subset_arc`, `…endpoints_subset_arc'` — the two cut
  vertices lie on both arcs, which is what "the crosscut meets `C` only in its endpoints" has
  to say to be usable.
* `ClosedPolygon.parity_ne_iff_mem_farRegion` — Theorem 2.3 read as a separation criterion.
* `IsPolygonalCrosscut` — the hypotheses of Theorem 2.8; `IsPolygonalCrosscut.of_endpoints` is
  the constructor a consumer should use, and `IsPolygonalCrosscut.symm` swaps the two arcs.
* `IsPolygonalCrosscut.separates_xor` — Lemma 2.7's "consequently", in the uniform form.
* `IsPolygonalCrosscut.region_eq`, `…cells_disjoint`, `…cells_ne`, `…cell_isComponent₁/₂`,
  `…frontier_cell₁/₂`, `…closure_cell_inter₁/₂` — the two cells of `Ω ∖ P`.
* `IsPolygonalCrosscut.inside_diff_eq` — Theorem 2.8(a).
* `IsPolygonalCrosscut.outside_diff_eq`, `…inside_exactly_one` — Theorem 2.8(b).
* `IsPolygonalCrosscut.compl_eq`, `…isComponent`, `…near_isComponent`,
  `…cell_isComponent_compl₁/₂`, `…cell_ne_near₁/₂`, `…frontier_near` — "in either case
  `ℝ² ∖ (C ∪ P)` has exactly three regions, with boundaries `C, J₁, J₂`".
* `polygonal_crosscut` — Theorem 2.8, bundled.
-/

public section

open Bornology Set

namespace Schoenflies

variable {C J P Ω Ω' W V : Set Plane} {x y z : Plane}

/-! ## The region on the far side of a point

The blueprint names the four regions in play — `Ω`, `Ω†`, `Wᵢ`, `Vᵢ` — by their relation to one
another: `Ω†` is the region of `ℝ² ∖ C` the crosscut does not enter, and `Vᵢ` is the region of
`ℝ² ∖ Jᵢ` on the other side of `Jᵢ` from `Ω†`. Fixing a point `y ∈ Ω†` turns all four into
functions of the data. -/

/-- The region of `ℝ² ∖ C` that does **not** contain `y`: everything off `C` except the
component of `y`. For a separating curve this really is the other region
(`IsSeparating.isRegionPair_farRegion`); no hypothesis is needed to define it. -/
def farRegion (C : Set Plane) (y : Plane) : Set Plane := Cᶜ \ connectedComponentIn Cᶜ y

theorem mem_farRegion_iff : x ∈ farRegion C y ↔ x ∉ C ∧ x ∉ connectedComponentIn Cᶜ y := Iff.rfl

theorem farRegion_subset_compl : farRegion C y ⊆ Cᶜ := fun _ hx => hx.1

theorem notMem_farRegion_self (hy : y ∉ C) : y ∉ farRegion C y :=
  fun h => h.2 (mem_connectedComponentIn hy)

/-- Off the curve, being in the far region is exactly being in another component. -/
theorem mem_farRegion_iff_connectedComponentIn_ne (hx : x ∉ C) :
    x ∈ farRegion C y ↔ connectedComponentIn Cᶜ x ≠ connectedComponentIn Cᶜ y := by
  refine ⟨fun h hEq => h.2 (hEq ▸ mem_connectedComponentIn hx), fun h => ⟨hx, fun hmem => ?_⟩⟩
  exact h (connectedComponentIn_eq hmem).symm

/-- The crosscut misses the region of `y`, so all of it off the curve is in the far region. -/
theorem diff_subset_farRegion (hdis : Disjoint P (connectedComponentIn Cᶜ y)) :
    P \ C ⊆ farRegion C y :=
  fun _ hz => ⟨hz.2, fun hmem => Set.disjoint_left.1 hdis hz.1 hmem⟩

theorem compl_diff_inside (C : Set Plane) : Cᶜ \ inside C = outside C := by
  ext w
  constructor
  · rintro ⟨hw, hwin⟩
    have hcov : w ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hw
    exact hcov.resolve_left hwin
  · exact fun hw => ⟨hw.1, fun h => Set.disjoint_left.1 disjoint_inside_outside h hw⟩

theorem compl_diff_outside (C : Set Plane) : Cᶜ \ outside C = inside C := by
  ext w
  constructor
  · rintro ⟨hw, hwout⟩
    have hcov : w ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hw
    exact hcov.resolve_right hwout
  · exact fun hw => ⟨hw.1, fun h => Set.disjoint_left.1 disjoint_inside_outside hw h⟩

/-- The component of `y` and the far region are *the* two regions of `ℝ² ∖ C`. -/
theorem IsSeparating.isRegionPair_farRegion (hC : IsSeparating C) (hy : y ∉ C) :
    IsRegionPair C (connectedComponentIn Cᶜ y) (farRegion C y) := by
  rcases hC.isRegionOf_connectedComponentIn hy with hc | hc
  · exact Or.inl ⟨hc, by rw [farRegion, hc, compl_diff_inside]⟩
  · exact Or.inr ⟨hc, by rw [farRegion, hc, compl_diff_outside]⟩

theorem IsSeparating.isRegionOf_farRegion (hC : IsSeparating C) (hy : y ∉ C) :
    IsRegionOf C (farRegion C y) := (hC.isRegionPair_farRegion hy).right

/-- Seen from the unbounded region, the far region is the bounded one — the blueprint's case
(a), where `Vᵢ = Int(Jᵢ)`. -/
theorem IsSeparating.farRegion_eq_inside (hC : IsSeparating C) (hy : y ∈ outside C) :
    farRegion C y = inside C := by
  rw [farRegion, hC.connectedComponentIn_eq_outside hy, compl_diff_outside]

/-- Seen from the bounded region, the far region is the unbounded one. -/
theorem IsSeparating.farRegion_eq_outside (hC : IsSeparating C) (hy : y ∈ inside C) :
    farRegion C y = outside C := by
  rw [farRegion, hC.connectedComponentIn_eq_inside hy, compl_diff_inside]

/-! ## The three regions of `ℝ² ∖ (C ∪ P)`, abstractly

Lemma 2.6 places the two cells inside `Ω ∖ P`; the last paragraph of the proof of Theorem 2.8
places all three regions inside `ℝ² ∖ (C ∪ P)`, and the argument is the same each time: an open
connected set whose frontier misses the ambient open set is a component of it (Lemma 1.7). -/

/-- `ℝ² ∖ (C ∪ P)` is `Ω ∖ P` together with the untouched region `Ω'`. -/
theorem compl_union_eq_of_isRegionPair (hΩ : IsRegionPair C Ω Ω') (hdis : Disjoint P Ω') :
    (C ∪ P)ᶜ = (Ω \ P) ∪ Ω' := by
  ext w
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_sdiff, not_or]
  constructor
  · rintro ⟨hwC, hwP⟩
    have hcov : w ∈ Ω ∪ Ω' := by rw [hΩ.union_eq]; exact hwC
    exact hcov.imp (fun h => ⟨h, hwP⟩) id
  · rintro (⟨hwΩ, hwP⟩ | hwΩ')
    · exact ⟨hΩ.left.subset_compl hwΩ, hwP⟩
    · exact ⟨hΩ.right.subset_compl hwΩ', fun hwP => Set.disjoint_left.1 hdis hwP hwΩ'⟩

/-- The untouched region is a component of `ℝ² ∖ (C ∪ P)`: its frontier is `C`. -/
theorem far_isComponent (hC : IsSeparating C) (hΩ : IsRegionPair C Ω Ω')
    (hdis : Disjoint P Ω') (hz : z ∈ Ω') : connectedComponentIn (C ∪ P)ᶜ z = Ω' := by
  refine Plane.connectedComponentIn_eq_of_frontier_disjoint (hΩ.right.isOpen hC)
    (hΩ.right.isConnected hC).isPreconnected (fun w hw => ?_) ?_ hz
  · rintro (h | h)
    · exact hΩ.right.subset_compl hw h
    · exact Set.disjoint_left.1 hdis h hw
  · rw [hΩ.right.frontier_eq hC]
    refine Set.eq_empty_iff_forall_notMem.2 ?_
    rintro w ⟨hwC, hw⟩
    exact hw (Or.inl hwC)

/-- A cell is a component of `ℝ² ∖ (C ∪ P)`: its frontier is `J ⊆ C ∪ P`. -/
theorem cell_isComponent_compl (hJ : IsSeparating J) (hWV : IsRegionPair J W V)
    (hJCP : J ⊆ C ∪ P) (hV : V ⊆ (C ∪ P)ᶜ) (hz : z ∈ V) :
    connectedComponentIn (C ∪ P)ᶜ z = V := by
  refine Plane.connectedComponentIn_eq_of_frontier_disjoint (hWV.right.isOpen hJ)
    (hWV.right.isConnected hJ).isPreconnected hV ?_ hz
  rw [hWV.right.frontier_eq hJ]
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro w ⟨hwJ, hw⟩
  exact hw (hJCP hwJ)

/-! ## The arcs of a polygon, and parity as a separation criterion -/

/-- Going `k` steps forward and then the remaining `m + 3 - k` returns to where one started:
the second arc of a split ends at the first arc's starting vertex. -/
theorem zmod_add_sub_cancel {m k : ℕ} (hk : k ≤ m + 3) (a : ZMod (m + 3)) :
    a + (k : ZMod (m + 3)) + ((m + 3 - k : ℕ) : ZMod (m + 3)) = a := by
  have hcast : ((k : ℕ) : ZMod (m + 3)) + ((m + 3 - k : ℕ) : ZMod (m + 3)) = 0 := by
    rw [← Nat.cast_add, show k + (m + 3 - k) = m + 3 by omega]
    exact ZMod.natCast_self _
  rw [add_assoc, hcast, add_zero]

namespace ClosedPolygon

variable {m : ℕ} {C : ClosedPolygon m} {a : ZMod (m + 3)} {k : ℕ}

/-- The arc of `C` that leaves vertex `a` and runs forward through `k` edges, as a set: the
blueprint's `A₁` for `k` edges and `A₂` for the remaining `m + 3 - k`. -/
def arc (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) : Set Plane := cover (C.arcPieces a k)

theorem arc_subset_carrier (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    C.arc a k ⊆ C.carrier := cover_arcPieces_subset C a k

/-- The two arcs cover the polygon. -/
theorem arc_union (C : ClosedPolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    C.arc a k ∪ C.arc (a + k) (m + 3 - k) = C.carrier := cover_arcPieces_union C a hk

/-- A curve of the split occupies its arc together with the crosscut. -/
theorem carrier_eq_arc_union {m' : ℕ} {J : ClosedPolygon m'} {K : List Piece}
    (h : SameEdges J.pieces (C.arcPieces a k ++ K)) : J.carrier = C.arc a k ∪ cover K :=
  carrier_eq_of_sameEdges h

/-- **The crossing count separates points exactly as the polygon does** (Theorem 2.3, read as a
criterion). Two points off the polygon lie in different regions precisely when their crossing
counts differ: equal components force equal counts by Lemma 2.2, and different components are
the bounded and the unbounded one, whose counts are `1` and `0`. -/
theorem parity_ne_iff_mem_farRegion (C : ClosedPolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∉ C.carrier) (hy : y ∉ C.carrier) :
    parity u C.pieces x ≠ parity u C.pieces y ↔ x ∈ farRegion C.carrier y := by
  rw [mem_farRegion_iff_connectedComponentIn_ne hx]
  constructor
  · intro hne heq
    exact hne (C.parity_eq_of_mem_connectedComponentIn_carrier hu hL hy
      (heq ▸ mem_connectedComponentIn hx))
  · intro hne
    rcases C.connectedComponentIn_eq_inside_or_outside hx with hxr | hxr <;>
      rcases C.connectedComponentIn_eq_inside_or_outside hy with hyr | hyr
    · exact absurd (hxr.trans hyr.symm) hne
    · rw [C.parity_eq_one_of_mem_inside hu hL (hxr ▸ mem_connectedComponentIn hx),
        C.parity_eq_zero_of_mem_outside hu hL (hyr ▸ mem_connectedComponentIn hy)]
      decide
    · rw [C.parity_eq_zero_of_mem_outside hu hL (hxr ▸ mem_connectedComponentIn hx),
        C.parity_eq_one_of_mem_inside hu hL (hyr ▸ mem_connectedComponentIn hy)]
      decide
    · exact absurd (hxr.trans hyr.symm) hne

/-- The first vertex of a nonempty arc lies on it. -/
theorem vertex_mem_arc (C : ClosedPolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    C.vertex a ∈ C.arc a k := by
  have h0 : a + ((0 : ℕ) : ZMod (m + 3)) = a := by rw [Nat.cast_zero, add_zero]
  refine mem_cover (P := (C.vertex a, C.vertex (a + 1))) ?_ ?_
  · exact List.mem_map.2 ⟨0, List.mem_range.2 hk, by rw [h0]⟩
  · exact left_mem_segment ℝ _ _

/-- The last vertex of a nonempty arc lies on it. -/
theorem vertex_add_mem_arc (C : ClosedPolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    C.vertex (a + k) ∈ C.arc a k := by
  have hlast : a + ((k - 1 : ℕ) : ZMod (m + 3)) + 1 = a + (k : ZMod (m + 3)) := by
    have : ((k - 1 : ℕ) : ZMod (m + 3)) + 1 = ((k : ℕ) : ZMod (m + 3)) := by
      rw [show ((k : ℕ) : ZMod (m + 3)) = (((k - 1) + 1 : ℕ) : ZMod (m + 3)) by
        congr 1; omega, Nat.cast_add, Nat.cast_one]
    rw [add_assoc, this]
  refine mem_cover (P := (C.vertex (a + ((k - 1 : ℕ) : ZMod (m + 3))),
    C.vertex (a + ((k - 1 : ℕ) : ZMod (m + 3)) + 1))) ?_ ?_
  · exact List.mem_map.2 ⟨k - 1, List.mem_range.2 (by omega), rfl⟩
  · rw [Piece.seg, hlast]
    exact right_mem_segment ℝ _ _

/-- **The two cut vertices lie on both arcs.** This is what turns the blueprint's "the crosscut
meets `C` only in its two endpoints" into the hypotheses `meets₁` and `meets₂`. -/
theorem endpoints_subset_arc (C : ClosedPolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    ({C.vertex a, C.vertex (a + k)} : Set Plane) ⊆ C.arc a k := by
  rintro w (rfl | rfl)
  · exact C.vertex_mem_arc a hk
  · exact C.vertex_add_mem_arc a hk

/-- The same for the complementary arc, whose two ends are the same two vertices in the other
order. -/
theorem endpoints_subset_arc' (C : ClosedPolygon m) (a : ZMod (m + 3)) (hk2 : k ≤ m + 2) :
    ({C.vertex a, C.vertex (a + k)} : Set Plane) ⊆ C.arc (a + k) (m + 3 - k) := by
  have hpos : 1 ≤ m + 3 - k := by omega
  have hwrap := zmod_add_sub_cancel (k := k) (by omega) a
  rintro w (rfl | rfl)
  · have hm := C.vertex_add_mem_arc (a + k) hpos
    rwa [hwrap] at hm
  · exact C.vertex_mem_arc (a + k) hpos

end ClosedPolygon

/-! ## The hypotheses of Theorem 2.8 -/

variable {m m₁ m₂ : ℕ} {C : ClosedPolygon m} {J₁ : ClosedPolygon m₁} {J₂ : ClosedPolygon m₂}
  {K : List Piece} {a : ZMod (m + 3)} {k : ℕ}

/-- **The setting of Theorem 2.8.** `K` is the edge list of a polygonal crosscut of the polygon
`C`, cutting it at the vertices `a` and `a + k`; `J₁` and `J₂` are the two closed curves formed
by the crosscut with each of the two arcs; and `y` is a point of the region of `ℝ² ∖ C` that the
crosscut does not enter, which is what fixes which side of `C` the crosscut is on.

The blueprint's "`P` is a simple arc meeting `C` exactly in its two endpoints" appears here in
two pieces: `meets₁` and `meets₂` say that whatever the crosscut has in common with `C` lies on
*both* arcs, which for a genuine crosscut is the two cut vertices (`ClosedPolygon.vertex_mem_arc`,
`ClosedPolygon.vertex_add_mem_arc`); and simplicity is carried by the assumption that `J₁` and
`J₂` really are `ClosedPolygon`s. Nothing else about `K` is assumed — not even that its pieces
are nondegenerate, which follows from `edges₁`. -/
structure IsPolygonalCrosscut (C : ClosedPolygon m) (J₁ : ClosedPolygon m₁)
    (J₂ : ClosedPolygon m₂) (K : List Piece) (a : ZMod (m + 3)) (k : ℕ) (y : Plane) : Prop where
  /-- The first arc runs forward through at most a full turn. -/
  le : k ≤ m + 3
  /-- `J₁` carries the edges of the first arc together with those of the crosscut. -/
  edges₁ : SameEdges J₁.pieces (C.arcPieces a k ++ K)
  /-- `J₂` carries the edges of the second arc together with those of the crosscut. -/
  edges₂ : SameEdges J₂.pieces (C.arcPieces (a + k) (m + 3 - k) ++ K)
  /-- The crosscut meets the polygon only in points of the first arc … -/
  meets₁ : cover K ∩ C.carrier ⊆ C.arc a k
  /-- … and only in points of the second arc. -/
  meets₂ : cover K ∩ C.carrier ⊆ C.arc (a + k) (m + 3 - k)
  /-- The reference point lies off the polygon … -/
  notMem : y ∉ C.carrier
  /-- … and the crosscut does not enter its region. -/
  avoids : Disjoint (cover K) (connectedComponentIn C.carrierᶜ y)

/-- **The front door.** A crosscut is normally presented by saying that it meets `C` exactly in
its two endpoints, and that those endpoints are the two cut vertices; `meets₁` and `meets₂`
follow, because both cut vertices lie on both arcs. The bound `k ≤ m + 2` says the second arc is
nonempty, as `1 ≤ k` says the first one is. -/
theorem IsPolygonalCrosscut.of_endpoints {y : Plane} (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2)
    (edges₁ : SameEdges J₁.pieces (C.arcPieces a k ++ K))
    (edges₂ : SameEdges J₂.pieces (C.arcPieces (a + k) (m + 3 - k) ++ K))
    (meets : cover K ∩ C.carrier ⊆ ({C.vertex a, C.vertex (a + k)} : Set Plane))
    (notMem : y ∉ C.carrier)
    (avoids : Disjoint (cover K) (connectedComponentIn C.carrierᶜ y)) :
    IsPolygonalCrosscut C J₁ J₂ K a k y :=
  ⟨by omega, edges₁, edges₂, meets.trans (C.endpoints_subset_arc a hk1),
    meets.trans (C.endpoints_subset_arc' a hk2), notMem, avoids⟩

namespace IsPolygonalCrosscut

variable {y : Plane} (h : IsPolygonalCrosscut C J₁ J₂ K a k y)
include h

/-- **The two arcs may be swapped.** Every statement below is therefore proved for `J₁` only. -/
theorem symm : IsPolygonalCrosscut C J₂ J₁ K (a + k) (m + 3 - k) y := by
  have hk : k ≤ m + 3 := h.le
  have hnat : m + 3 - (m + 3 - k) = k := by omega
  have hzmod := zmod_add_sub_cancel (k := k) hk a
  refine ⟨by omega, h.edges₂, ?_, h.meets₂, ?_, h.notMem, h.avoids⟩
  · rw [hzmod, hnat]; exact h.edges₁
  · rw [hzmod, hnat]; exact h.meets₁

/-! ### The elementary consequences -/

theorem notMem_cover : y ∉ cover K :=
  fun hy => Set.disjoint_left.1 h.avoids hy (mem_connectedComponentIn h.notMem)

theorem carrier₁ : J₁.carrier = C.arc a k ∪ cover K :=
  ClosedPolygon.carrier_eq_arc_union h.edges₁

theorem notMem_carrier₁ : y ∉ J₁.carrier :=
  ClosedPolygon.notMem_carrier_of_sameEdges h.edges₁ h.notMem h.notMem_cover

theorem cover_subset_carrier₁ : cover K ⊆ J₁.carrier := by
  rw [h.carrier₁]; exact Set.subset_union_right

theorem carrier₁_subset : J₁.carrier ⊆ C.carrier ∪ cover K := by
  rw [h.carrier₁]
  exact Set.union_subset_union_left _ (C.arc_subset_carrier a k)

/-- The edges of the crosscut are nondegenerate, because they are edges of `J₁`. -/
theorem nondeg : ∀ Q ∈ K, Q.Nondeg := by
  intro Q hQ
  obtain ⟨R, hR, hRQ⟩ := h.edges₁.symm.exists_mem (List.mem_append_right _ hQ)
  have hRn : (orientPiece R).Nondeg := orientPiece_nondeg (J₁.pieces_nondeg R hR)
  rw [hRQ] at hRn
  rcases orientPiece_eq_or Q with e | e
  · rw [e] at hRn; exact hRn
  · rw [e] at hRn; exact fun hh => hRn hh.symm

/-- A ray direction transverse to every edge of `C` and of the crosscut at once. -/
theorem exists_direction : ∃ u : Plane, Plane.IsDirection u ∧
    (∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2) ∧ (∀ Q ∈ K, hgt u Q.1 ≠ hgt u Q.2) := by
  obtain ⟨u, hu, hlev⟩ := exists_direction_hgt_ne (C.pieces ++ K) (by
    intro Q hQ
    rcases List.mem_append.1 hQ with hQ' | hQ'
    · exact C.pieces_nondeg Q hQ'
    · exact h.nondeg Q hQ')
  exact ⟨u, hu, fun Q hQ => hlev Q (List.mem_append_left _ hQ),
    fun Q hQ => hlev Q (List.mem_append_right _ hQ)⟩

/-! ### The two cells

Lemma 2.6 applies with `Ω = farRegion C.carrier y`, `Ω' = connectedComponentIn C.carrierᶜ y`,
`Wᵢ = connectedComponentIn Jᵢ.carrierᶜ y` and `Vᵢ = farRegion Jᵢ.carrier y`. The inclusion
`Ω' ⊆ Wᵢ` — the blueprint's "being connected it lies in one region of `ℝ² ∖ Jᵢ`" — is
`near_subset₁`, and needs no separation hypothesis at all. -/

theorem regionPairC :
    IsRegionPair C.carrier (farRegion C.carrier y) (connectedComponentIn C.carrierᶜ y) :=
  (C.isSeparating_carrier.isRegionPair_farRegion h.notMem).symm

theorem regionPair₁ :
    IsRegionPair J₁.carrier (connectedComponentIn J₁.carrierᶜ y) (farRegion J₁.carrier y) :=
  J₁.isSeparating_carrier.isRegionPair_farRegion h.notMem_carrier₁

/-- The untouched region of `ℝ² ∖ C` lies in one region of `ℝ² ∖ J₁`, namely the one of `y`. -/
theorem near_subset₁ :
    connectedComponentIn C.carrierᶜ y ⊆ connectedComponentIn J₁.carrierᶜ y := by
  refine IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
    (mem_connectedComponentIn h.notMem) (fun w hw => ?_)
  have hwC : w ∉ C.carrier := connectedComponentIn_subset _ _ hw
  have hwK : w ∉ cover K := fun hK => Set.disjoint_left.1 h.avoids hK hw
  exact ClosedPolygon.notMem_carrier_of_sameEdges h.edges₁ hwC hwK

/-- **Lemma 2.6(a), first half**: the cell lies in `Ω ∖ P`. -/
theorem cell_subset₁ : farRegion J₁.carrier y ⊆ farRegion C.carrier y \ cover K :=
  cell_subset_region_diff (P := cover K) C.isSeparating_carrier J₁.isSeparating_carrier
    h.regionPairC h.regionPair₁ h.near_subset₁ h.cover_subset_carrier₁

theorem cell_subset₂ : farRegion J₂.carrier y ⊆ farRegion C.carrier y \ cover K :=
  h.symm.cell_subset₁

/-- **Lemma 2.6(a)**: the cell is a connected component of `Ω ∖ P`. -/
theorem cell_isComponent₁ : ∀ z ∈ farRegion J₁.carrier y,
    connectedComponentIn (farRegion C.carrier y \ cover K) z = farRegion J₁.carrier y :=
  cell_isComponent (P := cover K) C.isSeparating_carrier J₁.isSeparating_carrier
    h.regionPairC h.regionPair₁ h.near_subset₁ h.cover_subset_carrier₁ h.carrier₁_subset

theorem cell_isComponent₂ : ∀ z ∈ farRegion J₂.carrier y,
    connectedComponentIn (farRegion C.carrier y \ cover K) z = farRegion J₂.carrier y :=
  h.symm.cell_isComponent₁

/-- **Lemma 2.6(c)**: the closure of the cell meets the polygon exactly in its arc. -/
theorem closure_cell_inter₁ : closure (farRegion J₁.carrier y) ∩ C.carrier = C.arc a k := by
  rw [closure_cell_inter_curve C.isSeparating_carrier J₁.isSeparating_carrier
    h.regionPairC.right h.regionPair₁ h.near_subset₁, h.carrier₁]
  refine Set.Subset.antisymm ?_ (fun w hw => ⟨Or.inl hw, C.arc_subset_carrier a k hw⟩)
  rintro w ⟨hw | hw, hwC⟩
  · exact hw
  · exact h.meets₁ ⟨hw, hwC⟩

theorem closure_cell_inter₂ :
    closure (farRegion J₂.carrier y) ∩ C.carrier = C.arc (a + k) (m + 3 - k) :=
  h.symm.closure_cell_inter₁

/-- The cell has `J₁` as its frontier. -/
theorem frontier_cell₁ : frontier (farRegion J₁.carrier y) = J₁.carrier :=
  h.regionPair₁.right.frontier_eq J₁.isSeparating_carrier

theorem frontier_cell₂ : frontier (farRegion J₂.carrier y) = J₂.carrier :=
  h.symm.frontier_cell₁

theorem cell_nonempty₁ : (farRegion J₁.carrier y).Nonempty :=
  (h.regionPair₁.right.isConnected J₁.isSeparating_carrier).nonempty

/-! ### Exhaustion: the crossing counts add up

This is the whole of Theorem 2.8 beyond Lemma 2.6, and it is one `ZMod 2` computation. -/

/-- **A point off `C ∪ P` is separated from `y` by `C` exactly when it is separated from `y` by
exactly one of `J₁, J₂`.** Lemma 2.7 gives `πJ₁ + πJ₂ = πC` at every point; evaluating it at `x`
and at `y` and subtracting turns the three "different region" statements — which Theorem 2.3
reads off the three crossing counts — into the exclusive disjunction. -/
theorem separates_xor {x : Plane} (hxC : x ∉ C.carrier) (hxK : x ∉ cover K) :
    x ∈ farRegion C.carrier y ↔
      (x ∈ farRegion J₁.carrier y ↔ ¬ x ∈ farRegion J₂.carrier y) := by
  obtain ⟨u, hu, hlevC, hlevK⟩ := h.exists_direction
  have hlev₁ := h.edges₁.hgt_ne (ClosedPolygon.arcPieces_append_hgt_ne hlevC hlevK)
  have hlev₂ := h.edges₂.hgt_ne (ClosedPolygon.arcPieces_append_hgt_ne hlevC hlevK)
  have hxJ₁ := ClosedPolygon.notMem_carrier_of_sameEdges h.edges₁ hxC hxK
  have hxJ₂ := ClosedPolygon.notMem_carrier_of_sameEdges h.edges₂ hxC hxK
  rw [← C.parity_ne_iff_mem_farRegion hu hlevC hxC h.notMem,
    ← J₁.parity_ne_iff_mem_farRegion hu hlev₁ hxJ₁ h.notMem_carrier₁,
    ← J₂.parity_ne_iff_mem_farRegion hu hlev₂ hxJ₂ h.symm.notMem_carrier₁]
  have hsx := C.parity_splitting u a h.le h.edges₁ h.edges₂ x
  have hsy := C.parity_splitting u a h.le h.edges₁ h.edges₂ y
  have key : ∀ s₁ s₂ s t₁ t₂ t : ZMod 2, s₁ + s₂ = s → t₁ + t₂ = t →
      (s ≠ t ↔ ((s₁ ≠ t₁) ↔ ¬ (s₂ ≠ t₂))) := by decide
  exact key _ _ _ _ _ _ hsx hsy

/-- **Theorem 2.8, the two cells.** The region the crosscut enters, with the crosscut removed,
is the disjoint union of the two cells. -/
theorem region_eq :
    farRegion C.carrier y \ cover K = farRegion J₁.carrier y ∪ farRegion J₂.carrier y := by
  refine Set.Subset.antisymm ?_ (Set.union_subset h.cell_subset₁ h.cell_subset₂)
  rintro w ⟨hwΩ, hwK⟩
  by_cases hw₁ : w ∈ farRegion J₁.carrier y
  · exact Or.inl hw₁
  · refine Or.inr ?_
    by_contra hw₂
    exact hw₁ (((h.separates_xor hwΩ.1 hwK).1 hwΩ).2 hw₂)

theorem cells_disjoint : Disjoint (farRegion J₁.carrier y) (farRegion J₂.carrier y) := by
  rw [Set.disjoint_left]
  intro w hw₁ hw₂
  obtain ⟨hwΩ, hwK⟩ := h.cell_subset₁ hw₁
  exact ((h.separates_xor hwΩ.1 hwK).1 hwΩ).1 hw₁ hw₂

theorem cells_ne : farRegion J₁.carrier y ≠ farRegion J₂.carrier y := by
  intro heq
  obtain ⟨w, hw⟩ := h.cell_nonempty₁
  exact Set.disjoint_left.1 h.cells_disjoint hw (heq ▸ hw)

/-- A cell is not the untouched region: it lies on the other side of `C`. -/
theorem cell_ne_near₁ : farRegion J₁.carrier y ≠ connectedComponentIn C.carrierᶜ y := by
  intro heq
  obtain ⟨w, hw⟩ := h.cell_nonempty₁
  exact Set.disjoint_left.1 h.regionPairC.disjoint (h.cell_subset₁ hw).1 (heq ▸ hw)

theorem cell_ne_near₂ : farRegion J₂.carrier y ≠ connectedComponentIn C.carrierᶜ y :=
  h.symm.cell_ne_near₁

/-! ### The three regions of `ℝ² ∖ (C ∪ P)` -/

theorem cell_subset_compl₁ : farRegion J₁.carrier y ⊆ (C.carrier ∪ cover K)ᶜ := by
  intro w hw
  obtain ⟨hwΩ, hwK⟩ := h.cell_subset₁ hw
  rintro (hw' | hw')
  · exact hwΩ.1 hw'
  · exact hwK hw'

/-- The three regions together are the whole of `ℝ² ∖ (C ∪ P)`. -/
theorem compl_eq : (C.carrier ∪ cover K)ᶜ =
    (farRegion J₁.carrier y ∪ farRegion J₂.carrier y) ∪ connectedComponentIn C.carrierᶜ y := by
  rw [← h.region_eq]
  exact compl_union_eq_of_isRegionPair h.regionPairC h.avoids

/-- The untouched region is a component of `ℝ² ∖ (C ∪ P)`, with frontier `C`. -/
theorem near_isComponent {z : Plane} (hz : z ∈ connectedComponentIn C.carrierᶜ y) :
    connectedComponentIn (C.carrier ∪ cover K)ᶜ z = connectedComponentIn C.carrierᶜ y :=
  far_isComponent C.isSeparating_carrier h.regionPairC h.avoids hz

theorem frontier_near :
    frontier (connectedComponentIn C.carrierᶜ y) = C.carrier :=
  h.regionPairC.right.frontier_eq C.isSeparating_carrier

/-- The first cell is a component of `ℝ² ∖ (C ∪ P)`, with frontier `J₁`. -/
theorem cell_isComponent_compl₁ {z : Plane} (hz : z ∈ farRegion J₁.carrier y) :
    connectedComponentIn (C.carrier ∪ cover K)ᶜ z = farRegion J₁.carrier y :=
  cell_isComponent_compl J₁.isSeparating_carrier h.regionPair₁ h.carrier₁_subset
    h.cell_subset_compl₁ hz

theorem cell_isComponent_compl₂ {z : Plane} (hz : z ∈ farRegion J₂.carrier y) :
    connectedComponentIn (C.carrier ∪ cover K)ᶜ z = farRegion J₂.carrier y :=
  h.symm.cell_isComponent_compl₁ hz

/-- **"`ℝ² ∖ (C ∪ P)` has exactly three regions."** Every component is one of the three named
sets, and each of the three is a component (`cell_isComponent_compl₁`, `…₂`,
`near_isComponent`). Their frontiers are `J₁`, `J₂` and `C`. -/
theorem isComponent {z : Plane} (hz : z ∉ C.carrier ∪ cover K) :
    connectedComponentIn (C.carrier ∪ cover K)ᶜ z = farRegion J₁.carrier y ∨
      connectedComponentIn (C.carrier ∪ cover K)ᶜ z = farRegion J₂.carrier y ∨
      connectedComponentIn (C.carrier ∪ cover K)ᶜ z = connectedComponentIn C.carrierᶜ y := by
  have hmem : z ∈ (C.carrier ∪ cover K)ᶜ := hz
  rw [h.compl_eq] at hmem
  rcases hmem with (h₁ | h₂) | h₃
  · exact Or.inl (h.cell_isComponent_compl₁ h₁)
  · exact Or.inr (Or.inl (h.cell_isComponent_compl₂ h₂))
  · exact Or.inr (Or.inr (h.near_isComponent h₃))

/-! ### The blueprint's two cases -/

/-- Seen from the unbounded region of `C`, `J₁` too has `y` outside it: otherwise the unbounded
`Ext(C)` would sit inside the bounded `Int(J₁)`. -/
theorem mem_outside₁ (hy : y ∈ outside C.carrier) : y ∈ outside J₁.carrier := by
  rcases J₁.isSeparating_carrier.isRegionOf_connectedComponentIn h.notMem_carrier₁ with hc | hc
  · refine absurd ?_ C.isSeparating_carrier.not_isBounded_outside
    refine J₁.isSeparating_carrier.isBounded_inside.subset ?_
    rw [← hc, ← C.isSeparating_carrier.connectedComponentIn_eq_outside hy]
    exact h.near_subset₁
  · exact hc ▸ mem_connectedComponentIn h.notMem_carrier₁

theorem cell₁_eq_inside (hy : y ∈ outside C.carrier) :
    farRegion J₁.carrier y = inside J₁.carrier :=
  J₁.isSeparating_carrier.farRegion_eq_inside (h.mem_outside₁ hy)

theorem cell₂_eq_inside (hy : y ∈ outside C.carrier) :
    farRegion J₂.carrier y = inside J₂.carrier :=
  h.symm.cell₁_eq_inside hy

/-- **Theorem 2.8(a).** If the crosscut runs inside `C` — that is, if the reference point `y`
lies in `Ext(C)` — then `Int(C) ∖ P` is exactly the union of the two bounded regions of `J₁` and
`J₂`, and those two are disjoint. -/
theorem inside_diff_eq (hy : y ∈ outside C.carrier) :
    inside C.carrier \ cover K = inside J₁.carrier ∪ inside J₂.carrier := by
  rw [← C.isSeparating_carrier.farRegion_eq_inside hy, ← h.cell₁_eq_inside hy,
    ← h.cell₂_eq_inside hy]
  exact h.region_eq

/-- **Theorem 2.8(b).** If the crosscut runs outside `C` — that is, if `y ∈ Int(C)` — then
`Ext(C) ∖ P` has exactly the two regions `farRegion Jᵢ.carrier y`, whose frontiers are `J₁` and
`J₂` (`frontier_cell₁`, `frontier_cell₂`) and which are components of it
(`cell_isComponent₁`, `…₂`). Which of the two is `Int(Jᵢ)` and which `Ext(Jᵢ)` is settled by
`inside_exactly_one`. -/
theorem outside_diff_eq (hy : y ∈ inside C.carrier) :
    outside C.carrier \ cover K = farRegion J₁.carrier y ∪ farRegion J₂.carrier y := by
  rw [← C.isSeparating_carrier.farRegion_eq_outside hy]
  exact h.region_eq

/-- In case (b), `Int(C)` lies inside exactly one of `J₁, J₂` — the blueprint's "relabel so that
it lies inside `J₁`". -/
theorem inside_exactly_one (hy : y ∈ inside C.carrier) :
    y ∈ inside J₁.carrier ↔ y ∉ inside J₂.carrier := by
  obtain ⟨u, hu, hlevC, hlevK⟩ := h.exists_direction
  exact C.crosscut_inside_exactly_one J₁ J₂ hu hlevC hlevK h.le h.edges₁ h.edges₂ hy
    h.notMem_cover

end IsPolygonalCrosscut

/-- **Theorem 2.8 (two-sided polygonal crosscuts).** Let `C` be a simple closed polygon, `K` the
edge list of a polygonal crosscut cutting it at the vertices `a` and `a + k`, and `J₁, J₂` the
two closed polygons formed by the crosscut with the two arcs. Let `y` be a point of the region
of `ℝ² ∖ C` that the crosscut does not enter, and write `Ω = farRegion C.carrier y` for the
other region and `Vᵢ = farRegion Jᵢ.carrier y` for the region of `ℝ² ∖ Jᵢ` on the far side from
`y`. Then

* `Ω ∖ P` is the disjoint union of `V₁` and `V₂`, which are its two connected components;
* their frontiers are `J₁` and `J₂`, and the closure of `Vᵢ` meets `C` exactly in the arc `Aᵢ`;
* `ℝ² ∖ (C ∪ P)` has exactly three regions, `V₁`, `V₂` and the region of `y`.

Case (a) of the blueprint is `IsPolygonalCrosscut.inside_diff_eq`, which rewrites `Ω` as
`Int(C)` and `Vᵢ` as `Int(Jᵢ)`; case (b) is `IsPolygonalCrosscut.outside_diff_eq`. -/
theorem polygonal_crosscut {y : Plane} (h : IsPolygonalCrosscut C J₁ J₂ K a k y) :
    farRegion C.carrier y \ cover K = farRegion J₁.carrier y ∪ farRegion J₂.carrier y ∧
      Disjoint (farRegion J₁.carrier y) (farRegion J₂.carrier y) ∧
      (∀ z ∈ farRegion J₁.carrier y,
        connectedComponentIn (farRegion C.carrier y \ cover K) z = farRegion J₁.carrier y) ∧
      (∀ z ∈ farRegion J₂.carrier y,
        connectedComponentIn (farRegion C.carrier y \ cover K) z = farRegion J₂.carrier y) ∧
      frontier (farRegion J₁.carrier y) = J₁.carrier ∧
      frontier (farRegion J₂.carrier y) = J₂.carrier ∧
      closure (farRegion J₁.carrier y) ∩ C.carrier = C.arc a k ∧
      closure (farRegion J₂.carrier y) ∩ C.carrier = C.arc (a + k) (m + 3 - k) ∧
      (∀ z ∉ C.carrier ∪ cover K,
        connectedComponentIn (C.carrier ∪ cover K)ᶜ z = farRegion J₁.carrier y ∨
          connectedComponentIn (C.carrier ∪ cover K)ᶜ z = farRegion J₂.carrier y ∨
          connectedComponentIn (C.carrier ∪ cover K)ᶜ z = connectedComponentIn C.carrierᶜ y) :=
  ⟨h.region_eq, h.cells_disjoint, h.cell_isComponent₁, h.cell_isComponent₂, h.frontier_cell₁,
    h.frontier_cell₂, h.closure_cell_inter₁, h.closure_cell_inter₂, fun _ hz => h.isComponent hz⟩

end Schoenflies
