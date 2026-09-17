/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.SimpleArc
import LeanPool.Schoenflies.PolygonalCrosscut
import LeanPool.Schoenflies.TwoArcs

/-!
# Realizing a polygonal Jordan curve as a `ClosedPolygon`

The blueprint's "simple closed polygonal curve" is set-theoretic: an `IsJordanCurve` that is
also `IsPolygonal`, with no condition on vertices at all. The development works instead with
`Schoenflies.ClosedPolygon`, a cyclic vertex list carrying a `corner` field — no three
consecutive vertices collinear. That field is a *presentation* condition, strictly stronger than
the blueprint's notion, and until now nothing said that a set-level polygonal Jordan curve
admits such a presentation. This module proves it.

## How the vertex list is found

The curve is *not* read off the vertex list `IsPolygonal` hands over: that list may retrace
itself, cross itself, and repeat segments, and it carries no order along the curve. Two
structures are laid over the point set instead and then matched.

* **From the plane side**, the overlay of `Schoenflies/OverlayGraph.lean`, with the graph
  discarded: `Schoenflies.IsClean` is a finite list of nondegenerate segments occupying the
  curve, with pairwise disjoint interiors and no end interior to any of them. Around an interior
  point of a piece the curve *is* that piece (`IsClean.exists_ball_subset_seg`), so the piece
  interiors are separated by honest open sets of the plane (`Schoenflies.nearPiece`) and a
  connected subset of the curve away from the ends lies inside a single piece.
* **From the curve side**, the loop's parameters at which it reaches an end of a piece. They
  form a finite subset of `[0, 1)` containing `0` — `0` because the loop's start is put on the
  cut list, so that the last gap is the one that closes the curve — and, listed in increasing
  order, they cut `[0, 1)` into gaps.

The two match: a gap image is connected and misses the ends, so it lies in one piece interior;
and the interior is connected and covered by the *closed* gap images, so it lies in that one
gap. Gaps and pieces therefore correspond one to one, the ends of a gap are the ends of its
piece, and the ends listed in the loop's order are a cyclic vertex list whose edges are the
pieces. That list satisfies `vertex_inj` and `edges_meet` but not `corner`, which is what
`Schoenflies.PrePolygon` is for; `corner` is then arranged by deleting redundant vertices.

## Blueprint

* `Schoenflies.PrePolygon` — a `ClosedPolygon` less the `corner` field: the blueprint's simple
  closed polygonal curve *presented by a vertex list*, redundant vertices allowed.
* `Schoenflies.PrePolygon.deleteLast`, `Schoenflies.PrePolygon.exists_closedPolygon_of_prePolygon`
  — the blueprint's opening move in Lemma 1.8, "delete redundant vertices at which two
  consecutive edges are collinear", as an operation rather than an invariant.
* `Schoenflies.IsClean`, `Schoenflies.exists_isClean` — Lemma 3.7 (polygonal overlay) with the
  combinatorics dropped: what the overlay says about the point set alone.
* `Schoenflies.par`, `Schoenflies.parNext`, `Schoenflies.exists_mem_gap` — the parameters in
  increasing order, and that their gaps tile `[0, 1)`.
* `Schoenflies.exists_prePolygon_of_isJordanCurve`, `Schoenflies.exists_closedPolygon` — §1:
  every simple closed polygonal curve, in the blueprint's set-level sense, is the carrier of a
  `ClosedPolygon`.
* `Schoenflies.IsStraightAt`, `Schoenflies.IsCornerAt`,
  `Schoenflies.ClosedPolygon.exists_vertex_eq_of_isCornerAt`,
  `Schoenflies.ClosedPolygon.isCornerAt_vertex` — the vertex set of a realization is *exactly*
  the set of points at which the curve does not run straight. So a named point can be required
  to be a vertex precisely when it is a corner, and no realization has any choice about it.
* `Schoenflies.ClosedPolygon.rotate`, `…isArcBetween_arc`, `…arc_inter` — the two arcs of a
  splitting, as arcs between the two cut vertices meeting exactly there.
* `Schoenflies.two_arcs_unique` — two points cut a Jordan curve into two arcs in only one way.
* `Schoenflies.exists_closedPolygon_corners`, `Schoenflies.exists_closedPolygon_split`,
  `Schoenflies.exists_closedPolygon_arcs`, `Schoenflies.exists_closedPolygon_arcs_ordered` — the
  realization with named corners, with the splitting indices, and with the two arcs identified.
  The last is the shape `Graph.IsHexRealization` asks for.

## The corner hypothesis is not an artefact

`exists_closedPolygon_arcs` requires the two cut points to be corners.
`ClosedPolygon.isCornerAt_vertex` shows that this cannot be dropped: every vertex of every
realization is a corner, so a cut point at which the curve runs straight is a vertex of *no*
realization, and no `ClosedPolygon` with that carrier has an arc ending there. A consumer that
needs to cut at a straight point has to change the curve — bend it there — which is a different
theorem, and is exactly the freedom `Graph.IsK33Config.not_isDrawing` reserves for itself.
-/

open Metric Set unitInterval

namespace Schoenflies

open Plane

/-! ## Polygons before normalization

`PrePolygon` is `ClosedPolygon` with the `corner` field removed. Everything the curve bridge of
`Schoenflies/PolygonBridge.lean` proves about a `ClosedPolygon` — that its carrier is a Jordan
curve, that it is polygonal — uses only `vertex_inj` and `edges_meet`, so it is already true
here; what `corner` buys is the germ argument of the strip lemma, and nothing else. -/

/-- A simple closed polygonal curve presented by its cyclic vertex list, with redundant
vertices allowed: `ClosedPolygon` less its `corner` field. -/
structure PrePolygon (m : ℕ) where
  /-- The vertices, in cyclic order. -/
  vertex : ZMod (m + 3) → Plane
  /-- The vertices are distinct. -/
  vertex_inj : Function.Injective vertex
  /-- Simplicity: an edge meets any other edge only at one of its own endpoints. -/
  edges_meet : ∀ i j : ZMod (m + 3), i ≠ j →
    segment ℝ (vertex i) (vertex (i + 1)) ∩ segment ℝ (vertex j) (vertex (j + 1)) ⊆
      {vertex i, vertex (i + 1)}

namespace PrePolygon

variable {m : ℕ} (P : PrePolygon m)

/-- The edge leaving vertex `i`. -/
def edge (i : ZMod (m + 3)) : Set Plane := segment ℝ (P.vertex i) (P.vertex (i + 1))

/-- The carrier: the union of the edges. -/
def carrier : Set Plane := ⋃ i, P.edge i

variable {P}

theorem edge_subset_carrier (i : ZMod (m + 3)) : P.edge i ⊆ P.carrier := Set.subset_iUnion _ i

theorem vertex_mem_carrier (i : ZMod (m + 3)) : P.vertex i ∈ P.carrier :=
  edge_subset_carrier i (left_mem_segment ℝ _ _)

theorem vertex_ne_succ (i : ZMod (m + 3)) : P.vertex i ≠ P.vertex (i + 1) := fun h =>
  ClosedPolygon.succ_ne_self i (P.vertex_inj h).symm

end PrePolygon

/-- A `ClosedPolygon` read as a `PrePolygon`: forget the `corner` field. -/
def ClosedPolygon.toPre {m : ℕ} (P : ClosedPolygon m) : PrePolygon m :=
  ⟨P.vertex, P.vertex_inj, P.edges_meet⟩

@[simp] theorem ClosedPolygon.carrier_toPre {m : ℕ} (P : ClosedPolygon m) :
    P.toPre.carrier = P.carrier := rfl

/-! ## Small facts about the cyclic index

`ZMod (m + 3)` has at least three elements; `0`, `1` and `2` are distinct, which is what makes
a vertex, its successor and its predecessor three different vertices. -/

namespace PrePolygon

variable {m : ℕ}

theorem two_ne_zero' : (2 : ZMod (m + 3)) ≠ 0 := by
  intro h
  rw [show (2 : ZMod (m + 3)) = ((2 : ℕ) : ZMod (m + 3)) by norm_num,
    ZMod.natCast_eq_zero_iff] at h
  have := Nat.le_of_dvd (by norm_num) h
  omega

theorem pred_ne_succ (i : ZMod (m + 3)) : i - 1 ≠ i + 1 := fun h =>
  two_ne_zero' (m := m) (by linear_combination -h)

theorem val_one_eq : (1 : ZMod (m + 3)).val = 1 := by
  rw [show (1 : ZMod (m + 3)) = ((1 : ℕ) : ZMod (m + 3)) by norm_num]
  exact ZMod.val_cast_of_lt (by omega)

/-- The successor of a non-final index is the next one. -/
theorem val_succ_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) : (j + 1).val = j.val + 1 := by
  rw [ZMod.val_add, val_one_eq, Nat.mod_eq_of_lt h]

/-- The successor of the final index wraps to `0`. -/
theorem val_succ_last {j : ZMod (m + 3)} (h : j.val + 1 = m + 3) : (j + 1).val = 0 := by
  rw [ZMod.val_add, val_one_eq, h, Nat.mod_self]

/-! ## Rotation

Reading the same cyclic list from a different starting vertex. It is used once, to bring the
vertex that is about to be deleted to the end of the list. -/

/-- The same closed polygon, read from vertex `a` onwards. -/
def rotate (P : PrePolygon m) (a : ZMod (m + 3)) : PrePolygon m where
  vertex j := P.vertex (a + j)
  vertex_inj i j h := add_left_cancel (P.vertex_inj h)
  edges_meet i j hij := by
    have hi : a + (i + 1) = a + i + 1 := by ring
    have hj : a + (j + 1) = a + j + 1 := by ring
    simp only [hi, hj]
    exact P.edges_meet _ _ fun h => hij (add_left_cancel h)

@[simp] theorem rotate_vertex (P : PrePolygon m) (a j : ZMod (m + 3)) :
    (P.rotate a).vertex j = P.vertex (a + j) := rfl

/-- Rotating does not move the curve: the edges are the same, listed from elsewhere. -/
theorem carrier_rotate (P : PrePolygon m) (a : ZMod (m + 3)) :
    (P.rotate a).carrier = P.carrier := by
  have hedge : ∀ j : ZMod (m + 3), (P.rotate a).edge j = P.edge (a + j) := by
    intro j
    rw [edge, edge, rotate_vertex, rotate_vertex, show a + (j + 1) = a + j + 1 by ring]
  refine Set.Subset.antisymm (Set.iUnion_subset fun j => ?_) (Set.iUnion_subset fun i => ?_)
  · rw [hedge]; exact edge_subset_carrier _
  · refine le_trans (le_of_eq ?_) (edge_subset_carrier (P := P.rotate a) (i - a))
    rw [hedge, add_sub_cancel]

/-! ## Deleting the last vertex

The blueprint's opening move in the strip lemma. The vertex to be deleted is brought to the end
of the list by `rotate`, so only that one case has to be treated. `emb` is the inclusion of the
shortened index set into the old one: the same numeral, one modulus smaller. -/

section Delete

variable {m : ℕ}

/-- An index of the shortened list, read in the original one: the same numeral. -/
def emb (j : ZMod (m + 3)) : ZMod (m + 1 + 3) := ((j.val : ℕ) : ZMod (m + 1 + 3))

theorem neg_one_eq_cast : (-1 : ZMod (m + 1 + 3)) = ((m + 3 : ℕ) : ZMod (m + 1 + 3)) := by
  have h0 : ((m + 1 + 3 : ℕ) : ZMod (m + 1 + 3)) = 0 := ZMod.natCast_self _
  push_cast at h0 ⊢
  linear_combination -h0

theorem neg_two_eq_cast : (-1 - 1 : ZMod (m + 1 + 3)) = ((m + 2 : ℕ) : ZMod (m + 1 + 3)) := by
  have h0 : ((m + 1 + 3 : ℕ) : ZMod (m + 1 + 3)) = 0 := ZMod.natCast_self _
  push_cast at h0 ⊢
  linear_combination -h0

theorem emb_injective : Function.Injective (emb (m := m)) := fun i j h =>
  ZMod.val_injective _ (ClosedPolygon.natCast_inj (m := m + 1)
    (by have := ZMod.val_lt i; omega) (by have := ZMod.val_lt j; omega) h)

theorem emb_succ_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) : emb (j + 1) = emb j + 1 := by
  rw [emb, emb, val_succ_of_lt h, Nat.cast_add, Nat.cast_one]

theorem emb_succ_last {j : ZMod (m + 3)} (h : j.val + 1 = m + 3) : emb (j + 1) = 0 := by
  rw [emb, val_succ_last h, Nat.cast_zero]

theorem emb_eq_last {j : ZMod (m + 3)} (h : j.val + 1 = m + 3) : emb j = -1 - 1 := by
  rw [emb, neg_two_eq_cast, show j.val = m + 2 by omega]

/-- Below the last index, `emb` misses both the deleted vertex and its predecessor. -/
theorem emb_ne_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) :
    emb j ≠ -1 ∧ emb j ≠ -1 - 1 := by
  have hj := ZMod.val_lt j
  constructor
  · rw [neg_one_eq_cast]
    exact fun he => (by omega : j.val ≠ m + 3)
      (ClosedPolygon.natCast_inj (m := m + 1) (by omega) (by omega) he)
  · rw [neg_two_eq_cast]
    exact fun he => (by omega : j.val ≠ m + 2)
      (ClosedPolygon.natCast_inj (m := m + 1) (by omega) (by omega) he)

/-- Every index other than the deleted vertex and its predecessor is hit by `emb`. -/
theorem exists_emb_eq {i : ZMod (m + 1 + 3)} (h1 : i ≠ -1) (h2 : i ≠ -1 - 1) :
    ∃ j : ZMod (m + 3), j.val + 1 < m + 3 ∧ emb j = i := by
  have hi := ZMod.val_lt i
  have hne1 : i.val ≠ m + 3 := by
    rintro he
    exact h1 (by rw [neg_one_eq_cast, ← he, ZMod.natCast_rightInverse i])
  have hne2 : i.val ≠ m + 2 := by
    rintro he
    exact h2 (by rw [neg_two_eq_cast, ← he, ZMod.natCast_rightInverse i])
  refine ⟨(i.val : ZMod (m + 3)), ?_, ?_⟩
  · rw [ZMod.val_cast_of_lt (show i.val < m + 3 by omega)]; omega
  · rw [emb, ZMod.val_cast_of_lt (show i.val < m + 3 by omega), ZMod.natCast_rightInverse i]

variable (P : PrePolygon (m + 1))

/-- The vertex list with its last entry dropped. -/
def dropVertex (j : ZMod (m + 3)) : Plane := P.vertex (emb j)

variable {P}

theorem dropVertex_injective : Function.Injective P.dropVertex :=
  fun _ _ h => emb_injective (P.vertex_inj h)

/-- Away from the deleted vertex the edges are unchanged. -/
theorem dropVertex_edge_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) :
    segment ℝ (P.dropVertex j) (P.dropVertex (j + 1)) = P.edge (emb j) := by
  rw [dropVertex, dropVertex, emb_succ_of_lt h, edge]

/-- The final edge of the shortened list is the union of the two edges at the deleted vertex —
which is a segment precisely because the deleted vertex is interior to it. -/
theorem dropVertex_edge_last
    (hcol : P.vertex (-1) ∈ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0))
    {j : ZMod (m + 3)} (h : j.val + 1 = m + 3) :
    segment ℝ (P.dropVertex j) (P.dropVertex (j + 1)) = P.edge (-1 - 1) ∪ P.edge (-1) := by
  have e1 : (-1 - 1 : ZMod (m + 1 + 3)) + 1 = -1 := by ring
  have e2 : (-1 : ZMod (m + 1 + 3)) + 1 = 0 := by ring
  rw [dropVertex, dropVertex, emb_succ_last h, emb_eq_last h, edge, edge, e1, e2]
  exact segment_split (openSegment_subset_segment ℝ _ _ hcol)

/-- The deleted vertex lies on no edge but its own two: `edges_meet` puts a meeting point at an
end of the other edge, and the deleted vertex is an end only of the two edges at it. -/
theorem vertex_last_notMem_edge {i : ZMod (m + 1 + 3)} (h1 : i ≠ -1) (h2 : i ≠ -1 - 1) :
    P.vertex (-1) ∉ P.edge i := by
  intro hmem
  have hself : P.vertex (-1) ∈ P.edge (-1) := left_mem_segment ℝ _ _
  have hme := P.edges_meet i (-1) h1 (Set.mem_inter hmem hself)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hme
  rcases hme with he | he
  · exact h1 (P.vertex_inj he).symm
  · exact h2 (by linear_combination -P.vertex_inj he)

/-- **Simplicity survives the deletion.** The only new edge is the merged one, and the point
that has to be kept out of it — the deleted vertex — lies on no other edge at all. -/
theorem dropVertex_edges_meet
    (hcol : P.vertex (-1) ∈ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0))
    (j k : ZMod (m + 3)) (hjk : j ≠ k) :
    segment ℝ (P.dropVertex j) (P.dropVertex (j + 1)) ∩
      segment ℝ (P.dropVertex k) (P.dropVertex (k + 1)) ⊆
      {P.dropVertex j, P.dropVertex (j + 1)} := by
  have e1 : (-1 - 1 : ZMod (m + 1 + 3)) + 1 = -1 := by ring
  have e2 : (-1 : ZMod (m + 1 + 3)) + 1 = 0 := by ring
  have hjv : j.val + 1 ≤ m + 3 := ZMod.val_lt j
  have hkv : k.val + 1 ≤ m + 3 := ZMod.val_lt k
  rcases eq_or_lt_of_le hjv with hj | hj
  · -- `j` is the last index, so its edge is the merged one.
    have hdj : P.dropVertex j = P.vertex (-1 - 1) := by rw [dropVertex, emb_eq_last hj]
    have hdj1 : P.dropVertex (j + 1) = P.vertex 0 := by rw [dropVertex, emb_succ_last hj]
    rcases eq_or_lt_of_le hkv with hk | hk
    · exact absurd (ZMod.val_injective _ (by omega : j.val = k.val)) hjk
    obtain ⟨hk1, hk2⟩ := emb_ne_of_lt hk
    have hout := vertex_last_notMem_edge (P := P) hk1 hk2
    rw [dropVertex_edge_last hcol hj, dropVertex_edge_of_lt hk, hdj, hdj1]
    rintro x ⟨hx1 | hx1, hx2⟩
    · have hme := P.edges_meet _ _ (fun h => hk2 h.symm) (Set.mem_inter hx1 hx2)
      rw [e1] at hme
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hme ⊢
      exact hme.imp id fun h => absurd (h ▸ hx2) hout
    · have hme := P.edges_meet _ _ (fun h => hk1 h.symm) (Set.mem_inter hx1 hx2)
      rw [e2] at hme
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hme ⊢
      exact Or.inr (hme.resolve_left fun h => absurd (h ▸ hx2) hout)
  · -- `j` is an ordinary index, so its edge is unchanged.
    obtain ⟨hj1, hj2⟩ := emb_ne_of_lt hj
    have hdj : P.dropVertex j = P.vertex (emb j) := rfl
    have hdj1 : P.dropVertex (j + 1) = P.vertex (emb j + 1) := by
      rw [dropVertex, emb_succ_of_lt hj]
    rw [dropVertex_edge_of_lt hj, hdj, hdj1]
    rcases eq_or_lt_of_le hkv with hk | hk
    · rw [dropVertex_edge_last hcol hk]
      rintro x ⟨hx1, hx2 | hx2⟩
      · exact P.edges_meet _ _ hj2 (Set.mem_inter hx1 hx2)
      · exact P.edges_meet _ _ hj1 (Set.mem_inter hx1 hx2)
    · rw [dropVertex_edge_of_lt hk]
      exact fun x hx => P.edges_meet _ _ (fun h => hjk (emb_injective h)) hx

/-- **The polygon with a redundant vertex deleted.** -/
def deleteLast (P : PrePolygon (m + 1))
    (hcol : P.vertex (-1) ∈ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0)) : PrePolygon m where
  vertex := P.dropVertex
  vertex_inj := dropVertex_injective
  edges_meet := dropVertex_edges_meet hcol

/-- **Deleting a redundant vertex does not move the curve.** -/
theorem carrier_deleteLast
    (hcol : P.vertex (-1) ∈ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0)) :
    (deleteLast P hcol).carrier = P.carrier := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun j => ?_) (Set.iUnion_subset fun i => ?_)
  · have hjv : j.val + 1 ≤ m + 3 := ZMod.val_lt j
    rcases eq_or_lt_of_le hjv with hj | hj
    · rw [show (deleteLast P hcol).edge j = _ from dropVertex_edge_last hcol hj]
      exact Set.union_subset (edge_subset_carrier _) (edge_subset_carrier _)
    · rw [show (deleteLast P hcol).edge j = _ from dropVertex_edge_of_lt hj]
      exact edge_subset_carrier _
  · by_cases hi : i = -1 ∨ i = -1 - 1
    · -- The two edges at the deleted vertex are both inside the merged one.
      set j : ZMod (m + 3) := ((m + 2 : ℕ) : ZMod (m + 3)) with hjdef
      have hj : j.val + 1 = m + 3 := by rw [hjdef, ZMod.val_cast_of_lt (by omega)]
      have hmerge : (deleteLast P hcol).edge j = P.edge (-1 - 1) ∪ P.edge (-1) :=
        dropVertex_edge_last hcol hj
      refine le_trans ?_ (le_trans (le_of_eq hmerge.symm) (edge_subset_carrier j))
      rcases hi with rfl | rfl
      · exact Set.subset_union_right
      · exact Set.subset_union_left
    · push Not at hi
      obtain ⟨j, hj, hemb⟩ := exists_emb_eq hi.1 hi.2
      have : (deleteLast P hcol).edge j = P.edge i := by
        rw [show (deleteLast P hcol).edge j = _ from dropVertex_edge_of_lt hj, hemb]
      exact le_trans (le_of_eq this.symm) (edge_subset_carrier j)

end Delete

/-! ## Recognising a redundant vertex

The `corner` field is `det ≠ 0` at every vertex. Where it fails the vertex is *interior* to the
segment joining its two neighbours, never an endpoint of it. That is the geometric content of
`edges_meet`: two edges leaving a vertex in the *same* direction would overlap in a
nondegenerate segment, and `edges_meet` would then put a whole segment inside a two-point
set. -/

/-- A nondegenerate segment is not contained in the pair of its own endpoints. -/
theorem exists_mem_segment_ne {a b : Plane} (hab : a ≠ b) :
    ∃ p ∈ segment ℝ a b, p ≠ a ∧ p ≠ b := by
  have hmem : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b ∈ openSegment ℝ a b :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  refine ⟨_, openSegment_subset_segment ℝ a b hmem, ?_, ?_⟩
  · intro h
    rw [h] at hmem
    exact hab (left_mem_openSegment_iff.1 hmem)
  · intro h
    rw [h] at hmem
    exact hab (right_mem_openSegment_iff.1 hmem)

/-- **Three collinear points meeting only at the shared one are in the order that makes the
middle one interior.** The alternative — the two segments running the same way out of `b` —
makes them overlap in a nondegenerate segment, which the meeting hypothesis forbids. -/
theorem mem_openSegment_of_det_eq_zero' {a b c : Plane} (hab : a ≠ b) (hcb : c ≠ b)
    (hmeet : segment ℝ a b ∩ segment ℝ b c ⊆ {a, b})
    (h : det (a - b) (c - b) = 0) : b ∈ openSegment ℝ a c := by
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab
  obtain ⟨r, hr⟩ := (det_eq_zero_iff_smul _ _ hab').1 h
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_smul, sub_eq_zero] at hr
    exact hcb hr
  have hcexp : c = b + r • (a - b) := by linear_combination (norm := module) hr
  have hrneg : r < 0 := by
    rcases lt_trichotomy r 0 with hlt | heq | hgt
    · exact hlt
    · exact absurd heq hr0
    exfalso
    -- A short step out of `b` towards `a` is then also a step towards `c`.
    have hμpos : 0 < min 1 r / 2 := by positivity
    set μ : ℝ := min 1 r / 2 with hμdef
    have hμ1 : μ < 1 := by
      have h1 : min 1 r ≤ 1 := min_le_left _ _
      rw [hμdef]; linarith
    have hμler : μ / r < 1 := by
      rw [div_lt_one hgt]
      have h1 : min 1 r ≤ r := min_le_right _ _
      rw [hμdef]; linarith
    have hμr : μ / r * r = μ := div_mul_cancel₀ _ (ne_of_gt hgt)
    have hz₁ : μ • a + (1 - μ) • b ∈ segment ℝ a b :=
      ⟨μ, 1 - μ, hμpos.le, by linarith, by ring, rfl⟩
    have hz₂ : μ • a + (1 - μ) • b ∈ segment ℝ b c := by
      refine ⟨1 - μ / r, μ / r, by linarith, by positivity, by ring, ?_⟩
      have expand : (1 - μ / r) • b + (μ / r) • (b + r • (a - b))
          = (μ / r * r) • a + (1 - μ / r * r) • b := by module
      rw [hcexp, expand, hμr]
    have hmem := hmeet ⟨hz₁, hz₂⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with he | he
    · have hkey : (1 - μ) • (a - b) = 0 := by linear_combination (norm := module) -he
      rcases smul_eq_zero.1 hkey with h' | h'
      · exact (by linarith : (0 : ℝ) < 1 - μ).ne' h'
      · exact hab' h'
    · have hkey : μ • (a - b) = 0 := by linear_combination (norm := module) he
      rcases smul_eq_zero.1 hkey with h' | h'
      · exact hμpos.ne' h'
      · exact hab' h'
  -- Opposite directions: the vertex is a strict convex combination of its neighbours.
  have hden : (0 : ℝ) < 1 - r := by linarith
  refine ⟨-r / (1 - r), 1 / (1 - r), div_pos (by linarith) hden, div_pos one_pos hden,
    by field_simp; ring, ?_⟩
  have expand : (-r / (1 - r)) • a + (1 / (1 - r)) • (b + r • (a - b))
      = (-r / (1 - r) + 1 / (1 - r) * r) • a + (1 / (1 - r) - 1 / (1 - r) * r) • b := by module
  rw [hcexp, expand, show -r / (1 - r) + 1 / (1 - r) * r = 0 by field_simp; ring,
    show (1 : ℝ) / (1 - r) - 1 / (1 - r) * r = 1 by field_simp, zero_smul, one_smul, zero_add]

variable {m : ℕ} {P : PrePolygon m}

/-- **A redundant vertex is interior to the segment joining its neighbours.** -/
theorem mem_openSegment_of_det_eq_zero (i : ZMod (m + 3))
    (h : det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) = 0) :
    P.vertex i ∈ openSegment ℝ (P.vertex (i - 1)) (P.vertex (i + 1)) := by
  have hpred : i - 1 + 1 = i := sub_add_cancel i 1
  have hne : i - 1 ≠ i := fun he =>
    ClosedPolygon.succ_ne_self (i - 1) (by rw [hpred]; exact he.symm)
  have hmeet := P.edges_meet (i - 1) i hne
  rw [hpred] at hmeet
  exact mem_openSegment_of_det_eq_zero' (fun he => hne (P.vertex_inj he))
    (fun he => ClosedPolygon.succ_ne_self i (P.vertex_inj he)) hmeet h

/-! ## Normalization

Delete redundant vertices until none is left. Each deletion shortens the list by one, and the
list can never shrink below three vertices: a triangle with a redundant vertex would have one
edge inside another, which `edges_meet` forbids. -/

/-- A three-vertex polygon has no redundant vertex: were the last one interior to the segment
joining the other two, the edge before it would lie inside the edge opposite it. -/
theorem not_collinear_triangle (P : PrePolygon 0) :
    P.vertex (-1) ∉ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0) := by
  intro hcol
  have e1 : (-1 - 1 : ZMod (0 + 3)) + 1 = -1 := by decide
  have e2 : (-1 : ZMod (0 + 3)) ≠ -1 - 1 := by decide
  have hsplit : segment ℝ (P.vertex (-1 - 1)) (P.vertex 0)
      = segment ℝ (P.vertex (-1 - 1)) (P.vertex (-1)) ∪ segment ℝ (P.vertex (-1)) (P.vertex 0) :=
    segment_split (openSegment_subset_segment ℝ _ _ hcol)
  -- The edge before the redundant vertex sits inside the edge opposite it.
  have hsub : P.edge (-1 - 1) ⊆ P.edge (-1 - 1 - 1) := by
    have e3 : (-1 - 1 - 1 : ZMod (0 + 3)) = 0 := by decide
    have e4 : (0 : ZMod (0 + 3)) + 1 = -1 - 1 := by decide
    rw [edge, edge, e1, e3, e4, segment_symm ℝ (P.vertex 0) (P.vertex (-1 - 1)), hsplit]
    exact Set.subset_union_left
  obtain ⟨p, hp, hp1, hp2⟩ := exists_mem_segment_ne (P.vertex_ne_succ (-1 - 1))
  rcases P.edges_meet (-1 - 1) (-1 - 1 - 1) (by decide) ⟨hp, hsub hp⟩ with h | h
  exacts [hp1 h, hp2 h]

/-- **Every `PrePolygon` normalizes to a `ClosedPolygon` with the same carrier.** This is the
blueprint's "delete redundant vertices at which two consecutive edges are collinear", run to
completion; the induction is on the number of vertices, which each deletion lowers by one. -/
theorem exists_closedPolygon_of_prePolygon :
    ∀ (m : ℕ) (P : PrePolygon m), ∃ (m' : ℕ) (P' : ClosedPolygon m'), P'.carrier = P.carrier := by
  intro m
  induction m with
  | zero =>
    intro P
    by_cases hc : ∀ i : ZMod (0 + 3),
        det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0
    · exact ⟨0, ⟨P.vertex, P.vertex_inj, P.edges_meet, hc⟩, rfl⟩
    · push Not at hc
      obtain ⟨i, hi⟩ := hc
      refine absurd ?_ (not_collinear_triangle (P.rotate (i + 1)))
      have e1 : i + 1 + (-1 : ZMod (0 + 3)) = i := by ring
      have e2 : i + 1 + (-1 - 1 : ZMod (0 + 3)) = i - 1 := by ring
      have e3 : i + 1 + (0 : ZMod (0 + 3)) = i + 1 := by ring
      rw [rotate_vertex, rotate_vertex, rotate_vertex, e1, e2, e3]
      exact mem_openSegment_of_det_eq_zero i hi
  | succ m ih =>
    intro P
    by_cases hc : ∀ i : ZMod (m + 1 + 3),
        det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0
    · exact ⟨m + 1, ⟨P.vertex, P.vertex_inj, P.edges_meet, hc⟩, rfl⟩
    · push Not at hc
      obtain ⟨i, hi⟩ := hc
      have hcol : (P.rotate (i + 1)).vertex (-1) ∈
          openSegment ℝ ((P.rotate (i + 1)).vertex (-1 - 1)) ((P.rotate (i + 1)).vertex 0) := by
        have e1 : i + 1 + (-1 : ZMod (m + 1 + 3)) = i := by ring
        have e2 : i + 1 + (-1 - 1 : ZMod (m + 1 + 3)) = i - 1 := by ring
        have e3 : i + 1 + (0 : ZMod (m + 1 + 3)) = i + 1 := by ring
        rw [rotate_vertex, rotate_vertex, rotate_vertex, e1, e2, e3]
        exact mem_openSegment_of_det_eq_zero i hi
      obtain ⟨m', P', hP'⟩ := ih (deleteLast (P.rotate (i + 1)) hcol)
      exact ⟨m', P', by rw [hP', carrier_deleteLast, carrier_rotate]⟩

/-- Assembling a cyclic vertex family into a `PrePolygon`. The index type is `ZMod n` for an
`n` known only to be at least three, which is what `PrePolygon` asks for after `n` is written
`m + 3`. -/
theorem exists_prePolygon {n : ℕ} (hn : 3 ≤ n) (w : ZMod n → Plane) (hinj : Function.Injective w)
    (hmeet : ∀ i j : ZMod n, i ≠ j →
      segment ℝ (w i) (w (i + 1)) ∩ segment ℝ (w j) (w (j + 1)) ⊆ {w i, w (i + 1)}) :
    ∃ (m : ℕ) (P : PrePolygon m), P.carrier = ⋃ i, segment ℝ (w i) (w (i + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  exact ⟨m, ⟨w, hinj, hmeet⟩, rfl⟩

end PrePolygon

/-! ## Clean pieces

The overlay of `Schoenflies/OverlayGraph.lean`, stripped of the graph. All that is wanted from
it is a finite list of segments occupying the curve whose interiors are pairwise disjoint and
none of whose ends is interior to any of them — the geometric content of `lem:polygonal-overlay`
with the combinatorics left out. -/

/-- A finite list of segments presenting a polygonal set as a plane graph would: occupying it,
nondegenerate, with pairwise disjoint interiors, and with no end interior to any piece. -/
structure IsClean (Q : List Piece) (C : Set Plane) : Prop where
  /-- The pieces occupy the set. -/
  cover_eq : cover Q = C
  /-- No piece is a point. -/
  nondeg : ∀ R ∈ Q, R.Nondeg
  /-- No end of any piece is interior to any piece. -/
  ends : ∀ R ∈ Q, ∀ S ∈ Q, ∀ z, (z = R.1 ∨ z = R.2) → z ∉ S.interior
  /-- Distinct pieces have disjoint interiors. -/
  interiors : ∀ R ∈ Q, ∀ S ∈ Q, R ≠ S → ∀ x ∈ R.interior, x ∉ S.interior

/-- **Every polygonal set with two points in it has a clean presentation**, and any finite list
of points of it may be required to be among the ends. Lengthening the cut list is free: both
`EndsAreCut` and `MeetsAreCut` only ask that certain points *occur* in it. -/
theorem exists_isClean {C : Set Plane} (hC : IsPolygonal C) {a b : Plane} (ha : a ∈ C)
    (hb : b ∈ C) (hab : a ≠ b) (extra : List Plane) :
    ∃ Q : List Piece, IsClean Q C ∧ ∀ p ∈ extra, p ∈ C → ∃ R ∈ Q, p = R.1 ∨ p = R.2 := by
  obtain ⟨vs, rfl⟩ := hC
  have hnd : ∀ P ∈ segsOf vs, P.Nondeg := segsOf_nondeg vs
  have hcov : cover (segsOf vs) = poly vs := cover_segsOf_eq ha hb hab
  obtain ⟨pts, hEnds, hMeets⟩ := exists_cut_points (segsOf vs)
  refine ⟨overlayPieces (segsOf vs) (pts ++ extra), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [overlayPieces_cover, hcov]
  · exact overlayPieces_nondeg _ hnd
  · intro R hR S hS z hz
    exact overlayPieces_avoids hnd z
      (overlayPieces_ends_cut (fun P hP y hy => List.mem_append_left _ (hEnds P hP y hy)) R hR z hz)
      S hS
  · intro R hR S hS hRS x hx
    refine overlayPieces_disjoint_interiors hnd
      (fun P hP y hy => List.mem_append_left _ (hEnds P hP y hy)) (fun P hP Q hQ hPQ hne => ?_)
      hR hS hRS hx
    obtain ⟨u, v, huv, hu, hv⟩ := hMeets P hP Q hQ hPQ hne
    exact ⟨u, v, huv, List.mem_append_left _ hu, List.mem_append_left _ hv⟩
  · -- A required point lies on some piece and is interior to none, hence is an end of one.
    intro p hp hpC
    have hpts : p ∈ pts ++ extra := List.mem_append_right _ hp
    have hpcov : p ∈ cover (overlayPieces (segsOf vs) (pts ++ extra)) := by
      rw [overlayPieces_cover, hcov]; exact hpC
    obtain ⟨R, hR, hpR⟩ := ClosedPolygon.exists_of_mem_cover hpcov
    refine ⟨R, hR, ?_⟩
    by_contra hcon
    push Not at hcon
    exact overlayPieces_avoids hnd p hpts R hR
      (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hpR)

/-- A point of a piece is interior to it or one of its ends. -/
theorem mem_interior_or_end {R : Piece} {x : Plane} (hx : x ∈ R.seg) :
    x ∈ R.interior ∨ x = R.1 ∨ x = R.2 := by
  by_cases hcon : x = R.1 ∨ x = R.2
  · exact Or.inr hcon
  · push Not at hcon
    exact Or.inl (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hx)

/-- The open set that isolates one piece from the others: the union of the balls in which the
curve is that piece alone. -/
def nearPiece (C : Set Plane) (R : Piece) : Set Plane :=
  {y | ∃ x ∈ R.interior, ∃ r > 0, y ∈ ball x r ∧ ball x r ∩ C ⊆ R.seg}

theorem isOpen_nearPiece {C : Set Plane} {R : Piece} : IsOpen (nearPiece C R) := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨x, hx, r, hr, hyb, hsub⟩
  exact ⟨ball x r, fun z hz => ⟨x, hx, r, hr, hz, hsub⟩, isOpen_ball, hyb⟩

namespace IsClean

variable {Q : List Piece} {C : Set Plane} {R S : Piece} {x : Plane} (h : IsClean Q C)
include h

/-- **Two distinct clean pieces meet only at ends of the first.** This is `edges_meet`, before
the pieces have been put in cyclic order. -/
theorem seg_inter_subset (hR : R ∈ Q) (hS : S ∈ Q) (hRS : R ≠ S) :
    R.seg ∩ S.seg ⊆ {R.1, R.2} := by
  rintro z ⟨hzR, hzS⟩
  rcases mem_interior_or_end hzR with hz | hz
  · exfalso
    rcases mem_interior_or_end hzS with hz' | hz'
    · exact h.interiors R hR S hS hRS z hz hz'
    · exact h.ends S hS R hR z hz' hz
  · exact hz

theorem seg_subset (hR : R ∈ Q) : R.seg ⊆ C := by
  rw [← h.cover_eq]
  exact fun z hz => mem_cover hR hz

theorem endSet_subset : endSet Q ⊆ C := by
  rintro z ⟨R, hR, hz⟩
  rcases hz with rfl | rfl
  exacts [h.seg_subset hR (left_mem_segment ℝ _ _), h.seg_subset hR (right_mem_segment ℝ _ _)]

theorem mem_cover_of_mem (hz : x ∈ C) : x ∈ cover Q := by rw [h.cover_eq]; exact hz

/-- **The curve minus the ends is the disjoint union of the piece interiors.** -/
theorem diff_endSet_eq : C \ endSet Q = ⋃ R ∈ Q, R.interior := by
  refine Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨R, hR, hzR⟩ := ClosedPolygon.exists_of_mem_cover (h.mem_cover_of_mem hz.1)
    refine Set.mem_iUnion₂.2 ⟨R, hR, ?_⟩
    rcases mem_interior_or_end hzR with hz' | hz'
    · exact hz'
    · exact absurd (show z ∈ endSet Q from ⟨R, hR, hz'⟩) hz.2
  · obtain ⟨R, hR, hzR⟩ := Set.mem_iUnion₂.1 hz
    exact ⟨h.seg_subset hR (openSegment_subset_segment ℝ _ _ hzR),
      fun ⟨S, hS, hz'⟩ => h.ends S hS R hR z hz' hzR⟩

/-- **Near an interior point the curve is that piece alone.** The other pieces are finitely many
closed sets missing the point: interior points are not shared, and an end of another piece
cannot be interior to this one. -/
theorem exists_ball_subset_seg (hR : R ∈ Q) (hx : x ∈ R.interior) :
    ∃ r > 0, ball x r ∩ C ⊆ R.seg := by
  have hmiss : ∀ S ∈ Q, S ≠ R → x ∉ S.seg := by
    intro S hS hSR hxS
    rcases mem_interior_or_end hxS with hz | hz
    · exact h.interiors S hS R hR hSR x hz hx
    · exact h.ends S hS R hR x hz hx
  obtain ⟨r, hr, hball⟩ := exists_pos_forall_of_finite
    (S := {S : Piece | S ∈ Q ∧ S ≠ R}) (Q.finite_toSet.subset fun _ hS => hS.1)
    (P := fun S ε => ∀ y ∈ ball x ε, y ∉ S.seg)
    (fun _ _ _ _ hδε hP y hy => hP y (ball_subset_ball hδε hy))
    (fun S hS => by
      obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1
        (isCompact_segment S.1 S.2).isClosed.isOpen_compl x (hmiss S hS.1 hS.2)
      exact ⟨ρ, hρ, fun y hy => hsub hy⟩)
  refine ⟨r, hr, ?_⟩
  rintro z ⟨hzb, hzC⟩
  obtain ⟨S, hS, hzS⟩ := ClosedPolygon.exists_of_mem_cover (h.mem_cover_of_mem hzC)
  by_cases hSR : S = R
  · exact hSR ▸ hzS
  · exact absurd hzS (hball S ⟨hS, hSR⟩ z hzb)

theorem interior_subset_nearPiece (hR : R ∈ Q) : R.interior ⊆ nearPiece C R := by
  intro y hy
  obtain ⟨r, hr, hsub⟩ := h.exists_ball_subset_seg hR hy
  exact ⟨y, hy, r, hr, mem_ball_self hr, hsub⟩

omit h in
theorem nearPiece_inter_diff (hR : R ∈ Q) : nearPiece C R ∩ (C \ endSet Q) ⊆ R.interior := by
  rintro z ⟨⟨y, hy, r, hr, hzb, hsub⟩, hzC, hzV⟩
  rcases mem_interior_or_end (hsub ⟨hzb, hzC⟩) with hz | hz
  · exact hz
  · exact absurd (show z ∈ endSet Q from ⟨R, hR, hz⟩) hzV

/-- **A connected piece of the curve away from the ends lies inside a single piece.** The
`nearPiece` sets are honest open sets of the plane that trace out the pieces on the curve, so
`IsPreconnected` can be applied to them directly. -/
theorem preconnected_subset_interior {A : Set Plane} (hA : IsPreconnected A) (hA0 : A.Nonempty)
    (hAsub : A ⊆ C \ endSet Q) : ∃ R ∈ Q, A ⊆ R.interior := by
  obtain ⟨x₀, hx₀⟩ := hA0
  have hAint : A ⊆ ⋃ R ∈ Q, R.interior := by rw [← h.diff_endSet_eq]; exact hAsub
  obtain ⟨R, hR, hx₀R⟩ := Set.mem_iUnion₂.1 (hAint hx₀)
  refine ⟨R, hR, ?_⟩
  set W : Set Plane := ⋃ S ∈ {S : Piece | S ∈ Q ∧ S ≠ R}, nearPiece C S with hW
  have hWopen : IsOpen W := isOpen_biUnion fun _ _ => isOpen_nearPiece
  have hcover : A ⊆ nearPiece C R ∪ W := by
    intro z hz
    obtain ⟨S, hS, hzS⟩ := Set.mem_iUnion₂.1 (hAint hz)
    by_cases hSR : S = R
    · exact Or.inl (h.interior_subset_nearPiece hR (hSR ▸ hzS))
    · exact Or.inr (Set.mem_iUnion₂.2 ⟨S, ⟨hS, hSR⟩, h.interior_subset_nearPiece hS hzS⟩)
  have hempty : ¬ (A ∩ (nearPiece C R ∩ W)).Nonempty := by
    rintro ⟨z, hzA, hzR, hzW⟩
    obtain ⟨S, hS, hzS⟩ := Set.mem_iUnion₂.1 hzW
    exact h.interiors R hR S hS.1 (Ne.symm hS.2) z (nearPiece_inter_diff hR ⟨hzR, hAsub hzA⟩)
      (nearPiece_inter_diff hS.1 ⟨hzS, hAsub hzA⟩)
  have hnotW : ¬ (A ∩ W).Nonempty := fun hv =>
    hempty (hA _ _ isOpen_nearPiece hWopen hcover ⟨x₀, hx₀, h.interior_subset_nearPiece hR hx₀R⟩ hv)
  intro z hz
  refine nearPiece_inter_diff hR ⟨?_, hAsub hz⟩
  exact (hcover hz).resolve_right fun hzW => hnotW ⟨z, hz, hzW⟩

end IsClean

/-! ## The gaps between the parameters

The loop's parameters at which it visits an end of a piece form a finite subset of `[0, 1)`
containing `0`. Listed in increasing order they cut `[0, 1)` into gaps, one per piece; the last
gap runs to `1`, where the loop closes. This section is pure order theory on `ℝ`. -/

section Gaps

variable {n : ℕ} {T : Finset ℝ} (hcard : T.card = n)

/-- The `i`-th parameter, in increasing order. -/
noncomputable def par (T : Finset ℝ) (hcard : T.card = n) (i : Fin n) : ℝ :=
  T.orderEmbOfFin hcard i

/-- The right end of the `i`-th gap: the next parameter, or `1` for the last gap. -/
noncomputable def parNext (T : Finset ℝ) (hcard : T.card = n) (i : Fin n) : ℝ :=
  if h : (i : ℕ) + 1 < n then T.orderEmbOfFin hcard ⟨(i : ℕ) + 1, h⟩ else 1

theorem par_mem (i : Fin n) : par T hcard i ∈ T := T.orderEmbOfFin_mem hcard i

theorem par_lt_par {i j : Fin n} (h : i < j) : par T hcard i < par T hcard j :=
  (T.orderEmbOfFin hcard).strictMono h

theorem par_lt_iff {i j : Fin n} : par T hcard i < par T hcard j ↔ i < j :=
  (T.orderEmbOfFin hcard).lt_iff_lt

theorem par_le_par {i j : Fin n} (h : i ≤ j) : par T hcard i ≤ par T hcard j :=
  (T.orderEmbOfFin hcard).monotone h

theorem exists_par_eq {s : ℝ} (hs : s ∈ T) : ∃ i : Fin n, par T hcard i = s := by
  have := T.range_orderEmbOfFin hcard
  rw [Set.ext_iff] at this
  exact (this s).2 hs

variable (hT : ∀ s ∈ T, s ∈ Ico (0 : ℝ) 1) (h0 : (0 : ℝ) ∈ T)
include hcard hT h0

omit hT in
theorem par_card_pos : 0 < n := by
  rw [← hcard]
  exact Finset.card_pos.2 ⟨0, h0⟩

/-- The first parameter is `0`: the loop is at a vertex when it starts. -/
theorem par_zero : par T hcard ⟨0, par_card_pos hcard h0⟩ = 0 := by
  rw [par, Finset.orderEmbOfFin_zero hcard (par_card_pos hcard h0)]
  exact le_antisymm (Finset.min'_le _ _ h0)
    (Finset.le_min' _ _ _ fun s hs => (hT s hs).1)

omit h0 in
theorem parNext_le_one (i : Fin n) : parNext T hcard i ≤ 1 := by
  rw [parNext]
  split_ifs with hi
  · exact le_of_lt (hT _ (T.orderEmbOfFin_mem hcard _)).2
  · exact le_refl 1

omit h0 in
theorem par_lt_parNext (i : Fin n) : par T hcard i < parNext T hcard i := by
  rw [parNext]
  split_ifs with hi
  · exact par_lt_par hcard (by exact Fin.mk_lt_mk.2 (Nat.lt_succ_self _) : i < ⟨(i : ℕ) + 1, hi⟩)
  · exact (hT _ (par_mem hcard i)).2

omit hT h0 in
/-- No parameter lies strictly inside a gap. -/
theorem notMem_of_mem_gap {i : Fin n} {s : ℝ} (hs : s ∈ Ioo (par T hcard i) (parNext T hcard i)) :
    s ∉ T := by
  intro hsT
  obtain ⟨j, rfl⟩ := exists_par_eq hcard hsT
  have hij : i < j := (par_lt_iff hcard).1 hs.1
  rw [parNext] at hs
  split_ifs at hs with hi
  · exact absurd hs.2 (not_lt.2 (par_le_par hcard (by exact Fin.mk_le_of_le_val hij)))
  · exact absurd j.isLt (by omega)

omit hT h0 in
/-- Distinct gaps are disjoint. -/
theorem gap_disjoint {i j : Fin n} (hij : i ≠ j) :
    Disjoint (Ioo (par T hcard i) (parNext T hcard i))
      (Ioo (par T hcard j) (parNext T hcard j)) := by
  -- One of the two comes first; its right end is at most the other's left end.
  have key : ∀ a b : Fin n, a < b → parNext T hcard a ≤ par T hcard b := by
    intro a b hab
    rw [parNext]
    split_ifs with ha
    · exact par_le_par hcard (Fin.mk_le_of_le_val hab)
    · exact absurd b.isLt (by omega)
  rw [Set.disjoint_left]
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact fun x hx hx' => absurd (lt_of_lt_of_le hx.2 (key i j hlt)) (not_lt.2 hx'.1.le)
  · exact fun x hx hx' => absurd (lt_of_lt_of_le hx'.2 (key j i hlt)) (not_lt.2 hx.1.le)

omit h0 in
theorem gap_subset_Ico (i : Fin n) :
    Ioo (par T hcard i) (parNext T hcard i) ⊆ Ico (0 : ℝ) 1 := fun _ hs =>
  ⟨le_of_lt (lt_of_le_of_lt (hT _ (par_mem hcard i)).1 hs.1),
    lt_of_lt_of_le hs.2 (parNext_le_one hcard hT i)⟩

omit h0 in
theorem gapClosure_subset_I (i : Fin n) :
    Icc (par T hcard i) (parNext T hcard i) ⊆ I := by
  intro s hs
  exact ⟨le_trans (hT _ (par_mem hcard i)).1 hs.1, le_trans hs.2 (parNext_le_one hcard hT i)⟩

/-- **The gaps cover `[0, 1)` minus the parameters.** The gap containing `s` starts at the
largest parameter below `s`. -/
theorem exists_mem_gap {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) (hsT : s ∉ T) :
    ∃ i : Fin n, s ∈ Ioo (par T hcard i) (parNext T hcard i) := by
  classical
  have hn : 0 < n := par_card_pos hcard h0
  -- The gap containing `s` starts at the largest parameter below it.
  obtain ⟨i₀, hi₀le, hi₀max⟩ : ∃ i₀ : Fin n, par T hcard i₀ ≤ s ∧
      ∀ j : Fin n, par T hcard j ≤ s → j ≤ i₀ := by
    have hSne : (Finset.univ.filter fun i : Fin n => par T hcard i ≤ s).Nonempty :=
      ⟨⟨0, hn⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _,
        by rw [par_zero hcard hT h0]; exact hs.1⟩⟩
    exact ⟨_, (Finset.mem_filter.1 (Finset.max'_mem _ hSne)).2,
      fun j hj => Finset.le_max' _ j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)⟩
  refine ⟨i₀, lt_of_le_of_ne hi₀le fun he => hsT (he ▸ par_mem hcard _), ?_⟩
  rw [parNext]
  split_ifs with hi
  · by_contra hcon
    push Not at hcon
    exact absurd (hi₀max ⟨(i₀ : ℕ) + 1, hi⟩ hcon)
      (not_le.2 (Fin.lt_def.2 (Nat.lt_succ_self _)))
  · exact hs.2

end Gaps

/-- A closed interval is its interior together with its two ends. -/
theorem Icc_eq_Ioo_union_ends {a b : ℝ} (hab : a ≤ b) : Icc a b = Ioo a b ∪ {a, b} := by
  ext x
  simp only [mem_Icc, mem_union, mem_Ioo, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    rcases eq_or_lt_of_le h1 with rfl | h1'
    · exact Or.inr (Or.inl rfl)
    · rcases eq_or_lt_of_le h2 with rfl | h2'
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl ⟨h1', h2'⟩
  · rintro (⟨h1, h2⟩ | rfl | rfl)
    · exact ⟨h1.le, h2.le⟩
    · exact ⟨le_refl _, hab⟩
    · exact ⟨hab, le_refl _⟩

/-- Two points of a nondegenerate pair, each known to be one of two given points, exhaust
them. -/
theorem pair_eq_of_mem_pair {a b p q : Plane} (hab : a ≠ b) (ha : a = p ∨ a = q)
    (hb : b = p ∨ b = q) : (a = p ∧ b = q) ∨ (a = q ∧ b = p) := by
  rcases ha with rfl | rfl
  · rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact Or.inl ⟨rfl, rfl⟩
  · rcases hb with rfl | rfl
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hab

/-- The successor in `ZMod n`, read as a numeral below `n`. -/
theorem zmod_val_succ {n : ℕ} (hn : 1 < n) (j : ZMod n) :
    (j + 1).val = if j.val + 1 < n then j.val + 1 else 0 := by
  let _ : NeZero n := ⟨by omega⟩
  have h1 : (1 : ZMod n).val = 1 := by
    rw [show (1 : ZMod n) = ((1 : ℕ) : ZMod n) by norm_num]
    exact ZMod.val_cast_of_lt hn
  rw [ZMod.val_add, h1]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have hj : j.val + 1 = n := by have := ZMod.val_lt j; omega
    rw [hj, Nat.mod_self]

/-! ## From a clean presentation to a cyclic vertex list

The loop reaches an end of a piece at finitely many parameters. Between two consecutive ones it
runs through one whole piece interior — the gap image is connected and misses the ends, so it
lies in one interior; and the interior, being connected and covered by the closed gap images,
lies in that one gap. So the ends, listed in the order the loop reaches them, are the cyclic
vertex list of a `PrePolygon` whose edges are the pieces. -/

/-- A connected set in a finite relatively closed partition lies in the member it meets.
This is shared by the arc and closed-curve realization arguments. -/
theorem eq_of_preconnected_finite_partition {ι X : Type*} [Finite ι] [TopologicalSpace X]
    {A D : Set X} {G Z : ι → Set X} (i : ι)
    (hA : IsPreconnected A) (hAD : A ⊆ D) (hGi : (G i).Nonempty) (hGA : G i ⊆ A)
    (hZclosed : ∀ j, IsClosed (Z j)) (hZdiff : ∀ j, Z j ∩ D = G j)
    (hdisjoint : ∀ j k, j ≠ k → G j ∩ G k = ∅) (hcover : (⋃ j, G j) = D) :
    A = G i := by
  classical
  have hGZ : ∀ j, G j ⊆ Z j := fun j => (hZdiff j) ▸ inter_subset_left
  set W : Set X := ⋃ j ∈ ({i}ᶜ : Set ι), Z j
  have hWclosed : IsClosed W :=
    Set.Finite.isClosed_biUnion (Set.toFinite _) fun j _ => hZclosed j
  have hAZ : A ⊆ Z i ∪ W := by
    intro z hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hcover.symm ▸ hAD hz)
    by_cases hji : j = i
    · exact Or.inl (hGZ i (hji ▸ hj))
    · exact Or.inr (Set.mem_iUnion₂.2 ⟨j, hji, hGZ j hj⟩)
  have hGW : ∀ z ∈ G i, z ∉ W := by
    intro z hz hzW
    obtain ⟨j, hji, hzj⟩ := Set.mem_iUnion₂.1 hzW
    have : z ∈ G j := (hZdiff j) ▸ ⟨hzj, hAD (hGA hz)⟩
    exact Set.eq_empty_iff_forall_notMem.1 (hdisjoint i j (Ne.symm hji)) z ⟨hz, this⟩
  have hcover2 : A ⊆ Wᶜ ∪ (Z i)ᶜ := by
    intro z hz
    by_cases hzW : z ∈ W
    · exact Or.inr fun hzZ => hGW z ((hZdiff i) ▸ ⟨hzZ, hAD hz⟩) hzW
    · exact Or.inl hzW
  have hnone : ¬ (A ∩ (Wᶜ ∩ (Z i)ᶜ)).Nonempty := by
    rintro ⟨z, hz, hzW, hzZ⟩
    rcases hAZ hz with h | h
    exacts [hzZ h, hzW h]
  obtain ⟨z₀, hz₀⟩ := hGi
  have hAu : (A ∩ Wᶜ).Nonempty := ⟨z₀, hGA hz₀, hGW z₀ hz₀⟩
  have hnotv : ¬ (A ∩ (Z i)ᶜ).Nonempty := fun hv =>
    hnone (hA _ _ hWclosed.isOpen_compl (hZclosed i).isOpen_compl hcover2 hAu hv)
  refine Subset.antisymm (fun z hz => ?_) hGA
  have hzZ : z ∈ Z i := by
    by_contra hzZ
    exact hnotv ⟨z, hz, hzZ⟩
  exact (hZdiff i) ▸ ⟨hzZ, hAD hz⟩

/-- The endpoints of a nondegenerate piece are the two boundary points of a closed gap. -/
theorem Piece.ends_of_closed_gap {R : Piece} {Z G : Set Plane} {a b : Plane}
    (hnd : R.1 ≠ R.2) (hclosed : IsClosed Z) (hinterior : R.interior = G)
    (hZ : Z = G ∪ {a, b}) :
    (R.1 = a ∧ R.2 = b) ∨ (R.1 = b ∧ R.2 = a) := by
  have hclosure : R.seg ⊆ Z := by
    have hcl : closure R.interior ⊆ Z := by
      rw [hinterior]
      exact closure_minimal (fun z hz => hZ ▸ Or.inl hz) hclosed
    rwa [Piece.interior, closure_openSegment] at hcl
  have hmem : ∀ z, z = R.1 ∨ z = R.2 → z = a ∨ z = b := by
    intro z hz
    have hzseg : z ∈ R.seg := by
      rcases hz with rfl | rfl
      exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
    rcases hZ ▸ hclosure hzseg with hzG | hzE
    · exfalso
      rw [← hinterior] at hzG
      rcases hz with rfl | rfl
      exacts [hnd (left_mem_openSegment_iff.1 hzG), hnd (right_mem_openSegment_iff.1 hzG)]
    · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hzE
  exact pair_eq_of_mem_pair hnd (hmem _ (Or.inl rfl)) (hmem _ (Or.inr rfl))

/-- A family whose interiors cover a clean presentation contains every piece. -/
theorem IsClean.exists_piece_index {Q : List Piece} {C : Set Plane} (hQ : IsClean Q C)
    {ι : Type*} {pc : ι → Piece} (hpcQ : ∀ i, pc i ∈ Q)
    (hcover : (⋃ i, (pc i).interior) = C \ endSet Q) :
    ∀ R ∈ Q, ∃ i, pc i = R := by
  intro R hR
  have hx : (1 / 2 : ℝ) • R.1 + (1 / 2 : ℝ) • R.2 ∈ R.interior :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hxd : (1 / 2 : ℝ) • R.1 + (1 / 2 : ℝ) • R.2 ∈ C \ endSet Q := by
    rw [hQ.diff_endSet_eq]
    exact Set.mem_iUnion₂.2 ⟨R, hR, hx⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcover.symm ▸ hxd)
  refine ⟨i, ?_⟩
  by_contra hne
  exact hQ.interiors (pc i) (hpcQ i) R hR hne _ hi hx

/-- **A polygonal Jordan curve is the carrier of a cyclic vertex list.** -/
theorem exists_prePolygon_of_isJordanCurve {C : Set Plane} (hJ : IsJordanCurve C)
    (hP : IsPolygonal C) : ∃ (m : ℕ) (P : PrePolygon m), P.carrier = C := by
  classical
  obtain ⟨f, hf, hfC⟩ := hJ
  -- Two distinct points of `C`, so that the clean presentation does not collapse.
  have hmemC : ∀ s ∈ I, f s ∈ C := fun s hs => hfC ▸ ⟨s, hs, rfl⟩
  have h0C : f 0 ∈ C := hmemC 0 zero_mem_I
  have hhC : f (1 / 2) ∈ C := hmemC _ ⟨by norm_num, by norm_num⟩
  have hne : f 0 ≠ f (1 / 2) := fun he =>
    absurd (hf.injOn ⟨le_refl 0, by norm_num⟩ ⟨by norm_num, by norm_num⟩ he) (by norm_num)
  obtain ⟨Q, hQ, hextra⟩ := exists_isClean hP h0C hhC hne [f 0]
  obtain ⟨R₀, hR₀, hR₀end⟩ := hextra (f 0) (List.mem_singleton_self _) h0C
  have hV₀ : f 0 ∈ endSet Q := ⟨R₀, hR₀, hR₀end⟩
  -- Every point of the curve is reached before the loop closes.
  have hsurj : ∀ z ∈ C, ∃ s ∈ Ico (0 : ℝ) 1, f s = z := by
    intro z hz
    rw [← hfC] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    rcases eq_or_lt_of_le hs.2 with rfl | hlt
    · exact ⟨0, ⟨le_refl 0, by norm_num⟩, hf.closes⟩
    · exact ⟨s, ⟨hs.1, hlt⟩, rfl⟩
  -- The parameters at which the loop is at an end of a piece.
  have hTfin : {t : ℝ | t ∈ Ico (0 : ℝ) 1 ∧ f t ∈ endSet Q}.Finite := by
    refine Set.Finite.of_finite_image (f := f) ((finite_endSet Q).subset ?_)
      (hf.injOn.mono fun t ht => ht.1)
    rintro x ⟨t, ht, rfl⟩
    exact ht.2
  obtain ⟨n, hcard⟩ : ∃ n, hTfin.toFinset.card = n := ⟨_, rfl⟩
  set TF : Finset ℝ := hTfin.toFinset with hTFdef
  have hmemTF : ∀ t : ℝ, t ∈ TF ↔ (t ∈ Ico (0 : ℝ) 1 ∧ f t ∈ endSet Q) := by
    intro t; rw [hTFdef, Set.Finite.mem_toFinset]; exact Iff.rfl
  have hTle : ∀ s ∈ TF, s ∈ Ico (0 : ℝ) 1 := fun s hs => ((hmemTF s).1 hs).1
  have h0TF : (0 : ℝ) ∈ TF := (hmemTF 0).2 ⟨⟨le_refl 0, by norm_num⟩, hV₀⟩
  set tp : Fin n → ℝ := par TF hcard with htp
  set nx : Fin n → ℝ := parNext TF hcard with hnx
  -- Both ends of every gap are ends of pieces.
  have htpV : ∀ i : Fin n, f (tp i) ∈ endSet Q := fun i =>
    ((hmemTF _).1 (par_mem hcard i)).2
  have hnxV : ∀ i : Fin n, f (nx i) ∈ endSet Q := by
    intro i
    rw [hnx, parNext]
    split_ifs with hi
    · exact ((hmemTF _).1 (Finset.orderEmbOfFin_mem _ _ _)).2
    · rw [← hf.closes]; exact hV₀
  have hlt : ∀ i : Fin n, tp i < nx i := fun i => par_lt_parNext hcard hTle i
  have hIcc : ∀ i : Fin n, Icc (tp i) (nx i) ⊆ I := fun i => gapClosure_subset_I hcard hTle i
  have hIoo : ∀ i : Fin n, Ioo (tp i) (nx i) ⊆ Ico (0 : ℝ) 1 := fun i =>
    gap_subset_Ico hcard hTle i
  set G : Fin n → Set Plane := fun i => f '' Ioo (tp i) (nx i) with hG
  set Z : Fin n → Set Plane := fun i => f '' Icc (tp i) (nx i) with hZ
  have hGne : ∀ i, (G i).Nonempty := fun i =>
    ((Set.nonempty_Ioo.2 (hlt i)).image f)
  have hGconn : ∀ i, IsPreconnected (G i) := fun i =>
    isPreconnected_Ioo.image f (hf.continuousOn.mono (fun s hs => hIcc i (Ioo_subset_Icc_self hs)))
  have hGdiff : ∀ i, G i ⊆ C \ endSet Q := by
    rintro i z ⟨s, hs, rfl⟩
    refine ⟨hmemC s (hIcc i (Ioo_subset_Icc_self hs)), fun hzV => ?_⟩
    exact notMem_of_mem_gap hcard hs ((hmemTF s).2 ⟨hIoo i hs, hzV⟩)
  have hZcompact : ∀ i, IsCompact (Z i) := fun i =>
    isCompact_image_of_subset_I hf.continuousOn (hIcc i) isClosed_Icc
  have hZeq : ∀ i, Z i = G i ∪ {f (tp i), f (nx i)} := by
    intro i
    simp only [hZ, hG]
    rw [Icc_eq_Ioo_union_ends (hlt i).le, Set.image_union, Set.image_pair]
  have hZdiff : ∀ i, Z i ∩ (C \ endSet Q) = G i := by
    intro i
    refine Set.Subset.antisymm ?_ (fun z hz => ⟨(hZeq i) ▸ Or.inl hz, hGdiff i hz⟩)
    rintro z ⟨hzZ, hzC, hzV⟩
    rcases (hZeq i) ▸ hzZ with hz | hz
    · exact hz
    · rcases hz with rfl | rfl
      exacts [absurd (htpV i) hzV, absurd (hnxV i) hzV]
  have hGdisj : ∀ i j : Fin n, i ≠ j → G i ∩ G j = ∅ := by
    intro i j hij
    refine Set.eq_empty_of_forall_notMem ?_
    rintro z ⟨⟨s, hs, rfl⟩, t, ht, hts⟩
    have := hf.injOn (hIoo j ht) (hIoo i hs) hts
    exact Set.disjoint_left.1 (gap_disjoint hcard hij) hs (this ▸ ht)
  -- The gaps cover the curve away from the ends of the pieces.
  have hcov : (⋃ i, G i) = C \ endSet Q := by
    refine Set.Subset.antisymm (Set.iUnion_subset hGdiff) (fun z hz => ?_)
    obtain ⟨s, hs, rfl⟩ := hsurj z hz.1
    obtain ⟨i, hi⟩ := exists_mem_gap hcard hTle h0TF hs
      (fun hsT => hz.2 ((hmemTF s).1 hsT).2)
    exact Set.mem_iUnion.2 ⟨i, ⟨s, hi, rfl⟩⟩
  -- Each gap image lies in one piece interior.
  have hchoose : ∀ i, ∃ R ∈ Q, G i ⊆ R.interior := fun i =>
    hQ.preconnected_subset_interior (hGconn i) (hGne i) (hGdiff i)
  choose pc hpcQ hpcsub using hchoose
  -- And is the whole of it: the interior is connected and covered by the closed gap images.
  have hpceq : ∀ i, (pc i).interior = G i := by
    intro i
    apply eq_of_preconnected_finite_partition i (convex_openSegment _ _).isPreconnected
      (G := G) (Z := Z) ?_ (hGne i) (hpcsub i)
      (fun j => (hZcompact j).isClosed) hZdiff hGdisj hcov
    rw [hQ.diff_endSet_eq]
    exact fun z hz => Set.mem_iUnion₂.2 ⟨pc i, hpcQ i, hz⟩
  -- The correspondence between gaps and pieces is a bijection.
  have hpcinj : Function.Injective pc := by
    intro i j hij
    by_contra hne'
    obtain ⟨z, hz⟩ := hGne i
    have hzj : z ∈ G j := by rw [← hpceq j, ← hij, hpceq i]; exact hz
    exact Set.eq_empty_iff_forall_notMem.1 (hGdisj i j hne') z ⟨hz, hzj⟩
  have hpcsurj : ∀ R ∈ Q, ∃ i, pc i = R :=
    hQ.exists_piece_index hpcQ (by simpa only [hpceq] using hcov)
  -- The ends of the piece are the two ends of the gap.
  have hends : ∀ i, ((pc i).1 = f (tp i) ∧ (pc i).2 = f (nx i)) ∨
      ((pc i).1 = f (nx i) ∧ (pc i).2 = f (tp i)) := by
    intro i
    exact Piece.ends_of_closed_gap (hQ.nondeg _ (hpcQ i)) (hZcompact i).isClosed
      (hpceq i) (hZeq i)
  have hpcseg : ∀ i, (pc i).seg = segment ℝ (f (tp i)) (f (nx i)) := by
    intro i
    rcases hends i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Piece.seg, h1, h2]
    · rw [Piece.seg, h1, h2, segment_symm]
  have hfne : ∀ i, f (tp i) ≠ f (nx i) := by
    intro i he
    refine hQ.nondeg _ (hpcQ i) ?_
    rcases hends i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact he
    · rw [h1, h2]; exact he.symm
  -- There are at least three parameters.
  have hn0 : 0 < n := par_card_pos hcard h0TF
  have htp0 : tp ⟨0, hn0⟩ = 0 := par_zero hcard hTle h0TF
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with hlt2 | hge
    · exfalso
      have hcond : ¬ ((⟨0, hn0⟩ : Fin n) : ℕ) + 1 < n :=
        fun hc => absurd (lt_of_le_of_lt (Nat.le_add_left 1 _) hc) (by omega)
      have hnx0 : nx ⟨0, hn0⟩ = 1 := by rw [hnx, parNext, dite_eq_right hcond]
      exact hfne ⟨0, hn0⟩ (by rw [htp0, hnx0]; exact hf.closes)
    · exact hge
  let _ : NeZero n := ⟨by omega⟩
  -- The cyclic vertex list: the ends, in the order the loop reaches them.
  set w : ZMod n → Plane := fun j => f (tp ⟨j.val, ZMod.val_lt j⟩) with hw
  have hwsucc : ∀ j : ZMod n, w (j + 1) = f (nx ⟨j.val, ZMod.val_lt j⟩) := by
    intro j
    have hjlt := ZMod.val_lt j
    by_cases hj : j.val + 1 < n
    · have hval : (j + 1).val = j.val + 1 := by rw [zmod_val_succ (by omega) j, ite_eq_left hj]
      have hfin : (⟨(j + 1).val, ZMod.val_lt (j + 1)⟩ : Fin n) = ⟨j.val + 1, hj⟩ :=
        Fin.val_injective hval
      simp only [hw, hfin]
      rw [hnx, parNext, dite_eq_left (show (⟨j.val, hjlt⟩ : Fin n).val + 1 < n from hj)]
      rfl
    · have hval : (j + 1).val = 0 := by rw [zmod_val_succ (by omega) j, ite_eq_right hj]
      have hfin : (⟨(j + 1).val, ZMod.val_lt (j + 1)⟩ : Fin n) = ⟨0, hn0⟩ :=
        Fin.val_injective hval
      simp only [hw, hfin]
      rw [htp0, hnx, parNext, dite_eq_right (show ¬ ((⟨j.val, hjlt⟩ : Fin n).val + 1 < n) from hj)]
      exact hf.closes
  have hedgeq : ∀ j : ZMod n,
      segment ℝ (w j) (w (j + 1)) = (pc ⟨j.val, ZMod.val_lt j⟩).seg := by
    intro j
    rw [hwsucc j, hpcseg]
  have hwinj : Function.Injective w := by
    intro j k hjk
    simp only [hw] at hjk
    have h1 := hf.injOn (hTle _ (par_mem hcard ⟨j.val, ZMod.val_lt j⟩))
      (hTle _ (par_mem hcard ⟨k.val, ZMod.val_lt k⟩)) hjk
    exact ZMod.val_injective _ (congrArg Fin.val ((TF.orderEmbOfFin hcard).injective h1))
  have hwmeet : ∀ i j : ZMod n, i ≠ j →
      segment ℝ (w i) (w (i + 1)) ∩ segment ℝ (w j) (w (j + 1)) ⊆ {w i, w (i + 1)} := by
    intro i j hij
    rw [hedgeq i, hedgeq j]
    have hne' : pc ⟨i.val, ZMod.val_lt i⟩ ≠ pc ⟨j.val, ZMod.val_lt j⟩ := fun he =>
      hij (ZMod.val_injective _ (congrArg Fin.val (hpcinj he)))
    refine le_trans (hQ.seg_inter_subset (hpcQ _) (hpcQ _) hne') ?_
    have hwi : w i = f (tp ⟨i.val, ZMod.val_lt i⟩) := rfl
    rcases hends ⟨i.val, ZMod.val_lt i⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, ← hwi, ← hwsucc i]
    · rw [h1, h2, ← hwi, ← hwsucc i, Set.pair_comm]
  have hn3 : 3 ≤ n := by
    rcases Nat.lt_or_ge n 3 with hlt3 | hge
    · exfalso
      have hn2' : n = 2 := by omega
      have hone : (1 : ZMod n).val = 1 := by
        rw [show (1 : ZMod n) = ((1 : ℕ) : ZMod n) by norm_num]
        exact ZMod.val_cast_of_lt (by omega)
      have h01 : (0 : ZMod n) ≠ 1 := by
        intro he
        have hv : (0 : ZMod n).val = (1 : ZMod n).val := by rw [he]
        rw [ZMod.val_zero, hone] at hv
        omega
      have hsucc1 : (1 : ZMod n) + 1 = 0 := by
        refine ZMod.val_injective _ ?_
        rw [zmod_val_succ (by omega) 1, hone, ite_eq_right (by omega), ZMod.val_zero]
      have hw01 : w 0 ≠ w 1 := fun he => h01 (hwinj he)
      obtain ⟨p, hp, hp1, hp2⟩ := PrePolygon.exists_mem_segment_ne hw01
      have hmem := hwmeet 0 1 h01
        ⟨by rw [zero_add]; exact hp, by rw [hsucc1, segment_symm]; exact hp⟩
      rw [zero_add] at hmem
      rcases hmem with h | h
      exacts [hp1 h, hp2 h]
    · exact hge
  -- Assemble.
  refine (PrePolygon.exists_prePolygon hn3 w hwinj hwmeet).imp fun m hm => hm.imp fun P hP => ?_
  rw [hP, ← hQ.cover_eq]
  refine Set.Subset.antisymm (Set.iUnion_subset fun j => ?_) ?_
  · rw [hedgeq j]
    exact fun z hz => mem_cover (hpcQ _) hz
  · rw [cover]
    refine Set.iUnion₂_subset fun R hR => ?_
    obtain ⟨i, rfl⟩ := hpcsurj R hR
    have hfin : (⟨((i.val : ℕ) : ZMod n).val, ZMod.val_lt _⟩ : Fin n) = i :=
      Fin.val_injective (ZMod.val_cast_of_lt i.isLt)
    refine le_trans (le_of_eq ?_)
      (Set.subset_iUnion (fun j : ZMod n => segment ℝ (w j) (w (j + 1))) ((i.val : ℕ) : ZMod n))
    rw [hedgeq, hfin]

/-! ## The realization theorem -/

/-- **Every simple closed polygonal curve is the carrier of a `ClosedPolygon`.** This is the
blueprint's set-level notion — `IsJordanCurve` together with `IsPolygonal`, no condition on
vertices — matched with the presentation the development works with. -/
theorem exists_closedPolygon {C : Set Plane} (hJ : IsJordanCurve C) (hP : IsPolygonal C) :
    ∃ (m : ℕ) (P : ClosedPolygon m), P.carrier = C := by
  obtain ⟨m, P, hcar⟩ := exists_prePolygon_of_isJordanCurve hJ hP
  obtain ⟨m', P', hcar'⟩ := PrePolygon.exists_closedPolygon_of_prePolygon m P
  exact ⟨m', P', by rw [hcar', hcar]⟩

/-! ## Corners

A realization cannot put a vertex wherever it likes: `corner` forbids a vertex at which the
curve runs straight through. The points that *must* be vertices are exactly the ones at which
it does not, and this is what a consumer needing a named point to be a vertex has to check. -/

/-- `C` runs **straight** through `p` when, near `p`, it lies inside a segment having `p` in its
interior. -/
def IsStraightAt (C : Set Plane) (p : Plane) : Prop :=
  ∃ a b : Plane, p ∈ openSegment ℝ a b ∧ ∃ r > 0, ball p r ∩ C ⊆ segment ℝ a b

/-- A **corner** of `C`: a point of it at which it does not run straight. -/
def IsCornerAt (C : Set Plane) (p : Plane) : Prop := p ∈ C ∧ ¬ IsStraightAt C p

/-- **Every corner is a vertex.** A point interior to an edge lies on no other edge, so a small
ball meets the curve only in that edge — and then the curve runs straight through it. -/
theorem ClosedPolygon.exists_vertex_eq_of_isCornerAt {m : ℕ} (P : ClosedPolygon m) {p : Plane}
    (hp : IsCornerAt P.carrier p) : ∃ i : ZMod (m + 3), P.vertex i = p := by
  obtain ⟨i, hpi⟩ := Set.mem_iUnion.1 hp.1
  by_cases hend : p = P.vertex i ∨ p = P.vertex (i + 1)
  · rcases hend with rfl | rfl
    exacts [⟨i, rfl⟩, ⟨i + 1, rfl⟩]
  · exfalso
    push Not at hend
    have hopen : p ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1)) :=
      mem_openSegment_of_ne_left_right (Ne.symm hend.1) (Ne.symm hend.2) hpi
    -- The other edges are finitely many closed sets missing `p`.
    obtain ⟨r, hr, hball⟩ := exists_pos_forall_of_finite
      (S := {j : ZMod (m + 3) | j ≠ i}) (Set.toFinite _)
      (P := fun j ε => ∀ y ∈ ball p ε, y ∉ P.edge j)
      (fun _ _ _ _ hδε hQ y hy => hQ y (ball_subset_ball hδε hy))
      (fun j hj => by
        obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1
          (isCompact_segment (P.vertex j) (P.vertex (j + 1))).isClosed.isOpen_compl p
          (ClosedPolygon.notMem_edge_of_mem_openSegment hj hopen)
        exact ⟨ρ, hρ, fun y hy => hsub hy⟩)
    refine hp.2 ⟨P.vertex i, P.vertex (i + 1), hopen, r, hr, ?_⟩
    rintro z ⟨hzb, hzC⟩
    obtain ⟨j, hzj⟩ := Set.mem_iUnion.1 hzC
    by_cases hji : j = i
    · exact hji ▸ hzj
    · exact absurd hzj (hball j hji z hzb)

/-- Two points of a segment differ by a multiple of its direction. -/
theorem sub_eq_smul_of_mem_segment {a b x y : Plane} (hx : x ∈ segment ℝ a b)
    (hy : y ∈ segment ℝ a b) : ∃ c : ℝ, x - y = c • (a - b) := by
  obtain ⟨α, β, -, -, hαβ, rfl⟩ := hx
  obtain ⟨γ, δ, -, -, hγδ, rfl⟩ := hy
  have hb : β = 1 - α := by linarith
  have hd : δ = 1 - γ := by linarith
  subst hb; subst hd
  exact ⟨α - γ, by module⟩

/-- Three points of one segment are collinear. -/
theorem det_eq_zero_of_mem_segment {a b x y z : Plane} (hx : x ∈ segment ℝ a b)
    (hy : y ∈ segment ℝ a b) (hz : z ∈ segment ℝ a b) : det (x - z) (y - z) = 0 := by
  obtain ⟨c, hc⟩ := sub_eq_smul_of_mem_segment hx hz
  obtain ⟨d, hd⟩ := sub_eq_smul_of_mem_segment hy hz
  rw [hc, hd, det_smul_left, det_smul_right, det_self, mul_zero, mul_zero]

/-- **Every vertex is a corner.** With `ClosedPolygon.exists_vertex_eq_of_isCornerAt` this says
that the vertex set of a realization is *exactly* the corner set of the curve — so any two
realizations of one curve have the same vertices, and a point can be required to be a vertex
precisely when it is a corner. -/
theorem ClosedPolygon.isCornerAt_vertex {m : ℕ} (P : ClosedPolygon m) (i : ZMod (m + 3)) :
    IsCornerAt P.carrier (P.vertex i) := by
  refine ⟨P.vertex_mem_carrier, ?_⟩
  rintro ⟨a, b, hvab, r, hr, hsub⟩
  refine P.corner i ?_
  set u : Plane := P.vertex (i + 1) - P.vertex i with hu
  set w : Plane := P.vertex (i - 1) - P.vertex i with hw
  set t : ℝ := min 1 (r / (2 * (‖u‖ + ‖w‖ + 1))) with ht
  have hM : (0 : ℝ) < ‖u‖ + ‖w‖ + 1 := by positivity
  have htpos : 0 < t := lt_min one_pos (by positivity)
  have htle : t ≤ 1 := min_le_left _ _
  -- A short step along either edge stays inside the ball.
  have key : ∀ v : Plane, ‖v‖ ≤ ‖u‖ + ‖w‖ + 1 → t * ‖v‖ < r := by
    intro v hv
    calc t * ‖v‖ ≤ (r / (2 * (‖u‖ + ‖w‖ + 1))) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg v)
      _ < r := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg v]
  have hstep : ∀ v : Plane, ‖v‖ ≤ ‖u‖ + ‖w‖ + 1 →
      P.vertex i + t • v ∈ ball (P.vertex i) r := by
    intro v hv
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos htpos]
    exact key v hv
  have hxmem : P.vertex i + t • u ∈ segment ℝ a b := by
    refine hsub ⟨hstep u (by linarith [norm_nonneg w]), ?_⟩
    refine ClosedPolygon.edge_subset_carrier (i := i)
      ⟨1 - t, t, by linarith, htpos.le, by ring, ?_⟩
    rw [hu]; module
  have hymem : P.vertex i + t • w ∈ segment ℝ a b := by
    refine hsub ⟨hstep w (by linarith [norm_nonneg u]), ?_⟩
    refine ClosedPolygon.edge_subset_carrier (i := i - 1)
      ⟨t, 1 - t, htpos.le, by linarith, by ring, ?_⟩
    rw [hw, sub_add_cancel]; module
  have hvmem : P.vertex i ∈ segment ℝ a b := openSegment_subset_segment ℝ _ _ hvab
  have hdet := det_eq_zero_of_mem_segment hymem hxmem hvmem
  rw [add_sub_cancel_left, add_sub_cancel_left, det_smul_left, det_smul_right] at hdet
  have hne : t * (t * det w u) = 0 := hdet
  rcases mul_eq_zero.1 hne with h | h
  · exact absurd h htpos.ne'
  · rcases mul_eq_zero.1 h with h' | h'
    · exact absurd h' htpos.ne'
    · exact h'

/-- **The realization theorem, with named corners.** Any finite list of corners of the curve can
be required to be among the vertices — and by `ClosedPolygon.exists_vertex_eq_of_isCornerAt`,
being a corner is exactly what a point must be for that to be possible. -/
theorem exists_closedPolygon_corners {C : Set Plane} (hJ : IsJordanCurve C) (hP : IsPolygonal C)
    (S : List Plane) (hS : ∀ p ∈ S, IsCornerAt C p) :
    ∃ (m : ℕ) (P : ClosedPolygon m), P.carrier = C ∧
      ∀ p ∈ S, ∃ i : ZMod (m + 3), P.vertex i = p := by
  obtain ⟨m, P, hcar⟩ := exists_closedPolygon hJ hP
  exact ⟨m, P, hcar, fun p hp => P.exists_vertex_eq_of_isCornerAt (by rw [hcar]; exact hS p hp)⟩

/-- **The realization theorem, tracking a splitting.** Two distinct corners of the curve become
two vertices `a` and `a + k` of the realization, which is what names the two arcs
`P.arc a k` and `P.arc (a + k) (m + 3 - k)` that they cut it into.

The corner hypothesis is not an artefact: `ClosedPolygon.corner` forbids a vertex where the
curve runs straight through, so a splitting point that is *not* a corner cannot be a vertex of
any realization. -/
theorem exists_closedPolygon_split {C : Set Plane} (hJ : IsJordanCurve C) (hP : IsPolygonal C)
    {p q : Plane} (hp : IsCornerAt C p) (hq : IsCornerAt C q) (hpq : p ≠ q) :
    ∃ (m : ℕ) (P : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ), P.carrier = C ∧
      P.vertex a = p ∧ P.vertex (a + (k : ZMod (m + 3))) = q ∧ 1 ≤ k ∧ k ≤ m + 2 := by
  obtain ⟨m, P, hcar, hvert⟩ := exists_closedPolygon_corners hJ hP [p, q]
    (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      exacts [hp, hq])
  obtain ⟨a, ha⟩ := hvert p (by simp)
  obtain ⟨b, hb⟩ := hvert q (by simp)
  have hab : b - a ≠ 0 := fun he => hpq (by rw [← ha, ← hb, show b = a by linear_combination he])
  refine ⟨m, P, a, (b - a).val, hcar, ha, ?_, ?_, ?_⟩
  · rw [ZMod.natCast_rightInverse (b - a), add_sub_cancel]; exact hb
  · rcases Nat.eq_zero_or_pos (b - a).val with h0 | h0
    · exact absurd (by rw [← ZMod.natCast_rightInverse (b - a), h0, Nat.cast_zero]) hab
    · exact h0
  · have := ZMod.val_lt (b - a)
    omega

/-! ## The two arcs of a splitting

`ClosedPolygon.arc a k` and `ClosedPolygon.arc (a + k) (m + 3 - k)` are what a consumer tracking
a decomposition of the curve has to be handed. This section says what they are: two arcs between
the two cut vertices, covering the curve and meeting exactly there. -/

namespace ClosedPolygon

variable {m : ℕ}

/-- The same closed polygon, read from vertex `a` onwards. -/
def rotate (P : ClosedPolygon m) (a : ZMod (m + 3)) : ClosedPolygon m where
  vertex j := P.vertex (a + j)
  vertex_inj i j h := add_left_cancel (P.vertex_inj h)
  edges_meet i j hij := by
    have hi : a + (i + 1) = a + i + 1 := by ring
    have hj : a + (j + 1) = a + j + 1 := by ring
    simp only [hi, hj]
    exact P.edges_meet _ _ fun h => hij (add_left_cancel h)
  corner i := by
    have h1 : a + (i - 1) = a + i - 1 := by ring
    have h2 : a + (i + 1) = a + i + 1 := by ring
    simp only [h1, h2]
    exact P.corner (a + i)

@[simp] theorem rotate_vertex (P : ClosedPolygon m) (a j : ZMod (m + 3)) :
    (P.rotate a).vertex j = P.vertex (a + j) := rfl

theorem rotate_edge (P : ClosedPolygon m) (a j : ZMod (m + 3)) :
    (P.rotate a).edge j = P.edge (a + j) := by
  rw [edge, edge, rotate_vertex, rotate_vertex, show a + (j + 1) = a + j + 1 by ring]

variable {P : ClosedPolygon m} {a : ZMod (m + 3)} {k : ℕ} {z : Plane}

/-- An arc is the union of the `k` edges leaving vertices `a, a + 1, …`. -/
theorem mem_arc_iff : z ∈ P.arc a k ↔ ∃ t < k, z ∈ P.edge (a + (t : ZMod (m + 3))) := by
  constructor
  · intro hz
    obtain ⟨R, hR, hzR⟩ := exists_of_mem_cover hz
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hR
    exact ⟨t, List.mem_range.1 ht, hzR⟩
  · rintro ⟨t, ht, hz⟩
    exact mem_cover (List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩) hz

/-- An arc of `P` is a chain of the polygon read from its first vertex. -/
theorem arc_eq_chain (P : ClosedPolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    P.arc a k = (P.rotate a).chain (k - 1) := by
  ext z
  rw [mem_arc_iff, mem_chain_iff]
  constructor
  · rintro ⟨t, ht, hz⟩
    exact ⟨t, by omega, by rw [rotate_edge]; exact hz⟩
  · rintro ⟨j, hj, hz⟩
    rw [rotate_edge] at hz
    exact ⟨j, by omega, hz⟩

/-- **An arc of a splitting is an arc between the two cut vertices.** -/
theorem isArcBetween_arc (P : ClosedPolygon m) (a : ZMod (m + 3)) (hk1 : 1 ≤ k)
    (hk2 : k ≤ m + 2) : IsArcBetween (P.arc a k) (P.vertex a) (P.vertex (a + k)) := by
  have h := (P.rotate a).isArcBetween_chain (k - 1) (by omega)
  rw [← arc_eq_chain P a hk1, show ((k - 1 + 1 : ℕ) : ZMod (m + 3)) = (k : ZMod (m + 3)) by
    congr 1; omega] at h
  simpa using h

/-- Distinct index numerals below the modulus name distinct vertices, after any shift. -/
theorem natCast_shift_inj (P : ClosedPolygon m) (a : ZMod (m + 3)) {x y : ℕ} (hx : x < m + 3)
    (hy : y < m + 3) (he : P.vertex (a + (x : ZMod (m + 3))) = P.vertex (a + (y : ZMod (m + 3)))) :
    x = y :=
  natCast_inj hx hy (add_left_cancel (P.vertex_inj he))

/-- **The two arcs of a splitting meet exactly at the two cut vertices.** A point on both lies
on an edge of each; `edges_meet`, read in both directions, puts it at a vertex shared by the two
edges, and the only shared vertices are the two ends of the split. -/
theorem arc_inter (P : ClosedPolygon m) (a : ZMod (m + 3)) (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2) :
    P.arc a k ∩ P.arc (a + k) (m + 3 - k) = {P.vertex a, P.vertex (a + k)} := by
  refine Set.Subset.antisymm ?_ (Set.subset_inter (P.endpoints_subset_arc a hk1)
    (P.endpoints_subset_arc' a hk2))
  rintro z ⟨hz1, hz2⟩
  obtain ⟨s, hs, hzs⟩ := mem_arc_iff.1 hz1
  obtain ⟨t, ht, hzt⟩ := mem_arc_iff.1 hz2
  have hkt : k + t < m + 3 := by omega
  rw [show a + (k : ZMod (m + 3)) + (t : ZMod (m + 3)) = a + ((k + t : ℕ) : ZMod (m + 3)) by
    push_cast; ring] at hzt
  -- The two edges are different, so each traps `z` among its own two ends.
  have hij : a + (s : ZMod (m + 3)) ≠ a + ((k + t : ℕ) : ZMod (m + 3)) := fun he =>
    absurd (natCast_inj (by omega) hkt (add_left_cancel he)) (by omega)
  have hsucc₁ : a + (s : ZMod (m + 3)) + 1 = a + ((s + 1 : ℕ) : ZMod (m + 3)) := by
    push_cast; ring
  have hsucc₂ : a + ((k + t : ℕ) : ZMod (m + 3)) + 1 = a + ((k + t + 1 : ℕ) : ZMod (m + 3)) := by
    push_cast; ring
  have hA := P.edges_meet _ _ hij (Set.mem_inter hzs hzt)
  have hB := P.edges_meet _ _ (Ne.symm hij) (Set.mem_inter hzt hzs)
  rw [hsucc₁] at hA
  rw [hsucc₂] at hB
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB ⊢
  -- The wrap-around: `k + t + 1` is either below the modulus or exactly it.
  have hzero : k + t + 1 = m + 3 → ((k + t + 1 : ℕ) : ZMod (m + 3)) = ((0 : ℕ) : ZMod (m + 3)) := by
    intro he
    rw [he, Nat.cast_zero, ZMod.natCast_self]
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact absurd (hA.symm.trans hB) fun he => hij (P.vertex_inj he)
  · -- `s ≡ k + t + 1`: possible only by wrapping round, and then `s = 0`.
    rcases Nat.lt_or_ge (k + t + 1) (m + 3) with hlt | hge
    · exact absurd (P.natCast_shift_inj a (by omega) hlt (hA.symm.trans hB)) (by omega)
    · have he : k + t + 1 = m + 3 := by omega
      have hs0 : s = 0 := P.natCast_shift_inj a (by omega) (by omega)
        ((hA.symm.trans hB).trans (by rw [hzero he]))
      exact Or.inl (by rw [hA, hs0, Nat.cast_zero, add_zero])
  · -- `s + 1 ≡ k + t`: forces `s + 1 = k` and `t = 0`.
    have hst : s + 1 = k + t := P.natCast_shift_inj a (by omega) hkt (hA.symm.trans hB)
    exact Or.inr (by rw [hA, show s + 1 = k by omega])
  · exfalso
    rcases Nat.lt_or_ge (k + t + 1) (m + 3) with hlt | hge
    · exact absurd (P.natCast_shift_inj a (by omega) hlt (hA.symm.trans hB)) (by omega)
    · have he : k + t + 1 = m + 3 := by omega
      have := P.natCast_shift_inj a (show s + 1 < m + 3 by omega) (show 0 < m + 3 by omega)
        ((hA.symm.trans hB).trans (by rw [hzero he]))
      omega

end ClosedPolygon

/-! ## The two-arc decomposition is unique

Two points cut a Jordan curve into two arcs, and *only* into those two: the interior of any arc
of the curve between them is connected and misses both, so it lies on one side of any other such
splitting. Without this a realization could name two arcs and still not be known to name the two
arcs a consumer started from. -/

/-- The interior of an arc — the arc less its two endpoints — is connected and nonempty. The
paired form the uniqueness argument below destructures; both halves are in
`Schoenflies/Subarc.lean`, which is where the shared set identity `A ∖ {p, q} = f '' Ioo 0 1`
lives. -/
theorem IsArcBetween.preconnected_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    IsPreconnected (A \ {p, q}) ∧ (A \ {p, q}).Nonempty :=
  ⟨h.isPreconnected_diff, h.nonempty_diff⟩

/-- **The two arcs a pair of points cuts a curve into are determined.** -/
theorem two_arcs_unique {C A₁ A₂ D₁ D₂ : Set Plane} {p q : Plane}
    (hA : A₁ ∪ A₂ = C) (hAi : A₁ ∩ A₂ = {p, q})
    (hD : D₁ ∪ D₂ = C) (hDi : D₁ ∩ D₂ = {p, q})
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q)
    (hD1 : IsArcBetween D₁ p q) (hD2 : IsArcBetween D₂ p q) :
    (A₁ = D₁ ∧ A₂ = D₂) ∨ (A₁ = D₂ ∧ A₂ = D₁) := by
  have hpA : p ∈ A₁ ∩ A₂ := by rw [hAi]; exact Or.inl rfl
  have hqA : q ∈ A₁ ∩ A₂ := by rw [hAi]; exact Or.inr rfl
  have hpD : p ∈ D₁ ∩ D₂ := by rw [hDi]; exact Or.inl rfl
  have hqD : q ∈ D₁ ∩ D₂ := by rw [hDi]; exact Or.inr rfl
  -- An arc between the two points lies on one side of the other splitting.
  have key : ∀ A : Set Plane, IsArcBetween A p q → A ⊆ C → A ⊆ D₁ ∨ A ⊆ D₂ := by
    intro A hAar hAC
    obtain ⟨hconn, hne⟩ := hAar.preconnected_diff
    have hsub : A \ {p, q} ⊆ D₁ᶜ ∪ D₂ᶜ := by
      intro z hz
      by_cases h1 : z ∈ D₁
      · by_cases h2 : z ∈ D₂
        · exact absurd (show z ∈ ({p, q} : Set Plane) by rw [← hDi]; exact ⟨h1, h2⟩) hz.2
        · exact Or.inr h2
      · exact Or.inl h1
    have hnone : ¬ ((A \ {p, q}) ∩ (D₁ᶜ ∩ D₂ᶜ)).Nonempty := by
      rintro ⟨z, hz, h1, h2⟩
      have hzC : z ∈ C := hAC hz.1
      rw [← hD] at hzC
      exact hzC.elim h1 h2
    -- Whichever side the interior meets, it stays there; the two endpoints are on both.
    have hends : ∀ D : Set Plane, p ∈ D → q ∈ D → A \ {p, q} ⊆ D → A ⊆ D := by
      intro D hpD' hqD' hsub' z hz
      by_cases hzpq : z ∈ ({p, q} : Set Plane)
      · rcases hzpq with rfl | rfl
        exacts [hpD', hqD']
      · exact hsub' ⟨hz, hzpq⟩
    by_cases hcase : ((A \ {p, q}) ∩ D₁ᶜ).Nonempty
    · refine Or.inr (hends D₂ hpD.2 hqD.2 fun z hz => ?_)
      by_contra hzD2
      exact hnone (hconn _ _ (hD1.isArc.isClosed).isOpen_compl (hD2.isArc.isClosed).isOpen_compl
        hsub hcase ⟨z, hz, hzD2⟩)
    · refine Or.inl (hends D₁ hpD.1 hqD.1 fun z hz => ?_)
      by_contra hzD1
      exact hcase ⟨z, hz, hzD1⟩
  -- Both arcs cannot land on the same side: the other side would be just the two points.
  have hthird : ∀ D : Set Plane, IsArcBetween D p q → ¬ D ⊆ ({p, q} : Set Plane) := by
    intro D hDar hsub
    obtain ⟨-, z, hz⟩ := hDar.preconnected_diff
    exact hz.2 (hsub hz.1)
  have hnotboth : ∀ D D' : Set Plane, D ∪ D' = C → D ∩ D' = {p, q} → IsArcBetween D' p q →
      A₁ ⊆ D → A₂ ⊆ D → False := by
    intro D D' hDD hDDi hD'ar h1 h2
    refine hthird D' hD'ar ?_
    rw [← hDDi]
    intro z hz
    have hzC : z ∈ C := by rw [← hDD]; exact Or.inr hz
    rw [← hA] at hzC
    exact hzC.elim (fun h => ⟨h1 h, hz⟩) fun h => ⟨h2 h, hz⟩
  -- On opposite sides, the inclusions are equalities.
  have heq : ∀ X Y X' Y' : Set Plane, X ∪ Y = C → X' ∪ Y' = C → X' ∩ Y' = {p, q} →
      p ∈ X → q ∈ X → X ⊆ X' → Y ⊆ Y' → X = X' := by
    intro X Y X' Y' hXY hX'Y' hX'Y'i hpX hqX hXX hYY
    refine Set.Subset.antisymm hXX fun z hz => ?_
    have hzC : z ∈ C := by rw [← hX'Y']; exact Or.inl hz
    rw [← hXY] at hzC
    rcases hzC with h | h
    · exact h
    · have hzpq : z ∈ ({p, q} : Set Plane) := by rw [← hX'Y'i]; exact ⟨hz, hYY h⟩
      rcases hzpq with rfl | rfl
      exacts [hpX, hqX]
  have hAC₁ : A₁ ⊆ C := by rw [← hA]; exact Set.subset_union_left
  have hAC₂ : A₂ ⊆ C := by rw [← hA]; exact Set.subset_union_right
  rcases key A₁ hA1 hAC₁ with h1 | h1 <;> rcases key A₂ hA2 hAC₂ with h2 | h2
  · exact absurd (hnotboth D₁ D₂ hD hDi hD2 h1 h2) (by simp)
  · exact Or.inl ⟨heq A₁ A₂ D₁ D₂ hA hD hDi hpA.1 hqA.1 h1 h2,
      heq A₂ A₁ D₂ D₁ (by rw [Set.union_comm]; exact hA) (by rw [Set.union_comm]; exact hD)
        (by rw [Set.inter_comm]; exact hDi) hpA.2 hqA.2 h2 h1⟩
  · exact Or.inr ⟨heq A₁ A₂ D₂ D₁ hA (by rw [Set.union_comm]; exact hD)
      (by rw [Set.inter_comm]; exact hDi) hpA.1 hqA.1 h1 h2,
      heq A₂ A₁ D₁ D₂ (by rw [Set.union_comm]; exact hA) hD hDi hpA.2 hqA.2 h2 h1⟩
  · exact absurd (hnotboth D₂ D₁ (by rw [Set.union_comm]; exact hD)
      (by rw [Set.inter_comm]; exact hDi) hD1 h1 h2) (by simp)

/-- **The realization theorem, tracking a splitting.** A polygonal Jordan curve decomposed into
two arcs meeting at two of its corners is the carrier of a `ClosedPolygon` whose two arcs at the
corresponding vertices are those two arcs.

This is the form the plane-graph layer wants — compare `Graph.IsHexRealization`. The corner
hypothesis on the two cut points is not an artefact of the proof:
`ClosedPolygon.isCornerAt_vertex` says every vertex of a realization is a corner, so a cut point
that is *not* one cannot be a vertex of any realization at all. -/
theorem exists_closedPolygon_arcs {C A₁ A₂ : Set Plane} (hJ : IsJordanCurve C)
    (hP : IsPolygonal C) {p q : Plane} (hp : IsCornerAt C p) (hq : IsCornerAt C q) (hpq : p ≠ q)
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q) (hunion : A₁ ∪ A₂ = C)
    (hinter : A₁ ∩ A₂ = {p, q}) :
    ∃ (m : ℕ) (P : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ), P.carrier = C ∧
      1 ≤ k ∧ k ≤ m + 2 ∧ P.vertex a = p ∧ P.vertex (a + (k : ZMod (m + 3))) = q ∧
      ((P.arc a k = A₁ ∧ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = A₂) ∨
        (P.arc a k = A₂ ∧ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = A₁)) := by
  obtain ⟨m, P, a, k, hcar, hpa, hqa, hk1, hk2⟩ := exists_closedPolygon_split hJ hP hp hq hpq
  refine ⟨m, P, a, k, hcar, hk1, hk2, hpa, hqa, ?_⟩
  have hD1 : IsArcBetween (P.arc a k) p q := by
    rw [← hpa, ← hqa]; exact P.isArcBetween_arc a hk1 hk2
  have hD2 : IsArcBetween (P.arc (a + (k : ZMod (m + 3))) (m + 3 - k)) p q := by
    have h := P.isArcBetween_arc (a + (k : ZMod (m + 3))) (k := m + 3 - k) (by omega) (by omega)
    rw [zmod_add_sub_cancel (by omega) a] at h
    rw [← hpa, ← hqa]
    exact h.reverse
  have hDunion : P.arc a k ∪ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = C := by
    rw [P.arc_union a (by omega), hcar]
  have hDinter : P.arc a k ∩ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = {p, q} := by
    rw [P.arc_inter a hk1 hk2, hpa, hqa]
  rcases two_arcs_unique hunion hinter hDunion hDinter hA1 hA2 hD1 hD2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact Or.inl ⟨e1.symm, e2.symm⟩
  · exact Or.inr ⟨e2.symm, e1.symm⟩

/-- **The realization theorem, with the two arcs in the order they were given.** The same as
`Schoenflies.exists_closedPolygon_arcs` with the disjunction moved off the arcs and onto the two
cut vertices: reading the polygon from the other cut point exchanges the two arcs, so exactly
one of the two starting vertices makes `P.arc a k` the *first* arc. This is the shape
`Graph.IsHexRealization` asks for. -/
theorem exists_closedPolygon_arcs_ordered {C A₁ A₂ : Set Plane} (hJ : IsJordanCurve C)
    (hP : IsPolygonal C) {p q : Plane} (hp : IsCornerAt C p) (hq : IsCornerAt C q) (hpq : p ≠ q)
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q) (hunion : A₁ ∪ A₂ = C)
    (hinter : A₁ ∩ A₂ = {p, q}) :
    ∃ (m : ℕ) (P : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ), P.carrier = C ∧
      1 ≤ k ∧ k ≤ m + 2 ∧
      P.arc a k = A₁ ∧ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = A₂ ∧
      ((P.vertex a = p ∧ P.vertex (a + (k : ZMod (m + 3))) = q) ∨
        (P.vertex a = q ∧ P.vertex (a + (k : ZMod (m + 3))) = p)) := by
  obtain ⟨m, P, a, k, hcar, hk1, hk2, hpa, hqa, hcase⟩ :=
    exists_closedPolygon_arcs hJ hP hp hq hpq hA1 hA2 hunion hinter
  rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact ⟨m, P, a, k, hcar, hk1, hk2, e1, e2, Or.inl ⟨hpa, hqa⟩⟩
  · refine ⟨m, P, a + (k : ZMod (m + 3)), m + 3 - k, hcar, by omega, by omega, e2, ?_, ?_⟩
    · rw [zmod_add_sub_cancel (by omega) a, show m + 3 - (m + 3 - k) = k by omega]
      exact e1
    · rw [zmod_add_sub_cancel (by omega) a]
      exact Or.inr ⟨hqa, hpa⟩

end Schoenflies
