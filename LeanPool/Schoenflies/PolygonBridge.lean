/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Strip
public import LeanPool.Schoenflies.Parity
public import LeanPool.Schoenflies.Polygonal
public import LeanPool.Schoenflies.Concatenate

/-!
# The polygon bridge

Two independent representations of a closed polygon had grown up side by side and never met.
`Schoenflies/Strip.lean` carries `ClosedPolygon m`, a cyclic vertex list indexed by
`ZMod (m + 3)`, and everything the collar of Lemma 1.8 says is said about it.
`Schoenflies/Parity.lean` carries `List Piece` together with `IsClosedChain`, and everything
the crossing count of Lemma 2.1 and Lemma 2.2 says is said about *that*. Neither knew about
the other, and — worse — nothing anywhere produced a `ClosedPolygon`, so every theorem about
one was formally a theorem about a structure that might have been empty.

This module closes the three gaps.

## Non-vacuity

`Schoenflies.triangle` builds a `ClosedPolygon 0` out of any three points with nonzero
orientation determinant, and `Schoenflies.unitTriangle` is the concrete instance with vertices
`(0,0)`, `(1,0)`, `(0,1)`. The only real work is `edges_meet`: two edges of a triangle share
exactly one endpoint, and `Schoenflies.segment_inter_shared` says two segments meeting at an
endpoint whose far ends are off the shared line meet nowhere else. That lemma is proved by
taking the orientation form against the first segment's direction, which kills the first
segment's own parameter and forces the second's to vanish.

## The representation bridge

`ClosedPolygon.pieces` lists the `m + 3` edges as pairs of endpoints, in cyclic order.
It is a closed chain (`ClosedPolygon.isClosedChain_pieces`), every piece is nondegenerate
(`ClosedPolygon.pieces_nondeg`), and — the point of the exercise —
`ClosedPolygon.cover_pieces` says it occupies exactly the polygon's carrier. Closedness is a
telescoping sum: `Schoenflies.sum_range_boundary` evaluates the mod-`2` boundary of the chain
`0 → 1 → ⋯ → n` as the sum of its two ends, and the two ends of `0 → ⋯ → m + 3` are the same
vertex because `m + 3` is `0` in `ZMod (m + 3)`.

## The curve bridge

`ClosedPolygon.isJordanCurve_carrier` and `ClosedPolygon.isPolygonal_carrier` say the carrier
is a simple closed polygonal curve in the blueprint's sense, which is what the polygonal Jordan
curve theorem (Theorem 2.3) takes as its hypothesis. The loop is built by concatenating edge
parametrizations around the cycle: `ClosedPolygon.chain k` is the union of the edges leaving
vertices `0, …, k`, and `ClosedPolygon.isArcBetween_chain` grows it one edge at a time by
`IsArcBetween.concatenate`. The hypothesis that concatenation needs — the new edge meets what
came before only at the vertex they share — is exactly `edges_meet` twice over: once to place
the meeting point among the new edge's own two endpoints, and once more to rule out the far
one, which would otherwise let the polygon close early. The last edge closes the loop through
`IsJordanCurve.of_two_arcs`, and there the far endpoint is *not* ruled out: it is the second
shared point that makes the two arcs a curve rather than an arc.

## Both halves at once

The last section is what the bridge is for: the two statements of Lemma 2.2 — parity is
constant on a component of the complement, and it flips across an edge — restated for the
*carrier* of a `ClosedPolygon` rather than for the cover of an anonymous list. The flip needs
the edge list split around the edge being crossed, which is `List.append_of_mem` together with
`ClosedPolygon.pieces_nodup`; that the two remaining fragments miss the crossing point is
`edges_meet` a third time.

## Blueprint

* `Schoenflies.triangle`, `Schoenflies.unitTriangle` — witnesses that §1's "simple closed
  polygonal curve" is not vacuous.
* `ClosedPolygon.pieces`, `ClosedPolygon.cover_pieces`, `ClosedPolygon.isClosedChain_pieces` —
  the edge list the crossing count of §2 is defined on, and that it carries the polygon.
* `ClosedPolygon.isJordanCurve_carrier`, `ClosedPolygon.isPolygonal_carrier` — §1, "a simple
  closed polygonal curve"; jointly the hypothesis of Theorem 2.3.
* `ClosedPolygon.parity_eq_of_mem_connectedComponentIn_carrier`,
  `ClosedPolygon.parity_flip_carrier` — the two halves of Lemma 2.2, read off a
  `ClosedPolygon`. These are the statements Theorem 2.3 consumes.

One general lemma is stated here that does not belong here: `Schoenflies.exists_of_mem_cover`,
the destructor matching `Schoenflies.mem_cover`, whose home is `Schoenflies/Parity.lean`.
-/

@[expose] public section

open Metric Set

namespace Schoenflies

open Plane

variable {m : ℕ}

/-! ## Two segments that share an endpoint

The one piece of plane geometry this module needs. `Schoenflies/SegmentMeet.lean` describes
the intersection of two arbitrary segments; here the two are known to share an endpoint, and
the conclusion is sharper and the proof shorter. -/

/-- Two segments sharing the endpoint `b`, whose far ends are off the line through the other,
meet only at `b`. Taking the orientation form against `b - a` annihilates the first segment's
own parameter, so the second segment's parameter must vanish. -/
theorem segment_inter_shared {a b c : Plane} (h : det (b - a) (c - b) ≠ 0) :
    segment ℝ a b ∩ segment ℝ b c ⊆ {b} := by
  rintro z ⟨hz1, hz2⟩
  rw [segment_eq_image' ℝ a b] at hz1
  rw [segment_eq_image' ℝ b c] at hz2
  obtain ⟨s, -, hs⟩ := hz1
  obtain ⟨t, -, ht⟩ := hz2
  simp only at hs ht
  have hvec : t • (c - b) = (s - 1) • (b - a) := by
    have hz := ht.trans hs.symm
    linear_combination (norm := module) hz
  have key : t * det (b - a) (c - b) = 0 := by
    have h2 : det (b - a) (t • (c - b)) = det (b - a) ((s - 1) • (b - a)) := by rw [hvec]
    rw [det_smul_right, det_smul_right, det_self, mul_zero] at h2
    exact h2
  have ht0 : t = 0 := by
    rcases mul_eq_zero.1 key with h0 | h0
    · exact h0
    · exact absurd h0 h
  simp only [mem_singleton_iff]
  rw [← ht, ht0, zero_smul, add_zero]

/-! ## Non-vacuity: a triangle is a closed polygon

Nothing in the strip development ever built a `ClosedPolygon`, so `polygonal_collar` and every
theorem beside it was formally a theorem about a structure with no known inhabitant. A triangle
is the smallest witness, and no coordinates are needed: any three points with nonzero
orientation determinant will do. -/

section Triangle

variable {a b c : Plane}

/-- The orientation of a triple, read at its first corner and at its second, is the same. -/
private theorem det_rot₁ (a b c : Plane) : det (b - a) (c - b) = det (b - a) (c - a) := by
  simp only [Plane.det, Plane.sub_apply]; ring

/-- The same, one corner further round. -/
private theorem det_rot₂ (a b c : Plane) : det (c - b) (a - c) = det (b - a) (c - a) := by
  simp only [Plane.det, Plane.sub_apply]; ring

/-- And once more; the orientation form is invariant under cycling the triple. -/
private theorem det_rot₃ (a b c : Plane) : det (a - c) (b - a) = det (b - a) (c - a) := by
  simp only [Plane.det, Plane.sub_apply]; ring

/-- **A triangle is a simple closed polygon.** Any three points that are not collinear, taken
in that cyclic order. `edges_meet` holds because two of the three edges always share exactly
one endpoint, and `corner` because the orientation form is what nonzero says. -/
def triangle (h : det (b - a) (c - a) ≠ 0) : ClosedPolygon 0 where
  vertex := ![a, b, c]
  vertex_inj := by
    have hab : a ≠ b := by
      rintro rfl
      exact h (by simp [Plane.det])
    have hbc : b ≠ c := by
      rintro rfl
      exact h (det_self _)
    have hac : a ≠ c := by
      rintro rfl
      exact h (by simp [Plane.det])
    intro i j hij
    have hi : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
    rcases hi i with rfl | rfl | rfl <;> rcases hi j with rfl | rfl | rfl
    · rfl
    · exact absurd (show a = b from hij) hab
    · exact absurd (show a = c from hij) hac
    · exact absurd (show a = b from hij.symm) hab
    · rfl
    · exact absurd (show b = c from hij) hbc
    · exact absurd (show a = c from hij.symm) hac
    · exact absurd (show b = c from hij.symm) hbc
    · rfl
  edges_meet := by
    have mab : segment ℝ a b ∩ segment ℝ b c ⊆ {b} :=
      segment_inter_shared (by rw [det_rot₁]; exact h)
    have mbc : segment ℝ b c ∩ segment ℝ c a ⊆ {c} :=
      segment_inter_shared (by rw [det_rot₂]; exact h)
    have mca : segment ℝ c a ∩ segment ℝ a b ⊆ {a} :=
      segment_inter_shared (by rw [det_rot₃]; exact h)
    intro i j hij
    have hi : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
    rcases hi i with rfl | rfl | rfl <;> rcases hi j with rfl | rfl | rfl
    · exact absurd rfl hij
    · change segment ℝ a b ∩ segment ℝ b c ⊆ {a, b}
      exact subset_trans mab (by simp)
    · change segment ℝ a b ∩ segment ℝ c a ⊆ {a, b}
      rw [Set.inter_comm]
      exact subset_trans mca (by simp)
    · change segment ℝ b c ∩ segment ℝ a b ⊆ {b, c}
      rw [Set.inter_comm]
      exact subset_trans mab (by simp)
    · exact absurd rfl hij
    · change segment ℝ b c ∩ segment ℝ c a ⊆ {b, c}
      exact subset_trans mbc (by simp)
    · change segment ℝ c a ∩ segment ℝ a b ⊆ {c, a}
      exact subset_trans mca (by simp)
    · change segment ℝ c a ∩ segment ℝ b c ⊆ {c, a}
      rw [Set.inter_comm]
      exact subset_trans mbc (by simp)
    · exact absurd rfl hij
  corner := by
    intro i
    have hi : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
    rcases hi i with rfl | rfl | rfl
    · change det (c - a) (b - a) ≠ 0
      intro hc
      apply h
      simp only [Plane.det, Plane.sub_apply] at hc ⊢
      linarith
    · change det (a - b) (c - b) ≠ 0
      intro hc
      apply h
      simp only [Plane.det, Plane.sub_apply] at hc ⊢
      linarith
    · change det (b - c) (a - c) ≠ 0
      intro hc
      apply h
      simp only [Plane.det, Plane.sub_apply] at hc ⊢
      linarith

@[simp] theorem triangle_vertex_zero (h : det (b - a) (c - a) ≠ 0) :
    (triangle h).vertex 0 = a := rfl

@[simp] theorem triangle_vertex_one (h : det (b - a) (c - a) ≠ 0) :
    (triangle h).vertex 1 = b := rfl

@[simp] theorem triangle_vertex_two (h : det (b - a) (c - a) ≠ 0) :
    (triangle h).vertex 2 = c := rfl

end Triangle

/-- A concrete simple closed polygon: the triangle with vertices `(0,0)`, `(1,0)` and
`(0,1)`. -/
def unitTriangle : ClosedPolygon 0 :=
  triangle (a := mk 0 0) (b := mk 1 0) (c := mk 0 1)
    (by norm_num [Plane.det, Plane.sub_apply])

/-! ## A telescoping sum mod two -/

/-- The mod-`2` boundary of the chain `0 → 1 → ⋯ → n` is the sum of its two ends: every
interior vertex is counted twice. This is the whole content of "a cycle is a closed chain". -/
theorem sum_range_boundary (g : ℕ → ZMod 2) :
    ∀ n : ℕ, ((List.range n).map fun j => g j + g (j + 1)).sum = g 0 + g n
  | 0 => by simpa using (add_self_zmod_two (g 0)).symm
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_boundary g n]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    linear_combination add_self_zmod_two (g n)

namespace ClosedPolygon

/-! ## Natural-number indices

Both bridges run over the vertices with a natural number and cast into `ZMod (m + 3)`. Below
the modulus the cast is injective, which is what turns "these two indices are different
naturals" into "these are different edges" and back. -/

/-- Below the modulus, casting a natural number into `ZMod (m + 3)` is injective. -/
theorem natCast_inj {j k : ℕ} (hj : j < m + 3) (hk : k < m + 3)
    (h : (j : ZMod (m + 3)) = (k : ZMod (m + 3))) : j = k := by
  have hval := congrArg ZMod.val h
  rwa [ZMod.val_cast_of_lt hj, ZMod.val_cast_of_lt hk] at hval

/-- The successor, pushed through the cast. -/
theorem natCast_succ (j : ℕ) : ((j + 1 : ℕ) : ZMod (m + 3)) = (j : ZMod (m + 3)) + 1 := by
  push_cast; ring

variable {P : ClosedPolygon m}

/-- Distinct indices below the modulus name distinct vertices. -/
theorem vertex_natCast_ne {j k : ℕ} (hj : j < m + 3) (hk : k < m + 3) (hjk : j ≠ k) :
    P.vertex (j : ZMod (m + 3)) ≠ P.vertex (k : ZMod (m + 3)) :=
  fun heq => hjk (natCast_inj hj hk (P.vertex_inj heq))

/-- **An edge meets an earlier edge only at its own initial vertex.** `edges_meet` puts the
meeting point at one of the two ends of the later edge; the far end is ruled out by applying
`edges_meet` the other way round, which would put the later edge's *terminal* vertex on the
earlier edge and hence make it one of two vertices it cannot be. This is what stops the
polygon from closing before it has run through all its vertices. -/
theorem edge_meet_earlier {j k : ℕ} (hjk : j < k) (hk : k + 1 < m + 3) {z : Plane}
    (hzj : z ∈ P.edge (j : ZMod (m + 3))) (hzk : z ∈ P.edge (k : ZMod (m + 3))) :
    z = P.vertex (k : ZMod (m + 3)) := by
  have hjn : j < m + 3 := by omega
  have hkn : k < m + 3 := by omega
  have hne : (k : ZMod (m + 3)) ≠ (j : ZMod (m + 3)) :=
    fun heq => (by omega : k ≠ j) (natCast_inj hkn hjn heq)
  have hmem := P.edges_meet _ _ hne (Set.mem_inter hzk hzj)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hmem | hmem
  · exact hmem
  -- The far end: it would have to be one of the earlier edge's two ends as well.
  exfalso
  have hmem2 := P.edges_meet _ _ (Ne.symm hne) (Set.mem_inter hzj hzk)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem2
  rw [← natCast_succ] at hmem
  rcases hmem2 with hmem2 | hmem2
  · have : k + 1 = j := natCast_inj hk hjn (P.vertex_inj (hmem ▸ hmem2))
    omega
  · rw [← natCast_succ] at hmem2
    have : k + 1 = j + 1 := natCast_inj hk (by omega) (P.vertex_inj (hmem ▸ hmem2))
    omega

/-- **The last edge meets every earlier edge only at a vertex it shares with the cycle's ends.**
Here the far end is *not* excluded: the last edge runs back to vertex `0`, so both of its ends
are legitimate meeting points, and that is precisely what makes the carrier a closed curve
rather than an arc. -/
theorem edge_meet_last {j : ℕ} (hj : j < m + 2) {z : Plane}
    (hzj : z ∈ P.edge (j : ZMod (m + 3)))
    (hz : z ∈ P.edge ((m + 2 : ℕ) : ZMod (m + 3))) :
    z = P.vertex 0 ∨ z = P.vertex ((m + 2 : ℕ) : ZMod (m + 3)) := by
  have hne : ((m + 2 : ℕ) : ZMod (m + 3)) ≠ (j : ZMod (m + 3)) :=
    fun heq => (by omega : m + 2 ≠ j) (natCast_inj (by omega) (by omega) heq)
  have hlast : ((m + 2 : ℕ) : ZMod (m + 3)) + 1 = 0 := by
    rw [← natCast_succ]
    exact ZMod.natCast_self (m + 3)
  have hmem := P.edges_meet _ _ hne (Set.mem_inter hz hzj)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hmem | hmem
  · exact Or.inr hmem
  · rw [hlast] at hmem
    exact Or.inl hmem

/-! ## The representation bridge

`Schoenflies/Parity.lean` counts crossings of a `List Piece`; `ClosedPolygon.pieces` is the
list it should be handed. The four obligations below are exactly what every parity statement
asks for: a list, closedness, nondegeneracy, and — the one that carries the geometry — that
the list occupies the polygon. -/

/-- The `m + 3` edges of the polygon, as a list of pieces in cyclic order. This is the form
the crossing count of §2 is defined on. -/
def pieces (P : ClosedPolygon m) : List Piece :=
  (List.range (m + 3)).map fun j : ℕ =>
    (P.vertex (j : ZMod (m + 3)), P.vertex ((j : ZMod (m + 3)) + 1))

/-- Every edge of the polygon is on the list. -/
theorem mem_pieces (P : ClosedPolygon m) (i : ZMod (m + 3)) :
    (P.vertex i, P.vertex (i + 1)) ∈ P.pieces := by
  refine List.mem_map.2 ⟨i.val, List.mem_range.2 (ZMod.val_lt i), ?_⟩
  rw [ZMod.natCast_rightInverse i]

/-- Every piece on the list is an edge of the polygon. -/
theorem exists_of_mem_pieces {P : ClosedPolygon m} {Q : Piece} (hQ : Q ∈ P.pieces) :
    ∃ i : ZMod (m + 3), Q = (P.vertex i, P.vertex (i + 1)) := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hQ
  exact ⟨(j : ZMod (m + 3)), rfl⟩

/-- No edge of a simple closed polygon is degenerate: consecutive vertices are distinct. -/
theorem pieces_nondeg (P : ClosedPolygon m) : ∀ Q ∈ P.pieces, Q.Nondeg := by
  intro Q hQ
  obtain ⟨i, rfl⟩ := exists_of_mem_pieces hQ
  exact P.vertex_ne i

/-- **The edge list is a closed chain.** Each vertex is the terminal end of one edge and the
initial end of the next, so it is counted twice; the cycle closes because `m + 3` is `0` in
`ZMod (m + 3)`, which makes the two ends of the telescoping sum the same vertex. -/
theorem isClosedChain_pieces (P : ClosedPolygon m) : IsClosedChain P.pieces := by
  intro f
  have hmap : (P.pieces.map fun Q => f Q.1 + f Q.2)
      = (List.range (m + 3)).map fun j : ℕ =>
        f (P.vertex (j : ZMod (m + 3))) + f (P.vertex ((j + 1 : ℕ) : ZMod (m + 3))) := by
    rw [pieces, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply, natCast_succ]
  rw [hmap]
  have key := sum_range_boundary (fun k : ℕ => f (P.vertex (k : ZMod (m + 3)))) (m + 3)
  rw [key, Nat.cast_zero, ZMod.natCast_self]
  exact add_self_zmod_two _

/-- **The edge list carries the polygon.** Without this equation no parity statement says
anything about a `ClosedPolygon`: the crossing count is defined against `cover`, and the collar
against `carrier`. -/
theorem cover_pieces (P : ClosedPolygon m) : cover P.pieces = P.carrier := by
  apply Set.Subset.antisymm
  · rw [cover]
    refine Set.iUnion₂_subset fun Q hQ => ?_
    obtain ⟨i, rfl⟩ := exists_of_mem_pieces hQ
    exact Set.subset_iUnion (fun i => P.edge i) i
  · refine Set.iUnion_subset fun i => ?_
    exact fun z hz => mem_cover (P.mem_pieces i) hz

/-! ## The curve bridge

`chain k` is the union of the edges leaving vertices `0, …, k`. Each is an arc from vertex `0`
to vertex `k + 1`, obtained from its predecessor by `IsArcBetween.concatenate`; the whole
carrier is the last of them plus the edge that runs back to vertex `0`. -/

/-- The union of the edges leaving vertices `0, 1, …, k`. -/
def chain (P : ClosedPolygon m) : ℕ → Set Plane
  | 0 => P.edge 0
  | k + 1 => chain P k ∪ P.edge ((k + 1 : ℕ) : ZMod (m + 3))

theorem mem_chain_iff {z : Plane} {k : ℕ} :
    z ∈ P.chain k ↔ ∃ j ≤ k, z ∈ P.edge (j : ZMod (m + 3)) := by
  induction k with
  | zero =>
    constructor
    · intro hz
      exact ⟨0, le_rfl, by simpa [chain] using hz⟩
    · rintro ⟨j, hj, hzj⟩
      obtain rfl : j = 0 := Nat.le_zero.1 hj
      simpa [chain] using hzj
  | succ k ih =>
    simp only [chain, Set.mem_union]
    constructor
    · rintro (hz | hz)
      · obtain ⟨j, hj, hzj⟩ := ih.1 hz
        exact ⟨j, le_trans hj (Nat.le_succ k), hzj⟩
      · exact ⟨k + 1, le_rfl, hz⟩
    · rintro ⟨j, hj, hzj⟩
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · exact Or.inl (ih.2 ⟨j, Nat.lt_succ_iff.1 hlt, hzj⟩)
      · obtain rfl : j = k + 1 := le_antisymm hj hge
        exact Or.inr hzj

/-- Running through all `m + 3` edges exhausts the carrier. -/
theorem chain_eq_carrier (P : ClosedPolygon m) : P.chain (m + 2) = P.carrier := by
  ext z
  rw [mem_chain_iff]
  constructor
  · rintro ⟨j, -, hzj⟩
    exact Set.mem_iUnion.2 ⟨_, hzj⟩
  · intro hz
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.1 hz
    refine ⟨i.val, ?_, ?_⟩
    · have := ZMod.val_lt i
      omega
    · rwa [ZMod.natCast_rightInverse i]

/-- **The partial chains are arcs.** One edge at a time, glued at the vertex they share:
`edge_meet_earlier` is exactly the hypothesis `IsArcBetween.concatenate` asks for. The bound
`k + 1 < m + 3` is what keeps the growing arc from meeting its own start. -/
theorem isArcBetween_chain (P : ClosedPolygon m) :
    ∀ k : ℕ, k + 1 < m + 3 →
      IsArcBetween (P.chain k) (P.vertex 0) (P.vertex ((k + 1 : ℕ) : ZMod (m + 3))) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [natCast_succ]
    exact isArcBetween_segment (P.vertex_ne 0)
  | succ k ih =>
    intro hk
    have hA := ih (by omega)
    have hB : IsArcBetween (P.edge ((k + 1 : ℕ) : ZMod (m + 3)))
        (P.vertex ((k + 1 : ℕ) : ZMod (m + 3)))
        (P.vertex ((k + 1 + 1 : ℕ) : ZMod (m + 3))) := by
      rw [natCast_succ (k + 1)]
      exact isArcBetween_segment (P.vertex_ne _)
    have hmeet : ∀ z ∈ P.chain k, z ∈ P.edge ((k + 1 : ℕ) : ZMod (m + 3)) →
        z = P.vertex ((k + 1 : ℕ) : ZMod (m + 3)) := by
      intro z hz hze
      obtain ⟨j, hj, hzj⟩ := mem_chain_iff.1 hz
      exact edge_meet_earlier (by omega) (by omega) hzj hze
    exact hA.concatenate hB hmeet

/-- **The carrier of a simple closed polygon is a Jordan curve.** The arc through all but the
last edge, and the last edge running back to where it started, meet exactly at their two
shared endpoints. -/
theorem isJordanCurve_carrier (P : ClosedPolygon m) : IsJordanCurve P.carrier := by
  have hlast : ((m + 2 : ℕ) : ZMod (m + 3)) + 1 = 0 := by
    rw [← natCast_succ]
    exact ZMod.natCast_self (m + 3)
  have hA : IsArcBetween (P.chain (m + 1)) (P.vertex 0)
      (P.vertex ((m + 2 : ℕ) : ZMod (m + 3))) := P.isArcBetween_chain (m + 1) (by omega)
  have hedge : P.edge ((m + 2 : ℕ) : ZMod (m + 3))
      = segment ℝ (P.vertex ((m + 2 : ℕ) : ZMod (m + 3))) (P.vertex 0) := by
    rw [edge, hlast]
  have hB : IsArcBetween (P.edge ((m + 2 : ℕ) : ZMod (m + 3)))
      (P.vertex ((m + 2 : ℕ) : ZMod (m + 3))) (P.vertex 0) := by
    rw [hedge]
    refine isArcBetween_segment ?_
    rw [← hlast]
    exact P.vertex_ne _
  have hmeet : ∀ z ∈ P.chain (m + 1), z ∈ P.edge ((m + 2 : ℕ) : ZMod (m + 3)) →
      z = P.vertex 0 ∨ z = P.vertex ((m + 2 : ℕ) : ZMod (m + 3)) := by
    intro z hz hze
    obtain ⟨j, hj, hzj⟩ := mem_chain_iff.1 hz
    exact edge_meet_last (by omega) hzj hze
  have hcurve := IsJordanCurve.of_two_arcs hA hB hmeet
  have hsplit : P.chain (m + 2)
      = P.chain (m + 1) ∪ P.edge ((m + 2 : ℕ) : ZMod (m + 3)) := rfl
  rwa [← hsplit, chain_eq_carrier] at hcurve

/-! ### The carrier is polygonal

`IsPolygonal` asks for a vertex list whose `poly` carrier is the set. Cycling once round the
polygon and coming back to the first vertex is that list. -/

/-- The vertex list `v₀, v₁, …, v_{k+1}`, which walks the first `k + 1` edges. -/
def vlist (P : ClosedPolygon m) : ℕ → List Plane
  | 0 => [P.vertex 0, P.vertex ((1 : ℕ) : ZMod (m + 3))]
  | k + 1 => vlist P k ++ [P.vertex ((k + 1 + 1 : ℕ) : ZMod (m + 3))]

theorem vlist_ne_nil (P : ClosedPolygon m) (k : ℕ) : P.vlist k ≠ [] := by
  cases k <;> simp [vlist]

theorem getLast_vlist (P : ClosedPolygon m) (k : ℕ) :
    (P.vlist k).getLast (P.vlist_ne_nil k) = P.vertex ((k + 1 : ℕ) : ZMod (m + 3)) := by
  cases k with
  | zero => simp [vlist]
  | succ k => simp [vlist]

theorem poly_vlist (P : ClosedPolygon m) (k : ℕ) : poly (P.vlist k) = P.chain k := by
  induction k with
  | zero =>
    rw [vlist, poly_pair, chain, edge, natCast_succ]
    norm_num
  | succ k ih =>
    rw [vlist, poly_concat (P.vlist_ne_nil k), getLast_vlist, ih, chain, edge,
      natCast_succ (k + 1)]

/-- **The carrier of a simple closed polygon is polygonal**: it is the carrier of the vertex
list that runs once round the cycle and back to its first vertex. -/
theorem isPolygonal_carrier (P : ClosedPolygon m) : IsPolygonal P.carrier :=
  ⟨P.vlist (m + 2), by rw [poly_vlist, chain_eq_carrier]⟩

/-! ## The bridge in use

With both halves in place a parity statement can be read off a `ClosedPolygon` directly. -/

/-- A ray direction level for no edge of the polygon; the blueprint's "rotate the coordinate
system so that no edge is horizontal", with nothing rotated. -/
theorem exists_direction_pieces (P : ClosedPolygon m) :
    ∃ u : Plane, Plane.IsDirection u ∧ ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2 :=
  exists_direction_hgt_ne P.pieces P.pieces_nondeg

/-- **Crossing parity for a closed polygon** (Lemma 2.2): `π_C` is constant on the component
of the complement of the *carrier* containing a given point. -/
theorem parity_eq_of_mem_connectedComponentIn_carrier (P : ClosedPolygon m) {u : Plane}
    (hu : Plane.IsDirection u) (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∉ P.carrier) (hy : y ∈ connectedComponentIn P.carrierᶜ x) :
    parity u P.pieces y = parity u P.pieces x := by
  rw [← P.cover_pieces] at hx hy
  exact parity_eq_of_mem_connectedComponentIn hu hL P.isClosedChain_pieces hx hy

/-! ### The flip across an edge

The second half of Lemma 2.2 is stated for the edge list split around the edge being crossed,
`L₁ ++ (a, b) :: L₂`. Splitting is `List.append_of_mem`; what has to be checked is that the two
remaining fragments miss the point being crossed, and that is `edges_meet` again — another edge
can reach an interior point of this one only at one of this one's two ends, which an interior
point is not. -/

/-- What a list of pieces occupies, taken apart. The counterpart of `Schoenflies.mem_cover`,
which only builds; **this belongs next to it in `Schoenflies/Parity.lean`.** -/
theorem exists_of_mem_cover {L : List Piece} {z : Plane} (hz : z ∈ cover L) :
    ∃ R ∈ L, z ∈ R.seg := by
  rw [cover] at hz
  simpa using hz

/-- An interior point of one edge lies on no other edge: `edges_meet` puts any other edge's
meeting point at an end of this one, and an interior point is neither end. -/
theorem notMem_edge_of_mem_openSegment {i j : ZMod (m + 3)} (hij : j ≠ i) {p : Plane}
    (hp : p ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1))) : p ∉ P.edge j := by
  intro hpj
  have hmem := P.edges_meet i j (Ne.symm hij)
    (Set.mem_inter (openSegment_subset_segment ℝ _ _ hp) hpj)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with rfl | rfl
  · exact P.vertex_ne i (left_mem_openSegment_iff.1 hp)
  · exact P.vertex_ne i (right_mem_openSegment_iff.1 hp)

/-- The edge list has no repeated entry: distinct indices name distinct initial vertices. -/
theorem pieces_nodup (P : ClosedPolygon m) : P.pieces.Nodup := by
  rw [pieces]
  refine List.Nodup.map_on (fun j hj k hk heq => ?_) List.nodup_range
  exact natCast_inj (List.mem_range.1 hj) (List.mem_range.1 hk)
    (P.vertex_inj (congrArg Prod.fst heq))

/-- **Opposite sides of an edge, for a closed polygon** (Lemma 2.2, second half). Just before
and just after an interior point of an edge, in the ray direction, the base point is off the
carrier and the crossing parity differs by one. -/
theorem parity_flip_carrier (P : ClosedPolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) (i : ZMod (m + 3)) {p : Plane}
    (hp : p ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1))) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      p - t • u ∉ P.carrier ∧ p + t • u ∉ P.carrier ∧
        parity u P.pieces (p - t • u) = parity u P.pieces (p + t • u) + 1 := by
  obtain ⟨L₁, L₂, hsplit⟩ := List.append_of_mem (P.mem_pieces i)
  -- the edge being crossed occurs only once, so it is on neither fragment
  have hnodup := P.pieces_nodup
  rw [hsplit, List.nodup_append] at hnodup
  obtain ⟨-, hnd2, hdisj⟩ := hnodup
  have hQ₁ : (P.vertex i, P.vertex (i + 1)) ∉ L₁ := fun hmem => hdisj _ hmem _ (by simp) rfl
  have hQ₂ : (P.vertex i, P.vertex (i + 1)) ∉ L₂ := (List.nodup_cons.1 hnd2).1
  have hmiss : ∀ R ∈ L₁ ++ L₂, p ∉ Piece.seg R := by
    intro R hR
    have hRne : R ≠ (P.vertex i, P.vertex (i + 1)) := by
      rcases List.mem_append.1 hR with h | h
      · exact fun heq => hQ₁ (heq ▸ h)
      · exact fun heq => hQ₂ (heq ▸ h)
    have hRmem : R ∈ P.pieces := by
      rw [hsplit]
      rcases List.mem_append.1 hR with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    obtain ⟨j, rfl⟩ := exists_of_mem_pieces hRmem
    exact notMem_edge_of_mem_openSegment (fun heq => hRne (by rw [heq])) hp
  have h1 : p ∉ cover L₁ := by
    intro hmem
    obtain ⟨R, hR, hpR⟩ := exists_of_mem_cover hmem
    exact hmiss R (List.mem_append_left _ hR) hpR
  have h2 : p ∉ cover L₂ := by
    intro hmem
    obtain ⟨R, hR, hpR⟩ := exists_of_mem_cover hmem
    exact hmiss R (List.mem_append_right _ hR) hpR
  have hL' : ∀ R ∈ L₁ ++ (P.vertex i, P.vertex (i + 1)) :: L₂, hgt u R.1 ≠ hgt u R.2 := by
    rw [← hsplit]; exact hL
  obtain ⟨δ, hδ, hmain⟩ := parity_flip hu hL' hp h1 h2
  refine ⟨δ, hδ, fun t ht htδ => ?_⟩
  obtain ⟨ha, hb, hc⟩ := hmain t ht htδ
  rw [← hsplit] at ha hb hc
  rw [P.cover_pieces] at ha hb
  exact ⟨ha, hb, hc⟩

end ClosedPolygon

end Schoenflies
