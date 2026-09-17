/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.PrePolygonSep

/-!
# The arcs of a `PrePolygon`, and inserting a vertex

`Schoenflies.PrePolygon` is `Schoenflies.ClosedPolygon` without the `corner` field, so its
vertices may sit anywhere on the curve. This module carries §1 and §2 of the blueprint for such
a presentation: the edge list of an arc, the arc as a set, the two arcs of a splitting, and the
construction that makes the whole thing worth having — a prescribed point of the curve can be
made a vertex.

Everything below is the `Schoenflies.ClosedPolygon` development of
`Schoenflies/PolygonBridge.lean`, `Schoenflies/ParitySplitting.lean`,
`Schoenflies/PolygonalCrosscut.lean` and `Schoenflies/Realization.lean` with the structure
changed; every proof uses only `vertex_inj` and `edges_meet`, and `corner` is never mentioned.

## Why this module exists

`Schoenflies/Graph/K33Land.lean` and `Schoenflies/FaceCyclesLand.lean` each needed the same
apparatus and each transcribed it, the second under an `FC` suffix. The two copies were not
alpha-equivalent — `insertLast` in particular carried an extra hypothesis in one of them — so
the import checker never complained, and there were two of everything. This module is the
single copy; both consumers import it.

The one signature that genuinely differed is `Schoenflies.PrePolygon.insertLast`. The
`FaceCyclesLand` copy took, besides `hz : z ∈ openSegment ℝ (P.vertex (-1)) (P.vertex 0)`, a
hypothesis `∀ j, P.vertex j ≠ z` saying the new point is not already a vertex. That is not an
extra assumption but a consequence: `Schoenflies.PrePolygon.vertex_ne_of_mem_openSegment`
derives it from `hz`. The general form — the one with `hz` alone — is what survives here.

## Inserting a vertex, and why it is the crux

`Schoenflies.PrePolygon.deleteLast` removes a vertex at which the curve runs straight (the
blueprint's Lemma 1.8); `Schoenflies.PrePolygon.insertLast` is the inverse move, and it is the
reason `PrePolygon` is the right structure for a consumer that needs named points to be
vertices. The vertex is inserted at the end of the list, interior to the last edge, so that the
only edge that changes is the last one, which splits in two;
`Schoenflies.PrePolygon.rotate` brings any edge there. Simplicity survives because the far end
of the split edge lies on neither half.

## Blueprint

* `Schoenflies.PrePolygon.vertex_natCast_ne`, `…edge_meet_earlier` — the elementary simplicity
  facts, §1.
* `Schoenflies.PrePolygon.chain`, `…mem_chain_iff`, `…isArcBetween_chain` — the union of the
  first `k` edges, and that it is an arc.
* `Schoenflies.PrePolygon.arcPieces`, `…arcPieces_add`, `…arcPieces_full`,
  `…isChainFrom_arcPieces`, `…arcPieces_split_perm`, `…sameEdges_arcPieces_split`,
  `…parity_splitting` — the edge list of an arc, and Lemma 2.7 for it.
* `Schoenflies.PrePolygon.arc`, `…arc_union`, `…arc_inter`, `…isArcBetween_arc`,
  `…arc_not_subset_endpoints`, `…isCompact_arc` — the two arcs of a splitting, §2.
* `Schoenflies.PrePolygon.parity_ne_iff_mem_farRegion` — `thm:polygonal-jordan` read as a
  separation criterion.
* `Schoenflies.PrePolygon.arcList`, `…poly_arcList`, `…isPolygonal_arc` — an arc as a polyline,
  which is how it is glued to a crosscut.
* `Schoenflies.segment_halves_inter`, `Schoenflies.right_notMem_left_half`,
  `Schoenflies.left_notMem_right_half` — §1: cutting a segment at an interior point, in order.
  General-purpose; they belong beside `Schoenflies.segment_split` in `Schoenflies/SegmentCut.lean`.
* `Schoenflies.PrePolygon.insertLast`, `…carrier_insertLast`,
  `Schoenflies.PrePolygon.exists_prePolygon_insert`, `…exists_prePolygon_vertices` — the inverse
  of the blueprint's "delete redundant vertices" (Lemma 1.8): *insert* one, anywhere on the curve.
* `Schoenflies.exists_prePolygon_points`, `…exists_prePolygon_split` — §1, the realization
  theorem **with the cut points anywhere on the curve**. Compare
  `Schoenflies.exists_closedPolygon_split`, which requires them to be corners.
-/

open Bornology Metric Set

namespace Schoenflies

open Plane

namespace PrePolygon

variable {m : ℕ} {P : PrePolygon m} {a : ZMod (m + 3)} {k : ℕ} {u : Plane}

/-! ## Indices, edges and the elementary simplicity facts

Verbatim the `Schoenflies.ClosedPolygon` facts of `Schoenflies/PolygonBridge.lean` whose proofs
use only `vertex_inj` and `edges_meet`. -/

/-- Distinct indices below the modulus name distinct vertices. -/
theorem vertex_natCast_ne {j l : ℕ} (hj : j < m + 3) (hl : l < m + 3) (hjl : j ≠ l) :
    P.vertex (j : ZMod (m + 3)) ≠ P.vertex (l : ZMod (m + 3)) :=
  fun heq => hjl (ClosedPolygon.natCast_inj hj hl (P.vertex_inj heq))

/-- **An edge meets an earlier edge only at its own initial vertex.** -/
theorem edge_meet_earlier {j l : ℕ} (hjl : j < l) (hl : l + 1 < m + 3) {z : Plane}
    (hzj : z ∈ P.edge (j : ZMod (m + 3))) (hzl : z ∈ P.edge (l : ZMod (m + 3))) :
    z = P.vertex (l : ZMod (m + 3)) := by
  have hjn : j < m + 3 := by omega
  have hln : l < m + 3 := by omega
  have hne : (l : ZMod (m + 3)) ≠ (j : ZMod (m + 3)) :=
    fun heq => (by omega : l ≠ j) (ClosedPolygon.natCast_inj hln hjn heq)
  have hmem := P.edges_meet _ _ hne (Set.mem_inter hzl hzj)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hmem | hmem
  · exact hmem
  exfalso
  have hmem2 := P.edges_meet _ _ (Ne.symm hne) (Set.mem_inter hzj hzl)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem2
  rw [← ClosedPolygon.natCast_succ] at hmem
  rcases hmem2 with hmem2 | hmem2
  · have : l + 1 = j := ClosedPolygon.natCast_inj hl hjn (P.vertex_inj (hmem ▸ hmem2))
    omega
  · rw [← ClosedPolygon.natCast_succ] at hmem2
    have : l + 1 = j + 1 :=
      ClosedPolygon.natCast_inj hl (by omega) (P.vertex_inj (hmem ▸ hmem2))
    omega

/-! ## The chain of the first `k` edges, and that it is an arc -/

/-- The union of the edges leaving vertices `0, 1, …, k`. -/
def chain (P : PrePolygon m) : ℕ → Set Plane
  | 0 => P.edge 0
  | k + 1 => chain P k ∪ P.edge ((k + 1 : ℕ) : ZMod (m + 3))

theorem mem_chain_iff {z : Plane} : z ∈ P.chain k ↔ ∃ j ≤ k, z ∈ P.edge (j : ZMod (m + 3)) := by
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

/-- **The partial chains are arcs.** One edge at a time, glued at the vertex they share. -/
theorem isArcBetween_chain (P : PrePolygon m) :
    ∀ k : ℕ, k + 1 < m + 3 →
      IsArcBetween (P.chain k) (P.vertex 0) (P.vertex ((k + 1 : ℕ) : ZMod (m + 3))) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [ClosedPolygon.natCast_succ]
    exact isArcBetween_segment (vertex_ne_succ 0)
  | succ k ih =>
    intro hk
    have hA := ih (by omega)
    have hB : IsArcBetween (P.edge ((k + 1 : ℕ) : ZMod (m + 3)))
        (P.vertex ((k + 1 : ℕ) : ZMod (m + 3)))
        (P.vertex ((k + 1 + 1 : ℕ) : ZMod (m + 3))) := by
      rw [ClosedPolygon.natCast_succ (k + 1)]
      exact isArcBetween_segment (vertex_ne_succ _)
    have hmeet : ∀ z ∈ P.chain k, z ∈ P.edge ((k + 1 : ℕ) : ZMod (m + 3)) →
        z = P.vertex ((k + 1 : ℕ) : ZMod (m + 3)) := by
      intro z hz hze
      obtain ⟨j, hj, hzj⟩ := mem_chain_iff.1 hz
      exact edge_meet_earlier (by omega) (by omega) hzj hze
    exact hA.concatenate hB hmeet

/-! ## The edge list of an arc

`Schoenflies.ClosedPolygon.arcPieces` with the structure changed; every proof below uses only
`vertex_inj` and `edges_meet`, so it is the old proof verbatim. -/

/-- The edge list of the arc of `P` that leaves vertex `a` and runs forward through `k` edges. -/
def arcPieces (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) : List Piece :=
  (List.range k).map fun t : ℕ => (P.vertex (a + t), P.vertex (a + t + 1))

/-- Forgetting the `corner` field does not change the edge list of an arc. -/
@[simp] theorem arcPieces_toPre (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    C.toPre.arcPieces a k = C.arcPieces a k := rfl

@[simp] theorem arcPieces_zero (P : PrePolygon m) (a : ZMod (m + 3)) : P.arcPieces a 0 = [] := rfl

/-- Running through `k + l` edges is running through `k` and then through `l`. -/
theorem arcPieces_add (P : PrePolygon m) (a : ZMod (m + 3)) (k l : ℕ) :
    P.arcPieces a (k + l) = P.arcPieces a k ++ P.arcPieces (a + k) l := by
  rw [arcPieces, arcPieces, arcPieces, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply, Nat.cast_add, ← add_assoc]

/-- Running through all `m + 3` edges from vertex `0` is the whole edge list. -/
theorem arcPieces_full (P : PrePolygon m) : P.arcPieces 0 (m + 3) = P.pieces := by
  rw [arcPieces, pieces]
  exact List.map_congr_left fun t _ => by rw [zero_add]

/-- Every edge of an arc is an edge of the polygon. -/
theorem mem_pieces_of_mem_arcPieces {Q : Piece} (hQ : Q ∈ P.arcPieces a k) : Q ∈ P.pieces := by
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hQ
  exact P.mem_pieces _

theorem arcPieces_nondeg (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    ∀ Q ∈ P.arcPieces a k, Q.Nondeg :=
  fun _ hQ => P.pieces_nondeg _ (mem_pieces_of_mem_arcPieces hQ)

theorem arcPieces_hgt_ne (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) :
    ∀ Q ∈ P.arcPieces a k, hgt u Q.1 ≠ hgt u Q.2 :=
  fun _ hQ => hL _ (mem_pieces_of_mem_arcPieces hQ)

/-- **An arc is a chain from its first vertex to its last.** -/
theorem isChainFrom_arcPieces (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    IsChainFrom (P.arcPieces a k) (P.vertex a) (P.vertex (a + k)) := by
  intro f
  have hmap : ((P.arcPieces a k).map fun Q => f Q.1 + f Q.2)
      = (List.range k).map fun j : ℕ =>
          f (P.vertex (a + (j : ZMod (m + 3))))
            + f (P.vertex (a + ((j + 1 : ℕ) : ZMod (m + 3)))) := by
    rw [arcPieces, List.map_map]
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, ClosedPolygon.natCast_succ, ← add_assoc]
  have key := sum_range_boundary (fun i : ℕ => f (P.vertex (a + (i : ZMod (m + 3))))) k
  rw [hmap, key]
  simp

/-- **The two arcs from a vertex use every edge exactly once.** -/
theorem arcPieces_full_perm (P : PrePolygon m) (a : ZMod (m + 3)) :
    (P.arcPieces a (m + 3)).Perm P.pieces := by
  have hlt : a.val < m + 3 := ZMod.val_lt a
  have hcast : ((a.val : ℕ) : ZMod (m + 3)) = a := ZMod.natCast_rightInverse a
  have hzero : a + ((m + 3 - a.val : ℕ) : ZMod (m + 3)) = 0 := by
    rw [Nat.cast_sub hlt.le, hcast]
    simp
  have hsplit1 : P.arcPieces a (m + 3)
      = P.arcPieces a (m + 3 - a.val) ++ P.arcPieces 0 a.val := by
    have h1 : (m + 3 - a.val) + a.val = m + 3 := by omega
    have h2 := arcPieces_add P a (m + 3 - a.val) a.val
    rwa [h1, hzero] at h2
  have hsplit2 : P.pieces = P.arcPieces 0 a.val ++ P.arcPieces a (m + 3 - a.val) := by
    have h1 : a.val + (m + 3 - a.val) = m + 3 := by omega
    have h2 := arcPieces_add P 0 a.val (m + 3 - a.val)
    rw [h1, arcPieces_full, zero_add, hcast] at h2
    exact h2
  rw [hsplit1, hsplit2]
  exact List.perm_append_comm

/-- **The split.** For `k ≤ m + 3` the two arcs at `a` and `a + k` between them use every edge
of `P` exactly once. -/
theorem arcPieces_split_perm (P : PrePolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    (P.arcPieces a k ++ P.arcPieces (a + k) (m + 3 - k)).Perm P.pieces := by
  rw [← arcPieces_add, Nat.add_sub_cancel' hk]
  exact arcPieces_full_perm P a

theorem sameEdges_arcPieces_split (P : PrePolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    SameEdges P.pieces (P.arcPieces a k ++ P.arcPieces (a + k) (m + 3 - k)) :=
  SameEdges.of_perm (arcPieces_split_perm P a hk).symm

/-- The two arcs between them carry the polygon. -/
theorem cover_arcPieces_union (P : PrePolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    cover (P.arcPieces a k) ∪ cover (P.arcPieces (a + k) (m + 3 - k)) = P.carrier := by
  rw [← cover_append, cover_perm (arcPieces_split_perm P a hk), cover_pieces]

theorem cover_arcPieces_subset (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    cover (P.arcPieces a k) ⊆ P.carrier := by
  intro z hz
  obtain ⟨R, hR, hzR⟩ := ClosedPolygon.exists_of_mem_cover hz
  rw [← cover_pieces]
  exact mem_cover (mem_pieces_of_mem_arcPieces hR) hzR

theorem arcPieces_append_hgt_ne {K : List Piece}
    (hC : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) (hK : ∀ Q ∈ K, hgt u Q.1 ≠ hgt u Q.2) :
    ∀ Q ∈ P.arcPieces a k ++ K, hgt u Q.1 ≠ hgt u Q.2 :=
  hgt_ne_append (arcPieces_hgt_ne hC) hK

/-- **A curve of the split occupies its arc together with the crosscut.** -/
theorem carrier_eq_of_sameEdges {m' : ℕ} {J : PrePolygon m'} {K : List Piece}
    (h : SameEdges J.pieces (P.arcPieces a k ++ K)) :
    J.carrier = cover (P.arcPieces a k) ∪ cover K := by
  rw [← cover_pieces, h.cover_eq, cover_append]

/-- A point off `P` and off the crosscut is off `J`. -/
theorem notMem_carrier_of_sameEdges {m' : ℕ} {J : PrePolygon m'} {K : List Piece}
    (h : SameEdges J.pieces (P.arcPieces a k ++ K)) {x : Plane} (hxC : x ∉ P.carrier)
    (hxK : x ∉ cover K) : x ∉ J.carrier := by
  rw [carrier_eq_of_sameEdges h]
  rintro (hx | hx)
  · exact hxC (cover_arcPieces_subset P a k hx)
  · exact hxK hx

/-- **Parity splitting** (Lemma 2.7) for a polygon presented with redundant vertices. -/
theorem parity_splitting (P : PrePolygon m) (u : Plane) (a : ZMod (m + 3)) (hk : k ≤ m + 3)
    {L₁ L₂ K : List Piece} (h₁ : SameEdges L₁ (P.arcPieces a k ++ K))
    (h₂ : SameEdges L₂ (P.arcPieces (a + k) (m + 3 - k) ++ K)) (q : Plane) :
    parity u L₁ q + parity u L₂ q = parity u P.pieces q :=
  parity_split u (sameEdges_arcPieces_split P a hk) h₁ h₂ q

/-! ## The arcs as sets -/

/-- The arc of `P` that leaves vertex `a` and runs forward through `k` edges, as a set. -/
def arc (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) : Set Plane := cover (P.arcPieces a k)

@[simp] theorem arc_toPre (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    C.toPre.arc a k = C.arc a k := rfl

theorem arc_subset_carrier (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    P.arc a k ⊆ P.carrier := cover_arcPieces_subset P a k

theorem arc_union (P : PrePolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    P.arc a k ∪ P.arc (a + k) (m + 3 - k) = P.carrier := cover_arcPieces_union P a hk

/-- An arc is compact: it is a finite union of segments. -/
theorem isCompact_arc (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) : IsCompact (P.arc a k) :=
  isCompact_cover _

theorem mem_arc_iff {z : Plane} :
    z ∈ P.arc a k ↔ ∃ t < k, z ∈ P.edge (a + (t : ZMod (m + 3))) := by
  constructor
  · intro hz
    obtain ⟨R, hR, hzR⟩ := ClosedPolygon.exists_of_mem_cover hz
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hR
    exact ⟨t, List.mem_range.1 ht, hzR⟩
  · rintro ⟨t, ht, hz⟩
    exact mem_cover (List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩) hz

/-- The first vertex of a nonempty arc lies on it. -/
theorem vertex_mem_arc (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    P.vertex a ∈ P.arc a k := by
  refine mem_arc_iff.2 ⟨0, hk, ?_⟩
  rw [Nat.cast_zero, add_zero, edge]
  exact left_mem_segment ℝ _ _

/-- The last vertex of a nonempty arc lies on it. -/
theorem vertex_add_mem_arc (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    P.vertex (a + k) ∈ P.arc a k := by
  have hlast : a + ((k - 1 : ℕ) : ZMod (m + 3)) + 1 = a + (k : ZMod (m + 3)) := by
    have h : ((k - 1 : ℕ) : ZMod (m + 3)) + 1 = ((k : ℕ) : ZMod (m + 3)) := by
      rw [show ((k : ℕ) : ZMod (m + 3)) = (((k - 1) + 1 : ℕ) : ZMod (m + 3)) by
        congr 1; omega, Nat.cast_add, Nat.cast_one]
    rw [add_assoc, h]
  refine mem_arc_iff.2 ⟨k - 1, by omega, ?_⟩
  rw [edge, hlast]
  exact right_mem_segment ℝ _ _

/-- **The two cut vertices lie on both arcs.** -/
theorem endpoints_subset_arc (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    ({P.vertex a, P.vertex (a + k)} : Set Plane) ⊆ P.arc a k := by
  rintro w (rfl | rfl)
  · exact P.vertex_mem_arc a hk
  · exact P.vertex_add_mem_arc a hk

theorem endpoints_subset_arc' (P : PrePolygon m) (a : ZMod (m + 3)) (hk2 : k ≤ m + 2) :
    ({P.vertex a, P.vertex (a + k)} : Set Plane) ⊆ P.arc (a + k) (m + 3 - k) := by
  have hpos : 1 ≤ m + 3 - k := by omega
  have hwrap := zmod_add_sub_cancel (k := k) (by omega) a
  rintro w (rfl | rfl)
  · have hm := P.vertex_add_mem_arc (a + k) hpos
    rwa [hwrap] at hm
  · exact P.vertex_mem_arc (a + k) hpos

/-- Distinct index numerals below the modulus name distinct vertices, after any shift. -/
theorem natCast_shift_inj (P : PrePolygon m) (a : ZMod (m + 3)) {x z : ℕ} (hx : x < m + 3)
    (hz : z < m + 3) (he : P.vertex (a + (x : ZMod (m + 3))) = P.vertex (a + (z : ZMod (m + 3)))) :
    x = z :=
  ClosedPolygon.natCast_inj hx hz (add_left_cancel (P.vertex_inj he))

/-- An arc of `P` is a chain of the polygon read from its first vertex. -/
theorem arc_eq_chain (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    P.arc a k = (P.rotate a).chain (k - 1) := by
  have hedge : ∀ j : ZMod (m + 3), (P.rotate a).edge j = P.edge (a + j) := by
    intro j
    rw [edge, edge, rotate_vertex, rotate_vertex, show a + (j + 1) = a + j + 1 by ring]
  ext z
  rw [mem_arc_iff, mem_chain_iff]
  constructor
  · rintro ⟨t, ht, hz⟩
    exact ⟨t, by omega, by rw [hedge]; exact hz⟩
  · rintro ⟨j, hj, hz⟩
    rw [hedge] at hz
    exact ⟨j, by omega, hz⟩

/-- **An arc of a splitting is an arc between the two cut vertices.** -/
theorem isArcBetween_arc (P : PrePolygon m) (a : ZMod (m + 3)) (hk1 : 1 ≤ k)
    (hk2 : k ≤ m + 2) : IsArcBetween (P.arc a k) (P.vertex a) (P.vertex (a + k)) := by
  have h := (P.rotate a).isArcBetween_chain (k - 1) (by omega)
  rw [← arc_eq_chain P a hk1, show ((k - 1 + 1 : ℕ) : ZMod (m + 3)) = (k : ZMod (m + 3)) by
    congr 1; omega] at h
  simpa using h

/-- **The two arcs of a splitting meet exactly at the two cut vertices.** -/
theorem arc_inter (P : PrePolygon m) (a : ZMod (m + 3)) (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2) :
    P.arc a k ∩ P.arc (a + k) (m + 3 - k) = {P.vertex a, P.vertex (a + k)} := by
  refine Set.Subset.antisymm ?_ (Set.subset_inter (P.endpoints_subset_arc a hk1)
    (P.endpoints_subset_arc' a hk2))
  rintro z ⟨hz1, hz2⟩
  obtain ⟨s, hs, hzs⟩ := mem_arc_iff.1 hz1
  obtain ⟨t, ht, hzt⟩ := mem_arc_iff.1 hz2
  have hkt : k + t < m + 3 := by omega
  rw [show a + (k : ZMod (m + 3)) + (t : ZMod (m + 3)) = a + ((k + t : ℕ) : ZMod (m + 3)) by
    push_cast; ring] at hzt
  have hij : a + (s : ZMod (m + 3)) ≠ a + ((k + t : ℕ) : ZMod (m + 3)) := fun he =>
    absurd (ClosedPolygon.natCast_inj (by omega) hkt (add_left_cancel he)) (by omega)
  have hsucc₁ : a + (s : ZMod (m + 3)) + 1 = a + ((s + 1 : ℕ) : ZMod (m + 3)) := by
    push_cast; ring
  have hsucc₂ : a + ((k + t : ℕ) : ZMod (m + 3)) + 1 = a + ((k + t + 1 : ℕ) : ZMod (m + 3)) := by
    push_cast; ring
  have hA := P.edges_meet _ _ hij (Set.mem_inter hzs hzt)
  have hB := P.edges_meet _ _ (Ne.symm hij) (Set.mem_inter hzt hzs)
  rw [hsucc₁] at hA
  rw [hsucc₂] at hB
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB ⊢
  have hzero : k + t + 1 = m + 3 →
      ((k + t + 1 : ℕ) : ZMod (m + 3)) = ((0 : ℕ) : ZMod (m + 3)) := by
    intro he
    rw [he, Nat.cast_zero, ZMod.natCast_self]
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact absurd (hA.symm.trans hB) fun he => hij (P.vertex_inj he)
  · rcases Nat.lt_or_ge (k + t + 1) (m + 3) with hlt | hge
    · exact absurd (P.natCast_shift_inj a (by omega) hlt (hA.symm.trans hB)) (by omega)
    · have he : k + t + 1 = m + 3 := by omega
      have hs0 : s = 0 := P.natCast_shift_inj a (by omega) (by omega)
        ((hA.symm.trans hB).trans (by rw [hzero he]))
      exact Or.inl (by rw [hA, hs0, Nat.cast_zero, add_zero])
  · have hst : s + 1 = k + t := P.natCast_shift_inj a (by omega) hkt (hA.symm.trans hB)
    exact Or.inr (by rw [hA, show s + 1 = k by omega])
  · exfalso
    rcases Nat.lt_or_ge (k + t + 1) (m + 3) with hlt | hge
    · exact absurd (P.natCast_shift_inj a (by omega) hlt (hA.symm.trans hB)) (by omega)
    · have he : k + t + 1 = m + 3 := by omega
      have := P.natCast_shift_inj a (show s + 1 < m + 3 by omega) (show 0 < m + 3 by omega)
        ((hA.symm.trans hB).trans (by rw [hzero he]))
      omega

/-- An interior point of the first edge of an arc: a point of the arc that is neither cut
vertex, which is what says the arc is more than its two ends. -/
theorem arc_not_subset_endpoints (P : PrePolygon m) (a : ZMod (m + 3)) (hk1 : 1 ≤ k)
    (hk2 : k ≤ m + 2) : ¬ P.arc a k ⊆ ({P.vertex a, P.vertex (a + k)} : Set Plane) := by
  intro hsub
  set x : Plane := (1 / 2 : ℝ) • P.vertex a + (1 / 2 : ℝ) • P.vertex (a + 1) with hxdef
  have hxo : x ∈ openSegment ℝ (P.vertex a) (P.vertex (a + 1)) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hxarc : x ∈ P.arc a k :=
    mem_arc_iff.2 ⟨0, hk1, by
      rw [Nat.cast_zero, add_zero]; exact openSegment_subset_segment ℝ _ _ hxo⟩
  have hkne : (k : ZMod (m + 3)) ≠ 0 := by
    intro he
    have h0 : ((k : ℕ) : ZMod (m + 3)) = ((0 : ℕ) : ZMod (m + 3)) := by rw [he, Nat.cast_zero]
    have hk0 := ClosedPolygon.natCast_inj (m := m) (show k < m + 3 by omega)
      (show 0 < m + 3 by omega) h0
    omega
  rcases hsub hxarc with h | h
  · exact P.vertex_ne_succ a (left_mem_openSegment_iff.1 (h ▸ hxo))
  · refine notMem_edge_of_mem_openSegment (P := P) (i := a) (j := a + k)
      (fun he => hkne (by linear_combination he)) hxo ?_
    rw [edge, h]
    exact left_mem_segment ℝ _ _

/-- **The crossing count separates points exactly as the polygon does** (Theorem 2.3, read as a
criterion), for a polygon presented with redundant vertices. -/
theorem parity_ne_iff_mem_farRegion (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∉ P.carrier) (hy : y ∉ P.carrier) :
    parity u P.pieces x ≠ parity u P.pieces y ↔ x ∈ farRegion P.carrier y := by
  rw [mem_farRegion_iff_connectedComponentIn_ne hx]
  constructor
  · intro hne heq
    exact hne (P.parity_eq_of_mem_connectedComponentIn_carrier hu hL hy
      (heq ▸ mem_connectedComponentIn hx))
  · intro hne
    rcases P.connectedComponentIn_eq_inside_or_outside hx with hxr | hxr <;>
      rcases P.connectedComponentIn_eq_inside_or_outside hy with hyr | hyr
    · exact absurd (hxr.trans hyr.symm) hne
    · rw [P.parity_eq_one_of_mem_inside hu hL (hxr ▸ mem_connectedComponentIn hx),
        P.parity_eq_zero_of_mem_outside hu hL (hyr ▸ mem_connectedComponentIn hy)]
      decide
    · rw [P.parity_eq_zero_of_mem_outside hu hL (hxr ▸ mem_connectedComponentIn hx),
        P.parity_eq_one_of_mem_inside hu hL (hyr ▸ mem_connectedComponentIn hy)]
      decide
    · exact absurd (hxr.trans hyr.symm) hne

/-! ### An arc as a polyline

`arc a k` is the carrier of the vertex list `v a, v (a+1), …, v (a+k)`; that is how it is seen
to be polygonal, and how it is glued to a crosscut. -/

/-- The vertex list of an arc. -/
def arcList (P : PrePolygon m) (a : ZMod (m + 3)) : ℕ → List Plane
  | 0 => [P.vertex a]
  | k + 1 => P.vertex a :: arcList P (a + 1) k

theorem arcList_ne_nil (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) : P.arcList a k ≠ [] := by
  cases k <;> simp [arcList]

theorem head_arcList (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    (P.arcList a k).head (P.arcList_ne_nil a k) = P.vertex a := by
  cases k <;> rfl

theorem getLast_arcList : ∀ (k : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)),
    (P.arcList a k).getLast (P.arcList_ne_nil a k) = P.vertex (a + k)
  | 0, P, a => by simp [arcList]
  | k + 1, P, a => by
    change (P.vertex a :: P.arcList (a + 1) k).getLast (List.cons_ne_nil _ _)
        = P.vertex (a + ((k + 1 : ℕ) : ZMod (m + 3)))
    rw [List.getLast_cons (P.arcList_ne_nil (a + 1) k), getLast_arcList k P (a + 1)]
    congr 1
    push_cast
    ring

theorem arcPieces_succ (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    P.arcPieces a (k + 1) = (P.vertex a, P.vertex (a + 1)) :: P.arcPieces (a + 1) k := by
  rw [arcPieces, arcPieces, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · rw [Nat.cast_zero, add_zero]
  · refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply]
    congr 2 <;> · push_cast; ring

theorem poly_arcList : ∀ (k : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)),
    poly (P.arcList a (k + 1)) = P.arc a (k + 1)
  | 0, P, a => by
    change segment ℝ (P.vertex a) (P.vertex (a + 1)) ∪ ({P.vertex (a + 1)} : Set Plane)
        = cover (P.arcPieces a 1)
    rw [arcPieces_succ P a 0, arcPieces_zero, cover_cons, cover_nil, Set.union_empty]
    exact union_eq_self_of_subset_right (singleton_subset_iff.2 (right_mem_segment ℝ _ _))
  | k + 1, P, a => by
    have hstep : poly (P.arcList a (k + 2))
        = segment ℝ (P.vertex a) (P.vertex (a + 1)) ∪ poly (P.arcList (a + 1) (k + 1)) := rfl
    rw [hstep, poly_arcList k P (a + 1)]
    change segment ℝ (P.vertex a) (P.vertex (a + 1)) ∪ cover (P.arcPieces (a + 1) (k + 1))
        = cover (P.arcPieces a (k + 2))
    rw [arcPieces_succ P a (k + 1), cover_cons]
    rfl

theorem poly_arcList_of_pos (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    poly (P.arcList a k) = P.arc a k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact poly_arcList k' P a

theorem isPolygonal_arc (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    IsPolygonal (P.arc a k) := ⟨P.arcList a k, (poly_arcList_of_pos P a hk).symm⟩

end PrePolygon

/-! ## Cutting a segment at an interior point, in order

The two halves of a cut segment meet only at the cut, and neither reaches the far end of the
other. Both are read off `Schoenflies/SegmentOrder.lean`: along a nondegenerate segment the
distance from one end is a coordinate. -/

/-- **The two halves of a cut segment meet only at the cut point.** -/
theorem segment_halves_inter {u v w : Plane} (huv : u ≠ v) (hw : w ∈ openSegment ℝ u v) :
    segment ℝ u w ∩ segment ℝ w v ⊆ {w} := by
  rintro x ⟨hx1, hx2⟩
  have hws : w ∈ segment ℝ u v := openSegment_subset_segment ℝ _ _ hw
  have hwd := dist_le_of_mem_segment huv (left_mem_segment ℝ u v) (right_mem_segment ℝ u v)
    (by simp) hws
  have h1 := dist_le_of_mem_segment huv (left_mem_segment ℝ u v) hws (by simp) hx1
  have h2 := dist_le_of_mem_segment huv hws (right_mem_segment ℝ u v) hwd.2 hx2
  have hxs : x ∈ segment ℝ u v :=
    (convex_segment u v).segment_subset (left_mem_segment ℝ u v) hws hx1
  exact eq_of_dist_left_eq huv hxs hws (le_antisymm h1.2 h2.1)

/-- The far end of a cut segment is not on the near half. -/
theorem right_notMem_left_half {u v w : Plane} (huv : u ≠ v) (hw : w ∈ openSegment ℝ u v) :
    v ∉ segment ℝ u w := by
  intro hv
  have hvw : v = w := segment_halves_inter huv hw ⟨hv, right_mem_segment ℝ w v⟩
  rw [← hvw] at hw
  exact huv (right_mem_openSegment_iff.1 hw)

/-- The near end of a cut segment is not on the far half. -/
theorem left_notMem_right_half {u v w : Plane} (huv : u ≠ v) (hw : w ∈ openSegment ℝ u v) :
    u ∉ segment ℝ w v := by
  intro hu
  have huw : u = w := segment_halves_inter huv hw ⟨left_mem_segment ℝ u w, hu⟩
  rw [← huw] at hw
  exact huv (left_mem_openSegment_iff.1 hw)

namespace PrePolygon

/-! ## Inserting a vertex

`Schoenflies.PrePolygon.deleteLast` removes a redundant vertex; this is the inverse operation,
and it is what makes `PrePolygon` the right presentation for a consumer that must cut the curve
at prescribed points. The vertex is inserted at the end of the list, interior to the last edge;
`Schoenflies.PrePolygon.rotate` brings any edge there. -/

section Insert

variable {m : ℕ} {P : PrePolygon m} {z : Plane}

/-- The index `-1` of a cyclic list of length `m + 3`, as a numeral. -/
theorem val_neg_one : (-1 : ZMod (m + 3)).val = m + 2 := by
  have h : (-1 : ZMod (m + 3)) = ((m + 2 : ℕ) : ZMod (m + 3)) := by
    have h0 : ((m + 3 : ℕ) : ZMod (m + 3)) = 0 := ZMod.natCast_self _
    push_cast at h0 ⊢
    linear_combination -h0
  rw [h, ZMod.val_cast_of_lt (by omega)]

/-- The last edge, with its second endpoint written as vertex `0`. -/
theorem edge_neg_one (P : PrePolygon m) :
    P.edge (-1) = segment ℝ (P.vertex (-1)) (P.vertex 0) := by
  rw [edge, show (-1 : ZMod (m + 3)) + 1 = 0 by ring]

/-- **A point interior to an edge is a vertex of no index.** -/
theorem vertex_ne_of_mem_openSegment {i : ZMod (m + 3)} {w : Plane}
    (hw : w ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1))) (j : ZMod (m + 3)) :
    P.vertex j ≠ w := by
  intro he
  by_cases hji : j = i
  · rw [hji] at he
    rw [← he] at hw
    exact vertex_ne_succ i (left_mem_openSegment_iff.1 hw)
  · have hmem : w ∈ P.edge j := by rw [edge, ← he]; exact left_mem_segment ℝ _ _
    exact notMem_edge_of_mem_openSegment hji hw hmem

/-- The vertex family with `z` appended at the end: the old numerals name the old vertices, and
the one new index names `z`. -/
def insVertex (P : PrePolygon m) (z : Plane) (j : ZMod (m + 1 + 3)) : Plane :=
  if j.val < m + 3 then P.vertex ((j.val : ℕ) : ZMod (m + 3)) else z

theorem insVertex_emb (P : PrePolygon m) (z : Plane) (j : ZMod (m + 3)) :
    insVertex P z (emb j) = P.vertex j := by
  have hlt : j.val < m + 3 := ZMod.val_lt j
  have hval : (emb j).val = j.val := by
    rw [emb, ZMod.val_cast_of_lt (by omega)]
  rw [insVertex, ite_eq_left (by rw [hval]; exact hlt), hval, ZMod.natCast_rightInverse j]

theorem val_neg_one' : (-1 : ZMod (m + 1 + 3)).val = m + 3 := by
  rw [neg_one_eq_cast, ZMod.val_cast_of_lt (by omega)]

theorem insVertex_neg_one (P : PrePolygon m) (z : Plane) : insVertex P z (-1) = z := by
  rw [insVertex, ite_eq_right (by rw [val_neg_one' (m := m)]; omega)]

/-- Away from the inserted vertex the edges are unchanged. -/
theorem insEdge_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) :
    segment ℝ (insVertex P z (emb j)) (insVertex P z (emb j + 1)) = P.edge j := by
  rw [← emb_succ_of_lt h, insVertex_emb, insVertex_emb, edge]

/-- The penultimate edge of the lengthened list: the near half of the cut edge. -/
theorem insEdge_pen (P : PrePolygon m) (z : Plane) :
    segment ℝ (insVertex P z (-1 - 1)) (insVertex P z (-1 - 1 + 1))
      = segment ℝ (P.vertex (-1)) z := by
  have he : emb (-1 : ZMod (m + 3)) = -1 - 1 := emb_eq_last (by rw [val_neg_one])
  have h1 : insVertex P z (-1 - 1) = P.vertex (-1) := by rw [← he, insVertex_emb]
  have h2 : insVertex P z (-1 - 1 + 1) = z := by
    rw [show (-1 - 1 : ZMod (m + 1 + 3)) + 1 = -1 by ring, insVertex_neg_one]
  rw [h1, h2]

/-- The last edge of the lengthened list: the far half of the cut edge. -/
theorem insEdge_last (P : PrePolygon m) (z : Plane) :
    segment ℝ (insVertex P z (-1)) (insVertex P z (-1 + 1)) = segment ℝ z (P.vertex 0) := by
  have hemb0 : emb (0 : ZMod (m + 3)) = 0 := by rw [emb, ZMod.val_zero, Nat.cast_zero]
  have h1 : insVertex P z (-1) = z := insVertex_neg_one P z
  have h2 : insVertex P z (-1 + 1) = P.vertex 0 := by
    rw [show (-1 : ZMod (m + 1 + 3)) + 1 = 0 by ring, ← hemb0, insVertex_emb]
  rw [h1, h2]

theorem vertex_neg_one_ne_zero (P : PrePolygon m) : P.vertex (-1) ≠ P.vertex 0 := by
  have h := vertex_ne_succ (P := P) (-1)
  rwa [show (-1 : ZMod (m + 3)) + 1 = 0 by ring] at h

variable (hz : z ∈ openSegment ℝ (P.vertex (-1)) (P.vertex 0))
include hz

/-- The two new edges cover the edge they replace. -/
theorem insEdge_union : segment ℝ (P.vertex (-1)) z ∪ segment ℝ z (P.vertex 0) = P.edge (-1) := by
  rw [edge_neg_one]
  exact (segment_split (openSegment_subset_segment ℝ _ _ hz)).symm

theorem insEdge_pen_subset : segment ℝ (P.vertex (-1)) z ⊆ P.edge (-1) := by
  rw [← insEdge_union hz]; exact Set.subset_union_left

theorem insEdge_last_subset : segment ℝ z (P.vertex 0) ⊆ P.edge (-1) := by
  rw [← insEdge_union hz]; exact Set.subset_union_right

/-- **The polygon with one extra vertex, interior to its last edge** — equivalently, with the
last edge split in two at a prescribed interior point. -/
def insertLast (P : PrePolygon m) (hz : z ∈ openSegment ℝ (P.vertex (-1)) (P.vertex 0)) :
    PrePolygon (m + 1) where
  vertex := insVertex P z
  vertex_inj := by
    intro i j hij
    have hzv : ∀ l : ZMod (m + 3), P.vertex l ≠ z := by
      intro l
      refine vertex_ne_of_mem_openSegment (i := -1) ?_ l
      rwa [show (-1 : ZMod (m + 3)) + 1 = 0 by ring]
    simp only [insVertex] at hij
    have hi := ZMod.val_lt i
    have hj := ZMod.val_lt j
    by_cases hli : i.val < m + 3 <;> by_cases hlj : j.val < m + 3
    · rw [ite_eq_left hli, ite_eq_left hlj] at hij
      exact ZMod.val_injective _
        (ClosedPolygon.natCast_inj hli hlj (P.vertex_inj hij))
    · rw [ite_eq_left hli, ite_eq_right hlj] at hij
      exact absurd hij (hzv _)
    · rw [ite_eq_right hli, ite_eq_left hlj] at hij
      exact absurd hij.symm (hzv _)
    · exact ZMod.val_injective _ (by omega)
  edges_meet := by
    have hne0 : P.vertex (-1) ≠ P.vertex 0 := vertex_neg_one_ne_zero P
    have hhalf := segment_halves_inter hne0 hz
    have hpen := insEdge_pen P z
    have hlast := insEdge_last P z
    -- The shape of the edge at each of the three kinds of index.
    have hshape : ∀ i : ZMod (m + 1 + 3),
        (∃ j : ZMod (m + 3), j.val + 1 < m + 3 ∧ emb j = i ∧
            segment ℝ (insVertex P z i) (insVertex P z (i + 1)) = P.edge j ∧
            ({insVertex P z i, insVertex P z (i + 1)} : Set Plane)
              = {P.vertex j, P.vertex (j + 1)}) ∨
          (i = -1 - 1 ∧ segment ℝ (insVertex P z i) (insVertex P z (i + 1))
              = segment ℝ (P.vertex (-1)) z) ∨
          (i = -1 ∧ segment ℝ (insVertex P z i) (insVertex P z (i + 1))
              = segment ℝ z (P.vertex 0)) := by
      intro i
      by_cases h1 : i = -1
      · exact Or.inr (Or.inr ⟨h1, by rw [h1]; exact hlast⟩)
      by_cases h2 : i = -1 - 1
      · exact Or.inr (Or.inl ⟨h2, by rw [h2]; exact hpen⟩)
      obtain ⟨j, hjv, rfl⟩ := exists_emb_eq h1 h2
      refine Or.inl ⟨j, hjv, rfl, insEdge_of_lt hjv, ?_⟩
      rw [insVertex_emb, ← emb_succ_of_lt hjv, insVertex_emb]
    intro i j hij
    have hi := hshape i
    have hj := hshape j
    -- The names of the two ends of the edge at `i`, in each case.
    rcases hi with ⟨ji, hjiv, rfl, hEi, hVi⟩ | ⟨rfl, hEi⟩ | ⟨rfl, hEi⟩
    · have hjine : ji ≠ -1 := by
        intro he
        rw [he, val_neg_one] at hjiv
        omega
      rw [hEi, hVi]
      rcases hj with ⟨jj, hjjv, rfl, hEj, -⟩ | ⟨rfl, hEj⟩ | ⟨rfl, hEj⟩
      · rw [hEj]
        exact P.edges_meet ji jj fun he => hij (by rw [he])
      · rw [hEj]
        exact fun x hx =>
          P.edges_meet ji (-1) hjine ⟨hx.1, insEdge_pen_subset hz hx.2⟩
      · rw [hEj]
        exact fun x hx =>
          P.edges_meet ji (-1) hjine ⟨hx.1, insEdge_last_subset hz hx.2⟩
    · rw [hEi]
      have hV : ({insVertex P z (-1 - 1), insVertex P z (-1 - 1 + 1)} : Set Plane)
          = {P.vertex (-1), z} := by
        have he : emb (-1 : ZMod (m + 3)) = -1 - 1 := emb_eq_last (by rw [val_neg_one])
        rw [show insVertex P z (-1 - 1) = P.vertex (-1) by rw [← he, insVertex_emb],
          show insVertex P z (-1 - 1 + 1) = z by
            rw [show (-1 - 1 : ZMod (m + 1 + 3)) + 1 = -1 by ring, insVertex_neg_one]]
      rw [hV]
      rcases hj with ⟨jj, hjjv, rfl, hEj, -⟩ | ⟨rfl, -⟩ | ⟨rfl, hEj⟩
      · have hjjne : jj ≠ -1 := by
          intro he
          rw [he, val_neg_one] at hjjv
          omega
        rw [hEj]
        rintro x ⟨hx1, hx2⟩
        have hmem := P.edges_meet (-1) jj (Ne.symm hjjne)
          ⟨insEdge_pen_subset hz hx1, hx2⟩
        rw [show (-1 : ZMod (m + 3)) + 1 = 0 by ring] at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
        rcases hmem with hmem | hmem
        · exact Or.inl hmem
        · exact absurd (hmem ▸ hx1) (right_notMem_left_half hne0 hz)
      · exact absurd rfl hij
      · rw [hEj]
        exact fun x hx => Or.inr (hhalf hx)
    · rw [hEi]
      have hV : ({insVertex P z (-1), insVertex P z (-1 + 1)} : Set Plane)
          = {z, P.vertex 0} := by
        have hemb0 : emb (0 : ZMod (m + 3)) = 0 := by rw [emb, ZMod.val_zero, Nat.cast_zero]
        rw [insVertex_neg_one,
          show insVertex P z (-1 + 1) = P.vertex 0 by
            rw [show (-1 : ZMod (m + 1 + 3)) + 1 = 0 by ring, ← hemb0, insVertex_emb]]
      rw [hV]
      rcases hj with ⟨jj, hjjv, rfl, hEj, -⟩ | ⟨rfl, hEj⟩ | ⟨rfl, -⟩
      · have hjjne : jj ≠ -1 := by
          intro he
          rw [he, val_neg_one] at hjjv
          omega
        rw [hEj]
        rintro x ⟨hx1, hx2⟩
        have hmem := P.edges_meet (-1) jj (Ne.symm hjjne)
          ⟨insEdge_last_subset hz hx1, hx2⟩
        rw [show (-1 : ZMod (m + 3)) + 1 = 0 by ring] at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
        rcases hmem with hmem | hmem
        · exact absurd (hmem ▸ hx1) (left_notMem_right_half hne0 hz)
        · exact Or.inr hmem
      · rw [hEj]
        exact fun x hx => Or.inl (hhalf ⟨hx.2, hx.1⟩)
      · exact absurd rfl hij

@[simp] theorem insertLast_vertex : (insertLast P hz).vertex = insVertex P z := rfl

/-- **Inserting a vertex does not move the curve.** -/
theorem carrier_insertLast : (insertLast P hz).carrier = P.carrier := by
  have hpen := insEdge_pen P z
  have hlast := insEdge_last P z
  refine Set.Subset.antisymm (Set.iUnion_subset fun i => ?_) (Set.iUnion_subset fun j => ?_)
  · by_cases h1 : i = -1
    · subst h1
      refine le_trans (le_of_eq ?_) (le_trans (insEdge_last_subset hz) (edge_subset_carrier _))
      exact hlast
    by_cases h2 : i = -1 - 1
    · subst h2
      refine le_trans (le_of_eq ?_) (le_trans (insEdge_pen_subset hz) (edge_subset_carrier _))
      exact hpen
    · obtain ⟨j, hjv, rfl⟩ := exists_emb_eq h1 h2
      refine le_trans (le_of_eq ?_) (edge_subset_carrier j)
      exact insEdge_of_lt hjv
  · by_cases hjlast : j.val + 1 < m + 3
    · refine le_trans (le_of_eq ?_) (edge_subset_carrier (P := insertLast P hz) (emb j))
      exact (insEdge_of_lt hjlast (P := P) (z := z)).symm
    · have hjm : j = -1 := by
        have := ZMod.val_lt j
        exact ZMod.val_injective _ (by rw [val_neg_one]; omega)
      subst hjm
      rw [← insEdge_union hz]
      refine Set.union_subset ?_ ?_
      · refine le_trans (le_of_eq hpen.symm)
          (edge_subset_carrier (P := insertLast P hz) (-1 - 1))
      · refine le_trans (le_of_eq hlast.symm)
          (edge_subset_carrier (P := insertLast P hz) (-1))

/-- The inserted vertex is a vertex. -/
theorem insertLast_mem_vertex : ∃ j, (insertLast P hz).vertex j = z :=
  ⟨-1, insVertex_neg_one P z⟩

/-- The old vertices are still vertices. -/
theorem insertLast_old_vertex (i : ZMod (m + 3)) : ∃ j, (insertLast P hz).vertex j = P.vertex i :=
  ⟨emb i, insVertex_emb P z i⟩

end Insert

/-- **A named point of the curve becomes a vertex**, and the old vertices stay vertices. Either
the point already is a vertex, or it is interior to exactly one edge, and then that edge is
brought to the end of the list by `Schoenflies.PrePolygon.rotate` and cut by
`Schoenflies.PrePolygon.insertLast`. -/
theorem exists_prePolygon_insert {m : ℕ} (P : PrePolygon m) {z : Plane} (hz : z ∈ P.carrier) :
    ∃ (m' : ℕ) (P' : PrePolygon m'), P'.carrier = P.carrier ∧ (∃ j, P'.vertex j = z) ∧
      ∀ i, ∃ j, P'.vertex j = P.vertex i := by
  obtain ⟨i, hzi⟩ := Set.mem_iUnion.1 hz
  by_cases hend : z = P.vertex i ∨ z = P.vertex (i + 1)
  · exact ⟨m, P, rfl, by rcases hend with rfl | rfl; exacts [⟨i, rfl⟩, ⟨i + 1, rfl⟩],
      fun i => ⟨i, rfl⟩⟩
  · push Not at hend
    have hopen : z ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1)) :=
      mem_openSegment_of_ne_left_right (Ne.symm hend.1) (Ne.symm hend.2) hzi
    -- Rotate so that the edge in question is the last one.
    set Q : PrePolygon m := P.rotate (i + 1) with hQ
    have hQm : Q.vertex (-1) = P.vertex i := by
      rw [hQ, rotate_vertex, show i + 1 + (-1 : ZMod (m + 3)) = i by ring]
    have hQ0 : Q.vertex 0 = P.vertex (i + 1) := by
      rw [hQ, rotate_vertex, add_zero]
    have hopen' : z ∈ openSegment ℝ (Q.vertex (-1)) (Q.vertex 0) := by rw [hQm, hQ0]; exact hopen
    refine ⟨m + 1, insertLast Q hopen', ?_, insertLast_mem_vertex hopen', fun l => ?_⟩
    · rw [carrier_insertLast hopen', hQ, carrier_rotate]
    · obtain ⟨j, hj⟩ := insertLast_old_vertex hopen' (l - (i + 1))
      exact ⟨j, by rw [hj, hQ, rotate_vertex, add_sub_cancel]⟩

/-- **Every point of a finite list on the curve can be made a vertex at once.** -/
theorem exists_prePolygon_vertices : ∀ (S : List Plane) {m : ℕ} (P : PrePolygon m),
    (∀ z ∈ S, z ∈ P.carrier) →
      ∃ (m' : ℕ) (P' : PrePolygon m'), P'.carrier = P.carrier ∧
        (∀ z ∈ S, ∃ j, P'.vertex j = z) ∧ (∀ i, ∃ j, P'.vertex j = P.vertex i)
  | [], m, P, _ => ⟨m, P, rfl, by simp, fun i => ⟨i, rfl⟩⟩
  | z :: S, m, P, hS => by
    obtain ⟨m₁, P₁, hcar₁, ⟨j₀, hj₀⟩, hold₁⟩ :=
      exists_prePolygon_insert P (hS z (List.mem_cons_self ..))
    obtain ⟨m₂, P₂, hcar₂, hnew₂, hold₂⟩ := exists_prePolygon_vertices S P₁
      (fun w hw => by rw [hcar₁]; exact hS w (List.mem_cons_of_mem _ hw))
    refine ⟨m₂, P₂, by rw [hcar₂, hcar₁], fun w hw => ?_, fun i => ?_⟩
    · rcases List.mem_cons.1 hw with rfl | hw'
      · obtain ⟨j, hj⟩ := hold₂ j₀
        exact ⟨j, by rw [hj, hj₀]⟩
      · exact hnew₂ w hw'
    · obtain ⟨j₁, hj₁⟩ := hold₁ i
      obtain ⟨j, hj⟩ := hold₂ j₁
      exact ⟨j, by rw [hj, hj₁]⟩

/-- A one-edge arc is that edge. -/
theorem arc_one {m : ℕ} (P : PrePolygon m) (a : ZMod (m + 3)) : P.arc a 1 = P.edge a := by
  ext z
  rw [mem_arc_iff]
  constructor
  · rintro ⟨t, ht, hz⟩
    obtain rfl : t = 0 := by omega
    rwa [Nat.cast_zero, add_zero] at hz
  · intro hz
    exact ⟨0, by omega, by rwa [Nat.cast_zero, add_zero]⟩

/-- **A vertex on an edge is one of that edge's own two ends.** -/
theorem vertex_mem_edge_elim {m : ℕ} {P : PrePolygon m} {c i : ZMod (m + 3)}
    (hc : P.vertex c ∈ P.edge i) :
    P.vertex c ∈ ({P.vertex i, P.vertex (i + 1)} : Set Plane) := by
  by_cases hci : c = i
  · exact Or.inl (by rw [hci])
  · exact P.edges_meet i c (Ne.symm hci) ⟨hc, left_mem_segment ℝ _ _⟩

end PrePolygon

/-! ## The realization theorem, with the cut points anywhere on the curve

`Schoenflies.exists_closedPolygon_split` requires the two cut points to be *corners*, and by
`Schoenflies.ClosedPolygon.isCornerAt_vertex` that requirement cannot be dropped while the
realization is a `ClosedPolygon`. For a `PrePolygon` there is no such obstruction: a point of the
curve is either already a vertex or interior to an edge, and an edge may be cut. -/

/-- **The realization theorem for `PrePolygon`, with named points.** Any finite list of points of
the curve — corners or not — can be required to be among the vertices. -/
theorem exists_prePolygon_points {C : Set Plane} (hJ : IsJordanCurve C) (hP : IsPolygonal C)
    (S : List Plane) (hS : ∀ p ∈ S, p ∈ C) :
    ∃ (m : ℕ) (P : PrePolygon m), P.carrier = C ∧ ∀ p ∈ S, ∃ i : ZMod (m + 3), P.vertex i = p := by
  obtain ⟨m, P, hcar⟩ := exists_prePolygon_of_isJordanCurve hJ hP
  obtain ⟨m', P', hcar', hnew, -⟩ :=
    PrePolygon.exists_prePolygon_vertices S P (fun z hz => by rw [hcar]; exact hS z hz)
  exact ⟨m', P', by rw [hcar', hcar], hnew⟩

/-- **The realization theorem tracking two named points**, for a presentation that may carry
redundant vertices. Unlike `Schoenflies.exists_closedPolygon_split` this asks nothing of the two
points but that they lie on the curve: a `PrePolygon` has no `corner` field to obstruct a vertex
where the curve runs straight. -/
theorem exists_prePolygon_split {C : Set Plane} (hJ : IsJordanCurve C) (hP : IsPolygonal C)
    {p q : Plane} (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q) :
    ∃ (m : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ), P.carrier = C ∧
      P.vertex a = p ∧ P.vertex (a + (k : ZMod (m + 3))) = q ∧ 1 ≤ k ∧ k ≤ m + 2 := by
  obtain ⟨m, P, hcar, hvert⟩ := exists_prePolygon_points hJ hP [p, q]
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

end Schoenflies
