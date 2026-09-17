/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.PrePolygonArc
import LeanPool.Schoenflies.Graph.K33Closed

/-!
# `lem:k33` and `cor:k33-subdivision`, with nothing assumed

`Schoenflies/Graph/K33Planar.lean` proves the nonplanarity of `K(3,3)` from
`Graph.IsHexRealization`; `Schoenflies/Graph/K33Closed.lean` reduces that to `Graph.Bendable` —
"every polygonal drawing can be redrawn so that no two edges leave a vertex along one line". This
module removes the hypothesis altogether. Nothing is bent.

## Where the hypothesis came from, and why it is not needed

`Schoenflies.ClosedPolygon` carries a `corner` field, and
`Schoenflies.ClosedPolygon.isCornerAt_vertex` shows the field is not slack: *every* vertex of
*every* `ClosedPolygon` presentation is a point at which the curve turns. So a crosscut interface
phrased with `ClosedPolygon`s — `Schoenflies.IsPolygonalCrosscut`, and hence
`Schoenflies.alternating_crosscuts` — can only cut the curve at corners, and a drawn `K(3,3)` puts
its branch points wherever it likes.

The blueprint's `cor:alternating-crosscuts` has no such condition: it is stated for a set-level
simple closed polygonal curve and simple polygonal arcs with endpoints anywhere on it. The fix is
to state the crosscut for `Schoenflies.PrePolygon` — `ClosedPolygon` without `corner` — whose
vertices may sit anywhere on the curve. `Schoenflies/PrePolygonSep.lean` already supplies the two
things Theorem 2.8 asks of such a curve: that its carrier separates the plane, and the two values
of the crossing parity. Everything else in the chain is about *edge lists*, and edge lists do not
know about corners.

## The one construction this needed

Three closed polygons enter Theorem 2.8 — the curve `C` and the two curves `Jᵢ` the crosscut
forms with the two arcs — and their **edge lists** must agree: `SameEdges Jᵢ.pieces (Aᵢ ++ K)`.
`Schoenflies/Graph/K33Closed.lean` found three realizations independently and matched them with
`Schoenflies.ClosedPolygon.arcPieces_eq`, whose proof is exactly where `corner` was consumed. For
`PrePolygon` no such matching theorem can exist: two presentations of one arc need not agree.

So the two spliced curves are not found — they are *built*. `Schoenflies.PrePolygon.exists_splice`
lays two chains with common ends end to end and returns a `PrePolygon` whose edge list is their
concatenation, so the three lists agree by construction and nothing has to be matched. The chains
themselves come from `Schoenflies.exists_prePolygon_arcs_oriented`, which needs
`Schoenflies.PrePolygon.insertLast` of `Schoenflies/PrePolygonArc.lean`: a point of the curve that
is not yet a vertex is interior to an edge, and an edge may be cut. That is the inverse of
`Schoenflies.PrePolygon.deleteLast`, and it is what makes "a `PrePolygon` may be presented with
vertices at any prescribed finite set of points of its carrier" a theorem
(`Schoenflies.PrePolygon.exists_prePolygon_vertices`).

## What this module rests on

The `Schoenflies.PrePolygon` arc apparatus — `chain`, `arcPieces`, `arc`, `arc_inter`,
`isArcBetween_arc`, `parity_splitting`, `parity_ne_iff_mem_farRegion`, `insertLast`,
`exists_prePolygon_vertices`, `Schoenflies.exists_prePolygon_split` and the segment-cutting
lemmas — is in `Schoenflies/PrePolygonArc.lean`, shared with `Schoenflies/FaceCyclesLand.lean`.
Only what is peculiar to the crosscut wiring is left here.

## Blueprint

* `Schoenflies.PrePolygon.exists_splice` — two arcs with common ends, laid end to end.
* `Schoenflies.PrePolygon.reverse`, `…reverse_arc`, `…sameEdges_reverse_arcPieces` — the polygon
  traversed the other way, which is what pins the direction of a prescribed arc.
* `Schoenflies.exists_prePolygon_arcs`, `…exists_prePolygon_arcs_oriented` — §1, the realization
  theorem **with the cut points anywhere on the curve**, tracking a prescribed splitting.
  Compare `Schoenflies.exists_closedPolygon_arcs`, which requires the cut points to be corners.
* `Schoenflies.IsPrePolygonalCrosscut` and its API up to
  `…alternating_inter_nonempty_of_same_side` — `thm:polygonal-crosscut` and
  `cor:alternating-crosscuts` in the blueprint's own generality: the split points need not be
  corners.
* `Graph.IsPreHexCrosscut`, `Graph.IsK33Config.isPreHexCrosscut` — the six-cycle of a polygonally
  drawn `K(3,3)`, cut at the two ends of one remaining edge, as such a crosscut. **This is what
  `Graph.IsHexRealization` was assuming, and it is proved here.**
* `Graph.IsK33Config.false_of_isPreHexCrosscut`, `…false_of_polygonal`,
  `Graph.IsK33Config.not_exists_isDrawing` — `lem:k33`.
* `Graph.IsArcK33.elim`, `Graph.IsK33Subdivision.elim` — `cor:k33-subdivision`.
* `Graph.k33Graph_not_exists_isDrawing` — `lem:k33` for the concrete graph.

## A note on names, for the integrator

The direct statements use eliminator-style names because the realization-parametric lemmas are
still in the import closure:

| realization-parametric lemma                      | direct theorem                             |
|---------------------------------------------------|--------------------------------------------|
| `Graph.IsK33Config.not_isDrawing` (K33Planar)      | `Graph.IsK33Config.not_exists_isDrawing`   |
| `Graph.IsK33Config.not_isDrawing_of_bendable`      | `Graph.IsK33Config.not_exists_isDrawing`   |
| `Graph.IsArcK33.false_of_realization`/`_bendable`  | `Graph.IsArcK33.elim`                      |
| `Graph.IsK33Subdivision.false_of_realization`/`…`  | `Graph.IsK33Subdivision.elim`              |
| `Graph.k33Graph_not_isDrawing`                     | `Graph.k33Graph_not_exists_isDrawing`      |

With this module in place `Graph.IsHexRealization`, `Graph.IsHexCrosscut`, `Graph.IsHexGeneric`
and `Graph.Bendable` have no consumers left.
-/

open Bornology Metric Set unitInterval
open scoped Graph

namespace Schoenflies

open Plane

namespace PrePolygon

/-! ## Splicing two chains into a closed polygon

The crosscut of Theorem 2.8 asks for three closed polygons whose *edge lists* fit together, and
independent realizations of three curves do not. The way out is to realize only the curve `C`,
and to build the two spliced curves out of one arc of `C` and one presentation of the crosscut —
so that the three edge lists agree by construction. This is that construction: two chains with
the same pair of ends, meeting only there, laid end to end. -/

/-- **Two arcs with common ends splice into a closed polygon whose edge list is their
concatenation.** `P.arcPieces a k` runs from `p` to `q` and `P'.arcPieces b l` runs from `q` back
to `p`; the two meet only at `p` and `q`. -/
theorem exists_splice {m m' : ℕ} (P : PrePolygon m) (P' : PrePolygon m')
    {a : ZMod (m + 3)} {k : ℕ} {b : ZMod (m' + 3)} {l : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2) (hl1 : 1 ≤ l) (hl2 : l ≤ m' + 2)
    (hstart : P'.vertex b = P.vertex (a + (k : ZMod (m + 3))))
    (hend : P'.vertex (b + (l : ZMod (m' + 3))) = P.vertex a)
    (hinter : P.arc a k ∩ P'.arc b l = {P.vertex a, P.vertex (a + (k : ZMod (m + 3)))}) :
    ∃ (n : ℕ) (Q : PrePolygon n), Q.pieces = P.arcPieces a k ++ P'.arcPieces b l := by
  -- The two chains cannot both be a single edge: they would be the same segment.
  have hthree : 3 ≤ k + l := by
    by_contra hcon
    obtain rfl : k = 1 := by omega
    obtain rfl : l = 1 := by omega
    rw [Nat.cast_one] at hstart hinter
    rw [Nat.cast_one] at hend
    have hseg : P'.edge b = P.edge a := by
      rw [edge, edge, hstart, hend, segment_symm]
    rw [P.arc_one a, P'.arc_one b, hseg, Set.inter_self] at hinter
    obtain ⟨z, hz, hz1, hz2⟩ := exists_mem_segment_ne (vertex_ne_succ (P := P) a)
    rcases hinter.subset hz with h | h
    exacts [hz1 h, hz2 h]
  obtain ⟨n, hn⟩ : ∃ n, k + l = n + 3 := ⟨k + l - 3, by omega⟩
  -- Pieces of one arc lie in that arc; that is all the intersection hypothesis is used through.
  have hPedge : ∀ t : ℕ, t < k → P.edge (a + (t : ZMod (m + 3))) ⊆ P.arc a k :=
    fun t ht z hz => mem_arc_iff.2 ⟨t, ht, hz⟩
  have hP'edge : ∀ t : ℕ, t < l → P'.edge (b + (t : ZMod (m' + 3))) ⊆ P'.arc b l :=
    fun t ht z hz => mem_arc_iff.2 ⟨t, ht, hz⟩
  have hcross : ∀ s : ℕ, s < k → ∀ t : ℕ, t < l →
      P.edge (a + (s : ZMod (m + 3))) ∩ P'.edge (b + (t : ZMod (m' + 3)))
        ⊆ ({P.vertex a, P.vertex (a + (k : ZMod (m + 3)))} : Set Plane) := by
    intro s hs t ht z hz
    rw [← hinter]
    exact ⟨hPedge s hs hz.1, hP'edge t ht hz.2⟩
  -- The spliced vertex list.
  set w : ZMod (n + 3) → Plane := fun j =>
    if j.val < k then P.vertex (a + ((j.val : ℕ) : ZMod (m + 3)))
    else P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3))) with hwdef
  have hbound : ∀ j : ZMod (n + 3), j.val < k + l := fun j => by
    have := ZMod.val_lt j; omega
  have hw_lt : ∀ j : ZMod (n + 3), j.val < k →
      w j = P.vertex (a + ((j.val : ℕ) : ZMod (m + 3))) := fun j hj => by
    rw [hwdef]; exact ite_eq_left hj
  have hw_ge : ∀ j : ZMod (n + 3), ¬ j.val < k →
      w j = P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3))) := fun j hj => by
    rw [hwdef]; exact ite_eq_right hj
  have hsucc_lt : ∀ j : ZMod (n + 3), j.val < k →
      w (j + 1) = P.vertex (a + ((j.val : ℕ) : ZMod (m + 3)) + 1) := by
    intro j hj
    have hval : (j + 1).val = j.val + 1 := val_succ_of_lt (m := n) (by omega)
    by_cases hlt : j.val + 1 < k
    · rw [hw_lt (j + 1) (by omega), hval]
      congr 1
      push_cast
      ring
    · have hk' : j.val + 1 = k := by omega
      rw [hw_ge (j + 1) (by omega), hval, hk', Nat.sub_self, Nat.cast_zero, add_zero, hstart]
      congr 1
      rw [← hk']
      push_cast
      ring
  have hsucc_ge : ∀ j : ZMod (n + 3), ¬ j.val < k →
      w (j + 1) = P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3)) + 1) := by
    intro j hj
    have hjb := hbound j
    by_cases hlt : j.val + 1 < n + 3
    · have hval : (j + 1).val = j.val + 1 := val_succ_of_lt (m := n) (by omega)
      rw [hw_ge (j + 1) (by omega), hval]
      congr 1
      rw [show j.val + 1 - k = (j.val - k) + 1 by omega]
      push_cast
      ring
    · have hval : (j + 1).val = 0 := val_succ_last (m := n) (by omega)
      rw [hw_lt (j + 1) (by omega), hval, Nat.cast_zero, add_zero, ← hend]
      congr 1
      have hc : ((l - 1 : ℕ) : ZMod (m' + 3)) + 1 = ((l : ℕ) : ZMod (m' + 3)) :=
        ClosedPolygon.natCast_pred_succ (by omega)
      rw [show j.val - k = l - 1 by omega, add_assoc, hc]
  -- The edges of the spliced list are the edges of the two arcs.
  have hE_lt : ∀ j : ZMod (n + 3), j.val < k →
      segment ℝ (w j) (w (j + 1)) = P.edge (a + ((j.val : ℕ) : ZMod (m + 3))) := by
    intro j hj
    rw [hw_lt j hj, hsucc_lt j hj, edge]
  have hE_ge : ∀ j : ZMod (n + 3), ¬ j.val < k →
      segment ℝ (w j) (w (j + 1)) = P'.edge (b + ((j.val - k : ℕ) : ZMod (m' + 3))) := by
    intro j hj
    rw [hw_ge j hj, hsucc_ge j hj, edge]
  have hends_lt : ∀ j : ZMod (n + 3), j.val < k →
      ({w j, w (j + 1)} : Set Plane)
        = {P.vertex (a + ((j.val : ℕ) : ZMod (m + 3))),
           P.vertex (a + ((j.val : ℕ) : ZMod (m + 3)) + 1)} := by
    intro j hj
    rw [hw_lt j hj, hsucc_lt j hj]
  have hends_ge : ∀ j : ZMod (n + 3), ¬ j.val < k →
      ({w j, w (j + 1)} : Set Plane)
        = {P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3))),
           P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3)) + 1)} := by
    intro j hj
    rw [hw_ge j hj, hsucc_ge j hj]
  refine ⟨n, ⟨w, ?_, ?_⟩, ?_⟩
  · -- injectivity
    intro i j hij
    have hib := hbound i
    have hjb := hbound j
    have hcase : ∀ i' j' : ZMod (n + 3), i'.val < k → ¬ j'.val < k → w i' ≠ w j' := by
      intro i' j' hi' hj' he
      rw [hw_lt i' hi', hw_ge j' hj'] at he
      have hval : P.vertex (a + ((i'.val : ℕ) : ZMod (m + 3))) ∈
          ({P.vertex a, P.vertex (a + (k : ZMod (m + 3)))} : Set Plane) := by
        rw [← hinter]
        exact ⟨hPedge i'.val hi' (left_mem_segment ℝ _ _),
          he ▸ hP'edge (j'.val - k) (by have := hbound j'; omega) (left_mem_segment ℝ _ _)⟩
      rcases hval with hval | hval
      · -- the common point is `p`: on the second arc that forces the last index
        have h0 : i'.val = 0 := by
          have := P.natCast_shift_inj a (show i'.val < m + 3 by omega) (show 0 < m + 3 by omega)
            (by rw [hval, Nat.cast_zero, add_zero])
          omega
        have hlast : P'.vertex (b + ((j'.val - k : ℕ) : ZMod (m' + 3)))
            = P'.vertex (b + ((l : ℕ) : ZMod (m' + 3))) := by rw [hend, ← he, hval]
        have := P'.natCast_shift_inj b (show j'.val - k < m' + 3 by have := hbound j'; omega)
          (show l < m' + 3 by omega) hlast
        have := hbound j'
        omega
      · have := P.natCast_shift_inj a (show i'.val < m + 3 by omega) (show k < m + 3 by omega)
          (by rw [hval])
        omega
    by_cases hli : i.val < k <;> by_cases hlj : j.val < k
    · rw [hw_lt i hli, hw_lt j hlj] at hij
      exact ZMod.val_injective _ (P.natCast_shift_inj a (by omega) (by omega) hij)
    · exact absurd hij (hcase i j hli hlj)
    · exact absurd hij.symm (hcase j i hlj hli)
    · rw [hw_ge i hli, hw_ge j hlj] at hij
      have := P'.natCast_shift_inj b (show i.val - k < m' + 3 by omega)
        (show j.val - k < m' + 3 by omega) hij
      exact ZMod.val_injective _ (by omega)
  · -- simplicity
    intro i j hij
    have hib := hbound i
    have hjb := hbound j
    by_cases hli : i.val < k <;> by_cases hlj : j.val < k
    · rw [hE_lt i hli, hE_lt j hlj, hends_lt i hli]
      refine P.edges_meet _ _ fun he => hij (ZMod.val_injective _ ?_)
      exact P.natCast_shift_inj a (by omega) (by omega) (by rw [he])
    · rw [hE_lt i hli, hE_ge j hlj, hends_lt i hli]
      intro z hz
      have hz' := hcross i.val hli (j.val - k) (by omega) hz
      rcases hz' with rfl | rfl
      exacts [vertex_mem_edge_elim (P := P) (c := a) hz.1,
        vertex_mem_edge_elim (P := P) (c := a + (k : ZMod (m + 3))) hz.1]
    · rw [hE_ge i hli, hE_lt j hlj, hends_ge i hli]
      intro z hz
      have hz' := hcross j.val hlj (i.val - k) (by omega) ⟨hz.2, hz.1⟩
      rcases hz' with rfl | rfl
      · rw [← hend]
        exact vertex_mem_edge_elim (P := P') (c := b + (l : ZMod (m' + 3)))
          (by rw [hend]; exact hz.1)
      · rw [← hstart]
        exact vertex_mem_edge_elim (P := P') (c := b) (by rw [hstart]; exact hz.1)
    · rw [hE_ge i hli, hE_ge j hlj, hends_ge i hli]
      refine P'.edges_meet _ _ fun he => hij (ZMod.val_injective _ ?_)
      have := P'.natCast_shift_inj b (show i.val - k < m' + 3 by omega)
        (show j.val - k < m' + 3 by omega) (by rw [he])
      omega
  · -- the edge list
    have hrange : List.range (n + 3) = List.range k ++ (List.range l).map (k + ·) := by
      rw [← hn]; exact List.range_add
    change ((List.range (n + 3)).map fun j : ℕ =>
        (w ((j : ℕ) : ZMod (n + 3)), w (((j : ℕ) : ZMod (n + 3)) + 1))) = _
    rw [hrange, List.map_append, List.map_map, arcPieces, arcPieces]
    congr 1
    · refine List.map_congr_left fun t ht => ?_
      have htk : t < k := List.mem_range.1 ht
      have hval : ((t : ZMod (n + 3))).val = t := ZMod.val_cast_of_lt (by omega)
      have h1 : ((t : ZMod (n + 3))).val < k := by rw [hval]; exact htk
      rw [hw_lt _ h1, hsucc_lt _ h1, hval]
    · refine List.map_congr_left fun s hs => ?_
      have hsl : s < l := List.mem_range.1 hs
      have hval : (((k + s : ℕ) : ZMod (n + 3))).val = k + s := ZMod.val_cast_of_lt (by omega)
      have h1 : ¬ (((k + s : ℕ) : ZMod (n + 3))).val < k := by rw [hval]; omega
      simp only [Function.comp_apply]
      rw [hw_ge _ h1, hsucc_ge _ h1, hval, show k + s - k = s by omega]

/-! ## The polygon read backwards

Needed only to pin the *direction* in which a realization traverses a prescribed arc; the
`Schoenflies.ClosedPolygon` version is in `Schoenflies/Graph/K33Closed.lean`, and this is the
same construction with the `corner` field dropped. -/

/-- **The same closed polygon, traversed the other way.** -/
def reverse {m : ℕ} (P : PrePolygon m) : PrePolygon m where
  vertex j := P.vertex (-j)
  vertex_inj _ _ h := neg_injective (P.vertex_inj h)
  edges_meet i j hij := by
    have e1 : (-(i + 1) : ZMod (m + 3)) = -i - 1 := by ring
    have e2 : (-(j + 1) : ZMod (m + 3)) = -j - 1 := by ring
    have e3 : (-i - 1 : ZMod (m + 3)) + 1 = -i := by ring
    have e4 : (-j - 1 : ZMod (m + 3)) + 1 = -j := by ring
    have hij' : (-i - 1 : ZMod (m + 3)) ≠ -j - 1 := fun h => hij (by linear_combination -h)
    have h := P.edges_meet (-i - 1) (-j - 1) hij'
    rw [e3, e4] at h
    simp only [e1, e2]
    rw [segment_symm ℝ (P.vertex (-i)) (P.vertex (-i - 1)),
      segment_symm ℝ (P.vertex (-j)) (P.vertex (-j - 1)), Set.pair_comm]
    exact h

@[simp] theorem reverse_vertex {m : ℕ} (P : PrePolygon m) (j : ZMod (m + 3)) :
    P.reverse.vertex j = P.vertex (-j) := rfl

theorem reverse_edge {m : ℕ} (P : PrePolygon m) (j : ZMod (m + 3)) :
    P.reverse.edge j = P.edge (-j - 1) := by
  rw [edge, edge, reverse_vertex, reverse_vertex,
    show (-(j + 1) : ZMod (m + 3)) = -j - 1 by ring,
    show (-j - 1 : ZMod (m + 3)) + 1 = -j by ring]
  exact segment_symm ℝ _ _

@[simp] theorem reverse_carrier {m : ℕ} (P : PrePolygon m) : P.reverse.carrier = P.carrier := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
    rw [reverse_edge] at hi
    exact Set.mem_iUnion.2 ⟨_, hi⟩
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
    refine Set.mem_iUnion.2 ⟨-i - 1, ?_⟩
    rw [reverse_edge, show (-(-i - 1) - 1 : ZMod (m + 3)) = i by ring]
    exact hi

/-- **Reversing does not move an arc**, it only starts it at the other end. -/
theorem reverse_arc {m : ℕ} (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    P.reverse.arc (-a - (k : ZMod (m + 3))) k = P.arc a k := by
  ext z
  rw [mem_arc_iff, mem_arc_iff]
  constructor
  · rintro ⟨t, ht, hz⟩
    rw [reverse_edge] at hz
    refine ⟨k - t - 1, by omega, ?_⟩
    rw [show a + ((k - t - 1 : ℕ) : ZMod (m + 3))
        = -(-a - (k : ZMod (m + 3)) + (t : ZMod (m + 3))) - 1 by
      linear_combination ClosedPolygon.reverse_natCast (n := m + 3) ht]
    exact hz
  · rintro ⟨t, ht, hz⟩
    refine ⟨k - t - 1, by omega, ?_⟩
    rw [reverse_edge, show -(-a - (k : ZMod (m + 3)) + ((k - t - 1 : ℕ) : ZMod (m + 3))) - 1
        = a + (t : ZMod (m + 3)) by
      linear_combination -ClosedPolygon.reverse_natCast (n := m + 3) ht]
    exact hz

/-- **Reversing does not change the edge list either**, up to the order and the naming of each
edge's two ends — which is exactly what `Schoenflies.SameEdges` forgives. -/
theorem sameEdges_reverse_arcPieces {m : ℕ} (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    SameEdges (P.reverse.arcPieces (-a - (k : ZMod (m + 3))) k) (P.arcPieces a k) := by
  have key : (P.reverse.arcPieces (-a - (k : ZMod (m + 3))) k).map orientPiece
      = ((P.arcPieces a k).map orientPiece).reverse := by
    rw [arcPieces, arcPieces, List.map_map, List.map_map, ← List.map_reverse,
      List.range_eq_range', List.reverse_range', ← List.range_eq_range', List.map_map]
    refine List.map_congr_left fun t ht => ?_
    have htk : t < k := List.mem_range.1 ht
    have he : (0 + k - 1 - t : ℕ) = k - t - 1 := by omega
    simp only [Function.comp_apply, he, reverse_vertex]
    rw [show -(-a - (k : ZMod (m + 3)) + (t : ZMod (m + 3)))
          = a + ((k - t - 1 : ℕ) : ZMod (m + 3)) + 1 by
        linear_combination -ClosedPolygon.reverse_natCast (n := m + 3) htk,
      show -(-a - (k : ZMod (m + 3)) + (t : ZMod (m + 3)) + 1)
        = a + ((k - t - 1 : ℕ) : ZMod (m + 3)) by
        linear_combination -ClosedPolygon.reverse_natCast (n := m + 3) htk]
    exact orientPiece_swap (_, _)
  rw [SameEdges, key]
  exact List.reverse_perm _

end PrePolygon

/-! ## The realization theorem, tracking a prescribed splitting

`Schoenflies.exists_prePolygon_split` of `Schoenflies/PrePolygonArc.lean` presents the curve with
the two cut points among its vertices, with no corner condition on them. What remains is to say
*which* arc of that presentation is which of two prescribed arcs, and in which direction the
first is traversed. -/

/-- **The realization theorem, tracking a splitting into two named arcs.** -/
theorem exists_prePolygon_arcs {C A₁ A₂ : Set Plane} (hJ : IsJordanCurve C) (hP : IsPolygonal C)
    {p q : Plane} (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q)
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q) (hunion : A₁ ∪ A₂ = C)
    (hinter : A₁ ∩ A₂ = {p, q}) :
    ∃ (m : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ), P.carrier = C ∧
      1 ≤ k ∧ k ≤ m + 2 ∧ P.vertex a = p ∧ P.vertex (a + (k : ZMod (m + 3))) = q ∧
      ((P.arc a k = A₁ ∧ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = A₂) ∨
        (P.arc a k = A₂ ∧ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = A₁)) := by
  obtain ⟨m, P, a, k, hcar, hpa, hqa, hk1, hk2⟩ := exists_prePolygon_split hJ hP hp hq hpq
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

/-- **The realization of a splitting, with both the arcs and the direction fixed.** The two arcs
come out in the order they were given *and* the first is traversed from `p` to `q`; reading the
polygon backwards when it is not is what pins the direction.

This is the shape the crosscut wiring consumes, and — unlike
`Schoenflies.exists_closedPolygon_arcs_oriented` — it asks nothing of `p` and `q` beyond lying on
the curve. -/
theorem exists_prePolygon_arcs_oriented {C A₁ A₂ : Set Plane} (hJ : IsJordanCurve C)
    (hP : IsPolygonal C) {p q : Plane} (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q)
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q) (hunion : A₁ ∪ A₂ = C)
    (hinter : A₁ ∩ A₂ = {p, q}) :
    ∃ (m : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ), P.carrier = C ∧
      1 ≤ k ∧ k ≤ m + 2 ∧ P.vertex a = p ∧ P.vertex (a + (k : ZMod (m + 3))) = q ∧
      P.arc a k = A₁ ∧ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = A₂ := by
  obtain ⟨m, P, a, k, hcar, hk1, hk2, hpa, hqa, hcase⟩ :=
    exists_prePolygon_arcs hJ hP hp hq hpq hA1 hA2 hunion hinter
  rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact ⟨m, P, a, k, hcar, hk1, hk2, hpa, hqa, e1, e2⟩
  · -- The realization runs the two arcs the other way round: read it backwards.
    have hneg : ((m + 3 - k : ℕ) : ZMod (m + 3)) = -(k : ZMod (m + 3)) := by
      linear_combination zmod_add_sub_cancel (m := m) (k := k) (by omega) 0
    refine ⟨m, P.reverse, -a, m + 3 - k, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
    · rw [PrePolygon.reverse_carrier]; exact hcar
    · rw [PrePolygon.reverse_vertex, neg_neg]; exact hpa
    · rw [PrePolygon.reverse_vertex, hneg,
        show -(-a + -(k : ZMod (m + 3))) = a + (k : ZMod (m + 3)) by ring]
      exact hqa
    · have h := P.reverse_arc (a + (k : ZMod (m + 3))) (m + 3 - k)
      rw [hneg, show -(a + (k : ZMod (m + 3))) - -(k : ZMod (m + 3)) = -a by ring] at h
      rw [h]; exact e2
    · have h := P.reverse_arc a k
      rw [show m + 3 - (m + 3 - k) = k by omega, hneg,
        show -a + -(k : ZMod (m + 3)) = -a - (k : ZMod (m + 3)) by ring, h]
      exact e1

/-! ## Theorem 2.8 and Corollary 2.9 for a polygon presented with redundant vertices

`Schoenflies.IsPolygonalCrosscut` is stated for `ClosedPolygon`s, and by
`Schoenflies.ClosedPolygon.isCornerAt_vertex` that pins the two cut points to be *corners* of the
curve. Nothing in the proof of Theorem 2.8 needs the `corner` field: what it uses of `C`, `J₁`,
`J₂` is that their carriers separate the plane and that their crossing counts are the ones the
edge lists compute. `Schoenflies/PrePolygonSep.lean` supplies both for a `PrePolygon`, so the
whole chain goes through with the cut points anywhere on the curve. -/

variable {m m₁ m₂ : ℕ} {C : PrePolygon m} {J₁ : PrePolygon m₁} {J₂ : PrePolygon m₂}
  {K : List Piece} {a : ZMod (m + 3)} {k : ℕ} {y : Plane}

/-- **The setting of Theorem 2.8, with the cut points unrestricted.** Word for word
`Schoenflies.IsPolygonalCrosscut`, with `PrePolygon` for `ClosedPolygon`. -/
structure IsPrePolygonalCrosscut (C : PrePolygon m) (J₁ : PrePolygon m₁) (J₂ : PrePolygon m₂)
    (K : List Piece) (a : ZMod (m + 3)) (k : ℕ) (y : Plane) : Prop where
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
its two endpoints, and that those endpoints are the two cut vertices. -/
theorem IsPrePolygonalCrosscut.of_endpoints (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2)
    (edges₁ : SameEdges J₁.pieces (C.arcPieces a k ++ K))
    (edges₂ : SameEdges J₂.pieces (C.arcPieces (a + k) (m + 3 - k) ++ K))
    (meets : cover K ∩ C.carrier ⊆ ({C.vertex a, C.vertex (a + k)} : Set Plane))
    (notMem : y ∉ C.carrier)
    (avoids : Disjoint (cover K) (connectedComponentIn C.carrierᶜ y)) :
    IsPrePolygonalCrosscut C J₁ J₂ K a k y :=
  ⟨by omega, edges₁, edges₂, meets.trans (C.endpoints_subset_arc a hk1),
    meets.trans (C.endpoints_subset_arc' a hk2), notMem, avoids⟩

namespace IsPrePolygonalCrosscut

variable (h : IsPrePolygonalCrosscut C J₁ J₂ K a k y)
include h

/-- **The two arcs may be swapped.** -/
theorem symm : IsPrePolygonalCrosscut C J₂ J₁ K (a + k) (m + 3 - k) y := by
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
  PrePolygon.carrier_eq_of_sameEdges h.edges₁

theorem notMem_carrier₁ : y ∉ J₁.carrier :=
  PrePolygon.notMem_carrier_of_sameEdges h.edges₁ h.notMem h.notMem_cover

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

/-! ### The two cells -/

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
  exact PrePolygon.notMem_carrier_of_sameEdges h.edges₁ hwC hwK

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

/-! ### Exhaustion: the crossing counts add up -/

/-- **A point off `C ∪ P` is separated from `y` by `C` exactly when it is separated from `y` by
exactly one of `J₁, J₂`.** -/
theorem separates_xor {x : Plane} (hxC : x ∉ C.carrier) (hxK : x ∉ cover K) :
    x ∈ farRegion C.carrier y ↔
      (x ∈ farRegion J₁.carrier y ↔ ¬ x ∈ farRegion J₂.carrier y) := by
  obtain ⟨u, hu, hlevC, hlevK⟩ := h.exists_direction
  have hlev₁ := h.edges₁.hgt_ne (PrePolygon.arcPieces_append_hgt_ne hlevC hlevK)
  have hlev₂ := h.edges₂.hgt_ne (PrePolygon.arcPieces_append_hgt_ne hlevC hlevK)
  have hxJ₁ := PrePolygon.notMem_carrier_of_sameEdges h.edges₁ hxC hxK
  have hxJ₂ := PrePolygon.notMem_carrier_of_sameEdges h.edges₂ hxC hxK
  rw [← C.parity_ne_iff_mem_farRegion hu hlevC hxC h.notMem,
    ← J₁.parity_ne_iff_mem_farRegion hu hlev₁ hxJ₁ h.notMem_carrier₁,
    ← J₂.parity_ne_iff_mem_farRegion hu hlev₂ hxJ₂ h.symm.notMem_carrier₁]
  have hsx := C.parity_splitting u a h.le h.edges₁ h.edges₂ x
  have hsy := C.parity_splitting u a h.le h.edges₁ h.edges₂ y
  have key : ∀ s₁ s₂ s t₁ t₂ t : ZMod 2, s₁ + s₂ = s → t₁ + t₂ = t →
      (s ≠ t ↔ ((s₁ ≠ t₁) ↔ ¬ (s₂ ≠ t₂))) := by decide
  exact key _ _ _ _ _ _ hsx hsy

/-- **Theorem 2.8, the two cells.** -/
theorem region_eq :
    farRegion C.carrier y \ cover K = farRegion J₁.carrier y ∪ farRegion J₂.carrier y := by
  refine Set.Subset.antisymm ?_ (Set.union_subset h.cell_subset₁ h.cell_subset₂)
  rintro w ⟨hwΩ, hwK⟩
  by_cases hw₁ : w ∈ farRegion J₁.carrier y
  · exact Or.inl hw₁
  · refine Or.inr ?_
    by_contra hw₂
    exact hw₁ (((h.separates_xor hwΩ.1 hwK).1 hwΩ).2 hw₂)

/-! ### Corollary 2.9 -/

/-- **The region the crosscut enters is the component of any of its points off `C`.** -/
theorem connectedComponentIn_cover_eq {z : Plane} (hz : z ∈ cover K) (hzC : z ∉ C.carrier) :
    connectedComponentIn C.carrierᶜ z = farRegion C.carrier y :=
  h.regionPairC.left.connectedComponentIn_eq C.isSeparating_carrier
    (diff_subset_farRegion h.avoids ⟨hz, hzC⟩)

/-- **Corollary 2.9, core form.** -/
theorem inter_cover_nonempty {Q : Set Plane} {w₁ w₂ : Plane}
    (hconn : IsPreconnected Q) (hside : Q ⊆ farRegion C.carrier y)
    (hw₁ : w₁ ∈ closure Q) (hw₂ : w₂ ∈ closure Q)
    (hw₁A : w₁ ∈ C.arc a k) (hw₁B : w₁ ∉ C.arc (a + k) (m + 3 - k))
    (hw₂B : w₂ ∈ C.arc (a + k) (m + 3 - k)) (hw₂A : w₂ ∉ C.arc a k) :
    (Q ∩ cover K).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hempty
  have hsub : Q ⊆ farRegion C.carrier y \ cover K :=
    fun z hz => ⟨hside hz, fun hzK => hempty z ⟨hz, hzK⟩⟩
  obtain ⟨z, hz⟩ : Q.Nonempty := by
    by_contra hQ
    rw [Set.not_nonempty_iff_eq_empty] at hQ
    rw [hQ, closure_empty] at hw₁
    simp at hw₁
  have hzcell : z ∈ farRegion J₁.carrier y ∪ farRegion J₂.carrier y := by
    rw [← h.region_eq]; exact hsub hz
  rcases hzcell with hz₁ | hz₂
  · have hQ₁ : Q ⊆ farRegion J₁.carrier y := by
      have hcc := hconn.subset_connectedComponentIn hz hsub
      rwa [h.cell_isComponent₁ z hz₁] at hcc
    have hmem : w₂ ∈ closure (farRegion J₁.carrier y) ∩ C.carrier :=
      ⟨closure_mono hQ₁ hw₂, C.arc_subset_carrier _ _ hw₂B⟩
    rw [h.closure_cell_inter₁] at hmem
    exact hw₂A hmem
  · have hQ₂ : Q ⊆ farRegion J₂.carrier y := by
      have hcc := hconn.subset_connectedComponentIn hz hsub
      rwa [h.cell_isComponent₂ z hz₂] at hcc
    have hmem : w₁ ∈ closure (farRegion J₂.carrier y) ∩ C.carrier :=
      ⟨closure_mono hQ₂ hw₁, C.arc_subset_carrier _ _ hw₁A⟩
    rw [h.closure_cell_inter₂] at hmem
    exact hw₁B hmem

/-- **Corollary 2.9 for a second crosscut presented as a simple arc.** -/
theorem arc_inter_cover_nonempty {Q : Set Plane} {w₁ w₂ : Plane}
    (hQ : IsArcBetween Q w₁ w₂) (hside : Q \ {w₁, w₂} ⊆ farRegion C.carrier y)
    (hw₁A : w₁ ∈ C.arc a k) (hw₁B : w₁ ∉ C.arc (a + k) (m + 3 - k))
    (hw₂B : w₂ ∈ C.arc (a + k) (m + 3 - k)) (hw₂A : w₂ ∉ C.arc a k) :
    (Q ∩ cover K).Nonempty := by
  obtain ⟨z, hzQ, hzK⟩ := h.inter_cover_nonempty hQ.isPreconnected_diff hside
    hQ.left_mem_closure_diff hQ.right_mem_closure_diff hw₁A hw₁B hw₂B hw₂A
  exact ⟨z, hzQ.1, hzK⟩

/-- **Corollary 2.9 in the shape a plane-graph argument produces it.** -/
theorem alternating_inter_nonempty {A B Q : Set Plane} {p q w₁ w₂ : Plane}
    (hA : C.arc a k = A) (hB : C.arc (a + k) (m + 3 - k) = B)
    (hAB : A ∩ B = ({p, q} : Set Plane))
    (hQ : IsArcBetween Q w₁ w₂) (hside : Q \ {w₁, w₂} ⊆ farRegion C.carrier y)
    (hw₁ : w₁ ∈ A \ ({p, q} : Set Plane)) (hw₂ : w₂ ∈ B \ ({p, q} : Set Plane)) :
    (Q ∩ cover K).Nonempty := by
  refine h.arc_inter_cover_nonempty hQ hside (hA ▸ hw₁.1) ?_ (hB ▸ hw₂.1) ?_
  · rw [hB]; exact fun hmem => hw₁.2 (hAB ▸ Set.mem_inter hw₁.1 hmem)
  · rw [hA]; exact fun hmem => hw₂.2 (hAB ▸ Set.mem_inter hmem hw₂.1)

/-- **Corollary 2.9 with "the same side" read as "the same connected component".** -/
theorem alternating_inter_nonempty_of_same_side {A B Q : Set Plane} {p q w₁ w₂ z : Plane}
    (hz : z ∈ cover K) (hzC : z ∉ C.carrier)
    (hA : C.arc a k = A) (hB : C.arc (a + k) (m + 3 - k) = B)
    (hAB : A ∩ B = ({p, q} : Set Plane))
    (hQ : IsArcBetween Q w₁ w₂)
    (hside : Q \ {w₁, w₂} ⊆ connectedComponentIn C.carrierᶜ z)
    (hw₁ : w₁ ∈ A \ ({p, q} : Set Plane)) (hw₂ : w₂ ∈ B \ ({p, q} : Set Plane)) :
    (Q ∩ cover K).Nonempty :=
  h.alternating_inter_nonempty hA hB hAB hQ
    (hside.trans (h.connectedComponentIn_cover_eq hz hzC).subset) hw₁ hw₂

end IsPrePolygonalCrosscut

end Schoenflies

namespace Graph

open Schoenflies

variable {β : Type*} {G : Graph Plane β} {x y : Fin 3 → Plane} {e : Fin 3 → Fin 3 → β}
variable {drawing : β → ℝ → Plane} {s : Fin 3} {R : Set Plane}

/-! ## The six-cycle and one remaining edge, as a crosscut

`Graph.IsHexCrosscut` of `Schoenflies/Graph/K33Planar.lean` is the same statement with
`Schoenflies.ClosedPolygon` for `Schoenflies.PrePolygon`; the change is what removes the corner
condition on the two cut points, which is the whole of the remaining gap. -/

/-- **The six-cycle and one remaining edge, realized as a polygonal crosscut**, with the two cut
points wherever the drawing put them. -/
def IsPreHexCrosscut (drawing : β → ℝ → Plane) (e : Fin 3 → Fin 3 → β) (s : Fin 3) : Prop :=
  ∃ (m m₁ m₂ : ℕ) (C : PrePolygon m) (J₁ : PrePolygon m₁) (J₂ : PrePolygon m₂)
    (K : List Piece) (a : ZMod (m + 3)) (k : ℕ) (yref : Plane),
      C.carrier = hexSet drawing e ∧
      C.arc a k = edgesCover drawing (arcA e s) ∧
      C.arc (a + k) (m + 3 - k) = edgesCover drawing (arcB e s) ∧
      cover K = edgeArc drawing (e s (s + 1)) ∧
      IsPrePolygonalCrosscut C J₁ J₂ K a k yref

namespace IsK33Config

/-- **The crosscut exists for any polygonal drawing.** The six-cycle is
realized as a `Schoenflies.PrePolygon` cut at the two ends of the remaining edge — possible
because a `PrePolygon` may have a vertex wherever one likes — and the two closed curves the
remaining edge forms with the two halves are then *built* from that realization and from one
presentation of the remaining edge, rather than found independently. That is what makes the three
edge lists agree, and it is why no matching lemma, and hence no general position, is needed. -/
theorem isPreHexCrosscut (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc drawing f)) (s : Fin 3) :
    IsPreHexCrosscut drawing e s := by
  have hpq : x s ≠ y (s + 1) := h.x_ne_y s (s + 1)
  have hA1 := h.arcA_isArcBetween hd s
  have hA2 := h.arcB_isArcBetween hd s
  have hCh := hd.edge_isArcBetween (h.isLink s (s + 1))
  have hinterA := h.chord_inter_arcA hd s
  have hinterB := h.chord_inter_arcB hd s
  have hPch : IsPolygonal (edgeArc drawing (e s (s + 1))) :=
    hpoly _ (h.isLink s (s + 1)).edge_mem
  have hP1 : IsPolygonal (edgesCover drawing (arcA e s) ∪ edgeArc drawing (e s (s + 1))) :=
    (h.isPolygonal_arcA hd hpoly s).union hPch ⟨x s, hA1.left_mem, hCh.left_mem⟩
  have hJ1 : IsJordanCurve (edgesCover drawing (arcA e s) ∪ edgeArc drawing (e s (s + 1))) :=
    IsJordanCurve.of_two_arcs hA1 hCh.reverse fun z hz1 hz2 => by
      have hz : z ∈ ({x s, y (s + 1)} : Set Plane) := hinterA ▸ ⟨hz1, hz2⟩
      simpa using hz
  -- The six-cycle, cut at the two ends of the remaining edge.
  obtain ⟨m, C, a, k, hCcar, hk1, hk2, hCa, hCak, hCarc1, hCarc2⟩ :=
    exists_prePolygon_arcs_oriented (h.hexagon_isJordanCurve hd) (h.isPolygonal_hexSet hd hpoly)
      (h.x_mem_hexSet hd s) (h.y_mem_hexSet hd (s + 1)) hpq hA1 hA2
      (arcs_union (drawing := drawing) (e := e) s) (h.arcs_inter hd s)
  -- The remaining edge, as the second arc of the curve it forms with the first half.
  obtain ⟨m₁, D, b, l, -, hl1, hl2, hDb, hDbl, hDarc1, hDarc2⟩ :=
    exists_prePolygon_arcs_oriented hJ1 hP1 (Or.inl hA1.left_mem) (Or.inl hA1.right_mem) hpq
      hA1 hCh rfl hinterA
  set c : ZMod (m₁ + 3) := b + (l : ZMod (m₁ + 3)) with hc
  set r : ℕ := m₁ + 3 - l with hr
  have hwrapD : c + (r : ZMod (m₁ + 3)) = b := zmod_add_sub_cancel (by omega) b
  have hDc : D.vertex c = y (s + 1) := hDbl
  have hDcr : D.vertex (c + (r : ZMod (m₁ + 3))) = x s := by rw [hwrapD]; exact hDb
  have hKcover : cover (D.arcPieces c r) = edgeArc drawing (e s (s + 1)) := hDarc2
  have hKinter : C.arc a k ∩ D.arc c r
      = ({C.vertex a, C.vertex (a + (k : ZMod (m + 3)))} : Set Plane) := by
    rw [hCarc1, hDarc2, hCa, hCak]; exact hinterA
  -- The first spliced curve: the first half of the six-cycle, then the remaining edge.
  obtain ⟨n₁, J₁, hJ₁p⟩ := PrePolygon.exists_splice C D hk1 hk2 (by omega) (by omega)
    (by rw [hDc, hCak]) (by rw [hDcr, hCa]) hKinter
  -- The second spliced curve, with the remaining edge traversed the other way.
  have hwrapC : a + (k : ZMod (m + 3)) + ((m + 3 - k : ℕ) : ZMod (m + 3)) = a :=
    zmod_add_sub_cancel (by omega) a
  set c' : ZMod (m₁ + 3) := -c - (r : ZMod (m₁ + 3)) with hc'
  have hDrev1 : D.reverse.vertex c' = x s := by
    rw [PrePolygon.reverse_vertex, hc', show -(-c - (r : ZMod (m₁ + 3))) = c + (r : ZMod (m₁ + 3))
      by ring]
    exact hDcr
  have hDrev2 : D.reverse.vertex (c' + (r : ZMod (m₁ + 3))) = y (s + 1) := by
    rw [PrePolygon.reverse_vertex, hc',
      show -(-c - (r : ZMod (m₁ + 3)) + (r : ZMod (m₁ + 3))) = c by ring]
    exact hDc
  have hKinter' : C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∩ D.reverse.arc c' r
      = ({C.vertex (a + (k : ZMod (m + 3))),
          C.vertex (a + (k : ZMod (m + 3)) + ((m + 3 - k : ℕ) : ZMod (m + 3)))} : Set Plane) := by
    rw [hCarc2, hc', D.reverse_arc c r, hDarc2, hwrapC, hCa, hCak, Set.pair_comm]
    exact hinterB
  obtain ⟨n₂, J₂, hJ₂p⟩ := PrePolygon.exists_splice C D.reverse (a := a + (k : ZMod (m + 3)))
    (k := m + 3 - k) (b := c') (l := r) (by omega) (by omega) (by omega) (by omega)
    (by rw [hDrev1, hwrapC, hCa]) (by rw [hDrev2, hCak]) hKinter'
  -- The reference point, and the two "meets" clauses.
  have hsep : IsSeparating (hexSet drawing e) := hCcar ▸ C.isSeparating_carrier
  obtain ⟨yref, hyref, hdisj⟩ := h.exists_reference_point hd hsep s
  refine ⟨m, n₁, n₂, C, J₁, J₂, D.arcPieces c r, a, k, yref, hCcar, hCarc1, hCarc2, hKcover,
    ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hJ₁p]
  · rw [hJ₂p]
    exact SameEdges.append (SameEdges.refl _) (D.sameEdges_reverse_arcPieces c r)
  · rw [hKcover, hCcar, hCarc1, h.chord_inter_hexSet hd s]
    exact h.endpoints_subset_arcA hd s
  · rw [hKcover, hCcar, hCarc2, h.chord_inter_hexSet hd s]
    exact h.endpoints_subset_arcB hd s
  · rw [hCcar]; exact hyref
  · rw [hKcover, hCcar]; exact hdisj

/-! ### The contradiction -/

/-- **The two remaining edges indexed by `s` and `s + 1` cannot lie in one region.** Their four
ends alternate around the six-cycle, so `cor:alternating-crosscuts` makes them meet; but distinct
edges of a plane graph meet only at shared vertices, and these two share none. -/
theorem false_of_isPreHexCrosscut (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hcross : IsPreHexCrosscut drawing e s) (hsep : IsSeparating (hexSet drawing e))
    (hR : IsRegionOf (hexSet drawing e) R)
    (h1 : openArc (drawing (e s (s + 1))) ⊆ R)
    (h2 : openArc (drawing (e (s + 1) (s + 1 + 1))) ⊆ R) : False := by
  obtain ⟨m, m₁, m₂, C, J₁, J₂, K, a, k, yref, hcar, hA, hB, hK, hcc⟩ := hcross
  obtain ⟨z, hz⟩ := chord_openArc_nonempty (drawing := drawing) (e := e) s
  have hzK : z ∈ cover K := by rw [hK]; exact h.chord_openArc_subset_edgeArc hd s hz
  have hzC : z ∉ C.carrier := by rw [hcar]; exact h.chord_openArc_subset_compl hd s hz
  have hzR : z ∈ R := h1 hz
  have hside : edgeArc drawing (e (s + 1) (s + 1 + 1)) \ ({x (s + 1), y (s + 1 + 1)} : Set Plane)
      ⊆ connectedComponentIn C.carrierᶜ z := by
    rw [hcar, hR.connectedComponentIn_eq hsep hzR, ← h.chord_openArc_eq hd (s + 1)]
    exact h2
  obtain ⟨w, hw₁, hw₂⟩ := hcc.alternating_inter_nonempty_of_same_side hzK hzC hA hB
    (h.arcs_inter hd s) (hd.edge_isArcBetween (h.isLink (s + 1) (s + 1 + 1))) hside
    (h.x_succ_mem_arcA hd s) (h.y_succ_mem_arcB hd s)
  have hs1 : ∀ s : Fin 3, s + 1 ≠ s := by decide
  have hdis := h.chords_disjoint hd (hs1 s)
  rw [Set.eq_empty_iff_forall_notMem] at hdis
  exact hdis w ⟨hw₁, by rwa [hK] at hw₂⟩

/-- **`lem:k33` for a drawing that is already polygonal, with nothing assumed.** -/
theorem false_of_polygonal (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc drawing f)) : False := by
  have hsep : IsSeparating (hexSet drawing e) := by
    obtain ⟨_, _, _, C, _, _, _, _, _, _, hcar, _⟩ := h.isPreHexCrosscut hd hpoly 0
    exact hcar ▸ C.isSeparating_carrier
  obtain ⟨s, t, hst, R, hR, h1, h2⟩ := h.exists_two_chords_same_region hd hsep
  have hpair : ∀ s t : Fin 3, s ≠ t → t = s + 1 ∨ s = t + 1 := by decide
  rcases hpair s t hst with rfl | rfl
  · exact h.false_of_isPreHexCrosscut hd (h.isPreHexCrosscut hd hpoly s) hsep hR h1 h2
  · exact h.false_of_isPreHexCrosscut hd (h.isPreHexCrosscut hd hpoly t) hsep hR h2 h1

/-- **Lemma 3.10 (nonplanarity of `K(3,3)`), with no hypothesis left.** A finite graph carrying a
copy of `K(3,3)` has no plane drawing.

`lem:polygonal-redrawing` replaces an arbitrary drawing by a polygonal one on the same graph and
the same vertices; the contradiction is then `false_of_polygonal`. This is
`Graph.IsK33Config.not_isDrawing` of `Schoenflies/Graph/K33Planar.lean` with its realization
hypothesis discharged, and `Graph.IsK33Config.not_isDrawing_of_bendable` of
`Schoenflies/Graph/K33Closed.lean` with `Graph.Bendable` discharged: no drawing has to be bent,
because the crosscut no longer needs the six vertices to be corners. -/
theorem not_exists_isDrawing [G.Finite] (h : IsK33Config G x y e) :
    ¬ ∃ dr : β → ℝ → Plane, IsDrawing G dr := by
  rintro ⟨dr, hdr⟩
  obtain ⟨dr', hdr', hpoly'⟩ := polygonal_redrawing G dr hdr
  exact h.false_of_polygonal hdr' hpoly'

end IsK33Config

/-- **`lem:k33` for nine arcs**: no nine arcs in the plane meet only where a
`K(3,3)` forces them to. -/
theorem IsArcK33.elim {P : Fin 3 → Fin 3 → Set Plane} (h : IsArcK33 x y P) : False :=
  h.isK33Config.not_exists_isDrawing ⟨h.arcDrawing, h.isDrawing⟩

/-- **Corollary 3.11 (subdivisions of `K(3,3)`).** No subdivision of `K(3,3)`
has a plane drawing. -/
theorem IsK33Subdivision.elim {H : Graph Plane β} {W : Fin 3 → Fin 3 → List β}
    (hd : IsDrawing H drawing) (h : IsK33Subdivision H x y W) : False :=
  (h.isArcK33 hd).elim

/-- **The headline: `K(3,3)` has no plane drawing.** Stated for the concrete graph
`Graph.k33Graph x y`, whose nine edges are the index pairs, with nothing assumed beyond the six
points being six distinct points of the plane. -/
theorem k33Graph_not_exists_isDrawing (x y : Fin 3 → Plane) (hx : Function.Injective x)
    (hy : Function.Injective y) (hxy : ∀ i j, x i ≠ y j) :
    ¬ ∃ dr : Fin 3 × Fin 3 → ℝ → Plane, IsDrawing (k33Graph x y) dr :=
  IsK33Config.not_exists_isDrawing ⟨k33Graph_isLink x y, hx, hy, hxy⟩

end Graph
