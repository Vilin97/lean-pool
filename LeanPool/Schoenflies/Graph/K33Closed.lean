/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Realization
public import LeanPool.Schoenflies.Graph.K33Planar

/-!
# Discharging the realization hypothesis of `lem:k33`

`Schoenflies/Graph/K33Planar.lean` proves the nonplanarity of `K(3,3)` from one assumption,
`Graph.IsHexRealization`: that the six-cycle, the two arcs the chord cuts it into, and the two
closed curves the chord forms with them are all presented by cyclic vertex lists.
`Schoenflies/Realization.lean` now supplies the presentations. This module wires the two
together.

## Blueprint

* `Schoenflies.exists_poly_anchored`, `Schoenflies.IsPolygonal.union`,
  `Graph.IsDrawing.isPolygonal_edgesCover` — §1: a polygonal set is the carrier of a vertex list
  running between any two of its points, so two polygonal sets that meet have a polygonal union,
  and a walk of a polygonal plane graph draws a polygonal set.
* `Schoenflies.ClosedPolygon.reverse` — a closed polygon read backwards.
* `Schoenflies.ClosedPolygon.arc_vertex_eq`, `…arcPieces_eq` — **the decomposition of an arc is
  the arc's own**: two closed polygons that share an arc, starting at the same vertex, run
  through the same vertices along it. This is what makes the three presentations below fit
  together into one crosscut.
* `Schoenflies.exists_closedPolygon_arcs_oriented` — the realization of a splitting with the
  first arc's *direction* fixed as well, so that two realizations of one arc can be compared.
* `Graph.IsK33Config.isPolygonal_hexSet`, `…chord_inter_arcA`, `…chord_inter_arcB` — the three
  curves the crosscut is built from, as polygonal Jordan curves.
* `Graph.IsHexGeneric` — the general-position hypothesis that survives: at each of the two cut
  points, the six-cycle and both spliced curves turn.
* `Graph.IsK33Config.isHexRealization` — `Graph.IsHexRealization`, discharged from it. **This is
  the theorem this module exists for.**
* `Graph.Bendable`, `Graph.IsK33Config.false_of_hexGeneric`, `…not_isDrawing_of_bendable`,
  `Graph.IsArcK33.false_of_bendable`, `Graph.IsK33Subdivision.false_of_bendable`,
  `Graph.k33Graph_not_isDrawing` — `lem:k33` and `cor:k33-subdivision` with `IsHexRealization`
  replaced by `IsHexGeneric`.

## What is still assumed, and why — READ THIS BEFORE USING THE THEOREMS BELOW

**Milestone H8 is not closed here.** `Graph.IsHexRealization` is gone, but a strictly smaller
hypothesis has taken its place, and it is not discharged.

`Schoenflies.ClosedPolygon` forbids a vertex at which the curve runs straight through, and
`Schoenflies.ClosedPolygon.isCornerAt_vertex` says that this is not a defect of the proofs:
*every* vertex of *every* realization is a corner of the curve. A crosscut whose ends are cut
points of `C` therefore forces those ends to be corners — of `C`, and of both curves the
crosscut forms with the two arcs. `Graph.IsHexGeneric` says exactly that and nothing more, and
by the two corner theorems it cannot be weakened while the crosscut is presented as a
`Schoenflies.IsPolygonalCrosscut`.

For a drawn `K(3,3)` it is the statement that at each of the six vertices the three edges leave
along three pairwise non-collinear germs. A polygonal drawing need not have that: two of the
three edges at a vertex may leave along exactly opposite rays, which is perfectly compatible
with the drawing condition. The remaining gap is therefore a *bending* lemma — every polygonal
drawing can be redrawn so that no two edges at a vertex are collinear there — and it is
genuinely about changing the drawing, not about presentations. `Graph.Bendable` is that
statement in the shape the theorems below consume; nothing here proves it.
-/

@[expose] public section

open Metric Set unitInterval
open scoped Graph

namespace Schoenflies

/-! ## A polygonal set is a vertex list between any two of its points

`Schoenflies.IsPolygonal` is "the carrier of a vertex list", and a vertex list carries a *path*,
so the predicate is not closed under arbitrary finite unions — two disjoint segments are not the
carrier of any one list. It is closed under unions that meet, and the way to see that is to move
the ends of the list: a list can be made to start and end wherever one likes on its own carrier,
by running out and back. -/

/-! ## A closed polygon read backwards

A realization of a splitting names its two arcs *in a direction*, and two realizations of one
arc need not agree on it. Reversing the cyclic order is what reconciles them. -/

namespace ClosedPolygon

variable {m : ℕ}

/-- **The same closed polygon, traversed the other way.** -/
def reverse (P : ClosedPolygon m) : ClosedPolygon m where
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
  corner i := by
    have e1 : (-(i - 1) : ZMod (m + 3)) = -i + 1 := by ring
    have e2 : (-(i + 1) : ZMod (m + 3)) = -i - 1 := by ring
    simp only [e1, e2]
    rw [Plane.det_comm]
    exact fun h => P.corner (-i) (by linear_combination -h)

@[simp] theorem reverse_vertex (P : ClosedPolygon m) (j : ZMod (m + 3)) :
    P.reverse.vertex j = P.vertex (-j) := rfl

theorem reverse_edge (P : ClosedPolygon m) (j : ZMod (m + 3)) :
    P.reverse.edge j = P.edge (-j - 1) := by
  rw [edge, edge, reverse_vertex, reverse_vertex,
    show (-(j + 1) : ZMod (m + 3)) = -j - 1 by ring,
    show (-j - 1 : ZMod (m + 3)) + 1 = -j by ring]
  exact segment_symm ℝ _ _

@[simp] theorem reverse_carrier (P : ClosedPolygon m) : P.reverse.carrier = P.carrier := by
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

/-- The `t`-th edge of the reversed arc is the `k - 1 - t`-th of the original: the same edges,
listed backwards. -/
theorem reverse_natCast {n k t : ℕ} (ht : t < k) :
    ((k - t - 1 : ℕ) : ZMod n) + (t : ZMod n) + 1 = (k : ZMod n) := by
  have h : (k - t - 1) + t + 1 = k := by omega
  have hc := congrArg (fun j : ℕ => (j : ZMod n)) h
  push_cast at hc
  linear_combination hc

/-- **Reversing does not move an arc**, it only starts it at the other end. -/
theorem reverse_arc (P : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    P.reverse.arc (-a - (k : ZMod (m + 3))) k = P.arc a k := by
  ext z
  rw [mem_arc_iff, mem_arc_iff]
  constructor
  · rintro ⟨t, ht, hz⟩
    rw [reverse_edge] at hz
    refine ⟨k - t - 1, by omega, ?_⟩
    rw [show a + ((k - t - 1 : ℕ) : ZMod (m + 3))
        = -(-a - (k : ZMod (m + 3)) + (t : ZMod (m + 3))) - 1 by
      linear_combination reverse_natCast (n := m + 3) ht]
    exact hz
  · rintro ⟨t, ht, hz⟩
    refine ⟨k - t - 1, by omega, ?_⟩
    rw [reverse_edge, show -(-a - (k : ZMod (m + 3)) + ((k - t - 1 : ℕ) : ZMod (m + 3))) - 1
        = a + (t : ZMod (m + 3)) by linear_combination -reverse_natCast (n := m + 3) ht]
    exact hz

/-- **Reversing does not change the edge list either**, up to the order and the naming of each
edge's two ends — which is exactly what `Schoenflies.SameEdges` forgives. -/
theorem sameEdges_reverse_arcPieces (P : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) :
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
        linear_combination -reverse_natCast (n := m + 3) htk,
      show -(-a - (k : ZMod (m + 3)) + (t : ZMod (m + 3)) + 1)
        = a + ((k - t - 1 : ℕ) : ZMod (m + 3)) by
        linear_combination -reverse_natCast (n := m + 3) htk]
    exact orientPiece_swap (_, _)
  rw [SameEdges, key]
  exact List.reverse_perm _

/-! ## The decomposition of an arc is the arc's own

`Graph.IsHexRealization` asks for three closed polygons that agree on the arcs they share. They
are found independently, and nothing so far says they agree — until this: two closed polygons
carrying the same arc, and starting it at the same vertex, run through the same vertices along
it. The proof walks the arc: the first edges of the two are two segments leaving one point along
one ray, so one contains the other, and the shorter one's far end would be a vertex of its own
polygon interior to an edge of the other — which `corner` forbids. -/

/-- A numeral strictly between `0` and the modulus is not `0` in the cyclic index. -/
theorem natCast_ne_zero_of_lt {m t : ℕ} (ht1 : 0 < t) (ht2 : t < m + 3) :
    ((t : ℕ) : ZMod (m + 3)) ≠ 0 := by
  intro h
  have h0 : ((t : ℕ) : ZMod (m + 3)) = ((0 : ℕ) : ZMod (m + 3)) := by simpa using h
  have := natCast_inj (m := m) ht2 (by omega) h0
  omega

/-- **The first vertex of an arc lies on none of its later edges** — a step index below the
modulus reaches neither the edge leaving that vertex nor the one arriving at it. -/
theorem vertex_notMem_edge_natCast (P : ClosedPolygon m) (a : ZMod (m + 3)) {t : ℕ}
    (ht1 : 0 < t) (ht2 : t < m + 2) : P.vertex a ∉ P.edge (a + (t : ZMod (m + 3))) := by
  refine vertex_notMem_edge (fun h => ?_) (fun h => ?_)
  · exact natCast_ne_zero_of_lt (t := t + 1) (m := m) (by omega) (by omega)
      (by push_cast; linear_combination h)
  · exact natCast_ne_zero_of_lt (m := m) ht1 (by omega) (by linear_combination h)

/-- **Around a point that no later edge of the arc reaches, the arc is its first edge alone.** -/
theorem exists_ball_arc_subset_edge (P : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) {w : Plane}
    (hw : ∀ t : ℕ, 0 < t → t < k → w ∉ P.edge (a + (t : ZMod (m + 3)))) :
    ∃ r > 0, ball w r ∩ P.arc a k ⊆ P.edge a := by
  obtain ⟨r, hr, hball⟩ := exists_pos_forall_of_finite
    (S := {t : ℕ | 0 < t ∧ t < k})
    ((Set.finite_Icc 0 k).subset fun t ht => ⟨Nat.zero_le t, ht.2.le⟩)
    (P := fun t ε => ∀ y ∈ ball w ε, y ∉ P.edge (a + (t : ZMod (m + 3))))
    (fun _ _ _ _ hδε hQ y hy => hQ y (ball_subset_ball hδε hy))
    (fun t ht => by
      obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1
        (isCompact_segment _ _).isClosed.isOpen_compl w (hw t ht.1 ht.2)
      exact ⟨ρ, hρ, fun y hy => hsub hy⟩)
  refine ⟨r, hr, ?_⟩
  rintro z ⟨hzb, hzA⟩
  obtain ⟨t, ht, hzt⟩ := mem_arc_iff.1 hzA
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · simpa using hzt
  · exact absurd hzt (hball t ⟨htpos, ht⟩ z hzb)

/-- Bounds a step along two directions inside one ball. -/
theorem exists_step_lt {ρ : ℝ} (hρ : 0 < ρ) (u v : Plane) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ s * ‖u‖ < ρ ∧ s * ‖v‖ < ρ := by
  refine ⟨min 1 (ρ / (2 * (‖u‖ + ‖v‖ + 1))), lt_min one_pos (by positivity), min_le_left _ _,
    ?_, ?_⟩
  · calc min 1 (ρ / (2 * (‖u‖ + ‖v‖ + 1))) * ‖u‖
        ≤ (ρ / (2 * (‖u‖ + ‖v‖ + 1))) * ‖u‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg u)
      _ < ρ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg u, norm_nonneg v]
  · calc min 1 (ρ / (2 * (‖u‖ + ‖v‖ + 1))) * ‖v‖
        ≤ (ρ / (2 * (‖u‖ + ‖v‖ + 1))) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg v)
      _ < ρ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg u, norm_nonneg v]

/-- **Two segments leaving one point and agreeing near it leave along the same ray.** -/
theorem exists_pos_smul_of_ball_subset {v₀ v₁ u₁ : Plane} {r : ℝ} (hr : 0 < r) (hv : v₁ ≠ v₀)
    (hsub : segment ℝ v₀ v₁ ∩ ball v₀ r ⊆ segment ℝ v₀ u₁) :
    ∃ c : ℝ, 0 < c ∧ v₁ - v₀ = c • (u₁ - v₀) := by
  have hdne : v₁ - v₀ ≠ 0 := sub_ne_zero.2 hv
  obtain ⟨t, htpos, htle, ht, -⟩ := exists_step_lt hr (v₁ - v₀) (v₁ - v₀)
  have hzs : v₀ + t • (v₁ - v₀) ∈ segment ℝ v₀ v₁ := by
    rw [segment_eq_image' ℝ v₀ v₁]; exact ⟨t, ⟨htpos.le, htle⟩, rfl⟩
  have hzb : v₀ + t • (v₁ - v₀) ∈ ball v₀ r := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos htpos]
    exact ht
  have hmem := hsub ⟨hzs, hzb⟩
  rw [segment_eq_image' ℝ v₀ u₁] at hmem
  obtain ⟨θ, hθ, hθe⟩ := hmem
  simp only at hθe
  have hkey : t • (v₁ - v₀) = θ • (u₁ - v₀) := by
    linear_combination (norm := module) -hθe
  have hθpos : 0 < θ := by
    rcases lt_or_eq_of_le hθ.1 with h | h
    · exact h
    · exfalso
      rw [← h, zero_smul] at hkey
      exact hdne ((smul_eq_zero.1 hkey).resolve_left htpos.ne')
  refine ⟨θ / t, by positivity, ?_⟩
  have hrw : (θ / t) • (u₁ - v₀) = (1 / t) • (θ • (u₁ - v₀)) := by
    rw [smul_smul]; congr 1; field_simp
  rw [hrw, ← hkey, smul_smul, one_div, inv_mul_cancel₀ htpos.ne', one_smul]

/-- **A vertex of one polygon is never interior to the other's first edge.** Either the shared
arc is that single edge — and then the far end of the edge cannot be strictly inside it — or the
other polygon has two edges at the vertex, both lying near it inside one straight segment, which
is what its `corner` field forbids. -/
theorem notMem_openSegment_first_edge {m m' : ℕ} (P : ClosedPolygon m) (Q : ClosedPolygon m')
    (a : ZMod (m + 3)) (b : ZMod (m' + 3)) {k l : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2)
    (hl1 : 1 ≤ l) (harc : P.arc a k = Q.arc b l) (hstart : P.vertex a = Q.vertex b) :
    Q.vertex (b + 1) ∉ openSegment ℝ (P.vertex a) (P.vertex (a + 1)) := by
  intro hw
  have hedgeP : P.edge a ⊆ P.arc a k := fun z hz =>
    mem_arc_iff.2 ⟨0, by omega, by simpa using hz⟩
  rcases eq_or_lt_of_le hl1 with hl | hl
  · -- `l = 1`: the arc is `Q`'s single edge, which *ends* at the point in question.
    subst hl
    have hQarc : Q.arc b 1 = segment ℝ (P.vertex a) (Q.vertex (b + 1)) := by
      refine Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
      · obtain ⟨t, ht, hzt⟩ := mem_arc_iff.1 hz
        have ht0 : t = 0 := by omega
        subst ht0
        rw [hstart]
        simpa [edge] using hzt
      · refine mem_arc_iff.2 ⟨0, by omega, ?_⟩
        rw [hstart] at hz
        simpa [edge] using hz
    have hmem : P.vertex (a + 1) ∈ segment ℝ (P.vertex a) (Q.vertex (b + 1)) := by
      rw [← hQarc, ← harc]
      exact hedgeP (right_mem_segment ℝ _ _)
    -- Reading both memberships as parameters: `μ θ = 1` with `θ < 1` and `μ ≤ 1`.
    rw [openSegment_eq_image' ℝ] at hw
    rw [segment_eq_image' ℝ] at hmem
    obtain ⟨θ, hθ, hθe⟩ := hw
    obtain ⟨μ, hμ, hμe⟩ := hmem
    simp only at hθe hμe
    have hne : P.vertex (a + 1) - P.vertex a ≠ 0 := sub_ne_zero.2 (P.vertex_ne a).symm
    have hkey : (1 - μ * θ) • (P.vertex (a + 1) - P.vertex a) = 0 := by
      linear_combination (norm := module) -hμe - μ • hθe
    rcases smul_eq_zero.1 hkey with h | h
    · nlinarith [hθ.1, hθ.2, hμ.1, hμ.2]
    · exact hne h
  · -- `l ≥ 2`: `Q` turns at the point, but near it the arc is one straight segment.
    obtain ⟨ρ, hρ, hball⟩ := P.exists_ball_arc_subset_edge a k (w := Q.vertex (b + 1))
      fun t ht1 ht2 => notMem_edge_of_mem_openSegment
        (fun h => natCast_ne_zero_of_lt (m := m) ht1 (by omega) (by linear_combination h)) hw
    obtain ⟨s, hs0, hs1, hsu, hsv⟩ :=
      exists_step_lt hρ (Q.vertex b - Q.vertex (b + 1)) (Q.vertex (b + 2) - Q.vertex (b + 1))
    have hstep : ∀ y : Plane, s * ‖y - Q.vertex (b + 1)‖ < ρ →
        Q.vertex (b + 1) + s • (y - Q.vertex (b + 1)) ∈ ball (Q.vertex (b + 1)) ρ := by
      intro y hy
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hs0]
      exact hy
    have hseg : ∀ y : Plane,
        Q.vertex (b + 1) + s • (y - Q.vertex (b + 1)) ∈ segment ℝ (Q.vertex (b + 1)) y :=
      fun y => by rw [segment_eq_image' ℝ]; exact ⟨s, ⟨hs0.le, hs1⟩, rfl⟩
    have hz₁ : Q.vertex (b + 1) + s • (Q.vertex b - Q.vertex (b + 1)) ∈ P.edge a := by
      refine hball ⟨hstep _ hsu, ?_⟩
      rw [harc]
      refine mem_arc_iff.2 ⟨0, by omega, ?_⟩
      rw [show b + ((0 : ℕ) : ZMod (m' + 3)) = b by simp, edge,
        segment_symm ℝ (Q.vertex b) (Q.vertex (b + 1))]
      exact hseg (Q.vertex b)
    have hz₂ : Q.vertex (b + 1) + s • (Q.vertex (b + 2) - Q.vertex (b + 1)) ∈ P.edge a := by
      refine hball ⟨hstep _ hsv, ?_⟩
      rw [harc]
      refine mem_arc_iff.2 ⟨1, by omega, ?_⟩
      rw [show b + ((1 : ℕ) : ZMod (m' + 3)) = b + 1 by push_cast; ring, edge,
        show b + 1 + 1 = b + 2 by ring]
      exact hseg (Q.vertex (b + 2))
    have hwmem : Q.vertex (b + 1) ∈ P.edge a := openSegment_subset_segment ℝ _ _ hw
    have hdet := det_eq_zero_of_mem_segment hz₁ hz₂ hwmem
    rw [add_sub_cancel_left, add_sub_cancel_left, Plane.det_smul_left, Plane.det_smul_right]
      at hdet
    refine Q.corner (b + 1) ?_
    rw [show b + 1 - 1 = b by ring, show b + 1 + 1 = b + 2 by ring]
    rcases mul_eq_zero.1 hdet with h | h
    · exact absurd h hs0.ne'
    · rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' hs0.ne'
      · exact h'

/-- Stepping the cyclic index by a positive numeral. -/
theorem natCast_pred_succ {n t : ℕ} (ht : 0 < t) : ((t - 1 : ℕ) : ZMod n) + 1 = (t : ZMod n) := by
  have h : (t - 1) + 1 = t := by omega
  have hc := congrArg (fun j : ℕ => (j : ZMod n)) h
  push_cast at hc
  linear_combination hc

/-- **An arc is its first edge together with the arc that leaves the next vertex.** -/
theorem arc_succ (P : ClosedPolygon m) (a : ZMod (m + 3)) {k : ℕ} (hk : 1 ≤ k) :
    P.arc a k = P.edge a ∪ P.arc (a + 1) (k - 1) := by
  ext z
  rw [mem_arc_iff, Set.mem_union, mem_arc_iff]
  constructor
  · rintro ⟨t, ht, hz⟩
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · exact Or.inl (by simpa using hz)
    · refine Or.inr ⟨t - 1, by omega, ?_⟩
      rw [show a + 1 + ((t - 1 : ℕ) : ZMod (m + 3)) = a + (t : ZMod (m + 3)) by
        linear_combination natCast_pred_succ (n := m + 3) htpos]
      exact hz
  · rintro (hz | ⟨t, ht, hz⟩)
    · exact ⟨0, by omega, by simpa using hz⟩
    · refine ⟨t + 1, by omega, ?_⟩
      rw [show a + ((t + 1 : ℕ) : ZMod (m + 3)) = a + 1 + (t : ZMod (m + 3)) by push_cast; ring]
      exact hz

/-- **The first edge of an arc meets the rest of it only at the vertex between them.** -/
theorem edge_inter_arc_succ (P : ClosedPolygon m) (a : ZMod (m + 3)) {k : ℕ} (hk : k ≤ m + 2) :
    P.edge a ∩ P.arc (a + 1) (k - 1) ⊆ {P.vertex (a + 1)} := by
  rintro z ⟨hze, hza⟩
  obtain ⟨t, ht, hzt⟩ := mem_arc_iff.1 hza
  rw [show a + 1 + (t : ZMod (m + 3)) = a + ((t + 1 : ℕ) : ZMod (m + 3)) by push_cast; ring] at hzt
  have hne : a ≠ a + ((t + 1 : ℕ) : ZMod (m + 3)) := fun h =>
    natCast_ne_zero_of_lt (m := m) (t := t + 1) (by omega) (by omega) (by linear_combination -h)
  have hmem := P.edges_meet a (a + ((t + 1 : ℕ) : ZMod (m + 3))) hne ⟨hze, hzt⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
  rcases hmem with rfl | rfl
  · exact absurd hzt (P.vertex_notMem_edge_natCast a (by omega) (by omega))
  · rfl

/-- **A one-edge arc has no second edge.** If the same arc were also presented with two or more
edges, its second edge would lie inside its first, which `edges_meet` forbids. -/
theorem arc_one_ne {m m' : ℕ} (P : ClosedPolygon m) (Q : ClosedPolygon m') (a : ZMod (m + 3))
    (b : ZMod (m' + 3)) {l : ℕ} (hl : 2 ≤ l) (harc : P.arc a 1 = Q.arc b l)
    (hedge : P.edge a = Q.edge b) : False := by
  have hsub : Q.edge (b + 1) ⊆ Q.edge b := by
    intro z hz
    have hzQ : z ∈ Q.arc b l := mem_arc_iff.2 ⟨1, by omega, by
      rw [show b + ((1 : ℕ) : ZMod (m' + 3)) = b + 1 by push_cast; ring]; exact hz⟩
    rw [← harc] at hzQ
    obtain ⟨t, ht, hzt⟩ := mem_arc_iff.1 hzQ
    have ht0 : t = 0 := by omega
    subst ht0
    rw [← hedge]
    simpa using hzt
  obtain ⟨p, hp, hp1, hp2⟩ := PrePolygon.exists_mem_segment_ne (Q.vertex_ne (b + 1))
  have hmem := Q.edges_meet (b + 1) b (succ_ne_self b) ⟨hp, hsub hp⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h
  exacts [hp1 h, hp2 h]

/-- **Two closed polygons that carry the same arc, starting it at the same vertex, run through
the same vertices along it** — and in particular use the same number of edges. This is what makes
independent realizations of the six-cycle and of the two spliced curves agree. -/
theorem arc_vertex_eq : ∀ (k : ℕ) {m m' : ℕ} (P : ClosedPolygon m) (Q : ClosedPolygon m')
    (a : ZMod (m + 3)) (b : ZMod (m' + 3)) (l : ℕ), 1 ≤ k → k ≤ m + 2 → 1 ≤ l → l ≤ m' + 2 →
      P.arc a k = Q.arc b l → P.vertex a = Q.vertex b →
      k = l ∧ ∀ t : ℕ, t ≤ k →
        P.vertex (a + (t : ZMod (m + 3))) = Q.vertex (b + (t : ZMod (m' + 3))) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m m' P Q a b l hk1 hk2 hl1 hl2 harc hstart
    -- The two first edges leave the common vertex along one ray, and neither may overshoot the
    -- other: the shorter one's far end would be a vertex of its polygon interior to the other's
    -- edge.
    have hA : Q.vertex (b + 1) ∉ openSegment ℝ (P.vertex a) (P.vertex (a + 1)) :=
      notMem_openSegment_first_edge P Q a b hk1 hk2 hl1 harc hstart
    have hB : P.vertex (a + 1) ∉ openSegment ℝ (Q.vertex b) (Q.vertex (b + 1)) :=
      notMem_openSegment_first_edge Q P b a hl1 hl2 hk1 harc.symm hstart.symm
    obtain ⟨rP, hrP, hballP⟩ := P.exists_ball_arc_subset_edge a k (w := P.vertex a)
      fun t ht1 ht2 => P.vertex_notMem_edge_natCast a ht1 (by omega)
    obtain ⟨rQ, hrQ, hballQ⟩ := Q.exists_ball_arc_subset_edge b l (w := Q.vertex b)
      fun t ht1 ht2 => Q.vertex_notMem_edge_natCast b ht1 (by omega)
    have hsub : segment ℝ (P.vertex a) (P.vertex (a + 1)) ∩ ball (P.vertex a) (min rP rQ)
        ⊆ segment ℝ (P.vertex a) (Q.vertex (b + 1)) := by
      rintro z ⟨hzs, hzb⟩
      have hzA : z ∈ P.arc a k := mem_arc_iff.2 ⟨0, by omega, by simpa [edge] using hzs⟩
      have hzQ := hballQ ⟨by rw [← hstart]; exact ball_subset_ball (min_le_right _ _) hzb,
        by rw [← harc]; exact hzA⟩
      rw [edge, ← hstart] at hzQ
      exact hzQ
    obtain ⟨c, hc, hce⟩ :=
      exists_pos_smul_of_ball_subset (lt_min hrP hrQ) (P.vertex_ne a).symm hsub
    have hv1 : P.vertex (a + 1) = Q.vertex (b + 1) := by
      rcases lt_trichotomy c 1 with hlt | heq | hgt
      · refine absurd ?_ hB
        rw [← hstart, openSegment_eq_image' ℝ]
        exact ⟨c, ⟨hc, hlt⟩, by linear_combination (norm := module) -hce⟩
      · rw [heq, one_smul] at hce
        exact sub_left_inj.1 hce
      · have hq : P.vertex a + (1 / c) • (P.vertex (a + 1) - P.vertex a) = Q.vertex (b + 1) := by
          rw [hce, smul_smul, one_div, inv_mul_cancel₀ (by linarith), one_smul, add_sub_cancel]
        refine absurd ?_ hA
        rw [openSegment_eq_image' ℝ]
        exact ⟨1 / c, ⟨by positivity, by rw [div_lt_one (by linarith)]; linarith⟩, hq⟩
    have hedge : P.edge a = Q.edge b := by rw [edge, edge, hstart, hv1]
    rcases Nat.lt_or_ge k 2 with hk | hk
    · -- One edge each: the arc is a single segment.
      have hk' : k = 1 := by omega
      subst hk'
      have hl' : l = 1 := by
        by_contra hcon
        exact arc_one_ne P Q a b (by omega) harc hedge
      subst hl'
      refine ⟨rfl, fun t ht => ?_⟩
      interval_cases t
      · simpa using hstart
      · simpa using hv1
    · -- Both arcs continue: strip the common first edge and recurse.
      have hl' : 2 ≤ l := by
        by_contra hcon
        have hl1' : l = 1 := by omega
        subst hl1'
        exact arc_one_ne Q P b a (by omega) harc.symm hedge.symm
      have hsplitP := P.arc_succ a hk1
      have hsplitQ := Q.arc_succ b hl1
      have hinterP := P.edge_inter_arc_succ a (k := k) hk2
      have hinterQ := Q.edge_inter_arc_succ b (k := l) hl2
      have hmemP : P.vertex (a + 1) ∈ P.arc (a + 1) (k - 1) := P.vertex_mem_arc (a + 1) (by omega)
      have hmemQ : Q.vertex (b + 1) ∈ Q.arc (b + 1) (l - 1) := Q.vertex_mem_arc (b + 1) (by omega)
      have htail : P.arc (a + 1) (k - 1) = Q.arc (b + 1) (l - 1) := by
        refine Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
        · have hzQ : z ∈ Q.arc b l := by rw [← harc, hsplitP]; exact Or.inr hz
          rw [hsplitQ] at hzQ
          rcases hzQ with hzE | hzR
          · have hzv : z = P.vertex (a + 1) := hinterP ⟨by rw [hedge]; exact hzE, hz⟩
            rw [hzv, hv1]; exact hmemQ
          · exact hzR
        · have hzP : z ∈ P.arc a k := by rw [harc, hsplitQ]; exact Or.inr hz
          rw [hsplitP] at hzP
          rcases hzP with hzE | hzR
          · have hzv : z = Q.vertex (b + 1) := hinterQ ⟨by rw [← hedge]; exact hzE, hz⟩
            rw [hzv, ← hv1]; exact hmemP
          · exact hzR
      obtain ⟨hkl, hvt⟩ := ih (k - 1) (by omega) P Q (a + 1) (b + 1) (l - 1)
        (by omega) (by omega) (by omega) (by omega) htail hv1
      refine ⟨by omega, fun t ht => ?_⟩
      rcases Nat.eq_zero_or_pos t with rfl | htpos
      · simpa using hstart
      · have hstep := hvt (t - 1) (by omega)
        rw [show a + 1 + ((t - 1 : ℕ) : ZMod (m + 3)) = a + (t : ZMod (m + 3)) by
            linear_combination natCast_pred_succ (n := m + 3) htpos,
          show b + 1 + ((t - 1 : ℕ) : ZMod (m' + 3)) = b + (t : ZMod (m' + 3)) by
            linear_combination natCast_pred_succ (n := m' + 3) htpos] at hstep
        exact hstep

/-- **Two closed polygons that carry the same arc, starting it at the same vertex, cut it into
the same edges.** -/
theorem arcPieces_eq {m m' : ℕ} (P : ClosedPolygon m) (Q : ClosedPolygon m') (a : ZMod (m + 3))
    (b : ZMod (m' + 3)) {k l : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2) (hl1 : 1 ≤ l)
    (hl2 : l ≤ m' + 2) (harc : P.arc a k = Q.arc b l) (hstart : P.vertex a = Q.vertex b) :
    P.arcPieces a k = Q.arcPieces b l := by
  obtain ⟨hkl, hv⟩ := arc_vertex_eq k P Q a b l hk1 hk2 hl1 hl2 harc hstart
  subst hkl
  refine List.map_congr_left fun t ht => ?_
  have htk : t < k := List.mem_range.1 ht
  have h1 := hv t htk.le
  have h2 := hv (t + 1) htk
  rw [show a + ((t + 1 : ℕ) : ZMod (m + 3)) = a + (t : ZMod (m + 3)) + 1 by push_cast; ring,
    show b + ((t + 1 : ℕ) : ZMod (m' + 3)) = b + (t : ZMod (m' + 3)) + 1 by push_cast; ring]
    at h2
  rw [h1, h2]

end ClosedPolygon

/-- **The realization of a splitting, with the first arc's direction fixed too.** The two arcs of
`Schoenflies.exists_closedPolygon_arcs_ordered` come out in the order they were given, but the
polygon may traverse them either way; reading it backwards when it does is what pins the first
arc to start at `p`. Two realizations of one arc can then be compared with
`Schoenflies.ClosedPolygon.arcPieces_eq`. -/
theorem exists_closedPolygon_arcs_oriented {C A₁ A₂ : Set Plane} (hJ : IsJordanCurve C)
    (hP : IsPolygonal C) {p q : Plane} (hp : IsCornerAt C p) (hq : IsCornerAt C q) (hpq : p ≠ q)
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q) (hunion : A₁ ∪ A₂ = C)
    (hinter : A₁ ∩ A₂ = {p, q}) :
    ∃ (m : ℕ) (P : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ), P.carrier = C ∧
      1 ≤ k ∧ k ≤ m + 2 ∧ P.vertex a = p ∧ P.vertex (a + (k : ZMod (m + 3))) = q ∧
      P.arc a k = A₁ ∧ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = A₂ := by
  obtain ⟨m, P, a, k, hcar, hpa, hqa, hk1, hk2⟩ :=
    exists_closedPolygon_split hJ hP hp hq hpq
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
  · exact ⟨m, P, a, k, hcar, hk1, hk2, hpa, hqa, e1.symm, e2.symm⟩
  · -- The realization runs the two arcs the other way round: read it backwards.
    have hneg : ((m + 3 - k : ℕ) : ZMod (m + 3)) = -(k : ZMod (m + 3)) := by
      linear_combination zmod_add_sub_cancel (m := m) (k := k) (by omega) 0
    refine ⟨m, P.reverse, -a, m + 3 - k, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
    · rw [ClosedPolygon.reverse_carrier]; exact hcar
    · rw [ClosedPolygon.reverse_vertex, neg_neg]; exact hpa
    · rw [ClosedPolygon.reverse_vertex, hneg,
        show -(-a + -(k : ZMod (m + 3))) = a + (k : ZMod (m + 3)) by ring]
      exact hqa
    · have h := P.reverse_arc (a + (k : ZMod (m + 3))) (m + 3 - k)
      rw [hneg, show -(a + (k : ZMod (m + 3))) - -(k : ZMod (m + 3)) = -a by ring] at h
      rw [h]; exact e1.symm
    · have h := P.reverse_arc a k
      rw [show m + 3 - (m + 3 - k) = k by omega, hneg,
        show -a + -(k : ZMod (m + 3)) = -a - (k : ZMod (m + 3)) by ring, h]
      exact e2.symm

end Schoenflies

namespace Graph

open Schoenflies

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}

/-! ## What the realization needs from the drawing, and nothing else -/

variable {x y : Fin 3 → Plane} {e : Fin 3 → Fin 3 → β} {s : Fin 3}

/-- **General position at the two cut points of the crosscut indexed by `s`.** At each of the two
ends `x s` and `y (s + 1)` of the remaining edge, the six-cycle turns, and so does each of the two
closed curves the remaining edge forms with the two halves of the six-cycle.

This is not a hypothesis chosen for convenience. `Schoenflies.ClosedPolygon.isCornerAt_vertex` and
`Schoenflies.ClosedPolygon.exists_vertex_eq_of_isCornerAt` together say that the vertex set of a
realization *is* the corner set of the curve; a crosscut cutting `C` at these two points forces
them to be vertices of all three closed polygons, hence corners of all three curves. For a drawn
`K(3,3)` it says that at each of the six vertices no two of the three edges leave along one
line. -/
def IsHexGeneric (drawing : β → ℝ → Plane) (e : Fin 3 → Fin 3 → β) (x y : Fin 3 → Plane)
    (s : Fin 3) : Prop :=
  ∀ p ∈ ({x s, y (s + 1)} : Set Plane),
    IsCornerAt (hexSet drawing e) p ∧
    IsCornerAt (edgesCover drawing (arcA e s) ∪ edgeArc drawing (e s (s + 1))) p ∧
    IsCornerAt (edgesCover drawing (arcB e s) ∪ edgeArc drawing (e s (s + 1))) p

namespace IsK33Config

/-- The first half of the six-cycle is polygonal: it is drawn by a path. -/
theorem isPolygonal_arcA (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc drawing f)) (s : Fin 3) :
    IsPolygonal (edgesCover drawing (arcA e s)) :=
  hd.isPolygonal_edgesCover hpoly (h.arcA_isPath s).isWalk (by simp [arcA])

/-- The second half of the six-cycle is polygonal. -/
theorem isPolygonal_arcB (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc drawing f)) (s : Fin 3) :
    IsPolygonal (edgesCover drawing (arcB e s)) :=
  hd.isPolygonal_edgesCover hpoly (h.arcB_isPath s).isWalk (by simp [arcB])

/-- **The six-cycle of a polygonally drawn `K(3,3)` is polygonal**: it is the union of its two
halves, which meet. -/
theorem isPolygonal_hexSet (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc drawing f)) :
    IsPolygonal (hexSet drawing e) := by
  rw [← arcs_union (drawing := drawing) (e := e) 0]
  exact (h.isPolygonal_arcA hd hpoly 0).union (h.isPolygonal_arcB hd hpoly 0)
    ⟨x 0, (h.arcA_isArcBetween hd 0).left_mem, (h.arcB_isArcBetween hd 0).left_mem⟩

/-- A remaining edge meets the first half of the six-cycle exactly in its own two ends. -/
theorem chord_inter_arcA (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    edgesCover drawing (arcA e s) ∩ edgeArc drawing (e s (s + 1)) = {x s, y (s + 1)} := by
  refine Set.Subset.antisymm (fun z hz => ?_) ?_
  · have hzhex : z ∈ hexSet drawing e := by
      rw [← arcs_union (drawing := drawing) (e := e) s]; exact Or.inl hz.1
    rw [← h.chord_inter_hexSet hd s]
    exact ⟨hz.2, hzhex⟩
  · rintro z (rfl | rfl)
    exacts [⟨(h.arcA_isArcBetween hd s).left_mem,
      (hd.edge_isArcBetween (h.isLink s (s + 1))).left_mem⟩,
      ⟨(h.arcA_isArcBetween hd s).right_mem,
      (hd.edge_isArcBetween (h.isLink s (s + 1))).right_mem⟩]

/-- A remaining edge meets the second half of the six-cycle exactly in its own two ends. -/
theorem chord_inter_arcB (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    edgesCover drawing (arcB e s) ∩ edgeArc drawing (e s (s + 1)) = {x s, y (s + 1)} := by
  refine Set.Subset.antisymm (fun z hz => ?_) ?_
  · have hzhex : z ∈ hexSet drawing e := by
      rw [← arcs_union (drawing := drawing) (e := e) s]; exact Or.inr hz.1
    rw [← h.chord_inter_hexSet hd s]
    exact ⟨hz.2, hzhex⟩
  · rintro z (rfl | rfl)
    exacts [⟨(h.arcB_isArcBetween hd s).left_mem,
      (hd.edge_isArcBetween (h.isLink s (s + 1))).left_mem⟩,
      ⟨(h.arcB_isArcBetween hd s).right_mem,
      (hd.edge_isArcBetween (h.isLink s (s + 1))).right_mem⟩]

/-- **`Graph.IsHexRealization`, discharged.** The six-cycle and the two curves the remaining edge
forms with its halves are three polygonal Jordan curves, so
`Schoenflies.exists_closedPolygon_arcs_oriented` presents each of them as a closed polygon whose
two arcs are the two given halves, both read from `x s` to `y (s+1)`.

The three presentations are found independently, and what makes them fit together is
`Schoenflies.ClosedPolygon.arcPieces_eq`: two closed polygons carrying one arc from one vertex cut
it into the same edges. So the six-cycle's presentation and the first spliced curve's agree on the
first half, the six-cycle's and the second spliced curve's agree on the second half, and the two
spliced curves agree on the remaining edge — the last only after reversing one of them, since a
crosscut is traversed one way in each of the two curves it bounds. -/
theorem isHexRealization (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc drawing f)) (hgen : IsHexGeneric drawing e x y s) :
    IsHexRealization drawing e s := by
  obtain ⟨hcp, hcp1, hcp2⟩ := hgen (x s) (by simp)
  obtain ⟨hcq, hcq1, hcq2⟩ := hgen (y (s + 1)) (by simp)
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
  have hP2 : IsPolygonal (edgesCover drawing (arcB e s) ∪ edgeArc drawing (e s (s + 1))) :=
    (h.isPolygonal_arcB hd hpoly s).union hPch ⟨x s, hA2.left_mem, hCh.left_mem⟩
  have hJ1 : IsJordanCurve (edgesCover drawing (arcA e s) ∪ edgeArc drawing (e s (s + 1))) :=
    IsJordanCurve.of_two_arcs hA1 hCh.reverse fun z hz1 hz2 => by
      have hz : z ∈ ({x s, y (s + 1)} : Set Plane) := hinterA ▸ ⟨hz1, hz2⟩
      simpa using hz
  have hJ2 : IsJordanCurve (edgesCover drawing (arcB e s) ∪ edgeArc drawing (e s (s + 1))) :=
    IsJordanCurve.of_two_arcs hA2 hCh.reverse fun z hz1 hz2 => by
      have hz : z ∈ ({x s, y (s + 1)} : Set Plane) := hinterB ▸ ⟨hz1, hz2⟩
      simpa using hz
  obtain ⟨m, C, a, k, hCcar, hk1, hk2, hCa, hCak, hCarc1, hCarc2⟩ :=
    exists_closedPolygon_arcs_oriented (h.hexagon_isJordanCurve hd)
      (h.isPolygonal_hexSet hd hpoly) hcp hcq hpq hA1 hA2
      (arcs_union (drawing := drawing) (e := e) s) (h.arcs_inter hd s)
  obtain ⟨m₁, J₁, b, l, -, hl1, hl2, hJ1b, hJ1bl, hJ1a1, hJ1a2⟩ :=
    exists_closedPolygon_arcs_oriented hJ1 hP1 hcp1 hcq1 hpq hA1 hCh rfl hinterA
  obtain ⟨m₂, J₂, b₂, l₂, -, hl21, hl22, hJ2b, hJ2bl, hJ2a1, hJ2a2⟩ :=
    exists_closedPolygon_arcs_oriented hJ2 hP2 hcq2 hcp2 hpq.symm hA2.reverse hCh.reverse rfl
      (by rw [hinterB, Set.pair_comm])
  refine ⟨m, m₁, m₂, C, J₁, J₂, J₁.arcPieces (b + (l : ZMod (m₁ + 3))) (m₁ + 3 - l), a, k,
    by omega, hCcar, hCarc1, hCarc2, hJ1a2, ?_, ?_⟩
  · -- The first curve: the first half of the six-cycle, then the remaining edge.
    have hpieces : C.arcPieces a k = J₁.arcPieces b l :=
      ClosedPolygon.arcPieces_eq C J₁ a b hk1 hk2 hl1 hl2 (hCarc1.trans hJ1a1.symm)
        (hCa.trans hJ1b.symm)
    rw [hpieces]
    exact ClosedPolygon.sameEdges_arcPieces_split J₁ b (by omega)
  · -- The second curve: the second half, then the remaining edge — traversed the other way.
    have hpieces : C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) = J₂.arcPieces b₂ l₂ :=
      ClosedPolygon.arcPieces_eq C J₂ _ b₂ (by omega) (by omega) hl21 hl22
        (hCarc2.trans hJ2a1.symm) (hCak.trans hJ2b.symm)
    have hrev := J₂.reverse_arc (b₂ + (l₂ : ZMod (m₂ + 3))) (m₂ + 3 - l₂)
    have hstart2 : J₂.reverse.vertex (-(b₂ + (l₂ : ZMod (m₂ + 3)))
        - ((m₂ + 3 - l₂ : ℕ) : ZMod (m₂ + 3))) = y (s + 1) := by
      rw [ClosedPolygon.reverse_vertex,
        show -(-(b₂ + (l₂ : ZMod (m₂ + 3))) - ((m₂ + 3 - l₂ : ℕ) : ZMod (m₂ + 3)))
          = b₂ + (l₂ : ZMod (m₂ + 3)) + ((m₂ + 3 - l₂ : ℕ) : ZMod (m₂ + 3)) by ring,
        zmod_add_sub_cancel (by omega) b₂]
      exact hJ2b
    have hKeq : J₂.reverse.arcPieces (-(b₂ + (l₂ : ZMod (m₂ + 3)))
          - ((m₂ + 3 - l₂ : ℕ) : ZMod (m₂ + 3))) (m₂ + 3 - l₂)
        = J₁.arcPieces (b + (l : ZMod (m₁ + 3))) (m₁ + 3 - l) :=
      ClosedPolygon.arcPieces_eq J₂.reverse J₁ _ _ (by omega) (by omega) (by omega) (by omega)
        (by rw [hrev, hJ2a2, hJ1a2]) (by rw [hstart2, hJ1bl])
    have hKsame : SameEdges (J₂.arcPieces (b₂ + (l₂ : ZMod (m₂ + 3))) (m₂ + 3 - l₂))
        (J₁.arcPieces (b + (l : ZMod (m₁ + 3))) (m₁ + 3 - l)) := by
      rw [← hKeq]
      exact (J₂.sameEdges_reverse_arcPieces (b₂ + (l₂ : ZMod (m₂ + 3))) (m₂ + 3 - l₂)).symm
    refine (ClosedPolygon.sameEdges_arcPieces_split (k := l₂) J₂ b₂ (by omega)).trans ?_
    rw [← hpieces]
    exact SameEdges.append (SameEdges.refl _) hKsame

/-! ### `lem:k33` and `cor:k33-subdivision`, with the realization gone

What is left as a hypothesis is a *bending* step, and only that: every polygonal drawing can be
redrawn so that no two edges at a vertex leave it along one line. -/

/-- **`lem:k33` for a polygonal drawing in general position.** -/
theorem false_of_hexGeneric (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc drawing f))
    (hgen : ∀ s : Fin 3, IsHexGeneric drawing e x y s) : False :=
  h.false_of_hexRealizations hd fun s => h.isHexRealization hd hpoly (hgen s)

/-- **Lemma 3.10 (nonplanarity of `K(3,3)`), with only the bending step assumed.** A graph
carrying a copy of `K(3,3)` has no plane drawing, provided a polygonal drawing can be bent into
general position at the six vertices. -/
theorem not_isDrawing_of_bendable [G.Finite] (h : IsK33Config G x y e)
    (hbend : ∀ dr : β → ℝ → Plane, IsDrawing G dr → (∀ f ∈ E(G), IsPolygonal (edgeArc dr f)) →
      ∃ dr' : β → ℝ → Plane, IsDrawing G dr' ∧ (∀ f ∈ E(G), IsPolygonal (edgeArc dr' f)) ∧
        ∀ s : Fin 3, IsHexGeneric dr' e x y s) :
    ¬ ∃ dr : β → ℝ → Plane, IsDrawing G dr := by
  rintro ⟨dr, hdr⟩
  obtain ⟨dr', hdr', hpoly'⟩ := polygonal_redrawing G dr hdr
  obtain ⟨dr'', hdr'', hpoly'', hgen⟩ := hbend dr' hdr' hpoly'
  exact h.false_of_hexGeneric hdr'' hpoly'' hgen

end IsK33Config

/-- **The bending step**, for the abstract `K(3,3)` on six named points of the plane: every
polygonal drawing of it can be redrawn, polygonally, so that at each of the six vertices no two
of the three edges leave along one line. This is the one thing left unproved; see "What is still
assumed" in the module docstring. -/
abbrev Bendable (x y : Fin 3 → Plane) : Prop :=
  ∀ dr : Fin 3 × Fin 3 → ℝ → Plane, IsDrawing (k33Graph x y) dr →
    (∀ f ∈ E(k33Graph x y), IsPolygonal (edgeArc dr f)) →
    ∃ dr' : Fin 3 × Fin 3 → ℝ → Plane, IsDrawing (k33Graph x y) dr' ∧
      (∀ f ∈ E(k33Graph x y), IsPolygonal (edgeArc dr' f)) ∧
      ∀ s : Fin 3, IsHexGeneric dr' (fun i j => (i, j)) x y s

/-- **`lem:k33` for nine arcs**: no nine arcs in the plane meet only where a `K(3,3)` forces them
to, assuming `Graph.Bendable`. -/
theorem IsArcK33.false_of_bendable {P : Fin 3 → Fin 3 → Set Plane} (h : IsArcK33 x y P)
    (hbend : Bendable x y) : False :=
  h.isK33Config.not_isDrawing_of_bendable hbend ⟨h.arcDrawing, h.isDrawing⟩

/-- **Corollary 3.11 (subdivisions of `K(3,3)`).** No subdivision of `K(3,3)` has a plane
drawing, assuming `Graph.Bendable`, and only for the *contracted* graph `k33Graph x y`,
whose nine edges are the branch paths. -/
theorem IsK33Subdivision.false_of_bendable {H : Graph Plane β} {W : Fin 3 → Fin 3 → List β}
    (hd : IsDrawing H drawing) (h : IsK33Subdivision H x y W) (hbend : Bendable x y) : False :=
  (h.isArcK33 hd).false_of_bendable hbend

/-- **The headline: `K(3,3)` has no plane drawing.** Stated for the concrete graph
`Graph.k33Graph x y`, whose nine edges are the index pairs. Assuming `Graph.Bendable`, the
one hypothesis this module leaves standing. -/
theorem k33Graph_not_isDrawing (x y : Fin 3 → Plane) (hx : Function.Injective x)
    (hy : Function.Injective y) (hxy : ∀ i j, x i ≠ y j) (hbend : Bendable x y) :
    ¬ ∃ dr : Fin 3 × Fin 3 → ℝ → Plane, IsDrawing (k33Graph x y) dr :=
  IsK33Config.not_isDrawing_of_bendable
    ⟨k33Graph_isLink x y, hx, hy, hxy⟩ hbend

end Graph
