/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.SquareMeshFixed
public import LeanPool.Schoenflies.Graph.TwoPaths

/-!
# The local source grid, and the missing hypothesis of the anchored square mesh

Two things, and the second is the more important.

## 1. `prop:anchored-square-mesh` clause 5 — which hypothesis repairs it

`docs/ROADMAP.md` records clause 5, *the skeleton of `T` is 2-connected*, as **false** for
`Schoenflies.squareMesh` when the fresh-point set is too small, and names
`Schoenflies.FreshDense` as "the shape the missing hypothesis should take". The first section
of this module checks that, and the answer is **no: `FreshDense` alone does not repair
clause 5.**

* `Schoenflies.freshDense_of_four_sqrt_two_le` — for `4√2 ≤ δ`, `FreshDense fresh δ` holds for
  **every** list `fresh`, the empty one included, because `S` itself has diameter `2√2`. So
  `FreshDense fresh δ` is vacuous at large `δ` and excludes nothing.
* `Schoenflies.freshDense_not_isTwoConnected` — the counterexample made formal: at
  `δ = 4√2` the hypotheses `0 < δ` and `FreshDense [] δ` both hold and
  `squareMesh δ [] anchors` is still not 2-connected.

What does repair it is `FreshDense` **together with a bound on `δ`**:

* `Schoenflies.exists_two_distinct_fresh_of_freshDense` — `FreshDense fresh δ` and `δ < 4`
  force two distinct fresh points. (`4` is not the sharp constant — `4√2` is — but it is the
  one a side of `S`, whose two ends are `2` apart, gives with no work. The blueprint's own
  `δ = ε_n = 2^{-n}` is far below either.)

and two distinct fresh points is exactly the right amount, because *fewer* is always fatal:

* `Schoenflies.not_isTwoConnected_meshGraph_of_fresh_subsingleton` — a mesh whose fresh points
  are not two distinct points is **never** 2-connected. This closes the case
  `SquareMeshFixed.lean` left open in prose: with exactly one fresh point `z` the mesh is
  connected, but `z` is a cut vertex, because the spoke at `z` is the only edge of the mesh
  that changes the sup norm and every other edge preserves it.

So the correct statement of clause 5 carries the hypothesis `∃ z ∈ fresh, ∃ w ∈ fresh, z ≠ w`,
which `FreshDense fresh δ ∧ δ < 4` supplies, and which is necessary as well as sufficient in
the degenerate range.

## 2. `prop:local-grid-attachment` — the grid

The blueprint's proof begins: *"Choose sufficiently fine finite horizontal and vertical
coordinate sets in `W`, with at least two intervals in each direction. Begin with the outer
rectangle of the resulting grid `K` … By `lem:subdivision-ear-preserve`, `K` is 2-connected."*

`Schoenflies.localGrid` is that `K`, as a `def`: the uniform `k × k` grid on the closed square
`W` of centre `p` and radius `s`. `Schoenflies/SquareMeshConnected.lean` and
`Schoenflies/SquareMeshFixed.lean` supply everything combinatorial about a grid, so what is
added here is the *quantitative* clause the proposition needs — every closed grid rectangle has
diameter `< ε` — together with the instantiation of the general grid lemmas at these
coordinates.

The rest of `prop:local-grid-attachment` — the overlay of `K` with the polygonal nonboundary
skeleton of `Γ`, the three cases, and the component-joining loop — is **not** here; see the
report.

## Blueprint

* `prop:anchored-square-mesh`, clause 5 — `freshDense_of_four_sqrt_two_le`,
  `freshDense_not_isTwoConnected`, `exists_two_distinct_fresh_of_freshDense`,
  `not_isTwoConnected_meshGraph_of_fresh_subsingleton`,
  `not_isTwoConnected_squareMesh_of_fresh_subsingleton`.
* `prop:local-grid-attachment`, the grid `K` — `localGrid`, `localGrid_isTwoConnected`,
  `localGrid_subdivide_isTwoConnected`, `localGrid_isDrawing`, `localGrid_outer_cycle`.
* `prop:local-grid-attachment`, clause 3 — `dist_le_of_mem_localGridCell` (the closed grid
  rectangle), `dist_lt_of_avoiding_localGrid` (a connected subset of `W` missing the grid),
  `localGridCount`, `localGridCount_spec`, `localGrid_fine`.
* `lem:union-two-connected` — used through `Graph.IsTwoConnected.union` and
  `Graph.IsTwoConnected.ear`; `Graph.IsTwoConnected.of_le_of_vertexSet_subset` is the
  "spanning 2-connected subgraph" form the assembly needs.
-/

public section

open Metric Set
open scoped Graph

namespace Schoenflies

/-! ### The diameter of `S`

`S = modelCurve` is the frame of `[-1,1]²`, so any two of its points are at sup distance at
most `2` and hence at Euclidean distance at most `2√2`. That single bound is what makes
`FreshDense fresh δ` vacuous once `δ ≥ 4√2`. -/

/-- The sup distance is at most the Euclidean distance. -/
theorem supDist_le_dist (x y : Plane) : Plane.supDist x y ≤ dist x y := by
  rw [dist_eq_norm]
  exact Plane.supNorm_le_norm _

/-- **Any two points of `S` are within `2√2`.** -/
theorem dist_le_of_mem_modelCurve {x y : Plane} (hx : x ∈ modelCurve) (hy : y ∈ modelCurve) :
    dist x y ≤ 2 * Real.sqrt 2 := by
  have hsq : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  calc dist x y ≤ Real.sqrt 2 * Plane.supNorm (x - y) := dist_le_sqrt_two_mul_supNorm x y
    _ ≤ Real.sqrt 2 * (Plane.supNorm x + Plane.supNorm y) :=
        mul_le_mul_of_nonneg_left (supNorm_sub_le x y) hsq.le
    _ = 2 * Real.sqrt 2 := by
        rw [show Plane.supNorm x = 1 from hx, show Plane.supNorm y = 1 from hy]; ring

/-- **`FreshDense` is vacuous at large `δ`.** For `δ ≥ 4√2` *every* list of fresh points is
`δ`-dense, the empty one included: the whole of `S` has diameter `2√2 ≤ δ/2`.

This is the first half of the finding: `FreshDense` alone cannot be the missing hypothesis of
`prop:anchored-square-mesh` clause 5, because it does not exclude `fresh = []`. -/
theorem freshDense_of_four_sqrt_two_le {fresh : List Plane} {δ : ℝ}
    (hδ : 4 * Real.sqrt 2 ≤ δ) : FreshDense fresh δ := by
  intro A hA _ x hx y hy
  have := dist_le_of_mem_modelCurve (hA hx).1 (hA hy).1
  linarith

/-- **The counterexample, formally.** There is a positive `δ` for which `FreshDense [] δ`
holds and the mesh is still not 2-connected. So clause 5 is not repaired by adding
`FreshDense` alone. -/
theorem freshDense_not_isTwoConnected (anchors : List Plane) :
    ∃ δ : ℝ, 0 < δ ∧ FreshDense [] δ ∧ ¬ (squareMesh δ [] anchors).IsTwoConnected := by
  have hsq : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  exact ⟨4 * Real.sqrt 2, by linarith, freshDense_of_four_sqrt_two_le le_rfl,
    not_isTwoConnected_squareMesh_of_fresh_nil _ _⟩

/-! ### What does repair clause 5

A side of `S` is a connected subset of `S` whose two ends are `2` apart. If no two fresh points
are distinct then some side avoids all of them — a single point cannot lie on both the top and
the bottom side — and `FreshDense fresh δ` applied to that side forces `4 ≤ δ`. -/

/-- The two ends of the top or the bottom side of `S` are at distance at least `2`. -/
theorem two_le_dist_side {P : Piece} (h : P = sideT ∨ P = sideB) : (2 : ℝ) ≤ dist P.1 P.2 := by
  refine le_trans (le_of_eq ?_) (supDist_le_dist P.1 P.2)
  rcases h with rfl | rfl <;>
    · simp only [sideT, sideB, Plane.supDist, Plane.supNorm, Plane.sub_apply]
      norm_num

/-- A single point cannot lie on both horizontal sides of `S`, so one of them avoids a
one-point set. -/
theorem exists_side_avoiding (fresh : List Plane) (hsub : ∀ z ∈ fresh, ∀ w ∈ fresh, z = w) :
    ∃ P : Piece, (P = sideT ∨ P = sideB) ∧ ∀ z ∈ fresh, z ∉ P.seg := by
  by_cases hex : ∃ z, z ∈ fresh
  · obtain ⟨z, hz⟩ := hex
    by_cases hzT : z ∈ sideT.seg
    · refine ⟨sideB, Or.inr rfl, fun w hw hwB => ?_⟩
      have : w = z := hsub w hw z hz
      subst this
      exact sideT_disjoint_sideB hzT hwB
    · exact ⟨sideT, Or.inl rfl, fun w hw hwT => hzT (by rwa [← hsub w hw z hz])⟩
  · push Not at hex
    exact ⟨sideT, Or.inl rfl, fun z hz _ => absurd hz (hex z)⟩

/-- **`FreshDense` with a small `δ` gives two distinct fresh points.** This is the hypothesis
`prop:anchored-square-mesh` clause 5 actually needs, and the blueprint supplies it: its
`δ = ε_n = 2^{-n}` is well below `4`. -/
theorem exists_two_distinct_fresh_of_freshDense {fresh : List Plane} {δ : ℝ}
    (hdense : FreshDense fresh δ) (hδ : δ < 4) : ∃ z ∈ fresh, ∃ w ∈ fresh, z ≠ w := by
  by_contra hcon
  push Not at hcon
  obtain ⟨P, hP, havoid⟩ := exists_side_avoiding fresh hcon
  have hseg : P.seg ⊆ modelCurve \ {x | x ∈ fresh} := by
    intro x hx
    refine ⟨side_seg_subset_modelCurve ?_ hx, fun hmem => havoid x hmem hx⟩
    rcases hP with rfl | rfl
    exacts [Or.inl rfl, Or.inr (Or.inr (Or.inl rfl))]
  have := hdense P.seg hseg (convex_segment P.1 P.2).isPreconnected
    P.1 (left_mem_segment ℝ _ _) P.2 (right_mem_segment ℝ _ _)
  have := two_le_dist_side hP
  linarith

/-! ### Fewer than two distinct fresh points is always fatal

`SquareMeshFixed.not_isTwoConnected_squareMesh_of_fresh_nil` settles `fresh = []` by showing
the mesh disconnected. The remaining degenerate case — exactly one fresh point — is settled
here, and by the same invariant.

Every edge of the mesh is a subsegment of a source segment, and a source segment is either a
side of a ring, on which the sup norm is constant, or the spoke at a fresh point `z`, along
which the only point of sup norm `1` is `z` itself. So once `z` is deleted, **no** edge of the
mesh joins a vertex of sup norm `1` to a vertex of smaller sup norm: `z` is a cut vertex. -/

/-- Along an edge of the mesh whose ends are both different from the one fresh point `z`, the
predicate "sup norm is `1`" is constant. -/
theorem supNorm_eq_one_iff_of_isLink {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (hsub : ∀ u ∈ fresh, ∀ w ∈ fresh, u = w)
    {anchors : List Plane} {z : Plane} (hz : z ∈ fresh) {P : Piece} {x y : Plane}
    (h : (meshGraph N fresh anchors).IsLink P x y) (hx : x ≠ z) (hy : y ≠ z) :
    (Plane.supNorm x = 1 ↔ Plane.supNorm y = 1) := by
  obtain ⟨R, hR, hRsub⟩ := meshGraph_edge_source h.1
  -- the ends of `P`, in whichever order the link presents them
  have hends : (x = P.1 ∧ y = P.2) ∨ (x = P.2 ∧ y = P.1) := h.2
  rcases mem_meshSegments.1 hR with ⟨r, hr, hRr⟩ | ⟨u, hu, rfl⟩
  · -- a side of a ring: both ends have sup norm `r`
    have hring : P.seg ⊆ ringSet r :=
      hRsub.trans (ringPieces_seg_subset (meshRadii_pos hN hr).le hRr)
    have h1 : Plane.supNorm P.1 = r := hring (left_mem_segment ℝ _ _)
    have h2 : Plane.supNorm P.2 = r := hring (right_mem_segment ℝ _ _)
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [by rw [h1, h2], by rw [h1, h2]]
  · -- the spoke at the single fresh point: sup norm `1` only at its outer end
    rw [hsub u hu z hz] at hRsub
    have hspoke : ∀ q ∈ (spokePiece N z).seg, Plane.supNorm q = 1 → q = z := by
      intro q hq hq1
      have : q ∈ (spokePiece N z).seg ∩ modelCurve := ⟨hq, hq1⟩
      rwa [spokePiece_inter_modelCurve hN (hfresh z hz)] at this
    have hne : ∀ q, (q = P.1 ∨ q = P.2) → q ≠ z → Plane.supNorm q ≠ 1 := by
      rintro q (rfl | rfl) hqz hq1
      exacts [hqz (hspoke _ (hRsub (left_mem_segment ℝ _ _)) hq1),
        hqz (hspoke _ (hRsub (right_mem_segment ℝ _ _)) hq1)]
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨fun hc => absurd hc (hne _ (Or.inl rfl) hx),
        fun hc => absurd hc (hne _ (Or.inr rfl) hy)⟩
    · exact ⟨fun hc => absurd hc (hne _ (Or.inr rfl) hx),
        fun hc => absurd hc (hne _ (Or.inl rfl) hy)⟩

/-- An end of a side of the outer ring is a vertex of the mesh. -/
theorem corner_mem_vertexSet_meshGraph {N : ℕ} (hN : 2 ≤ N) {fresh anchors : List Plane}
    {R : Piece} (hR : R ∈ ringPieces 1) : R.1 ∈ V(meshGraph N fresh anchors) :=
  end_mem_vertexSet_meshGraph (outer_ringPieces_mem hN hR) (Or.inl rfl)

theorem supNorm_corner_pp : Plane.supNorm (Plane.mk (1 : ℝ) (1 : ℝ)) = 1 := by
  simp [Plane.supNorm]

theorem supNorm_corner_mm : Plane.supNorm (Plane.mk (-1 : ℝ) (-1 : ℝ)) = 1 := by
  simp [Plane.supNorm]

/-- Whichever point `z` is, one of the two corners `(1,1)`, `(-1,-1)` differs from it and is a
vertex of the mesh of sup norm `1`. -/
theorem exists_outer_vertex_ne {N : ℕ} (hN : 2 ≤ N) {fresh anchors : List Plane} (z : Plane) :
    ∃ c : Plane, c ∈ V(meshGraph N fresh anchors) ∧ Plane.supNorm c = 1 ∧ c ≠ z := by
  by_cases h : (Plane.mk (1 : ℝ) (1 : ℝ)) = z
  · refine ⟨Plane.mk (-1 : ℝ) (-1 : ℝ), corner_mem_vertexSet_meshGraph (fresh := fresh)
      (anchors := anchors) hN (R := (Plane.mk (-1) (-1), Plane.mk 1 (-1))) (by simp [ringPieces]),
      supNorm_corner_mm, ?_⟩
    rw [← h]
    exact mk_ne_mk_of_fst (by norm_num)
  · exact ⟨Plane.mk (1 : ℝ) (1 : ℝ), corner_mem_vertexSet_meshGraph (fresh := fresh)
      (anchors := anchors) hN (R := (Plane.mk 1 1, Plane.mk (-1) 1)) (by simp [ringPieces]),
      supNorm_corner_pp, h⟩

/-- The corner of the innermost ring is a vertex of the mesh, and its sup norm is not `1`. -/
theorem exists_inner_vertex {N : ℕ} (hN : 2 ≤ N) {fresh anchors : List Plane} :
    ∃ c : Plane, c ∈ V(meshGraph N fresh anchors) ∧ Plane.supNorm c ≠ 1 := by
  refine ⟨Plane.mk ((N : ℝ)⁻¹) ((N : ℝ)⁻¹),
    end_mem_vertexSet_meshGraph
      (R := (Plane.mk ((N : ℝ)⁻¹) ((N : ℝ)⁻¹), Plane.mk (-(N : ℝ)⁻¹) ((N : ℝ)⁻¹)))
      (mem_meshSegments.2 (Or.inl ⟨(N : ℝ)⁻¹, inv_mem_meshRadii hN, by simp [ringPieces]⟩))
      (Or.inl rfl), ?_⟩
  rw [supNorm_mk, abs_of_nonneg (inv_cast_pos hN).le, max_self]
  exact ne_of_lt (inv_cast_lt_one hN)

/-- **A mesh whose fresh points are not two distinct points is never 2-connected.** With none
the mesh is disconnected (`not_connected_meshGraph_of_fresh_nil`); with one, `z`, the point `z`
is a cut vertex.

This is the second half of the finding: two distinct fresh points is not merely a convenient
hypothesis for clause 5, it is a *necessary* one. -/
theorem not_isTwoConnected_meshGraph_of_fresh_subsingleton {N : ℕ} (hN : 2 ≤ N)
    {fresh : List Plane} (hfresh : ∀ u ∈ fresh, u ∈ modelCurve)
    (hsub : ∀ u ∈ fresh, ∀ w ∈ fresh, u = w) (anchors : List Plane) :
    ¬ (meshGraph N fresh anchors).IsTwoConnected := by
  by_cases hex : ∃ z, z ∈ fresh
  swap
  · push Not at hex
    obtain rfl : fresh = [] := List.eq_nil_iff_forall_not_mem.2 hex
    exact fun h => not_connected_meshGraph_of_fresh_nil hN anchors h.connected
  obtain ⟨z, hz⟩ := hex
  intro h2
  -- after deleting `z`, no edge changes the truth of "the sup norm is `1`"
  have hinv : ∀ {u v : Plane}, ((meshGraph N fresh anchors).deleteVerts {z}).Reaches u v →
      (Plane.supNorm u = 1 ↔ Plane.supNorm v = 1) := by
    rintro u v ⟨W, hW⟩
    induction hW with
    | nil => exact Iff.rfl
    | @cons a b c e W hl _ ih =>
      rw [Graph.deleteVerts_isLink] at hl
      exact (supNorm_eq_one_iff_of_isLink hN hfresh hsub hz hl.1
        (by simpa using hl.2.1) (by simpa using hl.2.2)).trans ih
  obtain ⟨c, hcV, hc1, hcz⟩ := exists_outer_vertex_ne (fresh := fresh) (anchors := anchors) hN z
  obtain ⟨d, hdV, hd1⟩ := exists_inner_vertex (fresh := fresh) (anchors := anchors) hN
  have hdz : d ≠ z := by
    rintro rfl
    exact hd1 (hfresh d hz)
  have := hinv ((h2.deleteVerts_connected' z).reaches
    (Graph.mem_deleteVerts_singleton_of_ne hcV hcz)
    (Graph.mem_deleteVerts_singleton_of_ne hdV hdz))
  exact hd1 (this.1 hc1)

/-- **`prop:anchored-square-mesh` clause 5 needs two distinct fresh points**, for
`Schoenflies.squareMesh` itself. -/
theorem not_isTwoConnected_squareMesh_of_fresh_subsingleton {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (hsub : ∀ u ∈ fresh, ∀ w ∈ fresh, u = w)
    (δ : ℝ) (anchors : List Plane) : ¬ (squareMesh δ fresh anchors).IsTwoConnected :=
  not_isTwoConnected_meshGraph_of_fresh_subsingleton (two_le_meshCount δ) hfresh hsub anchors

end Schoenflies

/-! ### A spanning 2-connected subgraph makes the whole graph 2-connected

The form in which every assembly out of `lem:union-two-connected` is finished: a chain of
unions produces *some* graph, and what the consumer wants is 2-connectivity of the graph it
started from. As long as the assembled graph is a subgraph that misses no vertex, the two
coincide — extra edges can only help connectivity. -/

namespace Graph

variable {α β : Type*} {H K : Graph α β}

/-- Connectedness passes up to a graph with the same vertices. -/
theorem Connected.of_spanning_le (hH : H.Connected) (hHK : H ≤ K) (hV : V(K) ⊆ V(H)) :
    K.Connected := by
  obtain ⟨u, hu⟩ := hH.nonempty
  exact Connected.of_hub (hHK.vertexSet_mono hu) fun x hx => (hH.reaches hu (hV hx)).mono hHK

/-- **2-connectivity passes up to a graph with the same vertices.** -/
theorem IsTwoConnected.of_le_of_vertexSet_subset (hH : H.IsTwoConnected) (hHK : H ≤ K)
    (hV : V(K) ⊆ V(H)) : K.IsTwoConnected where
  hasThreeVertices := hH.hasThreeVertices.mono hHK.vertexSet_mono
  connected := hH.connected.of_spanning_le hHK hV
  deleteVerts_connected := fun x _ =>
    (hH.deleteVerts_connected' x).of_spanning_le (deleteVerts_mono hHK _) (by
      simp only [vertexSet_deleteVerts]
      exact Set.sdiff_subset_sdiff_left hV)

end Graph

namespace Schoenflies

/-! ### Uniform coordinates

`prop:local-grid-attachment` asks for "sufficiently fine finite horizontal and vertical
coordinate sets in `W`, with at least two intervals in each direction". Equally spaced ones
serve, and they make the fineness a single division. -/

/-- The `i`-th of the equally spaced coordinates starting at `a` with step `h`. -/
noncomputable def uniformCoord (a h : ℝ) (i : ℕ) : ℝ := a + i * h

@[simp] theorem uniformCoord_zero (a h : ℝ) : uniformCoord a h 0 = a := by
  simp [uniformCoord]

theorem uniformCoord_strictMono {h : ℝ} (hh : 0 < h) (a : ℝ) :
    StrictMono (uniformCoord a h) := by
  intro i j hij
  have hlt : (i : ℝ) < j := by exact_mod_cast hij
  have := mul_lt_mul_of_pos_right hlt hh
  simp only [uniformCoord]
  linarith

theorem uniformCoord_le {h : ℝ} (hh : 0 < h) (a : ℝ) {i j : ℕ} (hij : i ≤ j) :
    uniformCoord a h i ≤ uniformCoord a h j := (uniformCoord_strictMono hh a).monotone hij

/-- **A preconnected set of reals inside `[a, a + k·h]` that avoids every coordinate
`a + i·h` has diameter less than `h`.** Two of its points more than `h` apart would straddle
one of the coordinates, and a preconnected subset of `ℝ` contains the interval between any two
of its points. -/
theorem abs_sub_lt_of_avoiding {a h : ℝ} (hh : 0 < h) {k : ℕ} {I : Set ℝ}
    (hI : IsPreconnected I) (hIsub : I ⊆ Set.Icc a (a + k * h))
    (havoid : ∀ i ≤ k, uniformCoord a h i ∉ I) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    |x - y| < h := by
  -- one direction suffices, and the other is the same with `x` and `y` exchanged
  have key : ∀ u ∈ I, ∀ v ∈ I, u ≤ v → v - u < h := by
    intro u hu v hv huv
    by_contra hcon
    push Not at hcon
    have hua : a ≤ u := (hIsub hu).1
    have hq0 : 0 ≤ (u - a) / h := div_nonneg (by linarith) hh.le
    set i : ℕ := ⌈(u - a) / h⌉₊ with hi
    have hile : (u - a) / h ≤ (i : ℝ) := Nat.le_ceil _
    have hilt : (i : ℝ) < (u - a) / h + 1 := Nat.ceil_lt_add_one hq0
    have hcu : u ≤ uniformCoord a h i := by
      have := (div_le_iff₀ hh).1 hile
      simp only [uniformCoord]; linarith
    have hcv : uniformCoord a h i ≤ v := by
      have : (i : ℝ) * h < (u - a) + h := by
        have := mul_lt_mul_of_pos_right hilt hh
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hh), one_mul] at this
        linarith
      simp only [uniformCoord]; linarith
    have hik : i ≤ k := by
      have hvk : v ≤ a + k * h := (hIsub hv).2
      have : (i : ℝ) * h ≤ (k : ℝ) * h := by
        simp only [uniformCoord] at hcv; linarith
      have : (i : ℝ) ≤ (k : ℝ) := le_of_mul_le_mul_right this hh
      exact_mod_cast this
    exact havoid i hik (hI.Icc_subset hu hv (Set.mem_Icc.2 ⟨hcu, hcv⟩))
  rcases le_total x y with hxy | hxy
  · rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    exact key x hx y hy hxy
  · rw [abs_of_nonneg (by linarith)]
    exact key y hy x hx hxy

/-! ### The local grid

`prop:local-grid-attachment` clauses 2 and 3: a rectangular grid on the window `W`, all of
whose closed rectangles are smaller than `ε`. Everything combinatorial about it — that it is
2-connected, that it stays 2-connected after subdivision, that it is a plane graph and that its
boundary is a distinguished cycle — comes from `Schoenflies/SquareMeshConnected.lean` and
`Schoenflies/SquareMeshFixed.lean`; the content added here is the fineness. -/

variable {p : Plane} {s ε : ℝ} {k : ℕ}

/-- The `x`-coordinates of the local grid on the closed square of centre `p` and radius `s`,
cut into `k` intervals. -/
noncomputable def localGridX (p : Plane) (s : ℝ) (k : ℕ) : ℕ → ℝ :=
  uniformCoord (p 0 - s) (2 * s / k)

/-- The `y`-coordinates of the local grid. -/
noncomputable def localGridY (p : Plane) (s : ℝ) (k : ℕ) : ℕ → ℝ :=
  uniformCoord (p 1 - s) (2 * s / k)

/-- The edges of the local grid, as a list of segments. -/
noncomputable def localGridEdges (p : Plane) (s : ℝ) (k : ℕ) : List Piece :=
  gridEdges (localGridX p s k) (localGridY p s k) k k

/-- **The local grid** of `prop:local-grid-attachment`: the uniform `k × k` rectangular grid on
the closed square `W` of centre `p` and radius `s`. -/
noncomputable def localGrid (p : Plane) (s : ℝ) (k : ℕ) : Graph Plane Piece :=
  gridGraph (localGridX p s k) (localGridY p s k) k k

theorem localGrid_eq (p : Plane) (s : ℝ) (k : ℕ) :
    localGrid p s k = pieceListGraph (localGridEdges p s k) := rfl

theorem localGrid_step_pos (hs : 0 < s) (hk : 1 ≤ k) : 0 < 2 * s / (k : ℝ) := by
  have : (0 : ℝ) < k := by exact_mod_cast hk
  positivity

theorem localGridX_strictMono (hs : 0 < s) (hk : 1 ≤ k) :
    StrictMono (localGridX p s k) := uniformCoord_strictMono (localGrid_step_pos hs hk) _

theorem localGridY_strictMono (hs : 0 < s) (hk : 1 ≤ k) :
    StrictMono (localGridY p s k) := uniformCoord_strictMono (localGrid_step_pos hs hk) _

@[simp] theorem localGridX_zero (p : Plane) (s : ℝ) (k : ℕ) :
    localGridX p s k 0 = p 0 - s := uniformCoord_zero _ _

@[simp] theorem localGridY_zero (p : Plane) (s : ℝ) (k : ℕ) :
    localGridY p s k 0 = p 1 - s := uniformCoord_zero _ _

theorem localGridX_last (hk : 1 ≤ k) : localGridX p s k k = p 0 + s := by
  have hkR : (k : ℝ) ≠ 0 := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    exact ne_of_gt this
  simp only [localGridX, uniformCoord]
  field_simp
  ring

theorem localGridY_last (hk : 1 ≤ k) : localGridY p s k k = p 1 + s := by
  have hkR : (k : ℝ) ≠ 0 := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    exact ne_of_gt this
  simp only [localGridY, uniformCoord]
  field_simp
  ring

/-- **`prop:local-grid-attachment`: the grid `K` is 2-connected.** -/
theorem localGrid_isTwoConnected (hs : 0 < s) (hk : 1 ≤ k) :
    (localGrid p s k).IsTwoConnected :=
  gridGraph_isTwoConnected hk hk
    (fun i _ => ne_of_lt ((localGridX_strictMono hs hk) (Nat.lt_succ_self i)))
    (fun j _ => ne_of_lt ((localGridY_strictMono hs hk) (Nat.lt_succ_self j)))

/-- **The grid stays 2-connected after subdivision** — the `lem:subdivision-ear-preserve` half
of the blueprint's argument, at these coordinates. The overlay of `K` with the skeleton of `Γ`
subdivides `K` at the crossing points, and no hypothesis on those points is needed. -/
theorem localGrid_subdivide_isTwoConnected (hs : 0 < s) (hk : 1 ≤ k) (points : List Plane) :
    (pieceListGraph (subdivide (localGridEdges p s k) points)).IsTwoConnected :=
  gridGraph_subdivide_isTwoConnected ((localGridX_strictMono hs hk).strictMonoOn _)
    ((localGridY_strictMono hs hk).strictMonoOn _) hk hk points

/-- **The grid is a plane graph**, drawn with straight edges. -/
theorem localGrid_isDrawing (hs : 0 < s) (hk : 1 ≤ k) :
    Graph.IsDrawing (localGrid p s k) segmentDrawing :=
  gridGraph_isDrawing ((localGridX_strictMono hs hk).strictMonoOn _)
    ((localGridY_strictMono hs hk).strictMonoOn _) hk hk

/-- **The outer boundary of the local grid is a cycle**, and it occupies the frame of `W`. -/
theorem localGrid_outer_cycle (hs : 0 < s) (hk : 1 ≤ k) :
    (localGrid p s k).IsCycleThrough
        (gridBoundaryLast (localGridX p s k) (localGridY p s k) k k)
        (gridBoundaryPt (localGridX p s k) (localGridY p s k) k k 0)
        (gridBoundaryPt (localGridX p s k) (localGridY p s k) k k (2 * k + 2 * k - 1))
        (gridBoundaryDetour (localGridX p s k) (localGridY p s k) k k) ∧
      Graph.edgesCover segmentDrawing
          (gridBoundaryLast (localGridX p s k) (localGridY p s k) k k ::
            gridBoundaryDetour (localGridX p s k) (localGridY p s k) k k)
        = (segment ℝ (Plane.mk (p 0 - s) (p 1 - s)) (Plane.mk (p 0 + s) (p 1 - s)) ∪
            segment ℝ (Plane.mk (p 0 + s) (p 1 - s)) (Plane.mk (p 0 + s) (p 1 + s))) ∪
          (segment ℝ (Plane.mk (p 0 - s) (p 1 + s)) (Plane.mk (p 0 + s) (p 1 + s)) ∪
            segment ℝ (Plane.mk (p 0 - s) (p 1 - s)) (Plane.mk (p 0 - s) (p 1 + s))) := by
  have hxmono : ∀ i, i < k → localGridX p s k i ≤ localGridX p s k (i + 1) :=
    fun i _ => (localGridX_strictMono hs hk).monotone (Nat.le_succ i)
  have hymono : ∀ j, j < k → localGridY p s k j ≤ localGridY p s k (j + 1) :=
    fun j _ => (localGridY_strictMono hs hk).monotone (Nat.le_succ j)
  refine ⟨gridGraph_isCycleThrough_boundary hk hk
    (((localGridX_strictMono hs hk).strictMonoOn _).injOn)
    (((localGridY_strictMono hs hk).strictMonoOn _).injOn), ?_⟩
  rw [edgesCover_gridBoundary hk hk hxmono hymono]
  simp only [gridPt, localGridX_zero, localGridY_zero, localGridX_last hk, localGridY_last hk]

/-! ### Fineness

The one quantitative clause: every closed grid rectangle is smaller than `ε`. Stated twice —
for the closed rectangle itself, which is the blueprint's wording, and for any connected subset
of `W` that avoids the grid, which is the form a face of the overlay arrives in. -/

/-- The closed grid rectangle with lower-left index `(i, j)`. -/
def localGridCell (p : Plane) (s : ℝ) (k i j : ℕ) : Set Plane :=
  {z | z 0 ∈ Set.Icc (localGridX p s k i) (localGridX p s k (i + 1)) ∧
    z 1 ∈ Set.Icc (localGridY p s k j) (localGridY p s k (j + 1))}

theorem dist_le_of_supNorm_bounds {x y : Plane} {c : ℝ} (h0 : |x 0 - y 0| ≤ c)
    (h1 : |x 1 - y 1| ≤ c) : dist x y ≤ Real.sqrt 2 * c := by
  have hsq : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  refine le_trans (dist_le_sqrt_two_mul_supNorm x y) (mul_le_mul_of_nonneg_left ?_ hsq.le)
  simp only [Plane.supNorm, Plane.sub_apply]
  exact max_le h0 h1

theorem dist_lt_of_supNorm_bounds {x y : Plane} {c : ℝ} (h0 : |x 0 - y 0| < c)
    (h1 : |x 1 - y 1| < c) : dist x y < Real.sqrt 2 * c := by
  have hsq : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  refine lt_of_le_of_lt (dist_le_sqrt_two_mul_supNorm x y) (mul_lt_mul_of_pos_left ?_ hsq)
  simp only [Plane.supNorm, Plane.sub_apply]
  exact max_lt h0 h1

/-- **`prop:local-grid-attachment` clause 3.** Every closed grid rectangle has diameter at most
`√2 · (2s/k)`. -/
theorem dist_le_of_mem_localGridCell {i j : ℕ} {x y : Plane}
    (hx : x ∈ localGridCell p s k i j) (hy : y ∈ localGridCell p s k i j) :
    dist x y ≤ Real.sqrt 2 * (2 * s / k) := by
  have hstep : localGridX p s k (i + 1) - localGridX p s k i = 2 * s / k := by
    simp only [localGridX, uniformCoord]; push_cast; ring
  have hstep' : localGridY p s k (j + 1) - localGridY p s k j = 2 * s / k := by
    simp only [localGridY, uniformCoord]; push_cast; ring
  refine dist_le_of_supNorm_bounds ?_ ?_
  · rw [abs_le]
    constructor <;> [linarith [hx.1.1, hy.1.2]; linarith [hx.1.2, hy.1.1]]
  · rw [abs_le]
    constructor <;> [linarith [hx.2.1, hy.2.2]; linarith [hx.2.2, hy.2.1]]

/-- The grid line at index `i` is part of the grid: a point of `W` whose first coordinate is a
grid coordinate lies on the grid. -/
theorem mem_cover_of_coord_eq (hs : 0 < s) (hk : 1 ≤ k) {z : Plane} {i : ℕ} (hi : i ≤ k)
    (hz : z ∈ Plane.closedSquare p s) (hz0 : z 0 = localGridX p s k i) :
    z ∈ cover (localGridEdges p s k) := by
  have hymono : ∀ j, j < k → localGridY p s k j ≤ localGridY p s k (j + 1) :=
    fun j _ => (localGridY_strictMono hs hk).monotone (Nat.le_succ j)
  have hbounds := Plane.closedSquare_eq_inter p s ▸ hz
  obtain ⟨-, h3, h4⟩ : _ ∧ (p 1 - s ≤ z 1) ∧ (z 1 ≤ p 1 + s) := hbounds
  have hmem : z ∈ segment ℝ (gridPt (localGridX p s k) (localGridY p s k) i 0)
      (gridPt (localGridX p s k) (localGridY p s k) i k) := by
    refine mem_segment_vert.2 ⟨hz0, ?_⟩
    rw [segment_eq_Icc ((localGridY_strictMono hs hk).monotone (Nat.zero_le k))]
    rw [localGridY_zero, localGridY_last hk]
    exact ⟨h3, h4⟩
  rw [← iUnion_gridVEdge_seg hk hymono i] at hmem
  simp only [Set.mem_iUnion, Set.mem_Iio, exists_prop] at hmem
  obtain ⟨j, hj, hzj⟩ := hmem
  exact mem_cover_iff.2 ⟨_, gridVEdge_mem_gridEdges hi hj hk, hzj⟩

/-- The same for the second coordinate. -/
theorem mem_cover_of_coord_eq' (hs : 0 < s) (hk : 1 ≤ k) {z : Plane} {j : ℕ} (hj : j ≤ k)
    (hz : z ∈ Plane.closedSquare p s) (hz1 : z 1 = localGridY p s k j) :
    z ∈ cover (localGridEdges p s k) := by
  have hxmono : ∀ i, i < k → localGridX p s k i ≤ localGridX p s k (i + 1) :=
    fun i _ => (localGridX_strictMono hs hk).monotone (Nat.le_succ i)
  have hbounds := Plane.closedSquare_eq_inter p s ▸ hz
  obtain ⟨⟨h1, h2⟩, -⟩ : ((p 0 - s ≤ z 0) ∧ (z 0 ≤ p 0 + s)) ∧ _ := hbounds
  have hmem : z ∈ segment ℝ (gridPt (localGridX p s k) (localGridY p s k) 0 j)
      (gridPt (localGridX p s k) (localGridY p s k) k j) := by
    refine mem_segment_horiz.2 ⟨hz1, ?_⟩
    rw [segment_eq_Icc ((localGridX_strictMono hs hk).monotone (Nat.zero_le k))]
    rw [localGridX_zero, localGridX_last hk]
    exact ⟨h1, h2⟩
  rw [← iUnion_gridHEdge_seg hk hxmono j] at hmem
  simp only [Set.mem_iUnion, Set.mem_Iio, exists_prop] at hmem
  obtain ⟨i, hi, hzi⟩ := hmem
  exact mem_cover_iff.2 ⟨_, gridHEdge_mem_gridEdges hi hj hk, hzi⟩

/-- **`prop:local-grid-attachment` clause 3, in the form the overlay consumes.** A connected
subset of the window `W` that avoids the grid has diameter less than `√2 · (2s/k)`: it is
trapped inside one open grid rectangle, coordinate by coordinate. -/
theorem dist_lt_of_avoiding_localGrid (hs : 0 < s) (hk : 1 ≤ k) {F : Set Plane}
    (hF : IsPreconnected F) (hFW : F ⊆ Plane.closedSquare p s)
    (havoid : ∀ z ∈ F, z ∉ cover (localGridEdges p s k)) {x y : Plane}
    (hx : x ∈ F) (hy : y ∈ F) : dist x y < Real.sqrt 2 * (2 * s / k) := by
  have hstep := localGrid_step_pos hs hk
  have hcoord : ∀ (m : Fin 2) (a : ℝ), (∀ i ≤ k, uniformCoord a (2 * s / k) i ∉
      ((fun z : Plane => z m) '' F)) →
      (∀ z ∈ F, a ≤ z m ∧ z m ≤ a + k * (2 * s / k)) →
      |x m - y m| < 2 * s / k := by
    intro m a havd hbd
    refine abs_sub_lt_of_avoiding hstep (hF.image _ (Plane.continuous_coord m).continuousOn)
      ?_ havd ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    rintro _ ⟨z, hz, rfl⟩
    exact Set.mem_Icc.2 (hbd z hz)
  have hbdX : ∀ z ∈ F, (p 0 - s) ≤ z 0 ∧ z 0 ≤ (p 0 - s) + k * (2 * s / k) := by
    intro z hz
    have hbounds := Plane.closedSquare_eq_inter p s ▸ hFW hz
    obtain ⟨⟨h1, h2⟩, -⟩ : ((p 0 - s ≤ z 0) ∧ (z 0 ≤ p 0 + s)) ∧ _ := hbounds
    refine ⟨h1, ?_⟩
    have := localGridX_last (p := p) (s := s) hk
    simp only [localGridX, uniformCoord] at this
    linarith
  have hbdY : ∀ z ∈ F, (p 1 - s) ≤ z 1 ∧ z 1 ≤ (p 1 - s) + k * (2 * s / k) := by
    intro z hz
    have hbounds := Plane.closedSquare_eq_inter p s ▸ hFW hz
    obtain ⟨-, h3, h4⟩ : _ ∧ (p 1 - s ≤ z 1) ∧ (z 1 ≤ p 1 + s) := hbounds
    refine ⟨h3, ?_⟩
    have := localGridY_last (p := p) (s := s) hk
    simp only [localGridY, uniformCoord] at this
    linarith
  refine dist_lt_of_supNorm_bounds (hcoord 0 (p 0 - s) ?_ hbdX) (hcoord 1 (p 1 - s) ?_ hbdY)
  · rintro i hi ⟨z, hz, hzeq⟩
    exact havoid z hz (mem_cover_of_coord_eq hs hk hi (hFW hz)
      (by simpa [localGridX] using hzeq))
  · rintro j hj ⟨z, hz, hzeq⟩
    exact havoid z hz (mem_cover_of_coord_eq' hs hk hj (hFW hz)
      (by simpa [localGridY] using hzeq))

/-! ### Choosing the mesh

`prop:local-grid-attachment` clause 3 asks for rectangles of diameter `< ε`. -/

/-- The number of intervals per side of `W` that makes every grid rectangle smaller than
`ε`. -/
noncomputable def localGridCount (s ε : ℝ) : ℕ := max 1 (⌈2 * Real.sqrt 2 * s / ε⌉₊ + 1)

theorem one_le_localGridCount (s ε : ℝ) : 1 ≤ localGridCount s ε := le_max_left _ _

theorem localGridCount_spec (hε : 0 < ε) :
    Real.sqrt 2 * (2 * s / (localGridCount s ε : ℕ)) < ε := by
  have hN : (1 : ℝ) ≤ (localGridCount s ε : ℕ) := by
    exact_mod_cast one_le_localGridCount s ε
  have hN0 : (0 : ℝ) < (localGridCount s ε : ℕ) := by linarith
  have h1 : 2 * Real.sqrt 2 * s / ε < ((localGridCount s ε : ℕ) : ℝ) := by
    calc 2 * Real.sqrt 2 * s / ε ≤ (⌈2 * Real.sqrt 2 * s / ε⌉₊ : ℝ) := Nat.le_ceil _
      _ < (⌈2 * Real.sqrt 2 * s / ε⌉₊ : ℝ) + 1 := by linarith
      _ ≤ ((localGridCount s ε : ℕ) : ℝ) := by
          exact_mod_cast le_max_right 1 (⌈2 * Real.sqrt 2 * s / ε⌉₊ + 1)
  rw [div_lt_iff₀ hε] at h1
  rw [mul_div_assoc', div_lt_iff₀ hN0]
  linarith

/-- **`prop:local-grid-attachment` clauses 2 and 3, packaged.** On the window `W` of centre `p`
and radius `s` there is a rectangular grid — 2-connected, still 2-connected after any
subdivision, a plane graph — every closed rectangle of which has diameter `< ε`. -/
theorem localGrid_fine (hs : 0 < s) (hε : 0 < ε) :
    (localGrid p s (localGridCount s ε)).IsTwoConnected ∧
      Graph.IsDrawing (localGrid p s (localGridCount s ε)) segmentDrawing ∧
      ∀ i j : ℕ, ∀ x ∈ localGridCell p s (localGridCount s ε) i j,
        ∀ y ∈ localGridCell p s (localGridCount s ε) i j, dist x y < ε := by
  have hk := one_le_localGridCount s ε
  refine ⟨localGrid_isTwoConnected hs hk, localGrid_isDrawing hs hk, fun i j x hx y hy => ?_⟩
  exact lt_of_le_of_lt (dist_le_of_mem_localGridCell hx hy) (localGridCount_spec hε)

end Schoenflies
