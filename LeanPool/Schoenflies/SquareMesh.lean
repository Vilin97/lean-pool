/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.OverlayGraph
public import LeanPool.Schoenflies.ModelCurve
public import LeanPool.Schoenflies.Graph.OuterFace
public import LeanPool.Schoenflies.Graph.Redrawing

/-!
# The anchored square mesh

The geometric core of Proposition `prop:anchored-square-mesh`, in vocabulary that exists today:
Part II's cellulations, `V_boundary` and fresh points `u(𝒜)` are not built here, so the mesh is
stated as a **finite plane graph with a straight-line drawing**, with the clauses of the
proposition as separate theorems about it.

## The construction

`squareMesh δ fresh anchors` is `meshCount δ` concentric ring frames of radii
`1/N, 2/N, …, 1` inside `Q = [-1,1]²`, together with one full-length radial spoke
`[z, N⁻¹ • z]` at each fresh boundary point `z`. The list of segments is handed to
`overlayGraph` (Lemma 3.7), which subdivides at every crossing; the anchors are added to the
cut points, which is what makes each of them a vertex.

**This is not literally the blueprint's construction, and the difference is deliberate.** The
blueprint has one collar `λ ≤ ‖x‖∞ ≤ 1` plus a rectangular grid filling `λQ`. Here the collar
is repeated `N` times and there is no grid at all: the innermost square `N⁻¹ Q` is a *single*
cell, of diameter `2√2/N < δ`. That removes the "choose fine enough horizontal and vertical
coordinates, including the four corners and all the points `λ z_i`" step entirely, and makes
the whole mesh radial, so that one estimate — `‖tz - sw‖ ≤ t‖z - w‖ + |t - s|‖w‖`, the
blueprint's own — covers every cell. Nothing downstream can tell the difference: the clauses
are the interface.

The blueprint's cyclic ordering of the fresh points is likewise gone. Where it says "choose
`z_0, …, z_{m-1}` in cyclic order so that each boundary arc between consecutive ones has
diameter `< δ/4`", this module takes the order-free consequence as a hypothesis,
`FreshDense fresh δ`: *every connected subset of `S` avoiding all the fresh points has diameter
at most `δ/2`*. A set-level statement needs no ordering, and it is exactly what the blueprint's
own argument (parametrize `S` by a circle, cut it into small arcs, put one fresh point inside
each) produces.

## What is proved, and what is not

The clauses about faces, anchors, edges reaching `S` and connectedness of `|T| ∖ S` are proved
in full. Two gaps, both stated plainly:

* **The outer cycle is proved only as a point set.** `squareMesh_cover_outerEdges` says the
  edges whose segments lie on `S` occupy exactly `S`. That these edges form a **cycle** of the
  graph is *not* proved: it needs the fresh points, the anchors and the four corners put in
  cyclic order along `S`, which is precisely the ordering this construction was designed to
  avoid. A later module wanting the outer cycle must build it.
* **2-connectivity is not proved at all.** It is not present as a hypothesis either — a
  hypothesis restating the goal would be worthless. The route is the blueprint's: the innermost
  ring is a cycle, and each annulus between consecutive rings is added one rectangle at a time
  by `Graph.IsTwoConnected.union`, each added cycle sharing at least two vertices with what is
  already there. Nothing in this module obstructs it.

Connectedness of `|T| ∖ S` needs at least one fresh point (`hz₀ : z₀ ∈ fresh`): with no spokes
the rings are disjoint frames.

## Blueprint

* `ringSet`, `ringPieces`, `spokePiece`, `meshSegments` — the mesh as a list of segments.
* `meshGraph`, `squareMesh` — Proposition "Anchored square mesh", the construction itself.
* `FreshDense` — the order-free form of "consecutive fresh points bound an arc of diameter
  `< δ/4`".
* `squareMesh_face_small` — clause 1: every bounded 2-cell has diameter `< δ`, and lies in `Q`.
* `squareMesh_anchor_mem_vertexSet` — clause 2: every boundary vertex survives.
* `squareMesh_inner_edge_at_fresh`, `squareMesh_unique_inner_edge` — clauses 3 and 4: a new
  internal edge meeting `S` ends at a fresh point, and exactly one such edge is incident with
  each fresh point.
* `squareMesh_cover_outerEdges` — the point-set half of "`S` is the outer cycle" (see above).
* `squareMesh_isConnected_diff` — clause 6: `|T| ∖ S` is connected.
* `radial_diam_bound` — the blueprint's radial estimate, isolated from all graph language.
* `subdivide_covers_source`, `subdivide_end_of_mem` — two general facts about `subdivide` that
  belong in `Schoenflies/Subdivide.lean`.
-/

public section

open Metric Set
open scoped Graph

namespace Schoenflies

/-! ### Rings: the frame of a square about the origin -/

/-- The frame of the square of radius `r` about the origin. For `r = 1` this is definitionally
`modelCurve`. -/
def ringSet (r : ℝ) : Set Plane := {x : Plane | Plane.supNorm x = r}

theorem ringSet_one : ringSet 1 = modelCurve := rfl

/-- The four sides of the square of radius `r`, as a list of pieces. -/
@[expose] def ringPieces (r : ℝ) : List Piece :=
  [(Plane.mk r r, Plane.mk (-r) r),
   (Plane.mk (-r) r, Plane.mk (-r) (-r)),
   (Plane.mk (-r) (-r), Plane.mk r (-r)),
   (Plane.mk r (-r), Plane.mk r r)]

theorem segment_symm_Icc {r : ℝ} (hr : 0 ≤ r) :
    segment ℝ (-r) r = Icc (-r) r := segment_eq_Icc (by linarith)

theorem segment_symm_Icc' {r : ℝ} (hr : 0 ≤ r) :
    segment ℝ r (-r) = Icc (-r) r := by
  rw [segment_symm]; exact segment_symm_Icc hr

/-- The four sides of the square of radius `r` occupy exactly its frame. -/
theorem cover_ringPieces {r : ℝ} (hr : 0 ≤ r) : cover (ringPieces r) = ringSet r := by
  ext x
  simp only [ringPieces, cover_cons, cover_nil, union_empty, mem_union, Piece.seg,
    mem_segment_horiz, mem_segment_vert, segment_symm_Icc hr, segment_symm_Icc' hr,
    mem_Icc, ringSet, Set.mem_ofPred_eq, Plane.supNorm]
  -- On each side one coordinate is pinned to `±r` and the other is confined to `[-r, r]`;
  -- which of the two is pinned is the only difference between the four sides.
  have hleft : ∀ u v : ℝ, |u| = r → |v| ≤ r → max |u| |v| = r := by
    intro u v hu hv; rw [hu]; exact max_eq_left hv
  have hright : ∀ u v : ℝ, |u| ≤ r → |v| = r → max |u| |v| = r := by
    intro u v hu hv; rw [hv]; exact max_eq_right hu
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact hright _ _ (abs_le.2 ⟨h2, h3⟩) (by rw [h1, abs_of_nonneg hr])
    · exact hleft _ _ (by rw [h1, abs_neg, abs_of_nonneg hr]) (abs_le.2 ⟨h2, h3⟩)
    · exact hright _ _ (abs_le.2 ⟨h2, h3⟩) (by rw [h1, abs_neg, abs_of_nonneg hr])
    · exact hleft _ _ (by rw [h1, abs_of_nonneg hr]) (abs_le.2 ⟨h2, h3⟩)
  · intro h
    have h0 : |x 0| ≤ r := h ▸ le_max_left _ _
    have h1 : |x 1| ≤ r := h ▸ le_max_right _ _
    rcases max_choice |x 0| |x 1| with hm | hm
    · rcases abs_eq hr |>.1 (hm.symm.trans h) with he | he
      · exact Or.inr (Or.inr (Or.inr ⟨he, (abs_le.1 h1).1, (abs_le.1 h1).2⟩))
      · exact Or.inr (Or.inl ⟨he, (abs_le.1 h1).1, (abs_le.1 h1).2⟩)
    · rcases abs_eq hr |>.1 (hm.symm.trans h) with he | he
      · exact Or.inl ⟨he, (abs_le.1 h0).1, (abs_le.1 h0).2⟩
      · exact Or.inr (Or.inr (Or.inl ⟨he, (abs_le.1 h0).1, (abs_le.1 h0).2⟩))

theorem mk_ne_mk_of_fst {a b c d : ℝ} (h : a ≠ c) : Plane.mk a b ≠ Plane.mk c d := fun he => by
  rw [← Plane.mk_zero a b, he, Plane.mk_zero] at h; exact h rfl

theorem mk_ne_mk_of_snd {a b c d : ℝ} (h : b ≠ d) : Plane.mk a b ≠ Plane.mk c d := fun he => by
  rw [← Plane.mk_one a b, he, Plane.mk_one] at h; exact h rfl

/-- A ring of positive radius has nondegenerate sides. -/
theorem ringPieces_nondeg {r : ℝ} (hr : 0 < r) : ∀ P ∈ ringPieces r, P.Nondeg := by
  have hne : (r : ℝ) ≠ -r := by intro h; linarith
  intro P hP
  simp only [ringPieces, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl
  · exact mk_ne_mk_of_fst hne
  · exact mk_ne_mk_of_snd hne
  · exact mk_ne_mk_of_fst hne.symm
  · exact mk_ne_mk_of_snd hne.symm

/-- Scaling a ring: `t • x` has sup norm `|t|` times that of `x`. -/
theorem mem_ringSet_smul {t r : ℝ} (ht : 0 ≤ t) {x : Plane} (hx : x ∈ ringSet r) :
    t • x ∈ ringSet (t * r) := by
  change Plane.supNorm (t • x) = t * r
  rw [Plane.supNorm_smul, abs_of_nonneg ht]
  exact congrArg (fun s => t * s) hx

theorem supNorm_smul_of_mem_modelCurve {t : ℝ} (ht : 0 ≤ t) {z : Plane} (hz : z ∈ modelCurve) :
    Plane.supNorm (t • z) = t := by
  rw [Plane.supNorm_smul, abs_of_nonneg ht, show Plane.supNorm z = 1 from hz, mul_one]

theorem inv_cast_lt_one {N : ℕ} (hN : 2 ≤ N) : ((N : ℝ)⁻¹) < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hN)

theorem inv_cast_pos {N : ℕ} (hN : 2 ≤ N) : (0 : ℝ) < (N : ℝ)⁻¹ := by
  have : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hN
  positivity

/-! ### Radial segments

Every point of a segment between two multiples of `z` is itself a multiple of `z`, with the
coefficient running through the corresponding real segment. This is the only fact about spokes
the whole module uses: along a spoke the coefficient — equivalently, by
`supNorm_smul_of_mem_modelCurve`, the sup norm — is a faithful coordinate. -/

theorem mem_smul_segment {a b : ℝ} {z x : Plane} :
    x ∈ segment ℝ (a • z) (b • z) ↔ ∃ t ∈ segment ℝ a b, x = t • z := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq, rfl⟩
    refine ⟨p * a + q * b, ⟨p, q, hp, hq, hpq, rfl⟩, ?_⟩
    module
  · rintro ⟨t, ⟨p, q, hp, hq, hpq, rfl⟩, rfl⟩
    refine ⟨p, q, hp, hq, hpq, ?_⟩
    module

/-- The radial segment from `a • z` to `b • z`, as a set of multiples of `z`. -/
theorem smul_segment_eq_image {a b : ℝ} (hab : a ≤ b) (z : Plane) :
    segment ℝ (a • z) (b • z) = (fun t : ℝ => t • z) '' Icc a b := by
  ext x
  rw [mem_smul_segment, segment_eq_Icc hab]
  simp only [mem_image]
  exact ⟨fun ⟨t, ht, hx⟩ => ⟨t, ht, hx.symm⟩, fun ⟨t, ht, hx⟩ => ⟨t, ht, hx.symm⟩⟩

/-! ### Spokes -/

/-- The radial spoke at a boundary point `z`, running from `z` inwards to `N⁻¹ • z`. -/
noncomputable def spokePiece (N : ℕ) (z : Plane) : Piece := (z, ((N : ℝ)⁻¹) • z)

/-- A spoke is the set of multiples `t • z` with `N⁻¹ ≤ t ≤ 1`. -/
theorem spokePiece_seg {N : ℕ} (hN : 2 ≤ N) (z : Plane) :
    (spokePiece N z).seg = (fun t : ℝ => t • z) '' Icc ((N : ℝ)⁻¹) 1 := by
  have key : (spokePiece N z).seg = segment ℝ (((N : ℝ)⁻¹) • z) ((1 : ℝ) • z) := by
    rw [Piece.seg, spokePiece, one_smul, segment_symm]
  rw [key, smul_segment_eq_image (inv_cast_lt_one hN).le]

/-- A spoke meets the model curve exactly at its outer end. -/
theorem spokePiece_inter_modelCurve {N : ℕ} (hN : 2 ≤ N) {z : Plane} (hz : z ∈ modelCurve) :
    (spokePiece N z).seg ∩ modelCurve = {z} := by
  ext x
  simp only [mem_inter_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hx, hxS⟩
    rw [spokePiece_seg hN] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    have h0 : (0 : ℝ) ≤ t := le_trans (inv_cast_pos hN).le ht.1
    have : t = 1 := by
      have hval := supNorm_smul_of_mem_modelCurve h0 hz
      rw [show Plane.supNorm (t • z) = 1 from hxS] at hval
      exact hval.symm
    simp only [this, one_smul]
  · rintro rfl
    exact ⟨left_mem_segment ℝ _ _, hz⟩

/-- A spoke lies inside the closed square. -/
theorem spokePiece_subset_closedSquare {N : ℕ} (hN : 2 ≤ N) {z : Plane} (hz : z ∈ modelCurve) :
    (spokePiece N z).seg ⊆ Plane.closedSquare 0 1 := by
  rw [spokePiece_seg hN]
  rintro _ ⟨t, ht, rfl⟩
  have h0 : (0 : ℝ) ≤ t := le_trans (inv_cast_pos hN).le ht.1
  exact mem_closedSquare_zero_one.2 (by rw [supNorm_smul_of_mem_modelCurve h0 hz]; exact ht.2)

theorem spokePiece_nondeg {N : ℕ} (hN : 2 ≤ N) {z : Plane} (hz : z ∈ modelCurve) :
    (spokePiece N z).Nondeg := by
  intro h
  have h2 : Plane.supNorm (((N : ℝ)⁻¹) • z) = (N : ℝ)⁻¹ :=
    supNorm_smul_of_mem_modelCurve (inv_cast_pos hN).le hz
  rw [show (((N : ℝ)⁻¹) • z) = z from h.symm, show Plane.supNorm z = 1 from hz] at h2
  have := inv_cast_lt_one hN
  linarith

/-! ### Two more facts about `subdivide`

Both are general and belong beside the others in `Schoenflies/Subdivide.lean`; they are here
because that module is on `main`.

`subdivide_covers_source` refines `subdivide_cover`: a point of a *named* source piece lies on
a piece of the subdivision *inside that source*. Without the "inside that source" clause one
cannot tell, of a point where two sources cross, which of them the piece through it came from
— and the whole description of the mesh's edges is by their source.

`subdivide_end_of_mem` is the converse of `subdivide_avoids`: a cut point that lies on a source
piece is not merely absent from every interior, it is an **endpoint** of a piece inside that
source. That is what makes a prescribed point a vertex of the overlay graph. -/

theorem cover_map {α : Type*} (f : α → Piece) (l : List α) :
    cover (l.map f) = ⋃ a ∈ l, (f a).seg := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, cover_cons, ih]; simp

theorem cover_flatMap' {α : Type*} (f : α → List Piece) (l : List α) :
    cover (l.flatMap f) = ⋃ a ∈ l, cover (f a) := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, cover_append, ih]; simp

theorem mem_cover_iff {x : Plane} {l : List Piece} : x ∈ cover l ↔ ∃ P ∈ l, x ∈ P.seg := by
  simp only [cover, mem_iUnion, exists_prop]

/-- Cutting a piece at a point of it makes that point an endpoint of one of the halves. -/
theorem splitAt_end_of_mem (p : Plane) (P : Piece) (hmem : p ∈ P.seg) :
    ∃ R ∈ splitAt p P, R.seg ⊆ P.seg ∧ (p = R.1 ∨ p = R.2) := by
  classical
  by_cases hp : p ∈ P.interior
  · refine ⟨(P.1, p), by rw [splitAt, ite_eq_left hp]; simp, ?_, Or.inr rfl⟩
    exact (convex_segment P.1 P.2).segment_subset (left_mem_segment ℝ _ _) hmem
  · refine ⟨P, by rw [splitAt, ite_eq_right hp]; simp, subset_rfl, ?_⟩
    by_contra hcon
    push Not at hcon
    exact hp (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hmem)

/-- Cutting anywhere keeps an endpoint an endpoint. -/
theorem splitAt_preserves_end (q : Plane) {p : Plane} {P : Piece} (h : p = P.1 ∨ p = P.2) :
    ∃ R ∈ splitAt q P, R.seg ⊆ P.seg ∧ (p = R.1 ∨ p = R.2) := by
  classical
  by_cases hq : q ∈ P.interior
  · have hqseg : q ∈ P.seg := openSegment_subset_segment ℝ _ _ hq
    rcases h with rfl | rfl
    · refine ⟨(P.1, q), by rw [splitAt, ite_eq_left hq]; simp, ?_, Or.inl rfl⟩
      exact (convex_segment P.1 P.2).segment_subset (left_mem_segment ℝ _ _) hqseg
    · refine ⟨(q, P.2), by rw [splitAt, ite_eq_left hq]; simp, ?_, Or.inr rfl⟩
      exact (convex_segment P.1 P.2).segment_subset hqseg (right_mem_segment ℝ _ _)
  · exact ⟨P, by rw [splitAt, ite_eq_right hq]; simp, subset_rfl, h⟩

theorem splitAllAt_preserves_end (q : Plane) {p : Plane} {P : Piece} {pieces : List Piece}
    (h : ∃ R ∈ pieces, R.seg ⊆ P.seg ∧ (p = R.1 ∨ p = R.2)) :
    ∃ R ∈ splitAllAt q pieces, R.seg ⊆ P.seg ∧ (p = R.1 ∨ p = R.2) := by
  obtain ⟨R, hR, hsub, hend⟩ := h
  obtain ⟨R', hR', hsub', hend'⟩ := splitAt_preserves_end q hend
  exact ⟨R', List.mem_flatMap.2 ⟨R, hR, hR'⟩, hsub'.trans hsub, hend'⟩

theorem subdivide_preserves_end (points : List Plane) {pieces : List Piece} {p : Plane}
    {P : Piece} (h : ∃ R ∈ pieces, R.seg ⊆ P.seg ∧ (p = R.1 ∨ p = R.2)) :
    ∃ R ∈ subdivide pieces points, R.seg ⊆ P.seg ∧ (p = R.1 ∨ p = R.2) := by
  induction points generalizing pieces with
  | nil => exact h
  | cons q qs ih => exact ih (splitAllAt_preserves_end q h)

/-- Every point of a source piece lies on a piece of the subdivision contained in that
source. -/
theorem subdivide_covers_source (points : List Plane) : ∀ (pieces : List Piece) (P : Piece),
    P ∈ pieces → ∀ x ∈ P.seg,
      ∃ Q ∈ subdivide pieces points, x ∈ Q.seg ∧ Q.seg ⊆ P.seg := by
  induction points with
  | nil => exact fun _ P hP x hx => ⟨P, hP, hx, subset_rfl⟩
  | cons q qs ih =>
    intro pieces P hP x hx
    obtain ⟨P', hP', hxP'⟩ :=
      mem_cover_iff.1 (show x ∈ cover (splitAt q P) by rw [splitAt_cover]; exact hx)
    obtain ⟨Q, hQ, hxQ, hsub⟩ :=
      ih (splitAllAt q pieces) P' (List.mem_flatMap.2 ⟨P, hP, hP'⟩) x hxP'
    exact ⟨Q, hQ, hxQ, hsub.trans (splitAt_subset q P P' hP').1⟩

/-- **A cut point on a source piece is an endpoint of a piece of the subdivision inside it.** -/
theorem subdivide_end_of_mem (points : List Plane) : ∀ (pieces : List Piece) (p : Plane),
    p ∈ points → ∀ P ∈ pieces, p ∈ P.seg →
      ∃ Q ∈ subdivide pieces points, Q.seg ⊆ P.seg ∧ (p = Q.1 ∨ p = Q.2) := by
  induction points with
  | nil => intro _ p hp; simp at hp
  | cons q qs ih =>
    intro pieces p hp P hP hmem
    rcases List.mem_cons.1 hp with rfl | hp'
    · -- the cut happens at this step, and later cuts keep the new endpoint an endpoint
      obtain ⟨R, hR, hsub, hend⟩ := splitAt_end_of_mem p P hmem
      exact subdivide_preserves_end qs ⟨R, List.mem_flatMap.2 ⟨P, hP, hR⟩, hsub, hend⟩
    · obtain ⟨P', hP', hpP'⟩ :=
        mem_cover_iff.1 (show p ∈ cover (splitAt q P) by rw [splitAt_cover]; exact hmem)
      obtain ⟨Q, hQ, hsub, hend⟩ :=
        ih (splitAllAt q pieces) p hp' P' (List.mem_flatMap.2 ⟨P, hP, hP'⟩) hpP'
      exact ⟨Q, hQ, hsub.trans (splitAt_subset q P P' hP').1, hend⟩

/-! ### Enlarging the list of cut points

Both cut-point conditions ask only that certain points *be* in the list, so both survive
adding more. That is what lets the mesh prescribe extra vertices — the anchors — on top of the
cut points the overlay itself needs. -/

theorem EndsAreCut.mono {pieces : List Piece} {points points' : List Plane}
    (h : EndsAreCut pieces points) (hsub : points ⊆ points') : EndsAreCut pieces points' :=
  fun P hP z hz => hsub (h P hP z hz)

theorem MeetsAreCut.mono {pieces : List Piece} {points points' : List Plane}
    (h : MeetsAreCut pieces points) (hsub : points ⊆ points') : MeetsAreCut pieces points' := by
  intro P hP Q hQ hPQ hne
  obtain ⟨u, v, huv, hu, hv⟩ := h P hP Q hQ hPQ hne
  exact ⟨u, v, huv, hsub hu, hsub hv⟩

/-! ### The mesh, as a list of segments

`N` concentric ring frames of radii `1/N, 2/N, …, 1`, and one full-length radial spoke at each
fresh boundary point. There is no rectangular grid: the innermost region is the square of
radius `1/N`, which is a single cell of diameter `2√2/N`, so filling it is unnecessary once `N`
is large. That is the one deviation from the blueprint's construction, and it removes the whole
"choose horizontal and vertical coordinates" step. -/

/-- The radii of the `N` concentric rings, `1/N, 2/N, …, 1`. -/
noncomputable def meshRadii (N : ℕ) : List ℝ :=
  (List.range N).map fun j : ℕ => ((j : ℝ) + 1) / (N : ℝ)

theorem mem_meshRadii {N : ℕ} {r : ℝ} :
    r ∈ meshRadii N ↔ ∃ j < N, r = ((j : ℝ) + 1) / N := by
  rw [meshRadii]
  constructor
  · intro hr
    obtain ⟨j, hj, hval⟩ := List.mem_map.1 hr
    exact ⟨j, List.mem_range.1 hj, hval.symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩

theorem meshRadii_pos {N : ℕ} (hN : 2 ≤ N) {r : ℝ} (hr : r ∈ meshRadii N) : 0 < r := by
  obtain ⟨j, _, rfl⟩ := mem_meshRadii.1 hr
  have : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hN
  positivity

theorem meshRadii_le_one {N : ℕ} (hN : 2 ≤ N) {r : ℝ} (hr : r ∈ meshRadii N) : r ≤ 1 := by
  obtain ⟨j, hj, rfl⟩ := mem_meshRadii.1 hr
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hN
  rw [div_le_one hN0]
  have : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
  linarith

theorem one_mem_meshRadii {N : ℕ} (hN : 2 ≤ N) : (1 : ℝ) ∈ meshRadii N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hN
  refine mem_meshRadii.2 ⟨N - 1, Nat.sub_lt (by omega) one_pos, ?_⟩
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ N := by omega
    rw [Nat.cast_sub h1, Nat.cast_one]
  rw [hcast]
  field_simp
  ring

theorem inv_mem_meshRadii {N : ℕ} (hN : 2 ≤ N) : ((N : ℝ)⁻¹) ∈ meshRadii N := by
  refine mem_meshRadii.2 ⟨0, by omega, ?_⟩
  norm_num

/-- The mesh: the four sides of each ring, and one radial spoke at each fresh point. -/
noncomputable def meshSegments (N : ℕ) (fresh : List Plane) : List Piece :=
  (meshRadii N).flatMap ringPieces ++ fresh.map (spokePiece N)

theorem mem_meshSegments {N : ℕ} {fresh : List Plane} {P : Piece} :
    P ∈ meshSegments N fresh ↔
      (∃ r ∈ meshRadii N, P ∈ ringPieces r) ∨ ∃ z ∈ fresh, P = spokePiece N z := by
  simp only [meshSegments, List.mem_append, List.mem_flatMap, List.mem_map]
  exact or_congr Iff.rfl ⟨fun ⟨z, hz, h⟩ => ⟨z, hz, h.symm⟩, fun ⟨z, hz, h⟩ => ⟨z, hz, h.symm⟩⟩

theorem cover_meshSegments {N : ℕ} (hN : 2 ≤ N) (fresh : List Plane) :
    cover (meshSegments N fresh) =
      (⋃ r ∈ meshRadii N, ringSet r) ∪ ⋃ z ∈ fresh, (spokePiece N z).seg := by
  rw [meshSegments, cover_append, cover_flatMap', cover_map]
  congr 1
  exact iUnion₂_congr fun r hr => cover_ringPieces (meshRadii_pos hN hr).le

theorem meshSegments_nondeg {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) : ∀ P ∈ meshSegments N fresh, P.Nondeg := by
  intro P hP
  rcases mem_meshSegments.1 hP with ⟨r, hr, hPr⟩ | ⟨z, hz, rfl⟩
  · exact ringPieces_nondeg (meshRadii_pos hN hr) P hPr
  · exact spokePiece_nondeg hN (hfresh z hz)

/-- A side of a ring lies on that ring. -/
theorem ringPieces_seg_subset {r : ℝ} (hr : 0 ≤ r) {P : Piece} (hP : P ∈ ringPieces r) :
    P.seg ⊆ ringSet r := by
  rw [← cover_ringPieces hr]
  exact fun x hx => mem_cover_iff.2 ⟨P, hP, hx⟩

/-- Every mesh segment lies inside the closed square. -/
theorem meshSegments_subset_closedSquare {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) {P : Piece} (hP : P ∈ meshSegments N fresh) :
    P.seg ⊆ Plane.closedSquare 0 1 := by
  rcases mem_meshSegments.1 hP with ⟨r, hr, hPr⟩ | ⟨z, hz, rfl⟩
  · refine (ringPieces_seg_subset (meshRadii_pos hN hr).le hPr).trans ?_
    exact fun x hx => mem_closedSquare_zero_one.2 (le_of_eq_of_le hx (meshRadii_le_one hN hr))
  · exact spokePiece_subset_closedSquare hN (hfresh z hz)

/-! ### The mesh as a plane graph

The cut points are the ones `exists_cut_points` supplies for the mesh segments, *together with*
the prescribed anchors. Enlarging the list is harmless — `EndsAreCut.mono` and
`MeetsAreCut.mono` — and it is what makes each anchor a vertex. -/

open scoped Classical in
/-- Cut points for the mesh segments, as produced by `exists_cut_points`. -/
noncomputable def meshCutPoints (N : ℕ) (fresh : List Plane) : List Plane :=
  (exists_cut_points (meshSegments N fresh)).choose

theorem meshCutPoints_spec (N : ℕ) (fresh : List Plane) :
    EndsAreCut (meshSegments N fresh) (meshCutPoints N fresh) ∧
      MeetsAreCut (meshSegments N fresh) (meshCutPoints N fresh) :=
  (exists_cut_points (meshSegments N fresh)).choose_spec

/-- The cut points of the mesh: what the overlay needs, plus the prescribed anchors. -/
noncomputable def meshPoints (N : ℕ) (fresh anchors : List Plane) : List Plane :=
  anchors ++ meshCutPoints N fresh

theorem meshPoints_endsAreCut (N : ℕ) (fresh anchors : List Plane) :
    EndsAreCut (meshSegments N fresh) (meshPoints N fresh anchors) :=
  (meshCutPoints_spec N fresh).1.mono (List.subset_append_right _ _)

theorem meshPoints_meetsAreCut (N : ℕ) (fresh anchors : List Plane) :
    MeetsAreCut (meshSegments N fresh) (meshPoints N fresh anchors) :=
  (meshCutPoints_spec N fresh).2.mono (List.subset_append_right _ _)

theorem anchors_subset_meshPoints (N : ℕ) (fresh anchors : List Plane) :
    anchors ⊆ meshPoints N fresh anchors := List.subset_append_left _ _

/-- **The mesh graph.** -/
noncomputable def meshGraph (N : ℕ) (fresh anchors : List Plane) : Graph Plane Piece :=
  overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)

instance meshGraph_finite (N : ℕ) (fresh anchors : List Plane) :
    Graph.Finite (meshGraph N fresh anchors) :=
  overlayGraph_finite _ _

theorem meshGraph_isDrawing {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (anchors : List Plane) :
    Graph.IsDrawing (meshGraph N fresh anchors) segmentDrawing :=
  overlayGraph_isDrawing _ _ (meshSegments_nondeg hN hfresh)
    (meshPoints_endsAreCut N fresh anchors) (meshPoints_meetsAreCut N fresh anchors)

theorem meshGraph_pointSet (N : ℕ) (fresh anchors : List Plane) :
    Graph.pointSet (meshGraph N fresh anchors) segmentDrawing = cover (meshSegments N fresh) :=
  overlayGraph_pointSet _ _

/-- An edge of the mesh graph is a subsegment of a mesh segment. -/
theorem meshGraph_edge_source {N : ℕ} {fresh anchors : List Plane} {P : Piece}
    (hP : P ∈ E(meshGraph N fresh anchors)) :
    ∃ R ∈ meshSegments N fresh, P.seg ⊆ R.seg := by
  obtain ⟨Q, hQ, rfl⟩ := mem_overlayPieces.1 hP
  obtain ⟨R, hR, hsub, -⟩ := subdivide_subset _ _ Q hQ
  exact ⟨R, hR, by rwa [orientPiece_seg]⟩

theorem meshGraph_edge_nondeg {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) {anchors : List Plane} {P : Piece}
    (hP : P ∈ E(meshGraph N fresh anchors)) : P.Nondeg :=
  overlayPieces_nondeg _ (meshSegments_nondeg hN hfresh) P hP

theorem meshGraph_mem_vertexSet {N : ℕ} {fresh anchors : List Plane} {v : Plane} :
    v ∈ V(meshGraph N fresh anchors) ↔
      ∃ P ∈ E(meshGraph N fresh anchors), v = P.1 ∨ v = P.2 := Iff.rfl

/-- A side of the outer ring is a mesh segment. -/
theorem outer_ringPieces_mem {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane} {R : Piece}
    (hR : R ∈ ringPieces 1) : R ∈ meshSegments N fresh :=
  mem_meshSegments.2 (Or.inl ⟨1, one_mem_meshRadii hN, hR⟩)

theorem spokePiece_mem_meshSegments {N : ℕ} {fresh : List Plane} {z : Plane} (hz : z ∈ fresh) :
    spokePiece N z ∈ meshSegments N fresh := mem_meshSegments.2 (Or.inr ⟨z, hz, rfl⟩)

/-- A fresh point is a cut point: it is an endpoint of its own spoke. -/
theorem fresh_mem_meshPoints {N : ℕ} {fresh : List Plane} (anchors : List Plane) {z : Plane}
    (hz : z ∈ fresh) : z ∈ meshPoints N fresh anchors :=
  meshPoints_endsAreCut N fresh anchors _ (spokePiece_mem_meshSegments hz) z (Or.inl rfl)

/-! ### Clause 2: the anchors are vertices on `S` -/

/-- **Every prescribed anchor on `S` is a vertex of the mesh.** This is what the list of
anchors is for: `subdivide_end_of_mem` turns "is a cut point on a segment" into "is an
endpoint of a piece", and an endpoint of a piece is a vertex of the overlay graph. -/
theorem anchor_mem_vertexSet {N : ℕ} (hN : 2 ≤ N) {fresh anchors : List Plane} {p : Plane}
    (hp : p ∈ anchors) (hpS : p ∈ modelCurve) : p ∈ V(meshGraph N fresh anchors) := by
  obtain ⟨R, hR, hpR⟩ :=
    mem_cover_iff.1 (show p ∈ cover (ringPieces 1) by rw [cover_ringPieces zero_le_one]; exact hpS)
  obtain ⟨Q, hQ, -, hend⟩ := subdivide_end_of_mem (meshPoints N fresh anchors)
    (meshSegments N fresh) p (anchors_subset_meshPoints N fresh anchors hp) R
    (outer_ringPieces_mem hN hR) hpR
  exact ⟨orientPiece Q, mem_overlayPieces.2 ⟨Q, hQ, rfl⟩, (orientPiece_ends Q p).2 hend⟩

/-! ### Clause 3: the outer edges occupy exactly `S`

The blueprint asks for `S` to be the union of the edge arcs of a *cycle*. What is proved here
is the point-set half: the edges whose arcs lie on `S` occupy exactly `S`. See the module
docstring. -/

/-- The edges of the mesh that lie on the model curve. -/
def outerEdges (N : ℕ) (fresh anchors : List Plane) : Set Piece :=
  {P | P ∈ E(meshGraph N fresh anchors) ∧ P.seg ⊆ modelCurve}

/-- **The outer edges occupy exactly the model curve.** -/
theorem cover_outerEdges {N : ℕ} (hN : 2 ≤ N) (fresh anchors : List Plane) :
    ⋃ P ∈ outerEdges N fresh anchors, P.seg = modelCurve := by
  refine subset_antisymm (iUnion₂_subset fun P hP => hP.2) fun x hx => ?_
  obtain ⟨R, hR, hxR⟩ :=
    mem_cover_iff.1 (show x ∈ cover (ringPieces 1) by rw [cover_ringPieces zero_le_one]; exact hx)
  obtain ⟨Q, hQ, hxQ, hsub⟩ := subdivide_covers_source (meshPoints N fresh anchors)
    (meshSegments N fresh) R (outer_ringPieces_mem hN hR) x hxR
  refine mem_iUnion₂.2 ⟨orientPiece Q, ⟨mem_overlayPieces.2 ⟨Q, hQ, rfl⟩, ?_⟩, ?_⟩
  · rw [orientPiece_seg]
    exact hsub.trans (ringPieces_seg_subset zero_le_one hR)
  · rwa [orientPiece_seg]

/-! ### Clause 4: the edges that reach `S` from inside

An edge of the mesh that meets `S` without lying on it is a subsegment of a spoke, and it
touches `S` at that spoke's fresh point only. -/

theorem ringSet_disjoint_modelCurve {r : ℝ} (hr : r ≠ 1) : ringSet r ∩ modelCurve = ∅ := by
  ext x
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  intro hxr hx1
  exact hr (hxr.symm.trans hx1)

theorem smul_left_inj {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) {z : Plane} (hz : z ∈ modelCurve)
    (h : t • z = s • z) : t = s := by
  rw [← supNorm_smul_of_mem_modelCurve ht hz, ← supNorm_smul_of_mem_modelCurve hs hz, h]

/-- **An edge that meets `S` but does not lie on it is a piece of a spoke**, and it meets `S`
exactly at that spoke's fresh point, which is one of its endpoints. -/
theorem meshGraph_inner_edge_at_fresh {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) {anchors : List Plane} {P : Piece}
    (hP : P ∈ E(meshGraph N fresh anchors)) (hmeet : (P.seg ∩ modelCurve).Nonempty)
    (hnot : ¬ P.seg ⊆ modelCurve) :
    ∃ z ∈ fresh, P.seg ∩ modelCurve = {z} ∧ (z = P.1 ∨ z = P.2) ∧
      P.seg ⊆ (spokePiece N z).seg := by
  obtain ⟨R, hR, hsub⟩ := meshGraph_edge_source hP
  rcases mem_meshSegments.1 hR with ⟨r, hr, hRr⟩ | ⟨z, hz, rfl⟩
  · exfalso
    have hseg : P.seg ⊆ ringSet r :=
      hsub.trans (ringPieces_seg_subset (meshRadii_pos hN hr).le hRr)
    by_cases h1 : r = 1
    · exact hnot (by rw [← ringSet_one, ← h1]; exact hseg)
    · obtain ⟨x, hxP, hxS⟩ := hmeet
      have hmem : x ∈ ringSet r ∩ modelCurve := ⟨hseg hxP, hxS⟩
      rw [ringSet_disjoint_modelCurve h1] at hmem
      exact hmem
  · have hle : P.seg ∩ modelCurve ⊆ {z} := by
      rw [← spokePiece_inter_modelCurve hN (hfresh z hz)]
      exact inter_subset_inter_left _ hsub
    obtain ⟨x, hxP, hxS⟩ := hmeet
    have hxz : x = z := hle ⟨hxP, hxS⟩
    subst hxz
    refine ⟨x, hz, subset_antisymm hle (singleton_subset_iff.2 ⟨hxP, hxS⟩), ?_, hsub⟩
    -- `x` is a cut point, so it cannot be interior to an edge
    by_contra hcon
    push Not at hcon
    exact overlayPieces_avoids (meshSegments_nondeg hN hfresh) x
      (fresh_mem_meshPoints anchors hz) P hP
      (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hxP)

theorem mem_smul_openSegment {a b : ℝ} {z x : Plane} :
    x ∈ openSegment ℝ (a • z) (b • z) ↔ ∃ t ∈ openSegment ℝ a b, x = t • z := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq, rfl⟩
    refine ⟨p * a + q * b, ⟨p, q, hp, hq, hpq, rfl⟩, ?_⟩
    module
  · rintro ⟨t, ⟨p, q, hp, hq, hpq, rfl⟩, rfl⟩
    refine ⟨p, q, hp, hq, hpq, ?_⟩
    module

theorem smul_openSegment_eq_image {a b : ℝ} (hab : a < b) (z : Plane) :
    openSegment ℝ (a • z) (b • z) = (fun t : ℝ => t • z) '' Ioo a b := by
  ext x
  rw [mem_smul_openSegment, openSegment_eq_Ioo hab]
  simp only [mem_image]
  exact ⟨fun ⟨t, ht, hx⟩ => ⟨t, ht, hx.symm⟩, fun ⟨t, ht, hx⟩ => ⟨t, ht, hx.symm⟩⟩

/-- A nondegenerate subsegment of a spoke having the spoke's outer end `z` as an endpoint runs
from `z` inwards: its interior is `{t • z : t₀ < t < 1}` for some `t₀ < 1`. This is the whole
of "only one edge leaves `S` at a fresh point" — two such edges would overlap near `z`. -/
theorem spoke_subpiece_interior {N : ℕ} (hN : 2 ≤ N) {z : Plane}
    {P : Piece} (hnd : P.Nondeg) (hsub : P.seg ⊆ (spokePiece N z).seg)
    (hend : z = P.1 ∨ z = P.2) :
    ∃ t₀ : ℝ, t₀ < 1 ∧ P.interior = (fun t : ℝ => t • z) '' Ioo t₀ 1 := by
  have key : ∀ q : Plane, q ∈ (spokePiece N z).seg → q ≠ z →
      ∃ t₀ : ℝ, t₀ < 1 ∧ openSegment ℝ z q = (fun t : ℝ => t • z) '' Ioo t₀ 1 := by
    intro q hq hne
    rw [spokePiece_seg hN] at hq
    obtain ⟨t₀, ht₀, rfl⟩ := hq
    have hlt : t₀ < 1 := lt_of_le_of_ne ht₀.2 fun h => hne (by simp [h])
    refine ⟨t₀, hlt, ?_⟩
    have hz1 : openSegment ℝ z (t₀ • z) = openSegment ℝ (t₀ • z) ((1 : ℝ) • z) := by
      rw [one_smul, openSegment_symm]
    rw [hz1, smul_openSegment_eq_image hlt]
  rcases hend with h | h
  · obtain ⟨t₀, hlt, heq⟩ :=
      key P.2 (hsub (right_mem_segment ℝ _ _)) (by rw [h]; exact Ne.symm hnd)
    exact ⟨t₀, hlt, by change openSegment ℝ P.1 P.2 = _; rw [← h, heq]⟩
  · obtain ⟨t₀, hlt, heq⟩ := key P.1 (hsub (left_mem_segment ℝ _ _)) (by rw [h]; exact hnd)
    exact ⟨t₀, hlt, by change openSegment ℝ P.1 P.2 = _; rw [openSegment_symm, ← h, heq]⟩

/-- **Existence** for clause 4: a fresh point does carry an edge leaving `S`. -/
theorem exists_inner_edge_at_fresh {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ w ∈ fresh, w ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh) :
    ∃ P ∈ E(meshGraph N fresh anchors),
      (z = P.1 ∨ z = P.2) ∧ ¬ P.seg ⊆ modelCurve ∧ P.seg ⊆ (spokePiece N z).seg := by
  obtain ⟨Q, hQ, hsub, hend⟩ := subdivide_end_of_mem (meshPoints N fresh anchors)
    (meshSegments N fresh) z (fresh_mem_meshPoints anchors hz) (spokePiece N z)
    (spokePiece_mem_meshSegments hz) (left_mem_segment ℝ _ _)
  have hnd : Q.Nondeg :=
    subdivide_ne (meshPoints N fresh anchors) (meshSegments_nondeg hN hfresh) Q hQ
  refine ⟨orientPiece Q, mem_overlayPieces.2 ⟨Q, hQ, rfl⟩, (orientPiece_ends Q z).2 hend, ?_, ?_⟩
  · rw [orientPiece_seg]
    intro hcon
    -- an edge inside `S` and inside the spoke would be inside `{z}`, hence degenerate
    have hsing : Q.seg ⊆ {z} := by
      rw [← spokePiece_inter_modelCurve hN (hfresh z hz)]
      exact subset_inter hsub hcon
    exact hnd ((hsing (left_mem_segment ℝ _ _)).trans (hsing (right_mem_segment ℝ _ _)).symm)
  · rw [orientPiece_seg]; exact hsub

/-- **Uniqueness** for clause 4: exactly one edge leaves `S` at a fresh point. -/
theorem inner_edge_at_fresh_unique {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) {anchors : List Plane} {z : Plane} (hz : z ∈ fresh)
    {P Q : Piece} (hP : P ∈ E(meshGraph N fresh anchors)) (hendP : z = P.1 ∨ z = P.2)
    (hnotP : ¬ P.seg ⊆ modelCurve) (hQ : Q ∈ E(meshGraph N fresh anchors))
    (hendQ : z = Q.1 ∨ z = Q.2) (hnotQ : ¬ Q.seg ⊆ modelCurve) : P = Q := by
  have hzS : z ∈ modelCurve := hfresh z hz
  -- each of the two edges lies on the spoke at `z`
  have spoke_of : ∀ R : Piece, R ∈ E(meshGraph N fresh anchors) → (z = R.1 ∨ z = R.2) →
      ¬ R.seg ⊆ modelCurve → R.seg ⊆ (spokePiece N z).seg := by
    intro R hR hendR hnotR
    have hzR : z ∈ R.seg := by
      rcases hendR with rfl | rfl
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _
    obtain ⟨w, hw, hmeetw, -, hsubw⟩ :=
      meshGraph_inner_edge_at_fresh hN hfresh hR ⟨z, hzR, hzS⟩ hnotR
    have hzw : z = w := by
      have : z ∈ ({w} : Set Plane) := hmeetw ▸ (show z ∈ R.seg ∩ modelCurve from ⟨hzR, hzS⟩)
      exact this
    rwa [← hzw] at hsubw
  obtain ⟨tP, hltP, hintP⟩ := spoke_subpiece_interior hN
    (meshGraph_edge_nondeg hN hfresh hP) (spoke_of P hP hendP hnotP) hendP
  obtain ⟨tQ, hltQ, hintQ⟩ := spoke_subpiece_interior hN
    (meshGraph_edge_nondeg hN hfresh hQ) (spoke_of Q hQ hendQ hnotQ) hendQ
  by_contra hne
  -- both interiors contain every multiple `s • z` with `max tP tQ < s < 1`
  set s : ℝ := (max tP tQ + 1) / 2 with hs
  have hs1 : s < 1 := by
    rw [hs]
    rcases max_cases tP tQ with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith
  have hsP : tP < s := by
    rw [hs]; have : tP ≤ max tP tQ := le_max_left _ _
    have : max tP tQ < 1 := max_lt hltP hltQ
    linarith [le_max_left tP tQ]
  have hsQ : tQ < s := by
    rw [hs]; have : max tP tQ < 1 := max_lt hltP hltQ
    linarith [le_max_right tP tQ]
  refine overlayPieces_disjoint_interiors (meshSegments_nondeg hN hfresh)
    (meshPoints_endsAreCut N fresh anchors) (meshPoints_meetsAreCut N fresh anchors) hP hQ hne
    (x := s • z) ?_ ?_
  · rw [hintP]; exact ⟨s, ⟨hsP, hs1⟩, rfl⟩
  · rw [hintQ]; exact ⟨s, ⟨hsQ, hs1⟩, rfl⟩

/-- **Clause 4.** Exactly one edge of the mesh leaves `S` at each fresh point. -/
theorem unique_inner_edge_at_fresh {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh) :
    ∃! P : Piece, P ∈ E(meshGraph N fresh anchors) ∧ (z = P.1 ∨ z = P.2) ∧
      ¬ P.seg ⊆ modelCurve := by
  obtain ⟨P, hP, hend, hnot, -⟩ := exists_inner_edge_at_fresh hN hfresh anchors hz
  exact ⟨P, ⟨hP, hend, hnot⟩, fun Q hQ =>
    inner_edge_at_fresh_unique hN hfresh hz hQ.1 hQ.2.1 hQ.2.2 hP hend hnot⟩

/-! ### Clause 1: every bounded face is small

The estimate is the blueprint's, in radial coordinates. A connected set missing the mesh
misses every ring, so its sup norm — continuous, hence with a preconnected image in `ℝ` —
stays inside one open interval `(k/N, (k+1)/N)` between consecutive ring radii. Inside the
innermost square that is already the whole bound; outside it the radial projection
`x ↦ ‖x‖∞⁻¹ • x` maps the set into `S`, connectedly, and away from every fresh point, because
a point projecting to a fresh point lies on that point's spoke. The blueprint's

  `‖x - y‖ ≤ ‖tz - tw‖ + ‖tw - sw‖ < δ/4 + δ/4 + δ/4`

is then `t‖z - w‖ + |t - s|‖w‖`, with `‖z - w‖` controlled by `FreshDense` and `|t - s|` by
one ring thickness. -/

theorem continuous_supNorm : Continuous Plane.supNorm :=
  (continuous_abs.comp (Plane.continuous_coord 0)).max
    (continuous_abs.comp (Plane.continuous_coord 1))

theorem supNorm_sub_le (x y : Plane) :
    Plane.supNorm (x - y) ≤ Plane.supNorm x + Plane.supNorm y := by
  have h := Plane.supDist_triangle x 0 y
  rw [Plane.supDist_zero, Plane.supDist_comm 0 y, Plane.supDist_zero] at h
  exact h

theorem dist_le_sqrt_two_mul_supNorm (x y : Plane) :
    dist x y ≤ Real.sqrt 2 * Plane.supNorm (x - y) := by
  rw [dist_eq_norm]; exact Plane.norm_le_sqrt_two_mul_supNorm _

/-- The fresh points are `δ`-dense on `S`: every connected piece of `S` that avoids all of them
has diameter at most `δ/2`.

This is the hypothesis the blueprint discharges by "parametrize `S` by a circle, use uniform
continuity to cut it into arcs of diameter `< δ/8`, and pick one fresh point in the relative
interior of each". Stated as a property of a *set* rather than of a cyclic order, it needs no
ordering of the fresh points along `S` — which is what makes the whole mesh order-free. -/
def FreshDense (fresh : List Plane) (δ : ℝ) : Prop :=
  ∀ A : Set Plane, A ⊆ modelCurve \ {x | x ∈ fresh} → IsPreconnected A →
    ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ δ / 2

theorem ringSet_subset_cover {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane} {r : ℝ}
    (hr : r ∈ meshRadii N) : ringSet r ⊆ cover (meshSegments N fresh) := by
  rw [cover_meshSegments hN]
  exact fun x hx => mem_union_left _ (mem_iUnion₂.2 ⟨r, hr, hx⟩)

theorem spokePiece_seg_subset_cover {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane} {z : Plane}
    (hz : z ∈ fresh) : (spokePiece N z).seg ⊆ cover (meshSegments N fresh) := by
  rw [cover_meshSegments hN]
  exact fun x hx => mem_union_right _ (mem_iUnion₂.2 ⟨z, hz, hx⟩)

/-- **The radial estimate.** A connected set missing the mesh stays inside the open square and
has diameter at most `δ/2 + √2/N`. -/
theorem radial_diam_bound {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane} {δ : ℝ}
    (hNδ : 2 * Real.sqrt 2 ≤ δ * N) (hdense : FreshDense fresh δ)
    {F : Set Plane} (hconn : IsPreconnected F)
    (hdisj : ∀ x ∈ F, x ∉ cover (meshSegments N fresh))
    {base : Plane} (hb : base ∈ F) (hbase : Plane.supNorm base < 1) :
    (∀ x ∈ F, Plane.supNorm x < 1) ∧
      ∀ x ∈ F, ∀ y ∈ F, dist x y ≤ δ / 2 + Real.sqrt 2 / N := by
  have hNR0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hN
  have hsqrt : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  -- no point of `F` sits on a ring
  have hring : ∀ r ∈ meshRadii N, ∀ x ∈ F, Plane.supNorm x ≠ r := fun r hr x hx he =>
    hdisj x hx (ringSet_subset_cover hN hr he)
  have himg : IsPreconnected (Plane.supNorm '' F) :=
    hconn.image _ continuous_supNorm.continuousOn
  -- the ring index of the base point
  set c : ℝ := Plane.supNorm base with hc
  have hc0 : 0 ≤ c := Plane.supNorm_nonneg _
  have hcN : 0 ≤ c * (N : ℝ) := mul_nonneg hc0 hNR0.le
  set k : ℕ := ⌊c * (N : ℝ)⌋₊ with hk
  have hkle : (k : ℝ) ≤ c * N := Nat.floor_le hcN
  have hklt : c * (N : ℝ) < k + 1 := Nat.lt_floor_add_one _
  have hkN : k < N := by
    rw [hk, Nat.floor_lt hcN]
    calc c * (N : ℝ) < 1 * N := by exact mul_lt_mul_of_pos_right hbase hNR0
      _ = N := one_mul _
  set a : ℝ := (k : ℝ) / N with ha
  set b : ℝ := ((k : ℝ) + 1) / N with hbdef
  have hac : a ≤ c := by rw [ha, div_le_iff₀ hNR0]; exact hkle
  have hcb : c < b := by rw [hbdef, lt_div_iff₀ hNR0]; exact hklt
  have hbmem : b ∈ meshRadii N := mem_meshRadii.2 ⟨k, hkN, rfl⟩
  have hb1 : b ≤ 1 := meshRadii_le_one hN hbmem
  have hba : b - a = 1 / (N : ℝ) := by rw [ha, hbdef, div_sub_div_same]; ring_nf
  -- the sup norm on `F` stays inside `[a, b)`
  have hup : ∀ x ∈ F, Plane.supNorm x < b := by
    intro x hx
    by_contra hcon
    push Not at hcon
    obtain ⟨y, hy, hyb⟩ :=
      himg.Icc_subset ⟨base, hb, rfl⟩ ⟨x, hx, rfl⟩ (mem_Icc.2 ⟨hcb.le, hcon⟩)
    exact hring b hbmem y hy hyb
  have hlow : ∀ x ∈ F, a ≤ Plane.supNorm x := by
    intro x hx
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · rw [ha, hk0]; simpa using Plane.supNorm_nonneg x
    · have hamem : a ∈ meshRadii N := by
        refine mem_meshRadii.2 ⟨k - 1, by omega, ?_⟩
        rw [ha]
        congr 1
        rw [Nat.cast_sub hk1, Nat.cast_one]
        ring
      have hac' : a < c := lt_of_le_of_ne hac fun he => hring a hamem base hb he.symm
      by_contra hcon
      push Not at hcon
      obtain ⟨y, hy, hya⟩ :=
        himg.Icc_subset ⟨x, hx, rfl⟩ ⟨base, hb, rfl⟩ (mem_Icc.2 ⟨hcon.le, hac'.le⟩)
      exact hring a hamem y hy hya
  refine ⟨fun x hx => lt_of_lt_of_le (hup x hx) hb1, ?_⟩
  -- one ring thickness is at most `δ/2`
  have hthin : Real.sqrt 2 / (N : ℝ) ≤ δ / 2 := by
    rw [div_le_div_iff₀ hNR0 two_pos]
    linarith
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · -- the innermost square: both points are within `1/N` of the origin
    have hsmall : ∀ x ∈ F, Plane.supNorm x < 1 / (N : ℝ) := by
      intro x hx
      have := hup x hx
      rwa [hbdef, hk0, Nat.cast_zero, zero_add] at this
    intro x hx y hy
    calc dist x y ≤ Real.sqrt 2 * Plane.supNorm (x - y) := dist_le_sqrt_two_mul_supNorm x y
      _ ≤ Real.sqrt 2 * (Plane.supNorm x + Plane.supNorm y) :=
          mul_le_mul_of_nonneg_left (supNorm_sub_le x y) hsqrt.le
      _ ≤ Real.sqrt 2 * (1 / (N : ℝ) + 1 / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left (add_le_add (hsmall x hx).le (hsmall y hy).le) hsqrt.le
      _ = Real.sqrt 2 / N + Real.sqrt 2 / N := by ring
      _ ≤ δ / 2 + Real.sqrt 2 / N := by linarith
  · -- the annulus between two rings: project radially onto `S`
    have hainv : (N : ℝ)⁻¹ ≤ a := by
      rw [ha, inv_eq_one_div, div_le_div_iff_of_pos_right hNR0]
      exact_mod_cast hk1
    have hapos : 0 < a := lt_of_lt_of_le (by positivity) hainv
    have hpos : ∀ x ∈ F, 0 < Plane.supNorm x := fun x hx => lt_of_lt_of_le hapos (hlow x hx)
    set g : Plane → Plane := fun x => (Plane.supNorm x)⁻¹ • x with hg
    have hrecov : ∀ x ∈ F, Plane.supNorm x • g x = x := by
      intro x hx
      rw [hg]
      simp only [smul_smul]
      rw [mul_inv_cancel₀ (ne_of_gt (hpos x hx)), one_smul]
    have hgS : ∀ x ∈ F, g x ∈ modelCurve := by
      intro x hx
      change Plane.supNorm ((Plane.supNorm x)⁻¹ • x) = 1
      rw [Plane.supNorm_smul, abs_of_nonneg (inv_nonneg.2 (Plane.supNorm_nonneg x))]
      exact inv_mul_cancel₀ (ne_of_gt (hpos x hx))
    have hgcont : ContinuousOn g F :=
      ContinuousOn.smul (continuous_supNorm.continuousOn.inv₀ fun x hx => ne_of_gt (hpos x hx))
        continuousOn_id
    have hgavoid : ∀ x ∈ F, g x ∈ modelCurve \ {w : Plane | w ∈ fresh} := by
      intro x hx
      refine ⟨hgS x hx, fun hmem => hdisj x hx ?_⟩
      -- `x` lies on the spoke at `g x`
      refine spokePiece_seg_subset_cover hN hmem ?_
      rw [spokePiece_seg hN]
      exact ⟨Plane.supNorm x, ⟨le_trans hainv (hlow x hx),
        le_trans (hup x hx).le hb1⟩, hrecov x hx⟩
    have hgdist : ∀ x ∈ F, ∀ y ∈ F, dist (g x) (g y) ≤ δ / 2 := fun x hx y hy =>
      hdense (g '' F) (by rintro _ ⟨w, hw, rfl⟩; exact hgavoid w hw) (hconn.image g hgcont)
        (g x) ⟨x, hx, rfl⟩ (g y) ⟨y, hy, rfl⟩
    intro x hx y hy
    have hsplit : x - y = Plane.supNorm x • (g x - g y)
        + (Plane.supNorm x - Plane.supNorm y) • g y := by
      rw [smul_sub, sub_smul, hrecov x hx, hrecov y hy]
      abel
    have hnormy : ‖g y‖ ≤ Real.sqrt 2 := by
      have := Plane.norm_le_sqrt_two_mul_supNorm (g y)
      rwa [show Plane.supNorm (g y) = 1 from hgS y hy, mul_one] at this
    have hts : |Plane.supNorm x - Plane.supNorm y| ≤ 1 / (N : ℝ) := by
      rw [← hba]
      exact abs_le.2 ⟨by linarith [hlow x hx, hup y hy], by linarith [hup x hx, hlow y hy]⟩
    have hx1 : Plane.supNorm x ≤ 1 := le_of_lt (lt_of_lt_of_le (hup x hx) hb1)
    calc dist x y = ‖Plane.supNorm x • (g x - g y)
          + (Plane.supNorm x - Plane.supNorm y) • g y‖ := by rw [dist_eq_norm, hsplit]
      _ ≤ ‖Plane.supNorm x • (g x - g y)‖
          + ‖(Plane.supNorm x - Plane.supNorm y) • g y‖ := norm_add_le _ _
      _ = Plane.supNorm x * ‖g x - g y‖
          + |Plane.supNorm x - Plane.supNorm y| * ‖g y‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (Plane.supNorm_nonneg x)]
      _ ≤ 1 * (δ / 2) + 1 / (N : ℝ) * Real.sqrt 2 := by
          refine add_le_add (mul_le_mul hx1 ?_ (norm_nonneg _) zero_le_one)
            (mul_le_mul hts hnormy (norm_nonneg _) (by positivity))
          rw [← dist_eq_norm]
          exact hgdist x hx y hy
      _ = δ / 2 + Real.sqrt 2 / N := by ring

/-- The mesh occupies a subset of the closed square. -/
theorem cover_meshSegments_subset {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) :
    cover (meshSegments N fresh) ⊆ Plane.closedSquare 0 1 := by
  intro x hx
  obtain ⟨P, hP, hxP⟩ := mem_cover_iff.1 hx
  exact meshSegments_subset_closedSquare hN hfresh hP hxP

/-- **Clause 1.** Every bounded face of the mesh lies in the open square and has diameter
`< δ`. -/
theorem meshGraph_face_small {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) {anchors : List Plane} {δ : ℝ} (hδ : 0 < δ)
    (hNδ : 2 * Real.sqrt 2 < δ * N) (hdense : FreshDense fresh δ) {base : Plane}
    (hbase : base ∈ Graph.exterior (meshGraph N fresh anchors) segmentDrawing)
    (hbdd : Bornology.IsBounded (Graph.face (meshGraph N fresh anchors) segmentDrawing base)) :
    Graph.face (meshGraph N fresh anchors) segmentDrawing base ⊆ Plane.openSquare 0 1 ∧
      Metric.diam (Graph.face (meshGraph N fresh anchors) segmentDrawing base) < δ := by
  have hNR0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hN
  set F := Graph.face (meshGraph N fresh anchors) segmentDrawing base with hF
  have hpt : Graph.pointSet (meshGraph N fresh anchors) segmentDrawing
      = cover (meshSegments N fresh) := meshGraph_pointSet N fresh anchors
  have hsq : Graph.pointSet (meshGraph N fresh anchors) segmentDrawing
      ⊆ Plane.closedSquare 0 1 := by rw [hpt]; exact cover_meshSegments_subset hN hfresh
  -- the base point is inside the square: outside it the face would be the unbounded one
  have hbM : base ∉ cover (meshSegments N fresh) := by rw [← hpt]; exact hbase
  have hb1 : Plane.supNorm base < 1 := by
    rcases lt_trichotomy (Plane.supNorm base) 1 with h | h | h
    · exact h
    · exact absurd (ringSet_subset_cover hN (one_mem_meshRadii hN) h) hbM
    · exfalso
      have hmem : base ∈ Plane.beyondSquare 1 := by
        rw [Plane.beyondSquare_eq_compl]
        exact fun hc => absurd (mem_closedSquare_zero_one.1 hc) (not_le.2 h)
      exact Graph.not_isBounded_beyondSquare 1
        (hbdd.subset (Graph.beyondSquare_subset_face hsq hmem))
  have hdisj : ∀ x ∈ F, x ∉ cover (meshSegments N fresh) := by
    intro x hx
    have := Graph.face_subset_exterior _ _ _ hx
    rwa [Graph.exterior, hpt, mem_compl_iff] at this
  obtain ⟨hin, hdist⟩ := radial_diam_bound hN hNδ.le hdense
    (Graph.isConnected_face hbase).isPreconnected hdisj (Graph.mem_face hbase) hb1
  refine ⟨fun x hx => mem_openSquare_zero_one.2 (hin x hx), ?_⟩
  have hthin : Real.sqrt 2 / (N : ℝ) < δ / 2 := by
    rw [div_lt_div_iff₀ hNR0 two_pos]; linarith
  refine lt_of_le_of_lt (Metric.diam_le_of_forall_dist_le (by positivity) hdist) ?_
  linarith

/-! ### Clause 5: the mesh minus `S` is connected

The inner rings and the spokes-minus-their-outer-endpoint are each connected, every inner ring
meets every spoke, and every spoke meets the innermost ring. So a single point of the innermost
ring reaches everything, which is what `isPreconnected_of_forall` asks for. At least one fresh
point is needed: with no spokes the rings are disjoint circles. -/

/-- A spoke with its outer endpoint removed. -/
noncomputable def halfSpoke (N : ℕ) (z : Plane) : Set Plane :=
  (fun t : ℝ => t • z) '' Ico ((N : ℝ)⁻¹) 1

theorem isConnected_halfSpoke {N : ℕ} (hN : 2 ≤ N) (z : Plane) :
    IsConnected (halfSpoke N z) :=
  (isConnected_Ico (inv_cast_lt_one hN)).image _
    (Continuous.continuousOn (continuous_id.smul continuous_const))

theorem halfSpoke_subset {N : ℕ} (hN : 2 ≤ N) (z : Plane) :
    halfSpoke N z ⊆ (spokePiece N z).seg := by
  rw [halfSpoke, spokePiece_seg hN]
  exact Set.image_mono Ico_subset_Icc_self

theorem halfSpoke_disjoint_modelCurve {N : ℕ} (hN : 2 ≤ N) {z : Plane} (hz : z ∈ modelCurve) :
    ∀ x ∈ halfSpoke N z, x ∉ modelCurve := by
  rintro _ ⟨t, ht, rfl⟩ hmem
  have h0 : (0 : ℝ) ≤ t := le_trans (inv_cast_pos hN).le ht.1
  have : t = 1 := by
    have hval := supNorm_smul_of_mem_modelCurve h0 hz
    rw [show Plane.supNorm (t • z) = 1 from hmem] at hval
    exact hval.symm
  exact absurd this (ne_of_lt ht.2)

theorem smul_mem_halfSpoke {N : ℕ} {t : ℝ} (ht : (N : ℝ)⁻¹ ≤ t) (ht1 : t < 1) (z : Plane) :
    t • z ∈ halfSpoke N z := ⟨t, ⟨ht, ht1⟩, rfl⟩

/-- The frame of a square is connected: four segments in a cycle, meeting at the corners. -/
theorem isConnected_ringSet {r : ℝ} (hr : 0 ≤ r) : IsConnected (ringSet r) := by
  have hseg : ∀ u v : Plane, IsConnected (segment ℝ u v) := fun u v =>
    (convex_segment u v).isConnected ⟨u, left_mem_segment ℝ _ _⟩
  rw [← cover_ringPieces hr]
  simp only [ringPieces, cover_cons, cover_nil, union_empty]
  have hCD : IsConnected (segment ℝ (Plane.mk (-r) (-r)) (Plane.mk r (-r))
      ∪ segment ℝ (Plane.mk r (-r)) (Plane.mk r r)) :=
    (hseg _ _).union ⟨Plane.mk r (-r), right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩ (hseg _ _)
  have hBCD := (hseg (Plane.mk (-r) r) (Plane.mk (-r) (-r))).union
    ⟨Plane.mk (-r) (-r), right_mem_segment ℝ _ _, Or.inl (left_mem_segment ℝ _ _)⟩ hCD
  exact (hseg (Plane.mk r r) (Plane.mk (-r) r)).union
    ⟨Plane.mk (-r) r, right_mem_segment ℝ _ _, Or.inl (left_mem_segment ℝ _ _)⟩ hBCD

/-- **Clause 5.** The mesh with `S` removed is connected. -/
theorem isConnected_cover_diff_modelCurve {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) {z₀ : Plane} (hz₀ : z₀ ∈ fresh) :
    IsConnected (cover (meshSegments N fresh) \ modelCurve) := by
  have hinvpos := inv_cast_pos hN
  have hinvlt := inv_cast_lt_one hN
  set p : Plane := ((N : ℝ)⁻¹) • z₀ with hp
  have hpring : p ∈ ringSet ((N : ℝ)⁻¹) :=
    supNorm_smul_of_mem_modelCurve hinvpos.le (hfresh z₀ hz₀)
  have hphalf : p ∈ halfSpoke N z₀ := smul_mem_halfSpoke le_rfl hinvlt z₀
  have hinvmem : ((N : ℝ)⁻¹) ∈ meshRadii N := inv_mem_meshRadii hN
  -- the two building blocks, and the fact that they miss `S`
  have hringsub : ∀ r ∈ meshRadii N, r ≠ 1 →
      ringSet r ⊆ cover (meshSegments N fresh) \ modelCurve := by
    intro r hr hr1 x hx
    exact ⟨ringSet_subset_cover hN hr hx, fun hc => hr1 (hx.symm.trans hc)⟩
  have hhalfsub : ∀ z ∈ fresh, halfSpoke N z ⊆ cover (meshSegments N fresh) \ modelCurve := by
    intro z hz x hx
    exact ⟨spokePiece_seg_subset_cover hN hz (halfSpoke_subset hN z hx),
      halfSpoke_disjoint_modelCurve hN (hfresh z hz) x hx⟩
  refine ⟨⟨p, hhalfsub z₀ hz₀ hphalf⟩, isPreconnected_of_forall p ?_⟩
  intro y hy
  obtain ⟨hyM, hyS⟩ := hy
  rw [cover_meshSegments hN] at hyM
  rcases hyM with hyr | hyz
  · -- `y` is on a ring, which is not the outer one, and the ring meets the spoke at `z₀`
    obtain ⟨r, hr, hyr⟩ := mem_iUnion₂.1 hyr
    have hr1 : r ≠ 1 := fun h => hyS (by rw [← ringSet_one, ← h]; exact hyr)
    have hrpos : 0 < r := meshRadii_pos hN hr
    have hrlt : r < 1 := lt_of_le_of_ne (meshRadii_le_one hN hr) hr1
    have hrinv : ((N : ℝ)⁻¹) ≤ r := by
      obtain ⟨j, hj, rfl⟩ := mem_meshRadii.1 hr
      have hNR0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hN
      rw [inv_eq_one_div, div_le_div_iff_of_pos_right hNR0]
      linarith [Nat.cast_nonneg (α := ℝ) j]
    refine ⟨ringSet r ∪ halfSpoke N z₀, union_subset (hringsub r hr hr1) (hhalfsub z₀ hz₀),
      Or.inr hphalf, Or.inl hyr, ?_⟩
    exact ((isConnected_ringSet hrpos.le).union
      ⟨r • z₀, supNorm_smul_of_mem_modelCurve hrpos.le (hfresh z₀ hz₀),
        smul_mem_halfSpoke hrinv hrlt z₀⟩ (isConnected_halfSpoke hN z₀)).isPreconnected
  · -- `y` is on a spoke, below `S`, and the spoke meets the innermost ring
    obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.1 hyz
    rw [spokePiece_seg hN] at hyz
    obtain ⟨t, ht, rfl⟩ := hyz
    have h0 : (0 : ℝ) ≤ t := le_trans hinvpos.le ht.1
    have ht1 : t < 1 := lt_of_le_of_ne ht.2 fun h => hyS (by
      rw [← ringSet_one]
      exact (supNorm_smul_of_mem_modelCurve h0 (hfresh z hz)).trans h)
    refine ⟨halfSpoke N z ∪ ringSet ((N : ℝ)⁻¹),
      union_subset (hhalfsub z hz) (hringsub _ hinvmem (ne_of_lt hinvlt)),
      Or.inr hpring, Or.inl (smul_mem_halfSpoke ht.1 ht1 z), ?_⟩
    exact ((isConnected_halfSpoke hN z).union
      ⟨((N : ℝ)⁻¹) • z, smul_mem_halfSpoke le_rfl hinvlt z,
        supNorm_smul_of_mem_modelCurve hinvpos.le (hfresh z hz)⟩
      (isConnected_ringSet hinvpos.le)).isPreconnected

/-! ### The mesh of a given size

`meshCount δ` rings make both the innermost square and one ring thickness small compared with
`δ`; `2 √2 < δ N` is the single inequality the whole diameter estimate rests on. -/

/-- The number of concentric rings used for mesh size `δ`. -/
noncomputable def meshCount (δ : ℝ) : ℕ := max 2 (⌈2 * Real.sqrt 2 / δ⌉₊ + 1)

theorem two_le_meshCount (δ : ℝ) : 2 ≤ meshCount δ := le_max_left _ _

theorem meshCount_spec {δ : ℝ} (hδ : 0 < δ) : 2 * Real.sqrt 2 < δ * meshCount δ := by
  have h1 : 2 * Real.sqrt 2 / δ < (meshCount δ : ℝ) := by
    calc 2 * Real.sqrt 2 / δ ≤ (⌈2 * Real.sqrt 2 / δ⌉₊ : ℝ) := Nat.le_ceil _
      _ < (⌈2 * Real.sqrt 2 / δ⌉₊ : ℝ) + 1 := by linarith
      _ ≤ (meshCount δ : ℝ) := by exact_mod_cast le_max_right 2 (⌈2 * Real.sqrt 2 / δ⌉₊ + 1)
  rw [div_lt_iff₀ hδ] at h1
  linarith

/-- **The anchored square mesh**: `meshCount δ` concentric ring frames inside `Q = [-1,1]²`,
one radial spoke at each fresh boundary point, and the anchors inserted as extra vertices of
the outer ring. -/
noncomputable def squareMesh (δ : ℝ) (fresh anchors : List Plane) : Graph Plane Piece :=
  meshGraph (meshCount δ) fresh anchors

instance squareMesh_finite (δ : ℝ) (fresh anchors : List Plane) :
    Graph.Finite (squareMesh δ fresh anchors) := meshGraph_finite _ _ _

/-- The mesh is a plane graph, drawn with straight edges. -/
theorem squareMesh_isDrawing {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (δ : ℝ) (anchors : List Plane) :
    Graph.IsDrawing (squareMesh δ fresh anchors) segmentDrawing :=
  meshGraph_isDrawing (two_le_meshCount δ) hfresh anchors

theorem squareMesh_pointSet (δ : ℝ) (fresh anchors : List Plane) :
    Graph.pointSet (squareMesh δ fresh anchors) segmentDrawing
      = cover (meshSegments (meshCount δ) fresh) :=
  meshGraph_pointSet _ _ _

/-- The whole model curve is part of the mesh. -/
theorem modelCurve_subset_squareMesh_pointSet (δ : ℝ) (fresh anchors : List Plane) :
    modelCurve ⊆ Graph.pointSet (squareMesh δ fresh anchors) segmentDrawing := by
  rw [squareMesh_pointSet, ← ringSet_one]
  exact ringSet_subset_cover (two_le_meshCount δ) (one_mem_meshRadii (two_le_meshCount δ))

/-- The mesh occupies a subset of `Q`. -/
theorem squareMesh_pointSet_subset {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (δ : ℝ) (anchors : List Plane) :
    Graph.pointSet (squareMesh δ fresh anchors) segmentDrawing ⊆ Plane.closedSquare 0 1 := by
  rw [squareMesh_pointSet]
  exact cover_meshSegments_subset (two_le_meshCount δ) hfresh

/-- **Clause 1.** Every bounded face lies in the open square and has diameter `< δ`. -/
theorem squareMesh_face_small {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    {δ : ℝ} (hδ : 0 < δ) (hdense : FreshDense fresh δ) {anchors : List Plane} {base : Plane}
    (hbase : base ∈ Graph.exterior (squareMesh δ fresh anchors) segmentDrawing)
    (hbdd : Bornology.IsBounded (Graph.face (squareMesh δ fresh anchors) segmentDrawing base)) :
    Graph.face (squareMesh δ fresh anchors) segmentDrawing base ⊆ Plane.openSquare 0 1 ∧
      Metric.diam (Graph.face (squareMesh δ fresh anchors) segmentDrawing base) < δ :=
  meshGraph_face_small (two_le_meshCount δ) hfresh hδ (meshCount_spec hδ) hdense hbase hbdd

/-- **Clause 2.** Every anchor lying on `S` is a vertex. -/
theorem squareMesh_anchor_mem_vertexSet (δ : ℝ) {fresh anchors : List Plane} {p : Plane}
    (hp : p ∈ anchors) (hpS : p ∈ modelCurve) : p ∈ V(squareMesh δ fresh anchors) :=
  anchor_mem_vertexSet (two_le_meshCount δ) hp hpS

/-- **Clause 3.** The edges lying on `S` occupy exactly `S`. -/
theorem squareMesh_cover_outerEdges (δ : ℝ) (fresh anchors : List Plane) :
    ⋃ P ∈ outerEdges (meshCount δ) fresh anchors, P.seg = modelCurve :=
  cover_outerEdges (two_le_meshCount δ) fresh anchors

/-- **Clause 4, first half.** An edge meeting `S` without lying on it meets it in a single
fresh point, which is one of its endpoints. -/
theorem squareMesh_inner_edge_at_fresh {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) {anchors : List Plane} {P : Piece}
    (hP : P ∈ E(squareMesh δ fresh anchors)) (hmeet : (P.seg ∩ modelCurve).Nonempty)
    (hnot : ¬ P.seg ⊆ modelCurve) :
    ∃ z ∈ fresh, P.seg ∩ modelCurve = {z} ∧ (z = P.1 ∨ z = P.2) ∧
      P.seg ⊆ (spokePiece (meshCount δ) z).seg :=
  meshGraph_inner_edge_at_fresh (two_le_meshCount δ) hfresh hP hmeet hnot

/-- **Clause 4, second half.** Exactly one edge leaves `S` at each fresh point. -/
theorem squareMesh_unique_inner_edge {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane) {z : Plane}
    (hz : z ∈ fresh) :
    ∃! P : Piece, P ∈ E(squareMesh δ fresh anchors) ∧ (z = P.1 ∨ z = P.2) ∧
      ¬ P.seg ⊆ modelCurve :=
  unique_inner_edge_at_fresh (two_le_meshCount δ) hfresh anchors hz

/-- **Clause 5.** The mesh minus `S` is connected. -/
theorem squareMesh_isConnected_diff {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane) {z₀ : Plane}
    (hz₀ : z₀ ∈ fresh) :
    IsConnected
      (Graph.pointSet (squareMesh δ fresh anchors) segmentDrawing \ modelCurve) := by
  rw [squareMesh_pointSet]
  exact isConnected_cover_diff_modelCurve (two_le_meshCount δ) hfresh hz₀

end Schoenflies
