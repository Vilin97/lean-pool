/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Strip

/-!
# The collar of a closed polygon is two-sided

`Schoenflies/Strip.lean` builds the blocks of Lemma 1.8 and proves the hard local half of the
statement: the two labelled sides are disjoint. This module closes the lemma for a *closed*
polygon by supplying the two remaining global facts.

* **Each side is connected.** The blueprint says "consecutive edge and vertex blocks overlap in
  a nonempty labelled half-strip, so the union of all left pieces is connected". Here that
  overlap is produced explicitly: `StripData.mem_overlapL_start` puts the point at frame
  position `(3 lam / 2, rho / 2)` in both `blockL i` and `sectorL i`, and
  `StripData.mem_overlapL_finish` puts the point at `(len i - 3 lam / 2, rho / 2)` in both
  `blockL i` and `sectorL (i + 1)`. The two `StripData` constraints that make these work are
  exactly the two the structure advertises for the purpose: `four_lam_lt_len` keeps the frame
  position inside the block, and `two_lam_lt_R` keeps it inside the sector, since
  `3 lam / 2 + rho / 2 < 2 lam < R`.

  The chaining is then a finite induction along `chainL`, and it does **not** need the
  wrap-around: connectedness of a union of connected sets only needs *some* spanning tree of
  the overlap graph, and the linear chain `0, 1, …, m + 2` is one. The blueprint's "the labels
  return consistently after one circuit" is a statement about the *labelling*, not about
  connectedness, and it is `Strip.sideL_disjoint_sideR`, already proved: it is what makes
  `sideL` and `sideR` two sets rather than one.

* **The collar is a neighbourhood, and removing the curve leaves exactly the two sides.**
  `StripData.nbhd_diff_carrier` is immediate from the two disjointness results of `Strip.lean`.
  Openness of `nbhd` is not: `nbhd` contains the curve, so it has to be recognised as a union
  of open sets. `StripData.nbhd_eq` does that, rewriting it as the union of the vertex balls
  and the full edge tubes; the two inclusions are `ball_diff_carrier_subset` and
  `tube_diff_carrier_subset` one way, and the covering of each edge by "near the first vertex,
  near the second vertex, or in the trimmed middle" the other way.

## Blueprint

* `Schoenflies.StripData.isConnected_sideL`, `.isConnected_sideR` — "the union of all left
  pieces is connected; the same is true on the right", inside Lemma 1.8 (a).
* `Schoenflies.StripData.nbhd_diff_carrier` — `N \ P = N_L ⊔ N_R`, Lemma 1.8 (a).
* `Schoenflies.StripData.collar` — Lemma 1.8 (a) for a closed polygon, given the constants.

Producing the constants is `exists_stripData`, which lives elsewhere; every statement here is
for a given `D : StripData P`, exactly as in `Schoenflies/Strip.lean`.
-/

public section

open Metric Set

namespace Schoenflies

open Plane

variable {m : ℕ}

namespace ClosedPolygon

variable {P : ClosedPolygon m} {i : ZMod (m + 3)} {c t s : ℝ}

/-! ### Two frames at one edge

Everything below needs the edge frame read from *both* ends: `Strip.lean` has the departure
end, and the overlap with the sector at the far vertex needs the arrival end. -/

/-- The incoming ray at a vertex is a unit vector. -/
theorem isDirection_rayIn : IsDirection (P.rayIn i) := isDirection_dir vertex_pred_ne

/-- The far vertex of edge `i` sits at frame position `(len i, 0)`. -/
theorem off_sub_vertex_succ :
    P.off i t s - P.vertex (i + 1) = (t - P.len i) • P.tang i + s • perp (P.tang i) := by
  have hv : P.vertex (i + 1) = P.vertex i + (P.len i) • P.tang i := by
    rw [len_smul_tang]; module
  rw [off, hv]; module

/-- The block-to-far-sector distance bound, the mirror of `dist_off_vertex_le`. -/
theorem dist_off_vertex_succ_le : dist (P.off i t s) (P.vertex (i + 1)) ≤ |t - P.len i| + |s| := by
  rw [dist_eq_norm, off_sub_vertex_succ]
  calc ‖(t - P.len i) • P.tang i + s • perp (P.tang i)‖
      ≤ ‖(t - P.len i) • P.tang i‖ + ‖s • perp (P.tang i)‖ := norm_add_le _ _
    _ = |t - P.len i| + |s| := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, norm_perp,
          isDirection_tang.norm, mul_one, mul_one]

/-- The distance from a point of edge `i` to the edge's far endpoint, the mirror of
`dist_pt_vertex`. -/
theorem dist_pt_vertex_succ : dist (P.pt i c) (P.vertex (i + 1)) = |c - P.len i| := by
  rw [pt, dist_eq_norm, off_sub_vertex_succ, zero_smul, add_zero, norm_smul, Real.norm_eq_abs,
    isDirection_tang.norm, mul_one]

/-! ### The two incident edges, as rays out of a vertex

`mem_edge_sub` and `mem_edge_pred_sub` read a point of an incident edge as a multiple of a ray.
The converses are what says that a ball about a vertex minus the curve is covered by the two
sectors: a direction on one of the two rays is *on the curve*, not beside it. -/

/-- Walking back along the incoming ray from vertex `i` traverses the previous edge. -/
theorem vertex_add_smul_rayIn (P : ClosedPolygon m) (i : ZMod (m + 3)) (c : ℝ) :
    P.vertex i + c • P.rayIn i = P.pt (i - 1) (P.len (i - 1) - c) := by
  have hsucc : i - 1 + 1 = i := sub_add_cancel i 1
  have hr : P.rayIn i = -P.tang (i - 1) := by
    have h := rayIn_succ (P := P) (i := i - 1)
    rwa [hsucc] at h
  have hlen : P.vertex i = P.vertex (i - 1) + (P.len (i - 1)) • P.tang (i - 1) := by
    rw [len_smul_tang, hsucc]; module
  rw [pt_eq, hr, hlen]
  module

/-- A point of the incoming ray at distance at most the previous edge's length lies on that
edge. -/
theorem mem_edge_pred_of_smul_rayIn (hc0 : 0 ≤ c) (hc1 : c ≤ P.len (i - 1)) :
    P.vertex i + c • P.rayIn i ∈ P.edge (i - 1) := by
  rw [vertex_add_smul_rayIn]
  exact pt_mem_edge ⟨by linarith, by linarith⟩

/-- A point of the outgoing ray at distance at most the edge's length lies on that edge. -/
theorem mem_edge_of_smul_tang (hc0 : 0 ≤ c) (hc1 : c ≤ P.len i) :
    P.vertex i + c • P.tang i ∈ P.edge i := by
  rw [← pt_eq]
  exact pt_mem_edge ⟨hc0, hc1⟩

end ClosedPolygon

namespace StripData

variable {P : ClosedPolygon m} (D : StripData P) {i j : ZMod (m + 3)} {x : Plane}

/-! ### The overlaps

The blueprint's "consecutive edge and vertex blocks overlap in a nonempty labelled half-strip".
Both witnesses sit at across-coordinate `rho / 2`, at along-coordinate `3 lam / 2` from the
vertex in question. The two hypotheses of `StripData` that were put there for this are
`four_lam_lt_len` — which gives `3 lam / 2 < len i - lam`, so the point is inside the block —
and `two_lam_lt_R` together with `rho < lam` — which gives
`3 lam / 2 + rho / 2 < 2 lam < R`, so the point is inside the sector. -/

/-- The along-coordinate of the witnesses clears the near trim. -/
theorem lam_lt_three_halves_lam : D.lam < 3 * D.lam / 2 := by have := D.lam_pos; linarith

/-- …and stays short of the far one, by `four_lam_lt_len`. -/
theorem three_halves_lam_lt : 3 * D.lam / 2 < P.len i - D.lam := by
  have := D.lam_pos
  have := D.four_lam_lt_len i
  linarith

/-- …and the whole witness stays inside the sector, by `rho_lt_lam` and `two_lam_lt_R`. -/
theorem overlap_dist_lt : 3 * D.lam / 2 + D.rho / 2 < D.R := by
  have := D.rho_lt_lam
  have := D.two_lam_lt_R
  linarith

/-- **The overlap at the departure vertex.** The point at frame position `(3 lam / 2, rho / 2)`
of edge `i` lies both in the left block of that edge and in the left sector at `i`. -/
theorem mem_overlapL_start :
    P.off i (3 * D.lam / 2) (D.rho / 2) ∈ D.blockL i ∩ D.sectorL i := by
  have hmem : P.off i (3 * D.lam / 2) (D.rho / 2) ∈ D.blockL i :=
    D.mem_blockL_off.2 ⟨D.lam_lt_three_halves_lam, D.three_halves_lam_lt,
      by linarith [D.rho_pos], by linarith [D.rho_pos]⟩
  refine ⟨hmem, D.blockL_sub_mem_arcL_start hmem, ?_⟩
  -- The sector reaches this far because `3 lam / 2 + rho / 2 < 2 lam < R`.
  refine lt_of_le_of_lt ClosedPolygon.dist_off_vertex_le ?_
  rw [abs_of_pos (by linarith [D.lam_pos] : (0:ℝ) < 3 * D.lam / 2),
    abs_of_pos (by linarith [D.rho_pos] : (0:ℝ) < D.rho / 2)]
  exact D.overlap_dist_lt

/-- **The overlap at the arrival vertex.** The point at frame position
`(len i - 3 lam / 2, rho / 2)` of edge `i` lies both in the left block of that edge and in the
left sector at `i + 1`. -/
theorem mem_overlapL_finish :
    P.off i (P.len i - 3 * D.lam / 2) (D.rho / 2) ∈ D.blockL i ∩ D.sectorL (i + 1) := by
  have h1 : D.lam < P.len i - 3 * D.lam / 2 := by
    have := D.lam_pos; have := D.four_lam_lt_len i; linarith
  have h2 : P.len i - 3 * D.lam / 2 < P.len i - D.lam := by have := D.lam_pos; linarith
  have hmem : P.off i (P.len i - 3 * D.lam / 2) (D.rho / 2) ∈ D.blockL i :=
    D.mem_blockL_off.2 ⟨h1, h2, by linarith [D.rho_pos], by linarith [D.rho_pos]⟩
  refine ⟨hmem, D.blockL_sub_mem_arcL_finish hmem, ?_⟩
  refine lt_of_le_of_lt ClosedPolygon.dist_off_vertex_succ_le ?_
  rw [show P.len i - 3 * D.lam / 2 - P.len i = -(3 * D.lam / 2) by ring,
    abs_neg, abs_of_pos (by linarith [D.lam_pos] : (0:ℝ) < 3 * D.lam / 2),
    abs_of_pos (by linarith [D.rho_pos] : (0:ℝ) < D.rho / 2)]
  exact D.overlap_dist_lt

/-- The right-hand mirror of `mem_overlapL_start`. -/
theorem mem_overlapR_start :
    P.off i (3 * D.lam / 2) (-(D.rho / 2)) ∈ D.blockR i ∩ D.sectorR i := by
  have hmem : P.off i (3 * D.lam / 2) (-(D.rho / 2)) ∈ D.blockR i :=
    D.mem_blockR_off.2 ⟨D.lam_lt_three_halves_lam, D.three_halves_lam_lt,
      by linarith [D.rho_pos], by linarith [D.rho_pos]⟩
  refine ⟨hmem, D.blockR_sub_mem_arcR_start hmem, ?_⟩
  refine lt_of_le_of_lt ClosedPolygon.dist_off_vertex_le ?_
  rw [abs_of_pos (by linarith [D.lam_pos] : (0:ℝ) < 3 * D.lam / 2),
    abs_neg, abs_of_pos (by linarith [D.rho_pos] : (0:ℝ) < D.rho / 2)]
  exact D.overlap_dist_lt

/-- The right-hand mirror of `mem_overlapL_finish`. -/
theorem mem_overlapR_finish :
    P.off i (P.len i - 3 * D.lam / 2) (-(D.rho / 2)) ∈ D.blockR i ∩ D.sectorR (i + 1) := by
  have h1 : D.lam < P.len i - 3 * D.lam / 2 := by
    have := D.lam_pos; have := D.four_lam_lt_len i; linarith
  have h2 : P.len i - 3 * D.lam / 2 < P.len i - D.lam := by have := D.lam_pos; linarith
  have hmem : P.off i (P.len i - 3 * D.lam / 2) (-(D.rho / 2)) ∈ D.blockR i :=
    D.mem_blockR_off.2 ⟨h1, h2, by linarith [D.rho_pos], by linarith [D.rho_pos]⟩
  refine ⟨hmem, D.blockR_sub_mem_arcR_finish hmem, ?_⟩
  refine lt_of_le_of_lt ClosedPolygon.dist_off_vertex_succ_le ?_
  rw [show P.len i - 3 * D.lam / 2 - P.len i = -(3 * D.lam / 2) by ring,
    abs_neg, abs_of_pos (by linarith [D.lam_pos] : (0:ℝ) < 3 * D.lam / 2),
    abs_neg, abs_of_pos (by linarith [D.rho_pos] : (0:ℝ) < D.rho / 2)]
  exact D.overlap_dist_lt

theorem blockL_nonempty : (D.blockL i).Nonempty := ⟨_, D.mem_overlapL_start.1⟩
theorem blockR_nonempty : (D.blockR i).Nonempty := ⟨_, D.mem_overlapR_start.1⟩

theorem isConnected_blockL : IsConnected (D.blockL i) :=
  D.convex_blockL.isConnected D.blockL_nonempty

theorem isConnected_blockR : IsConnected (D.blockR i) :=
  D.convex_blockR.isConnected D.blockR_nonempty

end StripData

/-! ## Chaining a cyclic family

The union of the left pieces is connected because consecutive pieces overlap. This is a fact
about any cyclically indexed family, and it is worth isolating: it is used once on the left and
once on the right, and it is where the "cyclic" of the blueprint gets examined.

The point to notice is that the closing overlap `F (last) ∩ F 0` is **not used**. A union of
connected sets is connected as soon as the overlap graph is connected, and the path
`0 — 1 — ⋯ — N-1` already spans it; the extra edge back to `0` is a cycle, not a new vertex.
The blueprint's "the labels return consistently after one circuit" is therefore not needed
*here*: it is needed to know that the left label and the right label never collide, which is
`StripData.sideL_disjoint_sideR`, and that is already proved. -/

/-- A cyclically indexed family of connected sets in which every member meets its successor has
connected union. Only the overlaps along the linear chain `0, 1, …, N - 1` are consumed. -/
theorem isConnected_iUnion_zmod {α : Type*} [TopologicalSpace α] {N : ℕ} [NeZero N]
    (F : ZMod N → Set α) (hconn : ∀ i, IsConnected (F i))
    (hmeet : ∀ i, (F i ∩ F (i + 1)).Nonempty) : IsConnected (⋃ i, F i) := by
  -- `chain k` is the union of the pieces with index the cast of some `j ≤ k`.
  set chain : ℕ → Set α := fun k => ⋃ j : ℕ, ⋃ _ : j ≤ k, F (j : ZMod N) with hchain
  have hstep : ∀ k : ℕ, chain (k + 1) = chain k ∪ F ((k + 1 : ℕ) : ZMod N) := by
    intro k
    ext y
    simp only [hchain, Set.mem_iUnion, Set.mem_union, exists_prop]
    constructor
    · rintro ⟨j, hj, hy⟩
      rcases Nat.lt_or_ge j (k + 1) with h | h
      · exact Or.inl ⟨j, Nat.lt_succ_iff.1 h, hy⟩
      · exact Or.inr ((le_antisymm hj h) ▸ hy)
    · rintro (⟨j, hj, hy⟩ | hy)
      · exact ⟨j, le_trans hj (Nat.le_succ k), hy⟩
      · exact ⟨k + 1, le_refl _, hy⟩
  have hzero : chain 0 = F 0 := by
    ext y
    simp only [hchain, Set.mem_iUnion, Nat.le_zero, exists_prop]
    constructor
    · rintro ⟨j, rfl, hy⟩; simpa using hy
    · intro hy; exact ⟨0, rfl, by simpa using hy⟩
  have key : ∀ k : ℕ, IsConnected (chain k) := by
    intro k
    induction k with
    | zero => rw [hzero]; exact hconn 0
    | succ k ih =>
        rw [hstep k]
        refine IsConnected.union ?_ ih (hconn _)
        -- The overlap of the last two links, transported along `((k+1 : ℕ) : ZMod N) = k + 1`.
        obtain ⟨y, hy1, hy2⟩ := hmeet ((k : ℕ) : ZMod N)
        refine ⟨y, ?_, ?_⟩
        · exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨le_refl k, hy1⟩⟩
        · rwa [show ((k + 1 : ℕ) : ZMod N) = ((k : ℕ) : ZMod N) + 1 by push_cast; ring]
  have hcover : (⋃ i, F i) = chain (N - 1) := by
    refine Set.Subset.antisymm ?_ ?_
    · refine Set.iUnion_subset fun i y hy => ?_
      have hval : ((i.val : ℕ) : ZMod N) = i := ZMod.natCast_rightInverse i
      have hlt : i.val < N := ZMod.val_lt i
      refine Set.mem_iUnion.2 ⟨i.val, Set.mem_iUnion.2 ⟨by omega, ?_⟩⟩
      rw [hval]
      exact hy
    · refine Set.iUnion_subset fun j => Set.iUnion_subset fun _ => Set.subset_iUnion _ _
  rw [hcover]
  exact key _

namespace StripData

variable {P : ClosedPolygon m} (D : StripData P) {i j : ZMod (m + 3)} {x : Plane}

/-! ### The two sides are connected -/

/-- The left piece at index `i`: the left sector at vertex `i` glued to the left block of the
edge leaving `i`. -/
def pieceL (i : ZMod (m + 3)) : Set Plane := D.sectorL i ∪ D.blockL i

/-- The right piece at index `i`. -/
def pieceR (i : ZMod (m + 3)) : Set Plane := D.sectorR i ∪ D.blockR i

theorem sideL_eq_iUnion : D.sideL = ⋃ i, D.pieceL i := rfl
theorem sideR_eq_iUnion : D.sideR = ⋃ i, D.pieceR i := rfl

/-- A piece is connected: its sector and its block overlap, at `mem_overlapL_start`. -/
theorem isConnected_pieceL : IsConnected (D.pieceL i) :=
  IsConnected.union ⟨_, D.mem_overlapL_start.2, D.mem_overlapL_start.1⟩ D.isConnected_sectorL
    D.isConnected_blockL

theorem isConnected_pieceR : IsConnected (D.pieceR i) :=
  IsConnected.union ⟨_, D.mem_overlapR_start.2, D.mem_overlapR_start.1⟩ D.isConnected_sectorR
    D.isConnected_blockR

/-- Consecutive pieces overlap: the block of edge `i` reaches into the sector at `i + 1`. -/
theorem pieceL_inter_succ_nonempty : (D.pieceL i ∩ D.pieceL (i + 1)).Nonempty :=
  ⟨_, Or.inr D.mem_overlapL_finish.1, Or.inl D.mem_overlapL_finish.2⟩

theorem pieceR_inter_succ_nonempty : (D.pieceR i ∩ D.pieceR (i + 1)).Nonempty :=
  ⟨_, Or.inr D.mem_overlapR_finish.1, Or.inl D.mem_overlapR_finish.2⟩

/-- **The left side of the collar is connected.** -/
theorem isConnected_sideL : IsConnected D.sideL := by
  rw [D.sideL_eq_iUnion]
  exact isConnected_iUnion_zmod _ (fun i => D.isConnected_pieceL)
    (fun i => D.pieceL_inter_succ_nonempty)

/-- **The right side of the collar is connected.** -/
theorem isConnected_sideR : IsConnected D.sideR := by
  rw [D.sideR_eq_iUnion]
  exact isConnected_iUnion_zmod _ (fun i => D.isConnected_pieceR)
    (fun i => D.pieceR_inter_succ_nonempty)

theorem isOpen_sideL : IsOpen D.sideL :=
  isOpen_iUnion fun _ => D.isOpen_sectorL.union D.isOpen_blockL

theorem isOpen_sideR : IsOpen D.sideR :=
  isOpen_iUnion fun _ => D.isOpen_sectorR.union D.isOpen_blockR

/-! ### The collar minus the curve is exactly the two sides

`nbhd` was *defined* as `sideL ∪ sideR ∪ carrier`, so this is only the two disjointness
statements of `Strip.lean` read backwards. -/

/-- **Lemma 1.8 (a), the set equality.** Removing the curve from the collar leaves exactly the
two labelled sides. With `sideL_disjoint_sideR` this is `N \ P = N_L ⊔ N_R`. -/
theorem nbhd_diff_carrier : D.nbhd \ P.carrier = D.sideL ∪ D.sideR := by
  ext y
  constructor
  · rintro ⟨hy, hyc⟩
    rcases hy with h | h
    · exact h
    · exact absurd h hyc
  · intro hy
    refine ⟨Or.inl hy, ?_⟩
    rcases hy with h | h
    · exact fun hc => Set.disjoint_left.1 D.sideL_disjoint_carrier h hc
    · exact fun hc => Set.disjoint_left.1 D.sideR_disjoint_carrier h hc

theorem carrier_subset_nbhd : P.carrier ⊆ D.nbhd := fun _ hy => Or.inr hy

/-! ### The collar is open

`nbhd` contains the curve, so openness is not formal: it has to be exhibited as a union of open
sets. The two families are the vertex balls and the *full* edge tubes — the block of half-width
`rho` on both sides of the trimmed edge, core included. Each of the two is covered by
`nbhd` because its points off the curve are labelled (`ball_diff_carrier_subset`,
`tube_diff_carrier_subset`); conversely they cover `nbhd`, the only nontrivial part being that
they cover the curve itself, which is the three-way split of an edge into "within `R` of the
first vertex", "within `R` of the second", and "in the trimmed middle". -/

/-- The full tube of edge `i`: the trimmed edge thickened by `rho` on both sides. It is the
union of the two blocks with the piece of the edge between them. -/
def tube (i : ZMod (m + 3)) : Set Plane :=
  strip (P.vertex i) (P.tang i) D.lam (P.len i - D.lam) (-D.rho) D.rho

theorem isOpen_tube : IsOpen (D.tube i) := isOpen_strip _ _ _ _ _ _

theorem mem_tube_off {t s : ℝ} : P.off i t s ∈ D.tube i ↔
    D.lam < t ∧ t < P.len i - D.lam ∧ -D.rho < s ∧ s < D.rho := by
  rw [tube, mem_strip_iff, ClosedPolygon.coordAlong_off, ClosedPolygon.coordAcross_off]

theorem blockL_subset_tube : D.blockL i ⊆ D.tube i := by
  intro y hy
  obtain ⟨h1, h2, h3, h4⟩ := D.mem_blockL_iff.1 hy
  exact ⟨h1, h2, by linarith [D.rho_pos], h4⟩

theorem blockR_subset_tube : D.blockR i ⊆ D.tube i := by
  intro y hy
  obtain ⟨h1, h2, h3, h4⟩ := D.mem_blockR_iff.1 hy
  exact ⟨h1, h2, h3, by linarith [D.rho_pos]⟩

/-- **A vertex ball minus the curve is covered by the two sectors at that vertex.** A point of
the ball off the curve points in some direction from the vertex; by `mem_ray_or_mem_arcCCW'`
that direction is either one of the two incident rays — and then the point is *on* the incident
edge, because `R_le_len` says the sector does not run past the far end — or on one of the two
arcs, and then the point is in the corresponding sector. -/
theorem ball_diff_carrier_subset :
    ball (P.vertex i) D.R \ P.carrier ⊆ D.sectorL i ∪ D.sectorR i := by
  rintro y ⟨hy, hyc⟩
  have hne : y - P.vertex i ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    apply hyc
    rw [h]
    exact ClosedPolygon.vertex_mem_carrier
  rcases mem_ray_or_mem_arcCCW' (ClosedPolygon.det_rays_ne_zero (P := P) (i := i)) hne with
    ⟨c, hc, hcy⟩ | ⟨c, hc, hcy⟩ | harc | harc
  · -- Back along the incoming edge: the point lies on edge `i - 1`.
    exfalso
    apply hyc
    have hd : dist y (P.vertex i) = c := by
      rw [dist_eq_norm, hcy, norm_smul, Real.norm_eq_abs,
        ClosedPolygon.isDirection_rayIn.norm, mul_one, abs_of_pos hc]
    rw [mem_ball, hd] at hy
    have hy' : y = P.vertex i + c • P.rayIn i := by rw [← hcy]; module
    rw [hy']
    exact ClosedPolygon.edge_subset_carrier (ClosedPolygon.mem_edge_pred_of_smul_rayIn hc.le
      (le_trans hy.le (D.R_le_len (i - 1))))
  · -- Out along the outgoing edge: the point lies on edge `i`.
    exfalso
    apply hyc
    have hd : dist y (P.vertex i) = c := by
      rw [dist_eq_norm, hcy, norm_smul, Real.norm_eq_abs,
        ClosedPolygon.isDirection_tang.norm, mul_one, abs_of_pos hc]
    rw [mem_ball, hd] at hy
    have hy' : y = P.vertex i + c • P.tang i := by rw [← hcy]; module
    rw [hy']
    exact ClosedPolygon.edge_subset_carrier (ClosedPolygon.mem_edge_of_smul_tang hc.le
      (le_trans hy.le (D.R_le_len i)))
  · exact Or.inr ⟨harc, hy⟩
  · exact Or.inl ⟨harc, hy⟩

/-- **A tube minus the curve is its two blocks.** The only points of a tube on the curve are
those on the core of its own edge. -/
theorem tube_diff_carrier_subset : D.tube i \ P.carrier ⊆ D.blockL i ∪ D.blockR i := by
  rintro y ⟨⟨h1, h2, h3, h4⟩, hyc⟩
  rcases lt_trichotomy (coordAcross (P.vertex i) (P.tang i) y) 0 with h | h | h
  · exact Or.inr (D.mem_blockR_iff.2 ⟨h1, h2, h3, h⟩)
  · exfalso
    apply hyc
    have hy0 : y = P.pt i (coordAlong (P.vertex i) (P.tang i) y) := by
      rw [ClosedPolygon.pt, ← h]
      exact ClosedPolygon.off_coord P i y
    rw [hy0]
    exact ClosedPolygon.edge_subset_carrier (ClosedPolygon.pt_mem_edge
      ⟨by linarith [D.lam_pos], by linarith [D.lam_pos]⟩)
  · exact Or.inl (D.mem_blockL_iff.2 ⟨h1, h2, h, h4⟩)

/-- Each edge is covered by the ball at its first vertex, the ball at its second, and its own
tube: `lam < R` leaves no gap in the middle. -/
theorem carrier_subset_balls_union_tubes :
    P.carrier ⊆ (⋃ i, ball (P.vertex i) D.R) ∪ (⋃ i, D.tube i) := by
  rintro y hy
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
  rw [ClosedPolygon.mem_edge_iff] at hi
  obtain ⟨c, ⟨hc0, hc1⟩, rfl⟩ := hi
  rcases lt_or_ge c D.R with h1 | h1
  · refine Or.inl (Set.mem_iUnion.2 ⟨i, ?_⟩)
    rw [mem_ball, ClosedPolygon.dist_pt_vertex, abs_of_nonneg hc0]
    exact h1
  rcases lt_or_ge (P.len i - D.R) c with h2 | h2
  · refine Or.inl (Set.mem_iUnion.2 ⟨i + 1, ?_⟩)
    rw [mem_ball, ClosedPolygon.dist_pt_vertex_succ, abs_of_nonpos (by linarith)]
    linarith
  · refine Or.inr (Set.mem_iUnion.2 ⟨i, ?_⟩)
    rw [ClosedPolygon.pt]
    have hlam := D.lam_pos
    have hR := D.two_lam_lt_R
    exact D.mem_tube_off.2 ⟨by linarith, by linarith, by linarith [D.rho_pos], D.rho_pos⟩

/-- The collar is the union of the vertex balls and the edge tubes. This is the presentation
that makes it visibly open. -/
theorem nbhd_eq : D.nbhd = (⋃ i, ball (P.vertex i) D.R) ∪ (⋃ i, D.tube i) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ((hy | hy) | hy)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      rcases hi with hi | hi
      · exact Or.inl (Set.mem_iUnion.2 ⟨i, D.sector_subset_ball hi⟩)
      · exact Or.inr (Set.mem_iUnion.2 ⟨i, D.blockL_subset_tube hi⟩)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      rcases hi with hi | hi
      · exact Or.inl (Set.mem_iUnion.2 ⟨i, D.sectorR_subset_ball hi⟩)
      · exact Or.inr (Set.mem_iUnion.2 ⟨i, D.blockR_subset_tube hi⟩)
    · exact D.carrier_subset_balls_union_tubes hy
  · rintro y (hy | hy)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      by_cases hc : y ∈ P.carrier
      · exact Or.inr hc
      · rcases D.ball_diff_carrier_subset ⟨hi, hc⟩ with h | h
        · exact Or.inl (Or.inl (Set.mem_iUnion.2 ⟨i, Or.inl h⟩))
        · exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, Or.inl h⟩))
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      by_cases hc : y ∈ P.carrier
      · exact Or.inr hc
      · rcases D.tube_diff_carrier_subset ⟨hi, hc⟩ with h | h
        · exact Or.inl (Or.inl (Set.mem_iUnion.2 ⟨i, Or.inr h⟩))
        · exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, Or.inr h⟩))

theorem isOpen_nbhd : IsOpen D.nbhd := by
  rw [D.nbhd_eq]
  exact (isOpen_iUnion fun _ => isOpen_ball).union (isOpen_iUnion fun _ => D.isOpen_tube)

/-! ### Lemma 1.8 (a) -/

/-- **Two-sided polygonal strips, the closed case.** Given the constants, the collar of a simple
closed polygon is an open neighbourhood of the curve whose complement in it is the disjoint
union of the two connected open local sides. This is Lemma 1.8 (a) of the blueprint, modulo
`exists_stripData`, which produces the constants. -/
theorem collar :
    IsOpen D.nbhd ∧ P.carrier ⊆ D.nbhd ∧ D.nbhd \ P.carrier = D.sideL ∪ D.sideR ∧
      IsOpen D.sideL ∧ IsOpen D.sideR ∧ IsConnected D.sideL ∧ IsConnected D.sideR ∧
      Disjoint D.sideL D.sideR :=
  ⟨D.isOpen_nbhd, D.carrier_subset_nbhd, D.nbhd_diff_carrier, D.isOpen_sideL, D.isOpen_sideR,
    D.isConnected_sideL, D.isConnected_sideR, D.sideL_disjoint_sideR⟩

/-- The existential form of Lemma 1.8 (a): a simple closed polygonal curve for which the
constants exist has an open neighbourhood `N` with `N \ P` the disjoint union of two connected
open sets. -/
theorem exists_collar (D : StripData P) :
    ∃ N NL NR : Set Plane, IsOpen N ∧ P.carrier ⊆ N ∧ IsOpen NL ∧ IsOpen NR ∧
      IsConnected NL ∧ IsConnected NR ∧ Disjoint NL NR ∧ N \ P.carrier = NL ∪ NR :=
  ⟨D.nbhd, D.sideL, D.sideR, D.isOpen_nbhd, D.carrier_subset_nbhd, D.isOpen_sideL, D.isOpen_sideR,
    D.isConnected_sideL, D.isConnected_sideR, D.sideL_disjoint_sideR, D.nbhd_diff_carrier⟩

end StripData

end Schoenflies
