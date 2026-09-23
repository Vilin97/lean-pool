/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Realization

/-!
# Separation and crossing parity before normalization

`Schoenflies.ClosedPolygon` carries a `corner` field — no three consecutive vertices collinear —
and `Schoenflies.ClosedPolygon.isCornerAt_vertex` shows that field is not slack: a point at which
the curve runs straight is a vertex of *no* `ClosedPolygon` presentation of it. So a consumer that
must present a curve with vertices at prescribed points cannot use `ClosedPolygon` at all, and the
plane-graph arguments are exactly such consumers: the branch points of a drawing land wherever the
drawing puts them.

`Schoenflies.PrePolygon` is the presentation without that field, and vertices may be put anywhere.
This module gives it everything the crosscut chain asks of a simple closed polygon: an edge list
for the crossing count, the curve statements, the polygonal Jordan curve theorem, and the two
parity values.

## Everything transports across normalization, except the parity

`Schoenflies.PrePolygon.exists_closedPolygon_of_prePolygon` deletes redundant vertices and returns
a genuine `ClosedPolygon` **with the same carrier**. Any property of the carrier *as a set* is
therefore free: `isJordanCurve_carrier`, `isPolygonal_carrier` and `isSeparating_carrier` below are
each three lines, and none of them needs a word about vertices.

The crossing parity is not a property of the carrier. It is computed from a *list of edges*, and
normalization changes that list: it merges collinear edges, so `P.pieces` is a subdivision of the
normalized polygon's. Lemma 2.1 (`Schoenflies.parity_subdivide`) says subdivision does not change
the parity, which is why one *expects* the parity to transport — but the normalization theorem is
an existence statement and keeps no record of which points were deleted, so there is no
subdivision in hand to feed it. See the note at the end of this docstring.

The parity is therefore re-derived here, and the derivation turns out not to need the collar at
all. Once the curve is known to separate, the two values are forced:

* far along the ray direction the count is zero, and the half-plane where it is zero is convex and
  unbounded, hence lies in the unbounded region — so `π_C = 0` on the outside;
* across an interior point of any one edge the count jumps by one (Lemma 2.2), and the two test
  points lie off the curve, so they lie in different regions — so the other region carries `1`.

Both steps are stated for an arbitrary closed chain whose cover separates the plane
(`Schoenflies.parity_eq_zero_of_mem_outside_cover`, `…parity_eq_one_of_mem_inside_cover`); the
`PrePolygon` statements are instances. **The `ClosedPolygon` versions in
`Schoenflies/PolygonalJordan.lean` are instances too** — `ClosedPolygon.parity_eq_one_of_mem_inside`
currently goes through `StripData`, and does not have to.

## Blueprint

* `Schoenflies.PrePolygon.pieces`, `…cover_pieces`, `…isClosedChain_pieces`, `…pieces_nondeg` —
  the edge list the crossing count of §2 is defined on, for a vertex list that has not been
  normalized. Same list as `ClosedPolygon.pieces`; `PrePolygon.pieces_toPre` is `rfl`.
* `Schoenflies.PrePolygon.isJordanCurve_carrier`, `…isPolygonal_carrier` — §1, "a simple closed
  polygonal curve"; jointly the hypothesis of Theorem 2.3.
* `Schoenflies.PrePolygon.isSeparating_carrier` — **Theorem 2.3** in the form Definition 2.4 asks
  for, for a polygon presented with redundant vertices.
* `Schoenflies.PrePolygon.parity_flip_carrier` — Lemma 2.2, second half.
* `Schoenflies.parity_eq_zero_of_mem_outside_cover`,
  `Schoenflies.parity_eq_one_of_mem_inside_cover` — the last sentence of Theorem 2.3, for an
  arbitrary closed chain whose cover separates.
* `Schoenflies.PrePolygon.parity_eq_zero_of_mem_outside`, `…parity_eq_one_of_mem_inside`,
  `…parity_eq_zero_iff`, `…parity_eq_one_iff` — the same, read off a `PrePolygon`.

## Two notes for the integrator

**`PrePolygon.pieces` duplicates `ClosedPolygon.pieces`.** The two definitions are literally the
same expression and `PrePolygon.pieces_toPre` proves them equal by `rfl`. The right arrangement is
to define `ClosedPolygon.pieces P := P.toPre.pieces` and to keep only the `PrePolygon` proofs — the
proofs of `cover_pieces`, `isClosedChain_pieces`, `pieces_nondeg`, `pieces_nodup`,
`notMem_edge_of_mem_openSegment` and `parity_flip_carrier` in `Schoenflies/PolygonBridge.lean` use
`vertex_inj` and `edges_meet` and nothing else, so they are the proofs below with `ClosedPolygon`
written for `PrePolygon`. That refactor cannot happen inside this module: `PrePolygon` is declared
in `Schoenflies/Realization.lean`, which is *downstream* of `PolygonBridge`. It needs `PrePolygon`
moved up beside `ClosedPolygon` in `Schoenflies/Strip.lean`.

**Merging collinear edges is a subdivision, but not one this development can point at.** Deleting
a redundant vertex `v` replaces the two edges at `v` by their union, which is exactly undoing
`Schoenflies.splitAt v` on the merged edge; iterating, `P.pieces` is `subdivide P'.pieces vs` for
the list `vs` of deleted vertices — *up to the order of the list*, which `rotate` disturbs. So two
things are missing before `parity_subdivide` could be used here: `Schoenflies.parity` invariance
under `List.Perm` (immediate, `parity` is a sum over the list), and a strengthening of
`exists_closedPolygon_of_prePolygon` to
`∃ m' (P' : ClosedPolygon m') (vs : List Plane), P'.carrier = P.carrier ∧
  P.pieces ~ subdivide P'.pieces vs`, carried through the induction. The direct argument below is
shorter than either.
-/

@[expose] public section

open Bornology Metric Set

namespace Schoenflies

open Plane

/-! ## Small arithmetic helpers

Copies of two `private` facts of `Schoenflies/PolygonalJordan.lean`; they are `private` there and
so are these. -/

/-- In `ZMod 2` nothing is its own successor: this is what "the parities differ" comes down to. -/
private theorem ne_add_one_zmod_two (x : ZMod 2) : x ≠ x + 1 := by revert x; decide

/-- The only two values, named. -/
private theorem eq_one_of_ne_zero_zmod_two {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  revert h; revert x; decide

/-! ## The two parity values from separation alone

The blueprint reads the two values off a point far along the ray direction and off a point either
side of an edge. Neither step knows anything about vertices, so both are stated here for an
arbitrary closed chain whose cover separates the plane. -/

section GeneralParity

variable {L : List Piece} {u : Plane}

/-- The forward coordinate is linear. This is all that is needed to see that a half-plane is
convex. -/
private theorem isLinearMap_fwd (u : Plane) : IsLinearMap ℝ (fwd u) where
  map_add x y := by simp only [fwd_eq, Plane.add_apply]; ring
  map_smul c x := by simp only [fwd_eq, Plane.smul_apply, smul_eq_mul]; ring

/-- The half-plane of points more than `R` along the ray direction. Beyond a bound on the polygon
it is the region in which the crossing count is visibly zero, and it is unbounded, which is what
places it in the unbounded region. -/
private def farSide (u : Plane) (R : ℝ) : Set Plane := {z | R < fwd u z}

private theorem convex_farSide (u : Plane) (R : ℝ) : Convex ℝ (farSide u R) :=
  convex_halfSpace_gt (isLinearMap_fwd u) R

/-- The forward coordinate of a multiple of the direction is the multiple. -/
private theorem fwd_smul_self (hu : Plane.IsDirection u) (s : ℝ) : fwd u (s • u) = s := by
  have h : fwd u (s • u) = s * fwd u u := by simp only [fwd_eq, Plane.smul_apply]; ring
  rw [h, fwd_self hu, mul_one]

/-- The half-plane is unbounded: it contains points of every size along the direction. -/
private theorem not_isBounded_farSide (hu : Plane.IsDirection u) (R : ℝ) :
    ¬ IsBounded (farSide u R) := by
  intro hb
  obtain ⟨R', hR'⟩ := hb.subset_closedBall (0 : Plane)
  set t : ℝ := max (max R R') 0 + 1 with htdef
  have h0 : 0 ≤ max (max R R') 0 := le_max_right _ _
  have hpos : 0 < t := by rw [htdef]; linarith
  have hR1 : R < t := by
    have := le_trans (le_max_left R R') (le_max_left (max R R') 0)
    rw [htdef]; linarith
  have hR2 : R' < t := by
    have := le_trans (le_max_right R R') (le_max_left (max R R') 0)
    rw [htdef]; linarith
  have hmem : t • u ∈ farSide u R := by
    change R < fwd u (t • u)
    rw [fwd_smul_self hu]; exact hR1
  have hnorm : ‖t • u‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, hu, mul_one, abs_of_pos hpos]
  have := mem_closedBall_zero_iff.1 (hR' hmem)
  rw [hnorm] at this
  linarith

/-- **`π_C = 0` on the unbounded region** (Theorem 2.3, last sentence), for any closed chain whose
cover separates the plane.

The blueprint's argument: a point far enough along the ray direction is crossed by no edge, and the
whole half-plane of such points is convex — hence connected — and unbounded, so it lies in the
unbounded region. Parity is constant there (Lemma 2.2), and the value is the one read off the far
point. -/
theorem parity_eq_zero_of_mem_outside_cover (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ L, hgt u Q.1 ≠ hgt u Q.2) (hC : IsClosedChain L)
    (hsep : IsSeparating (cover L)) {x : Plane} (hx : x ∈ outside (cover L)) :
    parity u L x = 0 := by
  obtain ⟨R, hR⟩ := (isCompact_cover L).isBounded.subset_closedBall (0 : Plane)
  have hcov : ∀ z ∈ cover L, fwd u z ≤ R := fun z hz =>
    le_trans (le_trans (le_abs_self _) (abs_fwd_le_norm hu z)) (mem_closedBall_zero_iff.1 (hR hz))
  have hdisj : farSide u R ⊆ (cover L)ᶜ := fun z hz hzc => absurd (hcov z hzc) (not_le.2 hz)
  have hqf : fwd u ((R + 1) • u) = R + 1 := fwd_smul_self hu (R + 1)
  have hqmem : (R + 1) • u ∈ farSide u R := by
    change R < fwd u ((R + 1) • u)
    rw [hqf]; linarith
  -- the far point is in the unbounded region, because the whole half-plane is
  have hqout : (R + 1) • u ∈ outside (cover L) := by
    refine ⟨hdisj hqmem, fun hb => not_isBounded_farSide hu R (hb.subset ?_)⟩
    exact (convex_farSide u R).isPreconnected.subset_connectedComponentIn hqmem hdisj
  have hq0 : parity u L ((R + 1) • u) = 0 :=
    parity_eq_zero_of_lt hL fun z hz => lt_of_le_of_lt (hcov z hz) (by rw [hqf]; linarith)
  rw [← hq0]
  exact parity_eq_of_isPreconnected hu hL hC hsep.isConnected_outside.isPreconnected
    (fun z hz => hz.1) hx hqout

/-- **`π_C = 1` on the bounded region** (Theorem 2.3, last sentence), for any closed chain whose
cover separates the plane and which has *some* two points of the complement with different
parities.

Those two points cannot be in the same region, since parity is constant on a region; so one of them
is inside and the other outside. The outside carries `0`, hence the inside does not.

For a polygon the two points are supplied by Lemma 2.2: just before and just after an interior
point of any single edge. -/
theorem parity_eq_one_of_mem_inside_cover (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ L, hgt u Q.1 ≠ hgt u Q.2) (hC : IsClosedChain L)
    (hsep : IsSeparating (cover L)) {a b : Plane} (ha : a ∉ cover L) (hb : b ∉ cover L)
    (hab : parity u L a ≠ parity u L b) {x : Plane} (hx : x ∈ inside (cover L)) :
    parity u L x = 1 := by
  have hzero : ∀ y ∈ outside (cover L), parity u L y = 0 := fun y hy =>
    parity_eq_zero_of_mem_outside_cover hu hL hC hsep hy
  have hconst : ∀ y ∈ inside (cover L), parity u L y = parity u L x := fun y hy =>
    parity_eq_of_isPreconnected hu hL hC hsep.isConnected_inside.isPreconnected
      (fun z hz => hz.1) hy hx
  have hma : a ∈ inside (cover L) ∪ outside (cover L) := by rw [inside_union_outside]; exact ha
  have hmb : b ∈ inside (cover L) ∪ outside (cover L) := by rw [inside_union_outside]; exact hb
  refine eq_one_of_ne_zero_zmod_two ?_
  rcases hma with h | h <;> rcases hmb with h' | h'
  · exact absurd ((hconst a h).trans (hconst b h').symm) hab
  · rw [hzero b h'] at hab
    rw [← hconst a h]
    exact hab
  · rw [hzero a h] at hab
    rw [← hconst b h']
    exact Ne.symm hab
  · exact absurd ((hzero a h).trans (hzero b h').symm) hab

end GeneralParity

namespace PrePolygon

variable {m : ℕ}

/-! ## The edge list

Verbatim `Schoenflies.ClosedPolygon.pieces` with the structure changed; `pieces_toPre` records
that the two are the same list. -/

/-- The `m + 3` edges of the polygon, as a list of pieces in cyclic order. This is the form the
crossing count of §2 is defined on. -/
def pieces (P : PrePolygon m) : List Piece :=
  (List.range (m + 3)).map fun j : ℕ =>
    (P.vertex (j : ZMod (m + 3)), P.vertex ((j : ZMod (m + 3)) + 1))

/-- Forgetting the `corner` field does not change the edge list. -/
@[simp] theorem pieces_toPre (P : ClosedPolygon m) : P.toPre.pieces = P.pieces := rfl

/-- Every edge of the polygon is on the list. -/
theorem mem_pieces (P : PrePolygon m) (i : ZMod (m + 3)) :
    (P.vertex i, P.vertex (i + 1)) ∈ P.pieces := by
  refine List.mem_map.2 ⟨i.val, List.mem_range.2 (ZMod.val_lt i), ?_⟩
  rw [ZMod.natCast_rightInverse i]

/-- Every piece on the list is an edge of the polygon. -/
theorem exists_of_mem_pieces {P : PrePolygon m} {Q : Piece} (hQ : Q ∈ P.pieces) :
    ∃ i : ZMod (m + 3), Q = (P.vertex i, P.vertex (i + 1)) := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hQ
  exact ⟨(j : ZMod (m + 3)), rfl⟩

/-- No edge is degenerate: consecutive vertices are distinct. Redundant vertices are allowed, but
repeated ones are not. -/
theorem pieces_nondeg (P : PrePolygon m) : ∀ Q ∈ P.pieces, Q.Nondeg := by
  intro Q hQ
  obtain ⟨i, rfl⟩ := exists_of_mem_pieces hQ
  exact vertex_ne_succ i

/-- **The edge list is a closed chain.** Each vertex ends one edge and starts the next, so it is
counted twice; the cycle closes because `m + 3` is `0` in `ZMod (m + 3)`. -/
theorem isClosedChain_pieces (P : PrePolygon m) : IsClosedChain P.pieces := by
  intro f
  have hmap : (P.pieces.map fun Q => f Q.1 + f Q.2)
      = (List.range (m + 3)).map fun j : ℕ =>
        f (P.vertex (j : ZMod (m + 3))) + f (P.vertex ((j + 1 : ℕ) : ZMod (m + 3))) := by
    rw [pieces, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply, ClosedPolygon.natCast_succ]
  rw [hmap]
  have key := sum_range_boundary (fun k : ℕ => f (P.vertex (k : ZMod (m + 3)))) (m + 3)
  rw [key, Nat.cast_zero, ZMod.natCast_self]
  exact add_self_zmod_two _

/-- **The edge list carries the polygon.** This is the equation that turns every parity statement,
which is about `cover`, into a statement about the carrier. -/
theorem cover_pieces (P : PrePolygon m) : cover P.pieces = P.carrier := by
  apply Set.Subset.antisymm
  · rw [cover]
    refine Set.iUnion₂_subset fun Q hQ => ?_
    obtain ⟨i, rfl⟩ := exists_of_mem_pieces hQ
    exact Set.subset_iUnion (fun i => P.edge i) i
  · refine Set.iUnion_subset fun i => ?_
    exact fun z hz => mem_cover (P.mem_pieces i) hz

/-- The edge list has no repeated entry: distinct indices name distinct initial vertices. -/
theorem pieces_nodup (P : PrePolygon m) : P.pieces.Nodup := by
  rw [pieces]
  refine List.Nodup.map_on (fun j hj k hk heq => ?_) List.nodup_range
  exact ClosedPolygon.natCast_inj (List.mem_range.1 hj) (List.mem_range.1 hk)
    (P.vertex_inj (congrArg Prod.fst heq))

/-! ## The curve statements, and separation

All three are properties of the carrier as a set, and normalization keeps the carrier, so all three
come across from the `ClosedPolygon` versions with nothing to check. -/

/-- The carrier is compact: it is what a finite list of segments occupies. -/
theorem isCompact_carrier (P : PrePolygon m) : IsCompact P.carrier := by
  rw [← P.cover_pieces]; exact isCompact_cover _

theorem isClosed_carrier (P : PrePolygon m) : IsClosed P.carrier := P.isCompact_carrier.isClosed

/-- **The carrier is a Jordan curve**, redundant vertices and all. Deleting them does not move the
curve, and the normalized polygon's carrier is a Jordan curve. -/
theorem isJordanCurve_carrier (P : PrePolygon m) : IsJordanCurve P.carrier := by
  obtain ⟨m', P', hP'⟩ := exists_closedPolygon_of_prePolygon m P
  rw [← hP']
  exact P'.isJordanCurve_carrier

/-- **The carrier is polygonal.** -/
theorem isPolygonal_carrier (P : PrePolygon m) : IsPolygonal P.carrier := by
  obtain ⟨m', P', hP'⟩ := exists_closedPolygon_of_prePolygon m P
  rw [← hP']
  exact P'.isPolygonal_carrier

/-- **The polygonal Jordan curve theorem** (Theorem 2.3) for a polygon presented with redundant
vertices, in the form Definition 2.4 asks for.

This is the statement the crosscut machinery of `Schoenflies/CrosscutCells.lean` onwards consumes,
and `IsSeparating` speaks only of the carrier, so normalizing and quoting
`ClosedPolygon.isSeparating_carrier` is the whole proof. -/
theorem isSeparating_carrier (P : PrePolygon m) : IsSeparating P.carrier := by
  obtain ⟨m', P', hP'⟩ := exists_closedPolygon_of_prePolygon m P
  rw [← hP']
  exact P'.isSeparating_carrier

/-- Exactly two regions: the component of any point off the polygon is one of the two named
ones. -/
theorem connectedComponentIn_eq_inside_or_outside (P : PrePolygon m) {x : Plane}
    (hx : x ∉ P.carrier) :
    connectedComponentIn P.carrierᶜ x = inside P.carrier ∨
      connectedComponentIn P.carrierᶜ x = outside P.carrier := by
  have h : x ∈ inside P.carrier ∪ outside P.carrier := by rw [inside_union_outside]; exact hx
  rcases h with h | h
  · exact Or.inl (P.isSeparating_carrier.connectedComponentIn_eq_inside h)
  · exact Or.inr (P.isSeparating_carrier.connectedComponentIn_eq_outside h)

/-! ## The crossing parity

The list-level statements of `Schoenflies/Parity.lean`, read off a `PrePolygon`. -/

/-- A ray direction level for no edge of the polygon; the blueprint's "rotate the coordinate system
so that no edge is horizontal", with nothing rotated. -/
theorem exists_direction_pieces (P : PrePolygon m) :
    ∃ u : Plane, Plane.IsDirection u ∧ ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2 :=
  exists_direction_hgt_ne P.pieces P.pieces_nondeg

/-- **Crossing parity** (Lemma 2.2): `π_C` is constant on the component of the complement of the
carrier containing a given point. -/
theorem parity_eq_of_mem_connectedComponentIn_carrier (P : PrePolygon m) {u : Plane}
    (hu : Plane.IsDirection u) (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∉ P.carrier) (hy : y ∈ connectedComponentIn P.carrierᶜ x) :
    parity u P.pieces y = parity u P.pieces x := by
  rw [← P.cover_pieces] at hx hy
  exact parity_eq_of_mem_connectedComponentIn hu hL P.isClosedChain_pieces hx hy

/-- An interior point of one edge lies on no other edge: `edges_meet` puts any other edge's meeting
point at an end of this one, and an interior point is neither end. -/
theorem notMem_edge_of_mem_openSegment {P : PrePolygon m} {i j : ZMod (m + 3)} (hij : j ≠ i)
    {p : Plane} (hp : p ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1))) : p ∉ P.edge j := by
  intro hpj
  have hmem := P.edges_meet i j (Ne.symm hij)
    (Set.mem_inter (openSegment_subset_segment ℝ _ _ hp) hpj)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with rfl | rfl
  · exact vertex_ne_succ i (left_mem_openSegment_iff.1 hp)
  · exact vertex_ne_succ i (right_mem_openSegment_iff.1 hp)

/-- **Opposite sides of an edge** (Lemma 2.2, second half). Just before and just after an interior
point of an edge, in the ray direction, the base point is off the carrier and the crossing parity
differs by one.

The edge being crossed is split out of the list by `List.append_of_mem`; that the two remaining
fragments miss the crossing point is `edges_meet`, through
`PrePolygon.notMem_edge_of_mem_openSegment`. -/
theorem parity_flip_carrier (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
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
  -- `exists_of_mem_cover` is the destructor matching `Schoenflies.mem_cover`; it lives, by
  -- accident, inside the `ClosedPolygon` namespace in `Schoenflies/PolygonBridge.lean`.
  have h1 : p ∉ cover L₁ := by
    intro hmem
    obtain ⟨R, hR, hpR⟩ := ClosedPolygon.exists_of_mem_cover hmem
    exact hmiss R (List.mem_append_left _ hR) hpR
  have h2 : p ∉ cover L₂ := by
    intro hmem
    obtain ⟨R, hR, hpR⟩ := ClosedPolygon.exists_of_mem_cover hmem
    exact hmiss R (List.mem_append_right _ hR) hpR
  have hL' : ∀ R ∈ L₁ ++ (P.vertex i, P.vertex (i + 1)) :: L₂, hgt u R.1 ≠ hgt u R.2 := by
    rw [← hsplit]; exact hL
  obtain ⟨δ, hδ, hmain⟩ := parity_flip hu hL' hp h1 h2
  refine ⟨δ, hδ, fun t ht htδ => ?_⟩
  obtain ⟨ha, hb, hc⟩ := hmain t ht htδ
  rw [← hsplit] at ha hb hc
  rw [P.cover_pieces] at ha hb
  exact ⟨ha, hb, hc⟩

/-- Two points off the curve at which the parity differs: just before and just after the midpoint
of the first edge. This is what turns the separation theorem into the two parity *values*. -/
theorem exists_parity_ne (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) :
    ∃ a b : Plane, a ∉ P.carrier ∧ b ∉ P.carrier ∧
      parity u P.pieces a ≠ parity u P.pieces b := by
  have hpmem : (1 / 2 : ℝ) • P.vertex 0 + (1 / 2 : ℝ) • P.vertex 1
      ∈ openSegment ℝ (P.vertex 0) (P.vertex (0 + 1)) := by
    rw [zero_add]
    exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  obtain ⟨δ, hδ, hmain⟩ := P.parity_flip_carrier hu hL 0 hpmem
  obtain ⟨h1, h2, h3⟩ := hmain (δ / 2) (by linarith) (by linarith)
  refine ⟨_, _, h1, h2, fun hh => ?_⟩
  rw [h3] at hh
  exact ne_add_one_zmod_two _ hh.symm

/-- **`π_C = 0` on the unbounded region** (Theorem 2.3), for a polygon presented with redundant
vertices. -/
theorem parity_eq_zero_of_mem_outside (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∈ outside P.carrier) :
    parity u P.pieces x = 0 := by
  have hcov := P.cover_pieces
  refine parity_eq_zero_of_mem_outside_cover hu hL P.isClosedChain_pieces ?_ ?_
  · rw [hcov]; exact P.isSeparating_carrier
  · rw [hcov]; exact hx

/-- **`π_C = 1` on the bounded region** (Theorem 2.3), for a polygon presented with redundant
vertices. -/
theorem parity_eq_one_of_mem_inside (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∈ inside P.carrier) :
    parity u P.pieces x = 1 := by
  obtain ⟨a, b, ha, hb, hab⟩ := P.exists_parity_ne hu hL
  have hcov := P.cover_pieces
  refine parity_eq_one_of_mem_inside_cover (a := a) (b := b) hu hL P.isClosedChain_pieces
    ?_ ?_ ?_ hab ?_
  · rw [hcov]; exact P.isSeparating_carrier
  · rw [hcov]; exact ha
  · rw [hcov]; exact hb
  · rw [hcov]; exact hx

/-- **The crossing parity decides the region** (Theorem 2.3): off the curve, `π_C = 1` says
"inside". -/
theorem parity_eq_one_iff (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∉ P.carrier) :
    parity u P.pieces x = 1 ↔ x ∈ inside P.carrier := by
  have hmem : x ∈ inside P.carrier ∪ outside P.carrier := by
    rw [inside_union_outside]; exact hx
  refine ⟨fun h1 => ?_, P.parity_eq_one_of_mem_inside hu hL⟩
  rcases hmem with h | h
  · exact h
  · rw [P.parity_eq_zero_of_mem_outside hu hL h] at h1
    exact absurd h1 (by decide)

/-- **The crossing parity decides the region**, the other way round. -/
theorem parity_eq_zero_iff (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∉ P.carrier) :
    parity u P.pieces x = 0 ↔ x ∈ outside P.carrier := by
  have hmem : x ∈ inside P.carrier ∪ outside P.carrier := by
    rw [inside_union_outside]; exact hx
  refine ⟨fun h0 => ?_, P.parity_eq_zero_of_mem_outside hu hL⟩
  rcases hmem with h | h
  · rw [P.parity_eq_one_of_mem_inside hu hL h] at h0
    exact absurd h0 (by decide)
  · exact h

end PrePolygon

/-! ## The `ClosedPolygon` parity values are instances

A machine check of the claim made in this module's docstring. `Schoenflies/PolygonalJordan.lean`
proves `ClosedPolygon.parity_eq_one_of_mem_inside` from a `StripData` — the collar of Lemma 1.8,
which is where `corner` is used. The collar is needed for Theorem 2.3 itself, but *not* a second
time for the parity value: given separation, the two values follow from the general lemmas above.
The two `example`s below are the same statements, re-proved that way. -/

example {m : ℕ} (P : ClosedPolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∈ outside P.carrier) :
    parity u P.pieces x = 0 := by
  have hcov := P.cover_pieces
  refine parity_eq_zero_of_mem_outside_cover hu hL P.isClosedChain_pieces ?_ ?_
  · rw [hcov]; exact P.isSeparating_carrier
  · rw [hcov]; exact hx

example {m : ℕ} (P : ClosedPolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∈ inside P.carrier) :
    parity u P.pieces x = 1 := by
  -- the two points of opposite parity come from an edge, not from a track of the collar
  obtain ⟨a, b, ha, hb, hab⟩ := P.toPre.exists_parity_ne hu hL
  have hcov := P.cover_pieces
  refine parity_eq_one_of_mem_inside_cover (a := a) (b := b) hu hL P.isClosedChain_pieces
    ?_ ?_ ?_ hab ?_
  · rw [hcov]; exact P.isSeparating_carrier
  · rw [hcov]; exact ha
  · rw [hcov]; exact hb
  · rw [hcov]; exact hx

end Schoenflies
