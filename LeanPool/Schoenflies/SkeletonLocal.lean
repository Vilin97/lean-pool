/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Strip
public import LeanPool.Schoenflies.SimpleArc
public import LeanPool.Schoenflies.UniformBound
public import LeanPool.Schoenflies.Graph.Drawing

/-!
# Local structure of a polygonal skeleton

Close enough to any of its points, a finite union of segments and points looks like a *star*:
the point itself together with finitely many radial segments leaving it, one per local branch.
This module proves that, and hands the accessibility argument the form it needs.

## What is exported, and why in this shape

The data is `Schoenflies.localDirs S x`, the set of unit vectors `d` such that some initial
segment `[x, x + ε • d]` lies in `S`. It is defined for an arbitrary set, with no choices in
it: nothing about a segment decomposition of `S` enters the definition, so no consumer has to
carry one. "Pairwise distinct directions" is then not a clause to be proved but the meaning of
the word *set*, and the blueprint's real content becomes `localDirs_finite`.

The radius is the one genuinely existential ingredient — there is no canonical `r₀` — so it is
named by a predicate rather than returned inside an `∃`-packaged bundle of properties:

  `Schoenflies.IsLocalRadius S x r` : `0 < r`, and every point within `r` of `x` lies in `S`
  exactly when it is `x` itself or leaves `x` in a local direction.

That single membership criterion is equivalent to the blueprint's picture and implies all of
its parts, each proved here as a lemma about `IsLocalRadius` and hence available at every
radius below the one produced: the closed-disk formula
(`IsLocalRadius.closedBall_inter`), the open disk minus `S` as a *cone* over the complement of
the local rays (`IsLocalRadius.ball_diff_eq_cone`), and the star-shapedness that the
accessibility lemma actually cites (`IsLocalRadius.openSegment_subset_ball_diff`).

## What the consumer (`lem:polygonal-side-accessibility`) needs

That lemma takes `y` in a face `F` inside the disk, and wants a polygonal arc from `x` into
`F`. `IsLocalRadius.openSegment_subset_ball_diff` gives `(x, y) ⊆ B(x, r) \ S` directly, and
`openSegment ℝ x y ∪ {y}` is connected and disjoint from the skeleton — which is everything
the blueprint's "pick the sector containing `y`, then a short segment from `x` into it" is used
for. The decomposition of the punctured disk into its *individual* sectors, one per pair of
cyclically adjacent local directions, is therefore **not** proved here: it needs a cyclic
order on directions, and no consumer needs it. `IsLocalRadius.ball_diff_eq_cone` records the
sectors in aggregate — as one `Plane.cone` over all free directions at once.

## Blueprint

* `Schoenflies.localDirs`, `Schoenflies.localDirs_finite` — the finitely many local branch
  directions at `x` of Lemma "Local structure of a polygonal skeleton"
  (`lem:local-skeleton-structure`).
* `Schoenflies.IsLocalRadius`, `Schoenflies.exists_isLocalRadius`,
  `Schoenflies.IsLocalRadius.closedBall_inter` — the radius `r₀`, and "for every `0 < r ≤ r₀`
  the closed disk meets `|G|` exactly in finitely many straight segments from `x` with
  pairwise distinct directions" (same lemma).
* `Schoenflies.IsLocalRadius.ball_diff_eq_cone` — "consequently `B(x,r) \ |G|` is a finite
  union of open circular sectors" (same lemma), in aggregate form.
* `Schoenflies.IsLocalRadius.openSegment_subset_ball_diff` — the form
  `lem:polygonal-side-accessibility` cites: a short straight segment from `x` towards any
  point of the punctured disk misses the skeleton.
* `Graph.IsDrawing.exists_cover`, `Graph.IsDrawing.exists_isLocalRadius`,
  `Graph.IsDrawing.finite_localDirs` — the same statements for a finite plane graph all of
  whose edges are polygonal.
* `Graph.IsDrawing.openSegment_subset_face` — the access arc of
  `lem:polygonal-side-accessibility`, assembled: a straight segment from `x` to a point of the
  exterior inside a local disk lies, minus `x`, in that point's face.
-/

public section

open Metric Set
open scoped Graph

namespace Schoenflies

variable {S T F : Set Plane} {ps : List Piece} {x y z c d : Plane} {r R ε t : ℝ}

/-! ### Radial segments

`segment ℝ x (x + r • d)` with `d` a unit vector is the closed radius of length `r` leaving
`x` in the direction `d`. Two facts run the whole module: a point lies on it exactly when it
is near enough and points the right way (`mem_radial_iff`), and cutting a longer radius by a
smaller ball leaves the shorter radius (`radial_inter_closedBall`). -/

/-- The unit vector along a positive multiple of a unit vector is that vector. -/
theorem dir_smul_of_isDirection (hd : Plane.IsDirection d) (ht : 0 < t) :
    Plane.dir (t • d) = d := by
  have hn : ‖t • d‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, hd.norm, mul_one]
  rw [Plane.dir, hn, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]

/-- A nonzero vector is its own length times its own direction. -/
theorem smul_norm_dir (h : d ≠ 0) : ‖d‖ • Plane.dir d = d := by
  rw [Plane.dir, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 h), one_smul]

/-- Positive scaling does not move a direction. -/
theorem dir_smul_pos (ht : 0 < t) (u : Plane) : Plane.dir (t • u) = Plane.dir u := by
  have hn : ‖t • u‖ = t * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  rw [Plane.dir, Plane.dir, hn, smul_smul, mul_inv, mul_comm t⁻¹, mul_assoc,
    inv_mul_cancel₀ ht.ne', mul_one]

/-- Membership in a radius: near enough, and pointing the right way. -/
theorem mem_radial_iff (hd : Plane.IsDirection d) (hr : 0 < r) :
    z ∈ segment ℝ x (x + r • d) ↔ dist z x ≤ r ∧ (z = x ∨ Plane.dir (z - x) = d) := by
  constructor
  · intro hz
    rw [segment_eq_image'] at hz
    obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hz
    have hsub : x + θ • (x + r • d - x) - x = (θ * r) • d := by module
    have hnorm : dist (x + θ • (x + r • d - x)) x = θ * r := by
      rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), hd.norm, mul_one]
    refine ⟨by rw [hnorm]; nlinarith, ?_⟩
    rcases eq_or_lt_of_le hθ0 with rfl | hθpos
    · left; simp
    · exact Or.inr (by rw [hsub, dir_smul_of_isDirection hd (by positivity)])
  · rintro ⟨hdist, hz⟩
    rcases eq_or_ne z x with rfl | hzx
    · exact left_mem_segment ℝ _ _
    have hdir : Plane.dir (z - x) = d := hz.resolve_left hzx
    have hne : z - x ≠ 0 := sub_ne_zero.2 hzx
    have hL : ‖z - x‖ • d = z - x := by rw [← hdir]; exact smul_norm_dir hne
    have hdn : ‖z - x‖ ≤ r := by rwa [dist_eq_norm] at hdist
    -- The parameter is the fraction of the radius already travelled.
    refine ⟨1 - ‖z - x‖ / r, ‖z - x‖ / r, by
      have := (div_le_one hr).2 hdn; linarith, by positivity, by ring, ?_⟩
    have hθ : ‖z - x‖ / r * r = ‖z - x‖ := div_mul_cancel₀ _ hr.ne'
    calc (1 - ‖z - x‖ / r) • x + (‖z - x‖ / r) • (x + r • d)
        = x + (‖z - x‖ / r * r) • d := by module
      _ = x + ‖z - x‖ • d := by rw [hθ]
      _ = z := by rw [hL]; module

/-- A radius of length `r` lies in the closed disk of radius `r`. -/
theorem radial_subset_closedBall (hd : Plane.IsDirection d) (hr : 0 < r) :
    segment ℝ x (x + r • d) ⊆ closedBall x r := fun _ hz =>
  mem_closedBall.2 ((mem_radial_iff hd hr).1 hz).1

/-- Cutting a radius by a smaller concentric disk leaves the shorter radius. -/
theorem radial_inter_closedBall (hd : Plane.IsDirection d) (hr : 0 < r) (hrR : r ≤ R) :
    segment ℝ x (x + R • d) ∩ closedBall x r = segment ℝ x (x + r • d) := by
  ext z
  simp only [mem_inter_iff, mem_closedBall, mem_radial_iff hd (lt_of_lt_of_le hr hrR),
    mem_radial_iff hd hr]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans hrR, h.2⟩, h.1⟩⟩

/-- A segment out of `x` is the radius of its own length in its own direction. -/
theorem segment_eq_radial (h : c ≠ x) :
    segment ℝ x c = segment ℝ x (x + dist x c • Plane.dir (c - x)) := by
  have hne : c - x ≠ 0 := sub_ne_zero.2 h
  have : x + dist x c • Plane.dir (c - x) = c := by
    rw [dist_eq_norm', smul_norm_dir hne]
    module
  rw [this]

/-- **Inside a disk too small to reach `c`, the segment `[x, c]` is exactly a radius.** This is
the one geometric step behind the whole module: it turns each straight piece through `x` into
one or two radial segments. -/
theorem segment_inter_closedBall (hcx : c ≠ x) (hr : 0 < r) (hrc : r ≤ dist x c) :
    segment ℝ x c ∩ closedBall x r = segment ℝ x (x + r • Plane.dir (c - x)) := by
  rw [segment_eq_radial hcx]
  exact radial_inter_closedBall (Plane.isDirection_dir (sub_ne_zero.2 hcx)) hr hrc

/-! ### The local directions of a set -/

/-- The *local directions* of `S` at `x`: the unit vectors along which `S` contains an initial
segment issuing from `x`.

Choice-free and stated for an arbitrary set, so that a consumer never has to name a segment
decomposition of `S`. Being a *set* of unit vectors, its members are automatically pairwise
distinct — the blueprint's "with pairwise distinct directions". -/
def localDirs (S : Set Plane) (x : Plane) : Set Plane :=
  {d | Plane.IsDirection d ∧ ∃ ε : ℝ, 0 < ε ∧ segment ℝ x (x + ε • d) ⊆ S}

theorem isDirection_of_mem_localDirs (h : d ∈ localDirs S x) : Plane.IsDirection d := h.1

theorem mem_localDirs (hd : Plane.IsDirection d) (hε : 0 < ε)
    (h : segment ℝ x (x + ε • d) ⊆ S) : d ∈ localDirs S x := ⟨hd, ε, hε, h⟩

theorem localDirs_mono (h : S ⊆ T) : localDirs S x ⊆ localDirs T x := by
  rintro d ⟨hd, ε, hε, hsub⟩
  exact ⟨hd, ε, hε, hsub.trans h⟩

/-- A local direction witnesses that `x` itself belongs to `S`. -/
theorem mem_of_mem_localDirs (h : d ∈ localDirs S x) : x ∈ S :=
  h.2.choose_spec.2 (left_mem_segment ℝ _ _)

/-! ### The pieces through a point

Everything is now bookkeeping over a finite list of segments and a finite set of stray points.
`GoodRadius x P r` collects what a radius must avoid on account of one piece: pieces missing
`x` must stay outside the disk, and pieces through `x` must not end inside it. -/

/-- The radius conditions imposed at `x` by one piece: a piece missing `x` stays clear of the
closed disk, and an endpoint of a piece through `x` is never inside it. -/
def GoodRadius (x : Plane) (P : Piece) (r : ℝ) : Prop :=
  (x ∉ P.seg → ∀ z ∈ P.seg, r < dist x z) ∧
    (P.1 ≠ x → r ≤ dist x P.1) ∧ (P.2 ≠ x → r ≤ dist x P.2)

theorem GoodRadius.mono {P : Piece} (h : GoodRadius x P r) (hle : ε ≤ r) :
    GoodRadius x P ε :=
  ⟨fun hx z hz => lt_of_le_of_lt hle (h.1 hx z hz), fun h1 => hle.trans (h.2.1 h1),
    fun h2 => hle.trans (h.2.2 h2)⟩

theorem exists_goodRadius (x : Plane) (P : Piece) : ∃ r > 0, GoodRadius x P r := by
  by_cases hx : x ∈ P.seg
  · -- Only the endpoints matter; a coincident endpoint imposes nothing.
    refine ⟨min (if P.1 = x then 1 else dist x P.1) (if P.2 = x then 1 else dist x P.2), ?_,
      fun h => absurd hx h, ?_, ?_⟩
    · refine lt_min ?_ ?_ <;> split_ifs with h
      · exact one_pos
      · exact dist_pos.2 (Ne.symm h)
      · exact one_pos
      · exact dist_pos.2 (Ne.symm h)
    · intro h1
      exact le_trans (min_le_left _ _) (le_of_eq (ite_eq_right h1))
    · intro h2
      exact le_trans (min_le_right _ _) (le_of_eq (ite_eq_right h2))
  · -- A piece missing `x` is a compact set at positive distance from `x`.
    obtain ⟨ρ, hρ, hd⟩ := Plane.exists_dist_pos isCompact_singleton (isCompact_segment P.1 P.2)
      (Set.disjoint_singleton_left.2 hx)
    have hall : ∀ z ∈ P.seg, ρ ≤ dist x z := fun z hz => hd x rfl z hz
    refine ⟨ρ / 2, by positivity, fun _ z hz => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact lt_of_lt_of_le (by linarith) (hall z hz)
    · exact le_trans (by linarith) (hall P.1 (left_mem_segment ℝ _ _))
    · exact le_trans (by linarith) (hall P.2 (right_mem_segment ℝ _ _))

/-- Auxiliary: the directions in which the pieces of `ps` leave `x`. Unlike `localDirs` this
depends on the chosen segment decomposition; the two are proved equal at any good radius. -/
def pieceDirs (ps : List Piece) (x : Plane) : Set Plane :=
  {d | ∃ P ∈ ps, x ∈ P.seg ∧
    ((P.1 ≠ x ∧ d = Plane.dir (P.1 - x)) ∨ (P.2 ≠ x ∧ d = Plane.dir (P.2 - x)))}

theorem isDirection_of_mem_pieceDirs (h : d ∈ pieceDirs ps x) : Plane.IsDirection d := by
  obtain ⟨P, -, -, (⟨h1, rfl⟩ | ⟨h2, rfl⟩)⟩ := h
  · exact Plane.isDirection_dir (sub_ne_zero.2 h1)
  · exact Plane.isDirection_dir (sub_ne_zero.2 h2)

theorem pieceDirs_finite (ps : List Piece) (x : Plane) : (pieceDirs ps x).Finite := by
  refine Set.Finite.subset (Set.Finite.image (fun c => Plane.dir (c - x))
    (((List.finite_toSet ps).image Prod.fst).union ((List.finite_toSet ps).image Prod.snd))) ?_
  rintro d ⟨P, hP, -, (⟨-, rfl⟩ | ⟨-, rfl⟩)⟩
  · exact ⟨P.1, Or.inl ⟨P, hP, rfl⟩, rfl⟩
  · exact ⟨P.2, Or.inr ⟨P, hP, rfl⟩, rfl⟩

/-- A radius in a piece direction, at a good radius, stays inside the pieces. -/
theorem radial_subset_cover (hgood : ∀ P ∈ ps, GoodRadius x P r) (hr : 0 < r)
    (hd : d ∈ pieceDirs ps x) : segment ℝ x (x + r • d) ⊆ cover ps := by
  obtain ⟨P, hP, hxP, hcase⟩ := hd
  -- Both cases are the same computation with the two endpoints exchanged.
  have key : ∀ c ∈ P.seg, c ≠ x → r ≤ dist x c →
      segment ℝ x (x + r • Plane.dir (c - x)) ⊆ cover ps := by
    intro c hc hcx hrc
    have h1 : segment ℝ x (x + r • Plane.dir (c - x)) ⊆ segment ℝ x c := by
      rw [← segment_inter_closedBall hcx hr hrc]
      exact inter_subset_left
    have h2 : segment ℝ x c ⊆ P.seg := (convex_segment P.1 P.2).segment_subset hxP hc
    exact h1.trans (h2.trans (Set.subset_biUnion_of_mem (u := fun P : Piece => P.seg) hP))
  rcases hcase with ⟨h1, rfl⟩ | ⟨h2, rfl⟩
  · exact key P.1 (left_mem_segment ℝ _ _) h1 ((hgood P hP).2.1 h1)
  · exact key P.2 (right_mem_segment ℝ _ _) h2 ((hgood P hP).2.2 h2)

/-- At a good radius, the pieces meet the closed disk only in `x` and the radii. -/
theorem cover_inter_closedBall_subset (hgood : ∀ P ∈ ps, GoodRadius x P r) (hr : 0 < r) :
    cover ps ∩ closedBall x r ⊆ insert x (⋃ d ∈ pieceDirs ps x, segment ℝ x (x + r • d)) := by
  rintro z ⟨hzc, hzb⟩
  obtain ⟨P, hP, hzP⟩ : ∃ P ∈ ps, z ∈ P.seg := by
    simpa only [cover, mem_iUnion, exists_prop] using hzc
  have hdist : dist x z ≤ r := by rw [dist_comm]; exact mem_closedBall.1 hzb
  -- A piece meeting the disk at all must pass through `x`.
  have hxP : x ∈ P.seg := by
    by_contra hx
    exact absurd hdist (not_le.2 ((hgood P hP).1 hx z hzP))
  -- Split the piece at `x`; each half is a radius, unless it has collapsed onto `x`.
  rw [Piece.seg, segment_split hxP] at hzP
  rcases hzP with hz | hz
  · rw [segment_symm] at hz
    rcases eq_or_ne P.1 x with h1 | h1
    · rw [h1, segment_same] at hz
      exact Or.inl hz
    · have hmem : Plane.dir (P.1 - x) ∈ pieceDirs ps x := ⟨P, hP, hxP, Or.inl ⟨h1, rfl⟩⟩
      refine Or.inr (mem_biUnion hmem ?_)
      rw [← segment_inter_closedBall h1 hr ((hgood P hP).2.1 h1)]
      exact ⟨hz, hzb⟩
  · rcases eq_or_ne P.2 x with h2 | h2
    · rw [h2, segment_same] at hz
      exact Or.inl hz
    · have hmem : Plane.dir (P.2 - x) ∈ pieceDirs ps x := ⟨P, hP, hxP, Or.inr ⟨h2, rfl⟩⟩
      refine Or.inr (mem_biUnion hmem ?_)
      rw [← segment_inter_closedBall h2 hr ((hgood P hP).2.2 h2)]
      exact ⟨hz, hzb⟩

/-! ### The membership criterion -/

/-- **`r` is a local radius for `S` at `x`**: within distance `r` of `x`, the set `S` consists
of `x` together with the rays leaving `x` in the local directions.

This one criterion is the whole local picture; the disk formula, the sector description and
the star-shapedness are all derived from it below, and each therefore holds at every positive
radius below a local radius (`IsLocalRadius.mono`). -/
def IsLocalRadius (S : Set Plane) (x : Plane) (r : ℝ) : Prop :=
  0 < r ∧ ∀ z, dist z x ≤ r → (z ∈ S ↔ z = x ∨ Plane.dir (z - x) ∈ localDirs S x)

theorem IsLocalRadius.pos (h : IsLocalRadius S x r) : 0 < r := h.1

theorem IsLocalRadius.mono (h : IsLocalRadius S x r) (hε : 0 < ε) (hle : ε ≤ r) :
    IsLocalRadius S x ε :=
  ⟨hε, fun z hz => h.2 z (hz.trans hle)⟩

/-! ### A local radius exists

The construction: choose a radius good for every piece and strictly below the distance to
every stray point other than `x`. -/

theorem exists_pos_goodRadius (hF : F.Finite) (ps : List Piece) (x : Plane) :
    ∃ r > 0, (∀ P ∈ ps, GoodRadius x P r) ∧ ∀ p ∈ F, p ≠ x → r < dist x p := by
  obtain ⟨r₁, hr₁, h₁⟩ :=
    exists_pos_forall_of_finite (List.finite_toSet ps) (P := fun P r => GoodRadius x P r)
      (fun _ _ _ _ hle h => h.mono hle) (fun P _ => exists_goodRadius x P)
  have hex : ∀ p ∈ F, ∃ ε > 0, (p ≠ x → ε < dist x p) := by
    intro p _
    rcases eq_or_ne p x with rfl | hne
    · exact ⟨1, one_pos, fun h => absurd rfl h⟩
    · have hpos : 0 < dist x p := dist_pos.2 (Ne.symm hne)
      exact ⟨dist x p / 2, half_pos hpos, fun _ => by linarith⟩
  obtain ⟨r₂, hr₂, h₂⟩ :=
    exists_pos_forall_of_finite hF (P := fun p r => p ≠ x → r < dist x p)
      (fun _ _ _ _ hle h hne => lt_of_le_of_lt hle (h hne)) hex
  exact ⟨min r₁ r₂, lt_min hr₁ hr₂,
    fun P hP => (h₁ P hP).mono (min_le_left _ _),
    fun p hp hne => lt_of_le_of_lt (min_le_right _ _) (h₂ p hp hne)⟩

/-- Every piece direction is a local direction: at a good radius the whole radius fits in the
pieces. -/
theorem pieceDirs_subset_localDirs (hS : S = F ∪ cover ps) (hr : 0 < r)
    (hgood : ∀ P ∈ ps, GoodRadius x P r) : pieceDirs ps x ⊆ localDirs S x := fun _ hd =>
  ⟨isDirection_of_mem_pieceDirs hd, r, hr,
    (radial_subset_cover hgood hr hd).trans (hS ▸ subset_union_right)⟩

/-- The membership criterion, phrased with the auxiliary `pieceDirs`. -/
theorem mem_iff_of_goodRadius (hS : S = F ∪ cover ps) (hr : 0 < r) (hx : x ∈ S)
    (hgood : ∀ P ∈ ps, GoodRadius x P r) (hFgood : ∀ p ∈ F, p ≠ x → r < dist x p)
    (hz : dist z x ≤ r) : z ∈ S ↔ z = x ∨ Plane.dir (z - x) ∈ pieceDirs ps x := by
  constructor
  · intro hzS
    rcases eq_or_ne z x with rfl | hzx
    · exact Or.inl rfl
    rw [hS] at hzS
    rcases hzS with hzF | hzc
    · -- A stray point inside the disk can only be `x` itself.
      exact absurd (hFgood z hzF hzx) (not_lt.2 (by rw [dist_comm]; exact hz))
    · rcases cover_inter_closedBall_subset hgood hr ⟨hzc, mem_closedBall.2 hz⟩ with h | h
      · exact absurd h hzx
      · obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.1 h
        have := (mem_radial_iff (isDirection_of_mem_pieceDirs hd) hr).1 hzd
        exact Or.inr (((this.2.resolve_left hzx)) ▸ hd)
  · rintro (rfl | hd)
    · exact hx
    rcases eq_or_ne z x with rfl | hzx
    · exact hx
    have hmem : z ∈ segment ℝ x (x + r • Plane.dir (z - x)) :=
      (mem_radial_iff (isDirection_of_mem_pieceDirs hd) hr).2 ⟨hz, Or.inr rfl⟩
    exact hS ▸ Or.inr (radial_subset_cover hgood hr hd hmem)

/-- Conversely, at a good radius every local direction comes from a piece. This is where the
germ hypothesis in `localDirs` is cashed in: a short segment in `S` leaving `x` lands in a
piece, and that piece must pass through `x`. -/
theorem localDirs_subset_pieceDirs (hS : S = F ∪ cover ps) (hr : 0 < r)
    (hgood : ∀ P ∈ ps, GoodRadius x P r) (hFgood : ∀ p ∈ F, p ≠ x → r < dist x p) :
    localDirs S x ⊆ pieceDirs ps x := by
  rintro d hd
  obtain ⟨hdir, ε, hε, hsub⟩ := hd
  have hx : x ∈ S := hsub (left_mem_segment ℝ _ _)
  set t := min ε r with ht
  have htpos : 0 < t := lt_min hε hr
  -- Walk a distance `t` along the germ; the point reached is in `S` and inside the disk.
  have hmem : x + t • d ∈ segment ℝ x (x + ε • d) :=
    (mem_radial_iff hdir hε).2 ⟨by
        rw [dist_eq_norm, show x + t • d - x = t • d by module, norm_smul, Real.norm_eq_abs,
          abs_of_pos htpos, hdir.norm, mul_one]
        exact min_le_left _ _,
      Or.inr (by rw [show x + t • d - x = t • d by module, dir_smul_of_isDirection hdir htpos])⟩
  have hdist : dist (x + t • d) x ≤ r := by
    rw [dist_eq_norm, show x + t • d - x = t • d by module, norm_smul, Real.norm_eq_abs,
      abs_of_pos htpos, hdir.norm, mul_one]
    exact min_le_right _ _
  have hne : x + t • d ≠ x := by
    intro h
    have : t • d = 0 := by
      have := sub_eq_zero.2 h
      rw [show x + t • d - x = t • d by module] at this
      exact this
    rcases smul_eq_zero.1 this with h' | h'
    · exact absurd h' htpos.ne'
    · exact hdir.ne_zero h'
  have := (mem_iff_of_goodRadius hS hr hx hgood hFgood hdist).1 (hsub hmem)
  rcases this with h | h
  · exact absurd h hne
  · rwa [show x + t • d - x = t • d by module, dir_smul_of_isDirection hdir htpos] at h

/-- **The local directions of a finite union of segments and points are finitely many.** This
is the blueprint's "finitely many straight segments from `x` with pairwise distinct
directions": distinctness is automatic for a set, finiteness is the content. -/
theorem localDirs_finite (hF : F.Finite) (hS : S = F ∪ cover ps) (x : Plane) :
    (localDirs S x).Finite := by
  obtain ⟨r, hr, hgood, hFgood⟩ := exists_pos_goodRadius hF ps x
  exact (pieceDirs_finite ps x).subset (localDirs_subset_pieceDirs hS hr hgood hFgood)

/-- **A local radius exists.** Lemma "Local structure of a polygonal skeleton", for a set
presented as finitely many points together with finitely many segments. -/
theorem exists_isLocalRadius (hF : F.Finite) (hS : S = F ∪ cover ps) (hx : x ∈ S) :
    ∃ r, IsLocalRadius S x r := by
  obtain ⟨r, hr, hgood, hFgood⟩ := exists_pos_goodRadius hF ps x
  refine ⟨r, hr, fun z hz => ?_⟩
  rw [mem_iff_of_goodRadius hS hr hx hgood hFgood hz]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (pieceDirs_subset_localDirs hS hr hgood h)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (localDirs_subset_pieceDirs hS hr hgood hFgood h)

/-! ### What a local radius gives -/

/-- **The closed disk meets `S` exactly in the radial segments.** The blueprint's "the closed
disk `B(x,r)` meets `|G|` exactly in finitely many straight segments from `x` with pairwise
distinct directions". -/
theorem IsLocalRadius.closedBall_inter (h : IsLocalRadius S x r) (hx : x ∈ S) :
    closedBall x r ∩ S = insert x (⋃ d ∈ localDirs S x, segment ℝ x (x + r • d)) := by
  ext z
  constructor
  · rintro ⟨hzb, hzS⟩
    rcases (h.2 z (mem_closedBall.1 hzb)).1 hzS with hzx | hd
    · exact Or.inl hzx
    · refine Or.inr (mem_biUnion hd ?_)
      exact (mem_radial_iff (isDirection_of_mem_localDirs hd) h.pos).2
        ⟨mem_closedBall.1 hzb, Or.inr rfl⟩
  · rintro (rfl | hz)
    · exact ⟨mem_closedBall_self h.pos.le, hx⟩
    · obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.1 hz
      obtain ⟨hdist, hcase⟩ := (mem_radial_iff (isDirection_of_mem_localDirs hd) h.pos).1 hzd
      refine ⟨mem_closedBall.2 hdist, (h.2 z hdist).2 ?_⟩
      rcases hcase with hzx | hdir
      · exact Or.inl hzx
      · exact Or.inr (hdir ▸ hd)

/-- **The punctured disk is a union of open sectors**, in aggregate: `B(x,r) \ S` is the open
cone over the directions that are not local directions.

The individual sectors — one per cyclically adjacent pair of local directions — are not
separated out; see the module docstring. -/
theorem IsLocalRadius.ball_diff_eq_cone (h : IsLocalRadius S x r) :
    ball x r \ S = Plane.cone x {u | u ≠ 0 ∧ Plane.dir u ∉ localDirs S x} r := by
  ext z
  simp only [Set.mem_sdiff, mem_ball, Plane.mem_cone_iff, Set.mem_ofPred_eq, sub_ne_zero]
  constructor
  · rintro ⟨hzb, hzS⟩
    have hiff := h.2 z hzb.le
    refine ⟨⟨fun hzx => hzS (hiff.2 (Or.inl hzx)), fun hd => hzS (hiff.2 (Or.inr hd))⟩, hzb⟩
  · rintro ⟨⟨hzx, hd⟩, hzb⟩
    exact ⟨hzb, fun hzS => (h.2 z hzb.le).1 hzS |>.elim hzx hd⟩

/-- **The punctured disk is star-shaped about `x`.** This is the form
`lem:polygonal-side-accessibility` cites: a straight segment from `x` towards any point of the
disk that misses `S` misses `S` all the way.

Together with connectedness of `openSegment ℝ x y ∪ {y}` it replaces the blueprint's "pick the
sector containing `y`, then a short segment from `x` into it". -/
theorem IsLocalRadius.openSegment_subset_ball_diff (h : IsLocalRadius S x r) (hy : y ∈ ball x r)
    (hyS : y ∉ S) : openSegment ℝ x y ⊆ ball x r \ S := by
  have hyx : y ≠ x := fun hxy => hyS ((h.2 y (by rw [hxy, dist_self]; exact h.pos.le)).2
    (Or.inl hxy))
  have hdy : Plane.dir (y - x) ∉ localDirs S x := fun hd =>
    hyS ((h.2 y (mem_ball.1 hy).le).2 (Or.inr hd))
  intro w hw
  rw [openSegment_eq_image'] at hw
  obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hw
  have hsub : x + θ • (y - x) - x = θ • (y - x) := by module
  have hne : y - x ≠ 0 := sub_ne_zero.2 hyx
  have hdist : dist (x + θ • (y - x)) x = θ * dist y x := by
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hθ0, dist_eq_norm]
  have hlt : dist (x + θ • (y - x)) x < r := by
    rw [hdist]
    calc θ * dist y x ≤ 1 * dist y x := by
          have : 0 ≤ dist y x := dist_nonneg
          nlinarith
      _ = dist y x := one_mul _
      _ < r := mem_ball.1 hy
  refine ⟨mem_ball.2 hlt, fun hmem => ?_⟩
  -- The point points in the same direction as `y`, which is not a local direction.
  have hdir : Plane.dir (x + θ • (y - x) - x) = Plane.dir (y - x) := by
    rw [hsub, dir_smul_pos hθ0]
  rcases (h.2 _ hlt.le).1 hmem with hzx | hd
  · -- The point is `x`, so `θ • (y - x) = 0`, impossible.
    have : θ • (y - x) = 0 := by
      have := sub_eq_zero.2 hzx
      rwa [hsub] at this
    rcases smul_eq_zero.1 this with h' | h'
    · exact absurd h' hθ0.ne'
    · exact hne h'
  · exact hdy (hdir ▸ hd)

/-- Some direction at `x` is free, so the punctured disk is nonempty. -/
theorem IsLocalRadius.exists_mem_ball_diff (h : IsLocalRadius S x r)
    (hfin : (localDirs S x).Finite) : ∃ y ∈ ball x r, y ∉ S := by
  obtain ⟨u, hu, hdet⟩ := Plane.exists_isDirection_det_ne_zero hfin
  have hhalf : 0 < r / 2 := half_pos h.pos
  have hnorm : dist (x + (r / 2) • u) x = r / 2 := by
    rw [dist_eq_norm, show x + (r / 2) • u - x = (r / 2) • u by module, norm_smul,
      Real.norm_eq_abs, abs_of_pos hhalf, hu.norm, mul_one]
  refine ⟨x + (r / 2) • u, mem_ball.2 (by rw [hnorm]; linarith [h.pos]), fun hmem => ?_⟩
  rcases (h.2 _ (by rw [hnorm]; linarith [h.pos])).1 hmem with hzx | hd
  · have hz : (r / 2) • u = 0 := by
      have := sub_eq_zero.2 hzx
      rwa [show x + (r / 2) • u - x = (r / 2) • u by module] at this
    rcases smul_eq_zero.1 hz with h' | h'
    · exact absurd h' hhalf.ne'
    · exact hu.ne_zero h'
  · rw [show x + (r / 2) • u - x = (r / 2) • u by module,
      dir_smul_of_isDirection hu hhalf] at hd
    exact hdet u hd hu.ne_zero (by rw [Plane.det_self])

end Schoenflies

/-! ### Finite polygonal plane graphs -/

namespace Graph

open Schoenflies

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} {x : Plane}

/-- **The point set of a finite plane graph with polygonal edges is its vertex set together
with finitely many straight segments.** The blueprint's "write every edge as a finite union of
straight segments". -/
theorem IsDrawing.exists_cover [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e)) :
    ∃ ps : List Piece, pointSet G drawing = V(G) ∪ cover ps := by
  classical
  -- One vertex list per edge, then all their segments concatenated.
  choose! vs hvs using hpoly
  refine ⟨(Graph.edgeFinset G).toList.flatMap fun e => segsOf (vs e), ?_⟩
  rw [pointSet]
  congr 1
  rw [cover_flatMap_list]
  ext z
  simp only [mem_iUnion, exists_prop, Finset.mem_toList, mem_edgeFinset]
  refine exists_congr fun e => and_congr_right fun he => ?_
  -- An edge arc carries two distinct points, so its chain has not collapsed.
  have h01 : drawing e 0 ≠ drawing e 1 := by
    intro hcontra
    have := (h.edge_param he).2.1 zero_mem_I one_mem_I hcontra
    norm_num at this
  have hm0 : drawing e 0 ∈ edgeArc drawing e := ⟨0, zero_mem_I, rfl⟩
  have hm1 : drawing e 1 ∈ edgeArc drawing e := ⟨1, one_mem_I, rfl⟩
  rw [hvs e he] at hm0 hm1
  rw [cover_segsOf_eq hm0 hm1 h01, ← hvs e he]

/-- A finite polygonal plane graph without isolated vertices is carried exactly by finitely
many nondegenerate straight segments.  The incidence hypothesis removes the isolated-vertex
term from `IsDrawing.exists_cover`: every vertex already belongs to the segment cover. -/
theorem IsDrawing.exists_segmentCover [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e))
    (hincident : ∀ z ∈ V(G), ∃ e, G.Inc e z) :
    ∃ ps : List Piece, (∀ P ∈ ps, P.Nondeg) ∧ cover ps = pointSet G drawing ∧
      ∀ P ∈ ps, ∃ e ∈ E(G), P.seg ⊆ edgeArc drawing e := by
  classical
  choose! vs hvs using hpoly
  let ps := (Graph.edgeFinset G).toList.flatMap fun e => segsOf (vs e)
  have hnd : ∀ P ∈ ps, P.Nondeg := by
    intro P hP
    obtain ⟨e, -, hPe⟩ := List.mem_flatMap.1 hP
    exact segsOf_nondeg _ P hPe
  have hcover : cover ps = ⋃ e ∈ E(G), edgeArc drawing e := by
    dsimp only [ps]
    rw [cover_flatMap_list]
    ext z
    simp only [mem_iUnion, exists_prop, Finset.mem_toList, mem_edgeFinset]
    refine exists_congr fun e => and_congr_right fun he => ?_
    have h01 : drawing e 0 ≠ drawing e 1 := by
      intro hcontra
      have := (h.edge_param he).2.1 zero_mem_I one_mem_I hcontra
      norm_num at this
    have hm0 : drawing e 0 ∈ edgeArc drawing e := ⟨0, zero_mem_I, rfl⟩
    have hm1 : drawing e 1 ∈ edgeArc drawing e := ⟨1, one_mem_I, rfl⟩
    rw [hvs e he] at hm0 hm1
    rw [cover_segsOf_eq hm0 hm1 h01, ← hvs e he]
  have hvertices : V(G) ⊆ ⋃ e ∈ E(G), edgeArc drawing e := by
    intro z hz
    obtain ⟨e, hinc⟩ := hincident z hz
    obtain ⟨w, hlink⟩ := hinc
    exact Set.mem_iUnion₂_of_mem hlink.edge_mem
      (h.edge_isArcBetween hlink).left_mem
  refine ⟨ps, hnd, ?_, ?_⟩
  · rw [hcover, pointSet]
    exact (Set.union_eq_right.mpr hvertices).symm
  · intro P hP
    obtain ⟨e, heList, hPe⟩ := List.mem_flatMap.1 hP
    have he : e ∈ E(G) := by
      rwa [Finset.mem_toList, mem_edgeFinset] at heList
    have h01 : drawing e 0 ≠ drawing e 1 := by
      intro hcontra
      have := (h.edge_param he).2.1 zero_mem_I one_mem_I hcontra
      norm_num at this
    have hm0 : drawing e 0 ∈ edgeArc drawing e := ⟨0, zero_mem_I, rfl⟩
    have hm1 : drawing e 1 ∈ edgeArc drawing e := ⟨1, one_mem_I, rfl⟩
    rw [hvs e he] at hm0 hm1
    refine ⟨e, he, fun z hz => ?_⟩
    rw [hvs e he, ← cover_segsOf_eq hm0 hm1 h01]
    exact Set.mem_iUnion₂_of_mem hPe hz

/-- **Local structure of a polygonal skeleton** (`lem:local-skeleton-structure`): a point of a
finite polygonal plane graph has a local radius, hence a disk in which the graph is exactly
finitely many radial segments. -/
theorem IsDrawing.exists_isLocalRadius [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e)) (hx : x ∈ pointSet G drawing) :
    ∃ r, IsLocalRadius (pointSet G drawing) x r := by
  obtain ⟨ps, hps⟩ := h.exists_cover hpoly
  exact Schoenflies.exists_isLocalRadius (Graph.finite_vertexSet G) hps hx

/-- The local branches of a finite polygonal plane graph at a point are finitely many. -/
theorem IsDrawing.finite_localDirs [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e)) (x : Plane) :
    (localDirs (pointSet G drawing) x).Finite := by
  obtain ⟨ps, hps⟩ := h.exists_cover hpoly
  exact Schoenflies.localDirs_finite (Graph.finite_vertexSet G) hps x

/-- **The access arc.** A point of the exterior inside a local disk about `x` is joined to `x`
by a straight segment lying, except for `x` itself, in that point's own face.

This is `lem:polygonal-side-accessibility` with everything but the choice of `y` discharged:
the consumer picks `y` in the face it cares about (possible because the face accumulates at
`x`), shrinks the radius with `IsLocalRadius.mono` until the disk also misses whatever else it
must avoid, and reads off a polygonal access arc. No sector has to be named: the half-open
segment does the work the blueprint's sector does. -/
theorem IsDrawing.openSegment_subset_face {r : ℝ} {y : Plane}
    (hr : IsLocalRadius (pointSet G drawing) x r) (hy : y ∈ ball x r)
    (hyE : y ∈ exterior G drawing) : openSegment ℝ x y ⊆ face G drawing y := by
  -- The half-open segment `(x, y]` is convex, hence connected, and misses the point set.
  have hyS : y ∉ pointSet G drawing := hyE
  have hTsub : AffineMap.lineMap x y '' Ioc (0 : ℝ) 1 ⊆ exterior G drawing := by
    rintro w ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩
    rcases eq_or_lt_of_le hθ1 with rfl | hlt
    · rwa [AffineMap.lineMap_apply_one]
    · have hmem : AffineMap.lineMap x y θ ∈ openSegment ℝ x y := by
        rw [openSegment_eq_image_lineMap]
        exact ⟨θ, ⟨hθ0, hlt⟩, rfl⟩
      exact (hr.openSegment_subset_ball_diff hy hyS hmem).2
  have hconn : IsPreconnected (AffineMap.lineMap x y '' Ioc (0 : ℝ) 1) :=
    ((convex_Ioc (0 : ℝ) 1).affine_image (AffineMap.lineMap x y)).isPreconnected
  have hyT : y ∈ AffineMap.lineMap x y '' Ioc (0 : ℝ) 1 :=
    ⟨1, ⟨zero_lt_one, le_refl 1⟩, AffineMap.lineMap_apply_one x y⟩
  refine subset_trans ?_ (hconn.subset_connectedComponentIn hyT hTsub)
  rw [openSegment_eq_image_lineMap]
  exact Set.image_mono Ioo_subset_Ioc_self

end Graph
