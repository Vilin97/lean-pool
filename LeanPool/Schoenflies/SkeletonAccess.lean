/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.SkeletonSectors
public import LeanPool.Schoenflies.AccessibleJoin
public import LeanPool.Schoenflies.Square

/-!
# The sector decomposition at every point, and polygonal-side accessibility

Two things are done here. First, the last clause of Lemma "Local structure of a polygonal
skeleton" (`lem:local-skeleton-structure`) is closed: `Schoenflies/SkeletonSectors.lean` proves
it only at a point with **at least two** local branches, and the blueprint states it for every
point. Second, its consumer, Lemma "Polygonal-side accessibility"
(`lem:polygonal-side-accessibility`), is proved.

## 1. The two degenerate points

`Schoenflies.IsLocalRadius.ball_diff_eq_iUnion_cone` writes the punctured local disk as the
union of the sectors `Plane.cone x (Plane.arcCCW d w) r` between *consecutive* local directions
`d, w`. With fewer than two local directions there is no consecutive pair, and the two missing
configurations are genuinely different sets:

* **one** local direction `d` — the disk slit along the radius in direction `d`, a sector of
  full turn (`Schoenflies.IsLocalRadius.ball_diff_eq_slit`);
* **no** local direction — the punctured disk, `x` being an isolated point of the skeleton
  (`Schoenflies.IsLocalRadius.ball_diff_eq_punctured`).

Both are connected (`Schoenflies.isConnected_ball_diff_radial`,
`Schoenflies.isConnected_ball_diff_singleton`), which is everything the decomposition claims
about a sector, so the blueprint's clause holds at every point with a single sector. Both proofs
cut the set into convex pieces cut out by the sign of `Plane.det` and glue them along explicit
overlaps: no angle, no arctangent, no cyclic order.

The sectors are then named, for every point at once, as what
`Schoenflies.IsLocalRadius.connectedComponentIn_eq_cone` already proves them to be — the
connected components of the punctured disk:

  `Schoenflies.localSectors S x r : Set (Set Plane)`

with `Schoenflies.localSectors_finite`, `Schoenflies.sUnion_localSectors`,
`Schoenflies.localSectors_pairwiseDisjoint`, `Schoenflies.isOpen_of_mem_localSectors` and
`Schoenflies.isConnected_of_mem_localSectors`. In the generic case the members are exactly the
cones (`Schoenflies.cone_mem_localSectors`); in the degenerate cases there is exactly one
member (`Schoenflies.localSectors_eq_of_subsingleton`). A set of sets rather than an indexed
family, because the natural index — a consecutive pair of local directions — does not exist at
the two degenerate points.

## 2. Polygonal-side accessibility

`Graph.exists_access_segment` is the theorem, and it exports the *construction*: a point `y` of
the 2-cell `F`, as close to `x` as prescribed, whose straight segment from `x` lies in `F` apart
from `x` itself. `Graph.polygonal_side_accessibility` packages it as
`Schoenflies.PolyAccessible F x`. The length bound is not in the blueprint statement; the
shrinking-star arguments downstream need it, and it is free.

The blueprint's proof is followed step by step. Shrink the disk at `x` below the distance to the
compact wild curve `C` (`lem:compact-separation`(c)), so that inside it the whole skeleton
`K = |G| ∪ C` is just `|G|`; the punctured disk is then the union of the sectors; the sector
containing `y` is connected and misses `K`, so it lies in a single 2-cell, and that cell is `F`
because the sector meets `F` at `y` (`Graph.localSector_subset_cell` — this is the clause the
audit found missing from `Graph.exists_access_sector`); the straight segment from `x` to `y`
lies in that sector
(`Schoenflies.IsLocalRadius.openSegment_subset_connectedComponentIn`).

The case `x ∉ |G|` — not excluded by the statement, since `x` need only lie on the boundary of
`F` — is the degenerate configuration of part 1: the disk misses the skeleton entirely, is
itself the only sector, and `x` turns out to lie in `F`.

The sector is taken throughout as the connected component of `y` in the punctured disk, so the
*number* of local branches at `x` never enters the accessibility proof. Part 1 is what makes
that component a sector in the blueprint's sense — at a point with one branch or none there is
no consecutive pair of local directions to name it by, and the component is the whole punctured
disk.

## The one hypothesis

`Schoenflies.CellsAbsorb K cells` is `lem:cellulation-invariants`(i), *a connected set disjoint
from the skeleton lies in a single open 2-cell*, in the "meets, hence contained" reading. It is
the only thing assumed; two dischargers are supplied
(`Schoenflies.cellsAbsorb_of_isComponent`, `Schoenflies.cellsAbsorb_of_isComponent_in`), the
second of which covers the target side, where the 2-cells only fill an ambient region `Q` whose
frontier belongs to the skeleton.

## The target side

`Graph.polygonal_side_accessibility_target` and `Graph.polygonal_side_accessibility_square`.
The blueprint keeps a sector from leaking out of the square by applying `thm:polygonal-jordan`
to the square boundary; that is not needed here. The corresponding step is
`Schoenflies.subset_of_isPreconnected_of_frontier_disjoint` — a connected set missing the
frontier of an open set and meeting it lies inside it — together with
`Schoenflies.frontier_openSquare_subset`. Both are elementary, so the target side rests on
nothing beyond the shared hypothesis.

## Blueprint

* `Schoenflies.isConnected_ball_diff_radial`, `Schoenflies.isConnected_ball_diff_singleton`,
  `Schoenflies.IsLocalRadius.ball_diff_eq_slit`,
  `Schoenflies.IsLocalRadius.ball_diff_eq_punctured`,
  `Schoenflies.IsLocalRadius.isConnected_ball_diff_of_subsingleton` — "consequently
  `B(x,r) \ |G|` is a finite union of open circular sectors" of `lem:local-skeleton-structure`,
  at the two points where `Schoenflies/SkeletonSectors.lean` leaves it open.
* `Schoenflies.localSectors` and its API, `Graph.IsDrawing.localSectors_finite`,
  `Graph.IsDrawing.isOpen_of_mem_localSectors` — the same clause for a finite
  plane graph with polygonal edges.
* `Schoenflies.localDirs_union_of_disjoint`, `Schoenflies.IsLocalRadius.union_of_disjoint`,
  `Graph.IsDrawing.exists_isLocalRadius_union` — "shrink the disk at `x` until it also misses
  the compact set `C`; the disk then meets the whole skeleton in the finitely many radial
  segments" of `lem:polygonal-side-accessibility`.
* `Schoenflies.CellsAbsorb`, `Schoenflies.cellsAbsorb_of_isComponent`,
  `Schoenflies.cellsAbsorb_of_isComponent_in` — `lem:cellulation-invariants`(i), assumed, and
  the two ways a cellulation discharges it.
* `Graph.localSector_subset_face`, `Graph.localSector_subset_cell`,
  `Schoenflies.IsLocalRadius.openSegment_subset_connectedComponentIn` — "each sector is
  connected and disjoint from the skeleton, so … lies in a single open 2-cell; and at least one
  sector lies in `F` … a short straight segment from `x` into that sector is a polygonal access
  arc" of `lem:polygonal-side-accessibility`.
* `Graph.exists_access_segment`, `Graph.polygonal_side_accessibility` —
  `lem:polygonal-side-accessibility`, source side.
* `Graph.polygonal_side_accessibility_target`, `Graph.polygonal_side_accessibility_square`,
  `Schoenflies.subset_of_isPreconnected_of_frontier_disjoint`,
  `Schoenflies.frontier_openSquare_subset` — "the analogous assertion holds at every boundary
  point of a target face" of the same lemma.
-/

public section

open Metric Set
open scoped Graph

namespace Schoenflies

variable {S F Q K N : Set Plane} {x y z d : Plane} {r ε : ℝ}

/-! ### Bilinearity conveniences -/

private theorem det_sub_right (a b c : Plane) :
    Plane.det a (b - c) = Plane.det a b - Plane.det a c := by
  rw [show b - c = b + (-1 : ℝ) • c by module, Plane.det_add_right, Plane.det_smul_right]; ring

private theorem det_neg_right (a b : Plane) : Plane.det a (-b) = -Plane.det a b := by
  rw [show (-b : Plane) = (-1 : ℝ) • b by module, Plane.det_smul_right]; ring

private theorem det_zero_right (a : Plane) : Plane.det a 0 = 0 := by
  rw [show (0 : Plane) = (0 : ℝ) • (0 : Plane) by module, Plane.det_smul_right, zero_mul]

/-! ### Two ways to miss a radius

A point of the disk fails to lie on the radius at `x` in direction `d` for one of two reasons:
it is off the line of `d` altogether, or it is on that line but on the far side. Both are sign
conditions on `Plane.det`, and both are used three times below. -/

/-- A point off the line of `d` through `x` is not on the radius at `x` in direction `d`. -/
theorem notMem_radial_of_det_ne_zero (hd : Plane.IsDirection d) (hr : 0 < r)
    (h : Plane.det d (z - x) ≠ 0) : z ∉ segment ℝ x (x + r • d) := by
  intro hseg
  rcases ((mem_radial_iff hd hr).1 hseg).2 with hzx | hdir
  · exact h (by rw [hzx, sub_self, det_zero_right])
  · have hne : z - x ≠ 0 := fun h0 => h (by rw [h0, det_zero_right])
    have hrep : ‖z - x‖ • d = z - x := by rw [← hdir]; exact smul_norm_dir hne
    exact h (by rw [← hrep, Plane.det_smul_right, Plane.det_self, mul_zero])

/-- A point on the *far* side of `x` along the line of `d` is not on the radius at `x` in
direction `d`. The hypothesis `0 < det (perp d) (z - x)` is `⟪d, z - x⟫ < 0` written without an
inner product (`Plane.det_perp_left`). -/
theorem notMem_radial_of_det_perp_pos (hd : Plane.IsDirection d) (hr : 0 < r)
    (h : 0 < Plane.det (Plane.perp d) (z - x)) : z ∉ segment ℝ x (x + r • d) := by
  have hpd : Plane.det (Plane.perp d) d = -1 := by
    rw [Plane.det_comm, Plane.det_perp_self, hd.norm, one_pow]
  intro hseg
  rcases ((mem_radial_iff hd hr).1 hseg).2 with hzx | hdir
  · rw [hzx, sub_self, det_zero_right] at h; exact lt_irrefl 0 h
  · have hne : z - x ≠ 0 := by
      intro h0
      rw [h0, det_zero_right] at h
      exact lt_irrefl 0 h
    have hrep : ‖z - x‖ • d = z - x := by rw [← hdir]; exact smul_norm_dir hne
    rw [← hrep, Plane.det_smul_right, hpd] at h
    nlinarith [norm_nonneg (z - x)]

/-! ### The disk minus one radius, and the punctured disk

`Schoenflies/SkeletonSectors.lean` decomposes the punctured local disk into the open sectors
between *consecutive* local directions, and that decomposition says nothing when there are fewer
than two directions to be consecutive. The two missing configurations are settled here: with one
local direction the punctured disk is the disk slit along a single radius, and with none it is
the punctured disk itself. Both are connected, which is everything the decomposition claims
about a sector, so the blueprint's clause holds at every point with the number of sectors equal
to one. -/

/-- A cone over a *convex* set of directions is connected as soon as it is nonempty: it is the
translate of an intersection of two convex sets. -/
theorem isConnected_cone_of_convex {A : Set Plane} (hA : Convex ℝ A)
    (hne : (Plane.cone x A r).Nonempty) : IsConnected (Plane.cone x A r) := by
  rw [Plane.cone_eq_image] at hne ⊢
  exact ⟨hne, ((hA.inter (convex_ball (0 : Plane) r)).isPreconnected).image _
    ((continuous_const.add continuous_id).continuousOn)⟩

/-- A witness inside a cone: a quarter of the radius along any vector of length at most `2`. -/
private theorem mem_cone_quarter {A : Set Plane} (hr : 0 < r) (v : Plane) (hv : ‖v‖ ≤ 2)
    (hvA : (r / 4) • v ∈ A) : x + (r / 4) • v ∈ Plane.cone x A r := by
  refine Plane.mem_cone_iff.2 ⟨?_, ?_⟩
  · rw [show x + (r / 4) • v - x = (r / 4) • v by module]; exact hvA
  · rw [dist_eq_norm, show x + (r / 4) • v - x = (r / 4) • v by module, norm_smul,
      Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < r / 4)]
    nlinarith [norm_nonneg v]

/-- **The disk slit along one radius is connected.** When `d` is the only local direction at
`x`, this single set is the "sector of full turn" that `lem:local-skeleton-structure` claims;
it is *not* of the form `arcCCW d w` for two local directions, which is why
`Schoenflies.IsLocalRadius.ball_diff_eq_iUnion_cone` has to assume two branches.

The proof cuts the slit disk into three convex half-disks — the two open sides of the line of
`d`, and the open half-disk pointing away from `d` — and glues them along their two overlaps.
No angle and no cyclic order enters. -/
theorem isConnected_ball_diff_radial (hd : Plane.IsDirection d) (hr : 0 < r) :
    IsConnected (ball x r \ segment ℝ x (x + r • d)) := by
  have hd0 : d ≠ 0 := hd.ne_zero
  have hdp : Plane.det d (Plane.perp d) = 1 := by rw [Plane.det_perp_self, hd.norm, one_pow]
  have hpd : Plane.det (Plane.perp d) d = -1 := by rw [Plane.det_comm, hdp]
  have hnd : ‖d‖ = 1 := hd.norm
  have hnp : ‖Plane.perp d‖ = 1 := by rw [Plane.norm_perp, hnd]
  -- The three convex half-disks.
  set A : Set Plane := Plane.cone x {u | 0 < Plane.det d u} r with hAdef
  set B : Set Plane := Plane.cone x {u | Plane.det d u < 0} r with hBdef
  set E : Set Plane := Plane.cone x {u | 0 < Plane.det (Plane.perp d) u} r with hEdef
  -- Witnesses in each piece and in each overlap.
  have hAne : x + (r / 4) • Plane.perp d ∈ A :=
    mem_cone_quarter hr _ (by rw [hnp]; norm_num)
      (by change 0 < Plane.det d _; rw [Plane.det_smul_right, hdp]; positivity)
  have hEne : x + (r / 4) • (-d) ∈ E :=
    mem_cone_quarter hr _ (by rw [norm_neg, hnd]; norm_num)
      (by
        change 0 < Plane.det (Plane.perp d) _
        rw [Plane.det_smul_right, det_neg_right, hpd]
        norm_num
        positivity)
  have hBne : x + (r / 4) • (-Plane.perp d) ∈ B :=
    mem_cone_quarter hr _ (by rw [norm_neg, hnp]; norm_num)
      (by
        change Plane.det d _ < 0
        rw [Plane.det_smul_right, det_neg_right, hdp]
        nlinarith)
  have hAE : x + (r / 4) • (Plane.perp d - d) ∈ A ∩ E := by
    have hvn : ‖Plane.perp d - d‖ ≤ 2 := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [hnp, hnd]; norm_num
    refine ⟨mem_cone_quarter hr _ hvn ?_, mem_cone_quarter hr _ hvn ?_⟩
    · change 0 < Plane.det d _
      rw [Plane.det_smul_right, det_sub_right, hdp, Plane.det_self]
      norm_num
      positivity
    · change 0 < Plane.det (Plane.perp d) _
      rw [Plane.det_smul_right, det_sub_right, Plane.det_self, hpd]
      norm_num
      positivity
  have hBE : x + (r / 4) • (-Plane.perp d - d) ∈ B ∩ E := by
    have hvn : ‖-Plane.perp d - d‖ ≤ 2 := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_neg, hnp, hnd]; norm_num
    refine ⟨mem_cone_quarter hr _ hvn ?_, mem_cone_quarter hr _ hvn ?_⟩
    · change Plane.det d _ < 0
      rw [Plane.det_smul_right, det_sub_right, det_neg_right, hdp, Plane.det_self]
      nlinarith
    · change 0 < Plane.det (Plane.perp d) _
      rw [Plane.det_smul_right, det_sub_right, det_neg_right, Plane.det_self, hpd]
      norm_num
      positivity
  -- The three pieces are exactly the slit disk.
  have hsplit : ball x r \ segment ℝ x (x + r • d) = (A ∪ E) ∪ (B ∪ E) := by
    ext w
    constructor
    · rintro ⟨hzb, hzs⟩
      have hdist : dist w x < r := mem_ball.1 hzb
      have hz : w ≠ x ∧ Plane.dir (w - x) ≠ d := by
        by_contra hcon
        push Not at hcon
        exact hzs ((mem_radial_iff hd hr).2 ⟨hdist.le,
          by rcases eq_or_ne w x with h | h; exacts [Or.inl h, Or.inr (hcon h)]⟩)
      rcases lt_trichotomy (Plane.det d (w - x)) 0 with hlt | heq | hgt
      · exact Or.inr (Or.inl (Plane.mem_cone_iff.2 ⟨hlt, hdist⟩))
      · -- On the line of `d`: the point must be on the far side, since it is not on the radius.
        obtain ⟨c, hc⟩ := (Plane.det_eq_zero_iff_smul d (w - x) hd0).1 heq
        have hcne : c ≠ 0 := by
          rintro rfl
          refine hz.1 (sub_eq_zero.1 ?_)
          rw [hc]; module
        have hcneg : c < 0 := by
          rcases lt_or_gt_of_ne hcne with h | h
          · exact h
          · exact absurd (by rw [hc, dir_smul_of_isDirection hd h]) hz.2
        refine Or.inl (Or.inr (Plane.mem_cone_iff.2 ⟨?_, hdist⟩))
        change 0 < Plane.det (Plane.perp d) (w - x)
        rw [hc, Plane.det_smul_right, hpd]
        nlinarith
      · exact Or.inl (Or.inl (Plane.mem_cone_iff.2 ⟨hgt, hdist⟩))
    · rintro ((hz | hz) | (hz | hz))
      · exact ⟨Plane.cone_subset_ball hz,
          notMem_radial_of_det_ne_zero hd hr (ne_of_gt (Plane.mem_cone_iff.1 hz).1)⟩
      · exact ⟨Plane.cone_subset_ball hz,
          notMem_radial_of_det_perp_pos hd hr (Plane.mem_cone_iff.1 hz).1⟩
      · exact ⟨Plane.cone_subset_ball hz,
          notMem_radial_of_det_ne_zero hd hr (ne_of_lt (Plane.mem_cone_iff.1 hz).1)⟩
      · exact ⟨Plane.cone_subset_ball hz,
          notMem_radial_of_det_perp_pos hd hr (Plane.mem_cone_iff.1 hz).1⟩
  rw [hsplit]
  have hAc : IsConnected A :=
    isConnected_cone_of_convex (Plane.convex_det_right_pos d) ⟨_, hAne⟩
  have hBc : IsConnected B :=
    isConnected_cone_of_convex (Plane.convex_det_right_neg d) ⟨_, hBne⟩
  have hEc : IsConnected E :=
    isConnected_cone_of_convex (Plane.convex_det_right_pos (Plane.perp d)) ⟨_, hEne⟩
  exact IsConnected.union ⟨_, Or.inr hEne, Or.inr hEne⟩
    (IsConnected.union ⟨_, hAE.1, hAE.2⟩ hAc hEc) (IsConnected.union ⟨_, hBE.1, hBE.2⟩ hBc hEc)

/-- The horizontal unit vector, used only to have *some* direction to slit along. -/
theorem isDirection_mk_one_zero : Plane.IsDirection (Plane.mk 1 0) := by
  rw [Plane.IsDirection, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two]

/-- **The punctured disk is connected.** Two disks slit along opposite radii cover it and
overlap off the line of the slit. This is the "sector" at a point of the skeleton with *no*
local direction — an isolated vertex. -/
theorem isConnected_ball_diff_singleton (hr : 0 < r) : IsConnected (ball x r \ {x}) := by
  set d : Plane := Plane.mk 1 0 with hddef
  have hd : Plane.IsDirection d := isDirection_mk_one_zero
  have hnd : Plane.IsDirection (-d) := by rw [Plane.IsDirection, norm_neg]; exact hd.norm
  have hne : d ≠ -d := by
    intro h
    refine hd.ne_zero ?_
    have h2 : (2 : ℝ) • d = 0 := by
      rw [two_smul]
      nth_rewrite 2 [h]
      module
    rcases smul_eq_zero.1 h2 with h' | h'
    · norm_num at h'
    · exact h'
  have hsplit : ball x r \ {x} =
      (ball x r \ segment ℝ x (x + r • d)) ∪ (ball x r \ segment ℝ x (x + r • (-d))) := by
    ext w
    constructor
    · rintro ⟨hzb, hzx⟩
      by_cases h : w ∈ segment ℝ x (x + r • d)
      · exact Or.inr ⟨hzb, fun h' => hzx (radial_inter_radial hd hnd hne hr ⟨h, h'⟩)⟩
      · exact Or.inl ⟨hzb, h⟩
    · have key : ∀ (e : Plane) (w : Plane), w ∉ segment ℝ x (x + r • e) → w ∉ ({x} : Set Plane) :=
        fun e w h hw => h (by rw [mem_singleton_iff] at hw; rw [hw]; exact left_mem_segment ℝ _ _)
      rintro (⟨hzb, h⟩ | ⟨hzb, h⟩)
      · exact ⟨hzb, key d w h⟩
      · exact ⟨hzb, key (-d) w h⟩
  rw [hsplit]
  refine IsConnected.union ?_ (isConnected_ball_diff_radial hd hr)
    (isConnected_ball_diff_radial hnd hr)
  -- Off the line of the slit the two slit disks agree; `perp d` points there.
  have hnp : ‖Plane.perp d‖ = 1 := by rw [Plane.norm_perp, hd.norm]
  have hdp : Plane.det d (Plane.perp d) = 1 := by rw [Plane.det_perp_self, hd.norm, one_pow]
  have hmem : x + (r / 2) • Plane.perp d ∈ ball x r := by
    rw [mem_ball, dist_eq_norm, show x + (r / 2) • Plane.perp d - x = (r / 2) • Plane.perp d by
      module, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < r / 2), hnp]
    linarith
  have hsub : x + (r / 2) • Plane.perp d - x = (r / 2) • Plane.perp d := by module
  have hdet : Plane.det d (x + (r / 2) • Plane.perp d - x) = r / 2 := by
    rw [hsub, Plane.det_smul_right, hdp, mul_one]
  refine ⟨x + (r / 2) • Plane.perp d, ⟨hmem, ?_⟩, hmem, ?_⟩
  · exact notMem_radial_of_det_ne_zero hd hr (by rw [hdet]; positivity)
  · refine notMem_radial_of_det_ne_zero hnd hr ?_
    rw [show Plane.det (-d) (x + (r / 2) • Plane.perp d - x)
        = -Plane.det d (x + (r / 2) • Plane.perp d - x) by
      rw [show (-d : Plane) = (-1 : ℝ) • d by module, Plane.det_smul_left]; ring, hdet]
    have : (0 : ℝ) < r / 2 := by positivity
    linarith

/-! ### The degenerate local disks

With `Schoenflies.isConnected_ball_diff_radial` and
`Schoenflies.isConnected_ball_diff_singleton` in hand, the two configurations that
`Schoenflies/SkeletonSectors.lean` had to exclude are read off the membership criterion. -/

/-- A local radius is a radius *at a point of the set*: take `z = x` in the criterion. -/
theorem IsLocalRadius.center_mem (h : IsLocalRadius S x r) : x ∈ S :=
  (h.2 x (by rw [dist_self]; exact h.pos.le)).2 (Or.inl rfl)

/-- **No local branch**: inside the disk the set is the single point `x`. -/
theorem IsLocalRadius.ball_diff_eq_punctured (h : IsLocalRadius S x r)
    (hzero : localDirs S x = ∅) : ball x r \ S = ball x r \ {x} := by
  ext z
  simp only [mem_sdiff, mem_ball, mem_singleton_iff]
  refine and_congr_right fun hz => not_congr ?_
  rw [h.2 z hz.le, hzero]
  simp

/-- **One local branch**: inside the disk the set is the single radius in that direction. -/
theorem IsLocalRadius.ball_diff_eq_slit (h : IsLocalRadius S x r)
    (hone : localDirs S x = {d}) : ball x r \ S = ball x r \ segment ℝ x (x + r • d) := by
  have hdmem : d ∈ localDirs S x := by rw [hone]; rfl
  have hd : Plane.IsDirection d := isDirection_of_mem_localDirs hdmem
  ext z
  simp only [mem_sdiff, mem_ball]
  refine and_congr_right fun hz => not_congr ?_
  rw [h.2 z hz.le, hone, mem_radial_iff hd h.pos]
  simp [hz.le]

/-- **The punctured local disk is connected when `x` has fewer than two branches.** This closes
the two configurations `Schoenflies.IsLocalRadius.ball_diff_eq_iUnion_cone` excludes: there is
one sector, and it is the whole punctured disk. -/
theorem IsLocalRadius.isConnected_ball_diff_of_subsingleton (h : IsLocalRadius S x r)
    (hsub : (localDirs S x).Subsingleton) : IsConnected (ball x r \ S) := by
  rcases hsub.eq_empty_or_singleton with hzero | ⟨e, hone⟩
  · rw [h.ball_diff_eq_punctured hzero]
    exact isConnected_ball_diff_singleton h.pos
  · rw [h.ball_diff_eq_slit hone]
    exact isConnected_ball_diff_radial
      (isDirection_of_mem_localDirs (show e ∈ localDirs S x by rw [hone]; rfl)) h.pos

/-- The punctured local disk is open. `IsLocalRadius` does not say that `S` is closed, and does
not have to: inside the disk, `S` is a point together with finitely many closed segments. -/
theorem IsLocalRadius.isOpen_ball_diff (h : IsLocalRadius S x r)
    (hfin : (localDirs S x).Finite) : IsOpen (ball x r \ S) := by
  have hclosed : IsClosed (closedBall x r ∩ S) := by
    rw [h.closedBall_inter h.center_mem, insert_eq]
    exact isClosed_singleton.union
      (hfin.isClosed_biUnion fun e _ => (isCompact_segment _ _).isClosed)
  have heq : ball x r \ S = ball x r ∩ (closedBall x r ∩ S)ᶜ := by
    ext z
    simp only [mem_sdiff, mem_inter_iff, mem_compl_iff, mem_ball, mem_closedBall, not_and]
    exact and_congr_right fun hz => ⟨fun hnS _ => hnS, fun hf hS => hf hz.le hS⟩
  rw [heq]
  exact isOpen_ball.inter hclosed.isOpen_compl

/-! ### Adding a set the disk misses

The blueprint's "shrink the disk at `x` until it also misses the compact set `C`; the disk then
meets the *whole* skeleton in the finitely many radial segments". Once the disk is clear of `C`,
neither the membership criterion nor the set of local directions can tell `S` from `S ∪ C`. -/

/-- A set the closed disk misses contributes no local direction. -/
theorem localDirs_union_of_disjoint {C : Set Plane} (hr : 0 < r)
    (hC : Disjoint (closedBall x r) C) : localDirs (S ∪ C) x = localDirs S x := by
  refine subset_antisymm ?_ (localDirs_mono subset_union_left)
  rintro e ⟨he, t, ht, hsub⟩
  refine ⟨he, min t r, lt_min ht hr, fun w hw => ?_⟩
  -- Shorten the germ to fit inside the disk; there it cannot meet `C`.
  rw [← radial_inter_closedBall he (lt_min ht hr) (min_le_left t r)] at hw
  rcases hsub hw.1 with hwS | hwC
  · exact hwS
  · exact absurd hwC (Set.disjoint_left.1 hC
      (Metric.closedBall_subset_closedBall (min_le_right t r) hw.2))

/-- **A local radius survives adjoining a set the closed disk misses.** This is the step that
turns a local radius for the polygonal part of a skeleton into one for the whole skeleton. -/
theorem IsLocalRadius.union_of_disjoint {C : Set Plane} (h : IsLocalRadius S x r)
    (hC : Disjoint (closedBall x r) C) : IsLocalRadius (S ∪ C) x r := by
  refine ⟨h.pos, fun w hw => ?_⟩
  rw [localDirs_union_of_disjoint h.pos hC]
  refine ⟨?_, fun hcase => Or.inl ((h.2 w hw).2 hcase)⟩
  rintro (hwS | hwC)
  · exact (h.2 w hw).1 hwS
  · exact absurd hwC (Set.disjoint_left.1 hC (mem_closedBall.2 hw))

/-! ### The sectors of a local disk, at every point

The blueprint's "`B(x,r) \ |G|` is a finite union of open circular sectors" is delivered here
without the two-branch hypothesis, by naming the sectors as what they are proved to be in
`Schoenflies.IsLocalRadius.connectedComponentIn_eq_cone`: the connected components of the
punctured disk. With at least two branches each component *is* one of the cones
(`Schoenflies.cone_mem_localSectors`); with fewer there is exactly one component, the whole
punctured disk (`Schoenflies.localSectors_eq_of_subsingleton`). -/

/-- **The sectors of the punctured local disk at `x`**: its connected components.

Defined as a set of sets rather than as an indexed family, because the two degenerate
configurations have no natural index — the index in the generic case is a consecutive pair of
local directions, and there is no such pair when there are fewer than two of them. -/
def localSectors (S : Set Plane) (x : Plane) (r : ℝ) : Set (Set Plane) :=
  (fun z => connectedComponentIn (ball x r \ S) z) '' (ball x r \ S)

theorem mem_localSectors (hz : z ∈ ball x r \ S) :
    connectedComponentIn (ball x r \ S) z ∈ localSectors S x r := ⟨z, hz, rfl⟩

theorem subset_ball_diff_of_mem_localSectors (hN : N ∈ localSectors S x r) :
    N ⊆ ball x r \ S := by
  obtain ⟨z, -, rfl⟩ := hN
  exact connectedComponentIn_subset _ _

/-- Each sector is connected — in particular nonempty. -/
theorem isConnected_of_mem_localSectors (hN : N ∈ localSectors S x r) : IsConnected N := by
  obtain ⟨z, hz, rfl⟩ := hN
  exact ⟨⟨z, mem_connectedComponentIn hz⟩, isPreconnected_connectedComponentIn⟩

/-- Each sector is open. -/
theorem isOpen_of_mem_localSectors (h : IsLocalRadius S x r) (hfin : (localDirs S x).Finite)
    (hN : N ∈ localSectors S x r) : IsOpen N := by
  obtain ⟨z, -, rfl⟩ := hN
  exact Plane.isOpen_connectedComponentIn (h.isOpen_ball_diff hfin)

/-- **The sectors cover the punctured disk.** No hypothesis: this is true of components. -/
theorem sUnion_localSectors : ⋃₀ localSectors S x r = ball x r \ S := by
  refine subset_antisymm ?_ fun w hw => ⟨_, mem_localSectors hw, mem_connectedComponentIn hw⟩
  rintro w ⟨N, hN, hw⟩
  exact subset_ball_diff_of_mem_localSectors hN hw

/-- **The sectors are pairwise disjoint**, so the cover is a partition. -/
theorem localSectors_pairwiseDisjoint : (localSectors S x r).PairwiseDisjoint id := by
  rintro _ ⟨z₁, -, rfl⟩ _ ⟨z₂, -, rfl⟩ hne
  simp only [Function.onFun, id]
  rw [Set.disjoint_left]
  intro w hw₁ hw₂
  exact hne ((connectedComponentIn_eq hw₁).trans (connectedComponentIn_eq hw₂).symm)

/-- **There are finitely many sectors.** With at least two branches each is a cone between a
consecutive pair of local directions, and there are finitely many such pairs; with fewer there
is exactly one sector. -/
theorem localSectors_finite (h : IsLocalRadius S x r) (hfin : (localDirs S x).Finite) :
    (localSectors S x r).Finite := by
  by_cases hsub : (localDirs S x).Subsingleton
  · refine Set.Finite.subset (Set.finite_singleton (ball x r \ S)) ?_
    rintro _ ⟨z, hz, rfl⟩
    exact mem_singleton_iff.2 (subset_antisymm (connectedComponentIn_subset _ _)
      ((h.isConnected_ball_diff_of_subsingleton hsub).isPreconnected.subset_connectedComponentIn
        hz (subset_refl _)))
  · obtain ⟨a, ha, b, hb, hab⟩ := Set.not_subsingleton_iff.1 hsub
    have h2 : ∃ a ∈ localDirs S x, ∃ b ∈ localDirs S x, a ≠ b := ⟨a, ha, b, hb, hab⟩
    refine Set.Finite.subset (Set.Finite.image
      (fun p : Plane × Plane => Plane.cone x (Plane.arcCCW p.1 p.2) r)
      (Plane.sectorPairs_finite hfin)) ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.1 ((h.ball_diff_eq_iUnion_cone hfin h2) ▸ hz)
    exact ⟨p, hp, (h.connectedComponentIn_eq_cone hfin h2 (Plane.mem_sectorPairs_iff.1 hp)
      hzp).symm⟩

/-- With at least two branches, every cone between consecutive local directions is a sector. -/
theorem cone_mem_localSectors (h : IsLocalRadius S x r) (hfin : (localDirs S x).Finite)
    (h2 : ∃ a ∈ localDirs S x, ∃ b ∈ localDirs S x, a ≠ b) {e w : Plane}
    (hp : Plane.IsSectorPair (localDirs S x) e w) :
    Plane.cone x (Plane.arcCCW e w) r ∈ localSectors S x r := by
  obtain ⟨z, hz⟩ := (h.isConnected_cone hp).nonempty
  exact ⟨z, h.cone_subset_ball_diff hp hz, h.connectedComponentIn_eq_cone hfin h2 hp hz⟩

/-- With fewer than two branches there is exactly one sector: the whole punctured disk. -/
theorem localSectors_eq_of_subsingleton (h : IsLocalRadius S x r)
    (hfin : (localDirs S x).Finite) (hsub : (localDirs S x).Subsingleton) :
    localSectors S x r = {ball x r \ S} := by
  obtain ⟨w, hwb, hwS⟩ := h.exists_mem_ball_diff hfin
  refine subset_antisymm ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact mem_singleton_iff.2 (subset_antisymm (connectedComponentIn_subset _ _)
      ((h.isConnected_ball_diff_of_subsingleton hsub).isPreconnected.subset_connectedComponentIn
        hz (subset_refl _)))
  · rintro _ rfl
    refine ⟨w, ⟨hwb, hwS⟩, subset_antisymm (connectedComponentIn_subset _ _) ?_⟩
    exact (h.isConnected_ball_diff_of_subsingleton hsub).isPreconnected.subset_connectedComponentIn
      ⟨hwb, hwS⟩ (subset_refl _)

/-- **The access sector, with no hypothesis on the number of branches.** The straight segment
from `x` to a point `y` of the punctured disk lies in `y`'s own sector, so the sector is reached
from `x` without leaving it.

The sector is named — it is `connectedComponentIn (ball x r \ S) y`, a member of
`Schoenflies.localSectors` by `Schoenflies.mem_localSectors` — rather than packaged in an `∃`,
so a consumer can speak about it before producing it. -/
theorem IsLocalRadius.openSegment_subset_connectedComponentIn (h : IsLocalRadius S x r)
    (hy : y ∈ ball x r) (hyS : y ∉ S) :
    openSegment ℝ x y ⊆ connectedComponentIn (ball x r \ S) y := by
  -- The half-open segment `(x, y]` is connected, contains `y`, and misses `S`.
  have hTsub : AffineMap.lineMap x y '' Ioc (0 : ℝ) 1 ⊆ ball x r \ S := by
    rintro w ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩
    rcases eq_or_lt_of_le hθ1 with rfl | hlt
    · rw [AffineMap.lineMap_apply_one]; exact ⟨hy, hyS⟩
    · exact h.openSegment_subset_ball_diff hy hyS
        (by rw [openSegment_eq_image_lineMap]; exact ⟨θ, ⟨hθ0, hlt⟩, rfl⟩)
  have hconn : IsPreconnected (AffineMap.lineMap x y '' Ioc (0 : ℝ) 1) :=
    ((convex_Ioc (0 : ℝ) 1).affine_image (AffineMap.lineMap x y)).isPreconnected
  have hyT : y ∈ AffineMap.lineMap x y '' Ioc (0 : ℝ) 1 :=
    ⟨1, ⟨zero_lt_one, le_refl 1⟩, AffineMap.lineMap_apply_one x y⟩
  refine subset_trans ?_ (hconn.subset_connectedComponentIn hyT hTsub)
  rw [openSegment_eq_image_lineMap]
  exact Set.image_mono Ioo_subset_Ioc_self

/-! ### `lem:cellulation-invariants`(i), as a hypothesis

The only thing assumed in this module. It is *not* a restatement of the goal: it speaks about
the cells of a cellulation, an object that has no Lean definition yet, and it is exactly the
invariant that another module is proving by induction over the two elementary operations. -/

/-- **`lem:cellulation-invariants`(i)** for a family `cells` of open 2-cells whose skeleton is
`K`: *a connected set disjoint from the skeleton lies in a single open 2-cell.*

Stated in the "meets, hence contained" reading, which is the form the proof of
`lem:polygonal-side-accessibility` uses and which packages the word *single* — with the usual
`∃`-reading one still has to know that distinct 2-cells are disjoint before concluding that the
cell found is the prescribed one. It is discharged by
`Schoenflies.cellsAbsorb_of_isComponent` (each 2-cell is a connected component of the
complement of the skeleton, which is what invariant (i) asserts) or, when the cells live inside
an ambient region whose frontier belongs to the skeleton, by
`Schoenflies.cellsAbsorb_of_isComponent_in`. -/
def CellsAbsorb (K : Set Plane) (cells : Set (Set Plane)) : Prop :=
  ∀ N : Set Plane, IsPreconnected N → Disjoint N K → ∀ R ∈ cells, (N ∩ R).Nonempty → N ⊆ R

/-- A connected set that misses the frontier of an open set and meets it lies inside it. -/
theorem subset_of_isPreconnected_of_frontier_disjoint (hQ : IsOpen Q) (hN : IsPreconnected N)
    (hfr : Disjoint N (frontier Q)) (hmeet : (N ∩ Q).Nonempty) : N ⊆ Q := by
  have hcover : N ⊆ Q ∪ (closure Q)ᶜ := by
    intro w hw
    by_cases hwQ : w ∈ Q
    · exact Or.inl hwQ
    · refine Or.inr fun hcl => Set.disjoint_left.1 hfr hw ?_
      rw [hQ.frontier_eq]
      exact ⟨hcl, hwQ⟩
  have hempty : ¬ (N ∩ (closure Q)ᶜ).Nonempty := by
    intro hne
    obtain ⟨w, -, hwQ, hwc⟩ :=
      hN Q (closure Q)ᶜ hQ isClosed_closure.isOpen_compl hcover hmeet hne
    exact hwc (subset_closure hwQ)
  intro w hw
  rcases hcover hw with hq | hc
  · exact hq
  · exact absurd ⟨w, hw, hc⟩ hempty

/-- **The discharger for `Schoenflies.CellsAbsorb`**: the 2-cells are the connected components
of the complement of the skeleton. That is the content of `lem:cellulation-invariants`(i). -/
theorem cellsAbsorb_of_isComponent {cells : Set (Set Plane)}
    (h : ∀ R ∈ cells, ∃ z, R = connectedComponentIn Kᶜ z) : CellsAbsorb K cells := by
  rintro N hN hdisj R hR ⟨w, hwN, hwR⟩
  obtain ⟨z, rfl⟩ := h R hR
  have hNK : N ⊆ Kᶜ := fun v hv => Set.disjoint_left.1 hdisj hv
  rw [connectedComponentIn_eq hwR]
  exact hN.subset_connectedComponentIn hwN hNK

/-- **The discharger on the target side**: the 2-cells are the connected components of what is
left of an ambient open region `Q` after the skeleton is removed, and the frontier of `Q`
belongs to the skeleton. The second clause is what stops a sector from leaking out of `Q`; in
the blueprint it is `thm:polygonal-jordan` applied to the square boundary, and here it is
`Schoenflies.subset_of_isPreconnected_of_frontier_disjoint`. -/
theorem cellsAbsorb_of_isComponent_in (hQ : IsOpen Q) (hQK : frontier Q ⊆ K)
    {cells : Set (Set Plane)}
    (h : ∀ R ∈ cells, R ⊆ Q ∧ ∃ z, R = connectedComponentIn (Q \ K) z) : CellsAbsorb K cells := by
  rintro N hN hdisj R hR ⟨w, hwN, hwR⟩
  obtain ⟨hRQ, z, rfl⟩ := h R hR
  have hNQ : N ⊆ Q := subset_of_isPreconnected_of_frontier_disjoint hQ hN
    (hdisj.mono_right hQK) ⟨w, hwN, hRQ hwR⟩
  rw [connectedComponentIn_eq hwR]
  exact hN.subset_connectedComponentIn hwN
    fun v hv => ⟨hNQ hv, Set.disjoint_left.1 hdisj hv⟩

/-- The frontier of an open axis-parallel square lies in the square's boundary. This is how the
hypothesis "the boundary of `Q` is part of the skeleton" is checked on the target side. -/
theorem frontier_openSquare_subset (c : Plane) (s : ℝ) :
    frontier (Plane.openSquare c s) ⊆ Plane.closedSquare c s \ Plane.openSquare c s := by
  have hsub : Plane.openSquare c s ⊆ Plane.closedSquare c s := by
    intro w hw
    simp only [Plane.openSquare, Set.mem_ofPred_eq] at hw
    simp only [Plane.closedSquare, Set.mem_ofPred_eq]
    exact hw.le
  rw [(Plane.isOpen_openSquare c s).frontier_eq]
  exact Set.sdiff_subset_sdiff_left
    ((Plane.isClosed_closedSquare c s).closure_subset_iff.2 hsub)

end Schoenflies

/-! ## `lem:polygonal-side-accessibility` -/

namespace Graph

open Schoenflies

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
variable {C F K Q : Set Plane} {cells : Set (Set Plane)} {x y : Plane} {r ε : ℝ}

/-! ### The sector decomposition for a finite polygonal plane graph

`lem:local-skeleton-structure`'s last clause, "consequently `B(x,r) \ |G|` is a finite union of
open circular sectors", now holds at *every* point of `|G|`: at a point with at least two local
branches the sectors are the cones of `Schoenflies.IsLocalRadius.ball_diff_eq_iUnion_cone`, and
at the two degenerate points there is a single one. -/

/-- **The disk meets the whole skeleton in the finitely many radial segments.** The blueprint's
first step in `lem:polygonal-side-accessibility`: at a point of the polygonal graph off the
compact wild set `C`, a small enough disk is a local disk for `|G| ∪ C`, not merely for `|G|`.

Not used below — the accessibility proof works with `|G|` inside the disk and disposes of `C`
by disjointness — but it is the blueprint sentence, and a consumer wanting the sectors of the
*whole* skeleton wants this. -/
theorem IsDrawing.exists_isLocalRadius_union [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e)) (hC : IsCompact C)
    (hx : x ∈ pointSet G drawing) (hxC : x ∉ C) :
    ∃ r, IsLocalRadius (pointSet G drawing ∪ C) x r := by
  obtain ⟨r₀, hr₀⟩ := h.exists_isLocalRadius hpoly hx
  obtain ⟨ρ, hρ, hballC⟩ :=
    Schoenflies.Plane.exists_ball_subset_diff isOpen_univ hC ⟨mem_univ x, hxC⟩
  refine ⟨min r₀ (ρ / 2),
    (hr₀.mono (lt_min hr₀.pos (by linarith)) (min_le_left _ _)).union_of_disjoint ?_⟩
  refine Set.disjoint_left.2 fun w hw => ?_
  refine (hballC (mem_ball.2 ?_)).2
  have h1 := mem_closedBall.1 hw
  have h2 : min r₀ (ρ / 2) ≤ ρ / 2 := min_le_right _ _
  linarith

/-- **There are finitely many sectors at every point of `|G|`.** -/
theorem IsDrawing.localSectors_finite [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e))
    (hr : IsLocalRadius (pointSet G drawing) x r) :
    (localSectors (pointSet G drawing) x r).Finite :=
  Schoenflies.localSectors_finite hr (h.finite_localDirs hpoly x)

/-- **Every sector at a point of `|G|` is open.** -/
theorem IsDrawing.isOpen_of_mem_localSectors [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e))
    (hr : IsLocalRadius (pointSet G drawing) x r) {N : Set Plane}
    (hN : N ∈ localSectors (pointSet G drawing) x r) : IsOpen N :=
  Schoenflies.isOpen_of_mem_localSectors hr (h.finite_localDirs hpoly x) hN

/-- **Each sector lies in a single face**, namely the face of any of its points. This is the
clause `Graph.exists_access_sector` proves under the two-branch hypothesis, here with none — and
in fact with no hypothesis on the radius either, since a component of the punctured disk is a
connected subset of the exterior whatever the radius. -/
theorem localSector_subset_face (hy : y ∈ ball x r) (hyE : y ∈ exterior G drawing) :
    connectedComponentIn (ball x r \ pointSet G drawing) y ⊆ face G drawing y :=
  isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn ⟨hy, hyE⟩)
    fun _ hw => (connectedComponentIn_subset _ _ hw).2

/-- **At least one sector lies in `F`.** The clause of `lem:polygonal-side-accessibility` that
`Graph.exists_access_sector` was credited with and does not prove: the sector containing a point
`y` of the 2-cell `F` lies wholly inside `F`.

The reasoning is the blueprint's, once the disk has been shrunk below the distance to the wild
set `C`: the sector is connected and misses the whole skeleton `K = |G| ∪ C`, so by
`lem:cellulation-invariants`(i) it lies in a single 2-cell, and that cell is `F` because the
sector meets `F` at `y`. -/
theorem localSector_subset_cell (hK : K = pointSet G drawing ∪ C)
    (hcells : CellsAbsorb K cells) (hF : F ∈ cells)
    (hballC : Disjoint (ball x r) C) (hy : y ∈ ball x r) (hyF : y ∈ F)
    (hyS : y ∉ pointSet G drawing) :
    connectedComponentIn (ball x r \ pointSet G drawing) y ⊆ F := by
  refine hcells _ isPreconnected_connectedComponentIn ?_ F hF
    ⟨y, mem_connectedComponentIn ⟨hy, hyS⟩, hyF⟩
  rw [Set.disjoint_left]
  intro w hw hwK
  have hwd := connectedComponentIn_subset _ _ hw
  rcases hK ▸ hwK with hwP | hwC
  · exact hwd.2 hwP
  · exact Set.disjoint_left.1 hballC hwd.1 hwC

/-- **The access segment of `lem:polygonal-side-accessibility`, with a prescribed length
bound.** Let `G` be a finite plane graph with polygonal edges, `C` a compact set — the wild
outer curve — and `K = |G| ∪ C` the whole skeleton. Let `F` be an open 2-cell, and `x` a point
at which `F` accumulates, lying off `C`. Then arbitrarily near `x` there is a point `y` of `F`
whose straight segment from `x` lies, apart from `x` itself, inside `F`.

The straight segment is exported rather than the accessibility predicate, because the later
shrinking-star arguments need the access arc to be short; `PolyAccessible` follows in
`Graph.polygonal_side_accessibility`.

The proof is the blueprint's. Shrink the disk at `x` below the distance to `C`, so that inside
it the whole skeleton is `|G|`; then the punctured disk is the union of the sectors of
`Schoenflies.localSectors`, each of them connected and disjoint from the skeleton, and the one
containing `y` lies in a single 2-cell by the assumed `lem:cellulation-invariants`(i). That cell
is `F`, because the sector meets `F` at `y`. When `x` is not on `|G|` at all — which the
statement does not exclude, since `x` need only be a limit of points of `F` — the disk misses
the skeleton entirely and is itself the access region.

The sector is named as the connected component of `y` in the punctured disk, so no hypothesis
on the number of local branches at `x` is needed anywhere. -/
theorem exists_access_segment [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e))
    (hC : IsCompact C) (hK : K = pointSet G drawing ∪ C)
    (hcells : CellsAbsorb K cells) (hF : F ∈ cells) (hFK : Disjoint F K)
    (hx : x ∈ closure F) (hxC : x ∉ C) (hε : 0 < ε) :
    ∃ y, y ∈ F ∧ y ≠ x ∧ dist y x < ε ∧ openSegment ℝ x y ⊆ F := by
  -- A disk about `x` missing the wild curve (`lem:compact-separation`(c)).
  obtain ⟨ρ, hρ, hballC⟩ :=
    Schoenflies.Plane.exists_ball_subset_diff isOpen_univ hC ⟨mem_univ x, hxC⟩
  by_cases hxP : x ∈ pointSet G drawing
  · -- `x` is on the polygonal skeleton: shrink to a local radius as well.
    obtain ⟨r₀, hr₀⟩ := h.exists_isLocalRadius hpoly hxP
    have hrpos : 0 < min (min r₀ ρ) ε := lt_min (lt_min hr₀.pos hρ) hε
    have hr : IsLocalRadius (pointSet G drawing) x (min (min r₀ ρ) ε) :=
      hr₀.mono hrpos ((min_le_left _ _).trans (min_le_left _ _))
    -- `x` lies on the skeleton, so it is not in the 2-cell.
    have hxF : x ∉ F := fun hmem =>
      Set.disjoint_left.1 hFK hmem (by rw [hK]; exact Or.inl hxP)
    obtain ⟨y, hyF, hdist⟩ := Metric.mem_closure_iff.1 hx _ hrpos
    have hyx : y ≠ x := fun hh => hxF (hh ▸ hyF)
    have hyball : y ∈ ball x (min (min r₀ ρ) ε) := by rw [mem_ball, dist_comm]; exact hdist
    have hyS : y ∉ pointSet G drawing := fun hmem =>
      Set.disjoint_left.1 hFK hyF (by rw [hK]; exact Or.inl hmem)
    -- The sector of `y`: its component in the punctured disk.
    have hdisjC : Disjoint (ball x (min (min r₀ ρ) ε)) C :=
      Set.disjoint_left.2 fun w hw =>
        (hballC (Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hw)).2
    have hNF : connectedComponentIn (ball x (min (min r₀ ρ) ε) \ pointSet G drawing) y ⊆ F :=
      localSector_subset_cell hK hcells hF hdisjC hyball hyF hyS
    exact ⟨y, hyF, hyx,
      lt_of_lt_of_le (by rw [dist_comm]; exact hdist) (min_le_right _ _),
      (hr.openSegment_subset_connectedComponentIn hyball hyS).trans hNF⟩
  · -- `x` is off the polygonal skeleton: a whole disk about it misses the skeleton.
    obtain ⟨ρ', hρ', hballP⟩ := Schoenflies.Plane.exists_ball_subset_diff isOpen_univ
      h.isCompact_pointSet ⟨mem_univ x, hxP⟩
    have hrpos : 0 < min (min ρ ρ') ε := lt_min (lt_min hρ hρ') hε
    have hbK : Disjoint (ball x (min (min ρ ρ') ε)) K := by
      rw [Set.disjoint_left]
      intro w hw hwK
      rcases hK ▸ hwK with hwP | hwC
      · exact (hballP (Metric.ball_subset_ball
          ((min_le_left _ _).trans (min_le_right _ _)) hw)).2 hwP
      · exact (hballC (Metric.ball_subset_ball
          ((min_le_left _ _).trans (min_le_left _ _)) hw)).2 hwC
    obtain ⟨w, hwF, hwdist⟩ := Metric.mem_closure_iff.1 hx _ hrpos
    have hsub : ball x (min (min ρ ρ') ε) ⊆ F :=
      hcells _ (convex_ball x _).isPreconnected hbK F hF
        ⟨w, by rw [mem_ball, dist_comm]; exact hwdist, hwF⟩
    -- Any short segment out of `x` will do.
    set d : Plane := Plane.mk 1 0 with hddef
    have hd : Plane.IsDirection d := isDirection_mk_one_zero
    have hsm : x + (min (min ρ ρ') ε / 2) • d - x = (min (min ρ ρ') ε / 2) • d := by module
    have hdd : dist (x + (min (min ρ ρ') ε / 2) • d) x = min (min ρ ρ') ε / 2 := by
      rw [dist_eq_norm, hsm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < min (min ρ ρ') ε / 2), hd.norm, mul_one]
    have hyball : x + (min (min ρ ρ') ε / 2) • d ∈ ball x (min (min ρ ρ') ε) := by
      rw [mem_ball, hdd]; linarith
    have hshort : dist (x + (min (min ρ ρ') ε / 2) • d) x < ε := by
      have h1 : min (min ρ ρ') ε ≤ ε := min_le_right _ _
      rw [hdd]; linarith
    refine ⟨x + (min (min ρ ρ') ε / 2) • d, hsub hyball, ?_, hshort, ?_⟩
    · intro hh
      have h0 : (min (min ρ ρ') ε / 2) • d = 0 := by rw [← hsm, hh, sub_self]
      rcases smul_eq_zero.1 h0 with h' | h'
      · exact absurd h' (by positivity)
      · exact hd.ne_zero h'
    · exact ((openSegment_subset_segment ℝ _ _).trans
        ((convex_ball x _).segment_subset (mem_ball_self hrpos) hyball)).trans hsub

/-- **`lem:polygonal-side-accessibility`, source side.** A boundary point of a 2-cell `F` of a
finite cellulation, lying off the wild outer curve `C`, is polygonally accessible from `F`.

`x ∈ closure F` is assumed rather than `x ∈ frontier F`: the proof never uses `x ∉ F`, and the
weaker hypothesis is what a consumer holding a limit of points of `F` actually has. -/
theorem polygonal_side_accessibility [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e))
    (hC : IsCompact C) (hK : K = pointSet G drawing ∪ C)
    (hcells : CellsAbsorb K cells) (hF : F ∈ cells) (hFK : Disjoint F K)
    (hx : x ∈ closure F) (hxC : x ∉ C) :
    PolyAccessible F x := by
  obtain ⟨y, hyF, -, -, hseg⟩ :=
    exists_access_segment h hpoly hC hK hcells hF hFK hx hxC one_pos
  exact PolyAccessible.of_openSegment hyF hseg

/-- **`lem:polygonal-side-accessibility`, target side.** On the target every edge is polygonal,
including every outer edge, so there is no wild set to avoid; but the 2-cells only fill an
ambient region `Q` whose frontier belongs to the skeleton, and a sector at a boundary point of
`Q` may lie outside `Q` and belong to no cell. That is exactly what
`Schoenflies.cellsAbsorb_of_isComponent_in` handles. -/
theorem polygonal_side_accessibility_target [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e))
    (hQ : IsOpen Q) (hQK : frontier Q ⊆ pointSet G drawing)
    (hcell : ∀ R ∈ cells, R ⊆ Q ∧
      ∃ z, R = connectedComponentIn (Q \ pointSet G drawing) z)
    (hF : F ∈ cells) (hx : x ∈ closure F) :
    PolyAccessible F x := by
  have hFK : Disjoint F (pointSet G drawing) := by
    obtain ⟨-, z, hz⟩ := hcell F hF
    exact Set.disjoint_left.2 fun w hw => (connectedComponentIn_subset _ _ (hz ▸ hw)).2
  exact polygonal_side_accessibility h hpoly isCompact_empty (union_empty _).symm
    (cellsAbsorb_of_isComponent_in hQ hQK hcell) hF hFK hx (notMem_empty x)

/-- `Graph.polygonal_side_accessibility_target` with the ambient region the open square. The
blueprint gets "a sector meeting `F` lies in `Q°`" from `thm:polygonal-jordan` applied to the
square boundary; here it comes from `Schoenflies.frontier_openSquare_subset` and the clopen
argument in `Schoenflies.subset_of_isPreconnected_of_frontier_disjoint`, so the polygonal Jordan
theorem is not needed. -/
theorem polygonal_side_accessibility_square [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e)) (c : Plane) (s : ℝ)
    (hS : Plane.closedSquare c s \ Plane.openSquare c s ⊆ pointSet G drawing)
    (hcell : ∀ R ∈ cells, R ⊆ Plane.openSquare c s ∧
      ∃ z, R = connectedComponentIn (Plane.openSquare c s \ pointSet G drawing) z)
    (hF : F ∈ cells) (hx : x ∈ closure F) :
    PolyAccessible F x :=
  polygonal_side_accessibility_target h hpoly (Plane.isOpen_openSquare c s)
    ((frontier_openSquare_subset c s).trans hS) hcell hF hx

end Graph
