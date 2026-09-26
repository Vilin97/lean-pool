/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.FaceCycles
public import LeanPool.Schoenflies.Realization

/-!
# Face cycles: the proof

`lem:face-cycles` — *every face of a finite 2-connected polygonal plane graph has a cycle as its
boundary and is one of the two complementary regions of that cycle*. `Schoenflies/FaceCycles.lean`
built the base cycle, its 2-connectivity, and the topology of adding an ear; this module runs
the induction of the blueprint's proof on top of them.

## READ THIS FIRST: what is assumed

`Graph.face_cycles` **carries a hypothesis, `Schoenflies.CrosscutSplitsRegion`, which nothing
proves.** It is the exhaustion clause of `thm:polygonal-crosscut` — "the crosscut replaces `F`
by exactly two regions" — stated for a crosscut whose two endpoints are *arbitrary points of
the curve*. Everything else in the blueprint's proof is discharged here without hypotheses, and
each of those pieces is a standalone theorem below.

`main`'s Theorem 2.8 does **not** discharge it, and the obstruction is not a missing bridge.
`Schoenflies.IsPolygonalCrosscut` states its two splitting hypotheses against
`ClosedPolygon.arcPieces C a k`, which cuts the polygon's edge list at two of *its vertices*;
and `Schoenflies.ClosedPolygon.isCornerAt_vertex` says every vertex of every realization of a
curve is a corner of it. In the induction below the two cut points are the ear's endpoints —
graph vertices at which the two cycle edges may leave along opposite rays, so that the boundary
curve runs *straight* through the cut point. Such a point is a vertex of no `ClosedPolygon`
with that carrier, and `Schoenflies.exists_closedPolygon_split` (whose `IsCornerAt` hypotheses
are therefore not an artefact) cannot be applied.

There is a **second, independent** reason, and it bites even when both cut points *are*
corners. `IsPolygonalCrosscut.edges₁` asks for `SameEdges J₁.pieces (C.arcPieces a k ++ K)`,
a multiset equality of unoriented segments. The list on the right has two pieces ending at the
cut point `q` — the arc's last and the crosscut's first. If those two are collinear, the curve
`J₁ = A₁ ∪ P` runs straight through `q`, so `q` is a vertex of no `ClosedPolygon` with that
carrier and *no* piece of `J₁.pieces` ends there: the multiset equality is unsatisfiable. Since
the crosscut may perfectly well leave a cut vertex along the ray opposite the arriving arc edge,
`edges₁` and `edges₂` are not dischargeable as stated. Deleting the redundant vertex —
`Schoenflies.PrePolygon.deleteLast` — repairs the *realization* and breaks `SameEdges` in the
same move.

Closing the gap therefore means restating Theorem 2.8 with the edge lists related by *parity*
rather than by `SameEdges`, for a split made at arbitrary points of the curve. The tools exist:
`Schoenflies.parity_split` is already stated for arbitrary lists, and
`Schoenflies.parity_subdivide` (Lemma 2.1) absorbs the difference between a merged piece and its
two halves. What is missing is the parity theory of presentations carrying redundant vertices —
`Schoenflies.parity_eq_one_iff` for `Schoenflies.PrePolygon` rather than only for
`ClosedPolygon`, obtained by carrying the parity along the normalization induction of
`Schoenflies.PrePolygon.exists_closedPolygon_of_prePolygon`. That is a separate module.

## Main results

* **The realisation of a cycle is a separating curve** (`Graph.IsDrawing.cycle_isSeparating`),
  which is what the base case needed and what `main` could not say. It composes
  `Graph.IsDrawing.cycle_isJordanCurve` with `Schoenflies.exists_closedPolygon` and
  `Schoenflies.ClosedPolygon.isSeparating_carrier`. The polygonality half needed a bridge that
  `main` did not have: `Schoenflies.IsPolygonal` is the carrier of *one* vertex list, so a union
  of edge arcs is polygonal only once each arc is known to be a polyline running from one of its
  ends to the other (`Schoenflies.IsArcBetween.exists_poly_eq`, which rests on the arc
  uniqueness `Schoenflies.IsArcBetween.eq_of_subset`).
* **The base case** (`Graph.IsDrawing.hasFaceCycles_cycleGraph`): the cycle subgraph occupies
  exactly the cycle's realisation, so its faces are the two regions of that curve.
* **Cutting a cycle at two of its vertices** (`Graph.IsCycleThrough.split_at`) and **splicing an
  ear onto an arc** (`Graph.exists_spliced_cycle`) — the combinatorics of "both bounded by
  cycles" — together with the geometric reading of the split
  (`Graph.IsDrawing.arcs_of_split`).
* **The step's topology**: the enlarged exterior is the old one minus the ear
  (`Graph.IsDrawing.pointSet_pathGraphOf`), a face the ear misses survives with its cycle
  (`Graph.IsFaceCycle.mono`), and the face the ear cuts is cut only inside itself
  (`Schoenflies.connectedComponentIn_diff`).

## For the integrator

`Graph.IsPath.append`, `Graph.IsPath.split_meet`, `Graph.IsWalk.walkVertices_eq_covered`,
`Graph.IsWalk.walkVertices_reverse_eq`, `Graph.coveredVertices_congr_of_le`,
`Graph.walkVertices_congr_of_le` and `Graph.edgesCover_append` / `…_perm` / `…_reverse` are
general and belong in `Schoenflies/Graph/Walk.lean` and `Schoenflies/Graph/CycleJordan.lean`.
`Schoenflies.IsArcBetween.eq_of_subset` belongs in `Schoenflies/Subarc.lean` and
`Schoenflies.poly_append_join` in `Schoenflies/PolyPath.lean`.

## Blueprint

* `Schoenflies.IsArcBetween.eq_of_subset`, `Schoenflies.IsArcBetween.exists_poly_eq`,
  `Graph.IsDrawing.exists_poly_eq_edgesCover`, `Graph.IsDrawing.isPolygonal_edgesCover` — §1,
  the polygonality of what a walk draws.
* `Graph.IsDrawing.cycle_isSeparating` — `thm:polygonal-jordan` for the realisation of a cycle:
  "This is true for the initial cycle by Theorem `thm:polygonal-jordan`."
* `Graph.IsFaceCycle`, `Graph.HasFaceCycles` — the conclusion of `lem:face-cycles`, at one face
  and at all of them.
* `Graph.IsDrawing.hasFaceCycles_cycleGraph` — the base case.
* `Graph.IsCycleThrough.split_at`, `Graph.IsDrawing.arcs_of_split`,
  `Graph.exists_spliced_cycle` — "Theorem `thm:polygonal-crosscut` replaces `F` by exactly two
  regions, both bounded by cycles", combinatorially.
* `Schoenflies.CrosscutSplitsRegion` — **the assumed** exhaustion clause of
  `thm:polygonal-crosscut` at arbitrary cut points.
* `Graph.IsDrawing.hasFaceCycles_union` — one ear.
* `Graph.face_cycles` — `lem:face-cycles`, modulo `Schoenflies.CrosscutSplitsRegion`.
-/

public section

open Metric Set unitInterval
open scoped Graph

namespace Schoenflies

/-! ## An arc inside an arc with the same ends is the whole of it -/

/-- **An arc between two points contained in an arc between the same two points is all of
it.** Removing an interior point of the ambient arc splits it into two relatively open halves;
a connected subset containing both ends would have to meet both and therefore their empty
intersection. -/
theorem IsArcBetween.eq_of_subset {A B : Set Plane} {p q : Plane}
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q) (hBA : B ⊆ A) : B = A := by
  obtain ⟨f, hc, hi, hAim, hf0, hf1⟩ := hA
  refine Set.Subset.antisymm hBA fun x hx => ?_
  by_contra hxB
  obtain ⟨t, ht, rfl⟩ : ∃ t ∈ I, f t = x := by rw [← hAim] at hx; exact hx
  -- The parameter is strictly inside, since both ends belong to `B`.
  have ht0 : (0 : ℝ) < t := by
    rcases eq_or_lt_of_le ht.1 with rfl | h
    · exact absurd (hf0 ▸ hB.left_mem) hxB
    · exact h
  have ht1 : t < 1 := by
    rcases eq_or_lt_of_le ht.2 with rfl | h
    · exact absurd (hf1 ▸ hB.right_mem) hxB
    · exact h
  obtain ⟨V₁, hV₁open, hV₁⟩ := image_isRelOpen hc hi (U := Iio t) isOpen_Iio
  obtain ⟨V₂, hV₂open, hV₂⟩ := image_isRelOpen hc hi (U := Ioi t) isOpen_Ioi
  rw [hAim] at hV₁ hV₂
  -- The two halves are disjoint, by injectivity of the parametrisation.
  have hdisj : (A ∩ (V₁ ∩ V₂)) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun z ⟨hzA, hz₁, hz₂⟩ => ?_
    obtain ⟨s, hs, rfl⟩ : z ∈ f '' (Iio t ∩ I) := by rw [hV₁]; exact ⟨hz₁, hzA⟩
    obtain ⟨r, hr, hrs⟩ : f s ∈ f '' (Ioi t ∩ I) := by rw [hV₂]; exact ⟨hz₂, hzA⟩
    have hrs' : r = s := hi hr.2 hs.2 hrs
    have h1 : t < r := hr.1
    have h2 : s < t := hs.1
    rw [hrs'] at h1
    linarith
  -- `B` misses the removed point, so it lies in the union of the two halves.
  have hsub : B ⊆ V₁ ∪ V₂ := by
    intro z hz
    obtain ⟨s, hs, rfl⟩ : ∃ s ∈ I, f s = z := by
      have := hBA hz; rw [← hAim] at this; exact this
    have hst : s ≠ t := by rintro rfl; exact hxB hz
    rcases lt_or_gt_of_ne hst with h | h
    · exact Or.inl (by
        have : f s ∈ V₁ ∩ A := by rw [← hV₁]; exact ⟨s, ⟨h, hs⟩, rfl⟩
        exact this.1)
    · exact Or.inr (by
        have : f s ∈ V₂ ∩ A := by rw [← hV₂]; exact ⟨s, ⟨h, hs⟩, rfl⟩
        exact this.1)
  have hp₁ : (B ∩ V₁).Nonempty := by
    refine ⟨p, hB.left_mem, ?_⟩
    have : f 0 ∈ V₁ ∩ A := by rw [← hV₁]; exact ⟨0, ⟨ht0, zero_mem_I⟩, rfl⟩
    exact hf0 ▸ this.1
  have hq₂ : (B ∩ V₂).Nonempty := by
    refine ⟨q, hB.right_mem, ?_⟩
    have : f 1 ∈ V₂ ∩ A := by rw [← hV₂]; exact ⟨1, ⟨ht1, one_mem_I⟩, rfl⟩
    exact hf1 ▸ this.1
  obtain ⟨z, hzB, hz⟩ :=
    hB.isArc.isConnected.isPreconnected V₁ V₂ hV₁open hV₂open hsub hp₁ hq₂
  rw [Set.eq_empty_iff_forall_notMem] at hdisj
  exact hdisj z ⟨hBA hzB, hz⟩

/-! ## Concatenating polylines -/

/-- **Appending two vertex lists joins their carriers by one segment.** The segment runs from
the last vertex of the first list to the first vertex of the second, and is degenerate — hence
contributes nothing — exactly when the two lists already share that vertex. -/
theorem poly_append_join : ∀ {as : List Plane} (h₁ : as ≠ []) {bs : List Plane} (h₂ : bs ≠ []),
    poly (as ++ bs) = poly as ∪ segment ℝ (as.getLast h₁) (bs.head h₂) ∪ poly bs
  | [], h₁, _, _ => absurd rfl h₁
  | [x], _, bs, h₂ => by
    rw [List.singleton_append, poly_cons_of_ne_nil h₂, poly_singleton,
      List.getLast_singleton]
    rw [Set.union_assoc, Set.singleton_union]
    exact (Set.insert_eq_self.2
      (Set.mem_union_left _ (left_mem_segment ℝ x (bs.head h₂)))).symm
  | x :: y :: as, _, bs, h₂ => by
    have hne : (y :: as) ≠ [] := List.cons_ne_nil _ _
    rw [List.cons_append, poly_cons_of_ne_nil (by simp), poly_cons_cons,
      poly_append_join hne h₂, List.head_append_of_ne_nil hne,
      List.getLast_cons hne]
    ac_rfl

/-- **Two polylines meeting end to head concatenate.** The joining segment collapses to the
shared vertex. -/
theorem poly_append_of_eq {as bs : List Plane} (h₁ : as ≠ []) (h₂ : bs ≠ [])
    (h : as.getLast h₁ = bs.head h₂) : poly (as ++ bs) = poly as ∪ poly bs := by
  rw [poly_append_join h₁ h₂, h, segment_same, Set.union_assoc, Set.singleton_union,
    Set.insert_eq_self.2 (head_mem_poly h₂)]

/-! ## A component survives the removal of a set

The face of the enlarged graph through a point of an old face is a component of *that old
face* with the ear removed — not merely of the whole old exterior with the ear removed. No
topology is needed: a component of the small set is preconnected inside the big one, and back
again. -/

/-- **Cutting inside one component.** The component of `z` in `S ∖ P` sees only the component
of `z` in `S`. -/
theorem connectedComponentIn_diff (S P : Set Plane) (z : Plane) :
    connectedComponentIn (S \ P) z = connectedComponentIn (connectedComponentIn S z \ P) z := by
  by_cases hz : z ∈ S \ P
  · have hcomp : connectedComponentIn (S \ P) z ⊆ connectedComponentIn S z :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hz) ((connectedComponentIn_subset _ _).trans Set.sdiff_subset)
    have hzR : z ∈ connectedComponentIn (connectedComponentIn S z \ P) z :=
      mem_connectedComponentIn ⟨mem_connectedComponentIn hz.1, hz.2⟩
    refine Set.Subset.antisymm
      (isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hz) fun w hw =>
          ⟨hcomp hw, (connectedComponentIn_subset _ _ hw).2⟩)
      (isPreconnected_connectedComponentIn.subset_connectedComponentIn hzR fun w hw => ?_)
    have hw' : w ∈ connectedComponentIn S z \ P := connectedComponentIn_subset _ _ hw
    exact ⟨connectedComponentIn_subset _ _ hw'.1, hw'.2⟩
  · rw [connectedComponentIn_eq_empty hz, connectedComponentIn_eq_empty]
    rintro ⟨hw, hwP⟩
    exact hz ⟨connectedComponentIn_subset _ _ hw, hwP⟩

/-! ## A polygonal arc is a polyline running from one end to the other -/

/-- **A polygonal arc is `poly` of a vertex list running from one of its ends to the other.**
`Schoenflies.exists_simple_poly_of_isPolygonal` produces a simple polygonal arc *inside* the
set between the two points; being an arc between the same two ends it is the whole of it, by
`Schoenflies.IsArcBetween.eq_of_subset`. -/
theorem IsArcBetween.exists_poly_eq {A : Set Plane} {p q : Plane} (harc : IsArcBetween A p q)
    (hpoly : IsPolygonal A) (hpq : p ≠ q) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], vs.head h = p ∧ vs.getLast h = q ∧ poly vs = A := by
  obtain ⟨vs, hvs, hhead, hlast, hsub, hsubarc⟩ :=
    exists_simple_poly_of_isPolygonal hpoly harc.isArc.isConnected.isPreconnected hpq
      harc.left_mem harc.right_mem
  exact ⟨vs, hvs, hhead, hlast, harc.eq_of_subset hsubarc hsub⟩

end Schoenflies

namespace Graph

/-! ## Cutting and joining paths

Two general facts about paths that `Schoenflies/Graph/Walk.lean` does not have, and that the
splitting of a cycle at two of its vertices runs on. **The integrator should hoist both into
`Schoenflies/Graph/Walk.lean`**, next to `Graph.IsPath.split`, which is the weaker form of the
second. -/

section GeneralWalk

variable {α β : Type*} {G : Graph α β} {u v w x y : α} {e : β} {W W₁ W₂ : List β}

/-- **Two paths meeting only at the junction concatenate.** The freshness clause of the joined
path is the freshness of the first together with the meeting condition: a vertex the second
half visits and the first half departs from would be the junction, which the first half has
already arrived at. -/
theorem IsPath.append : ∀ {u w v : α} {W₁ W₂ : List β}, G.IsPath u W₁ w → G.IsPath w W₂ v →
    (∀ y ∈ G.walkVertices u W₁, y ∈ G.walkVertices w W₂ → y = w) → G.IsPath u (W₁ ++ W₂) v := by
  intro u w v W₁ W₂ h₁
  induction h₁ with
  | nil hx => intro h₂ _; simpa using h₂
  | @cons u w₀ w e W hl hW hfresh ih =>
    intro h₂ hmeet
    refine List.cons_append .. ▸ IsPath.cons hl
      (ih h₂ fun y hy hy₂ => hmeet y (mem_walkVertices_cons_of_mem hl hy) hy₂) fun hmem => ?_
    -- The departure vertex is fresh: the only new vertices are those of the second half, and
    -- one of those shared with the first half would be the junction, already visited.
    rcases mem_walkVertices_iff.1 hmem with rfl | hcov
    · exact hfresh mem_walkVertices_self
    rw [coveredVertices_append] at hcov
    rcases hcov with hcov | hcov
    · exact hfresh (mem_walkVertices_of_mem_covered hcov)
    · have := hmeet u mem_walkVertices_self (mem_walkVertices_of_mem_covered hcov)
      exact hfresh (this ▸ hW.target_mem_walkVertices)

/-- **A path splits at any vertex it visits, and the two halves meet only there.** This is
`Graph.IsPath.split` with the meeting condition in place of its weaker last clause. -/
theorem IsPath.split_meet (h : G.IsPath u W v) (hx : x ∈ G.walkVertices u W) :
    ∃ W₁ W₂, W = W₁ ++ W₂ ∧ G.IsPath u W₁ x ∧ G.IsPath x W₂ v ∧
      ∀ y ∈ G.walkVertices u W₁, y ∈ G.walkVertices x W₂ → y = x := by
  induction h with
  | nil hx' =>
    rw [walkVertices_nil] at hx
    obtain rfl := hx
    exact ⟨[], [], rfl, .nil hx', .nil hx', fun y hy _ => by simpa using hy⟩
  | @cons u w v e W hl hW hfresh ih =>
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    · exact ⟨[], e :: W, rfl, .nil hl.left_mem, .cons hl hW hfresh,
        fun y hy _ => by simpa using hy⟩
    obtain ⟨W₁, W₂, rfl, h₁, h₂, hmeet⟩ := ih hx'
    have hsub₁ : W₁ ⊆ W₁ ++ W₂ := List.subset_append_left _ _
    have hsub₂ : W₂ ⊆ W₁ ++ W₂ := List.subset_append_right _ _
    refine ⟨e :: W₁, W₂, rfl, .cons hl h₁ fun hmem => hfresh (walkVertices_mono hsub₁ hmem),
      h₂, fun y hy hy₂ => ?_⟩
    -- A vertex of the extended prefix is either the new source — which the far half never
    -- visits, by freshness — or one the induction hypothesis already handles.
    rcases mem_walkVertices_cons hl hy with rfl | hy'
    · exfalso
      rcases mem_walkVertices_iff.1 hy₂ with rfl | hcov
      · exact hfresh (walkVertices_mono hsub₁ h₁.target_mem_walkVertices)
      · exact hfresh (mem_walkVertices_of_mem_covered (coveredVertices_mono hsub₂ hcov))
    · exact hmeet y hy' hy₂

/-- The source of a nonempty walk is an end of its first edge, so a nonempty walk visits no
vertex its edges do not cover. -/
theorem IsWalk.walkVertices_eq_covered (h : G.IsWalk u W v) (hne : W ≠ []) :
    G.walkVertices u W = G.coveredVertices W := by
  refine Set.insert_eq_self.2 ?_
  cases h with
  | nil => exact absurd rfl hne
  | cons hl _ => exact mem_coveredVertices List.mem_cons_self hl.inc_left

/-- Running a nonempty walk backwards changes neither the edges nor the vertices it visits. -/
theorem IsWalk.walkVertices_reverse_eq (h : G.IsWalk u W v) (hne : W ≠ []) :
    G.walkVertices v W.reverse = G.walkVertices u W := by
  rw [h.reverse.walkVertices_eq_covered (by simpa using hne), coveredVertices_reverse,
    h.walkVertices_eq_covered hne]

/-! ### Cutting a cycle at two of its vertices

The cycle is `X ++ Y ++ Z` closed up by the edge `e`, cut at the two vertices `c` (between `X`
and `Y`) and `d` (between `Y` and `Z`). One arc is `Y`; the other runs `Z`, then the closing
edge, then `X`. Both cases of "which of the two named vertices comes first along the detour"
feed this one lemma. -/

/-- **The complementary arc of a cut cycle**, together with the two facts a geometric consumer
needs: that the two arcs between them use every edge of the cycle exactly once, and that they
visit no common vertex but the two cut points. -/
theorem IsCycleThrough.split_aux {G : Graph α β} {e : β} {u v c d : α} {D X Y Z : List β}
    (hc : G.IsCycleThrough e u v D) (hD : D = X ++ (Y ++ Z)) (hX : G.IsPath u X c)
    (hY : G.IsPath c Y d) (hZ : G.IsPath d Z v) (hcd : c ≠ d)
    (hM1 : ∀ y ∈ G.walkVertices u X, y ∈ G.walkVertices c (Y ++ Z) → y = c)
    (hM2 : ∀ y ∈ G.walkVertices c Y, y ∈ G.walkVertices d Z → y = d) :
    G.IsPath d (Z ++ e :: X) c ∧ (Y ++ (Z ++ e :: X)).Perm (e :: D) ∧
      ∀ y ∈ G.walkVertices c Y, y ∈ G.walkVertices d (Z ++ e :: X) → y = c ∨ y = d := by
  have hZsub : G.walkVertices d Z ⊆ G.walkVertices c (Y ++ Z) := by
    intro y hy
    rcases mem_walkVertices_iff.1 hy with rfl | hcov
    · exact walkVertices_mono (List.subset_append_left _ _) hY.target_mem_walkVertices
    · exact mem_walkVertices_of_mem_covered (coveredVertices_mono
        (List.subset_append_right _ _) hcov)
  -- A vertex of the first stretch that the last stretch also reaches would merge the two cuts.
  have hclash : ∀ y ∈ G.walkVertices u X, y ∈ G.walkVertices d Z → False := by
    intro y hy hyZ
    obtain rfl : y = c := hM1 y hy (hZsub hyZ)
    exact hcd (hM2 y mem_walkVertices_self hyZ)
  have hvZ : v ∈ G.walkVertices d Z := hZ.target_mem_walkVertices
  have hvX : v ∉ G.walkVertices u X := fun hh => hclash v hh hvZ
  -- The closing edge, then the first stretch, is a path from the far end back to the first cut.
  have hePath : G.IsPath v (e :: X) c := IsPath.cons hc.isLink.symm hX hvX
  -- Its vertices, other than `v` itself, are those of the first stretch.
  have hcons : ∀ y ∈ G.walkVertices v (e :: X), y = v ∨ y ∈ G.walkVertices u X := by
    intro y hy
    rcases mem_walkVertices_iff.1 hy with rfl | ⟨g, hg, hinc⟩
    · exact Or.inl rfl
    rcases List.mem_cons.1 hg with rfl | hg'
    · rcases hinc.eq_or_eq_of_isLink hc.isLink with rfl | rfl
      · exact Or.inr mem_walkVertices_self
      · exact Or.inl rfl
    · exact Or.inr (mem_walkVertices_of_mem_covered ⟨g, hg', hinc⟩)
  refine ⟨hZ.append hePath fun y hy hy' => ?_, ?_, fun y hy hy' => ?_⟩
  · rcases hcons y hy' with rfl | hyX
    · rfl
    · exact absurd hyX fun hh => hclash y hh hy
  · subst hD
    rw [show Y ++ (Z ++ e :: X) = (Y ++ Z) ++ (e :: X) by rw [List.append_assoc]]
    exact List.perm_middle.trans (List.Perm.cons _ List.perm_append_comm)
  · -- A vertex on both arcs is on the last stretch — hence the second cut — or on the first,
    -- hence the first cut.
    rcases mem_walkVertices_iff.1 hy' with rfl | hcov
    · exact Or.inr rfl
    rw [coveredVertices_append] at hcov
    rcases hcov with hcovZ | hcovE
    · exact Or.inr (hM2 y hy (mem_walkVertices_of_mem_covered hcovZ))
    · rcases hcons y (mem_walkVertices_of_mem_covered hcovE) with rfl | hyX
      · exact Or.inr (hM2 y hy hvZ)
      · exact Or.inl (hM1 y hyX (walkVertices_mono (List.subset_append_left _ _) hy))

/-- **A cycle cut at two of its vertices is two paths between them.** The two arcs use every
edge of the cycle exactly once — that is what the permutation says — and they have no vertex in
common but the two cut points. This is the combinatorial half of "the ear is a crosscut of the
face": the geometric half reads the two arcs of the Jordan curve off it. -/
theorem IsCycleThrough.split_at {G : Graph α β} {e : β} {u v a b : α} {D : List β}
    (hc : G.IsCycleThrough e u v D) (ha : a ∈ G.walkVertices u D) (hb : b ∈ G.walkVertices u D)
    (hab : a ≠ b) :
    ∃ D₁ D₂ : List β, G.IsPath a D₁ b ∧ G.IsPath b D₂ a ∧ (D₁ ++ D₂).Perm (e :: D) ∧
      ∀ y ∈ G.walkVertices a D₁, y ∈ G.walkVertices b D₂ → y = a ∨ y = b := by
  obtain ⟨P, Q, hPQ, hP, hQ, hM1⟩ := hc.isPath.split_meet ha
  -- The second cut point lies on one of the two stretches the first one made.
  have hcases : b ∈ G.walkVertices a Q ∨ b ∈ G.walkVertices u P := by
    rw [hPQ] at hb
    rcases mem_walkVertices_iff.1 hb with rfl | hcov
    · exact Or.inr mem_walkVertices_self
    rw [coveredVertices_append] at hcov
    rcases hcov with h | h
    · exact Or.inr (mem_walkVertices_of_mem_covered h)
    · exact Or.inl (mem_walkVertices_of_mem_covered h)
  rcases hcases with hbQ | hbP
  · -- `b` comes after `a`: cut the far stretch at `b`.
    obtain ⟨Q₁, Q₂, hQ12, hQ1, hQ2, hM2⟩ := hQ.split_meet hbQ
    obtain ⟨hpath, hperm, hmeet⟩ := hc.split_aux (X := P) (Y := Q₁) (Z := Q₂)
      (by rw [hPQ, hQ12]) hP hQ1 hQ2 hab (by rw [← hQ12]; exact hM1) hM2
    exact ⟨Q₁, Q₂ ++ e :: P, hQ1, hpath, hperm, hmeet⟩
  · -- `b` comes before `a`: cut the near stretch at `b`, and the two roles are exchanged.
    obtain ⟨P₁, P₂, hP12, hP1, hP2, hM2⟩ := hP.split_meet hbP
    have hP1sub : G.walkVertices u P₁ ⊆ G.walkVertices u P :=
      walkVertices_mono (by rw [hP12]; exact List.subset_append_left _ _)
    have hP2sub : G.walkVertices b P₂ ⊆ G.walkVertices u P := by
      intro y hy
      rcases mem_walkVertices_iff.1 hy with rfl | hcov
      · exact hbP
      · exact mem_walkVertices_of_mem_covered
          (coveredVertices_mono (by rw [hP12]; exact List.subset_append_right _ _) hcov)
    have hM1' : ∀ y ∈ G.walkVertices u P₁, y ∈ G.walkVertices b (P₂ ++ Q) → y = b := by
      intro y hy hy'
      rcases mem_walkVertices_iff.1 hy' with rfl | hcov
      · rfl
      rw [coveredVertices_append] at hcov
      rcases hcov with h | h
      · exact hM2 y hy (mem_walkVertices_of_mem_covered h)
      · -- A vertex both stretches of the near half and the far half reach merges the two cuts.
        exfalso
        obtain rfl : y = a := hM1 y (hP1sub hy) (mem_walkVertices_of_mem_covered h)
        exact hab (hM2 y hy hP2.target_mem_walkVertices)
    obtain ⟨hpath, hperm, hmeet⟩ := hc.split_aux (X := P₁) (Y := P₂) (Z := Q)
      (by rw [hPQ, hP12, List.append_assoc]) hP1 hP2 hQ (Ne.symm hab) hM1'
      fun y hy hy' => hM1 y (hP2sub hy) hy'
    refine ⟨Q ++ e :: P₁, P₂, hpath, hP2, List.perm_append_comm.trans hperm, fun y hy hy' => ?_⟩
    exact (hmeet y hy' hy).symm

/-! ### Splicing an ear onto an arc

The blueprint's "the crosscut replaces `F` by exactly two regions, both bounded by cycles": the
two new cycles are the two arcs of the old one, each closed up by the ear. This is the
combinatorial construction of one of them. -/

/-- Incidence along edges of a subgraph is the same in the subgraph as in the graph, so the
vertices a walk visits do not depend on which of the two it is read in. -/
theorem coveredVertices_congr_of_le {H G : Graph α β} (hHG : H ≤ G) (hW : ∀ f ∈ W, f ∈ E(H)) :
    G.coveredVertices W = H.coveredVertices W := by
  ext x
  constructor
  · rintro ⟨g, hg, y, hy⟩
    exact ⟨g, hg, y, (hHG.isLink_iff (hW g hg)).2 hy⟩
  · rintro ⟨g, hg, y, hy⟩
    exact ⟨g, hg, y, hy.mono hHG⟩

theorem walkVertices_congr_of_le {H G : Graph α β} (hHG : H ≤ G) (hW : ∀ f ∈ W, f ∈ E(H)) :
    G.walkVertices u W = H.walkVertices u W := by
  rw [walkVertices, walkVertices, coveredVertices_congr_of_le hHG hW]

/-- **The cycle an ear splices onto an arc of the old cycle.** The closed walk runs along the
arc and back along the ear; presented as `Graph.IsCycleThrough`, its named edge is the ear's
first, and its detour is the arc followed by the rest of the ear reversed. -/
theorem exists_spliced_cycle {B G : Graph α β} (hBG : B ≤ G) {a b : α} {D₁ D' : List β}
    (hD1 : B.IsPath a D₁ b) (hear : G.IsPath a D' b) (hab : a ≠ b)
    (hnew : ∀ g ∈ D', g ∉ E(B))
    (hint : ∀ y ∈ G.walkVertices a D', y ≠ a → y ≠ b → y ∉ V(B)) :
    ∃ (f : β) (x y : α) (T : List β),
      (B.union (G.pathGraphOf a D')).IsCycleThrough f x y T ∧ (f :: T).Perm (D₁ ++ D') := by
  obtain ⟨f, T, rfl⟩ : ∃ f T, D' = f :: T := by
    cases D' with
    | nil => exact absurd hear.isWalk.eq_of_nil hab
    | cons f T => exact ⟨f, T, rfl⟩
  obtain ⟨w, hl, hT, hfresh⟩ :
      ∃ w, G.IsLink f a w ∧ G.IsPath w T b ∧ a ∉ G.walkVertices w T := by
    cases hear with
    | cons hl hT hfr => exact ⟨_, hl, hT, hfr⟩
  set P := G.pathGraphOf a (f :: T) with hP
  have hPG : P ≤ G := pathGraphOf_le hear.isWalk
  have hcompat : B.Compatible P := Compatible.of_le_le hBG hPG
  have hPB : P ≤ B.union P := hcompat.right_le_union
  have hBB : B ≤ B.union P := left_le_union _ _
  have hedges : ∀ g ∈ T, g ∈ E(P) := fun g hg => by
    rw [pathGraphOf_edgeSet hear.isWalk]; exact List.mem_cons_of_mem _ hg
  -- The ear's tail, run backwards, is a path of the enlarged graph from the far end.
  have hTrev : (B.union P).IsPath b T.reverse w := by
    refine ((hT.reverse.anti hPG ?_ ?_).mono hPB)
    · rw [pathGraphOf_vertexSet]; exact hear.isWalk.target_mem_walkVertices
    · intro g hg; exact hedges g (List.mem_reverse.1 hg)
  have hD1' : (B.union P).IsPath a D₁ b := hD1.mono hBB
  have hTedges : ∀ g ∈ T.reverse, g ∈ E(P) := fun g hg => hedges g (List.mem_reverse.1 hg)
  have hcovP : ∀ W' : List β, (∀ g ∈ W', g ∈ E(P)) →
      (B.union P).coveredVertices W' = G.coveredVertices W' := by
    intro W' hW'
    rw [coveredVertices_congr_of_le hPB hW', ← coveredVertices_congr_of_le hPG hW']
  -- The arc and the ear's tail meet only at the ear's far end: a common vertex lies in the old
  -- subgraph, so the ear's freshness clause makes it one of the ear's two ends, and the source
  -- is not one the rest of the ear visits.
  have hmeet : ∀ y ∈ (B.union P).walkVertices a D₁, y ∈ (B.union P).walkVertices b T.reverse →
      y = b := by
    intro y hy hy'
    have hyB : y ∈ V(B) := by
      rw [walkVertices_congr_of_le hBB (fun g hg => hD1.edge_mem hg)] at hy
      exact hD1.isWalk.walkVertices_subset hy
    have hy'' : y = b ∨ y ∈ G.coveredVertices T := by
      rcases mem_walkVertices_iff.1 hy' with rfl | hcov
      · exact Or.inl rfl
      · rw [hcovP _ hTedges, coveredVertices_reverse] at hcov
        exact Or.inr hcov
    rcases hy'' with rfl | hcov
    · rfl
    have hyD : y ∈ G.walkVertices a (f :: T) :=
      mem_walkVertices_of_mem_covered (coveredVertices_mono (List.subset_cons_self _ _) hcov)
    by_contra hyb
    obtain rfl : y = a := by
      by_contra hya
      exact hint y hyD hya hyb hyB
    exact hfresh (mem_walkVertices_of_mem_covered hcov)
  refine ⟨f, a, w, D₁ ++ T.reverse, ⟨?_, hD1'.append hTrev hmeet, ?_⟩, ?_⟩
  · exact (pathGraphOf_isLink.2 ⟨List.mem_cons_self, hl, mem_walkVertices_self,
      mem_walkVertices_of_mem_covered ⟨f, List.mem_cons_self, hl.inc_right⟩⟩).mono hPB
  · -- The ear's first edge is on neither the arc — it is not an edge of the old subgraph at
    -- all — nor the rest of the ear, which is a path.
    intro hmem
    rcases List.mem_append.1 hmem with h | h
    · exact hnew f List.mem_cons_self (hD1.edge_mem h)
    · exact (List.nodup_cons.1 hear.nodup).1 (List.mem_reverse.1 h)
  · exact ((List.reverse_perm T).append_left D₁).cons f |>.trans List.perm_middle.symm

end GeneralWalk

open Schoenflies

variable {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane}
variable {e f : β} {u v w z a b : Plane} {W D : List β}

/-! ## What a walk of a polygonal plane graph draws -/

/-- **The realisation of a walk with polygonal edges is a polyline from its source to its
target.** The induction is along the walk: the first edge contributes its own vertex list, and
the two lists are joined at the waypoint, which is the last vertex of the first and the first
vertex of the rest. -/
theorem IsDrawing.exists_poly_eq_edgesCover (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e)) (hW : G.IsWalk u W v) (hne : W ≠ []) :
    ∃ vs : List Plane, ∃ hv : vs ≠ [], vs.head hv = u ∧ vs.getLast hv = v ∧
      poly vs = edgesCover drawing W := by
  induction hW with
  | nil => exact absurd rfl hne
  | @cons u w v e W hl hW ih =>
    have hedge : ∃ vs : List Plane, ∃ hv : vs ≠ [], vs.head hv = u ∧ vs.getLast hv = w ∧
        poly vs = edgeArc drawing e :=
      (h.edge_isArcBetween hl).exists_poly_eq (hpoly e hl.edge_mem) (h.ne_of_isLink hl)
    obtain ⟨es, hes, heshead, heslast, hespoly⟩ := hedge
    rcases eq_or_ne W [] with rfl | hWne
    · obtain rfl : w = v := hW.eq_of_nil
      exact ⟨es, hes, heshead, heslast, by
        rw [hespoly, edgesCover_cons, edgesCover_nil, Set.union_empty]⟩
    · obtain ⟨vs, hvs, hhead, hlast, hpolyv⟩ := ih hWne
      -- The two lists share the waypoint, so their carriers join there.
      refine ⟨es ++ vs, by simp [hes], ?_, ?_, ?_⟩
      · rw [List.head_append_of_ne_nil hes]; exact heshead
      · rw [List.getLast_append_of_ne_nil _ hvs]; exact hlast
      · rw [poly_append_of_eq hes hvs (by rw [heslast, hhead]), hespoly, hpolyv,
          edgesCover_cons]

/-! ## The realisation of a cycle is a separating curve

This is the composition the base case of `lem:face-cycles` needs, and the one thing that was
missing from it: `Graph.IsDrawing.cycle_isJordanCurve` says the realisation is a Jordan curve
and `Graph.IsDrawing.isPolygonal_edgesCover` says it is polygonal, and
`Schoenflies.exists_closedPolygon` — the realization theorem — turns that pair into a
`Schoenflies.ClosedPolygon`, whose carrier `Schoenflies.ClosedPolygon.isSeparating_carrier`
knows to separate the plane. Nothing here inspects the polygon; it is used and discarded. -/

/-- Going round the cycle the other way: the edge, then the detour, is a closed walk at the
edge's far end. This is the walk whose edge list is `e :: D`, the list every statement about
the realisation of a cycle is phrased with. -/
theorem IsCycleThrough.isWalk_cons {α : Type*} {G : Graph α β} {e : β} {u v : α} {D : List β}
    (hc : G.IsCycleThrough e u v D) : G.IsWalk v (e :: D) v :=
  IsWalk.cons hc.isLink.symm hc.isPath.isWalk

/-- **The realisation of a cycle of a polygonal plane graph is a separating Jordan curve.**
`Schoenflies.IsSeparating` is Definition 2.4: the complement has exactly two regions, one
bounded and one unbounded, each with the curve as its boundary. -/
theorem IsDrawing.cycle_isSeparating (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e)) {e : β} {u v : Plane} {D : List β}
    (hc : G.IsCycleThrough e u v D) : IsSeparating (edgesCover drawing (e :: D)) := by
  obtain ⟨m, P, hP⟩ := exists_closedPolygon (h.cycle_isJordanCurve hc)
    (h.isPolygonal_edgesCover hpoly hc.isWalk_cons (List.cons_ne_nil _ _))
  exact hP ▸ P.isSeparating_carrier

/-! ## What a subgraph spanned by a walk occupies -/

/-- An end of an edge lies on that edge's arc. -/
theorem IsDrawing.inc_mem_edgeArc (h : IsDrawing G drawing) {x : Plane} (hinc : G.Inc e x) :
    x ∈ edgeArc drawing e := by
  obtain ⟨y, hy⟩ := hinc
  exact (h.edge_isArcBetween hy).left_mem

/-- **The subgraph spanned by a nonempty walk occupies exactly what the walk draws.** Its
vertices are ends of its edges, so they add nothing to the union of the edge arcs. -/
theorem IsDrawing.pointSet_pathGraphOf (h : IsDrawing G drawing) (hW : G.IsWalk u W v)
    (hne : W ≠ []) : pointSet (G.pathGraphOf u W) drawing = edgesCover drawing W := by
  obtain ⟨f, T, rfl⟩ : ∃ f T, W = f :: T := by
    cases W with
    | nil => exact absurd rfl hne
    | cons f T => exact ⟨f, T, rfl⟩
  refine Set.Subset.antisymm (Set.union_subset ?_ ?_) ?_
  · -- Every vertex the walk visits is an end of one of its edges.
    intro x hx
    rw [pathGraphOf_vertexSet] at hx
    rcases mem_walkVertices_iff.1 hx with rfl | ⟨g, hg, hinc⟩
    · cases hW with
      | cons hl _ => exact mem_edgesCover List.mem_cons_self (h.inc_mem_edgeArc hl.inc_left)
    · exact mem_edgesCover hg (h.inc_mem_edgeArc hinc)
  · refine Set.iUnion₂_subset fun g hg => ?_
    rw [pathGraphOf_edgeSet hW] at hg
    exact fun z hz => mem_edgesCover hg hz
  · intro z hz
    obtain ⟨g, hg, hzg⟩ := mem_edgesCover_iff.1 hz
    refine edgeArc_subset_pointSet ?_ hzg
    rw [pathGraphOf_edgeSet hW]
    exact hg

/-- **The cycle subgraph occupies exactly what the cycle draws.** -/
theorem IsDrawing.pointSet_cycleGraph (h : IsDrawing G drawing) {e : β} {u v : Plane}
    {D : List β} (hc : G.IsCycleThrough e u v D) :
    pointSet (G.cycleGraph u e D) drawing = edgesCover drawing (e :: D) := by
  have hround := h.pointSet_pathGraphOf hc.isWalk_round (by simp)
  rw [cycleGraph, hround]
  refine Set.Subset.antisymm (edgesCover_mono fun g hg => ?_) (edgesCover_mono fun g hg => ?_)
  · rcases List.mem_append.1 hg with hg' | hg'
    · exact List.mem_cons_of_mem _ hg'
    · obtain rfl : g = e := by simpa using hg'
      exact List.mem_cons_self
  · rcases List.mem_cons.1 hg with rfl | hg'
    · exact List.mem_append_right _ List.mem_cons_self
    · exact List.mem_append_left _ hg'

/-! ## The conclusion of `lem:face-cycles`, at one face -/

/-- **A face bounded by a named cycle.** The face `face G drawing z` is one of the two regions
of the complement of the realisation of the cycle `e :: D` — which is the blueprint's "every
face … has a cycle as its boundary *and is one of the two complementary regions of that
cycle*". The cycle is a parameter rather than an existential so that a consumer that has
produced one keeps it. -/
structure IsFaceCycle (G : Graph Plane β) (drawing : β → ℝ → Plane) (z : Plane)
    (e : β) (u v : Plane) (D : List β) : Prop where
  /-- The named data really is a cycle of the graph. -/
  isCycle : G.IsCycleThrough e u v D
  /-- Its realisation separates the plane into exactly two regions. -/
  isSeparating : IsSeparating (edgesCover drawing (e :: D))
  /-- The face is one of those two. -/
  isRegionOf : IsRegionOf (edgesCover drawing (e :: D)) (face G drawing z)

namespace IsFaceCycle

variable {e : β} {u v : Plane} {D : List β}

/-- **"has a cycle as its boundary"**: the frontier of the face is the realisation. -/
theorem frontier_eq (h : IsFaceCycle G drawing z e u v D) :
    frontier (face G drawing z) = edgesCover drawing (e :: D) :=
  h.isRegionOf.frontier_eq h.isSeparating

/-- The face is the interior or the exterior of its boundary cycle. -/
theorem eq_inside_or_outside (h : IsFaceCycle G drawing z e u v D) :
    face G drawing z = inside (edgesCover drawing (e :: D)) ∨
      face G drawing z = outside (edgesCover drawing (e :: D)) := h.isRegionOf

/-- **"In particular, every bounded face is the interior of its boundary cycle."** The other
region of a separating curve is the unbounded one. -/
theorem eq_inside_of_isBounded (h : IsFaceCycle G drawing z e u v D)
    (hbdd : Bornology.IsBounded (face G drawing z)) :
    face G drawing z = inside (edgesCover drawing (e :: D)) := by
  rcases h.isRegionOf with hin | hout
  · exact hin
  · exact absurd (hout ▸ hbdd) h.isSeparating.not_isBounded_outside

/-- A face bounded by a cycle of a subgraph is bounded by the same cycle of the whole graph,
*provided the face itself is unchanged* — which is the shape the induction step needs when it
carries a face past an ear that does not touch it. -/
theorem mono (h : IsFaceCycle B drawing z e u v D) (hBG : B ≤ G)
    (hface : face G drawing z = face B drawing z) : IsFaceCycle G drawing z e u v D where
  isCycle := ⟨h.isCycle.isLink.mono hBG, h.isCycle.isPath.mono hBG, h.isCycle.notMem⟩
  isSeparating := h.isSeparating
  isRegionOf := hface ▸ h.isRegionOf

end IsFaceCycle

/-- **`lem:face-cycles`, as a property of a plane graph**: every face has a cycle as its
boundary and is one of the two complementary regions of that cycle. -/
def HasFaceCycles (G : Graph Plane β) (drawing : β → ℝ → Plane) : Prop :=
  ∀ z ∈ exterior G drawing, ∃ (e : β) (u v : Plane) (D : List β), IsFaceCycle G drawing z e u v D

/-! ## The base case: the faces of a single cycle

"This is true for the initial cycle by Theorem `thm:polygonal-jordan`." The cycle subgraph
occupies exactly the cycle's realisation, so its faces are literally the components of the
complement of that curve, and the curve is separating. -/

/-- **The base case of `lem:face-cycles`.** Both faces of the graph consisting of one cycle
are regions of that cycle. -/
theorem IsDrawing.hasFaceCycles_cycleGraph (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e)) {e : β} {u v : Plane} {D : List β}
    (hc : G.IsCycleThrough e u v D) : HasFaceCycles (G.cycleGraph u e D) drawing := by
  have hsep : IsSeparating (edgesCover drawing (e :: D)) := h.cycle_isSeparating hpoly hc
  -- The same cycle, read inside the subgraph it spans.
  have hcyc : (G.cycleGraph u e D).IsCycleThrough e u v D :=
    ⟨hc.cycleGraph_isLink,
      hc.isPath.anti hc.cycleGraph_le hc.left_mem_cycleGraph fun g hg => by
        rw [hc.cycleGraph_edgeSet]; exact List.mem_append_left _ hg,
      hc.notMem⟩
  intro z hz
  refine ⟨e, u, v, D, hcyc, hsep, ?_⟩
  rw [face, exterior, h.pointSet_cycleGraph hc]
  refine hsep.isRegionOf_connectedComponentIn ?_
  rw [exterior, h.pointSet_cycleGraph hc] at hz
  exact hz

/-! ## The two arcs a cycle is cut into, as sets

The combinatorial split of `Graph.IsCycleThrough.split_at` becomes the geometric one: the two
arcs of the Jordan curve between the two cut vertices. The drawing condition is used once, to
turn "the two edge lists are disjoint" into "the two arcs meet only at vertices". -/

/-- A vertex of the graph lying on the realisation of a cycle is a vertex of that cycle. -/
theorem IsDrawing.mem_walkVertices_of_mem_edgesCover (h : IsDrawing G drawing) {e : β}
    {u v z : Plane} {D : List β} (hc : G.IsCycleThrough e u v D) (hzV : z ∈ V(G))
    (hz : z ∈ edgesCover drawing (e :: D)) : z ∈ G.walkVertices u D := by
  obtain ⟨g, hg, hzg⟩ := mem_edgesCover_iff.1 hz
  rcases List.mem_cons.1 hg with rfl | hg'
  · rcases h.vertex_mem_edgeArc hc.isLink hzV hzg with rfl | rfl
    · exact mem_walkVertices_self
    · exact hc.isPath.target_mem_walkVertices
  · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet (hc.isPath.edge_mem hg')
    rcases h.vertex_mem_edgeArc hxy hzV hzg with rfl | rfl
    · exact mem_walkVertices_of_mem_covered ⟨g, hg', hxy.inc_left⟩
    · exact mem_walkVertices_of_mem_covered ⟨g, hg', hxy.inc_right⟩

/-- **The realisation of a cycle, cut at two of its vertices, is two arcs meeting exactly
there.** The hypotheses are the output of `Graph.IsCycleThrough.split_at`, read in the plane. -/
theorem IsDrawing.arcs_of_split (h : IsDrawing G drawing) {a b : Plane} {D₁ D₂ : List β}
    (h₁ : G.IsPath a D₁ b) (h₂ : G.IsPath b D₂ a) (hab : a ≠ b)
    (hdisj : ∀ g ∈ D₁, g ∉ D₂)
    (hmeet : ∀ y ∈ G.walkVertices a D₁, y ∈ G.walkVertices b D₂ → y = a ∨ y = b) :
    IsArcBetween (edgesCover drawing D₁) a b ∧ IsArcBetween (edgesCover drawing D₂) b a ∧
      edgesCover drawing D₁ ∩ edgesCover drawing D₂ = {a, b} := by
  have harc₁ : IsArcBetween (edgesCover drawing D₁) a b :=
    h.path_isArcBetween h₁ (h₁.ne_nil hab)
  have harc₂ : IsArcBetween (edgesCover drawing D₂) b a :=
    h.path_isArcBetween h₂ (h₂.ne_nil (Ne.symm hab))
  refine ⟨harc₁, harc₂, Set.Subset.antisymm (fun z ⟨hz₁, hz₂⟩ => ?_) ?_⟩
  · -- A common point lies on an edge of each, and the two edges are distinct.
    obtain ⟨g₁, hg₁, hzg₁⟩ := mem_edgesCover_iff.1 hz₁
    obtain ⟨g₂, hg₂, hzg₂⟩ := mem_edgesCover_iff.1 hz₂
    have hne : g₁ ≠ g₂ := fun hh => hdisj g₁ hg₁ (hh ▸ hg₂)
    obtain ⟨-, hinc₁, hinc₂⟩ :=
      h.edge_inter (h₁.edge_mem hg₁) (h₂.edge_mem hg₂) hne hzg₁ hzg₂
    exact hmeet z (mem_walkVertices_of_mem_covered ⟨g₁, hg₁, hinc₁⟩)
      (mem_walkVertices_of_mem_covered ⟨g₂, hg₂, hinc₂⟩)
  · rintro z (rfl | rfl)
    exacts [⟨harc₁.left_mem, harc₂.right_mem⟩, ⟨harc₁.right_mem, harc₂.left_mem⟩]

end Graph

namespace Schoenflies

/-! ## The obligation this module does not discharge

**Read this before using `Graph.face_cycles`.** Everything below the base case is proved
*modulo* one hypothesis, `Schoenflies.CrosscutSplitsRegion`, and the final theorem carries it
as an argument. It is the exhaustion clause of `thm:polygonal-crosscut` — Theorem 2.8, in the
shape `Schoenflies.IsPolygonalCrosscut.region_eq` and
`Schoenflies.IsPolygonalCrosscut.cell_isComponent₁` already have it — at a crosscut whose two
endpoints are **arbitrary points of the curve**.

`main`'s Theorem 2.8 cannot be applied here, and the reason is not a missing bridge. Its
hypotheses `edges₁`/`edges₂` are stated against `ClosedPolygon.arcPieces C a k`, which splits
the polygon's edge list **at two of its vertices**; and by
`Schoenflies.ClosedPolygon.isCornerAt_vertex` every vertex of every realization of a curve is a
*corner* of it. In the induction below the two cut points are the ear's endpoints, which are
graph vertices at which the two cycle edges may perfectly well leave along opposite rays — the
curve then runs straight through the cut point, which is therefore a vertex of no
`ClosedPolygon` with that carrier, and no realization theorem can supply one. Discharging this
hypothesis needs Theorem 2.8 restated for an edge-list split made at arbitrary points, which in
turn needs the parity theory for polygon presentations carrying redundant vertices
(`Schoenflies.PrePolygon`) rather than only for `ClosedPolygon`. That is a separate module. -/

/-- **The exhaustion clause of the polygonal crosscut theorem, at arbitrary cut points.**
`J` is a separating polygonal curve cut by the points `p, q` into the arcs `A₁, A₂`; `P` is a
polygonal crosscut from `p` to `q` meeting `J` only there and running inside the region `Ω`.
The claim is that every component of `Ω ∖ P` is a region of `A₁ ∪ P` or of `A₂ ∪ P` — the
blueprint's "Theorem 2.8 replaces `F` by exactly two regions, both bounded by cycles".

This is **assumed**, not proved; see the section docstring for why `main`'s Theorem 2.8 does
not apply. -/
def CrosscutSplitsRegion : Prop :=
  ∀ (J A₁ A₂ P Ω : Set Plane) (p q : Plane),
    IsSeparating J → IsPolygonal J → IsPolygonal P →
    IsArcBetween A₁ p q → IsArcBetween A₂ p q → A₁ ∪ A₂ = J → A₁ ∩ A₂ = {p, q} →
    IsArcBetween P p q → P ∩ J = {p, q} → IsRegionOf J Ω → P \ {p, q} ⊆ Ω →
    ∀ z ∈ Ω \ P, IsRegionOf (A₁ ∪ P) (connectedComponentIn (Ω \ P) z) ∨
      IsRegionOf (A₂ ∪ P) (connectedComponentIn (Ω \ P) z)

end Schoenflies

namespace Graph

open Schoenflies

variable {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane}
variable {e f : β} {u v w z a b : Plane} {W D : List β}

/-! ## What a list of edges draws depends only on which edges are on it -/

theorem edgesCover_append (drawing : β → ℝ → Plane) (W₁ W₂ : List β) :
    edgesCover drawing (W₁ ++ W₂) = edgesCover drawing W₁ ∪ edgesCover drawing W₂ := by
  refine Set.Subset.antisymm (fun z hz => ?_)
    (Set.union_subset (edgesCover_mono (List.subset_append_left _ _))
      (edgesCover_mono (List.subset_append_right _ _)))
  obtain ⟨g, hg, hzg⟩ := mem_edgesCover_iff.1 hz
  exact (List.mem_append.1 hg).imp (fun h => mem_edgesCover h hzg) fun h => mem_edgesCover h hzg

theorem edgesCover_perm {W₁ W₂ : List β} (hp : W₁.Perm W₂) :
    edgesCover drawing W₁ = edgesCover drawing W₂ :=
  Set.Subset.antisymm (edgesCover_mono fun _ hg => hp.mem_iff.1 hg)
    (edgesCover_mono fun _ hg => hp.mem_iff.2 hg)

theorem edgesCover_reverse (drawing : β → ℝ → Plane) (W : List β) :
    edgesCover drawing W.reverse = edgesCover drawing W := edgesCover_perm (List.reverse_perm W)

/-! ## The induction step: one ear

"Suppose it holds for the current graph and add the next geometric ear. Its interior is
connected and disjoint from the current graph, so it lies in one current face `F` … the ear is
therefore a crosscut of that side, and Theorem `thm:polygonal-crosscut` replaces `F` by exactly
two regions, both bounded by cycles; all other faces are unchanged."

Everything here is proved, except that the appeal to Theorem 2.8 is to the hypothesis
`Schoenflies.CrosscutSplitsRegion` instead. -/

/-- **One ear.** Given `lem:face-cycles` for the current subgraph, it holds for the subgraph
enlarged by an ear — modulo `Schoenflies.CrosscutSplitsRegion`. -/
theorem IsDrawing.hasFaceCycles_union [G.Finite] (h : IsDrawing G drawing)
    (hobl : CrosscutSplitsRegion) (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g))
    (hBG : B ≤ G) (hmot : HasFaceCycles B drawing) {D' : List β}
    (hpath : G.IsPath a D' b) (hab : a ≠ b) (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hint : ∀ y ∈ G.walkVertices a D', y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ D', g ∉ E(B)) :
    HasFaceCycles (B.union (G.pathGraphOf a D')) drawing := by
  let _ : B.Finite := Finite.of_le hBG
  have hB : IsDrawing B drawing := h.mono hBG
  have hne : D' ≠ [] := hpath.ne_nil hab
  have hPG : G.pathGraphOf a D' ≤ G := pathGraphOf_le hpath.isWalk
  have hB'G : B.union (G.pathGraphOf a D') ≤ G := union_le hBG hPG
  have hBB' : B ≤ B.union (G.pathGraphOf a D') := left_le_union _ _
  have hB' : IsDrawing (B.union (G.pathGraphOf a D')) drawing := h.mono hB'G
  have hpoly' : ∀ g ∈ E(B.union (G.pathGraphOf a D')), IsPolygonal (edgeArc drawing g) :=
    fun g hg => hpoly g (hB'G.edgeSet_mono hg)
  have hQarc : IsArcBetween (edgesCover drawing D') a b := h.path_isArcBetween hpath hne
  have hQpoly : IsPolygonal (edgesCover drawing D') :=
    h.isPolygonal_edgesCover hpoly hpath.isWalk hne
  have hext : exterior (B.union (G.pathGraphOf a D')) drawing =
      exterior B drawing \ edgesCover drawing D' := by
    rw [exterior_union, h.pointSet_pathGraphOf hpath.isWalk hne]
  -- The ear lies in one face of the old subgraph.
  obtain ⟨z₀, hz₀, hsub₀⟩ := h.exists_face_of_ear hBG hpath hab hint hnew
  have hQinter : ∀ w ∈ edgesCover drawing D', w ∈ exterior B drawing →
      w ∈ face B drawing z₀ := by
    intro w hw hwe
    refine hsub₀ ⟨hw, fun hcon => hwe ?_⟩
    rcases hcon with rfl | rfl
    exacts [vertexSet_subset_pointSet ha, vertexSet_subset_pointSet hb]
  intro z hz
  rw [hext] at hz
  obtain ⟨hzB, hzQ⟩ := hz
  obtain ⟨e, u, v, D, hface⟩ := hmot z hzB
  by_cases hsame : face B drawing z = face B drawing z₀
  · -- The face the ear cuts.
    have hopenF : IsOpen (face B drawing z₀) := hB.isOpen_face z₀
    obtain ⟨haF, hbF⟩ := h.ends_mem_frontier_face hopenF hpath hab ha hb hsub₀
    have hfr : frontier (face B drawing z₀) = edgesCover drawing (e :: D) := by
      rw [← hsame]; exact hface.frontier_eq
    have haW : a ∈ B.walkVertices u D :=
      hB.mem_walkVertices_of_mem_edgesCover hface.isCycle ha (hfr ▸ haF)
    have hbW : b ∈ B.walkVertices u D :=
      hB.mem_walkVertices_of_mem_edgesCover hface.isCycle hb (hfr ▸ hbF)
    obtain ⟨D₁, D₂, hD1, hD2, hperm, hmeet⟩ := hface.isCycle.split_at haW hbW hab
    -- The two arcs use disjoint edge lists, because the cycle's own list repeats nothing.
    have hnodup : (e :: D).Nodup := List.nodup_cons.2 ⟨hface.isCycle.notMem,
      hface.isCycle.isPath.nodup⟩
    have hdisj : ∀ g ∈ D₁, g ∉ D₂ := fun g hg hg₂ =>
      (List.nodup_append.1 (hperm.nodup_iff.2 hnodup)).2.2 g hg g hg₂ rfl
    obtain ⟨harc₁, harc₂, hinter⟩ := hB.arcs_of_split hD1 hD2 hab hdisj hmeet
    have hunion : edgesCover drawing D₁ ∪ edgesCover drawing D₂ = edgesCover drawing (e :: D) := by
      rw [← edgesCover_append, edgesCover_perm hperm]
    -- The ear meets the cycle exactly in its own two ends.
    have hJsub : edgesCover drawing (e :: D) ⊆ pointSet B drawing :=
      edgesCover_subset_pointSet fun g hg => by
        rcases List.mem_cons.1 hg with rfl | hg'
        exacts [hface.isCycle.isLink.edge_mem, hface.isCycle.isPath.edge_mem hg']
    have hmeetJ : edgesCover drawing D' ∩ edgesCover drawing (e :: D) = {a, b} := by
      refine Set.Subset.antisymm (fun w hw =>
        h.edgesCover_inter_pointSet hBG hpath hint hnew ⟨hw.1, hJsub hw.2⟩) ?_
      rintro w (rfl | rfl)
      exacts [⟨hQarc.left_mem, hfr ▸ haF⟩, ⟨hQarc.right_mem, hfr ▸ hbF⟩]
    -- The crosscut hypothesis.
    have hzF : z ∈ face B drawing z \ edgesCover drawing D' := ⟨mem_face hzB, hzQ⟩
    have hfaceEq : face (B.union (G.pathGraphOf a D')) drawing z =
        connectedComponentIn (face B drawing z \ edgesCover drawing D') z := by
      have hstep : face (B.union (G.pathGraphOf a D')) drawing z =
          connectedComponentIn (exterior B drawing \ edgesCover drawing D') z := by
        rw [face, hext]
      rw [hstep, connectedComponentIn_diff]
      rfl
    have hcross := hobl (edgesCover drawing (e :: D)) (edgesCover drawing D₁)
      (edgesCover drawing D₂) (edgesCover drawing D') (face B drawing z) a b
      hface.isSeparating
      (h.isPolygonal_edgesCover hpoly (hface.isCycle.isWalk_cons.mono hBG)
        (List.cons_ne_nil _ _))
      hQpoly harc₁ harc₂.reverse hunion hinter hQarc hmeetJ hface.isRegionOf
      (by rw [hsame]; exact hsub₀) z hzF
    -- Either way, the new face is a region of the arc closed up by the ear.
    rcases hcross with hreg | hreg
    · obtain ⟨f, x, y, T, hcyc, hpermT⟩ := exists_spliced_cycle hBG hD1 hpath hab hnew hint
      have hcov : edgesCover drawing (f :: T) =
          edgesCover drawing D₁ ∪ edgesCover drawing D' := by
        rw [edgesCover_perm hpermT, edgesCover_append]
      exact ⟨f, x, y, T, hcyc, hB'.cycle_isSeparating hpoly' hcyc,
        by rw [hcov, hfaceEq]; exact hreg⟩
    · obtain ⟨f, x, y, T, hcyc, hpermT⟩ :=
        exists_spliced_cycle hBG hD2.reverse hpath hab hnew hint
      have hcov : edgesCover drawing (f :: T) =
          edgesCover drawing D₂ ∪ edgesCover drawing D' := by
        rw [edgesCover_perm hpermT, edgesCover_append, edgesCover_reverse]
      exact ⟨f, x, y, T, hcyc, hB'.cycle_isSeparating hpoly' hcyc,
        by rw [hcov, hfaceEq]; exact hreg⟩
  · -- The ear misses this face, which therefore survives unchanged.
    have hdis : Disjoint (face B drawing z) (pointSet (G.pathGraphOf a D') drawing) := by
      rw [h.pointSet_pathGraphOf hpath.isWalk hne, Set.disjoint_left]
      intro w hw hwQ
      refine absurd ?_ hsame
      refine (face_eq_or_disjoint (G := B) (drawing := drawing) z z₀).resolve_right fun hd => ?_
      exact Set.disjoint_left.1 hd hw (hQinter w hwQ (face_subset_exterior _ _ _ hw))
    exact ⟨e, u, v, D, hface.mono hBB' (face_union_eq_of_disjoint hzB hdis)⟩

/-! ## `lem:face-cycles`

"The cycle `C` is 2-connected, so Lemma `lem:relative-ear` builds the graph from `C`. We prove
by induction that every face is exactly one of the two regions bounded by its boundary cycle." -/

/-- **`lem:face-cycles` (face cycles).** Every face of a finite 2-connected polygonal plane
graph has a cycle as its boundary and is one of the two complementary regions of that cycle.

**The statement carries the hypothesis `Schoenflies.CrosscutSplitsRegion`**, which is *not*
proved anywhere: it is the exhaustion clause of `thm:polygonal-crosscut` at a crosscut whose
endpoints need not be corners of the curve, and `main`'s Theorem 2.8 cannot supply it — see the
docstring of `Schoenflies.CrosscutSplitsRegion`. Everything else in the blueprint's proof is
discharged here: the base cycle and its 2-connectivity (`Schoenflies/FaceCycles.lean`), that
its realisation separates the plane (`Graph.IsDrawing.cycle_isSeparating`), that the ear lies in
one face and is a crosscut of it, that all other faces are unchanged, and that the two new
faces are bounded by the two cycles the ear splices onto the two arcs of the old one. -/
theorem face_cycles [G.Finite] (hobl : CrosscutSplitsRegion) (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g)) (hG : G.IsTwoConnected) :
    HasFaceCycles G drawing := by
  have hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x := fun g x => h.not_isLoopAt g x
  obtain ⟨e, u, v, D, w, hcyc⟩ := hG.exists_long_cycle hnl
  refine hG.ear_decomposition (motive := fun B => HasFaceCycles B drawing) hnl
    hcyc.isTwoConnected hcyc.isCycle.cycleGraph_le
    (h.hasFaceCycles_cycleGraph hpoly hcyc.isCycle) ?_
  intro B a b D' _ _ hBG hmot hpathD hab haB hbB hintB
  -- Either the ear is genuinely new, or it is an edge the subgraph already had and adding it
  -- changes nothing.
  rcases ear_edges_notMem_or_union_eq hBG hpathD hab haB hbB hintB with hnew | heq
  · exact h.hasFaceCycles_union hobl hpoly hBG hmot hpathD hab haB hbB hintB hnew
  · rw [heq]; exact hmot

end Graph
