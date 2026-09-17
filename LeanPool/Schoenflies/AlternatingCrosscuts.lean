/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.PolygonalCrosscut
import LeanPool.Schoenflies.Subarc

/-!
# Corollary 2.9: alternating crosscuts intersect

Two crosscuts of a simple closed polygon whose four endpoints alternate around the curve, and
whose interiors lie on the same side of it, must meet.

## What the proof actually uses, and what it therefore assumes

The blueprint's proof is three sentences, and it uses exactly three things about the *second*
crosscut: its interior is connected, its interior lies in the same region of `ℝ² ∖ C` as the
first crosscut's, and its two endpoints are limits of its interior lying one on each of the two
arcs. **Nothing about the second crosscut is polygonal, and nothing about it is simple.** So the
core statement here, `IsPolygonalCrosscut.inter_cover_nonempty`, takes the second crosscut as a
bare preconnected set `Q` — the blueprint's `P₂ ∖ {endpoints}` — with two named points of
`closure Q`. This is not a weakening: the polygonality of `P₂` is a hypothesis of the blueprint's
corollary that its proof never consumes, and dropping it is what lets a consumer apply the
corollary to a *drawn* edge of a plane graph, which is a topological arc.

`IsPolygonalCrosscut.arc_inter_cover_nonempty` is the same statement with `Q` presented as
`P ∖ {w₁, w₂}` for a simple arc `P` from `w₁` to `w₂`, which is the blueprint's own reading; the
two hypotheses about `closure Q` are then automatic (`IsArcBetween.left_mem_closure_diff`).

## The alternation hypothesis

"The endpoints alternate around `C`" is, concretely, that one endpoint of the second crosscut
lies on the first arc and not the second, and the other the other way round. That is how the
core statement takes it. The packaged form `IsPolygonalCrosscut.alternating_inter_nonempty`
takes instead the shape a plane-graph argument produces — two arcs `A, B` meeting exactly in the
two cut points `{p, q}`, one endpoint in `A ∖ {p, q}` and one in `B ∖ {p, q}` — which is
verbatim the conclusion of `Graph.IsK33Config.chords_alternate`, and derives the
non-memberships from `A ∩ B = {p, q}`.

## The "same side" hypothesis, in three interchangeable forms

Theorem 2.8 is parametrized by a reference point `y` in the region of `ℝ² ∖ C` that the first
crosscut does *not* enter, so "the region the crosscut enters" is `farRegion C.carrier y`. The
second crosscut's interior has to lie there too. A consumer may supply that as

* `Q ⊆ farRegion C.carrier y` — the primitive form;
* `Q ⊆ connectedComponentIn C.carrierᶜ z` for some point `z` of the first crosscut off `C`
  — literally "both interiors lie in the same component", which is what a plane-graph argument
  has in hand (`IsPolygonalCrosscut.connectedComponentIn_cover_eq` converts it);
* `Q ⊆ inside C.carrier` with `y ∈ outside C.carrier`, or `Q ⊆ outside C.carrier` with
  `y ∈ inside C.carrier` — the blueprint's literal "the same one of `Int(C)`, `Ext(C)`".

## How the `K(3,3)` argument closes on this

`alternating_inter_nonempty` was written against `Graph.IsK33Config.chords_alternate`, and the
fit was checked: with `hK33 : Graph.IsK33Config G x y e`, `hd : Graph.IsDrawing G drawing`,
`hcross : IsPolygonalCrosscut C J₁ J₂ K a k yref` the realization of the chord `e s (s+1)` as a
crosscut, and `hside` the "same side" clause supplied by
`Graph.IsK33Config.exists_two_chords_same_side`, the last step is one term:

```
obtain ⟨A, B, hAarc, hBarc, hunion, hinter, hw₁, hw₂⟩ := hK33.chords_alternate hd s
obtain ⟨hA, hB⟩ := hreal A B hAarc hBarc hunion
exact hcross.alternating_inter_nonempty hA hB hinter
  (hd.edge_isArcBetween (hK33.isLink (s + 1) (s + 1 + 1))) hside hw₁ hw₂
```

with `hreal` the still-missing realization step: the hexagon, as a polygonal Jordan curve cut
into the two arcs `A` and `B`, presented as a `ClosedPolygon` with `C.arc a k = A` and
`C.arc (a + k) (m + 3 - k) = B`. Everything on either side of that step is in place. Note that
the two arcs must be obtained from `chords_alternate` *before* the realization, since it is
those particular sets the realization has to reproduce.

## Blueprint

* `IsArcBetween.isPreconnected_diff`, `IsArcBetween.left_mem_closure_diff`,
  `IsArcBetween.right_mem_closure_diff` — the interior of an arc is connected and has both
  endpoints in its closure. General-purpose; they belong in `Subarc.lean`.
* `IsPolygonalCrosscut.connectedComponentIn_cover_eq` — the region the crosscut enters is the
  component of any of its points off `C`.
* `IsPolygonalCrosscut.inter_cover_nonempty` — `cor:alternating-crosscuts`, core form.
* `IsPolygonalCrosscut.arc_inter_cover_nonempty` — the same for a second crosscut presented as
  a simple arc.
* `IsPolygonalCrosscut.alternating_inter_nonempty` — the same in the two-arcs shape that
  `Graph.IsK33Config.chords_alternate` produces.
* `IsPolygonalCrosscut.alternating_inter_nonempty_of_same_side` — the same with "both interiors
  lie in one component of `ℝ² ∖ C`" as the side hypothesis.
* `IsPolygonalCrosscut.alternating_inter_nonempty_inside`,
  `…_outside` — the blueprint's literal cases (a) and (b).
* `alternating_crosscuts` — `cor:alternating-crosscuts`, bundled.
-/

open Set unitInterval

namespace Schoenflies

/-! ## The interior of an arc

`openArc f` is `f '' Ioo 0 1`; for an arc between two named points it is the arc minus those
points (`openArc_eq_diff`). The two facts the corollary needs — that the interior is connected,
and that each endpoint lies in its closure — are `Schoenflies.IsArcBetween.isPreconnected_diff`
and `…left_mem_closure_diff` in `Schoenflies/Subarc.lean`, where three modules can share them.
-/

variable {A : Set Plane} {p q : Plane}

/-! ## The corollary -/

variable {m m₁ m₂ : ℕ} {C : ClosedPolygon m} {J₁ : ClosedPolygon m₁} {J₂ : ClosedPolygon m₂}
  {K : List Piece} {a : ZMod (m + 3)} {k : ℕ} {y : Plane}

namespace IsPolygonalCrosscut

variable (h : IsPolygonalCrosscut C J₁ J₂ K a k y)
include h

/-- **The region the crosscut enters is the component of any of its points off `C`.** This is
what lets "both crosscuts lie on the same side" be supplied as a statement about one connected
component, which is the form a plane-graph argument has it in. -/
theorem connectedComponentIn_cover_eq {z : Plane} (hz : z ∈ cover K) (hzC : z ∉ C.carrier) :
    connectedComponentIn C.carrierᶜ z = farRegion C.carrier y :=
  h.regionPairC.left.connectedComponentIn_eq C.isSeparating_carrier
    (diff_subset_farRegion h.avoids ⟨hz, hzC⟩)

/-- **Corollary 2.9, core form.** Let `K` be a crosscut of `C` cutting it at `a` and `a + k`, and
let `Q` be a connected set lying in the same region of `ℝ² ∖ C` as `K` — the interior of a second
crosscut. If `Q` has in its closure a point of the first arc that is not on the second, and a
point of the second arc that is not on the first — that is, if the endpoints of the two crosscuts
alternate — then `Q` meets `K`.

The proof is the blueprint's. By Theorem 2.8 the region minus the first crosscut is the union of
the two cells; `Q`, being connected and (for contradiction) missing the first crosscut, lies in
one of them; and the closure of that cell meets `C` in one arc only
(`IsPolygonalCrosscut.closure_cell_inter₁`), so one of the two named points cannot be there. -/
theorem inter_cover_nonempty {Q : Set Plane} {w₁ w₂ : Plane}
    (hconn : IsPreconnected Q) (hside : Q ⊆ farRegion C.carrier y)
    (hw₁ : w₁ ∈ closure Q) (hw₂ : w₂ ∈ closure Q)
    (hw₁A : w₁ ∈ C.arc a k) (hw₁B : w₁ ∉ C.arc (a + k) (m + 3 - k))
    (hw₂B : w₂ ∈ C.arc (a + k) (m + 3 - k)) (hw₂A : w₂ ∉ C.arc a k) :
    (Q ∩ cover K).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hempty
  -- The second crosscut's interior lies in the region minus the first crosscut.
  have hsub : Q ⊆ farRegion C.carrier y \ cover K :=
    fun z hz => ⟨hside hz, fun hzK => hempty z ⟨hz, hzK⟩⟩
  -- It is nonempty, because it has a point in its closure.
  obtain ⟨z, hz⟩ : Q.Nonempty := by
    by_contra hQ
    rw [Set.not_nonempty_iff_eq_empty] at hQ
    rw [hQ, closure_empty] at hw₁
    simp at hw₁
  have hzcell : z ∈ farRegion J₁.carrier y ∪ farRegion J₂.carrier y := by
    rw [← h.region_eq]; exact hsub hz
  -- Being connected, it lies in a single cell; the closure of that cell meets `C` in one arc.
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

/-- **Corollary 2.9 for a second crosscut presented as a simple arc.** `P` is an arc from `w₁` to
`w₂` whose interior `P ∖ {w₁, w₂}` lies in the same region of `ℝ² ∖ C` as the first crosscut, and
whose endpoints alternate with the first crosscut's around `C`. Then `P` meets the first
crosscut — and in fact it does so in the *interior* of `P`, which is what the conclusion of
`inter_cover_nonempty` says. -/
theorem arc_inter_cover_nonempty {P : Set Plane} {w₁ w₂ : Plane}
    (hP : IsArcBetween P w₁ w₂) (hside : P \ {w₁, w₂} ⊆ farRegion C.carrier y)
    (hw₁A : w₁ ∈ C.arc a k) (hw₁B : w₁ ∉ C.arc (a + k) (m + 3 - k))
    (hw₂B : w₂ ∈ C.arc (a + k) (m + 3 - k)) (hw₂A : w₂ ∉ C.arc a k) :
    (P ∩ cover K).Nonempty := by
  obtain ⟨z, hzQ, hzK⟩ := h.inter_cover_nonempty hP.isPreconnected_diff hside
    hP.left_mem_closure_diff hP.right_mem_closure_diff hw₁A hw₁B hw₂B hw₂A
  exact ⟨z, hzQ.1, hzK⟩

/-- **Corollary 2.9 in the shape a plane-graph argument produces it.** The two arcs of `C` cut off
by the first crosscut are handed over as sets `A, B` meeting exactly in the two cut points
`{p, q}`; the second crosscut is an arc from `w₁` to `w₂` with `w₁` interior to `A` and `w₂`
interior to `B`. This is verbatim the data `Graph.IsK33Config.chords_alternate` returns. -/
theorem alternating_inter_nonempty {A B P : Set Plane} {p q w₁ w₂ : Plane}
    (hA : C.arc a k = A) (hB : C.arc (a + k) (m + 3 - k) = B)
    (hAB : A ∩ B = ({p, q} : Set Plane))
    (hP : IsArcBetween P w₁ w₂) (hside : P \ {w₁, w₂} ⊆ farRegion C.carrier y)
    (hw₁ : w₁ ∈ A \ ({p, q} : Set Plane)) (hw₂ : w₂ ∈ B \ ({p, q} : Set Plane)) :
    (P ∩ cover K).Nonempty := by
  -- A point interior to one arc is off the other, since the two arcs meet only in `{p, q}`.
  refine h.arc_inter_cover_nonempty hP hside (hA ▸ hw₁.1) ?_ (hB ▸ hw₂.1) ?_
  · rw [hB]; exact fun hmem => hw₁.2 (hAB ▸ Set.mem_inter hw₁.1 hmem)
  · rw [hA]; exact fun hmem => hw₂.2 (hAB ▸ Set.mem_inter hmem hw₂.1)

/-- **Corollary 2.9 with "the same side" read as "the same connected component".** The point `z`
is any point of the first crosscut off `C`; the hypothesis is that the interior of the second
crosscut lies in the component of `ℝ² ∖ C` containing `z`. -/
theorem alternating_inter_nonempty_of_same_side {A B P : Set Plane} {p q w₁ w₂ z : Plane}
    (hz : z ∈ cover K) (hzC : z ∉ C.carrier)
    (hA : C.arc a k = A) (hB : C.arc (a + k) (m + 3 - k) = B)
    (hAB : A ∩ B = ({p, q} : Set Plane))
    (hP : IsArcBetween P w₁ w₂)
    (hside : P \ {w₁, w₂} ⊆ connectedComponentIn C.carrierᶜ z)
    (hw₁ : w₁ ∈ A \ ({p, q} : Set Plane)) (hw₂ : w₂ ∈ B \ ({p, q} : Set Plane)) :
    (P ∩ cover K).Nonempty :=
  h.alternating_inter_nonempty hA hB hAB hP
    (hside.trans (h.connectedComponentIn_cover_eq hz hzC).subset) hw₁ hw₂

/-- **Corollary 2.9, case (a):** both crosscuts run inside `C`. The reference point of the first
crosscut lying in `Ext(C)` is exactly the statement that the first crosscut runs inside. -/
theorem alternating_inter_nonempty_inside {A B P : Set Plane} {p q w₁ w₂ : Plane}
    (hy : y ∈ outside C.carrier)
    (hA : C.arc a k = A) (hB : C.arc (a + k) (m + 3 - k) = B)
    (hAB : A ∩ B = ({p, q} : Set Plane))
    (hP : IsArcBetween P w₁ w₂) (hside : P \ {w₁, w₂} ⊆ inside C.carrier)
    (hw₁ : w₁ ∈ A \ ({p, q} : Set Plane)) (hw₂ : w₂ ∈ B \ ({p, q} : Set Plane)) :
    (P ∩ cover K).Nonempty :=
  h.alternating_inter_nonempty hA hB hAB hP
    (hside.trans (C.isSeparating_carrier.farRegion_eq_inside hy).symm.subset) hw₁ hw₂

/-- **Corollary 2.9, case (b):** both crosscuts run outside `C`. -/
theorem alternating_inter_nonempty_outside {A B P : Set Plane} {p q w₁ w₂ : Plane}
    (hy : y ∈ inside C.carrier)
    (hA : C.arc a k = A) (hB : C.arc (a + k) (m + 3 - k) = B)
    (hAB : A ∩ B = ({p, q} : Set Plane))
    (hP : IsArcBetween P w₁ w₂) (hside : P \ {w₁, w₂} ⊆ outside C.carrier)
    (hw₁ : w₁ ∈ A \ ({p, q} : Set Plane)) (hw₂ : w₂ ∈ B \ ({p, q} : Set Plane)) :
    (P ∩ cover K).Nonempty :=
  h.alternating_inter_nonempty hA hB hAB hP
    (hside.trans (C.isSeparating_carrier.farRegion_eq_outside hy).symm.subset) hw₁ hw₂

end IsPolygonalCrosscut

/-- **Corollary 2.9 (alternating crosscuts intersect).** Let `C` be a simple closed polygon and
`K` a polygonal crosscut of it cutting it at the vertices `a` and `a + k`, with `J₁` and `J₂` the
two closed polygons it forms with the two arcs `A` and `B`, and `y` a point of the region of
`ℝ² ∖ C` the crosscut does not enter. Let `P` be a second crosscut: a simple arc from `w₁` to
`w₂`, with interior in the same region of `ℝ² ∖ C` as `K`, and with its two endpoints alternating
with `K`'s around `C` — one interior to `A`, the other interior to `B`. Then the two crosscuts
meet.

The blueprint also assumes `P` polygonal and its four endpoints distinct. Neither is used: the
distinctness of the endpoints is subsumed by `w₁` and `w₂` being interior to different arcs, and
polygonality of `P` plays no part in the argument at all. -/
theorem alternating_crosscuts {A B P : Set Plane} {p q w₁ w₂ : Plane}
    (h : IsPolygonalCrosscut C J₁ J₂ K a k y)
    (hA : C.arc a k = A) (hB : C.arc (a + k) (m + 3 - k) = B)
    (hAB : A ∩ B = ({p, q} : Set Plane))
    (hP : IsArcBetween P w₁ w₂) (hside : P \ {w₁, w₂} ⊆ farRegion C.carrier y)
    (hw₁ : w₁ ∈ A \ ({p, q} : Set Plane)) (hw₂ : w₂ ∈ B \ ({p, q} : Set Plane)) :
    (P ∩ cover K).Nonempty :=
  h.alternating_inter_nonempty hA hB hAB hP hside hw₁ hw₂

end Schoenflies
