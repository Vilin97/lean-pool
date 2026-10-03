/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import LeanPool.Schoenflies.SegmentCut

/-!
# Along one segment: the distance from an end as a coordinate

Everything the polygonal overlay has to say about several collinear segments — which piece
lies inside which, where a piece may end, when two pieces have to coincide — is
one-dimensional: it happens along a single straight segment. This module supplies the
coordinate that makes it ordinary arithmetic. Along a nondegenerate `segment ℝ a b` the
distance from `a` determines the point, and it reads betweenness off as a pair of
inequalities, so a claim about four collinear points becomes a claim about four reals.

No new geometry is needed. `dist_left_lineMap` already says the distance from `a` *is* the
parameter of `AffineMap.lineMap a b`, scaled by the segment's length, and `image_segment`
already says that parametrization carries segments of `ℝ` to segments of the plane. What is
added here is the translation, stated once so that the arithmetic does not have to be redone
at every use.

The two results the module exists for come last, and they are what makes cutting at every
meet enough:

* a piece that meets an overlap and keeps the overlap's ends out of its interior lies inside
  the overlap (`segment_inside_of_ends_outside`);
* two pieces whose interiors meet, each keeping the other's ends out of its interior, are the
  same pair of points (`same_ends_of_meeting_interiors`).

Both are stated **inside one ambient segment**. Collinearity is not optional: a piece crossing
the overlap transversally would meet it and avoid both its ends without lying inside it, so
every point named is a point of one ambient `segment ℝ a b`.

Both are also stated with no orientation asked of the caller. The `_oriented` forms they wrap
are near-end-first, which is what the arithmetic wants; the unoriented forms decide the
orientation themselves, and they are what the overlay uses.

## A note on degenerate pieces

Mathlib's `openSegment ℝ u u` is `{u}`, not `∅`. A degenerate piece therefore has a nonempty
interior, and the strict translation `dist_lt_of_mem_openSegment` genuinely needs `u ≠ v`.
The two headline theorems do *not* ask for it: in each of them a degenerate piece is either
excluded by the hypotheses or settled outright, and that case split lives inside the proof.

## Blueprint

* `segment_inside_of_ends_outside`, `same_ends_of_meeting_interiors` — the separation behind
  the deduplication clause of the polygonal overlay (`lem:polygonal-overlay`, "represent every
  duplicate geometric subsegment only once") and of the subdivision in
  `lem:polygonal-connected` ("delete duplicate subsegments"): once every piece's ends are cut
  points, and so interior to nothing, two pieces that share an interior point coincide instead
  of merely overlapping.
-/

public section

open Set

namespace Schoenflies

variable {a b : Plane}

/-! ### The parametrization of a segment

`AffineMap.lineMap a b` walks from `a` to `b`. It carries a segment of `ℝ` onto the
corresponding piece of `[a, b]`, and it turns the distance from `a` into multiplication by
the segment's length. Those two facts are the whole content of the module; the rest is
arithmetic. -/

/-- The distance from the left endpoint to the point at parameter `t` is `t` times the
segment's length. This is `dist_left_lineMap` with the absolute value discharged. -/
theorem dist_left_lineMap_of_nonneg (a b : Plane) {t : ℝ} (ht : 0 ≤ t) :
    dist a (AffineMap.lineMap a b t) = t * dist a b := by
  rw [dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg ht]

/-- The piece of `[a, b]` spanned by two parameters is the image of the segment they span. -/
theorem segment_lineMap_image (a b : Plane) (p q : ℝ) :
    segment ℝ (AffineMap.lineMap a b p) (AffineMap.lineMap a b q)
      = (AffineMap.lineMap a b : ℝ →ᵃ[ℝ] Plane) '' segment ℝ p q := by
  simp

/-- The same for interiors. -/
theorem openSegment_lineMap_image (a b : Plane) (p q : ℝ) :
    openSegment ℝ (AffineMap.lineMap a b p) (AffineMap.lineMap a b q)
      = (AffineMap.lineMap a b : ℝ →ᵃ[ℝ] Plane) '' openSegment ℝ p q := by
  simp

/-- Every point of `[a, b]` carries a parameter: a number `t ∈ [0, 1]` placing it on the
segment, whose distance from `a` is `t` times the segment's length. This is the only way the
rest of the module looks at a point of the segment. -/
theorem exists_param_of_mem_segment {x : Plane} (hx : x ∈ segment ℝ a b) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ AffineMap.lineMap a b t = x ∧ dist a x = t * dist a b := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
  exact ⟨t, ht0, ht1, rfl, dist_left_lineMap_of_nonneg a b ht0⟩

/-! ### The coordinate -/

/-- Along a nondegenerate segment, the distance from the left endpoint **orders the
parameters**: a nonzero length cancels from `s * ‖b - a‖ ≤ t * ‖b - a‖`. -/
theorem parameter_le_of_distance (hab : a ≠ b) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (h : dist a (AffineMap.lineMap a b s) ≤ dist a (AffineMap.lineMap a b t)) : s ≤ t := by
  have hd : 0 < dist a b := dist_pos.2 hab
  rw [dist_left_lineMap_of_nonneg a b hs, dist_left_lineMap_of_nonneg a b ht] at h
  exact le_of_mul_le_mul_right (by linarith) hd

/-- The distance from `a` determines the point: two points of a nondegenerate `[a, b]` at
equal distance from `a` are equal. -/
theorem eq_of_dist_left_eq (hab : a ≠ b) {x y : Plane} (hx : x ∈ segment ℝ a b)
    (hy : y ∈ segment ℝ a b) (h : dist a x = dist a y) : x = y := by
  have hd : 0 < dist a b := dist_pos.2 hab
  obtain ⟨s, -, -, rfl, hsd⟩ := exists_param_of_mem_segment hx
  obtain ⟨t, -, -, rfl, htd⟩ := exists_param_of_mem_segment hy
  rw [hsd, htd] at h
  rw [mul_right_cancel₀ (ne_of_gt hd) h]

/-! ### Betweenness as a pair of inequalities -/

/-- A point between two points of the segment is between them in distance from `a` as well:
measured from `a`, the nearer end comes first. -/
theorem dist_le_of_mem_segment (hab : a ≠ b) {u v x : Plane} (hu : u ∈ segment ℝ a b)
    (hv : v ∈ segment ℝ a b) (huv : dist a u ≤ dist a v) (hx : x ∈ segment ℝ u v) :
    dist a u ≤ dist a x ∧ dist a x ≤ dist a v := by
  have hd : (0 : ℝ) ≤ dist a b := dist_nonneg
  obtain ⟨p, hp0, -, rfl, hpd⟩ := exists_param_of_mem_segment hu
  obtain ⟨q, hq0, -, rfl, hqd⟩ := exists_param_of_mem_segment hv
  have hpq : p ≤ q := parameter_le_of_distance hab hp0 hq0 huv
  -- The parametrization carries `[p, q]` onto the piece, so `x` has a parameter in `[p, q]`.
  rw [segment_lineMap_image, segment_eq_Icc hpq] at hx
  obtain ⟨t, ⟨hpt, htq⟩, rfl⟩ := hx
  rw [hpd, hqd, dist_left_lineMap_of_nonneg a b (hp0.trans hpt)]
  exact ⟨by nlinarith, by nlinarith⟩

/-- The converse: a point of the segment whose distance from `a` lies between the two ends'
distances lies between the ends. -/
theorem mem_segment_of_dist_le (hab : a ≠ b) {u v x : Plane} (hu : u ∈ segment ℝ a b)
    (hv : v ∈ segment ℝ a b) (hx : x ∈ segment ℝ a b) (h₁ : dist a u ≤ dist a x)
    (h₂ : dist a x ≤ dist a v) : x ∈ segment ℝ u v := by
  obtain ⟨p, hp0, -, rfl, -⟩ := exists_param_of_mem_segment hu
  obtain ⟨q, hq0, -, rfl, -⟩ := exists_param_of_mem_segment hv
  obtain ⟨t, ht0, -, rfl, -⟩ := exists_param_of_mem_segment hx
  have hpt : p ≤ t := parameter_le_of_distance hab hp0 ht0 h₁
  have htq : t ≤ q := parameter_le_of_distance hab ht0 hq0 h₂
  rw [segment_lineMap_image, segment_eq_Icc (hpt.trans htq)]
  exact ⟨t, ⟨hpt, htq⟩, rfl⟩

/-! ### The same translation for interiors

`openSegment ℝ u u = {u}` in Mathlib, so the strict form asks for a nondegenerate piece; its
converse does not, since strict inequalities force nondegeneracy on their own. -/

/-- A point interior to a nondegenerate piece of the segment is strictly between its ends in
distance from `a`. -/
theorem dist_lt_of_mem_openSegment (hab : a ≠ b) {u v x : Plane} (hu : u ∈ segment ℝ a b)
    (hv : v ∈ segment ℝ a b) (huv : u ≠ v) (hor : dist a u ≤ dist a v)
    (hx : x ∈ openSegment ℝ u v) : dist a u < dist a x ∧ dist a x < dist a v := by
  have hd : 0 < dist a b := dist_pos.2 hab
  obtain ⟨p, hp0, -, rfl, hpd⟩ := exists_param_of_mem_segment hu
  obtain ⟨q, hq0, -, rfl, hqd⟩ := exists_param_of_mem_segment hv
  have hpq : p < q :=
    lt_of_le_of_ne (parameter_le_of_distance hab hp0 hq0 hor) fun h => huv (by rw [h])
  rw [openSegment_lineMap_image, openSegment_eq_Ioo hpq] at hx
  obtain ⟨t, ⟨hpt, htq⟩, rfl⟩ := hx
  rw [hpd, hqd, dist_left_lineMap_of_nonneg a b (hp0.trans hpt.le)]
  exact ⟨by nlinarith, by nlinarith⟩

/-- The converse: a point of the segment strictly between the ends in distance from `a` is
interior to the piece they span. -/
theorem mem_openSegment_of_dist_lt (hab : a ≠ b) {u v x : Plane} (hu : u ∈ segment ℝ a b)
    (hv : v ∈ segment ℝ a b) (hx : x ∈ segment ℝ a b) (h₁ : dist a u < dist a x)
    (h₂ : dist a x < dist a v) : x ∈ openSegment ℝ u v := by
  have hd : 0 < dist a b := dist_pos.2 hab
  obtain ⟨p, -, -, rfl, hpd⟩ := exists_param_of_mem_segment hu
  obtain ⟨q, -, -, rfl, hqd⟩ := exists_param_of_mem_segment hv
  obtain ⟨t, -, -, rfl, htd⟩ := exists_param_of_mem_segment hx
  rw [hpd, htd] at h₁
  rw [htd, hqd] at h₂
  have hpt : p < t := lt_of_mul_lt_mul_right h₁ hd.le
  have htq : t < q := lt_of_mul_lt_mul_right h₂ hd.le
  rw [openSegment_lineMap_image, openSegment_eq_Ioo (hpt.trans htq)]
  exact ⟨t, ⟨hpt, htq⟩, rfl⟩

/-! ### Where a point that is not interior to a piece must sit

These two carry the whole one-dimensional argument. A point of the ambient segment kept out
of a piece's interior has to be outside on one side or the other, and knowing which side it
is not settles it. -/

/-- A point of the ambient segment kept out of `[u, v]`'s interior and lying before `v` lies
at or before `u`. -/
theorem dist_le_left_of_notMem_openSegment (hab : a ≠ b) {u v y : Plane}
    (hu : u ∈ segment ℝ a b) (hv : v ∈ segment ℝ a b) (hy : y ∈ segment ℝ a b)
    (hout : y ∉ openSegment ℝ u v) (hlt : dist a y < dist a v) : dist a y ≤ dist a u := by
  by_contra hcon
  exact hout (mem_openSegment_of_dist_lt hab hu hv hy (lt_of_not_ge hcon) hlt)

/-- The mirror: a point of the ambient segment kept out of `[u, v]`'s interior and lying
after `u` lies at or after `v`. -/
theorem le_dist_right_of_notMem_openSegment (hab : a ≠ b) {u v y : Plane}
    (hu : u ∈ segment ℝ a b) (hv : v ∈ segment ℝ a b) (hy : y ∈ segment ℝ a b)
    (hout : y ∉ openSegment ℝ u v) (hlt : dist a u < dist a y) : dist a v ≤ dist a y := by
  by_contra hcon
  exact hout (mem_openSegment_of_dist_lt hab hu hv hy hlt (lt_of_not_ge hcon))

/-! ### What the overlay is after -/

/-- A piece that meets an overlap and keeps the overlap's two ends out of its interior lies
inside the overlap — near-end-first form. -/
theorem segment_inside_of_ends_outside_oriented (hab : a ≠ b) {u v s t x : Plane}
    (hu : u ∈ segment ℝ a b) (hv : v ∈ segment ℝ a b) (hpiece : dist a u ≤ dist a v)
    (hs : s ∈ segment ℝ a b) (ht : t ∈ segment ℝ a b) (hover : dist a s ≤ dist a t)
    (hxp : x ∈ openSegment ℝ u v) (hxo : x ∈ openSegment ℝ s t)
    (hsout : s ∉ openSegment ℝ u v) (htout : t ∉ openSegment ℝ u v) :
    segment ℝ u v ⊆ segment ℝ s t := by
  -- A degenerate overlap is impossible: its only interior point is `s`, which by hypothesis
  -- is not interior to the piece, whereas `x` is.
  rcases eq_or_ne s t with rfl | hst
  · rw [openSegment_same, mem_singleton_iff] at hxo
    rw [← hxo] at hsout
    exact absurd hxp hsout
  -- A degenerate piece is the single point `x`, which already lies in the overlap.
  rcases eq_or_ne u v with rfl | huv
  · rw [openSegment_same, mem_singleton_iff] at hxp
    rw [segment_same, singleton_subset_iff, ← hxp]
    exact openSegment_subset_segment ℝ s t hxo
  obtain ⟨hux, hxv⟩ := dist_lt_of_mem_openSegment hab hu hv huv hpiece hxp
  obtain ⟨hsx, hxt⟩ := dist_lt_of_mem_openSegment hab hs ht hst hover hxo
  -- The overlap starts at or before the piece and ends at or after it.
  have hsu : dist a s ≤ dist a u :=
    dist_le_left_of_notMem_openSegment hab hu hv hs hsout (hsx.trans hxv)
  have hvt : dist a v ≤ dist a t :=
    le_dist_right_of_notMem_openSegment hab hu hv ht htout (hux.trans hxt)
  intro y hy
  have hyab : y ∈ segment ℝ a b := (convex_segment a b).segment_subset hu hv hy
  obtain ⟨huy, hyv⟩ := dist_le_of_mem_segment hab hu hv hpiece hy
  exact mem_segment_of_dist_le hab hs ht hyab (hsu.trans huy) (hyv.trans hvt)

/-- Two pieces of one ambient segment whose interiors meet, each keeping the other's ends out
of its interior, have the same ends — near-end-first form. -/
theorem same_ends_of_meeting_interiors_oriented (hab : a ≠ b) {u v s t x : Plane}
    (hu : u ∈ segment ℝ a b) (hv : v ∈ segment ℝ a b) (hfirst : dist a u ≤ dist a v)
    (hs : s ∈ segment ℝ a b) (ht : t ∈ segment ℝ a b) (hsecond : dist a s ≤ dist a t)
    (hxu : x ∈ openSegment ℝ u v) (hxs : x ∈ openSegment ℝ s t)
    (hsout : s ∉ openSegment ℝ u v) (htout : t ∉ openSegment ℝ u v)
    (huout : u ∉ openSegment ℝ s t) (hvout : v ∉ openSegment ℝ s t) :
    u = s ∧ v = t := by
  -- Neither piece can be degenerate: its only interior point would then be one of its own
  -- ends, which the other piece is required to keep out of its interior.
  rcases eq_or_ne u v with rfl | huv
  · rw [openSegment_same, mem_singleton_iff] at hxu
    rw [← hxu] at huout
    exact absurd hxs huout
  rcases eq_or_ne s t with rfl | hst
  · rw [openSegment_same, mem_singleton_iff] at hxs
    rw [← hxs] at hsout
    exact absurd hxu hsout
  obtain ⟨hux, hxv⟩ := dist_lt_of_mem_openSegment hab hu hv huv hfirst hxu
  obtain ⟨hsx, hxt⟩ := dist_lt_of_mem_openSegment hab hs ht hst hsecond hxs
  -- Each piece's near end lies at or before the other's, so they agree.
  have hsu : dist a s ≤ dist a u :=
    dist_le_left_of_notMem_openSegment hab hu hv hs hsout (hsx.trans hxv)
  have hus : dist a u ≤ dist a s :=
    dist_le_left_of_notMem_openSegment hab hs ht hu huout (hux.trans hxt)
  -- And the same on the far side.
  have hvt : dist a v ≤ dist a t :=
    le_dist_right_of_notMem_openSegment hab hu hv ht htout (hux.trans hxt)
  have htv : dist a t ≤ dist a v :=
    le_dist_right_of_notMem_openSegment hab hs ht hv hvout (hsx.trans hxv)
  exact ⟨eq_of_dist_left_eq hab hu hs (le_antisymm hus hsu),
    eq_of_dist_left_eq hab hv ht (le_antisymm hvt htv)⟩

/-! ### The same two, asking the caller nothing about orientation

A piece is a pair of ends, and which of them is nearer `a` is none of the caller's business —
`segment` and `openSegment` do not care. The oriented forms above are near-end-first because
that is what the arithmetic wants; these decide the orientation themselves. Every hypothesis
is restated in both spellings first, so each of the four cases is just "which way round, then
cite". -/

/-- A piece that meets an overlap and keeps the overlap's two ends out of its interior lies
inside the overlap.

Collinearity is not optional: every point named is a point of one ambient `segment ℝ a b`. A
piece crossing the overlap transversally would meet it and avoid both its ends without lying
inside it. -/
theorem segment_inside_of_ends_outside (hab : a ≠ b) {u v s t x : Plane}
    (hu : u ∈ segment ℝ a b) (hv : v ∈ segment ℝ a b)
    (hs : s ∈ segment ℝ a b) (ht : t ∈ segment ℝ a b)
    (hxp : x ∈ openSegment ℝ u v) (hxo : x ∈ openSegment ℝ s t)
    (hsout : s ∉ openSegment ℝ u v) (htout : t ∉ openSegment ℝ u v) :
    segment ℝ u v ⊆ segment ℝ s t := by
  have hxp' : x ∈ openSegment ℝ v u := by rwa [openSegment_symm ℝ v u]
  have hsout' : s ∉ openSegment ℝ v u := by rwa [openSegment_symm ℝ v u]
  have htout' : t ∉ openSegment ℝ v u := by rwa [openSegment_symm ℝ v u]
  have hxo' : x ∈ openSegment ℝ t s := by rwa [openSegment_symm ℝ t s]
  have hrevPiece : segment ℝ v u = segment ℝ u v := segment_symm ℝ v u
  have hrevOverlap : segment ℝ t s = segment ℝ s t := segment_symm ℝ t s
  rcases le_total (dist a u) (dist a v) with hp | hp <;>
    rcases le_total (dist a s) (dist a t) with ho | ho
  · exact segment_inside_of_ends_outside_oriented hab hu hv hp hs ht ho hxp hxo hsout htout
  · rw [← hrevOverlap]
    exact segment_inside_of_ends_outside_oriented hab hu hv hp ht hs ho hxp hxo' htout hsout
  · rw [← hrevPiece]
    exact segment_inside_of_ends_outside_oriented hab hv hu hp hs ht ho hxp' hxo hsout' htout'
  · rw [← hrevPiece, ← hrevOverlap]
    exact segment_inside_of_ends_outside_oriented hab hv hu hp ht hs ho hxp' hxo' htout' hsout'

/-- Two pieces of one ambient segment whose interiors meet, each keeping the other's ends out
of its interior, are the same pair of points — in one order or the other.

This is the separation the deduplication clause is for: overlapping collinear pieces cannot
be pulled apart by cutting, and after enough cuts they coincide instead. -/
theorem same_ends_of_meeting_interiors (hab : a ≠ b) {u v s t x : Plane}
    (hu : u ∈ segment ℝ a b) (hv : v ∈ segment ℝ a b)
    (hs : s ∈ segment ℝ a b) (ht : t ∈ segment ℝ a b)
    (hxu : x ∈ openSegment ℝ u v) (hxs : x ∈ openSegment ℝ s t)
    (hsout : s ∉ openSegment ℝ u v) (htout : t ∉ openSegment ℝ u v)
    (huout : u ∉ openSegment ℝ s t) (hvout : v ∉ openSegment ℝ s t) :
    (u = s ∧ v = t) ∨ (u = t ∧ v = s) := by
  have hxu' : x ∈ openSegment ℝ v u := by rwa [openSegment_symm ℝ v u]
  have hxs' : x ∈ openSegment ℝ t s := by rwa [openSegment_symm ℝ t s]
  have hsout' : s ∉ openSegment ℝ v u := by rwa [openSegment_symm ℝ v u]
  have htout' : t ∉ openSegment ℝ v u := by rwa [openSegment_symm ℝ v u]
  have huout' : u ∉ openSegment ℝ t s := by rwa [openSegment_symm ℝ t s]
  have hvout' : v ∉ openSegment ℝ t s := by rwa [openSegment_symm ℝ t s]
  rcases le_total (dist a u) (dist a v) with hp | hp <;>
    rcases le_total (dist a s) (dist a t) with ho | ho
  · exact Or.inl (same_ends_of_meeting_interiors_oriented hab hu hv hp hs ht ho hxu hxs
      hsout htout huout hvout)
  · exact Or.inr (same_ends_of_meeting_interiors_oriented hab hu hv hp ht hs ho hxu hxs'
      htout hsout huout' hvout')
  · obtain ⟨h₁, h₂⟩ := same_ends_of_meeting_interiors_oriented hab hv hu hp hs ht ho hxu' hxs
      hsout' htout' hvout huout
    exact Or.inr ⟨h₂, h₁⟩
  · obtain ⟨h₁, h₂⟩ := same_ends_of_meeting_interiors_oriented hab hv hu hp ht hs ho hxu' hxs'
      htout' hsout' hvout' huout'
    exact Or.inl ⟨h₂, h₁⟩

end Schoenflies
