/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Graph.VertexSquares
public import LeanPool.Schoenflies.Graph.CycleJordan
public import LeanPool.Schoenflies.PolyLocal
public import LeanPool.Schoenflies.Polygonal
public import LeanPool.Schoenflies.Concatenate

/-!
# The polygonal redrawing of a finite plane graph

Bricks B7 and B8 of `lem:polygonal-redrawing`, and the headline theorem: every finite plane
graph is drawn again, on the same abstract graph and the same vertices, with polygonal edges.
Since the vertices of a plane graph *are* plane points and the redrawing leaves them where
they are, the blueprint's "isomorphic plane drawing" is the identity isomorphism, and no
`Graph.IsIsomorphism` is built or needed.

## Three things the design did not have, and this module supplies

**Simple polygonal paths.** `Graph.IsDrawing.edge_param` asks for an *injective*
parametrisation, and brick B6 delivers only a `poly` vertex list, which may cross itself. The
blueprint's Lemma 1.1 makes the path simple "by subdividing at self-intersections and taking a
simple path in the resulting finite graph"; `Schoenflies/PolyPath.lean` deferred that half, and
without it brick B8 cannot discharge the drawing condition at all. `IsArcList` and
`PolyReaches.exists_arcList` supply it, by an induction over the inductive relation rather than
by an overlay graph: at each `step` the new segment is run *backwards* from its far end and
stopped the first time it meets the polygon already built, and the old path is truncated
there. That needs no plane geometry beyond `exists_first_mem_Icc`, and in particular no
connectivity theorem for the overlay graph.

**The contact point is on the frame.** `Graph.IsDrawing.exists_core` states that the core meets
the square about a vertex in exactly one point, but not that this point is on the square's
boundary — and if it were interior the core would not lie in the plane minus the open squares,
which is the carrier brick B5 speaks about, nor would the radial segment from the vertex reach
it. `Plane.supDist_eq_of_inter_eq_singleton` closes the gap by connectedness: an interior
contact point would make the core's trace on the square a nonempty proper clopen piece.

**Radial arithmetic.** That two radials of one square meet only at the centre, and that a
radial meets the plane minus the open squares only at its far end, are both the statement that
the sup distance to the centre is a faithful coordinate along a radius
(`Plane.supDist_lt_of_mem_segment`, `Plane.radial_meet`). These are the "distinct radials in
one square meet only at `v`" and "radials meet the replacement paths only at the designated
boundary points" of brick B8's design, and neither is free.

## Blueprint

Bricks B7 and B8 of `lem:polygonal-redrawing` (H6), and the lemma itself.

* `Plane.supNorm_smul`, `Plane.supDist_add_smul`, `Plane.supDist_lt_of_mem_segment`,
  `Plane.segment_subset_closedSquare`, `Plane.radial_meet` — the radial segments of brick B8.
* `Plane.supDist_eq_of_inter_eq_singleton` — a core's contact point lies on the frame of its
  square; the missing clause of brick B4.
* `lastP`, `poly_snoc`, `IsArcList` — a **simple** polygonal path, in the `u :: t`
  presentation that keeps every statement free of dependent nonemptiness proofs.
* `isArcBetween_poly` — the carrier of a simple polygonal path is an arc between its ends.
* `IsArcList.truncate`, `IsArcList.snoc` — cutting one at any of its points, and extending one
  by a segment that touches it only at its last vertex.
* `PolyReaches.exists_arcList` — **every polygonal path contains a simple one**; the deferred
  half of Lemma 1.1.
* `Graph.polygonal_redrawing` — `lem:polygonal-redrawing`, with bricks B7 and B8 inside its
  proof: the `ε` making the tubes about the cores pairwise disjoint, the component `U e` of
  the core inside its tube, and the assembly of radial, replacement path and radial.
-/

@[expose] public section

open Metric Set unitInterval
open scoped Graph

namespace Schoenflies

/-! ### Radial segments in a square

A segment from the centre of a square to a point of its boundary frame leaves the open square
only at its far end, and two such segments in one square meet only at the centre. Those two
facts are the whole of the "radials" half of brick B8, and both are statements about the sup
distance scaling along a segment. -/

namespace Plane

theorem supNorm_smul (a : ℝ) (x : Plane) : supNorm (a • x) = |a| * supNorm x := by
  have h0 : (a • x) 0 = a * x 0 := by simp
  have h1 : (a • x) 1 = a * x 1 := by simp
  simp only [supNorm, h0, h1, abs_mul]
  exact (mul_max_of_nonneg _ _ (abs_nonneg a)).symm

theorem supDist_add_smul (c u : Plane) (t : ℝ) : supDist (c + t • u) c = |t| * supNorm u := by
  have h : c + t • u - c = t • u := by abel
  rw [supDist, h, supNorm_smul]

/-- Everything on the segment from `c` to `p` except `p` itself is strictly nearer to `c` than
`p` is, in the sup metric. This is why a radial segment meets the frame of its square only at
its far end. -/
theorem supDist_lt_of_mem_segment {c p x : Plane} (hpc : 0 < supDist p c)
    (hx : x ∈ segment ℝ c p) (hne : x ≠ p) : supDist x c < supDist p c := by
  rw [segment_eq_image' ℝ c p] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  have hxt' : c + t • (p - c) = x := hxt
  have hval : supDist x c = t * supDist p c := by
    rw [← hxt', supDist_add_smul, abs_of_nonneg ht.1]; rfl
  have ht1 : t < 1 := by
    rcases eq_or_lt_of_le ht.2 with heq | h
    · refine absurd ?_ hne
      rw [← hxt', heq]
      module
    · exact h
  rw [hval]
  nlinarith

/-- A radial segment stays inside its square. -/
theorem openSquare_subset_closedSquare (c : Plane) (r : ℝ) :
    openSquare c r ⊆ closedSquare c r := fun x hx => show supDist x c ≤ r from le_of_lt hx

theorem segment_subset_closedSquare {c p : Plane} {r : ℝ} (hr : 0 ≤ r)
    (hpc : supDist p c ≤ r) : segment ℝ c p ⊆ closedSquare c r :=
  (convex_closedSquare c r).segment_subset (mem_closedSquare_self c hr) hpc

/-- **Two radials meet only at the centre.** Two segments from the centres of two squares of a
common radius `r` to points of their frames meet only where they can: if the centres are
distinct the squares are disjoint, and if they agree the two far ends are pinned by the sup
distance, which is injective along a radius. -/
theorem radial_meet {c c' p p' z : Plane} {r : ℝ} (hr : 0 < r) (hp : supDist p c = r)
    (hp' : supDist p' c' = r) (hpp' : p ≠ p')
    (hdisj : c ≠ c' → Disjoint (closedSquare c r) (closedSquare c' r))
    (hz : z ∈ segment ℝ c p) (hz' : z ∈ segment ℝ c' p') : z = c := by
  rcases eq_or_ne c c' with rfl | hcc'
  · -- One square: the two representations of `z` have the same parameter, which must be `0`.
    rw [segment_eq_image' ℝ c p] at hz
    rw [segment_eq_image' ℝ c p'] at hz'
    obtain ⟨t, ht, hzt⟩ := hz
    obtain ⟨s, hs, hzs⟩ := hz'
    have hzt' : c + t • (p - c) = z := hzt
    have hzs' : c + s • (p' - c) = z := hzs
    have h₁ : supDist z c = t * r := by
      rw [← hzt', supDist_add_smul, abs_of_nonneg ht.1, ← hp]; rfl
    have h₂ : supDist z c = s * r := by
      rw [← hzs', supDist_add_smul, abs_of_nonneg hs.1, ← hp']; rfl
    have hEq : t = s := mul_right_cancel₀ hr.ne' (h₁.symm.trans h₂)
    subst hEq
    have hsmul : t • (p - c) = t • (p' - c) := add_left_cancel (hzt'.trans hzs'.symm)
    have hkey : t • (p - p') = 0 := by linear_combination (norm := module) hsmul
    rcases smul_eq_zero.1 hkey with ht0 | hpp
    · rw [← hzt', ht0]; module
    · exact absurd (sub_eq_zero.1 hpp) hpp'
  · exact absurd (Set.disjoint_left.1 (hdisj hcc')
      (segment_subset_closedSquare hr.le hp.le hz)
      (segment_subset_closedSquare hr.le hp'.le hz')) not_false

end Plane

/-! ### Simple polygonal paths

`poly vs` is the carrier of a vertex list, and a general vertex list crosses itself. The
drawing condition of a plane graph asks for an *injective* parametrisation, so what brick B8
needs is a vertex list whose carrier is an **arc**. `IsArcList` is exactly the condition that
makes the concatenation of `Schoenflies/Concatenate.lean` apply at every step: consecutive
vertices differ, and each segment meets the rest of the polygon only at the vertex they
share.

The work of this section is `PolyReaches.exists_arcList`: *any* polygonal path inside a set
contains a simple one with the same ends. That is the half of the blueprint's Lemma 1.1 which
`Schoenflies/PolyPath.lean` deferred, and without it nothing downstream can discharge
`Graph.IsDrawing`. The induction is over the inductive relation `PolyReaches`, and the step
takes the *first* point at which the new segment, run backwards from its far end, meets the
polygon already built, truncates there and appends. -/

/-- The last vertex of a nonempty vertex list, with the nonemptiness discharged by the
`cons`. Carrying the list in the form `u :: t` removes every dependent proof argument from
the statements below. -/
def lastP (u : Plane) (t : List Plane) : Plane := (u :: t).getLast (List.cons_ne_nil u t)

@[simp] theorem lastP_nil (u : Plane) : lastP u [] = u := rfl

@[simp] theorem lastP_cons (u v : Plane) (t : List Plane) : lastP u (v :: t) = lastP v t :=
  List.getLast_cons (List.cons_ne_nil v t)

theorem lastP_append : ∀ (u : Plane) (t : List Plane) (z : Plane), lastP u (t ++ [z]) = z
  | _, [], _ => rfl
  | u, v :: t, z => by
    rw [List.cons_append, lastP_cons, lastP_append v t z]

theorem lastP_mem_poly (u : Plane) (t : List Plane) : lastP u t ∈ poly (u :: t) :=
  getLast_mem_poly (List.cons_ne_nil u t)

/-- Appending one vertex, in the `u :: t` presentation. -/
theorem poly_snoc (u : Plane) (t : List Plane) (z : Plane) :
    poly (u :: (t ++ [z])) = poly (u :: t) ∪ segment ℝ (lastP u t) z := by
  rw [← List.cons_append, poly_concat (List.cons_ne_nil u t) z]
  rfl

/-- A **simple** polygonal path: consecutive vertices are distinct, and each segment meets the
rest of the polygon exactly in the vertex where they are joined. That is precisely the
hypothesis `Schoenflies.IsArcBetween.concatenate` asks for, one step at a time. -/
def IsArcList : List Plane → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => u ≠ v ∧ segment ℝ u v ∩ poly (v :: rest) = {v} ∧ IsArcList (v :: rest)

@[simp] theorem isArcList_nil : IsArcList [] := trivial

@[simp] theorem isArcList_singleton (v : Plane) : IsArcList [v] := trivial

theorem isArcList_cons_cons {u v : Plane} {rest : List Plane} :
    IsArcList (u :: v :: rest) ↔
      u ≠ v ∧ segment ℝ u v ∩ poly (v :: rest) = {v} ∧ IsArcList (v :: rest) := Iff.rfl

/-- The carrier of a simple polygonal path is an arc between its ends. The induction glues one
segment at a time with `Schoenflies.IsArcBetween.concatenate`; the meeting hypothesis is the
second clause of `IsArcList`. -/
theorem isArcBetween_poly : ∀ (u v : Plane) (rest : List Plane), IsArcList (u :: v :: rest) →
    IsArcBetween (poly (u :: v :: rest)) u (lastP v rest)
  | u, v, [], h => by
    rw [poly_cons_cons, poly_singleton]
    have : segment ℝ u v ∪ {v} = segment ℝ u v :=
      union_eq_self_of_subset_right (singleton_subset_iff.2 (right_mem_segment ℝ u v))
    rw [this]
    exact isArcBetween_segment h.1
  | u, v, w :: rest, h => by
    rw [poly_cons_cons, lastP_cons]
    refine (isArcBetween_segment h.1).concatenate (isArcBetween_poly v w rest h.2.2) ?_
    intro z hz hz'
    have : z ∈ segment ℝ u v ∩ poly (v :: w :: rest) := ⟨hz, hz'⟩
    rw [h.2.1] at this
    exact this

/-- **Truncation.** A simple polygonal path may be cut at any point of its carrier: the piece
up to that point is again a simple polygonal path, inside the original one. -/
theorem IsArcList.truncate : ∀ (u : Plane) (t : List Plane), IsArcList (u :: t) →
    ∀ {w : Plane}, w ∈ poly (u :: t) →
      ∃ t' : List Plane, IsArcList (u :: t') ∧ poly (u :: t') ⊆ poly (u :: t) ∧
        lastP u t' = w
  | u, [], _, w, hw => by
    rw [poly_singleton, mem_singleton_iff] at hw
    exact ⟨[], isArcList_singleton u, subset_rfl, hw.symm⟩
  | u, v :: rest, h, w, hw => by
    by_cases hrest : w ∈ poly (v :: rest)
    · obtain ⟨rest', hlist, hsub, hlast⟩ := IsArcList.truncate v rest h.2.2 hrest
      refine ⟨v :: rest', ⟨h.1, ?_, hlist⟩, ?_, by rw [lastP_cons, hlast]⟩
      · refine Subset.antisymm ?_ ?_
        · exact fun z hz => h.2.1 ▸ ⟨hz.1, hsub hz.2⟩
        · rintro z rfl
          exact ⟨right_mem_segment ℝ u z, head_mem_poly (List.cons_ne_nil z rest')⟩
      · rw [poly_cons_cons, poly_cons_cons]
        exact union_subset_union_right _ hsub
    · rw [poly_cons_cons] at hw
      have hseg : w ∈ segment ℝ u v := hw.resolve_right hrest
      rcases eq_or_ne w u with heq | hwu
      · refine ⟨[], isArcList_singleton u, ?_, heq.symm⟩
        rw [poly_singleton, poly_cons_cons]
        exact singleton_subset_iff.2 (Or.inl (left_mem_segment ℝ u v))
      · refine ⟨[w], ⟨Ne.symm hwu, ?_, isArcList_singleton w⟩, ?_, rfl⟩
        · rw [poly_singleton]
          exact Subset.antisymm inter_subset_right
            (singleton_subset_iff.2 ⟨right_mem_segment ℝ u w, rfl⟩)
        · rw [poly_cons_cons, poly_singleton, poly_cons_cons]
          have : segment ℝ u w ∪ {w} = segment ℝ u w :=
            union_eq_self_of_subset_right (singleton_subset_iff.2 (right_mem_segment ℝ u w))
          rw [this]
          exact subset_union_of_subset_left
            ((convex_segment u v).segment_subset (left_mem_segment ℝ u v) hseg) _

/-- **Extension.** A simple polygonal path may be extended by a segment that meets it only at
its own last vertex. -/
theorem IsArcList.snoc : ∀ (u : Plane) (t : List Plane), IsArcList (u :: t) →
    ∀ {z : Plane}, z ≠ lastP u t →
      segment ℝ (lastP u t) z ∩ poly (u :: t) = {lastP u t} →
      IsArcList (u :: (t ++ [z]))
  | u, [], _, z, hz, _ => by
    refine ⟨Ne.symm hz, ?_, isArcList_singleton z⟩
    rw [poly_singleton]
    exact Subset.antisymm inter_subset_right
      (singleton_subset_iff.2 ⟨right_mem_segment ℝ u z, rfl⟩)
  | u, v :: rest, h, z, hz, hmeet => by
    rw [List.cons_append]
    refine ⟨h.1, ?_, ?_⟩
    · -- The first segment still meets the rest only at `v`: the new piece is barred from it
      -- because it meets the whole old polygon only at its last vertex, which lies on the
      -- rest and hence, if it were on the first segment, would have to be `v`.
      rw [lastP_cons] at hz hmeet
      rw [poly_snoc]
      refine Subset.antisymm ?_ ?_
      · rintro y ⟨hy1, hy2 | hy2⟩
        · exact h.2.1 ▸ ⟨hy1, hy2⟩
        · have hylast : y = lastP v rest := by
            have : y ∈ segment ℝ (lastP v rest) z ∩ poly (u :: v :: rest) :=
              ⟨hy2, Or.inl hy1⟩
            rw [hmeet] at this
            exact this
          have : lastP v rest ∈ segment ℝ u v ∩ poly (v :: rest) :=
            ⟨hylast ▸ hy1, lastP_mem_poly v rest⟩
          rw [h.2.1] at this
          rw [hylast]
          exact this
      · rintro y rfl
        exact ⟨right_mem_segment ℝ u y, Or.inl (head_mem_poly (List.cons_ne_nil y rest))⟩
    · rw [lastP_cons] at hz hmeet
      refine IsArcList.snoc v rest h.2.2 hz (Subset.antisymm ?_ ?_)
      · exact fun y hy => hmeet ▸ ⟨hy.1, Or.inr hy.2⟩
      · exact singleton_subset_iff.2
          ⟨left_mem_segment ℝ _ _, lastP_mem_poly v rest⟩

/-- **Every polygonal path contains a simple one.** This is the half of Lemma 1.1 that
`Schoenflies/PolyPath.lean` deferred, and the reason brick B8 can discharge the injectivity
clause of `Graph.IsDrawing`.

The induction is on `PolyReaches`. At a `step` the new segment is run *backwards* from its far
end and stopped the first time it touches the polygon already built — `exists_first_mem_Icc`
of `Schoenflies/Graph/VertexSquares.lean` is exactly that. The old path is truncated there and
the stub appended; the stub meets the truncation only at the join, because everything strictly
before the stopping parameter misses the old polygon altogether. -/
theorem PolyReaches.exists_arcList {S : Set Plane} {x y : Plane} (h : PolyReaches S x y) :
    ∃ t : List Plane, IsArcList (x :: t) ∧ poly (x :: t) ⊆ S ∧ lastP x t = y := by
  induction h with
  | refl hx => exact ⟨[], isArcList_singleton x, by simpa using hx, rfl⟩
  | @step w z _ hseg ih =>
    obtain ⟨t, hlist, hsub, hlast⟩ := ih
    -- The straight run from `z` back to `w`, stopped the first time it meets the old polygon.
    set γ : ℝ → Plane := fun a => z + a • (w - z) with hγ
    have hγc : ContinuousOn γ (Icc 0 1) := (by fun_prop : Continuous γ).continuousOn
    have hγ1 : γ 1 = w := by simp [hγ]
    have hclosed : IsClosed (poly (x :: t)) := (isCompact_poly _).isClosed
    have hmem1 : γ 1 ∈ poly (x :: t) := by
      rw [hγ1, ← hlast]; exact lastP_mem_poly x t
    obtain ⟨s, hs, -, hsmem, hbefore⟩ :=
      exists_first_mem_Icc hγc hclosed (right_mem_Icc.2 zero_le_one) hmem1
    -- Everything on the stub, bar its far end, is before the stopping parameter.
    have himg : segment ℝ (γ s) z ⊆ γ '' Icc 0 s := by
      rw [segment_symm, segment_eq_image' ℝ z (γ s)]
      rintro u ⟨θ, hθ, rfl⟩
      refine ⟨θ * s, ⟨mul_nonneg hθ.1 hs.1, mul_le_of_le_one_left hs.1 hθ.2⟩, ?_⟩
      simp only [hγ]
      module
    have hstub : ∀ u ∈ segment ℝ (γ s) z, u ∈ poly (x :: t) → u = γ s := by
      intro u hu humem
      obtain ⟨a, ha, rfl⟩ := himg hu
      rcases eq_or_lt_of_le ha.2 with heq | hlt
      · rw [heq]
      · exact absurd humem (hbefore a ⟨ha.1, le_trans ha.2 hs.2⟩ hlt)
    -- The stub lies on the new segment, since `γ s` does.
    have hγs_seg : γ s ∈ segment ℝ z w := by
      rw [segment_eq_image' ℝ z w]
      exact ⟨s, hs, rfl⟩
    have hsegzw : segment ℝ z w ⊆ S := by rw [segment_symm]; exact hseg
    have hstubsub : segment ℝ (γ s) z ⊆ S :=
      Subset.trans ((convex_segment z w).segment_subset hγs_seg (left_mem_segment ℝ z w)) hsegzw
    obtain ⟨t', hlist', hsub', hlast'⟩ := IsArcList.truncate x t hlist hsmem
    rcases eq_or_ne z (γ s) with heq | hzne
    · exact ⟨t', hlist', hsub'.trans hsub, by rw [hlast']; exact heq.symm⟩
    · refine ⟨t' ++ [z], ?_, ?_, lastP_append x t' z⟩
      · refine IsArcList.snoc x t' hlist' (by rw [hlast']; exact hzne) ?_
        rw [hlast']
        refine Subset.antisymm (fun u hu => hstub u hu.1 (hsub' hu.2)) ?_
        exact singleton_subset_iff.2 ⟨left_mem_segment ℝ _ _, hlast' ▸ lastP_mem_poly x t'⟩
      · rw [poly_snoc, hlast']
        exact union_subset (hsub'.trans hsub) hstubsub

/-! ### The contact point of a core sits on the frame of its square

`Graph.IsDrawing.exists_core` says the core meets the square about `v` in exactly one point.
That point is on the *frame* of the square and not in its interior, which is what puts the
core in the plane minus the open squares and what makes the radial segment reach the core.
The argument is connectedness, not the parametrisation: were the contact point interior, it
would be a nonempty proper clopen piece of the core. -/

namespace Plane

/-- If a connected set meets a closed square in exactly one point and is not contained in that
square, the meeting point is on the frame: its sup distance to the centre is exactly the
radius. -/
theorem supDist_eq_of_inter_eq_singleton {K : Set Plane} {c p q : Plane} {r : ℝ}
    (hK : IsPreconnected K) (hp : K ∩ closedSquare c r = {p}) (hq : q ∈ K)
    (hqc : q ∉ closedSquare c r) : supDist p c = r := by
  have hpmem : p ∈ K ∩ closedSquare c r := by rw [hp]; rfl
  refine le_antisymm hpmem.2 (le_of_not_gt fun hlt => ?_)
  obtain ⟨w, hwK, hw1, hw2⟩ := hK (openSquare c r) (closedSquare c r)ᶜ
    (isOpen_openSquare c r) (isClosed_closedSquare c r).isOpen_compl
    (fun z hz => by
      by_cases hzc : z ∈ closedSquare c r
      · refine Or.inl ?_
        have hzp : z ∈ K ∩ closedSquare c r := ⟨hz, hzc⟩
        rw [hp, mem_singleton_iff] at hzp
        rw [hzp]
        exact hlt
      · exact Or.inr hzc)
    ⟨p, hpmem.1, hlt⟩ ⟨q, hq, hqc⟩
  exact hw2 (openSquare_subset_closedSquare c r hw1)

end Plane

end Schoenflies

/-! ### Bricks B7 and B8, and the redrawing itself -/

open Schoenflies

namespace Graph

/-- Join a polygonal path to disjoint radial segments meeting its ambient carrier
only at their endpoints. The graph redrawing applies this independently to each edge. -/
theorem exists_polygonal_arc_with_radials {U M : Set Plane} {a b p q : Plane}
    (hpath : PolyReaches U p q) (hUM : U ⊆ M) (hAP : a ≠ p) (hBQ : b ≠ q)
    (hnear : ∀ z ∈ segment ℝ a p, z ∈ M → z = p)
    (hfar : ∀ z ∈ segment ℝ b q, z ∈ M → z = q)
    (hdisjoint : Disjoint (segment ℝ a p) (segment ℝ b q)) :
    ∃ g : ℝ → Plane, ContinuousOn g I ∧ InjOn g I ∧ g 0 = a ∧ g 1 = b ∧
      IsPolygonal (g '' I) ∧ g '' I ⊆ segment ℝ a p ∪ U ∪ segment ℝ b q := by
  obtain ⟨t, hlist, hsub, hlast⟩ := (hpath).exists_arcList
  have hpaM : ∀ z ∈ poly (p :: t), z ∈ M := fun z hz => hUM (hsub hz)
  have hpbpoly : q ∈ poly (p :: t) := hlast ▸ lastP_mem_poly (p) t
  -- The far radial meets the straightened path only at the far contact point.
  have hmeetQ : segment ℝ (q) (b) ∩ poly (p :: t) = {q} := by
    refine Subset.antisymm (fun z hz => ?_) ?_
    · rw [segment_symm] at hz
      exact hfar z hz.1 (hpaM z hz.2)
    · exact singleton_subset_iff.2 ⟨left_mem_segment ℝ _ _, hpbpoly⟩
  have hlist2 : IsArcList (p :: (t ++ [b])) :=
    IsArcList.snoc (p) t hlist (by rw [hlast]; exact hBQ)
      (by rw [hlast]; exact hmeetQ)
  have hpolysnoc : poly (p :: (t ++ [b]))
      = poly (p :: t) ∪ segment ℝ (q) (b) := by
    rw [poly_snoc, hlast]
  -- The near radial meets the rest only at the near contact point: the straightened path
  -- lives in `M`, and the far radial lives in the other square.
  have hmeetP : segment ℝ (a) (p) ∩ poly (p :: (t ++ [b])) = {p} := by
    rw [hpolysnoc]
    refine Subset.antisymm ?_ ?_
    · rintro z ⟨hz1, hz2 | hz2⟩
      · exact hnear z hz1 (hpaM z hz2)
      · rw [segment_symm] at hz2
        exact False.elim (Set.disjoint_left.1 hdisjoint hz1 hz2)
    · exact singleton_subset_iff.2 ⟨right_mem_segment ℝ _ _,
        Or.inl (head_mem_poly (List.cons_ne_nil _ _))⟩
  have hlist3 : IsArcList (a :: p :: (t ++ [b])) := ⟨hAP, hmeetP, hlist2⟩
  have harcb := isArcBetween_poly (a) (p) (t ++ [b]) hlist3
  rw [lastP_append] at harcb
  obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := harcb
  refine ⟨g, hgc, hgi, hg0, hg1, ⟨_, hgim⟩, ?_⟩
  rw [hgim, poly_cons_cons, hpolysnoc]
  refine union_subset (subset_union_of_subset_left subset_union_left _)
    (union_subset (hsub.trans (subset_union_of_subset_left subset_union_right _)) ?_)
  rw [segment_symm]
  exact subset_union_right

/-- **The polygonal redrawing of a finite plane graph** (`lem:polygonal-redrawing`). A finite
plane graph is drawn again, on the *same* abstract graph and the *same* vertices, with every
edge a polygonal arc. The blueprint speaks of an isomorphic plane drawing; since the vertices
of a plane graph are plane points and the redrawing leaves them where they are, the
isomorphism is the identity and no `Graph.IsIsomorphism` appears.

The construction, in the order the proof takes it.

* **The squares** (brick B2). One radius `r` serves every vertex: the square about a vertex
  meets no other vertex, meets no arc of an edge it is not incident with, and distinct squares
  are disjoint.
* **The cores** (brick B4). Each edge's arc, cut back to what lies between its last exit from
  the square at one end and its first entry into the square at the other. A core carries no
  vertex, so distinct cores are disjoint; and — `Plane.supDist_eq_of_inter_eq_singleton` — its
  two contact points sit on the *frames* of the two squares, so the core lies in the plane `M`
  minus the open squares.
* **The tubes** (brick B7). One `ε` makes the `ε`-tubes about the cores pairwise disjoint, by
  compact separation and the single-bound lemma. `U e` is the connected component, inside
  `M ∩ tube e`, of the core; it is relatively open in `M`, so the strengthened brick B5 joins
  the two contact points by a polygonal path *inside* `U e`.
* **The assembly** (brick B8). The path is straightened to a simple one
  (`Schoenflies.PolyReaches.exists_arcList`), then a radial segment is prepended at each end.
  A radial meets `M` only at its far end and two radials meet only at their common centre, so
  the three pieces glue to an arc; `Schoenflies.isArcBetween_poly` produces the
  parametrisation that `IsDrawing.edge_param` demands. -/
theorem polygonal_redrawing {β : Type*} (G : Graph Plane β) [G.Finite]
    (drawing : β → ℝ → Plane) (h : IsDrawing G drawing) :
    ∃ redrawing : β → ℝ → Plane, IsDrawing G redrawing ∧
      ∀ e ∈ E(G), IsPolygonal (edgeArc redrawing e) := by
  classical
  obtain ⟨r, hr, hvert, hnoninc, hsqdisj⟩ := h.exists_vertexSquares
  -- The core of every edge, with the edge's two ends and the core's two contact points.
  have hdata : ∀ e ∈ E(G), ∃ a b p q : Plane, ∃ Kc : Set Plane,
      G.IsLink e a b ∧ Kc ⊆ edgeArc drawing e ∧ IsCompact Kc ∧ IsArcBetween Kc p q ∧
        Kc ∩ Plane.closedSquare a r = {p} ∧ Kc ∩ Plane.closedSquare b r = {q} ∧
        Disjoint Kc V(G) := by
    intro e he
    obtain ⟨a, b, hl⟩ := G.exists_isLink_of_mem_edgeSet he
    obtain ⟨Kc, p, q, h1, h2, h3, h4, h5, h6⟩ :=
      h.exists_core hr hl (hsqdisj a hl.left_mem b hl.right_mem (h.ne_of_isLink hl))
    exact ⟨a, b, p, q, Kc, hl, h1, h2, h3, h4, h5, h6⟩
  choose! va vb pa pb core hlink hcoresub hcorecpt hcorearc hcoreA hcoreB hcoreV using hdata
  have hvaV : ∀ e ∈ E(G), va e ∈ V(G) := fun e he => (hlink e he).left_mem
  have hvbV : ∀ e ∈ E(G), vb e ∈ V(G) := fun e he => (hlink e he).right_mem
  have hvab : ∀ e ∈ E(G), va e ≠ vb e := fun e he => h.ne_of_isLink (hlink e he)
  have hpamem : ∀ e ∈ E(G), pa e ∈ core e ∩ Plane.closedSquare (va e) r := by
    intro e he; rw [hcoreA e he]; rfl
  have hpbmem : ∀ e ∈ E(G), pb e ∈ core e ∩ Plane.closedSquare (vb e) r := by
    intro e he; rw [hcoreB e he]; rfl
  have hcoreconn : ∀ e ∈ E(G), IsPreconnected (core e) :=
    fun e he => (hcorearc e he).isArc.isConnected.isPreconnected
  -- The contact points sit on the frames of their squares.
  have hpar : ∀ e ∈ E(G), Plane.supDist (pa e) (va e) = r := by
    intro e he
    refine Plane.supDist_eq_of_inter_eq_singleton (hcoreconn e he) (hcoreA e he)
      (hpbmem e he).1 fun hcon => ?_
    exact Set.disjoint_left.1 (hsqdisj (va e) (hvaV e he) (vb e) (hvbV e he) (hvab e he))
      hcon (hpbmem e he).2
  have hpbr : ∀ e ∈ E(G), Plane.supDist (pb e) (vb e) = r := by
    intro e he
    refine Plane.supDist_eq_of_inter_eq_singleton (hcoreconn e he) (hcoreB e he)
      (hpamem e he).1 fun hcon => ?_
    exact Set.disjoint_left.1 (hsqdisj (vb e) (hvbV e he) (va e) (hvaV e he)
      (Ne.symm (hvab e he))) hcon (hpamem e he).2
  -- The plane minus the open squares, and its local polygonal connectedness (brick B5).
  set M : Set Plane := (⋃ c ∈ V(G), Plane.openSquare c r)ᶜ with hMdef
  have hMloc : IsLocallyPolyConn' M :=
    isLocallyPolyConn'_compl_biUnion (Graph.finite_vertexSet (G := G)) (fun _ => r) hsqdisj
  have hMV : ∀ c ∈ V(G), c ∉ M := fun c hc hcM =>
    hcM (mem_biUnion hc (Plane.mem_openSquare_self hr))
  -- The cores avoid the open squares.
  have hcoreM : ∀ e ∈ E(G), core e ⊆ M := by
    intro e he z hz hcon
    obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.1 hcon
    have hzc' : z ∈ Plane.closedSquare c r := Plane.openSquare_subset_closedSquare c r hzc
    rcases eq_or_ne c (va e) with rfl | hca
    · have hzp : z ∈ core e ∩ Plane.closedSquare (va e) r := ⟨hz, hzc'⟩
      rw [hcoreA e he, mem_singleton_iff] at hzp
      rw [hzp] at hzc
      exact absurd (hpar e he) (ne_of_lt hzc)
    · rcases eq_or_ne c (vb e) with rfl | hcb
      · have hzp : z ∈ core e ∩ Plane.closedSquare (vb e) r := ⟨hz, hzc'⟩
        rw [hcoreB e he, mem_singleton_iff] at hzp
        rw [hzp] at hzc
        exact absurd (hpbr e he) (ne_of_lt hzc)
      · exact Set.disjoint_left.1
          (hnoninc c hc e he (not_inc_of_ne (hlink e he) hca hcb)) hzc' (hcoresub e he hz)
  -- Brick B7: one `ε` making the tubes about the cores pairwise disjoint.
  obtain ⟨ε, hε, hεall⟩ : ∃ ε > 0, ∀ e ∈ E(G), ∀ f ∈ E(G), f ≠ e →
      ∀ a ∈ core e, ∀ b ∈ core f, 2 * ε ≤ dist a b := by
    refine exists_pos_forall_of_finite (Graph.finite_edgeSet (G := G))
      (P := fun e ε => ∀ f ∈ E(G), f ≠ e → ∀ a ∈ core e, ∀ b ∈ core f, 2 * ε ≤ dist a b)
      (fun e δ ε _ hδε hP f hf hfe a ha b hb =>
        le_trans (by linarith) (hP f hf hfe a ha b hb)) ?_
    intro e he
    refine exists_pos_forall_of_finite (Graph.finite_edgeSet (G := G))
      (P := fun f ε => f ≠ e → ∀ a ∈ core e, ∀ b ∈ core f, 2 * ε ≤ dist a b)
      (fun f δ ε _ hδε hP hfe a ha b hb => le_trans (by linarith) (hP hfe a ha b hb)) ?_
    intro f hf
    by_cases hfe : f = e
    · exact ⟨1, one_pos, fun hcon => absurd hfe hcon⟩
    · obtain ⟨ρ, hρ, hsep⟩ := Plane.exists_dist_pos (hcorecpt e he) (hcorecpt f hf)
        (h.disjoint_of_subset_edgeArc he hf (Ne.symm hfe) (hcoresub e he) (hcoreV e he)
          (hcoresub f hf))
      exact ⟨ρ / 2, by linarith, fun _ a ha b hb => by have := hsep a ha b hb; linarith⟩
  set tube : β → Set Plane := fun e => ⋃ z ∈ core e, ball z ε with htubedef
  have htubeopen : ∀ e, IsOpen (tube e) := fun _ => isOpen_biUnion fun _ _ => isOpen_ball
  have htubedisj : ∀ e ∈ E(G), ∀ f ∈ E(G), e ≠ f → Disjoint (tube e) (tube f) := by
    intro e he f hf hef
    refine Set.disjoint_left.2 fun z hze hzf => ?_
    obtain ⟨a, ha, hza⟩ := mem_iUnion₂.1 hze
    obtain ⟨b, hb, hzb⟩ := mem_iUnion₂.1 hzf
    have h1 : dist a z < ε := by rw [dist_comm]; exact hza
    have h2 : dist z b < ε := hzb
    have h3 := hεall e he f hf (Ne.symm hef) a ha b hb
    have h4 := dist_triangle a z b
    linarith
  -- `U e` is the component of the core inside the tube, relatively open in `M`.
  set U : β → Set Plane := fun e => connectedComponentIn (M ∩ tube e) (pa e) with hUdef
  have hrel : ∀ e, IsRelOpenIn M (M ∩ tube e) := fun e => ⟨tube e, htubeopen e, rfl⟩
  have hcoreO : ∀ e ∈ E(G), core e ⊆ M ∩ tube e := fun e he z hz =>
    ⟨hcoreM e he hz, mem_iUnion₂.2 ⟨z, hz, mem_ball_self hε⟩⟩
  have hcoreU : ∀ e ∈ E(G), core e ⊆ U e := fun e he =>
    (hcoreconn e he).subset_connectedComponentIn (hpamem e he).1 (hcoreO e he)
  have hUM : ∀ e, U e ⊆ M := fun _ =>
    (connectedComponentIn_subset _ _).trans inter_subset_left
  have hUdisj : ∀ e ∈ E(G), ∀ f ∈ E(G), e ≠ f → Disjoint (U e) (U f) := fun e he f hf hef =>
    Set.disjoint_of_subset ((connectedComponentIn_subset _ _).trans inter_subset_right)
      ((connectedComponentIn_subset _ _).trans inter_subset_right) (htubedisj e he f hf hef)
  have hpaU : ∀ e ∈ E(G), pa e ∈ U e := fun e he => hcoreU e he (hpamem e he).1
  have hpbU : ∀ e ∈ E(G), pb e ∈ U e := fun e he => hcoreU e he (hpbmem e he).1
  have hpath : ∀ e ∈ E(G), PolyReaches (U e) (pa e) (pb e) := fun e he =>
    polyReaches_connectedComponentIn hMloc (hrel e) (hpaU e he) (hpbU e he)
  -- A radial segment meets `M` only at its far end, and stays inside its square.
  have hsegM : ∀ c p : Plane, c ∈ V(G) → Plane.supDist p c = r →
      ∀ z ∈ segment ℝ c p, z ∈ M → z = p := by
    intro c p hc hpc z hz hzM
    by_contra hne
    refine hzM (mem_biUnion hc ?_)
    have hlt := Plane.supDist_lt_of_mem_segment (by rw [hpc]; exact hr) hz hne
    rw [hpc] at hlt
    exact hlt
  have hsegSq : ∀ c p : Plane, Plane.supDist p c = r →
      segment ℝ c p ⊆ Plane.closedSquare c r :=
    fun c p hpc => Plane.segment_subset_closedSquare hr.le hpc.le
  -- The point set of a redrawn edge, before it is built.
  set Sset : β → Set Plane := fun e =>
    segment ℝ (va e) (pa e) ∪ U e ∪ segment ℝ (vb e) (pb e) with hSsetdef
  have hUcase : ∀ e ∈ E(G), ∀ f ∈ E(G), e ≠ f → ∀ z ∈ U e, z ∉ Sset f := by
    intro e he f hf hef z hz hzf
    have hzM : z ∈ M := hUM e hz
    have hdis := Set.disjoint_left.1 (hUdisj e he f hf hef) hz
    rcases hzf with (hzf | hzf) | hzf
    · exact hdis ((hsegM (va f) (pa f) (hvaV f hf) (hpar f hf) z hzf hzM) ▸ hpaU f hf)
    · exact hdis hzf
    · exact hdis ((hsegM (vb f) (pb f) (hvbV f hf) (hpbr f hf) z hzf hzM) ▸ hpbU f hf)
  have hRadial : ∀ e ∈ E(G), ∀ c p : Plane, c ∈ V(G) → Plane.supDist p c = r → p ∈ U e →
      ∀ f ∈ E(G), e ≠ f → ∀ z ∈ segment ℝ c p, z ∈ Sset f → z = c := by
    intro e he c p hc hpc hpU f hf hef z hz hzf
    have hdis := Set.disjoint_left.1 (hUdisj e he f hf hef) hpU
    rcases hzf with (hzf | hzf) | hzf
    · exact Plane.radial_meet hr hpc (hpar f hf)
        (fun hEq => hdis (hEq ▸ hpaU f hf)) (fun hne => hsqdisj c hc _ (hvaV f hf) hne) hz hzf
    · exact absurd (hdis ((hsegM c p hc hpc z hz (hUM f hzf)) ▸ hzf)) not_false
    · exact Plane.radial_meet hr hpc (hpbr f hf)
        (fun hEq => hdis (hEq ▸ hpbU f hf)) (fun hne => hsqdisj c hc _ (hvbV f hf) hne) hz hzf
  have hSmeet : ∀ e ∈ E(G), ∀ f ∈ E(G), e ≠ f → ∀ z ∈ Sset e, z ∈ Sset f →
      z = va e ∨ z = vb e := by
    intro e he f hf hef z hze hzf
    rcases hze with (hze | hze) | hze
    · exact Or.inl (hRadial e he (va e) (pa e) (hvaV e he) (hpar e he) (hpaU e he)
        f hf hef z hze hzf)
    · exact absurd hzf (hUcase e he f hf hef z hze)
    · exact Or.inr (hRadial e he (vb e) (pb e) (hvbV e he) (hpbr e he) (hpbU e he)
        f hf hef z hze hzf)
  have hSvert : ∀ e ∈ E(G), ∀ v ∈ V(G), v ∈ Sset e → v = va e ∨ v = vb e := by
    intro e he v hv hvS
    rcases hvS with (hvS | hvS) | hvS
    · refine Or.inl (by_contra fun hne => ?_)
      exact hvert (va e) (hvaV e he) v hv hne (hsegSq (va e) (pa e) (hpar e he) hvS)
    · exact absurd (hUM e hvS) (hMV v hv)
    · refine Or.inr (by_contra fun hne => ?_)
      exact hvert (vb e) (hvbV e he) v hv hne (hsegSq (vb e) (pb e) (hpbr e he) hvS)
  -- Brick B8: the redrawn edge, as a parametrisation.
  have harc : ∀ e ∈ E(G), ∃ g : ℝ → Plane,
      ContinuousOn g I ∧ InjOn g I ∧ g 0 = va e ∧ g 1 = vb e ∧
        IsPolygonal (g '' I) ∧ g '' I ⊆ Sset e := by
    intro e he
    apply exists_polygonal_arc_with_radials (hpath e he) (hUM e)
    · intro heq
      have hx := hpar e he
      rw [← heq, Plane.supDist_self] at hx
      exact hr.ne' hx.symm
    · intro heq
      have hx := hpbr e he
      rw [← heq, Plane.supDist_self] at hx
      exact hr.ne' hx.symm
    · exact hsegM (va e) (pa e) (hvaV e he) (hpar e he)
    · exact hsegM (vb e) (pb e) (hvbV e he) (hpbr e he)
    · exact Set.disjoint_of_subset (hsegSq _ _ (hpar e he)) (hsegSq _ _ (hpbr e he))
        (hsqdisj _ (hvaV e he) _ (hvbV e he) (hvab e he))
  choose! F hFc hFi hF0 hF1 hFpoly hFsub using harc
  refine ⟨F, ⟨fun e he => ⟨hFc e he, hFi e he, ?_⟩, ?_, ?_⟩, fun e he => hFpoly e he⟩
  · rw [hF0 e he, hF1 e he]; exact hlink e he
  · intro e a b v hl hv hvarc
    have he : e ∈ E(G) := hl.edge_mem
    rcases hSvert e he v hv (hFsub e he hvarc) with hEq | hEq <;>
      rcases hl.eq_and_eq_or_eq_and_eq (hlink e he) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (hEq.trans h1.symm)
    · exact Or.inr (hEq.trans h2.symm)
    · exact Or.inr (hEq.trans h2.symm)
    · exact Or.inl (hEq.trans h1.symm)
  · intro e f he hf hef z hze hzf
    have h1 := hSmeet e he f hf hef z (hFsub e he hze) (hFsub f hf hzf)
    have h2 := hSmeet f hf e he (Ne.symm hef) z (hFsub f hf hzf) (hFsub e he hze)
    refine ⟨?_, ?_, ?_⟩
    · rcases h1 with hEq | hEq
      · rw [hEq]; exact hvaV e he
      · rw [hEq]; exact hvbV e he
    · rcases h1 with hEq | hEq
      · rw [hEq]; exact (hlink e he).inc_left
      · rw [hEq]; exact (hlink e he).inc_right
    · rcases h2 with hEq | hEq
      · rw [hEq]; exact (hlink f hf).inc_left
      · rw [hEq]; exact (hlink f hf).inc_right

end Graph
