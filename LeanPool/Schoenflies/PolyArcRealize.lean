/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.ArcCollars
public import LeanPool.Schoenflies.GeneralCrosscut
public import LeanPool.Schoenflies.Realization

/-!
# Realizing a simple polygonal arc as a `PolyArc`

`Schoenflies/ArcCollars.lean` proves blueprint Lemma 1.8 (b) — the two-sided collar of an arc,
hence `Schoenflies.HasArcCollars` — for an arc *presented by its vertex list*, a
`Schoenflies.PolyArc`, and carries the presentation itself as the hypothesis
`Schoenflies.IsPolyArcCarrier`. Nothing on `main` could supply that hypothesis for anything but
a straight segment, so `lem:crosscut-at-most-two` and `thm:general-crosscut` were not in fact
unblocked. This module closes the gap: a set that is both an arc between two points and
polygonal *is* the carrier of a `PolyArc`.

This is the arc analogue of `Schoenflies.exists_closedPolygon`, and the route is the one
`Schoenflies/Realization.lean` takes in the closed case, on a linear index instead of a cyclic
one. The closed-case machinery is reused verbatim wherever it does not mention the loop.

## The three steps

1. **Cut the point set into pieces.** `Schoenflies.exists_isClean` gives a finite list `Q` of
   nondegenerate segments occupying `P`, with pairwise disjoint interiors and no end interior to
   any of them; the two endpoints `a`, `b` of the arc are put on the cut list, so both are ends
   of pieces.
2. **Order the pieces along the arc.** The parametrisation `f` reaches an end of a piece at
   finitely many parameters; listed in increasing order they cut `[0, 1]` into gaps. A gap image
   is connected and misses the ends, so it lies in one piece interior; the interior is connected
   and covered by the closed gap images, so it lies in that one gap. Gaps and pieces correspond
   one to one and the ends, in the order `f` reaches them, are a *linear* vertex list.

   The only change from the closed case is bookkeeping at the far end. There the loop returns to
   `f 0`, so the parameters live in `[0, 1)` and the last gap wraps; here `f 1 = b` is a genuine
   extra vertex. Taking the parameter set to be `{t ∈ [0, 1) | f t` is an end of a piece`}` —
   *exactly* the set `Schoenflies/Realization.lean` uses — makes `Schoenflies.parNext` of the
   last index equal `1` by definition, which is precisely the missing right end. So
   `Schoenflies.par`, `Schoenflies.parNext` and `Schoenflies.exists_mem_gap` are used unchanged,
   and `n` parameters give `n` edges and `n + 1` vertices.
3. **Delete redundant vertices.** `Schoenflies.PreArc` is a `PolyArc` less its `corner` field,
   and `Schoenflies.PreArc.deleteVertex` removes one vertex at which the two edges are
   collinear. Each deletion shortens the list by one, so the induction terminates; unlike the
   cyclic case it can never get stuck, because a one-edge arc satisfies `corner` vacuously.

## Why the arc is not closed into a curve first

The tempting shortcut is to join `b` back to `a` by one extra polygonal path far from the arc,
apply `Schoenflies.exists_closedPolygon_arcs` to the resulting Jordan curve, and read the arc off
the cyclic list. It is circular. The return path has to meet `P` only at `a` and `b`, so it has
to leave `a` in a direction along which the arc does not run; knowing that there *is* such a
direction — that `P` is locally one segment at `a` — is a consequence of the realization, not an
input to it. A *straight* segment from `b` to `a` will not do either: an arc can perfectly well
cross the chord joining its endpoints. And avoiding `P` in the large needs `ℝ² ∖ P` connected,
which is `thm:arc-complement`, stated there with an explicit hypothesis. Route (A) below needs
none of this.

## Padding the vertex list

`PolyArc.vertex` is a function on all of `ℕ` asked to be *globally* injective — the convention
its docstring records, which supplies `A.tang i` and `A.len i` directly. A realization
produces `n + 1` vertices and nothing beyond, so the list has to be padded.
`Schoenflies.exists_injective_extend` does it once and for all, by walking off along the first
coordinate past every value the finite list takes.

## Blueprint

There is no blueprint label for this statement: like the closed-curve realization theorem of
`Schoenflies/Realization.lean` it is the bridge the blueprint takes for granted when it says
"let `P` be a simple polygonal arc with vertices `v_0, …, v_{n+1}`". Its consumers are
`lem:polygonal-collar` (b) and, through it, `lem:crosscut-at-most-two` and
`thm:general-crosscut`.

* `Schoenflies.exists_injective_extend` — a finite injective vertex list extends to an injective
  sequence.
* `Schoenflies.PreArc` — a `PolyArc` less the `corner` field: a simple polygonal arc presented by
  a vertex list, redundant vertices allowed. The arc analogue of `Schoenflies.PrePolygon`.
* `Schoenflies.skipIdx`, `Schoenflies.PreArc.deleteVertex`,
  `Schoenflies.PreArc.carrier_deleteVertex` — the blueprint's "delete redundant vertices at which
  two consecutive edges are collinear", as an operation. The arc analogue of
  `Schoenflies.PrePolygon.deleteLast`, and simpler: with a linear index no rotation is needed, so
  the vertex to be deleted stays where it is.
* `Schoenflies.PreArc.exists_polyArc` — the deletion run to completion. The arc analogue of
  `Schoenflies.PrePolygon.exists_closedPolygon_of_prePolygon`.
* `Schoenflies.exists_preArc_of_isArcBetween` — steps 1 and 2: a set-level simple polygonal arc
  is the carrier of a vertex list. The arc analogue of
  `Schoenflies.exists_prePolygon_of_isJordanCurve`.
* `Schoenflies.isPolyArcCarrier_of_isPolygonal` — **the realization theorem for arcs**, and the
  discharge of `Schoenflies.IsPolyArcCarrier`.
* `Schoenflies.hasArcCollars_of_isPolygonal` — blueprint Lemma 1.8 (b) for a set-level simple
  polygonal arc, with nothing left standing.
* `Schoenflies.IsCrosscut.hasArcCollars`, `Schoenflies.crosscut_at_most_two_of_isPolygonal` — the
  same at the call site of `thm:general-crosscut`.
-/

@[expose] public section

open Metric Set unitInterval

namespace Schoenflies

open Plane

/-! ## Padding a finite vertex list to an injective sequence

`PolyArc` asks for a globally injective `vertex : ℕ → Plane`; a realization only produces
`n + 2` points. The padding walks off along the first coordinate, past every value the finite
part takes, which keeps the extension injective and disjoint from the finite part. -/

/-- **A vertex list injective on an initial segment extends to an injective sequence.** This is
the padding convention `Schoenflies.PolyArc`'s docstring describes, supplied once. -/
theorem exists_injective_extend {N : ℕ} (v : ℕ → Plane)
    (hv : ∀ i < N, ∀ j < N, v i = v j → i = j) :
    ∃ w : ℕ → Plane, Function.Injective w ∧ ∀ k < N, w k = v k := by
  classical
  -- A bound on the first coordinates of the finite part.
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ k < N, v k 0 ≤ M := by
    obtain ⟨M, hM⟩ := ((Set.finite_lt_nat N).image fun k => v k 0).bddAbove
    exact ⟨M, fun k hk => hM ⟨k, hk, rfl⟩⟩
  refine ⟨fun k => if k < N then v k else Plane.mk (M + 1 + k) 0, ?_, fun k hk => by simp [hk]⟩
  intro k l hkl
  dsimp only at hkl
  by_cases hk : k < N <;> by_cases hl : l < N
  · rw [ite_eq_left hk, ite_eq_left hl] at hkl
    exact hv k hk l hl hkl
  · -- A listed point cannot equal a padded one: its first coordinate is too small.
    exfalso
    rw [ite_eq_left hk, ite_eq_right hl] at hkl
    have h1 : v k 0 = M + 1 + (l : ℝ) := by rw [hkl]; exact Plane.mk_zero _ _
    have h2 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    have h3 := hM k hk
    linarith
  · exfalso
    rw [ite_eq_right hk, ite_eq_left hl] at hkl
    have h1 : v l 0 = M + 1 + (k : ℝ) := by rw [← hkl]; exact Plane.mk_zero _ _
    have h2 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h3 := hM l hl
    linarith
  · rw [ite_eq_right hk, ite_eq_right hl] at hkl
    have h1 : M + 1 + (k : ℝ) = M + 1 + (l : ℝ) := by
      rw [← Plane.mk_zero (M + 1 + (k : ℝ)) 0, hkl]; exact Plane.mk_zero _ _
    exact_mod_cast (by linarith : (k : ℝ) = (l : ℝ))

/-! ## The index map of a deletion

On a linear index there is nothing to rotate: a vertex is deleted where it stands, and `skipIdx i`
is the inclusion of the shortened index set into the old one — the identity up to `i`, a shift by
one beyond it. It is the arc analogue of `Schoenflies.PrePolygon.emb`, and much simpler, because
that one has to wrap. -/

section SkipIdx

variable {i k : ℕ}

/-- The index map that skips over vertex `i + 1`. -/
def skipIdx (i k : ℕ) : ℕ := if k ≤ i then k else k + 1

theorem skipIdx_of_le (h : k ≤ i) : skipIdx i k = k := ite_eq_left h

theorem skipIdx_of_lt (h : i < k) : skipIdx i k = k + 1 := ite_eq_right (by omega)

theorem skipIdx_injective (i : ℕ) : Function.Injective (skipIdx i) := by
  intro k l h
  simp only [skipIdx] at h
  split_ifs at h <;> omega

theorem skipIdx_succ (h : k ≠ i) : skipIdx i (k + 1) = skipIdx i k + 1 := by
  simp only [skipIdx]
  split_ifs <;> omega

theorem skipIdx_ne_left (h : k ≠ i) : skipIdx i k ≠ i := by
  simp only [skipIdx]; split_ifs <;> omega

theorem skipIdx_ne_right (i k : ℕ) : skipIdx i k ≠ i + 1 := by
  simp only [skipIdx]; split_ifs <;> omega

end SkipIdx

/-! ## Arcs before normalization

`PreArc` is `PolyArc` with the `corner` field removed, exactly as `Schoenflies.PrePolygon` is
`Schoenflies.ClosedPolygon` with it removed. Realization produces one of these; normalization
turns it into a `PolyArc`. -/

/-- A simple polygonal arc presented by its vertex list, with redundant vertices allowed:
`Schoenflies.PolyArc` less its `corner` field. -/
structure PreArc (n : ℕ) where
  /-- The vertices, in order along the arc. Only `vertex 0, …, vertex (n + 1)` are on it. -/
  vertex : ℕ → Plane
  /-- The vertices are distinct. -/
  vertex_inj : Function.Injective vertex
  /-- Simplicity: an edge meets any other edge only at one of its own endpoints. -/
  edges_meet : ∀ i ≤ n, ∀ j ≤ n, i ≠ j →
    segment ℝ (vertex i) (vertex (i + 1)) ∩ segment ℝ (vertex j) (vertex (j + 1)) ⊆
      {vertex i, vertex (i + 1)}

namespace PreArc

variable {n i j k : ℕ}

/-- Edge `i` of the arc. -/
def edge (A : PreArc n) (i : ℕ) : Set Plane := segment ℝ (A.vertex i) (A.vertex (i + 1))

/-- The carrier of the arc: the union of its `n + 1` edges. -/
def carrier (A : PreArc n) : Set Plane := ⋃ i, ⋃ (_ : i ≤ n), A.edge i

variable {A : PreArc n}

theorem mem_carrier_iff {x : Plane} : x ∈ A.carrier ↔ ∃ i ≤ n, x ∈ A.edge i := mem_iUnion_le_nat

theorem edge_subset_carrier (hi : i ≤ n) : A.edge i ⊆ A.carrier :=
  fun _ hx => mem_carrier_iff.2 ⟨i, hi, hx⟩

theorem vertex_ne : A.vertex i ≠ A.vertex (i + 1) := fun h => by
  have := A.vertex_inj h; omega

/-! ### Deleting a redundant vertex

The blueprint's opening move in the strip lemma, "delete redundant vertices at which two
consecutive edges are collinear", as an operation rather than an invariant. -/

/-- **A redundant vertex is interior to the segment joining its neighbours**, so the two edges
at it merge into a single one. This is `Schoenflies.PrePolygon.mem_openSegment_of_det_eq_zero'`
read on a linear index. -/
theorem edge_union_of_det_eq_zero (A : PreArc n) (hi : i < n)
    (hdet : det (A.vertex i - A.vertex (i + 1)) (A.vertex (i + 1 + 1) - A.vertex (i + 1)) = 0) :
    segment ℝ (A.vertex i) (A.vertex (i + 1 + 1)) = A.edge i ∪ A.edge (i + 1) :=
  segment_split (openSegment_subset_segment ℝ _ _
    (PrePolygon.mem_openSegment_of_det_eq_zero' vertex_ne
      (fun h => by have := A.vertex_inj h; omega)
      (A.edges_meet i (by omega) (i + 1) (by omega) (by omega)) hdet))

/-- The middle vertex of a merge lies on no other edge: it is an end of edge `i`, and an edge
meeting edge `i` there would have it as one of its own ends. -/
theorem vertex_notMem_edge (A : PreArc n) (hi : i < n) (hk : k ≤ n) (hk1 : k ≠ i)
    (hk2 : k ≠ i + 1) : A.vertex (i + 1) ∉ A.edge k := by
  intro hmem
  have h := A.edges_meet k hk i (by omega) hk1 ⟨hmem, right_mem_segment ℝ _ _⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h <;> exact absurd (A.vertex_inj h) (by omega)

/-- **The shortened vertex list is still simple.** The merged edge is the union of the two it
replaces, and the only point that could escape the two-point bound — the deleted vertex — lies
on no other edge. -/
theorem skip_edges_meet (A : PreArc (n + 1)) (hi : i < n + 1)
    (hdet : det (A.vertex i - A.vertex (i + 1)) (A.vertex (i + 1 + 1) - A.vertex (i + 1)) = 0) :
    ∀ j ≤ n, ∀ k ≤ n, j ≠ k →
      segment ℝ (A.vertex (skipIdx i j)) (A.vertex (skipIdx i (j + 1))) ∩
          segment ℝ (A.vertex (skipIdx i k)) (A.vertex (skipIdx i (k + 1))) ⊆
        {A.vertex (skipIdx i j), A.vertex (skipIdx i (j + 1))} := by
  -- Away from `i` the new edge is an old one; at `i` it is the union of two old ones.
  have hplain : ∀ l, l ≠ i →
      segment ℝ (A.vertex (skipIdx i l)) (A.vertex (skipIdx i (l + 1))) = A.edge (skipIdx i l) :=
    fun l hl => by rw [skipIdx_succ hl]; rfl
  have hmerge : segment ℝ (A.vertex (skipIdx i i)) (A.vertex (skipIdx i (i + 1)))
      = A.edge i ∪ A.edge (i + 1) := by
    rw [skipIdx_of_le (le_refl i), skipIdx_of_lt (Nat.lt_succ_self i)]
    exact A.edge_union_of_det_eq_zero hi hdet
  have hle : ∀ l ≤ n, skipIdx i l ≤ n + 1 := by
    intro l hl; simp only [skipIdx]; split_ifs <;> omega
  intro j hj k hk hjk z hz
  by_cases hji : i = j
  · -- The merged edge on the left: the deleted vertex has to be ruled out by hand.
    subst hji
    have hk1 : skipIdx i k ≠ i := skipIdx_ne_left (Ne.symm hjk)
    have hk2 : skipIdx i k ≠ i + 1 := skipIdx_ne_right i k
    rw [skipIdx_of_le (le_refl i), skipIdx_of_lt (Nat.lt_succ_self i)]
    have hzk : z ∈ A.edge (skipIdx i k) := by
      rw [← hplain k (Ne.symm hjk)]; exact hz.2
    have hzj : z ∈ A.edge i ∪ A.edge (i + 1) := hmerge ▸ hz.1
    rcases hzj with hzj | hzj
    · have h := A.edges_meet i (by omega) (skipIdx i k) (hle k hk) (Ne.symm hk1) ⟨hzj, hzk⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact absurd (h ▸ hzk) (A.vertex_notMem_edge hi (hle k hk) hk1 hk2)
    · have h := A.edges_meet (i + 1) (by omega) (skipIdx i k) (hle k hk)
        (fun he => hk2 he.symm) ⟨hzj, hzk⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
      rcases h with h | h
      · exact absurd (h ▸ hzk) (A.vertex_notMem_edge hi (hle k hk) hk1 hk2)
      · exact Or.inr h
  · -- An untouched edge on the left: the bound is one instance of `edges_meet`.
    have hji' : j ≠ i := fun he => hji he.symm
    rw [skipIdx_succ hji']
    have hzj : z ∈ A.edge (skipIdx i j) := (hplain j hji') ▸ hz.1
    by_cases hki : i = k
    · subst hki
      have hj1 : skipIdx i j ≠ i := skipIdx_ne_left hji'
      have hj2 : skipIdx i j ≠ i + 1 := skipIdx_ne_right i j
      rcases (hmerge ▸ hz.2 : z ∈ A.edge i ∪ A.edge (i + 1)) with hzk | hzk
      · exact A.edges_meet (skipIdx i j) (hle j hj) i (by omega) hj1 ⟨hzj, hzk⟩
      · exact A.edges_meet (skipIdx i j) (hle j hj) (i + 1) (by omega) hj2 ⟨hzj, hzk⟩
    · have hki' : k ≠ i := fun he => hki he.symm
      have hzk : z ∈ A.edge (skipIdx i k) := (hplain k hki') ▸ hz.2
      exact A.edges_meet (skipIdx i j) (hle j hj) (skipIdx i k) (hle k hk)
        (fun he => hjk (skipIdx_injective i he)) ⟨hzj, hzk⟩

/-- **The vertex list with a redundant vertex deleted.** -/
def deleteVertex (A : PreArc (n + 1)) (hi : i < n + 1)
    (hdet : det (A.vertex i - A.vertex (i + 1)) (A.vertex (i + 1 + 1) - A.vertex (i + 1)) = 0) :
    PreArc n where
  vertex k := A.vertex (skipIdx i k)
  vertex_inj := A.vertex_inj.comp (skipIdx_injective i)
  edges_meet := A.skip_edges_meet hi hdet

@[simp] theorem deleteVertex_vertex (A : PreArc (n + 1)) (hi : i < n + 1)
    (hdet : det (A.vertex i - A.vertex (i + 1)) (A.vertex (i + 1 + 1) - A.vertex (i + 1)) = 0)
    (k : ℕ) : (A.deleteVertex hi hdet).vertex k = A.vertex (skipIdx i k) := rfl

theorem deleteVertex_vertex_zero (A : PreArc (n + 1)) (hi : i < n + 1)
    (hdet : det (A.vertex i - A.vertex (i + 1)) (A.vertex (i + 1 + 1) - A.vertex (i + 1)) = 0) :
    (A.deleteVertex hi hdet).vertex 0 = A.vertex 0 := by
  rw [deleteVertex_vertex, skipIdx_of_le (Nat.zero_le i)]

theorem deleteVertex_vertex_last (A : PreArc (n + 1)) (hi : i < n + 1)
    (hdet : det (A.vertex i - A.vertex (i + 1)) (A.vertex (i + 1 + 1) - A.vertex (i + 1)) = 0) :
    (A.deleteVertex hi hdet).vertex (n + 1) = A.vertex (n + 1 + 1) := by
  rw [deleteVertex_vertex, skipIdx_of_lt (by omega)]

/-- **Deleting a redundant vertex does not move the arc.** -/
theorem carrier_deleteVertex (A : PreArc (n + 1)) (hi : i < n + 1)
    (hdet : det (A.vertex i - A.vertex (i + 1)) (A.vertex (i + 1 + 1) - A.vertex (i + 1)) = 0) :
    (A.deleteVertex hi hdet).carrier = A.carrier := by
  have hplain : ∀ l, l ≠ i → (A.deleteVertex hi hdet).edge l = A.edge (skipIdx i l) :=
    fun l hl => by rw [edge, deleteVertex_vertex, deleteVertex_vertex, skipIdx_succ hl]; rfl
  have hmerge : (A.deleteVertex hi hdet).edge i = A.edge i ∪ A.edge (i + 1) := by
    rw [edge, deleteVertex_vertex, deleteVertex_vertex, skipIdx_of_le (le_refl i),
      skipIdx_of_lt (Nat.lt_succ_self i)]
    exact A.edge_union_of_det_eq_zero hi hdet
  refine Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨l, hl, hzl⟩ := mem_carrier_iff.1 hz
    by_cases hli : l = i
    · subst hli
      rcases (hmerge ▸ hzl : z ∈ A.edge l ∪ A.edge (l + 1)) with h | h
      exacts [edge_subset_carrier (by omega) h, edge_subset_carrier (by omega) h]
    · refine edge_subset_carrier (show skipIdx i l ≤ n + 1 by simp only [skipIdx]; split_ifs <;>
        omega) ((hplain l hli) ▸ hzl)
  · obtain ⟨l, hl, hzl⟩ := mem_carrier_iff.1 hz
    rcases Nat.lt_trichotomy l i with hlt | heq | hgt
    · refine mem_carrier_iff.2 ⟨l, by omega, ?_⟩
      rw [hplain l (by omega), skipIdx_of_le (by omega)]
      exact hzl
    · exact mem_carrier_iff.2 ⟨i, by omega, hmerge ▸ Or.inl (heq ▸ hzl)⟩
    · rcases Nat.lt_or_ge (i + 1) l with hlt' | hle'
      · refine mem_carrier_iff.2 ⟨l - 1, by omega, ?_⟩
        rw [hplain (l - 1) (by omega), skipIdx_of_lt (by omega), show l - 1 + 1 = l by omega]
        exact hzl
      · exact mem_carrier_iff.2 ⟨i, by omega, hmerge ▸ Or.inr (show l = i + 1 by omega ▸ hzl)⟩

/-- **Every `PreArc` normalizes to a `PolyArc` with the same carrier and the same two extreme
vertices.** This is the blueprint's "delete redundant vertices at which two consecutive edges are
collinear", run to completion. Unlike the closed case the induction can never get stuck: a
one-edge arc satisfies `corner` vacuously. -/
theorem exists_polyArc : ∀ (n : ℕ) (A : PreArc n), ∃ (m : ℕ) (B : PolyArc m),
    B.carrier = A.carrier ∧ B.vertex 0 = A.vertex 0 ∧ B.vertex (m + 1) = A.vertex (n + 1) := by
  intro n
  induction n with
  | zero =>
      intro A
      exact ⟨0, ⟨A.vertex, A.vertex_inj, A.edges_meet, fun i hi => absurd hi (Nat.not_lt_zero i)⟩,
        rfl, rfl, rfl⟩
  | succ n ih =>
      intro A
      by_cases hc : ∀ i < n + 1,
          det (A.vertex i - A.vertex (i + 1)) (A.vertex (i + 2) - A.vertex (i + 1)) ≠ 0
      · exact ⟨n + 1, ⟨A.vertex, A.vertex_inj, A.edges_meet, hc⟩, rfl, rfl, rfl⟩
      · push Not at hc
        obtain ⟨i, hi, hdet⟩ := hc
        obtain ⟨m, B, hcar, h0, hlast⟩ := ih (A.deleteVertex hi hdet)
        exact ⟨m, B, by rw [hcar, carrier_deleteVertex],
          by rw [h0, deleteVertex_vertex_zero], by rw [hlast, deleteVertex_vertex_last]⟩

end PreArc

/-! ## From a clean presentation to a linear vertex list

The arc reaches an end of a piece at finitely many parameters. Between two consecutive ones it
runs through one whole piece interior — the gap image is connected and misses the ends, so it
lies in one interior; and the interior, being connected and covered by the closed gap images,
lies in that one gap. So the ends, listed in the order the arc reaches them, are the vertex list
of a `PreArc` whose edges are the pieces.

The parameter set is taken inside `[0, 1)`, exactly as in the closed case, so that
`Schoenflies.parNext` of the last index is `1` by definition. That is not a trick: `f 1 = b` is
the last vertex, and this is what puts it there. Both `a` and `b` are forced onto the cut list,
which is what makes `0` a parameter and `b` an end of a piece. -/

/-- **A simple polygonal arc is the carrier of a vertex list.** The arc analogue of
`Schoenflies.exists_prePolygon_of_isJordanCurve`. -/
theorem exists_preArc_of_isArcBetween {P : Set Plane} {a b : Plane}
    (hP : IsArcBetween P a b) (hpoly : IsPolygonal P) :
    ∃ (n : ℕ) (A : PreArc n), A.carrier = P ∧ A.vertex 0 = a ∧ A.vertex (n + 1) = b := by
  classical
  obtain ⟨f, hcont, hinj, hfP, hf0, hf1⟩ := hP
  have hIco : ∀ s ∈ Ico (0 : ℝ) 1, s ∈ I := fun s hs => ⟨hs.1, hs.2.le⟩
  have hmemP : ∀ s ∈ I, f s ∈ P := fun s hs => hfP ▸ ⟨s, hs, rfl⟩
  have haP : a ∈ P := by rw [← hf0]; exact hmemP 0 zero_mem_I
  have hbP : b ∈ P := by rw [← hf1]; exact hmemP 1 one_mem_I
  have hab : a ≠ b := by
    rw [← hf0, ← hf1]
    exact fun he => absurd (hinj zero_mem_I one_mem_I he) (by norm_num)
  -- Both endpoints of the arc are forced to be ends of pieces.
  obtain ⟨Q, hQ, hextra⟩ := exists_isClean hpoly haP hbP hab [a, b]
  obtain ⟨Ra, hRa, hRaend⟩ := hextra a (by simp) haP
  obtain ⟨Rb, hRb, hRbend⟩ := hextra b (by simp) hbP
  have h0V : f 0 ∈ endSet Q := by rw [hf0]; exact ⟨Ra, hRa, hRaend⟩
  have h1V : f 1 ∈ endSet Q := by rw [hf1]; exact ⟨Rb, hRb, hRbend⟩
  -- Every point of the arc away from the ends is reached strictly before the far endpoint.
  have hsurj : ∀ z ∈ P \ endSet Q, ∃ s ∈ Ico (0 : ℝ) 1, f s = z := by
    intro z hz
    obtain ⟨s, hs, rfl⟩ : ∃ s ∈ I, f s = z := by rw [← hfP] at hz; exact hz.1
    refine ⟨s, ⟨hs.1, ?_⟩, rfl⟩
    rcases eq_or_lt_of_le hs.2 with rfl | hlt
    · exact absurd h1V hz.2
    · exact hlt
  -- The parameters at which the arc is at an end of a piece, before the far endpoint.
  have hTfin : {t : ℝ | t ∈ Ico (0 : ℝ) 1 ∧ f t ∈ endSet Q}.Finite := by
    refine Set.Finite.of_finite_image (f := f) ((finite_endSet Q).subset ?_)
      (hinj.mono fun t ht => hIco t ht.1)
    rintro x ⟨t, ht, rfl⟩
    exact ht.2
  obtain ⟨n, hcard⟩ : ∃ n, hTfin.toFinset.card = n := ⟨_, rfl⟩
  set TF : Finset ℝ := hTfin.toFinset with hTFdef
  have hmemTF : ∀ t : ℝ, t ∈ TF ↔ (t ∈ Ico (0 : ℝ) 1 ∧ f t ∈ endSet Q) := by
    intro t; rw [hTFdef, Set.Finite.mem_toFinset]; exact Iff.rfl
  have hTle : ∀ s ∈ TF, s ∈ Ico (0 : ℝ) 1 := fun s hs => ((hmemTF s).1 hs).1
  have h0TF : (0 : ℝ) ∈ TF := (hmemTF 0).2 ⟨⟨le_refl 0, by norm_num⟩, h0V⟩
  set tp : Fin n → ℝ := par TF hcard with htp
  set nx : Fin n → ℝ := parNext TF hcard with hnx
  -- Both ends of every gap are ends of pieces; for the last gap the right end is `f 1 = b`.
  have htpV : ∀ i : Fin n, f (tp i) ∈ endSet Q := fun i =>
    ((hmemTF _).1 (par_mem hcard i)).2
  have hnxV : ∀ i : Fin n, f (nx i) ∈ endSet Q := by
    intro i
    rw [hnx, parNext]
    split_ifs with hi
    · exact ((hmemTF _).1 (Finset.orderEmbOfFin_mem _ _ _)).2
    · exact h1V
  have hlt : ∀ i : Fin n, tp i < nx i := fun i => par_lt_parNext hcard hTle i
  have hIcc : ∀ i : Fin n, Icc (tp i) (nx i) ⊆ I := fun i => gapClosure_subset_I hcard hTle i
  have hIoo : ∀ i : Fin n, Ioo (tp i) (nx i) ⊆ Ico (0 : ℝ) 1 := fun i =>
    gap_subset_Ico hcard hTle i
  set G : Fin n → Set Plane := fun i => f '' Ioo (tp i) (nx i) with hG
  set Z : Fin n → Set Plane := fun i => f '' Icc (tp i) (nx i) with hZ
  have hGne : ∀ i, (G i).Nonempty := fun i => ((Set.nonempty_Ioo.2 (hlt i)).image f)
  have hGconn : ∀ i, IsPreconnected (G i) := fun i =>
    isPreconnected_Ioo.image f (hcont.mono (fun s hs => hIcc i (Ioo_subset_Icc_self hs)))
  have hGdiff : ∀ i, G i ⊆ P \ endSet Q := by
    rintro i z ⟨s, hs, rfl⟩
    refine ⟨hmemP s (hIcc i (Ioo_subset_Icc_self hs)), fun hzV => ?_⟩
    exact notMem_of_mem_gap hcard hs ((hmemTF s).2 ⟨hIoo i hs, hzV⟩)
  have hZcompact : ∀ i, IsCompact (Z i) := fun i =>
    isCompact_image_of_subset_I hcont (hIcc i) isClosed_Icc
  have hZeq : ∀ i, Z i = G i ∪ {f (tp i), f (nx i)} := by
    intro i
    simp only [hZ, hG]
    rw [Icc_eq_Ioo_union_ends (hlt i).le, Set.image_union, Set.image_pair]
  have hZdiff : ∀ i, Z i ∩ (P \ endSet Q) = G i := by
    intro i
    refine Set.Subset.antisymm ?_ (fun z hz => ⟨(hZeq i) ▸ Or.inl hz, hGdiff i hz⟩)
    rintro z ⟨hzZ, hzC, hzV⟩
    rcases (hZeq i) ▸ hzZ with hz | hz
    · exact hz
    · rcases hz with rfl | rfl
      exacts [absurd (htpV i) hzV, absurd (hnxV i) hzV]
  have hGdisj : ∀ i j : Fin n, i ≠ j → G i ∩ G j = ∅ := by
    intro i j hij
    refine Set.eq_empty_of_forall_notMem ?_
    rintro z ⟨⟨s, hs, rfl⟩, t, ht, hts⟩
    have := hinj (hIco _ (hIoo j ht)) (hIco _ (hIoo i hs)) hts
    exact Set.disjoint_left.1 (gap_disjoint hcard hij) hs (this ▸ ht)
  -- The gaps cover the arc away from the ends of the pieces.
  have hcov : (⋃ i, G i) = P \ endSet Q := by
    refine Set.Subset.antisymm (Set.iUnion_subset hGdiff) (fun z hz => ?_)
    obtain ⟨s, hs, rfl⟩ := hsurj z hz
    obtain ⟨i, hi⟩ := exists_mem_gap hcard hTle h0TF hs
      (fun hsT => hz.2 ((hmemTF s).1 hsT).2)
    exact Set.mem_iUnion.2 ⟨i, ⟨s, hi, rfl⟩⟩
  -- Each gap image lies in one piece interior.
  have hchoose : ∀ i, ∃ R ∈ Q, G i ⊆ R.interior := fun i =>
    hQ.preconnected_subset_interior (hGconn i) (hGne i) (hGdiff i)
  choose pc hpcQ hpcsub using hchoose
  -- And is the whole of it: the interior is connected and covered by the closed gap images.
  have hpceq : ∀ i, (pc i).interior = G i := by
    intro i
    apply eq_of_preconnected_finite_partition i (convex_openSegment _ _).isPreconnected
      (G := G) (Z := Z) ?_ (hGne i) (hpcsub i)
      (fun j => (hZcompact j).isClosed) hZdiff hGdisj hcov
    rw [hQ.diff_endSet_eq]
    exact fun z hz => Set.mem_iUnion₂.2 ⟨pc i, hpcQ i, hz⟩
  -- The correspondence between gaps and pieces is a bijection.
  have hpcinj : Function.Injective pc := by
    intro i j hij
    by_contra hne'
    obtain ⟨z, hz⟩ := hGne i
    have hzj : z ∈ G j := by rw [← hpceq j, ← hij, hpceq i]; exact hz
    exact Set.eq_empty_iff_forall_notMem.1 (hGdisj i j hne') z ⟨hz, hzj⟩
  have hpcsurj : ∀ R ∈ Q, ∃ i, pc i = R :=
    hQ.exists_piece_index hpcQ (by simpa only [hpceq] using hcov)
  -- The ends of the piece are the two ends of the gap.
  have hends : ∀ i, ((pc i).1 = f (tp i) ∧ (pc i).2 = f (nx i)) ∨
      ((pc i).1 = f (nx i) ∧ (pc i).2 = f (tp i)) := by
    intro i
    exact Piece.ends_of_closed_gap (hQ.nondeg _ (hpcQ i)) (hZcompact i).isClosed
      (hpceq i) (hZeq i)
  have hpcseg : ∀ i, (pc i).seg = segment ℝ (f (tp i)) (f (nx i)) := by
    intro i
    rcases hends i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Piece.seg, h1, h2]
    · rw [Piece.seg, h1, h2, segment_symm]
  -- There is at least one gap, and the first one starts at `0`.
  have hn0 : 0 < n := par_card_pos hcard h0TF
  have htp0 : tp ⟨0, hn0⟩ = 0 := par_zero hcard hTle h0TF
  -- The linear vertex list: the ends, in the order the arc reaches them, and then `b`.
  set vf : ℕ → Plane := fun k => if h : k < n then f (par TF hcard ⟨k, h⟩) else b with hvf
  have hvflt : ∀ (k : ℕ) (hk : k < n), vf k = f (tp ⟨k, hk⟩) := by
    intro k hk; rw [hvf]; simp only [dite_eq_left hk, htp]
  have hvfn : vf n = b := by rw [hvf]; simp only [dite_eq_right (lt_irrefl n)]
  -- `f 1 = b` is the right end of the last gap, so the list has the right successor at each step.
  have hvfsucc : ∀ (k : ℕ) (hk : k < n), vf (k + 1) = f (nx ⟨k, hk⟩) := by
    intro k hk
    by_cases hk1 : k + 1 < n
    · rw [hvflt (k + 1) hk1, htp, hnx, parNext,
        dite_eq_left (show (⟨k, hk⟩ : Fin n).val + 1 < n from hk1)]
      rfl
    · have : k + 1 = n := by omega
      rw [this, hvfn, hnx, parNext,
        dite_eq_right (show ¬ ((⟨k, hk⟩ : Fin n).val + 1 < n) from hk1), hf1]
  -- The vertex list is injective on `{0, …, n}`: `f` is, and the parameters are increasing.
  have hvfinj : ∀ i < n + 1, ∀ j < n + 1, vf i = vf j → i = j := by
    have hkey : ∀ i < n, ∀ j < n, vf i = vf j → i = j := by
      intro i hi j hj he
      rw [hvflt i hi, hvflt j hj] at he
      have h1 := hinj (hIco _ (hTle _ (par_mem hcard ⟨i, hi⟩)))
        (hIco _ (hTle _ (par_mem hcard ⟨j, hj⟩))) he
      exact congrArg Fin.val ((TF.orderEmbOfFin hcard).injective h1)
    have hlast : ∀ i < n, vf i ≠ vf n := by
      intro i hi he
      rw [hvflt i hi, hvfn, ← hf1] at he
      have h1 := hinj (hIco _ (hTle _ (par_mem hcard ⟨i, hi⟩))) one_mem_I he
      exact absurd (h1 ▸ (hTle _ (par_mem hcard ⟨i, hi⟩)).2) (lt_irrefl 1)
    intro i hi j hj he
    rcases Nat.lt_or_ge i n with hi' | hi'
    · rcases Nat.lt_or_ge j n with hj' | hj'
      · exact hkey i hi' j hj' he
      · exact absurd (show j = n by omega ▸ he) (hlast i hi')
    · rcases Nat.lt_or_ge j n with hj' | hj'
      · exact absurd (show i = n by omega ▸ he.symm) (hlast j hj')
      · omega
  obtain ⟨w, hwinj, hwval⟩ := exists_injective_extend vf hvfinj
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- Edge `i` of the list is piece `i`.
  have hwedge : ∀ (i : ℕ) (hi : i < m + 1),
      segment ℝ (w i) (w (i + 1)) = (pc ⟨i, hi⟩).seg := by
    intro i hi
    rw [hwval i (by omega), hwval (i + 1) (by omega), hvflt i hi, hvfsucc i hi, hpcseg]
  -- Simplicity, transported from the clean presentation.
  have hmeet : ∀ i ≤ m, ∀ j ≤ m, i ≠ j →
      segment ℝ (w i) (w (i + 1)) ∩ segment ℝ (w j) (w (j + 1)) ⊆ {w i, w (i + 1)} := by
    intro i hi j hj hij
    rw [hwedge i (by omega), hwedge j (by omega)]
    have hne' : pc ⟨i, by omega⟩ ≠ pc ⟨j, by omega⟩ := fun he =>
      hij (congrArg Fin.val (hpcinj he))
    refine le_trans (hQ.seg_inter_subset (hpcQ _) (hpcQ _) hne') ?_
    have hwi : w i = f (tp ⟨i, by omega⟩) := by rw [hwval i (by omega), hvflt i (by omega)]
    have hwi' : w (i + 1) = f (nx ⟨i, by omega⟩) := by
      rw [hwval (i + 1) (by omega), hvfsucc i (by omega)]
    rcases hends ⟨i, by omega⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, ← hwi, ← hwi']
    · rw [h1, h2, ← hwi, ← hwi', Set.pair_comm]
  -- The carrier is the union of the pieces, which is the arc.
  have hcarrier : (⋃ i, ⋃ (_ : i ≤ m), segment ℝ (w i) (w (i + 1))) = P := by
    rw [← hQ.cover_eq]
    refine Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
    · obtain ⟨i, hi, hzi⟩ := mem_iUnion_le_nat.1 hz
      rw [hwedge i (by omega)] at hzi
      exact mem_cover (hpcQ _) hzi
    · obtain ⟨R, hR, hzR⟩ := ClosedPolygon.exists_of_mem_cover hz
      obtain ⟨i, rfl⟩ := hpcsurj R hR
      refine mem_iUnion_le_nat.2 ⟨i.val, by omega, ?_⟩
      rw [hwedge i.val i.isLt]
      exact hzR
  have hzero : w 0 = a := by rw [hwval 0 (by omega), hvflt 0 hn0, htp0, hf0]
  have hlastv : w (m + 1) = b := by rw [hwval (m + 1) (by omega), hvfn]
  exact ⟨m, ⟨w, hwinj, hmeet⟩, hcarrier, hzero, hlastv⟩

/-! ## The realization theorem for arcs

Realization followed by normalization. This is the statement
`Schoenflies/ArcCollars.lean` names at the end of its file as the one thing it does not prove. -/

/-- **Every simple polygonal arc is the carrier of a `PolyArc`.** The arc analogue of
`Schoenflies.exists_closedPolygon`, and the discharge of `Schoenflies.IsPolyArcCarrier`.

No `a ≠ b` hypothesis is needed: an arc between two points has them distinct, because its
parametrisation is injective on `[0, 1]`. -/
theorem isPolyArcCarrier_of_isPolygonal {P : Set Plane} {a b : Plane}
    (hP : IsArcBetween P a b) (hpoly : IsPolygonal P) : IsPolyArcCarrier P a b := by
  obtain ⟨n, A, hcar, h0, hlast⟩ := exists_preArc_of_isArcBetween hP hpoly
  obtain ⟨m, B, hcar', h0', hlast'⟩ := PreArc.exists_polyArc n A
  exact ⟨m, B, by rw [hcar', hcar], by rw [h0', h0], by rw [hlast', hlast]⟩

/-- **Blueprint Lemma 1.8 (b) for a set-level simple polygonal arc**, with nothing left
standing. This is `Schoenflies.hasArcCollars` with its presentation hypothesis discharged. -/
theorem hasArcCollars_of_isPolygonal {D P : Set Plane} {a b : Plane} (hD : IsOpen D)
    (ha : a ∉ D) (hb : b ∉ D) (hPD : P \ {a, b} ⊆ D)
    (hP : IsArcBetween P a b) (hpoly : IsPolygonal P) : HasArcCollars D P :=
  hasArcCollars hD ha hb hPD (isPolyArcCarrier_of_isPolygonal hP hpoly)

/-- **Lemma "At most two sides" for a set-level simple polygonal arc** (`lem:crosscut-at-most-two`),
with nothing left standing. -/
theorem crosscut_at_most_two_of_isPolygonal {D P : Set Plane} {a b : Plane}
    (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    (hP : IsArcBetween P a b) (hPpoly : IsPolygonal P)
    (ha : a ∉ D) (hb : b ∉ D) (hPD : P \ {a, b} ⊆ D) :
    ∃ zL ∈ D \ P, ∃ zR ∈ D \ P, ∀ x ∈ D \ P,
      x ∈ connectedComponentIn (D \ P) zL ∨ x ∈ connectedComponentIn (D \ P) zR :=
  crosscut_at_most_two hDopen hDconn hP hPpoly ha hb hPD
    (hasArcCollars_of_isPolygonal hDopen ha hb hPD hP hPpoly)

/-- **Lemma "At most two sides" in the form the crosscut theorem consumes**, with nothing left
standing. -/
theorem crosscut_components_exhaust_of_isPolygonal {D P : Set Plane} {a b v₁ v₂ : Plane}
    (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    (hP : IsArcBetween P a b) (hPpoly : IsPolygonal P)
    (ha : a ∉ D) (hb : b ∉ D) (hPD : P \ {a, b} ⊆ D)
    (h₁ : v₁ ∈ D \ P) (h₂ : v₂ ∈ D \ P)
    (hne : connectedComponentIn (D \ P) v₁ ≠ connectedComponentIn (D \ P) v₂) :
    ∀ x ∈ D \ P, x ∈ connectedComponentIn (D \ P) v₁ ∨ x ∈ connectedComponentIn (D \ P) v₂ :=
  crosscut_components_exhaust hDopen hDconn hP hPpoly ha hb hPD
    (hasArcCollars_of_isPolygonal hDopen ha hb hPD hP hPpoly) h₁ h₂ hne

/-! ## The collar hypothesis at the call site of `thm:general-crosscut`

`Schoenflies.IsCrosscut` carries exactly what the discharge needs: `P` is an arc from `p` to `q`,
`P` is polygonal, and `P ∖ {p, q}` lies in `inside C`, whose openness comes from the curve being
closed. So `hcollars` is never again a hypothesis of the crosscut theorem — only `thm:jordan`
is. -/

variable {C P A₁ A₂ : Set Plane} {p q : Plane}

/-- **The collar hypothesis of `thm:general-crosscut`, discharged.** -/
theorem IsCrosscut.hasArcCollars (h : IsCrosscut C P p q) : HasArcCollars (inside C) P :=
  Schoenflies.hasArcCollars (isOpen_inside h.curve.isClosed) h.left_notMem_inside
    h.right_notMem_inside h.sdiff_subset (isPolyArcCarrier_of_isPolygonal h.arc h.polygonal)

/-- **Theorem "Crosscut theorem", first sentence** (`thm:general-crosscut`), with the collar
hypothesis discharged: only `thm:jordan` is left. -/
theorem general_crosscut' (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    inside C \ P = inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∧
      Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) ∧
      (inside (A₁ ∪ P)).Nonempty ∧ (inside (A₂ ∪ P)).Nonempty ∧
      inside (A₁ ∪ P) ≠ inside (A₂ ∪ P) ∧
      (∀ z ∈ inside (A₁ ∪ P), connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P)) ∧
      (∀ z ∈ inside (A₂ ∪ P), connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P)) ∧
      (∀ z ∈ inside C \ P, connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P) ∨
        connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P)) ∧
      closure (inside (A₁ ∪ P)) ∩ C = A₁ ∧ closure (inside (A₂ ∪ P)) ∩ C = A₂ :=
  general_crosscut hjordan h hcut h.hasArcCollars

/-- **Theorem "Crosscut theorem", second sentence** (`thm:general-crosscut`), with the collar
hypothesis discharged. -/
theorem general_crosscut_three_regions'
    (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    (C ∪ P)ᶜ = outside C ∪ inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∧
      (∀ z ∈ outside C, connectedComponentIn (C ∪ P)ᶜ z = outside C) ∧
      (∀ z ∈ inside (A₁ ∪ P), connectedComponentIn (C ∪ P)ᶜ z = inside (A₁ ∪ P)) ∧
      (∀ z ∈ inside (A₂ ∪ P), connectedComponentIn (C ∪ P)ᶜ z = inside (A₂ ∪ P)) ∧
      (∀ z ∈ (C ∪ P)ᶜ, connectedComponentIn (C ∪ P)ᶜ z = outside C ∨
        connectedComponentIn (C ∪ P)ᶜ z = inside (A₁ ∪ P) ∨
        connectedComponentIn (C ∪ P)ᶜ z = inside (A₂ ∪ P)) ∧
      Disjoint (outside C) (inside (A₁ ∪ P)) ∧ Disjoint (outside C) (inside (A₂ ∪ P)) ∧
        Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) ∧
      outside C ≠ inside (A₁ ∪ P) ∧ outside C ≠ inside (A₂ ∪ P) ∧
        inside (A₁ ∪ P) ≠ inside (A₂ ∪ P) ∧
      frontier (outside C) = C ∧ frontier (inside (A₁ ∪ P)) = A₁ ∪ P ∧
        frontier (inside (A₂ ∪ P)) = A₂ ∪ P :=
  general_crosscut_three_regions hjordan h hcut h.hasArcCollars

end Schoenflies
