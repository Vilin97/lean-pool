/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.SquareMesh
public import LeanPool.Schoenflies.FaceCycles

/-!
# The inner grid of the anchored square mesh: 2-connectivity and the outer cycle

`Schoenflies/SquareMesh.lean` delivers the geometry of `prop:anchored-square-mesh` — the
diameter bound, the anchors, the inward edges at the fresh points, and connectedness of
`|T| ∖ S` — and leaves two clauses open, both of them combinatorial:

* clause 5, *the skeleton of `T` is 2-connected*, is absent;
* clause 3 is proved only as a point-set equation, never as a **cycle** of the graph.

This module supplies both for the object the blueprint's own proof of the proposition is about:
the **rectangular grid**. See "What this does and does not close" below for exactly what the
integrator still has to do.

## The grid, concretely

Two coordinate functions `xc yc : ℕ → ℝ` and two sizes `m n : ℕ` fix a grid: the vertices are
the `(m+1)(n+1)` points `gridPt xc yc i j = (xc i, yc j)`, the edges are the `m(n+1)`
horizontal steps `gridHEdge` and the `(m+1)n` vertical steps `gridVEdge`. Everything is a
`def` — an existentially quantified grid could not be refined against a second one, which is
what Part II does.

The hypotheses on the coordinates are exactly as strong as each statement needs, and no
stronger: 2-connectivity needs only that **consecutive** coordinates differ, the outer cycle
needs the coordinates **distinct** (`Set.InjOn xc (Set.Iic m)`), and only the drawing — the
clause that makes the grid a plane graph — needs them **increasing**
(`StrictMonoOn xc (Set.Iic m)`).

The graph is `pieceListGraph (gridEdges xc yc m n)`, where `pieceListGraph` is the general
"a list of straight segments, read as a graph" constructor: an edge is a `Piece`, and it links
exactly its two ends. `pieceListGraph` is `overlayGraph` without the subdivision — the vertices
are the ends of the listed segments and nothing is cut — and its point is that
`pieceListGraph l₁ ∪ pieceListGraph l₂ = pieceListGraph (l₁ ++ l₂)` **on the nose**
(`pieceListGraph_union`), so that the blueprint's "add these finitely many cycles one at a
time" is list concatenation and every union is an equation rather than an inclusion.

## 2-connectivity: two nested chains of `lem:union-two-connected`

The blueprint says "the inner grid is 2-connected by the same ear construction used for `K`".
The ear construction is replaced here by two applications of `Graph.IsTwoConnected.union`,
which is shorter and needs no ear at all:

* one **cell** — the boundary of a single rectangle of the grid — is a quadrilateral, and
  `Graph.isTwoConnected_of_quad` proves any quadrilateral 2-connected directly from the
  definition (delete a vertex; the other three are still a path);
* a **strip** (one column of cells) is the union of its cells, consecutive cells sharing the
  horizontal edge between them, hence two vertices;
* the **grid** is the union of its strips, consecutive strips sharing the whole vertical line
  between them, hence again two vertices.

Both chains need at least two vertices in common at every step, so both need `1 ≤ m` and
`1 ≤ n`: a grid with a single row of points is a path and is not 2-connected. That is the
degenerate case, and it is a hypothesis, not an oversight.

## The outer cycle

The boundary walk goes once round the four sides, `gridBoundaryEdge` and `gridBoundaryPt`
naming the `2m + 2n` edges and vertices in order by a four-way `if` on the index. Everything
about the walk is then arithmetic in `ℕ`, which `omega` decides.
`gridGraph_isCycleThrough_boundary` is a `Graph.IsCycleThrough` of the grid graph — the
distinguished outer cycle — and `edgesCover_gridBoundary` computes what it occupies: for
increasing coordinates it is exactly the frame of the bounding rectangle, and for the grid on
`[-1,1]²` that frame is `modelCurve`, i.e. `S` (`edgesCover_gridBoundary_modelCurve`,
`gridGraph_outer_cycle`). That is the cycle `thm:finite-transfer`(b) asks for, in the form it
asks for it.

The grid is also shown to be a **plane graph** (`gridGraph_isDrawing`), so the outer cycle is a
Jordan curve (`gridBoundary_isJordanCurve`) and the whole face machinery applies to it.

## What this does and does not close

**Closed.** Both clauses, for the rectangular grid, from an explicit construction, together
with the drawing that makes the grid a plane graph.

**Not closed.** Neither clause is transported to `Schoenflies.squareMesh`, and the reason is
structural, not a matter of effort: `squareMesh` is `overlayGraph` applied to a list of
segments *and an unspecified list of cut points* obtained from `exists_cut_points` by choice.
Its edges are therefore the pieces of a subdivision nobody can enumerate, so neither "the
edges on `S` form a cycle" nor "the rings are cycles glued along the spokes" is available
without first proving that the subdivision of a segment at a finite point set is a **path** —
a theorem no module on `main` has. The honest statement of the missing collar step is
`Graph.IsTwoConnected.attach_cycles` below: it takes a 2-connected hub `K` and finitely many
2-connected pieces each meeting `K` in two distinct vertices, and concludes for the union.
Instantiating it at `squareMesh` needs the collar rectangles of the mesh as cycles, which is
exactly the enumeration that is missing.

**A degenerate case that would have to be excluded.** `squareMesh δ fresh anchors` is *not*
2-connected when `fresh` has fewer than two distinct points, so the missing theorem cannot be
stated without a hypothesis. With `fresh = []` the mesh is `meshCount δ` pairwise disjoint
concentric ring frames and is not even connected. With one fresh point `z` the spoke at `z` is
the only thing joining the rings, so every vertex of that spoke is a cut vertex: deleting the
one at radius `k/N` separates the rings inside it from the rings outside. Two fresh points are
what make the rings and the two spokes a chain of quadrilaterals, which is the same picture the
grid presents here. The corresponding hypothesis for the grid is `1 ≤ m` and `1 ≤ n`, and it is
carried explicitly by every theorem below that needs it.

## Blueprint

* `prop:anchored-square-mesh`, clause 5, for the inner grid — `gridGraph_isTwoConnected`.
* `prop:anchored-square-mesh`, clause 3, as a cycle — `gridGraph_isCycleThrough_boundary`
  together with `edgesCover_gridBoundary`, `edgesCover_gridBoundary_modelCurve` and the
  packaged `gridGraph_outer_cycle`.
* `lem:polygonal-overlay`, the drawing clause, for the grid — `gridGraph_isDrawing`.
* `lem:union-two-connected` — used through `Graph.IsTwoConnected.union`; iterated here as
  `Graph.IsTwoConnected.attach_cycles`, which is the blueprint's "adding these finitely many
  cycles one at a time".
* `pieceListGraph`, `pieceListGraph_union` — the list-of-segments graph, and the fact that its
  unions are concatenations.
-/

public section

open Metric Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G : Graph α β}

/-! ### A quadrilateral is 2-connected

The base case of both chains below. The blueprint reaches it through the ear decomposition
(`lem:subdivision-ear-preserve` applied to a cycle); here it is read straight off the
definition of `Graph.IsTwoConnected`, because a four-vertex graph is small enough that
"delete one vertex and the rest is still connected" is four applications of one lemma. -/

/-- **A four-cycle is 2-connected.** No hypothesis on `G` beyond the four edges, the four
distinct vertices, and the fact that there are no other vertices. -/
theorem isTwoConnected_of_quad {e₁ e₂ e₃ e₄ : β} {a b c d : α}
    (h₁ : G.IsLink e₁ a b) (h₂ : G.IsLink e₂ b c) (h₃ : G.IsLink e₃ c d) (h₄ : G.IsLink e₄ d a)
    (hV : ∀ v ∈ V(G), v = a ∨ v = b ∨ v = c ∨ v = d)
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hda : d ≠ a) (hac : a ≠ c) (hbd : b ≠ d) :
    G.IsTwoConnected := by
  -- Deleting a vertex keeps every link neither of whose ends was the one deleted.
  have dl : ∀ {f : β} {u v x : α}, G.IsLink f u v → u ≠ x → v ≠ x →
      (G.deleteVerts {x}).IsLink f u v := by
    intro f u v x h hu hv
    exact (deleteVerts_isLink _ _).2 ⟨h, by simpa using hu, by simpa using hv⟩
  -- After a deletion the three survivors form a path `p — q — r`; `q` is the hub.
  have main : ∀ (x p q r : α) (f g : β), G.IsLink f p q → G.IsLink g q r →
      p ≠ x → q ≠ x → r ≠ x → (∀ v ∈ V(G), v = x ∨ v = p ∨ v = q ∨ v = r) →
      (G.deleteVerts {x}).Connected := by
    intro x p q r f g hf hg hp hq hr hcov
    refine Connected.of_hub (mem_deleteVerts_singleton_of_ne hf.right_mem hq) ?_
    intro v hv
    obtain ⟨hvG, hvx⟩ := mem_deleteVerts_singleton.1 hv
    rcases hcov v hvG with rfl | rfl | rfl | rfl
    · exact absurd rfl hvx
    · exact (Reaches.of_isLink (dl hf hp hq)).symm
    · exact Reaches.refl (mem_deleteVerts_singleton_of_ne hf.right_mem hq)
    · exact Reaches.of_isLink (dl hg hq hr)
  refine ⟨⟨a, h₁.left_mem, b, h₁.right_mem, c, h₂.right_mem, hab, hac, hbc⟩, ?_, ?_⟩
  · refine Connected.of_hub h₁.left_mem fun v hv ↦ ?_
    rcases hV v hv with rfl | rfl | rfl | rfl
    · exact Reaches.refl h₁.left_mem
    · exact Reaches.of_isLink h₁
    · exact (Reaches.of_isLink h₁).trans (Reaches.of_isLink h₂)
    · exact (Reaches.of_isLink h₄).symm
  · intro x _
    rcases em (x = a) with rfl | hxa
    · exact main x b c d e₂ e₃ h₂ h₃ (Ne.symm hab) (Ne.symm hac) hda
        fun v hv ↦ by rcases hV v hv with h | h | h | h <;> tauto
    rcases em (x = b) with rfl | hxb
    · exact main x c d a e₃ e₄ h₃ h₄ (Ne.symm hbc) (Ne.symm hbd) hab
        fun v hv ↦ by rcases hV v hv with h | h | h | h <;> tauto
    rcases em (x = c) with rfl | hxc
    · exact main x d a b e₄ e₁ h₄ h₁ (Ne.symm hcd) hac hbc
        fun v hv ↦ by rcases hV v hv with h | h | h | h <;> tauto
    rcases em (x = d) with rfl | hxd
    · exact main x a b c e₁ e₂ h₁ h₂ (Ne.symm hda) hbd hcd
        fun v hv ↦ by rcases hV v hv with h | h | h | h <;> tauto
    · -- Deleting a vertex the graph does not have changes nothing.
      refine Connected.deleteVerts_singleton_of_notMem ?_ fun hx ↦ ?_
      · refine Connected.of_hub h₁.left_mem fun v hv ↦ ?_
        rcases hV v hv with rfl | rfl | rfl | rfl
        · exact Reaches.refl h₁.left_mem
        · exact Reaches.of_isLink h₁
        · exact (Reaches.of_isLink h₁).trans (Reaches.of_isLink h₂)
        · exact (Reaches.of_isLink h₄).symm
      · rcases hV x hx with rfl | rfl | rfl | rfl
        exacts [hxa rfl, hxb rfl, hxc rfl, hxd rfl]

/-! ### Attaching finitely many pieces to a 2-connected hub

`prop:anchored-square-mesh`: *"The boundary of every collar rectangle is a cycle sharing with
the inner grid at least the two endpoints of its inner boundary arc. Adding these finitely many
cycles one at a time and applying `lem:union-two-connected` proves that the full mesh is
2-connected."*

`Graph.chainUnion_isTwoConnected` (`Schoenflies/OuterChain.lean`) iterates the same lemma along
a chain in which **consecutive** members meet. Here every piece meets the **hub**, which is
what the collar rectangles do — each meets the inner grid, but two collar rectangles on
opposite sides of the square meet nothing of each other. The two statements are independent;
the integrator may want them beside each other. -/

/-- The hub `K` with the pieces `Γ 0, …, Γ (m-1)` glued on, one at a time. -/
def attachUnion (K : Graph α β) (Γ : ℕ → Graph α β) : ℕ → Graph α β
  | 0 => K
  | (m + 1) => (attachUnion K Γ m).union (Γ m)

@[simp] theorem attachUnion_zero (K : Graph α β) (Γ : ℕ → Graph α β) :
    attachUnion K Γ 0 = K := rfl

@[simp] theorem attachUnion_succ (K : Graph α β) (Γ : ℕ → Graph α β) (m : ℕ) :
    attachUnion K Γ (m + 1) = (attachUnion K Γ m).union (Γ m) := rfl

theorem le_attachUnion (K : Graph α β) (Γ : ℕ → Graph α β) (m : ℕ) :
    K ≤ attachUnion K Γ m := by
  induction m with
  | zero => exact le_rfl
  | succ m ih => exact ih.trans (left_le_union _ _)

theorem attachUnion_le {K : Graph α β} {Γ : ℕ → Graph α β} {m : ℕ} (hK : K ≤ G)
    (hΓ : ∀ q, q < m → Γ q ≤ G) : attachUnion K Γ m ≤ G := by
  induction m with
  | zero => exact hK
  | succ m ih => exact union_le (ih fun q hq => hΓ q (by omega)) (hΓ m (by omega))

theorem piece_le_attachUnion {K : Graph α β} {Γ : ℕ → Graph α β} {m q : ℕ} (hK : K ≤ G)
    (hΓ : ∀ r, r < m → Γ r ≤ G) (hq : q < m) : Γ q ≤ attachUnion K Γ m := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hq with h | rfl
    · exact (ih (fun r hr => hΓ r (by omega)) h).trans (left_le_union _ _)
    · exact (Compatible.of_le_le (attachUnion_le hK fun r hr => hΓ r (by omega))
        (hΓ q (by omega))).right_le_union

/-- **`lem:union-two-connected`, iterated at a hub.** A 2-connected `K` and finitely many
2-connected pieces, each meeting `K` in two distinct vertices, have 2-connected union. -/
theorem IsTwoConnected.attach_cycles {K : Graph α β} {Γ : ℕ → Graph α β} {m : ℕ}
    (hK : K.IsTwoConnected) (hKG : K ≤ G) (hΓG : ∀ q, q < m → Γ q ≤ G)
    (hΓ : ∀ q, q < m → (Γ q).IsTwoConnected)
    (hmeet : ∀ q, q < m → ∃ a b : α, a ≠ b ∧ a ∈ V(K) ∧ a ∈ V(Γ q) ∧ b ∈ V(K) ∧ b ∈ V(Γ q)) :
    (attachUnion K Γ m).IsTwoConnected := by
  induction m with
  | zero => exact hK
  | succ m ih =>
    obtain ⟨a, b, hab, haK, haΓ, hbK, hbΓ⟩ := hmeet m (by omega)
    have hih := ih (fun q hq => hΓG q (by omega)) (fun q hq => hΓ q (by omega))
      fun q hq => hmeet q (by omega)
    have hcompat : (attachUnion K Γ m).Compatible (Γ m) :=
      Compatible.of_le_le (attachUnion_le hKG fun q hq => hΓG q (by omega)) (hΓG m (by omega))
    exact hih.union hcompat (hΓ m (by omega)) hab ((le_attachUnion K Γ m).vertexSet_mono haK)
      haΓ ((le_attachUnion K Γ m).vertexSet_mono hbK) hbΓ

/-! ### A march along indices is a path

The boundary walk of the grid is a march: vertices `p s, p (s+1), …` joined by edges
`q s, q (s+1), …`. The freshness clause of `Graph.IsPath` is then exactly the injectivity of
`p` on the index range, because an edge of the chain is incident with nothing but its own two
ends (`Graph.Inc.eq_or_eq_of_isLink`). -/

/-- **A chain of edges through pairwise distinct vertices is a path.** -/
theorem isPath_range' {p : ℕ → α} {q : ℕ → β} :
    ∀ (k s : ℕ), (∀ i, s ≤ i → i < s + k → G.IsLink (q i) (p i) (p (i + 1))) →
      (∀ i j, s ≤ i → i ≤ s + k → s ≤ j → j ≤ s + k → p i = p j → i = j) →
      p (s + k) ∈ V(G) → G.IsPath (p s) ((List.range' s k).map q) (p (s + k)) := by
  intro k
  induction k with
  | zero => exact fun s _ _ hmem => IsPath.nil hmem
  | succ k ih =>
    intro s hlink hinj hmem
    have hstep : G.IsLink (q s) (p s) (p (s + 1)) := hlink s le_rfl (by omega)
    have htail : G.IsPath (p (s + 1)) ((List.range' (s + 1) k).map q) (p (s + 1 + k)) :=
      ih (s + 1) (fun i h1 h2 => hlink i (by omega) (by omega))
        (fun i j h1 h2 h3 h4 h => hinj i j (by omega) (by omega) (by omega) (by omega) h)
        (by rw [show s + 1 + k = s + (k + 1) by omega]; exact hmem)
    have hfresh : p s ∉ G.walkVertices (p (s + 1)) ((List.range' (s + 1) k).map q) := by
      intro hmemw
      rcases mem_walkVertices_iff.1 hmemw with h | hcov
      · exact absurd (hinj s (s + 1) le_rfl (by omega) (by omega) (by omega) h) (by omega)
      · obtain ⟨-, ⟨i, hi, rfl⟩, hinc⟩ :
            ∃ e, (∃ i ∈ List.range' (s + 1) k, q i = e) ∧ G.Inc e (p s) := by
          obtain ⟨e, he, hinc⟩ := hcov
          exact ⟨e, List.mem_map.1 he, hinc⟩
        rw [List.mem_range'_1] at hi
        rcases hinc.eq_or_eq_of_isLink (hlink i (by omega) (by omega)) with h | h
        · exact absurd (hinj s i le_rfl (by omega) (by omega) (by omega) h) (by omega)
        · exact absurd (hinj s (i + 1) le_rfl (by omega) (by omega) (by omega) h) (by omega)
    rw [List.range'_succ, List.map_cons, show s + (k + 1) = s + 1 + k by omega]
    exact IsPath.cons hstep htail hfresh

end Graph

namespace Schoenflies

/-! ### The graph carried by a list of segments

`overlayGraph` subdivides; this does not. When the segments are already in general position —
which for a grid they are, by construction — no subdivision is wanted, and what is gained is
that unions are concatenations.

`Schoenflies/ArcComplement.lean` has the same construction indexed by a `Set Piece`, under the
name `segGraph`, and `pieceListGraph l` is `segGraph {P | P ∈ l}`. The two were written in
parallel and collided at merge; they are kept apart for now because this module's proofs run on
the list and the other's on the set. If a third consumer appears, hoist the set version into
`Schoenflies/OverlayGraph.lean` beside `endSet` and derive this one from it. -/

/-- The graph whose edges are the listed segments and whose vertices are their ends. -/
def pieceListGraph (edges : List Piece) : Graph Plane Piece where
  vertexSet := endSet edges
  IsLink P x y := P ∈ edges ∧ ((x = P.1 ∧ y = P.2) ∨ (x = P.2 ∧ y = P.1))
  edgeSet := {P | P ∈ edges}
  isLink_symm := fun _ _ => ⟨fun _ _ h => ⟨h.1, by tauto⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro P x y v w ⟨-, hxy⟩ ⟨-, hvw⟩
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  edge_mem_iff_exists_isLink := by
    intro P
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun hP => ⟨P.1, P.2, hP, Or.inl ⟨rfl, rfl⟩⟩, fun ⟨_, _, hP, _⟩ => hP⟩
  left_mem_of_isLink := by
    rintro P x y ⟨hP, h⟩
    exact ⟨P, hP, by tauto⟩

@[simp] theorem pieceListGraph_vertexSet (l : List Piece) : V(pieceListGraph l) = endSet l := rfl

@[simp] theorem pieceListGraph_mem_edgeSet {l : List Piece} {P : Piece} :
    P ∈ E(pieceListGraph l) ↔ P ∈ l := Iff.rfl

@[simp] theorem pieceListGraph_isLink {l : List Piece} {P : Piece} {x y : Plane} :
    (pieceListGraph l).IsLink P x y ↔
      P ∈ l ∧ ((x = P.1 ∧ y = P.2) ∨ (x = P.2 ∧ y = P.1)) := Iff.rfl

theorem pieceListGraph_mem_vertexSet {l : List Piece} {v : Plane} :
    v ∈ V(pieceListGraph l) ↔ ∃ P ∈ l, v = P.1 ∨ v = P.2 := Iff.rfl

/-- The canonical link of a listed segment: it joins its own two ends. -/
theorem pieceListGraph_isLink_self {l : List Piece} {P : Piece} (h : P ∈ l) :
    (pieceListGraph l).IsLink P P.1 P.2 := ⟨h, Or.inl ⟨rfl, rfl⟩⟩

theorem mem_vertexSet_pieceListGraph_left {l : List Piece} {P : Piece} (h : P ∈ l) :
    P.1 ∈ V(pieceListGraph l) := ⟨P, h, Or.inl rfl⟩

theorem mem_vertexSet_pieceListGraph_right {l : List Piece} {P : Piece} (h : P ∈ l) :
    P.2 ∈ V(pieceListGraph l) := ⟨P, h, Or.inr rfl⟩

/-- An end of a listed segment is incident with it. -/
theorem pieceListGraph_inc {l : List Piece} {P : Piece} {v : Plane} (hP : P ∈ l)
    (h : v = P.1 ∨ v = P.2) : (pieceListGraph l).Inc P v := by
  rcases h with rfl | rfl
  · exact ⟨P.2, hP, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨P.1, hP, Or.inr ⟨rfl, rfl⟩⟩

/-- Two plane points with the same coordinates are equal.

`Schoenflies.Plane.coord_ext` in `Schoenflies/JordanSeparates.lean` is the same fact in a more
general form; that module is not on this one's import path, and the integrator should collapse
the two if it ever is. -/
theorem plane_eq_of_coords {z w : Plane} (h0 : z 0 = w 0) (h1 : z 1 = w 1) : z = w := by
  ext k
  fin_cases k
  exacts [h0, h1]

theorem endSet_append (l l' : List Piece) : endSet (l ++ l') = endSet l ∪ endSet l' := by
  ext v
  simp only [endSet, Set.mem_ofPred_eq, Set.mem_union, List.mem_append]
  constructor
  · rintro ⟨P, hP | hP, h⟩
    exacts [Or.inl ⟨P, hP, h⟩, Or.inr ⟨P, hP, h⟩]
  · rintro (⟨P, hP, h⟩ | ⟨P, hP, h⟩)
    exacts [⟨P, Or.inl hP, h⟩, ⟨P, Or.inr hP, h⟩]

instance pieceListGraph_finite (l : List Piece) : Graph.Finite (pieceListGraph l) where
  finite_vertexSet := finite_endSet l
  finite_edgeSet := l.finite_toSet

/-- What a segment graph occupies is what its segments occupy: every vertex is an end of a
listed segment, so the vertices add nothing. -/
theorem pieceListGraph_pointSet (l : List Piece) :
    Graph.pointSet (pieceListGraph l) segmentDrawing = cover l := by
  ext z
  simp only [Graph.pointSet, Set.mem_union, Set.mem_iUnion, exists_prop, pieceListGraph_vertexSet,
    endSet, Set.mem_ofPred_eq, pieceListGraph_mem_edgeSet, edgeArc_segmentDrawing, cover]
  constructor
  · rintro (⟨P, hP, hzP⟩ | ⟨P, hP, hzP⟩)
    · refine ⟨P, hP, ?_⟩
      rcases hzP with rfl | rfl
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _
    · exact ⟨P, hP, hzP⟩
  · rintro ⟨P, hP, hzP⟩
    exact Or.inr ⟨P, hP, hzP⟩

theorem pieceListGraph_mono {l l' : List Piece} (h : l ⊆ l') :
    pieceListGraph l ≤ pieceListGraph l' where
  vertexSet_mono := by
    rintro v ⟨P, hP, hv⟩
    exact ⟨P, h hP, hv⟩
  isLink_mono := by
    rintro P x y ⟨hP, hxy⟩
    exact ⟨h hP, hxy⟩

/-- Two segment graphs never disagree about a shared edge: an edge is its own pair of ends. -/
theorem pieceListGraph_compatible (l l' : List Piece) :
    (pieceListGraph l).Compatible (pieceListGraph l') := by
  intro P hP hP' x y
  exact ⟨fun h => ⟨hP', h.2⟩, fun h => ⟨hP, h.2⟩⟩

/-- **The union of two segment graphs is the segment graph of the concatenation.** This is the
whole reason for `pieceListGraph`: it turns "glue one more cycle on" into an equation. -/
theorem pieceListGraph_union (l l' : List Piece) :
    (pieceListGraph l).union (pieceListGraph l') = pieceListGraph (l ++ l') := by
  refine Graph.eq_of_le_of_subset_subset
    (Graph.union_le (pieceListGraph_mono (List.subset_append_left _ _))
      (pieceListGraph_mono (List.subset_append_right _ _))) ?_ ?_
  · rw [pieceListGraph_vertexSet, endSet_append, Graph.vertexSet_union]
    exact subset_rfl
  · rintro P hP
    rcases List.mem_append.1 hP with h | h
    exacts [Or.inl h, Or.inr h]

/-! ### The rectangular grid

Two coordinate functions and two sizes. Nothing here asks the coordinates to be sorted: the
combinatorics needs only that **consecutive** coordinates differ, which is exactly what makes
each cell a genuine quadrilateral. Sortedness enters only with the geometry of the outer
cycle. -/

/-- The grid point with coordinate indices `(i, j)`. -/
@[expose] def gridPt (xc yc : ℕ → ℝ) (i j : ℕ) : Plane := Plane.mk (xc i) (yc j)

/-- The horizontal grid edge from `(i, j)` to `(i+1, j)`. -/
def gridHEdge (xc yc : ℕ → ℝ) (i j : ℕ) : Piece := (gridPt xc yc i j, gridPt xc yc (i + 1) j)

/-- The vertical grid edge from `(i, j)` to `(i, j+1)`. -/
def gridVEdge (xc yc : ℕ → ℝ) (i j : ℕ) : Piece := (gridPt xc yc i j, gridPt xc yc i (j + 1))

theorem gridPt_ne_of_fst {xc yc : ℕ → ℝ} {i i' j j' : ℕ} (h : xc i ≠ xc i') :
    gridPt xc yc i j ≠ gridPt xc yc i' j' := fun he => by
  have := congrArg (fun p : Plane => p 0) he
  simp only [gridPt, Plane.mk_zero] at this
  exact h this

theorem gridPt_ne_of_snd {xc yc : ℕ → ℝ} {i i' j j' : ℕ} (h : yc j ≠ yc j') :
    gridPt xc yc i j ≠ gridPt xc yc i' j' := fun he => by
  have := congrArg (fun p : Plane => p 1) he
  simp only [gridPt, Plane.mk_one] at this
  exact h this

/-- The four sides of the cell whose lower-left corner is `(i, j)`, listed bottom, right, top,
left. -/
def cellEdges (xc yc : ℕ → ℝ) (i j : ℕ) : List Piece :=
  [gridHEdge xc yc i j, gridVEdge xc yc (i + 1) j, gridHEdge xc yc i (j + 1),
    gridVEdge xc yc i j]

/-- One column of `n` cells, the cells `(i, 0), …, (i, n-1)`. -/
def stripEdges (xc yc : ℕ → ℝ) (i n : ℕ) : List Piece :=
  (List.range n).flatMap (cellEdges xc yc i)

/-- The `m × n` grid: `m` columns of `n` cells. -/
def gridEdges (xc yc : ℕ → ℝ) (m n : ℕ) : List Piece :=
  (List.range m).flatMap fun i => stripEdges xc yc i n

/-- **The grid graph**: the `m × n` rectangular grid on the coordinates `xc`, `yc`, as a plane
graph with straight edges. -/
def gridGraph (xc yc : ℕ → ℝ) (m n : ℕ) : Graph Plane Piece := pieceListGraph (gridEdges xc yc m n)

theorem stripEdges_succ (xc yc : ℕ → ℝ) (i n : ℕ) :
    stripEdges xc yc i (n + 1) = stripEdges xc yc i n ++ cellEdges xc yc i n := by
  rw [stripEdges, stripEdges, List.range_succ, List.flatMap_append, List.flatMap_singleton]

theorem stripEdges_one (xc yc : ℕ → ℝ) (i : ℕ) :
    stripEdges xc yc i 1 = cellEdges xc yc i 0 := by
  rw [stripEdges_succ]; simp [stripEdges]

theorem cellEdges_subset_stripEdges {xc yc : ℕ → ℝ} {i j n : ℕ} (h : j < n) :
    cellEdges xc yc i j ⊆ stripEdges xc yc i n :=
  fun _ hP => List.mem_flatMap.2 ⟨j, List.mem_range.2 h, hP⟩

theorem gridEdges_succ (xc yc : ℕ → ℝ) (m n : ℕ) :
    gridEdges xc yc (m + 1) n = gridEdges xc yc m n ++ stripEdges xc yc m n := by
  rw [gridEdges, gridEdges, List.range_succ, List.flatMap_append, List.flatMap_singleton]

theorem gridEdges_one (xc yc : ℕ → ℝ) (n : ℕ) :
    gridEdges xc yc 1 n = stripEdges xc yc 0 n := by
  rw [gridEdges_succ]; simp [gridEdges]

theorem stripEdges_subset_gridEdges {xc yc : ℕ → ℝ} {i m n : ℕ} (h : i < m) :
    stripEdges xc yc i n ⊆ gridEdges xc yc m n :=
  fun _ hP => List.mem_flatMap.2 ⟨i, List.mem_range.2 h, hP⟩

/-! ### The cell -/

/-- **One cell of the grid is 2-connected.** Its boundary is a quadrilateral, so this is
`Graph.isTwoConnected_of_quad` with the four corners named. Only the two consecutive-coordinate
inequalities are used. -/
theorem cellGraph_isTwoConnected {xc yc : ℕ → ℝ} {i j : ℕ} (hx : xc i ≠ xc (i + 1))
    (hy : yc j ≠ yc (j + 1)) : (pieceListGraph (cellEdges xc yc i j)).IsTwoConnected := by
  have h₁ : gridHEdge xc yc i j ∈ cellEdges xc yc i j := by simp [cellEdges]
  have h₂ : gridVEdge xc yc (i + 1) j ∈ cellEdges xc yc i j := by simp [cellEdges]
  have h₃ : gridHEdge xc yc i (j + 1) ∈ cellEdges xc yc i j := by simp [cellEdges]
  have h₄ : gridVEdge xc yc i j ∈ cellEdges xc yc i j := by simp [cellEdges]
  refine Graph.isTwoConnected_of_quad (a := gridPt xc yc i j) (b := gridPt xc yc (i + 1) j)
    (c := gridPt xc yc (i + 1) (j + 1)) (d := gridPt xc yc i (j + 1))
    (pieceListGraph_isLink_self h₁) (pieceListGraph_isLink_self h₂)
    (pieceListGraph_isLink_self h₃).symm (pieceListGraph_isLink_self h₄).symm ?_
    (gridPt_ne_of_fst hx) (gridPt_ne_of_snd hy) (gridPt_ne_of_fst (Ne.symm hx))
    (gridPt_ne_of_snd (Ne.symm hy)) (gridPt_ne_of_fst hx) (gridPt_ne_of_fst (Ne.symm hx))
  rintro v ⟨P, hP, hv⟩
  simp only [cellEdges, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl <;>
    simp only [gridHEdge, gridVEdge] <;> tauto

/-! ### The strip, then the grid

Two chains of `Graph.IsTwoConnected.union`, and the two shared vertices are in each case the
two ends of one edge that both parts contain. -/

/-- **A column of cells is 2-connected.** Consecutive cells share the horizontal edge between
them, hence its two ends. -/
theorem stripGraph_isTwoConnected {xc yc : ℕ → ℝ} {i : ℕ} (hx : xc i ≠ xc (i + 1)) :
    ∀ k : ℕ, (∀ j ≤ k, yc j ≠ yc (j + 1)) →
      (pieceListGraph (stripEdges xc yc i (k + 1))).IsTwoConnected := by
  intro k
  induction k with
  | zero =>
    intro hy
    rw [stripEdges_one]
    exact cellGraph_isTwoConnected hx (hy 0 le_rfl)
  | succ k ih =>
    intro hy
    -- The edge shared by the new cell and the previous one is the horizontal step at height
    -- `k+1`: the top of cell `(i, k)` and the bottom of cell `(i, k+1)`.
    have hold : gridHEdge xc yc i (k + 1) ∈ stripEdges xc yc i (k + 1) :=
      cellEdges_subset_stripEdges (Nat.lt_succ_self k) (by simp [cellEdges])
    have hnew : gridHEdge xc yc i (k + 1) ∈ cellEdges xc yc i (k + 1) := by simp [cellEdges]
    rw [stripEdges_succ, ← pieceListGraph_union]
    exact (ih fun j hj => hy j (by omega)).union (pieceListGraph_compatible _ _)
      (cellGraph_isTwoConnected hx (hy (k + 1) le_rfl)) (gridPt_ne_of_fst hx)
      (mem_vertexSet_pieceListGraph_left hold) (mem_vertexSet_pieceListGraph_left hnew)
      (mem_vertexSet_pieceListGraph_right hold) (mem_vertexSet_pieceListGraph_right hnew)

/-- **The grid is 2-connected.** Each new column shares with what is already there the whole
vertical line between them — in particular the two ends of its lowest edge.

The two size hypotheses are not decoration: a grid one point wide is a path, and a path is not
2-connected. -/
theorem gridGraph_isTwoConnected_aux {xc yc : ℕ → ℝ} {n : ℕ}
    (hy : ∀ j ≤ n, yc j ≠ yc (j + 1)) :
    ∀ k : ℕ, (∀ i ≤ k, xc i ≠ xc (i + 1)) →
      (pieceListGraph (gridEdges xc yc (k + 1) (n + 1))).IsTwoConnected := by
  intro k
  induction k with
  | zero =>
    intro hx
    rw [gridEdges_one]
    exact stripGraph_isTwoConnected (hx 0 le_rfl) n hy
  | succ k ih =>
    intro hx
    -- The shared edge is the lowest vertical step of the new column: the right side of cell
    -- `(k, 0)` and the left side of cell `(k+1, 0)`.
    have hold : gridVEdge xc yc (k + 1) 0 ∈ gridEdges xc yc (k + 1) (n + 1) :=
      stripEdges_subset_gridEdges (Nat.lt_succ_self k)
        (cellEdges_subset_stripEdges (Nat.succ_pos n) (by simp [cellEdges]))
    have hnew : gridVEdge xc yc (k + 1) 0 ∈ stripEdges xc yc (k + 1) (n + 1) :=
      cellEdges_subset_stripEdges (Nat.succ_pos n) (by simp [cellEdges])
    rw [gridEdges_succ, ← pieceListGraph_union]
    exact (ih fun i hi => hx i (by omega)).union (pieceListGraph_compatible _ _)
      (stripGraph_isTwoConnected (hx (k + 1) le_rfl) n hy) (gridPt_ne_of_snd (hy 0 (by omega)))
      (mem_vertexSet_pieceListGraph_left hold) (mem_vertexSet_pieceListGraph_left hnew)
      (mem_vertexSet_pieceListGraph_right hold) (mem_vertexSet_pieceListGraph_right hnew)

/-- **`prop:anchored-square-mesh`, clause 5, for the inner grid.** -/
theorem gridGraph_isTwoConnected {xc yc : ℕ → ℝ} {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hx : ∀ i < m, xc i ≠ xc (i + 1)) (hy : ∀ j < n, yc j ≠ yc (j + 1)) :
    (gridGraph xc yc m n).IsTwoConnected := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l, n = l + 1 := ⟨n - 1, by omega⟩
  exact gridGraph_isTwoConnected_aux (fun j hj => hy j (by omega)) k fun i hi => hx i (by omega)

/-! ### Which grid edges exist

Two membership lemmas, both by the same trick: a horizontal edge at height `n` is the *top*
of a cell rather than the bottom of one, and a vertical edge on the line `i = m` is the *right*
side of a cell rather than the left. -/

theorem gridHEdge_mem_gridEdges {xc yc : ℕ → ℝ} {i j m n : ℕ} (hi : i < m) (hj : j ≤ n)
    (hn : 1 ≤ n) : gridHEdge xc yc i j ∈ gridEdges xc yc m n := by
  rcases lt_or_ge j n with h | h
  · exact stripEdges_subset_gridEdges hi (cellEdges_subset_stripEdges h (by simp [cellEdges]))
  · obtain rfl : j = n := le_antisymm hj h
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact stripEdges_subset_gridEdges hi
      (cellEdges_subset_stripEdges (Nat.lt_succ_self k) (by simp [cellEdges]))

theorem gridVEdge_mem_gridEdges {xc yc : ℕ → ℝ} {i j m n : ℕ} (hi : i ≤ m) (hj : j < n)
    (hm : 1 ≤ m) : gridVEdge xc yc i j ∈ gridEdges xc yc m n := by
  rcases lt_or_ge i m with h | h
  · exact stripEdges_subset_gridEdges h (cellEdges_subset_stripEdges hj (by simp [cellEdges]))
  · obtain rfl : i = m := le_antisymm hi h
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    exact stripEdges_subset_gridEdges (Nat.lt_succ_self k)
      (cellEdges_subset_stripEdges hj (by simp [cellEdges]))

/-- **The edges of the grid, classified.** A grid edge is a horizontal step in a row, or a
vertical step in a column, and nothing else. -/
theorem mem_gridEdges_iff {xc yc : ℕ → ℝ} {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) {P : Piece} :
    P ∈ gridEdges xc yc m n ↔
      (∃ i < m, ∃ j ≤ n, P = gridHEdge xc yc i j) ∨
        ∃ i ≤ m, ∃ j < n, P = gridVEdge xc yc i j := by
  constructor
  · intro hP
    obtain ⟨i, hi, hPi⟩ := List.mem_flatMap.1 hP
    obtain ⟨j, hj, hPj⟩ := List.mem_flatMap.1 hPi
    rw [List.mem_range] at hi hj
    simp only [cellEdges, List.mem_cons, List.not_mem_nil, or_false] at hPj
    rcases hPj with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨i, hi, j, by omega, rfl⟩
    · exact Or.inr ⟨i + 1, by omega, j, hj, rfl⟩
    · exact Or.inl ⟨i, hi, j + 1, by omega, rfl⟩
    · exact Or.inr ⟨i, by omega, j, hj, rfl⟩
  · rintro (⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, j, hj, rfl⟩)
    · exact gridHEdge_mem_gridEdges hi hj hn
    · exact gridVEdge_mem_gridEdges hi hj hm

/-- **The vertices of the grid are exactly the grid points.** -/
theorem mem_vertexSet_gridGraph_iff {xc yc : ℕ → ℝ} {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {v : Plane} :
    v ∈ V(gridGraph xc yc m n) ↔ ∃ i ≤ m, ∃ j ≤ n, v = gridPt xc yc i j := by
  constructor
  · rintro ⟨P, hP, hv⟩
    rcases (mem_gridEdges_iff hm hn).1 hP with ⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, j, hj, rfl⟩
    · rcases hv with rfl | rfl
      exacts [⟨i, by omega, j, hj, rfl⟩, ⟨i + 1, by omega, j, hj, rfl⟩]
    · rcases hv with rfl | rfl
      exacts [⟨i, hi, j, by omega, rfl⟩, ⟨i, hi, j + 1, by omega, rfl⟩]
  · rintro ⟨i, hi, j, hj, rfl⟩
    -- a grid point is an end of the horizontal edge on one side of it
    rcases lt_or_ge i m with h | h
    · exact mem_vertexSet_pieceListGraph_left (gridHEdge_mem_gridEdges h hj hn)
    · obtain rfl : i = m := le_antisymm hi h
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      exact mem_vertexSet_pieceListGraph_right (gridHEdge_mem_gridEdges (Nat.lt_succ_self k) hj hn)

/-! ### The outer cycle

The boundary of the grid, walked once anticlockwise from the corner `(0,0)`: `m` steps right
along the bottom, `n` up the right side, `m` back along the top, `n` down the left side. The
walk is parametrised by an index `t < 2m + 2n`, and both the vertex and the edge at index `t`
are given by a four-way `if`. Everything about the walk then reduces to arithmetic in `ℕ`,
which `omega` decides; the geometry enters only in `edgesCover_gridBoundary` at the end. -/

/-- The `x`-index of the `t`-th vertex of the boundary walk. -/
def bIdx (m n t : ℕ) : ℕ :=
  if t ≤ m then t else if t ≤ m + n then m else if t ≤ 2 * m + n then 2 * m + n - t else 0

/-- The `y`-index of the `t`-th vertex of the boundary walk. -/
def bIdy (m n t : ℕ) : ℕ :=
  if t ≤ m then 0 else if t ≤ m + n then t - m
    else if t ≤ 2 * m + n then n else 2 * m + 2 * n - t

theorem bIdx_le (m n t : ℕ) : bIdx m n t ≤ m := by unfold bIdx; split_ifs <;> omega

theorem bIdy_le {m n t : ℕ} (h : t ≤ 2 * m + 2 * n) : bIdy m n t ≤ n := by
  unfold bIdy; split_ifs <;> omega

theorem bIdx_bottom {m n t : ℕ} (h : t ≤ m) : bIdx m n t = t := by unfold bIdx; exact ite_eq_left h

theorem bIdy_bottom {m n t : ℕ} (h : t ≤ m) : bIdy m n t = 0 := by unfold bIdy; exact ite_eq_left h

theorem bIdx_right {m n t : ℕ} (h₁ : m ≤ t) (h₂ : t ≤ m + n) : bIdx m n t = m := by
  unfold bIdx; split_ifs <;> omega

theorem bIdy_right {m n t : ℕ} (h₁ : m ≤ t) (h₂ : t ≤ m + n) : bIdy m n t = t - m := by
  unfold bIdy; split_ifs <;> omega

theorem bIdx_top {m n t : ℕ} (h₁ : m + n ≤ t) (h₂ : t ≤ 2 * m + n) :
    bIdx m n t = 2 * m + n - t := by unfold bIdx; split_ifs <;> omega

theorem bIdy_top {m n t : ℕ} (h₁ : m + n ≤ t) (h₂ : t ≤ 2 * m + n) : bIdy m n t = n := by
  unfold bIdy; split_ifs <;> omega

theorem bIdx_left {m n t : ℕ} (h₁ : 2 * m + n ≤ t) (_h₂ : t ≤ 2 * m + 2 * n) :
    bIdx m n t = 0 := by unfold bIdx; split_ifs <;> omega

theorem bIdy_left {m n t : ℕ} (h₁ : 2 * m + n ≤ t) (h₂ : t ≤ 2 * m + 2 * n) :
    bIdy m n t = 2 * m + 2 * n - t := by unfold bIdy; split_ifs <;> omega

/-- **The index pair determines the position on the walk.** Pure arithmetic: the four sides
overlap only at the corners, and there the two descriptions agree.

`1 ≤ m` and `1 ≤ n` are needed and are not slack. With `n = 0` the walk goes out along the
bottom and comes back along the *same* row, so index `t` and index `2m - t` name one point;
this is the degenerate case in which the grid is a path rather than a cycle. -/
theorem bIdx_bIdy_inj {m n t s : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (ht : t < 2 * m + 2 * n)
    (hs : s < 2 * m + 2 * n) (h₁ : bIdx m n t = bIdx m n s) (h₂ : bIdy m n t = bIdy m n s) :
    t = s := by
  unfold bIdx at h₁
  unfold bIdy at h₂
  split_ifs at h₁ h₂ <;> omega

/-- The `t`-th vertex of the boundary walk. -/
def gridBoundaryPt (xc yc : ℕ → ℝ) (m n t : ℕ) : Plane :=
  gridPt xc yc (bIdx m n t) (bIdy m n t)

/-- The `t`-th edge of the boundary walk. -/
def gridBoundaryEdge (xc yc : ℕ → ℝ) (m n t : ℕ) : Piece :=
  if t < m then gridHEdge xc yc t 0
  else if t < m + n then gridVEdge xc yc m (t - m)
  else if t < 2 * m + n then gridHEdge xc yc (2 * m + n - 1 - t) n
  else gridVEdge xc yc 0 (2 * m + 2 * n - 1 - t)

/-- The walk closes up: index `2m + 2n` is the corner it started from. -/
theorem gridBoundaryPt_wrap (xc yc : ℕ → ℝ) (m n : ℕ) :
    gridBoundaryPt xc yc m n (2 * m + 2 * n) = gridBoundaryPt xc yc m n 0 := by
  have e₁ : bIdx m n (2 * m + 2 * n) = 0 := bIdx_left (by omega) (by omega)
  have e₂ : bIdy m n (2 * m + 2 * n) = 0 := by rw [bIdy_left (by omega) (by omega)]; omega
  have e₃ : bIdx m n 0 = 0 := bIdx_bottom (Nat.zero_le m)
  have e₄ : bIdy m n 0 = 0 := bIdy_bottom (Nat.zero_le m)
  rw [gridBoundaryPt, gridBoundaryPt, e₁, e₂, e₃, e₄]

/-- The vertices of the boundary walk are pairwise distinct. -/
theorem gridBoundaryPt_inj {xc yc : ℕ → ℝ} {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hx : Set.InjOn xc (Set.Iic m)) (hy : Set.InjOn yc (Set.Iic n)) {t s : ℕ}
    (ht : t < 2 * m + 2 * n) (hs : s < 2 * m + 2 * n)
    (h : gridBoundaryPt xc yc m n t = gridBoundaryPt xc yc m n s) : t = s := by
  have h0 := congrArg (fun p : Plane => p 0) h
  have h1 := congrArg (fun p : Plane => p 1) h
  simp only [gridBoundaryPt, gridPt, Plane.mk_zero, Plane.mk_one] at h0 h1
  exact bIdx_bIdy_inj hm hn ht hs (hx (bIdx_le m n t) (bIdx_le m n s) h0)
    (hy (bIdy_le (by omega)) (bIdy_le (by omega)) h1)

/-- **Each step of the boundary walk is an edge of the grid**, joining the two vertices it
should. -/
theorem gridBoundary_isLink {xc yc : ℕ → ℝ} {m n t : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (ht : t < 2 * m + 2 * n) :
    (gridGraph xc yc m n).IsLink (gridBoundaryEdge xc yc m n t)
      (gridBoundaryPt xc yc m n t) (gridBoundaryPt xc yc m n (t + 1)) := by
  unfold gridBoundaryEdge gridBoundaryPt gridGraph
  rcases lt_or_ge t m with h₁ | h₁
  · -- along the bottom
    rw [ite_eq_left h₁, bIdx_bottom (by omega), bIdy_bottom (by omega), bIdx_bottom (by omega),
      bIdy_bottom (by omega)]
    exact pieceListGraph_isLink_self (gridHEdge_mem_gridEdges h₁ (Nat.zero_le n) hn)
  rcases lt_or_ge t (m + n) with h₂ | h₂
  · -- up the right side
    rw [ite_eq_right (by omega),
          ite_eq_left h₂, bIdx_right (by omega) (by omega),
      bIdy_right (by omega) (by omega), bIdx_right (by omega) (by omega),
      bIdy_right (by omega) (by omega), show t + 1 - m = (t - m) + 1 by omega]
    exact pieceListGraph_isLink_self (gridVEdge_mem_gridEdges le_rfl (by omega) hm)
  rcases lt_or_ge t (2 * m + n) with h₃ | h₃
  · -- back along the top, so the walk runs against the edge's own orientation
    rw [ite_eq_right (by omega),
      ite_eq_right (by omega),
          ite_eq_left h₃, bIdx_top (by omega) (by omega),
      bIdy_top (by omega) (by omega), bIdx_top (by omega) (by omega),
      bIdy_top (by omega) (by omega), show 2 * m + n - (t + 1) = 2 * m + n - 1 - t by omega,
      show 2 * m + n - t = 2 * m + n - 1 - t + 1 by omega]
    exact (pieceListGraph_isLink_self (gridHEdge_mem_gridEdges
      (show 2 * m + n - 1 - t < m by omega) le_rfl hn)).symm
  · -- down the left side, again against the edge's orientation
    rw [ite_eq_right (by omega),
      ite_eq_right (by omega),
      ite_eq_right (by omega), bIdx_left (by omega) (by omega),
      bIdy_left (by omega) (by omega), bIdx_left (by omega) (by omega),
      bIdy_left (by omega) (by omega),
      show 2 * m + 2 * n - (t + 1) = 2 * m + 2 * n - 1 - t by omega,
      show 2 * m + 2 * n - t = 2 * m + 2 * n - 1 - t + 1 by omega]
    exact (pieceListGraph_isLink_self (gridVEdge_mem_gridEdges (Nat.zero_le m)
      (show 2 * m + 2 * n - 1 - t < n by omega) hm)).symm

/-- The detour: all the boundary edges but the last. -/
def gridBoundaryDetour (xc yc : ℕ → ℝ) (m n : ℕ) : List Piece :=
  (List.range' 0 (2 * m + 2 * n - 1)).map (gridBoundaryEdge xc yc m n)

/-- The last boundary edge, which closes the cycle. -/
def gridBoundaryLast (xc yc : ℕ → ℝ) (m n : ℕ) : Piece :=
  gridBoundaryEdge xc yc m n (2 * m + 2 * n - 1)

/-- **`prop:anchored-square-mesh`, clause 3, as a cycle.** The boundary of the grid is a cycle
of the grid graph — not merely a point set. -/
theorem gridGraph_isCycleThrough_boundary {xc yc : ℕ → ℝ} {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hx : Set.InjOn xc (Set.Iic m)) (hy : Set.InjOn yc (Set.Iic n)) :
    (gridGraph xc yc m n).IsCycleThrough (gridBoundaryLast xc yc m n)
      (gridBoundaryPt xc yc m n 0) (gridBoundaryPt xc yc m n (2 * m + 2 * n - 1))
      (gridBoundaryDetour xc yc m n) := by
  have hL : 4 ≤ 2 * m + 2 * n := by omega
  have hlast := gridBoundary_isLink (xc := xc) (yc := yc) hm hn
    (show 2 * m + 2 * n - 1 < 2 * m + 2 * n by omega)
  rw [show 2 * m + 2 * n - 1 + 1 = 2 * m + 2 * n by omega, gridBoundaryPt_wrap] at hlast
  refine ⟨hlast.symm, ?_, ?_⟩
  · -- the detour is a path: `Graph.isPath_range'` with the vertices of the walk
    have := Graph.isPath_range' (G := gridGraph xc yc m n) (p := gridBoundaryPt xc yc m n)
      (q := gridBoundaryEdge xc yc m n) (2 * m + 2 * n - 1) 0
      (fun i _ h => gridBoundary_isLink hm hn (by omega))
      (fun i j _ hi _ hj h => gridBoundaryPt_inj hm hn hx hy (by omega) (by omega) h)
      (by rw [Nat.zero_add]; exact hlast.left_mem)
    rwa [Nat.zero_add] at this
  · -- the closing edge is not one of the others
    intro hmem
    obtain ⟨i, hi, heq⟩ := List.mem_map.1 hmem
    rw [List.mem_range'_1] at hi
    have hli := gridBoundary_isLink (xc := xc) (yc := yc) hm hn
      (show i < 2 * m + 2 * n by omega)
    rw [heq] at hli
    -- the two links carry the same edge name, so they have the same pair of ends
    rcases hli.left_eq_or_eq hlast with h | h
    · exact absurd (gridBoundaryPt_inj hm hn hx hy (by omega) (by omega) h) (by omega)
    · -- `i` is the start, and then its successor must be the last vertex, forcing `2m+2n = 2`
      obtain rfl : i = 0 := gridBoundaryPt_inj hm hn hx hy (by omega) (by omega) h
      have hnext := hli.right_unique (h ▸ hlast.symm)
      exact absurd (gridBoundaryPt_inj hm hn hx hy (by omega) (by omega) hnext) (by omega)

/-! ### What the outer cycle occupies

Up to here nothing has been asked of the order of the coordinates. It is asked now: the union
of the boundary edges is the frame of the bounding rectangle only if the coordinates increase,
and the proof is the one-dimensional fact `Set.Icc_union_Icc_eq_Icc` transported along
`Schoenflies.mem_segment_horiz` / `mem_segment_vert`. -/

theorem gridBoundaryEdge_bottom {xc yc : ℕ → ℝ} {m n i : ℕ} (h : i < m) :
    gridBoundaryEdge xc yc m n i = gridHEdge xc yc i 0 := by
  unfold gridBoundaryEdge; rw [ite_eq_left h]

theorem gridBoundaryEdge_right {xc yc : ℕ → ℝ} {m n j : ℕ} (h : j < n) :
    gridBoundaryEdge xc yc m n (m + j) = gridVEdge xc yc m j := by
  unfold gridBoundaryEdge
  rw [ite_eq_right (by omega),
          ite_eq_left (by omega), show m + j - m = j by omega]

theorem gridBoundaryEdge_top {xc yc : ℕ → ℝ} {m n i : ℕ} (hn : 1 ≤ n) (h : i < m) :
    gridBoundaryEdge xc yc m n (2 * m + n - 1 - i) = gridHEdge xc yc i n := by
  unfold gridBoundaryEdge
  rw [ite_eq_right (by omega),
      ite_eq_right (by omega),
          ite_eq_left (by omega),
    show 2 * m + n - 1 - (2 * m + n - 1 - i) = i by omega]

theorem gridBoundaryEdge_left {xc yc : ℕ → ℝ} {m n j : ℕ} (h : j < n) :
    gridBoundaryEdge xc yc m n (2 * m + 2 * n - 1 - j) = gridVEdge xc yc 0 j := by
  unfold gridBoundaryEdge
  rw [ite_eq_right (by omega),
      ite_eq_right (by omega),
      ite_eq_right (by omega),
    show 2 * m + 2 * n - 1 - (2 * m + 2 * n - 1 - j) = j by omega]

/-- The realisation of the cycle is the union of the boundary edges, indexed by position on
the walk. -/
theorem edgesCover_gridBoundary_eq_iUnion (xc yc : ℕ → ℝ) {m n : ℕ} (hL : 1 ≤ 2 * m + 2 * n) :
    Graph.edgesCover segmentDrawing
        (gridBoundaryLast xc yc m n :: gridBoundaryDetour xc yc m n)
      = ⋃ t ∈ Set.Iio (2 * m + 2 * n), (gridBoundaryEdge xc yc m n t).seg := by
  ext z
  simp only [Graph.mem_edgesCover_iff, List.mem_cons, gridBoundaryDetour, List.mem_map,
    edgeArc_segmentDrawing, Set.mem_iUnion, Set.mem_Iio, exists_prop]
  constructor
  · rintro ⟨P, (rfl | ⟨i, hi, rfl⟩), hzP⟩
    · exact ⟨2 * m + 2 * n - 1, by omega, hzP⟩
    · rw [List.mem_range'_1] at hi
      exact ⟨i, by omega, hzP⟩
  · rintro ⟨t, ht, hz⟩
    rcases eq_or_lt_of_le (show t ≤ 2 * m + 2 * n - 1 by omega) with rfl | hlt
    · exact ⟨_, Or.inl rfl, hz⟩
    · exact ⟨_, Or.inr ⟨t, List.mem_range'_1.2 ⟨Nat.zero_le t, by omega⟩, rfl⟩, hz⟩

/-- The boundary edges, sorted into the four sides. -/
theorem iUnion_gridBoundaryEdge (xc yc : ℕ → ℝ) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (⋃ t ∈ Set.Iio (2 * m + 2 * n), (gridBoundaryEdge xc yc m n t).seg) =
      ((⋃ i ∈ Set.Iio m, (gridHEdge xc yc i 0).seg) ∪
          ⋃ j ∈ Set.Iio n, (gridVEdge xc yc m j).seg) ∪
        ((⋃ i ∈ Set.Iio m, (gridHEdge xc yc i n).seg) ∪
          ⋃ j ∈ Set.Iio n, (gridVEdge xc yc 0 j).seg) := by
  ext z
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_Iio, exists_prop]
  constructor
  · rintro ⟨t, ht, hz⟩
    rcases lt_or_ge t m with h₁ | h₁
    · exact Or.inl (Or.inl ⟨t, h₁, by rwa [← gridBoundaryEdge_bottom h₁]⟩)
    rcases lt_or_ge t (m + n) with h₂ | h₂
    · refine Or.inl (Or.inr ⟨t - m, by omega, ?_⟩)
      rwa [← gridBoundaryEdge_right (m := m) (show t - m < n by omega),
        show m + (t - m) = t by omega]
    rcases lt_or_ge t (2 * m + n) with h₃ | h₃
    · refine Or.inr (Or.inl ⟨2 * m + n - 1 - t, by omega, ?_⟩)
      rwa [← gridBoundaryEdge_top hn (show 2 * m + n - 1 - t < m by omega),
        show 2 * m + n - 1 - (2 * m + n - 1 - t) = t by omega]
    · refine Or.inr (Or.inr ⟨2 * m + 2 * n - 1 - t, by omega, ?_⟩)
      rwa [← gridBoundaryEdge_left (m := m) (show 2 * m + 2 * n - 1 - t < n by omega),
        show 2 * m + 2 * n - 1 - (2 * m + 2 * n - 1 - t) = t by omega]
  · rintro ((⟨i, hi, hz⟩ | ⟨j, hj, hz⟩) | (⟨i, hi, hz⟩ | ⟨j, hj, hz⟩))
    · exact ⟨i, by omega, by rwa [gridBoundaryEdge_bottom hi]⟩
    · exact ⟨m + j, by omega, by rwa [gridBoundaryEdge_right hj]⟩
    · exact ⟨2 * m + n - 1 - i, by omega, by rwa [gridBoundaryEdge_top hn hi]⟩
    · exact ⟨2 * m + 2 * n - 1 - j, by omega, by rwa [gridBoundaryEdge_left (m := m) hj]⟩

/-! ### Consecutive intervals -/

theorem chain_le_of_le {f : ℕ → ℝ} {m : ℕ} (h : ∀ i, i < m → f i ≤ f (i + 1)) :
    ∀ a b, a ≤ b → b ≤ m → f a ≤ f b := by
  intro a b
  induction b with
  | zero =>
    intro hab _
    obtain rfl : a = 0 := by omega
    exact le_rfl
  | succ b ih =>
    intro hab hb
    rcases Nat.lt_or_ge a (b + 1) with h₁ | h₁
    · exact (ih (by omega) (by omega)).trans (h b (by omega))
    · obtain rfl : a = b + 1 := by omega
      exact le_rfl

theorem iUnion_Icc_chain {f : ℕ → ℝ} : ∀ m : ℕ, 1 ≤ m → (∀ i, i < m → f i ≤ f (i + 1)) →
    (⋃ i ∈ Set.Iio m, Set.Icc (f i) (f (i + 1))) = Set.Icc (f 0) (f m) := by
  intro m
  induction m with
  | zero => exact fun h => absurd h (by omega)
  | succ m ih =>
    intro _ hmono
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hsplit : (⋃ i ∈ Set.Iio (m + 1), Set.Icc (f i) (f (i + 1)))
          = (⋃ i ∈ Set.Iio m, Set.Icc (f i) (f (i + 1))) ∪ Set.Icc (f m) (f (m + 1)) := by
        ext z
        simp only [Set.mem_iUnion, Set.mem_Iio, exists_prop, Set.mem_union]
        constructor
        · rintro ⟨i, hi, hz⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
          exacts [Or.inl ⟨i, h, hz⟩, Or.inr hz]
        · rintro (⟨i, hi, hz⟩ | hz)
          exacts [⟨i, by omega, hz⟩, ⟨m, by omega, hz⟩]
      rw [hsplit, ih hm fun i hi => hmono i (by omega),
        Set.Icc_union_Icc_eq_Icc (chain_le_of_le hmono 0 m (by omega) (by omega))
          (hmono m (by omega))]

/-- A run of horizontal grid edges occupies the whole horizontal segment. -/
theorem iUnion_gridHEdge_seg {xc yc : ℕ → ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hmono : ∀ i, i < m → xc i ≤ xc (i + 1)) (j : ℕ) :
    (⋃ i ∈ Set.Iio m, (gridHEdge xc yc i j).seg)
      = segment ℝ (gridPt xc yc 0 j) (gridPt xc yc m j) := by
  have h0m : xc 0 ≤ xc m := chain_le_of_le hmono 0 m (by omega) le_rfl
  ext z
  simp only [gridHEdge, gridPt, Piece.seg, Set.mem_iUnion, Set.mem_Iio, exists_prop,
    mem_segment_horiz]
  constructor
  · rintro ⟨i, hi, hz1, hz0⟩
    refine ⟨hz1, ?_⟩
    rw [segment_eq_Icc (hmono i hi)] at hz0
    rw [segment_eq_Icc h0m]
    exact Set.Icc_subset_Icc (chain_le_of_le hmono 0 i (by omega) (by omega))
      (chain_le_of_le hmono (i + 1) m (by omega) (by omega)) hz0
  · rintro ⟨hz1, hz0⟩
    rw [segment_eq_Icc h0m, ← iUnion_Icc_chain m hm hmono] at hz0
    simp only [Set.mem_iUnion, Set.mem_Iio, exists_prop] at hz0
    obtain ⟨i, hi, hz⟩ := hz0
    exact ⟨i, hi, hz1, by rw [segment_eq_Icc (hmono i hi)]; exact hz⟩

/-- A run of vertical grid edges occupies the whole vertical segment. -/
theorem iUnion_gridVEdge_seg {xc yc : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hmono : ∀ j, j < n → yc j ≤ yc (j + 1)) (i : ℕ) :
    (⋃ j ∈ Set.Iio n, (gridVEdge xc yc i j).seg)
      = segment ℝ (gridPt xc yc i 0) (gridPt xc yc i n) := by
  have h0n : yc 0 ≤ yc n := chain_le_of_le hmono 0 n (by omega) le_rfl
  ext z
  simp only [gridVEdge, gridPt, Piece.seg, Set.mem_iUnion, Set.mem_Iio, exists_prop,
    mem_segment_vert]
  constructor
  · rintro ⟨j, hj, hz0, hz1⟩
    refine ⟨hz0, ?_⟩
    rw [segment_eq_Icc (hmono j hj)] at hz1
    rw [segment_eq_Icc h0n]
    exact Set.Icc_subset_Icc (chain_le_of_le hmono 0 j (by omega) (by omega))
      (chain_le_of_le hmono (j + 1) n (by omega) (by omega)) hz1
  · rintro ⟨hz0, hz1⟩
    rw [segment_eq_Icc h0n, ← iUnion_Icc_chain n hn hmono] at hz1
    simp only [Set.mem_iUnion, Set.mem_Iio, exists_prop] at hz1
    obtain ⟨j, hj, hz⟩ := hz1
    exact ⟨j, hj, hz0, by rw [segment_eq_Icc (hmono j hj)]; exact hz⟩

/-- **What the outer cycle occupies**: the frame of the bounding rectangle, as the union of its
four sides. -/
theorem edgesCover_gridBoundary {xc yc : ℕ → ℝ} {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hxmono : ∀ i, i < m → xc i ≤ xc (i + 1)) (hymono : ∀ j, j < n → yc j ≤ yc (j + 1)) :
    Graph.edgesCover segmentDrawing
        (gridBoundaryLast xc yc m n :: gridBoundaryDetour xc yc m n)
      = (segment ℝ (gridPt xc yc 0 0) (gridPt xc yc m 0) ∪
          segment ℝ (gridPt xc yc m 0) (gridPt xc yc m n)) ∪
        (segment ℝ (gridPt xc yc 0 n) (gridPt xc yc m n) ∪
          segment ℝ (gridPt xc yc 0 0) (gridPt xc yc 0 n)) := by
  rw [edgesCover_gridBoundary_eq_iUnion _ _ (by omega), iUnion_gridBoundaryEdge _ _ hm hn,
    iUnion_gridHEdge_seg hm hxmono 0, iUnion_gridHEdge_seg hm hxmono n,
    iUnion_gridVEdge_seg hn hymono m, iUnion_gridVEdge_seg hn hymono 0]

/-- **The outer cycle of a grid on `[-1,1]²` occupies exactly `S`.** This is the missing half of
`prop:anchored-square-mesh` clause 3: not "the edges lying on `S` cover `S`", but "`S` is the
realisation of a distinguished cycle of the graph", which is the form
`thm:finite-transfer`(b) consumes. -/
theorem edgesCover_gridBoundary_modelCurve {xc yc : ℕ → ℝ} {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hxmono : ∀ i, i < m → xc i ≤ xc (i + 1)) (hymono : ∀ j, j < n → yc j ≤ yc (j + 1))
    (hx0 : xc 0 = -1) (hxm : xc m = 1) (hy0 : yc 0 = -1) (hyn : yc n = 1) :
    Graph.edgesCover segmentDrawing
        (gridBoundaryLast xc yc m n :: gridBoundaryDetour xc yc m n) = modelCurve := by
  have hcov : cover (ringPieces 1) = modelCurve := by
    rw [cover_ringPieces zero_le_one, ringSet_one]
  rw [edgesCover_gridBoundary hm hn hxmono hymono, ← hcov]
  simp only [ringPieces, cover_cons, cover_nil, Set.union_empty, Piece.seg, gridPt, hx0, hxm,
    hy0, hyn]
  rw [segment_symm ℝ (Plane.mk (1 : ℝ) (1 : ℝ)) (Plane.mk (-1 : ℝ) (1 : ℝ)),
    segment_symm ℝ (Plane.mk (-1 : ℝ) (1 : ℝ)) (Plane.mk (-1 : ℝ) (-1 : ℝ))]
  ext z
  simp only [Set.mem_union]
  tauto

/-- **The distinguished outer cycle of the grid on `[-1,1]²`**, both halves at once: it is a
cycle of the grid graph, and what it occupies is `S`. -/
theorem gridGraph_outer_cycle {xc yc : ℕ → ℝ} {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hx : Set.InjOn xc (Set.Iic m)) (hy : Set.InjOn yc (Set.Iic n))
    (hxmono : ∀ i, i < m → xc i ≤ xc (i + 1)) (hymono : ∀ j, j < n → yc j ≤ yc (j + 1))
    (hx0 : xc 0 = -1) (hxm : xc m = 1) (hy0 : yc 0 = -1) (hyn : yc n = 1) :
    (gridGraph xc yc m n).IsCycleThrough (gridBoundaryLast xc yc m n)
        (gridBoundaryPt xc yc m n 0) (gridBoundaryPt xc yc m n (2 * m + 2 * n - 1))
        (gridBoundaryDetour xc yc m n) ∧
      Graph.edgesCover segmentDrawing
        (gridBoundaryLast xc yc m n :: gridBoundaryDetour xc yc m n) = modelCurve :=
  ⟨gridGraph_isCycleThrough_boundary hm hn hx hy,
    edgesCover_gridBoundary_modelCurve hm hn hxmono hymono hx0 hxm hy0 hyn⟩

/-! ### The grid is a plane graph

Sorted coordinates make the drawing clause a coordinate computation. A point of a horizontal
grid edge has the row's `y`-coordinate and an `x`-coordinate in one closed coordinate interval;
strict monotonicity turns "`xc a` lies in `[xc i, xc (i+1)]`" into "`a = i` or `a = i+1`", and
that single step settles both remaining clauses of `Graph.IsDrawing`. -/

theorem coord_le_of_idx_le {f : ℕ → ℝ} {N : ℕ} (hf : StrictMonoOn f (Set.Iic N)) {a b : ℕ}
    (ha : a ≤ N) (hb : b ≤ N) (h : a ≤ b) : f a ≤ f b := by
  rcases eq_or_lt_of_le h with rfl | h'
  · exact le_rfl
  · exact (hf ha hb h').le

theorem idx_le_of_coord_le {f : ℕ → ℝ} {N : ℕ} (hf : StrictMonoOn f (Set.Iic N)) {a b : ℕ}
    (ha : a ≤ N) (hb : b ≤ N) (h : f a ≤ f b) : a ≤ b := by
  by_contra hcon
  exact absurd (hf hb ha (by omega)) (by simpa using h)

/-- **Reading an index off a coordinate.** -/
theorem idx_of_coord_mem {f : ℕ → ℝ} {N : ℕ} (hf : StrictMonoOn f (Set.Iic N)) {a i : ℕ}
    (ha : a ≤ N) (hi : i + 1 ≤ N) (h₁ : f i ≤ f a) (h₂ : f a ≤ f (i + 1)) :
    a = i ∨ a = i + 1 := by
  have := idx_le_of_coord_le hf (by omega) ha h₁
  have := idx_le_of_coord_le hf ha hi h₂
  omega

theorem mem_gridHEdge_seg_iff {xc yc : ℕ → ℝ} {i j : ℕ} {z : Plane} :
    z ∈ (gridHEdge xc yc i j).seg ↔ z 1 = yc j ∧ z 0 ∈ segment ℝ (xc i) (xc (i + 1)) :=
  mem_segment_horiz

theorem mem_gridVEdge_seg_iff {xc yc : ℕ → ℝ} {i j : ℕ} {z : Plane} :
    z ∈ (gridVEdge xc yc i j).seg ↔ z 0 = xc i ∧ z 1 ∈ segment ℝ (yc j) (yc (j + 1)) :=
  mem_segment_vert

variable {xc yc : ℕ → ℝ} {m n : ℕ}

/-- A grid edge is nondegenerate: its two ends differ in one coordinate. -/
theorem gridEdges_nondeg (hxs : StrictMonoOn xc (Set.Iic m)) (hys : StrictMonoOn yc (Set.Iic n))
    (hm : 1 ≤ m) (hn : 1 ≤ n) {P : Piece} (hP : P ∈ gridEdges xc yc m n) : P.Nondeg := by
  rcases (mem_gridEdges_iff hm hn).1 hP with ⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, j, hj, rfl⟩
  · exact gridPt_ne_of_fst
      (ne_of_lt (hxs (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 (by omega)) (by omega)))
  · exact gridPt_ne_of_snd
      (ne_of_lt (hys (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 (by omega)) (by omega)))

/-- A grid point on a grid edge is one of that edge's two ends. -/
theorem end_of_gridPt_mem_seg (hxs : StrictMonoOn xc (Set.Iic m))
    (hys : StrictMonoOn yc (Set.Iic n)) (hm : 1 ≤ m) (hn : 1 ≤ n) {P : Piece}
    (hP : P ∈ gridEdges xc yc m n) {a b : ℕ} (ha : a ≤ m) (hb : b ≤ n)
    (hmem : gridPt xc yc a b ∈ P.seg) : gridPt xc yc a b = P.1 ∨ gridPt xc yc a b = P.2 := by
  rcases (mem_gridEdges_iff hm hn).1 hP with ⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, j, hj, rfl⟩
  · obtain ⟨hz1, hz0⟩ := mem_gridHEdge_seg_iff.1 hmem
    simp only [gridPt, Plane.mk_one, Plane.mk_zero] at hz1 hz0
    obtain rfl : b = j := hys.injOn hb hj hz1
    rw [segment_eq_Icc (coord_le_of_idx_le hxs (by omega) (by omega) (by omega))] at hz0
    rcases idx_of_coord_mem hxs ha (by omega) hz0.1 hz0.2 with rfl | rfl
    exacts [Or.inl rfl, Or.inr rfl]
  · obtain ⟨hz0, hz1⟩ := mem_gridVEdge_seg_iff.1 hmem
    simp only [gridPt, Plane.mk_one, Plane.mk_zero] at hz1 hz0
    obtain rfl : a = i := hxs.injOn ha hi hz0
    rw [segment_eq_Icc (coord_le_of_idx_le hys (by omega) (by omega) (by omega))] at hz1
    rcases idx_of_coord_mem hys hb (by omega) hz1.1 hz1.2 with rfl | rfl
    exacts [Or.inl rfl, Or.inr rfl]

/-- **A point on two grid edges is a grid point on both.** The heart of the drawing clause:
two grid segments cross only where a coordinate of one is pinned by the other. -/
theorem gridPt_of_mem_two_edges (hxs : StrictMonoOn xc (Set.Iic m))
    (hys : StrictMonoOn yc (Set.Iic n)) (hm : 1 ≤ m) (hn : 1 ≤ n) {P Q : Piece}
    (hP : P ∈ gridEdges xc yc m n) (hQ : Q ∈ gridEdges xc yc m n) (hPQ : P ≠ Q) {z : Plane}
    (hzP : z ∈ P.seg) (hzQ : z ∈ Q.seg) :
    ∃ a ≤ m, ∃ b ≤ n, z = gridPt xc yc a b := by
  -- an equal-direction pair: two rows or two columns, meeting at one shared coordinate
  have same : ∀ (f : ℕ → ℝ) (N i i' : ℕ), StrictMonoOn f (Set.Iic N) → i + 1 ≤ N → i' + 1 ≤ N →
      i ≠ i' → ∀ c : ℝ, c ∈ segment ℝ (f i) (f (i + 1)) → c ∈ segment ℝ (f i') (f (i' + 1)) →
      ∃ k ≤ N, c = f k := by
    intro f N i i' hf hi hi' hne c hc hc'
    rw [segment_eq_Icc (coord_le_of_idx_le hf (by omega) (by omega) (by omega))] at hc
    rw [segment_eq_Icc (coord_le_of_idx_le hf (by omega) (by omega) (by omega))] at hc'
    rcases lt_or_gt_of_ne hne with h | h
    · -- `i` is to the left: the two intervals can only touch at `f (i+1)`
      refine ⟨i + 1, hi, le_antisymm hc.2 ?_⟩
      exact le_trans (coord_le_of_idx_le hf (by omega) (by omega) (by omega)) hc'.1
    · refine ⟨i, by omega, le_antisymm ?_ hc.1⟩
      exact le_trans hc'.2 (coord_le_of_idx_le hf (by omega) (by omega) (by omega))
  rcases (mem_gridEdges_iff hm hn).1 hP with ⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, j, hj, rfl⟩ <;>
    rcases (mem_gridEdges_iff hm hn).1 hQ with ⟨i', hi', j', hj', rfl⟩ | ⟨i', hi', j', hj', rfl⟩
  · obtain ⟨hz1, hz0⟩ := mem_gridHEdge_seg_iff.1 hzP
    obtain ⟨hz1', hz0'⟩ := mem_gridHEdge_seg_iff.1 hzQ
    obtain rfl : j = j' := hys.injOn hj hj' (hz1 ▸ hz1')
    have hii : i ≠ i' := by rintro rfl; exact hPQ rfl
    obtain ⟨k, hk, hck⟩ := same xc m i i' hxs (by omega) (by omega) hii _ hz0 hz0'
    exact ⟨k, hk, j, hj, plane_eq_of_coords (by simpa [gridPt] using hck)
      (by simpa [gridPt] using hz1)⟩
  · obtain ⟨hz1, hz0⟩ := mem_gridHEdge_seg_iff.1 hzP
    obtain ⟨hz0', hz1'⟩ := mem_gridVEdge_seg_iff.1 hzQ
    exact ⟨i', hi', j, hj, plane_eq_of_coords (by simpa [gridPt] using hz0')
      (by simpa [gridPt] using hz1)⟩
  · obtain ⟨hz0, hz1⟩ := mem_gridVEdge_seg_iff.1 hzP
    obtain ⟨hz1', hz0'⟩ := mem_gridHEdge_seg_iff.1 hzQ
    exact ⟨i, hi, j', hj', plane_eq_of_coords (by simpa [gridPt] using hz0)
      (by simpa [gridPt] using hz1')⟩
  · obtain ⟨hz0, hz1⟩ := mem_gridVEdge_seg_iff.1 hzP
    obtain ⟨hz0', hz1'⟩ := mem_gridVEdge_seg_iff.1 hzQ
    obtain rfl : i = i' := hxs.injOn hi hi' (hz0 ▸ hz0')
    have hjj : j ≠ j' := by rintro rfl; exact hPQ rfl
    obtain ⟨k, hk, hck⟩ := same yc n j j' hys (by omega) (by omega) hjj _ hz1 hz1'
    exact ⟨i, hi, k, hk, plane_eq_of_coords (by simpa [gridPt] using hz0)
      (by simpa [gridPt] using hck)⟩

/-- **The grid is a plane graph**, drawn with straight edges. -/
theorem gridGraph_isDrawing (hxs : StrictMonoOn xc (Set.Iic m))
    (hys : StrictMonoOn yc (Set.Iic n)) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    Graph.IsDrawing (gridGraph xc yc m n) segmentDrawing := by
  refine ⟨?_, ?_, ?_⟩
  · intro P hP
    have hne : P.Nondeg := gridEdges_nondeg hxs hys hm hn hP
    refine ⟨AffineMap.lineMap_continuous.continuousOn, injOn_lineMap hne, ?_⟩
    have h0 : segmentDrawing P 0 = P.1 := by simp [segmentDrawing]
    have h1 : segmentDrawing P 1 = P.2 := by simp [segmentDrawing]
    rw [h0, h1]
    exact pieceListGraph_isLink_self hP
  · rintro P x y v ⟨hP, hxy⟩ hv hvarc
    rw [edgeArc_segmentDrawing] at hvarc
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_vertexSet_gridGraph_iff hm hn).1 hv
    have hend := end_of_gridPt_mem_seg hxs hys hm hn hP ha hb hvarc
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hend
    · exact hend.symm
  · intro P Q hP hQ hPQ p hpP hpQ
    rw [edgeArc_segmentDrawing] at hpP hpQ
    obtain ⟨a, ha, b, hb, rfl⟩ := gridPt_of_mem_two_edges hxs hys hm hn hP hQ hPQ hpP hpQ
    have hvert : gridPt xc yc a b ∈ V(gridGraph xc yc m n) :=
      (mem_vertexSet_gridGraph_iff hm hn).2 ⟨a, ha, b, hb, rfl⟩
    exact ⟨hvert, pieceListGraph_inc hP (end_of_gridPt_mem_seg hxs hys hm hn hP ha hb hpP),
      pieceListGraph_inc hQ (end_of_gridPt_mem_seg hxs hys hm hn hQ ha hb hpQ)⟩

/-- **The outer cycle is a Jordan curve.** Now that the grid is a plane graph this is
`Graph.IsDrawing.cycle_isJordanCurve` applied to the boundary cycle. -/
theorem gridBoundary_isJordanCurve (hxs : StrictMonoOn xc (Set.Iic m))
    (hys : StrictMonoOn yc (Set.Iic n)) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    IsJordanCurve (Graph.edgesCover segmentDrawing
      (gridBoundaryLast xc yc m n :: gridBoundaryDetour xc yc m n)) :=
  (gridGraph_isDrawing hxs hys hm hn).cycle_isJordanCurve
    (gridGraph_isCycleThrough_boundary hm hn hxs.injOn hys.injOn)

end Schoenflies
