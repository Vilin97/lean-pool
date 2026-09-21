/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import LeanPool.BKARForestFormula.BKAR.Forest

/-! # Forests and Mathlib simple graphs

Bridge between the edge-set forests of `BKAR.Forest` and Mathlib's
`SimpleGraph` API.  Associates to a finite edge set the simple graph it
generates, translates adjacency, walks, and acyclicity back and forth
(`SimpleGraph.IsAcyclic`), and derives the graph-theoretic facts used
elsewhere: existence and uniqueness of simple paths in an acyclic edge set,
and stability of acyclicity under adding an edge between distinct
components.
-/

noncomputable section

namespace BKAR

theorem simpleGraph_isAcyclic_sup_edge_of_not_reachable
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}
    (hG : G.IsAcyclic) (hxy : ¬ G.Reachable x y) :
    (G ⊔ SimpleGraph.edge x y).IsAcyclic := by
  by_cases hdiag : x = y
  · exact False.elim (hxy (hdiag ▸ SimpleGraph.Reachable.rfl))
  intro u c hc
  by_cases hmem : Sym2.mk x y ∈ c.edges
  · let H : SimpleGraph V := G ⊔ SimpleGraph.edge x y
    have hcycle :
        ∃ u : V, ∃ p : H.Walk u u,
          p.IsCycle ∧ Sym2.mk x y ∈ p.edges :=
      ⟨u, c, hc, hmem⟩
    have hreach :
        (H \ SimpleGraph.fromEdgeSet {Sym2.mk x y}).Reachable x y :=
      ((SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle
        (G := H) (v := x) (w := y)).mpr hcycle).2
    have hle : H \ SimpleGraph.fromEdgeSet {Sym2.mk x y} ≤ G := by
      intro a b hab
      rw [SimpleGraph.sdiff_adj, SimpleGraph.sup_adj] at hab
      rcases hab.1 with hGab | hedge
      · exact hGab
      · exact False.elim (hab.2 (by
          simpa [SimpleGraph.edge] using hedge))
    exact hxy (hreach.mono hle)
  · have hedge_mem_G :
        ∀ e, e ∈ c.edges → e ∈ G.edgeSet := by
      intro z hz
      have hzH : z ∈ (G ⊔ SimpleGraph.edge x y).edgeSet :=
        c.edges_subset_edgeSet hz
      rw [SimpleGraph.edgeSet_sup] at hzH
      rcases hzH with hzG | hzEdge
      · exact hzG
      · have hzxy : z = Sym2.mk x y := by
          rw [SimpleGraph.edgeSet_edge_of_ne hdiag] at hzEdge
          exact Set.mem_singleton_iff.mp hzEdge
        exact False.elim (hmem (hzxy ▸ hz))
    exact hG (c.transfer G hedge_mem_G) (hc.transfer hedge_mem_G)

namespace EdgePath

variable {V : Type*} [DecidableEq V]

/-- The simple graph whose edge set is the underlying `Sym2` image of `S`. -/
def edgeSetGraph (S : Finset (Edge V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {x : Sym2 V | ∃ e : Edge V, e ∈ S ∧ e.val = x}

theorem edgeSetGraph_adj_of_mem_between
    {S : Finset (Edge V)} {e : Edge V} {i j : V}
    (he : e ∈ S) (hbetween : e.Between i j) :
    (edgeSetGraph S).Adj i j := by
  rw [edgeSetGraph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · exact ⟨e, he, hbetween⟩
  · intro hij
    exact e.not_between_self j (hij ▸ hbetween)

theorem exists_mem_between_of_edgeSetGraph_adj
    {S : Finset (Edge V)} {i j : V}
    (h : (edgeSetGraph S).Adj i j) :
    ∃ e : Edge V, e ∈ S ∧ e.Between i j := by
  rw [edgeSetGraph, SimpleGraph.fromEdgeSet_adj] at h
  rcases h.1 with ⟨e, heS, heq⟩
  exact ⟨e, heS, heq⟩

/-- The local edge selected by an adjacency in `edgeSetGraph S`. -/
def edgeOfAdj {S : Finset (Edge V)} {i j : V}
    (h : (edgeSetGraph S).Adj i j) : Edge V :=
  Classical.choose (exists_mem_between_of_edgeSetGraph_adj h)

theorem edgeOfAdj_mem {S : Finset (Edge V)} {i j : V}
    (h : (edgeSetGraph S).Adj i j) :
    edgeOfAdj h ∈ S :=
  (Classical.choose_spec (exists_mem_between_of_edgeSetGraph_adj h)).1

theorem edgeOfAdj_between {S : Finset (Edge V)} {i j : V}
    (h : (edgeSetGraph S).Adj i j) :
    (edgeOfAdj h).Between i j :=
  (Classical.choose_spec (exists_mem_between_of_edgeSetGraph_adj h)).2

theorem edge_adj_iff_between (e : Edge V) {i j : V} :
    (SimpleGraph.edge e.left e.right).Adj i j ↔ e.Between i j := by
  constructor
  · intro h
    rw [SimpleGraph.edge, SimpleGraph.fromEdgeSet_adj] at h
    have hmk : Sym2.mk i j = Sym2.mk e.left e.right :=
      Set.mem_singleton_iff.mp h.1
    exact e.mk_left_right_eq.symm.trans hmk.symm
  · intro h
    rw [SimpleGraph.edge, SimpleGraph.fromEdgeSet_adj]
    constructor
    · rw [Set.mem_singleton_iff]
      exact (Eq.symm h).trans e.mk_left_right_eq.symm
    · intro hij
      exact e.not_between_self j (hij ▸ h)

theorem edgeSetGraph_insert (S : Finset (Edge V)) (e : Edge V) :
    edgeSetGraph (insert e S) = edgeSetGraph S ⊔ SimpleGraph.edge e.left e.right := by
  ext i j
  constructor
  · intro h
    rcases exists_mem_between_of_edgeSetGraph_adj h with ⟨e', he', hbetween⟩
    rw [Finset.mem_insert] at he'
    rcases he' with heq | heS
    · subst e'
      exact (SimpleGraph.sup_adj _ _ _ _).mpr
        (Or.inr ((edge_adj_iff_between e).mpr hbetween))
    · exact (SimpleGraph.sup_adj _ _ _ _).mpr
        (Or.inl (edgeSetGraph_adj_of_mem_between heS hbetween))
  · intro h
    rw [SimpleGraph.sup_adj] at h
    rcases h with hS | hedge
    · rcases exists_mem_between_of_edgeSetGraph_adj hS with ⟨e', heS, hbetween⟩
      exact edgeSetGraph_adj_of_mem_between
        (Finset.mem_insert_of_mem heS) hbetween
    · exact edgeSetGraph_adj_of_mem_between
        (Finset.mem_insert_self e S)
        ((edge_adj_iff_between e).mp hedge)

namespace IsPath

theorem exists_walk {S : Finset (Edge V)} :
    ∀ {γ : List (Edge V)} {i j : V}, IsPath S γ i j →
      ∃ p : (edgeSetGraph S).Walk i j,
        p.edges = γ.map (fun e : Edge V => e.val)
  | [], _i, _j, h => by
      cases h
      exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | _e :: _γ, _i, _k, h => by
      cases h with
      | cons he hbetween htail =>
          rcases exists_walk htail with ⟨p, hp⟩
          refine ⟨SimpleGraph.Walk.cons
            (edgeSetGraph_adj_of_mem_between he hbetween) p, ?_⟩
          rw [SimpleGraph.Walk.edges_cons, hp]
          simp only [List.map_cons, List.cons.injEq, and_true]
          exact Eq.symm hbetween

end IsPath

namespace IsSimplePath

theorem exists_walk_isTrail {S : Finset (Edge V)}
    {γ : List (Edge V)} {i j : V}
    (h : IsSimplePath S γ i j) :
    ∃ p : (edgeSetGraph S).Walk i j,
      p.edges = γ.map (fun e : Edge V => e.val) ∧ p.IsTrail := by
  rcases h.1.exists_walk with ⟨p, hp⟩
  refine ⟨p, hp, ?_⟩
  constructor
  rw [hp]
  exact h.2.map Subtype.val_injective

theorem exists_graph_path_of_isAcyclic {S : Finset (Edge V)}
    {γ : List (Edge V)} {i j : V}
    (hG : (edgeSetGraph S).IsAcyclic)
    (h : IsSimplePath S γ i j) :
    ∃ p : (edgeSetGraph S).Path i j,
      (p : (edgeSetGraph S).Walk i j).edges =
        γ.map (fun e : Edge V => e.val) := by
  rcases h.exists_walk_isTrail with ⟨p, hp_edges, hp_trail⟩
  exact ⟨⟨p, (hG.isPath_iff_isTrail p).mpr hp_trail⟩, hp_edges⟩

theorem unique_of_isAcyclic {S : Finset (Edge V)}
    {γ₁ γ₂ : List (Edge V)} {i j : V}
    (hG : (edgeSetGraph S).IsAcyclic)
    (h₁ : IsSimplePath S γ₁ i j) (h₂ : IsSimplePath S γ₂ i j) :
    γ₁ = γ₂ := by
  rcases h₁.exists_graph_path_of_isAcyclic hG with ⟨p₁, hp₁⟩
  rcases h₂.exists_graph_path_of_isAcyclic hG with ⟨p₂, hp₂⟩
  have hp : p₁ = p₂ := (hG.subsingleton_path i j).allEq p₁ p₂
  have hedges :
      (p₁ : (edgeSetGraph S).Walk i j).edges =
        (p₂ : (edgeSetGraph S).Walk i j).edges := by
    simpa using congrArg (fun p : (edgeSetGraph S).Path i j =>
      ((p : (edgeSetGraph S).Walk i j).edges)) hp
  rw [hp₁, hp₂] at hedges
  exact Subtype.val_injective.list_map hedges

end IsSimplePath

namespace Walk

/-- Convert a Mathlib walk in `edgeSetGraph S` back to a local edge-list. -/
def toEdgePath {S : Finset (Edge V)} {i j : V}
    (p : (edgeSetGraph S).Walk i j) : List (Edge V) :=
  match p with
  | SimpleGraph.Walk.nil => []
  | SimpleGraph.Walk.cons h p => edgeOfAdj h :: toEdgePath p

theorem toEdgePath_isPath {S : Finset (Edge V)} :
    ∀ {i j : V} (p : (edgeSetGraph S).Walk i j),
      IsPath S (toEdgePath p) i j := by
  intro i j p
  induction p with
  | nil =>
      exact IsPath.nil _
  | cons h p ih =>
      exact IsPath.cons (edgeOfAdj_mem h) (edgeOfAdj_between h) ih

theorem toEdgePath_edges {S : Finset (Edge V)} :
    ∀ {i j : V} (p : (edgeSetGraph S).Walk i j),
      (toEdgePath p).map (fun e : Edge V => e.val) = p.edges := by
  intro i j p
  induction p with
  | nil =>
      rfl
  | cons h p ih =>
      rw [SimpleGraph.Walk.edges_cons, ← ih]
      simp only [toEdgePath, List.map_cons, List.cons.injEq, and_true]
      exact edgeOfAdj_between h

theorem toEdgePath_isSimplePath_of_isTrail {S : Finset (Edge V)}
    {i j : V} {p : (edgeSetGraph S).Walk i j}
    (hp : p.IsTrail) :
    IsSimplePath S (toEdgePath p) i j := by
  constructor
  · exact toEdgePath_isPath p
  · apply List.Nodup.of_map (fun e : Edge V => e.val)
    rw [toEdgePath_edges p]
    exact hp.edges_nodup

theorem toEdgePath_isSimplePath_of_isPath {S : Finset (Edge V)}
    {i j : V} {p : (edgeSetGraph S).Walk i j}
    (hp : p.IsPath) :
    IsSimplePath S (toEdgePath p) i j :=
  toEdgePath_isSimplePath_of_isTrail hp.isTrail

end Walk

end EdgePath

namespace AcyclicEdgeSetData

open EdgePath

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem edgeSetGraph_isAcyclic
    {S : Finset (Edge V)} (data : AcyclicEdgeSetData S) :
    (EdgePath.edgeSetGraph S).IsAcyclic := by
  apply SimpleGraph.isAcyclic_iff_subsingleton_path.mpr
  intro i j
  refine ⟨fun p q => ?_⟩
  have hpLocal :
      EdgePath.IsSimplePath S
        (EdgePath.Walk.toEdgePath (p : (EdgePath.edgeSetGraph S).Walk i j))
        i j :=
    EdgePath.Walk.toEdgePath_isSimplePath_of_isPath p.property
  have hqLocal :
      EdgePath.IsSimplePath S
        (EdgePath.Walk.toEdgePath (q : (EdgePath.edgeSetGraph S).Walk i j))
        i j :=
    EdgePath.Walk.toEdgePath_isSimplePath_of_isPath q.property
  have hpaths :
      EdgePath.Walk.toEdgePath (p : (EdgePath.edgeSetGraph S).Walk i j) =
        EdgePath.Walk.toEdgePath (q : (EdgePath.edgeSetGraph S).Walk i j) :=
    data.path_unique
      (data.isSimplePath_iff.mpr hpLocal)
      (data.isSimplePath_iff.mpr hqLocal)
  apply Subtype.ext
  apply SimpleGraph.Walk.edges_injective
  calc
    (p : (EdgePath.edgeSetGraph S).Walk i j).edges =
        (EdgePath.Walk.toEdgePath
          (p : (EdgePath.edgeSetGraph S).Walk i j)).map
          (fun e : Edge V => e.val) :=
      (EdgePath.Walk.toEdgePath_edges
        (p : (EdgePath.edgeSetGraph S).Walk i j)).symm
    _ =
        (EdgePath.Walk.toEdgePath
          (q : (EdgePath.edgeSetGraph S).Walk i j)).map
          (fun e : Edge V => e.val) := by
      rw [hpaths]
    _ = (q : (EdgePath.edgeSetGraph S).Walk i j).edges :=
      EdgePath.Walk.toEdgePath_edges
        (q : (EdgePath.edgeSetGraph S).Walk i j)

theorem inSameComponent_of_edgeSetGraph_reachable
    {S : Finset (Edge V)} (data : AcyclicEdgeSetData S)
    {i j : V} (h : (EdgePath.edgeSetGraph S).Reachable i j) :
    data.inSameComponent i j := by
  rcases h.exists_isPath with ⟨p, hp⟩
  exact data.sameComponent_of_simplePath
    (data.isSimplePath_iff.mpr
      (EdgePath.Walk.toEdgePath_isSimplePath_of_isPath hp))

theorem inSameComponent_trans
    {S : Finset (Edge V)} (data : AcyclicEdgeSetData S)
    {i j k : V} (hij : data.inSameComponent i j)
    (hjk : data.inSameComponent j k) :
    data.inSameComponent i k := by
  rcases data.inSameComponent_iff_exists_isSimplePath.mp hij with
    ⟨γij, hγij⟩
  rcases data.inSameComponent_iff_exists_isSimplePath.mp hjk with
    ⟨γjk, hγjk⟩
  rcases hγij.1.exists_walk with ⟨pij, _hpij⟩
  rcases hγjk.1.exists_walk with ⟨pjk, _hpjk⟩
  exact data.inSameComponent_of_edgeSetGraph_reachable
    (SimpleGraph.Reachable.trans ⟨pij⟩ ⟨pjk⟩)

theorem inSameComponent_iff_of_between
    {S : Finset (Edge V)} (data : AcyclicEdgeSetData S)
    {e : Edge V} {i j : V} (hbetween : e.Between i j) :
    data.inSameComponent e.left e.right ↔ data.inSameComponent i j := by
  have hmk : Sym2.mk e.left e.right = Sym2.mk i j :=
    e.mk_left_right_eq.trans hbetween
  rw [Sym2.eq_iff] at hmk
  rcases hmk with h | h
  · rcases h with ⟨hleft, hright⟩
    subst i
    subst j
    rfl
  · rcases h with ⟨hleft, hright⟩
    subst i
    subst j
    exact ⟨inSameComponent_symm data, inSameComponent_symm data⟩

theorem isAcyclicEdgeSet_insert_of_not_inSameComponent
    {S : Finset (Edge V)} (data : AcyclicEdgeSetData S)
    {e : Edge V}
    (hnot : ¬ data.inSameComponent e.left e.right) :
    IsAcyclicEdgeSet (insert e S) := by
  let S' : Finset (Edge V) := insert e S
  have hnotReach : ¬ (EdgePath.edgeSetGraph S).Reachable e.left e.right := by
    intro hreach
    exact hnot (data.inSameComponent_of_edgeSetGraph_reachable hreach)
  have hG : (EdgePath.edgeSetGraph S').IsAcyclic := by
    dsimp [S']
    rw [EdgePath.edgeSetGraph_insert]
    exact simpleGraph_isAcyclic_sup_edge_of_not_reachable
      data.edgeSetGraph_isAcyclic hnotReach
  refine ⟨{
    inSameComponent := fun i j =>
      ∃ γ : List (Edge V), EdgePath.IsSimplePath S' γ i j
    isSimplePath := fun γ i j =>
      EdgePath.IsSimplePath S' γ i j
    pathIn := fun _ _ h => Classical.choose h
    pathIn_isSimple := ?_
    isSimplePath_iff := ?_
    sameComponent_of_simplePath := ?_
    path_unique := ?_
    path_edges_mem := ?_
    edge_isSimplePath := ?_ }⟩
  · intro i j h
    exact Classical.choose_spec h
  · intro i j γ
    rfl
  · intro i j γ hγ
    exact ⟨γ, hγ⟩
  · intro i j γ₁ γ₂ hγ₁ hγ₂
    exact EdgePath.IsSimplePath.unique_of_isAcyclic hG hγ₁ hγ₂
  · intro i j γ hγ e' he'
    exact hγ.edge_mem e' he'
  · intro e' he'
    exact
      ⟨EdgePath.IsPath.cons he' e'.between_left_right
        (EdgePath.IsPath.nil e'.right), by simp⟩

theorem acyclic_insert_iff
    {S : Finset (Edge V)} (data : AcyclicEdgeSetData S)
    {e : Edge V} (he : e ∉ S) :
    IsAcyclicEdgeSet (insert e S) ↔
      ¬ data.inSameComponent e.left e.right := by
  constructor
  · intro hacyclic hcomp
    exact (data.not_isAcyclicEdgeSet_insert_of_inSameComponent he hcomp)
      hacyclic
  · exact data.isAcyclicEdgeSet_insert_of_not_inSameComponent

/-- Upgrade any acyclicity certificate to a `Forest` representative certificate. -/
def toForest {S : Finset (Edge V)} (data : AcyclicEdgeSetData S) :
    Forest V where
  edges := S
  acyclic := data
  acyclic_insert_iff' := by
    intro i j hij he
    simpa [data.inSameComponent_iff_of_between (Edge.mk_between i j hij)]
      using data.acyclic_insert_iff (e := Edge.mk i j hij) he

theorem toForest_edges {S : Finset (Edge V)} (data : AcyclicEdgeSetData S) :
    data.toForest.edges = S :=
  rfl

end AcyclicEdgeSetData

namespace Forest

variable {V} [Fintype V] [DecidableEq V]

theorem inSameComponent_trans (F : Forest V)
    {i j k : V} (hij : F.inSameComponent i j)
    (hjk : F.inSameComponent j k) :
    F.inSameComponent i k :=
  F.acyclic.inSameComponent_trans hij hjk

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
