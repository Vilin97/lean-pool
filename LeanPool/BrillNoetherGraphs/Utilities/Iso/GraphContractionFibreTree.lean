/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Iso.GraphContractionEuler
public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.UnderlyingSimpleGraph
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Tactic

/-!
# Tree fibres in equal-genus topological contractions

The first ingredient is a small general fact about finite loopless
multigraphs: a connected graph has at least one fewer edge occurrence than
vertices.  We prove it by forgetting multiplicities, taking a spanning tree
in the resulting simple graph, and observing that every simple edge has an
ambient occurrence.

This is the local inequality used with the Euler accounting in
`GraphContractionEuler`: after the still-to-be-packaged partition identity for
the fibre edge multisets, equality of source and target genus forces equality
in this bound fibre by fibre.
-/

@[expose] public section

namespace Utilities

open Finset

universe u v

private theorem sum_card_filter_eq_sum_map {ι α : Type*} [Fintype ι]
    [DecidableEq ι] (M : Multiset α) (crit : ι → α → Prop)
    [∀ i edge, Decidable (crit i edge)] :
    ∑ i : ι, (M.filter (crit i)).card =
      Multiset.sum (M.map fun edge =>
        (Finset.univ.filter fun i => crit i edge).card) := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons edge M ih =>
      rw [Multiset.map_cons, Multiset.sum_cons]
      simp_rw [← Multiset.countP_eq_card_filter]
      simp only [Multiset.countP_cons]
      rw [Finset.sum_add_distrib]
      have hCount : (∑ i : ι, if crit i edge then 1 else 0) =
          (Finset.univ.filter fun i => crit i edge).card := by
        rw [← Finset.card_filter]
      rw [hCount]
      simp_rw [Multiset.countP_eq_card_filter]
      rw [add_comm, ih]

private theorem sum_map_ite_eq_card_filter {α : Type*} (M : Multiset α)
    (predicate : α → Prop) [DecidablePred predicate] :
    Multiset.sum (M.map fun edge => if predicate edge then 1 else 0) =
      (M.filter predicate).card := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons edge M ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.filter_cons]
      by_cases h : predicate edge
      · simp [h, ih, Nat.add_comm]
      · simp [h, ih]

private theorem sum_map_ite_const_eq_mul_card_filter {α : Type*} (M : Multiset α)
    (predicate : α → Prop) [DecidablePred predicate] (n : ℕ) :
    Multiset.sum (M.map fun edge => if predicate edge then n else 0) =
      n * (M.filter predicate).card := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons edge M ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.filter_cons]
      by_cases h : predicate edge
      · simp [h, ih, Nat.mul_succ, Nat.add_comm]
      · simp [h, ih]

/-- Forgetting multiplicities cannot create more edges than the ambient
multigraph has occurrences. -/
theorem underlyingSimpleGraph_edgeFinset_card_le (G : CFGraph.{u}) :
    (underlyingSimpleGraph G).edgeFinset.card ≤ G.edges.card := by
  classical
  calc
    (underlyingSimpleGraph G).edgeFinset.card ≤
        (G.edges.map fun edge => s(edge.1, edge.2)).toFinset.card := by
      apply Finset.card_le_card
      intro e he
      rw [Multiset.mem_toFinset]
      rw [SimpleGraph.mem_edgeFinset] at he
      refine Sym2.ind ?_ e he
      intro x y hxy
      change numEdges G x y > 0 at hxy
      change 0 < (G.edges.filter (fun edge =>
        edge = (x, y) ∨ edge = (y, x))).card at hxy
      rw [Multiset.card_pos_iff_exists_mem] at hxy
      obtain ⟨edge, hedge⟩ := hxy
      rw [Multiset.mem_filter] at hedge
      rcases hedge with ⟨hEdge, hEdgeEndpoints⟩
      refine Multiset.mem_map.mpr ⟨edge, hEdge, ?_⟩
      rcases hEdgeEndpoints with hEdgeEndpoints | hEdgeEndpoints
      · simp [hEdgeEndpoints]
      · simp [hEdgeEndpoints, Sym2.eq_swap]
    _ ≤ (G.edges.map fun edge => s(edge.1, edge.2)).card :=
      Multiset.toFinset_card_le _
    _ = G.edges.card := Multiset.card_map _ _

/-- Every connected loopless multigraph has at least `|V|-1` edge
occurrences.  Parallel edges are allowed. -/
theorem graph_connected_card_vertices_le_card_edges_add_one
    (G : CFGraph.{u}) (hConnected : graphConnected G) :
    Fintype.card G.V ≤ G.edges.card + 1 := by
  have hSimple : (underlyingSimpleGraph G).Connected :=
    (graph_connected_iff_underlyingSimpleGraph_connected G).mp hConnected
  have hTreeBound := hSimple.card_vert_le_card_edgeSet_add_one
  have hForget : (underlyingSimpleGraph G).edgeFinset.card ≤ G.edges.card :=
    underlyingSimpleGraph_edgeFinset_card_le G
  have hSimpleCard :
      Fintype.card G.V ≤ (underlyingSimpleGraph G).edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
      using hTreeBound
  omega

/-- The cyclomatic genus of a connected loopless multigraph is nonnegative. -/
theorem genus_nonneg_of_graph_connected (G : CFGraph.{u})
    (hConnected : graphConnected G) : 0 ≤ genus G := by
  have hBound := graph_connected_card_vertices_le_card_edges_add_one G hConnected
  simp only [genus]
  omega

namespace Certificate.GraphContractionCertificate

variable {G : CFGraph.{u}} {H : CFGraph.{v}}

private def edgeInternal (c : GraphContractionCertificate G H)
    (edge : G.V × G.V) : Prop :=
  c.vertexMap edge.1 = c.vertexMap edge.2

private def fibreEdgeAt (c : GraphContractionCertificate G H) (target : H.V)
    (edge : G.V × G.V) : Prop :=
  c.vertexMap edge.1 = target ∧ c.vertexMap edge.2 = target

private def edgeRealizesDirectedPair (c : GraphContractionCertificate G H)
    (pair : G.V × G.V) (edge : G.V × G.V) : Prop :=
  c.vertexMap pair.1 = c.vertexMap pair.2 ∧
    (edge = pair ∨ edge = pair.swap)

private theorem fibreEdgeAt_implies_internal (c : GraphContractionCertificate G H)
    (target : H.V) (edge : G.V × G.V) :
    c.fibreEdgeAt target edge → c.edgeInternal edge := by
  rintro ⟨hLeft, hRight⟩
  exact hLeft.trans hRight.symm

/-- The fibre vertex cards partition the source vertex set. -/
theorem sum_fibreVertices_card (c : GraphContractionCertificate G H) :
    ∑ target : H.V, (c.fibreVertices target).card = Fintype.card G.V := by
  symm
  simpa only [fibreVertices, Finset.card_filter, Finset.mem_univ,
    Finset.filter_true, Finset.sum_const_zero, Finset.sum_const,
    nsmul_eq_mul, mul_one, Finset.card_univ] using
    (Finset.card_eq_sum_card_fiberwise
      (f := c.vertexMap) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _))
/-- Fibre edge cards partition the source edge occurrences which are
contracted by the vertex map. -/
theorem sum_fibreGraph_edge_cards (c : GraphContractionCertificate G H)
    (hValid : c.Valid) :
    ∑ target : H.V, (c.fibreGraph hValid target).edges.card =
      (G.edges.filter fun edge =>
        c.vertexMap edge.1 = c.vertexMap edge.2).card := by
  classical
  have hCount (edge : G.V × G.V) :
      (Finset.univ.filter fun target => c.fibreEdgeAt target edge).card =
        if c.vertexMap edge.1 = c.vertexMap edge.2 then 1 else 0 := by
    by_cases hInternal : c.edgeInternal edge
    · change c.vertexMap edge.1 = c.vertexMap edge.2 at hInternal
      simp only [hInternal, ite_true]
      rw [Finset.card_eq_one]
      refine ⟨c.vertexMap edge.1, ?_⟩
      ext target
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hLeft, _⟩
        exact hLeft.symm
      · intro hTarget
        subst target
        exact ⟨rfl, hInternal.symm⟩
    · change ¬c.vertexMap edge.1 = c.vertexMap edge.2 at hInternal
      simp only [hInternal, ite_false]
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro target hTarget
      have hAt := (Finset.mem_filter.mp hTarget).2
      exact hInternal (c.fibreEdgeAt_implies_internal target edge hAt)
  have hCards : (∑ target : H.V, (c.fibreGraph hValid target).edges.card) =
      ∑ target : H.V, (G.edges.filter (c.fibreEdgeAt target)).card := by
    apply Finset.sum_congr rfl
    intro target _
    have hcard := inducedSubgraph_edge_card_eq_filter G (c.fibreVertices target)
      (c.fibreVertices_nonempty hValid target)
    simp only [fibreVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hcard
    convert! hcard using 1
    apply congrArg (fun edges : Multiset (G.V × G.V) => edges.card)
    exact Multiset.filter_congr (fun _ _ => Iff.rfl)
  rw [hCards]
  rw [sum_card_filter_eq_sum_map]
  calc
    _ = Multiset.sum (G.edges.map fun edge =>
        if c.vertexMap edge.1 = c.vertexMap edge.2 then 1 else 0) := by
      congr 1
      exact Multiset.map_congr rfl (fun edge _ => by
        simpa only [fibreEdgeAt] using hCount edge)
    _ = _ := sum_map_ite_eq_card_filter G.edges
      (fun edge => c.vertexMap edge.1 = c.vertexMap edge.2)

/-- Internal directed multiplicity counts every contracted edge occurrence at
each of its two endpoints. -/
theorem internalDirectedMultiplicity_eq_two_mul_contractedEdgeCard
    (c : GraphContractionCertificate G H) :
    c.internalDirectedMultiplicity =
      2 * ((G.edges.filter fun edge =>
        c.vertexMap edge.1 = c.vertexMap edge.2).card : ℤ) := by
  classical
  have hEndpointsDistinct (edge : G.V × G.V) (hEdge : edge ∈ G.edges) :
      edge.1 ≠ edge.2 := by
    intro hEqual
    have hLoop : edge = (edge.1, edge.1) := by
      apply Prod.ext
      · rfl
      · exact hEqual.symm
    rw [hLoop] at hEdge
    exact G.loopless edge.1 hEdge
  have hDirectedCount (edge : G.V × G.V) (hEdge : edge ∈ G.edges) :
      (Finset.univ.filter fun pair => c.edgeRealizesDirectedPair pair edge).card =
        if c.vertexMap edge.1 = c.vertexMap edge.2 then 2 else 0 := by
    by_cases hInternal : c.vertexMap edge.1 = c.vertexMap edge.2
    · simp only [hInternal, ite_true]
      rw [Finset.card_eq_two]
      refine ⟨(edge.1, edge.2), (edge.2, edge.1), ?_, ?_⟩
      · intro hEqual
        have hFirst := congrArg Prod.fst hEqual
        exact hEndpointsDistinct edge hEdge hFirst
      · ext pair
        rcases pair with ⟨x, y⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton]
        change
          (c.vertexMap x = c.vertexMap y ∧
            (edge = (x, y) ∨ edge = (y, x))) ↔
              (x, y) = (edge.1, edge.2) ∨ (x, y) = (edge.2, edge.1)
        constructor
        · intro h
          rcases h.2 with hPair | hPair
          · exact Or.inl hPair.symm
          · cases hPair
            exact Or.inr rfl
        · rintro (hPair | hPair)
          · injection hPair with hx hy
            subst x
            subst y
            exact ⟨hInternal, Or.inl rfl⟩
          · injection hPair with hx hy
            subst x
            subst y
            exact ⟨hInternal.symm, Or.inr rfl⟩
    · simp only [hInternal, ite_false]
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_of_forall_notMem
      intro pair hPair
      have hRealizes := (Finset.mem_filter.mp hPair).2
      rcases hRealizes.2 with hPairEq | hPairEq
      · have hEq : c.vertexMap edge.1 = c.vertexMap edge.2 := by
          rw [hPairEq]
          exact hRealizes.1
        exact hInternal hEq
      · have hEq : c.vertexMap edge.1 = c.vertexMap edge.2 := by
          rw [hPairEq]
          exact hRealizes.1.symm
        exact hInternal hEq
  let natInternal : ℕ := ∑ x : G.V, ∑ y : G.V,
    if c.vertexMap x = c.vertexMap y then numEdges G x y else 0
  have hNatInternal : natInternal =
      2 * (G.edges.filter fun edge =>
        c.vertexMap edge.1 = c.vertexMap edge.2).card := by
    calc
      natInternal = ∑ pair : G.V × G.V,
          (G.edges.filter fun edge =>
            c.edgeRealizesDirectedPair pair edge).card := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        simp only [edgeRealizesDirectedPair]
        by_cases hMap : c.vertexMap x = c.vertexMap y <;>
          simp [hMap, numEdges]
      _ = Multiset.sum (G.edges.map fun edge =>
          (Finset.univ.filter fun pair =>
            c.edgeRealizesDirectedPair pair edge).card) :=
        sum_card_filter_eq_sum_map G.edges c.edgeRealizesDirectedPair
      _ = Multiset.sum (G.edges.map fun edge =>
          if c.vertexMap edge.1 = c.vertexMap edge.2 then 2 else 0) := by
        apply congrArg Multiset.sum
        apply Multiset.map_congr rfl
        intro edge hEdge
        exact hDirectedCount edge hEdge
      _ = 2 * (G.edges.filter fun edge =>
          c.vertexMap edge.1 = c.vertexMap edge.2).card :=
        sum_map_ite_const_eq_mul_card_filter _ _ 2
  have hCastInternal : c.internalDirectedMultiplicity = (natInternal : ℤ) := by
    simp only [internalDirectedMultiplicity, natInternal, Nat.cast_sum,
      Nat.cast_ite, Nat.cast_zero]
  calc
    c.internalDirectedMultiplicity = (natInternal : ℤ) := hCastInternal
    _ = (2 * (G.edges.filter fun edge =>
        c.vertexMap edge.1 = c.vertexMap edge.2).card : ℕ) := by
      exact_mod_cast hNatInternal
    _ = 2 * ((G.edges.filter fun edge =>
        c.vertexMap edge.1 = c.vertexMap edge.2).card : ℤ) := by norm_num

/-- The internal directed multiplicity is twice the total number of edge
occurrences in the induced fibre graphs. -/
theorem internalDirectedMultiplicity_eq_two_mul_sum_fibreGraph_edge_cards
    (c : GraphContractionCertificate G H) (hValid : c.Valid) :
    c.internalDirectedMultiplicity =
      2 * (∑ target : H.V, (c.fibreGraph hValid target).edges.card : ℤ) := by
  rw [c.internalDirectedMultiplicity_eq_two_mul_contractedEdgeCard]
  congr 1
  rw [← c.sum_fibreGraph_edge_cards hValid, Nat.cast_sum]

/-- A connected-fibre quotient cannot increase cyclomatic genus. -/
theorem genus_le_of_topologicalValid (c : GraphContractionCertificate G H)
    (hTopological : c.TopologicalValid) : genus H ≤ genus G := by
  have hBound (target : H.V) :
      (Fintype.card (c.fibreGraph hTopological.1 target).V : ℤ) ≤
        (c.fibreGraph hTopological.1 target).edges.card + 1 := by
    exact_mod_cast graph_connected_card_vertices_le_card_edges_add_one _
      (c.fibreGraph_connected_of_topologicalValid hTopological target)
  have hVertexSum :
      (∑ target : H.V,
        (Fintype.card (c.fibreGraph hTopological.1 target).V : ℤ)) =
          Fintype.card G.V := by
    have hVertexSumNat :
        (∑ target : H.V,
          Fintype.card (c.fibreGraph hTopological.1 target).V) =
            Fintype.card G.V := by
      calc
        (∑ target : H.V,
          Fintype.card (c.fibreGraph hTopological.1 target).V) =
            ∑ target : H.V, (c.fibreVertices target).card := by
              apply Finset.sum_congr rfl
              intro target _
              rw [fibreGraph, inducedSubgraph_vertex_card]
        _ = Fintype.card G.V := c.sum_fibreVertices_card
    exact_mod_cast hVertexSumNat
  have hEdgeSum :
      (∑ target : H.V,
        ((c.fibreGraph hTopological.1 target).edges.card : ℤ)) =
          (G.edges.card : ℤ) - H.edges.card := by
    have hInternal :=
      c.internalDirectedMultiplicity_eq_two_mul_sum_fibreGraph_edge_cards
        hTopological.1
    have hEuler :=
      c.internalDirectedMultiplicity_eq_two_mul_edgeLoss hTopological.1
    omega
  have hTotalBound :
      (∑ target : H.V,
        (Fintype.card (c.fibreGraph hTopological.1 target).V : ℤ)) ≤
          ∑ target : H.V,
            (((c.fibreGraph hTopological.1 target).edges.card : ℤ) + 1) := by
    exact Finset.sum_le_sum fun target _ => hBound target
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, hVertexSum, hEdgeSum] at hTotalBound
  simp only [genus]
  omega

/-- If a connected-fibre quotient preserves genus, every fibre has exactly
one fewer edge occurrence than vertices. -/
theorem fibreGraph_edge_card_add_one_eq_vertex_card_of_genus_eq
    (c : GraphContractionCertificate G H) (hTopological : c.TopologicalValid)
    (hGenus : genus G = genus H) (target : H.V) :
    (c.fibreGraph hTopological.1 target).edges.card + 1 =
      Fintype.card (c.fibreGraph hTopological.1 target).V := by
  have hBound (vertex : H.V) :
      (Fintype.card (c.fibreGraph hTopological.1 vertex).V : ℤ) ≤
        (c.fibreGraph hTopological.1 vertex).edges.card + 1 := by
    exact_mod_cast graph_connected_card_vertices_le_card_edges_add_one _
      (c.fibreGraph_connected_of_topologicalValid hTopological vertex)
  have hVertexSum :
      (∑ vertex : H.V,
        (Fintype.card (c.fibreGraph hTopological.1 vertex).V : ℤ)) =
          Fintype.card G.V := by
    have hVertexSumNat :
        (∑ vertex : H.V,
          Fintype.card (c.fibreGraph hTopological.1 vertex).V) =
            Fintype.card G.V := by
      calc
        (∑ vertex : H.V,
          Fintype.card (c.fibreGraph hTopological.1 vertex).V) =
            ∑ vertex : H.V, (c.fibreVertices vertex).card := by
              apply Finset.sum_congr rfl
              intro vertex _
              rw [fibreGraph, inducedSubgraph_vertex_card]
        _ = Fintype.card G.V := c.sum_fibreVertices_card
    exact_mod_cast hVertexSumNat
  have hEdgeSum :
      (∑ vertex : H.V,
        ((c.fibreGraph hTopological.1 vertex).edges.card : ℤ)) =
          (G.edges.card : ℤ) - H.edges.card := by
    have hInternal :=
      c.internalDirectedMultiplicity_eq_two_mul_sum_fibreGraph_edge_cards
        hTopological.1
    have hEuler :=
      c.internalDirectedMultiplicity_eq_two_mul_edgeLoss hTopological.1
    omega
  have hTotalEqual :
      (∑ vertex : H.V,
        (((c.fibreGraph hTopological.1 vertex).edges.card : ℤ) + 1)) =
          ∑ vertex : H.V,
            (Fintype.card (c.fibreGraph hTopological.1 vertex).V : ℤ) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, hEdgeSum, hVertexSum]
    simp only [genus] at hGenus
    omega
  have hDeficitSum :
      (∑ vertex : H.V,
        (((c.fibreGraph hTopological.1 vertex).edges.card : ℤ) + 1 -
          Fintype.card (c.fibreGraph hTopological.1 vertex).V)) = 0 := by
    rw [Finset.sum_sub_distrib, hTotalEqual]
    omega
  have hEveryDeficitZero : ∀ vertex ∈ (Finset.univ : Finset H.V),
      ((c.fibreGraph hTopological.1 vertex).edges.card : ℤ) + 1 -
        Fintype.card (c.fibreGraph hTopological.1 vertex).V = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun vertex _ =>
      sub_nonneg.mpr (hBound vertex))).mp hDeficitSum
  have hTarget := hEveryDeficitZero target (Finset.mem_univ _)
  exact_mod_cast (by omega :
    ((c.fibreGraph hTopological.1 target).edges.card : ℤ) + 1 =
      Fintype.card (c.fibreGraph hTopological.1 target).V)

/-- In an equal-genus topological contraction, each fibre is a tree after
forgetting parallel-edge multiplicities. -/
theorem fibreGraph_underlyingSimpleGraph_isTree_of_genus_eq
    (c : GraphContractionCertificate G H) (hTopological : c.TopologicalValid)
    (hGenus : genus G = genus H) (target : H.V) :
    (underlyingSimpleGraph (c.fibreGraph hTopological.1 target)).IsTree := by
  let fibre := c.fibreGraph hTopological.1 target
  have hFibreConnected : _root_.graphConnected fibre := by
    exact c.fibreGraph_connected_of_topologicalValid hTopological target
  have hSimpleConnected : (underlyingSimpleGraph fibre).Connected :=
    (graph_connected_iff_underlyingSimpleGraph_connected fibre).mp hFibreConnected
  have hFibreCard : fibre.edges.card + 1 = Fintype.card fibre.V := by
    simpa only [fibre] using
      c.fibreGraph_edge_card_add_one_eq_vertex_card_of_genus_eq
        hTopological hGenus target
  have hSimpleLower :
      Fintype.card fibre.V ≤ (underlyingSimpleGraph fibre).edgeFinset.card + 1 := by
    have hTreeBound := hSimpleConnected.card_vert_le_card_edgeSet_add_one
    simpa only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
      using hTreeBound
  have hSimpleUpper : (underlyingSimpleGraph fibre).edgeFinset.card ≤ fibre.edges.card :=
    underlyingSimpleGraph_edgeFinset_card_le fibre
  have hSimpleCard :
      (underlyingSimpleGraph fibre).edgeFinset.card + 1 = Fintype.card fibre.V := by
    omega
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hSimpleConnected, ?_⟩
  simpa only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] using hSimpleCard

/-- Each connected contraction fibre has nonnegative cyclomatic genus. -/
theorem fibreGraph_genus_nonneg_of_topologicalValid
    (c : GraphContractionCertificate G H) (hTopological : c.TopologicalValid)
    (target : H.V) :
    0 ≤ genus (c.fibreGraph hTopological.1 target) :=
  genus_nonneg_of_graph_connected _
    (c.fibreGraph_connected_of_topologicalValid hTopological target)

end Certificate.GraphContractionCertificate

end Utilities
