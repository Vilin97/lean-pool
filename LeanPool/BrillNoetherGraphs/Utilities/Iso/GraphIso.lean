/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.Parameters

/-!
# Chip-firing graph isomorphisms

This module transports divisor theory along an equivalence of vertex types
that preserves every edge multiplicity. The definition deliberately ignores
the orientation chosen for pairs in the raw edge multiset: `num_edges` is the
mathematical graph structure used by chip firing.
-/

namespace Utilities

universe u v w

/-- An isomorphism of chip-firing graphs is an equivalence of their vertex
types preserving every edge multiplicity. -/
structure CFGraphIso (G : CFGraph.{u}) (H : CFGraph.{v}) where
  vertexEquiv : G.V ≃ H.V
  map_num_edges : ∀ x y : G.V,
    num_edges H (vertexEquiv x) (vertexEquiv y) = num_edges G x y

namespace CFGraphIso

variable {G : CFGraph.{u}} {H : CFGraph.{v}} {K : CFGraph.{w}}

/-- The identity graph isomorphism. -/
def refl (G : CFGraph.{u}) : CFGraphIso G G where
  vertexEquiv := Equiv.refl G.V
  map_num_edges := by simp

/-- The inverse of a graph isomorphism. -/
def symm (φ : CFGraphIso G H) : CFGraphIso H G where
  vertexEquiv := φ.vertexEquiv.symm
  map_num_edges := by
    intro x y
    simpa using
      (φ.map_num_edges (φ.vertexEquiv.symm x) (φ.vertexEquiv.symm y)).symm

/-- The composite of graph isomorphisms. -/
def trans (φ : CFGraphIso G H) (ψ : CFGraphIso H K) : CFGraphIso G K where
  vertexEquiv := φ.vertexEquiv.trans ψ.vertexEquiv
  map_num_edges := by
    intro x y
    exact (ψ.map_num_edges (φ.vertexEquiv x) (φ.vertexEquiv y)).trans
      (φ.map_num_edges x y)

/-- Relabel an integer-valued vertex function along a graph isomorphism.
This is used for both divisors and firing scripts. -/
def mapDiv (φ : CFGraphIso G H) : CFDiv G ≃+ CFDiv H :=
  AddEquiv.arrowCongr φ.vertexEquiv (AddEquiv.refl ℤ)

/-- Relabeling a firing script is the same additive equivalence as relabeling
a divisor. -/
abbrev mapScript (φ : CFGraphIso G H) : firing_script G ≃+ firing_script H :=
  φ.mapDiv

@[simp] theorem mapDiv_apply (φ : CFGraphIso G H) (D : CFDiv G) (w : H.V) :
    φ.mapDiv D w = D (φ.vertexEquiv.symm w) := rfl

@[simp] theorem mapDiv_apply_vertex
    (φ : CFGraphIso G H) (D : CFDiv G) (v : G.V) :
    φ.mapDiv D (φ.vertexEquiv v) = D v := by
  simp

@[simp] theorem mapDiv_symm (φ : CFGraphIso G H) :
    φ.symm.mapDiv = φ.mapDiv.symm := rfl

@[simp] theorem mapDiv_trans (φ : CFGraphIso G H) (ψ : CFGraphIso H K) :
    (φ.trans ψ).mapDiv = φ.mapDiv.trans ψ.mapDiv := rfl

@[simp] theorem mapDiv_symm_mapDiv
    (φ : CFGraphIso G H) (D : CFDiv G) :
    φ.symm.mapDiv (φ.mapDiv D) = D := by
  simp

@[simp] theorem mapDiv_mapDiv_symm
    (φ : CFGraphIso G H) (D : CFDiv H) :
    φ.mapDiv (φ.symm.mapDiv D) = D := by
  simp

/-- Relabeling carries a one-chip divisor to the corresponding vertex. -/
@[simp] theorem mapDiv_one_chip (φ : CFGraphIso G H) (v : G.V) :
    φ.mapDiv (one_chip v) = one_chip (φ.vertexEquiv v) := by
  funext w
  obtain ⟨x, rfl⟩ := φ.vertexEquiv.surjective w
  simp [one_chip]

/-- Vertex degree is invariant under graph isomorphism. -/
@[simp] theorem vertex_degree_map (φ : CFGraphIso G H) (v : G.V) :
    vertex_degree H (φ.vertexEquiv v) = vertex_degree G v := by
  unfold vertex_degree
  rw [← φ.vertexEquiv.sum_comp]
  simp [φ.map_num_edges]

/-- Divisor degree is invariant under relabeling. -/
@[simp] theorem deg_mapDiv (φ : CFGraphIso G H) (D : CFDiv G) :
    deg (φ.mapDiv D) = deg D := by
  change (∑ w : H.V, D (φ.vertexEquiv.symm w)) = ∑ v : G.V, D v
  exact φ.vertexEquiv.symm.sum_comp D

/-- Effectivity is invariant under relabeling. -/
@[simp] theorem effective_mapDiv_iff (φ : CFGraphIso G H) (D : CFDiv G) :
    effective (φ.mapDiv D) ↔ effective D := by
  constructor
  · intro h v
    simpa using h (φ.vertexEquiv v)
  · intro h w
    simpa using h (φ.vertexEquiv.symm w)

/-- Principal divisors commute with relabeling. -/
@[simp] theorem mapDiv_prin
    (φ : CFGraphIso G H) (σ : firing_script G) :
    φ.mapDiv (prin G σ) = prin H (φ.mapScript σ) := by
  funext w
  obtain ⟨v, rfl⟩ := φ.vertexEquiv.surjective w
  rw [mapDiv_apply_vertex]
  change
    (∑ u : G.V, (σ u - σ v) * (num_edges G v u : ℤ)) =
      ∑ z : H.V,
        (φ.mapScript σ z - φ.mapScript σ (φ.vertexEquiv v)) *
          (num_edges H (φ.vertexEquiv v) z : ℤ)
  rw [← φ.vertexEquiv.sum_comp]
  simp [φ.map_num_edges]

/-- Membership in the subgroup of principal divisors is invariant under
relabeling. -/
@[simp] theorem mem_principal_mapDiv_iff
    (φ : CFGraphIso G H) (D : CFDiv G) :
    φ.mapDiv D ∈ principal_divisors H ↔ D ∈ principal_divisors G := by
  constructor
  · intro h
    have hMapped : φ.symm.mapDiv (φ.mapDiv D) ∈ principal_divisors G := by
      rw [principal_iff_eq_prin] at h ⊢
      obtain ⟨σ, hσ⟩ := h
      refine ⟨φ.symm.mapScript σ, ?_⟩
      rw [hσ, mapDiv_prin]
    simpa using hMapped
  · intro h
    rw [principal_iff_eq_prin] at h ⊢
    obtain ⟨σ, hσ⟩ := h
    refine ⟨φ.mapScript σ, ?_⟩
    rw [← mapDiv_prin, hσ]

/-- Linear equivalence is invariant under relabeling. -/
@[simp] theorem linear_equiv_mapDiv_iff
    (φ : CFGraphIso G H) (D E : CFDiv G) :
    linear_equiv H (φ.mapDiv D) (φ.mapDiv E) ↔ linear_equiv G D E := by
  simpa [linear_equiv] using φ.mem_principal_mapDiv_iff (E - D)

/-- Winnability is invariant under relabeling. -/
@[simp] theorem winnable_mapDiv_iff
    (φ : CFGraphIso G H) (D : CFDiv G) :
    winnable H (φ.mapDiv D) ↔ winnable G D := by
  rw [winnable_iff_exists_effective, winnable_iff_exists_effective]
  constructor
  · rintro ⟨E, hEffective, hEquiv⟩
    refine ⟨φ.symm.mapDiv E, ?_, ?_⟩
    · exact (φ.symm.effective_mapDiv_iff E).mpr hEffective
    · have hMapped :=
        (φ.symm.linear_equiv_mapDiv_iff (φ.mapDiv D) E).mpr hEquiv
      simpa using hMapped
  · rintro ⟨E, hEffective, hEquiv⟩
    exact ⟨φ.mapDiv E, (φ.effective_mapDiv_iff E).mpr hEffective,
      (φ.linear_equiv_mapDiv_iff D E).mpr hEquiv⟩

/-- Relabeling preserves the set of effective divisors of each degree. -/
@[simp] theorem mem_eff_of_degree_mapDiv_iff
    (φ : CFGraphIso G H) (E : CFDiv G) (k : ℤ) :
    φ.mapDiv E ∈ eff_of_degree H k ↔ E ∈ eff_of_degree G k := by
  simp [eff_of_degree]

/-- Every rank lower bound is invariant under relabeling. -/
@[simp] theorem rank_geq_mapDiv_iff
    (φ : CFGraphIso G H) (D : CFDiv G) (k : ℤ) :
    rank_geq H (φ.mapDiv D) k ↔ rank_geq G D k := by
  constructor
  · intro hRank E hE
    have hTarget := hRank (φ.mapDiv E)
      ((φ.mem_eff_of_degree_mapDiv_iff E k).mpr hE)
    have hTarget' : winnable H (φ.mapDiv (D - E)) := by
      simpa using hTarget
    exact (φ.winnable_mapDiv_iff (D - E)).mp hTarget'
  · intro hRank E hE
    let E' : CFDiv G := φ.symm.mapDiv E
    have hE' : E' ∈ eff_of_degree G k := by
      exact (φ.symm.mem_eff_of_degree_mapDiv_iff E k).mpr hE
    have hSource := hRank E' hE'
    have hTarget := (φ.winnable_mapDiv_iff (D - E')).mpr hSource
    simpa [E'] using hTarget

/-- Baker--Norine rank is invariant under relabeling. -/
@[simp] theorem rank_mapDiv (φ : CFGraphIso G H) (D : CFDiv G) :
    rank H (φ.mapDiv D) = rank G D := by
  apply le_antisymm
  · apply (rank_geq_iff G D (rank H (φ.mapDiv D))).mp
    exact (φ.rank_geq_mapDiv_iff D (rank H (φ.mapDiv D))).mp
      ((rank_geq_iff H (φ.mapDiv D) (rank H (φ.mapDiv D))).mpr le_rfl)
  · apply (rank_geq_iff H (φ.mapDiv D) (rank G D)).mp
    exact (φ.rank_geq_mapDiv_iff D (rank G D)).mpr
      ((rank_geq_iff G D (rank G D)).mpr le_rfl)

/-- Isomorphic graphs have the same number of vertices. -/
@[simp] theorem vertex_card_eq (φ : CFGraphIso G H) :
    Fintype.card H.V = Fintype.card G.V := by
  exact (Fintype.card_congr φ.vertexEquiv).symm

/-- The raw edge multisets of isomorphic graphs have the same cardinality,
even though their choices of pair orientation need not agree. -/
@[simp] theorem edge_card_eq (φ : CFGraphIso G H) :
    H.edges.card = G.edges.card := by
  have hDegreeSum :
      (∑ w : H.V, vertex_degree H w) =
        ∑ v : G.V, vertex_degree G v := by
    rw [← φ.vertexEquiv.sum_comp]
    simp
  have hH := sum_vertex_degree_eq_twice_card_edges H
  have hG := sum_vertex_degree_eq_twice_card_edges G
  have hCast : (H.edges.card : ℤ) = (G.edges.card : ℤ) := by
    linarith
  exact_mod_cast hCast

/-- Graph genus is invariant under isomorphism. -/
@[simp] theorem genus_eq (φ : CFGraphIso G H) : genus H = genus G := by
  rw [genus, genus, φ.edge_card_eq, φ.vertex_card_eq]

/-- Connectivity is transported in the forward direction by a graph
isomorphism. -/
theorem graph_connected_map (φ : CFGraphIso G H)
    (hConnected : graph_connected G) : graph_connected H := by
  intro S hCut
  let T : Finset G.V := S.map φ.vertexEquiv.symm.toEmbedding
  obtain ⟨a, b, ha, hb⟩ := hCut
  have hCutT : ∃ x y : G.V, x ∈ T ∧ y ∉ T := by
    refine ⟨φ.vertexEquiv.symm a, φ.vertexEquiv.symm b, ?_, ?_⟩
    · simp [T, ha]
    · simp [T, hb]
  obtain ⟨x, hx, y, hy, hxy⟩ := hConnected T hCutT
  refine ⟨φ.vertexEquiv x, ?_, φ.vertexEquiv y, ?_, ?_⟩
  · simpa [T] using hx
  · simpa [T] using hy
  · rw [φ.map_num_edges]
    exact hxy

/-- Graph connectivity is invariant under isomorphism. -/
@[simp] theorem graph_connected_iff (φ : CFGraphIso G H) :
    graph_connected H ↔ graph_connected G := by
  exact ⟨φ.symm.graph_connected_map, φ.graph_connected_map⟩

/-- Brill--Noether existence is invariant under graph isomorphism. -/
@[simp] theorem BNExists_iff (φ : CFGraphIso G H) (r d : ℤ) :
    BNExists H r d ↔ BNExists G r d := by
  constructor
  · rintro ⟨D, hDegree, hRank⟩
    refine ⟨φ.symm.mapDiv D, ?_, ?_⟩
    · rw [φ.symm.deg_mapDiv]
      exact hDegree
    · rw [φ.symm.rank_mapDiv]
      exact hRank
  · rintro ⟨D, hDegree, hRank⟩
    refine ⟨φ.mapDiv D, ?_, ?_⟩
    · rw [φ.deg_mapDiv]
      exact hDegree
    · rw [φ.rank_mapDiv]
      exact hRank

end CFGraphIso

end Utilities
