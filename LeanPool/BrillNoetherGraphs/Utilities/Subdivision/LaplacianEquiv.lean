/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.Parameters

/-!
# Rank transport under an adjacency-preserving vertex equivalence

This file provides a narrow graph-transport layer for chip-firing
certificates.  Two `CFGraph`s are related when a vertex
equivalence preserves every edge multiplicity.  That is exactly the data used
by `prin`, so divisors, firing scripts, winnability, rank bounds, and
Brill--Noether existence transport without requiring a general graph
isomorphism API.
-/

@[expose] public section

namespace Utilities.Certificate

universe u v w

/-- A vertex equivalence preserving the multiplicity of every unordered edge.

The name emphasizes the only graph structure used below: preservation of the
chip-firing Laplacian.  No equality of the oriented edge multisets is required.
-/
structure LaplacianEquiv (G : CFGraph.{u}) (H : CFGraph.{v}) where
  /-- The vertex equivalence preserving edge multiplicities, hence transporting the graph
  Laplacian. -/
  toEquiv : G.V ≃ H.V
  num_edges_eq :
    ∀ x y : G.V,
      numEdges H (toEquiv x) (toEquiv y) = numEdges G x y

namespace LaplacianEquiv

variable {G : CFGraph.{u}} {H : CFGraph.{v}}

instance : CoeFun (LaplacianEquiv G H) (fun _ => G.V → H.V) :=
  ⟨fun equivalence => equivalence.toEquiv⟩

/-- Compose adjacency-preserving vertex equivalences.  This belongs in the
basic transport API rather than in a particular subdivision construction, so
proof-carrying normalization certificates can combine independent graph
presentations without changing universes. -/
def trans {K : CFGraph.{w}} (first : LaplacianEquiv G H)
    (second : LaplacianEquiv H K) : LaplacianEquiv G K where
  toEquiv := first.toEquiv.trans second.toEquiv
  num_edges_eq := by
    intro x y
    change numEdges K (second.toEquiv (first.toEquiv x))
      (second.toEquiv (first.toEquiv y)) = numEdges G x y
    rw [second.num_edges_eq, first.num_edges_eq]

/-- Reverse an adjacency-preserving vertex equivalence. -/
def symm (equivalence : LaplacianEquiv G H) : LaplacianEquiv H G where
  toEquiv := equivalence.toEquiv.symm
  num_edges_eq := by
    intro x y
    simpa using
      (equivalence.num_edges_eq
        (equivalence.toEquiv.symm x) (equivalence.toEquiv.symm y)).symm

/-- Transport a divisor forward along the vertex equivalence. -/
def mapDiv (equivalence : LaplacianEquiv G H) (D : CFDiv G) : CFDiv H :=
  fun y => D (equivalence.toEquiv.symm y)

/-- Transport a firing script forward along the vertex equivalence. -/
def mapScript (equivalence : LaplacianEquiv G H)
    (script : firingScript G) : firingScript H :=
  fun y => script (equivalence.toEquiv.symm y)

@[simp] theorem mapDiv_apply (equivalence : LaplacianEquiv G H)
    (D : CFDiv G) (y : H.V) :
    equivalence.mapDiv D y = D (equivalence.toEquiv.symm y) := rfl

@[simp] theorem mapScript_apply (equivalence : LaplacianEquiv G H)
    (script : firingScript G) (y : H.V) :
    equivalence.mapScript script y =
      script (equivalence.toEquiv.symm y) := rfl

@[simp] theorem symm_mapDiv (equivalence : LaplacianEquiv G H)
    (D : CFDiv G) :
    equivalence.symm.mapDiv (equivalence.mapDiv D) = D := by
  funext x
  simp [mapDiv, symm]

@[simp] theorem mapDiv_symm (equivalence : LaplacianEquiv G H)
    (D : CFDiv H) :
    equivalence.mapDiv (equivalence.symm.mapDiv D) = D := by
  funext y
  simp [mapDiv, symm]

@[simp] theorem mapDiv_zero (equivalence : LaplacianEquiv G H) :
    equivalence.mapDiv (0 : CFDiv G) = 0 := rfl

@[simp] theorem mapDiv_add (equivalence : LaplacianEquiv G H)
    (D E : CFDiv G) :
    equivalence.mapDiv (D + E) =
      equivalence.mapDiv D + equivalence.mapDiv E := rfl

@[simp] theorem mapDiv_sub (equivalence : LaplacianEquiv G H)
    (D E : CFDiv G) :
    equivalence.mapDiv (D - E) =
      equivalence.mapDiv D - equivalence.mapDiv E := rfl

@[simp] theorem mapDiv_neg (equivalence : LaplacianEquiv G H)
    (D : CFDiv G) :
    equivalence.mapDiv (-D) = -equivalence.mapDiv D := rfl

@[simp] theorem mapDiv_one_chip (equivalence : LaplacianEquiv G H)
    (x : G.V) :
    equivalence.mapDiv (oneChip x) = oneChip (equivalence x) := by
  funext y
  have hiff : equivalence.toEquiv.symm y = x ↔
      y = equivalence.toEquiv x := by
    constructor
    · intro h
      rw [← equivalence.toEquiv.apply_symm_apply y, h]
    · intro h
      rw [h, equivalence.toEquiv.symm_apply_apply]
  simp only [mapDiv, oneChip]
  by_cases h : equivalence.toEquiv.symm y = x
  · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
  · rw [ite_eq_right h, ite_eq_right (mt hiff.mpr h)]

/-- Vertex valence is preserved by an adjacency-preserving equivalence. -/
theorem vertex_degree_eq (equivalence : LaplacianEquiv G H) (x : G.V) :
    vertexDegree H (equivalence x) = vertexDegree G x := by
  unfold vertexDegree
  apply Fintype.sum_equiv equivalence.toEquiv.symm
  intro y
  simpa using congrArg (fun degree : ℕ => (degree : ℤ))
    (equivalence.num_edges_eq x (equivalence.toEquiv.symm y))

/-- Effectivity is unchanged by relabeling vertices. -/
theorem effective_mapDiv_iff (equivalence : LaplacianEquiv G H)
    (D : CFDiv G) :
    effective (equivalence.mapDiv D) ↔ effective D := by
  constructor
  · intro h x
    simpa using h (equivalence x)
  · intro h y
    exact h (equivalence.toEquiv.symm y)

/-- Divisor degree is unchanged by relabeling vertices. -/
@[simp] theorem deg_mapDiv (equivalence : LaplacianEquiv G H)
    (D : CFDiv G) :
    deg (equivalence.mapDiv D) = deg D := by
  change (∑ y : H.V, D (equivalence.toEquiv.symm y)) = ∑ x : G.V, D x
  exact Fintype.sum_equiv equivalence.toEquiv.symm _ _ (fun _ => rfl)

/-- The principal divisor of a transported firing script is the transported
principal divisor. -/
theorem mapDiv_prin (equivalence : LaplacianEquiv G H)
    (script : firingScript G) :
    equivalence.mapDiv (prin G script) =
      prin H (equivalence.mapScript script) := by
  funext y
  change
    (∑ x : G.V,
      (script x - script (equivalence.toEquiv.symm y)) *
        (numEdges G (equivalence.toEquiv.symm y) x : ℤ)) =
    ∑ z : H.V,
      (script (equivalence.toEquiv.symm z) -
          script (equivalence.toEquiv.symm y)) *
        (numEdges H y z : ℤ)
  apply Fintype.sum_equiv equivalence.toEquiv
  intro x
  simp only [Equiv.symm_apply_apply]
  rw [← equivalence.num_edges_eq
    (equivalence.toEquiv.symm y) x]
  simp

/-- Linear equivalence transports forward. -/
theorem linearEquiv_mapDiv (equivalence : LaplacianEquiv G H)
    {D E : CFDiv G} (h : linearEquiv G D E) :
    linearEquiv H (equivalence.mapDiv D) (equivalence.mapDiv E) := by
  unfold linearEquiv at h ⊢
  rw [principal_iff_eq_prin] at h ⊢
  obtain ⟨script, hscript⟩ := h
  refine ⟨equivalence.mapScript script, ?_⟩
  rw [← equivalence.mapDiv_prin script, ← equivalence.mapDiv_sub, hscript]

/-- Linear equivalence is unchanged by relabeling vertices. -/
theorem linearEquiv_mapDiv_iff (equivalence : LaplacianEquiv G H)
    (D E : CFDiv G) :
    linearEquiv H (equivalence.mapDiv D) (equivalence.mapDiv E) ↔
      linearEquiv G D E := by
  constructor
  · intro h
    have h' := equivalence.symm.linearEquiv_mapDiv h
    simpa using h'
  · exact equivalence.linearEquiv_mapDiv

/-- Winnability transports forward. -/
theorem winnable_mapDiv (equivalence : LaplacianEquiv G H)
    {D : CFDiv G} (h : winnable G D) :
    winnable H (equivalence.mapDiv D) := by
  rw [winnable_iff_exists_effective] at h ⊢
  obtain ⟨E, hEffective, hEquiv⟩ := h
  exact ⟨equivalence.mapDiv E,
    (equivalence.effective_mapDiv_iff E).2 hEffective,
    equivalence.linearEquiv_mapDiv hEquiv⟩

/-- Winnability is unchanged by relabeling vertices. -/
theorem winnable_mapDiv_iff (equivalence : LaplacianEquiv G H)
    (D : CFDiv G) :
    winnable H (equivalence.mapDiv D) ↔ winnable G D := by
  constructor
  · intro h
    have h' := equivalence.symm.winnable_mapDiv h
    simpa using h'
  · exact equivalence.winnable_mapDiv

/-- Every rank lower-bound predicate is unchanged by relabeling vertices. -/
theorem rank_geq_mapDiv_iff (equivalence : LaplacianEquiv G H)
    (D : CFDiv G) (k : ℤ) :
    rankGeq H (equivalence.mapDiv D) k ↔ rankGeq G D k := by
  constructor
  · intro h E hE
    have hMapped :
        winnable H
          (equivalence.mapDiv D - equivalence.mapDiv E) :=
      h (equivalence.mapDiv E)
        ⟨(equivalence.effective_mapDiv_iff E).2 hE.1, by simpa using hE.2⟩
    apply (equivalence.winnable_mapDiv_iff (D - E)).1
    simpa using hMapped
  · intro h E hE
    let E' : CFDiv G := equivalence.symm.mapDiv E
    have hE'Effective : effective E' :=
      (equivalence.symm.effective_mapDiv_iff E).2 hE.1
    have hE'Degree : deg E' = k := by
      simpa [E'] using hE.2
    have hWin : winnable G (D - E') := h E' ⟨hE'Effective, hE'Degree⟩
    have hMapped := equivalence.winnable_mapDiv hWin
    simpa [E'] using hMapped

/-- Numerical rank lower bounds are unchanged by relabeling vertices. -/
theorem rank_mapDiv_ge_iff (equivalence : LaplacianEquiv G H)
    (D : CFDiv G) (k : ℤ) :
    rank H (equivalence.mapDiv D) ≥ k ↔ rank G D ≥ k := by
  rw [← rank_geq_iff, equivalence.rank_geq_mapDiv_iff, rank_geq_iff]

/-- Graph connectivity is preserved by an adjacency-preserving vertex
equivalence. -/
theorem graphConnected (equivalence : LaplacianEquiv G H)
    (hG : graphConnected G) : graphConnected H := by
  classical
  intro S hS
  let pulled : Finset G.V :=
    S.preimage equivalence.toEquiv equivalence.toEquiv.injective.injOn
  obtain ⟨v, w, hv, hw⟩ := hS
  have hPulledSplit :
      ∃ x y : G.V, x ∈ pulled ∧ y ∉ pulled := by
    refine ⟨equivalence.toEquiv.symm v,
      equivalence.toEquiv.symm w, ?_, ?_⟩
    · simpa [pulled] using hv
    · simpa [pulled] using hw
  obtain ⟨x, hx, y, hy, hxy⟩ := hG pulled hPulledSplit
  refine ⟨equivalence x, ?_, equivalence y, ?_, ?_⟩
  · simpa [pulled] using hx
  · simpa [pulled] using hy
  · rw [equivalence.num_edges_eq]
    exact hxy

/-- Connectivity is unchanged by a Laplacian-preserving relabeling. -/
theorem graphConnected_iff (equivalence : LaplacianEquiv G H) :
    _root_.graphConnected G ↔ _root_.graphConnected H :=
  ⟨equivalence.graphConnected, equivalence.symm.graphConnected⟩

/-- Brill--Noether existence is unchanged by an adjacency-preserving vertex
equivalence.  The proof transports only the requested rank lower bound; it
does not require a general equality theorem for ranks. -/
theorem bnExists_iff (equivalence : LaplacianEquiv G H)
    (r d : ℤ) :
    BNExists G r d ↔ BNExists H r d := by
  constructor
  · rintro ⟨D, hDegree, hRank⟩
    refine ⟨equivalence.mapDiv D, ?_, ?_⟩
    · simpa using hDegree
    · exact (equivalence.rank_mapDiv_ge_iff D r).2 hRank
  · rintro ⟨D, hDegree, hRank⟩
    let D' : CFDiv G := equivalence.symm.mapDiv D
    refine ⟨D', ?_, ?_⟩
    · simpa [D'] using hDegree
    · have h' := (equivalence.symm.rank_mapDiv_ge_iff D r).2 hRank
      simpa [D'] using h'

end LaplacianEquiv

/-! ## A closed parallel-edge relabeling example -/

namespace LaplacianEquiv.Examples

/-- Vertex labels for the closed two-vertex example. -/
abbrev PairVertex := Fin 2

/-- Two vertices joined by two parallel edges. -/
def parallelPair : CFGraph where
  V := PairVertex
  edges := Multiset.ofList [(0, 1), (0, 1)]
  loopless := by decide

/-- The same parallel pair with both endpoint labels exchanged. -/
def relabeledParallelPair : CFGraph where
  V := PairVertex
  edges := Multiset.ofList [(1, 0), (1, 0)]
  loopless := by decide

/-- Swapping the two labels preserves every Laplacian entry, including the
off-diagonal multiplicity two. -/
def parallelPairEquiv : LaplacianEquiv parallelPair relabeledParallelPair where
  toEquiv := Equiv.swap (0 : PairVertex) (1 : PairVertex)
  num_edges_eq := by decide

theorem parallelPair_multiplicity_relabeling :
    numEdges parallelPair (0 : PairVertex) (1 : PairVertex) = 2 ∧
      numEdges relabeledParallelPair (parallelPairEquiv (0 : PairVertex))
        (parallelPairEquiv (1 : PairVertex)) = 2 := by
  decide

end LaplacianEquiv.Examples

end Utilities.Certificate
