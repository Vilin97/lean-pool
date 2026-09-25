/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Iso.GraphContractionTopology
public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.InducedSubgraph
public import Mathlib.Tactic

/-!
# Euler accounting for topological graph contractions

`GraphContractionCertificate.Valid` fixes precisely the edges joining
different vertex fibres.  This file packages the resulting Euler accounting.
It is intentionally phrased using *directed multiplicities*, because that is
the representation-independent quantity supplied by `numEdges`.

In particular, an equal-genus valid contraction has exactly the amount of
internal directed multiplicity forced by its loss of vertices.  Together with
connected fibres, the remaining graph-theoretic input for saying that every
fibre is a tree is the usual connected-graph lower bound on its internal edge
count.  Keeping this boundary explicit avoids silently treating arbitrary
quotients as rank-preserving contractions.
-/

@[expose] public section

namespace Utilities.Certificate

open Finset

universe u v

namespace GraphContractionCertificate

variable {G : CFGraph.{u}} {H : CFGraph.{v}}

/-- The total directed multiplicity of source edges which stay inside one
vertex fibre. -/
def internalDirectedMultiplicity (c : GraphContractionCertificate G H) : ℤ :=
  ∑ x : G.V, ∑ y : G.V,
    if c.vertexMap x = c.vertexMap y then (numEdges G x y : ℤ) else 0

/-- The total directed multiplicity of source edges which join two distinct
vertex fibres. -/
def externalDirectedMultiplicity (c : GraphContractionCertificate G H) : ℤ :=
  ∑ x : G.V, ∑ y : G.V,
    if c.vertexMap x ≠ c.vertexMap y then (numEdges G x y : ℤ) else 0

/-- The vertices in one contraction fibre. -/
def fibreVertices (c : GraphContractionCertificate G H) (target : H.V) :
    Finset G.V :=
  Finset.univ.filter fun x => c.vertexMap x = target

theorem fibreVertices_nonempty (c : GraphContractionCertificate G H)
    (hValid : c.Valid) (target : H.V) : (c.fibreVertices target).Nonempty := by
  obtain ⟨x, hx⟩ := hValid.1 target
  exact ⟨x, by simp [fibreVertices, hx]⟩

/-- The actual induced graph carried by a contraction fibre. -/
noncomputable def fibreGraph (c : GraphContractionCertificate G H)
    (hValid : c.Valid) (target : H.V) : CFGraph :=
  inducedSubgraph G (c.fibreVertices target) (c.fibreVertices_nonempty hValid target)

/-- The finite-cut connected-fibre condition is precisely enough to make each
induced fibre graph connected. -/
theorem inducedFibre_connected (c : GraphContractionCertificate G H)
    (hValid : c.Valid) (hFibres : c.ConnectedFibres) (target : H.V) :
    _root_.graphConnected (inducedSubgraph G (c.fibreVertices target)
      (c.fibreVertices_nonempty hValid target)) := by
  classical
  intro S hSplit
  let fibreNonempty := c.fibreVertices_nonempty hValid target
  let T : Finset G.V := S.image
    (inducedSubgraphInclusion G (c.fibreVertices target) fibreNonempty)
  obtain ⟨inside, outside, hInside, hOutside⟩ := hSplit
  have hAmbientSplit : ∃ inside outside : G.V,
      inside ∈ T ∧ outside ∉ T ∧
        c.vertexMap inside = target ∧ c.vertexMap outside = target := by
    refine ⟨inside.val, outside.val, ?_, ?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨inside, hInside, rfl⟩
    · intro hMem
      obtain ⟨outside', hOutside', hEq⟩ := Finset.mem_image.mp hMem
      apply hOutside
      have hCastEq : outside' = outside := by
        apply Subtype.ext
        exact hEq
      simpa [hCastEq] using hOutside'
    · have hInsideFibre := inside.property
      change inside.val ∈ c.fibreVertices target at hInsideFibre
      exact (Finset.mem_filter.mp hInsideFibre).2
    · have hOutsideFibre := outside.property
      change outside.val ∈ c.fibreVertices target at hOutsideFibre
      exact (Finset.mem_filter.mp hOutsideFibre).2
  obtain ⟨inside', hInside', outside', hOutside', hInsideMap, hOutsideMap, hEdge⟩ :=
    hFibres target T hAmbientSplit
  let insideSub : (inducedSubgraph G (c.fibreVertices target)
    fibreNonempty).V :=
    ⟨inside', by simp [fibreVertices, hInsideMap]⟩
  let outsideSub : (inducedSubgraph G (c.fibreVertices target)
    fibreNonempty).V :=
    ⟨outside', by simp [fibreVertices, hOutsideMap]⟩
  refine ⟨insideSub, ?_, outsideSub, ?_, ?_⟩
  · obtain ⟨inside'', hInside'', hEq⟩ := Finset.mem_image.mp hInside'
    have hSubtypeEq : inside'' = insideSub := by
      apply Subtype.ext
      exact hEq
    simpa [hSubtypeEq] using hInside''
  · intro hMem
    apply hOutside'
    exact Finset.mem_image.mpr ⟨outsideSub, hMem, rfl⟩
  · simpa [insideSub, outsideSub] using hEdge

theorem fibreGraph_connected (c : GraphContractionCertificate G H)
    (hValid : c.Valid) (hFibres : c.ConnectedFibres) (target : H.V) :
    _root_.graphConnected (c.fibreGraph hValid target) := by
  simpa [fibreGraph] using c.inducedFibre_connected hValid hFibres target

/-- Convenience form of fibre connectedness for a topological contraction. -/
theorem fibreGraph_connected_of_topologicalValid
    (c : GraphContractionCertificate G H) (hTopological : c.TopologicalValid)
    (target : H.V) :
    _root_.graphConnected (c.fibreGraph hTopological.1 target) :=
  c.fibreGraph_connected hTopological.1 hTopological.2 target

/-- Partition a finite sum by the value of the contraction map. -/
private theorem sum_by_vertexMap (c : GraphContractionCertificate G H)
    (f : G.V → ℤ) :
    (∑ x : G.V, f x) =
      ∑ a : H.V, ∑ x : G.V, if c.vertexMap x = a then f x else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

/-- Partition a double sum by the ordered pair of fibre labels. -/
private theorem sum_by_vertexMap_pair (c : GraphContractionCertificate G H)
    (f : G.V → G.V → ℤ) :
    (∑ x : G.V, ∑ y : G.V, f x y) =
      ∑ a : H.V, ∑ b : H.V, ∑ x : G.V, ∑ y : G.V,
        if c.vertexMap x = a ∧ c.vertexMap y = b then f x y else 0 := by
  calc
    (∑ x : G.V, ∑ y : G.V, f x y) =
        ∑ a : H.V, ∑ x : G.V,
          if c.vertexMap x = a then (∑ y : G.V, f x y) else 0 := by
      exact c.sum_by_vertexMap (fun x => ∑ y : G.V, f x y)
    _ = ∑ a : H.V, ∑ x : G.V, ∑ b : H.V, ∑ y : G.V,
          if c.vertexMap x = a then
            if c.vertexMap y = b then f x y else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro x _
      by_cases hxa : c.vertexMap x = a
      · simp only [hxa, if_true]
        exact c.sum_by_vertexMap (fun y => f x y)
      · simp [hxa]
    _ = ∑ a : H.V, ∑ b : H.V, ∑ x : G.V, ∑ y : G.V,
          if c.vertexMap x = a then
            if c.vertexMap y = b then f x y else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ a : H.V, ∑ b : H.V, ∑ x : G.V, ∑ y : G.V,
          if c.vertexMap x = a ∧ c.vertexMap y = b then f x y else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      by_cases hx : c.vertexMap x = a <;>
        by_cases hy : c.vertexMap y = b <;> simp [hx, hy]

/-- The source directed multiplicity partitions into internal and external
fibre contributions. -/
theorem internal_add_external_eq_total (c : GraphContractionCertificate G H) :
    c.internalDirectedMultiplicity + c.externalDirectedMultiplicity =
      ∑ x : G.V, vertexDegree G x := by
  rw [internalDirectedMultiplicity, externalDirectedMultiplicity]
  simp only [vertexDegree]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : c.vertexMap x = c.vertexMap y <;> simp [hxy]

/-- The off-fibre directed multiplicity is exactly the degree sum of the
quotient graph. -/
theorem externalDirectedMultiplicity_eq_degreeSum
    (c : GraphContractionCertificate G H) (hValid : c.Valid) :
    c.externalDirectedMultiplicity = ∑ a : H.V, vertexDegree H a := by
  rw [externalDirectedMultiplicity]
  calc
    (∑ x : G.V, ∑ y : G.V,
        if c.vertexMap x ≠ c.vertexMap y then (numEdges G x y : ℤ) else 0) =
      ∑ a : H.V, ∑ b : H.V, ∑ x : G.V, ∑ y : G.V,
        if c.vertexMap x = a ∧ c.vertexMap y = b then
          if a ≠ b then (numEdges G x y : ℤ) else 0 else 0 := by
      rw [c.sum_by_vertexMap_pair]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      by_cases hab : a = b
      · subst b
        by_cases hxa : c.vertexMap x = a <;>
          by_cases hyb : c.vertexMap y = a <;> simp [hxa, hyb]
      · by_cases hxa : c.vertexMap x = a <;>
          by_cases hyb : c.vertexMap y = b <;> simp [hxa, hyb, hab]
    _ = ∑ a : H.V, ∑ b : H.V, (numEdges H a b : ℤ) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases hab : a = b
      · subst b
        simp
      · have hq := hValid.2 a b hab
        have hqInt :
            (∑ x : G.V, ∑ y : G.V,
              if c.vertexMap x = a ∧ c.vertexMap y = b then
                (numEdges G x y : ℤ) else 0) =
              (numEdges H a b : ℤ) := by
          exact_mod_cast hq.symm
        simpa [hab] using hqInt
    _ = ∑ a : H.V, vertexDegree H a := by
      simp only [vertexDegree]

/-- Euler accounting in directed form.  The contracted internal multiplicity
is twice the loss of edge occurrences. -/
theorem internalDirectedMultiplicity_eq_two_mul_edgeLoss
    (c : GraphContractionCertificate G H) (hValid : c.Valid) :
    c.internalDirectedMultiplicity =
      2 * ((G.edges.card : ℤ) - H.edges.card) := by
  have hPartition := c.internal_add_external_eq_total
  rw [c.externalDirectedMultiplicity_eq_degreeSum hValid,
    sum_vertex_degree_eq_twice_card_edges,
    sum_vertex_degree_eq_twice_card_edges] at hPartition
  omega

/-- If a valid contraction has equal cyclomatic genus, its internal directed
multiplicity is exactly twice the number of vertices removed.  This is the
Euler identity underlying the assertion that connected fibres must be trees. -/
theorem internalDirectedMultiplicity_eq_two_mul_vertexLoss_of_genus_eq
    (c : GraphContractionCertificate G H) (hValid : c.Valid)
    (hGenus : genus G = genus H) :
    c.internalDirectedMultiplicity =
      2 * ((Fintype.card G.V : ℤ) - Fintype.card H.V) := by
  rw [c.internalDirectedMultiplicity_eq_two_mul_edgeLoss hValid]
  simp only [genus] at hGenus
  omega

end GraphContractionCertificate

end Utilities.Certificate
