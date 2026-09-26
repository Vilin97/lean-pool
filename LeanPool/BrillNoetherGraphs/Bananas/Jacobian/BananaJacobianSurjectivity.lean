/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Jacobian.BananaJacobianDiagonal

/-!
# Surjectivity of the banana coordinate map in degree zero

This file proves the surjectivity half of the graph-level Jacobian
presentation in Proposition 2.14.  Every vertex difference from the left
endpoint is represented by a multiple of one strand coordinate.  Expanding a
degree-zero divisor as a sum of these differences then gives a coordinate
vector whose image is linearly equivalent to that divisor.
-/

@[expose] public section

namespace Bananas

open Utilities
open scoped BigOperators
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

section Generic

private theorem linearEquiv_zsmul {G : CFGraph} {D E : CFDiv G}
    (h : linearEquiv G D E) (n : ℤ) :
    linearEquiv G (n • D) (n • E) := by
  unfold linearEquiv at h ⊢
  simpa [smul_sub] using (principalDivisors G).zsmul_mem h n

private theorem linearEquiv_sum {G : CFGraph} {ι : Type*} [Fintype ι]
    {D E : ι → CFDiv G} (h : ∀ i, linearEquiv G (D i) (E i)) :
    linearEquiv G (∑ i, D i) (∑ i, E i) := by
  classical
  unfold linearEquiv at h ⊢
  rw [← Finset.sum_sub_distrib]
  exact (principalDivisors G).sum_mem (fun i _ => h i)

/-- Every divisor is the sum of its coefficients times the corresponding
one-chip divisors. -/
private theorem divisor_eq_sum_smul_oneChip {G : CFGraph} (D : CFDiv G) :
    D = ∑ v : G.V, D v • oneChip v := by
  classical
  funext w
  simp [oneChip]

/-- A degree-zero divisor is the sum of its coefficient-weighted vertex
differences from any chosen basepoint. -/
private theorem sum_smul_vertexDifference_eq_of_degree_zero {G : CFGraph}
    (q : G.V) (D : CFDiv G) (hDegree : deg D = 0) :
    (∑ v : G.V, D v • (oneChip v - oneChip q)) = D := by
  rw [Finset.sum_congr rfl (fun v _ => smul_sub (D v) (oneChip v) (oneChip q))]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.sum_smul]
  rw [show ∑ v : G.V, D v = 0 by exact hDegree]
  rw [zero_smul, sub_zero]
  exact (divisor_eq_sum_smul_oneChip D).symm

end Generic

/-- Every difference between a banana vertex and the left endpoint is
represented by a strand-coordinate vector. -/
theorem exists_bananaCoordinate_linearEquiv_vertexDifference
    {g : ℕ} (B : Banana g) (v : B.graph.V) :
    ∃ a : Fin (g + 1) → ℤ,
      linearEquiv B.graph (bananaCoordinateDivisorHom B a)
        (oneChip v - oneChip (leftEndpoint B)) := by
  classical
  rcases v with core | ⟨alpha, offset⟩
  · rcases fin_two_eq_zero_or_one core with rfl | rfl
    · refine ⟨0, ?_⟩
      rw [map_zero]
      change linearEquiv B.graph 0
        (oneChip (leftEndpoint B) - oneChip (leftEndpoint B))
      simp [linearEquiv]
    · refine ⟨(B.length (0 : Fin (g + 1)) : ℤ) •
          bananaCoordinateBasis (0 : Fin (g + 1)), ?_⟩
      rw [AddMonoidHom.map_zsmul, bananaCoordinateDivisorHom_basis]
      exact bananaCoordinateStep_length_linearEquiv_endpointDifference B 0
  · obtain ⟨p, hp, hpVertex⟩ :=
      exists_interior_strandVertex B alpha offset
    refine ⟨(p.val : ℤ) • bananaCoordinateBasis alpha, ?_⟩
    rw [AddMonoidHom.map_zsmul, bananaCoordinateDivisorHom_basis]
    change linearEquiv B.graph ((p.val : ℤ) • bananaCoordinateStep B alpha)
      (oneChip (B.interiorVertex alpha offset) - oneChip (leftEndpoint B))
    rw [← hpVertex]
    simpa [bananaCoordinateStep] using strand_prefix_linearEquiv B alpha p

/-- Graph-level surjectivity onto the degree-zero component: every
degree-zero divisor class has a representative in the image of the banana
coordinate map.  This is the surjectivity half of Proposition 2.14 before
packaging the codomain as a degree-zero subgroup of the divisor-class
quotient. -/
theorem exists_bananaCoordinate_linearEquiv_of_degree_zero
    {g : ℕ} (B : Banana g) (D : CFDiv B.graph) (hDegree : deg D = 0) :
    ∃ a : Fin (g + 1) → ℤ,
      linearEquiv B.graph (bananaCoordinateDivisorHom B a) D := by
  classical
  choose coordinate hCoordinate using
    fun v : B.graph.V => exists_bananaCoordinate_linearEquiv_vertexDifference B v
  let a : Fin (g + 1) → ℤ :=
    ∑ v : B.graph.V, D v • coordinate v
  refine ⟨a, ?_⟩
  have hScaled : ∀ v : B.graph.V,
      linearEquiv B.graph
        (D v • bananaCoordinateDivisorHom B (coordinate v))
        (D v • (oneChip v - oneChip (leftEndpoint B))) := by
    intro v
    exact linearEquiv_zsmul (hCoordinate v) (D v)
  have hSum := linearEquiv_sum hScaled
  have hMap : bananaCoordinateDivisorHom B a =
      ∑ v : B.graph.V, D v • bananaCoordinateDivisorHom B (coordinate v) := by
    dsimp [a]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [AddMonoidHom.map_zsmul]
  rw [← hMap,
    sum_smul_vertexDifference_eq_of_degree_zero (leftEndpoint B) D hDegree] at hSum
  exact hSum

end Bananas
