/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaPrefix

/-!
# The coordinate map in the banana Jacobian presentation

This is the graph-level map used in Proposition 2.14 of the paper.  A
coordinate vector sends its `alpha`th coordinate to the same multiple of the
first normalized step on strand `alpha`, based at the left endpoint.

The file also supplies the exact quotient by the kernel of the induced map to
divisor classes, and verifies the paper's strand-length relation generators.
The remaining displayed generator `(1, ..., 1)` is the normalized
first-neighbor form of firing the left endpoint; that finite Laplacian identity
is kept separate from the pairwise path-prefix calculation below.
-/

namespace Bananas

open Utilities
open scoped BigOperators
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-- The degree-zero divisor representing one unit of the `alpha`th coordinate
in the paper's presentation. -/
def bananaCoordinateStep {g : ℕ} (B : Banana g) (alpha : Fin (g + 1)) :
    CFDiv B.graph :=
  oneChip (strandVertex B alpha ⟨1, by
    have := B.length_pos alpha
    omega⟩) - oneChip (leftEndpoint B)

/-- The free coordinate-vector map `tphi` in the proof of Proposition 2.14. -/
def bananaCoordinateDivisorHom {g : ℕ} (B : Banana g) :
    (Fin (g + 1) → ℤ) →+ CFDiv B.graph where
  toFun a := ∑ alpha : Fin (g + 1), a alpha • bananaCoordinateStep B alpha
  map_zero' := by simp
  map_add' a b := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- Every coordinate vector maps to a divisor of degree zero. -/
@[simp] theorem degree_bananaCoordinateDivisorHom {g : ℕ} (B : Banana g)
    (a : Fin (g + 1) → ℤ) :
    deg (bananaCoordinateDivisorHom B a) = 0 := by
  change deg (∑ alpha : Fin (g + 1),
    a alpha • bananaCoordinateStep B alpha) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro alpha _
  rw [AddMonoidHom.map_zsmul]
  simp [bananaCoordinateStep]

/-- The coordinate map followed by passage to divisor classes.  Its codomain
is the additive quotient by principal divisors, i.e. the graph-level Picard
group model used here.  The preceding degree lemma shows that its image lies
in the degree-zero (Jacobian) component. -/
def bananaCoordinateClassHom {g : ℕ} (B : Banana g) :
    (Fin (g + 1) → ℤ) →+
      (CFDiv B.graph ⧸ principalDivisors B.graph) :=
  (QuotientAddGroup.mk' (principalDivisors B.graph)).comp
    (bananaCoordinateDivisorHom B)

/-- The exact relation subgroup of the graph-level coordinate map.  Showing
that this kernel equals the paper's displayed lattice is the injectivity half
of Proposition 2.14. -/
def bananaCoordinateRelations {g : ℕ} (B : Banana g) :
    AddSubgroup (Fin (g + 1) → ℤ) :=
  (bananaCoordinateClassHom B).ker

/-- The canonical map from coordinates modulo their exact graph relations to
divisor classes. -/
def bananaPresentedClassHom {g : ℕ} (B : Banana g) :
    ((Fin (g + 1) → ℤ) ⧸ bananaCoordinateRelations B) →+
      (CFDiv B.graph ⧸ principalDivisors B.graph) :=
  QuotientAddGroup.lift (bananaCoordinateRelations B)
    (bananaCoordinateClassHom B) (by
      intro a ha
      exact ha)

/-- The standard coordinate vector `e_alpha`. -/
def bananaCoordinateBasis {g : ℕ} (alpha : Fin (g + 1)) :
    Fin (g + 1) → ℤ := fun beta => if beta = alpha then 1 else 0

@[simp] theorem bananaCoordinateDivisorHom_basis {g : ℕ} (B : Banana g)
    (alpha : Fin (g + 1)) :
    bananaCoordinateDivisorHom B (bananaCoordinateBasis alpha) =
      bananaCoordinateStep B alpha := by
  classical
  simp [bananaCoordinateDivisorHom, bananaCoordinateBasis]

/-- The displayed relation `n_0 e_0 - n_beta e_beta`. -/
def bananaStrandLengthRelation {g : ℕ} (B : Banana g)
    (beta : Fin (g + 1)) : Fin (g + 1) → ℤ :=
  (B.length 0 : ℤ) • bananaCoordinateBasis (0 : Fin (g + 1)) -
    (B.length beta : ℤ) • bananaCoordinateBasis beta

/-- The other displayed relation vector, `(1, ..., 1)`. -/
def bananaDiagonalRelation {g : ℕ} : Fin (g + 1) → ℤ := fun _ => 1

@[simp] theorem bananaCoordinateDivisorHom_diagonalRelation
    {g : ℕ} (B : Banana g) :
    bananaCoordinateDivisorHom B (bananaDiagonalRelation (g := g)) =
      ∑ alpha : Fin (g + 1), bananaCoordinateStep B alpha := by
  simp [bananaCoordinateDivisorHom, bananaDiagonalRelation]

@[simp] theorem bananaCoordinateDivisorHom_strandLengthRelation
    {g : ℕ} (B : Banana g) (beta : Fin (g + 1)) :
    bananaCoordinateDivisorHom B (bananaStrandLengthRelation B beta) =
      (B.length 0 : ℤ) • bananaCoordinateStep B 0 -
        (B.length beta : ℤ) • bananaCoordinateStep B beta := by
  unfold bananaStrandLengthRelation
  rw [map_sub, AddMonoidHom.map_zsmul, AddMonoidHom.map_zsmul,
    bananaCoordinateDivisorHom_basis, bananaCoordinateDivisorHom_basis]

section Generic

private theorem linearEquiv_sub_pair {G : CFGraph}
    {A B C D : CFDiv G}
    (hAC : linearEquiv G A C) (hBD : linearEquiv G B D) :
    linearEquiv G (A - B) (C - D) := by
  unfold linearEquiv at hAC hBD ⊢
  convert (principalDivisors G).sub_mem hAC hBD using 1
  all_goals abel

end Generic

/-- A full strand length advances the coordinate step from the left endpoint
to the common right endpoint.  This is Equation `eq:multDiff` at `a=n_alpha`.
-/
theorem bananaCoordinateStep_length_linearEquiv_endpointDifference
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1)) :
    linearEquiv B.graph
      ((B.length alpha : ℤ) • bananaCoordinateStep B alpha)
      (oneChip (rightEndpoint B) - oneChip (leftEndpoint B)) := by
  simpa [bananaCoordinateStep, strandVertex_length] using
    strand_prefix_linearEquiv B alpha
      (⟨B.length alpha, by omega⟩ : B.PathPosition alpha)

/-- Every displayed pairwise strand-length relation maps to a principal
divisor. -/
theorem bananaStrandLengthRelation_image_principal {g : ℕ} (B : Banana g)
    (beta : Fin (g + 1)) :
    bananaCoordinateDivisorHom B (bananaStrandLengthRelation B beta) ∈
      principalDivisors B.graph := by
  have h0 := bananaCoordinateStep_length_linearEquiv_endpointDifference B
    (0 : Fin (g + 1))
  have hBeta := bananaCoordinateStep_length_linearEquiv_endpointDifference B beta
  have hDifference := linearEquiv_sub_pair h0 hBeta
  have hZero : linearEquiv B.graph
      ((B.length 0 : ℤ) • bananaCoordinateStep B 0 -
        (B.length beta : ℤ) • bananaCoordinateStep B beta) 0 := by
    simpa using hDifference
  have hNegative :
      0 - ((B.length 0 : ℤ) • bananaCoordinateStep B 0 -
        (B.length beta : ℤ) • bananaCoordinateStep B beta) ∈
          principalDivisors B.graph := hZero
  have hPositive := (principalDivisors B.graph).neg_mem hNegative
  rw [bananaCoordinateDivisorHom_strandLengthRelation]
  convert hPositive using 1
  all_goals abel

/-- Hence the paper's pairwise strand-length generators belong to the exact
relation subgroup of the graph-level class map. -/
theorem bananaStrandLengthRelation_mem_relations {g : ℕ} (B : Banana g)
    (beta : Fin (g + 1)) :
    bananaStrandLengthRelation B beta ∈ bananaCoordinateRelations B := by
  rw [bananaCoordinateRelations, AddMonoidHom.mem_ker]
  apply (QuotientAddGroup.eq_zero_iff _).2
  exact bananaStrandLengthRelation_image_principal B beta


end Bananas
