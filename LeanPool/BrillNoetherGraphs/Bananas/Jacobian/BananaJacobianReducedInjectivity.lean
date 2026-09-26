/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Jacobian.BananaJacobianPresentation
public import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.Semibreak

/-!
# A reduced-coordinate injectivity criterion for banana Jacobians

The paper represents a coordinate `p_alpha` by the divisor
`[v_{alpha,p_alpha}] - [left]`.  This file isolates the Jacobian argument from
the remaining combinatorics of the paper's chosen fundamental domain: if the
resulting divisor is reduced at the left endpoint, then it represents zero
only when every coordinate is zero.

The missing step for the full injectivity half of Proposition 2.14 is now the
concrete reducedness theorem: the paper's three conditions on the coordinates
must be converted into the endpoint/semibreak normal form of `Semibreak.lean`.
-/

@[expose] public section

namespace Bananas

open Utilities
open scoped BigOperators
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-- The divisor attached in Proposition 2.14 to coordinates represented by
positions on their respective strands. -/
def bananaPositionCoordinateDivisor {g : ℕ} (B : Banana g)
    (p : ∀ alpha : Fin (g + 1), B.PathPosition alpha) : CFDiv B.graph :=
  ∑ alpha : Fin (g + 1),
    (oneChip (strandVertex B alpha (p alpha)) - oneChip (leftEndpoint B))

/-- Regard a vector of strand positions as the corresponding nonnegative
integer coordinate vector. -/
def bananaPositionCoordinates {g : ℕ} (B : Banana g)
    (p : ∀ alpha : Fin (g + 1), B.PathPosition alpha) :
    Fin (g + 1) → ℤ :=
  fun alpha => p alpha

/-- The paper's three conditions for its preferred coordinate representatives.
The bounds `0 ≤ a_alpha ≤ n_alpha` are built into `PathPosition`; the two
remaining clauses are recorded literally. -/
def IsPaperReducedPositionCoordinates {g : ℕ} (B : Banana g)
    (p : ∀ alpha : Fin (g + 1), B.PathPosition alpha) : Prop :=
  (∃ alpha, (p alpha).val = 0) ∧
    ∀ alpha beta, (p alpha).val = B.length alpha →
      (p beta).val = 0 → alpha < beta

section Generic

private theorem linearEquiv_sum {G : CFGraph} {ι : Type*} [Fintype ι]
    {D E : ι → CFDiv G} (h : ∀ i, linearEquiv G (D i) (E i)) :
    linearEquiv G (∑ i, D i) (∑ i, E i) := by
  classical
  unfold linearEquiv at h ⊢
  rw [← Finset.sum_sub_distrib]
  exact (principalDivisors G).sum_mem (fun i _ => h i)

end Generic

/-- The position-coordinate divisor is the prefix-fired representative of
the coordinate homomorphism. -/
theorem bananaCoordinateDivisorHom_linearEquiv_positionDivisor {g : ℕ}
    (B : Banana g) (p : ∀ alpha : Fin (g + 1), B.PathPosition alpha) :
    linearEquiv B.graph
      (bananaCoordinateDivisorHom B (bananaPositionCoordinates B p))
      (bananaPositionCoordinateDivisor B p) := by
  unfold bananaCoordinateDivisorHom bananaPositionCoordinates
    bananaPositionCoordinateDivisor
  exact linearEquiv_sum fun alpha => by
    simpa [bananaCoordinateStep] using
      strand_prefix_linearEquiv B alpha (p alpha)

private theorem zero_isSemibreak {g : ℕ} (B : Banana g) :
    IsSemibreak B 0 := by
  let chips : ∀ gamma : Fin (g + 1), Option (Fin (B.length gamma - 1)) :=
    fun _ => none
  refine ⟨chips, ?_⟩
  funext z
  rcases z with core | ⟨gamma, offset⟩
  · rfl
  · simp [semibreakDivisor, chips]

private theorem zero_q_reduced_at_left {g : ℕ} (B : Banana g) :
    qReduced B.graph (leftEndpoint B) 0 := by
  have h := q_reduced_bananaNormalForm B 0 0 0 (zero_isSemibreak B)
    (by omega) (by simp)
  simpa [bananaNormalForm] using h

/-- A position-coordinate representative that is reduced at the left
endpoint lies in the kernel of the coordinate class map only when all of its
coordinates are zero.

This is the q-reduced uniqueness core of the injectivity argument in
Proposition 2.14.  The hypothesis `hReduced` is exactly the remaining bridge
from the paper's elementary fundamental-domain inequalities to the formal
semibreak API. -/
theorem bananaPositionCoordinates_eq_zero_of_qReduced_of_mem_relations
    {g : ℕ} (B : Banana g)
    (p : ∀ alpha : Fin (g + 1), B.PathPosition alpha)
    (hReduced : qReduced B.graph (leftEndpoint B)
      (bananaPositionCoordinateDivisor B p))
    (hKernel : bananaPositionCoordinates B p ∈ bananaCoordinateRelations B) :
    bananaPositionCoordinates B p = 0 := by
  have hPrefix :=
    bananaCoordinateDivisorHom_linearEquiv_positionDivisor B p
  have hCoordinateZero : linearEquiv B.graph
      (bananaCoordinateDivisorHom B (bananaPositionCoordinates B p)) 0 := by
    rw [bananaCoordinateRelations, AddMonoidHom.mem_ker] at hKernel
    have hPrincipal :
        bananaCoordinateDivisorHom B (bananaPositionCoordinates B p) ∈
          principalDivisors B.graph := by
      exact (QuotientAddGroup.eq_zero_iff _).mp hKernel
    unfold linearEquiv
    simpa using (principalDivisors B.graph).neg_mem hPrincipal
  have hPositionZero : bananaPositionCoordinateDivisor B p = 0 :=
    q_reduced_unique B.graph (leftEndpoint B)
      (bananaPositionCoordinateDivisor B p) 0
      ⟨hReduced, zero_q_reduced_at_left B,
        hPrefix.symm.trans hCoordinateZero⟩
  funext alpha
  have hLeft := congrFun hPositionZero (leftEndpoint B)
  simp only [Pi.zero_apply] at hLeft
  have hTerm : ∀ beta : Fin (g + 1),
      (oneChip (strandVertex B beta (p beta)) -
          oneChip (leftEndpoint B)) (leftEndpoint B) =
        if (p beta).val = 0 then 0 else (-1 : ℤ) := by
    intro beta
    by_cases hpZero : (p beta).val = 0
    · have hp : p beta = ⟨0, by omega⟩ := Fin.ext hpZero
      rw [hp, strandVertex_zero]
      simp
    · have hpPos : 0 < (p beta).val := Nat.pos_of_ne_zero hpZero
      have hVertex := strandVertex_ne_leftEndpoint B beta (p beta) hpPos
      simp [oneChip, hpZero, hVertex.symm]
  unfold bananaPositionCoordinateDivisor at hLeft
  rw [Finset.sum_apply] at hLeft
  change (∑ beta : Fin (g + 1),
      (oneChip (strandVertex B beta (p beta)) -
        oneChip (leftEndpoint B)) (leftEndpoint B)) = 0 at hLeft
  rw [Finset.sum_congr rfl (fun beta _ => hTerm beta)] at hLeft
  have hEach := (Finset.sum_eq_zero_iff_of_nonpos (s := Finset.univ)
    (f := fun beta : Fin (g + 1) =>
      if (p beta).val = 0 then (0 : ℤ) else -1)
    (by intro beta _; split <;> omega)).mp hLeft
  have hAlpha := hEach alpha (Finset.mem_univ alpha)
  have hpVal : (p alpha).val = 0 := by
    by_contra hpZero
    rw [ite_eq_right hpZero] at hAlpha
    omega
  simp [bananaPositionCoordinates, hpVal]

end Bananas
