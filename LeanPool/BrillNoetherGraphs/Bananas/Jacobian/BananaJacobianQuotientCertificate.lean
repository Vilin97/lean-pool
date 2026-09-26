/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Jacobian.BananaJacobianLatticeReduction

/-!
# Quotient certificates for the displayed banana relation lattice

This module packages the arithmetic invariant used by the reduction
algorithm in Proposition 2.14.  After a common diagonal shift, suppose each
coordinate is written as a valid strand position plus an integral multiple
of that strand's length.  If the length quotients sum to zero, the original
vector and the position vector differ by an explicit combination of the
paper's displayed relation generators.
-/

@[expose] public section

namespace Bananas

open Utilities
open scoped BigOperators

private theorem strandLengthRelation_apply_zero {g : ℕ} (B : Banana g)
    (beta : Fin (g + 1)) (hBeta : beta ≠ 0) :
    bananaStrandLengthRelation B beta 0 = B.length 0 := by
  simp [bananaStrandLengthRelation, bananaCoordinateBasis, hBeta.symm]

private theorem strandLengthRelation_apply_self {g : ℕ} (B : Banana g)
    (alpha : Fin (g + 1)) (hAlpha : alpha ≠ 0) :
    bananaStrandLengthRelation B alpha alpha = -B.length alpha := by
  simp [bananaStrandLengthRelation, bananaCoordinateBasis, hAlpha]

private theorem strandLengthRelation_apply_other {g : ℕ} (B : Banana g)
    (alpha beta : Fin (g + 1)) (hAlpha : alpha ≠ 0)
    (hBeta : beta ≠ alpha) :
    bananaStrandLengthRelation B beta alpha = 0 := by
  simp [bananaStrandLengthRelation, bananaCoordinateBasis,
    hAlpha, hBeta.symm]

/-- Arithmetic certificate for membership in the displayed lattice.  The
integers `q_alpha` record how many strand lengths were removed after a common
diagonal shift `c`; their sum-zero condition is exactly what makes the
strand-zero coordinate agree with the other displayed generators. -/
theorem sub_positionCoordinates_mem_displayedRelations_of_quotients
    {g : ℕ} (B : Banana g) (a : Fin (g + 1) → ℤ)
    (p : ∀ alpha : Fin (g + 1), B.PathPosition alpha)
    (c : ℤ) (q : Fin (g + 1) → ℤ)
    (hCoordinates : ∀ alpha,
      a alpha + c = (p alpha).val + B.length alpha * q alpha)
    (hSum : ∑ alpha : Fin (g + 1), q alpha = 0) :
    a - bananaPositionCoordinates B p ∈ bananaDisplayedRelations B := by
  let nonzero : Finset (Fin (g + 1)) :=
    Finset.univ.erase (0 : Fin (g + 1))
  let combination : Fin (g + 1) → ℤ :=
    (-c) • bananaDiagonalRelation -
      ∑ beta ∈ nonzero, q beta • bananaStrandLengthRelation B beta
  have hCombinationMem : combination ∈ bananaDisplayedRelations B := by
    apply (bananaDisplayedRelations B).sub_mem
    · exact (bananaDisplayedRelations B).zsmul_mem
        (bananaDiagonalRelation_mem_displayedRelations B) (-c)
    · apply (bananaDisplayedRelations B).sum_mem
      intro beta _
      exact (bananaDisplayedRelations B).zsmul_mem
        (bananaStrandLengthRelation_mem_displayedRelations B beta) (q beta)
  have hSumNonzero : ∑ beta ∈ nonzero, q beta = -q 0 := by
    have hSplit := Finset.sum_erase_add (Finset.univ : Finset (Fin (g + 1)))
      q (Finset.mem_univ (0 : Fin (g + 1)))
    change (∑ beta ∈ nonzero, q beta) + q 0 =
      ∑ beta : Fin (g + 1), q beta at hSplit
    rw [hSum] at hSplit
    omega
  have hCombination : a - bananaPositionCoordinates B p = combination := by
    funext alpha
    have hAlpha := hCoordinates alpha
    by_cases hAlphaZero : alpha = 0
    · subst alpha
      have hEval :
          (∑ beta ∈ nonzero,
            q beta • bananaStrandLengthRelation B beta) 0 =
            (B.length 0 : ℤ) * (∑ beta ∈ nonzero, q beta) := by
        rw [Finset.sum_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro beta hBeta
        have hBetaZero : beta ≠ 0 := by
          exact Finset.ne_of_mem_erase hBeta
        rw [Pi.smul_apply, strandLengthRelation_apply_zero B beta hBetaZero]
        ring
      change a 0 - (p 0 : ℤ) = combination 0
      rw [show combination 0 =
          -c - (∑ beta ∈ nonzero,
            q beta • bananaStrandLengthRelation B beta) 0 by
        simp [combination, bananaDiagonalRelation]]
      rw [hEval, hSumNonzero]
      linear_combination hAlpha
    · have hAlphaMem : alpha ∈ nonzero := by
        simp [nonzero, hAlphaZero]
      have hEval :
          (∑ beta ∈ nonzero,
            q beta • bananaStrandLengthRelation B beta) alpha =
            q alpha * (-(B.length alpha : ℤ)) := by
        rw [Finset.sum_apply, Finset.sum_eq_single alpha]
        · rw [Pi.smul_apply,
            strandLengthRelation_apply_self B alpha hAlphaZero]
          simp
        · intro beta hBetaMem hBetaNe
          rw [Pi.smul_apply,
            strandLengthRelation_apply_other B alpha beta hAlphaZero hBetaNe]
          simp
        · exact fun hNot => (hNot hAlphaMem).elim
      change a alpha - (p alpha : ℤ) = combination alpha
      rw [show combination alpha =
          -c - (∑ beta ∈ nonzero,
            q beta • bananaStrandLengthRelation B beta) alpha by
        simp [combination, bananaDiagonalRelation]]
      rw [hEval]
      linear_combination hAlpha
  rw [hCombination]
  exact hCombinationMem

end Bananas
