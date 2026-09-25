/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffFiniteCountSol
import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffShortStrandPeriod

/-!
# Corrected both-off inversion lower bound

This is the graph-level assembly of the finite row injection and its exact
arithmetic count.  It is Corollary 4.31 with the corrected row block and its
explicit period-separation hypothesis.
-/

namespace Bananas

open Utilities

/-- Verified form of Corollary 4.31, conditional on the required period separation.

`correctedCrossOneOffForcedCount` treats a second strand of length two
separately, using `choose g 2` in that case and
`choose (g - 1) 2 + g / (n - 1)` otherwise. -/
theorem crossOneOff_corrected_inversion_lower_bound
    {g k : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (tau : ℤ → ℤ)
    (hg : 2 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha) (hBeta : 1 < B.length beta)
    (hLong : CrossOneOffLongEnough
      g (B.length alpha) (B.length beta))
    (hTau : IsTransmissionPermutation
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩))
      (g • oneChip (rightEndpoint B)) tau)
    (hSeparate : crossOneOffCutoff g (B.length beta) ≤ k)
    (hfinite : (kInversions k tau).Finite) :
    correctedCrossOneOffForcedCount g (B.length beta) ≤
      kInversionCount k tau := by
  apply crossOneOff_corrected_inversion_lower_bound_of_finiteRows
    B alpha beta tau hg hab hAlpha hBeta hLong hTau hSeparate hfinite
  exact correctedCrossOneOffForcedCount_le_card hg (by omega)

/-- Unconditional form of corrected Corollary 4.31: the period-separation
hypothesis `hSeparate` is now supplied internally from the exact torsion
order via `crossOneOff_cutoff_le_torsionOrder_of_not_both_two`
(`Bananas/CrossOneOffShortStrandPeriod.lean`), since `CrossOneOffLongEnough`
already forces `B.length alpha ≥ g + 1 ≥ 4 > 2`, so the two marked strand
lengths can never both be `2`. -/
theorem crossOneOff_corrected_inversion_lower_bound_of_not_both_two
    {g k : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (tau : ℤ → ℤ)
    (hg : 3 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha) (hBeta : 1 < B.length beta)
    (hLong : CrossOneOffLongEnough
      g (B.length alpha) (B.length beta))
    (hTau : IsTransmissionPermutation
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩))
      (g • oneChip (rightEndpoint B)) tau)
    (hTO : IsTorsionOrder
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩)) k)
    (hfinite : (kInversions k tau).Finite) :
    correctedCrossOneOffForcedCount g (B.length beta) ≤
      kInversionCount k tau := by
  have hAlphaLong : g + 1 ≤ B.length alpha := by
    have h : g + 1 + g / (B.length beta - 1) ≤ B.length alpha := hLong
    exact le_trans (Nat.le_add_right _ _) h
  have hNotBoth : ¬ (B.length alpha = 2 ∧ B.length beta = 2) := by
    rintro ⟨h2, -⟩
    rw [h2] at hAlphaLong
    omega
  have hSeparate : crossOneOffCutoff g (B.length beta) ≤ k :=
    crossOneOff_cutoff_le_torsionOrder_of_not_both_two
      B alpha beta hg hab hAlpha hBeta hNotBoth hTO
  exact crossOneOff_corrected_inversion_lower_bound
    B alpha beta tau (by omega) hab hAlpha hBeta hLong hTau hSeparate hfinite

end Bananas
