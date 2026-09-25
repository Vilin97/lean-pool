/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.EndpointBlock
import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.EndpointCardinality
import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.OneOffRefinedInversion
import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffCorrectedInversion
import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffPeriodSeparation

/-!
# Explicit quadratic inversion growth on bananas

This gives the precise formal reading of the quantity `M` in Theorem 4.18:
there is a divisor whose affine transmission permutation has at least the
displayed number of normalized inversion classes.  The paper leaves
"sufficiently long" informal; the three theorems below retain the actual
verified length hypotheses for its endpoint, one-off, and cross-one-off
families.
-/

namespace Bananas

open Utilities

/-- A marked graph has a transmission permutation with at least `q`
normalized `k`-inversion classes.  This is the existential lower-bound form
of the paper's maximum `M`. -/
def HasInversionLowerBound (M : TwiceMarked) (k q : ℕ) : Prop :=
  ∃ D : CFDiv M.graph, ∃ tau : ℤ → ℤ,
    IsTransmissionPermutation M D tau ∧ IsKAffine k tau ∧
      (kInversions k tau).Finite ∧ q ≤ kInversionCount k tau

/-- Endpoint branch of Theorem 4.18 / Proposition 4.21. -/
theorem endpoint_has_quadratic_inversion_lower_bound
    {g k : ℕ} (B : Banana g)
    (hSub : AllSubmodular
      (mark B.graph (leftEndpoint B) (rightEndpoint B)))
    (hTO : IsTorsionOrder
      (mark B.graph (leftEndpoint B) (rightEndpoint B)) k) :
    HasInversionLowerBound
      (mark B.graph (leftEndpoint B) (rightEndpoint B)) k
      (Nat.choose (g + 1) 2) := by
  obtain ⟨tau, hTau, hAffine, hBlock⟩ :=
    exists_endpoint_transmission_block B hSub hTO.1
  let hFinite := kInversions_finite_of_isKAffine hTO.1.1 hAffine
  refine ⟨g • oneChip (rightEndpoint B), tau, hTau, hAffine, hFinite, ?_⟩
  exact endpoint_block_inversion_lower_bound hTO.1.1 hAffine hBlock hFinite

/-- Same-strand one-off branch of Theorem 4.18 / Proposition 4.25. -/
theorem oneOff_has_quadratic_inversion_lower_bound
    {g k : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (hg : 2 ≤ g) (hLength : 1 < B.length alpha)
    (hSub : AllSubmodular (mark B.graph (leftEndpoint B)
      (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩)))
    (hTO : IsTorsionOrder (mark B.graph (leftEndpoint B)
      (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩)) k) :
    HasInversionLowerBound (mark B.graph (leftEndpoint B)
      (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩)) k
      (Nat.choose g 2 + g / (B.length alpha - 1)) := by
  let M := mark B.graph (leftEndpoint B)
    (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩)
  let D : CFDiv B.graph := g • oneChip (rightEndpoint B)
  obtain ⟨tau, hTau, hAffine⟩ :=
    exists_affineTransmissionPermutation_of_submodular M D
      (banana_graph_connected B) (hSub D) hTO.1
  have hFinite := kInversions_finite_of_isKAffine hTO.1.1 hAffine
  refine ⟨D, tau, hTau, hAffine, hFinite, ?_⟩
  exact oneOff_refined_inversion_lower_bound B alpha tau hg hTO.1.1
    hLength hTau hAffine hFinite

/-- Cross-one-off branch of Theorem 4.18 / corrected Corollary 4.31.  The
long-second-strand hypothesis supplies the period separation that the
published proof left implicit. -/
theorem crossOneOff_has_quadratic_inversion_lower_bound
    {g k : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (hg : 3 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha)
    (hBetaLong : g + 1 ≤ B.length beta)
    (hLong : CrossOneOffLongEnough
      g (B.length alpha) (B.length beta))
    (hSub : AllSubmodular (mark B.graph
      (strandVertex B alpha ⟨1, by omega⟩)
      (strandVertex B beta ⟨B.length beta - 1, by omega⟩)))
    (hTO : IsTorsionOrder (mark B.graph
      (strandVertex B alpha ⟨1, by omega⟩)
      (strandVertex B beta ⟨B.length beta - 1, by omega⟩)) k) :
    HasInversionLowerBound (mark B.graph
      (strandVertex B alpha ⟨1, by omega⟩)
      (strandVertex B beta ⟨B.length beta - 1, by omega⟩)) k
      (correctedCrossOneOffForcedCount g (B.length beta)) := by
  let M := mark B.graph
    (strandVertex B alpha ⟨1, by omega⟩)
    (strandVertex B beta ⟨B.length beta - 1, by omega⟩)
  let D : CFDiv B.graph := g • oneChip (rightEndpoint B)
  obtain ⟨tau, hTau, hAffine⟩ :=
    exists_affineTransmissionPermutation_of_submodular M D
      (banana_graph_connected B) (hSub D) hTO.1
  have hFinite := kInversions_finite_of_isKAffine hTO.1.1 hAffine
  have hSeparate : crossOneOffCutoff g (B.length beta) ≤ k :=
    crossOneOff_cutoff_le_torsionOrder B alpha beta hg hab hAlpha hBetaLong hTO
  refine ⟨D, tau, hTau, hAffine, hFinite, ?_⟩
  exact crossOneOff_corrected_inversion_lower_bound B alpha beta tau
    (by omega) hab hAlpha (by omega) hLong hTau hSeparate hFinite

/-- Cross-one-off branch of Theorem 4.18 / corrected Corollary 4.31, with no
hypothesis relating the two marked strand lengths: `CrossOneOffLongEnough`
already forces `B.length alpha ≥ g + 1 ≥ 4 > 2`, so the period-separation
premise is now supplied unconditionally by
`crossOneOff_cutoff_le_torsionOrder_of_not_both_two`
(`Bananas/CrossOneOffShortStrandPeriod.lean`) in place of the
long-second-strand hypothesis `hBetaLong`. -/
theorem crossOneOff_has_quadratic_inversion_lower_bound_of_not_both_two
    {g k : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (hg : 3 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha) (hBeta : 1 < B.length beta)
    (hLong : CrossOneOffLongEnough
      g (B.length alpha) (B.length beta))
    (hSub : AllSubmodular (mark B.graph
      (strandVertex B alpha ⟨1, by omega⟩)
      (strandVertex B beta ⟨B.length beta - 1, by omega⟩)))
    (hTO : IsTorsionOrder (mark B.graph
      (strandVertex B alpha ⟨1, by omega⟩)
      (strandVertex B beta ⟨B.length beta - 1, by omega⟩)) k) :
    HasInversionLowerBound (mark B.graph
      (strandVertex B alpha ⟨1, by omega⟩)
      (strandVertex B beta ⟨B.length beta - 1, by omega⟩)) k
      (correctedCrossOneOffForcedCount g (B.length beta)) := by
  let M := mark B.graph
    (strandVertex B alpha ⟨1, by omega⟩)
    (strandVertex B beta ⟨B.length beta - 1, by omega⟩)
  let D : CFDiv B.graph := g • oneChip (rightEndpoint B)
  obtain ⟨tau, hTau, hAffine⟩ :=
    exists_affineTransmissionPermutation_of_submodular M D
      (banana_graph_connected B) (hSub D) hTO.1
  have hFinite := kInversions_finite_of_isKAffine hTO.1.1 hAffine
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
  refine ⟨D, tau, hTau, hAffine, hFinite, ?_⟩
  exact crossOneOff_corrected_inversion_lower_bound B alpha beta tau
    (by omega) hab hAlpha hBeta hLong hTau hSeparate hFinite

end Bananas
