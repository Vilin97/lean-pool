/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffCorrectedInversion
public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffPeriodSeparation

/-!
# Corrected long-strand cross-one-off obstruction

The corrected Corollary 4.31 count, together with the strict period
separation, rules out `k`-general transmission in genus at least five as soon
as the second marked strand has length at least `g+1`.  This includes the
boundary length `g+1` omitted by the earlier extended-simple-block argument.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- The genus-five threshold is the first one at which the universal
`choose (g-1) 2` portion of the corrected count exceeds the genus. -/
theorem choose_genus_sub_one_two_gt_genus {g : ℕ} (hg : 5 ≤ g) :
    g < Nat.choose (g - 1) 2 := by
  rw [Nat.choose_two_right]
  have hPred : g - 1 - 1 = g - 2 := by omega
  rw [hPred]
  have hOne : g - 1 + 1 = g := Nat.sub_add_cancel (by omega)
  have hTwo : g - 2 + 2 = g := Nat.sub_add_cancel (by omega)
  have hProduct : 2 * g + 2 ≤ (g - 1) * (g - 2) := by
    nlinarith
  omega

/-- In the long-second-strand regime, the corrected forced count is already
strictly larger than the genus for `g ≥ 5`. -/
theorem genus_lt_correctedCrossOneOffForcedCount_of_second_long
    {g n : ℕ} (hg : 5 ≤ g) (hn : g + 1 ≤ n) :
    g < correctedCrossOneOffForcedCount g n := by
  have hnTwo : n ≠ 2 := by omega
  rw [correctedCrossOneOffForcedCount, if_neg hnTwo]
  exact (choose_genus_sub_one_two_gt_genus hg).trans_le
    (Nat.le_add_right _ _)

/-- **Corrected long-strand consequence of Corollary 4.31.**

For distinct cross-one-off marks, a second strand of length at least `g+1`
and the corrected long-first-strand range rule out `k`-general transmission
in every genus `g ≥ 5`.  The threshold is sharp for this count: at `g=4`
and `length beta = g+1`, its numerical lower bound equals `g`. -/
theorem crossOneOff_not_kGeneral_of_five_le_genus_second_long
    {g k : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (hg : 5 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha)
    (hBetaLong : g + 1 ≤ B.length beta)
    (hLong : CrossOneOffLongEnough
      g (B.length alpha) (B.length beta)) :
    ¬ KGeneralTransmission
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩)) k := by
  intro hK
  obtain ⟨tau, hTau, _hAffine, hFinite, hUpper⟩ :=
    hK.2.2 (g • oneChip (rightEndpoint B))
  have hSeparate : crossOneOffCutoff g (B.length beta) ≤ k :=
    crossOneOff_kGeneral_cutoff_le_period
      B alpha beta (by omega) hab hAlpha hBetaLong hK
  have hLower := crossOneOff_corrected_inversion_lower_bound
    B alpha beta tau (by omega) hab hAlpha (by omega) hLong hTau
      hSeparate hFinite
  have hGenus : Int.toNat (genus
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩)).graph) = g := by
    change Int.toNat (genus B.graph) = g
    rw [B.genus_graph]
    omega
  rw [hGenus] at hUpper
  have hCountLe : correctedCrossOneOffForcedCount g (B.length beta) ≤ g :=
    hLower.trans hUpper
  have hCountGt : g < correctedCrossOneOffForcedCount g (B.length beta) :=
    genus_lt_correctedCrossOneOffForcedCount_of_second_long hg hBetaLong
  omega

/-- At the first excluded genus and the boundary strand length, the corrected
numerical lower bound is exactly the KGT upper bound. -/
theorem correctedCrossOneOffForcedCount_genus_four_boundary :
    correctedCrossOneOffForcedCount 4 5 = 4 := by
  decide

/-- Boundary-length specialization: when `length beta = g+1`, the exact
long-range threshold is `length alpha ≥ g+2`. -/
theorem crossOneOff_not_kGeneral_boundary_second_length
    {g k : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (hg : 5 ≤ g) (hab : alpha ≠ beta)
    (hBeta : B.length beta = g + 1)
    (hAlphaLong : g + 2 ≤ B.length alpha) :
    ¬ KGeneralTransmission
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩)) k := by
  apply crossOneOff_not_kGeneral_of_five_le_genus_second_long
    B alpha beta hg hab (by omega) (by omega)
  unfold CrossOneOffLongEnough
  rw [hBeta]
  have hDiv : g / (g + 1 - 1) = 1 := by
    simpa using Nat.div_self (by omega : 0 < g)
  rw [hDiv]
  omega

/-- Strictly-long specialization: when `length beta ≥ g+2`, the exact
long-range threshold drops to `length alpha ≥ g+1`. -/
theorem crossOneOff_not_kGeneral_very_long_second_strand
    {g k : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (hg : 5 ≤ g) (hab : alpha ≠ beta)
    (hBetaVeryLong : g + 2 ≤ B.length beta)
    (hAlphaLong : g + 1 ≤ B.length alpha) :
    ¬ KGeneralTransmission
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩)) k := by
  apply crossOneOff_not_kGeneral_of_five_le_genus_second_long
    B alpha beta hg hab (by omega) (by omega)
  unfold CrossOneOffLongEnough
  have hDiv : g / (B.length beta - 1) = 0 :=
    Nat.div_eq_of_lt (by omega)
  rw [hDiv]
  omega

end Bananas
