/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.ElementaryExistence
import LeanPool.BrillNoetherGraphs.ChipFiringWithLean.RiemannRoch

/-!
# Brill--Noether existence through genus five from the two critical pencils

Atanasov--Ranganathan reduce Brill--Noether existence in genera at most five
to two rank-one statements:

* every connected genus-four graph has a degree-three rank-one divisor;
* every connected genus-five graph has a degree-four rank-one divisor.

This file formalizes that reduction independently of their geometric case
analysis.  In particular, the two inputs below are the exact public boundary
for a direct formalization of their proof.  No marked divisor, contraction
compatibility, or transmission condition occurs here.

The library's `BNExists G r d` uses the equivalent convenient convention
"degree exactly `d` and rank at least `r`".  The dependency's
`brill_noether_conjecture` uses the same convention with the Brill--Noether
inequality exposed as an implication.
-/

namespace Utilities

/-- The genus-four geometric heart of the Atanasov--Ranganathan theorem. -/
def GenusFourRankOneExistence : Prop :=
  ∀ (G : CFGraph.{0}), graph_connected G → genus G = 4 → BNExists G 1 3

/-- The genus-five geometric heart of the Atanasov--Ranganathan theorem. -/
def GenusFiveRankOneExistence : Prop :=
  ∀ (G : CFGraph.{0}), graph_connected G → genus G = 5 → BNExists G 1 4

/-- The two genuinely geometric inputs left after the low-genus arithmetic
reduction. -/
structure LowGenusCriticalPencils : Prop where
  genusFour : GenusFourRankOneExistence
  genusFive : GenusFiveRankOneExistence

/-- Nonnegativity of the Brill--Noether number is the rectangle-area bound. -/
theorem bnNumber_nonneg_iff_rectangle_area_le (G : CFGraph) (r d : ℤ) :
    0 ≤ bnNumber G r d ↔
      (r + 1) * rectangleWidth G r d ≤ genus G := by
  unfold bnNumber
  omega

/-- Every admissible Brill--Noether parameter pair on a connected graph of
genus at most three is elementary. -/
theorem bnExists_of_genus_le_three
    {G : CFGraph} (hG : graph_connected G) (hGenus : genus G ≤ 3)
    {r d : ℤ} (hR : 0 ≤ r) (hRho : 0 ≤ bnNumber G r d) :
    BNExists G r d := by
  apply BNExists_elementary hG hR hRho
  by_cases hRankZero : r = 0
  · exact Or.inl hRankZero
  · right
    by_contra hWidth
    have hr1 : 1 ≤ r := by omega
    have hq2 : 2 ≤ rectangleWidth G r d := by omega
    rw [bnNumber_nonneg_iff_rectangle_area_le] at hRho
    nlinarith

/-- In genus four, `r = 1`, `d = 3` is the only admissible pair outside the
elementary range. -/
theorem bnExists_genus_four_of_rankOneDegreeThree
    {G : CFGraph} (hG : graph_connected G) (hGenus : genus G = 4)
    (hCritical : BNExists G 1 3) {r d : ℤ}
    (hR : 0 ≤ r) (hRho : 0 ≤ bnNumber G r d) :
    BNExists G r d := by
  by_cases hEasy : r = 0 ∨ rectangleWidth G r d ≤ 1
  · exact BNExists_elementary hG hR hRho hEasy
  · push Not at hEasy
    have hr1 : 1 ≤ r := by omega
    have hq2 : 2 ≤ rectangleWidth G r d := by omega
    have hArea : (r + 1) * rectangleWidth G r d ≤ 4 := by
      rw [bnNumber_nonneg_iff_rectangle_area_le] at hRho
      omega
    have hr : r = 1 := by nlinarith
    have hq : rectangleWidth G r d = 2 := by
      subst r
      nlinarith
    have hd : d = 3 := by
      unfold rectangleWidth at hq
      omega
    simpa [hr, hd] using hCritical

/-- In genus five, `r = 1`, `d = 4` is the only admissible pair outside the
elementary range. -/
theorem bnExists_genus_five_of_rankOneDegreeFour
    {G : CFGraph} (hG : graph_connected G) (hGenus : genus G = 5)
    (hCritical : BNExists G 1 4) {r d : ℤ}
    (hR : 0 ≤ r) (hRho : 0 ≤ bnNumber G r d) :
    BNExists G r d := by
  by_cases hEasy : r = 0 ∨ rectangleWidth G r d ≤ 1
  · exact BNExists_elementary hG hR hRho hEasy
  · push Not at hEasy
    have hr1 : 1 ≤ r := by omega
    have hq2 : 2 ≤ rectangleWidth G r d := by omega
    have hArea : (r + 1) * rectangleWidth G r d ≤ 5 := by
      rw [bnNumber_nonneg_iff_rectangle_area_le] at hRho
      omega
    have hr : r = 1 := by nlinarith
    have hq : rectangleWidth G r d = 2 := by
      subst r
      nlinarith
    have hd : d = 4 := by
      unfold rectangleWidth at hq
      omega
    simpa [hr, hd] using hCritical

/-- The two critical pencils imply `BNExists` for every nonnegative rank and
every admissible parameter pair in genus at most five. -/
theorem bnExists_of_genus_le_five_of_criticalPencils
    (critical : LowGenusCriticalPencils)
    {G : CFGraph.{0}} (hG : graph_connected G) (hGenus : genus G ≤ 5)
    {r d : ℤ} (hR : 0 ≤ r) (hRho : 0 ≤ bnNumber G r d) :
    BNExists G r d := by
  by_cases hLow : genus G ≤ 3
  · exact bnExists_of_genus_le_three hG hLow hR hRho
  · have hAtLeastFour : 4 ≤ genus G := by omega
    rcases eq_or_lt_of_le hAtLeastFour with hFour | hAboveFour
    · exact bnExists_genus_four_of_rankOneDegreeThree hG hFour.symm
        (critical.genusFour G hG hFour.symm) hR hRho
    · have hFive : genus G = 5 := by omega
      exact bnExists_genus_five_of_rankOneDegreeFour hG hFive
        (critical.genusFive G hG hFive) hR hRho

/-- Atanasov--Ranganathan's two critical rank-one assertions imply the full
Brill--Noether existence conjecture for every connected graph of genus at
most five. -/
theorem brillNoetherConjecture_of_genus_le_five_of_criticalPencils
    (critical : LowGenusCriticalPencils)
    (G : CFGraph.{0}) (hG : graph_connected G) (hGenus : genus G ≤ 5)
    (r d : ℤ) : brill_noether_conjecture hG r d := by
  show 0 ≤ genus G - (r + 1) * (genus G - d + r) →
    ∃ D : CFDiv G, rank G D ≥ r ∧ deg D = d
  intro hRho
  by_cases hR : 0 ≤ r
  · obtain ⟨D, hDegree, hRank⟩ :=
      bnExists_of_genus_le_five_of_criticalPencils critical hG hGenus hR
        (by simpa [bnNumber, rectangleWidth] using hRho)
    exact ⟨D, hRank, hDegree⟩
  · let u : G.V := Classical.arbitrary G.V
    refine ⟨d • one_chip u, ?_, ?_⟩
    · have hLower := rank_geq_neg_one G (d • one_chip u)
      omega
    · rw [map_zsmul, deg_one_chip]
      ring

/-- The proposition represented by the paper's main theorem in the library's
degree-exact, rank-lower-bound convention. -/
def BrillNoetherExistenceThroughFive : Prop :=
  ∀ (G : CFGraph.{0}) (hG : graph_connected G), genus G ≤ 5 →
    ∀ r d : ℤ, brill_noether_conjecture hG r d

theorem criticalPencils_imply_brillNoetherExistenceThroughFive
    (critical : LowGenusCriticalPencils) :
    BrillNoetherExistenceThroughFive := by
  intro G hG hGenus r d
  exact brillNoetherConjecture_of_genus_le_five_of_criticalPencils
    critical G hG hGenus r d

end Utilities
