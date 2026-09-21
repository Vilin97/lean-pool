/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffInversions
import LeanPool.BrillNoetherGraphs.Bananas.Jacobian.BananaTorsionSlopes
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TorsionOrderExact

/-!
# The cross-one-off obstruction to general transmission

The exact-torsion theorem supplies the period separation that ordinary
inversion counting needs.  In the long-second-strand regime, the exceptional
order-two branch of the corrected torsion dichotomy is impossible, so a
`k`-general marking has `g ≤ k`.  The corrected decreasing block then has
more than `genus = g` inversions as soon as `g ≥ 7`.
-/

namespace Bananas

open Utilities

/-- In the long-second-strand regime, `k`-general transmission forces the
period to be at least the genus.  This is the graph-theoretic separation
missing from a count based only on the forced rows of corrected Lemma 4.30.

The proof uses exactness of the `k`-general period and corrected Lemma 4.27.
Its order-two midpoint alternative cannot occur because the second mark is
the penultimate point of a strand of length at least `g+1 > 2`. -/
theorem crossOneOff_kGeneral_period_ge_genus
    {g k : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (hg : 3 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha)
    (hBetaLong : g + 1 ≤ B.length beta)
    (hK : KGeneralTransmission
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩)) k) :
    g ≤ k := by
  let i : B.PathPosition alpha := ⟨1, by omega⟩
  let j : B.PathPosition beta := ⟨B.length beta - 1, by omega⟩
  have hi : B.IsInteriorPosition alpha i := by
    change 0 < (1 : ℕ) ∧ 1 < B.length alpha
    exact ⟨by omega, hAlpha⟩
  have hj : B.IsInteriorPosition beta j := by
    change 0 < B.length beta - 1 ∧ B.length beta - 1 < B.length beta
    omega
  have huv : strandVertex B alpha i ≠ strandVertex B beta j := by
    intro huvEq
    exact hab (strand_eq_of_interior_vertex_eq B alpha beta i j hi hj huvEq)
  have hTO : IsTorsionOrder
      (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)) k :=
    hK.isTorsionOrder huv (banana_graph_connected B) (by
      change 0 < genus B.graph
      rw [B.genus_graph]
      omega)
  have hDichotomy := cross_oneOff_torsion_dichotomy (by omega) B alpha beta
    i j hab hi hj (by simp [i]) (by simp [j]; omega) hTO
  rcases hDichotomy with hExceptional | hPeriod
  · rcases hExceptional.1 with ⟨_, _, hjMid, _⟩
    dsimp [j] at hjMid
    omega
  · exact hPeriod

/-- The corrected Corollary 4.29 block directly rules out `k`-general
transmission in genus at least seven, under the explicit long-strand range
needed by the row calculation.

The threshold `7` is sharp for this particular block: it contributes
`choose (g-2) 2` inversions, which first exceeds the genus at `g=7`.
No claim about the still-unproved larger count of Corollary 4.31 is used. -/
theorem crossOneOff_not_kGeneral_of_seven_le_genus
    {g k : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (hg : 7 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha)
    (hBetaLong : g + 1 ≤ B.length beta)
    (hLong : CrossOneOffLongEnough
      g (B.length alpha) (B.length beta)) :
    ¬ KGeneralTransmission
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩)) k := by
  intro hK
  have hPeriod : g ≤ k := crossOneOff_kGeneral_period_ge_genus
    B alpha beta (by omega) hab hAlpha hBetaLong hK
  obtain ⟨tau, hTau, _hAffine, hFinite, hUpper⟩ :=
    hK.2.2 (g • one_chip (rightEndpoint B))
  have hLower := crossOneOff_simple_inversion_lower_bound
    B alpha beta tau (by omega) hab hAlpha hBetaLong hLong hTau hPeriod hFinite
  have hGenus : Int.toNat (genus
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩)).graph) = g := by
    change Int.toNat (genus B.graph) = g
    rw [B.genus_graph]
    omega
  rw [hGenus] at hUpper
  have hBound : Nat.choose (g - 2) 2 ≤ g := hLower.trans hUpper
  let product := (g - 2) * (g - 3)
  have hChoose : Nat.choose (g - 2) 2 = product / 2 := by
    rw [Nat.choose_two_right]
    have hPred : g - 2 - 1 = g - 3 := by omega
    rw [hPred]
  have hProduct : 2 * g + 2 ≤ product := by
    dsimp [product]
    have hTwo : g - 2 + 2 = g := Nat.sub_add_cancel (by omega)
    have hThree : g - 3 + 3 = g := Nat.sub_add_cancel (by omega)
    nlinarith
  rw [hChoose] at hBound
  omega

end Bananas
