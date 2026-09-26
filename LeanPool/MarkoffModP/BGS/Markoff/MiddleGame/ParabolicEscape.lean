/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Core.ConicParametrization
public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.RightSubgroups

/-!
# The parabolic middle-game branch

The weighted Corvaja--Zannier argument is only needed for semisimple coordinate traces.
The two parabolic traces have exact rotation orders `p` and `2 * p`, already beyond every
endgame threshold `p ^ (1 / 2 + delta)` with `delta <= 1 / 2`.

For primes congruent to one modulo four, this module also connects the explicit affine-line
parametrizations to the concrete rotation cycles through every point on the two parabolic fibers.
For primes congruent to three modulo four those fibers are empty by the existing results in
`ParabolicFibers`.
-/

@[expose] public section

namespace BGS.Markoff

/-- Every endgame power threshold with exponent at most one is bounded by `p`. -/
theorem endgamePowerThreshold_le_prime
    (p : ℕ) [Fact p.Prime] (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2) :
    (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ (p : ℝ) := by
  have hp : (1 : ℝ) ≤ p := by
    exact_mod_cast (Fact.out : p.Prime).one_le
  calc
    (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ (p : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hp (by linarith)
    _ = (p : ℝ) := Real.rpow_one _

/-- The trace-`2` rotation already meets the endgame power threshold. -/
theorem endgamePowerThreshold_le_rotationOrder_two
    (p : ℕ) [Fact p.Prime] (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2) :
    (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤
      (rotationOrder (2 : ZMod p) : ℝ) := by
  rw [rotationOrder_two p]
  exact endgamePowerThreshold_le_prime p delta hdelta

/-- The trace-`-2` rotation has order `2 * p`, hence also meets the endgame threshold. -/
theorem endgamePowerThreshold_le_rotationOrder_neg_two
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2) :
    (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤
      (rotationOrder (-2 : ZMod p) : ℝ) := by
  rw [rotationOrder_neg_two p hpTwo]
  have hthreshold := endgamePowerThreshold_le_prime p delta hdelta
  exact hthreshold.trans (by
    exact_mod_cast (show p ≤ 2 * p by omega))

/-- Unified parabolic branch: either normalized parabolic trace is already in the endgame
large-order range. -/
theorem endgamePowerThreshold_le_rotationOrder_of_parabolicTrace
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (t : ZMod p) (ht : t = 2 ∨ t = -2) :
    (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ (rotationOrder t : ℝ) := by
  rcases ht with rfl | rfl
  · exact endgamePowerThreshold_le_rotationOrder_two p delta hdelta
  · exact endgamePowerThreshold_le_rotationOrder_neg_two p hpTwo delta hdelta

/-- Every point on the normalized trace-`2` fiber for `p = 1 mod 4` has a rotation cycle of
exactly `p` points. -/
theorem normalizedRotationCycle_card_of_mem_fiber_two
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2) (hmod : p % 4 = 1)
    (x : NormalizedPoint (ZMod p)) (hx : x ∈ normalizedFiber1 (2 : ZMod p)) :
    (normalizedRotationCycle (2 : ZMod p) x).card = p := by
  obtain ⟨i, hi, hfiberTwo, _⟩ :=
    exists_parabolic_line_decomposition_of_mod_four_eq_one p hmod
  rw [hfiberTwo] at hx
  rcases hx with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · simpa [rotationOrder_two p] using
      normalizedRotationCycle_card_parabolicLineAtTwo p hpTwo i s hi
  · have hnegI : (-i) ^ 2 = -(1 : ZMod p) := by simpa using hi
    simpa [rotationOrder_two p] using
      normalizedRotationCycle_card_parabolicLineAtTwo p hpTwo (-i) s hnegI

/-- Every point on the normalized trace-`-2` fiber for `p = 1 mod 4` has a rotation cycle of
exactly `2 * p` points. -/
theorem normalizedRotationCycle_card_of_mem_fiber_neg_two
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2) (hmod : p % 4 = 1)
    (x : NormalizedPoint (ZMod p)) (hx : x ∈ normalizedFiber1 (-2 : ZMod p)) :
    (normalizedRotationCycle (-2 : ZMod p) x).card = 2 * p := by
  obtain ⟨i, hi, _, hfiberNegTwo⟩ :=
    exists_parabolic_line_decomposition_of_mod_four_eq_one p hmod
  rw [hfiberNegTwo] at hx
  rcases hx with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · simpa [rotationOrder_neg_two p hpTwo] using
      normalizedRotationCycle_card_parabolicLineAtNegTwo p hpTwo i s hi
  · have hnegI : (-i) ^ 2 = -(1 : ZMod p) := by simpa using hi
    simpa [rotationOrder_neg_two p hpTwo] using
      normalizedRotationCycle_card_parabolicLineAtNegTwo p hpTwo (-i) s hnegI

/-- The exact trace-`2` cycle through any fiber point meets the endgame power threshold. -/
theorem endgamePowerThreshold_le_parabolicFiberTwo_cycleCard
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2) (hmod : p % 4 = 1)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (x : NormalizedPoint (ZMod p)) (hx : x ∈ normalizedFiber1 (2 : ZMod p)) :
    (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤
      ((normalizedRotationCycle (2 : ZMod p) x).card : ℝ) := by
  rw [normalizedRotationCycle_card_of_mem_fiber_two p hpTwo hmod x hx]
  exact endgamePowerThreshold_le_prime p delta hdelta

/-- The exact trace-`-2` cycle through any fiber point meets the endgame power threshold. -/
theorem endgamePowerThreshold_le_parabolicFiberNegTwo_cycleCard
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2) (hmod : p % 4 = 1)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (x : NormalizedPoint (ZMod p)) (hx : x ∈ normalizedFiber1 (-2 : ZMod p)) :
    (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤
      ((normalizedRotationCycle (-2 : ZMod p) x).card : ℝ) := by
  rw [normalizedRotationCycle_card_of_mem_fiber_neg_two p hpTwo hmod x hx]
  have hthreshold := endgamePowerThreshold_le_prime p delta hdelta
  exact hthreshold.trans (by
    exact_mod_cast (show p ≤ 2 * p by omega))

end BGS.Markoff
