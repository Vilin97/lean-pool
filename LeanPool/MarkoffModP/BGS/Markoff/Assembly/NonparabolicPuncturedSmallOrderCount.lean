/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Assembly.NonparabolicMaximalDivisorConcreteCount
import LeanPool.MarkoffModP.BGS.Markoff.Core.PuncturedNormalization

/-!
# Fixed-point-free small-order counts on the punctured surface

Restricting both counted coordinates to nonparabolic traces removes the
two-torsion correction from the torus trace count.  The resulting transported
punctured set satisfies

`2 * |small nonparabolic points| ≤ ((bound - 1) * M) ^ 2`.
-/

namespace BGS.Markoff

noncomputable section

/-- Normalized punctured points whose first two coordinates are both
nonparabolic and have rotation order below `bound`. -/
def normalizedPuncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)] (bound : ℕ) :
    Finset ↥(normalizedPuncturedSurface (ZMod p)) := by
  classical
  exact Finset.univ.filter fun x =>
    rotationOrder x.1.u1 < bound ∧
      rotationOrder x.1.u2 < bound ∧
      x.1.u1 ^ 2 ≠ 4 ∧ x.1.u2 ^ 2 ≠ 4

@[simp]
theorem mem_normalizedPuncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders_iff
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)] {bound : ℕ}
    {x : ↥(normalizedPuncturedSurface (ZMod p))} :
    x ∈
        normalizedPuncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders
          p bound ↔
      rotationOrder x.1.u1 < bound ∧
      rotationOrder x.1.u2 < bound ∧
      x.1.u1 ^ 2 ≠ 4 ∧ x.1.u2 ^ 2 ≠ 4 := by
  classical
  simp
    [normalizedPuncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders]

/-- Forgetting the puncture embeds the nonparabolic small-order set into the
ambient set cut out by the fixed-point-free trace set. -/
theorem normalizedPuncturedSmallNonparabolicOrderValues_subset_traceSet
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpTwo : p ≠ 2) (bound : ℕ) :
    (normalizedPuncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders
        p bound).map ⟨Subtype.val, Subtype.val_injective⟩ ⊆
      normalizedMarkoffPointsWithFirstTwoCoordinatesIn
        (nonparabolicConcreteLowOrderTraceSet p bound) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
  rw [
    mem_normalizedPuncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders_iff
  ] at hy
  exact mem_normalizedMarkoffPointsWithFirstTwoCoordinatesIn_iff.mpr
    ⟨y.2.1,
      mem_nonparabolicConcreteLowOrderTraceSet_of_rotationOrder_lt
        hpTwo y.1.u1 bound hy.2.2.1 hy.1,
      mem_nonparabolicConcreteLowOrderTraceSet_of_rotationOrder_lt
        hpTwo y.1.u2 bound hy.2.2.2 hy.2.1⟩

/-- Original punctured points transported from the normalized nonparabolic
small-order set. -/
def puncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)] (bound : ℕ) :
    Finset (PuncturedMarkoffSurface (ZMod p)) :=
  originalPuncturedFinsetOfNormalized
    (normalizedPuncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders
      p bound)

theorem puncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders_card_eq_normalized
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)] (bound : ℕ) :
    (puncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders
        p bound).card =
      (normalizedPuncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders
        p bound).card := by
  exact originalPuncturedFinsetOfNormalized_card _

/-- The fixed-point-free trace pairing on both coordinates gives a square
bound with no additive parabolic correction. -/
theorem two_mul_puncturedSmallNonparabolicOrder_card_le_maximalDivisors
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpTwo : p ≠ 2) (bound : ℕ) :
    2 *
        (puncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders
          p bound).card ≤
      ((bound - 1) * maximalDivisorCountSum p bound) ^ 2 := by
  classical
  rw [
    puncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders_card_eq_normalized
  ]
  let smallSet :=
    normalizedPuncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders
      p bound
  let traceSet := nonparabolicConcreteLowOrderTraceSet p bound
  have hpoints : smallSet.card ≤ 2 * traceSet.card ^ 2 := by
    rw [← Finset.card_map
      (f := ⟨Subtype.val, Subtype.val_injective⟩)]
    exact
      (Finset.card_mono
        (normalizedPuncturedSmallNonparabolicOrderValues_subset_traceSet
          hpTwo bound)).trans
        (normalizedMarkoffPointsWithFirstTwoCoordinatesIn_card_le traceSet)
  have htraces :
      2 * traceSet.card ≤
        (bound - 1) * maximalDivisorCountSum p bound := by
    exact two_mul_nonparabolicConcreteLowOrderTraceSet_card_le bound
  change 2 * smallSet.card ≤
    ((bound - 1) * maximalDivisorCountSum p bound) ^ 2
  calc
    2 * smallSet.card ≤ 2 * (2 * traceSet.card ^ 2) :=
      Nat.mul_le_mul_left 2 hpoints
    _ = (2 * traceSet.card) ^ 2 := by ring
    _ ≤ ((bound - 1) * maximalDivisorCountSum p bound) ^ 2 := by
      gcongr

/-- At `bound = d + 1`, the low-order square has coefficient exactly `d`. -/
theorem two_mul_puncturedSmallNonparabolicOrder_succ_card_le_maximalDivisors
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpTwo : p ≠ 2) (d : ℕ) :
    2 *
        (puncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders
          p (d + 1)).card ≤
      (d * maximalDivisorCountSum p (d + 1)) ^ 2 := by
  simpa using
    (two_mul_puncturedSmallNonparabolicOrder_card_le_maximalDivisors
      hpTwo (d + 1))

end

end BGS.Markoff
