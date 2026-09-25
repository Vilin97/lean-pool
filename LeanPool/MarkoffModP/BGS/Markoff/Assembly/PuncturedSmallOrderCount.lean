/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Core.PuncturedNormalization
public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.NormalizedSmallOrderCount

/-!
# Small-order counts on the punctured Markoff surface

This module transports the normalized small-order set through the core punctured-normalization
equivalence.  Keeping these finite-set estimates here prevents the core equivalence module from
depending on the giant-orbit counting layer.
-/

@[expose] public section

namespace BGS.Markoff

/-- The canonical small-order set, restricted to the normalized punctured surface. -/
noncomputable def normalizedPuncturedMarkoffPointsWithSmallFirstTwoRotationOrders
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)] (bound : ℕ) :
    Finset ↑(normalizedPuncturedSurface (ZMod p)) := by
  classical
  exact Finset.univ.filter fun x =>
    rotationOrder x.1.u1 < bound ∧ rotationOrder x.1.u2 < bound

@[simp]
theorem mem_normalizedPuncturedMarkoffPointsWithSmallFirstTwoRotationOrders_iff
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)] {bound : ℕ}
    {x : ↑(normalizedPuncturedSurface (ZMod p))} :
    x ∈ normalizedPuncturedMarkoffPointsWithSmallFirstTwoRotationOrders p bound ↔
      rotationOrder x.1.u1 < bound ∧ rotationOrder x.1.u2 < bound := by
  classical
  simp [normalizedPuncturedMarkoffPointsWithSmallFirstTwoRotationOrders]

/-- Forgetting the puncture proof embeds the normalized punctured small-order set in the
canonical normalized small-order set. -/
theorem normalizedPuncturedSmallOrderValues_subset
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)] (bound : ℕ) :
    (normalizedPuncturedMarkoffPointsWithSmallFirstTwoRotationOrders p bound).map
        ⟨Subtype.val, Subtype.val_injective⟩ ⊆
      normalizedMarkoffPointsWithSmallFirstTwoRotationOrders p bound := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
  rw [mem_normalizedPuncturedMarkoffPointsWithSmallFirstTwoRotationOrders_iff] at hy
  exact mem_normalizedMarkoffPointsWithSmallFirstTwoRotationOrders_iff.mpr
    ⟨y.2.1, hy.1, hy.2⟩

/-- After forgetting the puncture proof, the punctured small-order set is exactly the canonical
ambient small-order set with the normalized origin erased.  Thus the puncture is exposed rather
than silently discarded during transport. -/
theorem normalizedPuncturedSmallOrderValues_eq_erase_origin
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)] (bound : ℕ) :
    (normalizedPuncturedMarkoffPointsWithSmallFirstTwoRotationOrders p bound).map
        ⟨Subtype.val, Subtype.val_injective⟩ =
      (normalizedMarkoffPointsWithSmallFirstTwoRotationOrders p bound).erase normalizedOrigin := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    rw [mem_normalizedPuncturedMarkoffPointsWithSmallFirstTwoRotationOrders_iff] at hy
    apply Finset.mem_erase.mpr
    refine ⟨?_, mem_normalizedMarkoffPointsWithSmallFirstTwoRotationOrders_iff.mpr
      ⟨y.2.1, hy.1, hy.2⟩⟩
    simpa using y.2.2
  · intro hx
    obtain ⟨hxOrigin, hxSmall⟩ := Finset.mem_erase.mp hx
    rw [mem_normalizedMarkoffPointsWithSmallFirstTwoRotationOrders_iff] at hxSmall
    let y : ↑(normalizedPuncturedSurface (ZMod p)) :=
      ⟨x, by
        change IsNormalizedMarkoff x ∧ x ∉ ({normalizedOrigin} : Set (NormalizedPoint (ZMod p)))
        exact ⟨hxSmall.1, by simpa using hxOrigin⟩⟩
    apply Finset.mem_map.mpr
    refine ⟨y, ?_, rfl⟩
    exact mem_normalizedPuncturedMarkoffPointsWithSmallFirstTwoRotationOrders_iff.mpr
      ⟨hxSmall.2.1, hxSmall.2.2⟩

/-- Removing the normalized origin cannot enlarge the canonical small-order set. -/
theorem normalizedPuncturedMarkoffPointsWithSmallFirstTwoRotationOrders_card_le_ambient
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)] (bound : ℕ) :
    (normalizedPuncturedMarkoffPointsWithSmallFirstTwoRotationOrders p bound).card ≤
      (normalizedMarkoffPointsWithSmallFirstTwoRotationOrders p bound).card := by
  classical
  rw [← Finset.card_map (f := ⟨Subtype.val, Subtype.val_injective⟩)]
  exact Finset.card_mono (normalizedPuncturedSmallOrderValues_subset bound)

/-- Original punctured Markoff points obtained by transporting the canonical normalized
punctured small-order set. -/
noncomputable def puncturedMarkoffPointsWithSmallFirstTwoRotationOrders
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)] (bound : ℕ) :
    Finset (PuncturedMarkoffSurface (ZMod p)) :=
  originalPuncturedFinsetOfNormalized
    (normalizedPuncturedMarkoffPointsWithSmallFirstTwoRotationOrders p bound)

/-- The transported original punctured set has exactly the cardinality of its normalized
source. -/
theorem puncturedMarkoffPointsWithSmallFirstTwoRotationOrders_card_eq_normalized
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)] (bound : ℕ) :
    (puncturedMarkoffPointsWithSmallFirstTwoRotationOrders p bound).card =
      (normalizedPuncturedMarkoffPointsWithSmallFirstTwoRotationOrders p bound).card := by
  exact originalPuncturedFinsetOfNormalized_card _

/-- Equivalently, the transported original set has exactly the cardinality of the ambient
canonical normalized small-order set after its origin is removed. -/
theorem puncturedMarkoffPointsWithSmallFirstTwoRotationOrders_card_eq_normalized_erase_origin
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)] (bound : ℕ) :
    (puncturedMarkoffPointsWithSmallFirstTwoRotationOrders p bound).card =
      ((normalizedMarkoffPointsWithSmallFirstTwoRotationOrders p bound).erase
        normalizedOrigin).card := by
  rw [puncturedMarkoffPointsWithSmallFirstTwoRotationOrders_card_eq_normalized]
  rw [← normalizedPuncturedSmallOrderValues_eq_erase_origin]
  simp

/-- The elementary normalized small-order count therefore bounds the transported finite set on
the original punctured surface. -/
theorem puncturedMarkoffPointsWithSmallFirstTwoRotationOrders_card_le
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpTwo : p ≠ 2) (bound : ℕ) :
    (puncturedMarkoffPointsWithSmallFirstTwoRotationOrders p bound).card ≤
      2 * (2 + 2 * bound ^ 2) ^ 2 := by
  rw [puncturedMarkoffPointsWithSmallFirstTwoRotationOrders_card_eq_normalized]
  exact (normalizedPuncturedMarkoffPointsWithSmallFirstTwoRotationOrders_card_le_ambient bound).trans
    (normalizedMarkoffPointsWithSmallFirstTwoRotationOrders_card_le hpTwo bound)

/-- The divisor-sensitive normalized count also bounds the transported punctured set. -/
theorem puncturedMarkoffPointsWithSmallFirstTwoRotationOrders_card_le_divisor_sensitive
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpTwo : p ≠ 2) (bound : ℕ) :
    (puncturedMarkoffPointsWithSmallFirstTwoRotationOrders p bound).card ≤
      2 * (2 + (bound - 1) *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 2 := by
  rw [puncturedMarkoffPointsWithSmallFirstTwoRotationOrders_card_eq_normalized]
  exact (normalizedPuncturedMarkoffPointsWithSmallFirstTwoRotationOrders_card_le_ambient bound).trans
    (normalizedMarkoffPointsWithSmallFirstTwoRotationOrders_card_le_divisor_sensitive hpTwo bound)

theorem puncturedMarkoffPointsWithSmallFirstTwoRotationOrders_succ_card_le_divisor_sensitive
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpTwo : p ≠ 2) (d : ℕ) :
    (puncturedMarkoffPointsWithSmallFirstTwoRotationOrders p (d + 1)).card ≤
      2 * (2 + d * ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 2 := by
  simpa using
    (puncturedMarkoffPointsWithSmallFirstTwoRotationOrders_card_le_divisor_sensitive
      hpTwo (d + 1))

end BGS.Markoff
