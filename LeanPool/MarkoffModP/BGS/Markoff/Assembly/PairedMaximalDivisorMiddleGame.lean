/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.MiddleGameThenEndgame
public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.PairedMaximalDivisorCorvajaZannierEscape

/-!
# Paired maximal-divisor middle-game assembly

This module lifts the paired maximal-order escape from a chosen coordinate to
the maximum of the three coordinate rotation orders.
-/

@[expose] public section

namespace BGS.Markoff

open BGS.NumberTheory

noncomputable section

/-- One paired middle-game step strictly increases the maximum coordinate
order under the coefficient-sensitive maximal-divisor inequalities. -/
theorem
    exists_sameNormalizedComponent_maximalOrder_increase_of_pairedMaximalDivisorBounds
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)]
    [Fintype (quadraticFiniteField p)] (hpTwo : p ≠ 2)
    {delta : ℝ} (hdelta : delta ≤ (1 : ℝ) / 2)
    (x : NormalizedMarkoffSurface (ZMod p))
    (hbelow : (maximalCoordinateRotationOrder x.1 : ℝ) <
      (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hcube :
      (6 *
        (middleGameMaximalOrders p
          (maximalCoordinateRotationOrder x.1)).card) ^ 3 <
        maximalCoordinateRotationOrder x.1)
    (hlinear :
      24 *
        (middleGameMaximalOrders p
          (maximalCoordinateRotationOrder x.1)).card *
        maximalCoordinateRotationOrder x.1 < p) :
    ∃ y : NormalizedMarkoffSurface (ZMod p),
      SameNormalizedComponent x y ∧
        maximalCoordinateRotationOrder x.1 <
          maximalCoordinateRotationOrder y.1 := by
  obtain ⟨x', hxx', hx'Order⟩ :=
    exists_sameNormalizedComponent_firstRotation_eq_maximal x
  have hx'Cube :
      (6 *
        (middleGameMaximalOrders p (rotationOrder x'.1.u1)).card) ^ 3 <
          rotationOrder x'.1.u1 := by
    simpa [hx'Order] using hcube
  have hx'Linear :
      24 * (middleGameMaximalOrders p (rotationOrder x'.1.u1)).card *
          rotationOrder x'.1.u1 < p := by
    simpa [hx'Order] using hlinear
  have hordersPos :
      0 < (middleGameMaximalOrders p (rotationOrder x'.1.u1)).card := by
    apply Finset.card_pos.mpr
    have hpPlus : p + 1 ≠ 0 := by omega
    have honeBound : 1 < rotationOrder x'.1.u1 + 1 := by
      exact Nat.lt_succ_of_le (rotationOrder_pos x'.1.u1)
    obtain ⟨m, hm, _hmultiple⟩ :=
      exists_dvd_maximalDivisorBelow hpPlus (one_dvd (p + 1)) honeBound
    refine ⟨m, ?_⟩
    rw [middleGameMaximalOrders, Finset.mem_union]
    exact Or.inr hm
  have hbase :
      4 <
        (6 *
          (middleGameMaximalOrders p
            (rotationOrder x'.1.u1)).card) ^ 3 := by
    have hcoeff :
        6 ≤
          6 *
            (middleGameMaximalOrders p
              (rotationOrder x'.1.u1)).card := by
      nlinarith
    calc
      4 < 6 ^ 3 := by norm_num
      _ ≤ (6 *
          (middleGameMaximalOrders p
            (rotationOrder x'.1.u1)).card) ^ 3 :=
        Nat.pow_le_pow_left hcoeff 3
  have hx'AboveFour : 4 < rotationOrder x'.1.u1 :=
    hbase.trans hx'Cube
  have hx'Below : (rotationOrder x'.1.u1 : ℝ) <
      (p : ℝ) ^ ((1 : ℝ) / 2 + delta) := by
    simpa [hx'Order] using hbelow
  have hx'0 : x'.1.u1 ≠ 0 := by
    intro hzero
    have hle := rotationOrder_zero_le_four p
    rw [hzero] at hx'AboveFour
    omega
  have hx'Nonparabolic : x'.1.u1 ^ 2 ≠ 4 := by
    intro hparabolic
    have hcases : x'.1.u1 = 2 ∨ x'.1.u1 = -2 := by
      apply (sq_eq_sq_iff_eq_or_eq_neg).mp
      calc
        x'.1.u1 ^ 2 = 4 := hparabolic
        _ = (2 : ZMod p) ^ 2 := by norm_num
    have hpOne : (1 : ℝ) ≤ p := by
      exact_mod_cast
        (show 1 ≤ p by exact (Fact.out : p.Prime).one_le)
    have hexponentLe : (1 : ℝ) / 2 + delta ≤ 1 := by
      linarith
    have hrpowLe :
        (p : ℝ) ^ ((1 : ℝ) / 2 + delta) ≤ (p : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hpOne hexponentLe
    rcases hcases with htwo | hnegTwo
    · rw [htwo, rotationOrder_two] at hx'Below
      linarith
    · rw [hnegTwo, rotationOrder_neg_two p hpTwo] at hx'Below
      have htwoP : ((2 * p : ℕ) : ℝ) = 2 * (p : ℝ) := by norm_num
      rw [htwoP] at hx'Below
      have hpPos : (0 : ℝ) < p := by positivity
      linarith
  obtain ⟨n, hnIncrease⟩ :=
    exists_iterate_with_larger_secondRotationOrder_of_nonzero_nonparabolic_pairedMaximalOrders
      p hpTwo delta hdelta x'.1 x'.property hx'0 hx'Nonparabolic
        hx'Below hx'Cube hx'Linear
  let y := (normalizedRotate1Surface^[n]) x'
  have hcoe : y.1 = (normalizedRotate1^[n]) x'.1 :=
    coe_iterate_normalizedRotate1Surface x' n
  refine ⟨y, sameNormalizedComponent_trans hxx'
    (sameNormalizedComponent_iterate_normalizedRotate1Surface x' n), ?_⟩
  rw [← hx'Order]
  exact hnIncrease.trans_le <| by
    have hmeasureEq : maximalCoordinateRotationOrder y.1 =
        maximalCoordinateRotationOrder
          ((normalizedRotate1^[n]) x'.1) :=
      congrArg maximalCoordinateRotationOrder hcoe
    calc
      rotationOrder ((normalizedRotate1^[n]) x'.1).u2 ≤
          maximalCoordinateRotationOrder
            ((normalizedRotate1^[n]) x'.1) :=
        rotationOrder_second_le_maximalCoordinateRotationOrder _
      _ = maximalCoordinateRotationOrder y.1 := hmeasureEq.symm

end

end BGS.Markoff
