/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Assembly.ExactOrderComplementObstruction
import LeanPool.MarkoffModP.BGS.Markoff.Assembly.EulerSevenPairedMaximalDivisorMiddleGame

/-!
# Exact-order obstruction with the Euler-seven cap

The exact-order root budget and the Euler-seven middle-game cap must concern
the same maximal bad rotation order.  This file keeps that common witness
visible instead of composing two unrelated existential statements.
-/

namespace BGS.Markoff

noncomputable section

private def normalizedPuncturedPointExactOrderEulerSeven
    {R : Type*} [Field R] [Invertible (3 : R)]
    (x : PuncturedMarkoffSurface R) : NormalizedMarkoffSurface R :=
  normalizedSurfaceOfPunctured (puncturedNormalizationEquiv R x)

private theorem normalizedPuncturedPointExactOrderEulerSeven_smul
    {R : Type*} [Field R] [Invertible (3 : R)]
    (g : Gamma R) (z : PuncturedMarkoffSurface R) :
    normalizedPuncturedPointExactOrderEulerSeven (g • z) =
      normalizedGammaPerm R g
        (normalizedPuncturedPointExactOrderEulerSeven z) := by
  have hzinv :
      (normalizationSurfaceEquiv R).symm
          (normalizedSurfaceOfPunctured
            (puncturedNormalizationEquiv R z)) = z.1 := by
    apply Subtype.ext
    exact (normalizationEquiv R).symm_apply_apply z.1.1
  unfold normalizedPuncturedPointExactOrderEulerSeven
  rw [normalizedGammaPerm_apply, hzinv]
  apply Subtype.ext
  rfl

/-- A point outside the base component gives one order `d` which
simultaneously satisfies the exact root-sum obstruction and the negation of
the strict Euler-seven escape condition. -/
theorem
    exists_exactOrderRootSum_eulerSevenCap_of_not_samePuncturedComponent
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpThree : 3 < p)
    (c x : PuncturedMarkoffSurface (ZMod p))
    (hlarge : ∀ z : NormalizedMarkoffSurface (ZMod p),
      (p : ℝ) ^ (5 / 6 : ℝ) ≤
          maximalCoordinateRotationOrder z.1 →
      SameNormalizedComponent
        (normalizedPuncturedPointExactOrderEulerSeven c) z)
    (hlinear : ∀ d : ℕ,
      (d : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ) →
      24 * (middleGameMaximalOrders p d).card * d < p)
    (hfour : 4 ∣ (puncturedComponentComplementFinset p c).card)
    (hcx : ¬ SamePuncturedComponent c x) :
    ∃ d : ℕ,
      0 < d ∧
      (d : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ) ∧
      8 * p ≤ (combinedTruncatedOrderTotientSum p d) ^ 2 ∧
      d ≤ 189 * (middleGameMaximalOrders p d).card ^ 3 := by
  classical
  have hpTwo : p ≠ 2 := by omega
  letI : Fintype (quadraticFiniteField p) := Fintype.ofFinite _
  let bad := puncturedComponentComplementFinset p c
  have hxBad : x ∈ bad := by
    simpa [bad] using hcx
  have hbadNonempty : bad.Nonempty := ⟨x, hxBad⟩
  let orderMeasure : PuncturedMarkoffSurface (ZMod p) → ℕ := fun w =>
    maximalCoordinateRotationOrder
      (normalizedPuncturedPointExactOrderEulerSeven w).1
  obtain ⟨z, hzBad, hzMax⟩ :=
    Finset.exists_max_image bad orderMeasure hbadNonempty
  let d := orderMeasure z
  have hmax : ∀ w : PuncturedMarkoffSurface (ZMod p),
      w ∈ bad → orderMeasure w ≤ d := by
    intro w hw
    exact hzMax w hw
  have hzNotComponent : ¬ SamePuncturedComponent c z := by
    simpa [bad] using hzBad
  have hdPos : 0 < d := by
    have hfirstPos : 0 <
        rotationOrder
          (normalizedPuncturedPointExactOrderEulerSeven z).1.u1 :=
      rotationOrder_pos _
    exact hfirstPos.trans_le <| by
      simpa [d, orderMeasure] using
        rotationOrder_first_le_maximalCoordinateRotationOrder
          (normalizedPuncturedPointExactOrderEulerSeven z).1
  have hnotBaseZ : ¬ SameNormalizedComponent
      (normalizedPuncturedPointExactOrderEulerSeven c)
      (normalizedPuncturedPointExactOrderEulerSeven z) := by
    intro hcz
    apply hzNotComponent
    exact
      (samePuncturedComponent_iff_sameNormalizedComponent c z).2 hcz
  have hdUpper : (d : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ) := by
    by_contra hd
    apply hnotBaseZ
    apply hlarge (normalizedPuncturedPointExactOrderEulerSeven z)
    simpa [d, orderMeasure] using le_of_not_gt hd
  have hcap :
      d ≤ 189 * (middleGameMaximalOrders p d).card ^ 3 := by
    by_contra hnotCap
    have hcube :
        189 * (middleGameMaximalOrders p d).card ^ 3 < d :=
      Nat.lt_of_not_ge hnotCap
    have hlinearD :
        24 * (middleGameMaximalOrders p d).card * d < p :=
      hlinear d hdUpper
    obtain ⟨y, hzy, hincrease⟩ :=
      exists_sameNormalizedComponent_maximalOrder_increase_of_eulerSevenPairedMaximalDivisorBounds
        p hpTwo (delta := (1 / 3 : ℝ)) (by norm_num)
        (normalizedPuncturedPointExactOrderEulerSeven z)
        (by
          simpa only [
            show (1 / 2 + 1 / 3 : ℝ) = 5 / 6 by norm_num,
            d, orderMeasure] using hdUpper)
        (by simpa [d, orderMeasure] using hcube)
        (by simpa [d, orderMeasure] using hlinearD)
    obtain ⟨g, hg⟩ :=
      (sameNormalizedComponent_iff_exists_gamma
        (normalizedPuncturedPointExactOrderEulerSeven z) y).1 hzy
    let w : PuncturedMarkoffSurface (ZMod p) := g • z
    have hzw : SamePuncturedComponent z w :=
      (samePuncturedComponent_iff_exists z w).2 ⟨g, rfl⟩
    have hwBad : w ∈ bad := by
      rw [show bad = puncturedComponentComplementFinset p c by rfl,
        mem_puncturedComponentComplementFinset_iff]
      intro hcw
      apply hzNotComponent
      exact samePuncturedComponent_trans hcw
        (samePuncturedComponent_symm hzw)
    have hwNormalized :
        normalizedPuncturedPointExactOrderEulerSeven w = y := by
      change normalizedPuncturedPointExactOrderEulerSeven (g • z) = y
      rw [normalizedPuncturedPointExactOrderEulerSeven_smul]
      exact hg
    have hwMax := hmax w hwBad
    change maximalCoordinateRotationOrder
      (normalizedPuncturedPointExactOrderEulerSeven w).1 ≤ d at hwMax
    rw [hwNormalized] at hwMax
    have hincrease' : d < maximalCoordinateRotationOrder y.1 := by
      simpa [d, orderMeasure] using hincrease
    exact (not_lt_of_ge hwMax) hincrease'
  have hbadSmall :
      bad.card ≤
        (puncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders
          p (d + 1)).card := by
    apply Finset.card_le_card
    intro w hwBad
    have hwNotComponent : ¬ SamePuncturedComponent c w := by
      simpa [bad] using hwBad
    have hwNotBase : ¬ SameNormalizedComponent
        (normalizedPuncturedPointExactOrderEulerSeven c)
        (normalizedPuncturedPointExactOrderEulerSeven w) := by
      intro hcw
      apply hwNotComponent
      exact
        (samePuncturedComponent_iff_sameNormalizedComponent c w).2 hcw
    have hnonparabolic :=
      first_two_nonparabolic_of_not_sameComponent_of_endgame_large_connected
        hpTwo
        (normalizedPuncturedPointExactOrderEulerSeven c)
        (normalizedPuncturedPointExactOrderEulerSeven w)
        hlarge hwNotBase
    have hwMax := hmax w hwBad
    have hfirst :
        rotationOrder
            (normalizedPuncturedPointExactOrderEulerSeven w).1.u1 ≤ d :=
      (rotationOrder_first_le_maximalCoordinateRotationOrder
        (normalizedPuncturedPointExactOrderEulerSeven w).1).trans hwMax
    have hsecond :
        rotationOrder
            (normalizedPuncturedPointExactOrderEulerSeven w).1.u2 ≤ d :=
      (rotationOrder_second_le_maximalCoordinateRotationOrder
        (normalizedPuncturedPointExactOrderEulerSeven w).1).trans hwMax
    change w ∈
      puncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders
        p (d + 1)
    rw [
      puncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders,
      mem_originalPuncturedFinsetOfNormalized_iff,
      mem_normalizedPuncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders_iff
    ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [normalizedPuncturedPointExactOrderEulerSeven,
        normalizedSurfaceOfPunctured,
        puncturedNormalizationEquiv_coe] using Nat.lt_succ_of_le hfirst
    · simpa only [normalizedPuncturedPointExactOrderEulerSeven,
        normalizedSurfaceOfPunctured,
        puncturedNormalizationEquiv_coe] using Nat.lt_succ_of_le hsecond
    · simpa only [normalizedPuncturedPointExactOrderEulerSeven,
        normalizedSurfaceOfPunctured,
        puncturedNormalizationEquiv_coe] using hnonparabolic.1
    · simpa only [normalizedPuncturedPointExactOrderEulerSeven,
        normalizedSurfaceOfPunctured,
        puncturedNormalizationEquiv_coe] using hnonparabolic.2
  have hfourPLeBad : 4 * p ≤ bad.card := by
    apply four_mul_prime_le_puncturedComponentComplementFinset_card
      p hpThree c
    · simpa [bad] using hbadNonempty
    · exact hfour
  have hrootObstruction :
      8 * p ≤ (combinedTruncatedOrderTotientSum p d) ^ 2 := by
    calc
      8 * p = 2 * (4 * p) := by ring
      _ ≤ 2 * bad.card := Nat.mul_le_mul_left 2 hfourPLeBad
      _ ≤ 2 *
          (puncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders
            p (d + 1)).card :=
        Nat.mul_le_mul_left 2 hbadSmall
      _ ≤ (combinedTruncatedOrderTotientSum p d) ^ 2 :=
        two_mul_puncturedSmallNonparabolicOrder_succ_card_le_rootSumSq
          hpTwo d
  exact ⟨d, hdPos, hdUpper, hrootObstruction, hcap⟩

/-- Global nontransitivity forces one common exact-order/Euler-seven witness,
not two independently chosen orders. -/
theorem
    exists_exactOrderRootSum_eulerSevenCap_of_not_puncturedTransitive
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpThree : 3 < p)
    (c : PuncturedMarkoffSurface (ZMod p))
    (hlarge : ∀ z : NormalizedMarkoffSurface (ZMod p),
      (p : ℝ) ^ (5 / 6 : ℝ) ≤
          maximalCoordinateRotationOrder z.1 →
      SameNormalizedComponent
        (normalizedPuncturedPointExactOrderEulerSeven c) z)
    (hlinear : ∀ d : ℕ,
      (d : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ) →
      24 * (middleGameMaximalOrders p d).card * d < p)
    (hfour : 4 ∣ (puncturedComponentComplementFinset p c).card)
    (hnotTransitive : ¬ PuncturedMarkoffTransitiveAt p Fact.out) :
    ∃ d : ℕ,
      0 < d ∧
      (d : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ) ∧
      8 * p ≤ (combinedTruncatedOrderTotientSum p d) ^ 2 ∧
      d ≤ 189 * (middleGameMaximalOrders p d).card ^ 3 := by
  have hexists :
      ∃ x : PuncturedMarkoffSurface (ZMod p),
        ¬ SamePuncturedComponent c x := by
    by_contra hnone
    have hAll : ∀ x : PuncturedMarkoffSurface (ZMod p),
        SamePuncturedComponent c x := by
      intro x
      by_contra hx
      exact hnone ⟨x, hx⟩
    apply hnotTransitive
    intro a b
    obtain ⟨ga, hga⟩ :=
      (samePuncturedComponent_iff_exists c a).1 (hAll a)
    obtain ⟨gb, hgb⟩ :=
      (samePuncturedComponent_iff_exists c b).1 (hAll b)
    refine ⟨gb * ga⁻¹, ?_⟩
    calc
      (gb * ga⁻¹) • a = gb • (ga⁻¹ • a) := mul_smul _ _ _
      _ = gb • c := by rw [← hga]; simp
      _ = b := hgb
  obtain ⟨x, hx⟩ := hexists
  exact
    exists_exactOrderRootSum_eulerSevenCap_of_not_samePuncturedComponent
      p hpThree c x hlarge hlinear hfour hx

end

end BGS.Markoff
