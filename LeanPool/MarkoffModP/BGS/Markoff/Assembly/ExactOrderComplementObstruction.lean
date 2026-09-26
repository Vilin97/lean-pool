/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.ExactOrderPuncturedSmallOrderCount
public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.NonparabolicComplementFrontier

/-!
# Exact-order root obstruction from a nontransitive complement

With the root-sum convention

`R = Σ_{e ∣ p-1, 2<e≤d} φ(e) + Σ_{e ∣ p+1, 2<e≤d} φ(e)`,

inversion gives `2 * |trace values| ≤ R`.  The two-coordinate Markoff fiber
bound and the factor-four complement divisibility therefore force
`8 * p ≤ R^2` whenever the complement survives below the endgame threshold.
-/

@[expose] public section

namespace BGS.Markoff

noncomputable section

private def normalizedPuncturedPointExactOrderComplement
    {R : Type*} [Field R] [Invertible (3 : R)]
    (x : PuncturedMarkoffSurface R) : NormalizedMarkoffSurface R :=
  normalizedSurfaceOfPunctured (puncturedNormalizationEquiv R x)

/-- A point outside the base component produces an exact root-sum
obstruction at the maximal rotation order in the complement. -/
theorem exists_exactOrderRootSum_obstruction_of_not_samePuncturedComponent
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpThree : 3 < p)
    (c x : PuncturedMarkoffSurface (ZMod p))
    (hlarge : ∀ z : NormalizedMarkoffSurface (ZMod p),
      (p : ℝ) ^ (5 / 6 : ℝ) ≤
          maximalCoordinateRotationOrder z.1 →
      SameNormalizedComponent
        (normalizedSurfaceOfPunctured (puncturedNormalizationEquiv (ZMod p) c)) z)
    (hfour : 4 ∣ (puncturedComponentComplementFinset p c).card)
    (hcx : ¬ SamePuncturedComponent c x) :
    ∃ d : ℕ,
      0 < d ∧
      (d : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ) ∧
      8 * p ≤ (combinedTruncatedOrderTotientSum p d) ^ 2 := by
  classical
  have hpTwo : p ≠ 2 := by omega
  let : Fintype (quadraticFiniteField p) := Fintype.ofFinite _
  let bad := puncturedComponentComplementFinset p c
  have hxBad : x ∈ bad := by
    simpa [bad] using hcx
  have hbadNonempty : bad.Nonempty := ⟨x, hxBad⟩
  let orderMeasure : PuncturedMarkoffSurface (ZMod p) → ℕ := fun w =>
    maximalCoordinateRotationOrder
      (normalizedPuncturedPointExactOrderComplement w).1
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
          (normalizedPuncturedPointExactOrderComplement z).1.u1 :=
      rotationOrder_pos _
    exact hfirstPos.trans_le <| by
      simpa [d, orderMeasure] using
        rotationOrder_first_le_maximalCoordinateRotationOrder
          (normalizedPuncturedPointExactOrderComplement z).1
  have hnotBaseZ : ¬ SameNormalizedComponent
      (normalizedPuncturedPointExactOrderComplement c)
      (normalizedPuncturedPointExactOrderComplement z) := by
    intro hcz
    apply hzNotComponent
    exact
      (samePuncturedComponent_iff_sameNormalizedComponent c z).2 hcz
  have hdUpper : (d : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ) := by
    by_contra hd
    apply hnotBaseZ
    apply hlarge (normalizedPuncturedPointExactOrderComplement z)
    simpa [d, orderMeasure] using le_of_not_gt hd
  have hbadSmall :
      bad.card ≤
        (puncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders
          p (d + 1)).card := by
    apply Finset.card_le_card
    intro w hwBad
    have hwNotComponent : ¬ SamePuncturedComponent c w := by
      simpa [bad] using hwBad
    have hwNotBase : ¬ SameNormalizedComponent
        (normalizedPuncturedPointExactOrderComplement c)
        (normalizedPuncturedPointExactOrderComplement w) := by
      intro hcw
      apply hwNotComponent
      exact
        (samePuncturedComponent_iff_sameNormalizedComponent c w).2 hcw
    have hnonparabolic :=
      first_two_nonparabolic_of_not_sameComponent_of_endgame_large_connected
        hpTwo
        (normalizedPuncturedPointExactOrderComplement c)
        (normalizedPuncturedPointExactOrderComplement w)
        hlarge hwNotBase
    have hwMax := hmax w hwBad
    have hfirst :
        rotationOrder
            (normalizedPuncturedPointExactOrderComplement w).1.u1 ≤ d :=
      (rotationOrder_first_le_maximalCoordinateRotationOrder
        (normalizedPuncturedPointExactOrderComplement w).1).trans hwMax
    have hsecond :
        rotationOrder
            (normalizedPuncturedPointExactOrderComplement w).1.u2 ≤ d :=
      (rotationOrder_second_le_maximalCoordinateRotationOrder
        (normalizedPuncturedPointExactOrderComplement w).1).trans hwMax
    change w ∈
      puncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders
        p (d + 1)
    rw [
      puncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders,
      mem_originalPuncturedFinsetOfNormalized_iff,
      mem_normalizedPuncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders_iff
    ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [normalizedPuncturedPointExactOrderComplement,
        normalizedSurfaceOfPunctured,
        puncturedNormalizationEquiv_coe] using Nat.lt_succ_of_le hfirst
    · simpa only [normalizedPuncturedPointExactOrderComplement,
        normalizedSurfaceOfPunctured,
        puncturedNormalizationEquiv_coe] using Nat.lt_succ_of_le hsecond
    · simpa only [normalizedPuncturedPointExactOrderComplement,
        normalizedSurfaceOfPunctured,
        puncturedNormalizationEquiv_coe] using hnonparabolic.1
    · simpa only [normalizedPuncturedPointExactOrderComplement,
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
  exact ⟨d, hdPos, hdUpper, hrootObstruction⟩

/-- Global nontransitivity forces an exact root-sum obstruction below the
large-order endgame threshold. -/
theorem exists_exactOrderRootSum_obstruction_of_not_puncturedTransitive
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpThree : 3 < p)
    (c : PuncturedMarkoffSurface (ZMod p))
    (hlarge : ∀ z : NormalizedMarkoffSurface (ZMod p),
      (p : ℝ) ^ (5 / 6 : ℝ) ≤
          maximalCoordinateRotationOrder z.1 →
      SameNormalizedComponent
        (normalizedSurfaceOfPunctured (puncturedNormalizationEquiv (ZMod p) c)) z)
    (hfour : 4 ∣ (puncturedComponentComplementFinset p c).card)
    (hnotTransitive : ¬ PuncturedMarkoffTransitiveAt p Fact.out) :
    ∃ d : ℕ,
      0 < d ∧
      (d : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ) ∧
      8 * p ≤ (combinedTruncatedOrderTotientSum p d) ^ 2 := by
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
    exists_exactOrderRootSum_obstruction_of_not_samePuncturedComponent
      p hpThree c x hlarge hfour hx

end

end BGS.Markoff
