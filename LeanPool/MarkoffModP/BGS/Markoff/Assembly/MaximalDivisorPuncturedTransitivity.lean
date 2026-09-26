/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.ExplicitPuncturedTransitivity
public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.MaximalDivisorLowOrderCount
public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.MaximalDivisorMiddleGame

/-!
# Punctured transitivity from the maximal-divisor frontier

The maximal-orbit argument now uses the same maximal-divisor count in both
places where the published proof used all divisors:

* counting points whose first two rotation orders are small;
* the Corvaja--Zannier union that forces an order increase.

This is the idea-level endpoint.  A separate arithmetic certificate can
discharge its two explicit inequalities using the joint `p - 1`, `p + 1`
square envelope.
-/

@[expose] public section

namespace BGS.Markoff

noncomputable section

private def normalizedPuncturedPointMaximalDivisors
    {R : Type*} [Field R] [Invertible (3 : R)]
    (x : PuncturedMarkoffSurface R) : NormalizedMarkoffSurface R :=
  normalizedSurfaceOfPunctured (puncturedNormalizationEquiv R x)

private theorem normalizedPuncturedPointMaximalDivisors_smul
    {R : Type*} [Field R] [Invertible (3 : R)]
    (g : Gamma R) (z : PuncturedMarkoffSurface R) :
    normalizedPuncturedPointMaximalDivisors (g • z) =
      normalizedGammaPerm R g
        (normalizedPuncturedPointMaximalDivisors z) := by
  have hzinv :
      (normalizationSurfaceEquiv R).symm
          (normalizedSurfaceOfPunctured
            (puncturedNormalizationEquiv R z)) = z.1 := by
    apply Subtype.ext
    exact (normalizationEquiv R).symm_apply_apply z.1.1
  unfold normalizedPuncturedPointMaximalDivisors
  rw [normalizedGammaPerm_apply, hzinv]
  apply Subtype.ext
  rfl

/-- The finite maximal-orbit argument with maximal-divisor counts at both
small-order and middle-game boundaries. -/
theorem puncturedMarkoffTransitiveAt_of_maximalDivisor_frontier
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpThree : 3 < p)
    (c : PuncturedMarkoffSurface (ZMod p))
    (hcube : ∀ d : ℕ, 0 < d →
      p ≤ 2 * (2 + d * maximalDivisorCountSum p (d + 1)) ^ 2 →
      (corvajaZannierCorollaryTwoSafeCoefficient *
        maximalDivisorCountSum p (d + 1)) ^ 3 < d)
    (hlinear : ∀ d : ℕ,
      (d : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ) →
      corvajaZannierCorollaryTwoSafeCoefficient *
        maximalDivisorCountSum p (d + 1) * d < p)
    (hlarge : ∀ z : NormalizedMarkoffSurface (ZMod p),
      (p : ℝ) ^ (5 / 6 : ℝ) ≤
          maximalCoordinateRotationOrder z.1 →
      SameNormalizedComponent
        (normalizedSurfaceOfPunctured (puncturedNormalizationEquiv (ZMod p) c)) z) :
    PuncturedMarkoffTransitiveAt p Fact.out := by
  classical
  have hpTwo : p ≠ 2 := by omega
  letI : Fintype (quadraticFiniteField p) := Fintype.ofFinite _
  have hAll : ∀ x : PuncturedMarkoffSurface (ZMod p),
      SamePuncturedComponent c x := by
    intro x
    by_contra hcx
    let orderMeasure : PuncturedMarkoffSurface (ZMod p) → ℕ := fun w =>
      maximalCoordinateRotationOrder
        (normalizedPuncturedPointMaximalDivisors w).1
    let orbitFinset := (puncturedGammaOrbit x).toFinite.toFinset
    have hxMem : x ∈ orbitFinset := by
      have hxOrbit : x ∈ puncturedGammaOrbit x :=
        samePuncturedComponent_refl x
      simpa [orbitFinset] using hxOrbit
    obtain ⟨z, hzMem, hzMax⟩ :=
      Finset.exists_max_image orbitFinset orderMeasure ⟨x, hxMem⟩
    let d := orderMeasure z
    have hzComponent : SamePuncturedComponent x z := by
      change z ∈ puncturedGammaOrbit x
      simpa [orbitFinset] using hzMem
    have hmax : ∀ w : PuncturedMarkoffSurface (ZMod p),
        SamePuncturedComponent x w → orderMeasure w ≤ d := by
      intro w hw
      apply hzMax w
      change w ∈ puncturedGammaOrbit x at hw
      simpa [orbitFinset] using hw
    have hdPos : 0 < d := by
      have hfirstPos : 0 <
          rotationOrder
            (normalizedPuncturedPointMaximalDivisors z).1.u1 :=
        rotationOrder_pos _
      exact hfirstPos.trans_le <| by
        simpa [d, orderMeasure] using
          rotationOrder_first_le_maximalCoordinateRotationOrder
            (normalizedPuncturedPointMaximalDivisors z).1
    have hnotBaseZ : ¬ SameNormalizedComponent
        (normalizedPuncturedPointMaximalDivisors c)
        (normalizedPuncturedPointMaximalDivisors z) := by
      intro hcz
      apply hcx
      have hczPunctured : SamePuncturedComponent c z :=
        (samePuncturedComponent_iff_sameNormalizedComponent c z).2 hcz
      exact samePuncturedComponent_trans hczPunctured
        (samePuncturedComponent_symm hzComponent)
    have hdUpper : (d : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ) := by
      by_contra hd
      apply hnotBaseZ
      apply hlarge (normalizedPuncturedPointMaximalDivisors z)
      simpa [d, orderMeasure] using le_of_not_gt hd
    have hpLeOrbit : p ≤ (puncturedGammaOrbit x).ncard := by
      have horbitPos : 0 < (puncturedGammaOrbit x).ncard :=
        (Set.ncard_pos (Set.toFinite _)).2
          ⟨x, samePuncturedComponent_refl x⟩
      exact Nat.le_of_dvd horbitPos
        (prime_dvd_puncturedGammaOrbit_ncard p hpThree x)
    have horbitSmall : (puncturedGammaOrbit x).ncard ≤
        (puncturedMarkoffPointsWithSmallFirstTwoRotationOrders
          p (d + 1)).card := by
      rw [Set.ncard_eq_toFinset_card
        (puncturedGammaOrbit x) (Set.toFinite _)]
      apply Finset.card_le_card
      intro w hwFinset
      have hw : SamePuncturedComponent x w := by
        change w ∈ puncturedGammaOrbit x
        simpa [orbitFinset] using hwFinset
      have hwMax := hmax w hw
      have hfirst :
          rotationOrder
              (normalizedPuncturedPointMaximalDivisors w).1.u1 ≤ d :=
        (rotationOrder_first_le_maximalCoordinateRotationOrder
          (normalizedPuncturedPointMaximalDivisors w).1).trans hwMax
      have hsecond :
          rotationOrder
              (normalizedPuncturedPointMaximalDivisors w).1.u2 ≤ d :=
        (rotationOrder_second_le_maximalCoordinateRotationOrder
          (normalizedPuncturedPointMaximalDivisors w).1).trans hwMax
      change w ∈
        puncturedMarkoffPointsWithSmallFirstTwoRotationOrders p (d + 1)
      rw [puncturedMarkoffPointsWithSmallFirstTwoRotationOrders,
        mem_originalPuncturedFinsetOfNormalized_iff,
        mem_normalizedPuncturedMarkoffPointsWithSmallFirstTwoRotationOrders_iff]
      constructor
      · simpa only [normalizedPuncturedPointMaximalDivisors,
          normalizedSurfaceOfPunctured,
          puncturedNormalizationEquiv_coe] using
            Nat.lt_succ_of_le hfirst
      · simpa only [normalizedPuncturedPointMaximalDivisors,
          normalizedSurfaceOfPunctured,
          puncturedNormalizationEquiv_coe] using
            Nat.lt_succ_of_le hsecond
    have hpLeSmallOrderSet : p ≤
        2 * (2 + d * maximalDivisorCountSum p (d + 1)) ^ 2 := by
      calc
        p ≤ (puncturedGammaOrbit x).ncard := hpLeOrbit
        _ ≤ (puncturedMarkoffPointsWithSmallFirstTwoRotationOrders
            p (d + 1)).card := horbitSmall
        _ ≤ 2 * (2 + d *
            maximalDivisorCountSum p (d + 1)) ^ 2 :=
          puncturedMarkoffPointsWithSmallFirstTwoRotationOrders_succ_card_le_maximalDivisors
            hpTwo d
    have hcubeCount :=
      hcube d hdPos hpLeSmallOrderSet
    have hlinearCount := hlinear d hdUpper
    have hmaximalCard :
        (middleGameMaximalOrders p d).card ≤
          maximalDivisorCountSum p (d + 1) := by
      simpa [maximalDivisorCountSum] using
        middleGameMaximalOrders_card_le p d
    have hcoefficient :
        corvajaZannierCorollaryTwoSafeCoefficient *
            (middleGameMaximalOrders p d).card ≤
          corvajaZannierCorollaryTwoSafeCoefficient *
            maximalDivisorCountSum p (d + 1) :=
      Nat.mul_le_mul_left
        corvajaZannierCorollaryTwoSafeCoefficient hmaximalCard
    have hcube' :
        (corvajaZannierCorollaryTwoSafeCoefficient *
          (middleGameMaximalOrders p d).card) ^ 3 < d :=
      (Nat.pow_le_pow_left hcoefficient 3).trans_lt hcubeCount
    have hlinear' :
        corvajaZannierCorollaryTwoSafeCoefficient *
          (middleGameMaximalOrders p d).card * d < p :=
      (Nat.mul_le_mul_right d hcoefficient).trans_lt hlinearCount
    obtain ⟨y, hzy, hincrease⟩ :=
      exists_sameNormalizedComponent_maximalOrder_increase_of_maximalDivisorBounds
        p hpTwo (delta := (1 / 3 : ℝ)) (by norm_num)
        (corvajaZannierWeightedTraceBound p (quadraticFiniteField p))
        (normalizedPuncturedPointMaximalDivisors z)
        (by simpa only [show (1 / 2 + 1 / 3 : ℝ) = 5 / 6 by norm_num,
            d, orderMeasure] using hdUpper)
        (by simpa [d, orderMeasure] using hcube')
        (by simpa [d, orderMeasure] using hlinear')
    obtain ⟨g, hg⟩ :=
      (sameNormalizedComponent_iff_exists_gamma
        (normalizedPuncturedPointMaximalDivisors z) y).1 hzy
    let w : PuncturedMarkoffSurface (ZMod p) := g • z
    have hwComponent : SamePuncturedComponent x w :=
      samePuncturedComponent_trans hzComponent
        ((samePuncturedComponent_iff_exists z w).2 ⟨g, rfl⟩)
    have hwNormalized :
        normalizedPuncturedPointMaximalDivisors w = y := by
      change normalizedPuncturedPointMaximalDivisors (g • z) = y
      rw [normalizedPuncturedPointMaximalDivisors_smul]
      exact hg
    have hwMax := hmax w hwComponent
    change maximalCoordinateRotationOrder
      (normalizedPuncturedPointMaximalDivisors w).1 ≤ d at hwMax
    rw [hwNormalized] at hwMax
    have hincrease' : d < maximalCoordinateRotationOrder y.1 := by
      simpa [d, orderMeasure] using hincrease
    exact (not_lt_of_ge hwMax) hincrease'
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

end

end BGS.Markoff
