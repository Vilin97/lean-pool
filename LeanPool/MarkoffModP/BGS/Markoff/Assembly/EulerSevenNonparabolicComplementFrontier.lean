/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Assembly.NonparabolicComplementFrontier
import LeanPool.MarkoffModP.BGS.Markoff.Assembly.EulerSevenPairedMaximalDivisorMiddleGame

/-!
# Euler-seven nonparabolic complement frontier

This is the complement-maximal argument with the exact paired
Euler-characteristic middle-game condition `189 * M^3 < d`.
-/

namespace BGS.Markoff

open BGS.NumberTheory

noncomputable section

private def normalizedPuncturedPointEulerSevenComplement
    {R : Type*} [Field R] [Invertible (3 : R)]
    (x : PuncturedMarkoffSurface R) : NormalizedMarkoffSurface R :=
  normalizedSurfaceOfPunctured (puncturedNormalizationEquiv R x)

private theorem normalizedPuncturedPointEulerSevenComplement_smul
    {R : Type*} [Field R] [Invertible (3 : R)]
    (g : Gamma R) (z : PuncturedMarkoffSurface R) :
    normalizedPuncturedPointEulerSevenComplement (g • z) =
      normalizedGammaPerm R g
        (normalizedPuncturedPointEulerSevenComplement z) := by
  have hzinv :
      (normalizationSurfaceEquiv R).symm
          (normalizedSurfaceOfPunctured
            (puncturedNormalizationEquiv R z)) = z.1 := by
    apply Subtype.ext
    exact (normalizationEquiv R).symm_apply_apply z.1.1
  unfold normalizedPuncturedPointEulerSevenComplement
  rw [normalizedGammaPerm_apply, hzinv]
  apply Subtype.ext
  rfl

/-- Complement-maximal frontier with the exact Euler-seven paired
Corvaja--Zannier coefficient. The sign-invariance and factor-four inputs
remain explicit. -/
theorem
    puncturedMarkoffTransitiveAt_of_nonparabolicComplement_eulerSevenPairedMaximalDivisor_frontier
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpThree : 3 < p)
    (c : PuncturedMarkoffSurface (ZMod p))
    (hcube : ∀ d : ℕ, 0 < d →
      8 * p ≤
        (d * maximalDivisorCountSum p (d + 1)) ^ 2 →
      189 * maximalDivisorCountSum p (d + 1) ^ 3 < d)
    (hlinear : ∀ d : ℕ,
      (d : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ) →
      24 * maximalDivisorCountSum p (d + 1) * d < p)
    (hlarge : ∀ z : NormalizedMarkoffSurface (ZMod p),
      (p : ℝ) ^ (5 / 6 : ℝ) ≤
          maximalCoordinateRotationOrder z.1 →
      SameNormalizedComponent
        (normalizedPuncturedPointEulerSevenComplement c) z)
    (hsign : ∀ (s : EvenSign)
        (x : PuncturedMarkoffSurface (ZMod p)),
      s • x ∈ puncturedComponentComplementFinset p c ↔
        x ∈ puncturedComponentComplementFinset p c)
    (hfour : 4 ∣ (puncturedComponentComplementFinset p c).card) :
    PuncturedMarkoffTransitiveAt p Fact.out := by
  classical
  have hpTwo : p ≠ 2 := by omega
  let : Fintype (quadraticFiniteField p) := Fintype.ofFinite _
  have hAll : ∀ x : PuncturedMarkoffSurface (ZMod p),
      SamePuncturedComponent c x := by
    intro x
    by_contra hcx
    let bad := puncturedComponentComplementFinset p c
    have hxBad : x ∈ bad := by
      simpa [bad] using hcx
    have hbadNonempty : bad.Nonempty := by
      refine ⟨(1 : EvenSign) • x, ?_⟩
      exact (by simpa [bad] using (hsign (1 : EvenSign) x).2 hxBad)
    let orderMeasure : PuncturedMarkoffSurface (ZMod p) → ℕ := fun w =>
      maximalCoordinateRotationOrder
        (normalizedPuncturedPointEulerSevenComplement w).1
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
            (normalizedPuncturedPointEulerSevenComplement z).1.u1 :=
        rotationOrder_pos _
      exact hfirstPos.trans_le <| by
        simpa [d, orderMeasure] using
          rotationOrder_first_le_maximalCoordinateRotationOrder
            (normalizedPuncturedPointEulerSevenComplement z).1
    have hnotBaseZ : ¬ SameNormalizedComponent
        (normalizedPuncturedPointEulerSevenComplement c)
        (normalizedPuncturedPointEulerSevenComplement z) := by
      intro hcz
      apply hzNotComponent
      exact
        (samePuncturedComponent_iff_sameNormalizedComponent c z).2 hcz
    have hdUpper : (d : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ) := by
      by_contra hd
      apply hnotBaseZ
      apply hlarge (normalizedPuncturedPointEulerSevenComplement z)
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
          (normalizedPuncturedPointEulerSevenComplement c)
          (normalizedPuncturedPointEulerSevenComplement w) := by
        intro hcw
        apply hwNotComponent
        exact
          (samePuncturedComponent_iff_sameNormalizedComponent c w).2 hcw
      have hnonparabolic :=
        first_two_nonparabolic_of_not_sameComponent_of_endgame_large_connected
          hpTwo
          (normalizedPuncturedPointEulerSevenComplement c)
          (normalizedPuncturedPointEulerSevenComplement w)
          hlarge hwNotBase
      have hwMax := hmax w hwBad
      have hfirst :
          rotationOrder
              (normalizedPuncturedPointEulerSevenComplement w).1.u1 ≤ d :=
        (rotationOrder_first_le_maximalCoordinateRotationOrder
          (normalizedPuncturedPointEulerSevenComplement w).1).trans hwMax
      have hsecond :
          rotationOrder
              (normalizedPuncturedPointEulerSevenComplement w).1.u2 ≤ d :=
        (rotationOrder_second_le_maximalCoordinateRotationOrder
          (normalizedPuncturedPointEulerSevenComplement w).1).trans hwMax
      change w ∈
        puncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders
          p (d + 1)
      rw [
        puncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders,
        mem_originalPuncturedFinsetOfNormalized_iff,
        mem_normalizedPuncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders_iff
      ]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [normalizedPuncturedPointEulerSevenComplement,
          normalizedSurfaceOfPunctured,
          puncturedNormalizationEquiv_coe] using Nat.lt_succ_of_le hfirst
      · simpa only [normalizedPuncturedPointEulerSevenComplement,
          normalizedSurfaceOfPunctured,
          puncturedNormalizationEquiv_coe] using Nat.lt_succ_of_le hsecond
      · simpa only [normalizedPuncturedPointEulerSevenComplement,
          normalizedSurfaceOfPunctured,
          puncturedNormalizationEquiv_coe] using hnonparabolic.1
      · simpa only [normalizedPuncturedPointEulerSevenComplement,
          normalizedSurfaceOfPunctured,
          puncturedNormalizationEquiv_coe] using hnonparabolic.2
    have hfourPLeBad : 4 * p ≤ bad.card := by
      apply four_mul_prime_le_puncturedComponentComplementFinset_card
        p hpThree c
      · simpa [bad] using hbadNonempty
      · exact hfour
    have heightPLeSmallOrderSquare :
        8 * p ≤
          (d * maximalDivisorCountSum p (d + 1)) ^ 2 := by
      calc
        8 * p = 2 * (4 * p) := by ring
        _ ≤ 2 * bad.card := Nat.mul_le_mul_left 2 hfourPLeBad
        _ ≤ 2 *
            (puncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders
              p (d + 1)).card :=
          Nat.mul_le_mul_left 2 hbadSmall
        _ ≤ (d * maximalDivisorCountSum p (d + 1)) ^ 2 :=
          two_mul_puncturedSmallNonparabolicOrder_succ_card_le_maximalDivisors
            hpTwo d
    have hcubeCount := hcube d hdPos heightPLeSmallOrderSquare
    have hlinearCount := hlinear d hdUpper
    have hmaximalCard :
        (middleGameMaximalOrders p d).card ≤
          maximalDivisorCountSum p (d + 1) := by
      simpa [maximalDivisorCountSum] using
        middleGameMaximalOrders_card_le p d
    have hcube' :
        189 * (middleGameMaximalOrders p d).card ^ 3 < d := by
      apply lt_of_le_of_lt _ hcubeCount
      gcongr
    have hlinearCoefficient :
        24 * (middleGameMaximalOrders p d).card ≤
          24 * maximalDivisorCountSum p (d + 1) :=
      Nat.mul_le_mul_left 24 hmaximalCard
    have hlinear' :
        24 * (middleGameMaximalOrders p d).card * d < p :=
      (Nat.mul_le_mul_right d hlinearCoefficient).trans_lt hlinearCount
    obtain ⟨y, hzy, hincrease⟩ :=
      exists_sameNormalizedComponent_maximalOrder_increase_of_eulerSevenPairedMaximalDivisorBounds
        p hpTwo (delta := (1 / 3 : ℝ)) (by norm_num)
        (normalizedPuncturedPointEulerSevenComplement z)
        (by simpa only [show (1 / 2 + 1 / 3 : ℝ) = 5 / 6 by norm_num,
            d, orderMeasure] using hdUpper)
        (by simpa [d, orderMeasure] using hcube')
        (by simpa [d, orderMeasure] using hlinear')
    obtain ⟨g, hg⟩ :=
      (sameNormalizedComponent_iff_exists_gamma
        (normalizedPuncturedPointEulerSevenComplement z) y).1 hzy
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
        normalizedPuncturedPointEulerSevenComplement w = y := by
      change normalizedPuncturedPointEulerSevenComplement (g • z) = y
      rw [normalizedPuncturedPointEulerSevenComplement_smul]
      exact hg
    have hwMax := hmax w hwBad
    change maximalCoordinateRotationOrder
      (normalizedPuncturedPointEulerSevenComplement w).1 ≤ d at hwMax
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
