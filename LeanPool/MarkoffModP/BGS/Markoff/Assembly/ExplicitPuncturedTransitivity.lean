/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Assembly.GiantOrbit
import LeanPool.MarkoffModP.BGS.Markoff.Assembly.OrbitDivisibility
import LeanPool.MarkoffModP.BGS.Markoff.ExplicitEndgame
import LeanPool.MarkoffModP.BGS.Markoff.ExplicitNumericCertificates
import LeanPool.MarkoffModP.BGS.Markoff.PreliminaryEndgame

/-!
# Explicit punctured transitivity

This file isolates the finite maximal-orbit argument used by the explicit
punctured-transitivity proof. The only geometric input is a stated
large-order-to-base-component hypothesis; the middle-game step is the proved
Corvaja--Zannier escape theorem.
-/

namespace BGS.Markoff

noncomputable section

/-- The normalized surface point underlying an original punctured point. -/
private def normalizedPuncturedPoint
    {R : Type*} [Field R] [Invertible (3 : R)]
    (x : PuncturedMarkoffSurface R) : NormalizedMarkoffSurface R :=
  normalizedSurfaceOfPunctured (puncturedNormalizationEquiv R x)

/-- Normalizing an original punctured point intertwines the two `Gamma`
actions. -/
private theorem normalizedPuncturedPoint_smul
    {R : Type*} [Field R] [Invertible (3 : R)]
    (g : Gamma R) (z : PuncturedMarkoffSurface R) :
    normalizedPuncturedPoint (g • z) =
      normalizedGammaPerm R g (normalizedPuncturedPoint z) := by
  have hzinv :
      (normalizationSurfaceEquiv R).symm
          (normalizedSurfaceOfPunctured (puncturedNormalizationEquiv R z)) = z.1 := by
    apply Subtype.ext
    exact (normalizationEquiv R).symm_apply_apply z.1.1
  unfold normalizedPuncturedPoint
  rw [normalizedGammaPerm_apply, hzinv]
  apply Subtype.ext
  rfl

/-- The finite maximal-orbit argument at a fixed prime.  The hypotheses expose
exactly the three frontiers consumed by the argument: the divisor-sensitive
count forces the cubic middle-game bound, the upper range supplies the linear
bound, and large order connects to one base component. -/
theorem puncturedMarkoffTransitiveAt_of_maximalOrbit_frontier
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)] (hpThree : 3 < p)
    (c : PuncturedMarkoffSurface (ZMod p))
    (hcube : ∀ d : ℕ, 0 < d →
      p ≤ 2 * (2 + d *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 2 →
      (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 < d)
    (hlinear : ∀ d : ℕ,
      (d : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ) →
      corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) * d < p)
    (hlarge : ∀ z : NormalizedMarkoffSurface (ZMod p),
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ maximalCoordinateRotationOrder z.1 →
      SameNormalizedComponent (normalizedPuncturedPoint c) z) :
    PuncturedMarkoffTransitiveAt p Fact.out := by
  classical
  have hpTwo : p ≠ 2 := by omega
  letI : Fintype (quadraticFiniteField p) := Fintype.ofFinite _
  have hAll : ∀ x : PuncturedMarkoffSurface (ZMod p),
      SamePuncturedComponent c x := by
    intro x
    by_contra hcx
    let orderMeasure : PuncturedMarkoffSurface (ZMod p) → ℕ := fun w =>
      maximalCoordinateRotationOrder (normalizedPuncturedPoint w).1
    let orbitFinset := (puncturedGammaOrbit x).toFinite.toFinset
    have hxMem : x ∈ orbitFinset := by
      have hxOrbit : x ∈ puncturedGammaOrbit x := samePuncturedComponent_refl x
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
      have hfirstPos : 0 < rotationOrder (normalizedPuncturedPoint z).1.u1 :=
        rotationOrder_pos _
      exact hfirstPos.trans_le <| by
        simpa [d, orderMeasure] using
          rotationOrder_first_le_maximalCoordinateRotationOrder
            (normalizedPuncturedPoint z).1
    have hnotBaseZ : ¬ SameNormalizedComponent
        (normalizedPuncturedPoint c) (normalizedPuncturedPoint z) := by
      intro hcz
      apply hcx
      have hczPunctured : SamePuncturedComponent c z :=
        (samePuncturedComponent_iff_sameNormalizedComponent c z).2 hcz
      exact samePuncturedComponent_trans hczPunctured
        (samePuncturedComponent_symm hzComponent)
    have hdUpper : (d : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ) := by
      by_contra hd
      apply hnotBaseZ
      apply hlarge (normalizedPuncturedPoint z)
      simpa [d, orderMeasure] using le_of_not_gt hd
    have hpLeOrbit : p ≤ (puncturedGammaOrbit x).ncard := by
      have horbitPos : 0 < (puncturedGammaOrbit x).ncard :=
        (Set.ncard_pos (Set.toFinite _)).2 ⟨x, samePuncturedComponent_refl x⟩
      exact Nat.le_of_dvd horbitPos
        (prime_dvd_puncturedGammaOrbit_ncard p hpThree x)
    have horbitSmall : (puncturedGammaOrbit x).ncard ≤
        (puncturedMarkoffPointsWithSmallFirstTwoRotationOrders p (d + 1)).card := by
      rw [Set.ncard_eq_toFinset_card (puncturedGammaOrbit x) (Set.toFinite _)]
      apply Finset.card_le_card
      intro w hwFinset
      have hw : SamePuncturedComponent x w := by
        change w ∈ puncturedGammaOrbit x
        simpa [orbitFinset] using hwFinset
      have hwMax := hmax w hw
      have hfirst : rotationOrder (normalizedPuncturedPoint w).1.u1 ≤ d :=
        (rotationOrder_first_le_maximalCoordinateRotationOrder
          (normalizedPuncturedPoint w).1).trans hwMax
      have hsecond : rotationOrder (normalizedPuncturedPoint w).1.u2 ≤ d :=
        (rotationOrder_second_le_maximalCoordinateRotationOrder
          (normalizedPuncturedPoint w).1).trans hwMax
      change w ∈ puncturedMarkoffPointsWithSmallFirstTwoRotationOrders p (d + 1)
      rw [puncturedMarkoffPointsWithSmallFirstTwoRotationOrders,
        mem_originalPuncturedFinsetOfNormalized_iff,
        mem_normalizedPuncturedMarkoffPointsWithSmallFirstTwoRotationOrders_iff]
      constructor
      · simpa only [normalizedPuncturedPoint, normalizedSurfaceOfPunctured,
          puncturedNormalizationEquiv_coe] using Nat.lt_succ_of_le hfirst
      · simpa only [normalizedPuncturedPoint, normalizedSurfaceOfPunctured,
          puncturedNormalizationEquiv_coe] using Nat.lt_succ_of_le hsecond
    have hpLeSmallOrderSet : p ≤ 2 * (2 + d *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 2 := by
      calc
        p ≤ (puncturedGammaOrbit x).ncard := hpLeOrbit
        _ ≤ (puncturedMarkoffPointsWithSmallFirstTwoRotationOrders p (d + 1)).card :=
          horbitSmall
        _ ≤ 2 * (2 + d *
            ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 2 :=
          puncturedMarkoffPointsWithSmallFirstTwoRotationOrders_succ_card_le_divisor_sensitive
            hpTwo d
    have hcube' := hcube d hdPos hpLeSmallOrderSet
    have hlinear' := hlinear d hdUpper
    obtain ⟨y, hzy, hincrease⟩ :=
      exists_sameNormalizedComponent_maximalOrder_increase_of_directBounds
        p hpTwo (δ := (1 / 3 : ℝ)) (by norm_num)
        (corvajaZannierWeightedTraceBound p (quadraticFiniteField p))
        (normalizedPuncturedPoint z)
        (by simpa only [show (1 / 2 + 1 / 3 : ℝ) = 5 / 6 by norm_num,
            d, orderMeasure] using hdUpper)
        (by simpa [d, orderMeasure] using hcube')
        (by simpa [d, orderMeasure] using hlinear')
    obtain ⟨g, hg⟩ :=
      (sameNormalizedComponent_iff_exists_gamma (normalizedPuncturedPoint z) y).1 hzy
    let w : PuncturedMarkoffSurface (ZMod p) := g • z
    have hwComponent : SamePuncturedComponent x w :=
      samePuncturedComponent_trans hzComponent
        ((samePuncturedComponent_iff_exists z w).2 ⟨g, rfl⟩)
    have hwNormalized : normalizedPuncturedPoint w = y := by
      change normalizedPuncturedPoint (g • z) = y
      rw [normalizedPuncturedPoint_smul]
      exact hg
    have hwMax := hmax w hwComponent
    change maximalCoordinateRotationOrder (normalizedPuncturedPoint w).1 ≤ d at hwMax
    rw [hwNormalized] at hwMax
    have hincrease' : d < maximalCoordinateRotationOrder y.1 := by
      simpa [d, orderMeasure] using hincrease
    exact (not_lt_of_ge hwMax) hincrease'
  intro a b
  obtain ⟨ga, hga⟩ := (samePuncturedComponent_iff_exists c a).1 (hAll a)
  obtain ⟨gb, hgb⟩ := (samePuncturedComponent_iff_exists c b).1 (hAll b)
  refine ⟨gb * ga⁻¹, ?_⟩
  calc
    (gb * ga⁻¹) • a = gb • (ga⁻¹ • a) := mul_smul _ _ _
    _ = gb • c := by rw [← hga]; simp
    _ = b := hgb

private theorem explicitCutoff_seven_le_for_assembly
    {p : ℕ} [Fact p.Prime]
    (hp : explicitStrongApproximationCutoff ≤ p) : 7 ≤ p := by
  have hpOne : (1 : ℝ) ≤ p := by
    exact_mod_cast (explicitCutoff_gt_one.trans_le hp).le
  have hrootLe : (p : ℝ) ^ (1 / 8 : ℝ) ≤ p := by
    simpa using Real.rpow_le_self_of_one_le hpOne (by norm_num : (1 / 8 : ℝ) ≤ 1)
  have hfiveRoot : (5 : ℝ) < (p : ℝ) ^ (1 / 8 : ℝ) :=
    small_fixed_lt_rpow_one_div_eight_of_explicitCutoff hp (by norm_num)
  have hfive : 5 < p := by
    exact_mod_cast hfiveRoot.trans_le hrootLe
  have hpSix : p ≠ 6 := by
    intro hpEq
    subst p
    have hprime : Nat.Prime 6 := Fact.out
    norm_num at hprime
  omega

/-- **Explicit punctured transitivity.**  The closed cutoff supplies
all numerical estimates; the large-order route and cage connectivity are the
pointwise explicit endgame theorems. -/
theorem puncturedMarkoffTransitiveAt_of_explicitCutoff
    (p : ℕ) (hpPrime : p.Prime)
    (hp : explicitStrongApproximationCutoff ≤ p) :
    PuncturedMarkoffTransitiveAt p hpPrime := by
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hpSeven : 7 ≤ p := explicitCutoff_seven_le_for_assembly hp
  have hpThree : 3 < p := by omega
  have hthree : (3 : ZMod p) ≠ 0 := by
    intro hzero
    have hpDvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hzero
    exact (Nat.not_dvd_of_pos_of_lt (by omega) hpThree) hpDvd
  letI : Invertible (3 : ZMod p) := invertibleOfNonzero hthree
  obtain ⟨baseNormalized, hbaseCage⟩ :=
    exists_normalizedPunctured_splitCagePoint p hpSeven
  let base : PuncturedMarkoffSurface (ZMod p) :=
    (puncturedNormalizationEquiv (ZMod p)).symm baseNormalized
  apply puncturedMarkoffTransitiveAt_of_maximalOrbit_frontier p hpThree base
  · intro d hdPos hpLe
    exact explicit_lowOrder_divisorSensitive_cube hp hdPos hpLe
  · intro d hUpper
    exact explicit_middleGame_corvajaZannier_linearBound hp hUpper
  · intro z hzLarge
    have hcoordinate :
        (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder z.1.u1 ∨
        (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder z.1.u2 ∨
        (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder z.1.u3 := by
      by_contra hsmall
      push_neg at hsmall
      have hmaxSmall : (maximalCoordinateRotationOrder z.1 : ℝ) <
          (p : ℝ) ^ (5 / 6 : ℝ) := by
        rw [maximalCoordinateRotationOrder, Nat.cast_max, Nat.cast_max]
        exact max_lt hsmall.1 (max_lt hsmall.2.1 hsmall.2.2)
      exact (not_lt_of_ge hzLarge) hmaxSmall
    have hcomponent :=
      explicit_sameNormalizedComponent_of_largeOrder_to_splitCage
        hp (normalizedSurfaceOfPunctured baseNormalized) z hbaseCage hcoordinate
    simpa [base, normalizedPuncturedPoint] using hcomponent

/-- Raw-expression form of the explicit endpoint.  This displays the actual
closed natural-number bound without requiring clients to unfold either sealed
constant. -/
theorem puncturedMarkoffTransitiveAt_of_concreteExplicitBound
    (p : ℕ) (hpPrime : p.Prime)
    (hp : (2 ^ 9 * (48 ^ 3 + 1) ^ 18 *
      (2 ^ 9 * (9 ^ 9) ^ (2 ^ 9)) ^ 8 + 1) ≤ p) :
    PuncturedMarkoffTransitiveAt p hpPrime := by
  apply puncturedMarkoffTransitiveAt_of_explicitCutoff p hpPrime
  simpa only [explicitStrongApproximationCutoff_eq,
    explicitDivisorMomentConstant_eq] using hp

private theorem preliminaryCutoff_seven_le_for_assembly
    {p : ℕ} [Fact p.Prime]
    (hp : preliminaryStrongApproximationCutoff ≤ p) : 7 ≤ p := by
  have hpOne : (1 : ℝ) ≤ p := by
    exact_mod_cast (preliminaryCutoff_gt_one.trans_le hp).le
  have hrootLe : (p : ℝ) ^ (1 / 8 : ℝ) ≤ p := by
    simpa using
      Real.rpow_le_self_of_one_le hpOne (by norm_num : (1 / 8 : ℝ) ≤ 1)
  have hfiveRoot : (5 : ℝ) < (p : ℝ) ^ (1 / 8 : ℝ) :=
    preliminary_small_fixed_lt_rpow_one_div_eight hp (by norm_num)
  have hfive : 5 < p := by
    exact_mod_cast hfiveRoot.trans_le hrootLe
  have hpSix : p ≠ 6 := by
    intro hpEq
    subst p
    have hprime : Nat.Prime 6 := Fact.out
    norm_num at hprime
  omega
/-- **Elementary preliminary-route punctured transitivity.**  This is the
paper's all-divisors Corvaja--Zannier route with the analytic Nicolas estimate
replaced by the fully formalized elementary tenth-moment divisor bound. -/
theorem puncturedMarkoffTransitiveAt_of_preliminaryCutoff
    (p : ℕ) (hpPrime : p.Prime)
    (hp : preliminaryStrongApproximationCutoff ≤ p) :
    PuncturedMarkoffTransitiveAt p hpPrime := by
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hpSeven : 7 ≤ p := preliminaryCutoff_seven_le_for_assembly hp
  have hpThree : 3 < p := by omega
  have hthree : (3 : ZMod p) ≠ 0 := by
    intro hzero
    have hpDvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hzero
    exact (Nat.not_dvd_of_pos_of_lt (by omega) hpThree) hpDvd
  letI : Invertible (3 : ZMod p) := invertibleOfNonzero hthree
  obtain ⟨baseNormalized, hbaseCage⟩ :=
    exists_normalizedPunctured_splitCagePoint p hpSeven
  let base : PuncturedMarkoffSurface (ZMod p) :=
    (puncturedNormalizationEquiv (ZMod p)).symm baseNormalized
  apply puncturedMarkoffTransitiveAt_of_maximalOrbit_frontier p hpThree base
  · intro d hdPos hpLe
    exact preliminary_lowOrder_divisorSensitive_cube hp hdPos hpLe
  · intro d hUpper
    exact preliminary_middleGame_corvajaZannier_linearBound hp hUpper
  · intro z hzLarge
    have hcoordinate :
        (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder z.1.u1 ∨
        (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder z.1.u2 ∨
        (p : ℝ) ^ (5 / 6 : ℝ) ≤ rotationOrder z.1.u3 := by
      by_contra hsmall
      push_neg at hsmall
      have hmaxSmall : (maximalCoordinateRotationOrder z.1 : ℝ) <
          (p : ℝ) ^ (5 / 6 : ℝ) := by
        rw [maximalCoordinateRotationOrder, Nat.cast_max, Nat.cast_max]
        exact max_lt hsmall.1 (max_lt hsmall.2.1 hsmall.2.2)
      exact (not_lt_of_ge hzLarge) hmaxSmall
    have hcomponent :=
      preliminary_sameNormalizedComponent_of_largeOrder_to_splitCage
        hp (normalizedSurfaceOfPunctured baseNormalized) z hbaseCage hcoordinate
    simpa [base, normalizedPuncturedPoint] using hcomponent

/-- Raw-expression form of the elementary preliminary-route endpoint. -/
theorem puncturedMarkoffTransitiveAt_of_concretePreliminaryBound
    (p : ℕ) (hpPrime : p.Prime)
    (hp : (2 ^ 1833 * (48 ^ 3 + 1) ^ 10 + 1) ≤ p) :
    PuncturedMarkoffTransitiveAt p hpPrime := by
  apply puncturedMarkoffTransitiveAt_of_preliminaryCutoff p hpPrime
  simpa only [preliminaryStrongApproximationCutoff_eq] using hp
end

end BGS.Markoff
