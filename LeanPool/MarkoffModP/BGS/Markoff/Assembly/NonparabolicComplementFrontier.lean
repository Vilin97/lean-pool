/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Assembly.NonparabolicBadComponent
import LeanPool.MarkoffModP.BGS.Markoff.Assembly.NonparabolicPuncturedSmallOrderCount
import LeanPool.MarkoffModP.BGS.Markoff.Assembly.OrbitDivisibility
import LeanPool.MarkoffModP.BGS.Markoff.Assembly.PairedMaximalDivisorMiddleGame
import LeanPool.MarkoffModP.BGS.Markoff.Core.EvenSignAction

/-!
# Nonparabolic complement frontier

Instead of maximizing the rotation order on one bad orbit, this route
maximizes it on the entire complement of a fixed punctured component.  That
complement is Vieta-invariant, so its cardinality is divisible by `p`.
Assuming the expected even-sign divisibility by four, every nonempty
complement therefore has at least `4 * p` points.

The parabolic endgame bridge puts the whole complement in the
fixed-point-free small-order set.  Consequently its maximal order `d` forces

`8 * p ≤ (d * M) ^ 2`,

with no additive parabolic correction.
-/

namespace BGS.Markoff

open BGS.NumberTheory

noncomputable section

/-- The finite complement of the punctured component of `c`. -/
def puncturedComponentComplementFinset
    (p : ℕ) [Fact p.Prime]
    (c : PuncturedMarkoffSurface (ZMod p)) :
    Finset (PuncturedMarkoffSurface (ZMod p)) := by
  classical
  exact Finset.univ.filter fun x => ¬ SamePuncturedComponent c x

@[simp]
theorem mem_puncturedComponentComplementFinset_iff
    {p : ℕ} [Fact p.Prime]
    {c x : PuncturedMarkoffSurface (ZMod p)} :
    x ∈ puncturedComponentComplementFinset p c ↔
      ¬ SamePuncturedComponent c x := by
  classical
  simp [puncturedComponentComplementFinset]

theorem puncturedComponentComplementFinset_vieta1_mem_iff
    {p : ℕ} [Fact p.Prime]
    (c x : PuncturedMarkoffSurface (ZMod p)) :
    vieta1PuncturedPerm (ZMod p) x ∈
        puncturedComponentComplementFinset p c ↔
      x ∈ puncturedComponentComplementFinset p c := by
  rw [mem_puncturedComponentComplementFinset_iff,
    mem_puncturedComponentComplementFinset_iff]
  constructor
  · intro hnot hcx
    apply hnot
    exact samePuncturedComponent_trans hcx
      (samePuncturedComponent_vieta1 x)
  · intro hnot hcv
    apply hnot
    exact samePuncturedComponent_trans hcv
      (samePuncturedComponent_symm (samePuncturedComponent_vieta1 x))

theorem puncturedComponentComplementFinset_vieta2_mem_iff
    {p : ℕ} [Fact p.Prime]
    (c x : PuncturedMarkoffSurface (ZMod p)) :
    vieta2PuncturedPerm (ZMod p) x ∈
        puncturedComponentComplementFinset p c ↔
      x ∈ puncturedComponentComplementFinset p c := by
  rw [mem_puncturedComponentComplementFinset_iff,
    mem_puncturedComponentComplementFinset_iff]
  constructor
  · intro hnot hcx
    apply hnot
    exact samePuncturedComponent_trans hcx
      (samePuncturedComponent_vieta2 x)
  · intro hnot hcv
    apply hnot
    exact samePuncturedComponent_trans hcv
      (samePuncturedComponent_symm (samePuncturedComponent_vieta2 x))

theorem puncturedComponentComplementFinset_vieta3_mem_iff
    {p : ℕ} [Fact p.Prime]
    (c x : PuncturedMarkoffSurface (ZMod p)) :
    vieta3PuncturedPerm (ZMod p) x ∈
        puncturedComponentComplementFinset p c ↔
      x ∈ puncturedComponentComplementFinset p c := by
  rw [mem_puncturedComponentComplementFinset_iff,
    mem_puncturedComponentComplementFinset_iff]
  constructor
  · intro hnot hcx
    apply hnot
    exact samePuncturedComponent_trans hcx
      (samePuncturedComponent_vieta3 x)
  · intro hnot hcv
    apply hnot
    exact samePuncturedComponent_trans hcv
      (samePuncturedComponent_symm (samePuncturedComponent_vieta3 x))

/-- The complement of one component is itself Vieta-invariant, hence its
cardinality is divisible by the characteristic prime. -/
theorem prime_dvd_puncturedComponentComplementFinset_card
    (p : ℕ) [Fact p.Prime] (hpThree : 3 < p)
    (c : PuncturedMarkoffSurface (ZMod p)) :
    p ∣ (puncturedComponentComplementFinset p c).card := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hpDvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hpDvd
  have hthree : (3 : ZMod p) ≠ 0 := by
    intro hzero
    have hpDvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hzero
    exact (Nat.not_dvd_of_pos_of_lt (by omega) hpThree) hpDvd
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  exact card_cast_eq_zero_of_vieta_invariant htwo hthree
    (puncturedComponentComplementFinset p c)
    (puncturedComponentComplementFinset_vieta1_mem_iff c)
    (puncturedComponentComplementFinset_vieta2_mem_iff c)
    (puncturedComponentComplementFinset_vieta3_mem_iff c)

/-- Combining Vieta `p`-divisibility with a supplied even-sign
four-divisibility gives the exact `4 * p` lower bound for a nonempty
component complement. -/
theorem four_mul_prime_le_puncturedComponentComplementFinset_card
    (p : ℕ) [Fact p.Prime] (hpThree : 3 < p)
    (c : PuncturedMarkoffSurface (ZMod p))
    (hnonempty : (puncturedComponentComplementFinset p c).Nonempty)
    (hfour : 4 ∣ (puncturedComponentComplementFinset p c).card) :
    4 * p ≤ (puncturedComponentComplementFinset p c).card := by
  have hpOdd : Odd p :=
    (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hcoprime : Nat.Coprime 4 p := by
    simpa using
      hpOdd.coprime_two_left.mul_left hpOdd.coprime_two_left
  have hdiv :
      4 * p ∣ (puncturedComponentComplementFinset p c).card :=
    hcoprime.mul_dvd_of_dvd_of_dvd hfour
      (prime_dvd_puncturedComponentComplementFinset_card p hpThree c)
  exact Nat.le_of_dvd (Finset.card_pos.mpr hnonempty) hdiv

private def normalizedPuncturedPointNonparabolicComplement
    {R : Type*} [Field R] [Invertible (3 : R)]
    (x : PuncturedMarkoffSurface R) : NormalizedMarkoffSurface R :=
  normalizedSurfaceOfPunctured (puncturedNormalizationEquiv R x)

private theorem normalizedPuncturedPointNonparabolicComplement_smul
    {R : Type*} [Field R] [Invertible (3 : R)]
    (g : Gamma R) (z : PuncturedMarkoffSurface R) :
    normalizedPuncturedPointNonparabolicComplement (g • z) =
      normalizedGammaPerm R g
        (normalizedPuncturedPointNonparabolicComplement z) := by
  have hzinv :
      (normalizationSurfaceEquiv R).symm
          (normalizedSurfaceOfPunctured
            (puncturedNormalizationEquiv R z)) = z.1 := by
    apply Subtype.ext
    exact (normalizationEquiv R).symm_apply_apply z.1.1
  unfold normalizedPuncturedPointNonparabolicComplement
  rw [normalizedGammaPerm_apply, hzinv]
  apply Subtype.ext
  rfl

/-- Complement-maximal paired frontier with the fixed-point-free low-order
count.  The even-sign action is kept explicit: `hsign` records invariance of
the component complement, while `hfour` supplies the remaining free-action
cardinality consequence. -/
theorem
    puncturedMarkoffTransitiveAt_of_nonparabolicComplement_pairedMaximalDivisor_frontier
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpThree : 3 < p)
    (c : PuncturedMarkoffSurface (ZMod p))
    (hcube : ∀ d : ℕ, 0 < d →
      8 * p ≤
        (d * maximalDivisorCountSum p (d + 1)) ^ 2 →
      (6 * maximalDivisorCountSum p (d + 1)) ^ 3 < d)
    (hlinear : ∀ d : ℕ,
      (d : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ) →
      24 * maximalDivisorCountSum p (d + 1) * d < p)
    (hlarge : ∀ z : NormalizedMarkoffSurface (ZMod p),
      (p : ℝ) ^ (5 / 6 : ℝ) ≤
          maximalCoordinateRotationOrder z.1 →
      SameNormalizedComponent
        (normalizedPuncturedPointNonparabolicComplement c) z)
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
        (normalizedPuncturedPointNonparabolicComplement w).1
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
            (normalizedPuncturedPointNonparabolicComplement z).1.u1 :=
        rotationOrder_pos _
      exact hfirstPos.trans_le <| by
        simpa [d, orderMeasure] using
          rotationOrder_first_le_maximalCoordinateRotationOrder
            (normalizedPuncturedPointNonparabolicComplement z).1
    have hnotBaseZ : ¬ SameNormalizedComponent
        (normalizedPuncturedPointNonparabolicComplement c)
        (normalizedPuncturedPointNonparabolicComplement z) := by
      intro hcz
      apply hzNotComponent
      exact
        (samePuncturedComponent_iff_sameNormalizedComponent c z).2 hcz
    have hdUpper : (d : ℝ) < (p : ℝ) ^ (5 / 6 : ℝ) := by
      by_contra hd
      apply hnotBaseZ
      apply hlarge (normalizedPuncturedPointNonparabolicComplement z)
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
          (normalizedPuncturedPointNonparabolicComplement c)
          (normalizedPuncturedPointNonparabolicComplement w) := by
        intro hcw
        apply hwNotComponent
        exact
          (samePuncturedComponent_iff_sameNormalizedComponent c w).2 hcw
      have hnonparabolic :=
        first_two_nonparabolic_of_not_sameComponent_of_endgame_large_connected
          hpTwo
          (normalizedPuncturedPointNonparabolicComplement c)
          (normalizedPuncturedPointNonparabolicComplement w)
          hlarge hwNotBase
      have hwMax := hmax w hwBad
      have hfirst :
          rotationOrder
              (normalizedPuncturedPointNonparabolicComplement w).1.u1 ≤ d :=
        (rotationOrder_first_le_maximalCoordinateRotationOrder
          (normalizedPuncturedPointNonparabolicComplement w).1).trans hwMax
      have hsecond :
          rotationOrder
              (normalizedPuncturedPointNonparabolicComplement w).1.u2 ≤ d :=
        (rotationOrder_second_le_maximalCoordinateRotationOrder
          (normalizedPuncturedPointNonparabolicComplement w).1).trans hwMax
      change w ∈
        puncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders
          p (d + 1)
      rw [
        puncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders,
        mem_originalPuncturedFinsetOfNormalized_iff,
        mem_normalizedPuncturedMarkoffPointsWithSmallNonparabolicFirstTwoRotationOrders_iff
      ]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [normalizedPuncturedPointNonparabolicComplement,
          normalizedSurfaceOfPunctured,
          puncturedNormalizationEquiv_coe] using Nat.lt_succ_of_le hfirst
      · simpa only [normalizedPuncturedPointNonparabolicComplement,
          normalizedSurfaceOfPunctured,
          puncturedNormalizationEquiv_coe] using Nat.lt_succ_of_le hsecond
      · simpa only [normalizedPuncturedPointNonparabolicComplement,
          normalizedSurfaceOfPunctured,
          puncturedNormalizationEquiv_coe] using hnonparabolic.1
      · simpa only [normalizedPuncturedPointNonparabolicComplement,
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
    have hrootCoefficient :
        6 * (middleGameMaximalOrders p d).card ≤
          6 * maximalDivisorCountSum p (d + 1) :=
      Nat.mul_le_mul_left 6 hmaximalCard
    have hlinearCoefficient :
        24 * (middleGameMaximalOrders p d).card ≤
          24 * maximalDivisorCountSum p (d + 1) :=
      Nat.mul_le_mul_left 24 hmaximalCard
    have hcube' :
        (6 * (middleGameMaximalOrders p d).card) ^ 3 < d :=
      (Nat.pow_le_pow_left hrootCoefficient 3).trans_lt hcubeCount
    have hlinear' :
        24 * (middleGameMaximalOrders p d).card * d < p :=
      (Nat.mul_le_mul_right d hlinearCoefficient).trans_lt hlinearCount
    obtain ⟨y, hzy, hincrease⟩ :=
      exists_sameNormalizedComponent_maximalOrder_increase_of_pairedMaximalDivisorBounds
        p hpTwo (delta := (1 / 3 : ℝ)) (by norm_num)
        (normalizedPuncturedPointNonparabolicComplement z)
        (by simpa only [show (1 / 2 + 1 / 3 : ℝ) = 5 / 6 by norm_num,
            d, orderMeasure] using hdUpper)
        (by simpa [d, orderMeasure] using hcube')
        (by simpa [d, orderMeasure] using hlinear')
    obtain ⟨g, hg⟩ :=
      (sameNormalizedComponent_iff_exists_gamma
        (normalizedPuncturedPointNonparabolicComplement z) y).1 hzy
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
        normalizedPuncturedPointNonparabolicComplement w = y := by
      change normalizedPuncturedPointNonparabolicComplement (g • z) = y
      rw [normalizedPuncturedPointNonparabolicComplement_smul]
      exact hg
    have hwMax := hmax w hwBad
    change maximalCoordinateRotationOrder
      (normalizedPuncturedPointNonparabolicComplement w).1 ≤ d at hwMax
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
